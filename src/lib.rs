#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(associated_type_bounds)]
#![feature(let_chains)]
#![feature(anonymous_lifetime_in_impl_trait)]

pub mod context;
mod debug_info;
mod execute;
mod function_call_snapshot;
pub mod havoc;
pub mod heap;
pub mod path;
pub mod path_conditions;
mod pcs_interaction;
pub mod place;
pub mod results;
mod rustc_interface;
pub mod semantics;
mod stmt;
mod terminator;
pub mod transform;
mod util;
pub mod value;
pub mod visualization;

use crate::{
    rustc_interface::{
        ast::Mutability,
        hir::def_id::{DefId, LocalDefId},
        middle::{
            mir::{self, Body, Location, ProjectionElem, VarDebugInfo},
            ty::{self, GenericArgsRef, TyCtxt, TyKind},
        },
        span::ErrorGuaranteed,
    },
    value::BackwardsFn,
    visualization::StepType,
};
use context::{ErrorContext, ErrorLocation, SymExContext};
use function_call_snapshot::FunctionCallSnapshots;
use havoc::HavocData;
use heap::{HeapData, SymbolicHeap};
use pcs::{
    borrows::{domain::MaybeOldPlace, reborrowing_dag::ReborrowingDag},
    combined_pcs::UnblockAction,
    free_pcs::RepackOp,
    utils::PlaceRepacker,
    FpcsOutput,
};
use results::{ResultAssertion, ResultPath, SymbolicExecutionResult};
use semantics::VerifierSemantics;
use std::{
    collections::{BTreeSet, VecDeque},
    ops::Deref,
};
use value::SymValueKind;
use visualization::{export_assertions, export_path_json, export_path_list, VisFormat};

use self::{
    path::{AcyclicPath, Path},
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    place::Place,
    value::{AggregateKind, SymValue},
};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Assertion<'sym, 'tcx, T> {
    False,
    Eq(SymValue<'sym, 'tcx, T>, bool),
    Precondition(DefId, GenericArgsRef<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for Assertion<'sym, 'tcx, T> {
    fn to_vis_string(&self, tcx: Option<TyCtxt<'_>>, debug_info: &[VarDebugInfo]) -> String {
        match self {
            Assertion::False => "false".to_string(),
            Assertion::Eq(val, true) => val.to_vis_string(tcx, debug_info),
            Assertion::Eq(val, false) => format!("!{}", val.to_vis_string(tcx, debug_info)),
            Assertion::Precondition(def_id, substs, args) => {
                format!("{:?}({})", def_id, args.to_vis_string(tcx, debug_info))
            }
        }
    }
}

pub struct SymbolicExecution<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &'mir Body<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    havoc: HavocData,
    symvars: Vec<ty::Ty<'tcx>>,
    arena: &'sym SymExContext<'tcx>,
    verifier_semantics: S,
    debug_output_dir: Option<String>,
    err_ctx: Option<ErrorContext>,
}

trait LookupType {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym>;
    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>>;
}

struct LookupGet;
struct LookupTake;

impl LookupType for LookupGet {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym> = &'heap HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.get(place)
    }
}

impl LookupType for LookupTake {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym> = &'heap mut HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.take(place)
    }
}

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        body: &'mir Body<'tcx>,
        fpcs_analysis: FpcsOutput<'mir, 'tcx>,
        verifier_semantics: S,
        arena: &'sym SymExContext<'tcx>,
        debug_output_dir: Option<String>,
    ) -> Self {
        SymbolicExecution {
            tcx,
            def_id,
            body,
            fpcs_analysis,
            havoc: HavocData::new(&body),
            symvars: Vec::with_capacity(body.arg_count),
            verifier_semantics,
            arena,
            debug_output_dir,
            err_ctx: None,
        }
    }

    fn set_error_context(&mut self, path: AcyclicPath, location: ErrorLocation) {
        self.err_ctx = Some(ErrorContext {
            def_id: self.def_id,
            location,
            path,
        });
    }

    fn mk_internal_err_expr(
        &self,
        err: String,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        self.arena
            .mk_internal_error(err, ty, self.err_ctx.as_ref().unwrap())
    }

    fn encode_place_opt<'heap, T: LookupType, P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &self,
        heap: T::Heap<'heap, 'sym, 'tcx, S::SymValSynthetic>,
        place: &P,
    ) -> Option<SymValue<'sym, 'tcx, S::SymValSynthetic>> {
        let place = (*place).into();
        if place.is_ref(self.body, self.tcx) {
            return T::lookup(heap, &place.project_deref(self.repacker())).map(|v| {
                self.arena.mk_ref(
                    v,
                    if place.is_mut_ref(self.body, self.tcx) {
                        Mutability::Mut
                    } else {
                        Mutability::Not
                    },
                )
            });
        } else {
            return T::lookup(heap, &place);
        }
    }

    /// Encodes the symbolic value that the place currently holds. In the most
    /// simple cases, this is simply a heap lookup. If the place to lookup is a
    /// reference, we return a reference to the dereferenced value in the heap.
    fn encode_place<'heap, T: LookupType, P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &self,
        heap: T::Heap<'heap, 'sym, 'tcx, S::SymValSynthetic>,
        place: &P,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        self.encode_place_opt::<T, P>(heap, place)
            .unwrap_or_else(|| {
                let place = (*place).into();
                self.mk_internal_err_expr(
                    format!(
                        "Heap lookup failed for place [{}: {:?}]",
                        place.to_short_string(self.repacker()),
                        place.place().ty(self.repacker())
                    ),
                    place.place().ty(self.repacker()).ty,
                )
            })
    }

    fn encode_operand(
        &mut self,
        heap: &HeapData<'sym, 'tcx, S::SymValSynthetic>,
        operand: &mir::Operand<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let place: Place<'tcx> = (*place).into();
                self.encode_place::<LookupGet, _>(heap, &place)
            }
            mir::Operand::Constant(c) => self.arena.mk_constant(c.into()),
        }
    }

    fn apply_unblock_actions(
        &mut self,
        actions: Vec<UnblockAction<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: &FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        for action in actions {
            match action {
                UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                    is_mut,
                } => {
                    self.handle_removed_reborrow(&blocked_place, &assigned_place, is_mut, heap);
                }
                UnblockAction::Collapse(place, places) => {
                    self.collapse_place_from(&place.place(), &places[0].place(), heap, location);
                }
                UnblockAction::TerminateRegion(_, typ) => match &typ {
                    pcs::borrows::domain::AbstractionType::FunctionCall {
                        def_id,
                        location: call_location,
                        blocks_args,
                        blocked_place,
                    } => {
                        let snapshot = function_call_snapshots.get_snapshot(&call_location);
                        for (idx, place) in blocks_args {
                            let value = self.arena.mk_backwards_fn(BackwardsFn {
                                def_id: *def_id,
                                arg_snapshots: snapshot.args,
                                return_snapshot: self
                                    .encode_place::<LookupGet, _>(heap.0, blocked_place),
                                arg_index: *idx,
                            });
                            heap.insert_maybe_old_place(*place, value);
                        }
                    }
                },
            }
        }
    }

    fn add_to_result_paths(
        &mut self,
        path: &Path<'sym, 'tcx, S::SymValSynthetic>,
        result_paths: &mut BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>>,
    ) {
        let return_place: Place<'tcx> = mir::RETURN_PLACE.into();
        let expr = self.encode_place::<LookupGet, _>(&path.heap, &return_place);
        result_paths.insert((path.path.clone(), path.pcs.clone(), expr));
    }

    fn repacker(&self) -> PlaceRepacker<'_, 'tcx> {
        PlaceRepacker::new(&self.body, self.tcx)
    }

    fn havoc_refs_in_operand(
        &mut self,
        operand: &mir::Operand<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        reborrows: &ReborrowingDag<'tcx>,
    ) {
        match operand {
            mir::Operand::Move(place) => {
                let place: Place<'tcx> = (*place).into();
                if let ty::TyKind::Ref(_, ty, Mutability::Mut) =
                    place.ty(self.body, self.tcx).ty.kind()
                {
                    let blocked = reborrows.get_places_blocked_by(
                        pcs::borrows::domain::MaybeOldPlace::Current {
                            place: place.project_deref(self.repacker()).0,
                        },
                    );
                    assert!(blocked.len() == 1);
                    let blocked_by = blocked.into_iter().next().unwrap();
                    heap.insert_maybe_old_place(blocked_by, self.mk_fresh_symvar(*ty));
                };
            }
            _ => {}
        }
    }

    fn mk_fresh_symvar(&mut self, ty: ty::Ty<'tcx>) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        let var = self.arena.mk_var(self.symvars.len(), ty);
        self.symvars.push(ty);
        var
    }

    fn alloc_slice<T: Copy>(&self, t: &[T]) -> &'sym [T] {
        self.arena.alloc_slice(t)
    }

    fn explode_value(
        &self,
        place: &pcs::utils::Place<'tcx>,
        value: SymValue<'sym, 'tcx, S::SymValSynthetic>,
        places: impl Iterator<Item = pcs::utils::Place<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        let old_proj_len = place.projection.len();
        for f in places {
            assert_eq!(f.projection.len(), place.projection.len() + 1);
            let mut value = value;
            for elem in f.projection.iter().skip(old_proj_len) {
                value = self.arena.mk_projection(elem.clone(), value);
            }
            if f.is_ref(self.body, self.tcx) {
                heap.insert(
                    f.project_deref(self.repacker()),
                    self.arena.mk_projection(ProjectionElem::Deref, value),
                    location,
                );
            } else {
                heap.insert(f, value, location);
            }
        }
    }

    fn expand_place_with_guide(
        &self,
        place: &pcs::utils::Place<'tcx>,
        guide: &pcs::utils::Place<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        let value = match place.ty(self.fpcs_analysis.repacker()).ty.kind() {
            ty::TyKind::Ref(_, _, Mutability::Mut) => {
                // Expanding x into *x shouldn't expand sth in the heap
                return;
            }
            ty::TyKind::Ref(_, _, Mutability::Not) => {
                self.encode_place::<LookupGet, _>(heap.0, place)
            }
            _ => self.encode_place::<LookupTake, _>(heap.0, place),
        };
        let (field, rest, _) = place.expand_one_level(*guide, self.fpcs_analysis.repacker());
        self.explode_value(
            place,
            value,
            std::iter::once(field).chain(rest.into_iter()),
            heap,
            location,
        );
    }

    fn collapse_place_from(
        &self,
        place: &pcs::utils::Place<'tcx>,
        from: &pcs::utils::Place<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        if place.ty(self.fpcs_analysis.repacker()).ty.is_ref() {
            return;
        }
        let place_ty = place.ty(self.fpcs_analysis.repacker());
        let args: Vec<_> = if from.is_downcast_of(*place).is_some() || place_ty.ty.is_box() {
            vec![heap.0.take(from).unwrap_or_else(|| {
                self.mk_internal_err_expr(
                    format!("Place {:?} not found in heap[collapse]", from),
                    from.ty(self.fpcs_analysis.repacker()).ty,
                )
            })]
        } else {
            place
                .expand_field(None, self.fpcs_analysis.repacker())
                .iter()
                .map(|p| {
                    let place_to_take: MaybeOldPlace<'tcx> = (*p).into();
                    self.encode_place_opt::<LookupTake, MaybeOldPlace<'tcx>>(heap.0, &place_to_take)
                        .unwrap_or_else(|| {
                            self.mk_internal_err_expr(
                                format!("Place {:?} not found in heap[collapse]", place_to_take),
                                place_to_take.ty(self.fpcs_analysis.repacker()).ty,
                            )
                        })
                })
                .collect()
        };
        heap.insert(
            *place,
            self.arena.mk_aggregate(
                AggregateKind::pcs(
                    place_ty.ty,
                    from.ty(self.fpcs_analysis.repacker()).variant_index,
                ),
                self.arena.alloc_slice(&args),
            ),
            location,
        );
    }

    fn handle_repack(
        &self,
        repack: &RepackOp<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        match repack {
            RepackOp::StorageDead(_) => todo!(),
            RepackOp::IgnoreStorageDead(_) => {}
            RepackOp::Weaken(_, _, _) => {}
            RepackOp::Expand(place, guide, _) => {
                self.expand_place_with_guide(place, guide, heap, location)
            }
            RepackOp::Collapse(place, from, _) => {
                self.collapse_place_from(place, from, heap, location)
            }
            RepackOp::DerefShallowInit(_, _) => todo!(),
        }
    }
}

pub fn run_symbolic_execution<
    'mir,
    'sym,
    'tcx,
    S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>,
>(
    def_id: LocalDefId,
    mir: &'mir Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    verifier_semantics: S,
    arena: &'sym SymExContext<'tcx>,
    debug_output_dir: Option<&str>,
) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
    SymbolicExecution::new(
        tcx,
        def_id,
        mir,
        fpcs_analysis,
        verifier_semantics,
        arena,
        debug_output_dir.map(|s| s.to_string()),
    )
    .execute()
}
