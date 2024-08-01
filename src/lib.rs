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
pub mod terminator;
pub mod transform;
mod util;
pub mod value;
pub mod visualization;

use std::marker::PhantomData;

use crate::{
    rustc_interface::{
        ast::Mutability,
        hir::def_id::{DefId, LocalDefId},
        middle::{
            mir::{self, Body, Local, Location, ProjectionElem, Rvalue, VarDebugInfo},
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
    borrows::{
        domain::MaybeOldPlace,
        reborrowing_dag::ReborrowingDag,
        unblock_graph::UnblockGraph,
        unblock_reason::{UnblockReason, UnblockReasons},
    },
    combined_pcs::UnblockAction,
    free_pcs::RepackOp,
    utils::PlaceRepacker,
    FpcsOutput,
};
use pcs_interaction::PcsLocation;
use results::{BackwardsFacts, ResultPath, ResultPaths, SymbolicExecutionResult};
use semantics::VerifierSemantics;
use value::SymVar;
use visualization::{OutputMode, VisFormat};

use self::{
    path::{AcyclicPath, Path},
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
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        match self {
            Assertion::False => "false".to_string(),
            Assertion::Eq(val, true) => val.to_vis_string(tcx, debug_info, mode),
            Assertion::Eq(val, false) => format!("!{}", val.to_vis_string(tcx, debug_info, mode)),
            Assertion::Precondition(def_id, substs, args) => {
                format!(
                    "{:?}({})",
                    def_id,
                    args.to_vis_string(tcx, debug_info, mode)
                )
            }
        }
    }
}

pub struct SymbolicExecution<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    pub body: &'mir Body<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    havoc: HavocData,
    symvars: Vec<ty::Ty<'tcx>>,
    pub arena: &'sym SymExContext<'tcx>,
    debug_output_dir: Option<String>,
    err_ctx: Option<ErrorContext>,
    verifier_semantics: PhantomData<S>,
    new_symvars_allowed: bool,
}

trait LookupType {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone>: std::fmt::Debug;
    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>>;
}

struct LookupGet;
struct LookupTake;

struct LookupGetOldest;

impl LookupType for LookupGetOldest {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone> =
        &'heap HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.get_oldest_for_place(&place.place())
    }
}

impl LookupType for LookupGet {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone> =
        &'heap HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.get(place)
    }
}

impl LookupType for LookupTake {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone> =
        &'heap mut HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.take(place)
    }
}

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn new(params: SymExParams<'mir, 'sym, 'tcx, S>) -> Self {
        SymbolicExecution {
            new_symvars_allowed: params.new_symvars_allowed,
            tcx: params.tcx,
            def_id: params.def_id,
            body: params.body,
            fpcs_analysis: params.fpcs_analysis,
            havoc: HavocData::new(&params.body),
            verifier_semantics: PhantomData,
            arena: params.arena,
            debug_output_dir: params.debug_output_dir,
            err_ctx: None,
            symvars: vec![],
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
            .mk_internal_error(err, ty, self.err_ctx.as_ref())
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
        let heap_str = format!("{:#?}", heap);
        self.encode_place_opt::<T, P>(heap, place)
            .unwrap_or_else(|| {
                let place = (*place).into();
                self.mk_internal_err_expr(
                    format!(
                        "Heap lookup failed for place [{}: {:?}] in {}",
                        place.to_short_string(self.repacker()),
                        place.place().ty(self.repacker()),
                        heap_str
                    ),
                    place.place().ty(self.repacker()).ty,
                )
            })
    }

    pub fn encode_operand(
        &self,
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
                        substs,
                    } => {
                        let snapshot = function_call_snapshots.get_snapshot(&call_location);
                        for (idx, place) in blocks_args {
                            let value = self.arena.mk_backwards_fn(BackwardsFn {
                                caller_def_id: Some(self.def_id.into()),
                                def_id: *def_id,
                                substs,
                                arg_snapshots: snapshot.args,
                                return_snapshot: self.arena.mk_ref(
                                    self.encode_place::<LookupGet, _>(heap.0, blocked_place),
                                    Mutability::Mut,
                                ),
                                arg_index: *idx,
                            });
                            assert_eq!(value.ty(self.tcx), snapshot.args[*idx].ty(self.tcx));
                            heap.insert_maybe_old_place(
                                *place,
                                self.arena.mk_projection(ProjectionElem::Deref, value),
                            );
                        }
                    }
                },
            }
        }
    }

    fn compute_backwards_facts(
        &mut self,
        path: &Path<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
    ) -> BackwardsFacts<'sym, 'tcx, S::SymValSynthetic> {
        let return_place: mir::Place<'tcx> = mir::RETURN_PLACE.into();
        let return_place: Place<'tcx> = return_place.into();
        let mut facts = BackwardsFacts::new();
        if return_place.is_mut_ref(self.body, self.tcx) {
            let mut borrow_state = pcs.extra.after.clone();
            borrow_state.filter_for_path(&path.path.to_slice());
            for arg in 1..=self.body.arg_count {
                let local = Local::from_usize(arg);
                let arg_place: mir::Place<'tcx> = local.into();
                let arg_place: Place<'tcx> = arg_place.into();
                let blocked_place = arg_place.project_deref(self.repacker());
                if arg_place.is_mut_ref(self.body, self.tcx) {
                    let mut heap = path.heap.clone();
                    let mut heap = SymbolicHeap::new(&mut heap, self.tcx, self.body, &self.arena);
                    heap.insert(
                        return_place.project_deref(self.repacker()),
                        self.arena.mk_var(
                            SymVar::ReservedBackwardsFnResult,
                            return_place
                                .project_deref(self.repacker())
                                .ty(self.body, self.tcx)
                                .ty,
                        ),
                        pcs.location,
                    );
                    let mut ug = UnblockGraph::new();
                    ug.unblock_place(
                        blocked_place.into(),
                        &borrow_state,
                        pcs.location.block,
                        UnblockReasons::new(UnblockReason::BackwardsFunction(local)),
                        self.tcx,
                    );
                    let actions = ug.actions(self.tcx);
                    eprintln!("actions: {:#?}", actions);
                    self.apply_unblock_actions(
                        actions,
                        &mut heap,
                        &path.function_call_snapshots,
                        pcs.location,
                    );
                    eprintln!(
                        "At the place {:?} is {}",
                        blocked_place,
                        heap.0.get(&blocked_place).unwrap()
                    );
                    facts.insert(arg - 1, heap.0.get(&blocked_place).unwrap());
                }
            }
        }
        facts
    }

    fn add_to_result_paths(
        &mut self,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
        result_paths: &mut ResultPaths<'sym, 'tcx, S::SymValSynthetic>,
    ) {
        let return_place: Place<'tcx> = mir::RETURN_PLACE.into();
        let expr = self.encode_place::<LookupGet, _>(&path.heap, &return_place);
        let backwards_facts = self.compute_backwards_facts(path, pcs);
        result_paths.insert(ResultPath::new(
            path.path.clone(),
            path.pcs.clone(),
            expr,
            backwards_facts,
            path.heap.clone(),
        ));
    }

    fn repacker(&self) -> PlaceRepacker<'_, 'tcx> {
        PlaceRepacker::new(&self.body, self.tcx)
    }

    fn havoc_operand_ref(
        &mut self,
        operand: &mir::Operand<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        reborrows: &ReborrowingDag<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S::SymValSynthetic>> {
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
                    let sym_var = self.mk_fresh_symvar(*ty);
                    assert_eq!(blocked_by.ty(self.repacker()).ty, *ty);
                    heap.insert_maybe_old_place(blocked_by, sym_var);
                    Some(self.arena.mk_ref(sym_var, Mutability::Mut))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn mk_fresh_symvar(&mut self, ty: ty::Ty<'tcx>) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        assert!(self.new_symvars_allowed);
        let var = SymVar::Normal(self.symvars.len());
        self.symvars.push(ty);
        self.arena.mk_var(var, ty)
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
        let value = self.arena.mk_aggregate(
            AggregateKind::pcs(place_ty.ty, place_ty.variant_index),
            self.arena.alloc_slice(&args),
        );
        eprintln!("Collapse ty: {:#?} for {}: {}", place_ty, args[0], value);
        heap.insert(*place, value, location);
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

pub struct SymExParams<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    pub def_id: LocalDefId,
    pub body: &'mir Body<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    pub verifier_semantics: S,
    pub arena: &'sym SymExContext<'tcx>,
    pub debug_output_dir: Option<String>,
    pub new_symvars_allowed: bool,
}

pub fn run_symbolic_execution_with<
    'mir,
    'sym,
    'tcx,
    S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>,
>(
    params: SymExParams<'mir, 'sym, 'tcx, S>,
    heap_data: HeapData<'sym, 'tcx, S::SymValSynthetic>,
    symvars: Vec<ty::Ty<'tcx>>,
) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
    SymbolicExecution::new(params).execute(heap_data, symvars)
}
pub fn run_symbolic_execution<
    'mir,
    'sym,
    'tcx,
    S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>,
>(
    params: SymExParams<'mir, 'sym, 'tcx, S>,
) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
    let (heap_data, symvars) = HeapData::init_for_body(params.arena, params.tcx, params.body);
    SymbolicExecution::new(params).execute(heap_data, symvars)
}
