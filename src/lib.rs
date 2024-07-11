#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(associated_type_bounds)]
#![feature(let_chains)]
#![feature(anonymous_lifetime_in_impl_trait)]

pub mod context;
mod debug_info;
pub mod havoc;
pub mod heap;
pub mod path;
pub mod path_conditions;
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

use crate::rustc_interface::{
    ast::Mutability,
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, ProjectionElem, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt, TyKind},
    },
    span::ErrorGuaranteed,
};
use context::SymExContext;
use havoc::HavocData;
use heap::{HeapData, SymbolicHeap};
use pcs::{
    borrows::{
        domain::{BorrowsState, Reborrow, TerminatedReborrows},
        engine::{BorrowAction, BorrowsDomain, ReborrowAction},
        reborrowing_dag::ReborrowingDag,
    },
    combined_pcs::{PlaceCapabilitySummary, UnblockAction, UnblockEdgeType, UnblockGraph},
    free_pcs::{CapabilitySummary, FreePcsLocation, RepackOp},
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
    fn to_vis_string(&self, debug_info: &[VarDebugInfo]) -> String {
        match self {
            Assertion::False => "false".to_string(),
            Assertion::Eq(val, true) => val.to_vis_string(debug_info),
            Assertion::Eq(val, false) => format!("!{}", val.to_vis_string(debug_info)),
            Assertion::Precondition(def_id, substs, args) => {
                format!(
                    "{:?}({})",
                    def_id,
                    args.iter()
                        .map(|arg| arg.to_vis_string(debug_info))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

pub struct SymbolicExecution<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    havoc: HavocData,
    symvars: Vec<ty::Ty<'tcx>>,
    arena: &'sym SymExContext<'tcx>,
    verifier_semantics: S,
    debug_output_dir: Option<String>,
}

trait LookupType {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym>;
    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &Place<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>>;
}

struct LookupGet;
struct LookupTake;

impl LookupType for LookupGet {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym> = &'heap HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &Place<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.get(place)
    }
}

impl LookupType for LookupTake {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym> = &'heap mut HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &Place<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.take(place)
    }
}

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        fpcs_analysis: FpcsOutput<'mir, 'tcx>,
        verifier_semantics: S,
        arena: &'sym SymExContext<'tcx>,
        debug_output_dir: Option<String>,
    ) -> Self {
        SymbolicExecution {
            tcx,
            body,
            fpcs_analysis,
            havoc: HavocData::new(&body),
            symvars: Vec::with_capacity(body.arg_count),
            verifier_semantics,
            arena,
            debug_output_dir,
        }
    }

    /// Encodes the symbolic value that the place currently holds. In the most
    /// simple cases, this is simply a heap lookup. If the place to lookup is a
    /// reference, we return a reference to the dereferenced value in the heap.
    fn encode_place<'heap, T: LookupType>(
        &self,
        heap: T::Heap<'heap, 'sym, 'tcx, S::SymValSynthetic>,
        place: &Place<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        if place.0.is_ref(self.body, self.tcx) {
            return self.arena.mk_ref(
                T::lookup(heap, &place.project_deref(self.tcx)).unwrap_or(
                    self.arena.mk_internal_error(
                        format!("Heap lookup failed for place [{:?}]", place),
                        self.arena.tcx.mk_ty_from_kind(TyKind::Error(
                            ErrorGuaranteed::unchecked_claim_error_was_emitted(),
                        )),
                    ),
                ),
                if place.0.is_mut_ref(self.body, self.tcx) {
                    Mutability::Mut
                } else {
                    Mutability::Not
                },
            );
        } else {
            return T::lookup(heap, place).unwrap_or(self.arena.mk_internal_error(
                format!("Heap lookup failed for place: [{:?}]", place),
                self.arena.tcx.mk_ty_from_kind(TyKind::Error(
                    ErrorGuaranteed::unchecked_claim_error_was_emitted(),
                )),
            ));
        }
    }

    fn encode_operand(
        &mut self,
        heap: &HeapData<'sym, 'tcx, S::SymValSynthetic>,
        operand: &mir::Operand<'tcx>,
        reborrows: &ReborrowingDag<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let place: Place<'tcx> = (*place).into();
                self.encode_place::<LookupGet>(heap, &place)
            }
            mir::Operand::Constant(c) => self.arena.mk_constant(c.into()),
        }
    }

    fn apply_unblock_actions(
        &mut self,
        actions: Vec<UnblockAction<'tcx>>,
        reborrows: &ReborrowingDag<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for action in actions {
            match action {
                UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                } => {
                    let reborrow = reborrows
                        .iter()
                        .find(|rb| {
                            rb.assigned_place == assigned_place && rb.blocked_place == blocked_place
                        })
                        .unwrap();
                    self.handle_removed_reborrow(reborrow, heap);
                }
                UnblockAction::Collapse(place, places) => {
                    self.collapse_place_from(&place.place(), &places[0].place(), heap);
                }
            }
        }
    }

    pub fn execute(&mut self) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
        let mut result_paths: BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut assertions: BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut heap_data = HeapData::new();
        let mut heap = SymbolicHeap::new(&mut heap_data, self.tcx, &self.body);
        for (idx, arg) in self.body.args_iter().enumerate() {
            let local = &self.body.local_decls[arg];
            self.symvars.push(local.ty);
            let sym_var = self.arena.mk_var(idx, local.ty);
            let place = Place::new(arg, &[]);
            add_debug_note!(
                sym_var.debug_info,
                "Symvar for arg {:?} in {:?}",
                arg,
                self.body.span
            );
            /*
             * If we're passed in a reference-typed field, store in the heap its
             * dereference. TODO: Explain why
             */
            match sym_var.ty(self.tcx).rust_ty().kind() {
                ty::TyKind::Ref(_, _, _) => {
                    heap.insert(
                        place.project_deref(self.tcx),
                        self.arena.mk_projection(ProjectionElem::Deref, sym_var),
                    );
                }
                _ => {
                    heap.insert(place, sym_var);
                }
            }
        }
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            PathConditions::new(),
            heap_data,
        )];
        while let Some(mut path) = paths.pop() {
            let block = path.last_block();
            for local in self.havoc.get(block).iter() {
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body);
                heap.insert(
                    (*local).into(),
                    self.mk_fresh_symvar(self.body.local_decls[*local].ty),
                );
            }
            let pcs_block = self.fpcs_analysis.get_all_for_bb(block);
            let block_data = &self.body.basic_blocks[block];
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                let fpcs_loc = &pcs_block.statements[stmt_idx];
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body);
                let reborrow_actions_start = fpcs_loc.extra.reborrow_actions(true);
                let g1 = self.handle_reborrow_actions(
                    reborrow_actions_start,
                    &fpcs_loc.extra.before_start, // TODO: Check
                    &fpcs_loc.state,              // TODO: Not the state at the start
                    &mut heap,
                );
                eprintln!("g1: {block:?} {stmt_idx:?} {:?}", g1);
                eprintln!("Actions: {:?}", g1.clone().actions());
                eprintln!("{:?}", fpcs_loc.extra.before_start);
                self.handle_repacks(&fpcs_loc.repacks_start, &mut heap);
                self.handle_repacks(&fpcs_loc.repacks_middle, &mut heap);
                let reborrow_actions_end = fpcs_loc.extra.reborrow_actions(false);
                let g2 = self.handle_reborrow_actions(
                    reborrow_actions_end,
                    &fpcs_loc.extra.before_after, // TODO: Check
                    &fpcs_loc.state,              // TODO: Not the state at the start
                    &mut heap,
                );
                eprintln!("g2: {:?}", g2);
                self.handle_stmt(stmt, &mut heap, fpcs_loc);
                if let Some(debug_output_dir) = &self.debug_output_dir {
                    export_path_json(
                        &debug_output_dir,
                        &path,
                        fpcs_loc,
                        stmt_idx,
                        self.fpcs_analysis.repacker(),
                    );
                }
            }
            let last_fpcs_loc = pcs_block.statements.last().unwrap();
            assert!(pcs_block.statements.len() == block_data.statements.len() + 1);
            let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body);
            self.handle_repacks(&last_fpcs_loc.repacks_start, &mut heap);
            self.handle_terminator(
                block_data.terminator(),
                &mut paths,
                &mut assertions,
                &mut result_paths,
                &mut path,
                pcs_block.terminator,
            );
            if let Some(debug_output_dir) = &self.debug_output_dir {
                export_path_json(
                    &debug_output_dir,
                    &path,
                    last_fpcs_loc,
                    block_data.statements.len(),
                    self.fpcs_analysis.repacker(),
                );
            }
        }
        if let Some(debug_output_dir) = &self.debug_output_dir {
            export_assertions(&debug_output_dir, &assertions, &self.body.var_debug_info);
            export_path_list(&debug_output_dir, &result_paths);
        }
        SymbolicExecutionResult {
            paths: result_paths,
            assertions,
            symvars: self.symvars.clone(),
        }
    }

    fn add_to_result_paths_if_feasible(
        &mut self,
        path: &Path<'sym, 'tcx, S::SymValSynthetic>,
        result_paths: &mut BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>>,
    ) {
        if let Some(expr) = path.heap.get_return_place_expr() {
            result_paths.insert((path.path.clone(), path.pcs.clone(), expr));
        }
    }

    fn havoc_refs_in_operand(
        &mut self,
        operand: &mir::Operand<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        reborrows: &ReborrowingDag<'tcx>,
    ) {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let place: Place<'tcx> = (*place).into();
                if let ty::TyKind::Ref(_, ty, Mutability::Mut) =
                    place.ty(self.body, self.tcx).ty.kind()
                {
                    heap.insert(
                        place.project_deref(self.tcx).into(),
                        self.mk_fresh_symvar(*ty),
                    );
                };
            }
            mir::Operand::Constant(_) => {}
        }
    }

    fn mk_fresh_symvar(&mut self, ty: ty::Ty<'tcx>) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        let var = self.arena.mk_var(self.symvars.len(), ty);
        self.symvars.push(ty);
        var
    }

    fn handle_repacks(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for repack in repacks {
            self.handle_repack(repack, heap)
        }
    }

    fn handle_removed_reborrow(
        &self,
        reborrow: &Reborrow<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        match reborrow.assigned_place {
            pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                let heap_value = if reborrow.mutability.is_mut() {
                    self.encode_place::<LookupTake>(heap.0, &place.deref().into())
                } else {
                    self.encode_place::<LookupGet>(heap.0, &place.deref().into())
                };
                match reborrow.blocked_place {
                    pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                        heap.insert(place.deref().into(), heap_value);
                    }
                    pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
                }
            }
            pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
        }
    }

    fn handle_reborrow_actions(
        &mut self,
        reborrow_actions: Vec<ReborrowAction<'tcx>>,
        borrows: &BorrowsState<'tcx>,
        fpcs: &CapabilitySummary<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) -> UnblockGraph<'tcx> {
        let mut unblock_graph = UnblockGraph::new();
        let mut places_to_expand = vec![];
        let mut reborrows_to_add = vec![];
        for action in reborrow_actions {
            match action {
                ReborrowAction::CollapsePlace(places, place) => {
                    unblock_graph.unblock_place(place, borrows, fpcs);
                }
                ReborrowAction::ExpandPlace(place, places) => {
                    places_to_expand.push((place, places));
                }
                ReborrowAction::AddReborrow(rb) => {
                    reborrows_to_add.push(rb);
                }
                ReborrowAction::RemoveReborrow(rb) => {
                    unblock_graph.unblock_reborrow(rb, borrows, fpcs);
                }
            }
        }

        self.apply_unblock_actions(unblock_graph.clone().actions(), &borrows.reborrows, heap);
        places_to_expand.sort_by_key(|(p, _)| p.place().projection.len());
        for (place, places) in places_to_expand {
            if place.place().projection.len() == 0 {
                // The expansion from x to *x isn't necessary!
                continue;
            }
            let value = if place
                .place()
                .projects_shared_ref(self.fpcs_analysis.repacker())
            {
                heap.0.get(&place.place().into())
            } else {
                heap.0.take(&place.place().into())
            };
            let value = value.unwrap_or_else(|| {
                self.arena.mk_internal_error(
                    format!(
                        "Place {:?} not found in heap[reborrow_expand]",
                        place.place()
                    ),
                    (*place.place()).ty(self.body, self.tcx).ty,
                )
            });

            // TODO: old places
            self.explode_value(
                &place.place(),
                value,
                places.iter().map(|p| (*p).into()),
                heap,
            );
        }

        for reborrow in reborrows_to_add {
            let blocked_value = if reborrow.mutability.is_mut() {
                self.encode_place::<LookupTake>(heap.0, &reborrow.blocked_place.place().into())
            } else {
                self.encode_place::<LookupGet>(heap.0, &reborrow.blocked_place.place().into())
            };
            heap.insert(reborrow.assigned_place.place().into(), blocked_value);
        }
        unblock_graph
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
    ) {
        let old_proj_len = place.projection.len();
        for f in places {
            assert_eq!(f.projection.len(), place.projection.len() + 1);
            let mut value = value;
            for elem in f.projection.iter().skip(old_proj_len) {
                value = self.arena.mk_projection(elem.clone(), value);
            }
            heap.insert(f.deref().into(), value)
        }
    }

    fn expand_place_with_guide(
        &self,
        place: &pcs::utils::Place<'tcx>,
        guide: &pcs::utils::Place<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        let value = match place.ty(self.fpcs_analysis.repacker()).ty.kind() {
            ty::TyKind::Ref(_, _, Mutability::Mut) => {
                // Expanding x into *x shouldn't expand sth in the heap
                return;
            }
            ty::TyKind::Ref(_, _, Mutability::Not) => heap.0.get(&place.deref().into()),
            _ => heap.0.take(&place.deref().into()),
        };
        let value = value.unwrap_or_else(|| {
            self.arena.mk_internal_error(
                format!("Place {:?} not found in heap[repack]", place),
                place.ty(self.fpcs_analysis.repacker()).ty,
            )
        });
        let (field, rest, _) = place.expand_one_level(*guide, self.fpcs_analysis.repacker());
        self.explode_value(
            place,
            value,
            std::iter::once(field).chain(rest.into_iter()),
            heap,
        );
    }

    fn collapse_place_from(
        &self,
        place: &pcs::utils::Place<'tcx>,
        from: &pcs::utils::Place<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        if place.ty(self.fpcs_analysis.repacker()).ty.is_ref() {
            return;
        }
        let place_ty = place.ty(self.fpcs_analysis.repacker());
        let args: Vec<_> = if from.is_downcast_of(*place).is_some() || place_ty.ty.is_box() {
            vec![heap.0.take(&((*from).into())).unwrap()]
        } else {
            place
                .expand_field(None, self.fpcs_analysis.repacker())
                .iter()
                .map(|p| {
                    let place_to_take = &p.deref().into();
                    heap.0.take(place_to_take).unwrap_or_else(|| {
                        self.arena.mk_internal_error(
                            format!("Place {:?} not found in heap[collapse]", place_to_take),
                            place_to_take.ty(&self.body, self.tcx).ty,
                        )
                    })
                })
                .collect()
        };
        heap.insert(
            place.deref().into(),
            self.arena.mk_aggregate(
                AggregateKind::pcs(
                    place_ty.ty,
                    from.ty(self.fpcs_analysis.repacker()).variant_index,
                ),
                self.arena.alloc_slice(&args),
            ),
        );
    }

    fn handle_repack(
        &self,
        repack: &RepackOp<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        match repack {
            RepackOp::StorageDead(_) => todo!(),
            RepackOp::IgnoreStorageDead(_) => {}
            RepackOp::Weaken(_, _, _) => {}
            RepackOp::Expand(place, guide, _) => self.expand_place_with_guide(place, guide, heap),
            RepackOp::Collapse(place, from, _) => self.collapse_place_from(place, from, heap),
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
    mir: &'mir Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    verifier_semantics: S,
    arena: &'sym SymExContext<'tcx>,
    debug_output_dir: Option<&str>,
) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
    SymbolicExecution::new(
        tcx,
        mir,
        fpcs_analysis,
        verifier_semantics,
        arena,
        debug_output_dir.map(|s| s.to_string()),
    )
    .execute()
}
