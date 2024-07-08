#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(associated_type_bounds)]
#![feature(let_chains)]

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
        domain::ReborrowingDag,
        engine::{BorrowAction, BorrowsDomain, ReborrowAction},
    },
    free_pcs::{FreePcsLocation, RepackOp},
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

    fn heap_lookup_error(&self, message: String) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        self.arena.mk_internal_error(
            message,
            self.arena.tcx.mk_ty_from_kind(TyKind::Error(
                ErrorGuaranteed::unchecked_claim_error_was_emitted(),
            )),
        )
    }

    /// Encodes the symbolic value that the place currently holds. In the most
    /// simple cases, this is simply a heap lookup. For projections from shared
    /// references, the projection after the deref is encoded into the symval
    /// When derefing mutable references, the source of the underlying data is
    /// identified via the reborrowing dag
    fn encode_place(
        &mut self,
        heap: &HeapData<'sym, 'tcx, S::SymValSynthetic>,
        place: &Place<'tcx>,
        reborrows: &ReborrowingDag<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        let deref_of_place = place.project_deref(self.tcx);
        let value = if let Some((target, Mutability::Mut)) = reborrows.get_source(place.0) {
            match target {
                pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                    self.encode_place(heap, &Place(place), reborrows)
                }
                pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
            }
        } else if let Some((target, Mutability::Mut)) = reborrows.get_source(deref_of_place.0) {
            match target {
                pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                    let base = self.encode_place(heap, &Place(place), reborrows);
                    self.arena.mk_ref(base, Mutability::Mut)
                }
                pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
            }
        } else {
            let mut idx = 0;
            for (place, projection) in place.0.iter_projections() {
                if matches!(projection, ProjectionElem::Deref) {
                    let ty = place.ty(&self.body.local_decls, self.tcx).ty;
                    if ty.is_box() {
                        idx += 1;
                        continue;
                    }
                    match place.ty(&self.body.local_decls, self.tcx).ty.kind() {
                        ty::TyKind::Ref(_, _, Mutability::Mut) => {
                            // For mutable references, the dereference should be
                            // a key in the heap, but for immutable references,
                            // the place is encoded as a "reference to" a
                            // symbolic value
                            idx += 1;
                        }
                        _ => {}
                    }
                    break;
                }
                idx += 1;
            }
            let (projection_to_lookup, projection_to_encode) = place.projection().split_at(idx);
            let place_to_lookup = Place::new(place.local(), projection_to_lookup);
            let mut v = heap.get(&place_to_lookup).unwrap_or_else(|| {
                self.heap_lookup_error(format!(
                    "Heap lookup failed for place: {:?} when encoding place {place:?}",
                    place_to_lookup
                ))
            });

            for proj in projection_to_encode {
                v = self.arena.mk_projection(proj.clone(), v);
            }
            v
        };
        // assert_eq!(
        //     self.tcx.erase_regions(value.ty(self.tcx).rust_ty()),
        //     self.tcx.erase_regions(place.ty(&self.body, self.tcx).ty)
        // );
        value
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
                self.encode_place(heap, &place, reborrows)
            }
            mir::Operand::Constant(c) => self.arena.mk_constant(c.into()),
        }
    }

    pub fn execute(&mut self) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
        let mut result_paths: BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut assertions: BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut init_heap = HeapData::new();
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
            SymbolicHeap::new(&mut init_heap, self.tcx, &self.body).insert(place, sym_var);
        }
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            PathConditions::new(),
            init_heap,
        )];
        while let Some(mut path) = paths.pop() {
            eprintln!("Check path: {:?}", path);
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
                self.handle_repacks(&fpcs_loc.repacks_start, &mut heap);
                self.handle_repacks(&fpcs_loc.repacks_middle, &mut heap);
                self.handle_reborrow_actions(fpcs_loc.extra.reborrow_actions(true), &mut heap);
                self.handle_reborrow_actions(fpcs_loc.extra.reborrow_actions(false), &mut heap);
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
            let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body);
            self.handle_repacks(&last_fpcs_loc.repacks_start, &mut heap);
            self.handle_terminator(
                block_data.terminator(),
                &mut paths,
                &mut assertions,
                &mut result_paths,
                &mut path,
                last_fpcs_loc,
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
                if let Some((target, Mutability::Mut)) =
                    reborrows.get_source(place.project_deref(self.tcx).0)
                {
                    match target {
                        pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                            heap.insert(
                                place.deref().into(),
                                self.mk_fresh_symvar((*place).ty(self.body, self.tcx).ty),
                            );
                        }
                        pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => {}
                    }
                }
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

    fn handle_reborrow_actions(
        &self,
        reborrow_actions: Vec<ReborrowAction<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for action in reborrow_actions.iter().rev() {
            eprintln!("{:?}", action);
            match action {
                ReborrowAction::RemoveReborrow(reborrow) => match reborrow.assigned_place {
                    pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                        if let Some(value) = heap.0.take(&place.deref().into()) {
                            match reborrow.blocked_place {
                                pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                                    heap.insert(place.deref().into(), value);
                                }
                                pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
                            }
                        }
                    }
                    pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
                },
                _ => {}
            }
        }
    }

    fn alloc_slice<T: Copy>(&self, t: &[T]) -> &'sym [T] {
        self.arena.alloc_slice(t)
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
            RepackOp::Expand(place, guide, _) => {
                if place.ty(self.fpcs_analysis.repacker()).ty.is_ref() {
                    return;
                }
                let value = heap.0.take(&place.deref().into()).unwrap_or_else(|| {
                    self.arena.mk_internal_error(
                        format!("Place {:?} not found in heap[repack]", place),
                        place.ty(self.fpcs_analysis.repacker()).ty,
                    )
                });
                let old_proj_len = place.projection.len();
                let (field, rest, _) =
                    place.expand_one_level(*guide, self.fpcs_analysis.repacker());
                for f in std::iter::once(&field).chain(rest.iter()) {
                    let mut value = value;
                    for elem in f.projection.iter().skip(old_proj_len) {
                        value = self.arena.mk_projection(elem.clone(), value);
                    }
                    heap.insert(f.deref().into(), value)
                }
            }
            RepackOp::Collapse(place, from, _) => {
                if place.ty(self.fpcs_analysis.repacker()).ty.is_ref() {
                    return;
                }
                let place_ty = place.ty(self.fpcs_analysis.repacker());
                let args: Vec<_> = if from.is_downcast_of(*place).is_some() || place_ty.ty.is_box()
                {
                    vec![heap.0.take(&((*from).into())).unwrap()]
                } else {
                    place
                        .expand_field(None, self.fpcs_analysis.repacker())
                        .iter()
                        .map(|p| {
                            let place_to_take = &p.deref().into();
                            heap.0.take(place_to_take).unwrap_or_else(|| {
                                self.arena.mk_internal_error(
                                    format!(
                                        "Place {:?} not found in heap[collapse]",
                                        place_to_take
                                    ),
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
