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
pub mod transform;
pub mod value;
pub mod visualization;

use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt},
    },
};
use context::SymExContext;
use havoc::HavocData;
use heap::{HeapWrapper, SymbolicHeap};
use pcs::{
    borrows::engine::{BorrowAction, BorrowsDomain},
    free_pcs::{FreePcsLocation, RepackOp},
    FpcsOutput,
};
use results::{ResultAssertion, ResultPath, SymbolicExecutionResult};
use semantics::VerifierSemantics;
use std::{collections::BTreeSet, ops::Deref};
use value::SymValueKind;
use visualization::{export_path_json, export_path_list, VisFormat};

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

    fn handle_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        paths: &mut Vec<Path<'sym, 'tcx, S::SymValSynthetic>>,
        assertions: &mut BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>>,
        result_paths: &mut BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>>,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        loc: &FreePcsLocation<'tcx, BorrowsDomain<'tcx>>,
    ) {
        let mut heap = HeapWrapper::new(&mut path.heap, self.tcx, &self.body);
        match &terminator.kind {
            mir::TerminatorKind::Drop { target, .. }
            | mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | mir::TerminatorKind::Goto { target } => {
                if let Some(path) = path.push_if_acyclic(*target) {
                    paths.push(path);
                }
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let ty = discr.ty(&self.body.local_decls, self.tcx);
                for (value, target) in targets.iter() {
                    let pred = PathConditionPredicate::Eq(value, ty);
                    if let Some(mut path) = path.push_if_acyclic(target) {
                        path.pcs.insert(PathConditionAtom::new(
                            HeapWrapper::new(&mut path.heap, self.tcx, &self.body)
                                .encode_operand(self.arena, discr, &loc.extra),
                            pred.clone(),
                        ));
                        paths.push(path);
                    }
                }
                if let Some(mut path) = path.push_if_acyclic(targets.otherwise()) {
                    let pred =
                        PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty);
                    path.pcs.insert(PathConditionAtom::new(
                        HeapWrapper::new(&mut path.heap, self.tcx, &self.body)
                            .encode_operand(self.arena, discr, &loc.extra),
                        pred.clone(),
                    ));
                    paths.push(path);
                }
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let cond = heap.encode_operand(self.arena, cond, &loc.extra);
                assertions.insert((
                    path.path.clone(),
                    path.pcs.clone(),
                    Assertion::Eq(cond, *expected),
                ));
                if let Some(path) = path.push_if_acyclic(*target) {
                    paths.push(path);
                }
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => match func.ty(&self.body.local_decls, self.tcx).kind() {
                ty::TyKind::FnDef(def_id, substs) => {
                    let encoded_args: Vec<_> = args
                        .iter()
                        .map(|arg| heap.encode_operand(self.arena, arg, &loc.extra))
                        .collect();

                    let encoded_args: &'sym [SymValue<'sym, 'tcx, S::SymValSynthetic>] =
                        self.alloc_slice(&encoded_args);

                    let fn_name = &self.tcx.def_path_str(*def_id);

                    if fn_name == "core::panicking::panic" {
                        assertions.insert((
                            path.path.clone(),
                            path.pcs.clone(),
                            Assertion::False
                        ));
                        return
                    } else {
                        assertions.insert((
                            path.path.clone(),
                            path.pcs.clone(),
                            Assertion::Precondition(*def_id, substs, encoded_args),
                        ));
                    }

                    for arg in args {
                        self.havoc_refs_in_operand(arg, &mut heap);
                    }

                    let result = if fn_name == "std::intrinsics::discriminant_value" {
                        self.arena.mk_discriminant(
                            self.arena
                                .mk_projection(mir::ProjectionElem::Deref, encoded_args[0]),
                        )
                    } else {
                        self.verifier_semantics
                            .encode_fn_call(self.arena, *def_id, substs, encoded_args)
                            .unwrap_or_else(|| {
                                let sym_var = self.mk_fresh_symvar(
                                    destination.ty(&self.body.local_decls, self.tcx).ty,
                                );
                                eprintln!(
                                    "Making fresh symvar {:?} for call to {:?} at {:?}",
                                    sym_var, def_id, loc.location
                                );
                                add_debug_note!(
                                    sym_var.debug_info,
                                    "Fresh symvar for call to {:?}",
                                    def_id
                                );
                                sym_var
                            })
                    };
                    heap.insert((*destination).into(), result);
                    path.pcs.insert(PathConditionAtom::new(
                        result,
                        PathConditionPredicate::Postcondition(*def_id, substs, encoded_args),
                    ));
                    self.handle_borrow_actions(loc.extra.actions(true), &mut heap);
                    self.handle_borrow_actions(loc.extra.actions(false), &mut heap);
                    if let Some(target) = target {
                        if let Some(path) = path.push_if_acyclic(*target) {
                            paths.push(path);
                        }
                    }
                }
                _ => panic!(),
            },
            mir::TerminatorKind::Unreachable | mir::TerminatorKind::Return { .. } => {}
            other => {
                todo!("other terminator {:#?}", other)
            }
        }
        if terminator.successors().next().is_none() {
            self.add_to_result_paths_if_feasible(&path, result_paths);
        }
    }

    fn handle_borrow_actions<'a>(
        &self,
        actions: Vec<BorrowAction<'a, 'tcx>>,
        heap: &mut HeapWrapper<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for action in actions {
            if let BorrowAction::RemoveBorrow(borrow) = action && borrow.is_mut {
                let place_to_remove = &borrow.assigned_place.place().into();
                let reference = heap.0.take(place_to_remove).unwrap_or_else(|| {
                    self.arena.mk_internal_error(
                        format!("Place {:?} not found in heap", place_to_remove),
                        place_to_remove.ty(&self.body, self.tcx).ty,
                    )
                });
                let val = match &reference.kind {
                    SymValueKind::Ref(_, val) => val,
                    SymValueKind::Aggregate(_, vec) => vec[0],
                    SymValueKind::InternalError(_, _) => todo!(),
                    SymValueKind::Var(_, _) => todo!(),
                    SymValueKind::Constant(_) => todo!(),
                    SymValueKind::CheckedBinaryOp(_, _, _, _) => todo!(),
                    SymValueKind::BinaryOp(_, _, _, _) => todo!(),
                    SymValueKind::UnaryOp(_, _, _) => todo!(),
                    SymValueKind::Projection(_, _) => todo!(),
                    SymValueKind::Discriminant(_) => todo!(),
                    SymValueKind::Cast(_, _, _) => todo!(),
                    SymValueKind::Synthetic(_) => todo!(),
                };
                heap.insert(borrow.borrowed_place.place().into(), val)
            }
        }
    }

    pub fn execute(&mut self) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
        let mut result_paths: BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut assertions: BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut init_heap = SymbolicHeap::new();
        for (idx, arg) in self.body.args_iter().enumerate() {
            let local = &self.body.local_decls[arg];
            let arg_ty = local.ty;
            self.symvars.push(arg_ty);
            let place = Place::new(arg, &[]);
            let sym_var = self.arena.mk_var(idx, arg_ty);
            add_debug_note!(
                sym_var.debug_info,
                "Symvar for arg {:?} in {:?}",
                arg,
                self.body.span
            );
            init_heap.insert(place, sym_var);
        }
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            PathConditions::new(),
            init_heap,
        )];
        while let Some(mut path) = paths.pop() {
            let block = path.last_block();
            for local in self.havoc.get(block).iter() {
                let mut heap = HeapWrapper::new(&mut path.heap, self.tcx, &self.body);
                heap.insert(
                    (*local).into(),
                    self.mk_fresh_symvar(self.body.local_decls[*local].ty),
                );
            }
            let pcs_block = self.fpcs_analysis.get_all_for_bb(block);
            let block_data = &self.body.basic_blocks[block];
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                let fpcs_loc = &pcs_block.statements[stmt_idx];
                let mut heap = HeapWrapper::new(&mut path.heap, self.tcx, &self.body);
                self.handle_repacks(&fpcs_loc.repacks_start, &mut heap);
                self.handle_repacks(&fpcs_loc.repacks_middle, &mut heap);
                self.handle_borrow_actions(fpcs_loc.extra.actions(true), &mut heap);
                self.handle_borrow_actions(fpcs_loc.extra.actions(false), &mut heap);
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
            let mut heap = HeapWrapper::new(&mut path.heap, self.tcx, &self.body);
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
        heap: &mut HeapWrapper<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let place_ty = place.ty(&self.body.local_decls, self.tcx).ty;
                if let ty::TyKind::Ref(_, ty, mutbl) = place_ty.kind() && mutbl.is_mut()
                {
                    eprintln!("Havocing {:?}", place);
                    heap.insert(
                        (*place).into(),
                        self.arena.mk_ref(place_ty, self.mk_fresh_symvar(*ty)),
                    );
                }
            }
            mir::Operand::Constant(_) => {}
        }
    }

    fn handle_stmt(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &mut HeapWrapper<'_, 'sym, 'tcx, S::SymValSynthetic>,
        pcs: &FreePcsLocation<'tcx, BorrowsDomain<'tcx>>,
    ) {
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                let sym_value = match rvalue {
                    mir::Rvalue::Use(operand) => {
                        heap.encode_operand(self.arena, &operand, &pcs.extra)
                    }
                    mir::Rvalue::CheckedBinaryOp(op, box (lhs, rhs)) => {
                        let lhs = heap.encode_operand(self.arena, &lhs, &pcs.extra);
                        let rhs = heap.encode_operand(self.arena, &rhs, &pcs.extra);
                        self.arena.mk_checked_bin_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            lhs,
                            rhs,
                        )
                    }
                    mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                        let lhs = heap.encode_operand(self.arena, &lhs, &pcs.extra);
                        let rhs = heap.encode_operand(self.arena, &rhs, &pcs.extra);
                        self.arena.mk_bin_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            lhs,
                            rhs,
                        )
                    }
                    mir::Rvalue::Aggregate(kind, ops) => {
                        let ops = ops
                            .iter()
                            .map(|op| heap.encode_operand(self.arena, op, &pcs.extra))
                            .collect::<Vec<_>>();
                        self.arena.mk_aggregate(
                            AggregateKind::rust(
                                *kind.clone(),
                                place.ty(&self.body.local_decls, self.tcx).ty,
                            ),
                            self.alloc_slice(&ops),
                        )
                    }
                    mir::Rvalue::Discriminant(target) => self
                        .arena
                        .mk_discriminant(heap.0.get(&(*target).into()).unwrap()),
                    mir::Rvalue::Ref(_, _, target_place) => {
                        let referred_value = heap.0.get(&(*target_place).into());
                        if let Some(value) = referred_value {
                            self.arena
                                .mk_ref(place.ty(&self.body.local_decls, self.tcx).ty, value)
                        } else {
                            self.arena.mk_internal_error(
                                format!("No value for {:?} in heap", target_place),
                                place.ty(&self.body.local_decls, self.tcx).ty,
                            )
                        }
                    }
                    mir::Rvalue::UnaryOp(op, operand) => {
                        let operand = heap.encode_operand(self.arena, operand, &pcs.extra);
                        self.arena.mk_unary_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            operand,
                        )
                    }
                    mir::Rvalue::Cast(kind, operand, ty) => {
                        let operand = heap.encode_operand(self.arena, operand, &pcs.extra);
                        self.arena.mk_cast((*kind).into(), operand, *ty)
                    }
                    _ => todo!("{rvalue:?}"),
                };
                heap.insert((*place).into(), sym_value);
            }
            mir::StatementKind::StorageDead(local) => {
                heap.0.remove(&Place::new(*local, &[]));
            }
            mir::StatementKind::StorageLive(_)
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..) => {}
            other => todo!("{:?}", other),
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
        heap: &mut HeapWrapper<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for repack in repacks {
            self.handle_repack(repack, heap)
        }
    }

    fn alloc_slice<T: Copy>(&self, t: &[T]) -> &'sym [T] {
        self.arena.alloc_slice(t)
    }

    fn handle_repack(
        &self,
        repack: &RepackOp<'tcx>,
        heap: &mut HeapWrapper<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        match repack {
            RepackOp::StorageDead(_) => todo!(),
            RepackOp::IgnoreStorageDead(_) => {}
            RepackOp::Weaken(_, _, _) => {}
            RepackOp::Expand(place, guide, _) => {
                let value = heap.0.take(&place.deref().into()).unwrap_or_else(|| {
                    self.arena.mk_internal_error(
                        format!("Place {:?} not found in heap", place),
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
                                    format!("Place {:?} not found in heap", place_to_take),
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
