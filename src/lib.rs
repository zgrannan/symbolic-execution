#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(associated_type_bounds)]

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
pub mod value;

use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt},
    },
};
use context::SymExContext;
use havoc::HavocData;
use heap::SymbolicHeap;
use pcs::{
    borrows::engine::BorrowsDomain, free_pcs::{FreePcsLocation, RepackOp}, FpcsOutput
};
use results::{ResultAssertion, ResultPath, SymbolicExecutionResult};
use semantics::VerifierSemantics;
use std::{collections::BTreeSet, ops::Deref};

use self::{
    path::{AcyclicPath, Path},
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    place::Place,
    value::{AggregateKind, SymValue},
};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Assertion<'sym, 'tcx, T> {
    Eq(SymValue<'sym, 'tcx, T>, bool),
    Precondition(DefId, GenericArgsRef<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
}
pub struct SymbolicExecution<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    havoc: HavocData,
    symvars: Vec<ty::Ty<'tcx>>,
    arena: &'sym SymExContext,
    verifier_semantics: S,
    debug: bool,
}

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        fpcs_analysis: FpcsOutput<'mir, 'tcx>,
        verifier_semantics: S,
        arena: &'sym SymExContext,
    ) -> Self {
        SymbolicExecution {
            tcx,
            body,
            fpcs_analysis,
            havoc: HavocData::new(&body),
            symvars: Vec::with_capacity(body.arg_count),
            verifier_semantics,
            arena,
            debug: std::env::var("SYM_EX_DEBUG").map_or(false, |v| v == "true"),
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
                            path.heap.encode_operand(self.arena, discr, &loc.extra),
                            pred.clone(),
                        ));
                        paths.push(path);
                    }
                }
                if let Some(mut path) = path.push_if_acyclic(targets.otherwise()) {
                    let pred =
                        PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty);
                    path.pcs.insert(PathConditionAtom::new(
                        path.heap.encode_operand(self.arena, discr, &loc.extra),
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
                let cond = path.heap.encode_operand(self.arena, cond, &loc.extra);
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
                    let args: Vec<_> = args
                        .iter()
                        .map(|arg| path.heap.encode_operand(self.arena, arg, &loc.extra))
                        .collect();

                    let args: &'sym [SymValue<'sym, 'tcx, S::SymValSynthetic>] =
                        self.alloc_slice(&args);

                    assertions.insert((
                        path.path.clone(),
                        path.pcs.clone(),
                        Assertion::Precondition(*def_id, substs, args),
                    ));

                    let result = self
                        .verifier_semantics
                        .encode_fn_call(self.arena, *def_id, substs, args)
                        .unwrap_or_else(|| {
                            let sym_var = self.mk_fresh_symvar(
                                destination.ty(&self.body.local_decls, self.tcx).ty,
                            );
                            add_debug_note!(
                                sym_var.debug_info,
                                "Fresh symvar for call to {:?}",
                                def_id
                            );
                            sym_var
                        });
                    path.heap.insert((*destination).into(), result);
                    path.pcs.insert(PathConditionAtom::new(
                        result,
                        PathConditionPredicate::Postcondition(*def_id, substs, args),
                    ));
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

    pub fn execute(&mut self) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
        let mut result_paths: BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut assertions: BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut init_heap = SymbolicHeap::new();
        let fn_name = &format!("{}", self.tcx.item_name(self.body.source.def_id()));
        for (idx, arg) in self.body.args_iter().enumerate() {
            let local = &self.body.local_decls[arg];
            let arg_ty = local.ty;
            self.symvars.push(arg_ty);
            let place = Place::new(arg, Vec::new());
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
                path.heap.insert(
                    (*local).into(),
                    self.mk_fresh_symvar(self.body.local_decls[*local].ty),
                );
            }
            let pcs_block = self.fpcs_analysis.get_all_for_bb(block);
            let block_data = &self.body.basic_blocks[block];
            if self.debug {
                export_path_json(fn_name, &path, 0, &self.body.var_debug_info);
            }
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                if self.debug {
                    export_path_json(fn_name, &path, stmt_idx + 1, &self.body.var_debug_info);
                }
                let fpcs_loc = &pcs_block.statements[stmt_idx];
                self.handle_repacks(&fpcs_loc.repacks_start, &mut path.heap);
                self.handle_stmt(stmt, &mut path.heap, fpcs_loc);
            }
            let last_fpcs_loc = pcs_block.statements.last().unwrap();
            self.handle_repacks(&last_fpcs_loc.repacks_start, &mut path.heap);
            if let Some(terminator) = &block_data.terminator {
                self.handle_terminator(
                    terminator,
                    &mut paths,
                    &mut assertions,
                    &mut result_paths,
                    &mut path,
                    last_fpcs_loc,
                );
            } else {
                self.add_to_result_paths_if_feasible(&path, &mut result_paths);
            }
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

    fn handle_stmt(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &mut SymbolicHeap<'sym, 'tcx, S::SymValSynthetic>,
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
                        .mk_discriminant(heap.get(&(*target).into()).unwrap()),
                    mir::Rvalue::Ref(_, _, target_place) => self.arena.mk_ref(
                        place.ty(&self.body.local_decls, self.tcx).ty,
                        heap.get(&(*target_place).into()).unwrap_or_else(|| {
                            panic!(
                                "{:?} in {:?} at {:?}",
                                target_place, self.body.span, stmt.source_info
                            )
                        }),
                    ),
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
            mir::StatementKind::StorageDead(_)
            | mir::StatementKind::StorageLive(_)
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
        heap: &mut SymbolicHeap<'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for repack in repacks {
            self.handle_repack(repack, heap)
        }
    }

    fn alloc<T>(&self, t: T) -> &'sym T {
        self.arena.alloc(t)
    }
    fn alloc_slice<T: Copy>(&self, t: &[T]) -> &'sym [T] {
        self.arena.alloc_slice(t)
    }

    fn handle_repack(
        &self,
        repack: &RepackOp<'tcx>,
        heap: &mut SymbolicHeap<'sym, 'tcx, S::SymValSynthetic>,
    ) {
        match repack {
            RepackOp::StorageDead(_) => todo!(),
            RepackOp::IgnoreStorageDead(_) => todo!(),
            RepackOp::Weaken(_, _, _) => todo!(),
            RepackOp::Expand(place, guide, _) => {
                let value = heap.take(&place.deref().into());
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
                let places: Vec<_> = place
                    .expand_field(None, self.fpcs_analysis.repacker())
                    .iter()
                    .map(|p| heap.take(&p.deref().into()))
                    .collect();

                let place_ty = place.ty(self.fpcs_analysis.repacker());
                heap.insert(
                    place.deref().into(),
                    self.arena.mk_aggregate(
                        AggregateKind::pcs(
                            place_ty.ty,
                            from.ty(self.fpcs_analysis.repacker()).variant_index,
                        ),
                        self.arena.alloc_slice(&places),
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
    arena: &'sym SymExContext,
) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
    SymbolicExecution::new(tcx, mir, fpcs_analysis, verifier_semantics, arena).execute()
}

fn export_path_json<'sym, 'tcx, T: VisFormat>(
    fn_name: &str,
    path: &Path<'sym, 'tcx, T>,
    instruction_index: usize,
    debug_info: &[VarDebugInfo],
) {
    let path_component = path
        .path
        .blocks()
        .iter()
        .map(|block| format!("{:?}", block))
        .collect::<Vec<_>>()
        .join("_");
    let data_dir = std::env::var("PCS_VIS_DATA_DIR").expect("PCS_VIS_DATA_DIR not set");
    let fn_dir = format!("{}/{}", data_dir, fn_name);
    std::fs::create_dir_all(&fn_dir).expect("Unable to create directory");
    let filename = format!(
        "{}/path_{}_stmt_{}.json",
        fn_dir, path_component, instruction_index
    );
    let heap_json = path.heap.to_json(debug_info);
    std::fs::write(filename, serde_json::to_string_pretty(&heap_json).unwrap())
        .expect("Unable to write file");
}

pub trait VisFormat {
    fn to_vis_string(&self, debug_info: &[VarDebugInfo]) -> String;
}
