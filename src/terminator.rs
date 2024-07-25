use std::collections::BTreeSet;

use pcs::borrows::engine::{BorrowsDomain, ReborrowAction};
use pcs::borrows::reborrowing_dag::ReborrowingDag;
use pcs::free_pcs::{FreePcsLocation, FreePcsTerminator};
use pcs::ReborrowBridge;

use crate::context::ErrorLocation;
use crate::heap::SymbolicHeap;
use crate::path::Path;
use crate::path_conditions::{PathConditionAtom, PathConditionPredicate};
use crate::pcs_interaction::PcsLocation;
use crate::results::{ResultAssertion, ResultPath};
use crate::value::SymValue;
use crate::visualization::{export_path_json, StepType};
use crate::{add_debug_note, Assertion};
use crate::{semantics::VerifierSemantics, visualization::VisFormat, SymbolicExecution};

use crate::rustc_interface::middle::{
    mir::{self, Location},
    ty,
};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn handle_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        paths: &mut Vec<Path<'sym, 'tcx, S::SymValSynthetic>>,
        assertions: &mut BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>>,
        result_paths: &mut BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>>,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        fpcs_terminator: FreePcsTerminator<'tcx, BorrowsDomain<'mir, 'tcx>, ReborrowBridge<'tcx>>,
        location: &PcsLocation<'mir, 'tcx>,
    ) {
        //For havocing data behind references in fn calls, we use the
        //reborrow state before the terminator action has been applied
        //to PC
        let reborrows = location.extra.before_start.reborrows();
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body);
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
                let old_path = path.path.clone();
                if let Some(mut path) = path.push_if_acyclic(*target) {
                    self.set_error_context(
                        old_path.clone(),
                        ErrorLocation::TerminatorStart(*target),
                    );
                    self.handle_pcs(
                        &mut path,
                        &fpcs_terminator.succs[0],
                        true,
                        location.location,
                    );
                    self.set_error_context(old_path, ErrorLocation::TerminatorMid(*target));
                    self.handle_pcs(
                        &mut path,
                        &fpcs_terminator.succs[0],
                        false,
                        location.location,
                    );
                    if let Some(debug_output_dir) = &self.debug_output_dir {
                        export_path_json(
                            &debug_output_dir,
                            &path,
                            &fpcs_terminator.succs[0],
                            StepType::Transition,
                            self.fpcs_analysis.repacker(),
                        );
                    }
                    paths.push(path);
                }
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let ty = discr.ty(&self.body.local_decls, self.tcx);
                for ((value, target), loc) in targets.iter().zip(fpcs_terminator.succs.iter()) {
                    let pred = PathConditionPredicate::Eq(value, ty);
                    if let Some(mut path) = path.push_if_acyclic(target) {
                        path.pcs.insert(PathConditionAtom::new(
                            self.encode_operand(&path.heap, discr),
                            pred.clone(),
                        ));
                        paths.push(path);
                    }
                }
                if let Some(mut path) = path.push_if_acyclic(targets.otherwise()) {
                    let pred =
                        PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty);
                    path.pcs.insert(PathConditionAtom::new(
                        self.encode_operand(&path.heap, discr),
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
                let cond = self.encode_operand(&path.heap, cond);
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
                        .map(|arg| self.encode_operand(heap.0, arg))
                        .collect();

                    let encoded_args: &'sym [SymValue<'sym, 'tcx, S::SymValSynthetic>] =
                        self.alloc_slice(&encoded_args);

                    let fn_name = &self.tcx.def_path_str(*def_id);

                    if fn_name == "core::panicking::panic" {
                        assertions.insert((path.path.clone(), path.pcs.clone(), Assertion::False));
                        return;
                    } else {
                        assertions.insert((
                            path.path.clone(),
                            path.pcs.clone(),
                            Assertion::Precondition(*def_id, substs, encoded_args),
                        ));
                    }

                    for arg in args {
                        self.havoc_refs_in_operand(arg, &mut heap, reborrows);
                    }

                    let result = if fn_name == "std::intrinsics::discriminant_value" {
                        self.arena.mk_discriminant(
                            self.arena
                                .mk_projection(mir::ProjectionElem::Deref, encoded_args[0]),
                        )
                    } else {
                        path.function_call_snapshots
                            .add_snapshot(location.location, encoded_args);
                        self.verifier_semantics
                            .encode_fn_call(self.arena, *def_id, substs, encoded_args)
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
                            })
                    };
                    heap.insert(*destination, result, location.location);
                    path.pcs.insert(PathConditionAtom::new(
                        result,
                        PathConditionPredicate::Postcondition(*def_id, substs, encoded_args),
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
        match terminator.kind {
            mir::TerminatorKind::Return => {
                self.add_to_result_paths(path, location, result_paths);
            }
            _ => {}
        }
    }
}
