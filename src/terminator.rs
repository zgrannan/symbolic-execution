use std::collections::BTreeSet;

use pcs::borrows::engine::{BorrowsDomain, ReborrowAction};
use pcs::borrows::reborrowing_dag::ReborrowingDag;
use pcs::free_pcs::{FreePcsLocation, FreePcsTerminator};
use pcs::ReborrowBridge;

use crate::context::ErrorLocation;
use crate::function_call_snapshot::FunctionCallSnapshot;
use crate::heap::{HeapData, SymbolicHeap};
use crate::path::Path;
use crate::path_conditions::{PathConditionAtom, PathConditionPredicate};
use crate::pcs_interaction::PcsLocation;
use crate::results::{ResultAssertion, ResultPath, ResultPaths};
use crate::value::SymValue;
use crate::visualization::{export_path_json, StepType};
use crate::{add_debug_note, Assertion};
use crate::{semantics::VerifierSemantics, visualization::VisFormat, SymbolicExecution};

use crate::rustc_interface::hir::def_id::DefId;
use crate::rustc_interface::middle::{
    mir::{self, Location, Operand},
    ty::{self, GenericArgsRef},
};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn handle_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        paths: &mut Vec<Path<'sym, 'tcx, S::SymValSynthetic>>,
        assertions: &mut BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>>,
        result_paths: &mut ResultPaths<'sym, 'tcx, S::SymValSynthetic>,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        fpcs_terminator: FreePcsTerminator<'tcx, BorrowsDomain<'mir, 'tcx>, ReborrowBridge<'tcx>>,
        location: &PcsLocation<'mir, 'tcx>,
    ) {
        //For havocing data behind references in fn calls, we use the
        //reborrow state before the terminator action has been applied
        //to PC
        let reborrows = location.extra.before_start.reborrows();
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
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
                            self.encode_operand(&mut path.heap, discr),
                            pred.clone(),
                        ));
                        paths.push(path);
                    }
                }
                if let Some(mut path) = path.push_if_acyclic(targets.otherwise()) {
                    let pred =
                        PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty);
                    path.pcs.insert(PathConditionAtom::new(
                        self.encode_operand(&mut path.heap, discr),
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
                let cond = self.encode_operand(&mut path.heap, cond);
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
                    let effects = self.get_function_call_effects(
                        *def_id,
                        substs,
                        &mut heap,
                        args,
                        location.location,
                    );

                    if let Some(assertion) = effects.precondition_assertion {
                        assertions.insert((path.path.clone(), path.pcs.clone(), assertion));
                    }

                    match effects.result {
                        FunctionCallResult::Value {
                            value,
                            postcondition,
                        } => {
                            heap.insert(*destination, value, location.location);
                            if let Some(postcondition) = postcondition {
                                path.pcs
                                    .insert(PathConditionAtom::new(value, postcondition));
                            }
                        }
                        FunctionCallResult::Unknown { postcondition } => {
                            if let Some(snapshot) = effects.snapshot {
                                path.function_call_snapshots
                                    .add_snapshot(location.location, snapshot.args);
                            }
                            eprintln!("Fresh symvar for call to {:?}", def_id);
                            let sym_var = self.mk_fresh_symvar(
                                destination.ty(&self.body.local_decls, self.tcx).ty,
                            );
                            add_debug_note!(
                                sym_var.debug_info,
                                "Fresh symvar for call to {:?}",
                                def_id
                            );
                            heap.insert(*destination, sym_var, location.location);
                            path.pcs
                                .insert(PathConditionAtom::new(sym_var, postcondition));
                        }
                        FunctionCallResult::Never => {}
                    };
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

    fn get_function_call_effects(
        &mut self,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        args: &Vec<Operand<'tcx>>,
        location: Location,
    ) -> FunctionCallEffects<'sym, 'tcx, S::SymValSynthetic> {
        if let Some(result) = S::encode_fn_call(location, self, def_id, substs, heap.0, args) {
            return result;
        }
        let function_type = FunctionType::new(self.tcx, def_id);
        let encoded_args: Vec<_> = args
            .iter()
            .map(|arg| self.encode_operand(heap.0, arg))
            .collect();
        let encoded_args: &'sym [SymValue<'sym, 'tcx, S::SymValSynthetic>] =
            self.alloc_slice(&encoded_args);
        let precondition_assertion = match function_type {
            FunctionType::DiscriminantValue => None,
            FunctionType::Panic => Some(Assertion::False),
            FunctionType::RustFunction(_) => {
                Some(Assertion::Precondition(def_id, substs, encoded_args))
            }
        };

        let result = match function_type {
            FunctionType::DiscriminantValue => {
                let value = self.arena.mk_discriminant(
                    self.arena
                        .mk_projection(mir::ProjectionElem::Deref, encoded_args[0]),
                );
                FunctionCallResult::Value {
                    value,
                    postcondition: None,
                }
            }
            FunctionType::Panic => FunctionCallResult::Never,
            FunctionType::RustFunction(_) => {
                let postcondition_args = args
                    .iter()
                    .zip(encoded_args)
                    .map(|(operand, encoded)| {
                        self.havoc_operand_ref(operand, heap, location)
                            .unwrap_or(encoded)
                    })
                    .collect::<Vec<_>>();
                FunctionCallResult::Unknown {
                    postcondition: PathConditionPredicate::Postcondition {
                        def_id,
                        substs,
                        pre_values: self.alloc_slice(&encoded_args),
                        post_values: self.alloc_slice(&postcondition_args),
                    },
                }
            }
        };

        let snapshot = match function_type {
            FunctionType::DiscriminantValue => None,
            FunctionType::Panic => None,
            FunctionType::RustFunction(_) => Some(FunctionCallSnapshot { args: encoded_args }),
        };

        FunctionCallEffects {
            precondition_assertion,
            result,
            snapshot,
        }
    }
}

enum FunctionType {
    DiscriminantValue,
    Panic,
    RustFunction(String),
}

impl FunctionType {
    fn new<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: DefId) -> FunctionType {
        let fn_name = tcx.def_path_str(def_id);
        match fn_name.as_str() {
            "std::intrinsics::discriminant_value" => FunctionType::DiscriminantValue,
            "core::panicking::panic" => FunctionType::Panic,
            _ => FunctionType::RustFunction(fn_name),
        }
    }
}

pub enum FunctionCallResult<'sym, 'tcx, T> {
    Value {
        value: SymValue<'sym, 'tcx, T>,
        postcondition: Option<PathConditionPredicate<'sym, 'tcx, T>>,
    },
    Never,
    Unknown {
        postcondition: PathConditionPredicate<'sym, 'tcx, T>,
    },
}

pub struct FunctionCallEffects<'sym, 'tcx, T> {
    pub precondition_assertion: Option<Assertion<'sym, 'tcx, T>>,
    pub result: FunctionCallResult<'sym, 'tcx, T>,
    pub snapshot: Option<FunctionCallSnapshot<'sym, 'tcx, T>>,
}
