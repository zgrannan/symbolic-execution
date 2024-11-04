use pcs::borrows::engine::BorrowsDomain;
use pcs::free_pcs::FreePcsTerminator;
use pcs::BorrowsBridge;

use crate::context::ErrorLocation;
use crate::encoder::Encoder;
use crate::function_call_snapshot::FunctionCallSnapshot;
use crate::heap::SymbolicHeap;
use crate::path::Path;
use crate::pcs_interaction::PcsLocation;
use crate::predicate::Predicate;
use crate::results::ResultAssertion;
use crate::results::ResultAssertions;
use crate::value::SymValue;
use crate::value::SymVar;
use crate::visualization::{export_path_json, StepType};
use crate::Assertion;
use crate::{semantics::VerifierSemantics, visualization::VisFormat, SymbolicExecution};

use crate::rustc_interface::hir::def_id::DefId;
use crate::rustc_interface::middle::{
    mir::{self, Location, Operand},
    ty::{self, GenericArgsRef},
};
use crate::rustc_interface::span::Span;

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn handle_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        paths: &mut Vec<Path<'sym, 'tcx, S::SymValSynthetic>>,
        assertions: &mut ResultAssertions<'sym, 'tcx, S::SymValSynthetic>,
        mut path: Path<'sym, 'tcx, S::SymValSynthetic>,
        fpcs_terminator: FreePcsTerminator<'tcx>,
        location: &PcsLocation<'mir, 'tcx>,
    ) where
        S::SymValSynthetic: Eq,
    {
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
                if !path.path.can_push(*target) {
                    // Don't go down a loop a 2nd time; invariant after 1st
                    // execution presumably has already been asserted
                    return;
                }
                let old_path = path.path.clone();
                let mut path = path.push(*target);
                self.set_error_context(old_path.clone(), ErrorLocation::Terminator(*target));
                self.handle_pcg(&mut path, &fpcs_terminator.succs[0], location.location);
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
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let ty = discr.ty(&self.body.local_decls, self.tcx);
                for ((value, target), _loc) in targets.iter().zip(fpcs_terminator.succs.iter()) {
                    let mut path = path.push(target);
                    let mut heap: SymbolicHeap<'_, 'mir, 'sym, 'tcx, S::SymValSynthetic> =
                        SymbolicHeap::new(&mut path.heap, self.tcx, self.body, &self.arena);
                    let operand: SymValue<'sym, 'tcx, S::SymValSynthetic> =
                        self.encode_operand(&mut heap, discr);
                    let pred = Predicate::SwitchIntEq(operand, value, ty);
                    path.add_path_condition(pred);
                    paths.push(path);
                }
                let mut path = path.push(targets.otherwise());
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
                let pred = Predicate::SwitchIntNe(
                    self.encode_operand(&mut heap, discr),
                    targets.iter().map(|t| t.0).collect(),
                    ty,
                );
                path.add_path_condition(pred);
                paths.push(path);
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
                let cond = self.encode_operand(&mut heap, cond);
                let cond = if *expected {
                    cond
                } else {
                    self.arena.mk_not(cond)
                };
                assertions.insert(path.conditional_assertion(cond.into()));
                paths.push(path.push(*target));
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => match func.ty(&self.body.local_decls, self.tcx).kind() {
                ty::TyKind::FnDef(def_id, substs) => {
                    let mut heap =
                        SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
                    let effects = self.get_function_call_effects(
                        *def_id,
                        substs,
                        &mut heap,
                        &args.iter().map(|arg| &arg.node).collect(),
                        location.location,
                        terminator.source_info.span,
                    );

                    if let Some(assertion) = effects.precondition_assertion {
                        assertions.insert(path.conditional_assertion(assertion));
                    }

                    let mut heap =
                        SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
                    match effects.result {
                        FunctionCallResult::Value {
                            value,
                            postcondition,
                        } => {
                            heap.insert(*destination, value, location.location);
                            if let Some(postcondition) = postcondition {
                                path.add_path_condition(postcondition);
                            }
                        }
                        FunctionCallResult::Unknown {
                            pre_values,
                            post_values,
                        } => {
                            if let Some(snapshot) = effects.snapshot {
                                path.function_call_snapshots
                                    .add_snapshot(location.location, snapshot);
                            }
                            let sym_var = self.mk_fresh_symvar(
                                destination.ty(&self.body.local_decls, self.tcx).ty,
                            );
                            heap.insert(*destination, sym_var, location.location);
                            path.add_path_condition(Predicate::Postcondition {
                                expr: sym_var,
                                def_id: *def_id,
                                substs: *substs,
                                pre_values: self.alloc_slice(pre_values),
                                post_values: self.alloc_slice(post_values),
                            });
                        }
                        FunctionCallResult::Never => {}
                    };
                    if let Some(target) = target {
                        paths.push(path.push(*target));
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
                self.complete_path(path, location);
            }
            _ => {}
        }
    }

    fn get_function_call_effects<'heap>(
        &mut self,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut SymbolicHeap<'heap, 'mir, 'sym, 'tcx, S::SymValSynthetic>,
        args: &Vec<&Operand<'tcx>>,
        location: Location,
        span: Span,
    ) -> FunctionCallEffects<'sym, 'tcx, S::SymValSynthetic>
    where
        'mir: 'heap,
    {
        if let Some(result) = S::encode_fn_call(span, self, def_id, substs, heap.0, args) {
            return result;
        }
        let function_type = FunctionType::new(self.tcx, def_id);
        let encoded_args: Vec<_> = args
            .iter()
            .map(|arg| self.encode_operand(heap, arg))
            .collect();
        let encoded_args: &'sym [SymValue<'sym, 'tcx, S::SymValSynthetic>] =
            self.alloc_slice(&encoded_args);
        let precondition_assertion = match function_type {
            FunctionType::DiscriminantValue => None,
            FunctionType::Panic => Some(Assertion::false_(self.arena)),
            FunctionType::RustFunction => {
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
            FunctionType::RustFunction => {
                let postcondition_args = args
                    .iter()
                    .zip(encoded_args)
                    .map(|(operand, encoded)| {
                        self.havoc_operand_ref(operand, heap, location)
                            .unwrap_or(encoded)
                    })
                    .collect::<Vec<_>>();
                FunctionCallResult::Unknown {
                    pre_values: self.alloc_slice(&encoded_args),
                    post_values: self.alloc_slice(&postcondition_args),
                }
            }
        };

        let snapshot = match function_type {
            FunctionType::DiscriminantValue => None,
            FunctionType::Panic => None,
            FunctionType::RustFunction => Some(FunctionCallSnapshot::new(
                encoded_args,
                args.iter()
                    .map(|arg| arg.place().map(|p| p.local))
                    .collect(),
            )),
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
    RustFunction,
}

impl FunctionType {
    fn new<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: DefId) -> FunctionType {
        let fn_name = tcx.def_path_str(def_id);
        match fn_name.as_str() {
            "std::intrinsics::discriminant_value" => FunctionType::DiscriminantValue,
            "core::panicking::panic" => FunctionType::Panic,
            _ => FunctionType::RustFunction,
        }
    }
}

pub enum FunctionCallResult<'sym, 'tcx, T> {
    Value {
        value: SymValue<'sym, 'tcx, T>,
        postcondition: Option<Predicate<'sym, 'tcx, T>>,
    },
    Never,
    Unknown {
        /// The values of the arguments just before the call. These are used to evaluate
        /// `old()` expressions in the postcondition
        pre_values: &'sym [SymValue<'sym, 'tcx, T>],
        /// The values of the arguments just after the call. THe postcondition
        /// holds w.r.t these values
        post_values: &'sym [SymValue<'sym, 'tcx, T>],
    },
}

pub struct FunctionCallEffects<'sym, 'tcx, T> {
    pub precondition_assertion: Option<Assertion<'sym, 'tcx, T>>,
    pub result: FunctionCallResult<'sym, 'tcx, T>,
    pub snapshot: Option<FunctionCallSnapshot<'sym, 'tcx, T>>,
}
