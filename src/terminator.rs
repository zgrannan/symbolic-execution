use std::collections::BTreeSet;

use pcs::borrows::engine::BorrowsDomain;
use pcs::free_pcs::FreePcsTerminator;
use pcs::ReborrowBridge;

use crate::context::ErrorLocation;
use crate::encoder::Encoder;
use crate::execute::ResultAssertions;
use crate::function_call_snapshot::FunctionCallSnapshot;
use crate::heap::SymbolicHeap;
use crate::path::{InputPlace, LoopPath, OldMap, OldMapEncoder, Path};
use crate::path_conditions::{PathConditionAtom, PathConditionPredicate};
use crate::pcs_interaction::PcsLocation;
use crate::results::ResultAssertion;
use crate::value::SymValue;
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
        paths: &mut Vec<Path<'sym, 'tcx, S::SymValSynthetic, S::OldMapSymValSynthetic>>,
        assertions: &mut ResultAssertions<'sym, 'tcx, S::SymValSynthetic>,
        mut path: Path<'sym, 'tcx, S::SymValSynthetic, S::OldMapSymValSynthetic>,
        fpcs_terminator: FreePcsTerminator<'tcx, BorrowsDomain<'mir, 'tcx>, ReborrowBridge<'tcx>>,
        location: &PcsLocation<'mir, 'tcx>,
    ) where
        S::SymValSynthetic: Eq,
    {
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, self.body, &self.arena);
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
                self.set_error_context(old_path.clone(), ErrorLocation::TerminatorStart(*target));
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
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let ty = discr.ty(&self.body.local_decls, self.tcx);
                for ((value, target), _loc) in targets.iter().zip(fpcs_terminator.succs.iter()) {
                    let mut path = path.push(target);
                    let pred = PathConditionPredicate::Eq(value, ty);
                    let mut heap: SymbolicHeap<'_, 'mir, 'sym, 'tcx, S::SymValSynthetic> =
                        SymbolicHeap::new(&mut path.heap, self.tcx, self.body, &self.arena);
                    let operand: SymValue<'sym, 'tcx, S::SymValSynthetic> =
                        self.encode_operand(&mut heap, discr);
                    path.pcs
                        .insert(PathConditionAtom::new(operand, pred.clone()));
                    paths.push(path);
                }
                let mut path = path.push(targets.otherwise());
                let pred = PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty);
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
                path.pcs.insert(PathConditionAtom::new(
                    self.encode_operand(&mut heap, discr),
                    pred.clone(),
                ));
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
                assertions.insert(ResultAssertion {
                    path: path.path.clone(),
                    pcs: path.pcs.clone(),
                    assertion: Assertion::Eq(cond, *expected),
                });
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
                    let effects = self.get_function_call_effects(
                        *def_id,
                        substs,
                        &mut heap,
                        &mut path.old_map,
                        &args.iter().map(|arg| &arg.node).collect(),
                        location.location,
                        terminator.source_info.span,
                    );

                    if let Some(assertion) = effects.precondition_assertion {
                        assertions.insert(ResultAssertion {
                            path: path.path.clone(),
                            pcs: path.pcs.clone(),
                            assertion,
                        });
                    }

                    match effects.result {
                        FunctionCallResult::Value {
                            old_map_value,
                            value,
                            postcondition,
                        } => {
                            heap.insert(*destination, value, location.location);
                            if let Some(old_map_value) = old_map_value {
                                path.old_map.insert((*destination).into(), old_map_value);
                            }
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
                            let sym_var = self.mk_fresh_symvar(
                                destination.ty(&self.body.local_decls, self.tcx).ty,
                            );
                            heap.insert(*destination, sym_var, location.location);
                            path.pcs
                                .insert(PathConditionAtom::new(sym_var, postcondition));
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
        old_map: &mut OldMap<'sym, 'tcx, S::OldMapSymValSynthetic>,
        args: &Vec<&Operand<'tcx>>,
        location: Location,
        span: Span,
    ) -> FunctionCallEffects<'sym, 'tcx, S::SymValSynthetic, S::OldMapSymValSynthetic>
    where
        'mir: 'heap,
    {
        if let Some(result) = S::encode_fn_call(
            span,
            self,
            def_id,
            substs,
            heap.0,
            old_map,
            args,
        ) {
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
                let old_encoder = self.old_map_encoder();
                FunctionCallResult::Value {
                    value,
                    old_map_value: Some(self.arena.mk_projection(
                        mir::ProjectionElem::Deref,
                        <OldMapEncoder<'mir, 'sym, 'tcx> as Encoder<
                            'mir,
                            'sym,
                            'tcx,
                            S::OldMapSymValSynthetic,
                        >>::encode_operand(&old_encoder, old_map, &args[0]),
                    )),
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

pub enum FunctionCallResult<'sym, 'tcx, T, U> {
    Value {
        value: SymValue<'sym, 'tcx, T>,
        old_map_value: Option<SymValue<'sym, 'tcx, U, InputPlace<'tcx>>>,
        postcondition: Option<PathConditionPredicate<'sym, 'tcx, T>>,
    },
    Never,
    Unknown {
        postcondition: PathConditionPredicate<'sym, 'tcx, T>,
    },
}

pub struct FunctionCallEffects<'sym, 'tcx, T, U> {
    pub precondition_assertion: Option<Assertion<'sym, 'tcx, T>>,
    pub result: FunctionCallResult<'sym, 'tcx, T, U>,
    pub snapshot: Option<FunctionCallSnapshot<'sym, 'tcx, T>>,
}
