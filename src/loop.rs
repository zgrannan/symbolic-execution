use crate::{
    context::ErrorLocation,
    encoder::Encoder,
    execute::ResultAssertions,
    havoc::InvariantInfo,
    heap::{HeapData, SymbolicHeap},
    path::{AcyclicPath, Path, SymExPath},
    path_conditions::{
        PathConditionAtom, PathConditionPredicate, PathConditionPredicateAtom, PathConditions,
    },
    place::Place,
    results::{ResultAssertion, SymbolicExecutionResult},
    rustc_interface::middle::{
        mir::{self, BasicBlock, Location},
        ty,
    },
    semantics::VerifierSemantics,
    value::SymValue,
    visualization::{export_assertions, export_path_json, export_path_list, StepType, VisFormat},
    Assertion, SymbolicExecution,
};
use std::collections::{BTreeSet, HashSet};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn handle_loop(
        &mut self,
        condition_valid_block: BasicBlock,
        invariant_info: InvariantInfo,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        assertions: &mut ResultAssertions<'sym, 'tcx, S::SymValSynthetic>,
    ) -> bool
    where
        S::SymValSynthetic: Eq,
    {
        for (path_conditions, assertion) in
            S::encode_loop_invariant(invariant_info.loop_head, path.clone(), self)
        {
            let mut pcs = path.pcs.clone();
            pcs.extend(path_conditions);
            assertions.insert(ResultAssertion {
                path: path.path.clone(),
                pcs,
                assertion: Assertion::Eq(assertion, true),
            });
        }
        if let SymExPath::Loop(loop_path) = &path.path {
            self.add_loop_path(loop_path.clone(), path.pcs.clone());
            return false;
        }
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);

        for local in invariant_info.havoced_locals.iter() {
            let place = Place::new(*local, &[]);
            heap.insert(
                place,
                self.mk_fresh_symvar(self.body.local_decls[*local].ty),
                Location {
                    block: condition_valid_block,
                    statement_index: 0,
                },
            );
        }

        {
            let pcs_block = self
                .fpcs_analysis
                .get_all_for_bb(invariant_info.condition_check_block);
            let block_data = &self.body.basic_blocks[invariant_info.condition_check_block];
            self.execute_stmts_in_block(&pcs_block, block_data, path, false);
            match &block_data.terminator().kind {
                mir::TerminatorKind::SwitchInt { discr, targets } => {
                    let ty = discr.ty(&self.body.local_decls, self.tcx);
                    let pred = if let Some((value, _)) =
                        targets.iter().find(|t| t.1 == condition_valid_block)
                    {
                        PathConditionPredicate::Eq(value, ty)
                    } else {
                        PathConditionPredicate::Ne(targets.iter().map(|t| t.0).collect(), ty)
                    };
                    let mut heap: SymbolicHeap<'_, 'mir, 'sym, 'tcx, S::SymValSynthetic> =
                        SymbolicHeap::new(&mut path.heap, self.tcx, self.body, &self.arena);
                    let operand = self.encode_operand(&mut heap, discr);
                    path.pcs
                        .insert(PathConditionAtom::predicate(operand, pred.clone()));
                }
                _ => unreachable!(),
            }
        }

        // Assume invariant

        for (path_conditions, assertion) in
            S::encode_loop_invariant(invariant_info.loop_head, path.clone(), self)
        {
            if let Some(implication) =
                PathConditionAtom::implies(path_conditions, assertion, self.tcx)
            {
                path.pcs.insert(implication);
            }
        }
        true
    }
}
