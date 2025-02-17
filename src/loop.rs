use crate::{
    encoder::Encoder,
    havoc::InvariantInfo,
    heap::SymbolicHeap,
    path::{Path, SymExPath},
    place::Place,
    predicate::Predicate,
    results::ResultAssertions,
    rustc_interface::middle::mir::{self, BasicBlock, Location},
    semantics::VerifierSemantics,
    visualization::VisFormat,
    SymbolicExecution,
};

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
        for assertion in S::encode_loop_invariant(invariant_info.loop_head, path.clone(), self) {
            assertions.insert(path.conditional_assertion(assertion));
        }
        if let SymExPath::Loop(loop_path) = &path.path {
            self.add_loop_path(loop_path.clone(), path.pcs().clone());
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
                .get_all_for_bb(invariant_info.condition_check_block)
                // .unwrap()
                .unwrap();
            let block_data = &self.body.basic_blocks[invariant_info.condition_check_block];
            self.execute_stmts_in_block(&pcs_block, block_data, path, false);
            match &block_data.terminator().kind {
                mir::TerminatorKind::SwitchInt { discr, targets } => {
                    let ty = discr.ty(&self.body.local_decls, self.tcx);
                    let mut heap: SymbolicHeap<'_, 'mir, 'sym, 'tcx, S::SymValSynthetic> =
                        SymbolicHeap::new(&mut path.heap, self.tcx, self.body, &self.arena);
                    let operand = self.encode_operand(&mut heap, discr);
                    let pred = if let Some((value, _)) =
                        targets.iter().find(|t| t.1 == condition_valid_block)
                    {
                        Predicate::SwitchIntEq(operand, value, ty)
                    } else {
                        Predicate::SwitchIntNe(operand, targets.iter().map(|t| t.0).collect(), ty)
                    };
                    path.add_path_condition(pred);
                }
                _ => unreachable!(),
            }
        }

        // Assume invariant

        for assertion in S::encode_loop_invariant(invariant_info.loop_head, path.clone(), self) {
            path.add_path_condition(assertion);
        }
        true
    }
}
