use crate::{
    context::ErrorLocation,
    heap::{HeapData, SymbolicHeap},
    path::{AcyclicPath, Path},
    predicate::Predicate,
    results::{ResultAssertions, SymbolicExecutionResult},
    semantics::VerifierSemantics,
    visualization::{export_assertions, export_path_json, export_path_list, StepType, VisFormat},
    SymbolicExecution,
};

impl<'mir, 'sym, 'tcx, 'bc, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, 'bc, S>
{
    pub fn execute(
        mut self,
        heap_data: HeapData<'sym, 'tcx, S::SymValSynthetic>,
    ) -> SymbolicExecutionResult<'sym, 'tcx, S>
    where
        S::SymValSynthetic: Eq,
    {
        let mut assertions: ResultAssertions<'sym, 'tcx, S::SymValSynthetic> =
            ResultAssertions::new();
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            Predicate::true_(),
            heap_data,
        )];
        'mainloop: while let Some(mut path) = paths.pop() {
            let block = path.last_block();
            let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
            heap.snapshot_values(block);
            let pcg_block = self.fpcs_analysis.get_all_for_bb(block).unwrap().unwrap();
            let block_data = &self.body.basic_blocks[block];
            if let Some(invariant_info) = self.havoc.get_invariant_info(block) {
                if !self.handle_loop(block, invariant_info, &mut path, &mut assertions) {
                    continue 'mainloop;
                }
            }
            self.execute_stmts_in_block(&pcg_block, block_data, &mut path, true);
            // Actions made to evaluate terminator
            let last_fpcs_loc = pcg_block.statements.last().unwrap();
            self.set_error_context(
                path.path.clone(),
                ErrorLocation::Location(last_fpcs_loc.location),
            );
            assert!(pcg_block.statements.len() == block_data.statements.len() + 1);
            self.handle_pcg(&mut path, &last_fpcs_loc, last_fpcs_loc.location);
            if let Some(debug_output_dir) = &self.debug_output_dir {
                export_path_json(
                    &debug_output_dir,
                    &path,
                    StepType::Instruction(block_data.statements.len()),
                    self.fpcs_analysis.ctxt(),
                );
            }
            self.handle_terminator(
                block_data.terminator(),
                &mut paths,
                &mut assertions,
                path,
                pcg_block.terminator,
                &last_fpcs_loc,
            );
        }
        if let Some(debug_output_dir) = &self.debug_output_dir {
            export_assertions(
                &debug_output_dir,
                &assertions,
                &self.body.var_debug_info,
                self.tcx,
            );
            export_path_list(&debug_output_dir, &self.result_paths, &self.debug_paths);
        }
        SymbolicExecutionResult {
            paths: self.result_paths,
            assertions,
            fresh_symvars: self.fresh_symvars.clone(),
            verifier_semantics: self.verifier_semantics,
        }
    }
}
