use crate::{
    context::ErrorLocation,
    encoder::Encoder,
    heap::{HeapData, SymbolicHeap},
    path::{AcyclicPath, OldMapEncoder, Path, StructureTerm, SymExPath},
    path_conditions::{PathConditionAtom, PathConditionPredicate, PathConditions},
    place::Place,
    results::{ResultAssertion, SymbolicExecutionResult},
    rustc_interface::middle::{
        mir::{self, Location},
        ty,
    },
    semantics::VerifierSemantics,
    visualization::{export_assertions, export_path_json, export_path_list, StepType, VisFormat},
    Assertion, SymbolicExecution,
};
use std::collections::{BTreeSet, HashSet};

#[derive(Clone, Debug)]
pub struct ResultAssertions<'sym, 'tcx, T>(Vec<ResultAssertion<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T> ResultAssertions<'sym, 'tcx, T> {
    pub fn new() -> Self {
        ResultAssertions(Vec::new())
    }

    pub fn iter(&self) -> impl Iterator<Item = &ResultAssertion<'sym, 'tcx, T>> {
        self.0.iter()
    }
}
impl<'sym, 'tcx, T: Eq> ResultAssertions<'sym, 'tcx, T> {
    pub fn insert(&mut self, assertion: ResultAssertion<'sym, 'tcx, T>) {
        if !self.0.contains(&assertion) {
            self.0.push(assertion);
        }
    }
}

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn execute(
        mut self,
        heap_data: HeapData<'sym, 'tcx, S::SymValSynthetic>,
        symvars: Vec<ty::Ty<'tcx>>,
    ) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic>
    where
        S::SymValSynthetic: Eq,
    {
        self.symvars = symvars;
        let mut assertions: ResultAssertions<'sym, 'tcx, S::SymValSynthetic> =
            ResultAssertions::new();
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            PathConditions::new(),
            heap_data,
        )];
        'mainloop: while let Some(mut path) = paths.pop() {
            let block = path.last_block();
            let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
            heap.snapshot_values(block);
            let pcs_block = self.fpcs_analysis.get_all_for_bb(block);
            let block_data = &self.body.basic_blocks[block];
            if let Some(invariant_info) = self.havoc.get_invariant_info(block) {
                if !self.handle_loop(block, invariant_info, &mut path, &mut assertions) {
                    continue 'mainloop;
                }
            }
            self.execute_stmts_in_block(&pcs_block, block_data, &mut path, true);
            // Actions made to evaluate terminator
            let last_fpcs_loc = pcs_block.statements.last().unwrap();
            self.set_error_context(
                path.path.clone(),
                ErrorLocation::Location(last_fpcs_loc.location),
            );
            assert!(pcs_block.statements.len() == block_data.statements.len() + 1);
            self.handle_pcs(&mut path, &last_fpcs_loc, true, last_fpcs_loc.location);
            self.handle_pcs(&mut path, &last_fpcs_loc, false, last_fpcs_loc.location);
            if let Some(debug_output_dir) = &self.debug_output_dir {
                export_path_json(
                    &debug_output_dir,
                    &path,
                    last_fpcs_loc,
                    StepType::Instruction(block_data.statements.len()),
                    self.fpcs_analysis.repacker(),
                );
            }
            self.handle_terminator(
                block_data.terminator(),
                &mut paths,
                &mut assertions,
                path,
                pcs_block.terminator,
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
            symvars: self.symvars.clone(),
        }
    }
}
