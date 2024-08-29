use crate::{
    context::ErrorLocation,
    encoder::Encoder,
    heap::{HeapData, SymbolicHeap},
    path::{AcyclicPath, OldMapEncoder, Path, StructureTerm},
    path_conditions::PathConditions,
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
use std::collections::BTreeSet;

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn execute(
        mut self,
        heap_data: HeapData<'sym, 'tcx, S::SymValSynthetic>,
        symvars: Vec<ty::Ty<'tcx>>,
    ) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
        self.symvars = symvars;
        let mut assertions: BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            PathConditions::new(),
            heap_data,
            self.body.arg_count,
        )];
        while let Some(mut path) = paths.pop() {
            let block = path.last_block();
            let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
            heap.snapshot_values(block);
            for local in self.havoc.get(block).iter() {
                let place = Place::new(*local, &[]);
                heap.insert(
                    place,
                    self.mk_fresh_symvar(self.body.local_decls[*local].ty),
                    Location {
                        block,
                        statement_index: 0,
                    },
                );
            }
            for (path_conditions, assertion) in
                S::encode_loop_invariant(self.def_id.into(), block, &mut heap, &mut self)
            {
                assertions.insert((
                    path.path.clone(),
                    path_conditions,
                    Assertion::Eq(assertion, true),
                ));
            }
            let pcs_block = self.fpcs_analysis.get_all_for_bb(block);
            let block_data = &self.body.basic_blocks[block];
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                let fpcs_loc = &pcs_block.statements[stmt_idx];
                self.set_error_context(
                    path.path.clone(),
                    ErrorLocation::Location(fpcs_loc.location),
                );
                self.handle_pcs(&mut path, &fpcs_loc, true, fpcs_loc.location);
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
                let rhs = self.handle_stmt_rhs(stmt, &mut heap, fpcs_loc);
                self.handle_pcs(&mut path, &fpcs_loc, false, fpcs_loc.location);
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
                self.handle_stmt_lhs(stmt, &mut heap, fpcs_loc, rhs);
                let structure_encoder = self.old_map_encoder();
                match &stmt.kind {
                    mir::StatementKind::Assign(box (place, rvalue)) => {
                        let encoded_place: StructureTerm<'sym, 'tcx, S::OldMapSymValSynthetic> =
                            <OldMapEncoder<'mir, 'sym, 'tcx> as Encoder<
                                'mir,
                                'sym,
                                'tcx,
                                S::OldMapSymValSynthetic,
                            >>::encode_rvalue(
                                &structure_encoder, &mut path.old_map, rvalue
                            );
                        path.old_map.insert((*place).into(), encoded_place);
                    }
                    _ => {}
                }
                if let Some(debug_output_dir) = &self.debug_output_dir {
                    export_path_json(
                        &debug_output_dir,
                        &path,
                        fpcs_loc,
                        StepType::Instruction(stmt_idx),
                        self.fpcs_analysis.repacker(),
                    );
                }
            }
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
                &mut path,
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
