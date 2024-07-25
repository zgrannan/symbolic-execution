use crate::{
    add_debug_note, context::ErrorLocation, heap::{HeapData, SymbolicHeap}, path::{AcyclicPath, Path}, path_conditions::PathConditions, place::Place, results::{ResultAssertion, ResultPath, SymbolicExecutionResult}, rustc_interface::middle::{
        mir::{Location, ProjectionElem},
        ty::{self, TyKind},
    }, semantics::VerifierSemantics, value::SymVar, visualization::{export_assertions, export_path_json, export_path_list, StepType, VisFormat}, SymbolicExecution
};
use std::{
    collections::{BTreeSet, VecDeque},
    ops::Deref,
};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn execute(&mut self) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic> {
        let mut result_paths: BTreeSet<ResultPath<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut assertions: BTreeSet<ResultAssertion<'sym, 'tcx, S::SymValSynthetic>> =
            BTreeSet::new();
        let mut heap_data = HeapData::new();
        let mut heap = SymbolicHeap::new(&mut heap_data, self.tcx, &self.body);
        for (idx, arg) in self.body.args_iter().enumerate() {
            let local = &self.body.local_decls[arg];
            self.symvars.push(local.ty);
            let sym_var = self.arena.mk_var(SymVar::Normal(idx), local.ty);
            let place = Place::new(arg, &[]);
            add_debug_note!(
                sym_var.debug_info,
                "Symvar for arg {:?} in {:?}",
                arg,
                self.body.span
            );
            /*
             * If we're passed in a reference-typed field, store in the heap its
             * dereference. TODO: Explain why
             */
            match sym_var.ty(self.tcx).rust_ty().kind() {
                ty::TyKind::Ref(_, _, _) => {
                    heap.insert(
                        place.project_deref(self.repacker()),
                        self.arena.mk_projection(ProjectionElem::Deref, sym_var),
                        Location::START,
                    );
                }
                _ => {
                    heap.insert(place, sym_var, Location::START);
                }
            }
        }
        let mut paths = vec![Path::new(
            AcyclicPath::from_start_block(),
            PathConditions::new(),
            heap_data,
        )];
        while let Some(mut path) = paths.pop() {
            let block = path.last_block();
            for local in self.havoc.get(block).iter() {
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body);
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
            let pcs_block = self.fpcs_analysis.get_all_for_bb(block);
            let block_data = &self.body.basic_blocks[block];
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                let fpcs_loc = &pcs_block.statements[stmt_idx];
                self.set_error_context(
                    path.path.clone(),
                    ErrorLocation::Location(fpcs_loc.location),
                );
                self.handle_pcs(&mut path, &fpcs_loc, true, fpcs_loc.location);
                self.handle_pcs(&mut path, &fpcs_loc, false, fpcs_loc.location);
                let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body);
                self.handle_stmt(stmt, &mut heap, fpcs_loc);
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
                &mut result_paths,
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
            export_path_list(&debug_output_dir, &result_paths);
        }
        SymbolicExecutionResult {
            paths: result_paths,
            assertions,
            symvars: self.symvars.clone(),
        }
    }
}
