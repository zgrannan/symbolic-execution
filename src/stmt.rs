use pcs::borrows::engine::BorrowsDomain;
use pcs::{free_pcs::FreePcsBasicBlock, ReborrowBridge};

use crate::visualization::{export_path_json, StepType};
use crate::{
    context::ErrorLocation,
    encoder::Encoder,
    heap::SymbolicHeap,
    path::{OldMapEncoder, Path, StructureTerm},
    pcs_interaction::PcsLocation,
    place::Place,
    rustc_interface::middle::mir::{self},
    value::SymValue,
};
use crate::{semantics::VerifierSemantics, visualization::VisFormat, SymbolicExecution};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn handle_stmt_rhs<'heap>(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &'heap mut SymbolicHeap<'heap, 'mir, 'sym, 'tcx, S::SymValSynthetic>,
    ) -> Option<SymValue<'sym, 'tcx, S::SymValSynthetic>>
    where
        'mir: 'heap,
    {
        match &stmt.kind {
            mir::StatementKind::Assign(box (_place, rvalue)) => {
                let sym_value = self.encode_rvalue(heap, rvalue);
                Some(sym_value)
            }
            _ => None,
        }
    }
    pub fn handle_stmt_lhs(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: mir::Location,
        rhs: Option<SymValue<'sym, 'tcx, S::SymValSynthetic>>,
    ) {
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, _)) => {
                heap.insert(*place, rhs.unwrap(), location);
            }
            mir::StatementKind::StorageDead(local) => {
                heap.0.remove(&Place::new(*local, &[]));
            }
            mir::StatementKind::StorageLive(_)
            | mir::StatementKind::FakeRead(_)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..) => {}
            other => todo!("{:?}", other),
        }
    }

    pub fn handle_stmt(
        &mut self,
        pcs_block: &FreePcsBasicBlock<'tcx, BorrowsDomain<'mir, 'tcx>, ReborrowBridge<'tcx>>,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic, S::OldMapSymValSynthetic>,
        stmt: &mir::Statement<'tcx>,
        stmt_idx: usize,
    ) {
        let fpcs_loc = &pcs_block.statements[stmt_idx];
        self.set_error_context(
            path.path.clone(),
            ErrorLocation::Location(fpcs_loc.location),
        );
        self.handle_pcs(path, &fpcs_loc, true, fpcs_loc.location);
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
        let rhs = self.handle_stmt_rhs(stmt, &mut heap);
        self.handle_pcs(path, &fpcs_loc, false, fpcs_loc.location);
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
        self.handle_stmt_lhs(stmt, &mut heap, fpcs_loc.location, rhs);
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
    }

    pub fn execute_stmts_in_block(
        &mut self,
        pcs_block: &FreePcsBasicBlock<'tcx, BorrowsDomain<'mir, 'tcx>, ReborrowBridge<'tcx>>,
        block_data: &mir::BasicBlockData<'tcx>,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic, S::OldMapSymValSynthetic>,
        output_debug_json: bool,
    ) {
        for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
            let fpcs_loc = &pcs_block.statements[stmt_idx];
            self.handle_stmt(&pcs_block, path, stmt, stmt_idx);
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
    }
}
