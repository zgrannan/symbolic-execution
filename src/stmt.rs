use pcs::{
    borrows::engine::{BorrowsDomain, ReborrowAction},
    free_pcs::FreePcsLocation,
};

use crate::{
    encoder::Encoder,
    heap::SymbolicHeap,
    pcs_interaction::PcsLocation,
    place::Place,
    rustc_interface::{
        hir::Mutability,
        middle::mir::{self, ProjectionElem},
    },
    value::{AggregateKind, SymValue},
    LookupGet, LookupTake,
};
use crate::{semantics::VerifierSemantics, visualization::VisFormat, SymbolicExecution};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub(crate) fn handle_stmt_rhs<'heap>(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &'heap mut SymbolicHeap<'heap, 'mir, 'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'_, 'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S::SymValSynthetic>>
    where
        'mir: 'heap,
    {
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                let sym_value = self.encode_rvalue(heap, rvalue);
                Some(sym_value)
            }
            _ => None,
        }
    }
    pub(crate) fn handle_stmt_lhs(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
        rhs: Option<SymValue<'sym, 'tcx, S::SymValSynthetic>>,
    ) {
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, _)) => {
                heap.insert(*place, rhs.unwrap(), pcs.location);
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
}
