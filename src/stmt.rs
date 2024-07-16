use pcs::{
    borrows::engine::{BorrowsDomain, ReborrowAction},
    free_pcs::FreePcsLocation,
};

use crate::{
    heap::SymbolicHeap,
    pcs_interaction::PcsLocation,
    place::Place,
    rustc_interface::middle::mir::{self, ProjectionElem},
    value::AggregateKind,
    LookupGet, LookupTake,
};
use crate::{semantics::VerifierSemantics, visualization::VisFormat, SymbolicExecution};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub(crate) fn handle_stmt(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
    ) {
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                let sym_value = match rvalue {
                    mir::Rvalue::Use(operand) => {
                        let value = self.encode_operand(heap.0, &operand);
                        if operand.ty(&self.body.local_decls, self.tcx).is_ref() {
                            let place: Place<'tcx> = (*place).into();
                            return heap.insert(
                                place.project_deref(self.repacker()),
                                self.arena.mk_projection(ProjectionElem::Deref, value),
                            );
                        } else {
                            value
                        }
                    }
                    mir::Rvalue::CheckedBinaryOp(op, box (lhs, rhs)) => {
                        let lhs = self.encode_operand(heap.0, &lhs);
                        let rhs = self.encode_operand(heap.0, &rhs);
                        self.arena.mk_checked_bin_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            lhs,
                            rhs,
                        )
                    }
                    mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                        let lhs = self.encode_operand(heap.0, &lhs);
                        let rhs = self.encode_operand(heap.0, &rhs);
                        self.arena.mk_bin_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            lhs,
                            rhs,
                        )
                    }
                    mir::Rvalue::Aggregate(kind, ops) => {
                        let ops = ops
                            .iter()
                            .map(|op| self.encode_operand(heap.0, op))
                            .collect::<Vec<_>>();
                        self.arena.mk_aggregate(
                            AggregateKind::rust(
                                *kind.clone(),
                                place.ty(&self.body.local_decls, self.tcx).ty,
                            ),
                            self.alloc_slice(&ops),
                        )
                    }
                    mir::Rvalue::Discriminant(target) => self
                        .arena
                        .mk_discriminant(self.encode_place::<LookupGet, _>(heap.0, target)),
                    mir::Rvalue::Ref(_, kind, referred_place) => {
                        let base = if *kind == mir::BorrowKind::Shared {
                            self.encode_place::<LookupGet, _>(heap.0, referred_place)
                        } else {
                            self.encode_place::<LookupTake, _>(heap.0, referred_place)
                        };
                        let place: Place<'tcx> = (*place).into();
                        return heap.insert(place.project_deref(self.repacker()), base);
                    }
                    mir::Rvalue::UnaryOp(op, operand) => {
                        let operand = self.encode_operand(heap.0, operand);
                        self.arena.mk_unary_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            operand,
                        )
                    }
                    mir::Rvalue::Cast(kind, operand, ty) => {
                        let operand = self.encode_operand(heap.0, operand);
                        self.arena.mk_cast((*kind).into(), operand, *ty)
                    }
                    _ => todo!("{rvalue:?}"),
                };
                heap.insert(*place, sym_value);
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
