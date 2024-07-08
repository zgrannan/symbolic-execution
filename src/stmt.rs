use pcs::{borrows::engine::BorrowsDomain, free_pcs::FreePcsLocation};

use crate::{heap::SymbolicHeap, place::Place, rustc_interface::{
    ast::Mutability,
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, ProjectionElem, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt, TyKind},
    },
    span::ErrorGuaranteed,
}, value::AggregateKind};
use crate::{semantics::VerifierSemantics, visualization::VisFormat, SymbolicExecution};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn handle_stmt(
        &mut self,
        stmt: &mir::Statement<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        pcs: &FreePcsLocation<'tcx, BorrowsDomain<'tcx>>,
    ) {
        let reborrows = &pcs.extra.after.reborrows;
        match &stmt.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                match place.ty(&self.body.local_decls, self.tcx).ty.kind() {
                    ty::TyKind::Ref(_, _, Mutability::Mut) => return,
                    _ => {}
                }
                let sym_value = match rvalue {
                    mir::Rvalue::Use(operand) => self.encode_operand(heap.0, &operand, reborrows),
                    mir::Rvalue::CheckedBinaryOp(op, box (lhs, rhs)) => {
                        let lhs = self.encode_operand(heap.0, &lhs, reborrows);
                        let rhs = self.encode_operand(heap.0, &rhs, reborrows);
                        self.arena.mk_checked_bin_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            lhs,
                            rhs,
                        )
                    }
                    mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                        let lhs = self.encode_operand(heap.0, &lhs, reborrows);
                        let rhs = self.encode_operand(heap.0, &rhs, reborrows);
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
                            .map(|op| self.encode_operand(heap.0, op, reborrows))
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
                        .mk_discriminant(self.encode_place(heap.0, &(*target).into(), reborrows)),
                    mir::Rvalue::Ref(_, kind, place) => match kind {
                        mir::BorrowKind::Shared => {
                            let base = self.encode_place(heap.0, &(*place).into(), reborrows);
                            self.arena.mk_ref(base, Mutability::Not)
                        }
                        _ => return,
                    },
                    mir::Rvalue::UnaryOp(op, operand) => {
                        let operand = self.encode_operand(heap.0, operand, reborrows);
                        self.arena.mk_unary_op(
                            place.ty(&self.body.local_decls, self.tcx).ty,
                            *op,
                            operand,
                        )
                    }
                    mir::Rvalue::Cast(kind, operand, ty) => {
                        let operand = self.encode_operand(heap.0, operand, reborrows);
                        self.arena.mk_cast((*kind).into(), operand, *ty)
                    }
                    _ => todo!("{rvalue:?}"),
                };
                heap.insert((*place).into(), sym_value);
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
