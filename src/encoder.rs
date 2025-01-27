use pcs::utils::PlaceRepacker;

use crate::context::SymExContext;
use crate::heap::SymbolicHeap;
use crate::place::Place;
use crate::rustc_interface::middle::mir;
use crate::value::{AggregateKind, SymVar, SyntheticSymValue};
use crate::visualization::VisFormat;
use crate::{semantics::VerifierSemantics, value::SymValue};
use crate::{LookupGet, SymbolicExecution};

pub trait Encoder<'mir, 'sym, 'tcx: 'mir, S> {
    type V: 'sym;
    type Ctxt<'ctxt>
    where
        'mir: 'ctxt,
        'tcx: 'ctxt,
        'sym: 'ctxt;

    fn alloc<T>(&self, t: T) -> &'sym T
    where
        'tcx: 'sym,
    {
        self.arena().alloc(t)
    }
    fn arena(&self) -> &'sym SymExContext<'tcx>;
    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx>;
    fn encode_rvalue<'ctxt>(
        &self,
        ctxt: &mut Self::Ctxt<'ctxt>,
        rvalue: &mir::Rvalue<'tcx>,
    ) -> SymValue<'sym, 'tcx, S, Self::V>
    where
        'tcx: 'ctxt,
        'sym: 'ctxt,
        S: SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug,
        Self::V: std::fmt::Debug,
    {
        let body = self.repacker().body();
        let tcx = self.repacker().tcx();
        let rvalue_ty = rvalue.ty(body, tcx);
        let arena = self.arena();
        match rvalue {
            mir::Rvalue::Use(operand) => self.encode_operand(ctxt, &operand),
            mir::Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                let lhs = self.encode_operand(ctxt, &lhs);
                let rhs = self.encode_operand(ctxt, &rhs);
                arena.mk_bin_op(rvalue_ty, *op, lhs, rhs)
            }
            mir::Rvalue::Aggregate(kind, ops) => {
                let ops = ops
                    .iter()
                    .map(|op| self.encode_operand(ctxt, op))
                    .collect::<Vec<_>>();
                arena.mk_aggregate(
                    AggregateKind::rust(*kind.clone(), rvalue.ty(body, tcx)),
                    arena.alloc_slice(&ops),
                )
            }
            mir::Rvalue::Discriminant(target) => self
                .arena()
                .mk_discriminant(self.encode_place(ctxt, &(*target).into())),
            mir::Rvalue::Ref(_, kind, referred_place) => {
                let base = self.encode_place(ctxt, &(*referred_place).into());
                if kind.mutability().is_mut() {
                    self.remove_place_from_heap(ctxt, (*referred_place).into());
                }
                arena.mk_ref(base, kind.mutability())
            }
            mir::Rvalue::UnaryOp(op, operand) => {
                let operand = self.encode_operand(ctxt, operand);
                arena.mk_unary_op(rvalue_ty, *op, operand)
            }
            mir::Rvalue::Cast(kind, operand, ty) => {
                let operand = self.encode_operand(ctxt, operand);
                arena.mk_cast((*kind).into(), operand, *ty)
            }
            _ => todo!("{rvalue:?}"),
        }
    }

    fn encode_operand<'ctxt>(
        &self,
        ctxt: &mut Self::Ctxt<'ctxt>,
        operand: &mir::Operand<'tcx>,
    ) -> SymValue<'sym, 'tcx, S, Self::V>
    where
        'tcx: 'ctxt,
        'sym: 'ctxt,
    {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let place: Place<'tcx> = (*place).into();
                let sym_value = self.encode_place(ctxt, &place);
                // TODO: Remove the place from the heap if it is a move.
                // if matches!(operand, mir::Operand::Move(_)) {
                //     self.remove_place_from_heap(ctxt, place)
                // }
                sym_value
            }
            mir::Operand::Constant(box c) => self.arena().mk_constant(c.const_.into()),
        }
    }

    fn remove_place_from_heap<'ctxt>(&self, ctxt: &mut Self::Ctxt<'ctxt>, place: Place<'tcx>)
    where
        'mir: 'ctxt;

    fn encode_place<'ctxt>(
        &self,
        ctxt: &mut Self::Ctxt<'ctxt>,
        place: &Place<'tcx>,
    ) -> SymValue<'sym, 'tcx, S, Self::V>
    where
        'sym: 'ctxt,
        'tcx: 'ctxt;
}

impl<'mir, 'sym, 'tcx: 'mir, S> Encoder<'mir, 'sym, 'tcx, S::SymValSynthetic>
    for SymbolicExecution<'mir, 'sym, 'tcx, S>
where
    S: VerifierSemantics<'sym, 'tcx>,
    S::SymValSynthetic: VisFormat,
{
    type V = SymVar;
    type Ctxt<'ctxt> = SymbolicHeap<'ctxt, 'mir, 'sym, 'tcx, S::SymValSynthetic>
    where 'tcx: 'ctxt, 'sym: 'ctxt, 'mir: 'ctxt;

    fn arena(&self) -> &'sym SymExContext<'tcx> {
        self.arena
    }

    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx> {
        PlaceRepacker::new(self.body, self.tcx)
    }

    fn encode_place<'ctxt>(
        &self,
        ctxt: &mut Self::Ctxt<'ctxt>,
        place: &Place<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic, Self::V>
    where
        'tcx: 'ctxt,
        'sym: 'ctxt,
        'mir: 'ctxt,
    {
        self.encode_maybe_old_place::<LookupGet, _>(ctxt.0, place)
    }

    fn remove_place_from_heap<'ctxt>(&self, ctxt: &mut Self::Ctxt<'ctxt>, place: Place<'tcx>)
    where
        'mir: 'ctxt,
    {
        ctxt.0.remove(&place);
    }
}
