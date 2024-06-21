use crate::{rustc_interface::{
    borrowck::consumers::BodyWithBorrowckFacts,
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt},
    },
}, value::{AggregateKind, Constant}};
use crate::value::{CastKind, SymValue, SymValueData, SymValueKind, SyntheticSymValue};

pub struct SymExContext {
    bump: bumpalo::Bump,
}

impl SymExContext {
    pub fn new() -> Self {
        Self {
            bump: bumpalo::Bump::new(),
        }
    }

    pub fn alloc<T>(&self, t: T) -> &T {
        self.bump.alloc(t)
    }

    pub fn alloc_slice<T: Copy>(&self, t: &[T]) -> &[T] {
        self.bump.alloc_slice_copy(t)
    }

    pub fn mk_ref<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Ref(ty, val))
    }

    pub fn mk_discriminant<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Discriminant(val))
    }

    pub fn mk_sym_value<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: SymValueKind<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.alloc(SymValueData::new(kind, self))
    }

    pub fn mk_cast<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: CastKind,
        val: SymValue<'sym, 'tcx, T>,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Cast(kind, val, ty))
    }

    pub fn mk_var<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        idx: usize,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Var(idx, ty))
    }

    pub fn mk_constant<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        c: Constant<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Constant(c))
    }

    pub fn mk_synthetic<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        t: T,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Synthetic(t))
    }

    pub fn mk_projection<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: mir::ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Projection(kind, val))
    }

    pub fn mk_aggregate<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: AggregateKind<'tcx>,
        vals: &'sym [SymValue<'sym, 'tcx, T>],
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Aggregate(kind, vals))
    }

    pub fn mk_bin_op<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        bin_op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::BinaryOp(ty, bin_op, lhs, rhs))
    }

    pub fn mk_checked_bin_op<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        bin_op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::CheckedBinaryOp(ty, bin_op, lhs, rhs))
    }

    pub fn mk_unary_op<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        unary_op: mir::UnOp,
        operand: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::UnaryOp(ty, unary_op, operand))
    }
}
