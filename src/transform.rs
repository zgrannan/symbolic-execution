use crate::context::SymExContext;
use crate::value::{BackwardsFn, SyntheticSymValue};
use crate::{
    rustc_interface::{
        ast::Mutability,
        middle::{
            mir::{self, ProjectionElem},
            ty,
        },
    },
    value::{AggregateKind, CastKind, Constant, SymValue, SymVar},
};

pub trait SymValueTransformer<'sym, 'tcx, T, V = SymVar, U = SymVar, TT = T>:
    BaseSymValueTransformer<'sym, 'tcx, T, V, U, TT>
    + SyntheticSymValueTransformer<'sym, 'tcx, T, U, TT>
{
}

pub trait SyntheticSymValueTransformer<'sym, 'tcx, T, U = SymVar, TT = T> {
    fn transform_synthetic(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        s: T,
    ) -> SymValue<'sym, 'tcx, TT, U>;
}

pub trait BaseSymValueTransformer<'sym, 'tcx, T, V = SymVar, U = SymVar, TT = T> {
    fn transform_var(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        var: V,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, TT, U>;

    fn transform_constant(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        c: &'sym Constant<'tcx>,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_constant(c.clone())
    }
    fn transform_checked_binary_op(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, TT, U>,
        rhs: SymValue<'sym, 'tcx, TT, U>,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_checked_bin_op(ty, op, lhs, rhs)
    }
    fn transform_binary_op(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, TT, U>,
        rhs: SymValue<'sym, 'tcx, TT, U>,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_bin_op(ty, op, lhs, rhs)
    }
    fn transform_unary_op(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        ty: ty::Ty<'tcx>,
        op: mir::UnOp,
        val: SymValue<'sym, 'tcx, TT, U>,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_unary_op(ty, op, val)
    }
    fn transform_projection(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        elem: ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        val: SymValue<'sym, 'tcx, TT, U>,
    ) -> SymValue<'sym, 'tcx, TT, U>
    where
        TT: SyntheticSymValue<'sym, 'tcx>,
    {
        arena.mk_projection(elem, val)
    }
    fn transform_aggregate(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        kind: AggregateKind<'tcx>,
        vals: &'sym [SymValue<'sym, 'tcx, TT, U>],
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_aggregate(kind, vals)
    }
    fn transform_discriminant(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        val: SymValue<'sym, 'tcx, TT, U>,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_discriminant(val)
    }
    fn transform_cast(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        kind: CastKind,
        val: SymValue<'sym, 'tcx, TT, U>,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_cast(kind, val, ty)
    }
    fn transform_ref(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        val: SymValue<'sym, 'tcx, TT, U>,
        mutability: Mutability,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_ref(val, mutability)
    }

    fn transform_backwards_fn(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        backwards_fn: BackwardsFn<'sym, 'tcx, TT, U>,
    ) -> SymValue<'sym, 'tcx, TT, U> {
        arena.mk_backwards_fn(backwards_fn)
    }
}
