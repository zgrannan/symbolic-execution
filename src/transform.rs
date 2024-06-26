use crate::{rustc_interface::{
    abi::VariantIdx,
    const_eval::interpret::ConstValue,
    data_structures::fx::FxHasher,
    middle::{
        mir::{self, tcx::PlaceTy, ProjectionElem, VarDebugInfo},
        ty,
    },
    span::{def_id::DefId, DUMMY_SP},
}, value::{AggregateKind, CastKind, Constant, SymValue}};
use crate::{context::SymExContext, value::SyntheticSymValue};

pub trait SymValueTransformer<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> {
    fn transform_var(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        idx: usize,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_var(idx, ty)
    }
    fn transform_ref(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        ty: ty::Ty<'tcx>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_ref(ty, val)
    }
    fn transform_constant(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        c: &'sym Constant<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_constant(c.clone())
    }
    fn transform_checked_binary_op(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_checked_bin_op(ty, op, lhs, rhs)
    }
    fn transform_binary_op(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        ty: ty::Ty<'tcx>,
        op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_bin_op(ty, op, lhs, rhs)
    }
    fn transform_unary_op(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        ty: ty::Ty<'tcx>,
        op: mir::UnOp,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_unary_op(ty, op, val)
    }
    fn transform_projection(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        elem: ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_projection(elem, val)
    }
    fn transform_aggregate(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        kind: AggregateKind<'tcx>,
        vals: &'sym [SymValue<'sym, 'tcx, T>],
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_aggregate(kind, vals)
    }
    fn transform_discriminant(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_discriminant(val)
    }
    fn transform_cast(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        kind: CastKind,
        val: SymValue<'sym, 'tcx, T>,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_cast(kind, val, ty)
    }

    fn transform_synthetic(&mut self, arena: &'sym SymExContext<'tcx>, s: T) -> SymValue<'sym, 'tcx, T>;
}
