use crate::value::{CastKind, SymValue, SymValueData, SymValueKind, SyntheticSymValue};
use crate::{
    rustc_interface::{
        ast::Mutability,
        borrowck::consumers::BodyWithBorrowckFacts,
        hir::def_id::{DefId, LocalDefId},
        middle::{
            mir::{self, BasicBlock, Body, Location, VarDebugInfo},
            ty::{self, GenericArgsRef, TyCtxt},
        },
    },
    value::{AggregateKind, Constant},
};

#[derive(Debug)]
pub enum ErrorLocation {
    Location(Location),
    Terminator(BasicBlock),
}

pub struct ErrorContext {
    pub def_id: LocalDefId,
    pub location: ErrorLocation,
}

pub struct SymExContext<'tcx> {
    bump: bumpalo::Bump,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> SymExContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            bump: bumpalo::Bump::new(),
            tcx,
        }
    }

    pub fn alloc<T>(&self, t: T) -> &T {
        self.bump.alloc(t)
    }

    pub fn alloc_slice<T: Copy>(&self, t: &[T]) -> &[T] {
        self.bump.alloc_slice_copy(t)
    }

    pub fn mk_internal_error<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        err: String,
        ty: ty::Ty<'tcx>,
        ctx: &ErrorContext,
    ) -> SymValue<'sym, 'tcx, T> {
        let err = format!(
            "{:?} {:?} Internal error: {}",
            ctx.def_id, ctx.location, err
        );
        if cfg!(feature = "crash_on_internal_error") {
            panic!("{}", err);
        } else {
            eprintln!("{}", err);
        }
        self.mk_sym_value(SymValueKind::InternalError(err, ty))
    }

    pub fn mk_discriminant<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Discriminant(val))
    }

    pub fn mk_sym_value<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: SymValueKind<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.alloc(SymValueData::new(kind, self))
    }

    pub fn mk_cast<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: CastKind,
        val: SymValue<'sym, 'tcx, T>,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Cast(kind, val, ty))
    }

    pub fn mk_var<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        idx: usize,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Var(idx, ty))
    }

    pub fn mk_constant<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        c: Constant<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Constant(c))
    }

    pub fn mk_synthetic<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        t: T,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Synthetic(t))
    }

    pub fn mk_projection<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: mir::ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        val: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        match kind {
            mir::ProjectionElem::Field(_, _) => {
                if val.kind.ty(self.tcx).rust_ty().is_enum() {
                    // assert!(
                    //     val.kind.ty(self.tcx).variant_index().is_some(),
                    //     "Enum value must have a variant index set"
                    // );
                }
            }
            _ => {}
        }
        self.mk_sym_value(SymValueKind::Projection(kind, val))
    }

    pub fn mk_ref<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        val: SymValue<'sym, 'tcx, T>,
        mutability: Mutability,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Ref(val, mutability))
    }

    pub fn mk_aggregate<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        kind: AggregateKind<'tcx>,
        vals: &'sym [SymValue<'sym, 'tcx, T>],
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::Aggregate(kind, vals))
    }

    pub fn mk_bin_op<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        bin_op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::BinaryOp(ty, bin_op, lhs, rhs))
    }

    pub fn mk_checked_bin_op<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        bin_op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T>,
        rhs: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        // assert_eq!(
        //     lhs.kind.ty(self.tcx).rust_ty(),
        //     rhs.kind.ty(self.tcx).rust_ty()
        // );
        self.mk_sym_value(SymValueKind::CheckedBinaryOp(ty, bin_op, lhs, rhs))
    }

    pub fn mk_unary_op<'sym, T: SyntheticSymValue<'sym, 'tcx>>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        unary_op: mir::UnOp,
        operand: SymValue<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.mk_sym_value(SymValueKind::UnaryOp(ty, unary_op, operand))
    }
}
