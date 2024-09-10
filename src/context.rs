use crate::path::SymExPath;
use crate::value::{
    BackwardsFn, CastKind, SymValue, SymValueData, SymValueKind, SyntheticSymValue,
};
use crate::{
    rustc_interface::{
        ast::Mutability,
        hir::def_id::LocalDefId,
        middle::{
            mir::{self, BasicBlock, Location},
            ty::{self, TyCtxt},
        },
    },
    value::{AggregateKind, Constant},
};

#[derive(Debug)]
pub enum ErrorLocation {
    Location(Location),
    TerminatorStart(BasicBlock),
    TerminatorMid(BasicBlock),
}

#[derive(Debug)]
pub struct ErrorContext {
    pub def_id: LocalDefId,
    pub location: ErrorLocation,
    pub path: SymExPath,
}

impl std::fmt::Debug for SymExContext<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymExContext").finish()
    }
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

    pub fn mk_internal_error<'sym, T, V>(
        &'sym self,
        err: String,
        ty: ty::Ty<'tcx>,
        ctx: Option<&ErrorContext>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        let err = if let Some(ctx) = ctx {
            format!(
                "{} {:?} {:?} Internal error: {}",
                self.tcx.def_path_str(ctx.def_id),
                ctx.path,
                ctx.location,
                err
            )
        } else {
            format!("Internal error: {}", err)
        };
        if cfg!(feature = "crash_on_internal_error") {
            panic!("{}", err);
        } else {
            eprintln!("{}", err);
            eprintln!("Stack trace:");
            let backtrace = std::backtrace::Backtrace::capture();
            eprintln!("{}", backtrace);
        }
        self.mk_sym_value(SymValueKind::InternalError(err, ty))
    }

    pub fn mk_discriminant<'sym, T, V>(
        &'sym self,
        val: SymValue<'sym, 'tcx, T, V>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        self.mk_sym_value(SymValueKind::Discriminant(val))
    }

    pub fn mk_sym_value<'sym, T, V>(
        &'sym self,
        kind: SymValueKind<'sym, 'tcx, T, V>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        self.alloc(SymValueData::new(kind, self))
    }

    pub fn mk_cast<'sym, T, V>(
        &'sym self,
        kind: CastKind,
        val: SymValue<'sym, 'tcx, T, V>,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        self.mk_sym_value(SymValueKind::Cast(kind, val, ty))
    }

    pub fn mk_var<'sym, T, V>(&'sym self, var: V, ty: ty::Ty<'tcx>) -> SymValue<'sym, 'tcx, T, V> {
        self.mk_sym_value(SymValueKind::Var(var, ty))
    }

    pub fn mk_constant<'sym, T, V>(&'sym self, c: Constant<'tcx>) -> SymValue<'sym, 'tcx, T, V> {
        self.mk_sym_value(SymValueKind::Constant(c))
    }

    pub fn mk_synthetic<'sym, T, V>(&'sym self, t: T) -> SymValue<'sym, 'tcx, T, V> {
        self.mk_sym_value(SymValueKind::Synthetic(t))
    }

    pub fn mk_backwards_fn<'sym, T, V>(
        &'sym self,
        backwards_fn: BackwardsFn<'sym, 'tcx, T, V>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        self.mk_sym_value(SymValueKind::BackwardsFn(backwards_fn))
    }

    pub fn mk_projection<'sym, T: SyntheticSymValue<'sym, 'tcx>, V>(
        &'sym self,
        kind: mir::ProjectionElem<mir::Local, ty::Ty<'tcx>>,
        val: SymValue<'sym, 'tcx, T, V>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        if let mir::ProjectionElem::Field(idx, _) = kind {
            if let SymValueKind::Aggregate(kind, vals) = &val.kind {
                if let Some(val) = vals.get(idx.as_usize()) {
                    return val;
                }
            }
        }
        // if kind == mir::ProjectionElem::Deref {
        //     let ty = val.kind.ty(self.tcx).rust_ty();
        //     assert!(ty.is_box() || ty.is_ref(), "Deref on non-pointer: {:?}", ty);
        // }
        // TODO: Option to disable this optimization
        if let SymValueKind::Ref(v, _) = val.kind
            && kind == mir::ProjectionElem::Deref
        {
            return v;
        }
        self.mk_sym_value(SymValueKind::Projection(kind, val))
    }

    pub fn mk_ref<'sym, T, V>(
        &'sym self,
        val: SymValue<'sym, 'tcx, T, V>,
        mutability: Mutability,
    ) -> SymValue<'sym, 'tcx, T, V> {
        // TODO: Option to disable this optimization
        if let SymValueKind::Projection(mir::ProjectionElem::Deref, v) = val.kind {
            match &v.kind {
                SymValueKind::Var(_, ty) if ty.ref_mutability() == Some(mutability) => {
                    return v;
                }
                SymValueKind::Ref(v, _) => {
                    return self.mk_ref(v, mutability);
                }
                _ => {}
            }
        }
        self.mk_sym_value(SymValueKind::Ref(val, mutability))
    }

    pub fn mk_aggregate<'sym, T, V>(
        &'sym self,
        kind: AggregateKind<'tcx>,
        vals: &'sym [SymValue<'sym, 'tcx, T, V>],
    ) -> SymValue<'sym, 'tcx, T, V> {
        match kind.ty().rust_ty().kind() {
            // TODO: Option to disable this optimization
            ty::TyKind::Ref(_, _, mutbl) => {
                return self.mk_ref(vals[0], *mutbl);
            }
            _ => {}
        }
        self.mk_sym_value(SymValueKind::Aggregate(kind, vals))
    }

    pub fn mk_bin_op<'sym, T: SyntheticSymValue<'sym, 'tcx>, V>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        bin_op: mir::BinOp,
        lhs: SymValue<'sym, 'tcx, T, V>,
        rhs: SymValue<'sym, 'tcx, T, V>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        match bin_op {
            mir::BinOp::Add
            | mir::BinOp::AddUnchecked
            | mir::BinOp::AddWithOverflow
            | mir::BinOp::Sub
            | mir::BinOp::SubUnchecked
            | mir::BinOp::SubWithOverflow
            | mir::BinOp::Mul
            | mir::BinOp::MulUnchecked
            | mir::BinOp::MulWithOverflow => {
                assert!(!lhs.ty(self.tcx).rust_ty().is_ref());
                assert!(!rhs.ty(self.tcx).rust_ty().is_ref());
            }
            _ => {}
        }

        match (&lhs.kind, &rhs.kind) {
            (SymValueKind::Constant(lhs), SymValueKind::Constant(rhs)) => {
                if lhs.ty() == self.tcx.types.u32 && rhs.ty() == self.tcx.types.u32 {
                    let lhs_u32 = lhs.as_u32(self.tcx).unwrap();
                    let rhs_u32 = rhs.as_u32(self.tcx).unwrap();
                    match bin_op {
                        mir::BinOp::Lt => {
                            return self
                                .mk_constant(Constant::from_bool(self.tcx, lhs_u32 < rhs_u32));
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        self.mk_sym_value(SymValueKind::BinaryOp(ty, bin_op, lhs, rhs))
    }

    pub fn mk_unary_op<'sym, T, V>(
        &'sym self,
        ty: ty::Ty<'tcx>,
        unary_op: mir::UnOp,
        operand: SymValue<'sym, 'tcx, T, V>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        match (&operand.kind, unary_op) {
            (SymValueKind::Constant(c), mir::UnOp::Not) => {
                return self
                    .mk_constant(Constant::from_bool(self.tcx, !c.as_bool(self.tcx).unwrap()));
            }
            _ => {}
        }
        self.mk_sym_value(SymValueKind::UnaryOp(ty, unary_op, operand))
    }

    pub fn mk_not<'sym, T: SyntheticSymValue<'sym, 'tcx>, V>(
        &'sym self,
        operand: SymValue<'sym, 'tcx, T, V>,
    ) -> SymValue<'sym, 'tcx, T, V> {
        self.mk_unary_op(operand.ty(self.tcx).rust_ty(), mir::UnOp::Not, operand)
    }
}
