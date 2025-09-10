use crate::debug_info::DebugInfo;

use crate::rustc_interface::{
    abi::VariantIdx,
    ast::Mutability,
    data_structures::fx::FxHasher,
    middle::{
        mir::{self, ConstValue, PlaceElem, ProjectionElem, VarDebugInfo},
        ty::{self, GenericArgsRef},
    },
    span::def_id::DefId,
};
use crate::transform::{BaseSymValueTransformer, SymValueTransformer};
use crate::visualization::OutputMode;

use std::{
    cmp::Ordering,
    collections::BTreeMap,
    hash::{Hash, Hasher},
};

use super::SymExContext;

#[derive(Copy, Debug, Clone, Hash, Eq, PartialEq)]
pub struct Ty<'tcx>(ty::Ty<'tcx>, Option<VariantIdx>);

impl<'tcx> std::fmt::Display for Ty<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)?;
        if let Some(variant_index) = self.1 {
            write!(f, "@{:?}", variant_index)?;
        }
        Ok(())
    }
}

impl<'tcx> Ty<'tcx> {
    pub fn new(ty: ty::Ty<'tcx>, variant_index: Option<VariantIdx>) -> Self {
        Ty(ty, variant_index)
    }
    pub fn variant_index(&self) -> Option<VariantIdx> {
        self.1
    }
    pub fn rust_ty(&self) -> ty::Ty<'tcx> {
        self.0
    }
}

impl<'tcx> From<mir::PlaceTy<'tcx>> for Ty<'tcx> {
    fn from(ty: mir::PlaceTy<'tcx>) -> Self {
        Ty(ty.ty, ty.variant_index)
    }
}

pub trait CanSubst<'sym, 'tcx>: Sized {
    fn subst(
        self,
        arena: &'sym SymExContext<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        substs: &Substs<'sym, 'tcx, Self>,
    ) -> Self;
}

pub trait SyntheticSymValue<'sym, 'tcx>: Sized {
    fn optimize(self, arena: &'sym SymExContext<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Self;
    fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx>;
}

pub type SymValue<'sym, 'tcx, T, V = SymVar> = &'sym SymValueData<'sym, 'tcx, T, V>;

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct SymValueData<'sym, 'tcx, T, V = SymVar> {
    pub kind: SymValueKind<'sym, 'tcx, T, V>,
    pub debug_info: DebugInfo<'sym>,
}

#[derive(Copy, Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum CastKind {
    IntToInt,
    PointerCoercion,
}

impl From<mir::CastKind> for CastKind {
    fn from(value: mir::CastKind) -> Self {
        match value {
            mir::CastKind::IntToInt => CastKind::IntToInt,
            mir::CastKind::PointerCoercion(..) => CastKind::PointerCoercion,
            other => todo!("{:?}", other),
        }
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct BackwardsFn<'sym, 'tcx, T, V = SymVar> {
    /// The DefId of the Rust (forwards) function
    def_id: DefId,

    pub substs: GenericArgsRef<'tcx>,

    pub caller_def_id: Option<DefId>,

    /// Snapshots of the values when the forwards function was called
    pub arg_snapshots: &'sym [SymValue<'sym, 'tcx, T, V>],

    /// The snapshot of the returned value of the function at the point it
    /// expires
    pub return_snapshot: SymValue<'sym, 'tcx, T, V>,

    /// The the argument that the backwards function is for. For example, if the
    /// `arg` is `i` then backwards_fn(f, args, res, i) returns the value of the
    /// `i`th element of `args` at the point when the result of `f` expires with
    /// value `res`.
    pub arg: mir::Local,
}
impl<'sym, 'tcx, T, V> BackwardsFn<'sym, 'tcx, T, V> {
    pub fn def_id(&self) -> DefId {
        self.def_id
    }
    pub fn arg_index(&self) -> usize {
        self.arg.as_usize() - 1
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>, V> BackwardsFn<'sym, 'tcx, T, V> {
    pub fn new(
        tcx: ty::TyCtxt<'tcx>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        caller_def_id: Option<DefId>,
        arg_snapshots: &'sym [SymValue<'sym, 'tcx, T, V>],
        return_snapshot: SymValue<'sym, 'tcx, T, V>,
        arg: mir::Local,
    ) -> Self {
        assert!(
            !arg_snapshots[arg.as_usize() - 1].is_primitive(tcx),
            "Shouln't construct backwards fn for {}'th arg of {:?} with ty {:?}",
            arg.as_usize() - 1,
            def_id,
            arg_snapshots[arg.as_usize() - 1].kind.ty(tcx)
        );
        BackwardsFn {
            def_id,
            substs,
            caller_def_id,
            arg_snapshots,
            return_snapshot,
            arg
        }
    }
    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        self.arg_snapshots[self.arg_index()].kind.ty(tcx)
    }
}

impl<
        'sym,
        'tcx,
        T: Copy + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug,
        V: Copy + std::fmt::Debug,
    > BackwardsFn<'sym, 'tcx, T, V>
{
    pub fn apply_transformer<U: Copy, F, TT>(
        &'sym self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut F,
    ) -> BackwardsFn<'sym, 'tcx, TT, U>
    where
        F: SymValueTransformer<'sym, 'tcx, T, V, U, TT>,
        TT: SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug,
        U: std::fmt::Debug,
    {
        BackwardsFn {
            def_id: self.def_id,
            substs: self.substs,
            caller_def_id: self.caller_def_id,
            arg_snapshots: arena.alloc_slice(
                &self
                    .arg_snapshots
                    .iter()
                    .map(|v| v.apply_transformer(arena, transformer))
                    .collect::<Vec<_>>(),
            ),
            return_snapshot: self.return_snapshot.apply_transformer(arena, transformer),
            arg: self.arg,
        }
    }
}

#[derive(Copy, Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum SymVar {
    Input(mir::Local),
    Fresh(usize),

    /// The final `result` value that is applied to a backwards function
    /// For a function that returns an `&mut T`, this should be of type `T`
    ReservedBackwardsFnResult,
}

fn format_as_sym(value: impl std::fmt::Display, output_mode: OutputMode) -> String {
    format!("α{}", output_mode.subscript(value))
}

impl SymVar {
    pub fn nth_input(n: usize) -> Self {
        SymVar::Input(mir::Local::from_usize(n + 1))
    }

    pub fn to_string(&self, debug_info: &[VarDebugInfo], output_mode: OutputMode) -> String {
        match self {
            SymVar::Input(local) => {
                let info = debug_info.iter().find(|d| {
                    d.argument_index
                        .map_or(false, |arg_idx| arg_idx == local.as_usize() as u16)
                });
                if let Some(info) = info {
                    format_as_sym(info.name, output_mode)
                } else {
                    format_as_sym(format!("{:?}", local), output_mode)
                }
            }
            SymVar::Fresh(idx) => format_as_sym(idx, output_mode),
            SymVar::ReservedBackwardsFnResult => format_as_sym("result", output_mode),
        }
    }
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum SymValueKind<'sym, 'tcx, T, V = SymVar> {
    Var(V, ty::Ty<'tcx>),
    Constant(Constant<'tcx>),
    BinaryOp(
        ty::Ty<'tcx>,
        mir::BinOp,
        SymValue<'sym, 'tcx, T, V>,
        SymValue<'sym, 'tcx, T, V>,
    ),
    UnaryOp(ty::Ty<'tcx>, mir::UnOp, SymValue<'sym, 'tcx, T, V>),
    Projection(PlaceElem<'tcx>, SymValue<'sym, 'tcx, T, V>),
    Ref(SymValue<'sym, 'tcx, T, V>, Mutability),
    Aggregate(AggregateKind<'tcx>, &'sym [SymValue<'sym, 'tcx, T, V>]),
    Discriminant(SymValue<'sym, 'tcx, T, V>),
    Cast(CastKind, SymValue<'sym, 'tcx, T, V>, ty::Ty<'tcx>),
    Synthetic(T),
    InternalError(String, ty::Ty<'tcx>),
    BackwardsFn(BackwardsFn<'sym, 'tcx, T, V>),
}

#[derive(Debug)]
pub struct Substs<'sym, 'tcx, T>(BTreeMap<SymVar, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T> Substs<'sym, 'tcx, T> {
    pub fn from_iter(iter: impl Iterator<Item = (SymVar, SymValue<'sym, 'tcx, T>)>) -> Self {
        Substs(iter.collect())
    }
    pub fn get(&self, idx: &SymVar) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0.get(idx).copied()
    }
    pub fn singleton(idx: SymVar, val: SymValue<'sym, 'tcx, T>) -> Self {
        Substs(std::iter::once((idx, val)).collect())
    }
}

impl<'sym, 'tcx, T: Copy + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug> std::fmt::Display
    for Substs<'sym, 'tcx, T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in self.0.iter() {
            writeln!(f, "{:?}: {:?}", k, v.kind)?;
        }
        Ok(())
    }
}
impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>, V> SymValueData<'sym, 'tcx, T, V> {
    pub fn is_primitive(&self, tcx: ty::TyCtxt<'tcx>) -> bool {
        self.kind.ty(tcx).rust_ty().is_primitive()
    }
}

impl<
        'sym,
        'tcx,
        T: Copy + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug,
        V: Copy + std::fmt::Debug,
    > SymValueData<'sym, 'tcx, T, V>
{
    pub fn apply_transformer<U: Copy, F, TT>(
        &'sym self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut F,
    ) -> SymValue<'sym, 'tcx, TT, U>
    where
        F: SymValueTransformer<'sym, 'tcx, T, V, U, TT>,
        TT: SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug,
        U: std::fmt::Debug,
    {
        match &self.kind {
            SymValueKind::Var(var, ty) => transformer.transform_var(arena, *var, *ty),
            SymValueKind::Constant(c) => transformer.transform_constant(arena, c),
            SymValueKind::BinaryOp(ty, op, lhs, rhs) => {
                let transformed_lhs = lhs.apply_transformer(arena, transformer);
                let transformed_rhs = rhs.apply_transformer(arena, transformer);
                transformer.transform_binary_op(arena, *ty, *op, transformed_lhs, transformed_rhs)
            }
            SymValueKind::UnaryOp(ty, op, val) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_unary_op(arena, *ty, *op, transformed_val)
            }
            SymValueKind::Projection(elem, val) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_projection(arena, *elem, transformed_val)
            }
            SymValueKind::Aggregate(kind, vals) => {
                let transformed_vals: Vec<SymValue<'sym, 'tcx, TT, U>> = vals
                    .iter()
                    .map(|v| v.apply_transformer(arena, transformer))
                    .collect();
                transformer.transform_aggregate(
                    arena,
                    kind.clone(),
                    arena.alloc_slice(&transformed_vals),
                )
            }
            SymValueKind::Discriminant(val) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_discriminant(arena, transformed_val)
            }
            SymValueKind::Synthetic(s) => transformer.transform_synthetic(arena, *s),
            SymValueKind::Cast(kind, val, ty) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_cast(arena, *kind, transformed_val, *ty)
            }
            SymValueKind::InternalError(err, ty) => arena.mk_internal_error(err.clone(), *ty, None),
            SymValueKind::Ref(val, mutability) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_ref(arena, transformed_val, *mutability)
            }
            SymValueKind::BackwardsFn(backwards_fn) => {
                let backwards_fn = backwards_fn.apply_transformer(arena, transformer);
                transformer.transform_backwards_fn(arena, backwards_fn)
            }
        }
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>, V> SymValueKind<'sym, 'tcx, T, V> {
    pub fn as_bool(&self, tcx: ty::TyCtxt<'tcx>) -> Option<bool> {
        match self {
            SymValueKind::Constant(c) => c.as_bool(tcx),
            _ => None,
        }
    }

    pub fn is_true(&self, tcx: ty::TyCtxt<'tcx>) -> bool {
        self.as_bool(tcx).unwrap_or(false)
    }

    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            SymValueKind::Var(_, ty, ..) => Ty::new(*ty, None),
            SymValueKind::Constant(c) => Ty::new(c.ty(), None),
            SymValueKind::BinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValueKind::Projection(elem, val) => match elem {
                ProjectionElem::Deref => {
                    let ty = val.kind.ty(tcx);
                    match ty.rust_ty().kind() {
                        ty::TyKind::Adt(def, substs) => {
                            if let Some(box_def_id) = tcx.lang_items().owned_box() {
                                if def.did() == box_def_id {
                                    Ty::new(substs.type_at(0), None)
                                } else {
                                    panic!()
                                }
                            } else {
                                panic!()
                            }
                        }
                        ty::TyKind::Ref(_, target_ty, _) => Ty::new(*target_ty, ty.variant_index()),
                        _ => todo!(),
                    }
                }
                ProjectionElem::Field(_, ty) => Ty::new(*ty, None),
                ProjectionElem::Downcast(_, vidx) => {
                    Ty::new(val.kind.ty(tcx).rust_ty(), Some(*vidx))
                }
                _ => todo!(),
            },
            SymValueKind::Aggregate(kind, _) => kind.ty(),
            SymValueKind::Discriminant(sym_val) => {
                Ty::new(sym_val.kind.ty(tcx).rust_ty().discriminant_ty(tcx), None)
            }
            SymValueKind::UnaryOp(ty, _op, _val) => Ty::new(*ty, None),
            SymValueKind::Synthetic(sym_val) => sym_val.ty(tcx),
            SymValueKind::Cast(_, _, ty) => Ty::new(*ty, None),
            SymValueKind::InternalError(_, ty) => Ty::new(*ty, None),
            SymValueKind::Ref(val, mutability) => {
                let base_ty = val.kind.ty(tcx).rust_ty();
                let ty = tcx.mk_ty_from_kind(ty::TyKind::Ref(
                    tcx.lifetimes.re_erased,
                    base_ty,
                    *mutability,
                ));
                Ty::new(ty, None)
            }
            SymValueKind::BackwardsFn(backwards_fn) => backwards_fn.ty(tcx),
        }
    }
}

struct SubstsTransformer<'substs, 'sym, 'tcx, T>(ty::TyCtxt<'tcx>, &'substs Substs<'sym, 'tcx, T>);

impl<
        'substs,
        'sym,
        'tcx,
        T: SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx> + std::fmt::Debug,
    > SymValueTransformer<'sym, 'tcx, T> for SubstsTransformer<'substs, 'sym, 'tcx, T>
{
    fn transform_synthetic(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        s: T,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_synthetic(s.subst(arena, self.0, self.1))
    }
}

impl<
        'substs,
        'sym,
        'tcx,
        T: SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx> + std::fmt::Debug,
    > BaseSymValueTransformer<'sym, 'tcx, T> for SubstsTransformer<'substs, 'sym, 'tcx, T>
{
    fn transform_var(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        var: SymVar,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        let subst = self.1.get(&var);
        if let Some(val) = subst {
            // assert_eq!(
            //     self.0.erase_regions(val.kind.ty(self.0).rust_ty()),
            //     self.0.erase_regions(ty),
            //     "Cannot subst {:?}: {:?} with {:?}: {:?} of different type",
            //     var,
            //     ty,
            //     val,
            //     val.kind.ty(self.0),
            // );
            val
        } else {
            arena.mk_var(var, ty)
        }
    }
}

impl<
        'sym,
        'tcx,
        T: Clone + Copy + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > SymValueData<'sym, 'tcx, T>
{
    pub fn subst<'substs>(
        &'sym self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.apply_transformer(arena, &mut SubstsTransformer(arena.tcx, substs))
    }
}

// struct OptimizingTransformer<'tcx>(ty::TyCtxt<'tcx>);

// impl<'sym, 'tcx, T: Clone + Copy + SyntheticSymValue<'sym, 'tcx>> SymValueTransformer<'sym, 'tcx, T>
//     for OptimizingTransformer<'tcx>
// {
//     fn transform_var(
//         &mut self,
//         arena: &'sym SymExContext<'tcx>,
//         var: SymVar,
//         ty: ty::Ty<'tcx>,
//     ) -> SymValue<'sym, 'tcx, T> {
//         arena.mk_var(var, ty)
//     }
//     fn transform_synthetic(
//         &mut self,
//         arena: &'sym SymExContext<'tcx>,
//         s: T,
//     ) -> SymValue<'sym, 'tcx, T> {
//         arena.mk_synthetic(s.optimize(arena, self.0))
//     }
// }

// impl<'sym, 'tcx, T: Clone + Copy + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug>
//     SymValueData<'sym, 'tcx, T>
// {
//     pub fn optimize(
//         &'sym self,
//         arena: &'sym SymExContext<'tcx>,
//         tcx: ty::TyCtxt<'tcx>,
//     ) -> SymValue<'sym, 'tcx, T> {
//         self.apply_transformer(arena, &mut OptimizingTransformer(tcx))
//     }
// }

impl<'tcx> From<&Box<mir::Const<'tcx>>> for Constant<'tcx> {
    fn from(c: &Box<mir::Const<'tcx>>) -> Self {
        Constant(**c)
    }
}

impl<'tcx> From<mir::Const<'tcx>> for Constant<'tcx> {
    fn from(c: mir::Const<'tcx>) -> Self {
        Constant(c)
    }
}

#[derive(Clone, Debug, Hash)]
pub struct Constant<'tcx>(pub mir::Const<'tcx>);

impl<'tcx> Constant<'tcx> {
    pub fn as_bool(&self, tcx: ty::TyCtxt<'tcx>) -> Option<bool> {
        if self.ty() == tcx.types.bool {
            self.0.try_to_bool()
        } else {
            None
        }
    }

    pub fn as_u32(&self, tcx: ty::TyCtxt<'tcx>) -> Option<u32> {
        if self.ty() == tcx.types.u32 {
            let scalar_int = self.0.try_to_scalar_int()?;
            Some(scalar_int.to_u32())
        } else {
            None
        }
    }

    pub fn literal(&self) -> mir::Const<'tcx> {
        self.0
    }

    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.literal().ty()
    }

    pub fn from_bool(tcx: ty::TyCtxt<'tcx>, b: bool) -> Self {
        Constant(mir::Const::from_bool(tcx, b))
    }
    pub fn from_u32(u32: u32, ty: ty::Ty<'tcx>) -> Self {
        Constant(mir::Const::from_value(ConstValue::from_u64(u32 as u64), ty))
    }
}

impl<'tcx> Ord for Constant<'tcx> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(&other).unwrap()
    }
}

impl<'tcx> Eq for Constant<'tcx> {}

fn hash<T: Hash>(t: T) -> u64 {
    let mut hasher = FxHasher::default();
    t.hash(&mut hasher);
    hasher.finish()
}

impl<'tcx> PartialEq for Constant<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        hash(self) == hash(other)
    }
}

impl<'tcx> PartialOrd for Constant<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        hash(self).partial_cmp(&hash(other))
    }
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum AggregateKind<'tcx> {
    Rust(mir::AggregateKind<'tcx>, ty::Ty<'tcx>),
    PCS(ty::Ty<'tcx>, Option<VariantIdx>),
}

impl<'tcx> AggregateKind<'tcx> {
    pub fn pcs(ty: ty::Ty<'tcx>, variant_idx: Option<VariantIdx>) -> Self {
        AggregateKind::PCS(ty, variant_idx)
    }
    pub fn rust(kind: mir::AggregateKind<'tcx>, ty: ty::Ty<'tcx>) -> Self {
        AggregateKind::Rust(kind, ty)
    }

    pub fn variant_idx(&self) -> Option<VariantIdx> {
        self.ty().variant_index()
    }

    pub fn is_enum(&self, tcx: ty::TyCtxt<'tcx>) -> bool {
        self.def_id()
            .map_or(false, |def_id| tcx.adt_def(def_id).variants().len() > 1)
    }

    pub fn ty(&self) -> Ty<'tcx> {
        match self {
            AggregateKind::Rust(mir::AggregateKind::Adt(_, idx, ..), ty) => {
                Ty::new(*ty, Some(*idx))
            }
            AggregateKind::Rust(_, ty) => Ty::new(*ty, None),
            AggregateKind::PCS(ty, variant_idx) => Ty::new(*ty, *variant_idx),
        }
    }

    pub fn def_id(&self) -> Option<DefId> {
        match self {
            AggregateKind::Rust(mir::AggregateKind::Adt(def_id, ..), _) => Some(*def_id),
            AggregateKind::PCS(ty, _) => match ty.kind() {
                ty::TyKind::Adt(adt_def, _) => Some(adt_def.did()),
                _ => None,
            },
            _ => None,
        }
    }
}

impl<'tcx> PartialOrd for AggregateKind<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        hash(self).partial_cmp(&hash(other))
    }
}

impl<'tcx> Ord for AggregateKind<'tcx> {
    fn cmp(&self, other: &Self) -> Ordering {
        hash(self).partial_cmp(&hash(other)).unwrap()
    }
}
