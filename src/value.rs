use crate::debug_info::DebugInfo;
use crate::place::Place;
use crate::rustc_interface::{
    abi::VariantIdx,
    ast::Mutability,
    const_eval::interpret::ConstValue,
    data_structures::fx::FxHasher,
    middle::{
        mir::{self, tcx::PlaceTy, ProjectionElem, VarDebugInfo, PlaceElem},
        ty::{self, GenericArgsRef},
    },
    span::{def_id::DefId, DUMMY_SP},
};
use crate::transform::SymValueTransformer;
use crate::visualization::OutputMode;

use std::{
    cmp::Ordering,
    collections::BTreeMap,
    hash::{Hash, Hasher},
    rc::Rc,
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

impl<'tcx> From<PlaceTy<'tcx>> for Ty<'tcx> {
    fn from(ty: PlaceTy<'tcx>) -> Self {
        Ty(ty.ty, ty.variant_index)
    }
}

pub trait SyntheticSymValue<'sym, 'tcx>: Sized {
    fn optimize(self, arena: &'sym SymExContext<'tcx>, tcx: ty::TyCtxt<'tcx>) -> Self;
    fn subst(
        self,
        arena: &'sym SymExContext<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        substs: &Substs<'sym, 'tcx, Self>,
    ) -> Self;
    fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx>;
}

pub type SymValue<'sym, 'tcx, T> = &'sym SymValueData<'sym, 'tcx, T>;

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct SymValueData<'sym, 'tcx, T> {
    pub kind: SymValueKind<'sym, 'tcx, T>,
    pub debug_info: DebugInfo<'sym>,
}

#[derive(Copy, Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum CastKind {
    IntToInt,
}

impl From<mir::CastKind> for CastKind {
    fn from(value: mir::CastKind) -> Self {
        match value {
            mir::CastKind::IntToInt => CastKind::IntToInt,
            _ => todo!(),
        }
    }
}

#[derive(Copy, Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct BackwardsFn<'sym, 'tcx, T> {
    /// The DefId of the Rust (forwards) function
    pub def_id: DefId,

    pub substs: GenericArgsRef<'tcx>,

    pub caller_def_id: Option<DefId>,

    /// Snapshots of the values when the forwards function was called
    pub arg_snapshots: &'sym [SymValue<'sym, 'tcx, T>],

    /// The snapshot of the returned value of the function at the point it
    /// expires
    pub return_snapshot: SymValue<'sym, 'tcx, T>,

    /// The index of the argument that the backwards function is for. For
    /// example, if the `arg_index` is `i` then backwards_fn(f, args, res, i)
    /// returns the value of the `i`th element of `args` at the point when the
    /// result of `f` expires with value `res`.
    pub arg_index: usize,
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> BackwardsFn<'sym, 'tcx, T> {
    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        self.arg_snapshots[self.arg_index].kind.ty(tcx)
    }
}

#[derive(Copy, Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum SymVar {
    Normal(usize),

    /// The final `result` value that is applied to a backwards function
    /// For a function that returns an `&mut T`, this should be of type `T`
    ReservedBackwardsFnResult,
}

fn format_as_sym(value: impl std::fmt::Display, output_mode: OutputMode) -> String {
    format!("α{}", output_mode.subscript(value))
}

impl SymVar {
    pub fn to_string(&self, debug_info: &[VarDebugInfo], output_mode: OutputMode) -> String {
        match self {
            SymVar::Normal(idx) => {
                let info = debug_info.iter().find(|d| {
                    d.argument_index
                        .map_or(false, |arg_idx| arg_idx == (*idx + 1) as u16)
                });
                if let Some(info) = info {
                    format_as_sym(info.name, output_mode)
                } else {
                    format_as_sym(idx, output_mode)
                }
            }
            SymVar::ReservedBackwardsFnResult => format_as_sym("result", output_mode),
        }
    }
}

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum SymValueKind<'sym, 'tcx, T> {
    Var(SymVar, ty::Ty<'tcx>),
    Constant(Constant<'tcx>),
    CheckedBinaryOp(
        ty::Ty<'tcx>,
        mir::BinOp,
        SymValue<'sym, 'tcx, T>,
        SymValue<'sym, 'tcx, T>,
    ),
    BinaryOp(
        ty::Ty<'tcx>,
        mir::BinOp,
        SymValue<'sym, 'tcx, T>,
        SymValue<'sym, 'tcx, T>,
    ),
    UnaryOp(ty::Ty<'tcx>, mir::UnOp, SymValue<'sym, 'tcx, T>),
    Projection(PlaceElem<'tcx>, SymValue<'sym, 'tcx, T>),
    Ref(SymValue<'sym, 'tcx, T>, Mutability),
    Aggregate(AggregateKind<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
    Discriminant(SymValue<'sym, 'tcx, T>),
    Cast(CastKind, SymValue<'sym, 'tcx, T>, ty::Ty<'tcx>),
    Synthetic(T),
    InternalError(String, ty::Ty<'tcx>),
    BackwardsFn(BackwardsFn<'sym, 'tcx, T>),
}

pub trait ToSymVar {
    fn to_symvar(self) -> SymVar;
}

impl ToSymVar for SymVar {
    fn to_symvar(self) -> SymVar {
        self
    }
}

impl ToSymVar for usize {
    fn to_symvar(self) -> SymVar {
        SymVar::Normal(self)
    }
}

#[derive(Debug)]
pub struct Substs<'sym, 'tcx, T>(BTreeMap<SymVar, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T> Substs<'sym, 'tcx, T> {
    pub fn from_iter(iter: impl Iterator<Item = (impl ToSymVar, SymValue<'sym, 'tcx, T>)>) -> Self {
        Substs(iter.map(|(k, v)| (k.to_symvar(), v)).collect())
    }
    pub fn get(&self, idx: &SymVar) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0.get(idx).copied()
    }
    pub fn singleton(idx: impl ToSymVar, val: SymValue<'sym, 'tcx, T>) -> Self {
        Substs(std::iter::once((idx.to_symvar(), val)).collect())
    }
}

impl<'sym, 'tcx, T: Copy + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug> std::fmt::Display for Substs<'sym, 'tcx, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in self.0.iter() {
            writeln!(f, "{:?}: {:?}", k, v.kind)?;
        }
        Ok(())
    }
}

impl<'sym, 'tcx, T: Copy + SyntheticSymValue<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn apply_transformer<F>(
        &'sym self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut F,
    ) -> SymValue<'sym, 'tcx, T>
    where
        F: SymValueTransformer<'sym, 'tcx, T>,
    {
        match &self.kind {
            SymValueKind::Var(var, ty) => transformer.transform_var(arena, *var, *ty),
            SymValueKind::Constant(c) => transformer.transform_constant(arena, c),
            SymValueKind::CheckedBinaryOp(ty, op, lhs, rhs) => {
                let transformed_lhs = lhs.apply_transformer(arena, transformer);
                let transformed_rhs = rhs.apply_transformer(arena, transformer);
                transformer.transform_checked_binary_op(
                    arena,
                    *ty,
                    *op,
                    transformed_lhs,
                    transformed_rhs,
                )
            }
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
                let transformed_vals: Vec<SymValue<'sym, 'tcx, T>> = vals
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
            SymValueKind::InternalError(_, _) => self,
            SymValueKind::Ref(val, mutability) => {
                let transformed_val = val.apply_transformer(arena, transformer);
                transformer.transform_ref(arena, transformed_val, *mutability)
            }
            SymValueKind::BackwardsFn(backwards_fn) => {
                transformer.transform_backwards_fn(arena, *backwards_fn)
            }
        }
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> SymValueKind<'sym, 'tcx, T> {
    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            SymValueKind::Var(_, ty, ..) => Ty::new(*ty, None),
            SymValueKind::Constant(c) => Ty::new(c.ty(), None),
            SymValueKind::CheckedBinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValueKind::BinaryOp(ty, _, _, _) => Ty::new(*ty, None),
            SymValueKind::Projection(elem, val) => match elem {
                ProjectionElem::Deref => {
                    let ty = val.kind.ty(tcx);
                    match ty.rust_ty().kind() {
                        ty::TyKind::Bool => panic!(),
                        ty::TyKind::Char => panic!(),
                        ty::TyKind::Int(_) => panic!(),
                        ty::TyKind::Uint(_) => panic!(),
                        ty::TyKind::Float(_) => panic!(),
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
                        ty::TyKind::Foreign(_) => todo!(),
                        ty::TyKind::Str => todo!(),
                        ty::TyKind::Array(_, _) => todo!(),
                        ty::TyKind::Slice(_) => todo!(),
                        ty::TyKind::RawPtr(_) => todo!(),
                        ty::TyKind::Ref(_, target_ty, _) => Ty::new(*target_ty, ty.variant_index()),
                        ty::TyKind::FnDef(_, _) => todo!(),
                        ty::TyKind::FnPtr(_) => todo!(),
                        ty::TyKind::Dynamic(_, _, _) => todo!(),
                        ty::TyKind::Closure(_, _) => todo!(),
                        ty::TyKind::Generator(_, _, _) => todo!(),
                        ty::TyKind::GeneratorWitness(_) => todo!(),
                        ty::TyKind::GeneratorWitnessMIR(_, _) => todo!(),
                        ty::TyKind::Never => todo!(),
                        ty::TyKind::Tuple(_) => todo!(),
                        ty::TyKind::Alias(_, _) => todo!(),
                        ty::TyKind::Param(_) => todo!(),
                        ty::TyKind::Bound(_, _) => todo!(),
                        ty::TyKind::Placeholder(_) => todo!(),
                        ty::TyKind::Infer(_) => todo!(),
                        ty::TyKind::Error(_) => ty,
                    }
                }
                ProjectionElem::Field(_, ty) => Ty::new(*ty, None),
                ProjectionElem::Index(_) => todo!(),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                ProjectionElem::Subslice { from, to, from_end } => todo!(),
                ProjectionElem::Downcast(_, vidx) => {
                    Ty::new(val.kind.ty(tcx).rust_ty(), Some(*vidx))
                }
                ProjectionElem::OpaqueCast(_) => todo!(),
            },
            SymValueKind::Aggregate(kind, _) => kind.ty(),
            SymValueKind::Discriminant(sym_val) => {
                Ty::new(sym_val.kind.ty(tcx).rust_ty().discriminant_ty(tcx), None)
            }
            SymValueKind::UnaryOp(ty, op, val) => Ty::new(*ty, None),
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

impl<'substs, 'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug>
    SymValueTransformer<'sym, 'tcx, T> for SubstsTransformer<'substs, 'sym, 'tcx, T>
{
    fn transform_var(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        var: SymVar,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        let subst = self.1.get(&var);
        if let Some(val) = subst {
            assert_eq!(
                self.0.erase_regions(val.kind.ty(self.0).rust_ty()),
                self.0.erase_regions(ty),
                "Cannot subst {var:?}: {:?} with {val:?}: {:?} of different type",
                ty,
                val.kind.ty(self.0),
            );
            val
        } else {
            arena.mk_var(var, ty)
        }
    }

    fn transform_synthetic(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        s: T,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_synthetic(s.subst(arena, self.0, self.1))
    }
}

impl<'sym, 'tcx, T: Clone + Copy + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>>
    SymValueData<'sym, 'tcx, T>
{
    pub fn subst<'substs>(
        &'sym self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.apply_transformer(arena, &mut SubstsTransformer(arena.tcx, substs))
    }
}

struct OptimizingTransformer<'tcx>(ty::TyCtxt<'tcx>);

impl<'sym, 'tcx, T: Clone + Copy + SyntheticSymValue<'sym, 'tcx>> SymValueTransformer<'sym, 'tcx, T>
    for OptimizingTransformer<'tcx>
{
    fn transform_synthetic(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        s: T,
    ) -> SymValue<'sym, 'tcx, T> {
        arena.mk_synthetic(s.optimize(arena, self.0))
    }
}

impl<'sym, 'tcx, T: Clone + Copy + SyntheticSymValue<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn optimize(
        &'sym self,
        arena: &'sym SymExContext<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        self.apply_transformer(arena, &mut OptimizingTransformer(tcx))
    }
}

impl<'tcx> From<&Box<mir::Constant<'tcx>>> for Constant<'tcx> {
    fn from(c: &Box<mir::Constant<'tcx>>) -> Self {
        Constant(**c)
    }
}

impl<'tcx> From<mir::Constant<'tcx>> for Constant<'tcx> {
    fn from(c: mir::Constant<'tcx>) -> Self {
        Constant(c)
    }
}

#[derive(Clone, Debug, Hash)]
pub struct Constant<'tcx>(pub mir::Constant<'tcx>);

impl<'tcx> Constant<'tcx> {
    pub fn literal(&self) -> mir::ConstantKind<'tcx> {
        self.0.literal
    }

    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.0.literal.ty()
    }

    pub fn from_bool(tcx: ty::TyCtxt<'tcx>, b: bool) -> Self {
        Constant(mir::Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: mir::ConstantKind::from_bool(tcx, b),
        })
    }
    pub fn from_u32(u32: u32, ty: ty::Ty<'tcx>) -> Self {
        Constant(mir::Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: mir::ConstantKind::from_value(ConstValue::from_u64(u32 as u64), ty),
        })
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
