use serde_json::Value;

use crate::{
    transform::SymValueTransformer, value::CanSubst, visualization::OutputMode, Assertion, VisFormat
};

use super::{
    value::{Substs, SymValue, SyntheticSymValue},
    SymExContext,
};
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::VarDebugInfo,
        ty::{self, GenericArgsRef, TyCtxt, TyKind},
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PathConditionPredicate<'sym, 'tcx, T> {
    /// The compared-to expr is equal to the scalar interpreted as a
    /// value of the given type
    Eq(u128, ty::Ty<'tcx>),
    /// The compared-to expr is not equal to any of the scalars
    /// interpreted as a value of the given type
    Ne(Vec<u128>, ty::Ty<'tcx>),
    /// The postcondition of the function defined by the DefId, applied to the arguments
    /// The compared-to expr is the result of the fn
    Postcondition {
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        /// The values of the arguments just before the call. These are used to evaluate
        /// `old()` expressions in the postcondition
        pre_values: &'sym [SymValue<'sym, 'tcx, T>],
        /// The values of the arguments just after the call. THe postcondition
        /// holds w.r.t these values
        post_values: &'sym [SymValue<'sym, 'tcx, T>],
    },
    ImpliedBy(Box<PathConditions<'sym, 'tcx, T>>),
}

impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > PathConditionPredicate<'sym, 'tcx, T>
{
    pub fn apply_transformer(
        self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut impl SymValueTransformer<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            PathConditionPredicate::Eq(..) | PathConditionPredicate::Ne(..) => self,
            PathConditionPredicate::Postcondition {
                def_id,
                substs: s,
                pre_values,
                post_values,
            } => PathConditionPredicate::Postcondition {
                def_id,
                substs: s,
                pre_values: arena.alloc_slice(
                    &pre_values
                        .iter()
                        .map(|value| value.apply_transformer(arena, transformer))
                        .collect::<Vec<_>>(),
                ),
                post_values: arena.alloc_slice(
                    &post_values
                        .iter()
                        .map(|value| value.apply_transformer(arena, transformer))
                        .collect::<Vec<_>>(),
                ),
            },
            PathConditionPredicate::ImpliedBy(pc) => PathConditionPredicate::ImpliedBy(Box::new(
                pc.apply_transformer(arena, transformer),
            )),
        }
    }
    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            PathConditionPredicate::Eq(..) | PathConditionPredicate::Ne(..) => self,
            PathConditionPredicate::Postcondition {
                def_id,
                substs: s,
                pre_values,
                post_values,
            } => PathConditionPredicate::Postcondition {
                def_id,
                substs: s,
                pre_values: arena.alloc_slice(
                    &pre_values
                        .iter()
                        .map(|value| value.subst(arena, substs))
                        .collect::<Vec<_>>(),
                ),
                post_values: arena.alloc_slice(
                    &post_values
                        .iter()
                        .map(|value| value.subst(arena, substs))
                        .collect::<Vec<_>>(),
                ),
            },
            PathConditionPredicate::ImpliedBy(pc) => {
                PathConditionPredicate::ImpliedBy(Box::new(pc.subst(arena, substs)))
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathConditionPredicateAtom<'sym, 'tcx, T> {
    pub expr: SymValue<'sym, 'tcx, T>,
    pub predicate: PathConditionPredicate<'sym, 'tcx, T>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PathConditionAtom<'sym, 'tcx, T> {
    Assertion(Assertion<'sym, 'tcx, T>),
    Predicate(PathConditionPredicateAtom<'sym, 'tcx, T>),
    Not(Box<PathConditions<'sym, 'tcx, T>>),
}

impl<'sym, 'tcx, T: VisFormat> PathConditionAtom<'sym, 'tcx, T> {
    pub fn to_json(&self, tcx: Option<TyCtxt<'_>>, debug_info: &[VarDebugInfo]) -> Value {
        let json_string = self.to_vis_string(tcx, debug_info, OutputMode::HTML);
        serde_json::Value::String(json_string)
    }
}

impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > PathConditionAtom<'sym, 'tcx, T>
{
    pub fn apply_transformer(
        self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut impl SymValueTransformer<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            PathConditionAtom::Assertion(a) => {
                PathConditionAtom::Assertion(a.apply_transformer(arena, transformer))
            }
            PathConditionAtom::Predicate(p) => {
                PathConditionAtom::Predicate(p.apply_transformer(arena, transformer))
            }
            PathConditionAtom::Not(pc) => {
                PathConditionAtom::Not(Box::new(pc.apply_transformer(arena, transformer)))
            }
        }
    }

    fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            PathConditionAtom::Predicate(p) => PathConditionAtom::Predicate(p.subst(arena, substs)),
            PathConditionAtom::Not(pc) => PathConditionAtom::Not(Box::new(pc.subst(arena, substs))),
            PathConditionAtom::Assertion(a) => PathConditionAtom::Assertion(a.subst(arena, substs)),
        }
    }
}
impl<'sym, 'tcx, T: VisFormat> VisFormat for PathConditionAtom<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        match self {
            PathConditionAtom::Predicate(p) => p.to_vis_string(tcx, debug_info, mode),
            PathConditionAtom::Not(pc) => format!("!({})", pc.to_vis_string(tcx, debug_info, mode)),
            PathConditionAtom::Assertion(a) => a.to_vis_string(tcx, debug_info, mode),
        }
    }
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for PathConditionPredicateAtom<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        match &self.predicate {
            PathConditionPredicate::Eq(v, ty) => match ty.kind() {
                TyKind::Bool if *v == 0 => {
                    format!("!({})", self.expr.to_vis_string(tcx, debug_info, mode))
                }
                _ => format!(
                    "({} = {} as {})",
                    self.expr.to_vis_string(tcx, debug_info, mode),
                    v,
                    ty
                ),
            },
            PathConditionPredicate::Ne(vs, ty) if vs.len() == 1 => match ty.kind() {
                TyKind::Bool if vs[0] == 0 => self.expr.to_vis_string(tcx, debug_info, mode),
                _ => {
                    format!(
                        "({} != {}: {})",
                        self.expr.to_vis_string(tcx, debug_info, mode),
                        vs[0],
                        ty
                    )
                }
            },
            PathConditionPredicate::Ne(vs, ty) => {
                format!(
                    "({} does not equal any of [{}] as {})",
                    self.expr.to_vis_string(tcx, debug_info, mode),
                    vs.iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    ty
                )
            }
            PathConditionPredicate::Postcondition {
                def_id,
                post_values,
                ..
            } => {
                format!(
                    "({} satisfies the postcondition of {:?} applied to post values [{}])",
                    self.expr.to_vis_string(tcx, debug_info, mode),
                    def_id,
                    post_values.to_vis_string(tcx, debug_info, mode)
                )
            }
            PathConditionPredicate::ImpliedBy(pc) => {
                format!(
                    "({} ==> {})",
                    pc.to_vis_string(tcx, debug_info, mode),
                    self.expr.to_vis_string(tcx, debug_info, mode)
                )
            }
        }
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> PathConditionAtom<'sym, 'tcx, T> {
    pub fn implies(
        path_conditions: PathConditions<'sym, 'tcx, T>,
        assertion: SymValue<'sym, 'tcx, T>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<Self> {
        if let Some(bool_val) = assertion.kind.as_bool(tcx) {
            if bool_val {
                // TODO: Perhaps well-definedness isn't checked?
                None
            } else {
                Some(PathConditionAtom::Not(Box::new(path_conditions)))
            }
        } else {
            Some(PathConditionAtom::predicate(
                assertion,
                PathConditionPredicate::ImpliedBy(Box::new(path_conditions)),
            ))
        }
    }
    pub fn predicate(
        expr: SymValue<'sym, 'tcx, T>,
        predicate: PathConditionPredicate<'sym, 'tcx, T>,
    ) -> Self {
        PathConditionAtom::Predicate(PathConditionPredicateAtom { expr, predicate })
    }
}

impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > PathConditionPredicateAtom<'sym, 'tcx, T>
{
    pub fn new(
        expr: SymValue<'sym, 'tcx, T>,
        predicate: PathConditionPredicate<'sym, 'tcx, T>,
    ) -> Self {
        PathConditionPredicateAtom { expr, predicate }
    }

    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        let expr = self.expr.subst(arena, substs);
        let predicate = self.predicate.clone().subst(arena, substs);
        PathConditionPredicateAtom::new(expr, predicate)
    }
    pub fn apply_transformer(
        self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut impl SymValueTransformer<'sym, 'tcx, T>,
    ) -> Self {
        let expr = self.expr.apply_transformer(arena, transformer);
        let predicate = self.predicate.apply_transformer(arena, transformer);
        PathConditionPredicateAtom::new(expr, predicate)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathConditions<'sym, 'tcx, T> {
    pub atoms: Vec<PathConditionAtom<'sym, 'tcx, T>>,
}

impl<'sym, 'tcx, T: VisFormat> PathConditions<'sym, 'tcx, T> {
    pub fn to_json(&self, tcx: Option<TyCtxt<'_>>, debug_info: &[VarDebugInfo]) -> Value {
        self.atoms
            .iter()
            .map(|atom| atom.to_json(tcx, debug_info))
            .collect()
    }
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for PathConditions<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        if self.atoms.is_empty() {
            return "true".to_string();
        }
        self.atoms
            .iter()
            .map(|atom| atom.to_vis_string(tcx, debug_info, mode))
            .collect::<Vec<_>>()
            .join(" && ")
    }
}

impl<'sym, 'tcx, T> PathConditions<'sym, 'tcx, T> {
    pub fn new() -> Self {
        PathConditions { atoms: vec![] }
    }
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &PathConditionAtom<'sym, 'tcx, T>> {
        self.atoms.iter()
    }

    pub fn singleton(atom: PathConditionAtom<'sym, 'tcx, T>) -> Self {
        PathConditions { atoms: vec![atom] }
    }

    pub fn extend(&mut self, other: Self) {
        self.atoms.extend(other.atoms);
    }
}

impl<'sym, 'tcx, T: Eq> PathConditions<'sym, 'tcx, T> {
    pub fn insert(&mut self, atom: PathConditionAtom<'sym, 'tcx, T>) {
        if !self.atoms.contains(&atom) {
            self.atoms.push(atom);
        }
    }
}

impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > PathConditions<'sym, 'tcx, T>
{
    pub fn apply_transformer(
        self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut impl SymValueTransformer<'sym, 'tcx, T>,
    ) -> Self {
        let atoms = self
            .atoms
            .into_iter()
            .map(|atom| atom.apply_transformer(arena, transformer))
            .collect();
        PathConditions { atoms }
    }
    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        let atoms = self
            .atoms
            .into_iter()
            .map(|atom| atom.subst(arena, substs))
            .collect();
        PathConditions { atoms }
    }
}
