use std::collections::{btree_set::Iter, BTreeSet, HashSet};

use serde_json::Value;

use crate::{value::CanSubst, visualization::OutputMode, VisFormat};

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
pub struct PathConditionAtom<'sym, 'tcx, T> {
    pub expr: SymValue<'sym, 'tcx, T>,
    pub predicate: PathConditionPredicate<'sym, 'tcx, T>,
}

impl<'sym, 'tcx, T: VisFormat> PathConditionAtom<'sym, 'tcx, T> {
    pub fn to_json(&self, tcx: Option<TyCtxt<'_>>, debug_info: &[VarDebugInfo]) -> Value {
        let json_string = self.to_vis_string(tcx, debug_info, OutputMode::HTML);
        serde_json::Value::String(json_string)
    }
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for PathConditionAtom<'sym, 'tcx, T> {
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

impl<'sym, 'tcx, T> PathConditionAtom<'sym, 'tcx, T> {
    pub fn new(
        expr: SymValue<'sym, 'tcx, T>,
        predicate: PathConditionPredicate<'sym, 'tcx, T>,
    ) -> Self {
        PathConditionAtom { expr, predicate }
    }
}

impl<
        'sym,
        'tcx,
        T: Ord + Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > PathConditionAtom<'sym, 'tcx, T>
{
    pub fn subst(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'sym Substs<'sym, 'tcx, T>,
    ) -> Self {
        let expr = self.expr.subst(arena, substs);
        let predicate = self.predicate.clone().subst(arena, substs);
        PathConditionAtom::new(expr, predicate)
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
    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        let atoms = self
            .atoms
            .into_iter()
            .map(|atom| {
                let expr = atom.expr.subst(arena, substs);
                let predicate = atom.predicate.clone().subst(arena, substs);
                PathConditionAtom::new(expr, predicate)
            })
            .collect();
        PathConditions { atoms }
    }
}
