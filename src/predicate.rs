use crate::{
    context::SymExContext,
    rustc_interface::{
        hir::def_id::DefId,
        middle::{
            mir::VarDebugInfo,
            ty::{self, GenericArgsRef, TyCtxt, TyKind},
        },
    },
    transform::SymValueTransformer,
    value::{CanSubst, Substs, SymValue, SyntheticSymValue},
    visualization::{OutputMode, VisFormat},
};
use serde_json::Value;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Predicate<'sym, 'tcx, T> {
    All(Vec<Predicate<'sym, 'tcx, T>>),
    Value(SymValue<'sym, 'tcx, T>),
    Precondition(DefId, GenericArgsRef<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
    Implies(Box<Predicate<'sym, 'tcx, T>>, Box<Predicate<'sym, 'tcx, T>>),
    SwitchIntEq(SymValue<'sym, 'tcx, T>, u128, ty::Ty<'tcx>),
    SwitchIntNe(SymValue<'sym, 'tcx, T>, Vec<u128>, ty::Ty<'tcx>),
    Postcondition {
        expr: SymValue<'sym, 'tcx, T>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        /// The values of the arguments just before the call. These are used to evaluate
        /// `old()` expressions in the postcondition
        pre_values: &'sym [SymValue<'sym, 'tcx, T>],
        /// The values of the arguments just after the call. THe postcondition
        /// holds w.r.t these values
        post_values: &'sym [SymValue<'sym, 'tcx, T>],
    },
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for Predicate<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        match self {
            Predicate::Value(value) => value.to_vis_string(tcx, debug_info, mode),
            Predicate::Precondition(def_id, _, _) => todo!(),
            Predicate::Implies(predicate, predicate1) => {
                let predicate_str = predicate.to_vis_string(tcx, debug_info, mode);
                let predicate1_str = predicate1.to_vis_string(tcx, debug_info, mode);
                format!("({} ⇒ {})", predicate_str, predicate1_str)
            }
            Predicate::SwitchIntEq(value, switch_val, ty) => {
                let value = value.to_vis_string(tcx, debug_info, mode);
                format!("{} == {}", value, switch_val)
            }
            Predicate::SwitchIntNe(value, switch_vals, ty) => {
                let value = value.to_vis_string(tcx, debug_info, mode);
                if switch_vals.len() == 1 {
                    format!("{} ≠ {}", value, switch_vals[0])
                } else {
                    let switch_vals = switch_vals
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>();
                    format!("{} ∉ {{{}}}", value, switch_vals.join(", "))
                }
            }
            Predicate::Postcondition {
                expr,
                def_id,
                substs,
                pre_values,
                post_values,
            } => {
                let expr_str = expr.to_vis_string(tcx, debug_info, mode);
                let pre_values_str = pre_values
                    .iter()
                    .map(|v| v.to_vis_string(tcx, debug_info, mode))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "{} satisfies postcondition of {:?}({})",
                    expr_str, def_id, pre_values_str
                )
            }
            Predicate::All(vec) => {
                let vec = vec
                    .into_iter()
                    .map(|p| p.to_vis_string(tcx, debug_info, mode))
                    .collect::<Vec<_>>();
                format!("({})", vec.join(" && "))
            }
        }
    }
}
impl<'sym, 'tcx, T: VisFormat> Predicate<'sym, 'tcx, T> {
    pub fn to_json(&self, tcx: Option<TyCtxt<'_>>, debug_info: &[VarDebugInfo]) -> Value {
        let json_string = self.to_vis_string(tcx, debug_info, OutputMode::HTML);
        serde_json::Value::String(json_string)
    }
}
impl<'sym, 'tcx, T> Predicate<'sym, 'tcx, T> {
    pub fn true_() -> Self {
        Predicate::All(vec![])
    }
    pub fn is_true(&self) -> bool {
        matches!(self, Predicate::All(vec) if vec.is_empty())
    }
    pub fn implies(self, other: Self) -> Self {
        if self.is_true() {
            return other;
        }
        Predicate::Implies(Box::new(self), Box::new(other))
    }
    pub fn and(self, other: Self) -> Self {
        if let Predicate::All(mut vec) = self {
            vec.push(other);
            return Predicate::All(vec);
        }
        if let Predicate::All(mut vec) = other {
            vec.insert(0, self);
            return Predicate::All(vec);
        }
        Predicate::All(vec![self, other])
    }
}

impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > Predicate<'sym, 'tcx, T>
{
    pub fn apply_transformer(
        self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut impl SymValueTransformer<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            Predicate::Value(_) => todo!(),
            Predicate::Precondition(def_id, _, _) => todo!(),
            Predicate::Implies(predicate, predicate1) => todo!(),
            Predicate::SwitchIntEq(_, _, ty) => todo!(),
            Predicate::SwitchIntNe(_, vec, ty) => todo!(),
            Predicate::Postcondition {
                expr,
                def_id,
                substs,
                pre_values,
                post_values,
            } => todo!(),
            Predicate::All(vec) => todo!(),
        }
    }

    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            Predicate::All(vec) => {
                let vec = vec.into_iter().map(|p| p.subst(arena, substs)).collect();
                Predicate::All(vec)
            }
            Predicate::Value(value) => Predicate::Value(value.subst(arena, substs)),
            Predicate::Precondition(def_id, fn_substs, pre_values) => {
                let pre_values = pre_values
                    .iter()
                    .map(|v| v.subst(arena, substs))
                    .collect::<Vec<_>>();
                Predicate::Precondition(def_id, fn_substs, arena.alloc_slice(&pre_values))
            }
            Predicate::Implies(predicate, predicate1) => {
                let predicate = predicate.subst(arena, substs);
                let predicate1 = predicate1.subst(arena, substs);
                Predicate::Implies(Box::new(predicate), Box::new(predicate1))
            }
            Predicate::SwitchIntEq(value, switch_val, ty) => {
                let value = value.subst(arena, substs);
                Predicate::SwitchIntEq(value, switch_val, ty)
            }
            Predicate::SwitchIntNe(value, switch_vals, ty) => {
                let value = value.subst(arena, substs);
                Predicate::SwitchIntNe(value, switch_vals, ty)
            }
            Predicate::Postcondition {
                expr,
                def_id,
                substs: fn_substs,
                pre_values,
                post_values,
            } => {
                let expr = expr.subst(arena, substs);
                let pre_values = pre_values
                    .iter()
                    .map(|v| v.subst(arena, substs))
                    .collect::<Vec<_>>();
                let post_values = post_values
                    .iter()
                    .map(|v| v.subst(arena, substs))
                    .collect::<Vec<_>>();
                Predicate::Postcondition {
                    expr,
                    def_id,
                    substs: fn_substs,
                    pre_values: arena.alloc_slice(&pre_values),
                    post_values: arena.alloc_slice(&post_values),
                }
            }
        }
    }
}
