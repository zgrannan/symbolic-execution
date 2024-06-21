use std::collections::BTreeSet;

use crate::rustc_interface::middle::ty;

use crate::{path::AcyclicPath, path_conditions::PathConditions, value::SymValue, Assertion};
pub type ResultPath<'sym, 'tcx, T> = (
    AcyclicPath,
    PathConditions<'sym, 'tcx, T>,
    SymValue<'sym, 'tcx, T>,
);
pub type ResultAssertion<'sym, 'tcx, T> = (
    AcyclicPath,
    PathConditions<'sym, 'tcx, T>,
    Assertion<'sym, 'tcx, T>,
);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicExecutionResult<'sym, 'tcx, T> {
    pub paths: BTreeSet<ResultPath<'sym, 'tcx, T>>,
    pub assertions: BTreeSet<ResultAssertion<'sym, 'tcx, T>>,
    pub symvars: Vec<ty::Ty<'tcx>>,
}
