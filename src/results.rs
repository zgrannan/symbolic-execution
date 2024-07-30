use std::collections::{BTreeMap, BTreeSet};

use crate::rustc_interface::middle::ty;

use crate::{path::AcyclicPath, path_conditions::PathConditions, value::SymValue, Assertion};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
/// Defines equations for backwards functions for a path. For a function f(a_1,
/// ... a_n), the i'th backwards fact is the return value of back_f_i(a_1, ...,
/// a_n, result) that is, the value of *a_i after `result` expires down this
/// path
pub struct BackwardsFacts<'sym, 'tcx, T>(pub BTreeMap<usize, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T> BackwardsFacts<'sym, 'tcx, T> {
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    pub fn insert(&mut self, index: usize, value: SymValue<'sym, 'tcx, T>) {
        self.0.insert(index, value);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct ResultPath<'sym, 'tcx, T> {
    pub path: AcyclicPath,
    pub pcs: PathConditions<'sym, 'tcx, T>,
    pub result: SymValue<'sym, 'tcx, T>,
    pub backwards_facts: BackwardsFacts<'sym, 'tcx, T>,
}

impl<'sym, 'tcx, T> ResultPath<'sym, 'tcx, T> {
    pub fn new(
        path: AcyclicPath,
        pcs: PathConditions<'sym, 'tcx, T>,
        result: SymValue<'sym, 'tcx, T>,
        backwards_facts: BackwardsFacts<'sym, 'tcx, T>,
    ) -> Self {
        Self {
            path,
            pcs,
            result,
            backwards_facts,
        }
    }
}

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
