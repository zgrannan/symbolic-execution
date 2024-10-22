use std::collections::HashMap;

use crate::context::SymExContext;
use crate::heap::HeapData;
use crate::path::{LoopPath, SymExPath};
use crate::rustc_interface::middle::ty;

use crate::value::{CanSubst, Substs, SyntheticSymValue};
use crate::{path::AcyclicPath, path_conditions::PathConditions, value::SymValue, Assertion};

#[derive(Clone, Debug, Eq, PartialEq)]
/// Defines equations for backwards functions for a path. For a function f(a_1,
/// ... a_n), the i'th backwards fact is the return value of back_f_i(a_1, ...,
/// a_n, result) that is, the value of *a_i after `result` expires down this
/// path
pub struct BackwardsFacts<'sym, 'tcx, T>(pub HashMap<usize, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T> BackwardsFacts<'sym, 'tcx, T> {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn insert(&mut self, index: usize, value: SymValue<'sym, 'tcx, T>) {
        self.0.insert(index, value);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResultPath<'sym, 'tcx, T> {
    Loop {
        path: LoopPath,
        pcs: PathConditions<'sym, 'tcx, T>,
    },
    Return {
        path: AcyclicPath,
        pcs: PathConditions<'sym, 'tcx, T>,
        result: SymValue<'sym, 'tcx, T>,
        backwards_facts: BackwardsFacts<'sym, 'tcx, T>,
        heap: HeapData<'sym, 'tcx, T>,
    },
}

impl<'sym, 'tcx, T> ResultPath<'sym, 'tcx, T> {
    pub fn backwards_facts(&self) -> Option<&BackwardsFacts<'sym, 'tcx, T>> {
        match self {
            Self::Return {
                backwards_facts, ..
            } => Some(backwards_facts),
            _ => None,
        }
    }
    pub fn pcs(&self) -> &PathConditions<'sym, 'tcx, T> {
        match self {
            Self::Loop { pcs, .. } => pcs,
            Self::Return { pcs, .. } => pcs,
        }
    }
    pub fn result(&self) -> Option<SymValue<'sym, 'tcx, T>> {
        match self {
            Self::Return { result, .. } => Some(*result),
            _ => None,
        }
    }

    pub fn path(&self) -> SymExPath {
        match self {
            Self::Loop { path, .. } => SymExPath::Loop(path.clone()),
            Self::Return { path, .. } => SymExPath::Acyclic(path.clone()),
        }
    }

    pub fn loop_path(path: LoopPath, pcs: PathConditions<'sym, 'tcx, T>) -> Self {
        Self::Loop { path, pcs }
    }

    pub fn return_path(
        path: AcyclicPath,
        pcs: PathConditions<'sym, 'tcx, T>,
        result: SymValue<'sym, 'tcx, T>,
        backwards_facts: BackwardsFacts<'sym, 'tcx, T>,
        heap: HeapData<'sym, 'tcx, T>,
    ) -> Self {
        Self::Return {
            path,
            pcs,
            result,
            backwards_facts,
            heap,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResultAssertions<'sym, 'tcx, T>(Vec<ResultAssertion<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T> ResultAssertions<'sym, 'tcx, T> {
    pub fn new() -> Self {
        ResultAssertions(Vec::new())
    }

    pub fn iter(&self) -> impl Iterator<Item = &ResultAssertion<'sym, 'tcx, T>> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = ResultAssertion<'sym, 'tcx, T>> {
        self.0.into_iter()
    }
}
impl<'sym, 'tcx, T: Eq> ResultAssertions<'sym, 'tcx, T> {
    pub fn insert(&mut self, assertion: ResultAssertion<'sym, 'tcx, T>) {
        if !self.0.contains(&assertion) {
            self.0.push(assertion);
        }
    }
}
impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > ResultAssertions<'sym, 'tcx, T>
{
    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        ResultAssertions(
            self.0
                .into_iter()
                .map(|assertion| assertion.subst(arena, substs))
                .collect(),
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResultAssertion<'sym, 'tcx, T> {
    pub path: SymExPath,
    pub assertion: Assertion<'sym, 'tcx, T>,
}

impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > ResultAssertion<'sym, 'tcx, T>
{
    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Self {
        Self {
            path: self.path,
            assertion: self.assertion.subst(arena, substs),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SymbolicExecutionResult<'sym, 'tcx, T> {
    pub paths: ResultPaths<'sym, 'tcx, T>,
    pub assertions: ResultAssertions<'sym, 'tcx, T>,
    pub fresh_symvars: Vec<ty::Ty<'tcx>>,
}

#[derive(Clone, Debug)]
pub struct ResultPaths<'sym, 'tcx, T>(Vec<ResultPath<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T: Eq> ResultPaths<'sym, 'tcx, T> {
    pub fn insert(&mut self, path: ResultPath<'sym, 'tcx, T>) {
        if !self.0.contains(&path) {
            self.0.push(path);
        }
    }
}

impl<'sym, 'tcx, T> ResultPaths<'sym, 'tcx, T> {
    pub fn new() -> Self {
        Self(Vec::new())
    }
    pub fn iter(&self) -> impl Iterator<Item = &ResultPath<'sym, 'tcx, T>> {
        self.0.iter()
    }
    pub fn into_iter(self) -> impl Iterator<Item = ResultPath<'sym, 'tcx, T>> {
        self.0.into_iter()
    }
}
