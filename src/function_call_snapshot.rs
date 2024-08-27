use crate::rustc_interface::middle::mir::Location;
use std::collections::BTreeMap;

use super::value::SymValue;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionCallSnapshot<'sym, 'tcx, T> {
    pub args: &'sym [SymValue<'sym, 'tcx, T>],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionCallSnapshots<'sym, 'tcx, T>(
    BTreeMap<Location, FunctionCallSnapshot<'sym, 'tcx, T>>,
);

impl<'sym, 'tcx, T> FunctionCallSnapshots<'sym, 'tcx, T> {
    pub fn new() -> Self {
        FunctionCallSnapshots(BTreeMap::new())
    }

    pub fn add_snapshot(&mut self, location: Location, args: &'sym [SymValue<'sym, 'tcx, T>]) {
        self.0.insert(location, FunctionCallSnapshot { args });
    }

    pub fn get_snapshot(&self, location: &Location) -> &FunctionCallSnapshot<'sym, 'tcx, T> {
        self.0.get(location).unwrap()
    }
}
