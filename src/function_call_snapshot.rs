use crate::rustc_interface::middle::mir::{Local, Location};
use std::collections::BTreeMap;

use super::value::SymValue;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionCallSnapshot<'sym, 'tcx, T> {
    args: &'sym [SymValue<'sym, 'tcx, T>],
    input_places: Vec<Option<Local>>,
}

impl<'sym, 'tcx, T> FunctionCallSnapshot<'sym, 'tcx, T> {
    pub fn new(args: &'sym [SymValue<'sym, 'tcx, T>], input_places: Vec<Option<Local>>) -> Self {
        Self { args, input_places }
    }

    pub fn args(&self) -> &'sym [SymValue<'sym, 'tcx, T>] {
        self.args
    }

    pub fn arg(&self, idx: usize) -> SymValue<'sym, 'tcx, T> {
        self.args[idx]
    }

    pub fn index_of_arg_local(&self, local: Local) -> usize {
        self.input_places.iter().position(|&l| l == Some(local)).unwrap()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionCallSnapshots<'sym, 'tcx, T>(
    BTreeMap<Location, FunctionCallSnapshot<'sym, 'tcx, T>>,
);

impl<'sym, 'tcx, T> FunctionCallSnapshots<'sym, 'tcx, T> {
    pub fn new() -> Self {
        FunctionCallSnapshots(BTreeMap::new())
    }

    pub fn add_snapshot(
        &mut self,
        location: Location,
        snapshot: FunctionCallSnapshot<'sym, 'tcx, T>,
    ) {
        self.0.insert(location, snapshot);
    }

    pub fn get_snapshot(&self, location: &Location) -> Option<&FunctionCallSnapshot<'sym, 'tcx, T>> {
        self.0.get(location)
    }
}
