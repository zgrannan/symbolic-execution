use crate::{place::Place, VisFormat};
use crate::{
    rustc_interface::middle::{
        mir::{self, Body, Location},
        ty::TyCtxt,
    },
    util::assert_tys_match,
};
use pcs::borrows::domain::MaybeOldPlace;
use pcs::utils::{PlaceRepacker, PlaceSnapshot};
use std::collections::BTreeMap;

use super::value::{SymValue, SyntheticSymValue};

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
