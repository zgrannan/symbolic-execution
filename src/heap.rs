use crate::{place::Place, value::Constant, VisFormat};
use crate::{
    rustc_interface::{
        middle::{
            mir::{self, Body, VarDebugInfo},
            ty::{TyCtxt, TyKind},
        },
        span::ErrorGuaranteed,
    },
    util::assert_tys_match,
};
use pcs::{borrows::engine::BorrowsDomain, visualization::get_source_name_from_place};
use std::collections::BTreeMap;

use super::{
    value::{SymValue, SyntheticSymValue},
    SymExContext,
};

pub(crate) struct SymbolicHeap<'mir, 'sym, 'tcx, T>(
    pub &'mir mut HeapData<'sym, 'tcx, T>,
    TyCtxt<'tcx>,
    &'mir Body<'tcx>,
);

impl<'mir, 'sym, 'tcx, T: std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>>
    SymbolicHeap<'mir, 'sym, 'tcx, T>
{
    pub fn new(
        heap: &'mir mut HeapData<'sym, 'tcx, T>,
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
    ) -> Self {
        SymbolicHeap(heap, tcx, body)
    }
    pub fn insert(&mut self, place: Place<'tcx>, value: SymValue<'sym, 'tcx, T>) {
        let place_ty = place.ty(self.2, self.1);
        let value_ty = value.kind.ty(self.1);
        assert_tys_match(self.1, place_ty.ty, value_ty.rust_ty());
        self.0.insert(place, value);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct HeapData<'sym, 'tcx, T>(BTreeMap<Place<'tcx>, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T: VisFormat + SyntheticSymValue<'sym, 'tcx>> HeapData<'sym, 'tcx, T> {
    pub fn to_json(&self, tcx: TyCtxt<'tcx>, debug_info: &[VarDebugInfo]) -> serde_json::Value {
        let map = self
            .0
            .iter()
            .fold(BTreeMap::new(), |mut acc, (place, value)| {
                let key = format!(
                    "{}",
                    get_source_name_from_place(place.local(), &place.projection(), debug_info)
                        .unwrap_or_else(|| format!("{:?}", place))
                );
                let value_str = format!("{}", value.to_vis_string(debug_info));
                let ty_str = format!("{}", value.ty(tcx));

                if acc.contains_key(&key) {
                    panic!("Duplicate key found: {} in {:?}", key, debug_info);
                }
                acc.insert(key, serde_json::json!({ "value": value_str, "ty": ty_str }));
                acc
            });
        serde_json::to_value(map).unwrap()
    }
}

impl<'sym, 'tcx, T: std::fmt::Debug> HeapData<'sym, 'tcx, T> {
    // pub fn check_eq_debug(&self, other: &Self) {
    //     for (p, v) in self.0.iter() {
    //         if !other.0.contains_key(&p) {
    //             panic!("Heap missing key: {:?}", p);
    //         }
    //         let other_v = other.0.get(&p).unwrap();
    //         if *v != *other_v {
    //             panic!("Heap value mismatch: {:?} {:?} vs {:?}", p, v, other_v);
    //         }
    //     }
    //     for (p, v) in other.0.iter() {
    //         if !self.0.contains_key(&p) {
    //             panic!("Heap missing key: {:?}", p);
    //         }
    //     }
    // }

    pub fn new() -> Self {
        HeapData(BTreeMap::new())
    }

    fn insert(&mut self, place: Place<'tcx>, value: SymValue<'sym, 'tcx, T>) {
        self.0.insert(place, value);
    }

    pub fn get(&self, place: &Place<'tcx>) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0.get(&place).copied()
    }

    pub fn get_deref_of(&self, place: &Place<'tcx>) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0
            .iter()
            .find(|(p, v)| p.is_deref_of(place))
            .map(|(_, v)| v)
            .copied()
    }

    pub fn take(&mut self, place: &Place<'tcx>) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0.remove(&place)
    }

    pub fn remove(&mut self, place: &Place<'tcx>) {
        self.0.remove(&place);
    }

    pub fn get_return_place_expr(&self) -> Option<SymValue<'sym, 'tcx, T>> {
        self.get(&mir::RETURN_PLACE.into())
    }
}
