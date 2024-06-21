use crate::{
    place::Place,
    value::{Constant, SymValueData},
    VisFormat,
};
use pcs::{borrows::engine::BorrowsDomain, visualization::get_source_name_from_place};
use crate::rustc_interface::middle::mir::{self, VarDebugInfo};
use std::collections::BTreeMap;

use super::{
    value::{SymValue, SyntheticSymValue},
    SymExContext,
};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SymbolicHeap<'sym, 'tcx, T>(BTreeMap<Place<'tcx>, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T: VisFormat> SymbolicHeap<'sym, 'tcx, T> {
    pub fn to_json(&self, debug_info: &[VarDebugInfo]) -> serde_json::Value {
        let map: BTreeMap<_, _> = self
            .0
            .iter()
            .map(|(place, value)| {
                (
                    format!(
                        "{}",
                        get_source_name_from_place(place.local, &place.projection, debug_info)
                            .unwrap_or_else(|| format!("{:?}", place))
                    ),
                    format!("{}", value.to_vis_string(debug_info)),
                )
            })
            .collect();
        serde_json::to_value(map).unwrap()
    }
}

impl<'sym, 'tcx, T: std::fmt::Debug> SymbolicHeap<'sym, 'tcx, T> {
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
        SymbolicHeap(BTreeMap::new())
    }

    pub fn insert(&mut self, place: Place<'tcx>, value: SymValue<'sym, 'tcx, T>) {
        self.0.insert(place, value);
    }

    pub fn get(&self, place: &Place<'tcx>) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0.get(&place).copied()
    }

    pub fn get_deref_of(&self, place: &Place<'tcx>) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0.iter().find(|(p, v)| {
            p.is_deref_of(place)
        }).map(|(_, v)| v).copied()
    }

    pub fn take(&mut self, place: &Place<'tcx>) -> SymValue<'sym, 'tcx, T> {
        self.0
            .remove(&place)
            .unwrap_or_else(|| panic!("{place:?} not found in heap {:#?}", self.0))
    }

    pub fn get_return_place_expr(&self) -> Option<SymValue<'sym, 'tcx, T>> {
        self.get(&mir::RETURN_PLACE.into())
    }
}

impl<'sym, 'tcx, T: Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>>
    SymbolicHeap<'sym, 'tcx, T>
{
    pub fn encode_operand(
        &self,
        arena: &'sym SymExContext,
        operand: &mir::Operand<'tcx>,
        borrows: &BorrowsDomain<'tcx>
    ) -> SymValue<'sym, 'tcx, T> {
        match *operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self
                .get(&place.into())
                .unwrap_or_else(|| panic!("{place:?} not found in heap {:#?}", self.0)),
            mir::Operand::Constant(box c) => arena.mk_constant(Constant(c.clone())),
        }
    }
}
