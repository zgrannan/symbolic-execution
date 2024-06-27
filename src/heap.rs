use crate::rustc_interface::{
    middle::{
        mir::{self, Body, VarDebugInfo},
        ty::{TyCtxt, TyKind},
    },
    span::ErrorGuaranteed,
};
use crate::{place::Place, value::Constant, VisFormat};
use pcs::{borrows::engine::BorrowsDomain, visualization::get_source_name_from_place};
use std::collections::BTreeMap;

use super::{
    value::{SymValue, SyntheticSymValue},
    SymExContext,
};

pub(crate) struct HeapWrapper<'heap, 'sym, 'tcx, T>(
    pub &'heap mut SymbolicHeap<'sym, 'tcx, T>,
    TyCtxt<'tcx>,
    &'heap Body<'tcx>,
);

impl<'heap, 'sym, 'tcx, T: std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>>
    HeapWrapper<'heap, 'sym, 'tcx, T>
{
    pub fn new(
        heap: &'heap mut SymbolicHeap<'sym, 'tcx, T>,
        tcx: TyCtxt<'tcx>,
        body: &'heap Body<'tcx>,
    ) -> Self {
        HeapWrapper(heap, tcx, body)
    }
    pub fn insert(&mut self, place: Place<'tcx>, value: SymValue<'sym, 'tcx, T>) {
        let place_ty = place.ty(self.2, self.1);
        let value_ty = value.kind.ty(self.1);
        assert_eq!(
            self.1.erase_regions(place_ty.ty),
            self.1.erase_regions(value_ty.rust_ty())
        );
        self.0.insert(place, value);
    }

    pub fn encode_operand(
        &self,
        arena: &'sym SymExContext<'tcx>,
        operand: &mir::Operand<'tcx>,
        borrows: &BorrowsDomain<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        match *operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.0.get(&place.into()).unwrap_or_else(|| {
                    arena.mk_internal_error(
                        format!("Cannot place {:?}", place),
                        arena.tcx.mk_ty_from_kind(TyKind::Error(
                            ErrorGuaranteed::unchecked_claim_error_was_emitted(),
                        )),
                    )
                })
            }
            mir::Operand::Constant(box c) => arena.mk_constant(Constant(c.clone())),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SymbolicHeap<'sym, 'tcx, T>(BTreeMap<Place<'tcx>, SymValue<'sym, 'tcx, T>>);

impl<'sym, 'tcx, T: VisFormat> SymbolicHeap<'sym, 'tcx, T> {
    pub fn to_json(&self, debug_info: &[VarDebugInfo]) -> serde_json::Value {
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

                if acc.contains_key(&key) {
                    panic!("Duplicate key found: {} in {:?}", key, debug_info);
                }
                acc.insert(key, value_str);
                acc
            });
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
