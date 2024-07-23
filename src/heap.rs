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

    pub fn insert<P: Clone + Into<Place<'tcx>>>(
        &mut self,
        place: P,
        value: SymValue<'sym, 'tcx, T>,
        location: Location,
    ) {
        self.insert_maybe_old_place(place.clone().into(), value);
        self.insert_maybe_old_place(
            MaybeOldPlace::OldPlace(PlaceSnapshot::new(place.into().0, location)),
            value,
        );
    }

    pub fn insert_maybe_old_place<P: Into<MaybeOldPlace<'tcx>>>(
        &mut self,
        place: P,
        value: SymValue<'sym, 'tcx, T>,
    ) {
        let place: MaybeOldPlace<'tcx> = place.into();
        let place_ty = place.ty(PlaceRepacker::new(self.2, self.1));
        let value_ty = value.kind.ty(self.1);
        assert_tys_match(self.1, place_ty.ty, value_ty.rust_ty());
        self.0.insert(place, value);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeapData<'sym, 'tcx, T>(Vec<(MaybeOldPlace<'tcx>, SymValue<'sym, 'tcx, T>)>);

impl<'sym, 'tcx, T: VisFormat + SyntheticSymValue<'sym, 'tcx>> HeapData<'sym, 'tcx, T> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        let map = self
            .0
            .iter()
            .fold(BTreeMap::new(), |mut acc, (place, value)| {
                let mut key = place.to_short_string(repacker);
                let value_str = format!("{}", value.to_vis_string(&repacker.body().var_debug_info));
                let ty_str = format!("{}", value.ty(repacker.tcx()));

                if acc.contains_key(&key) {
                    key = format!("{:?}", place.to_short_string(repacker));
                    assert!(!acc.contains_key(&key));
                }
                acc.insert(key, serde_json::json!({ "value": value_str, "ty": ty_str }));
                acc
            });
        serde_json::to_value(map).unwrap()
    }
}

impl<'sym, 'tcx, T: std::fmt::Debug> HeapData<'sym, 'tcx, T> {
    pub fn new() -> Self {
        HeapData(Vec::new())
    }

    fn insert<P: Into<MaybeOldPlace<'tcx>>>(&mut self, place: P, value: SymValue<'sym, 'tcx, T>) {
        let place: MaybeOldPlace<'tcx> = place.into();
        self.remove(&place);
        self.0.push((place, value));
    }

    pub fn get<P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &self,
        place: &P,
    ) -> Option<SymValue<'sym, 'tcx, T>> {
        let place: MaybeOldPlace<'tcx> = (*place).into();
        self.0
            .iter()
            .find(|(p, _)| *p == place)
            .map(|(_, v)| v)
            .copied()
    }

    pub fn take<P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &mut self,
        place: &P,
    ) -> Option<SymValue<'sym, 'tcx, T>> {
        let place = place.into();
        let elem = self.get(place);
        if let Some(value) = elem {
            self.remove(place);
        }
        elem
    }

    pub fn remove<P: Into<MaybeOldPlace<'tcx>> + Copy>(&mut self, place: &P) {
        let place: MaybeOldPlace<'tcx> = (*place).into();
        self.0.retain(|(p, _)| *p != place);
    }

    pub fn get_return_place_expr(&self) -> Option<SymValue<'sym, 'tcx, T>> {
        self.get(&Into::<Place<'tcx>>::into(mir::RETURN_PLACE))
    }
}
