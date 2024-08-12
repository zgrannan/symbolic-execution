use crate::add_debug_note;
use crate::context::SymExContext;
use crate::value::SymVar;
use crate::visualization::OutputMode;
use crate::{place::Place, VisFormat};
use crate::{
    rustc_interface::hir::Mutability,
    rustc_interface::middle::{
        mir::{self, Body, Location, PlaceElem, ProjectionElem, VarDebugInfo},
        ty::{self, TyCtxt},
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
    &'sym SymExContext<'tcx>,
);

impl<'mir, 'sym, 'tcx, T: std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>>
    SymbolicHeap<'mir, 'sym, 'tcx, T>
{
    fn arena(&self) -> &'sym SymExContext<'tcx> {
        self.3
    }

    fn body(&self) -> &'mir Body<'tcx> {
        self.2
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.1
    }

    fn repacker(&self) -> PlaceRepacker<'_, 'tcx> {
        PlaceRepacker::new(self.2, self.1)
    }

    pub fn new(
        heap: &'mir mut HeapData<'sym, 'tcx, T>,
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        arena: &'sym SymExContext<'tcx>,
    ) -> Self {
        SymbolicHeap(heap, tcx, body, arena)
    }

    pub fn insert<P: Clone + Into<Place<'tcx>>>(
        &mut self,
        place: P,
        value: SymValue<'sym, 'tcx, T>,
        location: Location,
    ) {
        let place: Place<'tcx> = place.into();
        self.insert_maybe_old_place(place.clone(), value);
        self.insert_maybe_old_place(
            MaybeOldPlace::OldPlace(PlaceSnapshot::new(place.0, location)),
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
        if let Some(PlaceElem::Deref) = place.place().projection.last() {
            if let Some(base_place) = place.place().prefix_place(self.repacker()) {
                if base_place.is_ref(self.body(), self.tcx()) {
                    let place = MaybeOldPlace::new(base_place, place.location());
                    let value = self.arena().mk_ref(value, Mutability::Mut);
                    self.0.insert(place, value);
                    return;
                }
            }
        }
        self.0.insert(place, value);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeapData<'sym, 'tcx, T>(Vec<(MaybeOldPlace<'tcx>, SymValue<'sym, 'tcx, T>)>);

impl<'heap, 'sym, 'tcx, T: VisFormat> VisFormat for &'heap HeapData<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        self.vis_string(tcx, debug_info, mode)
    }
}
impl<'heap, 'sym, 'tcx, T: VisFormat> VisFormat for &'heap mut HeapData<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        self.vis_string(tcx, debug_info, mode)
    }
}
impl<'sym, 'tcx, T: VisFormat> HeapData<'sym, 'tcx, T> {
    pub fn vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        let mut str = String::new();
        for (place, value) in &self.0 {
            str.push_str(&format!(
                "{:?} -> {}{}",
                place,
                value.to_vis_string(tcx, debug_info, mode),
                mode.newline(),
            ));
        }
        str
    }
}

impl<'sym, 'tcx, T: VisFormat + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug> HeapData<'sym, 'tcx, T> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        let map = self
            .0
            .iter()
            .fold(BTreeMap::new(), |mut acc, (place, value)| {
                let key = place.to_short_string(repacker);
                let value_str = format!("{}", value.to_vis_string(
                    Some(repacker.tcx()), &repacker.body().var_debug_info, OutputMode::HTML));
                let ty_str = format!("{}", value.ty(repacker.tcx()));

                // if acc.contains_key(&key) {
                //     assert!(!acc.contains_key(&key), "Duplicate key: {:?} for {:?} {:?}", key, place, self);
                // }
                acc.insert(key, serde_json::json!({ "old": !place.is_current(), "value": value_str, "ty": ty_str }));
                acc
            });
        serde_json::to_value(map).unwrap()
    }
}
impl<'sym, 'tcx, T: std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>> HeapData<'sym, 'tcx, T> {
    pub fn init_for_body(
        arena: &'sym SymExContext<'tcx>,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
    ) -> (HeapData<'sym, 'tcx, T>, Vec<ty::Ty<'tcx>>) {
        let mut heap_data = HeapData::new();
        let mut heap = SymbolicHeap::new(&mut heap_data, tcx, body, arena);
        let mut sym_vars = Vec::new();
        for (idx, arg) in body.args_iter().enumerate() {
            let local = &body.local_decls[arg];
            let sym_var = arena.mk_var(SymVar::Normal(idx), local.ty);
            sym_vars.push(local.ty);
            let place = Place::new(arg, &[]);
            add_debug_note!(
                sym_var.debug_info,
                "Symvar for arg {:?} in {:?}",
                arg,
                body.span
            );
            heap.insert(place, sym_var, Location::START);
        }
        (heap_data, sym_vars)
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
        // TODO: actually remove
        // if let Some(_) = elem {
        //     self.remove(place);
        // }
        elem
    }

    pub fn remove<P: Into<MaybeOldPlace<'tcx>> + Copy>(&mut self, place: &P) {
        let place: MaybeOldPlace<'tcx> = (*place).into();
        self.0.retain(|(p, _)| *p != place);
    }
}
