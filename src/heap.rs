use crate::add_debug_note;
use crate::context::SymExContext;
use crate::rustc_interface::middle::{
    mir::{self, Body, Location, PlaceElem, VarDebugInfo},
    ty::TyCtxt,
};
use crate::value::SymVar;
use crate::visualization::OutputMode;
use crate::{place::Place, VisFormat};
use pcs::utils::{PlaceRepacker, PlaceSnapshot, SnapshotLocation};
use pcs::utils::HasPlace;
use pcs::utils::place::maybe_old::MaybeOldPlace;
use std::collections::BTreeMap;
use pcs::utils::display::DisplayWithRepacker;

use super::value::{SymValue, SyntheticSymValue};

pub struct SymbolicHeap<'heap, 'mir, 'sym, 'tcx, T>(
    pub &'heap mut HeapData<'sym, 'tcx, T>,
    TyCtxt<'tcx>,
    &'mir Body<'tcx>,
    &'sym SymExContext<'tcx>,
);

impl<'heap, 'mir, 'sym, 'tcx, T: std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>>
    SymbolicHeap<'heap, 'mir, 'sym, 'tcx, T>
{
    pub fn arena(&self) -> &'sym SymExContext<'tcx> {
        self.3
    }

    pub fn body(&self) -> &'mir Body<'tcx> {
        self.2
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.1
    }

    pub fn data(&self) -> &HeapData<'sym, 'tcx, T> {
        self.0
    }

    fn repacker(&self) -> PlaceRepacker<'_, 'tcx> {
        PlaceRepacker::new(self.2, self.1)
    }

    pub fn new(
        heap: &'heap mut HeapData<'sym, 'tcx, T>,
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        arena: &'sym SymExContext<'tcx>,
    ) -> Self {
        SymbolicHeap(heap, tcx, body, arena)
    }

    pub fn snapshot_values(&mut self, block: mir::BasicBlock) {
        for (place, value) in &self.0.current_values() {
            self.0.insert(
                MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                    place.clone(),
                    SnapshotLocation::Start(block),
                )),
                value,
            );
        }
    }

    /// Sets the heap entry for this place to `value`. If `place` is a current
    /// place, also sets the heap entry for the place snapshot at `location`.
    pub (crate) fn insert<P: Clone + Into<MaybeOldPlace<'tcx>>>(
        &mut self,
        place: P,
        value: SymValue<'sym, 'tcx, T>,
        location: impl Into<SnapshotLocation>,
    ) {
        let place: MaybeOldPlace<'tcx> = place.into();
        self.insert_maybe_old_place(place.clone(), value);
        if let MaybeOldPlace::Current { place } = place {
            self.insert_maybe_old_place(
                MaybeOldPlace::OldPlace(PlaceSnapshot::new(place, location)),
                value,
            );
        }
    }

    pub fn insert_maybe_old_place(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        value: SymValue<'sym, 'tcx, T>,
    ) {
        if let Some(PlaceElem::Deref) = place.place().projection.last() {
            if let Some(base_place) = place.place().prefix_place(self.repacker()) {
                if let Some(mutability) = base_place.ref_mutability(self.repacker()) {
                    let place = MaybeOldPlace::new(base_place, place.location());
                    let value = self.arena().mk_ref(value, mutability);
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

impl<'sym, 'tcx, T: VisFormat + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug>
    HeapData<'sym, 'tcx, T>
{
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
    ) -> HeapData<'sym, 'tcx, T> {
        let mut heap_data = HeapData::new();
        let mut heap = SymbolicHeap::new(&mut heap_data, tcx, body, arena);
        let mut sym_vars = Vec::new();
        for arg in body.args_iter() {
            let local = &body.local_decls[arg];
            let sym_var = arena.mk_var(SymVar::Input(arg), local.ty);
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
        heap_data
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
        if let Some(_) = elem {
            self.remove(place);
        }
        elem
    }

    pub fn remove<P: Into<MaybeOldPlace<'tcx>> + Copy>(&mut self, place: &P) {
        let place: MaybeOldPlace<'tcx> = (*place).into();
        self.0.retain(|(p, _)| *p != place);
    }

    pub fn current_values(&self) -> Vec<(pcs::utils::Place<'tcx>, SymValue<'sym, 'tcx, T>)> {
        self.0
            .iter()
            .filter_map(|(p, v)| {
                if p.is_current() {
                    Some((p.place(), *v))
                } else {
                    None
                }
            })
            .collect()
    }
}
