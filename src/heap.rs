use crate::add_debug_note;
use crate::context::SymExContext;
use crate::value::SymVar;
use crate::visualization::OutputMode;
use crate::{place::Place, VisFormat};
use crate::{
    rustc_interface::middle::{
        mir::{self, Body, Location, ProjectionElem},
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
    pub fn new(
        heap: &'mir mut HeapData<'sym, 'tcx, T>,
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        arena: &'sym SymExContext<'tcx>,
    ) -> Self {
        SymbolicHeap(heap, tcx, body, arena)
    }

    pub fn insert_maybe_deref<P: Clone + Into<Place<'tcx>>>(
        &mut self,
        place: P,
        value: SymValue<'sym, 'tcx, T>,
        location: Location,
    ) {
        let p: Place<'tcx> = place.into();
        if p.ty(self.2, self.1).ty.is_ref() {
            self.insert(
                p.project_deref(PlaceRepacker::new(self.2, self.1)),
                self.3.mk_projection(ProjectionElem::Deref, value),
                location,
            );
        } else {
            self.insert(p, value, location);
        }
    }

    pub fn insert<P: Clone + Into<Place<'tcx>>>(
        &mut self,
        place: P,
        value: SymValue<'sym, 'tcx, T>,
        location: Location,
    ) {
        let place: Place<'tcx> = place.into();
        // let (place, value) = if value.kind.ty(self.1).rust_ty().is_ref() {
        //     (
        //         place.project_deref(PlaceRepacker::new(self.2, self.1)),
        //         self.3.mk_projection(ProjectionElem::Deref, value),
        //     )
        // } else {
        //     (place, value)
        // };
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
                let value_str = format!("{}", value.to_vis_string(
                    Some(repacker.tcx()), &repacker.body().var_debug_info, OutputMode::HTML));
                let ty_str = format!("{}", value.ty(repacker.tcx()));

                if acc.contains_key(&key) {
                    key = format!("{:?}", place.to_short_string(repacker));
                    assert!(!acc.contains_key(&key));
                }
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
            /*
             * If we're passed in a reference-typed field, store in the heap its
             * dereference. TODO: Explain why
             */
            match sym_var.ty(tcx).rust_ty().kind() {
                ty::TyKind::Ref(_, _, _) => {
                    heap.insert(
                        place.project_deref(PlaceRepacker::new(body, tcx)),
                        arena.mk_projection(ProjectionElem::Deref, sym_var),
                        Location::START,
                    );
                }
                _ => {
                    heap.insert(place, sym_var, Location::START);
                }
            }
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

    pub fn get_oldest_for_place(
        &self,
        place: &pcs::utils::Place<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, T>> {
        self.0
            .iter()
            .filter(|(k, _)| k.place() == *place)
            .flat_map(|(k, v)| (k.old_place().map(|p| (p, v))))
            .min_by_key(|(k, _)| k.at)
            .map(|(_, v)| v)
            .copied()
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
