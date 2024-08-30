use pcs::{borrows::domain::MaybeOldPlace, utils::PlaceRepacker};

use crate::rustc_interface::{
    middle::{
        mir::{self, tcx::PlaceTy, ProjectionElem},
        ty,
    },
};
use std::{
    hash::{Hash},
};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Place<'tcx>(pub pcs::utils::Place<'tcx>);

impl<'tcx> From<Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        MaybeOldPlace::Current { place: place.0 }
    }
}

impl<'tcx> std::fmt::Debug for Place<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'tcx> From<mir::Local> for Place<'tcx> {
    fn from(value: mir::Local) -> Self {
        Place(pcs::utils::Place::new(value, &[]))
    }
}

impl<'tcx> From<pcs::utils::Place<'tcx>> for Place<'tcx> {
    fn from(place: pcs::utils::Place<'tcx>) -> Self {
        Place(place)
    }
}

impl<'tcx> From<mir::Place<'tcx>> for Place<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Place(place.into())
    }
}

impl<'tcx> From<&mir::PlaceRef<'tcx>> for Place<'tcx> {
    fn from(value: &mir::PlaceRef<'tcx>) -> Self {
        Place::new(value.local, value.projection.into())
    }
}

impl<'tcx> Place<'tcx> {
    pub fn new(
        local: mir::Local,
        projection: &'tcx [ProjectionElem<mir::Local, ty::Ty<'tcx>>],
    ) -> Self {
        Place(pcs::utils::Place::new(local, projection))
    }

    pub fn local(&self) -> mir::Local {
        self.0.local
    }

    pub fn projection(&self) -> &'tcx [ProjectionElem<mir::Local, ty::Ty<'tcx>>] {
        &self.0.projection
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        Place(self.0.project_deref(repacker))
    }

    pub fn deref_target(&self) -> Option<Self> {
        if let Some(ProjectionElem::Deref) = self.0.projection.last() {
            Some(Place::new(
                self.0.local,
                &self.0.projection[0..self.0.projection.len() - 1],
            ))
        } else {
            None
        }
    }

    pub fn is_deref_of(&self, other: &Place<'tcx>) -> bool {
        if let Some(place) = self.deref_target() {
            &place == other
        } else {
            false
        }
    }

    pub fn ty(&self, body: &mir::Body<'tcx>, tcx: ty::TyCtxt<'tcx>) -> PlaceTy<'tcx> {
        (*self.0).ty(body, tcx)
    }

    pub fn is_mut_ref(&self, body: &mir::Body<'tcx>, tcx: ty::TyCtxt<'tcx>) -> bool {
        match self.ty(body, tcx).ty.kind() {
            ty::TyKind::Ref(_, _, mutbl) => mutbl.is_mut(),
            _ => false,
        }
    }
}
