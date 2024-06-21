use crate::rustc_interface::{
    data_structures::fx::FxHasher,
    middle::{
        mir::{self, ProjectionElem},
        ty,
    },
};
use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
};

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Place<'tcx> {
    pub local: mir::Local,
    pub projection: Vec<ProjectionElem<mir::Local, ty::Ty<'tcx>>>,
}

impl<'tcx> From<mir::Local> for Place<'tcx> {
    fn from(value: mir::Local) -> Self {
        Place {
            local: value,
            projection: Vec::new(),
        }
    }
}

impl<'tcx> From<pcs::utils::Place<'tcx>> for Place<'tcx> {
    fn from(place: pcs::utils::Place<'tcx>) -> Self {
        Place {
            local: place.local,
            projection: place.projection.iter().copied().collect(),
        }
    }
}

impl<'tcx> From<mir::Place<'tcx>> for Place<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Place::new(place.local, place.projection.iter().collect())
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
        projection: Vec<ProjectionElem<mir::Local, ty::Ty<'tcx>>>,
    ) -> Self {
        Place { local, projection }
    }

    pub fn deref_target(&self) -> Option<Self> {
        if let Some(ProjectionElem::Deref) = self.projection.last() {
            let mut projection = self.projection.clone();
            projection.pop();
            Some(Place::new(self.local, projection))
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
}

fn hash<T: Hash>(t: T) -> u64 {
    let mut hasher = FxHasher::default();
    t.hash(&mut hasher);
    hasher.finish()
}

impl<'tcx> PartialOrd for Place<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        hash(self).partial_cmp(&hash(other))
    }
}

impl<'tcx> Ord for Place<'tcx> {
    fn cmp(&self, other: &Self) -> Ordering {
        hash(self).cmp(&hash(other))
    }
}
