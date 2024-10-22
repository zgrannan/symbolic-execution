use crate::predicate::Predicate;

pub type PathConditions<'sym, 'tcx, T> = Predicate<'sym, 'tcx, T>;
