use pcs::FpcsOutput;

use crate::{
    context::SymExContext,
    rustc_interface::{
        ast::Mutability,
        hir::def_id::{DefId, LocalDefId},
        middle::{
            mir::{self, Body, Local, Location, PlaceElem, ProjectionElem, VarDebugInfo},
            ty::{self, GenericArgsRef, TyCtxt},
        },
    },
    semantics::VerifierSemantics,
    value::BackwardsFn,
};
pub struct SymExParams<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    pub def_id: LocalDefId,
    pub body: &'mir Body<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    pub verifier_semantics: S,
    pub arena: &'sym SymExContext<'tcx>,
    pub debug_output_dir: Option<String>,
    pub new_symvars_allowed: bool,
}
