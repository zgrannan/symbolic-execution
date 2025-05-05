use pcg::PcgOutput;

use crate::{
    context::SymExContext,
    rustc_interface::{
        borrowck::consumers::RegionInferenceContext,
        hir::def_id::LocalDefId,
        middle::{
            mir::Body,
            ty::TyCtxt,
        },
    },
    semantics::VerifierSemantics,
};
pub struct SymExParams<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    pub def_id: LocalDefId,
    pub body: &'mir Body<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub fpcs_analysis: PcgOutput<'mir, 'tcx, &'sym bumpalo::Bump>,
    pub verifier_semantics: S,
    pub arena: &'sym SymExContext<'tcx>,
    pub debug_output_dir: Option<String>,
    pub new_symvars_allowed: bool,
    pub region_infer_ctxt: &'mir RegionInferenceContext<'tcx>,
}
