use pcg::FpcsOutput;

use crate::{
    context::SymExContext,
    rustc_interface::{
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
    pub fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    pub verifier_semantics: S,
    pub arena: &'sym SymExContext<'tcx>,
    pub debug_output_dir: Option<String>,
    pub new_symvars_allowed: bool,
}
