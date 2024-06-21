use crate::context::SymExContext;
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt},
    },
};
use crate::value::{SymValue, SyntheticSymValue};

pub trait VerifierSemantics<'sym, 'tcx> {
    type SymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
    fn encode_fn_call(
        &self,
        arena: &'sym SymExContext,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        args: &'sym [SymValue<'sym, 'tcx, Self::SymValSynthetic>],
    ) -> Option<SymValue<'sym, 'tcx, Self::SymValSynthetic>>;
}
