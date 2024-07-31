use crate::context::SymExContext;
use crate::heap::HeapData;
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, Operand, VarDebugInfo},
        ty::{self, GenericArgsRef, TyCtxt},
    },
};
use crate::terminator::FunctionCallEffects;
use crate::value::{SymValue, SyntheticSymValue};
use crate::SymbolicExecution;

pub trait VerifierSemantics<'sym, 'tcx> : std::marker::Sized {
    type SymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
    fn encode_fn_call<'mir>(
        location: mir::Location,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &HeapData<'sym, 'tcx, Self::SymValSynthetic>,
        args: &Vec<Operand<'tcx>>,
    ) -> Option<FunctionCallEffects<'sym, 'tcx, Self::SymValSynthetic>>;
}
