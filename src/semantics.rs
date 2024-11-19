use crate::heap::HeapData;
use crate::path::Path;
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Operand, Location},
        ty::GenericArgsRef,
    },
    span::Span,
};
use crate::terminator::FunctionCallEffects;
use crate::value::SyntheticSymValue;
use crate::{Assertion, SymbolicExecution};

pub trait VerifierSemantics<'sym, 'tcx>: std::marker::Sized {
    type SymValSynthetic: Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;

    /// Symbolic execution calls this function at the condition_valid_block
    fn encode_loop_invariant<'heap, 'mir: 'heap>(
        loop_head: mir::BasicBlock,
        path: Path<'sym, 'tcx, Self::SymValSynthetic>,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
    ) -> Vec<Assertion<'sym, 'tcx, Self::SymValSynthetic>>;
    fn encode_fn_call<'mir>(
        span: Span,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut HeapData<'sym, 'tcx, Self::SymValSynthetic>,
        args: &Vec<&Operand<'tcx>>,
        location: Location,
    ) -> Option<FunctionCallEffects<'sym, 'tcx, Self::SymValSynthetic>>;
}
