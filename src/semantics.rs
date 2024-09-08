use std::collections::BTreeSet;

use crate::heap::{HeapData, SymbolicHeap};
use crate::path::{OldMap, Path};
use crate::path_conditions::PathConditions;
use crate::rustc_interface::{
    hir::def_id::{DefId, LocalDefId},
    middle::{
        mir::{self, Operand},
        ty::GenericArgsRef,
    },
    span::Span,
};
use crate::terminator::FunctionCallEffects;
use crate::value::{SymValue, SyntheticSymValue};
use crate::SymbolicExecution;

pub trait VerifierSemantics<'sym, 'tcx>: std::marker::Sized {
    type SymValSynthetic: Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
    type OldMapSymValSynthetic: Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;

    /// Symbolic execution calls this function at the condition_valid_block
    fn encode_loop_invariant<'heap, 'mir: 'heap>(
        loop_head: mir::BasicBlock,
        path: Path<'sym, 'tcx, Self::SymValSynthetic, Self::OldMapSymValSynthetic>,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
    ) -> Vec<(
        PathConditions<'sym, 'tcx, Self::SymValSynthetic>,
        SymValue<'sym, 'tcx, Self::SymValSynthetic>,
    )>;
    fn encode_fn_call<'mir>(
        span: Span,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut HeapData<'sym, 'tcx, Self::SymValSynthetic>,
        old_map: &mut OldMap<'sym, 'tcx, Self::OldMapSymValSynthetic>,
        args: &Vec<&Operand<'tcx>>,
    ) -> Option<FunctionCallEffects<'sym, 'tcx, Self::SymValSynthetic, Self::OldMapSymValSynthetic>>;
}
