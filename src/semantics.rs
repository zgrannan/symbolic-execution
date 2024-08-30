use std::collections::BTreeSet;

use crate::context::SymExContext;
use crate::heap::{HeapData, SymbolicHeap};
use crate::path::{InputPlace, OldMap};
use crate::path_conditions::PathConditions;
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Body, Operand},
        ty::{self, GenericArgsRef},
    },
};
use crate::terminator::FunctionCallEffects;
use crate::value::{SymValue, SymVar, SyntheticSymValue};
use crate::SymbolicExecution;

pub trait VerifierSemantics<'sym, 'tcx>: std::marker::Sized {
    type SymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
    type OldMapSymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
    fn encode_loop_invariant_assumption<'heap, 'mir: 'heap>(
        def_id: DefId,
        block: mir::BasicBlock,
        heap: &mut SymbolicHeap<'heap, 'mir, 'sym, 'tcx, Self::SymValSynthetic>,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
    ) -> BTreeSet<(
        PathConditions<'sym, 'tcx, Self::SymValSynthetic>,
        SymValue<'sym, 'tcx, Self::SymValSynthetic>,
    )>;
    fn encode_fn_call<'mir>(
        location: mir::Location,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut HeapData<'sym, 'tcx, Self::SymValSynthetic>,
        old_map: &mut OldMap<'sym, 'tcx, Self::OldMapSymValSynthetic>,
        args: &Vec<Operand<'tcx>>,
    ) -> Option<FunctionCallEffects<'sym, 'tcx, Self::SymValSynthetic, Self::OldMapSymValSynthetic>>;
}
