use crate::heap::HeapData;
use crate::path::{InputPlace, OldMap};
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Operand},
        ty::GenericArgsRef,
    },
};
use crate::terminator::FunctionCallEffects;
use crate::value::{SymVar, SyntheticSymValue};
use crate::SymbolicExecution;

pub trait VerifierSemantics<'sym, 'tcx>: std::marker::Sized {
    type SymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
    type OldMapSymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
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
