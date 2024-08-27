use crate::heap::HeapData;
use crate::path::OldMap;
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::{
        mir::{self, Operand},
        ty::GenericArgsRef,
    },
};
use crate::terminator::FunctionCallEffects;
use crate::value::SyntheticSymValue;
use crate::SymbolicExecution;

pub trait VerifierSemantics<'sym, 'tcx> : std::marker::Sized {
    type SymValSynthetic: Clone + Ord + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx>;
    fn encode_fn_call<'mir>(
        location: mir::Location,
        sym_ex: &mut SymbolicExecution<'mir, 'sym, 'tcx, Self>,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        heap: &mut HeapData<'sym, 'tcx, Self::SymValSynthetic>,
        old_map: &OldMap<'sym, 'tcx, Self::SymValSynthetic>,
        args: &Vec<Operand<'tcx>>,
    ) -> Option<FunctionCallEffects<'sym, 'tcx, Self::SymValSynthetic>>;
}
