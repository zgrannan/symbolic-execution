#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(let_chains)]
#![feature(anonymous_lifetime_in_impl_trait)]

pub mod context;
mod debug_info;
pub mod encoder;
mod execute;
mod function_call_snapshot;
pub mod havoc;
pub mod heap;
mod r#loop;
pub mod path;
pub mod path_conditions;
mod pcs_interaction;
pub mod place;
pub mod results;
mod rustc_interface;
pub mod semantics;
mod stmt;
pub mod terminator;
pub mod transform;
mod util;
pub mod value;
pub mod visualization;

use std::marker::PhantomData;

use crate::{
    rustc_interface::{
        ast::Mutability,
        hir::def_id::{DefId, LocalDefId},
        middle::{
            mir::{self, Body, Local, Location, PlaceElem, ProjectionElem, VarDebugInfo},
            ty::{self, GenericArgsRef, TyCtxt},
        },
    },
    value::BackwardsFn,
};
use context::{ErrorContext, ErrorLocation, SymExContext};
use function_call_snapshot::FunctionCallSnapshots;
use havoc::LoopData;
use heap::{HeapData, SymbolicHeap};
use path::{LoopPath, SymExPath};
use path_conditions::PathConditions;
use pcs::{
    borrows::{
        domain::{MaybeOldPlace, MaybeRemotePlace},
        latest::Latest,
        unblock_graph::UnblockGraph,
    },
    combined_pcs::UnblockAction,
    free_pcs::RepackOp,
    utils::PlaceRepacker,
    FpcsOutput,
};
use pcs_interaction::PcsLocation;
use results::{BackwardsFacts, ResultPath, ResultPaths, SymbolicExecutionResult};
use semantics::VerifierSemantics;
use transform::SymValueTransformer;
use value::{CanSubst, Constant, Substs, SymVar, SyntheticSymValue};
use visualization::{OutputMode, VisFormat};

use self::{
    path::{AcyclicPath, Path},
    place::Place,
    value::{AggregateKind, SymValue},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Assertion<'sym, 'tcx, T> {
    Value(SymValue<'sym, 'tcx, T>),
    Precondition(DefId, GenericArgsRef<'tcx>, &'sym [SymValue<'sym, 'tcx, T>]),
    Implication(Box<Assertion<'sym, 'tcx, T>>, Box<Assertion<'sym, 'tcx, T>>),
    PathConditions(PathConditions<'sym, 'tcx, T>),
}

impl<'sym, 'tcx, T> Assertion<'sym, 'tcx, T> {
    pub fn implication(lhs: Assertion<'sym, 'tcx, T>, rhs: Assertion<'sym, 'tcx, T>) -> Self {
        Assertion::Implication(Box::new(lhs), Box::new(rhs))
    }
    pub fn false_(arena: &'sym SymExContext<'tcx>) -> Self {
        Assertion::Value(arena.mk_constant(Constant::from_bool(arena.tcx, false)))
    }
    pub fn from_value(value: SymValue<'sym, 'tcx, T>) -> Self {
        Assertion::Value(value)
    }
    pub fn from_path_conditions(pcs: PathConditions<'sym, 'tcx, T>) -> Self {
        Assertion::PathConditions(pcs)
    }
}

impl<
        'sym,
        'tcx,
        T: Copy + Clone + std::fmt::Debug + SyntheticSymValue<'sym, 'tcx> + CanSubst<'sym, 'tcx>,
    > Assertion<'sym, 'tcx, T>
{
    pub fn apply_transformer(
        self,
        arena: &'sym SymExContext<'tcx>,
        transformer: &mut impl SymValueTransformer<'sym, 'tcx, T>,
    ) -> Self {
        match self {
            Assertion::Value(value) => {
                Assertion::Value(value.apply_transformer(arena, transformer))
            }
            Assertion::Precondition(def_id, generics, args) => Assertion::Precondition(
                def_id,
                generics,
                arena.alloc_slice(
                    &args
                        .into_iter()
                        .map(|arg| arg.apply_transformer(arena, transformer))
                        .collect::<Vec<_>>(),
                ),
            ),
            Assertion::PathConditions(pcs) => {
                Assertion::PathConditions(pcs.apply_transformer(arena, transformer))
            }
            Assertion::Implication(lhs, rhs) => Assertion::Implication(
                Box::new(lhs.apply_transformer(arena, transformer)),
                Box::new(rhs.apply_transformer(arena, transformer)),
            ),
        }
    }

    pub fn subst<'substs>(
        self,
        arena: &'sym SymExContext<'tcx>,
        substs: &'substs Substs<'sym, 'tcx, T>,
    ) -> Assertion<'sym, 'tcx, T> {
        match self {
            Assertion::Precondition(def_id, generics, args) => Assertion::Precondition(
                def_id,
                generics,
                arena.alloc_slice(
                    &args
                        .into_iter()
                        .map(|arg| arg.subst(arena, substs))
                        .collect::<Vec<_>>(),
                ),
            ),
            Assertion::Value(val) => Assertion::Value(val.subst(arena, substs)),
            Assertion::Implication(lhs, rhs) => Assertion::Implication(
                Box::new(lhs.subst(arena, substs)),
                Box::new(rhs.subst(arena, substs)),
            ),
            Assertion::PathConditions(pcs) => Assertion::PathConditions(pcs.subst(arena, substs)),
        }
    }
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for Assertion<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        match self {
            Assertion::Value(val) => val.to_vis_string(tcx, debug_info, mode),
            Assertion::Precondition(def_id, _substs, args) => {
                format!(
                    "{:?}({})",
                    def_id,
                    args.to_vis_string(tcx, debug_info, mode)
                )
            }
            Assertion::Implication(lhs, rhs) => {
                format!(
                    "({} => {})",
                    lhs.to_vis_string(tcx, debug_info, mode),
                    rhs.to_vis_string(tcx, debug_info, mode)
                )
            }
            Assertion::PathConditions(pcs) => pcs.to_vis_string(tcx, debug_info, mode),
        }
    }
}

pub struct SymbolicExecution<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: LocalDefId,
    pub body: &'mir Body<'tcx>,
    fpcs_analysis: FpcsOutput<'mir, 'tcx>,
    havoc: LoopData,
    fresh_symvars: Vec<ty::Ty<'tcx>>,
    pub arena: &'sym SymExContext<'tcx>,
    debug_output_dir: Option<String>,
    err_ctx: Option<ErrorContext>,
    verifier_semantics: PhantomData<S>,
    new_symvars_allowed: bool,
    result_paths: ResultPaths<'sym, 'tcx, S::SymValSynthetic>,
    debug_paths: Vec<Path<'sym, 'tcx, S::SymValSynthetic>>,
}

trait LookupType {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone + VisFormat>: std::fmt::Debug + VisFormat;
    #[allow(unused)]
    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone + VisFormat>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>>;
}

struct LookupGet;
struct LookupTake;

impl LookupType for LookupGet {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone + VisFormat> =
        &'heap HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone + VisFormat>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        heap.get(place)
    }
}

impl LookupType for LookupTake {
    type Heap<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone + VisFormat> =
        &'heap mut HeapData<'sym, 'tcx, S>;

    fn lookup<'heap, 'sym: 'heap, 'tcx: 'sym, S: 'sym + std::fmt::Debug + Clone + VisFormat>(
        heap: Self::Heap<'heap, 'sym, 'tcx, S>,
        place: &MaybeOldPlace<'tcx>,
    ) -> Option<SymValue<'sym, 'tcx, S>> {
        // TODO: In principle we could make take actually remove from the heap, but
        // doing so would require a bit of refactoring
        heap.get(place)
    }
}

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub fn new(params: SymExParams<'mir, 'sym, 'tcx, S>) -> Self {
        SymbolicExecution {
            new_symvars_allowed: params.new_symvars_allowed,
            tcx: params.tcx,
            def_id: params.def_id,
            body: params.body,
            fpcs_analysis: params.fpcs_analysis,
            havoc: LoopData::new(&params.body),
            verifier_semantics: PhantomData,
            arena: params.arena,
            debug_output_dir: params.debug_output_dir,
            err_ctx: None,
            fresh_symvars: vec![],
            result_paths: ResultPaths::new(),
            debug_paths: vec![],
        }
    }

    fn set_error_context(&mut self, path: SymExPath, location: ErrorLocation) {
        self.err_ctx = Some(ErrorContext {
            def_id: self.def_id,
            location,
            path,
        });
    }

    fn mk_internal_err_expr(
        &self,
        err: String,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        self.arena.mk_internal_error(err, ty, self.err_ctx.as_ref())
    }

    fn encode_place_opt<'heap, T: LookupType, P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &self,
        heap: &SymbolicHeap<'heap, '_, 'sym, 'tcx, S::SymValSynthetic>,
        place: &P,
    ) -> Option<SymValue<'sym, 'tcx, S::SymValSynthetic>> {
        let place: MaybeOldPlace<'tcx> = (*place).into();
        if let Some(PlaceElem::Deref) = place.place().projection.last() {
            if let Some(base_place) = place.place().prefix_place(self.repacker()) {
                if base_place.is_ref(self.body, self.tcx) {
                    return Some(
                        self.arena.mk_projection(
                            ProjectionElem::Deref,
                            heap.0
                                .get(&MaybeOldPlace::new(base_place, place.location()))?,
                        ),
                    );
                }
            }
        }
        heap.0.get(&place)
    }

    /// Encodes the symbolic value that the place currently holds. In the most
    /// simple cases, this is simply a heap lookup. If the place to lookup is a
    /// reference, we return a reference to the dereferenced value in the heap.
    fn encode_maybe_old_place<'heap, T: LookupType, P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &self,
        heap: &mut SymbolicHeap<'heap, '_, 'sym, 'tcx, S::SymValSynthetic>,
        place: &P,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        let heap_str =
            heap.0
                .to_vis_string(Some(self.tcx), &self.body.var_debug_info, OutputMode::Text);
        self.encode_place_opt::<T, P>(heap, place)
            .unwrap_or_else(|| {
                let place = (*place).into();
                self.mk_internal_err_expr(
                    format!(
                        "Heap lookup failed for place [{}: {:?}] in {}",
                        place.to_short_string(self.repacker()),
                        place.place().ty(self.repacker()),
                        heap_str
                    ),
                    place.place().ty(self.repacker()).ty,
                )
            })
    }

    fn apply_unblock_actions(
        &mut self,
        actions: Vec<UnblockAction<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: &FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        for action in actions {
            match action {
                UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                    is_mut,
                    ..
                } => {
                    self.handle_removed_reborrow(
                        blocked_place,
                        &assigned_place,
                        is_mut,
                        heap,
                        location,
                    );
                }
                UnblockAction::Collapse(place, places) => {
                    self.collapse_place_from(place, places[0], heap, location);
                }
                UnblockAction::TerminateAbstraction(_, typ) => match &typ {
                    pcs::borrows::domain::AbstractionType::Loop(lp) => {
                        for edge in lp.edges() {
                            for input in edge.inputs() {
                                match input {
                                    pcs::borrows::domain::AbstractionTarget::Place(place) => {
                                        if let Some(place) = place.as_local_place() {
                                            heap.insert_maybe_old_place(
                                                place,
                                                self.mk_fresh_symvar(place.ty(self.repacker()).ty),
                                            );
                                        }
                                    }
                                    pcs::borrows::domain::AbstractionTarget::RegionProjection(
                                        _,
                                    ) => {
                                        {} // TODO
                                    }
                                }
                            }
                        }
                    }
                    pcs::borrows::domain::AbstractionType::FunctionCall(c) => {
                        let snapshot = function_call_snapshots.get_snapshot(&c.location());
                        for (idx, edge) in c.edges() {
                            for input in edge.inputs() {
                                for output in edge.outputs() {
                                    match input {
                                        pcs::borrows::domain::AbstractionTarget::Place(place) => {
                                            let place = place.as_local_place().unwrap();
                                            let assigned_place = match output {
                                                pcs::borrows::domain::AbstractionTarget::Place(
                                                    place,
                                                ) => place,
                                                _ => {
                                                    // TODO
                                                    continue;
                                                }
                                            };
                                            let value = self
                                                .arena
                                                .mk_backwards_fn(BackwardsFn::new(
                                                self.arena.tcx,
                                                c.def_id(),
                                                c.substs(),
                                                Some(self.def_id.into()),
                                                snapshot.args,
                                                self.arena.mk_ref(
                                                    self.encode_maybe_old_place::<LookupGet, _>(
                                                        heap,
                                                        &assigned_place,
                                                    ),
                                                    Mutability::Mut,
                                                ),
                                                Local::from_usize(*idx + 1),
                                            ));
                                            assert!(!snapshot.args[*idx]
                                                .kind
                                                .ty(self.tcx)
                                                .rust_ty()
                                                .is_primitive());
                                            assert_eq!(
                                                value.ty(self.tcx),
                                                snapshot.args[*idx].ty(self.tcx)
                                            );
                                            heap.insert_maybe_old_place(
                                                place,
                                                self.arena
                                                    .mk_projection(ProjectionElem::Deref, value),
                                            );
                                        }
                                        _ => {
                                            // TODO: Region projection
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
            }
        }
    }

    fn compute_backwards_facts(
        &mut self,
        path: &AcyclicPath,
        heap_data: &HeapData<'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
    ) -> BackwardsFacts<'sym, 'tcx, S::SymValSynthetic> {
        let return_place: mir::Place<'tcx> = mir::RETURN_PLACE.into();
        let return_place: Place<'tcx> = return_place.into();
        let mut facts = BackwardsFacts::new();
        if return_place.is_mut_ref(self.body, self.tcx) {
            let mut borrow_state = pcs.extra.after.clone();
            borrow_state.filter_for_path(path.blocks());
            for arg in self.body.args_iter() {
                let arg_place: mir::Place<'tcx> = arg.into();
                let arg_place: Place<'tcx> = arg_place.into();
                if arg_place.is_mut_ref(self.body, self.tcx) {
                    let remote_place = MaybeRemotePlace::place_assigned_to_local(arg);
                    let blocked_place = match borrow_state.get_place_blocking(remote_place) {
                        Some(blocked_place) => blocked_place,
                        None => {
                            eprintln!(
                                "{:?} No blocked place found for {:?} in path {:?}",
                                self.def_id, remote_place, path
                            );
                            continue;
                        }
                    };
                    let mut heap = heap_data.clone();
                    let mut heap = SymbolicHeap::new(&mut heap, self.tcx, self.body, &self.arena);
                    heap.insert(
                        return_place.project_deref(self.repacker()),
                        self.arena.mk_var(
                            SymVar::ReservedBackwardsFnResult,
                            return_place
                                .project_deref(self.repacker())
                                .ty(self.body, self.tcx)
                                .ty,
                        ),
                        pcs.location,
                    );
                    let ug = UnblockGraph::for_place(
                        blocked_place.into(),
                        &borrow_state,
                        self.repacker(),
                    );
                    let actions = ug.actions(self.repacker());
                    self.apply_unblock_actions(
                        actions,
                        &mut heap,
                        &function_call_snapshots,
                        pcs.location,
                    );
                    facts.insert(
                        arg.index() - 1,
                        self.encode_maybe_old_place::<LookupGet, _>(&mut heap, &blocked_place),
                    );
                }
            }
        }
        facts
    }

    fn add_loop_path(&mut self, path: LoopPath, pcs: PathConditions<'sym, 'tcx, S::SymValSynthetic>)
    where
        S::SymValSynthetic: Eq,
    {
        self.result_paths.insert(ResultPath::loop_path(path, pcs));
    }

    fn complete_path(
        &mut self,
        path: Path<'sym, 'tcx, S::SymValSynthetic>,
        pcs_loc: &PcsLocation<'mir, 'tcx>,
    ) where
        S::SymValSynthetic: Eq,
    {
        match path.path {
            SymExPath::Loop(loop_path) => {
                self.add_loop_path(loop_path, path.pcs);
            }
            SymExPath::Acyclic(acyclic_path) => {
                self.add_return_path(
                    acyclic_path,
                    path.heap,
                    path.pcs,
                    path.function_call_snapshots,
                    pcs_loc,
                );
            }
        }
    }

    fn add_return_path(
        &mut self,
        path: AcyclicPath,
        mut heap_data: HeapData<'sym, 'tcx, S::SymValSynthetic>,
        path_conditions: PathConditions<'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        pcs_loc: &PcsLocation<'mir, 'tcx>,
    ) where
        S::SymValSynthetic: Eq,
    {
        let return_place: Place<'tcx> = mir::RETURN_PLACE.into();
        let mut heap = SymbolicHeap::new(&mut heap_data, self.tcx, self.body, &self.arena);
        let expr = self.encode_maybe_old_place::<LookupGet, _>(&mut heap, &return_place);
        let backwards_facts =
            self.compute_backwards_facts(&path, &heap_data, function_call_snapshots, pcs_loc);
        self.result_paths.insert(ResultPath::return_path(
            path,
            path_conditions,
            expr,
            backwards_facts,
            heap_data,
        ));
    }

    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx> {
        PlaceRepacker::new(&self.body, self.tcx)
    }

    fn havoc_operand_ref(
        &mut self,
        operand: &mir::Operand<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) -> Option<SymValue<'sym, 'tcx, S::SymValSynthetic>> {
        match operand {
            mir::Operand::Move(place) => {
                let place: Place<'tcx> = (*place).into();
                if let ty::TyKind::Ref(_, _ty, Mutability::Mut) =
                    place.ty(self.body, self.tcx).ty.kind()
                {
                    let sym_var = self.mk_fresh_symvar(place.ty(self.body, self.tcx).ty);
                    heap.insert_maybe_old_place(
                        MaybeOldPlace::new(place.0, Some(location)),
                        sym_var,
                    );
                    Some(sym_var)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn mk_fresh_symvar(&mut self, ty: ty::Ty<'tcx>) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        assert!(self.new_symvars_allowed);
        let var = SymVar::Fresh(self.fresh_symvars.len());
        self.fresh_symvars.push(ty);
        self.arena.mk_var(var, ty)
    }

    fn alloc_slice<T: Copy>(&self, t: &[T]) -> &'sym [T] {
        self.arena.alloc_slice(t)
    }

    fn explode_value(
        &self,
        place: &MaybeOldPlace<'tcx>,
        value: SymValue<'sym, 'tcx, S::SymValSynthetic>,
        places: impl Iterator<Item = MaybeOldPlace<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
        latest: &Latest,
    ) {
        let old_proj_len = place.place().projection.len();
        for f in places {
            assert_eq!(
                f.place().projection.len(),
                place.place().projection.len() + 1,
                "Place {:?} is not a direct descendant of {:?}",
                f.place(),
                place.place(),
            );
            let mut value = value;
            for elem in f.place().projection.iter().skip(old_proj_len) {
                value = self.arena.mk_projection(elem.clone(), value);
            }
            match f {
                MaybeOldPlace::Current { place: p } => {
                    heap.insert(p, value, location);
                    heap.insert_maybe_old_place(
                        MaybeOldPlace::new(p, Some(latest.get(&place.place()))),
                        value,
                    );
                }
                MaybeOldPlace::OldPlace(_) => heap.insert_maybe_old_place(f, value),
            }
        }
    }

    fn expand_place_with_guide(
        &self,
        place: &pcs::utils::Place<'tcx>,
        guide: &pcs::utils::Place<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
        latest: &Latest,
    ) {
        let value = match place.ty(self.fpcs_analysis.repacker()).ty.kind() {
            ty::TyKind::Ref(_, _, Mutability::Mut) => {
                self.encode_maybe_old_place::<LookupTake, _>(heap, place)
            }
            ty::TyKind::Ref(_, _, Mutability::Not) => {
                self.encode_maybe_old_place::<LookupGet, _>(heap, place)
            }
            _ => self.encode_maybe_old_place::<LookupTake, _>(heap, place),
        };
        let (field, rest, _) = place.expand_one_level(*guide, self.fpcs_analysis.repacker());
        self.explode_value(
            &MaybeOldPlace::Current { place: *place },
            value,
            std::iter::once(field)
                .chain(rest.into_iter())
                .map(|p| p.into()),
            heap,
            location,
            latest,
        );
    }

    fn collapse_place_from(
        &self,
        place: MaybeOldPlace<'tcx>,
        from: MaybeOldPlace<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        let place_ty = place.ty(self.fpcs_analysis.repacker());
        let args: Vec<_> = if from.place().is_downcast_of(place.place()).is_some()
            || place_ty.ty.is_box()
        {
            vec![heap.0.take(&from).unwrap_or_else(|| {
                self.mk_internal_err_expr(
                    format!("Place {:?} not found in heap[collapse]", from),
                    from.ty(self.fpcs_analysis.repacker()).ty,
                )
            })]
        } else {
            place
                .place()
                .expand_field(None, self.fpcs_analysis.repacker())
                .iter()
                .map(|p| {
                    let place_to_take: MaybeOldPlace<'tcx> =
                        MaybeOldPlace::new(p.clone(), place.location());
                    self.encode_place_opt::<LookupTake, MaybeOldPlace<'tcx>>(heap, &place_to_take)
                        .unwrap_or_else(|| {
                            self.mk_internal_err_expr(
                                format!("Place {:?} not found in heap[collapse]", place_to_take),
                                place_to_take.ty(self.fpcs_analysis.repacker()).ty,
                            )
                        })
                })
                .collect()
        };
        let value = self.arena.mk_aggregate(
            AggregateKind::pcs(place_ty.ty, place_ty.variant_index),
            self.arena.alloc_slice(&args),
        );
        if place.is_current() {
            heap.insert(place.place(), value, location);
        } else {
            heap.insert_maybe_old_place(place, value);
        }
    }

    fn handle_repack(
        &self,
        repack: &RepackOp<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
        latest: &Latest,
    ) {
        match repack {
            RepackOp::StorageDead(_) => todo!(),
            RepackOp::IgnoreStorageDead(_) => {}
            RepackOp::Weaken(_, _, _) => {}
            RepackOp::Expand(place, guide, _) => {
                self.expand_place_with_guide(place, guide, heap, location, latest)
            }
            RepackOp::Collapse(place, from, _) => {
                self.collapse_place_from((*place).into(), (*from).into(), heap, location)
            }
            RepackOp::DerefShallowInit(_, _) => todo!(),
        }
    }
}

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

pub fn run_symbolic_execution<
    'mir,
    'sym,
    'tcx,
    S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat> + 'sym,
>(
    params: SymExParams<'mir, 'sym, 'tcx, S>,
) -> SymbolicExecutionResult<'sym, 'tcx, S::SymValSynthetic>
where
    S::SymValSynthetic: Eq,
{
    let heap_data = HeapData::init_for_body(params.arena, params.tcx, params.body);
    SymbolicExecution::new(params).execute(heap_data)
}
