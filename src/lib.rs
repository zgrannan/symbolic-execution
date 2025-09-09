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
pub mod params;
pub mod path;
pub mod path_conditions;
mod pcs_interaction;
pub mod place;
pub mod predicate;
pub mod results;
mod rustc_interface;
pub mod semantics;
mod stmt;
pub mod terminator;
pub mod transform;
mod util;
pub mod value;
pub mod visualization;

use crate::{
    rustc_interface::{
        ast::Mutability,
        borrowck::consumers::RegionInferenceContext,
        hir::def_id::LocalDefId,
        middle::{
            mir::{self, Body, Local, Location, PlaceElem, ProjectionElem},
            ty::{self, TyCtxt},
        },
    },
    value::BackwardsFn,
};
use context::{ErrorContext, ErrorLocation, SymExContext};
use function_call_snapshot::FunctionCallSnapshots;
use havoc::LoopData;
use heap::{HeapData, SymbolicHeap};
use params::SymExParams;
use path::{LoopPath, SymExPath};
use path_conditions::PathConditions;
use pcg::utils::display::DisplayWithCompilerCtxt;
use pcg::utils::maybe_old::{MaybeLabelledPlace, MaybeOldPlace};
use pcg::utils::maybe_remote::MaybeRemotePlace;
use pcg::utils::HasPlace;
use pcg::{borrow_pcg::edge::abstraction::AbstractionType, pcg::MaybeHasLocation};
use pcg::{borrow_pcg::edge::kind::BorrowPcgEdgeKind, pcg::EvalStmtPhase};
use pcg::{borrow_pcg::edge::outlives::BorrowFlowEdgeKind, free_pcs::RepackCollapse};
use pcg::{borrow_pcg::edge_data::EdgeData, PcgOutput};
use pcg::{
    borrow_pcg::{
        region_projection::RegionProjection, unblock_graph::BorrowPcgUnblockAction,
        unblock_graph::UnblockGraph,
    },
    utils::CompilerCtxt,
};
use pcg::{free_pcs::RepackExpand, results::PcgLocation, utils::AnalysisLocation};
use pcg::{pcg::PcgNode, utils::SnapshotLocation};
use predicate::Predicate;
use results::{BackwardsFacts, ResultPath, ResultPaths, SymbolicExecutionResult};
use semantics::VerifierSemantics;
use value::{Constant, SymVar};
use visualization::{OutputMode, VisFormat};

use self::{
    path::{AcyclicPath, Path},
    place::Place,
    value::{AggregateKind, SymValue},
};

pub type Assertion<'sym, 'tcx, T> = Predicate<'sym, 'tcx, T>;

impl<'sym, 'tcx, T> Assertion<'sym, 'tcx, T> {
    pub fn false_(arena: &'sym SymExContext<'tcx>) -> Self {
        Assertion::Value(arena.mk_constant(Constant::from_bool(arena.tcx, false)))
    }
}

impl<'sym, 'tcx, T> From<SymValue<'sym, 'tcx, T>> for Assertion<'sym, 'tcx, T> {
    fn from(value: SymValue<'sym, 'tcx, T>) -> Self {
        Assertion::Value(value)
    }
}

pub struct SymbolicExecution<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx>> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: LocalDefId,
    pub body: &'mir Body<'tcx>,
    fpcs_analysis: PcgOutput<'mir, 'tcx>,
    havoc: LoopData,
    fresh_symvars: Vec<ty::Ty<'tcx>>,
    pub arena: &'sym SymExContext<'tcx>,
    debug_output_dir: Option<String>,
    err_ctx: Option<ErrorContext>,
    pub verifier_semantics: S,
    new_symvars_allowed: bool,
    result_paths: ResultPaths<'sym, 'tcx, S::SymValSynthetic>,
    debug_paths: Vec<Path<'sym, 'tcx, S::SymValSynthetic>>,
    region_infer_ctxt: &'mir RegionInferenceContext<'tcx>,
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
        heap.take(place)
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
            verifier_semantics: params.verifier_semantics,
            arena: params.arena,
            debug_output_dir: params.debug_output_dir,
            err_ctx: None,
            fresh_symvars: vec![],
            result_paths: ResultPaths::new(),
            debug_paths: vec![],
            region_infer_ctxt: params.region_infer_ctxt,
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

    /// Encodes the symbolic value of the place in the heap. In the most
    /// simple cases, this is simply a heap lookup. If the place to lookup is a
    /// dereference, we return a dereference to the base value in the heap.
    fn encode_place_opt<'heap, T: LookupType, P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &self,
        heap: T::Heap<'heap, 'sym, 'tcx, S::SymValSynthetic>,
        place: &P,
    ) -> Option<SymValue<'sym, 'tcx, S::SymValSynthetic>> {
        let place: MaybeOldPlace<'tcx> = (*place).into();
        if let Some(PlaceElem::Deref) = place.place().projection.last() {
            if let Some(base_place) = place.place().prefix_place() {
                if base_place.is_ref(self.ctxt()) {
                    return Some(self.arena.mk_projection(
                        ProjectionElem::Deref,
                        T::lookup(heap, &MaybeOldPlace::new(base_place, place.location()))?,
                    ));
                }
            }
        }
        T::lookup(heap, &place)
    }

    fn encode_maybe_old_place<'heap, T: LookupType, P: Into<MaybeOldPlace<'tcx>> + Copy>(
        &self,
        heap: T::Heap<'heap, 'sym, 'tcx, S::SymValSynthetic>,
        place: &P,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic>
    where
        'sym: 'heap,
        'tcx: 'sym,
    {
        let heap_str =
            heap.to_vis_string(Some(self.tcx), &self.body.var_debug_info, OutputMode::Text);
        self.encode_place_opt::<T, P>(heap, place)
            .unwrap_or_else(move || {
                let place = (*place).into();
                self.mk_internal_err_expr(
                    format!(
                        "Heap lookup failed for place [{}: {:?}] in {}",
                        place.to_short_string(self.ctxt()),
                        place.place().ty(self.ctxt()),
                        heap_str
                    ),
                    place.place().ty(self.ctxt()).ty,
                )
            })
    }

    fn apply_unblock_action(
        &mut self,
        action: BorrowPcgUnblockAction<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: &FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        prev_snapshot_location: SnapshotLocation,
        curr_snapshot_location: SnapshotLocation,
    ) {
        match action.edge().kind() {
            BorrowPcgEdgeKind::Borrow(borrow) => {
                if borrow.is_mut(self.ctxt()) {
                    self.handle_removed_borrow(
                        borrow.blocked_place(),
                        &borrow.deref_place(self.ctxt()),
                        heap,
                        curr_snapshot_location,
                    );
                }
            }
            BorrowPcgEdgeKind::Deref(deref_edge) => {
                let base_place = deref_edge.blocked_place();
                let expansion_place = deref_edge.deref_place();
                self.collapse_place_from(base_place, expansion_place, heap, curr_snapshot_location);
            }
            BorrowPcgEdgeKind::BorrowPcgExpansion(borrow_pcg_expansion) => {
                match (
                    borrow_pcg_expansion.base(),
                    borrow_pcg_expansion.expansion()[0],
                ) {
                    (PcgNode::Place(base), PcgNode::Place(expansion)) => {
                        self.collapse_place_from(base, expansion, heap, curr_snapshot_location);
                    }
                    _ => {
                        // TODO: handle errors
                    }
                }
            }
            BorrowPcgEdgeKind::Abstraction(abstraction_edge) => match &abstraction_edge {
                AbstractionType::FunctionCall(c) => {
                    // A snapshot may not exist if the call is specification "ghost" code, e.g. old()
                    // statements applied to mutable refs in Prusti.
                    if let Some(snapshot) = function_call_snapshots.get_snapshot(&c.location()) {
                        let input = c.edge().input();
                        let output = c.edge().output();
                        let Some(input) = input.try_to_local_lifetime_projection() else {
                            return;
                        };
                        let idx = snapshot.index_of_arg_local(input.local());
                        let input_place = match input.deref(self.ctxt()) {
                            Some(place) => place,
                            None => {
                                // TODO: region projection
                                return;
                            }
                        };
                        let output_place = match (*output).deref(self.ctxt()) {
                            Some(place) => place,
                            None => {
                                // TODO: region projection
                                return;
                            }
                        };
                        if input_place == output_place {
                            // This is the abstraction edge connecting the "before" and "after"
                            // values of function call inputs. For now we ignore this.
                            return;
                        }
                        let value = self.arena.mk_backwards_fn(BackwardsFn::new(
                            self.arena.tcx,
                            c.def_id().unwrap(),
                            c.substs().unwrap(),
                            Some(self.def_id.into()),
                            snapshot.args(),
                            self.arena.mk_ref(
                                self.encode_maybe_old_place::<LookupGet, _>(heap.0, &output_place),
                                Mutability::Mut,
                            ),
                            Local::from_usize(idx + 1),
                        ));
                        assert!(!snapshot.arg(idx).kind.ty(self.tcx).rust_ty().is_primitive());
                        assert_eq!(value.ty(self.tcx), snapshot.arg(idx).ty(self.tcx));
                        heap.insert_maybe_old_place(
                            input_place,
                            self.arena.mk_projection(ProjectionElem::Deref, value),
                        );
                    }
                }
                _ => {
                    if let PcgNode::Place(MaybeRemotePlace::Local(place)) =
                        *abstraction_edge.input(self.ctxt())
                    {
                        heap.insert(
                            place,
                            self.mk_fresh_symvar(place.ty(self.ctxt()).ty),
                            curr_snapshot_location,
                        );
                    }
                }
            },
            BorrowPcgEdgeKind::BorrowFlow(block_edge) => {
                if matches!(block_edge.kind(), BorrowFlowEdgeKind::Move) {
                    self.handle_removed_borrow(
                        block_edge.long().deref(self.ctxt()).unwrap().into(),
                        &block_edge.short().deref(self.ctxt()).unwrap(),
                        heap,
                        curr_snapshot_location,
                    );
                }
                for input in block_edge.blocked_nodes(self.ctxt()) {
                    if let Ok(place) = TryInto::<MaybeOldPlace<'tcx>>::try_into(input) {
                        heap.insert(
                            place,
                            self.mk_fresh_symvar(place.ty(self.ctxt()).ty),
                            curr_snapshot_location,
                        );
                    }
                }
            }
        }
    }

    fn apply_unblock_actions(
        &mut self,
        actions: Vec<BorrowPcgUnblockAction<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: &FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        prev_snapshot_location: SnapshotLocation,
        curr_snapshot_location: SnapshotLocation,
    ) {
        for action in actions {
            self.apply_unblock_action(
                action,
                heap,
                function_call_snapshots,
                prev_snapshot_location,
                curr_snapshot_location,
            );
        }
    }

    #[tracing::instrument(skip(self, path, heap_data, function_call_snapshots, pcs))]
    fn compute_backwards_facts(
        &mut self,
        path: &AcyclicPath,
        heap_data: &HeapData<'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcgLocation<'tcx>,
    ) -> BackwardsFacts<'sym, 'tcx, S::SymValSynthetic> {
        let return_place: mir::Place<'tcx> = mir::RETURN_PLACE.into();
        let return_place: Place<'tcx> = return_place.into();
        let mut facts = BackwardsFacts::new();
        let prev_snapshot_location =
            SnapshotLocation::Before(AnalysisLocation::new(pcs.location, EvalStmtPhase::last()));
        let current_snapshot_location =
            SnapshotLocation::after_statement_at(pcs.location, self.ctxt());
        if return_place.is_mut_ref(self.body, self.tcx) {
            let borrow_state = {
                let mut mut_borrow_state = pcs.states[EvalStmtPhase::PostMain].borrow_pcg().clone();
                // let mut mut_borrow_state = pcs.borrows.post_main().clone();
                mut_borrow_state.filter_for_path(path.blocks(), self.ctxt());
                mut_borrow_state
            };
            for arg in self.body.args_iter() {
                let arg_place: mir::Place<'tcx> = arg.into();
                let arg_place: Place<'tcx> = arg_place.into();
                if arg_place.is_mut_ref(self.body, self.tcx) {
                    let remote_place = MaybeRemotePlace::place_assigned_to_local(arg);
                    let blocked_place =
                        match borrow_state.get_place_blocking(remote_place, self.ctxt()) {
                            Some(blocked_place) => {
                                eprintln!("Blocked place: {:?}", blocked_place);
                                blocked_place
                            }
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
                        return_place.project_deref(self.ctxt()),
                        self.arena.mk_var(
                            SymVar::ReservedBackwardsFnResult,
                            return_place
                                .project_deref(self.ctxt())
                                .ty(self.body, self.tcx)
                                .ty,
                        ),
                        current_snapshot_location,
                    );
                    let ug = UnblockGraph::for_node(blocked_place, &borrow_state, self.ctxt());

                    let actions = ug.actions(self.ctxt()).unwrap();
                    self.apply_unblock_actions(
                        actions,
                        &mut heap,
                        &function_call_snapshots,
                        prev_snapshot_location,
                        current_snapshot_location,
                    );
                    let blocked_place_value =
                        self.encode_maybe_old_place::<LookupGet, _>(heap.0, &blocked_place);
                    facts.insert(arg.index() - 1, blocked_place_value);
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
        pcs_loc: &PcgLocation<'tcx>,
    ) where
        S::SymValSynthetic: Eq,
    {
        let pcs = path.pcs().clone();
        match path.path {
            SymExPath::Loop(loop_path) => {
                self.add_loop_path(loop_path, pcs);
            }
            SymExPath::Acyclic(acyclic_path) => {
                self.add_return_path(
                    acyclic_path,
                    path.heap,
                    pcs,
                    path.function_call_snapshots,
                    pcs_loc,
                );
            }
        }
    }

    fn add_return_path(
        &mut self,
        path: AcyclicPath,
        heap_data: HeapData<'sym, 'tcx, S::SymValSynthetic>,
        path_conditions: PathConditions<'sym, 'tcx, S::SymValSynthetic>,
        function_call_snapshots: FunctionCallSnapshots<'sym, 'tcx, S::SymValSynthetic>,
        pcs_loc: &PcgLocation<'tcx>,
    ) where
        S::SymValSynthetic: Eq,
    {
        let return_place: Place<'tcx> = mir::RETURN_PLACE.into();
        let expr = self.encode_maybe_old_place::<LookupGet, _>(&heap_data, &return_place);
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

    pub fn ctxt(&self) -> CompilerCtxt<'mir, 'tcx> {
        self.fpcs_analysis.ctxt()
    }

    fn havoc_operand_ref(
        &mut self,
        operand: &mir::Operand<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: SnapshotLocation,
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
        base_value: SymValue<'sym, 'tcx, S::SymValSynthetic>,
        places: impl Iterator<Item = MaybeOldPlace<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
    ) {
        for f in places {
            let value = self
                .arena
                .mk_projection(f.last_projection().unwrap().1, base_value);
            heap.insert(f, value, curr_snapshot_location);
        }
    }

    fn handle_expand(
        &self,
        expand: RepackExpand<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
        take: bool,
    ) {
        let value = if take {
            self.encode_maybe_old_place::<LookupTake, _>(heap.0, &expand.from())
        } else {
            self.encode_maybe_old_place::<LookupGet, _>(heap.0, &expand.from())
        };
        let expansion = expand.target_places(self.fpcs_analysis.ctxt());
        self.explode_value(
            value,
            expansion.into_iter().map(|p| p.into()),
            heap,
            curr_snapshot_location,
        );
    }

    fn handle_collapse(
        &self,
        collapse: RepackCollapse<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
    ) {
        let args = if let Some(from) = collapse.box_deref_place(self.fpcs_analysis.ctxt()) {
            vec![heap.0.take(&from).unwrap_or_else(|| {
                self.mk_internal_err_expr(
                    format!("Place {:?} not found in heap[collapse]", from),
                    from.ty(self.fpcs_analysis.ctxt()).ty,
                )
            })]
        } else {
            let place_ty = collapse.to().ty(self.fpcs_analysis.ctxt());
            if place_ty.ty.is_enum() && place_ty.variant_index.is_none() {
                let place_to_take = heap.0.current_values().iter().find_map(|(p, _)| {
                    if p.is_downcast_of(collapse.to()).is_some() {
                        Some(*p)
                    } else {
                        None
                    }
                });
                vec![self
                    .encode_place_opt::<LookupTake, MaybeLabelledPlace<'tcx>>(
                        heap.0,
                        &place_to_take.unwrap().into(),
                    )
                    .unwrap()]
            } else {
                collapse
                    .to()
                    .expand_field(None, self.fpcs_analysis.ctxt())
                    .unwrap()
                    .iter()
                    .map(|p| {
                        let place_to_take: MaybeOldPlace<'tcx> = (*p).into();
                        self.encode_place_opt::<LookupTake, MaybeOldPlace<'tcx>>(
                            heap.0,
                            &place_to_take,
                        )
                        .unwrap_or_else(|| {
                            self.mk_internal_err_expr(
                                format!("Place {:?} not found in heap[collapse]", place_to_take),
                                place_to_take.ty(self.fpcs_analysis.ctxt()).ty,
                            )
                        })
                    })
                    .collect()
            }
        };
        let place_ty = collapse.to().ty(self.fpcs_analysis.ctxt());
        let value = self.arena.mk_aggregate(
            AggregateKind::pcs(place_ty.ty, place_ty.variant_index),
            self.arena.alloc_slice(&args),
        );
        heap.insert(collapse.to(), value, curr_snapshot_location);
    }

    fn collapse_place_from(
        &self,
        place: MaybeOldPlace<'tcx>,
        from: MaybeOldPlace<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
    ) {
        let place_ty = place.ty(self.fpcs_analysis.ctxt());
        let args: Vec<_> = if from.place().is_downcast_of(place.place()).is_some()
            || place_ty.ty.is_box()
        {
            vec![heap.0.take(&from).unwrap_or_else(|| {
                self.mk_internal_err_expr(
                    format!("Place {:?} not found in heap[collapse]", from),
                    from.ty(self.fpcs_analysis.ctxt()).ty,
                )
            })]
        } else {
            place
                .place()
                .expand_field(None, self.fpcs_analysis.ctxt())
                .unwrap()
                .iter()
                .map(|p| {
                    let place_to_take: MaybeOldPlace<'tcx> =
                        MaybeOldPlace::new(p.clone(), place.location());
                    self.encode_place_opt::<LookupTake, MaybeOldPlace<'tcx>>(heap.0, &place_to_take)
                        .unwrap_or_else(|| {
                            self.mk_internal_err_expr(
                                format!("Place {:?} not found in heap[collapse]", place_to_take),
                                place_to_take.ty(self.fpcs_analysis.ctxt()).ty,
                            )
                        })
                })
                .collect()
        };
        let value = self.arena.mk_aggregate(
            AggregateKind::pcs(place_ty.ty, place_ty.variant_index),
            self.arena.alloc_slice(&args),
        );
        heap.insert(place, value, curr_snapshot_location);
    }
}

pub fn run_symbolic_execution<
    'mir,
    'sym,
    'tcx,
    S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat> + 'sym,
>(
    params: SymExParams<'mir, 'sym, 'tcx, S>,
) -> SymbolicExecutionResult<'sym, 'tcx, S>
where
    S::SymValSynthetic: Eq,
{
    let heap_data = HeapData::init_for_body(params.arena, params.tcx, params.body);
    SymbolicExecution::new(params).execute(heap_data)
}
