use crate::rustc_interface::hir::Mutability;
use crate::{path::Path, rustc_interface::middle::mir::Location};

use pcg::action::PcgActions;
use pcg::borrow_pcg::action::actions::BorrowPcgActions;
use pcg::borrow_pcg::action::BorrowPcgActionKind;
use pcg::borrow_pcg::borrow_pcg_expansion::BorrowPcgExpansion;
use pcg::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use pcg::free_pcs::{CapabilityKind, RepackOp};
use pcg::results::PcgLocation;
use pcg::pcg::EvalStmtPhase;
use pcg::utils::place::maybe_old::{MaybeLabelledPlace, MaybeOldPlace};
use pcg::utils::place::maybe_remote::MaybeRemotePlace;
use pcg::utils::SnapshotLocation;
use pcg::utils::{AnalysisLocation, HasPlace};

use crate::{
    heap::SymbolicHeap, semantics::VerifierSemantics, visualization::VisFormat, LookupGet,
    LookupTake, SymbolicExecution,
};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub(crate) fn handle_pcg(
        &mut self,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        pcg: &PcgLocation<'_, 'tcx>,
        location: Location,
    ) {
        let pre_operands_loc = AnalysisLocation::new(location, EvalStmtPhase::PreOperands);
        self.handle_pcg_partial(
            path,
            pcg.actions(EvalStmtPhase::PreOperands),
            SnapshotLocation::Before(pre_operands_loc),
            pre_operands_loc.next_snapshot_location(self.ctxt().body()),
        );

        let pre_main_loc = AnalysisLocation::new(location, EvalStmtPhase::PreMain);
        self.handle_pcg_partial(
            path,
            pcg.actions(EvalStmtPhase::PreMain),
            SnapshotLocation::Before(pre_main_loc),
            pre_main_loc.next_snapshot_location(self.ctxt().body()),
        );
        let post_main_loc = AnalysisLocation::new(location, EvalStmtPhase::PostMain);
        let curr_snapshot_location = SnapshotLocation::Before(post_main_loc);
        self.handle_borrow_pcg_added_edges(
            pcg.borrow_pcg_actions(EvalStmtPhase::PostMain),
            &mut SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena),
            curr_snapshot_location,
        );
    }
    pub(crate) fn handle_pcg_partial(
        &mut self,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        actions: &PcgActions<'tcx>,
        prev_snapshot_location: SnapshotLocation,
        curr_snapshot_location: SnapshotLocation,
    ) {
        let mut ug_actions = actions.borrow_pcg_unblock_actions();
        ug_actions.retain(|action| {
            action
                .edge()
                .valid_for_path(&path.path.blocks(), self.ctxt().body())
        });
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
        self.apply_unblock_actions(
            ug_actions,
            &mut heap,
            &path.function_call_snapshots,
            prev_snapshot_location,
            curr_snapshot_location,
        );
        let repacks = actions
            .owned_pcg_actions()
            .into_iter()
            .map(|action| action.kind())
            .collect::<Vec<_>>();
        self.handle_repack_collapses(&repacks, &mut heap, curr_snapshot_location);
        self.handle_repack_expands(&repacks, &mut heap, curr_snapshot_location);
        self.handle_borrow_pcg_added_edges(
            actions.borrow_pcg_actions(),
            &mut heap,
            curr_snapshot_location,
        );
    }

    fn handle_borrow_pcg_added_edges(
        &self,
        borrow_pcg_actions: BorrowPcgActions<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
    ) {
        for action in borrow_pcg_actions.iter() {
            if let BorrowPcgActionKind::AddEdge { edge, .. } = action.kind() {
                match edge.kind() {
                    BorrowPcgEdgeKind::Deref(deref_edge) => {
                        let value = self.encode_maybe_old_place::<LookupGet, _>(
                            heap.0,
                            &deref_edge.blocked_place(),
                        );

                        self.explode_value(
                            value,
                            vec![deref_edge.deref_place().into()].into_iter(),
                            heap,
                            curr_snapshot_location,
                        );
                    }
                    BorrowPcgEdgeKind::BorrowPcgExpansion(ep) => {
                        let ep: BorrowPcgExpansion<'tcx, MaybeOldPlace<'tcx>> =
                            if let Ok(ep) = (ep.clone()).try_into() {
                                ep
                            } else {
                                // Expansion of region projections are not supported
                                continue;
                            };
                        let place = ep.base();
                        let value = self.encode_maybe_old_place::<LookupGet, _>(heap.0, &place);

                        self.explode_value(
                            value,
                            ep.expansion().into_iter().copied(),
                            heap,
                            curr_snapshot_location,
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    pub(crate) fn handle_removed_borrow(
        &self,
        blocked_place: MaybeLabelledPlace<'tcx>,
        assigned_place: &MaybeOldPlace<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
    ) {
        let heap_value = self.encode_maybe_old_place::<LookupGet, _>(heap.0, assigned_place);

                if blocked_place.is_old() {
                    heap.insert_maybe_old_place(blocked_place, heap_value);
                } else {
                    heap.insert(blocked_place.place(), heap_value, curr_snapshot_location);
                }
    }

    pub(crate) fn handle_repack_collapses(
        &self,
        repacks: &[&RepackOp<'tcx>],
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
    ) {
        for repack in repacks {
            if let RepackOp::Collapse(collapse) = repack
                && collapse.capability() == CapabilityKind::Exclusive
            {
                self.handle_collapse(*collapse, heap, curr_snapshot_location)
            }
        }
    }

    pub(crate) fn handle_repack_expands(
        &self,
        repacks: &[&RepackOp<'tcx>],
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        curr_snapshot_location: SnapshotLocation,
    ) {
        for repack in repacks {
            if let RepackOp::Expand(expansion) = repack {
                let is_shared_ref = expansion
                    .from()
                    .ty(self.fpcs_analysis.ctxt())
                    .ty
                    .ref_mutability()
                    == Some(Mutability::Not);
                let take = expansion.capability() == CapabilityKind::Exclusive && !is_shared_ref;
                self.handle_expand(*expansion, heap, curr_snapshot_location, take)
            }
        }
    }
}
