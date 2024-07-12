use std::ops::Deref;

use pcs::{
    borrows::{
        domain::{BorrowsState, Reborrow},
        engine::{BorrowsDomain, ReborrowAction},
    },
    combined_pcs::UnblockGraph,
    free_pcs::{CapabilitySummary, FreePcsLocation, RepackOp},
};

use crate::{
    heap::SymbolicHeap, semantics::VerifierSemantics, visualization::VisFormat, LookupGet,
    LookupTake, SymbolicExecution,
};

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub (crate) fn handle_pcs(
        &mut self,
        pcs: &FreePcsLocation<'tcx, BorrowsDomain<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        start: bool,
    ) {
        let reborrow_actions = pcs.extra.reborrow_actions(start);
        let borrow_state = if start {
            &pcs.extra.before_start
        } else {
            &pcs.extra.before_after
        };
        self.handle_reborrow_collapses(
            &reborrow_actions,
            borrow_state,
            &pcs.state,              // TODO: Not the state at the start
            heap,
        );
        let repacks = if start {
            &pcs.repacks_start
        } else {
            &pcs.repacks_middle
        };
        self.handle_repack_collapses(repacks, heap);
        self.handle_repack_expands(repacks, heap);
        self.handle_reborrow_expands(
            reborrow_actions,
            borrow_state,
            &pcs.state,              // TODO: Not the state at the start
            heap,
        );
    }
    pub(crate) fn handle_removed_reborrow(
        &self,
        reborrow: &Reborrow<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        match reborrow.assigned_place {
            pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                let heap_value = if reborrow.mutability.is_mut() {
                    self.encode_place::<LookupTake>(heap.0, &place.deref().into())
                } else {
                    self.encode_place::<LookupGet>(heap.0, &place.deref().into())
                };
                match reborrow.blocked_place {
                    pcs::borrows::domain::MaybeOldPlace::Current { place } => {
                        heap.insert(place.deref().into(), heap_value);
                    }
                    pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
                }
            }
            pcs::borrows::domain::MaybeOldPlace::OldPlace(_) => todo!(),
        }
    }
    pub(crate) fn handle_repack_collapses(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for repack in repacks {
            if matches!(repack, RepackOp::Collapse(..)) {
                self.handle_repack(repack, heap)
            }
        }
    }

    pub(crate) fn handle_reborrow_collapses(
        &mut self,
        reborrow_actions: &Vec<ReborrowAction<'tcx>>,
        borrows: &BorrowsState<'tcx>,
        fpcs: &CapabilitySummary<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) -> UnblockGraph<'tcx> {
        let mut unblock_graph = UnblockGraph::new();
        for action in reborrow_actions {
            match action {
                ReborrowAction::CollapsePlace(places, place) => {
                    unblock_graph.unblock_place(place.clone(), borrows, fpcs);
                }
                ReborrowAction::RemoveReborrow(rb) => {
                    unblock_graph.unblock_reborrow(rb.clone(), borrows, fpcs);
                }
                _ => {}
            }
        }

        self.apply_unblock_actions(unblock_graph.clone().actions(), &borrows.reborrows, heap);
        unblock_graph
    }

    pub(crate) fn handle_reborrow_expands(
        &mut self,
        reborrow_actions: Vec<ReborrowAction<'tcx>>,
        borrows: &BorrowsState<'tcx>,
        fpcs: &CapabilitySummary<'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        let mut places_to_expand = vec![];
        let mut reborrows_to_add = vec![];
        for action in reborrow_actions {
            match action {
                ReborrowAction::ExpandPlace(place, places) => {
                    places_to_expand.push((place, places));
                }
                ReborrowAction::AddReborrow(rb) => {
                    reborrows_to_add.push(rb);
                }
                _ => {}
            }
        }
        places_to_expand.sort_by_key(|(p, _)| p.place().projection.len());
        for (place, places) in places_to_expand {
            if place.place().projection.len() == 0 {
                // The expansion from x to *x isn't necessary!
                continue;
            }
            let value = if place
                .place()
                .projects_shared_ref(self.fpcs_analysis.repacker())
            {
                heap.0.get(&place.place().into())
            } else {
                heap.0.take(&place.place().into())
            };
            let value = value.unwrap_or_else(|| {
                self.arena.mk_internal_error(
                    format!(
                        "Place {:?} not found in heap[reborrow_expand]",
                        place.place()
                    ),
                    (*place.place()).ty(self.body, self.tcx).ty,
                )
            });

            // TODO: old places
            self.explode_value(
                &place.place(),
                value,
                places.iter().map(|p| (*p).into()),
                heap,
            );
        }

        for reborrow in reborrows_to_add {
            let blocked_value = if reborrow.mutability.is_mut() {
                self.encode_place::<LookupTake>(heap.0, &reborrow.blocked_place.place().into())
            } else {
                self.encode_place::<LookupGet>(heap.0, &reborrow.blocked_place.place().into())
            };
            heap.insert(reborrow.assigned_place.place().into(), blocked_value);
        }
    }

    pub(crate) fn handle_repack_expands(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for repack in repacks {
            if matches!(repack, RepackOp::Expand(..)) {
                self.handle_repack(repack, heap)
            }
        }
    }
}
