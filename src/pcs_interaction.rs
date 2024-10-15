use crate::{
    path::{Path, SymExPath},
    rustc_interface::middle::mir::Location,
    value::SymValue,
    LookupType,
};

use pcs::{
    borrows::{
        deref_expansion::{BorrowDerefExpansion, DerefExpansion},
        domain::{MaybeOldPlace, MaybeRemotePlace, Reborrow},
        engine::BorrowsDomain,
        latest::Latest,
    },
    free_pcs::{FreePcsLocation, RepackOp},
    ReborrowBridge,
};

use crate::{
    heap::SymbolicHeap, semantics::VerifierSemantics, visualization::VisFormat, LookupGet,
    LookupTake, SymbolicExecution,
};

pub type PcsLocation<'mir, 'tcx> =
    FreePcsLocation<'tcx, BorrowsDomain<'mir, 'tcx>, ReborrowBridge<'tcx>>;

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub(crate) fn handle_pcs(
        &mut self,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
        start: bool,
        location: Location,
    ) {
        let bridge = if start {
            Some(pcs.extra_start.clone())
        } else {
            pcs.extra_middle.clone()
        };
        let (ug_actions, added_reborrows, reborrow_expands) = if let Some(mut bridge) = bridge {
            bridge.ug.filter_for_path(&path.path.blocks());
            (
                bridge.ug.actions(self.repacker()),
                bridge.added_reborrows,
                bridge.expands,
            )
        } else {
            (
                vec![],
                vec![].into_iter().collect(),
                vec![].into_iter().collect(),
            )
        };
        let mut heap = SymbolicHeap::new(&mut path.heap, self.tcx, &self.body, &self.arena);
        self.apply_unblock_actions(
            ug_actions,
            &mut heap,
            &path.function_call_snapshots,
            location,
        );
        let repacks = if start {
            &pcs.repacks_start
        } else {
            &pcs.repacks_middle
        };
        self.handle_repack_collapses(repacks, &mut heap, location, &pcs.extra.after.latest);
        self.handle_repack_expands(repacks, &mut heap, location, &pcs.extra.after.latest);
        self.handle_reborrow_expands(
            reborrow_expands.into_iter().map(|ep| ep.value).collect(),
            &mut heap,
            location,
            &pcs.extra.after.latest,
        );
        self.handle_added_reborrows(
            &added_reborrows
                .into_iter()
                .map(|r| r.value)
                .collect::<Vec<_>>(),
            &mut heap,
            &path.path,
        );
    }

    pub(crate) fn handle_removed_reborrow(
        &self,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: &MaybeOldPlace<'tcx>,
        is_mut: bool,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        if !is_mut {
            return;
        }
        let heap_value = self.encode_maybe_old_place::<LookupTake, _>(heap, assigned_place);
        match blocked_place {
            MaybeRemotePlace::Local(blocked_place) => {
                if blocked_place.is_old() {
                    heap.insert_maybe_old_place(blocked_place, heap_value);
                } else {
                    heap.insert(blocked_place.place(), heap_value, location);
                }
            }
            MaybeRemotePlace::Remote(_) => {
                // Presumably this is to determine the result value for a pledge
                // Don't do anything, we'll use the assigned place from the heap
            }
        }
    }

    pub(crate) fn handle_repack_collapses(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
        latest: &Latest,
    ) {
        for repack in repacks {
            if matches!(repack, RepackOp::Collapse(..)) {
                self.handle_repack(repack, heap, location, latest)
            }
        }
    }

    pub(crate) fn handle_reborrow_expands(
        &self,
        expands: Vec<DerefExpansion<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
        latest: &Latest,
    ) {
        // TODO: Explain why owned expansions don't need to be handled
        let mut expands: Vec<BorrowDerefExpansion<'tcx>> = expands
            .into_iter()
            .flat_map(|ep| ep.borrow_expansion().cloned())
            .collect();
        expands.sort_by_key(|ep| ep.base().place().projection.len());
        for ep in expands {
            let place = ep.base();
            let value = self.encode_maybe_old_place::<LookupGet, _>(heap, &place);

            self.explode_value(
                &place,
                value,
                ep.expansion(self.fpcs_analysis.repacker()).into_iter(),
                heap,
                location,
                latest,
            );
        }
    }

    pub(crate) fn handle_added_reborrows(
        &self,
        reborrows: &[Reborrow<'tcx>],
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        path: &SymExPath,
    ) {
        for reborrow in reborrows {
            if !path.contains(reborrow.reserve_location().block) {
                continue;
            }
            let blocked_value = if reborrow.mutability.is_mut() {
                self.encode_reborrow_blocked_place::<LookupTake>(heap, reborrow.blocked_place)
            } else {
                self.encode_reborrow_blocked_place::<LookupGet>(heap, reborrow.blocked_place)
            };
            heap.insert_maybe_old_place(reborrow.assigned_place, blocked_value);
        }
    }

    fn encode_reborrow_blocked_place<'heap, T: LookupType>(
        &self,
        heap: &mut SymbolicHeap<'heap, '_, 'sym, 'tcx, S::SymValSynthetic>,
        place: MaybeRemotePlace<'tcx>,
    ) -> SymValue<'sym, 'tcx, S::SymValSynthetic> {
        match place {
            MaybeRemotePlace::Local(place) => self.encode_maybe_old_place::<T, _>(heap, &place),
            MaybeRemotePlace::Remote(_) => {
                todo!()
            }
        }
    }

    pub(crate) fn handle_repack_expands(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
        latest: &Latest,
    ) {
        for repack in repacks {
            if matches!(repack, RepackOp::Expand(..)) {
                self.handle_repack(repack, heap, location, latest)
            }
        }
    }
}
