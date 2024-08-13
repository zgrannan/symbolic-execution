use crate::{path::Path, rustc_interface::middle::mir::Location};

use pcs::{
    borrows::{
        deref_expansion::{BorrowDerefExpansion, DerefExpansion},
        domain::{MaybeOldPlace, Reborrow},
        engine::BorrowsDomain,
    },
    free_pcs::{FreePcsLocation, RepackOp},
    ReborrowBridge,
};

use crate::{
    heap::SymbolicHeap, path::AcyclicPath, semantics::VerifierSemantics, visualization::VisFormat,
    LookupGet, LookupTake, SymbolicExecution,
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
            bridge.ug.filter_for_path(path.path.to_slice(), self.tcx);
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
        self.handle_repack_collapses(repacks, &mut heap, location);
        self.handle_repack_expands(repacks, &mut heap, location);
        self.handle_reborrow_expands(
            reborrow_expands.into_iter().map(|ep| ep.value).collect(),
            &mut heap,
            &path.path,
            location,
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
        blocked_place: &MaybeOldPlace<'tcx>,
        assigned_place: &MaybeOldPlace<'tcx>,
        is_mut: bool,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        if !is_mut {
            return;
        }
        let heap_value = self.encode_place::<LookupTake, _>(heap, assigned_place);
        if blocked_place.is_old() {
            heap.insert_maybe_old_place(*blocked_place, heap_value);
        } else {
            heap.insert(blocked_place.place(), heap_value, location);
        }
    }

    pub(crate) fn handle_repack_collapses(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        for repack in repacks {
            if matches!(repack, RepackOp::Collapse(..)) {
                self.handle_repack(repack, heap, location)
            }
        }
    }

    pub(crate) fn handle_reborrow_expands(
        &self,
        expands: Vec<DerefExpansion<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        path: &AcyclicPath,
        location: Location,
    ) {
        // TODO: Explain why owned expansions don't need to be handled
        let mut expands: Vec<BorrowDerefExpansion<'tcx>> = expands
            .into_iter()
            .flat_map(|ep| ep.borrow_expansion().cloned())
            .collect();
        expands.sort_by_key(|ep| ep.base().place().projection.len());
        for ep in expands {
            if !path.contains(ep.location().block) {
                continue;
            }
            let place = ep.base();
            let value = self.encode_place::<LookupGet, _>(heap, &place);

            self.explode_value(
                &place,
                value,
                ep.expansion(self.fpcs_analysis.repacker()).into_iter(),
                heap,
                location,
            );
        }
    }

    pub(crate) fn handle_added_reborrows(
        &self,
        reborrows: &[Reborrow<'tcx>],
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        path: &AcyclicPath,
    ) {
        for reborrow in reborrows {
            if !path.contains(reborrow.location.block) {
                continue;
            }
            let blocked_value = if reborrow.mutability.is_mut() {
                self.encode_place::<LookupTake, _>(heap, &reborrow.blocked_place)
            } else {
                self.encode_place::<LookupGet, _>(heap, &reborrow.blocked_place)
            };
            heap.insert_maybe_old_place(reborrow.assigned_place, blocked_value);
        }
    }

    pub(crate) fn handle_repack_expands(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        for repack in repacks {
            if matches!(repack, RepackOp::Expand(..)) {
                self.handle_repack(repack, heap, location)
            }
        }
    }
}
