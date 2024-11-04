use crate::{
    path::{Path, SymExPath},
    rustc_interface::middle::mir::Location,
    value::SymValue,
    LookupType,
};

use pcs::{
    borrows::{
        deref_expansion::{BorrowDerefExpansion, DerefExpansion},
        domain::{Borrow, MaybeOldPlace, MaybeRemotePlace},
        engine::BorrowsDomain,
        latest::Latest,
    },
    free_pcs::{FreePcsLocation, RepackOp},
    BorrowsBridge,
};

use crate::{
    heap::SymbolicHeap, semantics::VerifierSemantics, visualization::VisFormat, LookupGet,
    LookupTake, SymbolicExecution,
};

pub type PcsLocation<'mir, 'tcx> = FreePcsLocation<'tcx>;

impl<'mir, 'sym, 'tcx, S: VerifierSemantics<'sym, 'tcx, SymValSynthetic: VisFormat>>
    SymbolicExecution<'mir, 'sym, 'tcx, S>
{
    pub(crate) fn handle_pcg(
        &mut self,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
        location: Location,
    ) {
        self.handle_pcg_partial(path, pcs, true, location);
        self.handle_pcg_partial(path, pcs, false, location);
    }

    pub(crate) fn handle_pcg_partial(
        &mut self,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcsLocation<'mir, 'tcx>,
        start: bool,
        location: Location,
    ) {
        let mut bridge = if start {
            pcs.extra_start.clone()
        } else {
            pcs.extra_middle.clone()
        };
        bridge.ug.filter_for_path(&path.path.blocks());
        let ug_actions = bridge.ug.actions(self.repacker());
        let added_borrows = bridge.added_borrows;
        let borrows_expands = bridge.expands;
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
            borrows_expands.into_iter().map(|ep| ep.value).collect(),
            &mut heap,
            location,
        );
        self.handle_added_borrows(
            &added_borrows
                .into_iter()
                .filter(|r| r.conditions.valid_for_path(&path.path.blocks()))
                .map(|r| r.value)
                .collect::<Vec<_>>(),
            &mut heap,
        );
    }

    pub(crate) fn handle_removed_reborrow(
        &self,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: &MaybeOldPlace<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
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
    ) {
        for repack in repacks {
            if let RepackOp::Collapse(place, from, _) = repack {
                self.collapse_place_from((*place).into(), (*from).into(), heap, location)
            }
        }
    }

    pub(crate) fn handle_reborrow_expands(
        &self,
        expands: Vec<DerefExpansion<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        // TODO: Explain why owned expansions don't need to be handled
        let mut expands: Vec<BorrowDerefExpansion<'tcx>> = expands
            .into_iter()
            .flat_map(|ep| ep.borrow_expansion().cloned())
            .collect();

        // Expand places with smaller projections first. For example, if f ->
        // {f.g} and f.g -> {f.g.h}, are expansions, we must expand f before
        // f.g.
        expands.sort_by_key(|ep| ep.base().place().projection.len());

        for ep in expands {
            let place = ep.base();
            let value = self.encode_maybe_old_place::<LookupGet, _>(heap, &place);

            self.explode_value(
                value,
                ep.expansion(self.fpcs_analysis.repacker()).into_iter(),
                heap,
                location,
            );
        }
    }

    fn handle_added_borrows(
        &self,
        reborrows: &[Borrow<'tcx>],
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        for reborrow in reborrows {
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
    ) {
        for repack in repacks {
            if let RepackOp::Expand(place, guide, _) = repack {
                self.expand_place_with_guide(place, guide, heap, location)
            }
        }
    }
}
