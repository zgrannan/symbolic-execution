use crate::rustc_interface::hir::Mutability;
use crate::{path::Path, rustc_interface::middle::mir::Location};

use pcs::borrows::borrow_pcg_expansion::BorrowPCGExpansion;
use pcs::borrows::latest::Latest;
use pcs::utils::HasPlace;
use pcs::free_pcs::{CapabilityKind, PcgLocation, RepackOp};
use pcs::utils::place::maybe_old::MaybeOldPlace;
use pcs::utils::place::maybe_remote::MaybeRemotePlace;

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
        pcs: &PcgLocation<'tcx>,
        location: Location,
    ) {
        self.handle_pcg_partial(path, pcs, true, location);
        self.handle_pcg_partial(path, pcs, false, location);
    }

    pub(crate) fn handle_pcg_partial(
        &mut self,
        path: &mut Path<'sym, 'tcx, S::SymValSynthetic>,
        pcs: &PcgLocation<'tcx>,
        start: bool,
        location: Location,
    ) {
        let bridge = if start {
            pcs.extra_start.clone()
        } else {
            pcs.extra_middle.clone()
        };
        let mut ug_actions = bridge.unblock_actions();
        ug_actions.retain(|action| action.edge().valid_for_path(&path.path.blocks()));
        let borrows_expands = bridge.expands();
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
        self.handle_repack_weakens(repacks, &mut heap, location);
        self.handle_repack_expands(repacks, &mut heap, location);
        self.handle_reborrow_expands(
            borrows_expands.into_iter().map(|ep| ep.value).collect(),
            &mut heap,
            pcs.latest(),
        );
    }

    pub(crate) fn handle_removed_borrow(
        &self,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: &MaybeOldPlace<'tcx>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        let heap_value = self.encode_maybe_old_place::<LookupTake, _>(heap.0, assigned_place);
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

    pub(crate) fn handle_repack_weakens(
        &self,
        _repacks: &Vec<RepackOp<'tcx>>,
        _heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        _location: Location,
    ) {
        // TODO: Check why this doesn't work
        // for repack in repacks {
        //     if let RepackOp::Weaken(place, _, CapabilityKind::Write) = repack {
        //         heap.0.remove(place);
        //     }
        // }
    }

    pub(crate) fn handle_repack_collapses(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        for repack in repacks {
            if let RepackOp::Collapse(
                place,
                from,
                CapabilityKind::Exclusive | CapabilityKind::Lent,
            ) = repack
            {
                self.collapse_place_from((*place).into(), (*from).into(), heap, location)
            }
        }
    }

    pub(crate) fn handle_reborrow_expands(
        &self,
        mut expands: Vec<BorrowPCGExpansion<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        latest: &Latest<'tcx>,
    ) {
        expands.sort_by_key(|ep| ep.base().place().projection().len());

        for ep in expands {
            let ep: BorrowPCGExpansion<'tcx, MaybeOldPlace<'tcx>> = if let Ok(ep) = ep.try_into() {
                ep
            } else {
                // Expansion of region projections are not supported
                continue;
            };
            let place = ep.base();
            let value = self.encode_maybe_old_place::<LookupGet, _>(heap.0, &place);

            self.explode_value(
                value,
                ep.expansion(self.fpcs_analysis.repacker()).into_iter(),
                heap,
                latest.get(place.place()),
            );
        }
    }

    pub(crate) fn handle_repack_expands(
        &self,
        repacks: &Vec<RepackOp<'tcx>>,
        heap: &mut SymbolicHeap<'_, '_, 'sym, 'tcx, S::SymValSynthetic>,
        location: Location,
    ) {
        for repack in repacks {
            if let RepackOp::Expand(place, guide, capability) = repack {
                let is_shared_ref = place.ty(self.fpcs_analysis.repacker()).ty.ref_mutability()
                    == Some(Mutability::Not);
                let take = capability == &CapabilityKind::Exclusive && !is_shared_ref;
                self.expand_place_with_guide(place, guide, heap, location, take)
            }
        }
    }
}
