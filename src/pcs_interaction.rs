use crate::rustc_interface::middle::mir::Location;

use pcs::{
    borrows::{
        domain::{DerefExpansion, MaybeOldPlace, Reborrow},
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
        path: &AcyclicPath,
        pcs: &PcsLocation<'mir, 'tcx>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        start: bool,
        location: Location,
    ) {
        let bridge = if start {
            Some(pcs.extra_start.clone())
        } else {
            pcs.extra_middle.clone()
        };
        let (ug_actions, added_reborrows, reborrow_expands) = if let Some(mut bridge) = bridge {
            eprintln!("Pre filter for {:?}: {:#?}", location, bridge.ug);
            bridge.ug.filter_for_path(path.to_slice(), self.tcx);
            eprintln!("Post filter for {:?}: {:#?}", location, bridge.ug);
            (
                bridge.ug.actions(self.tcx),
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
        eprintln!("Actions for {:?}: {:#?}", location, ug_actions);
        self.apply_unblock_actions(ug_actions, heap, location);
        let repacks = if start {
            &pcs.repacks_start
        } else {
            &pcs.repacks_middle
        };
        self.handle_repack_collapses(repacks, heap, location);
        self.handle_repack_expands(repacks, heap, location);
        self.handle_reborrow_expands(reborrow_expands.into_iter().collect(), heap, path, location);
        self.handle_added_reborrows(&added_reborrows.into_iter().collect::<Vec<_>>(), heap, path);
    }

    pub(crate) fn handle_removed_reborrow(
        &self,
        blocked_place: &MaybeOldPlace<'tcx>,
        assigned_place: &MaybeOldPlace<'tcx>,
        is_mut: bool,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
    ) {
        let heap_value = if is_mut {
            self.encode_place::<LookupTake, _>(heap.0, assigned_place)
        } else {
            self.encode_place::<LookupGet, _>(heap.0, assigned_place)
        };
        heap.insert_maybe_old_place(*blocked_place, heap_value);
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
        mut expands: Vec<DerefExpansion<'tcx>>,
        heap: &mut SymbolicHeap<'_, 'sym, 'tcx, S::SymValSynthetic>,
        path: &AcyclicPath,
        location: Location,
    ) {
        expands.sort_by_key(|ep| ep.base.place().projection.len());
        for ep in expands {
            if !path.contains(ep.location.block) {
                continue;
            }
            let place = ep.base.place();
            if place.is_ref(self.body, self.tcx) {
                // The expansion from x to *x isn't necessary!
                continue;
            }
            let value = if place.projects_shared_ref(self.fpcs_analysis.repacker()) {
                heap.0.get(&place)
            } else {
                heap.0.take(&place)
            };
            let value = value.unwrap_or_else(|| {
                self.mk_internal_err_expr(
                    format!(
                        "Place {:?} not found in heap[reborrow_expand]",
                        place.to_string(self.fpcs_analysis.repacker())
                    ),
                    (*place).ty(self.body, self.tcx).ty,
                )
            });

            // TODO: old places
            self.explode_value(
                &place,
                value,
                ep.expansion(self.tcx).iter().map(|p| p.place()),
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
                self.encode_place::<LookupTake, _>(heap.0, &reborrow.blocked_place)
            } else {
                self.encode_place::<LookupGet, _>(heap.0, &reborrow.blocked_place)
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
