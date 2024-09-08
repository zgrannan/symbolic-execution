use std::collections::{BTreeMap, BTreeSet};

use crate::rustc_interface::middle::mir::{
    BasicBlock, Body, Local, StatementKind, Terminator, TerminatorEdges, TerminatorKind,
};

use crate::path::AcyclicPath;

pub struct LoopData {
    /// A map from the condition check point to invariant info
    pub invariant_info: BTreeMap<BasicBlock, InvariantInfo>,
}

fn get_successor<'tcx>(terminator: &Terminator<'tcx>) -> Option<BasicBlock> {
    match terminator.kind {
        TerminatorKind::Goto { target } => Some(target),
        TerminatorKind::SwitchInt { .. } => None,
        TerminatorKind::UnwindResume => None,
        TerminatorKind::UnwindTerminate(_) => None,
        TerminatorKind::Return => None,
        TerminatorKind::Unreachable => None,
        TerminatorKind::Drop { target, .. } => Some(target),
        TerminatorKind::Call { target, .. } => target,
        TerminatorKind::Assert { .. } => None,
        TerminatorKind::Yield { .. } => todo!(),
        TerminatorKind::CoroutineDrop => todo!(),
        TerminatorKind::FalseEdge {
            real_target,
            imaginary_target,
        } => Some(real_target),
        TerminatorKind::FalseUnwind {
            real_target,
            unwind,
        } => Some(real_target),
        TerminatorKind::InlineAsm { .. } => todo!(),
        _ => todo!(),
    }
}

fn find_condition_check_and_valid_block<'tcx>(
    loop_part: &[BasicBlock],
    body: &Body<'tcx>,
) -> Option<(BasicBlock, BasicBlock)> {
    let mut iter = loop_part.iter();
    let mut current_block = iter.next().unwrap();
    while let Some(next) = iter.next() {
        if let Some(succ) = get_successor(body.basic_blocks[*current_block].terminator()) {
            assert!(*next == succ);
            current_block = next;
        } else {
            return Some((*current_block, *next));
        }
    }
    return None;
}

#[derive(Clone, Debug)]
pub struct InvariantInfo {
    pub havoced_locals: BTreeSet<Local>,
    pub loop_head: BasicBlock,
    pub condition_check_block: BasicBlock,
}

impl LoopData {
    /// Get the invariant info for the block indicating the loop condition is valid
    pub fn get_invariant_info(
        &self,
        loop_condition_valid_block: BasicBlock,
    ) -> Option<InvariantInfo> {
        self.invariant_info
            .get(&loop_condition_valid_block)
            .cloned()
    }

    pub fn new(body: &Body) -> Self {
        let modified_locals: BTreeMap<BasicBlock, BTreeSet<Local>> = body
            .basic_blocks
            .iter_enumerated()
            .map(|(id, bb)| {
                let mut locals = BTreeSet::new();
                for stmt in bb.statements.iter() {
                    match &stmt.kind {
                        StatementKind::Assign(box (place, _)) => {
                            locals.insert(place.local);
                        }
                        StatementKind::StorageLive(_)
                        | StatementKind::StorageDead(_)
                        | StatementKind::FakeRead(_)
                        | StatementKind::PlaceMention(_)
                        | StatementKind::AscribeUserType(..) => {}
                        other => todo!("{:?}", other),
                    }
                }
                if let Some(terminator) = &bb.terminator {
                    match &terminator.kind {
                        TerminatorKind::Call { destination, .. } => {
                            locals.insert(destination.local);
                        }
                        TerminatorKind::Goto { .. }
                        | TerminatorKind::FalseEdge { .. }
                        | TerminatorKind::FalseUnwind { .. }
                        | TerminatorKind::SwitchInt { .. }
                        | TerminatorKind::Assert { .. }
                        | TerminatorKind::UnwindResume { .. }
                        | TerminatorKind::Unreachable { .. }
                        | TerminatorKind::Drop { .. }
                        | TerminatorKind::Return => {}
                        _ => todo!("{:?}", terminator.kind),
                    }
                }
                (id, locals)
            })
            .collect();
        let mut invariant_info: BTreeMap<BasicBlock, InvariantInfo> = BTreeMap::new();
        let mut paths: Vec<AcyclicPath> = vec![AcyclicPath::from_start_block()];
        while let Some(path) = paths.pop() {
            for successor in body.basic_blocks[path.last()].terminator().successors() {
                if let Some(loop_part) = path.check_loop(successor) {
                    if let Some((check_point, valid_point)) =
                        find_condition_check_and_valid_block(&loop_part, body)
                    {
                        let mut havoced_locals = invariant_info
                            .get(&check_point)
                            .map(|info| info.havoced_locals.clone())
                            .unwrap_or(BTreeSet::new());
                        for block in loop_part {
                            havoced_locals.extend(modified_locals[&block].clone());
                        }
                        invariant_info.insert(
                            valid_point,
                            InvariantInfo {
                                havoced_locals,
                                loop_head: successor,
                                condition_check_block: check_point,
                            },
                        );
                    }
                } else {
                    let mut new_path = path.clone();
                    new_path.push(successor);
                    paths.push(new_path);
                }
            }
        }
        eprintln!("invariant_info: {:?}", invariant_info);
        Self { invariant_info }
    }
}
