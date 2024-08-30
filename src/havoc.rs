use std::collections::{BTreeMap, BTreeSet};

use crate::rustc_interface::middle::mir::{
    BasicBlock, Body, Local, StatementKind, TerminatorKind,
};

use crate::path::AcyclicPath;

pub struct HavocData {
    havoced_locals: BTreeMap<BasicBlock, BTreeSet<Local>>,
}

impl HavocData {
    pub fn is_loop_head(&self, block: BasicBlock) -> bool {
        !self.get(block).is_empty()
    }
    pub fn get(&self, block: BasicBlock) -> BTreeSet<Local> {
        self.havoced_locals
            .get(&block)
            .cloned()
            .unwrap_or(BTreeSet::new())
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
                        StatementKind::StorageLive(_) |
                        StatementKind::StorageDead(_) |
                        StatementKind::FakeRead(_) |
                        StatementKind::PlaceMention(_) |
                        StatementKind::AscribeUserType(..) => {}
                        other => todo!("{:?}", other),
                    }
                }
                if let Some(terminator) = &bb.terminator {
                    match &terminator.kind {
                        TerminatorKind::Call { destination, .. } => {
                            locals.insert(destination.local);
                        }
                        TerminatorKind::Goto {..} |
                        TerminatorKind::FalseEdge {..} |
                        TerminatorKind::FalseUnwind {..} |
                        TerminatorKind::SwitchInt {..} |
                        TerminatorKind::Assert {..} |
                        TerminatorKind::UnwindResume {..} |
                        TerminatorKind::Unreachable {..} |
                        TerminatorKind::Drop {..} |
                        TerminatorKind::Return => {}
                        _ => todo!("{:?}", terminator.kind),
                    }
                }
                (id, locals)
            })
            .collect();
        let mut havoced_locals: BTreeMap<BasicBlock, BTreeSet<Local>> = BTreeMap::new();
        let mut paths: Vec<AcyclicPath> = vec![AcyclicPath::from_start_block()];
        while let Some(path) = paths.pop() {
            for successor in body.basic_blocks[path.last()].terminator().successors() {
                if let Some(loop_part) = path.check_loop(successor) {
                    let mut havoced = havoced_locals
                        .get(&successor)
                        .cloned()
                        .unwrap_or(BTreeSet::new());
                    for block in loop_part {
                        havoced.extend(modified_locals[&block].clone());
                    }
                    havoced_locals.insert(successor, havoced);
                } else {
                    let mut new_path = path.clone();
                    new_path.push(successor);
                    paths.push(new_path);
                }
            }
        }
        Self { havoced_locals }
    }
}
