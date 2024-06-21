use crate::rustc_interface::middle::mir::{BasicBlock, START_BLOCK};

use super::{heap::SymbolicHeap, path_conditions::PathConditions};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct AcyclicPath(Vec<BasicBlock>);

impl AcyclicPath {

    pub fn blocks(&self) -> &[BasicBlock] {
        &self.0
    }

    pub fn from_start_block() -> Self {
        AcyclicPath(vec![START_BLOCK])
    }

    pub fn push_if_acyclic(&mut self, block: BasicBlock) -> bool {
        if self.0.contains(&block) {
            return false;
        }
        self.0.push(block);
        true
    }

    pub fn push(&mut self, block: BasicBlock) {
        if self.0.contains(&block) {
            panic!("Loop adding {:?} to {:?}", block, self.0)
        }
        self.0.push(block)
    }

    pub fn last(&self) -> BasicBlock {
        *self.0.last().unwrap()
    }

    pub fn check_loop(&self, loop_head: BasicBlock) -> Option<Vec<BasicBlock>> {
        let candidate_loop: Vec<_> = self
            .0
            .iter()
            .cloned()
            .skip_while(|b| b != &loop_head)
            .collect();
        if !candidate_loop.is_empty() {
            Some(candidate_loop)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Path<'sym, 'tcx, T> {
    pub path: AcyclicPath,
    pub pcs: PathConditions<'sym, 'tcx, T>,
    pub heap: SymbolicHeap<'sym, 'tcx, T>,
}


impl<'sym, 'tcx, T> Path<'sym, 'tcx, T> {
    pub fn new(
        path: AcyclicPath,
        pcs: PathConditions<'sym, 'tcx, T>,
        heap: SymbolicHeap<'sym, 'tcx, T>,
    ) -> Self {
        Path { path, pcs, heap }
    }

    pub fn has_path_conditions(&self) -> bool {
        !self.pcs.is_empty()
    }

    pub fn last_block(&self) -> BasicBlock {
        self.path.last()
    }
}

impl<'sym, 'tcx, T: Clone> Path<'sym, 'tcx, T> {
    pub fn push_if_acyclic(&self, block: BasicBlock) -> Option<Path<'sym, 'tcx, T>> {
        let mut result = self.clone();
        if result.path.push_if_acyclic(block) {
            Some(result)
        } else {
            None
        }
    }
}
