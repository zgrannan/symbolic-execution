use crate::{
    function_call_snapshot::{FunctionCallSnapshot, FunctionCallSnapshots},
    predicate::Predicate,
    results::ResultAssertion,
    rustc_interface::middle::mir::{BasicBlock, Location, START_BLOCK},
    value::SyntheticSymValue,
};

use super::{heap::HeapData, path_conditions::PathConditions};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum SymExPath {
    Acyclic(AcyclicPath),
    Loop(LoopPath),
}

impl SymExPath {
    pub fn contains(&self, block: BasicBlock) -> bool {
        match self {
            SymExPath::Acyclic(path) => path.contains(block),
            SymExPath::Loop(path) => path.contains(block),
        }
    }

    pub fn last(&self) -> BasicBlock {
        match self {
            SymExPath::Acyclic(path) => path.last(),
            SymExPath::Loop(path) => path.last(),
        }
    }

    pub fn can_push(&self, block: BasicBlock) -> bool {
        match self {
            SymExPath::Acyclic(_) => true,
            SymExPath::Loop(path) => path.can_push(block),
        }
    }

    pub fn push(&mut self, block: BasicBlock) {
        match self {
            SymExPath::Acyclic(path) => {
                if path.contains(block) {
                    *self = SymExPath::Loop(LoopPath::new(path.clone(), block));
                } else {
                    path.push(block);
                }
            }
            SymExPath::Loop(path) => {
                path.push(block);
            }
        }
    }

    pub fn blocks(&self) -> Vec<BasicBlock> {
        match self {
            SymExPath::Acyclic(path) => path.to_vec(),
            SymExPath::Loop(path) => path.blocks(),
        }
    }

    pub fn expect_acyclic(&self) -> &AcyclicPath {
        match self {
            SymExPath::Acyclic(path) => path,
            SymExPath::Loop(path) => panic!("Expected acyclic path, got loop {:?}", path),
        }
    }

    pub fn to_index_vec(&self) -> Vec<usize> {
        match self {
            SymExPath::Acyclic(path) => path.to_index_vec(),
            SymExPath::Loop(path) => path.to_index_vec(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct LoopPath {
    init: AcyclicPath,
    ret: AcyclicPath,
}

impl LoopPath {
    pub fn can_push(&self, block: BasicBlock) -> bool {
        !self.ret.contains(block)
    }

    pub fn contains(&self, block: BasicBlock) -> bool {
        self.init.contains(block) || self.ret.contains(block)
    }

    pub fn last(&self) -> BasicBlock {
        self.ret.last()
    }

    pub fn new(init: AcyclicPath, ret: BasicBlock) -> Self {
        Self {
            init,
            ret: AcyclicPath::new(ret),
        }
    }

    pub fn blocks(&self) -> Vec<BasicBlock> {
        let mut result = self.init.to_vec();
        result.extend(self.ret.to_vec());
        result
    }

    pub fn push(&mut self, block: BasicBlock) {
        self.ret.push(block);
    }

    pub fn to_index_vec(&self) -> Vec<usize> {
        let mut result = self.init.to_index_vec();
        result.extend(self.ret.to_index_vec());
        result
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct AcyclicPath(Vec<BasicBlock>);

impl AcyclicPath {
    pub fn to_vec(&self) -> Vec<BasicBlock> {
        self.0.clone()
    }

    pub fn to_index_vec(&self) -> Vec<usize> {
        self.0.iter().map(|b| b.index()).collect()
    }

    pub fn contains(&self, block: BasicBlock) -> bool {
        self.0.contains(&block)
    }

    pub fn to_slice(&self) -> &[BasicBlock] {
        &self.0
    }

    pub fn blocks(&self) -> &[BasicBlock] {
        &self.0
    }

    pub fn new(block: BasicBlock) -> Self {
        AcyclicPath(vec![block])
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
    pub path: SymExPath,
    pcs: PathConditions<'sym, 'tcx, T>,
    pub heap: HeapData<'sym, 'tcx, T>,
    pub function_call_snapshots: FunctionCallSnapshots<'sym, 'tcx, T>,
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> Path<'sym, 'tcx, T> {
    pub fn pcs(&self) -> &PathConditions<'sym, 'tcx, T> {
        &self.pcs
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx> + Clone> Path<'sym, 'tcx, T> {
    pub fn conditional_assertion(
        &self,
        assertion: Predicate<'sym, 'tcx, T>,
    ) -> ResultAssertion<'sym, 'tcx, T> {
        ResultAssertion {
            path: self.path.clone(),
            assertion: Predicate::implies(self.pcs().clone(), assertion),
        }
    }
    pub fn add_path_condition(&mut self, predicate: Predicate<'sym, 'tcx, T>) {
        let new_pcs = self.pcs.clone().and(predicate);
        self.pcs = new_pcs;
    }
    pub fn new(
        path: AcyclicPath,
        pcs: PathConditions<'sym, 'tcx, T>,
        heap: HeapData<'sym, 'tcx, T>,
    ) -> Self {
        Path {
            path: SymExPath::Acyclic(path),
            pcs,
            heap,
            function_call_snapshots: FunctionCallSnapshots::new(),
        }
    }

    pub fn add_function_call_snapshot(
        &mut self,
        location: Location,
        snapshot: FunctionCallSnapshot<'sym, 'tcx, T>,
    ) {
        self.function_call_snapshots.add_snapshot(location, snapshot);
    }

    pub fn has_path_conditions(&self) -> bool {
        !self.pcs.is_true()
    }

    pub fn last_block(&self) -> BasicBlock {
        self.path.last()
    }
}

impl<'sym, 'tcx, T: Clone> Path<'sym, 'tcx, T> {
    pub fn push(&self, block: BasicBlock) -> Path<'sym, 'tcx, T> {
        let mut result = self.clone();
        result.path.push(block);
        result
    }
}
