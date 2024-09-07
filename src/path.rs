use std::collections::{BTreeMap, BTreeSet, HashMap};

use pcs::utils::PlaceRepacker;

use crate::{
    context::SymExContext,
    encoder::Encoder,
    function_call_snapshot::FunctionCallSnapshots,
    place::Place,
    rustc_interface::middle::mir::{self, BasicBlock, Body, Location, ProjectionElem, START_BLOCK},
    rustc_interface::middle::ty,
    transform::SymValueTransformer,
    value::{self, SymValue, SymValueData, SymValueKind, SyntheticSymValue},
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
            SymExPath::Acyclic(path) => true,
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct InputPlace<'tcx>(Place<'tcx>);

impl<'tcx> InputPlace<'tcx> {
    pub fn new(place: Place<'tcx>) -> Self {
        Self(place)
    }

    pub fn local(&self) -> mir::Local {
        self.0.local()
    }

    pub fn projection(&self) -> &'tcx [ProjectionElem<mir::Local, ty::Ty<'tcx>>] {
        self.0.projection()
    }
}

pub type StructureTerm<'sym, 'tcx, T> = SymValue<'sym, 'tcx, T, InputPlace<'tcx>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OldMap<'sym, 'tcx, T>(HashMap<Place<'tcx>, StructureTerm<'sym, 'tcx, T>>);

pub struct OldMapEncoder<'mir, 'sym, 'tcx> {
    pub repacker: PlaceRepacker<'mir, 'tcx>,
    pub arena: &'sym SymExContext<'tcx>,
}

impl<'mir, 'sym, 'tcx> OldMapEncoder<'mir, 'sym, 'tcx> {
    fn num_args(&self) -> usize {
        self.repacker.num_args()
    }
}

impl<'mir, 'sym, 'tcx: 'mir, S: SyntheticSymValue<'sym, 'tcx> + 'sym> Encoder<'mir, 'sym, 'tcx, S>
    for OldMapEncoder<'mir, 'sym, 'tcx>
{
    type V = InputPlace<'tcx>;
    type Ctxt<'ctxt> = OldMap<'sym, 'tcx, S>
    where
        'mir: 'ctxt,
        'tcx: 'ctxt,
        'sym: 'ctxt;

    fn arena(&self) -> &'sym SymExContext<'tcx> {
        self.arena
    }

    fn repacker(&self) -> PlaceRepacker<'mir, 'tcx> {
        self.repacker
    }

    fn encode_place<'ctxt>(
        &self,
        ctxt: &mut OldMap<'sym, 'tcx, S>,
        place: &Place<'tcx>,
    ) -> StructureTerm<'sym, 'tcx, S>
    where
        'tcx: 'ctxt,
        'sym: 'ctxt,
    {
        if place.local().as_usize() <= self.num_args() {
            self.arena.alloc(SymValueData::new(
                SymValueKind::Var(
                    InputPlace(*place),
                    place.ty(self.repacker.body(), self.repacker.tcx()).ty,
                ),
                self.arena,
            ))
        } else {
            ctxt.get(place, self.arena).unwrap_or_else(|| {
                // panic!(
                //     "Place {:?} not found in old map {:?}",
                //     place, ctxt
                // )
                self.arena.alloc(SymValueData::new(
                    SymValueKind::Var(
                        InputPlace(*place),
                        place.ty(self.repacker.body(), self.repacker.tcx()).ty,
                    ),
                    self.arena,
                ))
            })
        }
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> OldMap<'sym, 'tcx, T> {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn insert(&mut self, place: Place<'tcx>, term: StructureTerm<'sym, 'tcx, T>) {
        self.0.insert(place, term);
    }

    pub fn get(
        &self,
        place: &Place<'tcx>,
        arena: &'sym SymExContext<'tcx>,
    ) -> Option<StructureTerm<'sym, 'tcx, T>> {
        for (k, v) in self.0.iter() {
            if k.local() == place.local() {
                match place.projection().strip_prefix(k.projection()) {
                    Some(remaining) => {
                        return Some(
                            remaining
                                .iter()
                                .fold(v, |p, elem| arena.mk_projection(*elem, p)),
                        );
                    }
                    None => {} // None => todo!(
                               //     "Projection {:?} does not match prefix {:?}",
                               //     place,
                               //     k,
                               // ),
                }
            }
        }
        None
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Path<'sym, 'tcx, T, U> {
    pub path: SymExPath,
    pub pcs: PathConditions<'sym, 'tcx, T>,
    pub heap: HeapData<'sym, 'tcx, T>,
    pub function_call_snapshots: FunctionCallSnapshots<'sym, 'tcx, T>,
    pub old_map: OldMap<'sym, 'tcx, U>,
    pub re_enter_blocks: BTreeSet<BasicBlock>,
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>, U: SyntheticSymValue<'sym, 'tcx>>
    Path<'sym, 'tcx, T, U>
{
    pub fn re_enter_block(mut self, block: BasicBlock) -> Self {
        self.re_enter_blocks.insert(block);
        self
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
            old_map: OldMap::new(),
            re_enter_blocks: BTreeSet::new(),
        }
    }

    pub fn add_function_call_snapshot(
        &mut self,
        location: Location,
        args: &'sym [SymValue<'sym, 'tcx, T>],
    ) {
        self.function_call_snapshots.add_snapshot(location, args);
    }

    pub fn has_path_conditions(&self) -> bool {
        !self.pcs.is_empty()
    }

    pub fn last_block(&self) -> BasicBlock {
        self.path.last()
    }
}

impl<'sym, 'tcx, T: Clone, U: Clone> Path<'sym, 'tcx, T, U> {
    pub fn push(&self, block: BasicBlock) -> Path<'sym, 'tcx, T, U> {
        let mut result = self.clone();
        result.path.push(block);
        result
    }
}
