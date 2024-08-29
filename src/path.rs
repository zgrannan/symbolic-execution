use std::collections::BTreeMap;

use pcs::utils::PlaceRepacker;

use crate::{
    context::SymExContext,
    encoder::Encoder,
    function_call_snapshot::FunctionCallSnapshots,
    place::Place,
    rustc_interface::middle::mir::{
        self, BasicBlock, Body, Local, Location, ProjectionElem, START_BLOCK,
    },
    rustc_interface::middle::ty,
    semantics::VerifierSemantics,
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
    ret: BasicBlock,
}

impl LoopPath {
    pub fn new(init: AcyclicPath, ret: BasicBlock) -> Self {
        Self { init, ret }
    }

    pub fn to_index_vec(&self) -> Vec<usize> {
        let mut result = self.init.to_index_vec();
        result.push(self.ret.index());
        result
    }
}

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct AcyclicPath(Vec<BasicBlock>);

impl AcyclicPath {
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

#[derive(Ord, PartialOrd, Copy, Clone, Debug, PartialEq, Eq)]
pub struct InputPlace<'tcx>(Place<'tcx>);

impl<'tcx> InputPlace<'tcx> {
    pub fn local(&self) -> mir::Local {
        self.0.local()
    }

    pub fn projection(&self) -> &'tcx [ProjectionElem<mir::Local, ty::Ty<'tcx>>] {
        self.0.projection()
    }
}

pub type StructureTerm<'sym, 'tcx, T> = SymValue<'sym, 'tcx, T, InputPlace<'tcx>>;

struct Transformer<'mir, 'tcx>(&'mir Body<'tcx>);
impl<'mir, 'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>>
    SymValueTransformer<'sym, 'tcx, T, InputPlace<'tcx>, value::SymVar>
    for Transformer<'mir, 'tcx>
{
    fn transform_var(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        var: InputPlace<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        let sym_var = arena.mk_var(
            value::SymVar::Normal(var.0.local().as_usize() - 1),
            self.0.local_decls[var.0.local()].ty,
        );
        var.0
            .projection()
            .iter()
            .fold(sym_var, |p, elem| arena.mk_projection(*elem, p))
    }

    fn transform_synthetic(
        &mut self,
        arena: &'sym SymExContext<'tcx>,
        s: T,
    ) -> SymValue<'sym, 'tcx, T> {
        todo!()
    }
}

impl<'sym, 'tcx, T: Copy + Clone + SyntheticSymValue<'sym, 'tcx>>
    SymValueData<'sym, 'tcx, T, InputPlace<'tcx>>
{
    pub fn to_sym_value<'mir>(
        &'sym self,
        body: &'mir Body<'tcx>,
        arena: &'sym SymExContext<'tcx>,
    ) -> SymValue<'sym, 'tcx, T> {
        let mut transformer = Transformer(body);
        self.apply_transformer(arena, &mut transformer)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OldMap<'sym, 'tcx, T>(BTreeMap<Place<'tcx>, StructureTerm<'sym, 'tcx, T>>);

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
        Self(BTreeMap::new())
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
                    None => {}
                    // None => todo!(
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
    pub path: AcyclicPath,
    pub pcs: PathConditions<'sym, 'tcx, T>,
    pub heap: HeapData<'sym, 'tcx, T>,
    pub function_call_snapshots: FunctionCallSnapshots<'sym, 'tcx, T>,
    pub old_map: OldMap<'sym, 'tcx, U>,
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>, U: SyntheticSymValue<'sym, 'tcx>>
    Path<'sym, 'tcx, T, U>
{
    pub fn new(
        path: AcyclicPath,
        pcs: PathConditions<'sym, 'tcx, T>,
        heap: HeapData<'sym, 'tcx, T>,
        num_args: usize,
    ) -> Self {
        Path {
            path,
            pcs,
            heap,
            function_call_snapshots: FunctionCallSnapshots::new(),
            old_map: OldMap::new(),
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
    pub fn push_if_acyclic(&self, block: BasicBlock) -> Option<Path<'sym, 'tcx, T, U>> {
        let mut result = self.clone();
        if result.path.push_if_acyclic(block) {
            Some(result)
        } else {
            None
        }
    }
}
