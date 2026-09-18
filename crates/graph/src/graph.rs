//! The value graph: every definition a file's bodies make, as a node with
//! an operation and the nodes it reads, in regions that run only when
//! their context is live.
//!
//! One table holds the whole file. A function's nodes are a run of it, its
//! parameters first; a region's nodes are a run inside its function's,
//! with the regions of its branches nested inside. A read of a local is
//! not a node but an edge to the local's definition, or to the narrowed
//! definition a guard gives it inside a branch. What could not be built is
//! a hole over whatever was built beneath it, so every function has a
//! result and every construct a node, and a rejected file is as complete
//! a graph as an accepted one.

use std::num::NonZeroU32;
use std::ops::Range;

use sumi_text::Span;

use crate::{BinaryOp, FunctionId, Int, Ty};

/// A function's run of the graph: its entry context, then a node per
/// parameter, then its body region's nodes, then, for a declared result,
/// the copy the body's value is held in.
#[derive(Debug)]
pub struct Run {
    nodes: Range<u32>,
    arity: u32,
    region: RegionId,
    result: NodeId,
}

impl Run {
    /// The function's nodes, in definition order.
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (self.nodes.start as usize..self.nodes.end as usize).map(NodeId::new)
    }

    /// The context the function runs in: live when it can be called.
    pub fn entry(&self) -> NodeId {
        NodeId::new(self.nodes.start as usize)
    }

    /// A node per parameter, in declaration order.
    pub fn params(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        let first = self.nodes.start as usize + 1;
        (first..first + self.arity as usize).map(NodeId::new)
    }

    /// The body's region, run in the entry context.
    pub fn region(&self) -> RegionId {
        self.region
    }

    /// The function's value: the body region's result, or the declared
    /// result the body's value is held to.
    pub fn result(&self) -> NodeId {
        self.result
    }

    /// Whether `node` is one of the run's.
    pub fn holds(&self, node: NodeId) -> bool {
        (self.nodes.start as usize..self.nodes.end as usize).contains(&node.index())
    }

    /// The position of `node` in the run, for a slot per node.
    pub fn slot(&self, node: NodeId) -> usize {
        debug_assert!(self.holds(node), "a node of the run");
        node.index() - self.nodes.start as usize
    }
}

/// A node of the file's graph. One past its index, so an `Option<NodeId>`
/// is one word.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NodeId(NonZeroU32);

impl NodeId {
    /// The node at `index` of its graph.
    pub fn new(index: usize) -> Self {
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("node count fits u32")).unwrap())
    }

    /// Index into the graph's `nodes()`.
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "n{}", self.index())
    }
}

/// A region of the file's graph.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct RegionId(NonZeroU32);

impl RegionId {
    fn new(index: usize) -> Self {
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("region count fits u32")).unwrap())
    }

    /// Index into the graph's `regions()`.
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl std::fmt::Debug for RegionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{}", self.index())
    }
}

/// What a node computes from its inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    Int(Int),
    Bool(bool),
    /// The function's parameter at `index`.
    Param(u32),
    /// Unit, held while its input, a context, is live: a block without a
    /// tail. An `if` without an else is unit too, as its own `Join`.
    Unit,
    /// What could not be built, over whatever was built beneath it: a
    /// construct the checker refuses, a name it cannot resolve, syntax the
    /// parser could not repair. Its type is whatever its context asks.
    Hole,
    /// The input, with a name or a declaration: a `let` binding, which
    /// may declare its type, or a declared result the body's value is
    /// held to. A declared copy is known to have its type on its own
    /// account, whatever flows in, because of the annotation at the span.
    Copy {
        declared: Option<(Ty, Span)>,
    },
    Neg,
    Not,
    /// An eager operator over its two inputs.
    Binary(BinaryOp),
    /// `&&` or `||`: the left input, then the region of the right operand,
    /// which runs only when the left leaves the answer open.
    And {
        rhs: RegionId,
    },
    Or {
        rhs: RegionId,
    },
    /// A read of a local narrowed by a comparison with the second input
    /// holding in `sense`: the first input is the local's definition as
    /// read outside the guard.
    Refine {
        op: BinaryOp,
        local_is_lhs: bool,
        sense: bool,
    },
    /// A read of a boolean local narrowed to one value.
    Exactly(bool),
    /// A function's entry context: live when the function can run.
    Entry,
    /// A branch's context: live when the first input, a condition, may be
    /// true, or false, and the second, the enclosing context, is live.
    Then,
    Else,
    /// An `if`: the input is its condition, and its value is the result of
    /// whichever region runs. Without an else region the value is unit.
    Join {
        then: RegionId,
        else_: Option<RegionId>,
    },
    /// A call: the inputs are its arguments.
    Call(FunctionId),
}

#[derive(Debug)]
pub struct Node {
    pub op: Op,
    inputs: Range<u32>,
    pub origin: Span,
    /// The name a parameter or a `let` gives the node, where it is written.
    pub name: Option<Span>,
}

/// A run of nodes that runs only while its context is live, with the node
/// its value is.
#[derive(Debug)]
pub struct Region {
    pub context: NodeId,
    nodes: Range<u32>,
    result: Option<NodeId>,
}

impl Region {
    /// The nodes the region defines, in definition order, nested regions'
    /// included.
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (self.nodes.start as usize..self.nodes.end as usize).map(NodeId::new)
    }

    /// The region's value: a region opened but never closed has none,
    /// which a complete build leaves no region.
    pub fn result(&self) -> NodeId {
        self.result.expect("a closed region has a result")
    }
}

#[derive(Debug, Default)]
pub struct Graph {
    nodes: Vec<Node>,
    inputs: Vec<NodeId>,
    regions: Vec<Region>,
    runs: Vec<Run>,
}

impl Graph {
    /// A graph with room for `nodes` nodes and as many inputs before its
    /// tables grow. Only a guide.
    pub fn with_capacity(nodes: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(nodes),
            inputs: Vec::with_capacity(nodes),
            regions: Vec::new(),
            runs: Vec::new(),
        }
    }

    /// Every function's run, in declaration order: the index is the
    /// function's ID.
    pub fn runs(&self) -> &[Run] {
        &self.runs
    }

    pub fn run(&self, id: FunctionId) -> &Run {
        &self.runs[id.index()]
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// Every node's ID, in definition order: the index into `nodes()`.
    pub fn node_ids(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (0..self.nodes.len()).map(NodeId::new)
    }

    pub fn regions(&self) -> &[Region] {
        &self.regions
    }

    /// Every region's ID, outermost first where regions nest.
    pub fn region_ids(&self) -> impl ExactSizeIterator<Item = RegionId> + use<> {
        (0..self.regions.len()).map(RegionId::new)
    }

    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.index()]
    }

    pub fn region(&self, id: RegionId) -> &Region {
        &self.regions[id.index()]
    }

    /// The nodes `id` reads, in operand order.
    pub fn inputs(&self, id: NodeId) -> &[NodeId] {
        let node = &self.nodes[id.index()];
        &self.inputs[node.inputs.start as usize..node.inputs.end as usize]
    }

    /// The next node's ID: where a run starts.
    pub fn next(&self) -> NodeId {
        NodeId::new(self.nodes.len())
    }

    /// A node computing `op` from `inputs`, which must be nodes of this
    /// graph, at `origin`, named `name`.
    pub fn push(&mut self, op: Op, inputs: &[NodeId], origin: Span, name: Option<Span>) -> NodeId {
        let start = u32::try_from(self.inputs.len()).expect("input count fits u32");
        self.inputs.extend_from_slice(inputs);
        let end = u32::try_from(self.inputs.len()).expect("input count fits u32");
        let id = self.next();
        self.nodes.push(Node {
            op,
            inputs: start..end,
            origin,
            name,
        });
        id
    }

    /// Open a region gated by `context`; its nodes begin at the next node
    /// pushed after [`Graph::enter`].
    pub fn open(&mut self, context: NodeId) -> RegionId {
        let id = RegionId::new(self.regions.len());
        self.regions.push(Region {
            context,
            nodes: 0..0,
            result: None,
        });
        id
    }

    /// The region's nodes begin here.
    pub fn enter(&mut self, region: RegionId) {
        let start = u32::try_from(self.nodes.len()).expect("node count fits u32");
        self.regions[region.index()].nodes = start..start;
    }

    /// The region's nodes end here, and `result` is its value.
    pub fn close(&mut self, region: RegionId, result: NodeId) {
        let end = u32::try_from(self.nodes.len()).expect("node count fits u32");
        let region = &mut self.regions[region.index()];
        region.nodes.end = end;
        region.result = Some(result);
    }

    /// Close the run of `function`, which must be the next in declaration
    /// order: the nodes from `start`, where its entry was pushed, to here,
    /// with `arity` parameters after the entry, its body `region`, and its
    /// `result`.
    pub fn close_run(
        &mut self,
        function: FunctionId,
        start: NodeId,
        arity: u32,
        region: RegionId,
        result: NodeId,
    ) {
        assert_eq!(self.runs.len(), function.index(), "runs close in order");
        let end = u32::try_from(self.nodes.len()).expect("node count fits u32");
        let start = u32::try_from(start.index()).expect("node count fits u32");
        debug_assert!(matches!(self.nodes[start as usize].op, Op::Entry));
        debug_assert!(start + 1 + arity <= end);
        self.runs.push(Run {
            nodes: start..end,
            arity,
            region,
            result,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sumi_text::{FileId, TextRange, TextSize};

    fn at(offset: u32) -> Span {
        Span::new(
            FileId::new(0),
            TextRange::new(TextSize::new(offset), TextSize::new(offset + 1)),
        )
    }

    #[test]
    fn ids_are_one_word_with_room_for_none() {
        assert_eq!(size_of::<NodeId>(), 4);
        assert_eq!(size_of::<Option<NodeId>>(), 4);
        assert_eq!(size_of::<Option<RegionId>>(), 4);
        for index in [0, 1, 8192] {
            assert_eq!(NodeId::new(index).index(), index);
            assert_eq!(format!("{:?}", NodeId::new(index)), format!("n{index}"));
            assert_eq!(RegionId::new(index).index(), index);
        }
    }

    /// A function's run: an entry, a parameter, a region opened in the
    /// entry whose nodes begin after `enter` and end at `close`, and a
    /// node after it reading the region's result.
    #[test]
    fn runs_and_regions_follow_the_protocol() {
        let mut graph = Graph::with_capacity(8);
        let start = graph.next();
        let entry = graph.push(Op::Entry, &[], at(0), None);
        assert_eq!(entry, start);
        let param = graph.push(Op::Param(0), &[], at(1), Some(at(1)));
        let region = graph.open(entry);
        graph.enter(region);
        let one = graph.push(Op::Int(1.into()), &[], at(2), None);
        let sum = graph.push(Op::Binary(BinaryOp::Add), &[param, one], at(3), None);
        graph.close(region, sum);
        let copy = graph.push(Op::Copy { declared: None }, &[sum], at(4), None);
        graph.close_run(FunctionId::new(0), start, 1, region, copy);
        assert_eq!(graph.nodes().len(), 5);
        let run = graph.run(FunctionId::new(0));
        assert_eq!(
            run.nodes().collect::<Vec<_>>(),
            [entry, param, one, sum, copy]
        );
        assert_eq!(run.entry(), entry);
        assert_eq!(run.params().collect::<Vec<_>>(), [param]);
        assert_eq!(run.region(), region);
        assert_eq!(run.result(), copy);
        assert_eq!(run.slot(sum), 3);
        assert_eq!(
            graph.node_ids().collect::<Vec<_>>(),
            [entry, param, one, sum, copy]
        );
        assert_eq!(graph.inputs(sum), [param, one]);
        assert_eq!(graph.inputs(entry), []);
        assert_eq!(graph.node(param).name, Some(at(1)));
        let region = graph.region(region);
        assert_eq!(region.context, entry);
        assert_eq!(region.nodes().collect::<Vec<_>>(), [one, sum]);
        assert_eq!(region.result(), sum);
        assert_eq!(graph.region_ids().count(), 1);
    }

    /// A region entered and closed around nothing is empty, and may still
    /// have a result defined outside it.
    #[test]
    fn an_empty_region_reads_an_outer_definition() {
        let mut graph = Graph::default();
        let entry = graph.push(Op::Entry, &[], at(0), None);
        let param = graph.push(Op::Param(0), &[], at(1), Some(at(1)));
        let region = graph.open(entry);
        graph.enter(region);
        graph.close(region, param);
        assert_eq!(graph.region(region).nodes().len(), 0);
        assert_eq!(graph.region(region).result(), param);
    }

    #[test]
    #[should_panic(expected = "a closed region has a result")]
    fn an_open_region_has_no_result() {
        let mut graph = Graph::default();
        let entry = graph.push(Op::Entry, &[], at(0), None);
        let region = graph.open(entry);
        graph.region(region).result();
    }
}
