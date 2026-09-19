//! The value graph: one table of nodes per file, each an op over the nodes it reads, in regions
//! that run only while their context node is live. A read of a local is an edge to its definition,
//! not a node, and what could not be built is a hole over what was, so a rejected file's graph is
//! complete.

use std::num::NonZeroU32;
use std::ops::Range;

use sumi_text::TextRange;

use crate::{BinaryOp, CmpOp, FunctionId, Int, Ty};

/// A function's nodes: the entry, then one per parameter, then its body region's, then the
/// declared-result copy if any.
#[derive(Debug)]
pub struct Run {
    nodes: Range<u32>,
    arity: u32,
    region: RegionId,
    result: NodeId,
}

impl Run {
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (self.nodes.start as usize..self.nodes.end as usize).map(NodeId::new)
    }

    pub fn entry(&self) -> NodeId {
        NodeId::new(self.nodes.start as usize)
    }

    pub fn params(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        let first = self.nodes.start as usize + 1;
        (first..first + self.arity as usize).map(NodeId::new)
    }

    pub fn region(&self) -> RegionId {
        self.region
    }

    pub fn result(&self) -> NodeId {
        self.result
    }

    fn holds(&self, node: NodeId) -> bool {
        (self.nodes.start as usize..self.nodes.end as usize).contains(&node.index())
    }

    pub fn slot(&self, node: NodeId) -> usize {
        debug_assert!(self.holds(node), "a node of the run");
        node.index() - self.nodes.start as usize
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NodeId(NonZeroU32);

impl NodeId {
    pub fn new(index: usize) -> Self {
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("node count fits u32")).unwrap())
    }

    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "n{}", self.index())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct RegionId(NonZeroU32);

impl RegionId {
    fn new(index: usize) -> Self {
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("region count fits u32")).unwrap())
    }

    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl std::fmt::Debug for RegionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{}", self.index())
    }
}

/// A function a call may be held to: one with a whole parameter list. An ID from one graph names
/// nothing in another.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Callee(u32);

impl Callee {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub struct Callable {
    pub function: FunctionId,
    pub params: Box<[Ty]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    Int(Int),
    Bool(bool),
    /// `ty` is the parameter's declared type when the node carries it; a parameter that fails
    /// its declaration, or repeats a name, has none.
    Param {
        index: u32,
        ty: Option<Ty>,
    },
    /// Its input is the context it is held in.
    Unit,
    /// Its type is whatever its context asks.
    Hole,
    /// The input under a `let` name or a declared result; `declared` is the annotation's type and
    /// range, and the copy has that type whatever flows in.
    Copy {
        declared: Option<(Ty, TextRange)>,
    },
    Neg,
    Not,
    Binary(BinaryOp),
    And {
        rhs: RegionId,
    },
    Or {
        rhs: RegionId,
    },
    /// A narrowed read: the first input is the local's definition, the second what `op` compares it
    /// with, and the comparison holds iff `sense`.
    Refine {
        op: CmpOp,
        local_is_lhs: bool,
        sense: bool,
    },
    /// A read of a boolean local narrowed to one value.
    Exactly(bool),
    /// An expression statement: no value itself.
    Unused,
    Entry,
    /// A branch's context: the inputs are the condition, then the enclosing context.
    Then,
    Else,
    /// The input is the condition; the value is the run branch's result, or unit without `else_`.
    Join {
        then: RegionId,
        else_: Option<RegionId>,
    },
    /// The inputs are the arguments as written, which may not match the callee's arity.
    Call(Callee),
}

#[derive(Debug)]
pub struct Node {
    pub op: Op,
    inputs: Range<u32>,
    pub origin: TextRange,
    pub name: Option<TextRange>,
}

#[derive(Debug)]
pub struct Region {
    pub context: NodeId,
    nodes: Range<u32>,
    result: Option<NodeId>,
}

impl Region {
    /// Includes the nodes of nested regions.
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (self.nodes.start as usize..self.nodes.end as usize).map(NodeId::new)
    }

    pub fn result(&self) -> NodeId {
        self.result.expect("a closed region has a result")
    }
}

#[derive(Debug, Default)]
pub struct Graph {
    nodes: Vec<Node>,
    inputs: Vec<NodeId>,
    reads: Vec<TextRange>,
    regions: Vec<Region>,
    runs: Vec<Run>,
    callables: Vec<Callable>,
}

impl Graph {
    pub fn with_capacity(nodes: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(nodes),
            inputs: Vec::with_capacity(nodes),
            reads: Vec::with_capacity(nodes),
            regions: Vec::new(),
            runs: Vec::new(),
            callables: Vec::new(),
        }
    }

    pub fn callable(&self, callee: Callee) -> &Callable {
        &self.callables[callee.index()]
    }

    /// In declaration order.
    pub fn callables(&self) -> &[Callable] {
        &self.callables
    }

    /// `params` is `function`'s whole parameter list, one type per parameter node of its run.
    pub fn declare(&mut self, function: FunctionId, params: Box<[Ty]>) -> Callee {
        let callee = Callee(u32::try_from(self.callables.len()).expect("function count fits u32"));
        self.callables.push(Callable { function, params });
        callee
    }

    /// Indexed by function ID.
    pub fn runs(&self) -> &[Run] {
        &self.runs
    }

    pub fn run(&self, id: FunctionId) -> &Run {
        &self.runs[id.index()]
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    pub fn node_ids(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (0..self.nodes.len()).map(NodeId::new)
    }

    /// Outermost first where regions nest.
    pub fn region_ids(&self) -> impl ExactSizeIterator<Item = RegionId> + use<> {
        (0..self.regions.len()).map(RegionId::new)
    }

    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.index()]
    }

    pub fn region(&self, id: RegionId) -> &Region {
        &self.regions[id.index()]
    }

    pub fn inputs(&self, id: NodeId) -> &[NodeId] {
        let node = &self.nodes[id.index()];
        &self.inputs[node.inputs.start as usize..node.inputs.end as usize]
    }

    /// Where `id` reads each input, parallel to `inputs`: the read's range, not the definition's.
    pub fn reads(&self, id: NodeId) -> &[TextRange] {
        let node = &self.nodes[id.index()];
        &self.reads[node.inputs.start as usize..node.inputs.end as usize]
    }

    pub fn next(&self) -> NodeId {
        NodeId::new(self.nodes.len())
    }

    /// Each input is a node and where it is read.
    pub fn push(
        &mut self,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        origin: TextRange,
        name: Option<TextRange>,
    ) -> NodeId {
        let start = u32::try_from(self.inputs.len()).expect("input count fits u32");
        self.inputs.reserve(inputs.len());
        self.reads.reserve(inputs.len());
        for &(input, read) in inputs {
            self.inputs.push(input);
            self.reads.push(read);
        }
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

    /// The region's nodes are those pushed between `enter` and `close`; an `if` opens both branches
    /// before entering either.
    pub fn open(&mut self, context: NodeId) -> RegionId {
        let id = RegionId::new(self.regions.len());
        self.regions.push(Region {
            context,
            nodes: 0..0,
            result: None,
        });
        id
    }

    pub fn enter(&mut self, region: RegionId) {
        let start = u32::try_from(self.nodes.len()).expect("node count fits u32");
        self.regions[region.index()].nodes = start..start;
    }

    pub fn close(&mut self, region: RegionId, result: NodeId) {
        let end = u32::try_from(self.nodes.len()).expect("node count fits u32");
        let region = &mut self.regions[region.index()];
        region.nodes.end = end;
        region.result = Some(result);
    }

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
    use crate::ArithOp;
    use sumi_text::TextSize;

    fn at(offset: u32) -> TextRange {
        TextRange::new(TextSize::new(offset), TextSize::new(offset + 1))
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

    #[test]
    fn runs_and_regions_follow_the_protocol() {
        let mut graph = Graph::with_capacity(8);
        let start = graph.next();
        let entry = graph.push(Op::Entry, &[], at(0), None);
        assert_eq!(entry, start);
        let param = graph.push(
            Op::Param {
                index: 0,
                ty: Some(Ty::Int),
            },
            &[],
            at(1),
            Some(at(1)),
        );
        let region = graph.open(entry);
        graph.enter(region);
        let one = graph.push(Op::Int(1.into()), &[], at(2), None);
        let sum = graph.push(
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            &[(param, at(5)), (one, at(2))],
            at(3),
            None,
        );
        graph.close(region, sum);
        let copy = graph.push(Op::Copy { declared: None }, &[(sum, at(3))], at(4), None);
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
        assert_eq!(graph.reads(sum), [at(5), at(2)]);
        assert_eq!(graph.inputs(entry), []);
        assert_eq!(graph.reads(entry), []);
        assert_eq!(graph.node(param).name, Some(at(1)));
        let region = graph.region(region);
        assert_eq!(region.context, entry);
        assert_eq!(region.nodes().collect::<Vec<_>>(), [one, sum]);
        assert_eq!(region.result(), sum);
        assert_eq!(graph.region_ids().count(), 1);
    }

    #[test]
    fn an_empty_region_reads_an_outer_definition() {
        let mut graph = Graph::default();
        let entry = graph.push(Op::Entry, &[], at(0), None);
        let param = graph.push(
            Op::Param {
                index: 0,
                ty: Some(Ty::Int),
            },
            &[],
            at(1),
            Some(at(1)),
        );
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
