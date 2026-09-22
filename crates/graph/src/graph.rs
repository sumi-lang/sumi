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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoopId(u32);

impl LoopId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub struct Loop {
    pub body: RegionId,
    pub index: NodeId,
    pub carried: Box<[(NodeId, NodeId)]>,
    pub continuation: NodeId,
    pub empty: NodeId,
}

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
    /// A mutable local's next SSA version; its input is the assigned value.
    Assign {
        declaration: NodeId,
    },
    /// The machine-bound index; inputs are the inclusive start and exclusive end.
    LoopIndex,
    /// A machine-bound mutable local at the loop header; its input is the initial value.
    Carry {
        declaration: NodeId,
    },
    /// Executes the body for each integer in its start-inclusive, end-exclusive input bounds.
    Loop(LoopId),
    /// The final carry at `index`, including on zero trips; its input is the loop node.
    LoopValue {
        loop_: LoopId,
        index: u32,
    },
    /// A mutable local's value after a conditional fork. Inputs are the condition, true value,
    /// and false value; `contexts` gate the corresponding values in the abstract domain.
    Phi {
        declaration: NodeId,
        contexts: [NodeId; 2],
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
    /// Completes the current function with its first input; the second is its analysis context.
    Return,
    /// Evaluates its first input for control, then yields its second.
    Sequence,
    /// The inputs are the condition and analysis context. Observes only the selected region's
    /// control projection and yields unit if it falls through.
    Observe {
        then: Option<RegionId>,
        else_: Option<RegionId>,
    },
    /// A continuation context after the control in its first input, inside its second input.
    After,
    /// The first input is the ordinary body result; the rest are explicit returns.
    Result {
        declared: Option<(Ty, TextRange)>,
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
    result: NodeId,
    result_value: bool,
    control: Option<NodeId>,
}

impl Region {
    /// Includes the nodes of nested regions.
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (self.nodes.start as usize..self.nodes.end as usize).map(NodeId::new)
    }

    /// The index in node order where the region begins, which an empty region has too.
    pub fn start(&self) -> usize {
        self.nodes.start as usize
    }

    pub fn result(&self) -> NodeId {
        self.result
    }

    /// Whether the result supplies an ordinary value when the region is entered.
    pub fn result_has_value(&self) -> bool {
        self.result_value
    }

    pub fn control(&self) -> Option<NodeId> {
        self.control
    }
}

#[derive(Debug)]
pub struct Graph {
    nodes: Vec<Node>,
    loops: Vec<Loop>,
    inputs: Vec<NodeId>,
    input_values: Vec<bool>,
    reads: Vec<TextRange>,
    regions: Vec<Region>,
    runs: Vec<Run>,
    callables: Vec<Callable>,
}

impl Graph {
    pub fn loop_(&self, id: LoopId) -> &Loop {
        &self.loops[id.index()]
    }

    pub fn loop_ids(&self) -> impl ExactSizeIterator<Item = LoopId> + use<> {
        (0..self.loops.len()).map(|index| LoopId(index as u32))
    }

    pub fn callable(&self, callee: Callee) -> &Callable {
        &self.callables[callee.index()]
    }

    /// In declaration order.
    pub fn callables(&self) -> &[Callable] {
        &self.callables
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

    /// Whether each input supplies an ordinary value rather than completing its function.
    pub fn input_values(&self, id: NodeId) -> &[bool] {
        let node = &self.nodes[id.index()];
        &self.input_values[node.inputs.start as usize..node.inputs.end as usize]
    }

    /// Where `id` reads each input, parallel to `inputs`: the read's range, not the definition's.
    pub fn reads(&self, id: NodeId) -> &[TextRange] {
        let node = &self.nodes[id.index()];
        &self.reads[node.inputs.start as usize..node.inputs.end as usize]
    }
}

#[derive(Debug)]
struct Opening {
    context: NodeId,
    /// The first node's index once entered.
    start: Option<u32>,
    /// The end, result, whether it supplies a value, and control once closed.
    closed: Option<(u32, NodeId, bool, Option<NodeId>)>,
}

#[derive(Debug)]
enum Slot {
    Declared,
    Open,
    Closed(Run),
}

/// A run between `open_run` and `close_run`.
#[must_use = "a run opened is closed"]
#[derive(Debug)]
pub struct OpenRun {
    function: FunctionId,
    start: u32,
}

/// Builds a [`Graph`]: nodes in push order, each region's nodes those pushed between `enter` and
/// `close`, each run's those pushed between `open_run` and `close_run`; runs do not overlap.
#[derive(Debug)]
pub struct GraphBuilder {
    nodes: Vec<Node>,
    loops: Vec<Loop>,
    inputs: Vec<NodeId>,
    input_values: Vec<bool>,
    reads: Vec<TextRange>,
    regions: Vec<Opening>,
    runs: Vec<Slot>,
    callables: Vec<Callable>,
}

impl GraphBuilder {
    /// `nodes` is the count to expect.
    pub fn new(nodes: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(nodes),
            loops: Vec::new(),
            inputs: Vec::with_capacity(nodes),
            input_values: Vec::with_capacity(nodes),
            reads: Vec::with_capacity(nodes),
            regions: Vec::new(),
            runs: Vec::new(),
            callables: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, loop_: Loop) -> LoopId {
        let id = LoopId(u32::try_from(self.loops.len()).expect("loop count fits u32"));
        self.loops.push(loop_);
        id
    }

    /// The next function, in declaration order.
    pub fn function(&mut self) -> FunctionId {
        let function = FunctionId::new(self.runs.len());
        self.runs.push(Slot::Declared);
        function
    }

    pub fn callable(&self, callee: Callee) -> &Callable {
        &self.callables[callee.index()]
    }

    /// `params` is `function`'s whole parameter list, one type per parameter node of its run.
    pub fn declare(&mut self, function: FunctionId, params: Box<[Ty]>) -> Callee {
        let callee = Callee(u32::try_from(self.callables.len()).expect("function count fits u32"));
        self.callables.push(Callable { function, params });
        callee
    }

    pub fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.index()]
    }

    pub fn inputs(&self, id: NodeId) -> &[NodeId] {
        let node = &self.nodes[id.index()];
        &self.inputs[node.inputs.start as usize..node.inputs.end as usize]
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
        self.input_values.reserve(inputs.len());
        self.reads.reserve(inputs.len());
        for &(input, read) in inputs {
            self.inputs.push(input);
            self.input_values.push(true);
            self.reads.push(read);
        }
        let end = u32::try_from(self.inputs.len()).expect("input count fits u32");
        let id = NodeId::new(self.nodes.len());
        self.nodes.push(Node {
            op,
            inputs: start..end,
            origin,
            name,
        });
        id
    }

    /// Marks an input as structurally completing the current function instead of yielding a value.
    pub fn complete_input(&mut self, node: NodeId, index: usize) {
        let inputs = self.nodes[node.index()].inputs.clone();
        assert!(index < inputs.len(), "an input exists before it completes");
        self.input_values[inputs.start as usize + index] = false;
    }

    /// An `if` opens both branches before entering either.
    pub fn open(&mut self, context: NodeId) -> RegionId {
        let id = RegionId::new(self.regions.len());
        self.regions.push(Opening {
            context,
            start: None,
            closed: None,
        });
        id
    }

    pub fn enter(&mut self, region: RegionId) {
        let start = u32::try_from(self.nodes.len()).expect("node count fits u32");
        self.regions[region.index()].start = Some(start);
    }

    /// The region must have been entered.
    pub fn close(&mut self, region: RegionId, result: NodeId) {
        self.close_with_control(region, result, true, None);
    }

    /// The region must have been entered; `control` observes returns without demanding `result`.
    pub fn close_with_control(
        &mut self,
        region: RegionId,
        result: NodeId,
        result_value: bool,
        control: Option<NodeId>,
    ) {
        let end = u32::try_from(self.nodes.len()).expect("node count fits u32");
        let opening = &mut self.regions[region.index()];
        assert!(
            opening.start.is_some(),
            "a region is entered before it closes"
        );
        opening.closed = Some((end, result, result_value, control));
    }

    pub fn context(&self, region: RegionId) -> NodeId {
        self.regions[region.index()].context
    }

    /// The run's nodes begin with the next push: its entry, then one per parameter. A function's
    /// run opens once.
    pub fn open_run(&mut self, function: FunctionId) -> OpenRun {
        let slot = &mut self.runs[function.index()];
        assert!(
            matches!(slot, Slot::Declared),
            "a function's run opens once"
        );
        *slot = Slot::Open;
        OpenRun {
            function,
            start: u32::try_from(self.nodes.len()).expect("node count fits u32"),
        }
    }

    /// `region` is the body's, already closed.
    pub fn close_run(&mut self, run: OpenRun, region: RegionId, result: NodeId) {
        let end = u32::try_from(self.nodes.len()).expect("node count fits u32");
        let arity = self.nodes[run.start as usize..]
            .iter()
            .skip(1)
            .take_while(|node| matches!(node.op, Op::Param { .. }))
            .count();
        self.runs[run.function.index()] = Slot::Closed(Run {
            nodes: run.start..end,
            arity: u32::try_from(arity).expect("parameter count fits u32"),
            region,
            result,
        });
    }

    /// Every region opened must be closed, and every function's run opened and closed.
    pub fn finish(self) -> Graph {
        Graph {
            nodes: self.nodes,
            loops: self.loops,
            inputs: self.inputs,
            input_values: self.input_values,
            reads: self.reads,
            regions: self
                .regions
                .into_iter()
                .map(|opening| {
                    let (end, result, result_value, control) =
                        opening.closed.expect("a region opened is closed");
                    Region {
                        context: opening.context,
                        nodes: opening.start.expect("a region closed was entered")..end,
                        result,
                        result_value,
                        control,
                    }
                })
                .collect(),
            runs: self
                .runs
                .into_iter()
                .map(|slot| match slot {
                    Slot::Closed(run) => run,
                    Slot::Open => panic!("a run opened is closed"),
                    Slot::Declared => panic!("a function declared has a run"),
                })
                .collect(),
            callables: self.callables,
        }
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
    fn value_completion_belongs_to_reads_and_region_results() {
        let mut builder = GraphBuilder::new(3);
        let entry = builder.push(Op::Entry, &[], at(0), None);
        let region = builder.open(entry);
        builder.enter(region);
        let one = builder.push(Op::Int(1.into()), &[], at(1), None);
        let sum = builder.push(
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            &[(one, at(2)), (one, at(3))],
            at(4),
            None,
        );
        builder.complete_input(sum, 1);
        builder.close_with_control(region, sum, false, None);
        let graph = builder.finish();

        assert_eq!(graph.inputs(sum), [one, one]);
        assert_eq!(graph.input_values(sum), [true, false]);
        assert!(!graph.region(region).result_has_value());
    }

    #[test]
    fn runs_and_regions_follow_the_protocol() {
        let mut builder = GraphBuilder::new(8);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = builder.push(Op::Entry, &[], at(0), None);
        let param = builder.push(
            Op::Param {
                index: 0,
                ty: Some(Ty::Int),
            },
            &[],
            at(1),
            Some(at(1)),
        );
        let region = builder.open(entry);
        assert_eq!(builder.context(region), entry);
        builder.enter(region);
        let one = builder.push(Op::Int(1.into()), &[], at(2), None);
        let sum = builder.push(
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            &[(param, at(5)), (one, at(2))],
            at(3),
            None,
        );
        builder.close(region, sum);
        let copy = builder.push(Op::Copy { declared: None }, &[(sum, at(3))], at(4), None);
        builder.close_run(run, region, copy);
        let graph = builder.finish();
        assert_eq!(graph.nodes().len(), 5);
        let run = graph.run(function);
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
        assert_eq!(graph.input_values(sum), [true, true]);
        assert_eq!(graph.reads(sum), [at(5), at(2)]);
        assert_eq!(graph.inputs(entry), []);
        assert_eq!(graph.input_values(entry), []);
        assert_eq!(graph.reads(entry), []);
        assert_eq!(graph.node(param).name, Some(at(1)));
        let region = graph.region(region);
        assert_eq!(region.context, entry);
        assert_eq!(region.nodes().collect::<Vec<_>>(), [one, sum]);
        assert_eq!(region.result(), sum);
        assert!(region.result_has_value());
        assert_eq!(region.control(), None);
        assert_eq!(graph.region_ids().count(), 1);
    }

    #[test]
    fn an_empty_region_reads_an_outer_definition() {
        let mut builder = GraphBuilder::new(2);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = builder.push(Op::Entry, &[], at(0), None);
        let param = builder.push(
            Op::Param {
                index: 0,
                ty: Some(Ty::Int),
            },
            &[],
            at(1),
            Some(at(1)),
        );
        let region = builder.open(entry);
        builder.enter(region);
        builder.close(region, param);
        builder.close_run(run, region, param);
        let graph = builder.finish();
        assert_eq!(graph.region(region).nodes().len(), 0);
        assert_eq!(graph.region(region).start(), 2);
        assert_eq!(graph.region(region).result(), param);
    }

    #[test]
    #[should_panic(expected = "a region opened is closed")]
    fn an_open_region_does_not_finish() {
        let mut builder = GraphBuilder::new(1);
        let entry = builder.push(Op::Entry, &[], at(0), None);
        builder.open(entry);
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "a region is entered before it closes")]
    fn a_region_closes_only_entered() {
        let mut builder = GraphBuilder::new(1);
        let entry = builder.push(Op::Entry, &[], at(0), None);
        let region = builder.open(entry);
        builder.close(region, entry);
    }

    #[test]
    #[should_panic(expected = "a run opened is closed")]
    fn an_open_run_does_not_finish() {
        let mut builder = GraphBuilder::new(1);
        let function = builder.function();
        let run = builder.open_run(function);
        builder.push(Op::Entry, &[], at(0), None);
        drop(run);
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "a function declared has a run")]
    fn a_function_without_a_run_does_not_finish() {
        let mut builder = GraphBuilder::new(0);
        builder.function();
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "a function's run opens once")]
    fn a_run_opens_once() {
        let mut builder = GraphBuilder::new(2);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = builder.push(Op::Entry, &[], at(0), None);
        let region = builder.open(entry);
        builder.enter(region);
        builder.close(region, entry);
        builder.close_run(run, region, entry);
        let _again = builder.open_run(function);
    }
}
