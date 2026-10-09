//! The value graph: one table of nodes per file, each an op over its edges, in regions that run
//! only while their context node is live. Every node a node names is an edge with a [`Role`], the
//! operands first, so one walk reaches all of them. A read of a local is an edge to its
//! definition, not a node, and what could not be built is a hole over what was, so a rejected
//! file's graph is complete.

use std::num::NonZeroU32;
use std::ops::Range;

use crate::{BinaryOp, CmpOp, FunctionId, Int, Ty};

/// A function's nodes: the entry, then one per parameter, then its body region's, then the
/// declared-result copy if any.
#[derive(Debug)]
pub struct Run {
    nodes: Range<u32>,
    arity: u32,
    region: RegionId,
    result: NodeId,
    params: Option<Box<[Ty]>>,
}

impl Run {
    /// The parameter types a call is held to: one per parameter node, present when the declared
    /// list is whole and every type resolved.
    pub fn param_types(&self) -> Option<&[Ty]> {
        self.params.as_deref()
    }

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
    /// The input under a `let` name or a declared result; `declared` is the annotation's type,
    /// and the copy has that type whatever flows in.
    Copy {
        declared: Option<Ty>,
    },
    /// A mutable local's next SSA version: its input is the assigned value, its reference the
    /// local's declaration.
    Assign,
    /// The machine-bound index; inputs are the inclusive start and exclusive end.
    LoopIndex,
    /// A machine-bound mutable local at the loop header: its input is the initial value, its
    /// reference the local's declaration.
    Carry,
    /// Executes `body` for each integer in its start-inclusive, end-exclusive input bounds. Its
    /// references are the index, the continuation and empty contexts, then a carry and its next
    /// value per carried local.
    Loop {
        body: RegionId,
    },
    /// A carried local's final value, including on zero trips: its input is the loop node, its
    /// references the carry and its next value.
    LoopValue,
    /// A mutable local's value after a conditional fork. Inputs are the condition, true value,
    /// and false value; the references are the local's declaration, then the contexts that gate
    /// the true and false values in the abstract domain.
    Phi,
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
    /// The first input is the ordinary body result; the rest are explicit returns; `declared` is
    /// the result annotation's type.
    Result {
        declared: Option<Ty>,
    },
    /// A call to a function whose run has parameter types; the inputs are the arguments as
    /// written, which may not match its arity.
    Call(FunctionId),
}

impl Op {
    /// The regions the op runs itself.
    pub fn regions(&self) -> impl Iterator<Item = RegionId> + use<> {
        let [first, second] = match *self {
            Self::Join { then, else_ } => [Some(then), else_],
            Self::Observe { then, else_ } => [then, else_],
            Self::And { rhs } | Self::Or { rhs } => [Some(rhs), None],
            Self::Loop { body } => [Some(body), None],
            _ => [None, None],
        };
        [first, second].into_iter().flatten()
    }

    /// The op with each region it runs replaced.
    pub fn with_regions(self, mut map: impl FnMut(RegionId) -> RegionId) -> Self {
        match self {
            Self::Join { then, else_ } => Self::Join {
                then: map(then),
                else_: else_.map(&mut map),
            },
            Self::Observe { then, else_ } => Self::Observe {
                then: then.map(&mut map),
                else_: else_.map(&mut map),
            },
            Self::And { rhs } => Self::And { rhs: map(rhs) },
            Self::Or { rhs } => Self::Or { rhs: map(rhs) },
            Self::Loop { body } => Self::Loop { body: map(body) },
            op => op,
        }
    }
}

/// What an edge is to the node that holds it. A node's operands come first among its edges; the
/// rest reference nodes the op names but does not read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    /// An operand that supplies an ordinary value.
    Value,
    /// An operand that completes the function instead of supplying a value.
    Completes,
    /// The declaration of the mutable local a version is of.
    Declaration,
    /// A context that gates a value in the abstract domain.
    Context,
    /// A loop's machine-bound index.
    Index,
    /// A loop header carrying a mutable local; the carry's next value follows.
    Carry,
    Next,
}

impl Role {
    pub fn is_value(self) -> bool {
        self == Self::Value
    }
}

/// The nodes an op names but does not read, in the form its variant states; the builder stores
/// them as edges by role and the graph reads them back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum References<'a> {
    None,
    /// `Assign` and `Carry`: the declaration of the local the version is of.
    Version(NodeId),
    /// `Phi`: the local's declaration, then the contexts gating the true and false values.
    Phi {
        declaration: NodeId,
        contexts: [NodeId; 2],
    },
    /// `Loop`: the index, the context live after an iteration, the context live when no
    /// iteration runs, and the carried locals.
    Loop {
        index: NodeId,
        continuation: NodeId,
        empty: NodeId,
        carried: Carried<'a>,
    },
    /// `LoopValue`: the carry read and its next value.
    LoopValue {
        carry: NodeId,
        next: NodeId,
    },
}

/// A loop's carries, each followed by its next value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Carried<'a>(&'a [NodeId]);

impl<'a> Carried<'a> {
    /// `nodes` alternates a carry and its next value.
    pub fn new(nodes: &'a [NodeId]) -> Self {
        assert_eq!(nodes.len() % 2, 0, "a carry has its next value");
        Self(nodes)
    }

    pub fn nodes(self) -> &'a [NodeId] {
        self.0
    }

    pub fn len(self) -> usize {
        self.0.len() / 2
    }

    pub fn is_empty(self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(self) -> impl DoubleEndedIterator<Item = (NodeId, NodeId)> + ExactSizeIterator {
        self.0
            .as_chunks::<2>()
            .0
            .iter()
            .map(|&[carry, next]| (carry, next))
    }
}

impl References<'_> {
    /// `self` over the nodes `map` gives; `carried` holds a loop's mapped carries.
    pub fn map<'b>(
        self,
        carried: &'b mut Vec<NodeId>,
        mut map: impl FnMut(NodeId) -> NodeId,
    ) -> References<'b> {
        match self {
            Self::None => References::None,
            Self::Version(declaration) => References::Version(map(declaration)),
            Self::Phi {
                declaration,
                contexts,
            } => References::Phi {
                declaration: map(declaration),
                contexts: contexts.map(&mut map),
            },
            Self::Loop {
                index,
                continuation,
                empty,
                carried: nodes,
            } => {
                let (index, continuation, empty) = (map(index), map(continuation), map(empty));
                carried.clear();
                carried.extend(nodes.nodes().iter().map(|&node| map(node)));
                References::Loop {
                    index,
                    continuation,
                    empty,
                    carried: Carried::new(carried),
                }
            }
            Self::LoopValue { carry, next } => References::LoopValue {
                carry: map(carry),
                next: map(next),
            },
        }
    }

    /// Whether `op` names what `self` holds.
    fn fits(&self, op: &Op) -> bool {
        match (op, self) {
            (Op::Assign | Op::Carry, Self::Version(_))
            | (Op::Phi, Self::Phi { .. })
            | (Op::Loop { .. }, Self::Loop { .. })
            | (Op::LoopValue, Self::LoopValue { .. }) => true,
            (Op::Assign | Op::Carry | Op::Phi | Op::Loop { .. } | Op::LoopValue, _)
            | (
                _,
                Self::Version(_) | Self::Phi { .. } | Self::Loop { .. } | Self::LoopValue { .. },
            ) => false,
            (_, Self::None) => true,
        }
    }

    fn encode(&self, edges: &mut Vec<NodeId>, roles: &mut Vec<Role>) {
        match *self {
            Self::None => {}
            Self::Version(declaration) => {
                edges.push(declaration);
                roles.push(Role::Declaration);
            }
            Self::Phi {
                declaration,
                contexts,
            } => {
                edges.extend([declaration, contexts[0], contexts[1]]);
                roles.extend([Role::Declaration, Role::Context, Role::Context]);
            }
            Self::Loop {
                index,
                continuation,
                empty,
                carried,
            } => {
                edges.extend([index, continuation, empty]);
                roles.extend([Role::Index, Role::Context, Role::Context]);
                edges.extend_from_slice(carried.nodes());
                roles.extend(
                    [Role::Carry, Role::Next]
                        .into_iter()
                        .cycle()
                        .take(carried.nodes().len()),
                );
            }
            Self::LoopValue { carry, next } => {
                edges.extend([carry, next]);
                roles.extend([Role::Carry, Role::Next]);
            }
        }
    }

    /// The inverse of `encode`, told apart by the roles.
    fn decode<'a>(edges: &'a [NodeId], roles: &[Role]) -> References<'a> {
        match (edges, roles) {
            ([], []) => References::None,
            (&[declaration], [Role::Declaration]) => References::Version(declaration),
            (&[declaration, then, else_], [Role::Declaration, Role::Context, Role::Context]) => {
                References::Phi {
                    declaration,
                    contexts: [then, else_],
                }
            }
            (&[carry, next], [Role::Carry, Role::Next]) => References::LoopValue { carry, next },
            (
                [index, continuation, empty, carried @ ..],
                [Role::Index, Role::Context, Role::Context, ..],
            ) => References::Loop {
                index: *index,
                continuation: *continuation,
                empty: *empty,
                carried: Carried(carried),
            },
            _ => unreachable!("references are stored as encoded"),
        }
    }
}

#[derive(Debug)]
pub struct Node {
    pub op: Op,
    edges: Range<u32>,
    operands: u32,
}

const _: () = assert!(size_of::<Node>() == 32, "nodes stay four words");

/// The nodes with their edges, shared by the builder and the finished graph.
#[derive(Debug, Default)]
struct Store {
    nodes: Vec<Node>,
    edges: Vec<NodeId>,
    roles: Vec<Role>,
}

impl Store {
    fn with_capacity(nodes: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(nodes),
            edges: Vec::with_capacity(nodes),
            roles: Vec::with_capacity(nodes),
        }
    }

    fn range(&self, id: NodeId) -> Range<usize> {
        let node = &self.nodes[id.index()];
        node.edges.start as usize..node.edges.end as usize
    }

    fn operands(&self, id: NodeId) -> Range<usize> {
        let node = &self.nodes[id.index()];
        node.edges.start as usize..node.edges.start as usize + node.operands as usize
    }

    fn references(&self, id: NodeId) -> References<'_> {
        let node = &self.nodes[id.index()];
        let range = node.edges.start as usize + node.operands as usize..node.edges.end as usize;
        References::decode(&self.edges[range.clone()], &self.roles[range])
    }

    fn push(
        &mut self,
        op: Op,
        inputs: impl IntoIterator<Item = NodeId>,
        references: References<'_>,
    ) -> NodeId {
        assert!(references.fits(&op), "{op:?} names {references:?}");
        let start = u32::try_from(self.edges.len()).expect("edge count fits u32");
        self.edges.extend(inputs);
        let operands = self.edges.len() - start as usize;
        self.roles.resize(self.edges.len(), Role::Value);
        references.encode(&mut self.edges, &mut self.roles);
        let end = u32::try_from(self.edges.len()).expect("edge count fits u32");
        let id = NodeId::new(self.nodes.len());
        self.nodes.push(Node {
            op,
            edges: start..end,
            operands: u32::try_from(operands).expect("operand count fits u32"),
        });
        id
    }
}

#[derive(Debug)]
pub struct Region {
    pub context: NodeId,
    nodes: Range<u32>,
    result: NodeId,
    result_has_value: bool,
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
        self.result_has_value
    }

    pub fn control(&self) -> Option<NodeId> {
        self.control
    }
}

#[derive(Debug)]
pub struct Graph {
    store: Store,
    regions: Vec<Region>,
    runs: Vec<Run>,
}

impl Graph {
    pub fn node(&self, id: NodeId) -> &Node {
        &self.store.nodes[id.index()]
    }

    /// The operands, then the references.
    pub fn edges(&self, id: NodeId) -> &[NodeId] {
        &self.store.edges[self.store.range(id)]
    }

    /// Parallel to `edges`.
    pub fn roles(&self, id: NodeId) -> &[Role] {
        &self.store.roles[self.store.range(id)]
    }

    /// The operands: the edges the node reads a value, or a completion, from.
    pub fn inputs(&self, id: NodeId) -> &[NodeId] {
        &self.store.edges[self.store.operands(id)]
    }

    /// Parallel to `inputs`: `Value` or `Completes` each.
    pub fn input_roles(&self, id: NodeId) -> &[Role] {
        &self.store.roles[self.store.operands(id)]
    }

    /// The nodes `id`'s op names but does not read.
    pub fn references(&self, id: NodeId) -> References<'_> {
        self.store.references(id)
    }

    /// The declaration an `Assign`, `Carry`, or `Phi` is a version of.
    pub fn declaration(&self, id: NodeId) -> NodeId {
        match self.references(id) {
            References::Version(declaration) | References::Phi { declaration, .. } => declaration,
            _ => unreachable!("{id:?} is no version of a local"),
        }
    }

    /// The contexts gating a `Phi`'s true and false values.
    pub fn phi_contexts(&self, id: NodeId) -> [NodeId; 2] {
        let References::Phi { contexts, .. } = self.references(id) else {
            unreachable!("{id:?} is no phi")
        };
        contexts
    }

    /// A `Loop`'s index node.
    pub fn loop_index(&self, id: NodeId) -> NodeId {
        self.loop_references(id).0
    }

    /// A `Loop`'s continuation context, live after an iteration, and its empty context, live
    /// when no iteration runs.
    pub fn loop_contexts(&self, id: NodeId) -> [NodeId; 2] {
        let (_, continuation, empty, _) = self.loop_references(id);
        [continuation, empty]
    }

    /// Each carry of a `Loop` with its next value, in carried order.
    pub fn carried(
        &self,
        id: NodeId,
    ) -> impl DoubleEndedIterator<Item = (NodeId, NodeId)> + ExactSizeIterator {
        self.loop_references(id).3.iter()
    }

    fn loop_references(&self, id: NodeId) -> (NodeId, NodeId, NodeId, Carried<'_>) {
        let References::Loop {
            index,
            continuation,
            empty,
            carried,
        } = self.references(id)
        else {
            unreachable!("{id:?} is no loop")
        };
        (index, continuation, empty, carried)
    }

    /// The carry a `LoopValue` reads and its next value.
    pub fn carry(&self, id: NodeId) -> (NodeId, NodeId) {
        let References::LoopValue { carry, next } = self.references(id) else {
            unreachable!("{id:?} is no loop value")
        };
        (carry, next)
    }

    /// Indexed by function ID.
    pub fn runs(&self) -> &[Run] {
        &self.runs
    }

    pub fn run(&self, id: FunctionId) -> &Run {
        &self.runs[id.index()]
    }

    pub fn nodes(&self) -> &[Node] {
        &self.store.nodes
    }

    pub fn node_ids(&self) -> impl ExactSizeIterator<Item = NodeId> + use<> {
        (0..self.store.nodes.len()).map(NodeId::new)
    }

    /// Outermost first where regions nest.
    pub fn region_ids(&self) -> impl ExactSizeIterator<Item = RegionId> + use<> {
        (0..self.regions.len()).map(RegionId::new)
    }

    pub fn region(&self, id: RegionId) -> &Region {
        &self.regions[id.index()]
    }
}

#[derive(Debug)]
struct Opening {
    context: NodeId,
    /// The first node's index once entered.
    start: Option<u32>,
    closed: Option<Closed>,
}

/// A region's end in node order, its result, whether the result supplies a value, and its
/// control.
#[derive(Debug)]
struct Closed {
    end: u32,
    result: NodeId,
    result_has_value: bool,
    control: Option<NodeId>,
}

#[derive(Debug)]
enum Slot {
    Declared(Option<Box<[Ty]>>),
    Open(Option<Box<[Ty]>>),
    Closed(Run),
}

impl Slot {
    fn param_types(&self) -> Option<&[Ty]> {
        match self {
            Self::Declared(params) | Self::Open(params) => params.as_deref(),
            Self::Closed(run) => run.param_types(),
        }
    }
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
    store: Store,
    regions: Vec<Opening>,
    runs: Vec<Slot>,
}

impl GraphBuilder {
    pub fn node(&self, id: NodeId) -> &Node {
        &self.store.nodes[id.index()]
    }

    pub fn inputs(&self, id: NodeId) -> &[NodeId] {
        &self.store.edges[self.store.operands(id)]
    }

    /// `nodes` is the count to expect.
    pub fn new(nodes: usize) -> Self {
        Self {
            store: Store::with_capacity(nodes),
            regions: Vec::new(),
            runs: Vec::new(),
        }
    }

    /// The next function, in declaration order; `params` is its whole parameter list, every type
    /// resolved, or none.
    pub fn function(&mut self, params: Option<Box<[Ty]>>) -> FunctionId {
        let function = FunctionId::new(self.runs.len());
        self.runs.push(Slot::Declared(params));
        function
    }

    /// As [`Run::param_types`], whether or not the run has opened or closed.
    pub fn param_types(&self, function: FunctionId) -> Option<&[Ty]> {
        self.runs[function.index()].param_types()
    }

    /// `references` must be the form `op` names.
    pub fn push(
        &mut self,
        op: Op,
        inputs: impl IntoIterator<Item = NodeId>,
        references: References<'_>,
    ) -> NodeId {
        self.store.push(op, inputs, references)
    }

    /// Marks an input as structurally completing the current function instead of yielding a value.
    pub fn complete_input(&mut self, node: NodeId, index: usize) {
        let operands = self.store.operands(node);
        assert!(
            index < operands.len(),
            "an input exists before it completes"
        );
        self.store.roles[operands.start + index] = Role::Completes;
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
        let start = u32::try_from(self.store.nodes.len()).expect("node count fits u32");
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
        result_has_value: bool,
        control: Option<NodeId>,
    ) {
        let end = u32::try_from(self.store.nodes.len()).expect("node count fits u32");
        let opening = &mut self.regions[region.index()];
        assert!(
            opening.start.is_some(),
            "a region is entered before it closes"
        );
        opening.closed = Some(Closed {
            end,
            result,
            result_has_value,
            control,
        });
    }

    pub fn context(&self, region: RegionId) -> NodeId {
        self.regions[region.index()].context
    }

    /// The run's nodes begin with the next push: its entry, then one per parameter. A function's
    /// run opens once.
    pub fn open_run(&mut self, function: FunctionId) -> OpenRun {
        let slot = &mut self.runs[function.index()];
        let Slot::Declared(params) = std::mem::replace(slot, Slot::Open(None)) else {
            panic!("a function's run opens once")
        };
        *slot = Slot::Open(params);
        OpenRun {
            function,
            start: u32::try_from(self.store.nodes.len()).expect("node count fits u32"),
        }
    }

    /// `region` is the body's, already closed; a run with parameter types has one parameter node
    /// per type.
    pub fn close_run(&mut self, run: OpenRun, region: RegionId, result: NodeId) {
        let end = u32::try_from(self.store.nodes.len()).expect("node count fits u32");
        let arity = self.store.nodes[run.start as usize..]
            .iter()
            .skip(1)
            .take_while(|node| matches!(node.op, Op::Param { .. }))
            .count();
        let slot = &mut self.runs[run.function.index()];
        let Slot::Open(params) = std::mem::replace(slot, Slot::Open(None)) else {
            unreachable!("a run closes once, after it opens")
        };
        assert!(
            params.as_ref().is_none_or(|params| params.len() == arity),
            "a parameter node per parameter type"
        );
        *slot = Slot::Closed(Run {
            nodes: run.start..end,
            arity: u32::try_from(arity).expect("parameter count fits u32"),
            region,
            result,
            params,
        });
    }

    /// Every region opened must be closed, and every function's run opened and closed.
    pub fn finish(self) -> Graph {
        Graph {
            store: self.store,
            regions: self
                .regions
                .into_iter()
                .map(|opening| {
                    let closed = opening.closed.expect("a region opened is closed");
                    Region {
                        context: opening.context,
                        nodes: opening.start.expect("a region closed was entered")..closed.end,
                        result: closed.result,
                        result_has_value: closed.result_has_value,
                        control: closed.control,
                    }
                })
                .collect(),
            runs: self
                .runs
                .into_iter()
                .map(|slot| match slot {
                    Slot::Closed(run) => run,
                    Slot::Open(_) => panic!("a run opened is closed"),
                    Slot::Declared(_) => panic!("a function declared has a run"),
                })
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ArithOp;

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
        let entry = builder.push(Op::Entry, [], References::None);
        let region = builder.open(entry);
        builder.enter(region);
        let one = builder.push(Op::Int(1.into()), [], References::None);
        let sum = builder.push(
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            [one, one],
            References::None,
        );
        builder.complete_input(sum, 1);
        builder.close_with_control(region, sum, false, None);
        let graph = builder.finish();

        assert_eq!(graph.inputs(sum), [one, one]);
        assert_eq!(graph.input_roles(sum), [Role::Value, Role::Completes]);
        assert!(!graph.region(region).result_has_value());
    }

    #[test]
    fn runs_and_regions_follow_the_protocol() {
        let mut builder = GraphBuilder::new(8);
        let function = builder.function(None);
        let run = builder.open_run(function);
        let entry = builder.push(Op::Entry, [], References::None);
        let param = builder.push(
            Op::Param {
                index: 0,
                ty: Some(Ty::Int),
            },
            [],
            References::None,
        );
        let region = builder.open(entry);
        assert_eq!(builder.context(region), entry);
        builder.enter(region);
        let one = builder.push(Op::Int(1.into()), [], References::None);
        let sum = builder.push(
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            [param, one],
            References::None,
        );
        builder.close(region, sum);
        let copy = builder.push(Op::Copy { declared: None }, [sum], References::None);
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
        assert_eq!(graph.input_roles(sum), [Role::Value, Role::Value]);
        assert_eq!(graph.inputs(entry), []);
        assert_eq!(graph.input_roles(entry), []);
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
        let function = builder.function(None);
        let run = builder.open_run(function);
        let entry = builder.push(Op::Entry, [], References::None);
        let param = builder.push(
            Op::Param {
                index: 0,
                ty: Some(Ty::Int),
            },
            [],
            References::None,
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
        let entry = builder.push(Op::Entry, [], References::None);
        builder.open(entry);
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "a region is entered before it closes")]
    fn a_region_closes_only_entered() {
        let mut builder = GraphBuilder::new(1);
        let entry = builder.push(Op::Entry, [], References::None);
        let region = builder.open(entry);
        builder.close(region, entry);
    }

    #[test]
    #[should_panic(expected = "a run opened is closed")]
    fn an_open_run_does_not_finish() {
        let mut builder = GraphBuilder::new(1);
        let function = builder.function(None);
        let run = builder.open_run(function);
        builder.push(Op::Entry, [], References::None);
        drop(run);
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "a function declared has a run")]
    fn a_function_without_a_run_does_not_finish() {
        let mut builder = GraphBuilder::new(0);
        builder.function(None);
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "a function's run opens once")]
    fn a_run_opens_once() {
        let mut builder = GraphBuilder::new(2);
        let function = builder.function(None);
        let run = builder.open_run(function);
        let entry = builder.push(Op::Entry, [], References::None);
        let region = builder.open(entry);
        builder.enter(region);
        builder.close(region, entry);
        builder.close_run(run, region, entry);
        let _again = builder.open_run(function);
    }
}
