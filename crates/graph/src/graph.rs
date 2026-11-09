//! The value graph: one table of nodes per file, each an op over its edges, in regions that run
//! only while their context node is live. Every node a node names is an edge with a [`Role`], the
//! operands first, so one walk reaches all of them. A read of a local is an edge to its
//! definition, not a node, and what could not be built is a hole over what was, so a rejected
//! file's graph is complete.

use std::num::NonZeroU32;
use std::ops::Range;

use crate::{BinaryOp, CmpOp, DeclId, FieldName, FunctionId, Int, Ty, TyKind, UnionId};

mod rebuild;
pub use rebuild::Rebuild;

/// A declared type: its fields by name, in declaration order, each with its type when that
/// resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    fields: Box<[(FieldName, Option<Ty>)]>,
}

impl Decl {
    pub fn new(fields: Box<[(FieldName, Option<Ty>)]>) -> Self {
        Self { fields }
    }

    pub fn fields(&self) -> &[(FieldName, Option<Ty>)] {
        &self.fields
    }

    /// The position of the field called `name`.
    pub fn index_of(&self, name: FieldName) -> Option<usize> {
        self.fields.iter().position(|&(field, _)| field == name)
    }

    /// The field types a construction is held to, present when every one resolved.
    pub fn field_types(&self) -> Option<Box<[Ty]>> {
        self.fields.iter().map(|&(_, ty)| ty).collect()
    }
}

/// The unions by ID: each a sorted set of two or more declared types, interned, so equal sets
/// share an ID.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Unions(Vec<Box<[DeclId]>>);

impl Unions {
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    pub fn get(&self, id: UnionId) -> &[DeclId] {
        &self.0[id.index()]
    }

    /// The ID of the union of `members`, minted if new; `members` need not be sorted or distinct.
    /// None for fewer than two distinct members, which are no union.
    pub fn intern(&mut self, members: impl IntoIterator<Item = DeclId>) -> Option<UnionId> {
        let mut members: Vec<DeclId> = members.into_iter().collect();
        members.sort_unstable();
        members.dedup();
        if members.len() < 2 {
            return None;
        }
        let members = members.into_boxed_slice();
        let index = self
            .0
            .iter()
            .position(|union| *union == members)
            .unwrap_or_else(|| {
                self.0.push(members);
                self.0.len() - 1
            });
        Some(UnionId::new(index))
    }

    /// The declared types `ty` admits: a union's members, or the declared type itself.
    pub fn members(&self, ty: Ty) -> &[DeclId] {
        match ty.kind() {
            TyKind::Union(id) => self.get(id),
            TyKind::Decl(_) | TyKind::Int | TyKind::Bool | TyKind::Unit => &[],
        }
    }

    /// Whether a value of the declared type `decl` is one of `ty`.
    pub fn admits(&self, ty: Ty, decl: DeclId) -> bool {
        ty.as_decl() == Some(decl) || self.members(ty).contains(&decl)
    }

    /// Whether every value of `actual` is one of `expected`.
    pub fn fits(&self, actual: Ty, expected: Ty) -> bool {
        if actual == expected {
            return true;
        }
        match actual.kind() {
            TyKind::Decl(decl) => self.admits(expected, decl),
            TyKind::Union(id) => self.get(id).iter().all(|&decl| self.admits(expected, decl)),
            TyKind::Int | TyKind::Bool | TyKind::Unit => false,
        }
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// What an arm of a switch selects of the scrutinee.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Case {
    Bool(bool),
    /// A value of the type, or of a member of it.
    Is(Ty),
    /// A value of no member of the type: a rest arm after arms naming them.
    Not(Ty),
    /// Any declared value: a rest arm after none.
    Any,
}

impl Case {
    pub fn selects_decl(self, decl: DeclId, unions: &Unions) -> bool {
        match self {
            Self::Bool(_) => false,
            Self::Is(ty) => unions.admits(ty, decl),
            Self::Not(ty) => !unions.admits(ty, decl),
            Self::Any => true,
        }
    }
}

/// A switch's arms: the regions `open_arms` opened together, so they are consecutive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Arms {
    first: RegionId,
    len: u32,
}

impl Arms {
    #[inline]
    pub fn iter(self) -> impl DoubleEndedIterator<Item = RegionId> + ExactSizeIterator {
        let first = self.first.0.get();
        (first..first + self.len).map(|raw| RegionId(NonZeroU32::new(raw).unwrap()))
    }

    pub fn len(self) -> usize {
        self.len as usize
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    /// `self` over the regions `map` gives, which keeps them consecutive.
    pub fn map(self, mut map: impl FnMut(RegionId) -> RegionId) -> Self {
        if self.len == 0 {
            return self;
        }
        let first = map(self.first);
        for (offset, region) in self.iter().enumerate().skip(1) {
            debug_assert_eq!(
                map(region).index(),
                first.index() + offset,
                "arms stay consecutive"
            );
        }
        Self {
            first,
            len: self.len,
        }
    }
}

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
    #[inline]
    pub fn new(index: usize) -> Self {
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("node count fits u32")).unwrap())
    }

    #[inline]
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
    #[inline]
    fn new(index: usize) -> Self {
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("region count fits u32")).unwrap())
    }

    #[inline]
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
    /// A mutable local's value after a switch. Inputs are the scrutinee, then a value per arm; the
    /// references are the local's declaration, then the arm context that gates each value, whose
    /// case selects it.
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
    /// Its input's values of the type: the binding of a switch arm.
    Narrow(Ty),
    /// An expression statement: no value itself.
    Unused,
    Entry,
    /// An arm's context: the inputs are the scrutinee, then the enclosing context; live where the
    /// case selects the scrutinee.
    Arm(Case),
    /// The input is the scrutinee; the value is the first arm's result whose case selects it, or
    /// unit when none does.
    Switch {
        arms: Arms,
    },
    /// Completes the current function with its first input; the second is its analysis context.
    Return,
    /// Evaluates its first input for control, then yields its second.
    Sequence,
    /// The inputs are the scrutinee and analysis context. Observes only the selected arm's control
    /// projection and yields unit if it falls through, or when no arm's case selects.
    Observe {
        arms: Arms,
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
    /// A value of the declared type over its inputs, one per field in declaration order.
    Make(DeclId),
    /// The field so named of its input, whatever declared type reaches it.
    Field(FieldName),
}

impl Op {
    /// The regions the op runs itself.
    pub fn regions(&self) -> impl Iterator<Item = RegionId> + use<> {
        let (arms, single) = match *self {
            Self::Switch { arms } | Self::Observe { arms } => (Some(arms), None),
            Self::And { rhs } | Self::Or { rhs } => (None, Some(rhs)),
            Self::Loop { body } => (None, Some(body)),
            _ => (None, None),
        };
        arms.into_iter().flat_map(Arms::iter).chain(single)
    }

    /// The op with each region it runs replaced; a switch's arms stay consecutive.
    pub fn with_regions(self, mut map: impl FnMut(RegionId) -> RegionId) -> Self {
        match self {
            Self::Switch { arms } => Self::Switch {
                arms: arms.map(map),
            },
            Self::Observe { arms } => Self::Observe {
                arms: arms.map(map),
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

/// A node's read of an ordinary value or a completion of its function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    Value(NodeId),
    Completes(NodeId),
}

impl Operand {
    pub fn node(self) -> NodeId {
        match self {
            Self::Value(node) | Self::Completes(node) => node,
        }
    }
}

/// The nodes an op names but does not read, in the form its variant states; the builder stores
/// them as edges by role and the graph reads them back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum References<'a> {
    None,
    /// `Assign` and `Carry`: the declaration of the local the version is of.
    Version(NodeId),
    /// `Phi`: the local's declaration, then the arm context gating each value.
    Phi {
        declaration: NodeId,
        contexts: &'a [NodeId],
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

    fn encode(
        &self,
        edges: &mut Vec<NodeId>,
        roles: &mut Vec<Role>,
        mut map: impl FnMut(NodeId) -> NodeId,
    ) {
        match *self {
            Self::None => {}
            Self::Version(declaration) => {
                edges.push(map(declaration));
                roles.push(Role::Declaration);
            }
            Self::Phi {
                declaration,
                contexts,
            } => {
                edges.push(map(declaration));
                roles.push(Role::Declaration);
                edges.extend(contexts.iter().copied().map(map));
                roles.extend(contexts.iter().map(|_| Role::Context));
            }
            Self::Loop {
                index,
                continuation,
                empty,
                carried,
            } => {
                edges.extend([index, continuation, empty].map(&mut map));
                roles.extend([Role::Index, Role::Context, Role::Context]);
                edges.extend(carried.nodes().iter().copied().map(map));
                roles.extend(
                    [Role::Carry, Role::Next]
                        .into_iter()
                        .cycle()
                        .take(carried.nodes().len()),
                );
            }
            Self::LoopValue { carry, next } => {
                edges.extend([carry, next].map(map));
                roles.extend([Role::Carry, Role::Next]);
            }
        }
    }

    /// The inverse of `encode`, told apart by the roles.
    fn decode<'a>(edges: &'a [NodeId], roles: &[Role]) -> References<'a> {
        match (edges, roles) {
            ([], []) => References::None,
            (&[declaration], [Role::Declaration]) => References::Version(declaration),
            (&[carry, next], [Role::Carry, Role::Next]) => References::LoopValue { carry, next },
            ([declaration, contexts @ ..], [Role::Declaration, Role::Context, ..]) => {
                References::Phi {
                    declaration: *declaration,
                    contexts,
                }
            }
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

    #[inline]
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
        inputs: impl IntoIterator<Item = Operand>,
        references: References<'_>,
        mut map: impl FnMut(NodeId) -> NodeId,
    ) -> NodeId {
        assert!(references.fits(&op), "{op:?} names {references:?}");
        let start = u32::try_from(self.edges.len()).expect("edge count fits u32");
        for input in inputs {
            self.edges.push(map(input.node()));
            self.roles.push(match input {
                Operand::Value(_) => Role::Value,
                Operand::Completes(_) => Role::Completes,
            });
        }
        let operands = self.edges.len() - start as usize;
        references.encode(&mut self.edges, &mut self.roles, map);
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
    decls: Vec<Decl>,
    unions: Unions,
}

impl Graph {
    #[inline]
    pub fn node(&self, id: NodeId) -> &Node {
        &self.store.nodes[id.index()]
    }

    /// Indexed by declared type ID.
    pub fn decls(&self) -> &[Decl] {
        &self.decls
    }

    pub fn decl(&self, id: DeclId) -> &Decl {
        &self.decls[id.index()]
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
    #[inline]
    pub fn inputs(&self, id: NodeId) -> &[NodeId] {
        &self.store.edges[self.store.operands(id)]
    }

    /// Parallel to `inputs`: `Value` or `Completes` each.
    #[inline]
    pub fn input_roles(&self, id: NodeId) -> &[Role] {
        &self.store.roles[self.store.operands(id)]
    }

    pub fn operands(&self, id: NodeId) -> impl ExactSizeIterator<Item = Operand> + '_ {
        self.inputs(id)
            .iter()
            .zip(self.input_roles(id))
            .map(|(&node, role)| match role {
                Role::Value => Operand::Value(node),
                Role::Completes => Operand::Completes(node),
                _ => unreachable!("operands precede references"),
            })
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

    /// The arm contexts gating a `Phi`'s values, one per value.
    pub fn phi_contexts(&self, id: NodeId) -> &[NodeId] {
        let References::Phi { contexts, .. } = self.references(id) else {
            unreachable!("{id:?} is no phi")
        };
        contexts
    }

    /// The case of the arm `context` is in: itself, or the arm a continuation context follows.
    #[inline]
    pub fn case(&self, mut context: NodeId) -> Case {
        loop {
            match self.node(context).op {
                Op::Arm(case) => return case,
                Op::After => context = self.inputs(context)[1],
                ref op => unreachable!("{context:?} is {op:?}, in no arm"),
            }
        }
    }

    pub fn unions(&self) -> &Unions {
        &self.unions
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

    #[inline]
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
    decls: Vec<Decl>,
    unions: Unions,
}

impl GraphBuilder {
    #[inline]
    pub fn node(&self, id: NodeId) -> &Node {
        &self.store.nodes[id.index()]
    }

    #[inline]
    pub fn inputs(&self, id: NodeId) -> &[NodeId] {
        &self.store.edges[self.store.operands(id)]
    }

    /// `nodes` is the count to expect.
    pub fn new(nodes: usize) -> Self {
        Self {
            store: Store::with_capacity(nodes),
            regions: Vec::new(),
            runs: Vec::new(),
            decls: Vec::new(),
            unions: Unions::default(),
        }
    }

    /// The union of `members`, interned; see [`Unions::intern`].
    pub fn union(&mut self, members: impl IntoIterator<Item = DeclId>) -> Option<Ty> {
        self.unions.intern(members).map(Ty::union)
    }

    pub fn unions(&self) -> &Unions {
        &self.unions
    }

    /// The unions the ops name, which must cover every `Ty::union` pushed.
    pub fn set_unions(&mut self, unions: Unions) {
        self.unions = unions;
    }

    /// The declared types in declaration order, so `DeclId::new(i)` is the `i`th; the field types
    /// name them the same way.
    pub fn declare(&mut self, decls: impl IntoIterator<Item = Decl>) {
        assert!(self.decls.is_empty(), "the types are declared once");
        self.decls.extend(decls);
    }

    pub fn decl(&self, id: DeclId) -> &Decl {
        &self.decls[id.index()]
    }

    pub fn decls(&self) -> &[Decl] {
        &self.decls
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
        self.store.push(
            op,
            inputs.into_iter().map(Operand::Value),
            references,
            std::convert::identity,
        )
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

    /// A switch's arms, one region per context, opened together so they stay consecutive.
    pub fn open_arms(&mut self, contexts: &[NodeId]) -> Arms {
        let first = RegionId::new(self.regions.len());
        for &context in contexts {
            self.open(context);
        }
        Arms {
            first,
            len: u32::try_from(contexts.len()).expect("arm count fits u32"),
        }
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
            decls: self.decls,
            unions: self.unions,
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
                ty: Some(Ty::INT),
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
                ty: Some(Ty::INT),
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
