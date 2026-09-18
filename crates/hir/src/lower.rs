//! Lowering of one file to the graph: names, structure, and holes.
//!
//! Every function's header is read first: its name, its parameter types,
//! and what its declaration says of its result. A structural walk per
//! function then resolves names and builds the body's nodes of the graph,
//! marking which carry a value the typing follows, and records what the
//! walk learns beyond the graph: a demand wherever a context requires a
//! value to have a type, and every division. The walk rejects nothing on
//! type grounds; it fails only on names, syntax, and unsupported
//! constructs, and what it refuses it leaves as a hole.
//!
//! Names are never copied: every map is keyed by a slice of the source,
//! and the one builder keeps its scratch across bodies, so a body costs
//! its nodes of the graph and nothing else.

use std::collections::HashMap;
use std::collections::hash_map::Entry;

use rustc_hash::FxBuildHasher;
use sumi_frontend::{DiagnosticCode, Label};
use sumi_lexer::{RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    NodeIdx, NodeKind, SyntaxTree,
    ast::{self, AstNode},
};

use crate::codes;
use crate::lattice::Claim;
use crate::typing::{Expected, Typing};
use crate::*;

/// A map from names, as slices of the source, to whatever they name.
type NameMap<'s, V> = HashMap<&'s str, V, FxBuildHasher>;

/// What a function name resolves to. One word, so the table of every
/// function in the file stays small enough to probe from cache.
#[derive(Clone, Copy)]
enum Named {
    Function(FunctionId),
    /// Declared more than once; the first declaration, for the report.
    Ambiguous(FunctionId),
}

impl Named {
    fn first(self) -> FunctionId {
        match self {
            Self::Function(id) | Self::Ambiguous(id) => id,
        }
    }
}

pub(crate) struct Header {
    /// Where the name is written, when the item has one.
    pub name: Option<TextRange>,
    /// The parameter types, when the parameter list is whole.
    pub params: Option<Box<[Ty]>>,
    /// The type each parameter's node carries, whole list or not: none for
    /// a parameter without one, or a duplicate, whose reads are held to
    /// nothing while the signature keeps its type.
    pub param_types: Box<[Option<Ty>]>,
    pub result: HeaderResult,
    pub item: NodeIdx,
}

/// What a declaration says of its result.
#[derive(Clone, Copy)]
pub(crate) enum HeaderResult {
    /// The declaration is too damaged to have one.
    None,
    /// A declared type, at the annotation or, for a bare block body, the
    /// whole item: a contract the body is held to, never changed by it.
    Declared(Ty, NodeIdx),
    /// A result to infer from the body.
    Inferred,
}

/// What a context requires of an expression, checked after solving.
pub(crate) enum DemandKind {
    /// The expression must have the expected type, which a declaration may
    /// have set: a called function, a result annotation, or a binding's
    /// annotation.
    Type {
        expected: Expected,
        declared: Option<NodeIdx>,
    },
    /// An expression statement's value must be unit.
    Unused,
    /// The operands of `==` and `!=` must not be unit.
    Comparable,
    /// The branches of an `if` must agree on one type: the expression is
    /// the `if`, and each branch delivers its type to it first.
    Agree { branches: [NodeId; 2] },
}

/// One demand, kept small: the verdict pass reads every one, and a body
/// makes one per operand, argument, branch, and statement.
pub(crate) struct Demand {
    pub owner: u32,
    pub node: NodeIdx,
    pub actual: NodeId,
    pub kind: DemandKind,
}

/// A division whose divisor must exclude zero wherever it can run.
pub(crate) struct Obligation {
    pub owner: u32,
    pub node: NodeIdx,
    pub divisor: NodeId,
    pub context: NodeId,
}

/// A whole call: its node, its ends, the context it runs in, and its run
/// of the arguments as written.
pub(crate) struct Call {
    pub node: NodeId,
    pub caller: FunctionId,
    pub callee: FunctionId,
    pub context: NodeId,
    arguments: std::ops::Range<u32>,
}

/// What the walk of every body leaves beside the graph for the verdicts.
pub(crate) struct Lowered {
    /// Whether each body built whole.
    pub built: Vec<bool>,
    /// Whether each node carries a value the typing follows, by
    /// [`Builder::follows`].
    pub typed: Vec<bool>,
    /// Every whole call, in definition order.
    pub calls: Vec<Call>,
    /// The arguments of every whole call as written, one run per call,
    /// which a read passed as an argument has no node of its own to say.
    arguments: Vec<NodeIdx>,
    /// Every call that reached a callee with parameters, whole or not, as
    /// the context it runs in and the callee: the callee is checked on the
    /// strength of any call to it.
    pub entered: Vec<(NodeId, FunctionId)>,
    pub demands: Vec<Demand>,
    pub obligations: Vec<Obligation>,
}

impl Lowered {
    /// The arguments of `call` as written.
    pub fn arguments(&self, call: &Call) -> &[NodeIdx] {
        &self.arguments[call.arguments.start as usize..call.arguments.end as usize]
    }
}

/// One file's source and tree, and the diagnostics checking it makes.
pub(crate) struct Source<'s> {
    pub parsed: &'s ParsedSource,
    pub tree: &'s SyntaxTree,
    pub diagnostics: Vec<Diagnostic>,
}

impl<'s> Source<'s> {
    pub fn new(parsed: &'s ParsedSource) -> Self {
        Self {
            parsed,
            tree: parsed.parse().tree(),
            diagnostics: Vec::new(),
        }
    }
    pub fn range(&self, node: NodeIdx) -> TextRange {
        self.tree.byte_range(node, self.parsed.lexed())
    }
    pub fn text(&self, node: NodeIdx) -> &'s str {
        self.tree
            .byte_range(node, self.parsed.lexed())
            .text(self.parsed.source())
    }
    fn name(&self, name: Option<ast::Name>) -> Option<(&'s str, NodeIdx)> {
        let node = name?.node();
        (!self.tree.has_error(node)
            && self.parsed.lexed().kind(self.tree.first_token(node)) == SyntaxKind::Ident)
            .then(|| (self.text(node), node))
    }
    pub fn error(
        &mut self,
        node: NodeIdx,
        code: DiagnosticCode,
        message: impl Into<Box<str>>,
        related: Option<(TextRange, &'static str)>,
    ) {
        let related = related.map(|(range, message)| (range, Box::from(message)));
        self.report(self.range(node), code, message, related);
    }
    pub fn report(
        &mut self,
        primary: TextRange,
        code: DiagnosticCode,
        message: impl Into<Box<str>>,
        related: impl IntoIterator<Item = (TextRange, Box<str>)>,
    ) {
        self.diagnostics
            .push(diagnostic(primary, code, message, related));
    }
    pub fn type_mismatch(
        &mut self,
        node: NodeIdx,
        expected: Ty,
        actual: Ty,
        related: Option<(TextRange, &'static str)>,
    ) {
        self.error(
            node,
            codes::TYPE_MISMATCH,
            format!("expected {expected}, found {actual}"),
            related,
        );
    }
    /// Report that `node` is claimed to be every type in `claims`, in
    /// source order, and where each claim was made. `message` wraps the
    /// list of types.
    pub fn conflict(
        &mut self,
        node: NodeIdx,
        code: DiagnosticCode,
        typing: &Typing,
        claims: &[(Ty, Claim)],
        message: impl FnOnce(String) -> String,
    ) {
        let mut claims: Vec<_> = claims
            .iter()
            .map(|(ty, claim)| (*ty, typing.origin(*claim)))
            .collect();
        claims.sort_by_key(|(_, origin)| origin.map(|range| range.start()));
        let types: Vec<_> = claims.iter().map(|(ty, _)| ty.to_string()).collect();
        let (last, rest) = types.split_last().expect("a conflict names two types");
        let joined = if rest.len() == 1 {
            format!("{} and {last}", rest[0])
        } else {
            format!("{}, and {last}", rest.join(", "))
        };
        let labels = claims
            .into_iter()
            .filter_map(|(ty, origin)| Some((origin?, format!("{ty} here").into())));
        self.report(self.range(node), code, message(joined), labels);
    }
    fn ty(&mut self, node: ast::TypeRef) -> Option<Ty> {
        if self.tree.has_error(node.node()) {
            return None;
        }
        let name = self.text(node.node());
        let ty = Ty::from_name(name);
        if ty.is_none() {
            self.error(
                node.node(),
                codes::UNKNOWN_TYPE,
                format!("unknown type `{name}`"),
                None,
            );
        }
        ty
    }
    // Read only a token gap, never scan an expression subtree for its operator.
    fn tokens(&self, start: RawIdx, end: RawIdx) -> impl Iterator<Item = SyntaxKind> + '_ {
        start
            .until(end)
            .map(|raw| self.parsed.lexed().kind(raw))
            .filter(|kind| !kind.is_trivia())
    }
    fn peel(&self, mut expr: ast::Expr) -> ast::Expr {
        while let ast::Expr::ParenExpr(paren) = expr {
            if self.tree.has_error(paren.node()) {
                break;
            }
            expr = paren.inner(self.tree).expect("clean parentheses");
        }
        expr
    }
}

/// An error at `primary` with `related` labels.
pub(crate) fn diagnostic(
    primary: TextRange,
    code: DiagnosticCode,
    message: impl Into<Box<str>>,
    related: impl IntoIterator<Item = (TextRange, Box<str>)>,
) -> Diagnostic {
    Diagnostic {
        code,
        message: message.into(),
        primary,
        labels: related
            .into_iter()
            .map(|(range, message)| Label { range, message })
            .collect(),
        fix: None,
    }
}

pub(crate) struct Parameter<'s> {
    node: NodeIdx,
    name: Option<(&'s str, NodeIdx)>,
    /// The declared type, whether or not the name is a duplicate: the
    /// signature keeps it.
    ty: Option<Ty>,
    /// Named like an earlier parameter, whose reads are held to nothing.
    duplicate: bool,
}

/// The headers of every function, the names that resolve to them, and
/// their parameters.
pub(crate) struct Declarations<'s> {
    pub headers: Vec<Header>,
    names: NameMap<'s, Named>,
    parameters: Vec<Vec<Parameter<'s>>>,
}

/// The header of every item: its name, parameter types, and what its
/// declaration says of its result.
pub(crate) fn declare<'s>(source: &mut Source<'s>, items: &[ast::FnItem]) -> Declarations<'s> {
    let tree = source.tree;
    let mut names: NameMap<Named> = NameMap::with_capacity_and_hasher(items.len(), FxBuildHasher);
    let mut parameters = Vec::with_capacity(items.len());
    let mut headers = Vec::with_capacity(items.len());
    for item in items {
        let name = source.name(item.name(tree));
        let id = FunctionId::new(headers.len());
        if let Some((name, node)) = name {
            match names.entry(name) {
                Entry::Occupied(mut entry) => {
                    let first = items[entry.get().first().index()]
                        .name(tree)
                        .expect("a named function has a name")
                        .node();
                    source.error(
                        node,
                        codes::DUPLICATE_NAME,
                        format!("duplicate function `{name}`"),
                        Some((source.range(first), "declared here")),
                    );
                    *entry.get_mut() = Named::Ambiguous(entry.get().first());
                }
                Entry::Vacant(entry) => {
                    entry.insert(Named::Function(id));
                }
            }
        }
        let list = item.param_list(tree);
        let mut valid = list.is_some_and(|list| !tree.has_error(list.node()));
        let mut params: Vec<Parameter> = Vec::new();
        if let Some(list) = list {
            for param in list.params(tree) {
                // An item's parameter has a type or a syntax error: the
                // parser requires the annotation.
                let ty = param.type_ref(tree).and_then(|ty| source.ty(ty));
                valid &= ty.is_some();
                let name = source.name(param.name(tree));
                let first = name.and_then(|(name, node)| {
                    let first = params
                        .iter()
                        .find_map(|p| p.name.filter(|(earlier, _)| *earlier == name))?;
                    Some((name, node, first.1))
                });
                if let Some((name, node, first)) = first {
                    source.error(
                        node,
                        codes::DUPLICATE_NAME,
                        format!("duplicate parameter `{name}`"),
                        Some((source.range(first), "declared here")),
                    );
                }
                params.push(Parameter {
                    node: param.node(),
                    name,
                    ty,
                    duplicate: first.is_some(),
                });
            }
        }
        let result = if let Some(ret) = item.ret(tree) {
            match source.ty(ret) {
                Some(ty) => HeaderResult::Declared(ty, ret.node()),
                None => HeaderResult::None,
            }
        } else {
            // A missing annotation can mean damaged syntax, not omission.
            // Only an empty gap or the expression-body `=` says it was left
            // out: a bare block is unit, an expression body is inferred.
            let gap = list
                .filter(|list| !tree.has_error(list.node()))
                .map(|list| {
                    let end = item
                        .body(tree)
                        .map_or(tree.end_token(item.node()), |e| tree.first_token(e.node()));
                    let mut tokens = source.tokens(tree.end_token(list.node()), end);
                    (tokens.next(), tokens.next())
                });
            match gap {
                Some((None, None)) => HeaderResult::Declared(Ty::Unit, item.node()),
                Some((Some(SyntaxKind::Eq), None)) => HeaderResult::Inferred,
                _ => HeaderResult::None,
            }
        };
        headers.push(Header {
            name: name.map(|(_, node)| source.range(node)),
            params: valid.then(|| params.iter().map(|p| p.ty.unwrap()).collect()),
            param_types: params
                .iter()
                .map(|p| p.ty.filter(|_| !p.duplicate))
                .collect(),
            result,
            item: item.node(),
        });
        parameters.push(params);
    }
    Declarations {
        headers,
        names,
        parameters,
    }
}

/// The graph of every body, and what the walk left beside it.
pub(crate) fn lower<'s>(
    source: &mut Source<'s>,
    items: &[ast::FnItem],
    declared: &Declarations<'s>,
) -> (Graph, Lowered) {
    let mut builder = Builder::new(source, &declared.headers, &declared.names);
    for (index, (item, params)) in items.iter().zip(&declared.parameters).enumerate() {
        let built = builder.build(index, *item, params);
        builder.lowered.built.push(built);
    }
    (builder.graph, builder.lowered)
}

/// The eager operator a syntactic one is, if it is not lazy.
fn eager(op: sumi_syntax::BinaryOp) -> Option<BinaryOp> {
    use sumi_syntax::BinaryOp::*;
    Some(match op {
        Add => BinaryOp::Add,
        Sub => BinaryOp::Sub,
        Mul => BinaryOp::Mul,
        Div => BinaryOp::Div,
        Rem => BinaryOp::Rem,
        Eq => BinaryOp::Eq,
        Ne => BinaryOp::Ne,
        Lt => BinaryOp::Lt,
        Le => BinaryOp::Le,
        Gt => BinaryOp::Gt,
        Ge => BinaryOp::Ge,
        And | Or => return None,
    })
}

/// An index into a run of the placed arguments, which the syntax tree's
/// node count bounds.
fn run(index: usize) -> u32 {
    u32::try_from(index).expect("list index fits u32")
}

/// The names in scope, each bound to the node that defines it: a
/// parameter, a `let`, or the hole a damaged `let` leaves. Scope
/// transitions and let completion are explicit work items, so
/// initializers see the old scope.
type Scope<'s> = NameMap<'s, NodeId>;

enum Work {
    Enter(NodeIdx),
    Finish(NodeIdx),
    /// A call whose arguments are walked, to the function its callee
    /// names, when it names one.
    Call(NodeIdx, Option<FunctionId>),
    /// An `if` whose condition is walked: open its branches' contexts.
    Branches(NodeIdx),
    /// A lazy operator whose left operand is walked: open the right one's.
    Rhs(NodeIdx),
    /// An `if` whose branches are walked in these regions.
    Join {
        node: NodeIdx,
        then: RegionId,
        else_: Option<RegionId>,
    },
    /// A lazy operator whose right operand is walked in `rhs`.
    Lazy {
        node: NodeIdx,
        rhs: RegionId,
    },
    /// Enter `region`, narrowing the locals the condition `guard`
    /// compares, holding in its sense, for the reads inside it.
    Push {
        region: RegionId,
        guard: (NodeIdx, bool),
    },
    /// Leave `region`, whose value is what `root` built.
    Pop {
        region: RegionId,
        root: NodeIdx,
    },
}

/// Push `nodes` to enter, first to be entered last: the stack walks them
/// in the order given.
fn enter_each(work: &mut Vec<Work>, nodes: impl Iterator<Item = NodeIdx>) {
    let base = work.len();
    work.extend(nodes.map(Work::Enter));
    work[base..].reverse();
}

/// The one walker for every body of the file. What a body builds are its
/// nodes of the graph; everything else the walk needs is kept and reused,
/// so no body pays for scratch.
struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    headers: &'a [Header],
    names: &'a NameMap<'s, Named>,
    graph: Graph,
    lowered: Lowered,
    /// The graph node each syntax node built, by node.
    nodes_of: Vec<Option<NodeId>>,
    // The body under construction.
    owner: u32,
    failed: bool,
    /// The open regions, innermost last: where a pushed node stands, and
    /// whose context the point runs in, with where each one's refinements
    /// begin in `refinements`.
    regions: Vec<(RegionId, usize)>,
    /// The nodes locals read as inside the open regions, innermost last,
    /// by the local's defining node.
    refinements: Vec<(NodeId, NodeId)>,
    // Scratch kept across bodies.
    /// A pool of scopes; the first `depth` are open, innermost last. A map
    /// per scope costs a probe per enclosing scope on lookup, and nothing on
    /// close; an undo log measured slower on binding-heavy code, since every
    /// binding then pays a removal.
    scopes: Vec<Scope<'s>>,
    depth: usize,
    work: Vec<Work>,
    /// The inputs of the node being pushed, when there are more than two.
    inputs: Vec<NodeId>,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
        source: &'a mut Source<'s>,
        headers: &'a [Header],
        names: &'a NameMap<'s, Named>,
    ) -> Self {
        // About a node per syntax node of a body, and a demand per two;
        // only a guide.
        let nodes = source.tree.len();
        Self {
            source,
            headers,
            names,
            graph: Graph::with_capacity(nodes),
            lowered: Lowered {
                built: Vec::with_capacity(headers.len()),
                typed: Vec::with_capacity(nodes),
                calls: Vec::new(),
                arguments: Vec::new(),
                entered: Vec::new(),
                demands: Vec::with_capacity(nodes / 2),
                obligations: Vec::new(),
            },
            // Syntax node IDs are dense and bodies have disjoint nodes.
            nodes_of: vec![None; nodes],
            owner: 0,
            failed: false,
            regions: Vec::new(),
            refinements: Vec::new(),
            scopes: Vec::new(),
            depth: 0,
            work: Vec::new(),
            inputs: Vec::new(),
        }
    }
    /// Build the body of the function `owner`, closing its run of the
    /// graph: whether the walk built it whole.
    fn build(&mut self, owner: usize, item: ast::FnItem, parameters: &[Parameter<'s>]) -> bool {
        self.owner = u32::try_from(owner).expect("function count fits u32");
        self.failed = false;
        self.depth = 0;
        self.open_scope();
        self.regions.clear();
        self.refinements.clear();
        let header = &self.headers[owner];
        let item_node = header.item;
        let start = self.graph.next();
        let entry = self.push(item_node, Op::Entry, &[], None);
        let arity = u32::try_from(parameters.len()).expect("parameter count fits u32");
        for (index, param) in parameters.iter().enumerate() {
            let index = u32::try_from(index).expect("parameter count fits u32");
            let name = param.name.map(|(_, node)| self.source.range(node));
            let node = self.push(param.node, Op::Param(index), &[], name);
            self.failed |= param.ty.is_none() || param.duplicate;
            if let Some((name, _)) = param.name {
                self.bind(name, node);
            } else {
                self.failed = true;
            }
        }
        let declared = header.result;
        self.failed |= header.params.is_none() || matches!(declared, HeaderResult::None);
        let tree = self.source.tree;
        let region = self.graph.open(entry);
        self.graph.enter(region);
        self.regions.push((region, 0));
        let root_node = item.body(tree).map(|body| body.node());
        if let Some(root_node) = root_node {
            let mut work = std::mem::take(&mut self.work);
            work.push(Work::Enter(root_node));
            while let Some(task) = work.pop() {
                let built = match task {
                    Work::Finish(node) => self.finish(node),
                    Work::Call(node, target) => self.call(node, target),
                    Work::Join { node, then, else_ } => self.join(node, then, else_),
                    Work::Lazy { node, rhs } => self.lazy(node, rhs),
                    Work::Enter(node) => {
                        self.enter(node, &mut work);
                        continue;
                    }
                    Work::Branches(node) => {
                        self.branches(node, &mut work);
                        continue;
                    }
                    Work::Rhs(node) => {
                        self.rhs(node, &mut work);
                        continue;
                    }
                    Work::Push { region, guard } => {
                        self.regions.push((region, self.refinements.len()));
                        self.graph.enter(region);
                        self.refine(guard.0, guard.1);
                        continue;
                    }
                    Work::Pop { region, root } => {
                        let result = self.node_of(root);
                        self.graph.close(region, result);
                        let (_, keep) = self
                            .regions
                            .pop()
                            .expect("a region opened before it closes");
                        self.refinements.truncate(keep);
                        continue;
                    }
                };
                self.failed |= built.is_none();
            }
            self.work = work;
        }
        let root = root_node.and_then(|root| self.typed(root));
        let body_value = match root_node {
            Some(root) => self.node_of(root),
            None => self.push(item_node, Op::Hole, &[], None),
        };
        self.graph.close(region, body_value);
        self.regions.pop();
        // A failed parameter does not erase an independently known result
        // type. A declared result is a contract on the body; an inferred one
        // is the body's own value.
        let value = match declared {
            HeaderResult::Declared(ty, node) => self.push(
                node,
                Op::Copy {
                    declared: Some((ty, self.source.range(node))),
                },
                &[body_value],
                None,
            ),
            HeaderResult::Inferred | HeaderResult::None => body_value,
        };
        if let (Some(root), HeaderResult::Declared(ty, node)) = (root, declared) {
            self.require(root_node.unwrap(), root, Expected::Ty(ty), Some(node));
        }
        self.graph
            .close_run(FunctionId::new(owner), start, arity, region, value);
        !self.failed && root.is_some()
    }
    /// A graph node at `node`, which reads `inputs`.
    fn push(
        &mut self,
        node: NodeIdx,
        op: Op,
        inputs: &[NodeId],
        name: Option<TextRange>,
    ) -> NodeId {
        let id = self.place(op, inputs, self.source.range(node), name);
        self.nodes_of[node.to_usize()] = Some(id);
        id
    }
    /// A graph node that no syntax node is said to have built.
    fn place(
        &mut self,
        op: Op,
        inputs: &[NodeId],
        origin: TextRange,
        name: Option<TextRange>,
    ) -> NodeId {
        let typed = self.follows(&op, inputs);
        let id = self.graph.push(op, inputs, origin, name);
        self.lowered.typed.push(typed);
        id
    }
    /// Whether a node computing `op` from `inputs` carries a value the
    /// typing follows. A hole carries none, and neither does a node built
    /// over one: a lazy operator or an `if` over an untyped operand or
    /// branch, a call short of an argument, which is a hole. A context is
    /// followed whatever its condition; a parameter needs a type, a call
    /// a callee with a result, and a declared copy has its declaration
    /// whatever flows in.
    fn follows(&self, op: &Op, inputs: &[NodeId]) -> bool {
        let typed = |node: NodeId| self.lowered.typed[node.index()];
        let result = |region: RegionId| typed(self.graph.region(region).result());
        match *op {
            Op::Hole => false,
            Op::Entry | Op::Then | Op::Else | Op::Copy { declared: Some(_) } => true,
            Op::Param(index) => {
                self.headers[self.owner as usize].param_types[index as usize].is_some()
            }
            Op::Call(callee) => {
                inputs.iter().all(|&input| typed(input))
                    && !matches!(self.headers[callee.index()].result, HeaderResult::None)
            }
            Op::And { rhs } | Op::Or { rhs } => typed(inputs[0]) && result(rhs),
            Op::Join { then, else_ } => {
                typed(inputs[0]) && result(then) && else_.is_none_or(result)
            }
            _ => inputs.iter().all(|&input| typed(input)),
        }
    }
    /// A context node for the region whose syntax is `region`, derived
    /// from `condition` under `parent`. It is not what `region` built: the
    /// region's own node is its value, which the context gates.
    fn context_at(&mut self, region: NodeIdx, op: Op, condition: NodeId, parent: NodeId) -> NodeId {
        self.place(op, &[condition, parent], self.source.range(region), None)
    }
    /// The graph node `node` built, or a hole where nothing was: syntax
    /// the walk could not reach.
    fn node_of(&mut self, node: NodeIdx) -> NodeId {
        match self.nodes_of[node.to_usize()] {
            Some(id) => id,
            None => self.push(node, Op::Hole, &[], None),
        }
    }
    /// The value `node` built, if it built one the typing follows: a hole,
    /// and a node built over one, are none.
    fn typed(&self, node: NodeIdx) -> Option<NodeId> {
        let id = self.nodes_of[node.to_usize()]?;
        self.lowered.typed[id.index()].then_some(id)
    }
    /// A hole at `node`, over nothing: syntax the walk refuses.
    fn hole(&mut self, node: NodeIdx) -> NodeId {
        self.push(node, Op::Hole, &[], None)
    }
    fn open_scope(&mut self) {
        if self.depth == self.scopes.len() {
            self.scopes.push(Scope::default());
        } else {
            self.scopes[self.depth].clear();
        }
        self.depth += 1;
    }
    fn close_scope(&mut self) {
        self.depth -= 1;
    }
    /// Bind `name` to the local `node` defines until the innermost scope
    /// closes.
    fn bind(&mut self, name: &'s str, node: NodeId) {
        self.scopes[self.depth - 1].insert(name, node);
    }
    /// The node defining the local `name` reads, if one is in scope.
    fn lookup(&self, name: &str) -> Option<NodeId> {
        // An empty scope, the common case for a function's own, would cost
        // a hash to find nothing in.
        self.scopes[..self.depth]
            .iter()
            .rev()
            .filter(|scope| !scope.is_empty())
            .find_map(|scope| scope.get(name).copied())
    }
    /// The node a read of the local `defined` reads here: the innermost
    /// refinement that covers it, or the local's own.
    fn current(&self, defined: NodeId) -> NodeId {
        self.refinements
            .iter()
            .rev()
            .find(|(local, _)| *local == defined)
            .map_or(defined, |(_, node)| *node)
    }
    /// The context the open region runs in.
    fn context(&self) -> NodeId {
        let (region, _) = *self.regions.last().expect("a body runs in its region");
        self.graph.region(region).context
    }
    /// The operator of a clean binary expression, read from the token gap
    /// between its operands.
    fn binary_op(&self, node: NodeIdx) -> sumi_syntax::BinaryOp {
        let tree = self.source.tree;
        let binary = ast::BinaryExpr::cast(tree, node).unwrap();
        let lhs_node = binary.lhs(tree).unwrap().node();
        let rhs_node = binary.rhs(tree).unwrap().node();
        let lexed = self.source.parsed.lexed();
        let end = tree.first_token(rhs_node);
        let first = tree
            .end_token(lhs_node)
            .until(end)
            .find(|&raw| !lexed.kind(raw).is_trivia())
            .expect("clean binary operator");
        // Raw tokens partition source: the immediately adjacent token is
        // glued, whereas any intervening trivia breaks a compound.
        let glued = (first + 1 < end).then(|| lexed.kind(first + 1));
        sumi_syntax::binary_operator(lexed.kind(first), glued)
            .expect("clean binary operator")
            .0
    }
    /// The local the name at `node` reads, if it is a read of one with a
    /// value the typing follows. The scope is as it was when the read was
    /// built: a region is entered right after its condition finishes.
    fn read(&self, node: NodeIdx) -> Option<NodeId> {
        let tree = self.source.tree;
        let node = self.source.peel(ast::Expr::cast(tree, node)?).node();
        if tree.kind(node) != NodeKind::NameRef {
            return None;
        }
        let defined = self.lookup(self.source.text(node))?;
        self.lowered.typed[defined.index()].then_some(defined)
    }
    /// What the condition at `cond` holding in `sense` says about the
    /// locals it compares: a refined class and node per local, read inside
    /// the region just entered, each on top of what an earlier conjunct
    /// left. The condition's shape is syntactic: a comparison, a negation,
    /// a conjunction under the true sense, a disjunction under the false
    /// sense, or a bare boolean local.
    fn refine(&mut self, cond: NodeIdx, sense: bool) {
        use sumi_syntax::BinaryOp::*;

        let tree = self.source.tree;
        let Some(expr) = ast::Expr::cast(tree, cond) else {
            return;
        };
        let node = self.source.peel(expr).node();
        if tree.has_error(node) {
            return;
        }
        match tree.kind(node) {
            NodeKind::PrefixExpr => {
                let operand = ast::PrefixExpr::cast(tree, node)
                    .unwrap()
                    .operand(tree)
                    .unwrap()
                    .node();
                let not = self
                    .source
                    .tokens(tree.first_token(node), tree.first_token(operand))
                    .eq([SyntaxKind::Bang]);
                if not {
                    self.refine(operand, !sense);
                }
            }
            NodeKind::BinaryExpr => {
                let binary = ast::BinaryExpr::cast(tree, node).unwrap();
                let lhs = binary.lhs(tree).unwrap().node();
                let rhs = binary.rhs(tree).unwrap().node();
                let op = self.binary_op(node);
                match op {
                    And if sense => {
                        self.refine(lhs, sense);
                        self.refine(rhs, sense);
                    }
                    Or if !sense => {
                        self.refine(lhs, sense);
                        self.refine(rhs, sense);
                    }
                    Lt | Le | Gt | Ge | Eq | Ne => {
                        let op = eager(op).expect("a comparison is eager");
                        for (side, other, local_is_lhs) in [(lhs, rhs, true), (rhs, lhs, false)] {
                            if let (Some(local), Some(other)) = (self.read(side), self.typed(other))
                            {
                                let inputs = [self.current(local), other];
                                let read = self.place(
                                    Op::Refine {
                                        op,
                                        local_is_lhs,
                                        sense,
                                    },
                                    &inputs,
                                    self.source.range(node),
                                    None,
                                );
                                self.refinements.push((local, read));
                            }
                        }
                    }
                    _ => {}
                }
            }
            NodeKind::NameRef => {
                if let Some(local) = self.read(node) {
                    let inputs = [self.current(local)];
                    let read =
                        self.place(Op::Exactly(sense), &inputs, self.source.range(node), None);
                    self.refinements.push((local, read));
                }
            }
            _ => {}
        }
    }
    /// The condition of the `if` at `node` is walked: open a context and a
    /// region per branch and schedule the branches inside them, and the
    /// `if` after them.
    fn branches(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let branch = ast::IfExpr::cast(tree, node).unwrap();
        let cond = branch.condition(tree).unwrap().node();
        let then_node = branch.then_branch(tree).unwrap().node();
        let else_node = branch.else_branch(tree).map(|e| e.node());
        let parent = self.context();
        let cond_node = self.node_of(cond);
        let then = {
            let context = self.context_at(then_node, Op::Then, cond_node, parent);
            self.graph.open(context)
        };
        let else_ = else_node.map(|else_node| {
            let context = self.context_at(else_node, Op::Else, cond_node, parent);
            self.graph.open(context)
        });
        work.push(Work::Join { node, then, else_ });
        // The else branch is entered last. Without an else nothing enters
        // the false sense, so nothing is narrowed for it.
        if let (Some(else_node), Some(region)) = (else_node, else_) {
            work.push(Work::Pop {
                region,
                root: else_node,
            });
            work.push(Work::Enter(else_node));
            work.push(Work::Push {
                region,
                guard: (cond, false),
            });
        }
        work.push(Work::Pop {
            region: then,
            root: then_node,
        });
        work.push(Work::Enter(then_node));
        work.push(Work::Push {
            region: then,
            guard: (cond, true),
        });
    }
    /// The left operand of the lazy operator at `node` is walked: open the
    /// context and region the right one runs in and schedule it inside,
    /// and the operator after it.
    fn rhs(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let binary = ast::BinaryExpr::cast(tree, node).unwrap();
        let lhs = binary.lhs(tree).unwrap().node();
        let rhs = binary.rhs(tree).unwrap().node();
        let and = self.binary_op(node) == sumi_syntax::BinaryOp::And;
        let parent = self.context();
        let op = if and { Op::Then } else { Op::Else };
        let lhs_node = self.node_of(lhs);
        let context = self.context_at(rhs, op, lhs_node, parent);
        let region = self.graph.open(context);
        work.push(Work::Lazy { node, rhs: region });
        work.push(Work::Pop { region, root: rhs });
        work.push(Work::Enter(rhs));
        work.push(Work::Push {
            region,
            guard: (lhs, and),
        });
    }
    /// The context at `node` requires the value `actual` to be `expected`,
    /// which `declared` may have set. Recorded for the flows to join into
    /// the evidence, and for the verdict pass.
    fn require(
        &mut self,
        node: NodeIdx,
        actual: NodeId,
        expected: Expected,
        declared: Option<NodeIdx>,
    ) {
        if expected == Expected::Peer(actual) {
            return;
        }
        self.demand(node, actual, DemandKind::Type { expected, declared });
    }
    fn demand(&mut self, node: NodeIdx, actual: NodeId, kind: DemandKind) {
        self.lowered.demands.push(Demand {
            owner: self.owner,
            node,
            actual,
            kind,
        });
    }
    /// Refuse the construct at `node`, which leaves a hole.
    fn unsupported(&mut self, node: NodeIdx) {
        self.source.error(
            node,
            codes::UNSUPPORTED,
            "construct is not supported by scalar checking",
            None,
        );
        self.hole(node);
        self.failed = true;
    }
    fn enter(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let kind = tree.kind(node);
        let error = tree.has_error(node);
        match kind {
            NodeKind::LetStmt => {
                let binding = ast::LetStmt::cast(tree, node).unwrap();
                let mutable = self
                    .source
                    .tokens(
                        tree.first_token(node),
                        binding
                            .name(tree)
                            .map_or(tree.end_token(node), |n| tree.first_token(n.node())),
                    )
                    .eq([SyntaxKind::LetKw, SyntaxKind::MutKw]);
                if error || mutable {
                    if mutable && !error {
                        self.unsupported(node);
                    }
                    if let Some((name, name_node)) = self.source.name(binding.name(tree)) {
                        let hole =
                            self.push(node, Op::Hole, &[], Some(self.source.range(name_node)));
                        self.bind(name, hole);
                    }
                    self.failed = true;
                    return;
                }
            }
            NodeKind::Block => {
                self.failed |= error;
                self.open_scope();
            }
            _ if error => {
                self.hole(node);
                self.failed = true;
                return;
            }
            NodeKind::IfExpr => {
                let branch = ast::IfExpr::cast(tree, node).unwrap();
                let cond = branch.condition(tree).unwrap().node();
                work.push(Work::Branches(node));
                work.push(Work::Enter(cond));
                return;
            }
            NodeKind::BinaryExpr
                if matches!(
                    self.binary_op(node),
                    sumi_syntax::BinaryOp::And | sumi_syntax::BinaryOp::Or
                ) =>
            {
                let binary = ast::BinaryExpr::cast(tree, node).unwrap();
                let lhs = binary.lhs(tree).unwrap().node();
                work.push(Work::Rhs(node));
                work.push(Work::Enter(lhs));
                return;
            }
            NodeKind::PrefixExpr => {
                let operand = ast::PrefixExpr::cast(tree, node)
                    .unwrap()
                    .operand(tree)
                    .unwrap();
                let neg = self
                    .source
                    .tokens(tree.first_token(node), tree.first_token(operand.node()))
                    .eq([SyntaxKind::Minus]);
                let peeled = self.source.peel(operand);
                if neg
                    && tree.kind(peeled.node()) == NodeKind::LiteralExpr
                    && self
                        .source
                        .parsed
                        .lexed()
                        .kind(tree.first_token(peeled.node()))
                        == SyntaxKind::IntLiteral
                {
                    if self.integer(node, peeled.node(), true).is_none() {
                        self.failed = true;
                    }
                    return;
                }
            }
            NodeKind::CallExpr => {
                let call = ast::CallExpr::cast(tree, node).unwrap();
                let callee = self.source.peel(call.callee(tree).unwrap()).node();
                let target = if tree.kind(callee) == NodeKind::NameRef {
                    self.target(callee)
                } else {
                    self.unsupported(callee);
                    None
                };
                let list = call.arg_list(tree).unwrap();
                work.push(Work::Call(node, target));
                enter_each(
                    work,
                    tree.children(list.node())
                        .filter_map(|child| ast::Expr::cast(tree, child))
                        .map(|arg| arg.node()),
                );
                return;
            }
            _ => {}
        }
        match kind {
            NodeKind::Block
            | NodeKind::LetStmt
            | NodeKind::DiscardStmt
            | NodeKind::PrefixExpr
            | NodeKind::BinaryExpr
            | NodeKind::ParenExpr
            | NodeKind::IfExpr => {
                work.push(Work::Finish(node));
                enter_each(
                    work,
                    tree.children(node).filter(|&child| {
                        !matches!(tree.kind(child), NodeKind::Name | NodeKind::TypeRef)
                    }),
                );
            }
            NodeKind::NameRef | NodeKind::LiteralExpr => {
                if self.finish(node).is_none() {
                    self.failed = true;
                }
            }
            _ => self.unsupported(node),
        }
    }
    fn target(&mut self, node: NodeIdx) -> Option<FunctionId> {
        let name = self.source.text(node);
        if let Some(local) = self.lookup(name) {
            // A binding that failed is reported once, where it failed.
            if self.lowered.typed[local.index()] {
                self.source.error(
                    node,
                    codes::NOT_CALLABLE,
                    format!("local `{name}` is not callable"),
                    self.graph
                        .node(local)
                        .name
                        .map(|range| (range, "declared here")),
                );
            }
            return None;
        }
        match self.names.get(name) {
            Some(Named::Function(target)) => Some(*target),
            Some(Named::Ambiguous(_)) => None,
            None => {
                self.source.error(
                    node,
                    codes::UNKNOWN_NAME,
                    format!("unknown function `{name}`"),
                    None,
                );
                None
            }
        }
    }
    /// The literal's value, negated when a `-` prefix is folded into it.
    /// `None` for a malformed literal, which the lexer already reported.
    fn integer(&mut self, origin: NodeIdx, literal: NodeIdx, negative: bool) -> Option<NodeId> {
        let raw = self.source.tree.first_token(literal);
        if self
            .source
            .parsed
            .lexed()
            .flags(raw)
            .contains(TokenFlags::MALFORMED_NUMBER)
        {
            self.hole(origin);
            return None;
        }
        let magnitude: Int = self
            .source
            .text(literal)
            .parse()
            .expect("a well-formed literal is a run of digits");
        let value = if negative { -&magnitude } else { magnitude };
        Some(self.push(origin, Op::Int(value), &[], None))
    }
    fn finish(&mut self, node: NodeIdx) -> Option<()> {
        let tree = self.source.tree;
        match tree.kind(node) {
            NodeKind::Block => {
                self.close_scope();
                // Only the last child can be the tail. A statement built
                // itself; an expression statement must be unit; a child
                // that built nothing is a hole where it stood.
                let mut tail = None;
                let mut valid = !tree.has_error(node);
                let mut children = tree.children(node).peekable();
                while let Some(child) = children.next() {
                    let expression = ast::Expr::cast(tree, child).is_some();
                    if children.peek().is_none() && expression {
                        tail = Some(child);
                        break;
                    }
                    match self.typed(child) {
                        Some(value) if expression => {
                            self.demand(child, value, DemandKind::Unused);
                        }
                        Some(_) => {}
                        None => {
                            self.node_of(child);
                            valid = false;
                        }
                    }
                }
                // A block is its tail, or unit without one, whether or not
                // the rest of it built. A block the parser could not repair
                // may have lost its tail to recovery, so without one it is
                // a hole.
                let damaged = tree.has_error(node);
                match tail {
                    Some(tail) => {
                        let value = self.node_of(tail);
                        self.nodes_of[node.to_usize()] = Some(value);
                    }
                    None if damaged => {
                        self.hole(node);
                    }
                    None => {
                        let context = self.context();
                        self.push(node, Op::Unit, &[context], None);
                    }
                }
                if !valid || damaged {
                    return None;
                }
                self.typed(node)?;
            }
            NodeKind::LetStmt => {
                let binding = ast::LetStmt::cast(tree, node).unwrap();
                let initializer_node = binding.initializer(tree).unwrap().node();
                let initializer = self.typed(initializer_node);
                let value = self.node_of(initializer_node);
                let name = self.source.name(binding.name(tree));
                // An annotated binding has its declared type whatever its
                // initializer turns out to be; the initializer is held to it.
                // An annotation naming no type leaves a hole over it.
                let annotation = binding.type_ref(tree);
                let declared = annotation.and_then(|annotation| {
                    let ty = self.source.ty(annotation)?;
                    Some((ty, self.source.range(annotation.node())))
                });
                let op = match (annotation, declared) {
                    (Some(_), None) => Op::Hole,
                    _ => Op::Copy { declared },
                };
                let copy = self.push(
                    node,
                    op,
                    &[value],
                    name.map(|(_, node)| self.source.range(node)),
                );
                let (name, _) = name?;
                if let (Some(annotation), Some((ty, _)), Some(initializer)) =
                    (annotation, declared, initializer)
                {
                    self.require(
                        initializer_node,
                        initializer,
                        Expected::Ty(ty),
                        Some(annotation.node()),
                    );
                }
                self.bind(name, copy);
                self.lowered.typed[copy.index()].then_some(())?;
            }
            NodeKind::DiscardStmt => {
                let value = ast::DiscardStmt::cast(tree, node)
                    .unwrap()
                    .value(tree)
                    .unwrap()
                    .node();
                // The statement is its value, whether or not it built.
                let discarded = self.node_of(value);
                self.nodes_of[node.to_usize()] = Some(discarded);
                self.typed(value)?;
            }
            NodeKind::NameRef => {
                let name = self.source.text(node);
                match self.lookup(name) {
                    // A binding without a value the typing follows is still
                    // what the name reads.
                    Some(defined) => {
                        let read = self.current(defined);
                        self.nodes_of[node.to_usize()] = Some(read);
                        self.lowered.typed[read.index()].then_some(())?;
                    }
                    None => {
                        if self.names.contains_key(name) {
                            self.unsupported(node);
                        } else {
                            self.source.error(
                                node,
                                codes::UNKNOWN_NAME,
                                format!("unknown name `{name}`"),
                                None,
                            );
                            self.hole(node);
                        }
                        return None;
                    }
                }
            }
            NodeKind::LiteralExpr => {
                match self.source.parsed.lexed().kind(tree.first_token(node)) {
                    SyntaxKind::IntLiteral => {
                        self.integer(node, node, false)?;
                    }
                    _ if matches!(self.source.text(node), "true" | "false") => {
                        let value = self.source.text(node) == "true";
                        self.push(node, Op::Bool(value), &[], None);
                    }
                    _ => {
                        self.unsupported(node);
                        return None;
                    }
                }
            }
            NodeKind::ParenExpr => {
                let inner = ast::ParenExpr::cast(tree, node)
                    .unwrap()
                    .inner(tree)
                    .unwrap()
                    .node();
                let value = self.node_of(inner);
                self.nodes_of[node.to_usize()] = Some(value);
                self.typed(inner)?;
            }
            NodeKind::PrefixExpr => {
                let operand = ast::PrefixExpr::cast(tree, node)
                    .unwrap()
                    .operand(tree)
                    .unwrap()
                    .node();
                let neg = self
                    .source
                    .tokens(tree.first_token(node), tree.first_token(operand))
                    .eq([SyntaxKind::Minus]);
                let operand_node = self.node_of(operand);
                self.push(
                    node,
                    if neg { Op::Neg } else { Op::Not },
                    &[operand_node],
                    None,
                );
                let value = self.typed(operand)?;
                let ty = if neg { Ty::Int } else { Ty::Bool };
                self.require(operand, value, Expected::Ty(ty), None);
            }
            NodeKind::BinaryExpr => {
                use sumi_syntax::BinaryOp::*;

                let binary = ast::BinaryExpr::cast(tree, node).unwrap();
                let lhs_node = binary.lhs(tree).unwrap().node();
                let rhs_node = binary.rhs(tree).unwrap().node();
                let op = self.binary_op(node);
                let lhs = self.typed(lhs_node);
                let rhs = self.typed(rhs_node);
                let lhs_graph = self.node_of(lhs_node);
                let rhs_graph = self.node_of(rhs_node);
                let eager = eager(op).expect("a lazy operator finishes as its own item");
                self.push(node, Op::Binary(eager), &[lhs_graph, rhs_graph], None);
                // `==` and `!=` compare like with like: whichever operand
                // exists sets the other's expectation.
                let operand = match op {
                    Eq | Ne => lhs.or(rhs).map(Expected::Peer),
                    _ => Some(Expected::Ty(Ty::Int)),
                };
                if let Some(operand) = operand {
                    for (child, value) in [(lhs_node, lhs), (rhs_node, rhs)] {
                        if let Some(value) = value {
                            self.require(child, value, operand, None);
                        }
                    }
                    if matches!(op, Eq | Ne)
                        && let Some(operand) = lhs.or(rhs)
                    {
                        self.demand(node, operand, DemandKind::Comparable);
                    }
                }
                lhs?;
                rhs?;
                if matches!(op, Div | Rem) {
                    self.lowered.obligations.push(Obligation {
                        owner: self.owner,
                        node,
                        divisor: rhs_graph,
                        context: self.context(),
                    });
                }
            }
            _ => unreachable!("scheduled supported node"),
        }
        Some(())
    }
    /// The lazy operator at `node`, whose right operand is the region
    /// `rhs`.
    fn lazy(&mut self, node: NodeIdx, rhs: RegionId) -> Option<()> {
        let tree = self.source.tree;
        let binary = ast::BinaryExpr::cast(tree, node).unwrap();
        let lhs_node = binary.lhs(tree).unwrap().node();
        let rhs_node = binary.rhs(tree).unwrap().node();
        let and = self.binary_op(node) == sumi_syntax::BinaryOp::And;
        let lhs = self.typed(lhs_node);
        let rhs_value = self.typed(rhs_node);
        let lhs_graph = self.node_of(lhs_node);
        let op = if and { Op::And { rhs } } else { Op::Or { rhs } };
        self.push(node, op, &[lhs_graph], None);
        for (child, value) in [(lhs_node, lhs), (rhs_node, rhs_value)] {
            if let Some(value) = value {
                self.require(child, value, Expected::Ty(Ty::Bool), None);
            }
        }
        lhs?;
        rhs_value?;
        Some(())
    }
    /// The `if` at `node`, whose branches are the regions `then` and
    /// `else_`.
    fn join(&mut self, node: NodeIdx, then: RegionId, else_: Option<RegionId>) -> Option<()> {
        let tree = self.source.tree;
        let branch = ast::IfExpr::cast(tree, node).unwrap();
        let condition_node = branch.condition(tree).unwrap().node();
        let condition = self.typed(condition_node);
        let then_node = branch.then_branch(tree).unwrap().node();
        let then_branch = self.typed(then_node);
        let else_node = branch.else_branch(tree).map(|e| e.node());
        let else_branch = else_node.and_then(|n| self.typed(n));
        let cond_graph = self.node_of(condition_node);
        let join = self.push(node, Op::Join { then, else_ }, &[cond_graph], None);
        if let Some(condition) = condition {
            self.require(condition_node, condition, Expected::Ty(Ty::Bool), None);
        }
        let then_branch = then_branch?;
        match else_node {
            // Without an else, the then branch is unit, and so is the `if`.
            None => {
                self.require(then_node, then_branch, Expected::Ty(Ty::Unit), None);
                condition?;
            }
            // Each branch decides the `if` and learns nothing from the
            // other, so branches that disagree leave the `if` undetermined,
            // conflicted on its own class, and keep their own types. The
            // verdict pass reports it there.
            Some(_) => {
                let branches = [then_branch, else_branch?];
                condition?;
                self.demand(node, join, DemandKind::Agree { branches });
            }
        }
        Some(())
    }
    /// The call at `node`, whose arguments are walked, to `target` when
    /// its callee names a function. A call is a call when its callee has
    /// parameters to hold it to and every argument is there; otherwise it
    /// never happens, and is a hole over what it walked: its callee, when
    /// that built, and its arguments.
    fn call(&mut self, node: NodeIdx, target: Option<FunctionId>) -> Option<()> {
        let context = self.context();
        let tree = self.source.tree;
        let call = ast::CallExpr::cast(tree, node).unwrap();
        let list = call.arg_list(tree).unwrap();
        // The callee that holds the call: one with a whole parameter list.
        let callee: Option<(FunctionId, &Header, &[Ty])> = target.and_then(|target| {
            let function = &self.headers[target.index()];
            Some((target, function, function.params.as_deref()?))
        });
        if let Some((target, ..)) = callee {
            // The callee is reached, whole call or not: what it does is
            // checked on the strength of any call to it.
            self.lowered.entered.push((context, target));
        }
        // Every argument that exists is held to its parameter, arity aside;
        // its node and its syntax are kept in case the call is whole.
        let mut inputs = std::mem::take(&mut self.inputs);
        inputs.clear();
        if target.is_none() {
            let callee = self.source.peel(call.callee(tree).unwrap()).node();
            inputs.extend(self.nodes_of[callee.to_usize()]);
        }
        let written = run(self.lowered.arguments.len());
        let mut complete = true;
        let mut count = 0;
        for (index, arg) in list.args(tree).enumerate() {
            let syntax = arg.node();
            count += 1;
            inputs.push(self.node_of(syntax));
            self.lowered.arguments.push(syntax);
            match (self.typed(syntax), callee) {
                (Some(value), Some((_, function, params))) => {
                    if let Some(&expected) = params.get(index) {
                        self.require(syntax, value, Expected::Ty(expected), Some(function.item));
                    }
                }
                (None, _) => complete = false,
                _ => {}
            }
        }
        if let Some((_, function, params)) = callee
            && count != params.len()
        {
            self.source.error(
                node,
                codes::ARITY,
                format!("expected {} arguments, found {count}", params.len()),
                Some((self.source.range(function.item), "declared here")),
            );
        }
        let whole = callee.filter(|(_, _, params)| count == params.len() && complete);
        let op = whole.map_or(Op::Hole, |(target, ..)| Op::Call(target));
        let id = self.push(node, op, &inputs, None);
        self.inputs = inputs;
        let Some((target, function, _)) = whole else {
            self.lowered.arguments.truncate(written as usize);
            return None;
        };
        self.lowered.calls.push(Call {
            node: id,
            caller: FunctionId::new(self.owner as usize),
            callee: target,
            context,
            arguments: written..run(self.lowered.arguments.len()),
        });
        // The call has a value when its callee has a result.
        (!matches!(function.result, HeaderResult::None)).then_some(())
    }
}
