//! Function bodies to graph nodes, one recursive walk over the syntax: scopes and locals, versions
//! of mutable locals, regions and their contexts, and holes where the syntax or a name failed. The
//! parser bounds nesting, so the walk's depth is bounded with it.

use std::collections::{HashMap, HashSet};

use rustc_hash::FxBuildHasher;
use sumi_frontend::Fix;
use sumi_graph::{
    ArithOp, Arms, BinaryOp, Carried, Case, CmpOp, Decl, DeclId, FunctionId, Graph, GraphBuilder,
    Int, NodeId, Op, References, RegionId, Ty,
};
use sumi_lexer::{RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    AssignOp, Literal, NodeIdx, NodeKind, PrefixOp,
    ast::{self, AstNode, View},
};
use sumi_text::{TextEdit, TextRange, TextSize};

use super::declare::{Declarations, HeaderResult, Named, Order, RESULT, SELF, unbounded_calls};
use super::source::{NameMap, Source};
use super::versions::{Refinement, RegionState, Versions};
use super::{Call, Fallthrough, Lowered, Obligation, Statement, diagnostic, join};
use crate::codes;
use crate::spans::{Spans, SpansBuilder};
use crate::typing::{Checked, Checker, Read, Types};
use crate::{Binding, BindingId, BindingKind, Occurrence, Symbol};

/// Every function's body with its types, the instances of the generic ones among them. The items
/// are built in `Order`; a body names the instances it calls, and each is built in its turn.
pub(crate) fn lower<'s>(
    source: &mut Source<'s>,
    declared: Declarations<'s>,
    graph: GraphBuilder,
) -> (Graph, Spans, Lowered, Declarations<'s>, Checked) {
    let order = Order::new(source, &declared);
    let items = declared.items.len();
    let mut builder = Builder::new(source, declared, graph, order);
    for group in 0..builder.order.groups() {
        let is_recursive = builder.order.is_recursive(group);
        for member in 0..builder.order.members(group).len() {
            builder.build(builder.order.members(group)[member] as usize, !is_recursive);
        }
        if is_recursive {
            builder.checker().settle(group);
        }
    }
    let generic_calls = std::mem::take(&mut builder.generic_calls);
    unbounded_calls(builder.source, &mut builder.declared, &generic_calls);
    let mut index = items;
    while index < builder.declared.headers.len() {
        builder.build(index, true);
        index += 1;
    }
    builder.source.scope.clear();
    builder.source.is_muted = false;
    let checked = builder
        .types
        .finish(builder.source, builder.declared.headers.len());
    let fields = builder.source.take_fields();
    builder.graph.declare(fields.into_iter().map(Decl::new));
    builder
        .graph
        .set_unions(builder.source.unions.borrow().clone());
    let graph = builder.graph.finish();
    let spans = builder.spans.finish(&graph);
    let declared = builder.declared;
    let mut lowered = builder.lowered;
    lowered.calls.sort_by_key(|call| call.caller.index());
    lowered.references.append(&mut source.references);
    lowered
        .references
        .sort_unstable_by_key(|occurrence| occurrence.range.start());
    lowered.references.dedup();
    lowered
        .unresolved
        .sort_unstable_by_key(|range| range.start());
    (graph, spans, lowered, declared, checked)
}

/// The syntax's operator in the graph's vocabulary, which has no lazy operator.
fn eager(op: sumi_syntax::BinaryOp) -> Option<BinaryOp> {
    use sumi_syntax::BinaryOp as S;
    Some(match op {
        S::Or | S::And => return None,
        S::Cmp(op) => BinaryOp::Cmp(cmp(op)),
        S::Arith(op) => BinaryOp::Arith(arith(op)),
    })
}

fn cmp(op: sumi_syntax::CmpOp) -> CmpOp {
    use sumi_syntax::CmpOp as S;
    match op {
        S::Eq => CmpOp::Eq,
        S::Ne => CmpOp::Ne,
        S::Lt => CmpOp::Lt,
        S::Le => CmpOp::Le,
        S::Gt => CmpOp::Gt,
        S::Ge => CmpOp::Ge,
    }
}

fn arith(op: sumi_syntax::ArithOp) -> ArithOp {
    use sumi_syntax::ArithOp as S;
    match op {
        S::Add => ArithOp::Add,
        S::Sub => ArithOp::Sub,
        S::Mul => ArithOp::Mul,
        S::Div => ArithOp::Div,
        S::Rem => ArithOp::Rem,
    }
}

/// How a message says a value decides nothing yet.
fn pending_text(value: Decides) -> &'static str {
    match value {
        Decides::Pending => " while a result of this recursion is still inferred",
        _ => "",
    }
}

/// What a call names.
#[derive(Clone, Copy)]
enum Target {
    Function(FunctionId),
    Type(DeclId),
    /// `Self`: the type an `impl` is of, at its type parameters.
    Instance(DeclId),
    /// Reported where it was resolved, or ambiguous.
    Unknown,
}

/// What a call names once its type argument list is read.
#[derive(Clone, Copy)]
enum Applied {
    Function(FunctionId),
    Type(DeclId),
    /// A generic function named with no type arguments, which its arguments decide.
    Inferred(FunctionId),
    /// A generic type named with no type arguments, which its fields' values decide.
    InferredType(DeclId),
    Unknown,
}

/// What a value decides of a type parameter read from its type.
#[derive(Clone, Copy)]
enum Decides {
    Ty(Ty),
    /// Nothing, as what it failed at is reported elsewhere.
    Failed,
    /// Nothing until a result its recursion infers has settled.
    Pending,
    /// Nothing: it yields no value.
    Nothing,
}

/// Whether what is no place has a place's shape, a name and fields, so its name is resolved.
struct IsShaped(bool);

/// The records a place's fields are of, outermost first: each one's value, its type, and the
/// field's position in it.
type Path = Vec<(NodeId, DeclId, usize)>;

/// A place: a mutable local and the fields under it, outermost first, each with its name.
struct Place<'s> {
    local: LocalId,
    root: NodeIdx,
    fields: Vec<(&'s str, NodeIdx)>,
}

impl Place<'_> {
    /// Whether a write to one is a write to the other, or to a part of it.
    fn overlaps(&self, other: &Self) -> bool {
        let shared = self.fields.iter().zip(&other.fields);
        self.local == other.local && shared.into_iter().all(|(a, b)| a.0 == b.0)
    }
}

/// Where a call is written: the whole of it, the name it calls by, and the type arguments it
/// writes after that.
#[derive(Clone, Copy)]
pub(super) struct Site {
    pub node: NodeIdx,
    pub name: Option<NodeIdx>,
    pub list: Option<ast::TypeArgList>,
}

/// A call from a generic function's own body to a generic function, at the type arguments it
/// names or its arguments decide.
pub(super) struct GenericCall {
    pub caller: FunctionId,
    pub callee: FunctionId,
    pub site: Site,
    pub args: Vec<Ty>,
}

/// A call's arguments in order, a method's receiver first: each with its syntax, which a
/// receiver has none of, and its value.
type Args = Vec<(Option<ast::Arg>, Value)>;

/// The arguments a call writes `mut`, and a receiver its method changes: each by position, with
/// the place it is when it is one.
type Lent<'s> = Vec<(usize, Option<Place<'s>>)>;

/// A local's index in the body's `locals`, and in its versions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct LocalId(u32);

impl LocalId {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("local count fits u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

struct Local<'s> {
    name: &'s str,
    binding: BindingId,
    declaration: NodeId,
    completes: bool,
    /// A name beginning with `_` counts as read from its declaration.
    is_read: bool,
    is_assigned: bool,
}

/// A `let` binds after its initializer, so the initializer reads any outer binding of the name.
type Scope<'s> = NameMap<'s, LocalId>;

/// A whole node that lowers its left operand before anything of its own.
enum Link {
    /// `&&` when the flag is set, else `||`.
    Lazy(ast::BinaryExpr, bool),
    Eager(ast::BinaryExpr, BinaryOp),
    Field(ast::FieldExpr),
    /// A method call on a receiver that is no place: a place is read by the call itself.
    Method(ast::MethodCallExpr),
}

/// What holds where a chain of one lazy operator goes on to another operand: the refinements of
/// every operand before `last`, built outside any operand's region.
struct Guard {
    /// `&&`, whose next operand runs where the chain so far is true; `||`, where it is false.
    is_and: bool,
    refinements: Vec<Refinement>,
    last: NodeIdx,
}

/// An arm, its case, and the name and type its pattern binds.
type ArmCase = (ast::MatchArm, Case, Option<(NodeIdx, Ty)>);

/// What lowering a statement or expression yields: its node, where it is read, and what it does
/// to the control around it. A node the syntax lost is a hole, which is not valid.
#[derive(Clone, Copy)]
struct Value {
    node: NodeId,
    /// The syntax's own range.
    range: TextRange,
    /// Where the value is read: a block's innermost tail, else the syntax itself.
    at: TextRange,
    control: Option<NodeId>,
    /// Whether it never completes normally: it or a part of it returns.
    completes: bool,
    /// Whether the node has a type the typing follows.
    is_valid: bool,
    /// Whether the innermost tail is a plain value: valid and completing nothing.
    has_scalar_tail: bool,
}

impl Value {
    fn input(self) -> (NodeId, TextRange) {
        (self.node, self.at)
    }
}

struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    declared: Declarations<'s>,
    graph: GraphBuilder,
    spans: SpansBuilder,
    lowered: Lowered,
    order: Order,
    types: Types,
    generic_calls: Vec<GenericCall>,
    /// By the name a generic item's own body leaves without type arguments, those it decided
    /// there, which its instances take at their own.
    decided: HashMap<NodeIdx, Vec<Ty>, FxBuildHasher>,
    /// By syntax node, the graph node it built, which refinement reads by the condition's syntax.
    nodes_of: Vec<Option<NodeId>>,
    /// By syntax node, whether it completes; a condition's operand is read by its syntax.
    bottoms: Vec<bool>,
    /// The local and underlying version read by each name reference.
    reads_of: Vec<Option<(LocalId, NodeId)>>,
    owner: u32,
    has_failed: bool,
    /// Open regions with their contexts, innermost last.
    regions: Vec<(RegionId, NodeId)>,
    /// The first `depth` scopes are open, innermost last, each ending where its block does.
    scopes: Vec<Scope<'s>>,
    scope_ends: Vec<TextSize>,
    scope_mutables: Vec<usize>,
    depth: usize,
    locals: Vec<Local<'s>>,
    versions: Versions,
    /// The mutable locals of the open scopes, in declaration order.
    mutable_locals: Vec<LocalId>,
    returns: Vec<(NodeId, TextRange)>,
    /// The `mut` parameters of the function being built, whose values its every exit returns.
    outs: Vec<LocalId>,
    /// Scratch a version merge fills, kept across merges.
    merge_values: Vec<(NodeId, NodeId)>,
    merge_inputs: Vec<(NodeId, TextRange)>,
    merge_contexts: Vec<NodeId>,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
        source: &'a mut Source<'s>,
        declared: Declarations<'s>,
        graph: GraphBuilder,
        order: Order,
    ) -> Self {
        let nodes = source.tree.len();
        let functions = declared.headers.len();
        Self {
            source,
            types: Types::new(declared.items.len()),
            declared,
            graph,
            spans: SpansBuilder::new(nodes),
            order,
            generic_calls: Vec::new(),
            decided: HashMap::default(),
            lowered: Lowered {
                built: vec![false; functions],
                typed: Vec::with_capacity(nodes),
                calls: Vec::new(),
                called: Vec::new(),
                entered: Vec::new(),
                obligations: Vec::new(),
                fallthroughs: vec![None; functions],
                exits: vec![Vec::new(); functions],
                bindings: Vec::new(),
                references: Vec::new(),
                unresolved: Vec::new(),
                statements: Vec::new(),
                field_reads: Vec::new(),
            },
            nodes_of: vec![None; nodes],
            bottoms: vec![false; nodes],
            reads_of: vec![None; nodes],
            owner: 0,
            has_failed: false,
            regions: Vec::new(),
            scopes: Vec::new(),
            scope_ends: Vec::new(),
            scope_mutables: Vec::new(),
            depth: 0,
            locals: Vec::new(),
            versions: Versions::new(),
            mutable_locals: Vec::new(),
            returns: Vec::new(),
            outs: Vec::new(),
            merge_values: Vec::new(),
            merge_inputs: Vec::new(),
            merge_contexts: Vec::new(),
        }
    }

    /// The typing's reading of what is built so far.
    fn checker(&mut self) -> Checker<'_, 's> {
        Checker {
            types: &mut self.types,
            source: self.source,
            graph: &self.graph,
            spans: &self.spans,
            lowered: &self.lowered,
            declared: &self.declared,
            order: &self.order,
        }
    }

    /// What `value` decides of a type parameter read from its type, as the typing has it where
    /// the body has got to.
    fn decides(&mut self, value: &Value) -> Decides {
        if !value.is_valid {
            return Decides::Failed;
        }
        self.decides_at(value.node)
    }

    /// As [`decides`](Self::decides), of a node the typing follows.
    fn decides_at(&mut self, node: NodeId) -> Decides {
        let owner = FunctionId::new(self.owner as usize);
        match self.checker().read(owner, node) {
            Read::Ty(ty) => Decides::Ty(ty),
            Read::Unknown if self.types.is_pending() => Decides::Pending,
            Read::Unknown => Decides::Failed,
            Read::Unclaimed => Decides::Nothing,
        }
    }

    /// Keeps the type arguments the name at `at` decided, for the instances of a generic item
    /// whose own body this is.
    fn decide(&mut self, at: NodeIdx, args: &[Ty]) {
        if !self.declared.items[self.owner as usize].params.is_empty() {
            self.decided.insert(at, args.to_vec());
        }
    }

    /// In an instance's body, the type arguments its item's own body decided for the name at `at`,
    /// at the instance's own; none where that body decided none, which it reported.
    fn decided(&mut self, at: NodeIdx) -> Option<Vec<Ty>> {
        let decided = self.decided.get(&at)?;
        let item = self.declared.headers[self.owner as usize].generic;
        let params = &self.declared.type_args[item.index()];
        let args = &self.declared.type_args[self.owner as usize];
        let range = self.source.range(at);
        let own = decided.iter();
        own.map(|&ty| self.source.substitute(ty, params, args, range))
            .collect()
    }

    /// Builds the body of `owner` beside the walk of its types, which reports and settles it when
    /// `is_final`.
    fn build(&mut self, owner: usize, is_final: bool) {
        self.owner = u32::try_from(owner).expect("function count fits u32");
        self.has_failed = false;
        self.depth = 0;
        self.regions.clear();
        self.locals.clear();
        self.versions.clear();
        self.mutable_locals.clear();
        self.outs.clear();
        if self.lowered.built.len() <= owner {
            self.lowered.built.resize(owner + 1, false);
            self.lowered.fallthroughs.resize(owner + 1, None);
            self.lowered.exits.resize(owner + 1, Vec::new());
        }
        let header = self.declared.headers[owner];
        let item_node = header.item;
        let tree = self.source.tree;
        let generic = &self.declared.items[header.generic.index()];
        let item = generic.item;
        let type_args = &self.declared.type_args[owner];
        self.source.scope.clear();
        self.source.scope.extend(
            generic
                .params
                .iter()
                .copied()
                .zip(type_args.iter().copied()),
        );
        self.source
            .scope
            .extend(header.receiver.map(|ty| (SELF, ty)));
        self.source.is_muted = header.generic.index() != owner;
        if self.source.is_muted {
            // The item's syntax built another instance before this one.
            let syntax = item_node.to_usize()..item_node.to_usize() + tree.subtree_len(item_node);
            self.nodes_of[syntax.clone()].fill(None);
            self.bottoms[syntax.clone()].fill(false);
            self.reads_of[syntax].fill(None);
        }
        let root_node = item.body(tree).map(|body| body.node());
        let body_range = match root_node {
            Some(root) => TextRange::new(self.source.range(root).start(), self.scope_end(root)),
            None => {
                let end = tree.end_token(item_node);
                TextRange::new(self.source.lexed().boundary(end), self.start_after(end))
            }
        };
        self.open_scope(body_range.end());
        self.returns.clear();
        self.checker().open(FunctionId::new(owner), is_final);
        let run = self.graph.open_run(FunctionId::new(owner));
        let entry = self.push(item_node, Op::Entry, &[], None);
        for index in 0..self.declared.parameters[owner].len() {
            let param = self.declared.parameters[owner][index];
            let index = u32::try_from(index).expect("parameter count fits u32");
            let name = param.at;
            let ty = param.ty.filter(|_| !param.is_duplicate);
            let node = self.push(param.node, Op::Param { index, ty }, &[], name);
            self.has_failed |= ty.is_none();
            if let (Some((name, _)), Some(range)) = (param.name, name) {
                let kind = BindingKind::Param {
                    is_mutable: param.is_mut,
                };
                let local = self.bind(name, node, kind, range, body_range.start());
                if header.product.is_some() && param.out().is_some() {
                    self.outs.push(local);
                }
            } else {
                self.has_failed = true;
            }
        }
        let declared = header.result;
        self.has_failed |= self.graph.param_types(FunctionId::new(owner)).is_none()
            || matches!(declared, HeaderResult::None);
        let region = self.graph.open(entry);
        self.graph.enter(region);
        self.regions.push((region, entry));
        let body = match root_node {
            Some(root) => self.lower(root),
            None => self.hole_value(item_node),
        };
        // Where the body falls through, its value is one exit's.
        let body = match header.product {
            Some(product) if root_node.is_some() && body.is_valid && !body.completes => Value {
                node: self.exit(product, body.input()),
                has_scalar_tail: true,
                ..body
            },
            _ => body,
        };
        let control = body.control;
        let fallthrough = control.map(|control| {
            self.place(
                Op::Sequence,
                &[(control, body.at), body.input()],
                body.at,
                None,
            )
        });
        let completes = root_node.is_some() && body.completes;
        self.graph
            .close_with_control(region, body.node, !completes, control);
        self.spans.close(region, body.at);
        self.regions.pop();
        // A failed parameter does not erase a declared result; the body is still held to it. A
        // product's exits each hold their own result to it.
        let declared = declared.declared().filter(|_| header.product.is_none());
        let value = match (control.is_none() && self.returns.is_empty(), declared) {
            (true, Some((ty, node))) => {
                let copy = self.push(node, Op::Copy { declared: Some(ty) }, &[body.input()], None);
                self.annotate(copy, node);
                copy
            }
            (true, None) => body.node,
            (false, declared) => {
                let node = declared.map_or(item_node, |(_, node)| node);
                let mut outcomes = Vec::with_capacity(self.returns.len() + 1);
                outcomes.push((fallthrough.unwrap_or(body.node), body.at));
                outcomes.extend(self.returns.iter().copied());
                let result = self.push(
                    node,
                    Op::Result {
                        declared: declared.map(|(ty, _)| ty),
                    },
                    &outcomes,
                    None,
                );
                if let Some((_, annotation)) = declared {
                    self.annotate(result, annotation);
                }
                let completes = root_node.is_none_or(|_| body.completes);
                // The body's value is read at its tail; a tail that is no plain value leaves a
                // declared result read at the body as a whole.
                let fallthrough = if body.has_scalar_tail {
                    Some((body.node, body.at))
                } else if declared.is_some() && body.is_valid && !body.completes {
                    Some((body.node, body.range))
                } else {
                    None
                };
                if (declared.is_some() || completes)
                    && let Some((value, at)) = fallthrough
                {
                    self.lowered.fallthroughs[self.owner as usize] =
                        Some(Fallthrough { value, at });
                }
                if completes {
                    self.completes_input(result, 0);
                }
                result
            }
        };
        self.graph.close_run(run, region, value);
        let is_whole = !self.has_failed && root_node.is_some() && body.is_valid;
        self.lowered.built[owner] = is_whole;
        if is_final {
            self.checker().close(FunctionId::new(owner), value);
        }
        if is_whole && !self.source.is_muted {
            self.unused();
        }
    }

    /// Only after a whole build: a walk that stopped early leaves reads unresolved.
    fn unused(&mut self) {
        if self.locals.iter().all(|local| local.is_read) {
            return;
        }
        let taken: HashSet<&str, FxBuildHasher> =
            self.locals.iter().map(|local| local.name).collect();
        for (index, local) in self.locals.iter().enumerate() {
            // What a `mut` parameter is assigned, its caller reads.
            let is_out = local.is_assigned && self.outs.contains(&LocalId::new(index));
            // A receiver is what makes a function a method, read or not.
            if local.is_read || is_out || local.name == "self" {
                continue;
            }
            let declaration = self.graph.node(local.declaration);
            let at = self
                .spans
                .name(local.declaration)
                .expect("a bound local is named");
            let (kind, reads) = match (&declaration.op, local.is_assigned) {
                (Op::Param { .. }, _) => ("parameter", "is never read"),
                (Op::Narrow(_), _) => ("binding", "is never read"),
                (Op::LoopIndex, _) => ("loop index", "is never read"),
                (_, false) => ("local", "is never read"),
                (_, true) => ("local", "is assigned but never read"),
            };
            let renamed = format!("_{}", local.name);
            // Renaming onto a name already in use would capture its reads or duplicate it.
            let is_free = !local.is_assigned
                && !self.declared.names.contains_key(renamed.as_str())
                && !taken.contains(renamed.as_str());
            let mut diagnostic = diagnostic(
                at,
                codes::UNUSED_NAME,
                format!("{kind} `{}` {reads}", local.name),
                [],
            );
            diagnostic.fix = is_free.then(|| Fix {
                message: "prefix the name with `_`".into(),
                edit: TextEdit::new(TextRange::new(at.start(), at.start()), "_"),
            });
            self.source.diagnostics.push(diagnostic);
        }
    }

    fn push(
        &mut self,
        node: NodeIdx,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        name: Option<TextRange>,
    ) -> NodeId {
        self.push_over(node, op, inputs, References::None, name, &[])
    }

    /// `results` are those of the regions `op` holds.
    fn push_over(
        &mut self,
        node: NodeIdx,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        references: References<'_>,
        name: Option<TextRange>,
        results: &[NodeId],
    ) -> NodeId {
        let id = self.place_over(
            op,
            inputs,
            references,
            self.source.range(node),
            name,
            results,
        );
        self.nodes_of[node.to_usize()] = Some(id);
        id
    }

    /// Unlike `push`, records no syntax node as having built the node.
    fn place(
        &mut self,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        origin: TextRange,
        name: Option<TextRange>,
    ) -> NodeId {
        self.place_with(op, inputs, References::None, origin, name)
    }

    fn place_with(
        &mut self,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        references: References<'_>,
        origin: TextRange,
        name: Option<TextRange>,
    ) -> NodeId {
        self.place_over(op, inputs, references, origin, name, &[])
    }

    /// Each input is a node and where it is read.
    fn place_over(
        &mut self,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        references: References<'_>,
        origin: TextRange,
        name: Option<TextRange>,
        results: &[NodeId],
    ) -> NodeId {
        let is_typed = self.follows(&op, inputs, references, results);
        let id = self
            .graph
            .push(op, inputs.iter().map(|&(input, _)| input), references);
        self.spans
            .push(origin, name, inputs.iter().map(|&(_, read)| read));
        self.lowered.typed.push(is_typed);
        id
    }

    /// The type annotation `node`, the last pushed, is declared with.
    fn annotate(&mut self, node: NodeId, annotation: NodeIdx) {
        debug_assert!(!self.types.has_walked(node), "{node:?} is walked");
        self.spans.annotate(node, self.source.range(annotation));
    }

    fn completes_input(&mut self, node: NodeId, index: usize) {
        debug_assert!(!self.types.has_walked(node), "{node:?} is walked");
        self.graph.complete_input(node, index);
    }

    /// Whether a node of `op` over `inputs`, and over the regions with `results`, carries a value
    /// the typing follows.
    fn follows(
        &self,
        op: &Op,
        inputs: &[(NodeId, TextRange)],
        references: References<'_>,
        results: &[NodeId],
    ) -> bool {
        let typed = |node: NodeId| self.lowered.typed[node.index()];
        let declaration = || match references {
            References::Version(declaration) | References::Phi { declaration, .. } => declaration,
            _ => unreachable!("a version names its declaration"),
        };
        match *op {
            Op::Hole | Op::Unused => false,
            Op::Entry
            | Op::Arm(_)
            | Op::Return
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After
            | Op::Result { declared: Some(_) }
            | Op::Copy { declared: Some(_) } => true,
            Op::Loop { .. } | Op::LoopIndex => true,
            Op::Carry => typed(declaration()),
            Op::Result { declared: None } => inputs.iter().all(|&(input, _)| typed(input)),
            Op::Param { ty, .. } => ty.is_some(),
            // An operator's result has its type whatever its operands; a call has its callee's
            // whatever its arguments.
            Op::Neg | Op::Not | Op::Binary(_) | Op::And { .. } | Op::Or { .. } => true,
            Op::Call(function) => !matches!(
                self.declared.headers[function.index()].result,
                HeaderResult::None
            ),
            // A construction has its type whatever its fields.
            Op::Make(_) => true,
            Op::Assign => typed(declaration()) && typed(inputs[0].0),
            Op::Phi => typed(declaration()) && inputs.iter().all(|&(input, _)| typed(input)),
            Op::Switch { .. } => typed(inputs[0].0) && results.iter().all(|&result| typed(result)),
            _ => inputs.iter().all(|&(input, _)| typed(input)),
        }
    }

    fn is_typed(&self, node: NodeId) -> bool {
        self.lowered.typed[node.index()]
    }

    /// A whole call has an argument per parameter, none a hole.
    fn whole(&self, callee: FunctionId, inputs: &[(NodeId, TextRange)]) -> bool {
        self.arity(callee) == inputs.len()
            && inputs
                .iter()
                .all(|&(input, _)| self.lowered.typed[input.index()])
    }

    fn arity(&self, callee: FunctionId) -> usize {
        self.graph
            .param_types(callee)
            .expect("a callee has parameter types")
            .len()
    }

    fn context_at(
        &mut self,
        region: NodeIdx,
        op: Op,
        condition: (NodeId, TextRange),
        parent: NodeId,
    ) -> NodeId {
        let at = self.source.range(region);
        self.place(op, &[condition, (parent, at)], at, None)
    }

    /// The graph node a condition's operand built, when it has a type.
    fn typed(&self, node: NodeIdx) -> Option<NodeId> {
        let id = self.nodes_of[node.to_usize()]?;
        self.lowered.typed[id.index()].then_some(id)
    }

    fn hole(&mut self, node: NodeIdx) -> NodeId {
        self.push(node, Op::Hole, &[], None)
    }

    fn hole_value(&mut self, node: NodeIdx) -> Value {
        let id = self.hole(node);
        let range = self.source.range(node);
        Value {
            node: id,
            range,
            at: range,
            control: None,
            completes: false,
            is_valid: false,
            has_scalar_tail: false,
        }
    }

    /// A value of its own: no block, so read where it is written.
    fn value(&self, node: NodeIdx, id: NodeId, control: Option<NodeId>, completes: bool) -> Value {
        let range = self.source.range(node);
        let is_valid = self.is_typed(id);
        Value {
            node: id,
            range,
            at: range,
            control,
            completes,
            is_valid,
            has_scalar_tail: is_valid && !completes,
        }
    }

    /// A child's value, or a hole at `node` for a missing one.
    fn present(&mut self, node: NodeIdx, child: Option<Value>) -> Value {
        match child {
            Some(child) => child,
            None => self.hole_value(node),
        }
    }

    fn fail(&mut self) {
        self.has_failed = true;
    }

    /// Where a scope bounded by `node` ends: after its own closing brace, or, for a node without
    /// one, where the next significant token starts, so a name typed after an unclosed block
    /// still sees its locals.
    fn scope_end(&self, node: NodeIdx) -> TextSize {
        let lexed = self.source.lexed();
        let tree = self.source.tree;
        let end = tree.end_token(node);
        if tree.holds(node, lexed, SyntaxKind::RBrace, None) {
            lexed.boundary(end)
        } else {
            self.start_after(end)
        }
    }

    fn significant_after(&self, from: RawIdx) -> Option<RawIdx> {
        let lexed = self.source.lexed();
        from.until(lexed.end())
            .find(|&index| !lexed.kind(index).is_trivia())
    }

    /// One past the source's end, so an offset at the end is before it.
    fn past_end(&self) -> TextSize {
        TextSize::new(self.source.lexed().source_len().to_u32() + 1)
    }

    /// Where the first significant token at or after `from` starts, or past the end.
    fn start_after(&self, from: RawIdx) -> TextSize {
        let lexed = self.source.lexed();
        self.significant_after(from)
            .map_or(self.past_end(), |index| lexed.boundary(index))
    }

    fn open_scope(&mut self, end: TextSize) {
        if self.depth == self.scopes.len() {
            self.scopes.push(Scope::default());
            self.scope_ends.push(end);
            self.scope_mutables.push(self.mutable_locals.len());
        } else {
            self.scopes[self.depth].clear();
            self.scope_ends[self.depth] = end;
            self.scope_mutables[self.depth] = self.mutable_locals.len();
        }
        self.depth += 1;
    }

    fn close_scope(&mut self) {
        self.depth -= 1;
        self.mutable_locals
            .truncate(self.scope_mutables[self.depth]);
    }

    /// `from` is where reads of the name start to see it, within the innermost open scope, which
    /// bounds them.
    fn bind(
        &mut self,
        name: &'s str,
        node: NodeId,
        kind: BindingKind,
        range: TextRange,
        from: TextSize,
    ) -> LocalId {
        let is_mutable = matches!(
            kind,
            BindingKind::Let { is_mutable: true } | BindingKind::Param { is_mutable: true }
        );
        let end = self.scope_ends[self.depth - 1];
        let from = from.min(end);
        // A muted instance declares no binding, so its locals' IDs name none; `refer` is muted
        // with it.
        let binding = BindingId::new(self.lowered.bindings.len());
        if !self.source.is_muted {
            self.lowered
                .bindings
                .push(Binding::new(range, kind, node, TextRange::new(from, end)));
        }
        let id = self.versions.declare(node, is_mutable);
        debug_assert_eq!(
            id.index(),
            self.locals.len(),
            "a local's versions are its own"
        );
        self.locals.push(Local {
            name,
            binding,
            declaration: node,
            completes: false,
            is_read: name.starts_with('_'),
            is_assigned: false,
        });
        if is_mutable {
            self.mutable_locals.push(id);
        }
        self.scopes[self.depth - 1].insert(name, id);
        id
    }

    /// The state of a guard that opens no region: what its refinements make of the versions.
    fn guarded_state(&mut self, condition: NodeIdx, sense: bool, context: NodeId) -> RegionState {
        let mark = self.versions.mark();
        self.refine(condition, sense);
        self.versions.guarded(mark, context)
    }

    /// Opens `region` for lowering: versions assigned inside it are undone when it closes.
    fn enter_region(&mut self, region: RegionId) {
        self.versions.fork();
        self.regions.push((region, self.graph.context(region)));
        self.graph.enter(region);
    }

    /// Closes `region` on `result`, taking back the versions it assigned as its state.
    fn leave_region(&mut self, region: RegionId, result: &Value) -> RegionState {
        self.advance(result);
        let fallthrough = self.context();
        self.graph
            .close_with_control(region, result.node, !result.completes, result.control);
        self.spans.close(region, result.at);
        self.regions
            .pop()
            .expect("a region opened before it closes");
        self.versions.join(fallthrough)
    }

    /// Lowers `root` inside `region`, guarded by the condition holding in `sense` when given.
    fn region(
        &mut self,
        region: RegionId,
        guard: Option<(NodeIdx, bool)>,
        root: impl FnOnce(&mut Self) -> Value,
    ) -> (Value, RegionState) {
        self.enter_region(region);
        if let Some((condition, sense)) = guard {
            self.refine(condition, sense);
        }
        let value = root(self);
        let state = self.leave_region(region, &value);
        (value, state)
    }

    fn merge_versions(
        &mut self,
        condition: (NodeId, TextRange),
        states: &[&RegionState],
        at: TextRange,
    ) {
        let mut changed: Vec<_> = states
            .iter()
            .flat_map(|state| state.changes.iter().map(|&(local, _, _)| local))
            .collect();
        changed.sort_unstable_by_key(|local| local.index());
        changed.dedup();
        let mut values = std::mem::take(&mut self.merge_values);
        let mut inputs = std::mem::take(&mut self.merge_inputs);
        let mut contexts = std::mem::take(&mut self.merge_contexts);
        for local in changed {
            values.clear();
            values.extend(states.iter().map(|state| {
                if let Ok(index) = state
                    .changes
                    .binary_search_by_key(&local.index(), |&(local, _, _)| local.index())
                {
                    let (_, version, value) = state.changes[index];
                    (version, value)
                } else {
                    let version = self.versions.version(local);
                    let value = state
                        .refinements
                        .iter()
                        .rev()
                        .find(|&&(id, source, _)| id == local && source == version)
                        .map_or_else(|| self.versions.read(local), |&(_, _, value)| value);
                    (version, value)
                }
            }));
            if values.iter().all(|&(version, _)| version == values[0].0) {
                continue;
            }
            let declaration = self.locals[local.index()].declaration;
            inputs.clear();
            inputs.push(condition);
            inputs.extend(
                values
                    .iter()
                    .map(|&(_, value)| (value, self.spans.origin(value))),
            );
            contexts.clear();
            contexts.extend(states.iter().map(|state| state.context));
            let phi = self.place_with(
                Op::Phi,
                &inputs,
                References::Phi {
                    declaration,
                    contexts: &contexts,
                },
                at,
                None,
            );
            self.versions.set(local, phi);
        }
        self.merge_values = values;
        self.merge_inputs = inputs;
        self.merge_contexts = contexts;
    }

    fn refer(&mut self, node: NodeIdx, symbol: Symbol, is_write: bool) {
        if self.source.is_muted {
            return;
        }
        self.lowered.references.push(Occurrence {
            range: self.source.range(node),
            symbol,
            is_write,
        });
    }

    fn lookup(&self, name: &str) -> Option<LocalId> {
        // An empty scope is common and would cost a hash to find nothing in.
        self.scopes[..self.depth]
            .iter()
            .rev()
            .filter(|scope| !scope.is_empty())
            .find_map(|scope| scope.get(name).copied())
    }

    fn context(&self) -> NodeId {
        self.regions.last().expect("a body runs in its region").1
    }

    fn compose_control(
        &mut self,
        at: TextRange,
        parts: impl IntoIterator<Item = Option<NodeId>>,
    ) -> Option<NodeId> {
        parts.into_iter().flatten().reduce(|before, value| {
            self.place(Op::Sequence, &[(before, at), (value, at)], at, None)
        })
    }

    /// Moves the context past `value`'s control: what follows runs only if it completed.
    fn advance(&mut self, value: &Value) {
        let Some(control) = value.control else {
            return;
        };
        let context = self.context();
        if matches!(self.graph.node(context).op, Op::After)
            && self.graph.inputs(context)[0] == control
        {
            return;
        }
        let at = value.range;
        let after = self.place(Op::After, &[(control, at), (context, at)], at, None);
        self.regions
            .last_mut()
            .expect("a body runs in its region")
            .1 = after;
    }

    /// The scope is as it was when the read was built: a region is entered right after its
    /// condition finishes.
    fn read(&self, node: NodeIdx) -> Option<(LocalId, NodeId)> {
        let tree = self.source.tree;
        let ast::Expr::NameRef(name) = self.source.peel(ast::Expr::cast(tree, node)?) else {
            return None;
        };
        self.reads_of[name.node().to_usize()]
    }

    /// Narrow the locals `cond` compares, for `cond` holding in `sense`. Operands are taken in
    /// source order off a stack, since a chain of `&&` nests as deep as it is long.
    fn refine(&mut self, cond: NodeIdx, sense: bool) {
        let mut pending = vec![(cond, sense)];
        while let Some((cond, sense)) = pending.pop() {
            self.refine_one(cond, sense, &mut pending);
        }
    }

    fn refine_one(&mut self, cond: NodeIdx, sense: bool, pending: &mut Vec<(NodeIdx, bool)>) {
        use sumi_syntax::BinaryOp::*;

        if self.bottoms[cond.to_usize()] {
            return;
        }
        let tree = self.source.tree;
        let Some(expr) = ast::Expr::cast(tree, cond)
            .map(|expr| self.source.peel(expr))
            .and_then(|expr| expr.clean(tree, self.source.lexed()))
        else {
            return;
        };
        let node = expr.node();
        match expr {
            ast::CleanExpr::PrefixExpr(prefix) => match prefix.op() {
                PrefixOp::Not => pending.push((prefix.operand().node(), !sense)),
                PrefixOp::Neg => {}
            },
            ast::CleanExpr::BinaryExpr(binary) => {
                let lhs = binary.lhs().node();
                let rhs = binary.rhs().node();
                let op = binary.op();
                match op {
                    And if sense => {
                        pending.push((rhs, sense));
                        pending.push((lhs, sense));
                    }
                    Or if !sense => {
                        pending.push((rhs, sense));
                        pending.push((lhs, sense));
                    }
                    Cmp(op) => {
                        let op = cmp(op);
                        for (side, other, local_is_lhs) in [(lhs, rhs, true), (rhs, lhs, false)] {
                            if let (Some((local, version)), Some(_), Some(value)) =
                                (self.read(side), self.typed(side), self.typed(other))
                                && self.versions.version(local) == version
                            {
                                let inputs = [
                                    (self.versions.read(local), self.source.range(side)),
                                    (value, self.source.range(other)),
                                ];
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
                                self.versions.refine(local, version, read);
                            }
                        }
                    }
                    _ => {}
                }
            }
            ast::CleanExpr::NameRef(_) => {
                if let Some((local, version)) = self.read(node)
                    && self.versions.version(local) == version
                {
                    let at = self.source.range(node);
                    let inputs = [(self.versions.read(local), at)];
                    let read = self.place(Op::Exactly(sense), &inputs, at, None);
                    self.versions.refine(local, version, read);
                }
            }
            _ => {}
        }
    }

    /// A statement or expression, from the children it has. One the parser recovered in is
    /// lowered where its kind decides its type and is a hole otherwise; either way the body fails.
    /// An operator's or field's left operand is lowered first, off a stack of the operators and
    /// fields it is under: the parser nests such a chain as deep as it is long.
    fn lower(&mut self, node: NodeIdx) -> Value {
        self.lower_guarded(node).0
    }

    /// `lower`, with what holds after the chain of one lazy operator the value came off, for an
    /// operator of that kind around it to go on from.
    fn lower_guarded(&mut self, node: NodeIdx) -> (Value, Option<Guard>) {
        let mut chain = Vec::new();
        let mut leaf = node;
        while let Some((left, link)) = self.link(leaf) {
            chain.push(link);
            leaf = left;
        }
        // Parentheses hand on the guard of the chain inside them.
        let (mut value, mut guard) = match self.parenthesized(leaf) {
            Some(inner) => {
                let (value, guard) = self.lower_guarded(inner);
                (self.through(leaf, value, false), guard)
            }
            None => (self.lower_one(leaf), None),
        };
        while let Some(link) = chain.pop() {
            let before = guard.take();
            value = match link {
                Link::Lazy(expr, is_and) => {
                    let (value, held) = self.lazy(expr, is_and, value, before);
                    guard = Some(held);
                    value
                }
                Link::Eager(expr, op) => {
                    let damaged = self.is_damaged(expr.node());
                    self.binary(expr, op, damaged, Some(value))
                }
                Link::Field(expr) => {
                    let damaged = self.is_damaged(expr.node());
                    self.field(expr, damaged, Some(value))
                }
                Link::Method(expr) => {
                    let damaged = self.is_damaged(expr.node());
                    self.method_call(expr, damaged, Some(value))
                }
            };
        }
        (value, guard)
    }

    /// `node` as a link of a chain, with the left operand it lowers before anything of its own.
    fn link(&self, node: NodeIdx) -> Option<(NodeIdx, Link)> {
        use ast::{Expr, Stmt};

        let tree = self.source.tree;
        match Stmt::cast(tree, node)? {
            Stmt::Expr(Expr::BinaryExpr(expr)) => {
                let op = expr.op(tree, self.source.lexed())?;
                let left = expr.lhs(tree)?.node();
                match eager(op) {
                    Some(op) => Some((left, Link::Eager(expr, op))),
                    None if tree.has_error(node) => None,
                    None => Some((left, Link::Lazy(expr, op == sumi_syntax::BinaryOp::And))),
                }
            }
            Stmt::Expr(Expr::FieldExpr(expr)) => Some((expr.base(tree)?.node(), Link::Field(expr))),
            Stmt::Expr(Expr::MethodCallExpr(expr)) => {
                let receiver = expr.callee(tree)?.base(tree)?;
                let is_place = self.receiver_place(receiver).is_some();
                (!is_place).then_some((receiver.node(), Link::Method(expr)))
            }
            _ => None,
        }
    }

    /// What whole parentheses hold.
    fn parenthesized(&self, node: NodeIdx) -> Option<NodeIdx> {
        let tree = self.source.tree;
        let ast::Expr::ParenExpr(paren) = ast::Expr::cast(tree, node)? else {
            return None;
        };
        (!tree.has_error(node))
            .then(|| paren.inner(tree))?
            .map(|inner| inner.node())
    }

    /// Whether the parser recovered in `node`, which fails the body.
    fn is_damaged(&mut self, node: NodeIdx) -> bool {
        let damaged = self.source.tree.has_error(node);
        if damaged {
            self.fail();
        }
        damaged
    }

    /// A node that is no link of a chain: one with no left operand to lower first.
    fn lower_one(&mut self, node: NodeIdx) -> Value {
        use ast::{Expr, Stmt};

        let tree = self.source.tree;
        let damaged = tree.has_error(node);
        let Some(stmt) = Stmt::cast(tree, node) else {
            if !damaged {
                unreachable!("a statement without syntax errors has a view");
            }
            return self.holed(node);
        };
        if damaged {
            self.fail();
        }
        match stmt {
            Stmt::LetStmt(binding) => self.let_(binding, damaged),
            Stmt::AssignStmt(assignment) => self.assign(assignment, damaged),
            Stmt::DiscardStmt(discard) => match discard.value(tree) {
                Some(value) => {
                    let value = self.lower(value.node());
                    self.through(node, value, damaged)
                }
                None => self.holed(node),
            },
            Stmt::ReturnStmt(return_) => self.return_(return_, damaged),
            Stmt::Expr(Expr::Block(_)) => self.block(node),
            Stmt::Expr(Expr::IfExpr(branch)) => self.if_(branch),
            Stmt::Expr(
                Expr::ForExpr(_)
                | Expr::MatchExpr(_)
                | Expr::NameRef(_)
                | Expr::SelfExpr(_)
                | Expr::LiteralExpr(_),
            ) if damaged => self.holed(node),
            Stmt::Expr(Expr::ForExpr(expr)) => self.for_(expr),
            Stmt::Expr(Expr::MatchExpr(expr)) => self.match_(expr),
            Stmt::Expr(Expr::NameRef(_) | Expr::SelfExpr(_)) => self.name_ref(node),
            Stmt::Expr(Expr::LiteralExpr(literal)) => self.literal(literal),
            // A lazy operator here lost a part to recovery: a whole one is a link of a chain.
            Stmt::Expr(Expr::BinaryExpr(expr)) => {
                match expr.op(tree, self.source.lexed()).and_then(eager) {
                    Some(op) => self.binary(expr, op, damaged, None),
                    None => self.holed(node),
                }
            }
            Stmt::Expr(Expr::PrefixExpr(expr)) => self.prefix(expr, damaged),
            Stmt::Expr(Expr::ParenExpr(paren)) => match paren.inner(tree) {
                Some(inner) => {
                    let value = self.lower(inner.node());
                    self.through(node, value, damaged)
                }
                None => self.holed(node),
            },
            Stmt::Expr(Expr::CallExpr(call)) => self.call(call, damaged),
            Stmt::Expr(Expr::MethodCallExpr(call)) => self.method_call(call, damaged, None),
            Stmt::Expr(Expr::FieldExpr(expr)) => self.field(expr, damaged, None),
        }
    }

    /// A hole still resolves the names under it, so an editor finds them; one a declaration
    /// under the hole may bind is left unresolved, since that binding was never made.
    fn holed(&mut self, node: NodeIdx) -> Value {
        let value = self.hole_value(node);
        let tree = self.source.tree;
        let subtree = || {
            let end =
                node.to_u32() + u32::try_from(tree.subtree_len(node)).expect("node count fits u32");
            node.until(NodeIdx::new(end))
        };
        let declared: HashSet<&str, FxBuildHasher> = subtree()
            .filter(|&inner| tree.kind(inner) == NodeKind::Name)
            .map(|inner| self.source.text(inner))
            .collect();
        for inner in subtree() {
            if tree.kind(inner) != NodeKind::NameRef {
                continue;
            }
            let name = self.source.text(inner);
            if declared.contains(name) {
                if !self.source.is_muted {
                    self.lowered.unresolved.push(self.source.range(inner));
                }
                continue;
            }
            if let Some(local) = self.lookup(name) {
                self.refer(
                    inner,
                    Symbol::Local(self.locals[local.index()].binding),
                    false,
                );
            } else if let Some(&Named::Function(id)) = self.declared.names.get(name) {
                self.refer(inner, Symbol::Function(id), false);
            }
        }
        self.fail();
        value
    }

    /// A hole where a name or literal denotes no value; the body fails.
    fn failed_hole(&mut self, node: NodeIdx) -> Value {
        let value = self.hole_value(node);
        self.fail();
        value
    }

    fn let_(&mut self, binding: ast::LetStmt, damaged: bool) -> Value {
        let tree = self.source.tree;
        let node = binding.node();
        let Some(initializer) = binding.initializer(tree) else {
            return self.damaged_let(binding);
        };
        let value = self.lower(initializer.node());
        let annotation = binding.type_ref(tree);
        let declared = annotation.and_then(|annotation| self.source.ty(annotation));
        let Some((name, name_node)) = self.source.name(binding.name(tree)) else {
            return self.failed_hole(node);
        };
        let op = match (annotation, declared) {
            (Some(_), None) => Op::Hole,
            _ => Op::Copy { declared },
        };
        let name_range = self.source.range(name_node);
        let copy = self.push(node, op, &[value.input()], Some(name_range));
        if let (Some(annotation), Some(_)) = (annotation, declared) {
            self.annotate(copy, annotation.node());
        }
        let is_mutable = binding.mutable(tree, self.source.lexed());
        let local = self.bind(
            name,
            copy,
            BindingKind::Let { is_mutable },
            name_range,
            self.source.range(node).end(),
        );
        self.locals[local.index()].completes = value.completes;
        self.bottoms[node.to_usize()] = value.completes;
        if value.completes {
            self.completes_input(copy, 0);
        }
        if damaged || !value.is_valid || !self.is_typed(copy) {
            self.fail();
        }
        self.value(node, copy, value.control, value.completes)
    }

    /// A binding that cannot be built still takes its name, as a hole.
    fn damaged_let(&mut self, binding: ast::LetStmt) -> Value {
        let tree = self.source.tree;
        let node = binding.node();
        let hole = match self.source.name(binding.name(tree)) {
            Some((name, name_node)) => {
                let name_range = self.source.range(name_node);
                let hole = self.push(node, Op::Hole, &[], Some(name_range));
                self.bind(
                    name,
                    hole,
                    BindingKind::Let {
                        is_mutable: binding.mutable(tree, self.source.lexed()),
                    },
                    name_range,
                    self.source.range(node).end(),
                );
                hole
            }
            None => self.hole(node),
        };
        self.fail();
        self.value(node, hole, None, false)
    }

    fn assign(&mut self, assignment: ast::AssignStmt, damaged: bool) -> Value {
        let tree = self.source.tree;
        let node = assignment.node();
        let at = self.source.range(node);
        let place = assignment
            .target(tree)
            .and_then(|target| self.place_of(target).ok());
        let value = assignment.value(tree).map(|value| self.lower(value.node()));
        let value = self.present(node, value);
        let op = assignment.op(tree, self.source.lexed());
        let assigned = match &place {
            // A value that returns first is assigned to nothing.
            Some(place) if value.completes => {
                let declaration = self.locals[place.local.index()].declaration;
                let references = References::Version(declaration);
                let assigned = self.place_with(Op::Assign, &[value.input()], references, at, None);
                self.completes_input(assigned, 0);
                Some(assigned)
            }
            Some(place) => self.path(place).and_then(|path| {
                self.refer_path(place, &path, true);
                let value = match op {
                    Some(AssignOp::Arith(op)) => self.combined(place, &path, op, &value, node)?,
                    _ => value.input(),
                };
                Some(self.write(place, path, value, at))
            }),
            None => None,
        };
        let id = match assigned {
            Some(assigned) => assigned,
            None => self.place(Op::Hole, &[value.input()], at, None),
        };
        self.nodes_of[node.to_usize()] = Some(id);
        self.bottoms[node.to_usize()] = value.completes;
        if damaged || assigned.is_none() || !value.is_valid || !self.is_typed(id) {
            self.fail();
        }
        self.value(node, id, value.control, value.completes)
    }

    /// The place's own value and `value` under `op`, for a compound assignment at `node`; none
    /// where the place holds no integer, which is reported as the operand it is.
    fn combined(
        &mut self,
        place: &Place<'s>,
        path: &Path,
        op: sumi_syntax::ArithOp,
        value: &Value,
        node: NodeIdx,
    ) -> Option<(NodeId, TextRange)> {
        let held = self.held(place, path);
        let range = self.place_range(place, place.fields.len());
        if !self.is_typed(held) {
            return None;
        }
        match self.decides_at(held) {
            Decides::Ty(ty) if ty != Ty::INT => {
                self.source.type_mismatch(range, Ty::INT, ty, None);
                return None;
            }
            Decides::Failed => return None,
            _ => {}
        }
        let op = BinaryOp::Arith(arith(op));
        let at = self.source.range(node);
        let id = self.place(Op::Binary(op), &[(held, range), value.input()], at, None);
        if value.is_valid {
            self.divides(op, node, value.node);
        }
        Some((id, value.at))
    }

    /// A `/` or `%` at `node` owes its divisor a proof that it is no zero.
    fn divides(&mut self, op: BinaryOp, node: NodeIdx, divisor: NodeId) {
        if matches!(op, BinaryOp::Arith(ArithOp::Div | ArithOp::Rem)) {
            self.lowered.obligations.push(Obligation {
                owner: self.owner,
                node,
                divisor,
                context: self.context(),
            });
        }
    }

    /// The place `target` names: a mutable local, or a field under one. Any other is reported,
    /// and is no name's reference unless its shape is a place's.
    fn place_of(&mut self, target: ast::Expr) -> Result<Place<'s>, IsShaped> {
        let (root, fields) = match self.place_shape(target) {
            Ok(shape) => shape,
            Err(other) => {
                self.source.error(
                    other,
                    codes::INVALID_ASSIGNMENT_TARGET,
                    "this is no place: a place is a `mut` name, or a field under one",
                    None,
                );
                return Err(IsShaped(false));
            }
        };
        let name = root;
        let text = self.source.text(name);
        let Some(local) = self.lookup(text) else {
            if let Some(&named) = self.declared.names.get(text) {
                let what = match named {
                    Named::Function(id) => {
                        self.refer(name, Symbol::Function(id), true);
                        "function"
                    }
                    Named::Type(id) => {
                        self.refer(name, Symbol::Type(id), true);
                        "type"
                    }
                    Named::Ambiguous => "name",
                };
                self.source.error(
                    name,
                    codes::INVALID_ASSIGNMENT_TARGET,
                    format!("{what} `{text}` is not assignable"),
                    None,
                );
            } else {
                self.source.error(
                    name,
                    codes::UNKNOWN_NAME,
                    format!("unknown name `{text}`"),
                    None,
                );
            }
            return Err(IsShaped(true));
        };
        self.refer(
            name,
            Symbol::Local(self.locals[local.index()].binding),
            true,
        );
        if !self.versions.is_mutable(local) {
            let declaration = self.locals[local.index()].declaration;
            self.source.error(
                name,
                codes::IMMUTABLE_ASSIGNMENT,
                format!("cannot assign to immutable local `{text}`"),
                self.spans
                    .name(declaration)
                    .map(|range| (range, "declared here")),
            );
            return Err(IsShaped(true));
        }
        self.locals[local.index()].is_assigned = true;
        Ok(Place {
            local,
            root: name,
            fields,
        })
    }

    /// The name, or `self`, a place's syntax begins with and the fields under it, outermost
    /// first; else the expression that is no part of one.
    #[allow(clippy::type_complexity)]
    fn place_shape(
        &self,
        target: ast::Expr,
    ) -> Result<(NodeIdx, Vec<(&'s str, NodeIdx)>), NodeIdx> {
        let tree = self.source.tree;
        let mut fields = Vec::new();
        let mut expr = self.source.peel(target);
        let root = loop {
            let step = match expr {
                ast::Expr::NameRef(_) | ast::Expr::SelfExpr(_) => break expr.node(),
                ast::Expr::FieldExpr(field) if !tree.has_error(field.node()) => {
                    field.base(tree).zip(field.field(tree))
                }
                _ => None,
            };
            let Some((base, field)) = step else {
                return Err(expr.node());
            };
            fields.push((self.source.text(field.node()), field.node()));
            expr = self.source.peel(base);
        };
        fields.reverse();
        Ok((root, fields))
    }

    /// The place a method's receiver is, where it has a place's shape under a local.
    fn receiver_place(&self, receiver: ast::Expr) -> Option<Place<'s>> {
        let (root, fields) = self.place_shape(receiver).ok()?;
        let local = self.lookup(self.source.text(root))?;
        Some(Place {
            local,
            root,
            fields,
        })
    }

    /// Where the place is written in the source, through the field at `depth` of its fields.
    fn place_range(&self, place: &Place<'s>, depth: usize) -> TextRange {
        let end = match depth.checked_sub(1) {
            Some(last) => place.fields[last].1,
            None => place.root,
        };
        TextRange::new(
            self.source.range(place.root).start(),
            self.source.range(end).end(),
        )
    }

    /// The record each field of the place is of, outermost first: none where a field is not
    /// known, which is reported at its name.
    fn path(&mut self, place: &Place<'s>) -> Option<Path> {
        let mut base = self.versions.read(place.local);
        let mut path = Vec::with_capacity(place.fields.len());
        for (depth, &(name, node)) in place.fields.iter().enumerate() {
            let (decl, field) = self.field_of(base, name, node)?;
            path.push((base, decl, field));
            if depth + 1 < place.fields.len() {
                let name = self.source.field_name(name);
                let range = self.place_range(place, depth + 1);
                let read = (base, self.place_range(place, depth));
                base = self.place(Op::Field(name), &[read], range, None);
            }
        }
        Some(path)
    }

    /// Refers each field of the place to the field it names, the last one as written if `writes`.
    fn refer_path(&mut self, place: &Place<'s>, path: &Path, writes: bool) {
        for (depth, (&(_, node), &(_, decl, field))) in place.fields.iter().zip(path).enumerate() {
            let item = self.source.decls[decl.index()].item;
            let is_written = writes && depth + 1 == path.len();
            self.refer(node, Symbol::Field(item, field as u32), is_written);
        }
    }

    /// The value the place holds now: the field of the last record on its path, or its local.
    fn held(&mut self, place: &Place<'s>, path: &Path) -> NodeId {
        let Some(&(base, decl, field)) = path.last() else {
            return self.versions.read(place.local);
        };
        let name = self.source.fields(decl)[field].0;
        let range = self.place_range(place, path.len());
        let base = (base, self.place_range(place, path.len() - 1));
        self.place(Op::Field(name), &[base], range, None)
    }

    /// The value a `mut` argument's place holds, for its parameter.
    fn read_place(&mut self, place: &Place<'s>) -> Value {
        self.locals[place.local.index()].is_read = true;
        let range = self.place_range(place, place.fields.len());
        let read = match self.path(place) {
            Some(path) => {
                self.refer_path(place, &path, true);
                self.held(place, &path)
            }
            None => self.place(Op::Hole, &[], range, None),
        };
        let is_valid = self.is_typed(read);
        if !is_valid {
            self.fail();
        }
        Value {
            node: read,
            range,
            at: range,
            control: None,
            completes: false,
            is_valid,
            has_scalar_tail: is_valid,
        }
    }

    /// The declared type the value at `base` is of and its field `name`, by position; none where
    /// it has no such field, or its type is not known, which is reported unless it failed.
    fn field_of(&mut self, base: NodeId, name: &str, at: NodeIdx) -> Option<(DeclId, usize)> {
        if !self.is_typed(base) {
            return None;
        }
        let ty = match self.decides_at(base) {
            Decides::Ty(ty) => ty,
            Decides::Failed => return None,
            read => {
                let message = format!(
                    "the type the field `{name}` is of is not known here{}",
                    pending_text(read)
                );
                self.source.error(at, codes::UNKNOWN_FIELD, message, None);
                return None;
            }
        };
        let decl = ty.as_decl();
        let field = decl.and_then(|decl| self.source.decls[decl.index()].index_of(name));
        if let (Some(decl), Some(field)) = (decl, field) {
            return Some((decl, field));
        }
        let declared = decl
            .and_then(|decl| self.source.decls[decl.index()].name_node)
            .map(|node| (self.source.range(node), "declared here"));
        let message = format!("`{}` has no field `{name}`", self.source.show(ty));
        self.source
            .error(at, codes::UNKNOWN_FIELD, message, declared);
        None
    }

    /// Writes `value` to the place: its local's next version, which is every record on `path`
    /// made again with what changed under it.
    fn write(
        &mut self,
        place: &Place<'s>,
        path: Path,
        value: (NodeId, TextRange),
        at: TextRange,
    ) -> NodeId {
        let mut value = value;
        for (depth, (base, decl, field)) in path.into_iter().enumerate().rev() {
            let range = self.place_range(place, depth);
            let count = self.source.fields(decl).len();
            let mut inputs = Vec::with_capacity(count);
            for other in 0..count {
                if other == field {
                    inputs.push(value);
                } else {
                    let name = self.source.fields(decl)[other].0;
                    let read = self.place(Op::Field(name), &[(base, range)], range, None);
                    inputs.push((read, range));
                }
            }
            value = (self.place(Op::Make(decl), &inputs, at, None), range);
        }
        let declaration = self.locals[place.local.index()].declaration;
        let references = References::Version(declaration);
        let assigned = self.place_with(Op::Assign, &[value], references, at, None);
        if self.is_typed(assigned) {
            self.versions.set(place.local, assigned);
        }
        assigned
    }

    /// One exit's value of a function with `mut` parameters: its result there, held to the type
    /// declared for it, then the value each `mut` parameter has.
    fn exit(&mut self, product: DeclId, result: (NodeId, TextRange)) -> NodeId {
        let owner = self.owner as usize;
        let (value, at) = result;
        let value = match self.declared.headers[owner].result.declared() {
            Some((ty, annotation)) => {
                let range = self.source.range(annotation);
                let copy = self.place(Op::Copy { declared: Some(ty) }, &[result], range, None);
                self.annotate(copy, annotation);
                copy
            }
            None => value,
        };
        self.lowered.exits[owner].push((value, at));
        let mut inputs = vec![(value, at)];
        for index in 0..self.outs.len() {
            inputs.push((self.versions.read(self.outs[index]), at));
        }
        self.place(Op::Make(product), &inputs, at, None)
    }

    fn through(&mut self, node: NodeIdx, value: Value, damaged: bool) -> Value {
        self.nodes_of[node.to_usize()] = Some(value.node);
        self.bottoms[node.to_usize()] = value.completes;
        if damaged || !value.is_valid {
            self.fail();
        }
        self.value(node, value.node, value.control, value.completes)
    }

    fn return_(&mut self, return_: ast::ReturnStmt, damaged: bool) -> Value {
        let node = return_.node();
        let at = self.source.range(node);
        let value = return_.value(self.source.tree);
        if damaged && value.is_none() {
            return self.holed(node);
        }
        let value = value.map(|value| {
            let value = self.lower(value.node());
            self.advance(&value);
            value
        });
        let payload = match value {
            Some(value) => value.input(),
            None => {
                let unit = self.push(node, Op::Unit, &[(self.context(), at)], None);
                (unit, at)
            }
        };
        let product = self.declared.headers[self.owner as usize].product;
        let payload = match product {
            Some(product) if !value.is_some_and(|value| value.completes) => {
                (self.exit(product, payload), at)
            }
            _ => payload,
        };
        let returned = self.push(node, Op::Return, &[payload, (self.context(), at)], None);
        let control =
            self.compose_control(at, [value.and_then(|value| value.control), Some(returned)]);
        if value.is_some_and(|value| value.completes) {
            self.completes_input(returned, 0);
        } else {
            self.returns.push((returned, at));
        }
        let is_valid = value.is_none_or(|value| value.is_valid);
        if !is_valid {
            self.fail();
        }
        self.bottoms[node.to_usize()] = is_valid;
        Value {
            node: returned,
            range: at,
            at,
            control,
            completes: is_valid,
            is_valid: self.is_typed(returned),
            has_scalar_tail: false,
        }
    }

    fn block(&mut self, node: NodeIdx) -> Value {
        let tree = self.source.tree;
        let damaged = tree.has_error(node);
        let range = self.source.range(node);
        self.open_scope(self.scope_end(node));
        let mut children = tree.children(node).peekable();
        let mut controls = Vec::new();
        let mut tail: Option<Value> = None;
        let mut is_valid = !damaged;
        let mut is_bottom = false;
        while let Some(child) = children.next() {
            let is_expression = ast::Expr::cast(tree, child).is_some();
            let is_tail = is_expression && children.peek().is_none();
            self.lowered.statements.push(Statement {
                owner: FunctionId::new(self.owner as usize),
                block: node,
                range: self.source.range(child),
                context: self.context(),
            });
            let value = self.lower(child);
            if is_expression && !is_tail {
                // An unused statement is discarded whole, so it is read as a whole.
                let input = (value.node, value.range);
                let unused = self.place(Op::Unused, &[input], value.range, None);
                if value.completes {
                    self.completes_input(unused, 0);
                }
            }
            self.advance(&value);
            controls.push(value.control);
            is_valid &= value.is_valid;
            is_bottom |= value.completes;
            if is_tail {
                tail = Some(value);
            }
        }
        self.close_scope();
        let control = self.compose_control(range, controls);
        // A damaged block may have lost its tail to recovery, so without one it is a hole, not
        // unit.
        let (id, at, has_scalar_tail) = match tail {
            Some(tail) => {
                self.nodes_of[node.to_usize()] = Some(tail.node);
                (tail.node, tail.at, tail.has_scalar_tail)
            }
            None if damaged => (self.hole(node), range, false),
            None => {
                let context = self.context();
                let unit = self.push(node, Op::Unit, &[(context, range)], None);
                (unit, range, false)
            }
        };
        self.bottoms[node.to_usize()] = is_bottom;
        let is_typed = self.is_typed(id);
        if !is_valid || damaged || (!is_bottom && !is_typed) {
            self.fail();
        }
        Value {
            node: id,
            range,
            at,
            control,
            completes: is_bottom,
            is_valid: is_typed,
            has_scalar_tail,
        }
    }

    /// A read of the local a name, or `self`, at `node` names.
    fn name_ref(&mut self, node: NodeIdx) -> Value {
        let name = self.source.text(node);
        let Some(local) = self.lookup(name) else {
            if self.source.tree.kind(node) == NodeKind::SelfExpr {
                self.source.error(
                    node,
                    codes::INVALID_SELF,
                    "`self` is a method's receiver, and this function takes none",
                    None,
                );
            } else if self.source.param(name).is_some() {
                self.source.error(
                    node,
                    codes::NOT_A_VALUE,
                    format!("type parameter `{name}` is not a value"),
                    None,
                );
            } else if let Some(&named) = self.declared.names.get(name) {
                let what = match named {
                    Named::Function(id) => {
                        self.refer(node, Symbol::Function(id), false);
                        "function"
                    }
                    Named::Type(id) => {
                        self.refer(node, Symbol::Type(id), false);
                        "type"
                    }
                    Named::Ambiguous => "name",
                };
                self.source.error(
                    node,
                    codes::NOT_A_VALUE,
                    format!("{what} `{name}` is not a value"),
                    None,
                );
            } else {
                self.source.error(
                    node,
                    codes::UNKNOWN_NAME,
                    format!("unknown name `{name}`"),
                    None,
                );
            }
            return self.failed_hole(node);
        };
        self.refer(
            node,
            Symbol::Local(self.locals[local.index()].binding),
            false,
        );
        self.locals[local.index()].is_read = true;
        let version = self.versions.version(local);
        let read = self.versions.read(local);
        self.nodes_of[node.to_usize()] = Some(read);
        self.reads_of[node.to_usize()] = Some((local, version));
        let completes = self.locals[local.index()].completes;
        self.bottoms[node.to_usize()] = completes;
        if !self.is_typed(read) {
            self.fail();
        }
        self.value(node, read, None, completes)
    }

    fn literal(&mut self, literal: ast::LiteralExpr) -> Value {
        let node = literal.node();
        let id = match literal.value(self.source.tree, self.source.lexed()) {
            Some(Literal::Int) => match self.integer(node, node, false) {
                Some(id) => id,
                None => return self.failed_hole(node),
            },
            Some(Literal::True) => self.push(node, Op::Bool(true), &[], None),
            Some(Literal::False) => self.push(node, Op::Bool(false), &[], None),
            None => unreachable!("a literal without syntax errors has a value"),
        };
        self.value(node, id, None, false)
    }

    /// `None` for a malformed literal, which the lexer already reported.
    fn integer(&mut self, origin: NodeIdx, literal: NodeIdx, is_negative: bool) -> Option<NodeId> {
        let raw = self.source.tree.first_token(literal);
        if self
            .source
            .lexed()
            .flags(raw)
            .contains(TokenFlags::MALFORMED_NUMBER)
        {
            return None;
        }
        let magnitude: Int = self
            .source
            .text(literal)
            .parse()
            .expect("a well-formed literal is a run of digits");
        let value = if is_negative { -&magnitude } else { magnitude };
        Some(self.push(origin, Op::Int(value), &[], None))
    }

    fn prefix(&mut self, expr: ast::PrefixExpr, damaged: bool) -> Value {
        let tree = self.source.tree;
        let node = expr.node();
        let Some(op) = expr.op(tree, self.source.lexed()) else {
            return self.holed(node);
        };
        let is_neg = op == PrefixOp::Neg;
        let operand = expr.operand(tree);
        // A negative literal is one value, so its magnitude is never read on its own.
        if !damaged
            && is_neg
            && let Some(operand) = operand
            && let ast::Expr::LiteralExpr(literal) = self.source.peel(operand)
            && literal.value(tree, self.source.lexed()) == Some(Literal::Int)
        {
            return match self.integer(node, literal.node(), true) {
                Some(id) => self.value(node, id, None, false),
                None => self.failed_hole(node),
            };
        }
        let operand = operand.map(|operand| self.lower(operand.node()));
        let operand = self.present(node, operand);
        let id = self.push(
            node,
            if is_neg { Op::Neg } else { Op::Not },
            &[operand.input()],
            None,
        );
        self.bottoms[node.to_usize()] = operand.completes;
        if operand.completes {
            self.completes_input(id, 0);
        }
        if damaged || !operand.is_valid {
            self.fail();
        }
        self.value(node, id, operand.control, operand.completes)
    }

    /// `lhs` is the lowered left operand, when the operator has one.
    fn binary(
        &mut self,
        expr: ast::BinaryExpr,
        op: BinaryOp,
        damaged: bool,
        lhs: Option<Value>,
    ) -> Value {
        let tree = self.source.tree;
        let node = expr.node();
        if let Some(lhs) = &lhs {
            self.advance(lhs);
        }
        let rhs = expr.rhs(tree).map(|rhs| self.lower(rhs.node()));
        let lhs = self.present(node, lhs);
        let rhs = self.present(node, rhs);
        let id = self.push(node, Op::Binary(op), &[lhs.input(), rhs.input()], None);
        let range = self.source.range(node);
        let control = self.compose_control(range, [lhs.control, rhs.control]);
        for (index, operand) in [lhs, rhs].into_iter().enumerate() {
            if operand.completes {
                self.completes_input(id, index);
            }
        }
        let completes = lhs.completes || rhs.completes;
        self.bottoms[node.to_usize()] = completes;
        let is_valid = lhs.is_valid && rhs.is_valid;
        if damaged || !is_valid {
            self.fail();
        } else if !completes {
            self.divides(op, node, rhs.node);
        }
        self.value(node, id, control, completes)
    }

    /// `chain` is what held for the operator before it in its chain. The right operand's guard is
    /// built outside its region, so the next operator of the chain holds the same nodes again.
    fn lazy(
        &mut self,
        expr: ast::BinaryExpr,
        is_and: bool,
        lhs: Value,
        chain: Option<Guard>,
    ) -> (Value, Guard) {
        let tree = self.source.tree;
        let node = expr.node();
        let at = self.source.range(node);
        let whole = "a whole operator has its operands";
        let lhs_node = expr.lhs(tree).expect(whole).node();
        let rhs_node = expr.rhs(tree).expect(whole).node();
        self.advance(&lhs);
        let mark = self.versions.mark();
        match chain {
            // The operand before narrows on top of those before it, which hold while it does.
            Some(guard) if guard.is_and == is_and => {
                self.versions.hold(&guard.refinements);
                self.refine(guard.last, is_and);
            }
            _ => self.refine(lhs_node, is_and),
        }
        let refinements = self.versions.take(mark);
        let parent = self.context();
        let left = lhs.input();
        let selected = usize::from(!is_and);
        let mut contexts = [parent; 2];
        contexts[selected] = self.context_at(rhs_node, Op::Arm(Case::Bool(is_and)), left, parent);
        if !self.mutable_locals.is_empty() {
            contexts[usize::from(is_and)] =
                self.context_at(rhs_node, Op::Arm(Case::Bool(!is_and)), left, parent);
        }
        let arms = self.graph.open_arms(&[contexts[selected]]);
        let region = arms.iter().next().expect("the right operand has its arm");
        self.enter_region(region);
        self.versions.hold(&refinements);
        let rhs = self.lower(rhs_node);
        let state = self.leave_region(region, &rhs);
        let held = Guard {
            is_and,
            refinements,
            last: rhs_node,
        };
        let op = if is_and {
            Op::And { rhs: region }
        } else {
            Op::Or { rhs: region }
        };
        let id = self.push_over(node, op, &[left], References::None, None, &[rhs.node]);
        let observe = rhs.control.map(|_| {
            self.place(
                Op::Observe { arms },
                &[left, (self.context(), at)],
                at,
                None,
            )
        });
        let control = self.compose_control(at, [lhs.control, observe]);
        let mut value = self.value(node, id, control, false);
        if !lhs.is_valid || (!lhs.completes && !rhs.is_valid) {
            self.fail();
        } else if lhs.completes {
            self.completes_input(id, 0);
            self.bottoms[node.to_usize()] = true;
            value.completes = true;
            value.has_scalar_tail = false;
        } else if rhs.completes {
            self.refine(lhs_node, !is_and);
        } else {
            let skipped = self.guarded_state(lhs_node, !is_and, contexts[usize::from(is_and)]);
            let states = if is_and {
                [&state, &skipped]
            } else {
                [&skipped, &state]
            };
            self.merge_versions(left, &states, at);
        }
        (value, held)
    }

    /// An `if` by its parts. A part the parser lost stands as the `if` itself, which is a hole by
    /// then: its region closes on that hole, and nothing is entered for it.
    fn if_(&mut self, branch: ast::IfExpr) -> Value {
        let tree = self.source.tree;
        let lexed = self.source.lexed();
        let node = branch.node();
        let cond = branch.condition(tree).map_or(node, |cond| cond.node());
        let then_node = branch.then_branch(tree).map_or(node, |block| block.node());
        // An `else` keyword without its block is still an else.
        let else_node = branch
            .else_branch(tree)
            .map(|branch| branch.node())
            .or_else(|| {
                tree.holds(node, lexed, SyntaxKind::ElseKw, None)
                    .then_some(node)
            });
        let mut lost: Option<Value> = None;
        let condition = self.part(node, cond, &mut lost);
        self.advance(&condition);
        let parent = self.context();
        let on_true = Op::Arm(Case::Bool(true));
        let on_false = Op::Arm(Case::Bool(false));
        let then_context = self.context_at(then_node, on_true, condition.input(), parent);
        let else_context = match else_node {
            Some(else_node) => self.context_at(else_node, on_false, condition.input(), parent),
            None if !self.mutable_locals.is_empty() => {
                self.context_at(node, on_false, condition.input(), parent)
            }
            None => parent,
        };
        let contexts = [then_context, else_context];
        let arms = match else_node {
            Some(_) => self.graph.open_arms(&contexts),
            None => self.graph.open_arms(&contexts[..1]),
        };
        let then_region = arms.iter().next().expect("a switch has its then arm");
        let (then, then_state) = self.region(then_region, Some((cond, true)), |this| {
            this.part(node, then_node, &mut lost)
        });
        let (else_, false_state) = match else_node.zip(arms.iter().nth(1)) {
            Some((else_node, region)) => {
                let (value, state) = self.region(region, Some((cond, false)), |this| {
                    this.part(node, else_node, &mut lost)
                });
                (Some(value), state)
            }
            None => (None, self.guarded_state(cond, false, contexts[1])),
        };
        let values = [then, else_.unwrap_or(then)];
        let result = self.switch(
            node,
            &condition,
            arms,
            &values[..arms.len()],
            &[&then_state, &false_state],
        );
        // A switch that failed narrows nothing after it.
        if result.is_valid && !result.completes {
            if then.completes {
                self.refine(cond, false);
            }
            if else_.is_some_and(|value| value.completes) {
                self.refine(cond, true);
            }
        }
        result
    }

    /// A part of `node`, or `node` itself standing for a part the parser lost: one hole for all
    /// such parts, made where the first is read.
    fn part(&mut self, node: NodeIdx, part: NodeIdx, lost: &mut Option<Value>) -> Value {
        if part != node {
            return self.lower(part);
        }
        match lost {
            Some(value) => *value,
            None => {
                let value = self.hole_value(node);
                *lost = Some(value);
                value
            }
        }
    }

    /// A `match`'s arms by case: a member pattern names a declared type and binds a value of it; a
    /// rest pattern takes what the arms before leave. A pattern naming no type leaves a hole.
    fn match_(&mut self, expr: ast::MatchExpr) -> Value {
        let tree = self.source.tree;
        let lexed = self.source.lexed();
        let node = expr.node();
        let whole = "a whole match has its parts";
        let scrutinee_node = expr.scrutinee(tree).expect(whole).node();
        let scrutinee = self.lower(scrutinee_node);
        self.advance(&scrutinee);
        let parent = self.context();
        let input = scrutinee.input();
        let mut named: Vec<DeclId> = Vec::new();
        let mut cases: Vec<ArmCase> = Vec::new();
        let mut is_valid = true;
        for arm in expr.arm_list(tree).expect(whole).arms(tree) {
            let pattern = arm
                .pattern(tree)
                .and_then(|pattern| pattern.clean(tree, lexed))
                .expect(whole);
            let (case, binding) = match pattern {
                ast::CleanPattern::RestPattern(_) => (
                    if named.is_empty() {
                        Case::Any
                    } else {
                        Case::Not(self.source.union_of(&named))
                    },
                    None,
                ),
                ast::CleanPattern::MemberPattern(pattern) => {
                    let member = pattern.member().node();
                    let name = self.source.text(member);
                    if self.source.param(name).is_some() {
                        self.source.error(
                            member,
                            codes::INVALID_UNION_MEMBER,
                            format!("`{name}` is a type parameter, so no member an arm can name"),
                            None,
                        );
                        is_valid = false;
                        continue;
                    }
                    match self.declared.names.get(name).copied() {
                        Some(Named::Type(item)) => {
                            self.refer(member, Symbol::Type(item), false);
                            let at = self.source.range(member);
                            let type_args = pattern.type_args(tree);
                            let decl = if type_args.is_none() && self.source.is_generic(item) {
                                self.infer_member(member, item, &scrutinee)
                            } else {
                                self.source.apply(item, type_args, at, false)
                            };
                            let Some(decl) = decl else {
                                is_valid = false;
                                continue;
                            };
                            named.push(decl);
                            let binding = pattern
                                .binding(tree)
                                .map(|name| (name.node(), Ty::decl(decl)));
                            (Case::Is(Ty::decl(decl)), binding)
                        }
                        Some(Named::Function(id)) => {
                            self.refer(member, Symbol::Function(id), false);
                            self.source.error(
                                member,
                                codes::UNKNOWN_TYPE,
                                format!("`{name}` is a function, not a type"),
                                None,
                            );
                            is_valid = false;
                            continue;
                        }
                        Some(Named::Ambiguous) => {
                            is_valid = false;
                            continue;
                        }
                        None => {
                            self.source.error(
                                member,
                                codes::UNKNOWN_TYPE,
                                format!("unknown type `{name}`"),
                                None,
                            );
                            is_valid = false;
                            continue;
                        }
                    }
                }
            };
            cases.push((arm, case, binding));
        }
        if cases.is_empty() && is_valid {
            self.source
                .error(node, codes::NON_EXHAUSTIVE_MATCH, "match has no arms", None);
            is_valid = false;
        }
        if !is_valid {
            let id = self.push(node, Op::Hole, &[input], None);
            self.fail();
            return self.value(node, id, scrutinee.control, false);
        }
        let contexts: Vec<NodeId> = cases
            .iter()
            .map(|&(arm, case, _)| self.context_at(arm.node(), Op::Arm(case), input, parent))
            .collect();
        let arms = self.graph.open_arms(&contexts);
        let mut values = Vec::with_capacity(cases.len());
        let mut states = Vec::with_capacity(cases.len());
        for (&(arm, _, binding), region) in cases.iter().zip(arms.iter()) {
            self.enter_region(region);
            self.open_scope(self.scope_end(arm.node()));
            if let Some((name, ty)) = binding {
                let at = self.source.range(name);
                let narrow = self.push(name, Op::Narrow(ty), &[input], Some(at));
                let text = self.source.text(name);
                let local = self.bind(text, narrow, BindingKind::Arm, at, at.end());
                self.locals[local.index()].completes = scrutinee.completes;
            }
            let value = self.lower(arm.value(tree).expect(whole).node());
            states.push(self.leave_region(region, &value));
            self.close_scope();
            values.push(value);
        }
        let states: Vec<&RegionState> = states.iter().collect();
        self.switch(node, &scrutinee, arms, &values, &states)
    }

    /// The instance of the generic type `item` an arm names without type arguments: the one
    /// member of the scrutinee's type that is an instance of it.
    fn infer_member(&mut self, member: NodeIdx, item: DeclId, scrutinee: &Value) -> Option<DeclId> {
        let at = self.source.range(member);
        if self.source.is_muted {
            let args = self.decided(member)?;
            return self.source.instantiate(item, args, at);
        }
        let name = self.source.decls[item.index()].name;
        let ty = match self.decides(scrutinee) {
            Decides::Ty(ty) => ty,
            Decides::Failed => return None,
            read => {
                let message = format!(
                    "the type matched does not decide which `{name}` this is{}; write its type \
                     arguments",
                    pending_text(read)
                );
                self.source
                    .error(member, codes::TYPE_ARGUMENTS, message, None);
                return None;
            }
        };
        let members = self.source.decls_of(ty).into_iter();
        let mut instances = members.filter(|&decl| self.source.decls[decl.index()].item == item);
        match (instances.next(), instances.next()) {
            (Some(decl), None) => {
                let args = self.source.decls[decl.index()].args.clone();
                self.decide(member, &args);
                Some(decl)
            }
            (first, _) => {
                let found = if first.is_some() {
                    "more than one"
                } else {
                    "no"
                };
                let message = format!(
                    "`{}` holds {found} `{name}`; write its type arguments",
                    self.source.show(ty)
                );
                self.source
                    .error(member, codes::TYPE_ARGUMENTS, message, None);
                None
            }
        }
    }

    /// A switch over `scrutinee`: `values` are the arms' results, each with the state its region
    /// left, and an omitted `else` contributes a state but no value.
    fn switch(
        &mut self,
        node: NodeIdx,
        scrutinee: &Value,
        arms: Arms,
        values: &[Value],
        states: &[&RegionState],
    ) -> Value {
        let at = self.source.range(node);
        let input = scrutinee.input();
        let results: Vec<NodeId> = values.iter().map(|value| value.node).collect();
        let is_valid = values.iter().all(|value| value.is_valid);
        let completes = states.len() == values.len() && values.iter().all(|value| value.completes);
        let id = self.push_over(
            node,
            Op::Switch { arms },
            &[input],
            References::None,
            None,
            &results,
        );
        let observe = values.iter().any(|value| value.control.is_some()).then(|| {
            self.place(
                Op::Observe { arms },
                &[input, (self.context(), at)],
                at,
                None,
            )
        });
        let control = self.compose_control(at, [scrutinee.control, observe]);
        if scrutinee.completes {
            self.completes_input(id, 0);
        }
        let mut value = self.value(node, id, control, false);
        if !scrutinee.is_valid || !is_valid {
            self.fail();
            return value;
        }
        if scrutinee.completes || completes {
            self.bottoms[node.to_usize()] = true;
            value.completes = true;
            value.has_scalar_tail = false;
        } else {
            self.merge_versions(input, states, at);
        }
        value
    }

    fn for_(&mut self, expr: ast::ForExpr) -> Value {
        let tree = self.source.tree;
        let node = expr.node();
        let at = self.source.range(node);
        let whole = "a whole loop has its parts";
        let start_node = expr.start(tree).expect(whole).node();
        let end_node = expr.end(tree).expect(whole).node();
        let body_node = expr.body(tree).expect(whole).node();
        let name = expr.name(tree).expect(whole).node();
        let bounds = [start_node, end_node].map(|bound| {
            let value = self.lower(bound);
            self.advance(&value);
            value
        });
        let inputs = bounds.map(Value::input);
        let range = TextRange::new(
            self.source.range(start_node).start(),
            self.source.range(end_node).end(),
        );
        let condition = self.place(Op::Binary(BinaryOp::Cmp(CmpOp::Lt)), &inputs, range, None);
        let context = self.context_at(
            body_node,
            Op::Arm(Case::Bool(true)),
            (condition, at),
            self.context(),
        );
        let empty = self.context_at(
            node,
            Op::Arm(Case::Bool(false)),
            (condition, at),
            self.context(),
        );
        let region = self.graph.open(context);
        self.enter_region(region);
        let body_range = TextRange::new(
            self.source.range(body_node).start(),
            self.scope_end(body_node),
        );
        self.open_scope(body_range.end());
        let name_range = self.source.range(name);
        let index = self.place(Op::LoopIndex, &inputs, at, Some(name_range));
        for (position, bound) in bounds.iter().enumerate() {
            if bound.completes {
                self.completes_input(condition, position);
                self.completes_input(index, position);
            }
        }
        self.bind(
            self.source.text(name),
            index,
            BindingKind::LoopIndex,
            name_range,
            body_range.start(),
        );
        let mut carried = Vec::with_capacity(self.mutable_locals.len());
        for position in 0..self.mutable_locals.len() {
            let local = self.mutable_locals[position];
            if self.locals[local.index()].completes {
                continue;
            }
            let initial = self.versions.read(local);
            let declaration = self.locals[local.index()].declaration;
            let header = self.place_with(
                Op::Carry,
                &[(initial, self.spans.origin(initial))],
                References::Version(declaration),
                at,
                None,
            );
            self.versions.set(local, header);
            carried.push((local, header));
        }
        let body = self.lower(body_node);
        let body_state = self.leave_region(region, &body);
        self.close_scope();
        let next: Vec<_> = carried
            .iter()
            .map(|&(local, header)| {
                let position = body_state
                    .changes
                    .binary_search_by_key(&local.index(), |&(local, _, _)| local.index())
                    .expect("a carried local has a header version");
                (header, body_state.changes[position].2)
            })
            .collect();
        let carried_nodes: Vec<NodeId> = next
            .iter()
            .flat_map(|&(header, next)| [header, next])
            .collect();
        let references = References::Loop {
            index,
            continuation: body_state.context,
            empty,
            carried: Carried::new(&carried_nodes),
        };
        let loop_inputs = bounds.map(|bound| {
            let (value, at) = bound.input();
            let value = bound.control.map_or(value, |control| {
                self.place(Op::Sequence, &[(control, at), (value, at)], at, None)
            });
            (value, at)
        });
        let id = self.push_over(
            node,
            Op::Loop { body: region },
            &loop_inputs,
            references,
            None,
            &[],
        );
        for ((local, header), (_, next)) in carried.into_iter().zip(next) {
            if header == next {
                continue;
            }
            let value = self.place_with(
                Op::LoopValue,
                &[(id, at)],
                References::LoopValue {
                    carry: header,
                    next,
                },
                at,
                None,
            );
            self.versions.set(local, value);
        }
        let mut is_valid = body.is_valid;
        let mut completes = false;
        for (position, bound) in bounds.iter().enumerate() {
            is_valid &= bound.is_valid;
            if bound.completes {
                self.completes_input(id, position);
                completes = true;
            }
        }
        self.bottoms[node.to_usize()] = completes;
        if !is_valid {
            self.fail();
        }
        self.value(node, id, Some(id), completes)
    }

    fn target(&mut self, node: NodeIdx) -> Target {
        let name = self.source.text(node);
        if let Some(local) = self.lookup(name) {
            self.refer(
                node,
                Symbol::Local(self.locals[local.index()].binding),
                false,
            );
            self.locals[local.index()].is_read = true;
            let declaration = self.locals[local.index()].declaration;
            // A binding that failed is reported once, where it failed.
            if self.lowered.typed[declaration.index()] {
                self.source.error(
                    node,
                    codes::NOT_CALLABLE,
                    format!("local `{name}` is not callable"),
                    self.spans
                        .name(declaration)
                        .map(|range| (range, "declared here")),
                );
            }
            return Target::Unknown;
        }
        if let Some(ty) = self.source.param(name) {
            if let (SELF, Some(decl)) = (name, ty.as_decl()) {
                return Target::Instance(decl);
            }
            self.source.error(
                node,
                codes::NOT_CALLABLE,
                format!("type parameter `{name}` is not callable"),
                None,
            );
            return Target::Unknown;
        }
        match self.declared.names.get(name).copied() {
            Some(Named::Function(target)) => {
                self.refer(node, Symbol::Function(target), false);
                Target::Function(target)
            }
            Some(Named::Type(decl)) => {
                self.refer(node, Symbol::Type(decl), false);
                Target::Type(decl)
            }
            Some(Named::Ambiguous) => Target::Unknown,
            None => {
                self.source.error(
                    node,
                    codes::UNKNOWN_NAME,
                    format!("unknown function `{name}`"),
                    None,
                );
                Target::Unknown
            }
        }
    }

    /// What a call names once its type argument list is read: its target at the list's types,
    /// one per type parameter. A call that names none is reported here.
    fn applied(&mut self, site: Site, callee: NodeIdx, target: Target, damaged: bool) -> Applied {
        let list = site.list;
        let at = self.source.range(callee);
        match target {
            Target::Unknown => {
                self.source.type_args(list);
                Applied::Unknown
            }
            Target::Instance(decl) => {
                let (given, _) = self.source.type_args(list);
                let takes = self.source.takes(0, given, list, at, None, damaged);
                if takes {
                    Applied::Type(decl)
                } else {
                    Applied::Unknown
                }
            }
            Target::Type(item) if list.is_none() && self.source.is_generic(item) => {
                Applied::InferredType(item)
            }
            Target::Type(item) => match self.source.apply(item, list, at, damaged) {
                Some(decl) => Applied::Type(decl),
                None => Applied::Unknown,
            },
            Target::Function(generic) => {
                let expected = self.declared.items[generic.index()].params.len();
                if list.is_none() && expected > 0 {
                    return Applied::Inferred(generic);
                }
                let (given, args) = self.source.type_args(list);
                let declared = self.declared.headers[generic.index()].name;
                let takes = self
                    .source
                    .takes(expected, given, list, at, declared, damaged);
                if !takes {
                    return Applied::Unknown;
                }
                if expected == 0 {
                    return Applied::Function(generic);
                }
                let instance = args.and_then(|args| self.instance(site, generic, args));
                instance.map_or(Applied::Unknown, Applied::Function)
            }
        }
    }

    /// What a method call names once its type argument list is read. The list is of the method's
    /// own type parameters: its `impl`'s come first and are the receiver's to decide, so they
    /// are returned undecided beside the written ones.
    fn applied_method(
        &mut self,
        site: Site,
        method: FunctionId,
        damaged: bool,
    ) -> (Applied, Vec<Option<Ty>>) {
        let item = &self.declared.items[method.index()];
        let total = item.params.len();
        let own = total - item.method.map_or(0, |method| method.impl_params);
        let Some(list) = site.list else {
            let applied = if total == 0 {
                Applied::Function(method)
            } else {
                Applied::Inferred(method)
            };
            return (applied, Vec::new());
        };
        let (given, args) = self.source.type_args(Some(list));
        let at = site
            .name
            .map_or(self.source.range(site.node), |name| self.source.range(name));
        let declared = self.declared.headers[method.index()].name;
        let takes = self
            .source
            .takes(own, given, Some(list), at, declared, damaged);
        match args.filter(|_| takes) {
            Some(_) if total == 0 => (Applied::Function(method), Vec::new()),
            Some(args) => {
                let mut bound = vec![None; total - own];
                bound.extend(args.into_iter().map(Some));
                (Applied::Inferred(method), bound)
            }
            None => (Applied::Unknown, Vec::new()),
        }
    }

    /// The instance of `generic` the call names at `args`; none for a call marked as having no
    /// last instance.
    fn instance(&mut self, site: Site, generic: FunctionId, args: Vec<Ty>) -> Option<FunctionId> {
        if self.declared.unbounded.contains(&site.node) {
            return None;
        }
        let caller = self.declared.headers[self.owner as usize].generic;
        if caller.index() == self.owner as usize
            && !self.declared.items[caller.index()].params.is_empty()
        {
            self.generic_calls.push(GenericCall {
                caller,
                callee: generic,
                site,
                args: args.clone(),
            });
        }
        self.declared
            .instance(self.source, &mut self.graph, generic, args)
    }

    /// Reports the type parameters of `name` that `bound` leaves open, unless a value that
    /// failed may be what would have decided them.
    fn undecided(
        &mut self,
        at: NodeIdx,
        name: &str,
        params: &[&'s str],
        bound: &[Option<Ty>],
        values: &[Decides],
        declared: Option<TextRange>,
    ) {
        if values.iter().any(|read| matches!(read, Decides::Failed)) {
            return;
        }
        let open: Vec<String> = params
            .iter()
            .zip(bound)
            .filter(|(_, bound)| bound.is_none())
            .map(|(param, _)| format!("`{param}`"))
            .collect();
        let what = if open.len() == 1 {
            "type parameter"
        } else {
            "type parameters"
        };
        let pending = values.iter().find(|read| matches!(read, Decides::Pending));
        let message = format!(
            "the arguments do not decide {what} {} of `{name}`{}; write its type arguments",
            join(&open),
            pending.map_or("", |&read| pending_text(read)),
        );
        self.source.error(
            at,
            codes::TYPE_ARGUMENTS,
            message,
            declared.map(|declared| (declared, "declared here")),
        );
    }

    /// The instance of `generic` its arguments decide, one per parameter: each type parameter
    /// `bound` leaves open is the type of the first argument whose parameter names it.
    fn infer_call(
        &mut self,
        site: Site,
        generic: FunctionId,
        args: &Args,
        bound: Vec<Option<Ty>>,
    ) -> Option<FunctionId> {
        let name = site.name?;
        if self.source.is_muted {
            let args = self.decided(name)?;
            return self.instance(site, generic, args);
        }
        let patterns = self.graph.param_types(generic)?.to_vec();
        let values: Vec<Decides> = args.iter().map(|(_, value)| self.decides(value)).collect();
        let params = self.declared.type_args[generic.index()].clone();
        let mut bound = bound;
        bound.resize(params.len(), None);
        for (&pattern, &value) in patterns.iter().zip(&values) {
            if let Decides::Ty(actual) = value {
                self.source.bind(pattern, actual, &params, &mut bound);
            }
        }
        match bound.iter().copied().collect::<Option<Vec<Ty>>>() {
            Some(args) => {
                self.decide(name, &args);
                self.instance(site, generic, args)
            }
            None => {
                let names = self.declared.items[generic.index()].params.clone();
                let text = self.source.text(name);
                let declared = self.declared.headers[generic.index()].name;
                self.undecided(name, text, &names, &bound, &values, declared);
                None
            }
        }
    }

    /// The instance of the type `item` the values given its fields decide, one per field.
    fn infer_fields(
        &mut self,
        callee: NodeIdx,
        item: DeclId,
        given: &[Option<(Value, NodeIdx)>],
    ) -> Option<DeclId> {
        let at = self.source.range(callee);
        if self.source.is_muted {
            let args = self.decided(callee)?;
            return self.source.instantiate(item, args, at);
        }
        let params = self.source.decls[item.index()].args.clone();
        let mut bound = vec![None; params.len()];
        let mut values = Vec::with_capacity(given.len());
        for (field, given) in given.iter().enumerate() {
            let (value, _) = given.expect("every field given");
            let value = self.decides(&value);
            if let (Some(pattern), Decides::Ty(actual)) = (self.source.fields(item)[field].1, value)
            {
                self.source.bind(pattern, actual, &params, &mut bound);
            }
            values.push(value);
        }
        match bound.iter().copied().collect::<Option<Vec<Ty>>>() {
            Some(args) => {
                self.decide(callee, &args);
                self.source.instantiate(item, args, at)
            }
            None => {
                let names = self.source.type_items[item.index()].params.clone();
                let name = self.source.decls[item.index()].name;
                let declared = self.source.decls[item.index()]
                    .name_node
                    .map(|node| self.source.range(node));
                self.undecided(callee, name, &names, &bound, &values, declared);
                None
            }
        }
    }

    /// Lowers the arguments of `list` onto `args`, in order, up to any garbage: the ones whose
    /// position is reliable. One written `mut` is a place, and joins `lent`.
    fn arguments(&mut self, list: Option<ast::ArgList>, args: &mut Args, lent: &mut Lent<'s>) {
        let tree = self.source.tree;
        if let Some(list) = list {
            for child in tree.children(list.node()) {
                let Some((arg, value)) =
                    ast::Arg::cast(tree, child).and_then(|arg| Some((arg, arg.value(tree)?)))
                else {
                    break;
                };
                let is_mut = arg.mutable(tree, self.source.lexed());
                let place = is_mut.then(|| self.place_of(value));
                let value = match &place {
                    Some(Ok(place)) => self.read_place(place),
                    Some(Err(IsShaped(true))) => self.failed_hole(value.node()),
                    Some(Err(IsShaped(false))) => self.holed(value.node()),
                    None => {
                        let value = self.lower(value.node());
                        self.advance(&value);
                        value
                    }
                };
                if let Some(place) = place {
                    lent.push((args.len(), place.ok()));
                }
                args.push((Some(arg), value));
            }
        }
        // A place is read where the call begins: again, if an argument after it wrote its local.
        for (index, place) in lent.iter() {
            let Some(place) = place.as_ref().filter(|_| args[*index].1.is_valid) else {
                continue;
            };
            let mut read = args[*index].1.node;
            for _ in &place.fields {
                read = self.graph.inputs(read)[0];
            }
            if read != self.versions.read(place.local) {
                args[*index].1 = self.read_place(place);
            }
        }
    }

    /// Every argument is read, arity aside: the typing holds each to its parameter. A damaged
    /// list is not yet the wrong length, and its labels are not yet in order.
    fn call(&mut self, call: ast::CallExpr, damaged: bool) -> Value {
        let tree = self.source.tree;
        let site = Site {
            node: call.node(),
            name: call.callee(tree).map(|callee| callee.node()),
            list: call.type_args(tree),
        };
        let applied = match site.name {
            Some(name) => {
                let target = self.target(name);
                self.applied(site, name, target, damaged)
            }
            None => Applied::Unknown,
        };
        let (mut args, mut lent) = (Vec::new(), Vec::new());
        self.arguments(call.arg_list(tree), &mut args, &mut lent);
        if !damaged && matches!(applied, Applied::Type(_) | Applied::InferredType(_)) {
            for &(index, _) in &lent {
                self.source.report(
                    args[index].1.range,
                    codes::MUT_ARGUMENT,
                    "a field takes a value: `mut` is written for a `mut` parameter",
                    [],
                );
                self.fail();
            }
        }
        match applied {
            Applied::Type(decl) if !damaged => self.construct(call, decl, false, &args),
            Applied::InferredType(item) if !damaged => self.construct(call, item, true, &args),
            _ => self.invoke(site, applied, Vec::new(), args, lent, damaged, false),
        }
    }

    /// A call of the method its receiver's type gives the name. `receiver` is the lowered
    /// receiver where the call is a link of a chain; one that is a place is read here.
    fn method_call(
        &mut self,
        call: ast::MethodCallExpr,
        damaged: bool,
        receiver: Option<Value>,
    ) -> Value {
        let tree = self.source.tree;
        let node = call.node();
        let callee = call.callee(tree);
        let name = callee
            .and_then(|callee| callee.field(tree))
            .filter(|name| !tree.has_error(name.node()))
            .map(|name| name.node());
        let site = Site {
            node,
            name,
            list: call.type_args(tree),
        };
        let base = callee.and_then(|callee| callee.base(tree));
        let place = base
            .filter(|_| receiver.is_none())
            .and_then(|base| self.receiver_place(base));
        let path = place.as_ref().and_then(|place| self.path(place));
        let value = match (&place, receiver, base) {
            (Some(place), ..) => self.receiver_value(place, path.as_ref()),
            (None, Some(value), _) => value,
            (None, None, Some(base)) => self.lower(base.node()),
            (None, None, None) => self.hole_value(node),
        };
        self.advance(&value);
        let method = name.and_then(|name| self.method(name, &value));
        // Where the method says it changes its receiver.
        let taken = method.and_then(|method| {
            let receiver = self.declared.parameters[method.index()].first()?;
            let at = self.source.range(receiver.node);
            receiver
                .out()
                .map(|_| (at, Box::from("the receiver is `mut` here")))
        });
        let changes = taken.is_some();
        // A receiver its method changes is a place, as an argument written `mut` is.
        let mut lent = Vec::new();
        let mut is_refused = false;
        match &place {
            Some(place) => {
                let local = &mut self.locals[place.local.index()];
                local.is_assigned |= changes;
                let (binding, declaration) = (local.binding, local.declaration);
                self.refer(place.root, Symbol::Local(binding), changes);
                if let Some(path) = &path {
                    self.refer_path(place, path, changes);
                }
                if let Some(taken) = taken.clone()
                    && !self.versions.is_mutable(place.local)
                {
                    let message = format!(
                        "`{}` changes its receiver, and `{}` is immutable",
                        name.map_or("", |name| self.source.text(name)),
                        self.source.text(place.root)
                    );
                    let declared = self.spans.name(declaration);
                    let declared = declared.map(|range| (range, Box::from("declared here")));
                    self.source.report(
                        self.source.range(place.root),
                        codes::IMMUTABLE_ASSIGNMENT,
                        message,
                        declared.into_iter().chain([taken]),
                    );
                    is_refused = true;
                }
            }
            None => {
                if let Some(taken) = taken.clone() {
                    let message = format!(
                        "`{}` changes its receiver, which is no place: a place is a `mut` name, \
                         or a field under one",
                        name.map_or("", |name| self.source.text(name)),
                    );
                    let code = codes::INVALID_ASSIGNMENT_TARGET;
                    self.source.report(value.range, code, message, [taken]);
                    is_refused = true;
                }
            }
        }
        if is_refused {
            self.fail();
        } else if let (true, Some(place)) = (changes, place) {
            lent.push((0, Some(place)));
        }
        let mut args: Args = vec![(None, value)];
        self.arguments(call.arg_list(tree), &mut args, &mut lent);
        let (applied, bound) = match method {
            Some(method) => self.applied_method(site, method, damaged),
            None => {
                self.source.type_args(site.list);
                (Applied::Unknown, Vec::new())
            }
        };
        self.invoke(
            site,
            applied,
            bound,
            args,
            lent,
            damaged || is_refused,
            true,
        )
    }

    /// What a receiver that is a place holds: read along `path`, or a hole where that failed.
    fn receiver_value(&mut self, place: &Place<'s>, path: Option<&Path>) -> Value {
        self.locals[place.local.index()].is_read = true;
        let range = self.place_range(place, place.fields.len());
        let read = match path {
            Some(path) => self.held(place, path),
            None => self.place(Op::Hole, &[], range, None),
        };
        let is_valid = self.is_typed(read);
        if !is_valid {
            self.fail();
        }
        Value {
            node: read,
            range,
            at: range,
            control: None,
            completes: false,
            is_valid,
            has_scalar_tail: is_valid,
        }
    }

    /// The method the name at `name` is of the receiver's type; none is reported, unless the
    /// receiver failed.
    fn method(&mut self, name: NodeIdx, receiver: &Value) -> Option<FunctionId> {
        let text = self.source.text(name);
        let ty = match self.decides(receiver) {
            Decides::Ty(ty) => ty,
            Decides::Failed => return None,
            read => {
                let message = format!(
                    "the type `{text}` is a method of is not known here{}",
                    pending_text(read)
                );
                self.source
                    .error(name, codes::UNKNOWN_METHOD, message, None);
                return None;
            }
        };
        let decl = ty.as_decl();
        let item = decl.map(|decl| self.source.decls[decl.index()].item);
        let found = item.and_then(|item| self.declared.methods.get(&(item, text)).copied());
        let method = match found {
            Some((_, method)) => method?,
            None => {
                let declared = item
                    .and_then(|item| self.source.decls[item.index()].name_node)
                    .map(|node| (self.source.range(node), "declared here"));
                let is_field = item
                    .is_some_and(|item| self.source.decls[item.index()].index_of(text).is_some());
                let (code, message) = if is_field {
                    let message = format!(
                        "`{text}` is a field of `{}`, not a method",
                        self.source.show(ty)
                    );
                    (codes::NOT_CALLABLE, message)
                } else {
                    let message = format!("`{}` has no method `{text}`", self.source.show(ty));
                    (codes::UNKNOWN_METHOD, message)
                };
                self.source.error(name, code, message, declared);
                return None;
            }
        };
        self.refer(name, Symbol::Function(method), false);
        let header = self.declared.headers[method.index()];
        let takes_self = self.declared.parameters[method.index()]
            .first()
            .is_some_and(|receiver| receiver.name.is_some_and(|(name, _)| name == "self"));
        if !takes_self {
            self.source.error(
                name,
                codes::UNKNOWN_METHOD,
                format!("`{text}` takes no `self`, so it is called on no value"),
                header.name.map(|name| (name, "declared here")),
            );
            return None;
        }
        Some(method)
    }

    /// The call of what `applied` names over `args`, a method's receiver the first of them:
    /// `bound` are the type arguments already decided for one whose arguments decide the rest.
    #[allow(clippy::too_many_arguments)]
    fn invoke(
        &mut self,
        site: Site,
        applied: Applied,
        bound: Vec<Option<Ty>>,
        args: Args,
        lent: Lent<'s>,
        damaged: bool,
        is_method: bool,
    ) -> Value {
        let tree = self.source.tree;
        let node = site.node;
        let context = self.context();
        // The function named, whose parameter list its every instance shares.
        let named = match applied {
            Applied::Function(function) | Applied::Inferred(function) => Some(function),
            _ => None,
        };
        let arity = named
            .and_then(|function| self.graph.param_types(function))
            .map(<[Ty]>::len);
        let mut is_labeled = false;
        if !damaged {
            for (arg, _) in &args {
                // A label on an argument to a name that resolved to nothing is reported there.
                if let Some(label) = arg.and_then(|arg| arg.label(tree))
                    && let Some(function) = named
                {
                    let item = self.declared.headers[function.index()].item;
                    self.source.error(
                        label.node(),
                        codes::LABELED_ARGUMENT,
                        "a function's arguments take no labels",
                        Some((self.source.range(item), "declared here")),
                    );
                    is_labeled = true;
                }
            }
            if let (Some(function), Some(arity)) = (named, arity)
                && args.len() != arity
            {
                // A receiver is no argument of the call as it is written.
                let receiver = usize::from(is_method);
                let item = self.declared.headers[function.index()].item;
                let message = format!(
                    "expected {} arguments, found {}",
                    arity - receiver,
                    args.len() - receiver
                );
                self.source.error(
                    node,
                    codes::ARITY,
                    message,
                    Some((self.source.range(item), "declared here")),
                );
            }
        }
        let mut changes = !damaged && self.changes(named, &args, &lent, is_method);
        let target = match applied {
            Applied::Function(function) => Some(function),
            Applied::Inferred(generic) if !damaged && arity == Some(args.len()) => {
                self.infer_call(site, generic, &args, bound)
            }
            _ => None,
        };
        // The function the call is held to: one with parameter types.
        let callee = target.filter(|&function| self.graph.param_types(function).is_some());
        if let Some(target) = callee {
            self.lowered.entered.push((context, target));
        }
        let inputs: Vec<(NodeId, TextRange)> =
            args.iter().map(|(_, value)| value.input()).collect();
        let whole =
            callee.filter(|&id| !damaged && !is_labeled && changes && self.whole(id, &inputs));
        let op = callee.map_or(Op::Hole, Op::Call);
        let id = self.push(node, op, &inputs, None);
        if let Some(target) = callee
            && self.is_typed(id)
        {
            self.lowered.called.push((id, target));
        }
        let at = self.source.range(node);
        // What a function with `mut` parameters returns holds its result as a field.
        let product = callee.and_then(|callee| self.declared.headers[callee.index()].product);
        let result = match product {
            Some(_) if self.is_typed(id) => {
                let name = self.source.field_name(RESULT);
                let result = self.place(Op::Field(name), &[(id, at)], at, None);
                self.nodes_of[node.to_usize()] = Some(result);
                result
            }
            _ => id,
        };
        let control = self.compose_control(at, args.iter().map(|(_, value)| value.control));
        let mut completes = false;
        let mut is_valid = true;
        for (index, (_, value)) in args.iter().enumerate() {
            completes |= value.completes;
            is_valid &= value.is_valid;
            if value.completes {
                self.completes_input(id, index);
            }
        }
        self.bottoms[node.to_usize()] = completes;
        let value = self.value(node, result, control, completes);
        if damaged || !is_valid {
            self.fail();
            return value;
        }
        let Some(target) = whole else {
            self.fail();
            return value;
        };
        self.lowered.calls.push(Call {
            node: id,
            caller: FunctionId::new(self.owner as usize),
            callee: target,
            context,
        });
        // Each `mut` parameter's final value is written to the place it was read from, in order.
        for (index, place) in &lent {
            let index = *index;
            let Some(place) = place.as_ref().filter(|_| !completes) else {
                continue;
            };
            let name = self.declared.parameters[target.index()][index].out();
            let name = name.expect("a place is passed to a `mut` parameter");
            let range = args[index].1.range;
            if !self.lends(target, index, name, &args[index].1) {
                changes = false;
                continue;
            }
            let Some(path) = self.path(place) else {
                changes = false;
                continue;
            };
            let name = self.source.field_name(name);
            let out = self.place(Op::Field(name), &[(id, range)], range, None);
            self.write(place, path, (out, range), range);
        }
        let result = self.declared.headers[target.index()].result;
        if !changes || !completes && matches!(result, HeaderResult::None) {
            self.fail();
        }
        value
    }

    /// Whether the place `value` was read from can take back what the `mut` parameter `name` of
    /// `callee` holds: its type is the parameter's. A value that does not fit is the typing's.
    fn lends(&mut self, callee: FunctionId, index: usize, name: &str, value: &Value) -> bool {
        let types = self.graph.param_types(callee);
        let param = types.expect("a callee has parameter types")[index];
        let message = match self.decides(value) {
            Decides::Ty(ty) if ty == param => return true,
            Decides::Ty(ty) if self.source.unions.borrow().fits(ty, param) => format!(
                "this place holds {}, and `mut` parameter `{name}` may leave {} in it; their \
                 types must be the same",
                self.source.show(ty),
                self.source.show(param)
            ),
            Decides::Ty(_) | Decides::Failed => return false,
            read => format!(
                "the type of this place is not known here{}",
                pending_text(read)
            ),
        };
        let declared = self.declared.parameters[callee.index()][index].node;
        let declared = (self.source.range(declared), Box::from("declared here"));
        self.source
            .report(value.range, codes::TYPE_MISMATCH, message, [declared]);
        false
    }

    /// Whether the call writes `mut` where its function's parameters are, on places no two of
    /// which overlap; reported where not. A method's receiver is written none, and held to its
    /// method by the call.
    fn changes(
        &mut self,
        named: Option<FunctionId>,
        args: &Args,
        lent: &Lent<'s>,
        is_method: bool,
    ) -> bool {
        let takes =
            named.is_some_and(|named| self.declared.headers[named.index()].product.is_some());
        if lent.is_empty() && !takes {
            return true;
        }
        let Some(function) = named else {
            // The name that resolved to nothing is reported; what it would change is unknown.
            return false;
        };
        let mut agrees = true;
        let name = self.declared.headers[function.index()].name;
        let name = name.map_or("<missing>", |name| name.text(self.source.parsed.source()));
        for (index, (_, value)) in args.iter().enumerate().skip(usize::from(is_method)) {
            let Some(param) = self.declared.parameters[function.index()].get(index) else {
                break;
            };
            let is_lent = lent.iter().any(|&(lent, _)| lent == index);
            let (wants, node) = (param.out().is_some(), param.node);
            let Some((param, _)) = param.name.filter(|_| wants != is_lent) else {
                continue;
            };
            let message = if wants {
                format!(
                    "parameter `{param}` of `{name}` is `mut`; write `mut` before the place it \
                     changes"
                )
            } else {
                format!("parameter `{param}` of `{name}` is not `mut`")
            };
            let declared = (self.source.range(node), Box::from("declared here"));
            self.source
                .report(value.range, codes::MUT_ARGUMENT, message, [declared]);
            agrees = false;
        }
        for (position, (index, place)) in lent.iter().enumerate() {
            let Some(place) = place else { continue };
            let earlier = lent[..position].iter();
            let mut earlier =
                earlier.filter_map(|(index, earlier)| Some((*index, earlier.as_ref()?)));
            if let Some((first, _)) = earlier.find(|(_, earlier)| earlier.overlaps(place)) {
                let first = (args[first].1.range, Box::from("also changed here"));
                self.source.report(
                    args[*index].1.range,
                    codes::OVERLAPPING_PLACES,
                    "this place overlaps another the call changes",
                    [first],
                );
                agrees = false;
            }
        }
        agrees
    }

    /// Fields are stored in declaration order; argument controls run in source order. `decl` is the
    /// generic item when `is_inferred`: the fields' values decide its instance.
    fn construct(
        &mut self,
        call: ast::CallExpr,
        decl: DeclId,
        is_inferred: bool,
        args: &Args,
    ) -> Value {
        let tree = self.source.tree;
        let node = call.node();
        let fields = self.source.decls[decl.index()].fields.len();
        let type_name = self.source.show(Ty::decl(decl)).to_string();
        let item = self.source.decls[decl.index()].item;
        let declared = self.source.decls[decl.index()]
            .name_node
            .map(|name| (self.source.range(name), "declared here"));
        let mut given: Vec<Option<(Value, NodeIdx)>> = vec![None; fields];
        // A type with a field of no type is reported at its declaration.
        let mut is_damaged = self.source.fields(decl).iter().any(|(_, ty)| ty.is_none());
        for &(arg, value) in args {
            let Some(label) = arg.and_then(|arg| arg.label(tree)) else {
                self.source.report(
                    value.range,
                    codes::UNLABELED_FIELD,
                    format!("a value of `{type_name}` names each field: `field: value`"),
                    declared.map(|(range, message)| (range, Box::from(message))),
                );
                is_damaged = true;
                continue;
            };
            let field = self.source.text(label.node());
            match self.source.decls[decl.index()].index_of(field) {
                None => {
                    self.source.error(
                        label.node(),
                        codes::UNKNOWN_FIELD,
                        format!("type `{type_name}` has no field `{field}`"),
                        declared,
                    );
                    is_damaged = true;
                }
                Some(index) => match given[index] {
                    Some((_, first)) => {
                        self.source.error(
                            label.node(),
                            codes::DUPLICATE_FIELD,
                            format!("field `{field}` is given twice"),
                            Some((self.source.range(first), "first given here")),
                        );
                        is_damaged = true;
                    }
                    None => {
                        self.refer(label.node(), Symbol::Field(item, index as u32), false);
                        given[index] = Some((value, label.node()));
                    }
                },
            }
        }
        let missing: Vec<&str> = given
            .iter()
            .enumerate()
            .filter(|(_, given)| given.is_none())
            .map(|(index, _)| self.source.decls[decl.index()].fields[index].0)
            .collect();
        if !missing.is_empty() {
            let names: Vec<String> = missing.iter().map(|name| format!("`{name}`")).collect();
            let what = if names.len() == 1 { "field" } else { "fields" };
            self.source.error(
                node,
                codes::MISSING_FIELD,
                format!("missing {what} {} of `{type_name}`", join(&names)),
                declared,
            );
            is_damaged = true;
        }
        let instance = match call.callee(tree) {
            Some(callee) if is_inferred && !is_damaged => {
                self.infer_fields(callee.node(), decl, &given)
            }
            _ => Some(decl),
        };
        is_damaged |= instance.is_none();
        let decl = instance.unwrap_or(decl);
        let ordered: Vec<Value> = if is_damaged {
            args.iter().map(|&(_, value)| value).collect()
        } else {
            given
                .iter()
                .map(|given| given.expect("every field given").0)
                .collect()
        };
        let inputs: Vec<(NodeId, TextRange)> = ordered.iter().map(|value| value.input()).collect();
        let op = if is_damaged { Op::Hole } else { Op::Make(decl) };
        let id = self.push(node, op, &inputs, None);
        let at = self.source.range(node);
        let control = self.compose_control(at, args.iter().map(|(_, value)| value.control));
        let mut completes = false;
        let mut is_valid = true;
        for (index, value) in ordered.iter().enumerate() {
            completes |= value.completes;
            is_valid &= value.is_valid;
            if value.completes {
                self.completes_input(id, index);
            }
        }
        self.bottoms[node.to_usize()] = completes;
        if !is_valid || is_damaged {
            self.fail();
        }
        self.value(node, id, control, completes)
    }

    /// `base` is the lowered base, when the read has one.
    fn field(&mut self, expr: ast::FieldExpr, damaged: bool, base: Option<Value>) -> Value {
        let tree = self.source.tree;
        let node = expr.node();
        let field = expr
            .field(tree)
            .filter(|field| !tree.has_error(field.node()));
        let name = field.map(|field| self.source.field_name(self.source.text(field.node())));
        let base = self.present(node, base);
        let op = name.map_or(Op::Hole, Op::Field);
        let id = self.push(node, op, &[base.input()], None);
        if let Some(field) = field
            && !damaged
            && !self.source.is_muted
        {
            self.lowered
                .field_reads
                .push((id, self.source.range(field.node())));
        }
        self.bottoms[node.to_usize()] = base.completes;
        if base.completes {
            self.completes_input(id, 0);
        }
        if damaged || !base.is_valid {
            self.fail();
        }
        self.value(node, id, base.control, base.completes)
    }
}
