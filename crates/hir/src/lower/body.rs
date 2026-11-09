//! Function bodies to graph nodes, one recursive walk over the syntax: scopes and locals, versions
//! of mutable locals, regions and their contexts, and holes where the syntax or a name failed. The
//! parser bounds nesting, so the walk's depth is bounded with it.

use std::collections::HashSet;

use rustc_hash::FxBuildHasher;
use sumi_frontend::Fix;
use sumi_graph::{
    ArithOp, Arms, BinaryOp, Carried, Case, CmpOp, DeclId, FunctionId, Graph, GraphBuilder, Int,
    NodeId, Op, References, RegionId, Ty,
};
use sumi_lexer::{RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    Literal, NodeIdx, NodeKind, PrefixOp,
    ast::{self, AstNode, View},
};
use sumi_text::{TextEdit, TextRange, TextSize};

use super::declare::{Declarations, Header, HeaderResult, Named, Parameter};
use super::source::{NameMap, Source};
use super::versions::{RegionState, Versions};
use super::{Call, Fallthrough, Lowered, Obligation, Statement, diagnostic, join};
use crate::codes;
use crate::spans::{Spans, SpansBuilder};
use crate::{Binding, BindingId, BindingKind, Occurrence, Symbol};

pub(crate) fn lower<'s>(
    source: &mut Source<'s>,
    items: &[ast::FnItem],
    declared: &Declarations<'s>,
    graph: GraphBuilder,
) -> (Graph, Spans, Lowered) {
    let mut builder = Builder::new(source, &declared.headers, &declared.names, graph);
    for (index, (item, params)) in items.iter().zip(&declared.parameters).enumerate() {
        let built = builder.build(index, *item, params);
        builder.lowered.built.push(built);
    }
    builder
        .graph
        .set_unions(builder.source.unions.borrow().clone());
    let graph = builder.graph.finish();
    let spans = builder.spans.finish(&graph);
    let mut lowered = builder.lowered;
    lowered.references.append(&mut source.references);
    lowered
        .references
        .sort_unstable_by_key(|occurrence| occurrence.range.start());
    lowered.references.dedup();
    lowered
        .unresolved
        .sort_unstable_by_key(|range| range.start());
    (graph, spans, lowered)
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

/// What a call names.
#[derive(Clone, Copy)]
enum Target {
    Function(FunctionId),
    Type(DeclId),
    /// Reported where it was resolved, or ambiguous.
    Unknown,
}

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
    headers: &'a [Header],
    names: &'a NameMap<'s, Named>,
    graph: GraphBuilder,
    spans: SpansBuilder,
    lowered: Lowered,
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
    /// Scratch a version merge fills, kept across merges.
    merge_values: Vec<(NodeId, NodeId)>,
    merge_inputs: Vec<(NodeId, TextRange)>,
    merge_contexts: Vec<NodeId>,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
        source: &'a mut Source<'s>,
        headers: &'a [Header],
        names: &'a NameMap<'s, Named>,
        graph: GraphBuilder,
    ) -> Self {
        let nodes = source.tree.len();
        Self {
            source,
            headers,
            names,
            graph,
            spans: SpansBuilder::new(nodes),
            lowered: Lowered {
                built: Vec::with_capacity(headers.len()),
                typed: Vec::with_capacity(nodes),
                calls: Vec::new(),
                called: Vec::new(),
                entered: Vec::new(),
                obligations: Vec::new(),
                fallthroughs: vec![None; headers.len()],
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
            merge_values: Vec::new(),
            merge_inputs: Vec::new(),
            merge_contexts: Vec::new(),
        }
    }

    fn build(&mut self, owner: usize, item: ast::FnItem, parameters: &[Parameter<'s>]) -> bool {
        self.owner = u32::try_from(owner).expect("function count fits u32");
        self.has_failed = false;
        self.depth = 0;
        self.regions.clear();
        self.locals.clear();
        self.versions.clear();
        self.mutable_locals.clear();
        let header = &self.headers[owner];
        let item_node = header.item;
        let tree = self.source.tree;
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
        let run = self.graph.open_run(FunctionId::new(owner));
        let entry = self.push(item_node, Op::Entry, &[], None);
        for (index, param) in parameters.iter().enumerate() {
            let index = u32::try_from(index).expect("parameter count fits u32");
            let name = param.name.map(|(_, node)| self.source.range(node));
            let ty = param.ty.filter(|_| !param.is_duplicate);
            let node = self.push(param.node, Op::Param { index, ty }, &[], name);
            self.has_failed |= ty.is_none();
            if let (Some((name, _)), Some(range)) = (param.name, name) {
                self.bind(name, node, BindingKind::Param, range, body_range.start());
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
        // A failed parameter does not erase a declared result; the body is still held to it.
        let declared = declared.declared();
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
        if is_whole {
            self.unused();
        }
        is_whole
    }

    /// Only after a whole build: a walk that stopped early leaves reads unresolved.
    fn unused(&mut self) {
        if self.locals.iter().all(|local| local.is_read) {
            return;
        }
        let taken: HashSet<&str, FxBuildHasher> =
            self.locals.iter().map(|local| local.name).collect();
        for local in &self.locals {
            if local.is_read {
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
                && !self.names.contains_key(renamed.as_str())
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
        self.spans.annotate(node, self.source.range(annotation));
    }

    fn completes_input(&mut self, node: NodeId, index: usize) {
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
            Op::Call(function) => {
                !matches!(self.headers[function.index()].result, HeaderResult::None)
            }
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

    /// The function a call to `target` is held to: one with parameter types.
    fn callee(&self, target: Target) -> Option<(FunctionId, &'a Header)> {
        let Target::Function(target) = target else {
            return None;
        };
        self.graph.param_types(target)?;
        Some((target, &self.headers[target.index()]))
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
        let is_mutable = matches!(kind, BindingKind::Let { is_mutable: true });
        let end = self.scope_ends[self.depth - 1];
        let from = from.min(end);
        let binding = BindingId::new(self.lowered.bindings.len());
        self.lowered
            .bindings
            .push(Binding::new(range, kind, node, TextRange::new(from, end)));
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
        let mut chain = Vec::new();
        let mut leaf = node;
        while let Some(left) = self.left_operand(leaf) {
            chain.push(leaf);
            leaf = left;
        }
        let mut value = self.lower_one(leaf, None);
        while let Some(link) = chain.pop() {
            value = self.lower_one(link, Some(value));
        }
        value
    }

    /// The operand `node` lowers before anything of its own: an operator's or a field's left side.
    fn left_operand(&self, node: NodeIdx) -> Option<NodeIdx> {
        use ast::{Expr, Stmt};

        let tree = self.source.tree;
        match Stmt::cast(tree, node)? {
            Stmt::Expr(Expr::BinaryExpr(expr)) => {
                let op = expr.op(tree, self.source.lexed())?;
                if eager(op).is_none() && tree.has_error(node) {
                    return None;
                }
                expr.lhs(tree).map(|lhs| lhs.node())
            }
            Stmt::Expr(Expr::FieldExpr(expr)) => expr.base(tree).map(|base| base.node()),
            _ => None,
        }
    }

    /// `left` is the lowered left operand `left_operand` named, when there is one.
    fn lower_one(&mut self, node: NodeIdx, left: Option<Value>) -> Value {
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
            Stmt::DiscardStmt(discard) => {
                let value = discard.value(tree).map(|value| value.node());
                self.through(node, value, damaged)
            }
            Stmt::ReturnStmt(return_) => self.return_(return_, damaged),
            Stmt::Expr(Expr::Block(_)) => self.block(node),
            Stmt::Expr(Expr::IfExpr(branch)) => self.if_(branch),
            Stmt::Expr(
                Expr::ForExpr(_) | Expr::MatchExpr(_) | Expr::NameRef(_) | Expr::LiteralExpr(_),
            ) if damaged => self.holed(node),
            Stmt::Expr(Expr::ForExpr(expr)) => self.for_(expr),
            Stmt::Expr(Expr::MatchExpr(expr)) => self.match_(expr),
            Stmt::Expr(Expr::NameRef(name)) => self.name_ref(name),
            Stmt::Expr(Expr::LiteralExpr(literal)) => self.literal(literal),
            Stmt::Expr(Expr::BinaryExpr(expr)) => match expr.op(tree, self.source.lexed()) {
                None => self.holed(node),
                Some(op) => match eager(op) {
                    Some(op) => self.binary(expr, op, damaged, left),
                    None if damaged => self.holed(node),
                    None => self.lazy(expr, op == sumi_syntax::BinaryOp::And, left),
                },
            },
            Stmt::Expr(Expr::PrefixExpr(expr)) => self.prefix(expr, damaged),
            Stmt::Expr(Expr::ParenExpr(paren)) => {
                let inner = paren.inner(tree).map(|inner| inner.node());
                self.through(node, inner, damaged)
            }
            Stmt::Expr(Expr::CallExpr(call)) => self.call(call, damaged),
            Stmt::Expr(Expr::FieldExpr(expr)) => self.field(expr, damaged, left),
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
                self.lowered.unresolved.push(self.source.range(inner));
                continue;
            }
            if let Some(local) = self.lookup(name) {
                self.refer(
                    inner,
                    Symbol::Local(self.locals[local.index()].binding),
                    false,
                );
            } else if let Some(Named::Function(id)) = self.names.get(name) {
                self.refer(inner, Symbol::Function(*id), false);
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
        let target = assignment
            .target(tree)
            .and_then(|target| self.assignment_target(target));
        let value = assignment.value(tree).map(|value| self.lower(value.node()));
        let value = self.present(node, value);
        let assigned = match target {
            Some(local) => self.push_over(
                node,
                Op::Assign,
                &[value.input()],
                References::Version(self.locals[local.index()].declaration),
                None,
                &[],
            ),
            None => self.push(node, Op::Hole, &[value.input()], None),
        };
        self.bottoms[node.to_usize()] = value.completes;
        if value.completes {
            self.completes_input(assigned, 0);
        } else if let Some(local) = target
            && self.is_typed(assigned)
        {
            self.versions.set(local, assigned);
        }
        if damaged || target.is_none() || !value.is_valid || !self.is_typed(assigned) {
            self.fail();
        }
        self.value(node, assigned, value.control, value.completes)
    }

    /// A discard or parentheses: the value is the child's, read at `node`.
    fn through(&mut self, node: NodeIdx, child: Option<NodeIdx>, damaged: bool) -> Value {
        let Some(child) = child else {
            return self.holed(node);
        };
        let value = self.lower(child);
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

    fn name_ref(&mut self, name: ast::NameRef) -> Value {
        let node = name.node();
        let name = self.source.text(node);
        let Some(local) = self.lookup(name) else {
            if let Some(named) = self.names.get(name) {
                let what = match *named {
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
        } else if !completes && matches!(op, BinaryOp::Arith(ArithOp::Div | ArithOp::Rem)) {
            self.lowered.obligations.push(Obligation {
                owner: self.owner,
                node,
                divisor: rhs.node,
                context: self.context(),
            });
        }
        self.value(node, id, control, completes)
    }

    /// `lhs` is the lowered left operand, which a whole operator has.
    fn lazy(&mut self, expr: ast::BinaryExpr, is_and: bool, lhs: Option<Value>) -> Value {
        let tree = self.source.tree;
        let node = expr.node();
        let at = self.source.range(node);
        let whole = "a whole operator has its operands";
        let lhs_node = expr.lhs(tree).expect(whole).node();
        let rhs_node = expr.rhs(tree).expect(whole).node();
        let lhs = lhs.expect(whole);
        self.advance(&lhs);
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
        let (rhs, state) = self.region(region, Some((lhs_node, is_and)), |this| {
            this.lower(rhs_node)
        });
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
        if !lhs.is_valid {
            self.fail();
            return value;
        }
        if lhs.completes {
            self.completes_input(id, 0);
            self.bottoms[node.to_usize()] = true;
            value.completes = true;
            value.has_scalar_tail = false;
            return value;
        }
        if !rhs.is_valid {
            self.fail();
            return value;
        }
        if rhs.completes {
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
        value
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
                    match self.names.get(name).copied() {
                        Some(Named::Type(decl)) => {
                            self.refer(member, Symbol::Type(decl), false);
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

    fn assignment_target(&mut self, target: ast::Expr) -> Option<LocalId> {
        let target = self.source.peel(target);
        let ast::Expr::NameRef(name) = target else {
            self.source.error(
                target.node(),
                codes::INVALID_ASSIGNMENT_TARGET,
                "assignment target must be a mutable local name",
                None,
            );
            return None;
        };
        let text = self.source.text(name.node());
        let Some(local) = self.lookup(text) else {
            if let Some(named) = self.names.get(text) {
                let what = match *named {
                    Named::Function(id) => {
                        self.refer(name.node(), Symbol::Function(id), true);
                        "function"
                    }
                    Named::Type(id) => {
                        self.refer(name.node(), Symbol::Type(id), true);
                        "type"
                    }
                    Named::Ambiguous => "name",
                };
                self.source.error(
                    name.node(),
                    codes::INVALID_ASSIGNMENT_TARGET,
                    format!("{what} `{text}` is not assignable"),
                    None,
                );
            } else {
                self.source.error(
                    name.node(),
                    codes::UNKNOWN_NAME,
                    format!("unknown name `{text}`"),
                    None,
                );
            }
            return None;
        };
        self.refer(
            name.node(),
            Symbol::Local(self.locals[local.index()].binding),
            true,
        );
        if !self.versions.is_mutable(local) {
            let declaration = self.locals[local.index()].declaration;
            self.source.error(
                name.node(),
                codes::IMMUTABLE_ASSIGNMENT,
                format!("cannot assign to immutable local `{text}`"),
                self.spans
                    .name(declaration)
                    .map(|range| (range, "declared here")),
            );
            return None;
        }
        self.locals[local.index()].is_assigned = true;
        Some(local)
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
        match self.names.get(name) {
            Some(Named::Function(target)) => {
                let target = *target;
                self.refer(node, Symbol::Function(target), false);
                Target::Function(target)
            }
            Some(Named::Type(decl)) => {
                let decl = *decl;
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

    /// Every argument is read, arity aside: the typing holds each to its parameter. A damaged
    /// list is not yet the wrong length, and its labels are not yet in order.
    fn call(&mut self, call: ast::CallExpr, damaged: bool) -> Value {
        let tree = self.source.tree;
        let node = call.node();
        let target = match call.callee(tree) {
            Some(callee) => self.target(callee.node()),
            None => Target::Unknown,
        };
        // The arguments before any garbage: the ones whose position is reliable.
        let mut args: Vec<(ast::Arg, Value)> = Vec::new();
        if let Some(list) = call.arg_list(tree) {
            for child in tree.children(list.node()) {
                let Some((arg, value)) =
                    ast::Arg::cast(tree, child).and_then(|arg| Some((arg, arg.value(tree)?)))
                else {
                    break;
                };
                let value = self.lower(value.node());
                self.advance(&value);
                args.push((arg, value));
            }
        }
        if let Target::Type(decl) = target
            && !damaged
        {
            return self.construct(call, decl, &args);
        }
        let context = self.context();
        let callee = self.callee(target);
        if let Some((target, _)) = callee {
            self.lowered.entered.push((context, target));
        }
        let mut is_labeled = false;
        if !damaged {
            for (arg, _) in &args {
                // A label on an argument to a name that resolved to nothing is reported there.
                if let Some(label) = arg.label(tree)
                    && let Target::Function(function) = target
                {
                    let item = self.headers[function.index()].item;
                    self.source.error(
                        label.node(),
                        codes::LABELED_ARGUMENT,
                        "a function's arguments take no labels",
                        Some((self.source.range(item), "declared here")),
                    );
                    is_labeled = true;
                }
            }
            if let Some((id, function)) = callee
                && let arity = self.arity(id)
                && args.len() != arity
            {
                self.source.error(
                    node,
                    codes::ARITY,
                    format!("expected {arity} arguments, found {}", args.len()),
                    Some((self.source.range(function.item), "declared here")),
                );
            }
        }
        let inputs: Vec<(NodeId, TextRange)> =
            args.iter().map(|(_, value)| value.input()).collect();
        let whole = callee.filter(|&(id, _)| !damaged && !is_labeled && self.whole(id, &inputs));
        let op = callee.map_or(Op::Hole, |(id, _)| Op::Call(id));
        let id = self.push(node, op, &inputs, None);
        if let Some((target, _)) = callee
            && self.is_typed(id)
        {
            self.lowered.called.push((id, target));
        }
        let at = self.source.range(node);
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
        let value = self.value(node, id, control, completes);
        if damaged || !is_valid {
            self.fail();
            return value;
        }
        let Some((target, function)) = whole else {
            self.fail();
            return value;
        };
        self.lowered.calls.push(Call {
            node: id,
            caller: FunctionId::new(self.owner as usize),
            callee: target,
            context,
        });
        if !completes && matches!(function.result, HeaderResult::None) {
            self.fail();
        }
        value
    }

    /// Fields are stored in declaration order; argument controls run in source order.
    fn construct(
        &mut self,
        call: ast::CallExpr,
        decl: DeclId,
        args: &[(ast::Arg, Value)],
    ) -> Value {
        let tree = self.source.tree;
        let node = call.node();
        let fields = self.source.decls[decl.index()].fields.len();
        let type_name = self.source.decls[decl.index()].name;
        let declared = self.source.decls[decl.index()]
            .name_node
            .map(|name| (self.source.range(name), "declared here"));
        let mut given: Vec<Option<(Value, NodeIdx)>> = vec![None; fields];
        // A type with a field of no type is reported at its declaration.
        let mut is_damaged = self.graph.decl(decl).field_types().is_none();
        for &(arg, value) in args {
            let Some(label) = arg.label(tree) else {
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
                        self.refer(label.node(), Symbol::Field(decl, index as u32), false);
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
