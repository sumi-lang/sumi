//! Lowering of one file to the graph: names, structure, and holes. The walk rejects nothing on type
//! grounds; it fails only on names, syntax, and unsupported constructs, and leaves each as a hole.

use std::collections::HashMap;
use std::collections::hash_map::Entry;

use rustc_hash::FxBuildHasher;
use sumi_frontend::{DiagnosticCode, Label};
use sumi_graph::GraphBuilder;
use sumi_lexer::{LexedFile, RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    Literal, NodeIdx, PrefixOp, SyntaxTree,
    ast::{self, AstNode, Clean, CleanExpr, CleanStmt, View},
};

use crate::codes;
use crate::lattice::Claim;
use crate::typing::Typing;
use crate::*;

type NameMap<'s, V> = HashMap<&'s str, V, FxBuildHasher>;

#[derive(Clone, Copy)]
enum Named {
    Function(FunctionId),
    Ambiguous(FunctionId),
}

impl Named {
    fn first(self) -> FunctionId {
        match self {
            Self::Function(id) | Self::Ambiguous(id) => id,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Header {
    pub name: Option<TextRange>,
    /// `None` when the parameter list is not whole.
    pub callee: Option<Callee>,
    pub result: HeaderResult,
    pub item: NodeIdx,
}

#[derive(Clone, Copy)]
pub(crate) enum HeaderResult {
    /// The declaration is damaged; an omitted annotation is never this.
    None,
    /// The node is the annotation, or the whole item for a bare block body.
    Declared(Ty, NodeIdx),
    Inferred,
}

/// A division whose divisor must exclude zero under `context`.
pub(crate) struct Obligation {
    pub owner: u32,
    pub node: NodeIdx,
    pub divisor: NodeId,
    pub context: NodeId,
}

pub(crate) struct Call {
    pub node: NodeId,
    pub caller: FunctionId,
    pub callee: FunctionId,
    pub context: NodeId,
}

#[derive(Clone, Copy)]
pub(crate) struct Fallthrough {
    pub value: NodeId,
    pub at: TextRange,
}

pub(crate) struct Lowered {
    /// By function.
    pub built: Vec<bool>,
    /// By node.
    pub typed: Vec<bool>,
    /// Whole calls only, in definition order.
    pub calls: Vec<Call>,
    /// (context, callee) of every call whose callee has a whole parameter list, whole call or not.
    pub entered: Vec<(NodeId, FunctionId)>,
    pub obligations: Vec<Obligation>,
    pub fallthroughs: Vec<Option<Fallthrough>>,
}

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
    pub fn lexed(&self) -> &'s LexedFile {
        self.parsed.lexed()
    }
    pub fn range(&self, node: NodeIdx) -> TextRange {
        self.tree.byte_range(node, self.lexed())
    }
    pub fn text(&self, node: NodeIdx) -> &'s str {
        self.tree
            .byte_range(node, self.lexed())
            .text(self.parsed.source())
    }
    fn name(&self, name: Option<ast::Name>) -> Option<(&'s str, NodeIdx)> {
        let node = name?.clean(self.tree, self.lexed())?.node();
        Some((self.text(node), node))
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
        at: TextRange,
        expected: Ty,
        actual: Ty,
        related: Option<(TextRange, &'static str)>,
    ) {
        let related = related.map(|(range, message)| (range, Box::from(message)));
        self.report(
            at,
            codes::TYPE_MISMATCH,
            format!("expected {expected}, found {actual}"),
            related,
        );
    }
    /// `message` receives the claimed types joined as a list, in source order.
    pub fn conflict(
        &mut self,
        at: TextRange,
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
        self.report(at, code, message(joined), labels);
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
    fn tokens(&self, start: RawIdx, end: RawIdx) -> impl Iterator<Item = SyntaxKind> + '_ {
        start
            .until(end)
            .map(|raw| self.lexed().kind(raw))
            .filter(|kind| !kind.is_trivia())
    }
    fn peel(&self, mut expr: ast::Expr) -> ast::Expr {
        while let ast::Expr::ParenExpr(paren) = expr {
            let Some(paren) = paren.clean(self.tree, self.lexed()) else {
                break;
            };
            expr = paren.inner();
        }
        expr
    }
}

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
    ty: Option<Ty>,
    duplicate: bool,
}

pub(crate) struct Declarations<'s> {
    pub headers: Vec<Header>,
    names: NameMap<'s, Named>,
    parameters: Vec<Vec<Parameter<'s>>>,
}

/// In item order, so a `FunctionId` indexes `items`.
pub(crate) fn declare<'s>(
    source: &mut Source<'s>,
    items: &[ast::FnItem],
    graph: &mut GraphBuilder,
) -> Declarations<'s> {
    let tree = source.tree;
    let mut names: NameMap<Named> = NameMap::with_capacity_and_hasher(items.len(), FxBuildHasher);
    let mut parameters = Vec::with_capacity(items.len());
    let mut headers = Vec::with_capacity(items.len());
    for item in items {
        let name = source.name(item.name(tree));
        let id = graph.function();
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
        let whole_list = list.filter(|list| !tree.has_error(list.node()));
        let mut params: Vec<Parameter> = Vec::new();
        if let Some(list) = list {
            for param in list.params(tree) {
                // A parameter without a type is a syntax error the parser already reported.
                let ty = param.type_ref(tree).and_then(|ty| source.ty(ty));
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
            // A missing annotation may be damage: only an empty gap or the expression-body `=` says
            // it was left out.
            let gap = whole_list.map(|list| {
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
        // A whole list has every parameter typed, a repeated name aside.
        let callee = whole_list
            .and_then(|_| params.iter().map(|p| p.ty).collect::<Option<Box<[Ty]>>>())
            .map(|types| graph.declare(id, types));
        headers.push(Header {
            name: name.map(|(_, node)| source.range(node)),
            callee,
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

pub(crate) fn lower<'s>(
    source: &mut Source<'s>,
    items: &[ast::FnItem],
    declared: &Declarations<'s>,
    graph: GraphBuilder,
) -> (Graph, Lowered) {
    let mut builder = Builder::new(source, &declared.headers, &declared.names, graph);
    for (index, (item, params)) in items.iter().zip(&declared.parameters).enumerate() {
        let built = builder.build(index, *item, params);
        builder.lowered.built.push(built);
    }
    (builder.graph.finish(), builder.lowered)
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

/// A `let` binds at `Work::Finish`, after its initializer, so the initializer reads any outer
/// binding of the name.
type Scope<'s> = NameMap<'s, NodeId>;

enum Finish {
    Let(Clean<ast::LetStmt>),
    Discard(Clean<ast::DiscardStmt>),
    NameRef(Clean<ast::NameRef>),
    Literal(Clean<ast::LiteralExpr>),
    Paren(Clean<ast::ParenExpr>),
    Prefix {
        expr: Clean<ast::PrefixExpr>,
        neg: bool,
    },
    Binary {
        expr: Clean<ast::BinaryExpr>,
        op: BinaryOp,
    },
}

/// `&&` when `and`, else `||`, with its expression.
#[derive(Clone, Copy)]
struct LazyOp {
    expr: Clean<ast::BinaryExpr>,
    and: bool,
}

enum Work {
    Enter(NodeIdx),
    Advance(NodeIdx),
    Finish(Finish),
    /// Damaged or not: a block runs its statements.
    Block(NodeIdx),
    Unused(NodeIdx),
    Call {
        call: Clean<ast::CallExpr>,
        target: Option<FunctionId>,
    },
    Branches(Clean<ast::IfExpr>),
    Rhs(LazyOp),
    Join {
        branch: Clean<ast::IfExpr>,
        then: RegionId,
        else_: Option<RegionId>,
    },
    Lazy {
        expr: LazyOp,
        rhs: RegionId,
    },
    Push {
        region: RegionId,
        guard: (NodeIdx, bool),
    },
    Pop {
        region: RegionId,
        root: NodeIdx,
    },
    Return(Clean<ast::ReturnStmt>),
}

fn enter_each(work: &mut Vec<Work>, nodes: impl Iterator<Item = NodeIdx>) {
    let base = work.len();
    for node in nodes {
        work.push(Work::Enter(node));
        work.push(Work::Advance(node));
    }
    work[base..].reverse();
}

#[derive(Clone, Copy)]
struct Form {
    valid: bool,
    completes: bool,
}

impl Form {
    const SCALAR: Self = Self {
        valid: true,
        completes: false,
    };

    fn scalar(self) -> bool {
        self.valid && !self.completes
    }
}

struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    headers: &'a [Header],
    names: &'a NameMap<'s, Named>,
    graph: GraphBuilder,
    lowered: Lowered,
    nodes_of: Vec<Option<NodeId>>,
    owner: u32,
    failed: bool,
    /// Open regions, innermost last, each with where its refinements begin in `refinements`.
    regions: Vec<(RegionId, usize, NodeId)>,
    /// (defining node, the node its reads see) for the open regions, innermost last.
    refinements: Vec<(NodeId, NodeId)>,
    /// The first `depth` scopes are open, innermost last.
    scopes: Vec<Scope<'s>>,
    depth: usize,
    work: Vec<Work>,
    inputs: Vec<(NodeId, TextRange)>,
    controls: Vec<Option<NodeId>>,
    bottoms: Vec<bool>,
    returns: Vec<(NodeId, TextRange)>,
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
            lowered: Lowered {
                built: Vec::with_capacity(headers.len()),
                typed: Vec::with_capacity(nodes),
                calls: Vec::new(),
                entered: Vec::new(),
                obligations: Vec::new(),
                fallthroughs: vec![None; headers.len()],
            },
            nodes_of: vec![None; nodes],
            owner: 0,
            failed: false,
            regions: Vec::new(),
            refinements: Vec::new(),
            scopes: Vec::new(),
            depth: 0,
            work: Vec::new(),
            inputs: Vec::new(),
            controls: vec![None; nodes],
            bottoms: vec![false; nodes],
            returns: Vec::new(),
        }
    }
    /// Whether the body built whole.
    fn build(&mut self, owner: usize, item: ast::FnItem, parameters: &[Parameter<'s>]) -> bool {
        self.owner = u32::try_from(owner).expect("function count fits u32");
        self.failed = false;
        self.depth = 0;
        self.open_scope();
        self.regions.clear();
        self.refinements.clear();
        self.returns.clear();
        let header = &self.headers[owner];
        let item_node = header.item;
        let run = self.graph.open_run(FunctionId::new(owner));
        let entry = self.push(item_node, Op::Entry, &[], None);
        for (index, param) in parameters.iter().enumerate() {
            let index = u32::try_from(index).expect("parameter count fits u32");
            let name = param.name.map(|(_, node)| self.source.range(node));
            let ty = param.ty.filter(|_| !param.duplicate);
            let node = self.push(param.node, Op::Param { index, ty }, &[], name);
            self.failed |= ty.is_none();
            if let Some((name, _)) = param.name {
                self.bind(name, node);
            } else {
                self.failed = true;
            }
        }
        let declared = header.result;
        self.failed |= header.callee.is_none() || matches!(declared, HeaderResult::None);
        let tree = self.source.tree;
        let region = self.graph.open(entry);
        self.graph.enter(region);
        self.regions.push((region, 0, entry));
        let root_node = item.body(tree).map(|body| body.node());
        let explicit_tail = root_node.and_then(|root| self.explicit_tail(root));
        if let Some(root_node) = root_node {
            let mut work = std::mem::take(&mut self.work);
            work.push(Work::Enter(root_node));
            while let Some(task) = work.pop() {
                let built = match task {
                    Work::Finish(finish) => self.finish(finish),
                    Work::Block(node) => self.block(node),
                    Work::Call { call, target } => self.call(call, target),
                    Work::Join {
                        branch,
                        then,
                        else_,
                    } => self.join(branch, then, else_),
                    Work::Lazy { expr, rhs } => self.lazy(expr, rhs),
                    Work::Enter(node) => {
                        self.enter(node, &mut work);
                        continue;
                    }
                    Work::Advance(node) => {
                        self.advance(node);
                        continue;
                    }
                    Work::Unused(node) => {
                        let input = self.input(node);
                        let unused = self.place(Op::Unused, &[input], input.1, None);
                        if self.form(node).completes {
                            self.completes_input(unused, 0);
                        }
                        continue;
                    }
                    Work::Branches(branch) => {
                        self.branches(branch, &mut work);
                        continue;
                    }
                    Work::Rhs(expr) => {
                        self.rhs(expr, &mut work);
                        continue;
                    }
                    Work::Push { region, guard } => {
                        self.regions.push((
                            region,
                            self.refinements.len(),
                            self.graph.context(region),
                        ));
                        self.graph.enter(region);
                        self.refine(guard.0, guard.1);
                        continue;
                    }
                    Work::Pop { region, root } => {
                        let result = self.node_of(root);
                        self.graph.close_with_control(
                            region,
                            result,
                            !self.form(root).completes,
                            self.control(root),
                        );
                        let (_, keep, _) = self
                            .regions
                            .pop()
                            .expect("a region opened before it closes");
                        self.refinements.truncate(keep);
                        continue;
                    }
                    Work::Return(return_) => self.return_(return_),
                };
                self.failed |= built.is_none();
            }
            self.work = work;
        }
        let root = root_node.and_then(|root| self.form(root).valid.then(|| self.node_of(root)));
        let body = match root_node {
            Some(root) => self.input(root),
            None => {
                let hole = self.push(item_node, Op::Hole, &[], None);
                (hole, self.source.range(item_node))
            }
        };
        let control = root_node.and_then(|root| self.control(root));
        let fallthrough = if self.returns.is_empty() {
            None
        } else {
            control
                .map(|control| self.place(Op::Sequence, &[(control, body.1), body], body.1, None))
        };
        self.graph.close_with_control(
            region,
            body.0,
            root_node.is_none_or(|root| !self.form(root).completes),
            control,
        );
        self.regions.pop();
        // A failed parameter does not erase a declared result; the body is still held to it.
        let value = match (self.returns.is_empty(), declared) {
            (true, HeaderResult::Declared(ty, node)) => self.push(
                node,
                Op::Copy {
                    declared: Some((ty, self.source.range(node))),
                },
                &[body],
                None,
            ),
            (true, HeaderResult::Inferred | HeaderResult::None) => body.0,
            (false, declared) => {
                let node = match declared {
                    HeaderResult::Declared(_, node) => node,
                    HeaderResult::Inferred | HeaderResult::None => item_node,
                };
                let declared = match declared {
                    HeaderResult::Declared(ty, node) => Some((ty, self.source.range(node))),
                    HeaderResult::Inferred | HeaderResult::None => None,
                };
                let mut outcomes = Vec::with_capacity(self.returns.len() + 1);
                outcomes.push((fallthrough.unwrap_or(body.0), body.1));
                outcomes.extend(self.returns.iter().copied());
                let result = self.push(node, Op::Result { declared }, &outcomes, None);
                let completes = root_node.is_none_or(|root| self.form(root).completes);
                let fallthrough = explicit_tail
                    .filter(|&tail| self.form(tail).scalar())
                    .or_else(|| {
                        root_node.filter(|&root| declared.is_some() && self.form(root).scalar())
                    });
                if (declared.is_some() || completes)
                    && let Some(fallthrough) = fallthrough
                {
                    self.lowered.fallthroughs[self.owner as usize] = Some(Fallthrough {
                        value: self.node_of(fallthrough),
                        at: self.source.range(fallthrough),
                    });
                }
                if completes {
                    self.completes_input(result, 0);
                }
                result
            }
        };
        self.graph.close_run(run, region, value);
        !self.failed && root.is_some()
    }
    fn push(
        &mut self,
        node: NodeIdx,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        name: Option<TextRange>,
    ) -> NodeId {
        self.push_over(node, op, inputs, name, &[])
    }
    /// `results` are those of the regions `op` holds.
    fn push_over(
        &mut self,
        node: NodeIdx,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        name: Option<TextRange>,
        results: &[NodeId],
    ) -> NodeId {
        let typed = self.follows(&op, inputs, results);
        let id = self.graph.push(op, inputs, self.source.range(node), name);
        self.lowered.typed.push(typed);
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
        let typed = self.follows(&op, inputs, &[]);
        let id = self.graph.push(op, inputs, origin, name);
        self.lowered.typed.push(typed);
        id
    }
    fn completes_input(&mut self, node: NodeId, index: usize) {
        self.graph.complete_input(node, index);
    }
    /// Whether a node of `op` over `inputs`, and over the regions with `results`, carries a value
    /// the typing follows.
    fn follows(&self, op: &Op, inputs: &[(NodeId, TextRange)], results: &[NodeId]) -> bool {
        let typed = |node: NodeId| self.lowered.typed[node.index()];
        match *op {
            Op::Hole | Op::Unused => false,
            Op::Entry
            | Op::Then
            | Op::Else
            | Op::Return
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After
            | Op::Result { declared: Some(_) }
            | Op::Copy { declared: Some(_) } => true,
            Op::Result { declared: None } => inputs.iter().all(|&(input, _)| typed(input)),
            Op::Param { ty, .. } => ty.is_some(),
            Op::Call(callee) => {
                let function = self.graph.callable(callee).function;
                self.whole(callee, inputs)
                    && !matches!(self.headers[function.index()].result, HeaderResult::None)
            }
            Op::And { .. } | Op::Or { .. } | Op::Join { .. } => {
                typed(inputs[0].0) && results.iter().all(|&result| typed(result))
            }
            _ => inputs.iter().all(|&(input, _)| typed(input)),
        }
    }
    /// A whole call has an argument per parameter, none a hole.
    fn whole(&self, callee: Callee, inputs: &[(NodeId, TextRange)]) -> bool {
        self.graph.callable(callee).params.len() == inputs.len()
            && inputs
                .iter()
                .all(|&(input, _)| self.lowered.typed[input.index()])
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
    fn node_of(&mut self, node: NodeIdx) -> NodeId {
        match self.nodes_of[node.to_usize()] {
            Some(id) => id,
            None => self.push(node, Op::Hole, &[], None),
        }
    }
    fn input(&mut self, node: NodeIdx) -> (NodeId, TextRange) {
        (self.node_of(node), self.source.range(node))
    }
    fn typed(&self, node: NodeIdx) -> Option<NodeId> {
        let id = self.nodes_of[node.to_usize()]?;
        self.lowered.typed[id.index()].then_some(id)
    }
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
    fn bind(&mut self, name: &'s str, node: NodeId) {
        self.scopes[self.depth - 1].insert(name, node);
    }
    fn lookup(&self, name: &str) -> Option<NodeId> {
        // An empty scope is common and would cost a hash to find nothing in.
        self.scopes[..self.depth]
            .iter()
            .rev()
            .filter(|scope| !scope.is_empty())
            .find_map(|scope| scope.get(name).copied())
    }
    fn current(&self, defined: NodeId) -> NodeId {
        self.refinements
            .iter()
            .rev()
            .find(|(local, _)| *local == defined)
            .map_or(defined, |(_, node)| *node)
    }
    fn context(&self) -> NodeId {
        self.regions.last().expect("a body runs in its region").2
    }
    fn explicit_tail(&self, root: NodeIdx) -> Option<NodeIdx> {
        match ast::Expr::cast(self.source.tree, root) {
            Some(ast::Expr::Block(_)) => self
                .source
                .tree
                .children(root)
                .last()
                .filter(|&node| ast::Expr::cast(self.source.tree, node).is_some()),
            Some(_) => Some(root),
            None => None,
        }
    }
    fn form(&self, node: NodeIdx) -> Form {
        Form {
            valid: self.typed(node).is_some(),
            completes: self.bottoms[node.to_usize()],
        }
    }
    fn control(&self, node: NodeIdx) -> Option<NodeId> {
        self.controls[node.to_usize()]
    }
    fn compose_control(
        &mut self,
        node: NodeIdx,
        parts: impl IntoIterator<Item = Option<NodeId>>,
    ) -> Option<NodeId> {
        let at = self.source.range(node);
        parts.into_iter().flatten().reduce(|before, value| {
            self.place(Op::Sequence, &[(before, at), (value, at)], at, None)
        })
    }
    fn advance(&mut self, node: NodeIdx) {
        let Some(control) = self.control(node) else {
            return;
        };
        let context = self.context();
        if matches!(self.graph.node(context).op, Op::After)
            && self.graph.inputs(context)[0] == control
        {
            return;
        }
        let at = self.source.range(node);
        let after = self.place(Op::After, &[(control, at), (context, at)], at, None);
        self.regions
            .last_mut()
            .expect("a body runs in its region")
            .2 = after;
    }
    /// The scope is as it was when the read was built: a region is entered right after its
    /// condition finishes.
    fn read(&self, node: NodeIdx) -> Option<NodeId> {
        let tree = self.source.tree;
        let ast::Expr::NameRef(name) = self.source.peel(ast::Expr::cast(tree, node)?) else {
            return None;
        };
        self.local(name)
    }
    /// The typed local `name` refers to.
    fn local(&self, name: ast::NameRef) -> Option<NodeId> {
        let defined = self.lookup(self.source.text(name.node()))?;
        self.lowered.typed[defined.index()].then_some(defined)
    }
    /// Narrow the locals `cond` compares, for `cond` holding in `sense`.
    fn refine(&mut self, cond: NodeIdx, sense: bool) {
        use sumi_syntax::BinaryOp::*;

        let tree = self.source.tree;
        let Some(expr) = ast::Expr::cast(tree, cond)
            .map(|expr| self.source.peel(expr))
            .and_then(|expr| expr.clean(tree, self.source.lexed()))
        else {
            return;
        };
        let node = expr.node();
        match expr {
            CleanExpr::PrefixExpr(prefix) => match prefix.op() {
                PrefixOp::Not => self.refine(prefix.operand().node(), !sense),
                PrefixOp::Neg => {}
            },
            CleanExpr::BinaryExpr(binary) => {
                let lhs = binary.lhs().node();
                let rhs = binary.rhs().node();
                let op = binary.op();
                match op {
                    And if sense => {
                        self.refine(lhs, sense);
                        self.refine(rhs, sense);
                    }
                    Or if !sense => {
                        self.refine(lhs, sense);
                        self.refine(rhs, sense);
                    }
                    Cmp(op) => {
                        let op = cmp(op);
                        for (side, other, local_is_lhs) in [(lhs, rhs, true), (rhs, lhs, false)] {
                            if let (Some(local), Some(value)) = (self.read(side), self.typed(other))
                            {
                                let inputs = [
                                    (self.current(local), self.source.range(side)),
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
                                self.refinements.push((local, read));
                            }
                        }
                    }
                    _ => {}
                }
            }
            CleanExpr::NameRef(name) => {
                if let Some(local) = self.local(name.view()) {
                    let at = self.source.range(node);
                    let inputs = [(self.current(local), at)];
                    let read = self.place(Op::Exactly(sense), &inputs, at, None);
                    self.refinements.push((local, read));
                }
            }
            _ => {}
        }
    }
    fn branches(&mut self, branch: Clean<ast::IfExpr>, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let cond = branch.condition().node();
        self.advance(cond);
        let then_node = branch.then_branch().node();
        let else_node = branch.else_branch(tree).map(|e| e.node());
        let parent = self.context();
        let condition = self.input(cond);
        let then = {
            let context = self.context_at(then_node, Op::Then, condition, parent);
            self.graph.open(context)
        };
        let else_ = else_node.map(|else_node| {
            let context = self.context_at(else_node, Op::Else, condition, parent);
            self.graph.open(context)
        });
        work.push(Work::Join {
            branch,
            then,
            else_,
        });
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
    fn rhs(&mut self, expr: LazyOp, work: &mut Vec<Work>) {
        let and = expr.and;
        let lhs = expr.expr.lhs().node();
        self.advance(lhs);
        let rhs = expr.expr.rhs().node();
        let parent = self.context();
        let op = if and { Op::Then } else { Op::Else };
        let left = self.input(lhs);
        let context = self.context_at(rhs, op, left, parent);
        let region = self.graph.open(context);
        work.push(Work::Lazy { expr, rhs: region });
        work.push(Work::Pop { region, root: rhs });
        work.push(Work::Enter(rhs));
        work.push(Work::Push {
            region,
            guard: (lhs, and),
        });
    }
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
        use ast::{Expr, Stmt};

        let tree = self.source.tree;
        let stmt = Stmt::cast(tree, node);
        let Some(clean) = stmt.and_then(|stmt| stmt.clean(tree, self.source.lexed())) else {
            match stmt {
                Some(Stmt::LetStmt(binding)) => self.damaged_let(binding),
                Some(Stmt::Expr(Expr::Block(_))) => {
                    self.failed = true;
                    self.block_statements(node, work);
                }
                _ if tree.has_error(node) => {
                    self.hole(node);
                    self.failed = true;
                }
                _ => self.unsupported(node),
            }
            return;
        };
        match clean {
            CleanStmt::LetStmt(binding) => {
                if binding.mutable() {
                    self.unsupported(node);
                    self.damaged_let(binding.view());
                    return;
                }
                work.push(Work::Finish(Finish::Let(binding)));
                work.push(Work::Enter(binding.initializer().node()));
            }
            CleanStmt::Expr(CleanExpr::Block(_)) => self.block_statements(node, work),
            CleanStmt::DiscardStmt(discard) => {
                work.push(Work::Finish(Finish::Discard(discard)));
                work.push(Work::Enter(discard.value().node()));
            }
            CleanStmt::Expr(CleanExpr::IfExpr(branch)) => {
                work.push(Work::Branches(branch));
                work.push(Work::Enter(branch.condition().node()));
            }
            CleanStmt::Expr(CleanExpr::BinaryExpr(expr)) => {
                let op = expr.op();
                let lhs = expr.lhs().node();
                let rhs = expr.rhs().node();
                match eager(op) {
                    Some(op) => {
                        work.push(Work::Finish(Finish::Binary { expr, op }));
                        work.push(Work::Enter(rhs));
                        work.push(Work::Advance(lhs));
                    }
                    None => work.push(Work::Rhs(LazyOp {
                        expr,
                        and: op == sumi_syntax::BinaryOp::And,
                    })),
                }
                work.push(Work::Enter(lhs));
            }
            CleanStmt::Expr(CleanExpr::PrefixExpr(expr)) => {
                let neg = expr.op() == PrefixOp::Neg;
                let peeled = self.source.peel(expr.operand());
                if neg
                    && let Expr::LiteralExpr(literal) = peeled
                    && literal.value(tree, self.source.lexed()) == Some(Literal::Int)
                {
                    if self.integer(node, literal.node(), true).is_none() {
                        self.failed = true;
                    }
                    return;
                }
                work.push(Work::Finish(Finish::Prefix { expr, neg }));
                work.push(Work::Enter(expr.operand().node()));
            }
            CleanStmt::Expr(CleanExpr::ParenExpr(paren)) => {
                work.push(Work::Finish(Finish::Paren(paren)));
                work.push(Work::Enter(paren.inner().node()));
            }
            CleanStmt::Expr(CleanExpr::CallExpr(call)) => {
                let callee = self.source.peel(call.callee());
                let target = match callee {
                    Expr::NameRef(name) => self.target(name.node()),
                    _ => {
                        self.unsupported(callee.node());
                        None
                    }
                };
                work.push(Work::Call { call, target });
                enter_each(work, call.arg_list().args(tree).map(|arg| arg.node()));
            }
            CleanStmt::Expr(CleanExpr::NameRef(name)) => {
                work.push(Work::Finish(Finish::NameRef(name)));
            }
            CleanStmt::Expr(CleanExpr::LiteralExpr(literal)) => {
                work.push(Work::Finish(Finish::Literal(literal)));
            }
            CleanStmt::ReturnStmt(return_) => {
                work.push(Work::Return(return_));
                if let Some(value) = return_.value(tree) {
                    work.push(Work::Advance(value.node()));
                    work.push(Work::Enter(value.node()));
                }
            }
            CleanStmt::Expr(CleanExpr::ClosureExpr(_)) | CleanStmt::AssignStmt(_) => {
                self.unsupported(node)
            }
        }
    }
    fn return_(&mut self, return_: Clean<ast::ReturnStmt>) -> Option<()> {
        let node = return_.node();
        let at = self.source.range(node);
        let value = return_.value(self.source.tree);
        let payload = match value {
            Some(value) => self.input(value.node()),
            None => {
                let unit = self.push(node, Op::Unit, &[(self.context(), at)], None);
                (unit, at)
            }
        };
        let value = value.map(|value| (value, self.form(value.node())));
        let returned = self.push(node, Op::Return, &[payload, (self.context(), at)], None);
        let control = self.compose_control(
            node,
            [
                value.and_then(|(value, _)| self.control(value.node())),
                Some(returned),
            ],
        );
        self.controls[node.to_usize()] = control;
        if value.is_some_and(|(_, form)| form.completes) {
            self.completes_input(returned, 0);
        } else {
            self.returns.push((returned, at));
        }
        if value.is_none_or(|(_, form)| form.valid) {
            self.bottoms[node.to_usize()] = true;
            Some(())
        } else {
            None
        }
    }
    /// A binding that cannot be built still takes its name, as a hole.
    fn damaged_let(&mut self, binding: ast::LetStmt) {
        let tree = self.source.tree;
        if let Some((name, name_node)) = self.source.name(binding.name(tree)) {
            let hole = self.push(
                binding.node(),
                Op::Hole,
                &[],
                Some(self.source.range(name_node)),
            );
            self.bind(name, hole);
        }
        self.failed = true;
    }
    fn block_statements(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        self.open_scope();
        work.push(Work::Block(node));
        let base = work.len();
        let mut children = tree.children(node).peekable();
        while let Some(child) = children.next() {
            let statement = children.peek().is_some() && ast::Expr::cast(tree, child).is_some();
            work.push(Work::Enter(child));
            if statement {
                work.push(Work::Unused(child));
            }
            work.push(Work::Advance(child));
        }
        work[base..].reverse();
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
    /// `None` for a malformed literal, which the lexer already reported.
    fn integer(&mut self, origin: NodeIdx, literal: NodeIdx, negative: bool) -> Option<NodeId> {
        let raw = self.source.tree.first_token(literal);
        if self
            .source
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
    fn block(&mut self, node: NodeIdx) -> Option<()> {
        let tree = self.source.tree;
        self.close_scope();
        let mut tail = None;
        let damaged = tree.has_error(node);
        let mut valid = !damaged;
        let mut bottom = false;
        let mut controls = Vec::new();
        let mut children = tree.children(node).peekable();
        while let Some(child) = children.next() {
            let expression = ast::Expr::cast(tree, child).is_some();
            if children.peek().is_none() && expression {
                tail = Some(child);
                controls.push(self.control(child));
                let form = self.form(child);
                valid &= form.valid;
                bottom |= form.completes;
                break;
            }
            controls.push(self.control(child));
            let form = self.form(child);
            if !form.valid {
                self.node_of(child);
                valid = false;
            }
            bottom |= form.completes;
        }
        self.controls[node.to_usize()] = self.compose_control(node, controls);
        // A damaged block may have lost its tail to recovery, so without one it is a hole, not
        // unit.
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
                let at = self.source.range(node);
                self.push(node, Op::Unit, &[(context, at)], None);
            }
        }
        if bottom {
            self.bottoms[node.to_usize()] = true;
        }
        if !valid || damaged {
            return None;
        }
        if !bottom {
            self.typed(node)?;
        }
        Some(())
    }
    fn finish(&mut self, finish: Finish) -> Option<()> {
        let tree = self.source.tree;
        match finish {
            Finish::Let(binding) => {
                let name = binding.name().node();
                let value = self.input(binding.initializer().node());
                let annotation = binding.type_ref(tree);
                let declared = annotation.and_then(|annotation| {
                    let ty = self.source.ty(annotation)?;
                    Some((ty, self.source.range(annotation.node())))
                });
                let op = match (annotation, declared) {
                    (Some(_), None) => Op::Hole,
                    _ => Op::Copy { declared },
                };
                let copy = self.push(binding.node(), op, &[value], Some(self.source.range(name)));
                self.bind(self.source.text(name), copy);
                let initializer = binding.initializer().node();
                self.controls[binding.node().to_usize()] = self.control(initializer);
                let form = self.form(initializer);
                self.bottoms[binding.node().to_usize()] = form.completes;
                if !form.valid || !self.lowered.typed[copy.index()] {
                    return None;
                }
                if form.completes {
                    self.completes_input(copy, 0);
                    return Some(());
                }
            }
            Finish::Discard(discard) => {
                let value = discard.value().node();
                let discarded = self.node_of(value);
                self.nodes_of[discard.node().to_usize()] = Some(discarded);
                self.controls[discard.node().to_usize()] = self.control(value);
                let form = self.form(value);
                self.bottoms[discard.node().to_usize()] = form.completes;
                if !form.valid {
                    return None;
                }
                if form.completes {
                    return Some(());
                }
                self.typed(value)?;
            }
            Finish::NameRef(name) => {
                let node = name.node();
                let name = self.source.text(node);
                match self.lookup(name) {
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
            Finish::Literal(literal) => {
                let node = literal.node();
                match literal.value() {
                    Literal::Int => {
                        self.integer(node, node, false)?;
                    }
                    Literal::True => {
                        self.push(node, Op::Bool(true), &[], None);
                    }
                    Literal::False => {
                        self.push(node, Op::Bool(false), &[], None);
                    }
                    Literal::String => {
                        self.unsupported(node);
                        return None;
                    }
                }
            }
            Finish::Paren(paren) => {
                let inner = paren.inner().node();
                let value = self.node_of(inner);
                self.nodes_of[paren.node().to_usize()] = Some(value);
                self.controls[paren.node().to_usize()] = self.control(inner);
                let form = self.form(inner);
                self.bottoms[paren.node().to_usize()] = form.completes;
                if !form.valid {
                    return None;
                }
                if form.completes {
                    return Some(());
                }
                self.typed(inner)?;
            }
            Finish::Prefix { expr, neg } => {
                let operand = expr.operand().node();
                let value = self.input(operand);
                let id = self.push(
                    expr.node(),
                    if neg { Op::Neg } else { Op::Not },
                    &[value],
                    None,
                );
                self.controls[expr.node().to_usize()] = self.control(operand);
                let form = self.form(operand);
                self.bottoms[expr.node().to_usize()] = form.completes;
                self.lowered.typed[id.index()].then_some(())?;
                if form.completes {
                    self.completes_input(id, 0);
                    return Some(());
                }
                self.typed(operand)?;
            }
            Finish::Binary { expr, op } => {
                let node = expr.node();
                let lhs = expr.lhs().node();
                let rhs = expr.rhs().node();
                let lhs_input = self.input(lhs);
                let rhs_input = self.input(rhs);
                let id = self.push(node, Op::Binary(op), &[lhs_input, rhs_input], None);
                self.controls[node.to_usize()] =
                    self.compose_control(node, [self.control(lhs), self.control(rhs)]);
                let lhs_form = self.form(lhs);
                let rhs_form = self.form(rhs);
                if !lhs_form.valid || !rhs_form.valid {
                    return None;
                }
                if lhs_form.completes || rhs_form.completes {
                    if lhs_form.completes {
                        self.completes_input(id, 0);
                    }
                    if rhs_form.completes {
                        self.completes_input(id, 1);
                    }
                    self.bottoms[node.to_usize()] = true;
                    return Some(());
                }
                self.typed(lhs)?;
                self.typed(rhs)?;
                if matches!(op, BinaryOp::Arith(ArithOp::Div | ArithOp::Rem)) {
                    self.lowered.obligations.push(Obligation {
                        owner: self.owner,
                        node,
                        divisor: rhs_input.0,
                        context: self.context(),
                    });
                }
            }
        }
        Some(())
    }
    fn lazy(&mut self, expr: LazyOp, rhs: RegionId) -> Option<()> {
        let lhs = expr.expr.lhs().node();
        let rhs_node = expr.expr.rhs().node();
        let lhs_input = self.input(lhs);
        let result = self.node_of(rhs_node);
        let rhs_form = self.form(rhs_node);
        let op = if expr.and {
            Op::And { rhs }
        } else {
            Op::Or { rhs }
        };
        let id = self.push_over(expr.expr.node(), op, &[lhs_input], None, &[result]);
        let selected = self.control(rhs_node).map(|_| rhs);
        let observe = selected.map(|region| {
            let (then, else_) = if expr.and {
                (Some(region), None)
            } else {
                (None, Some(region))
            };
            self.place(
                Op::Observe { then, else_ },
                &[
                    lhs_input,
                    (self.context(), self.source.range(expr.expr.node())),
                ],
                self.source.range(expr.expr.node()),
                None,
            )
        });
        self.controls[expr.expr.node().to_usize()] =
            self.compose_control(expr.expr.node(), [self.control(lhs), observe]);
        let lhs_form = self.form(lhs);
        if !lhs_form.valid {
            return None;
        }
        if lhs_form.completes {
            self.completes_input(id, 0);
            self.bottoms[expr.expr.node().to_usize()] = true;
            return Some(());
        }
        self.typed(lhs)?;
        if !rhs_form.valid {
            return None;
        }
        if rhs_form.completes {
            self.refine(lhs, !expr.and);
        } else {
            self.typed(rhs_node)?;
        }
        Some(())
    }
    fn join(
        &mut self,
        branch: Clean<ast::IfExpr>,
        then: RegionId,
        else_: Option<RegionId>,
    ) -> Option<()> {
        let tree = self.source.tree;
        let cond = branch.condition().node();
        let then_node = branch.then_branch().node();
        let else_node = branch.else_branch(tree).map(|e| e.node());
        let condition = self.input(cond);
        let mut results = vec![self.node_of(then_node)];
        results.extend(else_node.map(|else_node| self.node_of(else_node)));
        let then_form = self.form(then_node);
        let else_form = else_node.map_or(Form::SCALAR, |node| self.form(node));
        let id = self.push_over(
            branch.node(),
            Op::Join { then, else_ },
            &[condition],
            None,
            &results,
        );
        let observe = (self.control(then_node).is_some()
            || else_node.is_some_and(|node| self.control(node).is_some()))
        .then(|| {
            self.place(
                Op::Observe {
                    then: Some(then),
                    else_,
                },
                &[
                    condition,
                    (self.context(), self.source.range(branch.node())),
                ],
                self.source.range(branch.node()),
                None,
            )
        });
        self.controls[branch.node().to_usize()] =
            self.compose_control(branch.node(), [self.control(cond), observe]);
        let cond_form = self.form(cond);
        if cond_form.completes {
            self.completes_input(id, 0);
        }
        if !cond_form.valid || !then_form.valid || !else_form.valid {
            return None;
        }
        if cond_form.completes || (then_form.completes && else_form.completes) {
            self.bottoms[branch.node().to_usize()] = true;
        } else {
            if then_form.scalar() {
                self.typed(then_node)?;
            } else {
                self.refine(cond, false);
            }
            if let Some(else_node) = else_node {
                if else_form.scalar() {
                    self.typed(else_node)?;
                } else {
                    self.refine(cond, true);
                }
            }
        }
        self.typed(cond)?;
        Some(())
    }
    fn call(&mut self, call: Clean<ast::CallExpr>, target: Option<FunctionId>) -> Option<()> {
        let context = self.context();
        let tree = self.source.tree;
        let node = call.node();
        let callee: Option<(FunctionId, &Header, Callee)> = target.and_then(|target| {
            let function = &self.headers[target.index()];
            Some((target, function, function.callee?))
        });
        if let Some((target, ..)) = callee {
            self.lowered.entered.push((context, target));
        }
        // Every argument is read, arity aside: the typing holds each to its parameter.
        let mut inputs = std::mem::take(&mut self.inputs);
        inputs.clear();
        if target.is_none() {
            let callee = self.source.peel(call.callee()).node();
            if let Some(built) = self.nodes_of[callee.to_usize()] {
                inputs.push((built, self.source.range(callee)));
            }
        }
        let mut count = 0;
        for arg in call.arg_list().args(tree) {
            count += 1;
            inputs.push(self.input(arg.node()));
        }
        if let Some((_, function, id)) = callee
            && let arity = self.graph.callable(id).params.len()
            && count != arity
        {
            self.source.error(
                node,
                codes::ARITY,
                format!("expected {arity} arguments, found {count}"),
                Some((self.source.range(function.item), "declared here")),
            );
        }
        let whole = callee.filter(|&(.., id)| self.whole(id, &inputs));
        let op = callee.map_or(Op::Hole, |(.., id)| Op::Call(id));
        let id = self.push(node, op, &inputs, None);
        let args: Vec<_> = call.arg_list().args(tree).map(|arg| arg.node()).collect();
        let controls: Vec<_> = args.iter().map(|&arg| self.control(arg)).collect();
        self.controls[node.to_usize()] = self.compose_control(node, controls);
        let mut bottom = false;
        let mut damaged = false;
        let first_arg = inputs.len() - args.len();
        for (index, &arg) in args.iter().enumerate() {
            let form = self.form(arg);
            bottom |= form.completes;
            damaged |= !form.valid;
            if form.completes {
                self.completes_input(id, first_arg + index);
            }
        }
        self.inputs = inputs;
        if bottom {
            self.bottoms[node.to_usize()] = true;
        }
        if damaged {
            return None;
        }
        let (target, function, _) = whole?;
        self.lowered.calls.push(Call {
            node: id,
            caller: FunctionId::new(self.owner as usize),
            callee: target,
            context,
        });
        if bottom {
            return Some(());
        }
        (!matches!(function.result, HeaderResult::None)).then_some(())
    }
}
