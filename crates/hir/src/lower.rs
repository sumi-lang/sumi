//! Lowering of one file to the graph: names, structure, and holes. The walk rejects nothing on type
//! grounds; it fails only on names, syntax, and unsupported constructs, and leaves each as a hole.

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

pub(crate) struct Header {
    pub name: Option<TextRange>,
    /// `None` when the parameter list is not whole.
    pub params: Option<Box<[Ty]>>,
    /// Per parameter, whole list or not; a duplicate name is `None` here while `params` keeps its
    /// type.
    pub param_types: Box<[Option<Ty>]>,
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
                // A parameter without a type is a syntax error the parser already reported.
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
            // A missing annotation may be damage: only an empty gap or the expression-body `=` says
            // it was left out.
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

/// A `let` binds at `Work::Finish`, after its initializer, so the initializer reads any outer
/// binding of the name.
type Scope<'s> = NameMap<'s, NodeId>;

enum Work {
    Enter(NodeIdx),
    Finish(NodeIdx),
    Unused(NodeIdx),
    Call(NodeIdx, Option<FunctionId>),
    Branches(NodeIdx),
    Rhs(NodeIdx),
    Join {
        node: NodeIdx,
        then: RegionId,
        else_: Option<RegionId>,
    },
    Lazy {
        node: NodeIdx,
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
}

fn enter_each(work: &mut Vec<Work>, nodes: impl Iterator<Item = NodeIdx>) {
    let base = work.len();
    work.extend(nodes.map(Work::Enter));
    work[base..].reverse();
}

struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    headers: &'a [Header],
    names: &'a NameMap<'s, Named>,
    graph: Graph,
    lowered: Lowered,
    nodes_of: Vec<Option<NodeId>>,
    owner: u32,
    failed: bool,
    /// Open regions, innermost last, each with where its refinements begin in `refinements`.
    regions: Vec<(RegionId, usize)>,
    /// (defining node, the node its reads see) for the open regions, innermost last.
    refinements: Vec<(NodeId, NodeId)>,
    /// The first `depth` scopes are open, innermost last.
    scopes: Vec<Scope<'s>>,
    depth: usize,
    work: Vec<Work>,
    inputs: Vec<(NodeId, TextRange)>,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
        source: &'a mut Source<'s>,
        headers: &'a [Header],
        names: &'a NameMap<'s, Named>,
    ) -> Self {
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
                entered: Vec::new(),
                obligations: Vec::new(),
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
                    Work::Unused(node) => {
                        let input = self.input(node);
                        self.place(Op::Unused, &[input], input.1, None);
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
        let body = match root_node {
            Some(root) => self.input(root),
            None => {
                let hole = self.push(item_node, Op::Hole, &[], None);
                (hole, self.source.range(item_node))
            }
        };
        self.graph.close(region, body.0);
        self.regions.pop();
        // A failed parameter does not erase a declared result; the body is still held to it.
        let value = match declared {
            HeaderResult::Declared(ty, node) => self.push(
                node,
                Op::Copy {
                    declared: Some((ty, self.source.range(node))),
                },
                &[body],
                None,
            ),
            HeaderResult::Inferred | HeaderResult::None => body.0,
        };
        self.graph
            .close_run(FunctionId::new(owner), start, arity, region, value);
        !self.failed && root.is_some()
    }
    fn push(
        &mut self,
        node: NodeIdx,
        op: Op,
        inputs: &[(NodeId, TextRange)],
        name: Option<TextRange>,
    ) -> NodeId {
        let id = self.place(op, inputs, self.source.range(node), name);
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
        let typed = self.follows(&op, inputs);
        let id = self.graph.push(op, inputs, origin, name);
        self.lowered.typed.push(typed);
        id
    }
    /// Whether a node of `op` over `inputs` carries a value the typing follows.
    fn follows(&self, op: &Op, inputs: &[(NodeId, TextRange)]) -> bool {
        let typed = |node: NodeId| self.lowered.typed[node.index()];
        let result = |region: RegionId| typed(self.graph.region(region).result());
        match *op {
            Op::Hole | Op::Unused => false,
            Op::Entry | Op::Then | Op::Else | Op::Copy { declared: Some(_) } => true,
            Op::Param(index) => {
                self.headers[self.owner as usize].param_types[index as usize].is_some()
            }
            Op::Call(callee) => {
                self.whole(callee, inputs)
                    && !matches!(self.headers[callee.index()].result, HeaderResult::None)
            }
            Op::And { rhs } | Op::Or { rhs } => typed(inputs[0].0) && result(rhs),
            Op::Join { then, else_ } => {
                typed(inputs[0].0) && result(then) && else_.is_none_or(result)
            }
            _ => inputs.iter().all(|&(input, _)| typed(input)),
        }
    }
    /// A whole call has an argument per parameter, none a hole.
    fn whole(&self, callee: FunctionId, inputs: &[(NodeId, TextRange)]) -> bool {
        let params = self.headers[callee.index()]
            .params
            .as_deref()
            .expect("a call names a whole callee");
        params.len() == inputs.len()
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
        let (region, _) = *self.regions.last().expect("a body runs in its region");
        self.graph.region(region).context
    }
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
        // Raw tokens partition the source, so the token at `first + 1` is glued to `first` unless
        // it is trivia.
        let glued = (first + 1 < end).then(|| lexed.kind(first + 1));
        sumi_syntax::binary_operator(lexed.kind(first), glued)
            .expect("clean binary operator")
            .0
    }
    /// The scope is as it was when the read was built: a region is entered right after its
    /// condition finishes.
    fn read(&self, node: NodeIdx) -> Option<NodeId> {
        let tree = self.source.tree;
        let node = self.source.peel(ast::Expr::cast(tree, node)?).node();
        if tree.kind(node) != NodeKind::NameRef {
            return None;
        }
        let defined = self.lookup(self.source.text(node))?;
        self.lowered.typed[defined.index()].then_some(defined)
    }
    /// Narrow the locals `cond` compares, for `cond` holding in `sense`.
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
            NodeKind::NameRef => {
                if let Some(local) = self.read(node) {
                    let at = self.source.range(node);
                    let inputs = [(self.current(local), at)];
                    let read = self.place(Op::Exactly(sense), &inputs, at, None);
                    self.refinements.push((local, read));
                }
            }
            _ => {}
        }
    }
    fn branches(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let branch = ast::IfExpr::cast(tree, node).unwrap();
        let cond = branch.condition(tree).unwrap().node();
        let then_node = branch.then_branch(tree).unwrap().node();
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
        work.push(Work::Join { node, then, else_ });
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
    fn rhs(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let binary = ast::BinaryExpr::cast(tree, node).unwrap();
        let lhs = binary.lhs(tree).unwrap().node();
        let rhs = binary.rhs(tree).unwrap().node();
        let and = self.binary_op(node) == sumi_syntax::BinaryOp::And;
        let parent = self.context();
        let op = if and { Op::Then } else { Op::Else };
        let left = self.input(lhs);
        let context = self.context_at(rhs, op, left, parent);
        let region = self.graph.open(context);
        work.push(Work::Lazy { node, rhs: region });
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
            NodeKind::Block => {
                work.push(Work::Finish(node));
                let base = work.len();
                let mut children = tree.children(node).peekable();
                while let Some(child) = children.next() {
                    let statement =
                        children.peek().is_some() && ast::Expr::cast(tree, child).is_some();
                    work.push(Work::Enter(child));
                    if statement {
                        work.push(Work::Unused(child));
                    }
                }
                work[base..].reverse();
            }
            NodeKind::LetStmt
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
                let mut tail = None;
                let mut valid = !tree.has_error(node);
                let mut children = tree.children(node).peekable();
                while let Some(child) = children.next() {
                    let expression = ast::Expr::cast(tree, child).is_some();
                    if children.peek().is_none() && expression {
                        tail = Some(child);
                        break;
                    }
                    if self.typed(child).is_none() {
                        self.node_of(child);
                        valid = false;
                    }
                }
                // A damaged block may have lost its tail to recovery, so without one it is a hole,
                // not unit.
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
                        let at = self.source.range(node);
                        self.push(node, Op::Unit, &[(context, at)], None);
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
                let value = self.input(initializer_node);
                let name = self.source.name(binding.name(tree));
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
                self.bind(name, copy);
                self.lowered.typed[copy.index()].then_some(())?;
            }
            NodeKind::DiscardStmt => {
                let value = ast::DiscardStmt::cast(tree, node)
                    .unwrap()
                    .value(tree)
                    .unwrap()
                    .node();
                let discarded = self.node_of(value);
                self.nodes_of[node.to_usize()] = Some(discarded);
                self.typed(value)?;
            }
            NodeKind::NameRef => {
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
                let value = self.input(operand);
                self.push(node, if neg { Op::Neg } else { Op::Not }, &[value], None);
                self.typed(operand)?;
            }
            NodeKind::BinaryExpr => {
                use sumi_syntax::BinaryOp::*;

                let binary = ast::BinaryExpr::cast(tree, node).unwrap();
                let lhs_node = binary.lhs(tree).unwrap().node();
                let rhs_node = binary.rhs(tree).unwrap().node();
                let op = self.binary_op(node);
                let lhs = self.input(lhs_node);
                let rhs = self.input(rhs_node);
                let eager = eager(op).expect("a lazy operator finishes as its own item");
                self.push(node, Op::Binary(eager), &[lhs, rhs], None);
                self.typed(lhs_node)?;
                self.typed(rhs_node)?;
                if matches!(op, Div | Rem) {
                    self.lowered.obligations.push(Obligation {
                        owner: self.owner,
                        node,
                        divisor: rhs.0,
                        context: self.context(),
                    });
                }
            }
            _ => unreachable!("scheduled supported node"),
        }
        Some(())
    }
    fn lazy(&mut self, node: NodeIdx, rhs: RegionId) -> Option<()> {
        let tree = self.source.tree;
        let binary = ast::BinaryExpr::cast(tree, node).unwrap();
        let lhs_node = binary.lhs(tree).unwrap().node();
        let rhs_node = binary.rhs(tree).unwrap().node();
        let and = self.binary_op(node) == sumi_syntax::BinaryOp::And;
        let lhs = self.input(lhs_node);
        let op = if and { Op::And { rhs } } else { Op::Or { rhs } };
        self.push(node, op, &[lhs], None);
        self.typed(lhs_node)?;
        self.typed(rhs_node)?;
        Some(())
    }
    fn join(&mut self, node: NodeIdx, then: RegionId, else_: Option<RegionId>) -> Option<()> {
        let tree = self.source.tree;
        let branch = ast::IfExpr::cast(tree, node).unwrap();
        let condition_node = branch.condition(tree).unwrap().node();
        let then_node = branch.then_branch(tree).unwrap().node();
        let else_node = branch.else_branch(tree).map(|e| e.node());
        let condition = self.input(condition_node);
        self.push(node, Op::Join { then, else_ }, &[condition], None);
        self.typed(then_node)?;
        if let Some(else_node) = else_node {
            self.typed(else_node)?;
        }
        self.typed(condition_node)?;
        Some(())
    }
    fn call(&mut self, node: NodeIdx, target: Option<FunctionId>) -> Option<()> {
        let context = self.context();
        let tree = self.source.tree;
        let call = ast::CallExpr::cast(tree, node).unwrap();
        let list = call.arg_list(tree).unwrap();
        let callee: Option<(FunctionId, &Header, &[Ty])> = target.and_then(|target| {
            let function = &self.headers[target.index()];
            Some((target, function, function.params.as_deref()?))
        });
        if let Some((target, ..)) = callee {
            self.lowered.entered.push((context, target));
        }
        // Every argument is read, arity aside: the typing holds each to its parameter.
        let mut inputs = std::mem::take(&mut self.inputs);
        inputs.clear();
        if target.is_none() {
            let callee = self.source.peel(call.callee(tree).unwrap()).node();
            if let Some(built) = self.nodes_of[callee.to_usize()] {
                inputs.push((built, self.source.range(callee)));
            }
        }
        let mut count = 0;
        for arg in list.args(tree) {
            count += 1;
            inputs.push(self.input(arg.node()));
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
        let whole = callee.filter(|&(target, ..)| self.whole(target, &inputs));
        let op = callee.map_or(Op::Hole, |(target, ..)| Op::Call(target));
        let id = self.push(node, op, &inputs, None);
        self.inputs = inputs;
        let (target, function, _) = whole?;
        self.lowered.calls.push(Call {
            node: id,
            caller: FunctionId::new(self.owner as usize),
            callee: target,
            context,
        });
        (!matches!(function.result, HeaderResult::None)).then_some(())
    }
}
