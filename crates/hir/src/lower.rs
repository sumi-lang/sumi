//! Lowering of one file to the graph: names, structure, and holes. Name and syntax failures become
//! holes rather than graph nodes.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use rustc_hash::FxBuildHasher;
use sumi_frontend::{DiagnosticCode, Fix, Label};
use sumi_graph::{Carried, GraphBuilder, References};
use sumi_lexer::{LexedFile, RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    Literal, NodeIdx, NodeKind, PrefixOp, SyntaxTree,
    ast::{self, AstNode, Clean, CleanExpr, CleanStmt, View},
};
use sumi_text::{TextEdit, TextRange, TextSize};

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
    /// The node is the annotation.
    Declared(Ty, NodeIdx),
    /// A block body with no annotation declares `unit`; the node is the parameter list.
    Omitted(NodeIdx),
    Inferred,
}

impl HeaderResult {
    /// The type the body is held to and the node declaring it, written or omitted.
    fn declared(self) -> Option<(Ty, NodeIdx)> {
        match self {
            Self::Declared(ty, node) => Some((ty, node)),
            Self::Omitted(node) => Some((Ty::Unit, node)),
            Self::None | Self::Inferred => None,
        }
    }
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

/// A block's statement and the context it runs in, which is dead after one that never completes.
pub(crate) struct Statement {
    pub block: NodeIdx,
    pub range: TextRange,
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
    /// Every typed call and its callee, whole or not: the result flows into a call missing an
    /// argument too.
    pub called: Vec<(NodeId, FunctionId)>,
    /// (context, callee) of every call whose callee has a whole parameter list, whole call or not.
    pub entered: Vec<(NodeId, FunctionId)>,
    pub obligations: Vec<Obligation>,
    pub fallthroughs: Vec<Option<Fallthrough>>,
    pub bindings: Vec<Binding>,
    /// In source order once `lower` returns.
    pub references: Vec<Occurrence>,
    /// Names under a hole that a declaration under the same hole may bind, so nothing resolves
    /// them; in source order once `lower` returns.
    pub unresolved: Vec<TextRange>,
    /// In source order within each block.
    pub statements: Vec<Statement>,
}

/// `a`, `a and b`, or `a, b, and c`.
fn join(types: &[String]) -> String {
    match types.split_last() {
        None => unreachable!("a list of types names one"),
        Some((only, [])) => only.clone(),
        Some((last, [first])) => format!("{first} and {last}"),
        Some((last, rest)) => format!("{}, and {last}", rest.join(", ")),
    }
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
    pub fn conflict(
        &mut self,
        at: TextRange,
        code: DiagnosticCode,
        typing: &Typing,
        claims: &[(Ty, Claim)],
        message: impl FnOnce(String) -> String,
    ) {
        let claimed = claims
            .iter()
            .map(|(ty, claim)| (*ty, typing.origin(*claim)))
            .collect();
        self.conflict_at(at, code, claimed, message);
    }
    /// `message` receives the two or more claimed types joined as a list, in source order. Types
    /// claimed at one origin share a label, since a call delivers all of its callee's.
    pub fn conflict_at(
        &mut self,
        at: TextRange,
        code: DiagnosticCode,
        mut claimed: Vec<(Ty, Option<TextRange>)>,
        message: impl FnOnce(String) -> String,
    ) {
        assert!(claimed.len() >= 2, "a conflict names two types");
        claimed.sort_by_key(|(_, origin)| origin.map(|range| (range.start(), range.end())));
        let types: Vec<_> = claimed.iter().map(|(ty, _)| ty.to_string()).collect();
        let mut labels: Vec<(TextRange, Vec<String>)> = Vec::new();
        for (ty, origin) in &claimed {
            let Some(origin) = origin else { continue };
            match labels.last_mut() {
                Some((labeled, types)) if labeled == origin => types.push(ty.to_string()),
                _ => labels.push((*origin, vec![ty.to_string()])),
            }
        }
        let labels = labels
            .into_iter()
            .map(|(origin, types)| (origin, format!("{} here", join(&types)).into()));
        self.report(at, code, message(join(&types)), labels);
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
    is_duplicate: bool,
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
                    is_duplicate: first.is_some(),
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
                (list, tokens.next(), tokens.next())
            });
            match gap {
                Some((list, None, None)) => HeaderResult::Omitted(list.node()),
                Some((_, Some(SyntaxKind::Eq), None)) => HeaderResult::Inferred,
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
    let mut lowered = builder.lowered;
    lowered
        .references
        .sort_unstable_by_key(|occurrence| occurrence.range.start());
    lowered.references.dedup();
    lowered
        .unresolved
        .sort_unstable_by_key(|range| range.start());
    (builder.graph.finish(), lowered)
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

#[derive(Clone, Copy, PartialEq, Eq)]
struct LocalId(u32);

impl LocalId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

struct Local<'s> {
    name: &'s str,
    binding: BindingId,
    declaration: NodeId,
    current: NodeId,
    is_mutable: bool,
    completes: bool,
    /// A name beginning with `_` counts as read from its declaration.
    is_read: bool,
    is_assigned: bool,
}

struct RegionState {
    changes: Vec<(LocalId, NodeId, NodeId)>,
    refinements: Vec<(LocalId, NodeId, NodeId)>,
    context: NodeId,
}

struct LoopState {
    expr: Clean<ast::ForExpr>,
    region: RegionId,
    index: NodeId,
    empty: NodeId,
    carried: Vec<(LocalId, NodeId)>,
}

/// A `let` binds at `Work::Finish`, after its initializer, so the initializer reads any outer
/// binding of the name.
type Scope<'s> = NameMap<'s, LocalId>;

enum Finish {
    Let(Clean<ast::LetStmt>),
    Assign {
        assignment: Clean<ast::AssignStmt>,
        target: Option<LocalId>,
    },
    Discard(Clean<ast::DiscardStmt>),
    NameRef(Clean<ast::NameRef>),
    Literal(Clean<ast::LiteralExpr>),
    Paren(Clean<ast::ParenExpr>),
    Prefix {
        expr: Clean<ast::PrefixExpr>,
        is_neg: bool,
    },
    Binary {
        expr: Clean<ast::BinaryExpr>,
        op: BinaryOp,
    },
    Partial(Partial),
}

/// An expression the parser recovered in, lowered from the children it has. Its operator or
/// callee decides its type, so the context around it is still checked; what is missing is a hole.
enum Partial {
    Discard {
        node: NodeIdx,
        value: NodeIdx,
    },
    Paren {
        node: NodeIdx,
        inner: NodeIdx,
    },
    Prefix {
        node: NodeIdx,
        is_neg: bool,
        operand: Option<NodeIdx>,
    },
    Binary {
        node: NodeIdx,
        op: BinaryOp,
        lhs: Option<NodeIdx>,
        rhs: Option<NodeIdx>,
    },
    Call {
        node: NodeIdx,
        target: Option<FunctionId>,
        /// The arguments before any garbage: the ones whose position is reliable.
        args: Vec<NodeIdx>,
    },
    Assign {
        node: NodeIdx,
        target: Option<LocalId>,
        value: Option<NodeIdx>,
    },
    /// A binding with an initializer: it still takes its name, typed by what it has.
    Let {
        binding: ast::LetStmt,
    },
}

/// `&&` when `is_and`, else `||`, with its expression.
#[derive(Clone, Copy)]
struct LazyOp {
    expr: Clean<ast::BinaryExpr>,
    is_and: bool,
}

enum Work {
    Enter(NodeIdx),
    Advance(NodeIdx),
    Finish(Finish),
    /// Damaged or not: a block runs its statements.
    Block(NodeIdx),
    Unused(NodeIdx),
    Statement {
        block: NodeIdx,
        child: NodeIdx,
    },
    Call {
        call: Clean<ast::CallExpr>,
        target: Option<FunctionId>,
    },
    Branches(Branch),
    LoopBody(Clean<ast::ForExpr>),
    LoopEnd(Box<LoopState>),
    Rhs(LazyOp),
    Join {
        branch: Branch,
        then: RegionId,
        else_: Option<RegionId>,
        contexts: [NodeId; 2],
    },
    Lazy {
        expr: LazyOp,
        rhs: RegionId,
        contexts: [NodeId; 2],
    },
    Push {
        region: RegionId,
        guard: (NodeIdx, bool),
    },
    Pop {
        region: RegionId,
        root: NodeIdx,
    },
    Return(ast::ReturnStmt),
}

/// An `if` by its parts. A part the parser lost stands as the `if` itself, whose node is a hole
/// by then: its region closes on that hole, and nothing is entered for it.
#[derive(Clone, Copy)]
struct Branch {
    node: NodeIdx,
    cond: NodeIdx,
    then: NodeIdx,
    else_: Option<NodeIdx>,
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
    is_valid: bool,
    completes: bool,
}

impl Form {
    const SCALAR: Self = Self {
        is_valid: true,
        completes: false,
    };

    fn is_scalar(self) -> bool {
        self.is_valid && !self.completes
    }
}

struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    headers: &'a [Header],
    names: &'a NameMap<'s, Named>,
    graph: GraphBuilder,
    lowered: Lowered,
    nodes_of: Vec<Option<NodeId>>,
    /// By block, its innermost tail expression once lowered.
    tails: Vec<Option<NodeIdx>>,
    owner: u32,
    has_failed: bool,
    /// Open regions, innermost last, each with where its refinements begin in `refinements`.
    regions: Vec<(RegionId, usize, NodeId)>,
    /// (local, source version, the node its reads see) for open regions, innermost last.
    refinements: Vec<(LocalId, NodeId, NodeId)>,
    /// The first `depth` scopes are open, innermost last, each ending where its block does.
    scopes: Vec<Scope<'s>>,
    scope_ends: Vec<TextSize>,
    scope_mutables: Vec<usize>,
    depth: usize,
    locals: Vec<Local<'s>>,
    mutable_locals: Vec<LocalId>,
    undo: Vec<(LocalId, NodeId)>,
    /// (undo length, local count) for open regions, innermost last.
    version_stack: Vec<(usize, usize)>,
    /// Closed regions whose state the enclosing join, lazy op, or loop has yet to take.
    region_states: Vec<(RegionId, RegionState)>,
    /// The local and underlying version read by each name reference.
    reads_of: Vec<Option<(LocalId, NodeId)>>,
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
                called: Vec::new(),
                entered: Vec::new(),
                obligations: Vec::new(),
                fallthroughs: vec![None; headers.len()],
                bindings: Vec::new(),
                references: Vec::new(),
                unresolved: Vec::new(),
                statements: Vec::new(),
            },
            nodes_of: vec![None; nodes],
            tails: vec![None; nodes],
            owner: 0,
            has_failed: false,
            regions: Vec::new(),
            refinements: Vec::new(),
            scopes: Vec::new(),
            scope_ends: Vec::new(),
            scope_mutables: Vec::new(),
            depth: 0,
            locals: Vec::new(),
            mutable_locals: Vec::new(),
            undo: Vec::new(),
            version_stack: Vec::new(),
            region_states: Vec::new(),
            reads_of: vec![None; nodes],
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
        self.has_failed = false;
        self.depth = 0;
        self.regions.clear();
        self.refinements.clear();
        self.locals.clear();
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
        self.undo.clear();
        self.version_stack.clear();
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
        self.has_failed |= header.callee.is_none() || matches!(declared, HeaderResult::None);
        let region = self.graph.open(entry);
        self.graph.enter(region);
        self.regions.push((region, 0, entry));
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
                        contexts,
                    } => self.join(branch, then, else_, contexts),
                    Work::Lazy {
                        expr,
                        rhs,
                        contexts,
                    } => self.lazy(expr, rhs, contexts),
                    Work::Enter(node) => {
                        self.enter(node, &mut work);
                        continue;
                    }
                    Work::Advance(node) => {
                        self.advance(node);
                        continue;
                    }
                    Work::Statement { block, child } => {
                        self.lowered.statements.push(Statement {
                            block,
                            range: self.source.range(child),
                            context: self.context(),
                        });
                        continue;
                    }
                    Work::Unused(node) => {
                        let at = self.source.range(node);
                        let input = (self.node_of(node), at);
                        let unused = self.place(Op::Unused, &[input], at, None);
                        if self.form(node).completes {
                            self.completes_input(unused, 0);
                        }
                        continue;
                    }
                    Work::Branches(branch) => {
                        self.branches(branch, &mut work);
                        continue;
                    }
                    Work::LoopBody(expr) => {
                        self.loop_body(expr, &mut work);
                        continue;
                    }
                    Work::LoopEnd(state) => self.loop_end(*state),
                    Work::Rhs(expr) => {
                        self.rhs(expr, &mut work);
                        continue;
                    }
                    Work::Push { region, guard } => {
                        self.version_stack
                            .push((self.undo.len(), self.locals.len()));
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
                        self.advance(root);
                        let result = self.input(root);
                        let fallthrough = self.context();
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
                        let (mark, _) = self.version_stack.pop().expect("a region fork has a mark");
                        let mut changed: Vec<_> =
                            self.undo[mark..].iter().map(|&(local, _)| local).collect();
                        changed.sort_unstable_by_key(|local| local.index());
                        changed.dedup();
                        let state = self.region_state(&changed, keep, fallthrough);
                        self.region_states.push((region, state));
                        for (local, version) in self.undo.drain(mark..).rev() {
                            self.locals[local.index()].current = version;
                        }
                        self.refinements.truncate(keep);
                        continue;
                    }
                    Work::Return(return_) => self.return_(return_),
                };
                self.has_failed |= built.is_none();
            }
            self.work = work;
        }
        let root = root_node.and_then(|root| self.form(root).is_valid.then(|| self.node_of(root)));
        let body = match root_node {
            Some(root) => self.input(root),
            None => {
                let hole = self.push(item_node, Op::Hole, &[], None);
                (hole, self.source.range(item_node))
            }
        };
        let control = root_node.and_then(|root| self.control(root));
        let fallthrough = control
            .map(|control| self.place(Op::Sequence, &[(control, body.1), body], body.1, None));
        self.graph.close_with_control(
            region,
            body,
            root_node.is_none_or(|root| !self.form(root).completes),
            control,
        );
        self.regions.pop();
        // A failed parameter does not erase a declared result; the body is still held to it.
        let declared = declared.declared();
        let value = match (control.is_none() && self.returns.is_empty(), declared) {
            (true, Some((ty, node))) => self.push(
                node,
                Op::Copy {
                    declared: Some((ty, self.source.range(node))),
                },
                &[body],
                None,
            ),
            (true, None) => body.0,
            (false, declared) => {
                let node = declared.map_or(item_node, |(_, node)| node);
                let declared = declared.map(|(ty, node)| (ty, self.source.range(node)));
                let mut outcomes = Vec::with_capacity(self.returns.len() + 1);
                outcomes.push((fallthrough.unwrap_or(body.0), body.1));
                outcomes.extend(self.returns.iter().copied());
                let result = self.push(node, Op::Result { declared }, &outcomes, None);
                let completes = root_node.is_none_or(|root| self.form(root).completes);
                let fallthrough = root_node
                    .and_then(|root| self.explicit_tail(root))
                    .filter(|&tail| self.form(tail).is_scalar())
                    .or_else(|| {
                        root_node.filter(|&root| declared.is_some() && self.form(root).is_scalar())
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
        let is_whole = !self.has_failed && root.is_some();
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
            let at = declaration.name.expect("a bound local is named");
            let (kind, reads) = match (&declaration.op, local.is_assigned) {
                (Op::Param { .. }, _) => ("parameter", "is never read"),
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
        let is_typed = self.follows(&op, inputs, references, results);
        let id = self
            .graph
            .push(op, inputs, references, self.source.range(node), name);
        self.lowered.typed.push(is_typed);
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
        let is_typed = self.follows(&op, inputs, references, &[]);
        let id = self.graph.push(op, inputs, references, origin, name);
        self.lowered.typed.push(is_typed);
        id
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
            | Op::Then
            | Op::Else
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
            Op::Call(callee) => {
                let function = self.graph.callable(callee).function;
                !matches!(self.headers[function.index()].result, HeaderResult::None)
            }
            Op::Assign => typed(declaration()) && typed(inputs[0].0),
            Op::Phi => typed(declaration()) && inputs.iter().all(|&(input, _)| typed(input)),
            Op::Join { .. } => typed(inputs[0].0) && results.iter().all(|&result| typed(result)),
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
    /// A value and where it is read: a block's at its tail, where the value is written.
    fn input(&mut self, node: NodeIdx) -> (NodeId, TextRange) {
        (self.node_of(node), self.source.range(self.value_at(node)))
    }
    /// The expression a value is read at: a block's tail, through nested blocks.
    fn value_at(&self, node: NodeIdx) -> NodeIdx {
        self.explicit_tail(node).unwrap_or(node)
    }
    fn typed(&self, node: NodeIdx) -> Option<NodeId> {
        let id = self.nodes_of[node.to_usize()]?;
        self.lowered.typed[id.index()].then_some(id)
    }
    fn hole(&mut self, node: NodeIdx) -> NodeId {
        self.push(node, Op::Hole, &[], None)
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
        let id = LocalId(u32::try_from(self.locals.len()).expect("local count fits u32"));
        self.locals.push(Local {
            name,
            binding,
            declaration: node,
            current: node,
            is_mutable,
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
    fn set_version(&mut self, local: LocalId, version: NodeId) {
        if let Some(&(_, count)) = self.version_stack.last()
            && local.index() < count
        {
            self.undo.push((local, self.locals[local.index()].current));
        }
        self.locals[local.index()].current = version;
    }
    fn region_state(&self, changed: &[LocalId], keep: usize, context: NodeId) -> RegionState {
        RegionState {
            changes: changed
                .iter()
                .map(|&local| {
                    (
                        local,
                        self.locals[local.index()].current,
                        self.current(local),
                    )
                })
                .collect(),
            refinements: self.refinements[keep..]
                .iter()
                .copied()
                .filter(|&(local, _, _)| self.locals[local.index()].is_mutable)
                .collect(),
            context,
        }
    }
    fn closed(&mut self, region: RegionId) -> RegionState {
        let position = self
            .region_states
            .iter()
            .rposition(|&(closed, _)| closed == region)
            .expect("a closed region has local state");
        self.region_states.remove(position).1
    }
    fn guarded_state(&mut self, condition: NodeIdx, sense: bool, context: NodeId) -> RegionState {
        let keep = self.refinements.len();
        self.refine(condition, sense);
        let state = self.region_state(&[], keep, context);
        self.refinements.truncate(keep);
        state
    }
    fn merge_versions(&mut self, condition: NodeIdx, states: [&RegionState; 2], at: TextRange) {
        let condition = self.input(condition);
        let mut changed: Vec<_> = states
            .iter()
            .flat_map(|state| state.changes.iter().map(|&(local, _, _)| local))
            .collect();
        changed.sort_unstable_by_key(|local| local.index());
        changed.dedup();
        for local in changed {
            let values = states.map(|state| {
                if let Ok(index) = state
                    .changes
                    .binary_search_by_key(&local.index(), |&(local, _, _)| local.index())
                {
                    let (_, version, value) = state.changes[index];
                    (version, value)
                } else {
                    let version = self.locals[local.index()].current;
                    let value = state
                        .refinements
                        .iter()
                        .rev()
                        .find(|&&(id, source, _)| id == local && source == version)
                        .map_or_else(|| self.current(local), |&(_, _, value)| value);
                    (version, value)
                }
            });
            if values[0].0 == values[1].0 {
                continue;
            }
            let [true_value, false_value] = values.map(|(_, value)| value);
            let declaration = self.locals[local.index()].declaration;
            let inputs = [
                condition,
                (true_value, self.graph.node(true_value).origin),
                (false_value, self.graph.node(false_value).origin),
            ];
            let phi = self.place_with(
                Op::Phi,
                &inputs,
                References::Phi {
                    declaration,
                    contexts: [states[0].context, states[1].context],
                },
                at,
                None,
            );
            self.set_version(local, phi);
        }
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
    fn current(&self, local: LocalId) -> NodeId {
        let version = self.locals[local.index()].current;
        self.refinements
            .iter()
            .rev()
            .find(|&&(refined, source, _)| refined == local && source == version)
            .map_or(version, |&(_, _, node)| node)
    }
    fn context(&self) -> NodeId {
        self.regions.last().expect("a body runs in its region").2
    }
    /// A lowered block's innermost tail expression, or a non-block expression itself.
    fn explicit_tail(&self, root: NodeIdx) -> Option<NodeIdx> {
        match ast::Expr::cast(self.source.tree, root) {
            Some(ast::Expr::Block(_)) => self.tails[root.to_usize()],
            Some(_) => Some(root),
            None => None,
        }
    }
    fn form(&self, node: NodeIdx) -> Form {
        Form {
            is_valid: self.typed(node).is_some(),
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
    fn read(&self, node: NodeIdx) -> Option<(LocalId, NodeId)> {
        let tree = self.source.tree;
        let ast::Expr::NameRef(name) = self.source.peel(ast::Expr::cast(tree, node)?) else {
            return None;
        };
        self.reads_of[name.node().to_usize()]
    }
    /// Narrow the locals `cond` compares, for `cond` holding in `sense`.
    fn refine(&mut self, cond: NodeIdx, sense: bool) {
        use sumi_syntax::BinaryOp::*;

        if self.form(cond).completes {
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
                            if let (Some((local, version)), Some(_), Some(value)) =
                                (self.read(side), self.typed(side), self.typed(other))
                                && self.locals[local.index()].current == version
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
                                self.refinements.push((local, version, read));
                            }
                        }
                    }
                    _ => {}
                }
            }
            CleanExpr::NameRef(_) => {
                if let Some((local, version)) = self.read(node)
                    && self.locals[local.index()].current == version
                {
                    let at = self.source.range(node);
                    let inputs = [(self.current(local), at)];
                    let read = self.place(Op::Exactly(sense), &inputs, at, None);
                    self.refinements.push((local, version, read));
                }
            }
            _ => {}
        }
    }
    fn branches(&mut self, branch: Branch, work: &mut Vec<Work>) {
        let Branch {
            node,
            cond,
            then: then_node,
            else_: else_node,
        } = branch;
        self.advance(cond);
        let parent = self.context();
        let condition = self.input(cond);
        let then_context = self.context_at(then_node, Op::Then, condition, parent);
        let else_context = match else_node {
            Some(else_node) => self.context_at(else_node, Op::Else, condition, parent),
            None if !self.mutable_locals.is_empty() => {
                self.context_at(node, Op::Else, condition, parent)
            }
            None => parent,
        };
        let contexts = [then_context, else_context];
        let then = self.graph.open(then_context);
        let else_ = else_node.map(|_| self.graph.open(else_context));
        work.push(Work::Join {
            branch,
            then,
            else_,
            contexts,
        });
        if let (Some(else_node), Some(region)) = (else_node, else_) {
            work.push(Work::Pop {
                region,
                root: else_node,
            });
            if else_node != node {
                work.push(Work::Enter(else_node));
            }
            work.push(Work::Push {
                region,
                guard: (cond, false),
            });
        }
        work.push(Work::Pop {
            region: then,
            root: then_node,
        });
        if then_node != node {
            work.push(Work::Enter(then_node));
        }
        work.push(Work::Push {
            region: then,
            guard: (cond, true),
        });
    }
    fn rhs(&mut self, expr: LazyOp, work: &mut Vec<Work>) {
        let is_and = expr.is_and;
        let lhs = expr.expr.lhs().node();
        self.advance(lhs);
        let rhs = expr.expr.rhs().node();
        let parent = self.context();
        let left = self.input(lhs);
        let selected = usize::from(!is_and);
        let mut contexts = [parent; 2];
        contexts[selected] =
            self.context_at(rhs, if is_and { Op::Then } else { Op::Else }, left, parent);
        if !self.mutable_locals.is_empty() {
            contexts[usize::from(is_and)] =
                self.context_at(rhs, if is_and { Op::Else } else { Op::Then }, left, parent);
        }
        let context = contexts[selected];
        let region = self.graph.open(context);
        work.push(Work::Lazy {
            expr,
            rhs: region,
            contexts,
        });
        work.push(Work::Pop { region, root: rhs });
        work.push(Work::Enter(rhs));
        work.push(Work::Push {
            region,
            guard: (lhs, is_and),
        });
    }
    fn loop_body(&mut self, expr: Clean<ast::ForExpr>, work: &mut Vec<Work>) {
        let at = self.source.range(expr.node());
        let bounds = [
            self.input(expr.start().node()),
            self.input(expr.end().node()),
        ];
        let range = TextRange::new(
            self.source.range(expr.start().node()).start(),
            self.source.range(expr.end().node()).end(),
        );
        let condition = self.place(Op::Binary(BinaryOp::Cmp(CmpOp::Lt)), &bounds, range, None);
        let context = self.context_at(
            expr.body().node(),
            Op::Then,
            (condition, at),
            self.context(),
        );
        let empty = self.context_at(expr.node(), Op::Else, (condition, at), self.context());
        let region = self.graph.open(context);
        self.version_stack
            .push((self.undo.len(), self.locals.len()));
        self.regions.push((region, self.refinements.len(), context));
        self.graph.enter(region);
        let body = expr.body().node();
        let body_range = TextRange::new(self.source.range(body).start(), self.scope_end(body));
        self.open_scope(body_range.end());
        let name = expr.name().node();
        let name_range = self.source.range(name);
        let index = self.place(Op::LoopIndex, &bounds, at, Some(name_range));
        for (position, bound) in [expr.start().node(), expr.end().node()]
            .into_iter()
            .enumerate()
        {
            if self.form(bound).completes {
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
            let initial = self.current(local);
            let declaration = self.locals[local.index()].declaration;
            let header = self.place_with(
                Op::Carry,
                &[(initial, self.graph.node(initial).origin)],
                References::Version(declaration),
                at,
                None,
            );
            self.set_version(local, header);
            carried.push((local, header));
        }
        work.push(Work::LoopEnd(Box::new(LoopState {
            expr,
            region,
            index,
            empty,
            carried,
        })));
        work.push(Work::Pop {
            region,
            root: expr.body().node(),
        });
        work.push(Work::Enter(expr.body().node()));
    }
    fn loop_end(&mut self, state: LoopState) -> Option<()> {
        let LoopState {
            expr,
            region,
            index,
            empty,
            carried,
        } = state;
        self.close_scope();
        let body = self.closed(region);
        let next: Vec<_> = carried
            .iter()
            .map(|&(local, header)| {
                let position = body
                    .changes
                    .binary_search_by_key(&local.index(), |&(local, _, _)| local.index())
                    .expect("a carried local has a header version");
                (header, body.changes[position].2)
            })
            .collect();
        let carried_nodes: Vec<NodeId> = next
            .iter()
            .flat_map(|&(header, next)| [header, next])
            .collect();
        let references = References::Loop {
            index,
            continuation: body.context,
            empty,
            carried: Carried::new(&carried_nodes),
        };
        let at = self.source.range(expr.node());
        let bounds = [expr.start().node(), expr.end().node()].map(|bound| {
            let (value, at) = self.input(bound);
            let value = self.control(bound).map_or(value, |control| {
                self.place(Op::Sequence, &[(control, at), (value, at)], at, None)
            });
            (value, at)
        });
        let node = self.push_over(
            expr.node(),
            Op::Loop { body: region },
            &bounds,
            references,
            None,
            &[],
        );
        self.controls[expr.node().to_usize()] = Some(node);
        for ((local, header), (_, next)) in carried.into_iter().zip(next) {
            if header == next {
                continue;
            }
            let value = self.place_with(
                Op::LoopValue,
                &[(node, at)],
                References::LoopValue {
                    carry: header,
                    next,
                },
                at,
                None,
            );
            self.set_version(local, value);
        }
        let mut is_valid = self.form(expr.body().node()).is_valid;
        for (position, bound) in [expr.start().node(), expr.end().node()]
            .into_iter()
            .enumerate()
        {
            let form = self.form(bound);
            is_valid &= form.is_valid;
            if form.completes {
                self.completes_input(node, position);
                self.bottoms[expr.node().to_usize()] = true;
            }
        }
        is_valid.then_some(())
    }
    fn enter(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        use ast::{Expr, Stmt};

        let tree = self.source.tree;
        let stmt = Stmt::cast(tree, node);
        let Some(clean) = stmt.and_then(|stmt| stmt.clean(tree, self.source.lexed())) else {
            match stmt {
                Some(Stmt::Expr(Expr::Block(_))) => {
                    self.has_failed = true;
                    self.block_statements(node, work);
                }
                Some(stmt) if tree.has_error(node) => {
                    self.has_failed = true;
                    self.damaged(stmt, work);
                }
                _ if tree.has_error(node) => {
                    self.holed(node);
                    self.has_failed = true;
                }
                _ => unreachable!("a statement without syntax errors has a clean view"),
            }
            return;
        };
        match clean {
            CleanStmt::LetStmt(binding) => {
                work.push(Work::Finish(Finish::Let(binding)));
                work.push(Work::Enter(binding.initializer().node()));
            }
            CleanStmt::AssignStmt(assignment) => {
                let target = self.assignment_target(assignment.target());
                work.push(Work::Finish(Finish::Assign { assignment, target }));
                work.push(Work::Enter(assignment.value().node()));
            }
            CleanStmt::Expr(CleanExpr::Block(_)) => self.block_statements(node, work),
            CleanStmt::DiscardStmt(discard) => {
                work.push(Work::Finish(Finish::Discard(discard)));
                work.push(Work::Enter(discard.value().node()));
            }
            CleanStmt::Expr(CleanExpr::IfExpr(branch)) => {
                let cond = branch.condition().node();
                work.push(Work::Branches(Branch {
                    node,
                    cond,
                    then: branch.then_branch().node(),
                    else_: branch.else_branch(tree).map(|e| e.node()),
                }));
                work.push(Work::Enter(cond));
            }
            CleanStmt::Expr(CleanExpr::ForExpr(expr)) => {
                work.push(Work::LoopBody(expr));
                enter_each(work, [expr.start().node(), expr.end().node()].into_iter());
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
                        is_and: op == sumi_syntax::BinaryOp::And,
                    })),
                }
                work.push(Work::Enter(lhs));
            }
            CleanStmt::Expr(CleanExpr::PrefixExpr(expr)) => {
                let is_neg = expr.op() == PrefixOp::Neg;
                let peeled = self.source.peel(expr.operand());
                if is_neg
                    && let Expr::LiteralExpr(literal) = peeled
                    && literal.value(tree, self.source.lexed()) == Some(Literal::Int)
                {
                    if self.integer(node, literal.node(), true).is_none() {
                        self.has_failed = true;
                    }
                    return;
                }
                work.push(Work::Finish(Finish::Prefix { expr, is_neg }));
                work.push(Work::Enter(expr.operand().node()));
            }
            CleanStmt::Expr(CleanExpr::ParenExpr(paren)) => {
                work.push(Work::Finish(Finish::Paren(paren)));
                work.push(Work::Enter(paren.inner().node()));
            }
            CleanStmt::Expr(CleanExpr::CallExpr(call)) => {
                let target = self.target(call.callee().node());
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
                work.push(Work::Return(return_.view()));
                if let Some(value) = return_.value(tree) {
                    work.push(Work::Advance(value.node()));
                    work.push(Work::Enter(value.node()));
                }
            }
        }
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
                if let Named::Function(id) = named {
                    self.refer(name.node(), Symbol::Function(*id), true);
                }
                self.source.error(
                    name.node(),
                    codes::INVALID_ASSIGNMENT_TARGET,
                    format!("function `{text}` is not assignable"),
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
        if !self.locals[local.index()].is_mutable {
            let declaration = self.locals[local.index()].declaration;
            self.source.error(
                name.node(),
                codes::IMMUTABLE_ASSIGNMENT,
                format!("cannot assign to immutable local `{text}`"),
                self.graph
                    .node(declaration)
                    .name
                    .map(|range| (range, "declared here")),
            );
            return None;
        }
        self.locals[local.index()].is_assigned = true;
        Some(local)
    }
    fn return_(&mut self, return_: ast::ReturnStmt) -> Option<()> {
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
        if value.is_none_or(|(_, form)| form.is_valid) {
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
            let name_range = self.source.range(name_node);
            let hole = self.push(binding.node(), Op::Hole, &[], Some(name_range));
            self.bind(
                name,
                hole,
                BindingKind::Let {
                    is_mutable: binding.mutable(tree, self.source.lexed()),
                },
                name_range,
                self.source.range(binding.node()).end(),
            );
        }
        self.has_failed = true;
    }
    fn block_statements(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        self.open_scope(self.scope_end(node));
        work.push(Work::Block(node));
        let base = work.len();
        let mut children = tree.children(node).peekable();
        while let Some(child) = children.next() {
            let is_statement = children.peek().is_some() && ast::Expr::cast(tree, child).is_some();
            work.push(Work::Statement { block: node, child });
            work.push(Work::Enter(child));
            if is_statement {
                work.push(Work::Unused(child));
            }
            work.push(Work::Advance(child));
        }
        work[base..].reverse();
    }
    fn target(&mut self, node: NodeIdx) -> Option<FunctionId> {
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
                    self.graph
                        .node(declaration)
                        .name
                        .map(|range| (range, "declared here")),
                );
            }
            return None;
        }
        match self.names.get(name) {
            Some(Named::Function(target)) => {
                let target = *target;
                self.refer(node, Symbol::Function(target), false);
                Some(target)
            }
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
    fn integer(&mut self, origin: NodeIdx, literal: NodeIdx, is_negative: bool) -> Option<NodeId> {
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
        let value = if is_negative { -&magnitude } else { magnitude };
        Some(self.push(origin, Op::Int(value), &[], None))
    }
    fn block(&mut self, node: NodeIdx) -> Option<()> {
        let tree = self.source.tree;
        self.close_scope();
        let mut tail = None;
        let is_damaged = tree.has_error(node);
        let mut is_valid = !is_damaged;
        let mut is_bottom = false;
        let mut controls = Vec::new();
        let mut children = tree.children(node).peekable();
        while let Some(child) = children.next() {
            let is_expression = ast::Expr::cast(tree, child).is_some();
            if children.peek().is_none() && is_expression {
                tail = Some(child);
                controls.push(self.control(child));
                let form = self.form(child);
                is_valid &= form.is_valid;
                is_bottom |= form.completes;
                break;
            }
            controls.push(self.control(child));
            let form = self.form(child);
            if !form.is_valid {
                self.node_of(child);
                is_valid = false;
            }
            is_bottom |= form.completes;
        }
        self.controls[node.to_usize()] = self.compose_control(node, controls);
        self.tails[node.to_usize()] = tail.map(|tail| self.value_at(tail));
        // A damaged block may have lost its tail to recovery, so without one it is a hole, not
        // unit.
        match tail {
            Some(tail) => {
                let value = self.node_of(tail);
                self.nodes_of[node.to_usize()] = Some(value);
            }
            None if is_damaged => {
                self.hole(node);
            }
            None => {
                let context = self.context();
                let at = self.source.range(node);
                self.push(node, Op::Unit, &[(context, at)], None);
            }
        }
        if is_bottom {
            self.bottoms[node.to_usize()] = true;
        }
        if !is_valid || is_damaged {
            return None;
        }
        if !is_bottom {
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
                let name_range = self.source.range(name);
                let copy = self.push(binding.node(), op, &[value], Some(name_range));
                let local = self.bind(
                    self.source.text(name),
                    copy,
                    BindingKind::Let {
                        is_mutable: binding.mutable(),
                    },
                    name_range,
                    self.source.range(binding.node()).end(),
                );
                let initializer = binding.initializer().node();
                self.controls[binding.node().to_usize()] = self.control(initializer);
                let form = self.form(initializer);
                self.locals[local.index()].completes = form.completes;
                self.bottoms[binding.node().to_usize()] = form.completes;
                if !form.is_valid || !self.lowered.typed[copy.index()] {
                    return None;
                }
                if form.completes {
                    self.completes_input(copy, 0);
                    return Some(());
                }
            }
            Finish::Assign { assignment, target } => {
                let node = assignment.node();
                let value = assignment.value().node();
                let input = self.input(value);
                let assigned = match target {
                    Some(local) => self.push_over(
                        node,
                        Op::Assign,
                        &[input],
                        References::Version(self.locals[local.index()].declaration),
                        None,
                        &[],
                    ),
                    None => self.push(node, Op::Hole, &[input], None),
                };
                self.controls[node.to_usize()] = self.control(value);
                let form = self.form(value);
                self.bottoms[node.to_usize()] = form.completes;
                if form.completes {
                    self.completes_input(assigned, 0);
                }
                let local = target?;
                if !form.is_valid || !self.lowered.typed[assigned.index()] {
                    return None;
                }
                if !form.completes {
                    self.set_version(local, assigned);
                }
            }
            Finish::Discard(discard) => {
                let value = discard.value().node();
                let discarded = self.node_of(value);
                self.nodes_of[discard.node().to_usize()] = Some(discarded);
                self.controls[discard.node().to_usize()] = self.control(value);
                let form = self.form(value);
                self.bottoms[discard.node().to_usize()] = form.completes;
                if !form.is_valid {
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
                    Some(local) => {
                        self.refer(
                            node,
                            Symbol::Local(self.locals[local.index()].binding),
                            false,
                        );
                        self.locals[local.index()].is_read = true;
                        let version = self.locals[local.index()].current;
                        let read = self.current(local);
                        self.nodes_of[node.to_usize()] = Some(read);
                        self.reads_of[node.to_usize()] = Some((local, version));
                        self.bottoms[node.to_usize()] = self.locals[local.index()].completes;
                        self.lowered.typed[read.index()].then_some(())?;
                    }
                    None => {
                        if let Some(named) = self.names.get(name) {
                            if let Named::Function(id) = named {
                                self.refer(node, Symbol::Function(*id), false);
                            }
                            self.source.error(
                                node,
                                codes::NOT_A_VALUE,
                                format!("function `{name}` is not a value"),
                                None,
                            );
                            self.hole(node);
                            self.has_failed = true;
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
                }
            }
            Finish::Paren(paren) => {
                let inner = paren.inner().node();
                let value = self.node_of(inner);
                self.nodes_of[paren.node().to_usize()] = Some(value);
                self.controls[paren.node().to_usize()] = self.control(inner);
                let form = self.form(inner);
                self.bottoms[paren.node().to_usize()] = form.completes;
                if !form.is_valid {
                    return None;
                }
                if form.completes {
                    return Some(());
                }
                self.typed(inner)?;
            }
            Finish::Prefix { expr, is_neg } => {
                let operand = expr.operand().node();
                let value = self.input(operand);
                let id = self.push(
                    expr.node(),
                    if is_neg { Op::Neg } else { Op::Not },
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
                if !lhs_form.is_valid || !rhs_form.is_valid {
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
            Finish::Partial(partial) => {
                self.partial(partial);
                return None;
            }
        }
        Some(())
    }
    /// A statement or expression the parser recovered in. Its children are lowered for what they
    /// hold, and it is lowered from them where its kind decides its type: an operator's result,
    /// a callee's, or a discard's or parentheses' value. A branch or a loop is a hole, since its
    /// regions want every part, and so is a name or a literal.
    fn damaged(&mut self, stmt: ast::Stmt, work: &mut Vec<Work>) {
        use ast::{Expr, Stmt};

        let tree = self.source.tree;
        let lexed = self.source.lexed();
        let node = stmt.node();
        let partial = match stmt {
            Stmt::DiscardStmt(discard) => match discard.value(tree) {
                Some(value) => Partial::Discard {
                    node,
                    value: value.node(),
                },
                None => return self.holed(node),
            },
            Stmt::AssignStmt(assign) => {
                let target = match assign.target(tree) {
                    Some(target) => self.assignment_target(target),
                    None => None,
                };
                Partial::Assign {
                    node,
                    target,
                    value: assign.value(tree).map(|value| value.node()),
                }
            }
            Stmt::ReturnStmt(return_) => {
                let Some(value) = return_.value(tree) else {
                    return self.holed(node);
                };
                work.push(Work::Return(return_));
                work.push(Work::Advance(value.node()));
                work.push(Work::Enter(value.node()));
                return;
            }
            Stmt::Expr(Expr::ParenExpr(paren)) => match paren.inner(tree) {
                Some(inner) => Partial::Paren {
                    node,
                    inner: inner.node(),
                },
                None => return self.holed(node),
            },
            Stmt::Expr(Expr::PrefixExpr(prefix)) => match prefix.op(tree, lexed) {
                Some(op) => Partial::Prefix {
                    node,
                    is_neg: op == PrefixOp::Neg,
                    operand: prefix.operand(tree).map(|operand| operand.node()),
                },
                None => return self.holed(node),
            },
            Stmt::Expr(Expr::BinaryExpr(binary)) => match binary.op(tree, lexed).and_then(eager) {
                Some(op) => Partial::Binary {
                    node,
                    op,
                    lhs: binary.lhs(tree).map(|lhs| lhs.node()),
                    rhs: binary.rhs(tree).map(|rhs| rhs.node()),
                },
                None => return self.holed(node),
            },
            Stmt::LetStmt(binding) => match binding.initializer(tree) {
                Some(_) => Partial::Let { binding },
                None => return self.damaged_let(binding),
            },
            Stmt::Expr(Expr::IfExpr(branch)) => {
                // A lost part stands as the `if` itself, which `node_of` holes on demand; an
                // `else` keyword without its block is still an else.
                let cond = branch.condition(tree).map_or(node, |cond| cond.node());
                let then = branch.then_branch(tree).map_or(node, |block| block.node());
                let else_ = branch
                    .else_branch(tree)
                    .map(|branch| branch.node())
                    .or_else(|| {
                        tree.holds(node, lexed, SyntaxKind::ElseKw, None)
                            .then_some(node)
                    });
                work.push(Work::Branches(Branch {
                    node,
                    cond,
                    then,
                    else_,
                }));
                if cond != node {
                    work.push(Work::Enter(cond));
                }
                return;
            }
            Stmt::Expr(Expr::CallExpr(call)) => {
                let target = match call.callee(tree) {
                    Some(callee) => self.target(callee.node()),
                    None => None,
                };
                let mut args = Vec::new();
                if let Some(list) = call.arg_list(tree) {
                    for child in tree.children(list.node()) {
                        let Some(arg) = Expr::cast(tree, child) else {
                            break;
                        };
                        args.push(arg.node());
                    }
                }
                Partial::Call { node, target, args }
            }
            Stmt::Expr(_) => return self.holed(node),
        };
        match &partial {
            Partial::Let { binding } => {
                let initializer = binding
                    .initializer(tree)
                    .map(|initializer| initializer.node());
                work.push(Work::Finish(Finish::Partial(partial)));
                if let Some(initializer) = initializer {
                    work.push(Work::Enter(initializer));
                }
            }
            Partial::Discard { value: child, .. } | Partial::Paren { inner: child, .. } => {
                let child = *child;
                work.push(Work::Finish(Finish::Partial(partial)));
                work.push(Work::Enter(child));
            }
            Partial::Prefix { operand: child, .. } | Partial::Assign { value: child, .. } => {
                let child = *child;
                work.push(Work::Finish(Finish::Partial(partial)));
                if let Some(child) = child {
                    work.push(Work::Enter(child));
                }
            }
            Partial::Binary { lhs, rhs, .. } => {
                let (lhs, rhs) = (*lhs, *rhs);
                work.push(Work::Finish(Finish::Partial(partial)));
                if let Some(rhs) = rhs {
                    work.push(Work::Enter(rhs));
                }
                if let Some(lhs) = lhs {
                    work.push(Work::Advance(lhs));
                    work.push(Work::Enter(lhs));
                }
            }
            Partial::Call { args, .. } => {
                let args = args.clone();
                work.push(Work::Finish(Finish::Partial(partial)));
                enter_each(work, args.into_iter());
            }
        }
    }
    /// A hole still resolves the names under it, so an editor finds them; one a declaration
    /// under the hole may bind is left unresolved, since that binding was never made.
    fn holed(&mut self, node: NodeIdx) {
        self.hole(node);
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
    }
    /// A child's value, or a hole at `node` for a missing one.
    fn present(&mut self, node: NodeIdx, child: Option<NodeIdx>) -> (NodeId, TextRange) {
        match child {
            Some(child) => self.input(child),
            None => (self.hole(node), self.source.range(node)),
        }
    }
    fn partial(&mut self, partial: Partial) {
        match partial {
            Partial::Let { binding } => {
                let tree = self.source.tree;
                let node = binding.node();
                let initializer = binding
                    .initializer(tree)
                    .map(|initializer| initializer.node());
                let value = self.present(node, initializer);
                let annotation = binding.type_ref(tree);
                let declared = annotation.and_then(|annotation| {
                    let ty = self.source.ty(annotation)?;
                    Some((ty, self.source.range(annotation.node())))
                });
                let Some((name, name_node)) = self.source.name(binding.name(tree)) else {
                    self.hole(node);
                    return;
                };
                let op = match (annotation, declared) {
                    (Some(_), None) => Op::Hole,
                    _ => Op::Copy { declared },
                };
                let name_range = self.source.range(name_node);
                let copy = self.push(node, op, &[value], Some(name_range));
                let is_mutable = binding.mutable(tree, self.source.lexed());
                let local = self.bind(
                    name,
                    copy,
                    BindingKind::Let { is_mutable },
                    name_range,
                    self.source.range(node).end(),
                );
                self.controls[node.to_usize()] =
                    initializer.and_then(|initializer| self.control(initializer));
                let completes =
                    initializer.is_some_and(|initializer| self.form(initializer).completes);
                self.locals[local.index()].completes = completes;
                self.bottoms[node.to_usize()] = completes;
                if completes {
                    self.completes_input(copy, 0);
                }
            }
            Partial::Discard { node, value } | Partial::Paren { node, inner: value } => {
                let id = self.node_of(value);
                self.nodes_of[node.to_usize()] = Some(id);
                self.controls[node.to_usize()] = self.control(value);
                self.bottoms[node.to_usize()] = self.form(value).completes;
            }
            Partial::Assign {
                node,
                target,
                value,
            } => {
                let input = self.present(node, value);
                let assigned = match target {
                    Some(local) => self.push_over(
                        node,
                        Op::Assign,
                        &[input],
                        References::Version(self.locals[local.index()].declaration),
                        None,
                        &[],
                    ),
                    None => self.push(node, Op::Hole, &[input], None),
                };
                self.controls[node.to_usize()] = value.and_then(|value| self.control(value));
                let completes = value.is_some_and(|value| self.form(value).completes);
                self.bottoms[node.to_usize()] = completes;
                match (target, completes) {
                    (_, true) => self.completes_input(assigned, 0),
                    (Some(local), false) if self.lowered.typed[assigned.index()] => {
                        self.set_version(local, assigned);
                    }
                    _ => {}
                }
            }
            Partial::Prefix {
                node,
                is_neg,
                operand,
            } => {
                let input = self.present(node, operand);
                let id = self.push(node, if is_neg { Op::Neg } else { Op::Not }, &[input], None);
                self.controls[node.to_usize()] = operand.and_then(|operand| self.control(operand));
                if operand.is_some_and(|operand| self.form(operand).completes) {
                    self.completes_input(id, 0);
                    self.bottoms[node.to_usize()] = true;
                }
            }
            Partial::Binary { node, op, lhs, rhs } => {
                let inputs = [self.present(node, lhs), self.present(node, rhs)];
                let id = self.push(node, Op::Binary(op), &inputs, None);
                let controls =
                    [lhs, rhs].map(|operand| operand.and_then(|operand| self.control(operand)));
                self.controls[node.to_usize()] = self.compose_control(node, controls);
                for (index, operand) in [lhs, rhs].into_iter().enumerate() {
                    if operand.is_some_and(|operand| self.form(operand).completes) {
                        self.completes_input(id, index);
                        self.bottoms[node.to_usize()] = true;
                    }
                }
            }
            Partial::Call { node, target, args } => {
                let context = self.context();
                let callee: Option<(FunctionId, &Header, Callee)> = target.and_then(|target| {
                    let function = &self.headers[target.index()];
                    Some((target, function, function.callee?))
                });
                if let Some((target, ..)) = callee {
                    self.lowered.entered.push((context, target));
                }
                let mut inputs = std::mem::take(&mut self.inputs);
                inputs.clear();
                for &arg in &args {
                    inputs.push(self.input(arg));
                }
                // A damaged list is not yet the wrong length.
                let op = callee.map_or(Op::Hole, |(.., id)| Op::Call(id));
                let id = self.push(node, op, &inputs, None);
                if let Some((target, ..)) = callee
                    && self.lowered.typed[id.index()]
                {
                    self.lowered.called.push((id, target));
                }
                self.inputs = inputs;
                let controls: Vec<_> = args.iter().map(|&arg| self.control(arg)).collect();
                self.controls[node.to_usize()] = self.compose_control(node, controls);
                for (index, &arg) in args.iter().enumerate() {
                    if self.form(arg).completes {
                        self.completes_input(id, index);
                        self.bottoms[node.to_usize()] = true;
                    }
                }
            }
        }
    }
    fn lazy(&mut self, expr: LazyOp, rhs: RegionId, contexts: [NodeId; 2]) -> Option<()> {
        let lhs = expr.expr.lhs().node();
        let rhs_node = expr.expr.rhs().node();
        let state = self.closed(rhs);
        let lhs_input = self.input(lhs);
        let result = self.node_of(rhs_node);
        let rhs_form = self.form(rhs_node);
        let op = if expr.is_and {
            Op::And { rhs }
        } else {
            Op::Or { rhs }
        };
        let id = self.push_over(
            expr.expr.node(),
            op,
            &[lhs_input],
            References::None,
            None,
            &[result],
        );
        let selected = self.control(rhs_node).map(|_| rhs);
        let observe = selected.map(|region| {
            let (then, else_) = if expr.is_and {
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
        if !lhs_form.is_valid {
            return None;
        }
        if lhs_form.completes {
            self.completes_input(id, 0);
            self.bottoms[expr.expr.node().to_usize()] = true;
            return Some(());
        }
        self.typed(lhs)?;
        if !rhs_form.is_valid {
            return None;
        }
        if rhs_form.completes {
            self.refine(lhs, !expr.is_and);
        } else {
            self.typed(rhs_node)?;
            let skipped = self.guarded_state(lhs, !expr.is_and, contexts[usize::from(expr.is_and)]);
            let states = if expr.is_and {
                [&state, &skipped]
            } else {
                [&skipped, &state]
            };
            self.merge_versions(lhs, states, self.source.range(expr.expr.node()));
        }
        Some(())
    }
    fn join(
        &mut self,
        branch: Branch,
        then: RegionId,
        else_: Option<RegionId>,
        contexts: [NodeId; 2],
    ) -> Option<()> {
        let Branch {
            node,
            cond,
            then: then_node,
            else_: else_node,
        } = branch;
        let then_state = self.closed(then);
        let false_state = match else_ {
            Some(else_) => self.closed(else_),
            None => self.guarded_state(cond, false, contexts[1]),
        };
        let condition = self.input(cond);
        let mut results = vec![self.node_of(then_node)];
        results.extend(else_node.map(|else_node| self.node_of(else_node)));
        let then_form = self.form(then_node);
        let else_form = else_node.map_or(Form::SCALAR, |node| self.form(node));
        let id = self.push_over(
            node,
            Op::Join { then, else_ },
            &[condition],
            References::None,
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
                &[condition, (self.context(), self.source.range(node))],
                self.source.range(node),
                None,
            )
        });
        self.controls[node.to_usize()] = self.compose_control(node, [self.control(cond), observe]);
        let cond_form = self.form(cond);
        if cond_form.completes {
            self.completes_input(id, 0);
        }
        if !cond_form.is_valid || !then_form.is_valid || !else_form.is_valid {
            return None;
        }
        if cond_form.completes || (then_form.completes && else_form.completes) {
            self.bottoms[node.to_usize()] = true;
        } else {
            self.merge_versions(cond, [&then_state, &false_state], self.source.range(node));
            if then_form.is_scalar() {
                self.typed(then_node)?;
            } else {
                self.refine(cond, false);
            }
            if let Some(else_node) = else_node {
                if else_form.is_scalar() {
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
        if let Some((target, ..)) = callee
            && self.lowered.typed[id.index()]
        {
            self.lowered.called.push((id, target));
        }
        let args: Vec<_> = call.arg_list().args(tree).map(|arg| arg.node()).collect();
        let controls: Vec<_> = args.iter().map(|&arg| self.control(arg)).collect();
        self.controls[node.to_usize()] = self.compose_control(node, controls);
        let mut is_bottom = false;
        let mut is_damaged = false;
        let first_arg = inputs.len() - args.len();
        for (index, &arg) in args.iter().enumerate() {
            let form = self.form(arg);
            is_bottom |= form.completes;
            is_damaged |= !form.is_valid;
            if form.completes {
                self.completes_input(id, first_arg + index);
            }
        }
        self.inputs = inputs;
        if is_bottom {
            self.bottoms[node.to_usize()] = true;
        }
        if is_damaged {
            return None;
        }
        let (target, function, _) = whole?;
        self.lowered.calls.push(Call {
            node: id,
            caller: FunctionId::new(self.owner as usize),
            callee: target,
            context,
        });
        if is_bottom {
            return Some(());
        }
        (!matches!(function.result, HeaderResult::None)).then_some(())
    }
}
