//! Semantic checking of one file: names, structure, and scalar types.
//!
//! Checking makes three passes over the items.
//!
//! 1. **Headers.** Every function's name, parameter types, and result class:
//!    an annotated result is a class known to be its type, an expression body
//!    without one is a fresh class to infer, and a bare block body is unit.
//! 2. **Bodies.** A structural walk per function resolves names, builds the
//!    body's expressions with every expression and local owning a class in
//!    the [`Typing`], and records what the walk learns: facts for literals
//!    and operator results, a flow for each call, and a demand wherever a
//!    context requires an expression to have a type. The walk rejects nothing
//!    on type grounds; it fails only on names, syntax, and unsupported
//!    constructs.
//! 3. **Verdicts.** The typing solves once. Signatures are read off result
//!    classes, independent of declaration order. Demands are then checked in
//!    source order against the final evidence, so a disagreement is blamed on
//!    the first demand that raised it. A body is published when its walk
//!    succeeded, none of its demands failed, every class it uses resolved,
//!    and every function it calls has a signature.
//!
//! Names are never copied while checking: every map is keyed by a slice of
//! the source, and the one builder keeps its scratch across bodies, so a
//! body costs the vectors it publishes and nothing else.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

use sumi_frontend::{DiagnosticCode, Label, Location};
use sumi_lexer::{RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    NodeIdx, NodeKind, SyntaxTree,
    ast::{self, AstNode},
};

use crate::codes;
use crate::solver::Var;
use crate::typing::{Expected, Typing};
use crate::*;

/// A hasher for identifiers: a word at a time, with a multiply to spread
/// the bits, which is all a short ASCII name needs and a fraction of what a
/// keyed hash costs.
#[derive(Default)]
struct NameHasher(u64);

impl NameHasher {
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl Hasher for NameHasher {
    fn write(&mut self, bytes: &[u8]) {
        let mut words = bytes.chunks_exact(8);
        for word in &mut words {
            self.add(u64::from_le_bytes(word.try_into().unwrap()));
        }
        let rest = words.remainder();
        if !rest.is_empty() {
            let mut word = [0; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(word));
        }
    }

    fn write_u8(&mut self, byte: u8) {
        self.add(u64::from(byte));
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

/// A map from names, as slices of the source, to whatever they name.
type NameMap<'s, V> = HashMap<&'s str, V, BuildHasherDefault<NameHasher>>;

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

struct Header {
    params: Option<Box<[Ty]>>,
    /// The result class; `None` when the declaration is too damaged to have
    /// one.
    result: Option<Var>,
    /// The declared result type and where: the annotation, or the whole item
    /// for a bare block body. A declaration is a contract the body is held
    /// to, never changed by it. `None` for a result to infer from the body.
    declared: Option<(Ty, Span)>,
    origin: Span,
}

struct DraftLocal<'s> {
    name: &'s str,
    origin: Span,
    class: Var,
}

/// A body whose expressions are built, with a placeholder type on each
/// until its class resolves.
struct DraftBody<'s> {
    params: Vec<LocalId>,
    locals: Vec<DraftLocal<'s>>,
    exprs: Vec<Expr>,
    /// The class of each expression, by index.
    classes: Vec<Var>,
    root: ExprId,
}

impl DraftBody<'_> {
    /// The body with every class resolved to its type, if every class
    /// resolved and every call agrees with its callee's signature.
    fn publish(self, typing: &Typing, functions: &[Function]) -> Option<Body> {
        let Self {
            params,
            locals,
            mut exprs,
            classes,
            root,
        } = self;
        let locals = locals
            .into_iter()
            .map(|local| {
                Some(Local {
                    name: local.name.into(),
                    origin: local.origin,
                    ty: typing.resolve(local.class)?,
                })
            })
            .collect::<Option<_>>()?;
        for (expr, &class) in exprs.iter_mut().zip(&classes) {
            let ty = typing.resolve(class)?;
            // A caller's demands can resolve its call's class without
            // resolving the callee. That is not a publishable call.
            if let ExprKind::Call { function, .. } = &expr.kind
                && functions[function.index()].signature.as_ref()?.result != ty
            {
                return None;
            }
            expr.ty = ty;
        }
        Some(Body {
            params,
            locals,
            exprs,
            root,
        })
    }
}

/// What a context requires of an expression, checked after solving.
enum DemandKind {
    /// The expression must have the expected type.
    Type {
        expected: Expected,
        related: Option<(Span, &'static str)>,
    },
    /// An expression statement's value must be unit.
    Unused,
    /// The operands of `==` and `!=` must not be unit.
    Comparable,
}

struct Demand {
    owner: usize,
    /// The expression whose type the demand is about: the innermost one
    /// the demanded expression takes its type from, through any number of
    /// tails and branches. Two demands with one subject are about one
    /// expression.
    subject: ExprId,
    node: NodeIdx,
    actual: Var,
    kind: DemandKind,
}

struct Source<'s> {
    parsed: &'s ParsedSource,
    tree: &'s SyntaxTree,
    diagnostics: Vec<Diagnostic>,
}

impl<'s> Source<'s> {
    fn span(&self, node: NodeIdx) -> Span {
        Span::new(
            self.parsed.file(),
            self.tree.byte_range(node, self.parsed.lexed()),
        )
    }
    fn text(&self, node: NodeIdx) -> &'s str {
        let range = self.tree.byte_range(node, self.parsed.lexed());
        let source: &'s str = self.parsed.source();
        &source[range.start().to_usize()..range.end().to_usize()]
    }
    fn name(&self, name: Option<ast::Name>) -> Option<(&'s str, NodeIdx)> {
        let node = name?.node();
        (!self.tree.has_error(node)
            && self.parsed.lexed().kind(self.tree.first_token(node)) == SyntaxKind::Ident)
            .then(|| (self.text(node), node))
    }
    fn error(
        &mut self,
        node: NodeIdx,
        code: DiagnosticCode,
        message: impl Into<Box<str>>,
        related: Option<(Span, &'static str)>,
    ) {
        let related = related.map(|(span, message)| (span, Box::from(message)));
        self.report(self.span(node), code, message, related);
    }
    fn report(
        &mut self,
        primary: Span,
        code: DiagnosticCode,
        message: impl Into<Box<str>>,
        related: impl IntoIterator<Item = (Span, Box<str>)>,
    ) {
        self.diagnostics.push(Diagnostic {
            code,
            severity: Severity::Error,
            message: message.into(),
            primary: Label {
                location: Location::range(primary),
                message: None,
            },
            secondary: related
                .into_iter()
                .map(|(span, message)| Label {
                    location: Location::range(span),
                    message: Some(message),
                })
                .collect(),
            notes: Box::new([]),
            fix: None,
        });
    }
    fn type_mismatch(
        &mut self,
        node: NodeIdx,
        expected: Ty,
        actual: Ty,
        related: Option<(Span, &'static str)>,
    ) {
        self.error(
            node,
            codes::TYPE_MISMATCH,
            format!("expected {expected}, found {actual}"),
            related,
        );
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

struct Parameter<'s> {
    name: Option<(&'s str, NodeIdx)>,
    ty: Option<Ty>,
}

pub fn analyze(parsed: ParsedSource) -> Analysis {
    let tree = parsed.parse().tree();
    let mut source = Source {
        parsed: &parsed,
        tree,
        diagnostics: Vec::new(),
    };
    let items: Vec<_> = ast::SourceFile::cast(tree, tree.root())
        .unwrap()
        .items(tree)
        .collect();
    let mut typing = Typing::new(parsed.file());

    // Pass 1: headers.
    let mut functions: Vec<Function> = Vec::with_capacity(items.len());
    let mut names: NameMap<Named> =
        NameMap::with_capacity_and_hasher(items.len(), Default::default());
    let mut parameters = Vec::with_capacity(items.len());
    let mut headers = Vec::with_capacity(items.len());
    for item in &items {
        let name = source.name(item.name(tree));
        let id = FunctionId(u32::try_from(functions.len()).expect("function count fits u32"));
        let origin = source.span(item.node());
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
                        Some((source.span(first), "declared here")),
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
        let mut params = Vec::new();
        if let Some(list) = list {
            for param in list.params(tree) {
                let ty = match param.type_ref(tree) {
                    Some(ty) => source.ty(ty),
                    None => {
                        if !tree.has_error(param.node()) {
                            source.error(
                                param.node(),
                                codes::MISSING_TYPE,
                                "function parameters require a type",
                                None,
                            );
                        }
                        None
                    }
                };
                valid &= ty.is_some();
                params.push(Parameter {
                    name: source.name(param.name(tree)),
                    ty,
                });
            }
        }
        let (result, declared) = if let Some(ret) = item.ret(tree) {
            let span = source.span(ret.node());
            match source.ty(ret) {
                Some(ty) => (Some(typing.known(ty, span)), Some((ty, span))),
                None => (None, None),
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
                Some((None, None)) => (
                    Some(typing.known(Ty::Unit, origin)),
                    Some((Ty::Unit, origin)),
                ),
                Some((Some(SyntaxKind::Eq), None)) => (Some(typing.fresh()), None),
                _ => (None, None),
            }
        };
        headers.push(Header {
            params: valid.then(|| params.iter().map(|p| p.ty.unwrap()).collect()),
            result,
            declared,
            origin,
        });
        parameters.push(params);
        functions.push(Function {
            name: name.map(|(name, _)| name.into()),
            origin,
            signature: None,
            body: None,
        });
    }

    // Pass 2: bodies.
    let mut demands = Vec::new();
    let mut bodies = Vec::with_capacity(items.len());
    // Syntax node IDs are dense and bodies have disjoint nodes. Expression
    // IDs remain body-local; a builder only reads entries in its own body.
    let mut values = vec![None; tree.len()];
    let mut builder = Builder::new(
        &mut source,
        &headers,
        &names,
        &mut typing,
        &mut demands,
        &mut values,
    );
    for (index, (item, params)) in items.iter().zip(parameters).enumerate() {
        bodies.push(builder.build(index, *item, params));
    }
    drop(builder);
    drop(values);

    // Pass 3: verdicts.
    typing.solve();
    let mut replay = typing.replay();
    let mut failed = vec![false; functions.len()];
    // An expression whose type is already in dispute is held to no further
    // demand: one report per expression, at the first demand it fails.
    let mut disputed = HashSet::new();
    for demand in demands {
        if disputed.contains(&(demand.owner, demand.subject)) {
            continue;
        }
        let actual = replay.resolve(demand.actual);
        match demand.kind {
            DemandKind::Type { expected, related } => {
                let expected_ty = match expected {
                    Expected::Ty(ty) => Some(ty),
                    Expected::Class(class) => replay.resolve(class),
                };
                match (actual, expected_ty) {
                    (Some(actual), Some(expected)) if actual != expected => {
                        source.type_mismatch(demand.node, expected, actual, related);
                    }
                    _ => {
                        replay.expect(demand.actual, expected);
                        continue;
                    }
                }
            }
            DemandKind::Unused => match actual {
                Some(ty) if ty != Ty::Unit => source.error(
                    demand.node,
                    codes::UNUSED_VALUE,
                    format!("unused value of type {ty}; use `_ =` to discard it"),
                    None,
                ),
                _ => {
                    replay.expect(demand.actual, Expected::Ty(Ty::Unit));
                    continue;
                }
            },
            DemandKind::Comparable => {
                if actual != Some(Ty::Unit) {
                    continue;
                }
                source.error(
                    demand.node,
                    codes::TYPE_MISMATCH,
                    "unit values cannot be compared",
                    None,
                );
            }
        }
        failed[demand.owner] = true;
        disputed.insert((demand.owner, demand.subject));
    }
    for (index, header) in headers.into_iter().enumerate() {
        let evidence = header.result.map(|result| *typing.evidence(result));
        let result = evidence.and_then(|evidence| evidence.ty());
        if let (Some(params), Some(result)) = (header.params, result) {
            functions[index].signature = Some(Signature { params, result });
        }
        // A result to infer that did not resolve is reported here, unless a
        // demand in the body already explained it, or the trouble arrived
        // whole from a callee, which reports it at its own declaration.
        if let (None, Some(evidence), None) = (header.declared, evidence, result)
            && bodies[index].is_some()
            && !failed[index]
            && !evidence.inherited()
        {
            let node = items[index].node();
            if evidence.is_conflict() {
                let claims = evidence.claims();
                let types: Vec<_> = claims.iter().map(|(ty, _)| ty.to_string()).collect();
                let (last, rest) = types.split_last().unwrap();
                let joined = if rest.len() == 1 {
                    format!("{} and {last}", rest[0])
                } else {
                    format!("{}, and {last}", rest.join(", "))
                };
                source.report(
                    source.span(node),
                    codes::CANNOT_INFER,
                    format!("function result is both {joined}; add a return type annotation"),
                    claims
                        .into_iter()
                        .map(|(ty, claim)| (typing.span(claim), format!("{ty} here").into())),
                );
            } else {
                source.error(
                    node,
                    codes::CANNOT_INFER,
                    "cannot infer function result; add a return type annotation",
                    None,
                );
            }
        }
    }
    for (index, body) in bodies.into_iter().enumerate() {
        if !failed[index] && functions[index].signature.is_some() {
            functions[index].body = body.and_then(|body| body.publish(&typing, &functions));
        }
    }
    source
        .diagnostics
        .sort_by_key(|d| d.primary.location.start());
    let diagnostics = source.diagnostics;
    let analysis = Analysis {
        parsed,
        functions,
        diagnostics,
    };
    assert!(
        analysis.is_valid()
            || analysis
                .parsed
                .diagnostics()
                .iter()
                .chain(&analysis.diagnostics)
                .any(|d| d.severity == Severity::Error),
        "incomplete semantic analysis without an error"
    );
    analysis
}

// None is a poisoned binding, distinct from an absent name. Scope transitions
// and let completion are explicit work items, so initializers see the old scope.
type Scope<'s> = NameMap<'s, Option<LocalId>>;
enum Work {
    Enter(NodeIdx),
    Finish(NodeIdx),
    Call(NodeIdx, FunctionId, NodeIdx),
}

/// The one walker for every body of the file. What a body publishes is
/// built in place and moved out; everything else the walk needs is kept
/// and reused, so no body pays for scratch.
struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    headers: &'a [Header],
    names: &'a NameMap<'s, Named>,
    typing: &'a mut Typing,
    demands: &'a mut Vec<Demand>,
    values: &'a mut [Option<ExprId>],
    // The body under construction.
    owner: usize,
    failed: bool,
    params: Vec<LocalId>,
    locals: Vec<DraftLocal<'s>>,
    exprs: Vec<Expr>,
    classes: Vec<Var>,
    // Scratch kept across bodies.
    /// The subject of each expression, by index.
    subjects: Vec<ExprId>,
    /// A pool of scopes; the first `depth` are open, innermost last. A map
    /// per scope costs a probe per enclosing scope on lookup, and nothing on
    /// close; an undo log measured slower on binding-heavy code, since every
    /// binding then pays a removal.
    scopes: Vec<Scope<'s>>,
    depth: usize,
    /// Parameter names seen so far, for duplicates.
    first: NameMap<'s, Span>,
    work: Vec<Work>,
    statements: Vec<(NodeIdx, Statement)>,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
        source: &'a mut Source<'s>,
        headers: &'a [Header],
        names: &'a NameMap<'s, Named>,
        typing: &'a mut Typing,
        demands: &'a mut Vec<Demand>,
        values: &'a mut [Option<ExprId>],
    ) -> Self {
        Self {
            source,
            headers,
            names,
            typing,
            demands,
            values,
            owner: 0,
            failed: false,
            params: Vec::new(),
            locals: Vec::new(),
            exprs: Vec::new(),
            classes: Vec::new(),
            subjects: Vec::new(),
            scopes: Vec::new(),
            depth: 0,
            first: NameMap::default(),
            work: Vec::new(),
            statements: Vec::new(),
        }
    }
    fn build(
        &mut self,
        owner: usize,
        item: ast::FnItem,
        parameters: Vec<Parameter<'s>>,
    ) -> Option<DraftBody<'s>> {
        self.owner = owner;
        self.failed = false;
        self.depth = 0;
        self.open_scope();
        self.first.clear();
        self.subjects.clear();
        // A published body took these; a failed one left them behind.
        self.params.clear();
        self.locals.clear();
        self.exprs.clear();
        self.classes.clear();
        for param in parameters {
            if let Some((name, node)) = param.name {
                if let Some(&span) = self.first.get(name) {
                    self.source.error(
                        node,
                        codes::DUPLICATE_NAME,
                        format!("duplicate parameter `{name}`"),
                        Some((span, "declared here")),
                    );
                    self.shadow(name, None);
                    self.failed = true;
                } else {
                    self.first.insert(name, self.source.span(node));
                    let class = param.ty.map(|ty| self.known(ty, node));
                    if let Some(local) = self.bind(name, node, class) {
                        self.params.push(local);
                    }
                }
            } else {
                self.failed = true;
            }
        }
        let header = &self.headers[self.owner];
        let result = header.result;
        let declared = header.declared;
        self.failed |= header.params.is_none() || result.is_none();
        let tree = self.source.tree;
        let root_node = item.body(tree)?.node();
        // At most one expression per node of the body.
        let nodes = tree.subtree_len(root_node);
        self.exprs.reserve(nodes);
        self.classes.reserve(nodes);
        self.subjects.reserve(nodes);
        let mut work = std::mem::take(&mut self.work);
        work.push(Work::Enter(root_node));
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(node) => self.enter(node, &mut work),
                Work::Finish(node) => {
                    if self.finish(node).is_none() {
                        self.failed = true;
                    }
                }
                Work::Call(node, target, callee) => {
                    if self.call(node, target, callee).is_none() {
                        self.failed = true;
                    }
                }
            }
        }
        self.work = work;
        let root = self.value(root_node);
        // A failed parameter does not erase an independently known result
        // type. A declared result is a contract on the body; an inferred one
        // is the body's own type.
        match (root, declared, result) {
            (Some(root), Some((ty, span)), _) => {
                self.require(
                    root_node,
                    root,
                    Expected::Ty(ty),
                    Some((span, "declared here")),
                );
            }
            (Some(root), None, Some(result)) => {
                self.require(root_node, root, Expected::Class(result), None);
            }
            _ => {}
        }
        if self.failed {
            return None;
        }
        Some(DraftBody {
            params: std::mem::take(&mut self.params),
            locals: std::mem::take(&mut self.locals),
            exprs: std::mem::take(&mut self.exprs),
            classes: std::mem::take(&mut self.classes),
            root: root?,
        })
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
    /// Give `name` the meaning `id` until the innermost scope closes.
    fn shadow(&mut self, name: &'s str, id: Option<LocalId>) {
        self.scopes[self.depth - 1].insert(name, id);
    }
    fn bind(&mut self, name: &'s str, node: NodeIdx, class: Option<Var>) -> Option<LocalId> {
        let id = class.map(|class| {
            let id = LocalId::new(self.locals.len());
            self.locals.push(DraftLocal {
                name,
                origin: self.source.span(node),
                class,
            });
            id
        });
        self.failed |= id.is_none();
        self.shadow(name, id);
        id
    }
    fn lookup(&self, name: &str) -> Option<Option<LocalId>> {
        self.scopes[..self.depth]
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }
    /// A class known to have `ty` because of `node`.
    fn known(&mut self, ty: Ty, node: NodeIdx) -> Var {
        self.typing.known(ty, self.source.span(node))
    }
    fn class(&self, expr: ExprId) -> Var {
        self.classes[expr.index()]
    }
    /// An expression of its own type.
    fn emit(&mut self, node: NodeIdx, kind: ExprKind, class: Var) -> ExprId {
        let id = ExprId::new(self.exprs.len());
        self.emit_as(node, kind, class, id)
    }
    /// An expression with the type of `inner`, one of its sub-expressions.
    fn emit_from(&mut self, node: NodeIdx, kind: ExprKind, inner: ExprId) -> ExprId {
        let (class, subject) = (self.class(inner), self.subjects[inner.index()]);
        self.emit_as(node, kind, class, subject)
    }
    fn emit_as(&mut self, node: NodeIdx, kind: ExprKind, class: Var, subject: ExprId) -> ExprId {
        let id = ExprId::new(self.exprs.len());
        self.exprs.push(Expr {
            kind,
            origin: self.source.span(node),
            // Resolved when the body is published.
            ty: Ty::Unit,
        });
        self.classes.push(class);
        self.subjects.push(subject);
        self.values[node.to_usize()] = Some(id);
        id
    }
    /// The context at `node` requires `expr` to be `expected`. Recorded for
    /// the verdict pass, and joined into the evidence now so inference sees
    /// it.
    fn require(
        &mut self,
        node: NodeIdx,
        expr: ExprId,
        expected: Expected,
        related: Option<(Span, &'static str)>,
    ) {
        let actual = self.class(expr);
        if expected == Expected::Class(actual) {
            return;
        }
        self.typing.expect(actual, expected, self.source.span(node));
        self.demand(node, expr, DemandKind::Type { expected, related });
    }
    fn demand(&mut self, node: NodeIdx, expr: ExprId, kind: DemandKind) {
        self.demands.push(Demand {
            owner: self.owner,
            subject: self.subjects[expr.index()],
            node,
            actual: self.class(expr),
            kind,
        });
    }
    fn unsupported(&mut self, node: NodeIdx) {
        self.source.error(
            node,
            codes::UNSUPPORTED,
            "construct is not supported by scalar checking",
            None,
        );
        self.failed = true;
    }
    fn enter(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        if let Some(binding) = ast::LetStmt::cast(tree, node) {
            let mutable = self
                .source
                .tokens(
                    tree.first_token(node),
                    binding
                        .name(tree)
                        .map_or(tree.end_token(node), |n| tree.first_token(n.node())),
                )
                .eq([SyntaxKind::LetKw, SyntaxKind::MutKw]);
            if tree.has_error(node) || mutable {
                if mutable && !tree.has_error(node) {
                    self.unsupported(node);
                }
                if let Some((name, name_node)) = self.source.name(binding.name(tree)) {
                    self.bind(name, name_node, None);
                }
                self.failed = true;
                return;
            }
        } else if tree.has_error(node) && tree.kind(node) != NodeKind::Block {
            self.failed = true;
            return;
        }
        if tree.kind(node) == NodeKind::Block {
            self.failed |= tree.has_error(node);
            self.open_scope();
        }
        if let Some(ast::Expr::PrefixExpr(prefix)) = ast::Expr::cast(tree, node) {
            let operand = prefix.operand(tree).unwrap();
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
        if let Some(call) = ast::CallExpr::cast(tree, node) {
            let callee = self.source.peel(call.callee(tree).unwrap()).node();
            let target = if tree.kind(callee) == NodeKind::NameRef {
                self.target(callee)
            } else {
                self.unsupported(callee);
                None
            };
            let list = call.arg_list(tree).unwrap();
            if let Some(target) = target {
                work.push(Work::Call(node, target, callee));
            } else {
                self.failed = true;
            }
            work.extend(
                tree.children(list.node())
                    .filter_map(|child| ast::Expr::cast(tree, child))
                    .map(|arg| Work::Enter(arg.node())),
            );
            return;
        }
        match tree.kind(node) {
            NodeKind::Block
            | NodeKind::LetStmt
            | NodeKind::DiscardStmt
            | NodeKind::PrefixExpr
            | NodeKind::BinaryExpr
            | NodeKind::ParenExpr
            | NodeKind::IfExpr => {
                work.push(Work::Finish(node));
                work.extend(
                    tree.children(node)
                        .filter(|&child| {
                            !matches!(tree.kind(child), NodeKind::Name | NodeKind::TypeRef)
                        })
                        .map(Work::Enter),
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
            if let Some(local) = local {
                self.source.error(
                    node,
                    codes::NOT_CALLABLE,
                    format!("local `{name}` is not callable"),
                    Some((self.locals[local.index()].origin, "declared here")),
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
    fn integer(&mut self, origin: NodeIdx, literal: NodeIdx, negative: bool) -> Option<ExprId> {
        let raw = self.source.tree.first_token(literal);
        if self
            .source
            .parsed
            .lexed()
            .flags(raw)
            .contains(TokenFlags::MALFORMED_NUMBER)
        {
            return None;
        }
        let value = self
            .source
            .text(literal)
            .bytes()
            .try_fold(0i64, |value, byte| {
                value.checked_mul(10)?.checked_sub(i64::from(byte - b'0'))
            })
            .and_then(|value| {
                if negative {
                    Some(value)
                } else {
                    value.checked_neg()
                }
            });
        match value {
            Some(value) => {
                let class = self.known(Ty::Int, origin);
                Some(self.emit(origin, ExprKind::Int(value), class))
            }
            None => {
                self.source.error(
                    literal,
                    codes::INTEGER_RANGE,
                    "integer literal is outside signed 64-bit range",
                    None,
                );
                None
            }
        }
    }
    fn value(&self, node: NodeIdx) -> Option<ExprId> {
        self.values[node.to_usize()]
    }
    fn finish(&mut self, node: NodeIdx) -> Option<()> {
        let tree = self.source.tree;
        match tree.kind(node) {
            NodeKind::Block => {
                self.close_scope();
                // Children arrive last first; only the first can be the tail.
                // Completed statements are stacked in source order. Nested
                // blocks consume their own statements before reaching here.
                let mut children = tree.children(node).peekable();
                let has_tail = children
                    .peek()
                    .is_some_and(|&last| self.statements.last().is_none_or(|(n, _)| *n != last));
                let count = tree.children(node).count() - usize::from(has_tail);
                let mut statements = Vec::with_capacity(count);
                let mut tail = None;
                let mut valid = !tree.has_error(node);
                for (index, child) in children.enumerate() {
                    if let Some((_, statement)) = self.statements.pop_if(|(node, _)| *node == child)
                    {
                        statements.push(statement);
                    } else if let Some(value) = self.value(child) {
                        if index == 0 {
                            tail = Some(value);
                        } else {
                            self.demand(child, value, DemandKind::Unused);
                            statements.push(Statement {
                                origin: self.source.span(child),
                                kind: StatementKind::Eval(value),
                            });
                        }
                    } else {
                        valid = false;
                    }
                }
                if !valid {
                    return None;
                }
                statements.reverse();
                match tail {
                    Some(tail) => {
                        let kind = ExprKind::Block {
                            statements,
                            tail: Some(tail),
                        };
                        self.emit_from(node, kind, tail);
                    }
                    None => {
                        let class = self.known(Ty::Unit, node);
                        self.emit(node, ExprKind::Block { statements, tail }, class);
                    }
                }
            }
            NodeKind::LetStmt => {
                let binding = ast::LetStmt::cast(tree, node).unwrap();
                let (name, name_node) = self.source.name(binding.name(tree))?;
                let initializer_node = binding.initializer(tree).unwrap().node();
                let initializer = self.value(initializer_node);
                // An annotated binding has its declared type whatever its
                // initializer turns out to be; the initializer is held to it.
                let class = match binding.type_ref(tree) {
                    Some(annotation) => self.source.ty(annotation).map(|ty| {
                        if let Some(value) = initializer {
                            self.require(
                                initializer_node,
                                value,
                                Expected::Ty(ty),
                                Some((self.source.span(annotation.node()), "declared here")),
                            );
                        }
                        self.known(ty, annotation.node())
                    }),
                    None => initializer.map(|value| self.class(value)),
                };
                let local = self.bind(name, name_node, class);
                self.statements.push((
                    node,
                    Statement {
                        origin: self.source.span(node),
                        kind: StatementKind::Let {
                            local: local?,
                            initializer: initializer?,
                        },
                    },
                ));
            }
            NodeKind::DiscardStmt => {
                let value = ast::DiscardStmt::cast(tree, node)
                    .unwrap()
                    .value(tree)
                    .unwrap();
                self.statements.push((
                    node,
                    Statement {
                        origin: self.source.span(node),
                        kind: StatementKind::Eval(self.value(value.node())?),
                    },
                ));
            }
            NodeKind::NameRef => {
                let name = self.source.text(node);
                match self.lookup(name) {
                    Some(Some(local)) => {
                        let class = self.locals[local.index()].class;
                        self.emit(node, ExprKind::Local(local), class);
                    }
                    Some(None) => return None,
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
                        let class = self.known(Ty::Bool, node);
                        self.emit(node, ExprKind::Bool(value), class);
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
                    .unwrap();
                self.values[node.to_usize()] = Some(self.value(inner.node())?);
            }
            NodeKind::PrefixExpr => {
                let operand = ast::PrefixExpr::cast(tree, node)
                    .unwrap()
                    .operand(tree)
                    .unwrap()
                    .node();
                let value = self.value(operand)?;
                let neg = self
                    .source
                    .tokens(tree.first_token(node), tree.first_token(operand))
                    .eq([SyntaxKind::Minus]);
                let ty = if neg { Ty::Int } else { Ty::Bool };
                self.require(operand, value, Expected::Ty(ty), None);
                let class = self.known(ty, node);
                self.emit(
                    node,
                    if neg {
                        ExprKind::Neg(value)
                    } else {
                        ExprKind::Not(value)
                    },
                    class,
                );
            }
            NodeKind::BinaryExpr => {
                use sumi_syntax::BinaryOp::*;

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
                // Raw tokens partition source: the immediately adjacent token
                // is glued, whereas any intervening trivia breaks a compound.
                let glued = (first + 1 < end).then(|| lexed.kind(first + 1));
                let (op, _) = sumi_syntax::binary_operator(lexed.kind(first), glued)
                    .expect("clean binary operator");
                let lhs = self.value(lhs_node);
                let rhs = self.value(rhs_node);
                // `==` and `!=` compare like with like: whichever operand
                // exists sets the other's expectation.
                let (operand, result) = match op {
                    Add | Sub | Mul | Div | Rem => (Some(Expected::Ty(Ty::Int)), Ty::Int),
                    Lt | Le | Gt | Ge => (Some(Expected::Ty(Ty::Int)), Ty::Bool),
                    Eq | Ne => (
                        lhs.or(rhs).map(|id| Expected::Class(self.class(id))),
                        Ty::Bool,
                    ),
                    And | Or => (Some(Expected::Ty(Ty::Bool)), Ty::Bool),
                };
                if let Some(operand) = operand {
                    for (child, value) in [(lhs_node, lhs), (rhs_node, rhs)] {
                        if let Some(value) = value {
                            self.require(child, value, operand, None);
                        }
                    }
                    if let Some(operand) = lhs.or(rhs) {
                        self.demand(node, operand, DemandKind::Comparable);
                    }
                }
                let (lhs, rhs) = (lhs?, rhs?);
                let class = self.known(result, node);
                self.emit(node, ExprKind::binary(op, lhs, rhs), class);
            }
            NodeKind::IfExpr => {
                let branch = ast::IfExpr::cast(tree, node).unwrap();
                let condition_node = branch.condition(tree).unwrap().node();
                let condition = self.value(condition_node);
                let then_node = branch.then_branch(tree).unwrap().node();
                let then_branch = self.value(then_node);
                let else_node = branch.else_branch(tree).map(|e| e.node());
                let else_branch = else_node.and_then(|n| self.value(n));
                if let Some(condition) = condition {
                    self.require(condition_node, condition, Expected::Ty(Ty::Bool), None);
                }
                // The branches agree; without an else, the then branch is unit.
                let expected = match else_node {
                    Some(_) => else_branch.map(|id| Expected::Class(self.class(id))),
                    None => Some(Expected::Ty(Ty::Unit)),
                };
                if let (Some(then_branch), Some(expected)) = (then_branch, expected) {
                    self.require(
                        then_node,
                        then_branch,
                        expected,
                        else_node.map(|n| {
                            (self.source.span(n), "other branch determines expected type")
                        }),
                    );
                }
                if else_node.is_some() && else_branch.is_none() {
                    return None;
                }
                let then_branch = then_branch?;
                self.emit_from(
                    node,
                    ExprKind::If {
                        condition: condition?,
                        then_branch,
                        else_branch,
                    },
                    then_branch,
                );
            }
            _ => unreachable!("scheduled supported node"),
        }
        Some(())
    }
    fn call(&mut self, node: NodeIdx, target: FunctionId, callee: NodeIdx) -> Option<()> {
        let function = &self.headers[target.index()];
        let params = function.params.as_ref()?;
        let origin = function.origin;
        let result = function.result;
        let tree = self.source.tree;
        let list = ast::CallExpr::cast(tree, node)
            .unwrap()
            .arg_list(tree)
            .unwrap();
        // Every argument that exists is held to its parameter, arity aside.
        let mut args = Vec::with_capacity(params.len());
        let mut complete = true;
        let mut count = 0;
        for (index, arg) in list.args(tree).enumerate() {
            count += 1;
            let arg = arg.node();
            match self.value(arg) {
                Some(value) => {
                    if let Some(&expected) = params.get(index) {
                        self.require(
                            arg,
                            value,
                            Expected::Ty(expected),
                            Some((origin, "declared here")),
                        );
                    }
                    args.push(value);
                }
                None => complete = false,
            }
        }
        if count != params.len() {
            self.source.error(
                node,
                codes::ARITY,
                format!("expected {} arguments, found {count}", params.len()),
                Some((origin, "declared here")),
            );
            return None;
        }
        if !complete {
            return None;
        }
        let class = self.typing.call(result?, self.source.span(node));
        self.emit(
            node,
            ExprKind::Call {
                function: target,
                args,
                callee: self.source.span(callee),
            },
            class,
        );
        Some(())
    }
}
