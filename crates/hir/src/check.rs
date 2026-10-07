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
//!    and operator results, a flow for each call and for each branch into
//!    its `if`, and a demand wherever a context requires an expression to
//!    have a type. The walk rejects nothing on type grounds. Where the
//!    parser recovered, a name is undeclared, or a construct is unsupported,
//!    it leaves a hole: a class and no expression, typed as far as the
//!    syntax around it decides and claiming the unknown otherwise, so the
//!    rest of the body is checked as if the hole were whatever it should
//!    be. A body with a hole is never published.
//! 3. **Verdicts.** The typing solves once. Signatures are read off result
//!    classes, independent of declaration order. Demands are then checked in
//!    source order against the final evidence, so a disagreement is blamed on
//!    the first demand that raised it. Every expression has one context, so
//!    it is held to one demand; an expression whose type is undetermined,
//!    because its branches or its callee disagree, satisfies any demand
//!    silently, and the disagreement is reported where it arose. A body is
//!    published when its walk succeeded, none of its demands failed, every
//!    class it uses resolved, and every function it calls has a signature.
//!
//! Names are never copied while checking: every map is keyed by a slice of
//! the source, and the one builder keeps its scratch across bodies, so a
//! body costs the vectors it publishes and nothing else.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::{BuildHasherDefault, Hasher};
use std::num::NonZeroU32;

use sumi_frontend::{DiagnosticCode, Label, Location};
use sumi_lexer::{RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    NodeIdx, NodeKind, SyntaxTree,
    ast::{self, AstNode},
};

use crate::codes;
use crate::solver::Var;
use crate::typing::{Claim, Expected, Typing};
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
        let (words, rest) = bytes.as_chunks::<8>();
        for word in words {
            self.add(u64::from_le_bytes(*word));
        }
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
    declared: Option<(Ty, NodeIdx)>,
    item: NodeIdx,
}

struct DraftLocal {
    origin: Span,
    class: Var,
}

/// A body whose expressions are built, with a placeholder type on each
/// until its class resolves.
struct DraftBody {
    params: Vec<LocalId>,
    locals: Vec<DraftLocal>,
    exprs: Vec<Expr>,
    /// The class of each expression, by index.
    classes: Vec<Var>,
    args: Vec<ExprId>,
    statements: Vec<Statement>,
    root: ExprId,
}

impl DraftBody {
    /// The body with every class resolved to its type, if every class
    /// resolved and every call agrees with its callee's signature.
    fn publish(self, typing: &Typing, functions: &[Function]) -> Option<Body> {
        let Self {
            params,
            locals,
            mut exprs,
            classes,
            args,
            statements,
            root,
        } = self;
        let locals = locals
            .into_iter()
            .map(|local| {
                Some(Local {
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
            args,
            statements,
            root,
        })
    }
}

/// What a context requires of an expression, checked after solving.
enum DemandKind {
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
    Agree { branches: [Var; 2] },
    /// A local is called: only function items are callable, since every
    /// local holds a scalar. Silent while the local's type is undetermined.
    Callable { declared: Span },
}

/// One demand, kept small: the verdict pass reads every one, and a body
/// makes one per operand, argument, branch, and statement.
struct Demand {
    owner: u32,
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
    /// Report that `node` is claimed to be every type in `claims`, in
    /// source order, and where each claim was made. `message` wraps the
    /// list of types.
    fn conflict(
        &mut self,
        node: NodeIdx,
        code: DiagnosticCode,
        typing: &Typing,
        claims: &[(Ty, Claim)],
        message: impl FnOnce(String) -> String,
    ) {
        let mut claims: Vec<_> = claims
            .iter()
            .map(|(ty, claim)| (*ty, typing.origin(*claim).map(|node| self.span(node))))
            .collect();
        claims.sort_by_key(|(_, origin)| origin.map(|span| span.range().start()));
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
        self.report(self.span(node), code, message(joined), labels);
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
    /// `expr` without the parentheses around it; none when they are empty.
    fn peel(&self, mut expr: ast::Expr) -> Option<ast::Expr> {
        while let ast::Expr::ParenExpr(paren) = expr {
            expr = paren.inner(self.tree)?;
        }
        Some(expr)
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
    let mut typing = Typing::for_nodes(tree.len());

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
                // An item's parameter has a type or a syntax error: the
                // parser requires the annotation.
                let ty = param.type_ref(tree).and_then(|ty| source.ty(ty));
                valid &= ty.is_some();
                params.push(Parameter {
                    name: source.name(param.name(tree)),
                    ty,
                });
            }
        }
        let (result, declared) = if let Some(ret) = item.ret(tree) {
            match source.ty(ret) {
                Some(ty) => (Some(typing.known(ty, ret.node())), Some((ty, ret.node()))),
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
                    Some(typing.known(Ty::Unit, item.node())),
                    Some((Ty::Unit, item.node())),
                ),
                Some((Some(SyntaxKind::Eq), None)) => (Some(typing.fresh()), None),
                _ => (None, None),
            }
        };
        headers.push(Header {
            params: valid.then(|| params.iter().map(|p| p.ty.unwrap()).collect()),
            result,
            declared,
            item: item.node(),
        });
        parameters.push(params);
        functions.push(Function {
            name: name.map(|(_, node)| source.span(node)),
            origin,
            signature: None,
            body: None,
        });
    }

    // Pass 2: bodies.
    // About a demand per two nodes; only a guide.
    let mut demands = Vec::with_capacity(tree.len() / 2);
    let mut bodies = Vec::with_capacity(items.len());
    // Syntax node IDs are dense and bodies have disjoint nodes. Expression
    // IDs remain body-local; a builder only reads entries in its own body.
    let mut values: Vec<Option<Slot>> = vec![None; tree.len()];
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
    for demand in demands {
        let actual = replay.resolve(demand.actual);
        match demand.kind {
            DemandKind::Type { expected, declared } => {
                let expected_ty = match expected {
                    Expected::Ty(ty) => Some(ty),
                    Expected::Class(class) => replay.resolve(class),
                };
                match (actual, expected_ty) {
                    (Some(actual), Some(expected)) if actual != expected => {
                        let related = declared.map(|node| (source.span(node), "declared here"));
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
            // Each branch delivers what it is so far, and only that: a
            // conflict on the `if` is the branches disagreeing, and nothing
            // else. The `if` then resolves to nothing, so whatever takes its
            // type is held to no type it never had.
            DemandKind::Agree { branches } => {
                for branch in branches {
                    replay.branch(branch, demand.actual);
                }
                let evidence = *replay.evidence(demand.actual);
                if !evidence.is_conflict() {
                    continue;
                }
                source.conflict(
                    demand.node,
                    codes::TYPE_MISMATCH,
                    &typing,
                    &evidence.claims(),
                    |types| format!("if branches are {types}"),
                );
            }
            DemandKind::Callable { declared } => {
                if actual.is_none() {
                    continue;
                }
                let name = source.text(demand.node);
                source.error(
                    demand.node,
                    codes::NOT_CALLABLE,
                    format!("local `{name}` is not callable"),
                    Some((declared, "declared here")),
                );
            }
        }
        failed[demand.owner as usize] = true;
    }
    for (index, header) in headers.into_iter().enumerate() {
        let evidence = header.result.map(|result| *typing.evidence(result));
        let result = evidence.and_then(|evidence| evidence.ty());
        if let (Some(params), Some(result)) = (header.params, result) {
            functions[index].signature = Some(Signature { params, result });
        }
        // A result to infer that did not resolve is reported here, unless a
        // demand in the body already explained it, a hole decided it, or the
        // trouble arrived whole from a callee, which reports it at its own
        // declaration.
        if let (None, Some(evidence), None) = (header.declared, evidence, result)
            && bodies[index].is_some()
            && !failed[index]
            && !evidence.unknown()
            && !evidence.inherited()
        {
            let node = items[index].node();
            if evidence.is_conflict() {
                source.conflict(
                    node,
                    codes::CANNOT_INFER,
                    &typing,
                    &evidence.claims(),
                    |types| {
                        format!("function result is both {types}; add a return type annotation")
                    },
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

/// An index into one of a body's lists, which the syntax tree's node count
/// bounds.
fn run(index: usize) -> u32 {
    u32::try_from(index).expect("list index fits u32")
}

// Scope transitions and let completion are explicit work items, so
// initializers see the old scope.
type Scope<'s> = NameMap<'s, LocalId>;
enum Work {
    Enter(NodeIdx),
    Finish(NodeIdx),
    Call(NodeIdx, FunctionId, NodeIdx),
}

/// What an expression node is worth to its context: the class its type is,
/// and the expression built for it, which a hole has none of. Every
/// expression node the walk visits leaves one, so a damaged construct is
/// typed around rather than skipped: an operator missing an operand still
/// has its result type, a call missing an argument still has its callee's
/// result, and a construct whose type nothing decides claims the unknown.
#[derive(Clone, Copy)]
struct Value {
    class: Var,
    expr: Option<ExprId>,
}

/// What a node left, in one word: an expression, whose class the body's
/// list holds, or a hole, whose class is kept aside under the top bit. The
/// table over every node of the file is sized by this.
#[derive(Clone, Copy)]
struct Slot(NonZeroU32);

const HOLE: u32 = 1 << 31;

impl Slot {
    fn expr(id: ExprId) -> Self {
        Self(id.0)
    }
    fn hole(index: usize) -> Self {
        let index = u32::try_from(index + 1).expect("hole count fits u32");
        assert!(index < HOLE, "hole count fits below the hole bit");
        Self(NonZeroU32::new(index | HOLE).unwrap())
    }
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
    values: &'a mut [Option<Slot>],
    // The body under construction.
    owner: u32,
    /// Whether the body has a hole, a syntax error, or a declaration it
    /// cannot bind: it is still checked, and never published.
    failed: bool,
    params: Vec<LocalId>,
    locals: Vec<DraftLocal>,
    exprs: Vec<Expr>,
    classes: Vec<Var>,
    /// The class of each hole, by its slot's index.
    holes: Vec<Var>,
    args: Vec<ExprId>,
    statements: Vec<Statement>,
    // Scratch kept across bodies.
    /// A pool of scopes; the first `depth` are open, innermost last. A map
    /// per scope costs a probe per enclosing scope on lookup, and nothing on
    /// close; an undo log measured slower on binding-heavy code, since every
    /// binding then pays a removal.
    scopes: Vec<Scope<'s>>,
    depth: usize,
    /// Parameter names seen so far, for duplicates.
    first: NameMap<'s, Span>,
    work: Vec<Work>,
    /// Statements completed but not yet claimed by their block, in source
    /// order.
    pending: Vec<(NodeIdx, Statement)>,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
        source: &'a mut Source<'s>,
        headers: &'a [Header],
        names: &'a NameMap<'s, Named>,
        typing: &'a mut Typing,
        demands: &'a mut Vec<Demand>,
        values: &'a mut [Option<Slot>],
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
            holes: Vec::new(),
            args: Vec::new(),
            statements: Vec::new(),
            scopes: Vec::new(),
            depth: 0,
            first: NameMap::default(),
            work: Vec::new(),
            pending: Vec::new(),
        }
    }
    fn build(
        &mut self,
        owner: usize,
        item: ast::FnItem,
        parameters: Vec<Parameter<'s>>,
    ) -> Option<DraftBody> {
        self.owner = u32::try_from(owner).expect("function count fits u32");
        self.failed = false;
        self.depth = 0;
        self.open_scope();
        self.first.clear();
        // A published body took these; a failed one left them behind.
        self.params.clear();
        self.locals.clear();
        self.exprs.clear();
        self.classes.clear();
        self.holes.clear();
        self.args.clear();
        self.statements.clear();
        for param in parameters {
            let Some((name, node)) = param.name else {
                self.failed = true;
                continue;
            };
            if let Some(&span) = self.first.get(name) {
                // Which declaration a use means is ambiguous, so its type
                // is unknown.
                self.source.error(
                    node,
                    codes::DUPLICATE_NAME,
                    format!("duplicate parameter `{name}`"),
                    Some((span, "declared here")),
                );
                let class = self.typing.unknown();
                self.bind(name, node, class);
                self.failed = true;
            } else {
                self.first.insert(name, self.source.span(node));
                let class = match param.ty {
                    Some(ty) => self.typing.known(ty, node),
                    None => self.typing.unknown(),
                };
                let local = self.bind(name, node, class);
                self.params.push(local);
            }
        }
        let header = &self.headers[self.owner as usize];
        let result = header.result;
        let declared = header.declared;
        self.failed |= header.params.is_none() || result.is_none();
        let tree = self.source.tree;
        let root_node = item.body(tree)?.node();
        self.failed |= tree.has_error(root_node);
        // At most one expression per node of the body.
        let nodes = tree.subtree_len(root_node);
        self.exprs.reserve(nodes);
        self.classes.reserve(nodes);
        let mut work = std::mem::take(&mut self.work);
        work.push(Work::Enter(root_node));
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(node) => self.enter(node, &mut work),
                Work::Finish(node) => self.finish(node),
                Work::Call(node, target, callee) => self.call(node, target, callee),
            }
        }
        self.work = work;
        let root = self.value(root_node);
        // A failed parameter does not erase an independently known result
        // type. A declared result is a contract on the body; an inferred one
        // is the body's own type.
        match (root, declared, result) {
            (Some(root), Some((ty, node)), _) => {
                self.require(root_node, root.class, Expected::Ty(ty), Some(node));
            }
            (Some(root), None, Some(result)) => {
                self.require(root_node, root.class, Expected::Class(result), None);
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
            args: std::mem::take(&mut self.args),
            statements: std::mem::take(&mut self.statements),
            root: root?.expr?,
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
    /// Declare `name` at `node` as a local of class `class`, until the
    /// innermost scope closes.
    fn bind(&mut self, name: &'s str, node: NodeIdx, class: Var) -> LocalId {
        let id = LocalId::new(self.locals.len());
        self.locals.push(DraftLocal {
            origin: self.source.span(node),
            class,
        });
        self.scopes[self.depth - 1].insert(name, id);
        id
    }
    fn lookup(&self, name: &str) -> Option<LocalId> {
        // An empty scope, the common case for a function's own, would cost
        // a hash to find nothing in.
        self.scopes[..self.depth]
            .iter()
            .rev()
            .filter(|scope| !scope.is_empty())
            .find_map(|scope| scope.get(name).copied())
    }
    /// An expression of the type `class` resolves to.
    fn emit(&mut self, node: NodeIdx, kind: ExprKind, class: Var) -> Value {
        let id = ExprId::new(self.exprs.len());
        self.exprs.push(Expr {
            kind,
            origin: self.source.span(node),
            // Resolved when the body is published.
            ty: Ty::Unit,
        });
        self.classes.push(class);
        self.values[node.to_usize()] = Some(Slot::expr(id));
        Value {
            class,
            expr: Some(id),
        }
    }
    /// A node with no expression, of whatever type `class` resolves to:
    /// its context is checked against it, and the body is not published.
    fn hole(&mut self, node: NodeIdx, class: Var) -> Value {
        self.failed = true;
        self.values[node.to_usize()] = Some(Slot::hole(self.holes.len()));
        self.holes.push(class);
        Value { class, expr: None }
    }
    /// A hole whose type nothing decides.
    fn unknown(&mut self, node: NodeIdx) -> Value {
        let class = self.typing.unknown();
        self.hole(node, class)
    }
    /// The context at `node` requires the class `actual` to be `expected`,
    /// which `declared` may have set. Recorded for the verdict pass, and
    /// joined into the evidence now so inference sees it.
    fn require(
        &mut self,
        node: NodeIdx,
        actual: Var,
        expected: Expected,
        declared: Option<NodeIdx>,
    ) {
        if expected == Expected::Class(actual) {
            return;
        }
        self.typing.expect(actual, expected, node);
        self.demand(node, actual, DemandKind::Type { expected, declared });
    }
    fn demand(&mut self, node: NodeIdx, actual: Var, kind: DemandKind) {
        self.demands.push(Demand {
            owner: self.owner,
            node,
            actual,
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
    /// Whether the binding at `node` is `let mut`.
    fn mutable(&self, node: NodeIdx) -> bool {
        let tree = self.source.tree;
        let binding = ast::LetStmt::cast(tree, node).unwrap();
        let end = binding
            .name(tree)
            .map_or(tree.end_token(node), |name| tree.first_token(name.node()));
        self.source
            .tokens(tree.first_token(node), end)
            .eq([SyntaxKind::LetKw, SyntaxKind::MutKw])
    }
    /// Whether the prefix expression at `node` is a negation: its operator
    /// is its first token.
    fn negates(&self, node: NodeIdx) -> bool {
        let lexed = self.source.parsed.lexed();
        lexed.kind(self.source.tree.first_token(node)) == SyntaxKind::Minus
    }
    fn enter(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        match tree.kind(node) {
            // Garbage the parser skipped: reported there, and nothing in it
            // stands where an expression does.
            NodeKind::Error => return,
            NodeKind::LetStmt => {
                if self.mutable(node) && !tree.has_error(node) {
                    self.unsupported(node);
                }
            }
            NodeKind::Block => self.open_scope(),
            NodeKind::PrefixExpr => {
                // `-` glued to an integer literal is one negative literal,
                // which is how the minimum is written.
                let prefix = ast::PrefixExpr::cast(tree, node).unwrap();
                if let Some(operand) = prefix
                    .operand(tree)
                    .and_then(|operand| self.source.peel(operand))
                    && self.negates(node)
                    && tree.kind(operand.node()) == NodeKind::LiteralExpr
                    && self
                        .source
                        .parsed
                        .lexed()
                        .kind(tree.first_token(operand.node()))
                        == SyntaxKind::IntLiteral
                {
                    self.integer(node, operand.node(), true);
                    return;
                }
            }
            NodeKind::CallExpr => {
                let call = ast::CallExpr::cast(tree, node).unwrap();
                let callee = call
                    .callee(tree)
                    .and_then(|callee| self.source.peel(callee))
                    .map(|callee| callee.node());
                let target = match callee {
                    Some(callee) if tree.kind(callee) == NodeKind::NameRef => {
                        self.target(callee).map(|target| (target, callee))
                    }
                    Some(callee) => {
                        self.unsupported(callee);
                        None
                    }
                    // Missing or garbage: the parser reported it.
                    None => None,
                };
                match target {
                    Some((target, callee)) => work.push(Work::Call(node, target, callee)),
                    None => {
                        self.unknown(node);
                    }
                }
                if let Some(list) = call.arg_list(tree) {
                    work.extend(
                        tree.children(list.node())
                            .filter_map(|child| ast::Expr::cast(tree, child))
                            .map(|arg| Work::Enter(arg.node())),
                    );
                }
                return;
            }
            NodeKind::NameRef | NodeKind::LiteralExpr => {
                self.finish(node);
                return;
            }
            NodeKind::DiscardStmt
            | NodeKind::BinaryExpr
            | NodeKind::ParenExpr
            | NodeKind::IfExpr => {}
            _ => {
                self.unsupported(node);
                self.unknown(node);
                return;
            }
        }
        work.push(Work::Finish(node));
        work.extend(
            tree.children(node)
                .filter(|&child| !matches!(tree.kind(child), NodeKind::Name | NodeKind::TypeRef))
                .map(Work::Enter),
        );
    }
    /// The function the call through the name at `node` targets. A local
    /// is not one: whether it is callable is a demand on its type.
    fn target(&mut self, node: NodeIdx) -> Option<FunctionId> {
        let name = self.source.text(node);
        if let Some(local) = self.lookup(name) {
            let local = &self.locals[local.index()];
            let (class, declared) = (local.class, local.origin);
            self.demand(node, class, DemandKind::Callable { declared });
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
    /// The integer literal at `literal`, as the value of `origin`: an int
    /// whatever its digits, a hole when they are malformed or out of range.
    fn integer(&mut self, origin: NodeIdx, literal: NodeIdx, negative: bool) -> Value {
        let class = self.typing.known(Ty::Int, origin);
        let raw = self.source.tree.first_token(literal);
        if self
            .source
            .parsed
            .lexed()
            .flags(raw)
            .contains(TokenFlags::MALFORMED_NUMBER)
        {
            return self.hole(origin, class);
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
            Some(value) => self.emit(origin, ExprKind::Int(value), class),
            None => {
                self.source.error(
                    literal,
                    codes::INTEGER_RANGE,
                    "integer literal is outside signed 64-bit range",
                    None,
                );
                self.hole(origin, class)
            }
        }
    }
    fn value(&self, node: NodeIdx) -> Option<Value> {
        let raw = self.values[node.to_usize()]?.0.get();
        Some(if raw & HOLE == 0 {
            let expr = ExprId(NonZeroU32::new(raw).unwrap());
            Value {
                class: self.classes[expr.index()],
                expr: Some(expr),
            }
        } else {
            Value {
                class: self.holes[(raw & !HOLE) as usize - 1],
                expr: None,
            }
        })
    }
    /// The value of the expression node `node`, which the walk visited.
    fn visited(&self, node: NodeIdx) -> Value {
        self.value(node)
            .expect("every expression node leaves a value")
    }
    fn finish(&mut self, node: NodeIdx) {
        let tree = self.source.tree;
        match tree.kind(node) {
            NodeKind::Block => {
                self.close_scope();
                // Children arrive last first; only the first can be the tail.
                // Completed statements are pending in source order, and
                // nested blocks claimed theirs before reaching here, so the
                // block's run of the body's list is filled backwards and
                // reversed in place.
                let start = self.statements.len();
                let mut tail = None;
                let mut complete = true;
                let mut garbage_tail = false;
                for (index, child) in tree.children(node).enumerate() {
                    if let Some((_, statement)) = self.pending.pop_if(|(node, _)| *node == child) {
                        self.statements.push(statement);
                    } else if let Some(value) = self.value(child) {
                        if index == 0 {
                            tail = Some(value);
                        } else {
                            self.demand(child, value.class, DemandKind::Unused);
                            match value.expr {
                                Some(expr) => self.statements.push(Statement {
                                    origin: self.source.span(child),
                                    kind: StatementKind::Eval(expr),
                                }),
                                None => complete = false,
                            }
                        }
                    } else {
                        // A statement that could not be built, or garbage.
                        complete = false;
                        garbage_tail |= index == 0 && tree.kind(child) == NodeKind::Error;
                    }
                }
                // A block has its tail's type, or is unit without one, unless
                // garbage stands where the tail would.
                let class = match tail {
                    Some(tail) => tail.class,
                    None if garbage_tail => self.typing.unknown(),
                    None => self.typing.known(Ty::Unit, node),
                };
                let tail = tail.map(|tail| tail.expr);
                match tail {
                    Some(Some(_)) | None if complete => {
                        self.statements[start..].reverse();
                        let statements = Statements {
                            start: run(start),
                            end: run(self.statements.len()),
                        };
                        self.emit(
                            node,
                            ExprKind::Block {
                                statements,
                                tail: tail.flatten(),
                            },
                            class,
                        );
                    }
                    _ => {
                        self.statements.truncate(start);
                        self.hole(node, class);
                    }
                }
            }
            NodeKind::LetStmt => {
                let binding = ast::LetStmt::cast(tree, node).unwrap();
                let initializer = binding.initializer(tree).map(|e| e.node());
                let value = initializer.map(|node| self.visited(node));
                let class = if self.mutable(node) {
                    // Mutation is not checked, so what the binding holds is
                    // unknown.
                    self.typing.unknown()
                } else {
                    match binding.type_ref(tree) {
                        // An annotated binding has its declared type whatever
                        // its initializer turns out to be; the initializer is
                        // held to it.
                        Some(annotation) => match self.source.ty(annotation) {
                            Some(ty) => {
                                if let (Some(node), Some(value)) = (initializer, value) {
                                    self.require(
                                        node,
                                        value.class,
                                        Expected::Ty(ty),
                                        Some(annotation.node()),
                                    );
                                }
                                self.typing.known(ty, annotation.node())
                            }
                            None => self.typing.unknown(),
                        },
                        None => match value {
                            Some(value) => value.class,
                            None => self.typing.unknown(),
                        },
                    }
                };
                let Some((name, name_node)) = self.source.name(binding.name(tree)) else {
                    self.failed = true;
                    return;
                };
                let local = self.bind(name, name_node, class);
                match value.and_then(|value| value.expr) {
                    Some(initializer) => self.pending.push((
                        node,
                        Statement {
                            origin: self.source.span(node),
                            kind: StatementKind::Let { local, initializer },
                        },
                    )),
                    None => self.failed = true,
                }
            }
            NodeKind::DiscardStmt => {
                let value = ast::DiscardStmt::cast(tree, node)
                    .unwrap()
                    .value(tree)
                    .map(|value| self.visited(value.node()));
                match value.and_then(|value| value.expr) {
                    Some(expr) => self.pending.push((
                        node,
                        Statement {
                            origin: self.source.span(node),
                            kind: StatementKind::Eval(expr),
                        },
                    )),
                    None => self.failed = true,
                }
            }
            NodeKind::NameRef => {
                let name = self.source.text(node);
                match self.lookup(name) {
                    Some(local) => {
                        let class = self.locals[local.index()].class;
                        self.emit(node, ExprKind::Local(local), class);
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
                        }
                        self.unknown(node);
                    }
                }
            }
            NodeKind::LiteralExpr => {
                match self.source.parsed.lexed().kind(tree.first_token(node)) {
                    SyntaxKind::IntLiteral => {
                        self.integer(node, node, false);
                    }
                    _ if matches!(self.source.text(node), "true" | "false") => {
                        let value = self.source.text(node) == "true";
                        let class = self.typing.known(Ty::Bool, node);
                        self.emit(node, ExprKind::Bool(value), class);
                    }
                    _ => {
                        self.unsupported(node);
                        self.unknown(node);
                    }
                }
            }
            NodeKind::ParenExpr => {
                let inner_node = ast::ParenExpr::cast(tree, node)
                    .unwrap()
                    .inner(tree)
                    .map(|inner| inner.node());
                match inner_node {
                    // The parentheses leave what their contents did.
                    Some(inner) => self.values[node.to_usize()] = self.values[inner.to_usize()],
                    None => {
                        self.unknown(node);
                    }
                }
            }
            NodeKind::PrefixExpr => {
                let operand = ast::PrefixExpr::cast(tree, node)
                    .unwrap()
                    .operand(tree)
                    .map(|operand| operand.node());
                let value = operand.map(|operand| self.visited(operand));
                let neg = self.negates(node);
                let ty = if neg { Ty::Int } else { Ty::Bool };
                if let (Some(operand), Some(value)) = (operand, value) {
                    self.require(operand, value.class, Expected::Ty(ty), None);
                }
                let class = self.typing.known(ty, node);
                match value.and_then(|value| value.expr) {
                    Some(expr) => {
                        let kind = if neg {
                            ExprKind::Neg(expr)
                        } else {
                            ExprKind::Not(expr)
                        };
                        self.emit(node, kind, class);
                    }
                    None => {
                        self.hole(node, class);
                    }
                }
            }
            NodeKind::BinaryExpr => {
                use sumi_syntax::BinaryOp::*;

                let binary = ast::BinaryExpr::cast(tree, node).unwrap();
                let lhs_node = binary.lhs(tree).map(|lhs| lhs.node());
                let rhs_node = binary.rhs(tree).map(|rhs| rhs.node());
                let lexed = self.source.parsed.lexed();
                // The operator is the first significant token after the left
                // operand, or of the node without one.
                let from = lhs_node.map_or(tree.first_token(node), |lhs| tree.end_token(lhs));
                let end = rhs_node.map_or(tree.end_token(node), |rhs| tree.first_token(rhs));
                let first = from.until(end).find(|&raw| !lexed.kind(raw).is_trivia());
                // Raw tokens partition source: the immediately adjacent token
                // is glued, whereas any intervening trivia breaks a compound.
                let op = first.and_then(|first| {
                    let glued = (first + 1 < end).then(|| lexed.kind(first + 1));
                    sumi_syntax::binary_operator(lexed.kind(first), glued).map(|(op, _)| op)
                });
                let Some(op) = op else {
                    self.unknown(node);
                    return;
                };
                let lhs = lhs_node.map(|lhs| self.visited(lhs));
                let rhs = rhs_node.map(|rhs| self.visited(rhs));
                // `==` and `!=` compare like with like: whichever operand
                // exists sets the other's expectation.
                let (operand, result) = match op {
                    Add | Sub | Mul | Div | Rem => (Some(Expected::Ty(Ty::Int)), Ty::Int),
                    Lt | Le | Gt | Ge => (Some(Expected::Ty(Ty::Int)), Ty::Bool),
                    Eq | Ne => (
                        lhs.or(rhs).map(|value| Expected::Class(value.class)),
                        Ty::Bool,
                    ),
                    And | Or => (Some(Expected::Ty(Ty::Bool)), Ty::Bool),
                };
                if let Some(operand) = operand {
                    for (child, value) in [(lhs_node, lhs), (rhs_node, rhs)] {
                        if let (Some(child), Some(value)) = (child, value) {
                            self.require(child, value.class, operand, None);
                        }
                    }
                    if let Some(value) = lhs.or(rhs) {
                        self.demand(node, value.class, DemandKind::Comparable);
                    }
                }
                let class = self.typing.known(result, node);
                match (
                    lhs.and_then(|value| value.expr),
                    rhs.and_then(|value| value.expr),
                ) {
                    (Some(lhs), Some(rhs)) => {
                        self.emit(node, ExprKind::binary(op, lhs, rhs), class);
                    }
                    _ => {
                        self.hole(node, class);
                    }
                }
            }
            NodeKind::IfExpr => {
                let branch = ast::IfExpr::cast(tree, node).unwrap();
                let condition_node = branch.condition(tree).map(|c| c.node());
                let condition = condition_node.map(|node| self.visited(node));
                if let (Some(node), Some(condition)) = (condition_node, condition) {
                    self.require(node, condition.class, Expected::Ty(Ty::Bool), None);
                }
                let then_node = branch.then_branch(tree).map(|b| b.node());
                let then_branch = then_node.map(|node| self.visited(node));
                let else_node = branch.else_branch(tree).map(|e| e.node());
                let else_branch = else_node.map(|node| self.visited(node));
                // An `else` whose branch is missing is still an else: the
                // keyword stands after the then branch, outside any child.
                let after_then = then_node
                    .or(condition_node)
                    .map_or(tree.first_token(node), |child| tree.end_token(child));
                let has_else = else_node.is_some()
                    || self
                        .source
                        .tokens(after_then, tree.end_token(node))
                        .any(|kind| kind == SyntaxKind::ElseKw);
                let exprs = (
                    condition.and_then(|value| value.expr),
                    then_branch.and_then(|value| value.expr),
                    else_branch.and_then(|value| value.expr),
                );
                if !has_else {
                    // Without an else, the then branch is unit, and so is
                    // the `if`.
                    if let (Some(node), Some(then_branch)) = (then_node, then_branch) {
                        self.require(node, then_branch.class, Expected::Ty(Ty::Unit), None);
                    }
                    let class = self.typing.known(Ty::Unit, node);
                    match exprs {
                        (Some(condition), Some(then_branch), _) => {
                            self.emit(
                                node,
                                ExprKind::If {
                                    condition,
                                    then_branch,
                                    else_branch: None,
                                },
                                class,
                            );
                        }
                        _ => {
                            self.hole(node, class);
                        }
                    }
                    return;
                }
                // Each branch decides the `if` and learns nothing from the
                // other, so branches that disagree leave the `if`
                // undetermined, conflicted on its own class, and keep their
                // own types. The verdict pass reports it there. A missing
                // branch decides nothing.
                let mut branches = [then_branch, else_branch].map(|branch| branch.map(|b| b.class));
                for branch in &mut branches {
                    if branch.is_none() {
                        *branch = Some(self.typing.unknown());
                    }
                }
                let branches = branches.map(|branch| branch.unwrap());
                let join = self.typing.fresh();
                for branch in branches {
                    self.typing.branch(branch, join);
                }
                match exprs {
                    (Some(condition), Some(then_branch), Some(else_branch)) => {
                        self.emit(
                            node,
                            ExprKind::If {
                                condition,
                                then_branch,
                                else_branch: Some(else_branch),
                            },
                            join,
                        );
                    }
                    _ => {
                        self.hole(node, join);
                    }
                }
                self.demand(node, join, DemandKind::Agree { branches });
            }
            _ => unreachable!("scheduled supported node"),
        }
    }
    fn call(&mut self, node: NodeIdx, target: FunctionId, callee: NodeIdx) {
        let headers = self.headers;
        let function = &headers[target.index()];
        let Some(params) = function.params.as_ref() else {
            // A declaration too damaged to check calls against.
            self.unknown(node);
            return;
        };
        let item = function.item;
        let result = function.result;
        let tree = self.source.tree;
        let list = ast::CallExpr::cast(tree, node).unwrap().arg_list(tree);
        // Every argument that exists is held to its parameter, arity aside,
        // until garbage in the list makes the positions after it unreliable.
        // Arguments finish before their call does, so a call's run of the
        // body's argument list is contiguous.
        let start = self.args.len();
        let mut complete = true;
        let mut count = 0;
        let mut positioned = true;
        if let Some(list) = list {
            for child in tree.children_in_order(list.node()) {
                let Some(arg) = ast::Expr::cast(tree, child) else {
                    positioned = false;
                    continue;
                };
                let arg = arg.node();
                let value = self.visited(arg);
                if positioned && let Some(&expected) = params.get(count) {
                    self.require(arg, value.class, Expected::Ty(expected), Some(item));
                }
                count += 1;
                match value.expr {
                    Some(expr) => self.args.push(expr),
                    None => complete = false,
                }
            }
        }
        // An unclosed list is not yet the wrong length.
        let closed = list.is_some_and(|list| !tree.has_error(list.node()));
        if closed && count != params.len() {
            self.source.error(
                node,
                codes::ARITY,
                format!("expected {} arguments, found {count}", params.len()),
                Some((self.source.span(item), "declared here")),
            );
        }
        let class = match result {
            Some(result) => self.typing.call(result, node),
            None => self.typing.unknown(),
        };
        if closed && complete && count == params.len() {
            let args = Args {
                start: run(start),
                end: run(self.args.len()),
            };
            self.emit(
                node,
                ExprKind::Call {
                    function: target,
                    args,
                    callee: self.source.span(callee),
                },
                class,
            );
        } else {
            self.args.truncate(start);
            self.hole(node, class);
        }
    }
}
