//! Semantic checking of one file: names, structure, and scalar types.
//!
//! Checking makes three passes over the items.
//!
//! 1. **Headers.** Every function's name, parameter types, and result class:
//!    an annotated result is a class known to be its type, an expression body
//!    without one is a fresh class to infer, and a bare block body is unit.
//! 2. **Bodies.** A structural walk per function resolves names, builds the
//!    body's expressions with every expression and local owning a class in
//!    the [`Typing`], and records what the walk learns: facts for literals,
//!    with their values, and for operator results; a flow for each call,
//!    each argument into its parameter, and each branch into its `if`; each
//!    operator's values derived from its operands'; the constants the file
//!    spells or folds; and a demand wherever a context requires an
//!    expression to have a type. The walk rejects nothing on type grounds;
//!    it fails only on names, syntax, and unsupported constructs.
//! 3. **Verdicts.** The typing solves once. Signatures are read off result
//!    classes, independent of declaration order, and the values that may
//!    reach each parameter and result beside them. Demands are then checked in
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

use sumi_frontend::{DiagnosticCode, Label, Location};
use sumi_lexer::{RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    NodeIdx, NodeKind, SyntaxTree,
    ast::{self, AstNode},
};

use crate::codes;
use crate::ranges::{May, RangeEdge, UnaryOp};
use crate::recursion;
use crate::solver::{Backwards, Lattice, Var};
use crate::typing::{Claim, Expected, ProductContext, Typing};
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
    /// The function's run of the shared parameter classes, opened with the
    /// headers so a call walked before the callee's body has somewhere to
    /// send its arguments. Empty for an invalid parameter list.
    param_classes: std::ops::Range<usize>,
    /// The function's entry context: live when it can run.
    entry: Var,
    /// The result class; `None` when the declaration is too damaged to have
    /// one.
    result: Option<Var>,
    /// The declared result type and where: the annotation, or the whole item
    /// for a bare block body. A declaration is a contract the body is held
    /// to, never changed by it. `None` for a result to infer from the body.
    declared: Option<(Ty, NodeIdx)>,
    item: NodeIdx,
}

pub(crate) struct DraftLocal {
    pub origin: Span,
    pub class: Var,
}

/// A body whose expressions are built, with a placeholder type on each
/// until its class resolves.
pub(crate) struct DraftBody {
    pub params: Vec<LocalId>,
    pub locals: Vec<DraftLocal>,
    pub exprs: Vec<Expr>,
    /// The class of each expression, by index.
    pub classes: Vec<Var>,
    pub args: Vec<ExprId>,
    pub statements: Vec<Statement>,
    /// Every call expression beside the context it runs in, for the call
    /// graph: a call in a dead context never happens.
    pub calls: Vec<(ExprId, Var)>,
    /// Every `if` with an else beside its branches' contexts, for the
    /// offsets an argument reads: a dead branch never contributes a value.
    pub branches: Vec<(ExprId, Var, Var)>,
    pub root: ExprId,
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
            calls: _,
            branches: _,
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
}

/// One demand, kept small: the verdict pass reads every one, and a body
/// makes one per operand, argument, branch, and statement.
struct Demand {
    owner: u32,
    node: NodeIdx,
    actual: Var,
    kind: DemandKind,
}

/// A division whose divisor must exclude zero wherever it can run.
struct Obligation {
    owner: u32,
    node: NodeIdx,
    divisor: Var,
    context: Var,
}

/// What the walk of every body leaves for the verdict pass.
#[derive(Default)]
struct Recorded {
    demands: Vec<Demand>,
    obligations: Vec<Obligation>,
    /// Every integer the file spells or folds, for the thresholds.
    constants: Vec<Int>,
    /// Every call as `(caller, callee, context)`, for the call graph.
    calls: Vec<(FunctionId, FunctionId, Var)>,
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
    class: Option<Var>,
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
    let mut param_classes = Vec::with_capacity(items.len());
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
                let name = source.name(param.name(tree));
                let class =
                    ty.map(|ty| typing.known(ty, name.map_or(param.node(), |(_, node)| node)));
                params.push(Parameter { name, ty, class });
            }
        }
        let classes_start = param_classes.len();
        if valid {
            param_classes.extend(params.iter().map(|p| p.class.unwrap()));
        }
        let entry = typing.entry(valid && params.is_empty());
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
            param_classes: classes_start..param_classes.len(),
            entry,
            result,
            declared,
            item: item.node(),
        });
        parameters.push(params);
        functions.push(Function {
            name: name.map(|(_, node)| source.span(node)),
            origin,
            signature: None,
            ranges: None,
            body: None,
        });
    }

    // Pass 2: bodies.
    let mut recorded = Recorded {
        // About a demand per two nodes; only a guide.
        demands: Vec::with_capacity(tree.len() / 2),
        ..Recorded::default()
    };
    let mut bodies = Vec::with_capacity(items.len());
    // Syntax node IDs are dense and bodies have disjoint nodes. Expression
    // IDs remain body-local; a builder only reads entries in its own body.
    let mut values = vec![None; tree.len()];
    let mut builder = Builder::new(
        &mut source,
        &headers,
        &param_classes,
        &names,
        &mut typing,
        &mut recorded,
        &mut values,
    );
    for (index, (item, params)) in items.iter().zip(parameters).enumerate() {
        bodies.push(builder.build(index, *item, params));
    }
    drop(builder);
    drop(values);

    // Pass 3: verdicts.
    let Recorded {
        demands,
        obligations,
        constants,
        calls,
    } = recorded;
    let cx: ProductContext = ((), constants.into_iter().collect());
    typing.solve(&cx);
    let mut replay = typing.replay(&cx);
    let mut failed = vec![false; functions.len()];
    for demand in demands {
        let actual = replay.resolve(demand.actual);
        match demand.kind {
            DemandKind::Type { expected, declared } => {
                let expected_ty = match expected {
                    Expected::Ty(ty) => Some(ty),
                    Expected::Class(class) | Expected::Peer(class) => replay.resolve(class),
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
        }
        failed[demand.owner as usize] = true;
    }
    for (index, header) in headers.iter_mut().enumerate() {
        let evidence = header.result.map(|result| *typing.evidence(result));
        let result = evidence.and_then(|evidence| evidence.ty());
        if let (Some(params), Some(result)) = (header.params.take(), result) {
            functions[index].signature = Some(Signature { params, result });
            // A function nothing live reaches never returns either.
            let result = header.result.unwrap();
            functions[index].ranges = Some(Ranges {
                params: param_classes[header.param_classes.clone()]
                    .iter()
                    .map(|&class| typing.may(class).clone())
                    .collect(),
                result: if typing.may(header.entry).live() {
                    typing.may(result).clone()
                } else {
                    May::bottom()
                },
            });
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
    // Every reachable division excludes zero. The graph is read backwards
    // only once a division fails.
    let mut backwards = None;
    for obligation in &obligations {
        if failed[obligation.owner as usize] {
            continue;
        }
        let divisor = typing.may(obligation.divisor);
        if !typing.may(obligation.context).live() || !divisor.ints.contains_zero() {
            continue;
        }
        let message = if divisor.ints.is_zero() {
            "division by zero"
        } else {
            "divisor may be zero"
        };
        let backwards = backwards.get_or_insert_with(|| typing.backwards());
        let labels = explain_zero(&typing, backwards, &source, &cx, obligation.divisor);
        source.report(
            source.span(obligation.node),
            codes::DIVISION_BY_ZERO,
            message,
            labels,
        );
    }
    // Every recursion has a measure, which also bounds the call depth.
    let param_classes: Vec<&[Var]> = headers
        .iter()
        .map(|header| &param_classes[header.param_classes.clone()])
        .collect();
    let recursion = recursion::check(&bodies, &param_classes, &typing, &calls, &failed);
    for failure in recursion.failures {
        let names: Vec<_> = failure
            .members
            .iter()
            .take(4)
            .map(|&id| {
                let item = items[id.index()];
                format!(
                    "`{}`",
                    source.text(item.name(tree).map_or(item.node(), |n| n.node()))
                )
            })
            .collect();
        let others = failure.members.len() - names.len();
        let cycle = match names.as_slice() {
            [name] => format!("recursion in {name}"),
            [first, second] => format!("recursion between {first} and {second}"),
            [rest @ .., last] if others == 0 => {
                format!("recursion between {}, and {last}", rest.join(", "))
            }
            _ => format!("recursion between {}, and {others} more", names.join(", ")),
        };
        let message = format!("{cycle} has no argument that decreases on every call");
        let first = failure.members[0];
        let primary = items[first.index()]
            .name(tree)
            .map_or(items[first.index()].node(), |n| n.node());
        // A cycle of thousands of calls is one error; the first few calls
        // locate it.
        let labels = failure.labels.into_iter().take(8).map(|(call, text)| {
            let text = text.map(|(param, direction)| {
                let range = param.range();
                let param = &parsed.source()[range.start().to_usize()..range.end().to_usize()];
                let side = if direction == "decreases" {
                    "below"
                } else {
                    "above"
                };
                format!("argument {direction} `{param}`, which is unbounded {side}")
            });
            let text =
                text.unwrap_or_else(|| "no argument moves a parameter toward a bound".to_owned());
            (call, text.into())
        });
        source.report(
            source.span(primary),
            codes::UNBOUNDED_RECURSION,
            message,
            labels,
        );
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
        depth: recursion.depth,
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

/// Labels for the values that put zero into `class`: the flows into it
/// whose delivery contains zero, followed through the edges that pass a
/// value along until a fact, an operator, or an argument names it.
fn explain_zero(
    typing: &Typing,
    backwards: &Backwards,
    source: &Source<'_>,
    cx: &ProductContext,
    class: Var,
) -> Vec<(Span, Box<str>)> {
    use std::collections::{HashSet, VecDeque};

    use crate::ranges::Ints;
    use crate::solver::Lattice;

    const LABELS: usize = 4;
    const HOPS: usize = 6;
    let describe = |ints: &Ints, where_: &str| {
        if ints.is_zero() {
            format!("is 0{where_}")
        } else {
            format!("may be 0{where_}: {ints}")
        }
    };
    let mut labels: Vec<(Span, Box<str>)> = Vec::new();
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([(class, 0)]);
    while let Some((var, hops)) = queue.pop_front() {
        if labels.len() >= LABELS || !seen.insert(typing.find(var)) {
            continue;
        }
        if let Some((origin, fact)) = typing.fact(backwards, var)
            && fact.ints.contains_zero()
        {
            if let Some(node) = origin {
                labels.push((source.span(node), describe(&fact.ints, "").into()));
            }
            continue;
        }
        for (first, second, edge) in typing.incoming(backwards, var) {
            if labels.len() >= LABELS {
                break;
            }
            let delivered = typing.may(first).transfer(
                &edge.1,
                second.map(|second| typing.may(second)),
                false,
                &cx.1,
            );
            if !delivered.ints.contains_zero() {
                continue;
            }
            match edge.1 {
                RangeEdge::Copy | RangeEdge::Branch | RangeEdge::Call => {
                    if hops < HOPS {
                        queue.push_back((first, hops + 1));
                    }
                }
                // A guard that narrowed the local is where the zero was
                // singled out, and the local is where it came from.
                RangeEdge::Refine { origin, .. } => {
                    if delivered.ints != typing.may(first).ints {
                        labels.push((
                            source.span(origin),
                            describe(&delivered.ints, " under this guard").into(),
                        ));
                    }
                    if hops < HOPS {
                        queue.push_back((first, hops + 1));
                    }
                }
                RangeEdge::Argument(origin) => {
                    labels.push((
                        source.span(origin),
                        format!("argument {}", describe(&delivered.ints, "")).into(),
                    ));
                }
                RangeEdge::Unary { origin, .. } | RangeEdge::Binary { origin, .. } => {
                    labels.push((source.span(origin), describe(&delivered.ints, "").into()));
                }
                _ => {}
            }
        }
    }
    labels.sort_by_key(|(span, _)| span.range().start());
    labels
}

// None is a poisoned binding, distinct from an absent name. Scope transitions
// and let completion are explicit work items, so initializers see the old scope.
type Scope<'s> = NameMap<'s, Option<LocalId>>;
enum Work {
    Enter(NodeIdx),
    Finish(NodeIdx),
    Call(NodeIdx, FunctionId, NodeIdx),
    /// An `if` whose condition is walked: open its branches' contexts.
    Branches(NodeIdx),
    /// A lazy operator whose left operand is walked: open the right one's.
    Rhs(NodeIdx),
    /// Enter a context, reading the `refinements` staged locals inside it.
    Push {
        context: Var,
        refinements: usize,
    },
    /// Leave the context `refinements` locals were refined in.
    Pop(usize),
}

/// The one walker for every body of the file. What a body publishes is
/// built in place and moved out; everything else the walk needs is kept
/// and reused, so no body pays for scratch.
struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    headers: &'a [Header],
    param_classes: &'a [Var],
    names: &'a NameMap<'s, Named>,
    typing: &'a mut Typing,
    recorded: &'a mut Recorded,
    values: &'a mut [Option<ExprId>],
    // The body under construction.
    owner: u32,
    failed: bool,
    params: Vec<LocalId>,
    locals: Vec<DraftLocal>,
    exprs: Vec<Expr>,
    classes: Vec<Var>,
    /// The value of each expression the walk can fold, by index.
    consts: Vec<Option<Int>>,
    args: Vec<ExprId>,
    statements: Vec<Statement>,
    calls: Vec<(ExprId, Var)>,
    branches: Vec<(ExprId, Var, Var)>,
    /// The context each point runs in, innermost last.
    contexts: Vec<Var>,
    /// The classes locals read as inside the open contexts, innermost last.
    refinements: Vec<(LocalId, Var)>,
    /// Refinements computed for branches not yet entered, the next branch's
    /// on top, so entering one never allocates.
    staged: Vec<(LocalId, Var)>,
    /// The contexts of the branches of each `if` whose branches are walked
    /// and whose `if` is not yet finished, innermost last.
    branch_contexts: Vec<(Var, Var)>,
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
        param_classes: &'a [Var],
        names: &'a NameMap<'s, Named>,
        typing: &'a mut Typing,
        recorded: &'a mut Recorded,
        values: &'a mut [Option<ExprId>],
    ) -> Self {
        Self {
            source,
            headers,
            param_classes,
            names,
            typing,
            recorded,
            values,
            owner: 0,
            failed: false,
            params: Vec::new(),
            locals: Vec::new(),
            exprs: Vec::new(),
            classes: Vec::new(),
            consts: Vec::new(),
            args: Vec::new(),
            statements: Vec::new(),
            calls: Vec::new(),
            branches: Vec::new(),
            contexts: Vec::new(),
            refinements: Vec::new(),
            staged: Vec::new(),
            branch_contexts: Vec::new(),
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
        self.consts.clear();
        self.args.clear();
        self.statements.clear();
        self.calls.clear();
        self.branches.clear();
        self.contexts.clear();
        self.contexts.push(self.headers[owner].entry);
        self.refinements.clear();
        self.staged.clear();
        self.branch_contexts.clear();
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
                    if let Some(local) = self.bind(name, node, param.class) {
                        self.params.push(local);
                    }
                }
            } else {
                self.failed = true;
            }
        }
        let header = &self.headers[self.owner as usize];
        let result = header.result;
        let declared = header.declared;
        self.failed |= header.params.is_none() || result.is_none();
        let tree = self.source.tree;
        let root_node = item.body(tree)?.node();
        // At most one expression per node of the body.
        let nodes = tree.subtree_len(root_node);
        self.exprs.reserve(nodes);
        self.classes.reserve(nodes);
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
                Work::Branches(node) => self.branches(node, &mut work),
                Work::Rhs(node) => self.rhs(node, &mut work),
                Work::Push {
                    context,
                    refinements,
                } => {
                    self.contexts.push(context);
                    let from = self.staged.len() - refinements;
                    self.refinements.extend(self.staged.drain(from..));
                }
                Work::Pop(refinements) => {
                    self.contexts.pop();
                    let keep = self.refinements.len() - refinements;
                    self.refinements.truncate(keep);
                }
            }
        }
        self.work = work;
        let root = self.value(root_node);
        // A failed parameter does not erase an independently known result
        // type. A declared result is a contract on the body; an inferred one
        // is the body's own type.
        match (root, declared, result) {
            (Some(root), Some((ty, node)), Some(result)) => {
                self.require(root_node, root, Expected::Ty(ty), Some(node));
                self.typing.flow(self.class(root), result, RangeEdge::Copy);
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
            args: std::mem::take(&mut self.args),
            statements: std::mem::take(&mut self.statements),
            calls: std::mem::take(&mut self.calls),
            branches: std::mem::take(&mut self.branches),
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
        // An empty scope, the common case for a function's own, would cost
        // a hash to find nothing in.
        self.scopes[..self.depth]
            .iter()
            .rev()
            .filter(|scope| !scope.is_empty())
            .find_map(|scope| scope.get(name).copied())
    }
    fn class(&self, expr: ExprId) -> Var {
        self.classes[expr.index()]
    }
    /// The class a read of `local` has here: the innermost refinement that
    /// covers it, or the local's own.
    fn current_class(&self, local: LocalId) -> Var {
        self.refinements
            .iter()
            .rev()
            .find(|(refined, _)| *refined == local)
            .map_or(self.locals[local.index()].class, |(_, class)| *class)
    }
    fn context(&self) -> Var {
        *self
            .contexts
            .last()
            .expect("a body runs in its entry context")
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
    /// The local a finished expression reads, if it is a read.
    fn read(&self, node: NodeIdx) -> Option<LocalId> {
        match self.exprs[self.value(node)?.index()].kind {
            ExprKind::Local(local) => Some(local),
            _ => None,
        }
    }
    /// What the condition at `cond` holding in `sense` says about the
    /// locals it compares: a refined class per local, read inside the
    /// branch it guards. The condition's shape is syntactic: a comparison,
    /// a negation, a conjunction under the true sense, a disjunction under
    /// the false sense, or a bare boolean local.
    fn refinements(&mut self, cond: NodeIdx, sense: bool) -> usize {
        let before = self.staged.len();
        self.refine(cond, sense, before);
        self.staged.len() - before
    }
    /// The class a read of `local` has inside the branch being staged: the
    /// innermost refinement this condition staged from `before` on, so a
    /// later conjunct narrows what an earlier one left, else the class the
    /// read has here.
    fn staged_class(&self, local: LocalId, before: usize) -> Var {
        self.staged[before..]
            .iter()
            .rev()
            .find(|(refined, _)| *refined == local)
            .map_or_else(|| self.current_class(local), |(_, class)| *class)
    }
    fn refine(&mut self, cond: NodeIdx, sense: bool, before: usize) {
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
                    self.refine(operand, !sense, before);
                }
            }
            NodeKind::BinaryExpr => {
                let binary = ast::BinaryExpr::cast(tree, node).unwrap();
                let lhs = binary.lhs(tree).unwrap().node();
                let rhs = binary.rhs(tree).unwrap().node();
                let op = self.binary_op(node);
                match op {
                    And if sense => {
                        self.refine(lhs, sense, before);
                        self.refine(rhs, sense, before);
                    }
                    Or if !sense => {
                        self.refine(lhs, sense, before);
                        self.refine(rhs, sense, before);
                    }
                    Lt | Le | Gt | Ge | Eq | Ne => {
                        let ExprKind::Binary { op, .. } =
                            ExprKind::binary(op, ExprId::new(0), ExprId::new(0))
                        else {
                            unreachable!("a comparison is eager")
                        };
                        for (side, other, local_is_lhs) in [(lhs, rhs, true), (rhs, lhs, false)] {
                            if let (Some(local), Some(other)) = (self.read(side), self.value(other))
                            {
                                let class = self.staged_class(local, before);
                                let other = self.class(other);
                                let edge = RangeEdge::Refine {
                                    op,
                                    local_is_lhs,
                                    sense,
                                    origin: node,
                                };
                                let refined = self.typing.refine(class, other, edge);
                                self.staged.push((local, refined));
                            }
                        }
                    }
                    _ => {}
                }
            }
            NodeKind::NameRef => {
                if let Some(local) = self.read(node) {
                    let class = self.staged_class(local, before);
                    let refined = self.typing.refine_bool(class, sense);
                    self.staged.push((local, refined));
                }
            }
            _ => {}
        }
    }
    /// The condition of the `if` at `node` is walked: open a context per
    /// branch and schedule the branches inside them.
    fn branches(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let branch = ast::IfExpr::cast(tree, node).unwrap();
        let cond = branch.condition(tree).unwrap().node();
        let then_node = branch.then_branch(tree).unwrap().node();
        let else_node = branch.else_branch(tree).map(|e| e.node());
        let parent = self.context();
        let (then_context, else_context) = match self.value(cond) {
            Some(value) => {
                let cond = self.class(value);
                (
                    self.typing.derived(cond, parent, RangeEdge::Then),
                    self.typing.derived(cond, parent, RangeEdge::Else),
                )
            }
            None => (parent, parent),
        };
        self.branch_contexts.push((then_context, else_context));
        // The else branch is entered last, so its refinements are staged
        // first and the then branch's sit on top of them. Without an else
        // nothing enters the false sense, so nothing is staged for it: a
        // stage nobody drains would be read by the next branch entered.
        let else_refinements = if else_node.is_some() {
            self.refinements(cond, false)
        } else {
            0
        };
        let then_refinements = self.refinements(cond, true);
        if let Some(else_node) = else_node {
            work.push(Work::Pop(else_refinements));
            work.push(Work::Enter(else_node));
            work.push(Work::Push {
                context: else_context,
                refinements: else_refinements,
            });
        }
        work.push(Work::Pop(then_refinements));
        work.push(Work::Enter(then_node));
        work.push(Work::Push {
            context: then_context,
            refinements: then_refinements,
        });
    }
    /// The left operand of the lazy operator at `node` is walked: open the
    /// context the right one runs in and schedule it inside.
    fn rhs(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let binary = ast::BinaryExpr::cast(tree, node).unwrap();
        let lhs = binary.lhs(tree).unwrap().node();
        let rhs = binary.rhs(tree).unwrap().node();
        let and = self.binary_op(node) == sumi_syntax::BinaryOp::And;
        let parent = self.context();
        let context = match self.value(lhs) {
            Some(value) => {
                let edge = if and {
                    RangeEdge::Then
                } else {
                    RangeEdge::Else
                };
                self.typing.derived(self.class(value), parent, edge)
            }
            None => parent,
        };
        let refinements = self.refinements(lhs, and);
        work.push(Work::Pop(refinements));
        work.push(Work::Enter(rhs));
        work.push(Work::Push {
            context,
            refinements,
        });
    }
    /// An expression of the type `class` resolves to.
    fn emit(&mut self, node: NodeIdx, kind: ExprKind, class: Var) -> ExprId {
        let id = ExprId::new(self.exprs.len());
        self.exprs.push(Expr {
            kind,
            origin: self.source.span(node),
            // Resolved when the body is published.
            ty: Ty::Unit,
        });
        self.classes.push(class);
        self.consts.push(None);
        self.values[node.to_usize()] = Some(id);
        id
    }
    /// Record that `expr` folds to `value`, a constant the thresholds keep.
    fn fold(&mut self, expr: ExprId, value: Int) {
        self.recorded.constants.push(value.clone());
        self.consts[expr.index()] = Some(value);
    }
    /// The context at `node` requires `expr` to be `expected`, which
    /// `declared` may have set. Recorded for the verdict pass, and joined
    /// into the evidence now so inference sees it.
    fn require(
        &mut self,
        node: NodeIdx,
        expr: ExprId,
        expected: Expected,
        declared: Option<NodeIdx>,
    ) {
        let actual = self.class(expr);
        if expected == Expected::Class(actual) {
            return;
        }
        self.typing.expect(actual, expected, node);
        self.demand(node, expr, DemandKind::Type { expected, declared });
    }
    fn demand(&mut self, node: NodeIdx, expr: ExprId, kind: DemandKind) {
        self.recorded.demands.push(Demand {
            owner: self.owner,
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
                        self.bind(name, name_node, None);
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
                self.failed = true;
                return;
            }
            NodeKind::IfExpr => {
                let branch = ast::IfExpr::cast(tree, node).unwrap();
                let cond = branch.condition(tree).unwrap().node();
                work.push(Work::Finish(node));
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
                work.push(Work::Finish(node));
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
    /// The literal's value, negated when a `-` prefix is folded into it.
    /// `None` for a malformed literal, which the lexer already reported.
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
        let magnitude: Int = self
            .source
            .text(literal)
            .parse()
            .expect("a well-formed literal is a run of digits");
        let value = if negative { -&magnitude } else { magnitude };
        let class = self
            .typing
            .literal(Ty::Int, May::int(value.clone()), origin);
        let id = self.emit(origin, ExprKind::Int(value.clone()), class);
        self.fold(id, value);
        Some(id)
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
                // Completed statements are pending in source order, and
                // nested blocks claimed theirs before reaching here, so the
                // block's run of the body's list is filled backwards and
                // reversed in place.
                let start = self.statements.len();
                let mut tail = None;
                let mut valid = !tree.has_error(node);
                for (index, child) in tree.children(node).enumerate() {
                    if let Some((_, statement)) = self.pending.pop_if(|(node, _)| *node == child) {
                        self.statements.push(statement);
                    } else if let Some(value) = self.value(child) {
                        if index == 0 {
                            tail = Some(value);
                        } else {
                            self.demand(child, value, DemandKind::Unused);
                            self.statements.push(Statement {
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
                self.statements[start..].reverse();
                let statements = Statements {
                    start: run(start),
                    end: run(self.statements.len()),
                };
                // A block has its tail's type, or is unit without one.
                let class = match tail {
                    Some(tail) => self.class(tail),
                    None => self.typing.unit(self.context(), node),
                };
                self.emit(node, ExprKind::Block { statements, tail }, class);
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
                        let class = self.typing.known(ty, annotation.node());
                        if let Some(value) = initializer {
                            self.require(
                                initializer_node,
                                value,
                                Expected::Ty(ty),
                                Some(annotation.node()),
                            );
                            self.typing.flow(self.class(value), class, RangeEdge::Copy);
                        }
                        class
                    }),
                    None => initializer.map(|value| self.class(value)),
                };
                let local = self.bind(name, name_node, class);
                self.pending.push((
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
                self.pending.push((
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
                        let class = self.current_class(local);
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
                        let class = self.typing.literal(Ty::Bool, May::bool(value), node);
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
                let class = self.typing.known(ty, node);
                let op = if neg { UnaryOp::Neg } else { UnaryOp::Not };
                self.typing.flow(
                    self.class(value),
                    class,
                    RangeEdge::Unary { op, origin: node },
                );
                let id = self.emit(
                    node,
                    if neg {
                        ExprKind::Neg(value)
                    } else {
                        ExprKind::Not(value)
                    },
                    class,
                );
                if neg && let Some(folded) = self.consts[value.index()].clone() {
                    self.fold(id, -&folded);
                }
            }
            NodeKind::BinaryExpr => {
                use sumi_syntax::BinaryOp::*;

                let binary = ast::BinaryExpr::cast(tree, node).unwrap();
                let lhs_node = binary.lhs(tree).unwrap().node();
                let rhs_node = binary.rhs(tree).unwrap().node();
                let op = self.binary_op(node);
                let lhs = self.value(lhs_node);
                let rhs = self.value(rhs_node);
                // `==` and `!=` compare like with like: whichever operand
                // exists sets the other's expectation.
                let (operand, result) = match op {
                    Add | Sub | Mul | Div | Rem => (Some(Expected::Ty(Ty::Int)), Ty::Int),
                    Lt | Le | Gt | Ge => (Some(Expected::Ty(Ty::Int)), Ty::Bool),
                    Eq | Ne => (
                        lhs.or(rhs).map(|id| Expected::Peer(self.class(id))),
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
                let class = self.typing.known(result, node);
                let kind = ExprKind::binary(op, lhs, rhs);
                let edge = match &kind {
                    ExprKind::Binary { op, .. } => RangeEdge::Binary {
                        op: *op,
                        origin: node,
                    },
                    ExprKind::And { .. } => RangeEdge::Lazy { and: true },
                    ExprKind::Or { .. } => RangeEdge::Lazy { and: false },
                    _ => unreachable!("a binary expression"),
                };
                self.typing
                    .derive(self.class(lhs), self.class(rhs), class, edge);
                if let ExprKind::Binary {
                    op: BinaryOp::Div | BinaryOp::Rem,
                    ..
                } = kind
                {
                    self.recorded.obligations.push(Obligation {
                        owner: self.owner,
                        node,
                        divisor: self.class(rhs),
                        context: self.context(),
                    });
                }
                let folded = match (&kind, &self.consts[lhs.index()], &self.consts[rhs.index()]) {
                    (ExprKind::Binary { op, .. }, Some(a), Some(b)) => match op {
                        BinaryOp::Add => Some(a + b),
                        BinaryOp::Sub => Some(a - b),
                        BinaryOp::Mul => Some(a * b),
                        BinaryOp::Div => a.checked_div(b),
                        BinaryOp::Rem => a.checked_rem(b),
                        _ => None,
                    },
                    _ => None,
                };
                let id = self.emit(node, kind, class);
                if let Some(folded) = folded {
                    self.fold(id, folded);
                }
            }
            NodeKind::IfExpr => {
                let (then_context, else_context) = self
                    .branch_contexts
                    .pop()
                    .expect("an if's branches open before it finishes");
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
                let then_branch = then_branch?;
                let class = match else_node {
                    // Without an else, the then branch is unit, and so is
                    // the `if`.
                    None => {
                        self.require(then_node, then_branch, Expected::Ty(Ty::Unit), None);
                        self.typing.unit(self.context(), node)
                    }
                    // Each branch decides the `if` and learns nothing from
                    // the other, so branches that disagree leave the `if`
                    // undetermined, conflicted on its own class, and keep
                    // their own types. The verdict pass reports it there.
                    Some(_) => {
                        let branches = [then_branch, else_branch?].map(|branch| self.class(branch));
                        let join = self.typing.fresh();
                        for (branch, context) in
                            branches.into_iter().zip([then_context, else_context])
                        {
                            self.typing.branch(branch, context, join);
                        }
                        let id = self.emit(
                            node,
                            ExprKind::If {
                                condition: condition?,
                                then_branch,
                                else_branch,
                            },
                            join,
                        );
                        self.branches.push((id, then_context, else_context));
                        self.demand(node, id, DemandKind::Agree { branches });
                        return Some(());
                    }
                };
                self.emit(
                    node,
                    ExprKind::If {
                        condition: condition?,
                        then_branch,
                        else_branch,
                    },
                    class,
                );
            }
            _ => unreachable!("scheduled supported node"),
        }
        Some(())
    }
    fn call(&mut self, node: NodeIdx, target: FunctionId, callee: NodeIdx) -> Option<()> {
        let caller = FunctionId(self.owner);
        let context = self.context();
        self.recorded.calls.push((caller, target, context));
        let function = &self.headers[target.index()];
        let params = function.params.as_ref()?;
        let param_classes = &self.param_classes[function.param_classes.clone()];
        let entry = function.entry;
        let item = function.item;
        let result = function.result;
        self.typing.flow(context, entry, RangeEdge::Enter);
        let tree = self.source.tree;
        let list = ast::CallExpr::cast(tree, node)
            .unwrap()
            .arg_list(tree)
            .unwrap();
        // Every argument that exists is held to its parameter, arity aside.
        // Arguments finish before their call does, so a call's run of the
        // body's argument list is contiguous.
        let start = self.args.len();
        let mut complete = true;
        let mut count = 0;
        for (index, arg) in list.args(tree).enumerate() {
            count += 1;
            let arg = arg.node();
            match self.value(arg) {
                Some(value) => {
                    if let Some(&expected) = params.get(index) {
                        self.require(arg, value, Expected::Ty(expected), Some(item));
                    }
                    self.args.push(value);
                }
                None => complete = false,
            }
        }
        if count != params.len() {
            self.source.error(
                node,
                codes::ARITY,
                format!("expected {} arguments, found {count}", params.len()),
                Some((self.source.span(item), "declared here")),
            );
        }
        if count != params.len() || !complete {
            self.args.truncate(start);
            return None;
        }
        // A call that is not whole never happens, so only now do the
        // arguments reach the parameters.
        for ((arg, &value), &param) in list.args(tree).zip(&self.args[start..]).zip(param_classes) {
            let edge = RangeEdge::Argument(arg.node());
            self.typing.derive(self.class(value), context, param, edge);
        }
        let args = Args {
            start: run(start),
            end: run(self.args.len()),
        };
        let class = self.typing.call(result?, node);
        let id = self.emit(
            node,
            ExprKind::Call {
                function: target,
                args,
                callee: self.source.span(callee),
            },
            class,
        );
        self.calls.push((id, context));
        Some(())
    }
}
