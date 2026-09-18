//! Semantic checking of one file: names, structure, and scalar types.
//!
//! Checking makes three passes over the items.
//!
//! 1. **Headers.** Every function's name, parameter types, and result class:
//!    an annotated result is a class known to be its type, an expression body
//!    without one is a fresh class to infer, and a bare block body is unit.
//! 2. **Bodies.** A structural walk per function resolves names, builds the
//!    body's nodes of the graph with every node and local owning a class in
//!    the [`Typing`], and records what the walk learns: facts for literals,
//!    with their values, and for operator results; a flow for each call,
//!    each argument into its parameter, and each branch into its `if`; each
//!    operator's values derived from its operands'; the constants the file
//!    spells or folds; and a demand wherever a context requires an
//!    expression to have a type. The walk rejects nothing on type grounds;
//!    it fails only on names, syntax, and unsupported constructs, and what
//!    it refuses it leaves as a hole.
//! 3. **Verdicts.** The typing solves once. Signatures are read off result
//!    classes, independent of declaration order, and the values that may
//!    reach each parameter and result beside them. Demands are then checked in
//!    source order against the final evidence, so a disagreement is blamed on
//!    the first demand that raised it. Every expression has one context, so
//!    it is held to one demand; an expression whose type is undetermined,
//!    because its branches or its callee disagree, satisfies any demand
//!    silently, and the disagreement is reported where it arose. A body is
//!    complete when its walk succeeded, none of its demands failed, every
//!    class it uses resolved, and every function it calls has a signature.
//!
//! Names are never copied while checking: every map is keyed by a slice of
//! the source, and the one builder keeps its scratch across bodies, so a
//! body costs its nodes of the graph and nothing else.

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
use crate::ranges::{May, RangeEdge, UnaryOp};
use crate::recursion;
use crate::solver::{Lattice, Var};
use crate::typing::{Claim, Expected, ProductContext, Typing};
use crate::*;

/// A hasher for identifiers and integer constants: a word at a time, with
/// a multiply to spread the bits, which is all a short ASCII name or a
/// word-sized integer needs and a fraction of what a keyed hash costs.
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

struct DraftLocal {
    pub origin: Span,
    pub class: Var,
    /// The node a read of the local outside any guard reads.
    pub node: NodeId,
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
    divisor: NodeId,
    context: Var,
}

/// What the walk of every body leaves for the verdict pass.
#[derive(Default)]
struct Recorded {
    demands: Vec<Demand>,
    obligations: Vec<Obligation>,
    /// Every distinct integer the file spells or folds, in the order first
    /// seen, for the thresholds. A file repeats its few constants in every
    /// function, so the list stays short where one entry per literal would
    /// not, and it keeps source order, which is nearly sorted, where a set
    /// alone would not.
    constants: Vec<Int>,
    seen: HashSet<Int, BuildHasherDefault<NameHasher>>,
}

/// Where each node of the graph stands once the file is built: its class,
/// and every whole call with the context it runs in and its arguments as
/// written, which a read passed as an argument has no node of its own to
/// say.
pub(crate) struct Placed {
    /// The class of each node, by index; none for a hole, or for a node
    /// built where the expression tree could not be.
    classes: Vec<Option<Var>>,
    /// Every whole call, in definition order.
    calls: Vec<PlacedCall>,
    /// The arguments of every whole call as written, one run per call.
    arguments: Vec<NodeIdx>,
    bottom: May,
}

/// A whole call: its node, its ends, the context it runs in, and its run
/// of the arguments as written.
pub(crate) struct PlacedCall {
    pub node: NodeId,
    pub caller: FunctionId,
    pub callee: FunctionId,
    pub context: NodeId,
    arguments: std::ops::Range<u32>,
}

impl Placed {
    /// Room for a file of about `nodes` nodes.
    fn with_capacity(nodes: usize) -> Self {
        Self {
            classes: Vec::with_capacity(nodes),
            calls: Vec::new(),
            arguments: Vec::new(),
            bottom: May::bottom(),
        }
    }
    /// The values that may reach `node`: none for a node without a class.
    pub fn may<'t>(&'t self, typing: &'t Typing, node: NodeId) -> &'t May {
        match self.classes[node.index()] {
            Some(class) => typing.may(class),
            None => &self.bottom,
        }
    }
    /// Whether the context `node`, or a value at it, is live.
    pub fn live(&self, typing: &Typing, node: NodeId) -> bool {
        self.may(typing, node).live()
    }
    /// Every whole call.
    pub fn calls(&self) -> &[PlacedCall] {
        &self.calls
    }
    /// The arguments of `call` as written.
    pub fn arguments(&self, call: &PlacedCall) -> &[NodeIdx] {
        &self.arguments[call.arguments.start as usize..call.arguments.end as usize]
    }
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
    node: NodeIdx,
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
    let mut named: Vec<(Option<Span>, Span)> = Vec::with_capacity(items.len());
    let mut names: NameMap<Named> =
        NameMap::with_capacity_and_hasher(items.len(), Default::default());
    let mut parameters = Vec::with_capacity(items.len());
    let mut headers = Vec::with_capacity(items.len());
    let mut param_classes = Vec::with_capacity(items.len());
    for item in &items {
        let name = source.name(item.name(tree));
        let id = FunctionId::new(named.len());
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
                params.push(Parameter {
                    node: param.node(),
                    name,
                    ty,
                    class,
                });
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
        named.push((name.map(|(_, node)| source.span(node)), origin));
    }

    // Pass 2: bodies.
    let mut recorded = Recorded {
        // About a demand per two nodes; only a guide.
        demands: Vec::with_capacity(tree.len() / 2),
        ..Recorded::default()
    };
    let mut built = Vec::with_capacity(items.len());
    // Syntax node IDs are dense and bodies have disjoint nodes.
    let mut nodes_of = vec![None; tree.len()];
    // About a node per syntax node of a body; only a guide.
    let mut graph = Graph::with_capacity(tree.len());
    let mut placed = Placed::with_capacity(tree.len());
    let mut builder = Builder::new(
        &mut source,
        &headers,
        &param_classes,
        &names,
        &mut typing,
        &mut recorded,
        &mut nodes_of,
        &mut graph,
        &mut placed,
    );
    for (index, (item, params)) in items.iter().zip(parameters).enumerate() {
        built.push(builder.build(index, *item, params));
    }
    drop(builder);
    drop(nodes_of);
    let mut functions: Vec<Function> = named
        .into_iter()
        .map(|(name, origin)| Function {
            name,
            origin,
            signature: None,
            ranges: None,
            complete: false,
        })
        .collect();

    // Pass 3: verdicts.
    let Recorded {
        demands,
        obligations,
        constants,
        ..
    } = recorded;
    let cx: ProductContext = ((), constants.into_iter().collect());
    typing.solve(&cx);
    for (index, class) in placed.classes.iter().enumerate() {
        graph.set_type(
            NodeId::new(index),
            class.and_then(|class| typing.resolve(class)),
        );
    }
    let mut replay = typing.replay();
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
            && built[index]
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
    // Every reachable division excludes zero.
    for obligation in &obligations {
        if failed[obligation.owner as usize] {
            continue;
        }
        let divisor = placed.may(&typing, obligation.divisor);
        if !typing.may(obligation.context).live() || !divisor.ints.contains_zero() {
            continue;
        }
        let message = if divisor.ints.is_zero() {
            "division by zero"
        } else {
            "divisor may be zero"
        };
        let labels = explain_zero(&graph, &placed, &typing, &source, obligation.divisor);
        source.report(
            source.span(obligation.node),
            codes::DIVISION_BY_ZERO,
            message,
            labels,
        );
    }
    // Every recursion has a measure, which also bounds the call depth. A
    // function whose body did not build is out of scope like one that
    // failed a verdict.
    let out_of_scope: Vec<bool> = failed
        .iter()
        .zip(&built)
        .map(|(&failed, &built)| failed || !built)
        .collect();
    let recursion = recursion::check(&graph, &placed, &typing, &out_of_scope);
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
        let message = format!("{cycle} has no argument that moves toward a bound on every call");
        let first = failure.members[0];
        let primary = items[first.index()]
            .name(tree)
            .map_or(items[first.index()].node(), |n| n.node());
        // A cycle of thousands of calls is one error; the first few calls
        // locate it.
        let name = |param: Span| {
            let range = param.range();
            &parsed.source()[range.start().to_usize()..range.end().to_usize()]
        };
        let labels = failure.labels.into_iter().take(8).map(|(call, reason)| {
            let text = match reason {
                recursion::Reason::Unbounded { param, direction } => {
                    let (moves, side) = direction.words();
                    format!(
                        "argument {moves} `{}`, which is unbounded {side}",
                        name(param)
                    )
                }
                recursion::Reason::Moves { param, direction } => {
                    format!("argument {} `{}`", direction.words().0, name(param))
                }
                recursion::Reason::Passes { param } => {
                    format!("argument passes `{}` along", name(param))
                }
                recursion::Reason::Nothing => {
                    "no argument is a parameter moved by a constant".to_owned()
                }
            };
            (call, text.into())
        });
        source.report(
            source.span(primary),
            codes::UNBOUNDED_RECURSION,
            message,
            labels,
        );
    }
    // A body is complete when it built, none of its demands failed, every
    // value in it resolved, and every call agrees with its callee's
    // signature: a caller's demands can resolve its call's class without
    // resolving the callee, and that is not a complete call.
    for index in 0..functions.len() {
        if failed[index] || !built[index] || functions[index].signature.is_none() {
            continue;
        }
        let run = graph.run(FunctionId::new(index));
        let complete = run.nodes().all(|node| {
            let node = graph.node(node);
            match node.op {
                Op::Entry | Op::Then | Op::Else => true,
                Op::Call(callee) => functions[callee.index()]
                    .signature
                    .as_ref()
                    .is_some_and(|signature| Some(signature.result) == node.ty),
                _ => node.ty.is_some(),
            }
        });
        functions[index].complete = complete;
    }
    source
        .diagnostics
        .sort_by_key(|d| d.primary.location.start());
    let diagnostics = source.diagnostics;
    let analysis = Analysis {
        parsed,
        graph,
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

/// Labels for the values that put zero into `divisor`: what it reads,
/// followed through the copies, narrowed reads, branches, calls, and
/// arguments that pass a value along until a literal or an operator
/// produced it.
fn explain_zero(
    graph: &Graph,
    placed: &Placed,
    typing: &Typing,
    source: &Source<'_>,
    divisor: NodeId,
) -> Vec<(Span, Box<str>)> {
    use std::collections::{HashSet, VecDeque};

    use crate::ranges::Ints;

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
    let mut queue = VecDeque::from([(divisor, 0)]);
    while let Some((node, hops)) = queue.pop_front() {
        if labels.len() >= LABELS || !seen.insert(node) {
            continue;
        }
        let may = placed.may(typing, node);
        if !may.ints.contains_zero() {
            continue;
        }
        let entry = graph.node(node);
        let inputs = graph.inputs(node);
        let follow = |queue: &mut VecDeque<(NodeId, usize)>, next: NodeId, cost: usize| {
            if hops + cost <= HOPS {
                queue.push_back((next, hops + cost));
            }
        };
        match entry.op {
            Op::Int(_) | Op::Neg | Op::Binary(_) => {
                labels.push((entry.origin, describe(&may.ints, "").into()));
            }
            // A `let` passes the value on unchanged, at no distance.
            Op::Copy => follow(&mut queue, inputs[0], 0),
            // A guard that narrowed the local is where the zero was
            // singled out, and the local is where it came from.
            Op::Refine { .. } => {
                if may.ints != placed.may(typing, inputs[0]).ints {
                    labels.push((
                        entry.origin,
                        describe(&may.ints, " under this guard").into(),
                    ));
                }
                follow(&mut queue, inputs[0], 1);
            }
            Op::Join { then, else_ } => {
                for region in std::iter::once(then).chain(else_) {
                    let region = graph.region(region);
                    if placed.live(typing, region.context) {
                        follow(&mut queue, region.result(), 1);
                    }
                }
            }
            Op::Call(callee) => follow(&mut queue, graph.run(callee).result(), 1),
            Op::Param(index) => {
                // Runs are contiguous in declaration order: the parameter's
                // function is the last whose entry precedes it.
                let callee = graph
                    .runs()
                    .partition_point(|run| run.entry().index() <= node.index())
                    - 1;
                let callee = FunctionId::new(callee);
                for call in placed.calls().iter().filter(|call| call.callee == callee) {
                    if labels.len() >= LABELS {
                        break;
                    }
                    if !placed.live(typing, call.context) {
                        continue;
                    }
                    let arg = graph.inputs(call.node)[index as usize];
                    let delivered = placed.may(typing, arg);
                    if delivered.ints.contains_zero() {
                        let written = placed.arguments(call)[index as usize];
                        labels.push((
                            source.span(written),
                            format!("argument {}", describe(&delivered.ints, "")).into(),
                        ));
                    }
                }
            }
            Op::Bool(_)
            | Op::Unit
            | Op::Hole
            | Op::Not
            | Op::And { .. }
            | Op::Or { .. }
            | Op::Exactly(_)
            | Op::Entry
            | Op::Then
            | Op::Else => {}
        }
    }
    labels.sort_by_key(|(span, _)| span.range().start());
    labels
}

// None is a poisoned binding, distinct from an absent name, beside the node
// that defines it either way. Scope transitions and let completion are
// explicit work items, so initializers see the old scope.
type Scope<'s> = NameMap<'s, (Option<LocalId>, NodeId)>;
enum Work {
    Enter(NodeIdx),
    Finish(NodeIdx),
    Call(NodeIdx, FunctionId, NodeIdx),
    /// A call whose callee is no function: once its arguments are walked,
    /// a hole over them.
    Holed(NodeIdx),
    /// An `if` whose condition is walked: open its branches' contexts.
    Branches(NodeIdx),
    /// A lazy operator whose left operand is walked: open the right one's.
    Rhs(NodeIdx),
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

/// A local of the body under construction: an index into the builder's
/// locals.
#[derive(Clone, Copy, PartialEq, Eq)]
struct LocalId(u32);

impl LocalId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// The one walker for every body of the file. What a body builds are its
/// nodes of the graph; everything else the walk needs is kept and reused,
/// so no body pays for scratch.
struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    headers: &'a [Header],
    param_classes: &'a [Var],
    names: &'a NameMap<'s, Named>,
    typing: &'a mut Typing,
    recorded: &'a mut Recorded,
    /// The graph node each syntax node built, by node.
    nodes_of: &'a mut [Option<NodeId>],
    graph: &'a mut Graph,
    /// Where each node stands, filled as the node is pushed.
    placed: &'a mut Placed,
    /// The value of each node the walk can fold, by node, a constant the
    /// thresholds keep.
    consts: Vec<Option<Int>>,
    // The body under construction.
    owner: u32,
    failed: bool,
    locals: Vec<DraftLocal>,
    /// The open regions, innermost last: where a pushed node stands, and
    /// whose context the point runs in.
    regions: Vec<RegionId>,
    /// The classes and nodes locals read as inside the open regions,
    /// innermost last.
    refinements: Vec<(LocalId, Var, NodeId)>,
    /// Where each open region's refinements begin in `refinements`.
    marks: Vec<usize>,
    /// The contexts of the branches of each `if` whose branches are walked
    /// and whose `if` is not yet finished, innermost last.
    branch_contexts: Vec<(Var, Var)>,
    /// The regions of the same branches.
    branch_regions: Vec<(RegionId, Option<RegionId>)>,
    /// The regions of the right operands of the lazy operators whose right
    /// operands are walked and whose operators are not yet finished.
    lazy_regions: Vec<RegionId>,
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
    /// The inputs of the node being pushed, when there are more than two.
    inputs: Vec<NodeId>,
}

impl<'a, 's> Builder<'a, 's> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        source: &'a mut Source<'s>,
        headers: &'a [Header],
        param_classes: &'a [Var],
        names: &'a NameMap<'s, Named>,
        typing: &'a mut Typing,
        recorded: &'a mut Recorded,
        nodes_of: &'a mut [Option<NodeId>],
        graph: &'a mut Graph,
        placed: &'a mut Placed,
    ) -> Self {
        Self {
            source,
            headers,
            param_classes,
            names,
            typing,
            recorded,
            nodes_of,
            graph,
            placed,
            consts: Vec::new(),
            owner: 0,
            failed: false,
            locals: Vec::new(),
            regions: Vec::new(),
            refinements: Vec::new(),
            marks: Vec::new(),
            branch_contexts: Vec::new(),
            branch_regions: Vec::new(),
            lazy_regions: Vec::new(),
            scopes: Vec::new(),
            depth: 0,
            first: NameMap::default(),
            work: Vec::new(),
            inputs: Vec::new(),
        }
    }
    /// Build the body of the function `owner`, closing its run of the
    /// graph: whether the walk built it whole.
    fn build(&mut self, owner: usize, item: ast::FnItem, parameters: Vec<Parameter<'s>>) -> bool {
        self.owner = u32::try_from(owner).expect("function count fits u32");
        self.failed = false;
        self.depth = 0;
        self.open_scope();
        self.first.clear();
        self.locals.clear();
        self.regions.clear();
        self.refinements.clear();
        self.marks.clear();
        self.branch_contexts.clear();
        self.branch_regions.clear();
        self.lazy_regions.clear();
        let header = &self.headers[owner];
        let entry_class = header.entry;
        let item_node = header.item;
        let start = self.graph.next();
        let entry = self.push(item_node, Op::Entry, &[], None);
        self.placed.classes[entry.index()] = Some(entry_class);
        let arity = u32::try_from(parameters.len()).expect("parameter count fits u32");
        for (index, param) in parameters.into_iter().enumerate() {
            let index = u32::try_from(index).expect("parameter count fits u32");
            let name = param.name.map(|(_, node)| self.source.span(node));
            let node = self.push(param.node, Op::Param(index), &[], name);
            self.placed.classes[node.index()] = param.class;
            if let Some((name, name_node)) = param.name {
                if let Some(&span) = self.first.get(name) {
                    self.source.error(
                        name_node,
                        codes::DUPLICATE_NAME,
                        format!("duplicate parameter `{name}`"),
                        Some((span, "declared here")),
                    );
                    self.shadow(name, None, node);
                    self.failed = true;
                } else {
                    self.first.insert(name, self.source.span(name_node));
                    self.bind(name, name_node, param.class, node);
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
        let region = self.graph.open(entry);
        self.graph.enter(region);
        self.regions.push(region);
        let root_node = item.body(tree).map(|body| body.node());
        if let Some(root_node) = root_node {
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
                    Work::Holed(node) => self.holed(node),
                    Work::Branches(node) => self.branches(node, &mut work),
                    Work::Rhs(node) => self.rhs(node, &mut work),
                    Work::Push { region, guard } => {
                        self.marks.push(self.refinements.len());
                        self.graph.enter(region);
                        self.regions.push(region);
                        self.refine(guard.0, guard.1);
                    }
                    Work::Pop { region, root } => {
                        let result = self.node_of(root);
                        self.graph.close(region, result);
                        self.regions.pop();
                        let keep = self.marks.pop().expect("a region opened before it closes");
                        self.refinements.truncate(keep);
                    }
                }
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
        // is the body's own type.
        let value = match declared {
            Some((_, node)) => {
                let copy = self.push(node, Op::Copy, &[body_value], None);
                if let Some(result) = result {
                    self.placed.classes[copy.index()] = Some(result);
                }
                copy
            }
            None => body_value,
        };
        match (root, declared, result) {
            (Some(root), Some((ty, node)), Some(result)) => {
                self.require(root_node.unwrap(), root, Expected::Ty(ty), Some(node));
                self.typing.flow(root, result, RangeEdge::Copy);
            }
            (Some(root), None, Some(result)) => {
                self.require(root_node.unwrap(), root, Expected::Class(result), None);
            }
            _ => {}
        }
        self.graph
            .close_run(FunctionId::new(owner), start, arity, region, value);
        !self.failed && root.is_some()
    }
    /// A graph node at `node`, which reads `inputs`.
    fn push(&mut self, node: NodeIdx, op: Op, inputs: &[NodeId], name: Option<Span>) -> NodeId {
        let id = self.place(op, inputs, self.source.span(node), name);
        self.nodes_of[node.to_usize()] = Some(id);
        id
    }
    /// A graph node without a class yet, that no syntax node is said to
    /// have built.
    fn place(&mut self, op: Op, inputs: &[NodeId], origin: Span, name: Option<Span>) -> NodeId {
        let id = self.graph.push(op, inputs, origin, name);
        self.placed.classes.push(None);
        self.consts.push(None);
        id
    }
    /// A node of the type `class` resolves to, at `node`, which is built.
    fn classify(&mut self, node: NodeIdx, class: Var) -> NodeId {
        let id = self.nodes_of[node.to_usize()].expect("a graph node before its class");
        self.placed.classes[id.index()] = Some(class);
        id
    }
    /// A context node for the region whose syntax is `region`, derived
    /// from `condition` under `parent`. It is not what `region` built: the
    /// region's own node is its value, which the context gates.
    fn context_at(&mut self, region: NodeIdx, op: Op, condition: NodeId, parent: NodeId) -> NodeId {
        self.place(op, &[condition, parent], self.source.span(region), None)
    }
    /// The graph node `node` built, or a hole where nothing was: syntax
    /// the walk could not reach.
    fn node_of(&mut self, node: NodeIdx) -> NodeId {
        match self.nodes_of[node.to_usize()] {
            Some(id) => id,
            None => self.push(node, Op::Hole, &[], None),
        }
    }
    /// The class of the value `node` built, if it built one with a class:
    /// a hole, and a node built where the typing could not follow, have
    /// none.
    fn typed(&self, node: NodeIdx) -> Option<Var> {
        self.placed.classes[self.nodes_of[node.to_usize()]?.index()]
    }
    /// A hole at `node`, over nothing: syntax the walk refuses.
    fn hole(&mut self, node: NodeIdx) -> NodeId {
        self.push(node, Op::Hole, &[], None)
    }
    /// A hole at the call `node` over what it walked: its callee, when
    /// that built or was holed, and its arguments.
    fn holed(&mut self, node: NodeIdx) {
        let tree = self.source.tree;
        let call = ast::CallExpr::cast(tree, node).unwrap();
        let callee = self.source.peel(call.callee(tree).unwrap()).node();
        let list = call.arg_list(tree).unwrap();
        let mut inputs = std::mem::take(&mut self.inputs);
        inputs.clear();
        inputs.extend(self.nodes_of[callee.to_usize()]);
        for arg in list.args(tree) {
            let arg = self.node_of(arg.node());
            inputs.push(arg);
        }
        self.push(node, Op::Hole, &inputs, None);
        self.inputs = inputs;
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
    /// Give `name` the meaning `id`, defined by `node`, until the innermost
    /// scope closes.
    fn shadow(&mut self, name: &'s str, id: Option<LocalId>, node: NodeId) {
        self.scopes[self.depth - 1].insert(name, (id, node));
    }
    /// Bind `name` to a local defined by `node`, whose class is `class`.
    fn bind(&mut self, name: &'s str, name_node: NodeIdx, class: Option<Var>, node: NodeId) {
        let id = class.map(|class| {
            let id = LocalId(u32::try_from(self.locals.len()).expect("local count fits u32"));
            self.locals.push(DraftLocal {
                origin: self.source.span(name_node),
                class,
                node,
            });
            id
        });
        self.failed |= id.is_none();
        self.shadow(name, id, node);
    }
    fn lookup(&self, name: &str) -> Option<(Option<LocalId>, NodeId)> {
        // An empty scope, the common case for a function's own, would cost
        // a hash to find nothing in.
        self.scopes[..self.depth]
            .iter()
            .rev()
            .filter(|scope| !scope.is_empty())
            .find_map(|scope| scope.get(name).copied())
    }
    /// The class and the node a read of `local` has here: the innermost
    /// refinement that covers it, or the local's own.
    fn current(&self, local: LocalId) -> (Var, NodeId) {
        self.refinements
            .iter()
            .rev()
            .find(|(refined, _, _)| *refined == local)
            .map_or_else(
                || {
                    let local = &self.locals[local.index()];
                    (local.class, local.node)
                },
                |(_, class, node)| (*class, *node),
            )
    }
    /// The context the open region runs in.
    fn context_node(&self) -> NodeId {
        let region = *self.regions.last().expect("a body runs in its region");
        self.graph.region(region).context
    }
    fn context(&self) -> Var {
        self.placed.classes[self.context_node().index()].expect("a context has a class")
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
    /// class. The scope is as it was when the read was built: a region is
    /// entered right after its condition finishes.
    fn read(&self, node: NodeIdx) -> Option<LocalId> {
        if self.source.tree.kind(node) != NodeKind::NameRef {
            return None;
        }
        self.lookup(self.source.text(node))?.0
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
                            if let (Some(local), Some(other_class)) =
                                (self.read(side), self.typed(other))
                            {
                                let (class, read) = self.current(local);
                                let edge = RangeEdge::Refine {
                                    op,
                                    local_is_lhs,
                                    sense,
                                };
                                let refined = self.typing.refine(class, other_class, edge);
                                let inputs = [read, self.node_of(other)];
                                let read = self.place(
                                    Op::Refine {
                                        op,
                                        local_is_lhs,
                                        sense,
                                    },
                                    &inputs,
                                    self.source.span(node),
                                    None,
                                );
                                self.placed.classes[read.index()] = Some(refined);
                                self.refinements.push((local, refined, read));
                            }
                        }
                    }
                    _ => {}
                }
            }
            NodeKind::NameRef => {
                if let Some(local) = self.read(node) {
                    let (class, read) = self.current(local);
                    let refined = self.typing.refine_bool(class, sense);
                    let inputs = [read];
                    let read =
                        self.place(Op::Exactly(sense), &inputs, self.source.span(node), None);
                    self.placed.classes[read.index()] = Some(refined);
                    self.refinements.push((local, refined, read));
                }
            }
            _ => {}
        }
    }
    /// The condition of the `if` at `node` is walked: open a context and a
    /// region per branch and schedule the branches inside them.
    fn branches(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let branch = ast::IfExpr::cast(tree, node).unwrap();
        let cond = branch.condition(tree).unwrap().node();
        let then_node = branch.then_branch(tree).unwrap().node();
        let else_node = branch.else_branch(tree).map(|e| e.node());
        let parent = self.context();
        let parent_node = self.context_node();
        let (then_context, else_context) = match self.typed(cond) {
            Some(cond) => (
                self.typing.derived(cond, parent, RangeEdge::Then),
                self.typing.derived(cond, parent, RangeEdge::Else),
            ),
            None => (parent, parent),
        };
        let cond_node = self.node_of(cond);
        let then_region = {
            let context = self.context_at(then_node, Op::Then, cond_node, parent_node);
            self.placed.classes[context.index()] = Some(then_context);
            self.graph.open(context)
        };
        let else_region = else_node.map(|else_node| {
            let context = self.context_at(else_node, Op::Else, cond_node, parent_node);
            self.placed.classes[context.index()] = Some(else_context);
            self.graph.open(context)
        });
        self.branch_contexts.push((then_context, else_context));
        self.branch_regions.push((then_region, else_region));
        // The else branch is entered last. Without an else nothing enters
        // the false sense, so nothing is narrowed for it.
        if let (Some(else_node), Some(else_region)) = (else_node, else_region) {
            work.push(Work::Pop {
                region: else_region,
                root: else_node,
            });
            work.push(Work::Enter(else_node));
            work.push(Work::Push {
                region: else_region,
                guard: (cond, false),
            });
        }
        work.push(Work::Pop {
            region: then_region,
            root: then_node,
        });
        work.push(Work::Enter(then_node));
        work.push(Work::Push {
            region: then_region,
            guard: (cond, true),
        });
    }
    /// The left operand of the lazy operator at `node` is walked: open the
    /// context and region the right one runs in and schedule it inside.
    fn rhs(&mut self, node: NodeIdx, work: &mut Vec<Work>) {
        let tree = self.source.tree;
        let binary = ast::BinaryExpr::cast(tree, node).unwrap();
        let lhs = binary.lhs(tree).unwrap().node();
        let rhs = binary.rhs(tree).unwrap().node();
        let and = self.binary_op(node) == sumi_syntax::BinaryOp::And;
        let parent = self.context();
        let parent_node = self.context_node();
        let (edge, op) = if and {
            (RangeEdge::Then, Op::Then)
        } else {
            (RangeEdge::Else, Op::Else)
        };
        let context = match self.typed(lhs) {
            Some(class) => self.typing.derived(class, parent, edge),
            None => parent,
        };
        let lhs_node = self.node_of(lhs);
        let context_node = self.context_at(rhs, op, lhs_node, parent_node);
        self.placed.classes[context_node.index()] = Some(context);
        let region = self.graph.open(context_node);
        self.lazy_regions.push(region);
        work.push(Work::Pop { region, root: rhs });
        work.push(Work::Enter(rhs));
        work.push(Work::Push {
            region,
            guard: (lhs, and),
        });
    }
    /// Record that `node` folds to `value`, a constant the thresholds keep.
    fn fold(&mut self, node: NodeId, value: Int) {
        if self.recorded.seen.insert(value.clone()) {
            self.recorded.constants.push(value.clone());
        }
        self.consts[node.index()] = Some(value);
    }
    /// The context at `node` requires the value of class `actual` to be
    /// `expected`, which `declared` may have set. Recorded for the verdict
    /// pass, and joined into the evidence now so inference sees it.
    fn require(
        &mut self,
        node: NodeIdx,
        actual: Var,
        expected: Expected,
        declared: Option<NodeIdx>,
    ) {
        if expected == Expected::Class(actual) || expected == Expected::Peer(actual) {
            return;
        }
        self.typing.expect(actual, expected, node);
        self.demand(node, actual, DemandKind::Type { expected, declared });
    }
    fn demand(&mut self, node: NodeIdx, actual: Var, kind: DemandKind) {
        self.recorded.demands.push(Demand {
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
                            self.push(node, Op::Hole, &[], Some(self.source.span(name_node)));
                        self.bind(name, name_node, None, hole);
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
                    work.push(Work::Holed(node));
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
        if let Some((local, _)) = self.lookup(name) {
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
    fn integer(&mut self, origin: NodeIdx, literal: NodeIdx, negative: bool) -> Option<Var> {
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
        self.push(origin, Op::Int(value.clone()), &[], None);
        let class = self
            .typing
            .literal(Ty::Int, May::int(value.clone()), origin);
        let id = self.classify(origin, class);
        self.fold(id, value);
        Some(class)
    }
    fn finish(&mut self, node: NodeIdx) -> Option<()> {
        let tree = self.source.tree;
        match tree.kind(node) {
            NodeKind::Block => {
                self.close_scope();
                // Children arrive last first; only the first can be the
                // tail. A statement built itself; an expression statement
                // must be unit; a child that built nothing is a hole where
                // it stood.
                let mut tail = None;
                let mut valid = !tree.has_error(node);
                for (index, child) in tree.children(node).enumerate() {
                    let expression = ast::Expr::cast(tree, child).is_some();
                    if index == 0 && expression {
                        tail = Some(child);
                        continue;
                    }
                    match self.typed(child) {
                        Some(class) if expression => self.demand(child, class, DemandKind::Unused),
                        Some(_) => {}
                        None => {
                            self.node_of(child);
                            valid = false;
                        }
                    }
                }
                // A block is its tail, or unit without one, whether or not
                // the rest of it built.
                let class = match tail {
                    Some(tail) => {
                        let value = self.node_of(tail);
                        self.nodes_of[node.to_usize()] = Some(value);
                        self.typed(tail)
                    }
                    None => {
                        let context = self.context_node();
                        let unit = self.push(node, Op::Unit, &[context], None);
                        let class = self.typing.unit(self.context(), node);
                        self.placed.classes[unit.index()] = Some(class);
                        Some(class)
                    }
                };
                if !valid {
                    return None;
                }
                class?;
            }
            NodeKind::LetStmt => {
                let binding = ast::LetStmt::cast(tree, node).unwrap();
                let initializer_node = binding.initializer(tree).unwrap().node();
                let initializer = self.typed(initializer_node);
                let value = self.node_of(initializer_node);
                let name = self.source.name(binding.name(tree));
                let copy = self.push(
                    node,
                    Op::Copy,
                    &[value],
                    name.map(|(_, node)| self.source.span(node)),
                );
                let (name, name_node) = name?;
                // An annotated binding has its declared type whatever its
                // initializer turns out to be; the initializer is held to it.
                let class = match binding.type_ref(tree) {
                    Some(annotation) => self.source.ty(annotation).map(|ty| {
                        let class = self.typing.known(ty, annotation.node());
                        if let Some(initializer) = initializer {
                            self.require(
                                initializer_node,
                                initializer,
                                Expected::Ty(ty),
                                Some(annotation.node()),
                            );
                            self.typing.flow(initializer, class, RangeEdge::Copy);
                        }
                        class
                    }),
                    None => initializer,
                };
                self.placed.classes[copy.index()] = class;
                self.bind(name, name_node, class, copy);
                class?;
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
                    Some((Some(local), _)) => {
                        let (_, read) = self.current(local);
                        self.nodes_of[node.to_usize()] = Some(read);
                    }
                    // A binding without a type is still what the name
                    // reads; one the walk refused, a duplicate parameter,
                    // has a type its reads must not be held to, so the read
                    // is a hole.
                    Some((None, defined)) => {
                        if self.placed.classes[defined.index()].is_none() {
                            self.nodes_of[node.to_usize()] = Some(defined);
                        } else {
                            self.hole(node);
                        }
                        return None;
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
                        let class = self.typing.literal(Ty::Bool, May::bool(value), node);
                        self.classify(node, class);
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
                let class = self.typing.known(ty, node);
                let op = if neg { UnaryOp::Neg } else { UnaryOp::Not };
                self.typing.flow(value, class, RangeEdge::Unary(op));
                let id = self.classify(node, class);
                if neg && let Some(folded) = self.consts[operand_node.index()].clone() {
                    self.fold(id, -&folded);
                }
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
                let mut rhs_graph = None;
                match op {
                    And | Or => {
                        let region = self
                            .lazy_regions
                            .pop()
                            .expect("a lazy operator's right operand opens before it finishes");
                        let op = if op == And {
                            Op::And { rhs: region }
                        } else {
                            Op::Or { rhs: region }
                        };
                        self.push(node, op, &[lhs_graph], None);
                    }
                    _ => {
                        let rhs = self.node_of(rhs_node);
                        rhs_graph = Some(rhs);
                        let op = eager(op).expect("an eager operator");
                        self.push(node, Op::Binary(op), &[lhs_graph, rhs], None);
                    }
                }
                // `==` and `!=` compare like with like: whichever operand
                // exists sets the other's expectation.
                let (operand, result) = match op {
                    Add | Sub | Mul | Div | Rem => (Some(Expected::Ty(Ty::Int)), Ty::Int),
                    Lt | Le | Gt | Ge => (Some(Expected::Ty(Ty::Int)), Ty::Bool),
                    Eq | Ne => (lhs.or(rhs).map(Expected::Peer), Ty::Bool),
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
                let edge = match eager(op) {
                    Some(op) => RangeEdge::Binary(op),
                    None => RangeEdge::Lazy { and: op == And },
                };
                self.typing.derive(lhs, rhs, class, edge);
                if let Some(divisor) = rhs_graph
                    && matches!(op, Div | Rem)
                {
                    self.recorded.obligations.push(Obligation {
                        owner: self.owner,
                        node,
                        divisor,
                        context: self.context(),
                    });
                }
                // An operator over constants is the constant the machine
                // would compute, an integer for the thresholds.
                let folded = match (eager(op), rhs_graph) {
                    (Some(op), Some(rhs_graph)) => {
                        match (
                            &self.consts[lhs_graph.index()],
                            &self.consts[rhs_graph.index()],
                        ) {
                            (Some(a), Some(b)) => {
                                let (a, b) = (Value::Int(a.clone()), Value::Int(b.clone()));
                                match Op::Binary(op).apply(&[&a, &b]) {
                                    Ok(Value::Int(value)) => Some(value),
                                    _ => None,
                                }
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let id = self.classify(node, class);
                if let Some(folded) = folded {
                    self.fold(id, folded);
                }
            }
            NodeKind::IfExpr => {
                let (then_context, else_context) = self
                    .branch_contexts
                    .pop()
                    .expect("an if's branches open before it finishes");
                let (then_region, else_region) = self
                    .branch_regions
                    .pop()
                    .expect("an if's branches open before it finishes");
                let branch = ast::IfExpr::cast(tree, node).unwrap();
                let condition_node = branch.condition(tree).unwrap().node();
                let condition = self.typed(condition_node);
                let then_node = branch.then_branch(tree).unwrap().node();
                let then_branch = self.typed(then_node);
                let else_node = branch.else_branch(tree).map(|e| e.node());
                let else_branch = else_node.and_then(|n| self.typed(n));
                let cond_graph = self.node_of(condition_node);
                self.push(
                    node,
                    Op::Join {
                        then: then_region,
                        else_: else_region,
                    },
                    &[cond_graph],
                    None,
                );
                if let Some(condition) = condition {
                    self.require(condition_node, condition, Expected::Ty(Ty::Bool), None);
                }
                let then_branch = then_branch?;
                match else_node {
                    // Without an else, the then branch is unit, and so is
                    // the `if`.
                    None => {
                        self.require(then_node, then_branch, Expected::Ty(Ty::Unit), None);
                        let class = self.typing.unit(self.context(), node);
                        condition?;
                        self.classify(node, class);
                    }
                    // Each branch decides the `if` and learns nothing from
                    // the other, so branches that disagree leave the `if`
                    // undetermined, conflicted on its own class, and keep
                    // their own types. The verdict pass reports it there.
                    Some(_) => {
                        let branches = [then_branch, else_branch?];
                        let join = self.typing.fresh();
                        for (branch, context) in
                            branches.into_iter().zip([then_context, else_context])
                        {
                            self.typing.branch(branch, context, join);
                        }
                        condition?;
                        self.classify(node, join);
                        self.demand(node, join, DemandKind::Agree { branches });
                    }
                }
            }
            _ => unreachable!("scheduled supported node"),
        }
        Some(())
    }
    fn call(&mut self, node: NodeIdx, target: FunctionId, callee: NodeIdx) -> Option<()> {
        let _ = callee;
        let context = self.context();
        let function = &self.headers[target.index()];
        let tree = self.source.tree;
        let list = ast::CallExpr::cast(tree, node)
            .unwrap()
            .arg_list(tree)
            .unwrap();
        let params = function.params.as_deref();
        if params.is_some() {
            // The callee is reached, whole call or not: what it does is
            // checked on the strength of any call to it.
            self.typing.flow(context, function.entry, RangeEdge::Enter);
        }
        // Every argument that exists is held to its parameter, arity aside;
        // its node and its syntax are kept in case the call is whole.
        let mut inputs = std::mem::take(&mut self.inputs);
        inputs.clear();
        let written = run(self.placed.arguments.len());
        let mut complete = true;
        for (index, arg) in list.args(tree).enumerate() {
            let syntax = arg.node();
            inputs.push(self.node_of(syntax));
            self.placed.arguments.push(syntax);
            match (self.typed(syntax), params) {
                (Some(value), Some(params)) => {
                    if let Some(&expected) = params.get(index) {
                        self.require(syntax, value, Expected::Ty(expected), Some(function.item));
                    }
                }
                (None, _) => complete = false,
                _ => {}
            }
        }
        let count = inputs.len();
        if let Some(params) = params
            && count != params.len()
        {
            self.source.error(
                node,
                codes::ARITY,
                format!("expected {} arguments, found {count}", params.len()),
                Some((self.source.span(function.item), "declared here")),
            );
        }
        // A call is a call when its callee has parameters to hold it to
        // and every argument is there; otherwise it never happens, and is
        // a hole over what its arguments built.
        let whole = params.is_some_and(|params| count == params.len() && complete);
        let call = self.push(
            node,
            if whole { Op::Call(target) } else { Op::Hole },
            &inputs,
            None,
        );
        if !whole {
            self.placed.arguments.truncate(written as usize);
            self.inputs = inputs;
            return None;
        }
        self.placed.calls.push(PlacedCall {
            node: call,
            caller: FunctionId::new(self.owner as usize),
            callee: target,
            context: self.context_node(),
            arguments: written..run(self.placed.arguments.len()),
        });
        // Only now do the arguments reach the parameters.
        let param_classes = &self.param_classes[function.param_classes.clone()];
        for (&arg, &param) in inputs.iter().zip(param_classes) {
            let value =
                self.placed.classes[arg.index()].expect("a whole call's arguments have classes");
            self.typing
                .derive(value, context, param, RangeEdge::Argument);
        }
        self.inputs = inputs;
        let class = self.typing.call(function.result?, node);
        self.classify(node, class);
        Some(())
    }
}
