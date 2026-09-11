use std::collections::HashMap;

use sumi_frontend::{DiagnosticCode, DiagnosticGroup, Label, Location};
use sumi_lexer::{RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    NodeIdx, NodeKind, SyntaxTree,
    ast::{self, AstNode},
};

use crate::infer::{Inference, Term};
use crate::*;

struct Header {
    params: Option<Box<[Ty]>>,
    result: Option<Term>,
    origin: Span,
}

struct DraftLocal {
    name: Box<str>,
    origin: Span,
    ty: Term,
}

struct DraftExpr {
    kind: ExprKind,
    origin: Span,
    ty: Term,
}

struct DraftBody {
    params: Vec<LocalId>,
    locals: Vec<DraftLocal>,
    exprs: Vec<DraftExpr>,
    root: ExprId,
}

impl DraftBody {
    fn finish(self, inference: &Inference, functions: &[Function]) -> Option<Body> {
        let locals = self
            .locals
            .into_iter()
            .map(|local| {
                Some(Local {
                    name: local.name,
                    origin: local.origin,
                    ty: inference.resolve(local.ty)?,
                })
            })
            .collect::<Option<_>>()?;
        let exprs = self
            .exprs
            .into_iter()
            .map(|expr| {
                let ty = inference.resolve(expr.ty)?;
                if let ExprKind::Call { function, .. } = &expr.kind {
                    // A caller's local requirements can solve its call term without
                    // solving the provider. That is not a publishable call.
                    if functions[function.0].signature.as_ref()?.result != ty {
                        return None;
                    }
                }
                Some(Expr {
                    kind: expr.kind,
                    origin: expr.origin,
                    ty,
                })
            })
            .collect::<Option<_>>()?;
        Some(Body {
            params: self.params,
            locals,
            exprs,
            root: self.root,
        })
    }
}

enum ObligationKind {
    Equal(Term, Option<(Span, &'static str)>),
    Unused,
    Comparable,
}

struct Obligation {
    owner: usize,
    node: NodeIdx,
    actual: Term,
    kind: ObligationKind,
}

struct Source<'a> {
    parsed: &'a ParsedSource,
    tree: &'a SyntaxTree,
    diagnostics: Vec<Diagnostic>,
}

impl Source<'_> {
    fn span(&self, node: NodeIdx) -> Span {
        Span::new(
            self.parsed.file(),
            self.tree.byte_range(node, self.parsed.lexed()),
        )
    }
    fn text(&self, node: NodeIdx) -> &str {
        let range = self.span(node).range();
        &self.parsed.source()[range.start().to_usize()..range.end().to_usize()]
    }
    fn name(&self, name: Option<ast::Name>) -> Option<(Box<str>, NodeIdx)> {
        let node = name?.node();
        (!self.tree.has_error(node)
            && self.parsed.lexed().kind(self.tree.first_token(node)) == SyntaxKind::Ident)
            .then(|| (self.text(node).into(), node))
    }
    fn error(
        &mut self,
        node: NodeIdx,
        code: &'static str,
        message: impl Into<Box<str>>,
        related: Option<(Span, &'static str)>,
    ) {
        self.diagnostics.push(Diagnostic {
            code: DiagnosticCode::new(DiagnosticGroup::new("semantic"), code),
            severity: Severity::Error,
            message: message.into(),
            primary: Label {
                location: Location::range(self.span(node)),
                message: None,
            },
            secondary: related
                .into_iter()
                .map(|(span, message)| Label {
                    location: Location::range(span),
                    message: Some(message.into()),
                })
                .collect(),
            notes: Box::new([]),
            fix: None,
        });
    }
    fn ty(&mut self, node: ast::TypeRef) -> Option<Ty> {
        if self.tree.has_error(node.node()) {
            return None;
        }
        match self.text(node.node()) {
            "int" => Some(Ty::Int),
            "bool" => Some(Ty::Bool),
            "unit" => Some(Ty::Unit),
            name => {
                self.error(
                    node.node(),
                    "unknown-type",
                    format!("unknown type `{name}`"),
                    None,
                );
                None
            }
        }
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

struct Parameter {
    name: Option<(Box<str>, NodeIdx)>,
    ty: Option<Ty>,
}

/// Collect headers and body constraints before publishing concrete HIR.
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
    let mut functions: Vec<Function> = Vec::with_capacity(items.len());
    let mut names = HashMap::<Box<str>, (Span, Option<FunctionId>)>::new();
    let mut parameters = Vec::with_capacity(items.len());
    let mut headers = Vec::with_capacity(items.len());
    let mut inference = Inference::default();
    let mut obligations = Vec::new();
    for item in &items {
        let name = source.name(item.name(tree));
        let id = FunctionId(functions.len());
        if let Some((name, node)) = &name {
            if let Some((first, target)) = names.get_mut(name) {
                source.error(
                    *node,
                    "duplicate-name",
                    format!("duplicate function `{name}`"),
                    Some((*first, "declared here")),
                );
                *target = None;
            } else {
                names.insert(name.clone(), (source.span(*node), Some(id)));
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
                                "missing-type",
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
        let result = if let Some(ret) = item.ret(tree) {
            source.ty(ret).map(Term::Known)
        } else {
            // None can mean damaged syntax, not omission. Only an empty gap or
            // the expression-body '=' establishes an omitted result annotation.
            list.filter(|list| !tree.has_error(list.node()))
                .and_then(|list| {
                    let end = item
                        .body(tree)
                        .map_or(tree.end_token(item.node()), |e| tree.first_token(e.node()));
                    let mut tokens = source.tokens(tree.end_token(list.node()), end);
                    match (tokens.next(), tokens.next()) {
                        (None, None) => Some(Term::Known(Ty::Unit)),
                        (Some(SyntaxKind::Eq), None) => Some(inference.fresh()),
                        _ => None,
                    }
                })
        };
        headers.push(Header {
            params: valid.then(|| params.iter().map(|p| p.ty.unwrap()).collect()),
            result,
            origin: source.span(item.node()),
        });
        parameters.push(params);
        functions.push(Function {
            name: name.map(|n| n.0),
            origin: source.span(item.node()),
            signature: None,
            body: None,
        });
    }
    let mut bodies = Vec::with_capacity(items.len());
    // Syntax node IDs are dense and bodies have disjoint nodes. Expression
    // IDs remain body-local; a builder only reads entries in its own body.
    let mut values = vec![None; tree.len()];
    for (index, (item, params)) in items.iter().zip(parameters).enumerate() {
        bodies.push(
            Builder::new(
                &mut source,
                &headers,
                &names,
                &mut inference,
                &mut obligations,
                index,
                &mut values,
            )
            .build(*item, params),
        );
    }
    drop(values);
    inference.solve();
    let mut replay = inference.replay();
    let mut failed = vec![false; functions.len()];
    for obligation in obligations {
        let actual = replay.resolve(obligation.actual);
        let (code, message, related) = match obligation.kind {
            ObligationKind::Equal(expected, related) => match (actual, replay.resolve(expected)) {
                (Some(actual), Some(expected)) if actual != expected => (
                    "type-mismatch",
                    format!("expected {expected:?}, found {actual:?}"),
                    related,
                ),
                _ => {
                    replay.equal(obligation.actual, expected);
                    continue;
                }
            },
            ObligationKind::Unused => {
                if actual.is_none_or(|ty| ty == Ty::Unit) {
                    replay.equal(obligation.actual, Ty::Unit.into());
                    continue;
                }
                (
                    "unused-value",
                    format!(
                        "unused value of type {:?}; use `_ =` to discard it",
                        actual.unwrap()
                    ),
                    None,
                )
            }
            ObligationKind::Comparable => {
                if actual != Some(Ty::Unit) {
                    continue;
                }
                (
                    "type-mismatch",
                    "unit values cannot be compared".to_owned(),
                    None,
                )
            }
        };
        failed[obligation.owner] = true;
        source.error(obligation.node, code, message, related);
    }
    for (index, header) in headers.into_iter().enumerate() {
        let result = header.result.and_then(|term| inference.resolve(term));
        if let (Some(params), Some(result)) = (header.params, result) {
            functions[index].signature = Some(Signature { params, result });
        }
        if matches!(header.result, Some(Term::Var(_)))
            && result.is_none()
            && bodies[index].is_some()
            && !failed[index]
        {
            let message = if inference.conflicted(header.result.unwrap()) {
                "conflicting function result constraints; add a return type annotation"
            } else {
                "cannot infer function result; add a return type annotation"
            };
            source.error(items[index].node(), "cannot-infer", message, None);
        }
    }
    for (index, body) in bodies.into_iter().enumerate() {
        if !failed[index] && functions[index].signature.is_some() {
            functions[index].body = body.and_then(|body| body.finish(&inference, &functions));
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
type Scope = HashMap<Box<str>, Option<LocalId>>;
enum Work {
    Enter(NodeIdx),
    Finish(NodeIdx),
    Call(NodeIdx, FunctionId, NodeIdx),
}

struct Builder<'a, 's> {
    source: &'a mut Source<'s>,
    functions: &'a [Header],
    names: &'a HashMap<Box<str>, (Span, Option<FunctionId>)>,
    inference: &'a mut Inference,
    obligations: &'a mut Vec<Obligation>,
    owner: usize,
    scopes: Vec<Scope>,
    locals: Vec<DraftLocal>,
    exprs: Vec<DraftExpr>,
    values: &'a mut [Option<ExprId>],
    statements: Vec<(NodeIdx, Statement)>,
    failed: bool,
}

impl<'a, 's> Builder<'a, 's> {
    fn new(
        source: &'a mut Source<'s>,
        functions: &'a [Header],
        names: &'a HashMap<Box<str>, (Span, Option<FunctionId>)>,
        inference: &'a mut Inference,
        obligations: &'a mut Vec<Obligation>,
        owner: usize,
        values: &'a mut [Option<ExprId>],
    ) -> Self {
        Self {
            source,
            functions,
            names,
            inference,
            obligations,
            owner,
            scopes: vec![Scope::new()],
            locals: Vec::new(),
            exprs: Vec::new(),
            values,
            statements: Vec::new(),
            failed: false,
        }
    }
    fn build(mut self, item: ast::FnItem, parameters: Vec<Parameter>) -> Option<DraftBody> {
        let mut params = Vec::new();
        let mut first = HashMap::new();
        for param in parameters {
            if let Some((name, node)) = param.name {
                if let Some(&span) = first.get(&name) {
                    self.source.error(
                        node,
                        "duplicate-name",
                        format!("duplicate parameter `{name}`"),
                        Some((span, "declared here")),
                    );
                    self.scopes[0].insert(name, None);
                    self.failed = true;
                } else {
                    first.insert(name.clone(), self.source.span(node));
                    if let Some(local) = self.bind(name, node, param.ty.map(Term::Known)) {
                        params.push(local);
                    }
                }
            } else {
                self.failed = true;
            }
        }
        let header = &self.functions[self.owner];
        let result = header.result;
        self.failed |= header.params.is_none() || result.is_none();
        let root_node = item.body(self.source.tree)?.node();
        let mut work = vec![Work::Enter(root_node)];
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
        let root = self.value(root_node);
        // A failed parameter does not erase an independently known result type.
        if let (Some(root), Some(result)) = (root, result)
            && !self.require(
                root_node,
                root,
                result,
                Some((self.source.span(item.node()), "declared here")),
            )
        {
            self.failed = true;
        }
        if self.failed {
            return None;
        }
        Some(DraftBody {
            params,
            locals: self.locals,
            exprs: self.exprs,
            root: root?,
        })
    }
    fn bind(&mut self, name: Box<str>, node: NodeIdx, ty: Option<Term>) -> Option<LocalId> {
        let id = ty.map(|ty| {
            let id = LocalId::new(self.locals.len());
            self.locals.push(DraftLocal {
                name: name.clone(),
                origin: self.source.span(node),
                ty,
            });
            id
        });
        self.failed |= id.is_none();
        self.scopes.last_mut().unwrap().insert(name, id);
        id
    }
    fn lookup(&self, name: &str) -> Option<Option<LocalId>> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }
    fn emit(&mut self, node: NodeIdx, kind: ExprKind, ty: impl Into<Term>) -> ExprId {
        let id = ExprId::new(self.exprs.len());
        self.exprs.push(DraftExpr {
            kind,
            origin: self.source.span(node),
            ty: ty.into(),
        });
        self.values[node.to_usize()] = Some(id);
        id
    }
    fn unsupported(&mut self, node: NodeIdx) {
        self.source.error(
            node,
            "unsupported",
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
            self.scopes.push(Scope::new());
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
                    "not-callable",
                    format!("local `{name}` is not callable"),
                    Some((self.locals[local.index()].origin, "declared here")),
                );
            }
            return None;
        }
        match self.names.get(name) {
            Some((_, target)) => *target,
            None => {
                self.source.error(
                    node,
                    "unknown-name",
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
            Some(value) => Some(self.emit(origin, ExprKind::Int(value), Ty::Int)),
            None => {
                self.source.error(
                    literal,
                    "integer-range",
                    "integer literal is outside signed 64-bit range",
                    None,
                );
                None
            }
        }
    }
    fn require(
        &mut self,
        node: NodeIdx,
        expr: ExprId,
        expected: impl Into<Term>,
        related: Option<(Span, &'static str)>,
    ) -> bool {
        let expected = expected.into();
        let actual = self.exprs[expr.index()].ty;
        if actual == expected {
            return true;
        }
        if let (Term::Known(actual), Term::Known(expected)) = (actual, expected) {
            self.source.error(
                node,
                "type-mismatch",
                format!("expected {expected:?}, found {actual:?}"),
                related,
            );
            return false;
        }
        self.inference.equal(actual, expected);
        self.obligations.push(Obligation {
            owner: self.owner,
            node,
            actual,
            kind: ObligationKind::Equal(expected, related),
        });
        true
    }
    fn value(&self, node: NodeIdx) -> Option<ExprId> {
        self.values[node.to_usize()]
    }
    fn finish(&mut self, node: NodeIdx) -> Option<()> {
        let tree = self.source.tree;
        match tree.kind(node) {
            NodeKind::Block => {
                self.scopes.pop().unwrap();
                let mut statements = Vec::new();
                let mut tail = None;
                let mut valid = !tree.has_error(node);
                // Children arrive last first; only the first can be the tail.
                // Completed statements are stacked in source order. Nested
                // blocks consume their own statements before reaching here.
                for (index, child) in tree.children(node).enumerate() {
                    if let Some((_, statement)) = self.statements.pop_if(|(node, _)| *node == child)
                    {
                        statements.push(statement);
                    } else if let Some(value) = self.value(child) {
                        if index == 0 {
                            tail = Some(value);
                        } else {
                            let ty = self.exprs[value.index()].ty;
                            if let Term::Known(ty) = ty {
                                if ty != Ty::Unit {
                                    self.source.error(
                                        child,
                                        "unused-value",
                                        format!(
                                            "unused value of type {ty:?}; use `_ =` to discard it"
                                        ),
                                        None,
                                    );
                                    valid = false;
                                }
                            } else {
                                self.inference.equal(ty, Ty::Unit.into());
                                self.obligations.push(Obligation {
                                    owner: self.owner,
                                    node: child,
                                    actual: ty,
                                    kind: ObligationKind::Unused,
                                });
                            }
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
                let ty = tail.map_or(Term::Known(Ty::Unit), |id| self.exprs[id.index()].ty);
                self.emit(node, ExprKind::Block { statements, tail }, ty);
            }
            NodeKind::LetStmt => {
                let binding = ast::LetStmt::cast(tree, node).unwrap();
                let (name, name_node) = self.source.name(binding.name(tree))?;
                let initializer_node = binding.initializer(tree).unwrap().node();
                let mut initializer = self.value(initializer_node);
                if let Some(annotation) = binding.type_ref(tree) {
                    let ty = self.source.ty(annotation);
                    if let (Some(value), Some(ty)) = (initializer, ty) {
                        if !self.require(
                            initializer_node,
                            value,
                            ty,
                            Some((self.source.span(annotation.node()), "declared here")),
                        ) {
                            initializer = None;
                        }
                    } else {
                        initializer = None;
                    }
                }
                let local = self.bind(
                    name,
                    name_node,
                    initializer.map(|id| self.exprs[id.index()].ty),
                );
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
                        self.emit(node, ExprKind::Local(local), self.locals[local.index()].ty);
                    }
                    Some(None) => return None,
                    None => {
                        if self.names.contains_key(name) {
                            self.unsupported(node);
                        } else {
                            self.source.error(
                                node,
                                "unknown-name",
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
                        self.emit(
                            node,
                            ExprKind::Bool(self.source.text(node) == "true"),
                            Ty::Bool,
                        );
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
                if !self.require(operand, value, ty, None) {
                    return None;
                }
                self.emit(
                    node,
                    if neg {
                        ExprKind::Neg(value)
                    } else {
                        ExprKind::Not(value)
                    },
                    ty,
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
                let (expected, ty) = match op {
                    Add | Sub | Mul | Div | Rem => (Some(Term::Known(Ty::Int)), Ty::Int),
                    Lt | Le | Gt | Ge => (Some(Term::Known(Ty::Int)), Ty::Bool),
                    Eq | Ne => (lhs.or(rhs).map(|id| self.exprs[id.index()].ty), Ty::Bool),
                    And | Or => (Some(Term::Known(Ty::Bool)), Ty::Bool),
                };
                let mut valid = true;
                if let Some(expected) = expected {
                    for (child, value) in [(lhs_node, lhs), (rhs_node, rhs)] {
                        if let Some(value) = value {
                            valid &= self.require(child, value, expected, None);
                        }
                    }
                    if expected == Term::Known(Ty::Unit) {
                        self.source.error(
                            node,
                            "type-mismatch",
                            "unit values cannot be compared",
                            None,
                        );
                        valid = false;
                    } else if matches!(op, Eq | Ne) && matches!(expected, Term::Var(_)) {
                        self.obligations.push(Obligation {
                            owner: self.owner,
                            node,
                            actual: expected,
                            kind: ObligationKind::Comparable,
                        });
                    }
                }
                if !valid {
                    return None;
                }
                let (lhs, rhs) = (lhs?, rhs?);
                self.emit(node, ExprKind::binary(op, lhs, rhs), ty);
            }
            NodeKind::IfExpr => {
                let branch = ast::IfExpr::cast(tree, node).unwrap();
                let condition_node = branch.condition(tree).unwrap().node();
                let condition = self.value(condition_node);
                let then_node = branch.then_branch(tree).unwrap().node();
                let then_branch = self.value(then_node);
                let else_node = branch.else_branch(tree).map(|e| e.node());
                let else_branch = else_node.and_then(|n| self.value(n));
                let mut valid = true;
                if let Some(condition) = condition {
                    valid &= self.require(condition_node, condition, Ty::Bool, None);
                }
                let else_ty = if else_node.is_some() {
                    else_branch.map(|id| self.exprs[id.index()].ty)
                } else {
                    Some(Term::Known(Ty::Unit))
                };
                if let (Some(then_branch), Some(ty)) = (then_branch, else_ty) {
                    valid &= self.require(
                        then_node,
                        then_branch,
                        ty,
                        else_node.map(|n| {
                            (self.source.span(n), "other branch determines expected type")
                        }),
                    );
                }
                if !valid || (else_node.is_some() && else_branch.is_none()) {
                    return None;
                }
                let then_branch = then_branch?;
                // Preserve the equality class if either arm is inferred. A
                // literal arm must not hide conflicts arriving through imports.
                let ty = match (self.exprs[then_branch.index()].ty, else_ty) {
                    (_, Some(ty @ Term::Var(_))) => ty,
                    (ty, _) => ty,
                };
                self.emit(
                    node,
                    ExprKind::If {
                        condition: condition?,
                        then_branch,
                        else_branch,
                    },
                    ty,
                );
            }
            _ => unreachable!("scheduled supported node"),
        }
        Some(())
    }
    fn call(&mut self, node: NodeIdx, target: FunctionId, callee: NodeIdx) -> Option<()> {
        let function = &self.functions[target.0];
        let params = function.params.as_ref()?;
        let tree = self.source.tree;
        let list = ast::CallExpr::cast(tree, node)
            .unwrap()
            .arg_list(tree)
            .unwrap();
        let args: Vec<_> = list.args(tree).map(|arg| arg.node()).collect();
        let mut valid = args.len() == params.len();
        if !valid {
            self.source.error(
                node,
                "arity",
                format!("expected {} arguments, found {}", params.len(), args.len()),
                Some((function.origin, "declared here")),
            );
        }
        for (&arg, &expected) in args.iter().zip(params) {
            if let Some(value) = self.value(arg) {
                valid &= self.require(
                    arg,
                    value,
                    expected,
                    Some((function.origin, "declared here")),
                );
            }
        }
        let args: Option<Vec<_>> = args.into_iter().map(|n| self.value(n)).collect();
        if !valid {
            return None;
        }
        let result = match function.result? {
            term @ Term::Known(_) => term,
            term @ Term::Var(_) => self.inference.import(term),
        };
        self.emit(
            node,
            ExprKind::Call {
                function: target,
                args: args?,
                callee: self.source.span(callee),
            },
            result,
        );
        Some(())
    }
}
