//! Semantic goldens selected by `stages`, not by the existence of `hir.snap`.
//! Update with `UPDATE_HIR=1 cargo test -p sumi-hir --test corpus`.

use std::fmt::Write as _;

use sumi_frontend::{FileId, Location, Place, Severity, parse_source};
use sumi_hir::{
    Analysis, BinaryOp, Body, ExprId, ExprKind, Local, Statement, StatementKind, analyze,
};
use sumi_text::Span;

#[path = "../../../tests/support/corpus.rs"]
mod corpus;

#[test]
fn selected_cases_match_their_snapshots() {
    corpus::check(corpus::Stage::Hir, snapshot);
}

fn span(span: Span) -> String {
    format!(
        "@{}..{}",
        span.range().start().to_u32(),
        span.range().end().to_u32()
    )
}

fn location(location: Location) -> String {
    match location.place {
        Place::Range(_) => span(location.span()),
        Place::Point(offset) => format!("@{}", offset.to_u32()),
    }
}

fn local(analysis: &Analysis, local: &Local) -> String {
    format!("{}{}", analysis.text(local.origin), span(local.origin))
}

fn snapshot(source: &str) -> String {
    let analysis = analyze(parse_source(FileId::new(0), source.into()).unwrap());
    let syntax_errors = analysis
        .parsed()
        .diagnostics()
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .count();
    let semantic_errors = analysis
        .diagnostics()
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .count();
    let mut out = format!(
        "file: {}\nfrontend errors: {syntax_errors} (see frontend.snap)\nsemantic errors: {semantic_errors}\n",
        if analysis.is_valid() {
            "accepted"
        } else {
            "rejected"
        }
    );
    for function in analysis.functions() {
        write!(
            out,
            "\nfn {}{}",
            function
                .name()
                .map_or("<missing>", |name| analysis.text(name)),
            span(function.origin())
        )
        .unwrap();
        match function.signature() {
            Some(signature) => {
                let params = signature
                    .params
                    .iter()
                    .map(|param| param.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(out, " ({params}) -> {}", signature.result).unwrap();
            }
            None => out.push_str(" signature: unavailable\n"),
        }
        if let Some(body) = function.body() {
            for &param in body.params() {
                let param = body.local(param);
                writeln!(out, "  param {}: {}", local(&analysis, param), param.ty).unwrap();
            }
            dump_body(&analysis, body, &mut out);
        } else {
            out.push_str("  body: unavailable\n");
        }
    }
    if !analysis.diagnostics().is_empty() {
        out.push_str("\n== semantic diagnostics ==\n");
        for diagnostic in analysis.diagnostics() {
            writeln!(
                out,
                "{}[{}]: {}",
                diagnostic.severity.as_str(),
                diagnostic.code,
                diagnostic.message
            )
            .unwrap();
            for (role, label) in std::iter::once(("primary", &diagnostic.primary)).chain(
                diagnostic
                    .secondary
                    .iter()
                    .map(|label| ("secondary", label)),
            ) {
                write!(out, "  {role} {}", location(label.location)).unwrap();
                if let Some(message) = &label.message {
                    write!(out, ": {message}").unwrap();
                }
                out.push('\n');
            }
            for note in &diagnostic.notes {
                writeln!(out, "  note: {note}").unwrap();
            }
            assert!(
                diagnostic.fix.is_none(),
                "add semantic fix rendering when fixes are introduced"
            );
        }
    }
    out
}

// Render the ownership tree, never the arena's allocation order. A local or
// function reference uses its declaration spelling and source origin instead of
// a numeric storage ID. Iteration also keeps the renderer host-stack-safe.
enum Work<'a> {
    Expr(String, ExprId, usize),
    Statement(&'a Statement, usize),
    Unit(&'static str, usize),
}

fn dump_body(analysis: &Analysis, body: &Body, out: &mut String) {
    let mut work = vec![Work::Expr("body".into(), body.root(), 1)];
    while let Some(task) = work.pop() {
        let (role, id, depth) = match task {
            Work::Expr(role, id, depth) => (role, id, depth),
            Work::Unit(role, depth) => {
                writeln!(out, "{}{}: unit (implicit)", "  ".repeat(depth), role).unwrap();
                continue;
            }
            Work::Statement(statement, depth) => {
                let indent = "  ".repeat(depth);
                match statement.kind {
                    StatementKind::Let {
                        local: id,
                        initializer,
                    } => {
                        let binding = body.local(id);
                        writeln!(
                            out,
                            "{indent}let {}: {} {}",
                            local(analysis, binding),
                            binding.ty,
                            span(statement.origin)
                        )
                        .unwrap();
                        work.push(Work::Expr("initializer".into(), initializer, depth + 1));
                    }
                    StatementKind::Eval(id) => {
                        writeln!(out, "{indent}discard {}", span(statement.origin)).unwrap();
                        work.push(Work::Expr("value".into(), id, depth + 1));
                    }
                }
                continue;
            }
        };
        let expr = body.expression(id);
        let operation = match &expr.kind {
            ExprKind::Int(value) => format!("int {value}"),
            ExprKind::Bool(value) => format!("bool {value}"),
            ExprKind::Local(id) => format!("read {}", local(analysis, body.local(*id))),
            ExprKind::Neg(_) => "negate".into(),
            ExprKind::Not(_) => "not".into(),
            ExprKind::Binary { op, .. } => format!("eager {}", operator(*op)),
            ExprKind::And { .. } => "lazy and".into(),
            ExprKind::Or { .. } => "lazy or".into(),
            ExprKind::Call {
                function, callee, ..
            } => {
                let function = analysis.function(*function);
                format!(
                    "call {}{} (callee {})",
                    analysis.text(function.name().unwrap()),
                    span(function.origin()),
                    span(*callee)
                )
            }
            ExprKind::If { .. } => "if".into(),
            ExprKind::Block { .. } => "block".into(),
        };
        writeln!(
            out,
            "{}{role}: {operation} : {} {}",
            "  ".repeat(depth),
            expr.ty,
            span(expr.origin)
        )
        .unwrap();
        let child_depth = depth + 1;
        match &expr.kind {
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Local(_) => {}
            ExprKind::Neg(operand) | ExprKind::Not(operand) => {
                work.push(Work::Expr("operand".into(), *operand, child_depth))
            }
            ExprKind::Binary { lhs, rhs, .. }
            | ExprKind::And { lhs, rhs }
            | ExprKind::Or { lhs, rhs } => {
                work.push(Work::Expr("rhs".into(), *rhs, child_depth));
                work.push(Work::Expr("lhs".into(), *lhs, child_depth));
            }
            ExprKind::Call { args, .. } => {
                for (index, &arg) in body.args(*args).iter().enumerate().rev() {
                    work.push(Work::Expr(format!("arg[{index}]"), arg, child_depth));
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                work.push(match else_branch {
                    Some(branch) => Work::Expr("else".into(), *branch, child_depth),
                    None => Work::Unit("else", child_depth),
                });
                work.push(Work::Expr("then".into(), *then_branch, child_depth));
                work.push(Work::Expr("condition".into(), *condition, child_depth));
            }
            ExprKind::Block { statements, tail } => {
                work.push(match tail {
                    Some(tail) => Work::Expr("tail".into(), *tail, child_depth),
                    None => Work::Unit("tail", child_depth),
                });
                for statement in body.statements(*statements).iter().rev() {
                    work.push(Work::Statement(statement, child_depth));
                }
            }
        }
    }
}

fn operator(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Rem => "%",
        BinaryOp::Eq => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Le => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::Ge => ">=",
    }
}

#[test]
fn rendering_is_deterministic() {
    let source = "fn f(x: int) -> int { let x = x + 1\n x }";
    assert_eq!(snapshot(source), snapshot(source));
}
