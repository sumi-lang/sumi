//! Semantic goldens selected by `stages`, not by the existence of `hir.snap`:
//! the graph with what the checker decided, and, for cases that select
//! `eval`, every parameterless function of an accepted case run to its
//! value, with the machine's step count and deepest call nesting as the
//! witnesses of what running it costs, and the depth the analysis claimed
//! beside the depth the run observed. Update with
//! `UPDATE_HIR=1 cargo test -p sumi-hir --test corpus` and
//! `UPDATE_EVAL=1 cargo test -p sumi-hir --test corpus`.

use std::fmt::Write as _;

use sumi_frontend::{FileId, Location, Place, Severity, parse_source};
use sumi_hir::{Analysis, BinaryOp, FunctionId, Graph, NodeId, Op, RegionId, analyze};
use sumi_text::Span;

#[path = "../../../tests/support/corpus.rs"]
mod corpus;

#[test]
fn selected_cases_match_their_snapshots() {
    corpus::check(corpus::Stage::Hir, |source, _| snapshot(source));
}

#[test]
fn selected_cases_run_as_their_snapshots_say() {
    corpus::check(corpus::Stage::Eval, |source, _| run(source));
}

fn run(source: &str) -> String {
    let analysis = analyze(parse_source(FileId::new(0), source.into()).unwrap());
    let Some(program) = analysis.program() else {
        return "file: rejected (see hir.snap); nothing runs\n".to_owned();
    };
    let mut out = "file: accepted\n".to_owned();
    for (id, function) in program.functions() {
        let name = analysis.text(function.name().expect("a valid file names its functions"));
        if !program.signature(id).params.is_empty() {
            writeln!(out, "fn {name}: takes arguments, not run").unwrap();
            continue;
        }
        let mut machine = program.machine(id, &[]);
        while !machine.step() {}
        let value = match machine.outcome().expect("a finished run has its outcome") {
            Ok(value) => value,
            Err(refusal) => panic!("fn {name} was refused: {refusal:?}"),
        };
        write!(
            out,
            "fn {name} = {value} (steps {}, depth {}",
            machine.steps(),
            machine.max_depth()
        )
        .unwrap();
        match function.depth_bound() {
            Some(bound) => writeln!(out, " of at most {bound})").unwrap(),
            None => out.push_str(", unbounded)\n"),
        }
    }
    out
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

fn snapshot(source: &str) -> String {
    let analysis = analyze(parse_source(FileId::new(0), source.into()).unwrap());
    let syntax_errors = analysis
        .parsed()
        .diagnostics()
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .count();
    let semantic: Vec<_> = analysis.semantic_diagnostics().collect();
    let semantic_errors = semantic
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
    let shape = Shape::of(analysis.graph());
    for (index, function) in analysis.functions().iter().enumerate() {
        write!(
            out,
            "\nfn {}{}",
            function
                .name()
                .map_or("<missing>", |name| analysis.text(name)),
            span(function.origin())
        )
        .unwrap();
        match (
            function.signature(),
            analysis.ranges(FunctionId::new(index)),
        ) {
            (Some(signature), Some(ranges)) => {
                let params = signature
                    .params
                    .iter()
                    .zip(&ranges.params)
                    .map(|(ty, may)| format!("{ty} ∈ {}", may.shown(*ty)))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(
                    out,
                    " ({params}) -> {} ∈ {}",
                    signature.result,
                    ranges.result.shown(signature.result)
                )
                .unwrap();
            }
            _ => out.push_str(" signature: unavailable\n"),
        }
        dump(&analysis, &shape, FunctionId::new(index), &mut out);
    }
    if !semantic.is_empty() {
        out.push_str("\n== semantic diagnostics ==\n");
        for diagnostic in semantic {
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

/// What the graph does not store but a rendering needs: how often each
/// node is read, and the innermost region each node sits in.
struct Shape {
    users: Vec<u32>,
    region_of: Vec<Option<RegionId>>,
}

impl Shape {
    fn of(graph: &Graph) -> Self {
        let mut users = vec![0; graph.nodes().len()];
        for node in graph.node_ids() {
            for &input in graph.inputs(node) {
                users[input.index()] += 1;
            }
        }
        // Regions open outermost first, so a later region's run refines
        // an earlier one's.
        let mut region_of = vec![None; graph.nodes().len()];
        for region in graph.region_ids() {
            for node in graph.region(region).nodes() {
                region_of[node.index()] = Some(region);
            }
        }
        Self { users, region_of }
    }
}

fn ty(analysis: &Analysis, node: NodeId) -> String {
    analysis
        .ty(node)
        .map_or_else(|| "?".to_owned(), |ty| ty.to_string())
}

/// A named definition, as its declaration spelling and origin.
fn named(analysis: &Analysis, node: NodeId) -> String {
    match analysis.graph().node(node).name {
        Some(name) => format!("{}{}", analysis.text(name), span(name)),
        None => format!("<unnamed>{}", span(analysis.graph().node(node).origin)),
    }
}

fn dump(analysis: &Analysis, shape: &Shape, function: FunctionId, out: &mut String) {
    let graph = analysis.graph();
    let function = graph.run(function);
    for param in function.params() {
        writeln!(
            out,
            "  param {}: {}",
            named(analysis, param),
            ty(analysis, param)
        )
        .unwrap();
    }
    let region = function.region();
    let result = function.result();
    if result == graph.region(region).result() {
        dump_region(analysis, shape, "body", region, 1, out);
    } else {
        // The declared result the body's value is held to.
        let node = graph.node(result);
        writeln!(
            out,
            "  result: copy : {} {}",
            ty(analysis, result),
            span(node.origin)
        )
        .unwrap();
        dump_region(analysis, shape, "value", region, 2, out);
    }
}

// Render each region as its statements and its value: a named copy is a
// `let`, a node nothing reads is a discard, and every other node prints
// inline under the node that reads it, so the rendering follows use, never
// the table's order. A read of a named node uses its declaration spelling
// and origin; a read under a guard names the guard. A statement that only
// reads a local, `_ = x` or a bare `x`, is an edge and no node, so it does
// not print: what it demanded is in the diagnostics.
fn dump_region(
    analysis: &Analysis,
    shape: &Shape,
    role: &str,
    region: RegionId,
    depth: usize,
    out: &mut String,
) {
    let graph = analysis.graph();
    let region_ref = graph.region(region);
    let result = region_ref.result();
    // The result prints as the tail, unless it is a `let`, which prints as
    // its statement and is read by the tail.
    let statements: Vec<NodeId> = region_ref
        .nodes()
        .filter(|&node| shape.region_of[node.index()] == Some(region))
        .filter(|&node| {
            let named = graph.node(node).name.is_some();
            let contextual = matches!(
                graph.node(node).op,
                Op::Then | Op::Else | Op::Entry | Op::Refine { .. } | Op::Exactly(_)
            );
            named || (node != result && !contextual && shape.users[node.index()] == 0)
        })
        .collect();
    let indent = "  ".repeat(depth);
    if statements.is_empty() {
        dump_node(analysis, shape, role, result, depth, out);
        return;
    }
    writeln!(out, "{indent}{role}:").unwrap();
    for node in statements {
        match (graph.node(node).name, &graph.node(node).op) {
            (Some(_), Op::Copy { .. }) => {
                writeln!(
                    out,
                    "{indent}  let {}: {} {}",
                    named(analysis, node),
                    ty(analysis, node),
                    span(graph.node(node).origin)
                )
                .unwrap();
                let initializer = graph.inputs(node)[0];
                dump_node(analysis, shape, "initializer", initializer, depth + 2, out);
            }
            // A binding too damaged to have an initializer.
            (Some(_), _) => {
                let role = format!("let {}", named(analysis, node));
                dump_definition(analysis, shape, &role, node, depth + 1, out);
            }
            (None, _) => dump_node(analysis, shape, "discard", node, depth + 1, out),
        }
    }
    dump_node(analysis, shape, "tail", result, depth + 1, out);
}

/// The guards a read at `node` is narrowed by, innermost first, and the
/// definition it reads.
fn guards(analysis: &Analysis, mut node: NodeId) -> (Vec<String>, NodeId) {
    let graph = analysis.graph();
    let mut guards = Vec::new();
    loop {
        match graph.node(node).op {
            Op::Refine { sense, .. } => {
                let origin = graph.node(node).origin;
                guards.push(format!(
                    "{} {}{}",
                    analysis.text(origin),
                    if sense { "holds" } else { "fails" },
                    span(origin)
                ));
                node = graph.inputs(node)[0];
            }
            Op::Exactly(value) => {
                guards.push(format!("is {value}"));
                node = graph.inputs(node)[0];
            }
            _ => return (guards, node),
        }
    }
}

/// A use of `node`: a read, by name, of a named definition, under the
/// guards that narrow it, or the definition itself inline.
fn dump_node(
    analysis: &Analysis,
    shape: &Shape,
    role: &str,
    node: NodeId,
    depth: usize,
    out: &mut String,
) {
    let graph = analysis.graph();
    let (guards, definition) = guards(analysis, node);
    if graph.node(definition).name.is_some() {
        let guards = if guards.is_empty() {
            String::new()
        } else {
            format!(" [{}]", guards.join(", "))
        };
        writeln!(
            out,
            "{}{role}: read {}{guards} : {}",
            "  ".repeat(depth),
            named(analysis, definition),
            ty(analysis, node)
        )
        .unwrap();
        return;
    }
    dump_definition(analysis, shape, role, node, depth, out);
}

fn dump_definition(
    analysis: &Analysis,
    shape: &Shape,
    role: &str,
    node: NodeId,
    depth: usize,
    out: &mut String,
) {
    let graph = analysis.graph();
    let indent = "  ".repeat(depth);
    let inputs = graph.inputs(node);
    let entry = graph.node(node);
    let operation = match &entry.op {
        Op::Int(value) => format!("int {value}"),
        Op::Bool(value) => format!("bool {value}"),
        Op::Param(index) => format!("param {index}"),
        Op::Unit => "unit".into(),
        Op::Hole => "hole".into(),
        Op::Copy { .. } => "copy".into(),
        Op::Neg => "negate".into(),
        Op::Not => "not".into(),
        Op::Binary(op) => format!("eager {}", operator(*op)),
        Op::And { .. } => "lazy and".into(),
        Op::Or { .. } => "lazy or".into(),
        Op::Refine { .. } | Op::Exactly(_) => unreachable!("a narrowed read reads its definition"),
        Op::Entry => "entry".into(),
        Op::Then => "then".into(),
        Op::Else => "else".into(),
        Op::Join { .. } => "if".into(),
        Op::Call(function) => {
            let function = analysis.function(*function);
            format!(
                "call {}{}",
                function
                    .name()
                    .map_or("<missing>", |name| analysis.text(name)),
                span(function.origin())
            )
        }
    };
    writeln!(
        out,
        "{indent}{role}: {operation} : {} {}",
        ty(analysis, node),
        span(entry.origin)
    )
    .unwrap();
    let child = depth + 1;
    match &entry.op {
        Op::Int(_) | Op::Bool(_) | Op::Param(_) | Op::Unit | Op::Entry | Op::Then | Op::Else => {}
        Op::Hole => {
            for (index, &input) in inputs.iter().enumerate() {
                dump_node(
                    analysis,
                    shape,
                    &format!("part[{index}]"),
                    input,
                    child,
                    out,
                );
            }
        }
        Op::Copy { .. } => dump_node(analysis, shape, "value", inputs[0], child, out),
        Op::Neg | Op::Not => dump_node(analysis, shape, "operand", inputs[0], child, out),
        Op::Binary(_) => {
            dump_node(analysis, shape, "lhs", inputs[0], child, out);
            dump_node(analysis, shape, "rhs", inputs[1], child, out);
        }
        Op::And { rhs } | Op::Or { rhs } => {
            dump_node(analysis, shape, "lhs", inputs[0], child, out);
            dump_region(analysis, shape, "rhs", *rhs, child, out);
        }
        Op::Refine { .. } | Op::Exactly(_) => unreachable!("a narrowed read reads its definition"),
        Op::Join { then, else_ } => {
            dump_node(analysis, shape, "condition", inputs[0], child, out);
            dump_region(analysis, shape, "then", *then, child, out);
            match else_ {
                Some(else_) => dump_region(analysis, shape, "else", *else_, child, out),
                None => writeln!(out, "{}else: unit (implicit)", "  ".repeat(child)).unwrap(),
            }
        }
        Op::Call(_) => {
            for (index, &input) in inputs.iter().enumerate() {
                dump_node(analysis, shape, &format!("arg[{index}]"), input, child, out);
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
    let source = "fn f(x: int) -> int { let x = x + 1\n x }\nfn g() -> int = f(f(1))";
    assert_eq!(snapshot(source), snapshot(source));
    assert_eq!(run(source), run(source));
}
