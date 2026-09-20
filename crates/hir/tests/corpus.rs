//! Semantic goldens: `hir.snap` for the graph the checker built, `eval.snap` for every
//! parameterless function of an accepted case run to its value.

use std::fmt::Write as _;

use sumi_frontend::parse_source;
use sumi_hir::{
    Analysis, ArithOp, BinaryOp, CmpOp, FunctionId, Graph, NodeId, Op, RegionId, analyze,
};
use sumi_test::corpus;
use sumi_text::TextRange;

#[test]
fn selected_cases_match_their_snapshots() {
    corpus::check(corpus::Stage::Hir, |source, _| snapshot(source));
}

#[test]
fn selected_cases_run_as_their_snapshots_say() {
    corpus::check(corpus::Stage::Eval, |source, _| run(source));
}

fn run(source: &str) -> String {
    let analysis = analyze(parse_source(source.into()).unwrap());
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
        let value = loop {
            match machine.step() {
                None => continue,
                Some(Ok(value)) => break value.clone(),
                Some(Err(refusal)) => panic!("fn {name} was refused: {refusal:?}"),
            }
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

fn at(range: TextRange) -> String {
    let (start, end) = (range.start().to_u32(), range.end().to_u32());
    if start == end {
        format!("@{start}")
    } else {
        format!("@{start}..{end}")
    }
}

fn snapshot(source: &str) -> String {
    let analysis = analyze(parse_source(source.into()).unwrap());
    let syntax_errors = analysis.parsed().diagnostics().len();
    let semantic: Vec<_> = analysis.semantic_diagnostics().collect();
    let semantic_errors = semantic.len();
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
            at(function.origin())
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
                "error[{}]: {}\n  primary {}",
                diagnostic.code,
                diagnostic.message,
                at(diagnostic.primary)
            )
            .unwrap();
            for label in &diagnostic.labels {
                writeln!(out, "  secondary {}: {}", at(label.range), label.message).unwrap();
            }
            assert!(
                diagnostic.fix.is_none(),
                "add semantic fix rendering when fixes are introduced"
            );
        }
    }
    out
}

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
        // Regions are numbered outermost first, so the last write leaves each node's innermost
        // region.
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

fn named(analysis: &Analysis, node: NodeId) -> String {
    match analysis.graph().node(node).name {
        Some(name) => format!("{}{}", analysis.text(name), at(name)),
        None => format!("<unnamed>{}", at(analysis.graph().node(node).origin)),
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
    } else if matches!(graph.node(result).op, Op::Result { .. }) {
        let node = graph.node(result);
        writeln!(
            out,
            "  result: result : {} {}",
            ty(analysis, result),
            at(node.origin)
        )
        .unwrap();
        dump_region(analysis, shape, "outcome[0]", region, 2, out);
        for (index, &returned) in graph.inputs(result)[1..].iter().enumerate() {
            dump_node(
                analysis,
                shape,
                &format!("outcome[{}]", index + 1),
                returned,
                2,
                out,
            );
        }
    } else {
        let node = graph.node(result);
        writeln!(
            out,
            "  result: copy : {} {}",
            ty(analysis, result),
            at(node.origin)
        )
        .unwrap();
        dump_region(analysis, shape, "value", region, 2, out);
    }
}

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
    // A named result prints as its `let` statement, and the tail reads it.
    let statements: Vec<NodeId> = region_ref
        .nodes()
        .filter(|&node| shape.region_of[node.index()] == Some(region))
        .filter(|&node| {
            let named = graph.node(node).name.is_some();
            let contextual = matches!(
                graph.node(node).op,
                Op::Then | Op::Else | Op::Entry | Op::Refine { .. } | Op::Exactly(_)
            );
            named
                || matches!(graph.node(node).op, Op::Assign { .. })
                || (node != result && !contextual && shape.users[node.index()] == 0)
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
                    at(graph.node(node).origin)
                )
                .unwrap();
                let initializer = graph.inputs(node)[0];
                dump_node(analysis, shape, "initializer", initializer, depth + 2, out);
            }
            // A named node that is not a copy is a binding recovery left without an initializer.
            (Some(_), _) => {
                let role = format!("let {}", named(analysis, node));
                dump_definition(analysis, shape, &role, node, depth + 1, out);
            }
            (None, Op::Assign { .. }) => {
                dump_definition(analysis, shape, "assignment", node, depth + 1, out)
            }
            (None, Op::Unused) => {
                let value = graph.inputs(node)[0];
                dump_node(analysis, shape, "discard", value, depth + 1, out);
            }
            (None, _) => dump_node(analysis, shape, "discard", node, depth + 1, out),
        }
    }
    dump_node(analysis, shape, "tail", result, depth + 1, out);
}

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
                    at(origin)
                ));
                node = graph.inputs(node)[0];
            }
            Op::Exactly(value) => {
                guards.push(format!("is {value}"));
                node = graph.inputs(node)[0];
            }
            Op::Assign { declaration } => {
                return (guards, declaration);
            }
            _ => return (guards, node),
        }
    }
}

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
    let guard = if guards.is_empty() {
        String::new()
    } else {
        format!(" [{}]", guards.join(", "))
    };
    if graph.node(definition).name.is_some() {
        writeln!(
            out,
            "{}{role}: read {}{guard} : {}",
            "  ".repeat(depth),
            named(analysis, definition),
            ty(analysis, node)
        )
        .unwrap();
        return;
    }
    dump_definition(
        analysis,
        shape,
        &format!("{role}{guard}"),
        definition,
        depth,
        out,
    );
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
        Op::Param { index, .. } => format!("param {index}"),
        Op::Unit => "unit".into(),
        Op::Unused => unreachable!("nothing reads a statement; dump_region discards its input"),
        Op::Hole => "hole".into(),
        Op::Copy { .. } => "copy".into(),
        Op::Assign { declaration } => format!("assign {}", named(analysis, *declaration)),
        Op::Phi { declaration, .. } => format!("phi {}", named(analysis, *declaration)),
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
        Op::Call(callee) => {
            let function = analysis.function(analysis.graph().callable(*callee).function);
            format!(
                "call {}{}",
                function
                    .name()
                    .map_or("<missing>", |name| analysis.text(name)),
                at(function.origin())
            )
        }
        Op::Return => "return".into(),
        Op::Sequence => "sequence".into(),
        Op::Observe { .. } => "observe".into(),
        Op::After => "after".into(),
        Op::Result { .. } => "result".into(),
    };
    writeln!(
        out,
        "{indent}{role}: {operation} : {} {}",
        ty(analysis, node),
        at(entry.origin)
    )
    .unwrap();
    let child = depth + 1;
    match &entry.op {
        Op::Int(_)
        | Op::Bool(_)
        | Op::Param { .. }
        | Op::Unit
        | Op::Entry
        | Op::Then
        | Op::Else => {}
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
        Op::Copy { .. } | Op::Assign { .. } => {
            dump_node(analysis, shape, "value", inputs[0], child, out)
        }
        Op::Phi { .. } => {
            dump_node(analysis, shape, "condition", inputs[0], child, out);
            for (role, &input) in [("then", &inputs[1]), ("else", &inputs[2])] {
                if matches!(graph.node(input).op, Op::Assign { .. } | Op::Phi { .. }) {
                    dump_definition(analysis, shape, role, input, child, out);
                } else {
                    dump_node(analysis, shape, role, input, child, out);
                }
            }
        }
        Op::Unused => unreachable!("nothing reads a statement; dump_region discards its input"),
        Op::Neg | Op::Not => dump_node(analysis, shape, "operand", inputs[0], child, out),
        Op::Binary(_) => {
            dump_node(analysis, shape, "lhs", inputs[0], child, out);
            dump_node(analysis, shape, "rhs", inputs[1], child, out);
        }
        Op::And { rhs, .. } | Op::Or { rhs, .. } => {
            dump_node(analysis, shape, "lhs", inputs[0], child, out);
            dump_region(analysis, shape, "rhs", *rhs, child, out);
        }
        Op::Refine { .. } | Op::Exactly(_) => unreachable!("a narrowed read reads its definition"),
        Op::Join { then, else_, .. } => {
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
        Op::Return => dump_node(analysis, shape, "payload", inputs[0], child, out),
        Op::Sequence => {
            dump_node(analysis, shape, "before", inputs[0], child, out);
            dump_node(analysis, shape, "value", inputs[1], child, out);
        }
        Op::Observe { then, else_ } => {
            dump_node(analysis, shape, "condition", inputs[0], child, out);
            if let Some(then) = then {
                dump_region(analysis, shape, "then control", *then, child, out);
            }
            if let Some(else_) = else_ {
                dump_region(analysis, shape, "else control", *else_, child, out);
            }
        }
        Op::After => {
            dump_node(analysis, shape, "control", inputs[0], child, out);
            dump_node(analysis, shape, "context", inputs[1], child, out);
        }
        Op::Result { .. } => {
            for (index, &input) in inputs.iter().enumerate() {
                dump_node(
                    analysis,
                    shape,
                    &format!("outcome[{index}]"),
                    input,
                    child,
                    out,
                );
            }
        }
    }
}

fn operator(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Cmp(CmpOp::Eq) => "==",
        BinaryOp::Cmp(CmpOp::Ne) => "!=",
        BinaryOp::Cmp(CmpOp::Lt) => "<",
        BinaryOp::Cmp(CmpOp::Le) => "<=",
        BinaryOp::Cmp(CmpOp::Gt) => ">",
        BinaryOp::Cmp(CmpOp::Ge) => ">=",
        BinaryOp::Arith(ArithOp::Add) => "+",
        BinaryOp::Arith(ArithOp::Sub) => "-",
        BinaryOp::Arith(ArithOp::Mul) => "*",
        BinaryOp::Arith(ArithOp::Div) => "/",
        BinaryOp::Arith(ArithOp::Rem) => "%",
    }
}

#[test]
fn rendering_is_deterministic() {
    let source = "fn f(x: int) -> int { let x = x + 1\n x }\nfn g() -> int = f(f(1))";
    assert_eq!(snapshot(source), snapshot(source));
    assert_eq!(run(source), run(source));
}
