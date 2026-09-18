use super::*;
use sumi_frontend::{DiagnosticCode, FileId, parse_source};

use crate::codes::*;

fn check(source: &str) -> Analysis {
    analyze(parse_source(FileId::new(17), source.into()).unwrap())
}

fn clean(source: &str) -> Analysis {
    let analysis = check(source);
    assert!(
        analysis.is_valid(),
        "syntax: {:?}\nsemantic: {:?}",
        analysis.parsed.diagnostics(),
        analysis.diagnostics
    );
    for function in &analysis.functions {
        invariant(&analysis, function);
    }
    graph_invariant(&analysis);
    analysis
}

fn codes(analysis: &Analysis) -> Vec<DiagnosticCode> {
    analysis.diagnostics().iter().map(|d| d.code).collect()
}

#[test]
fn body_ids_are_compact_and_zero_based() {
    assert_eq!(size_of::<ExprId>(), 4);
    assert_eq!(size_of::<Option<ExprId>>(), 4);
    assert_eq!(size_of::<LocalId>(), 4);
    assert_eq!(size_of::<Option<LocalId>>(), 4);
    for index in [0, 1, 8192, u32::MAX as usize - 1] {
        let id = ExprId::new(index);
        assert_eq!(id.index(), index);
        assert_eq!(format!("{id:?}"), format!("ExprId({index})"));
        assert_ne!(Some(id), None);
        let local = LocalId::new(index);
        assert_eq!(local.index(), index);
        assert_eq!(format!("{local:?}"), format!("LocalId({index})"));
        assert_ne!(Some(local), None);
    }
}

fn reversed_declarations_preserve_types(analysis: &Analysis) {
    use sumi_syntax::ast::{AstNode, SourceFile};
    if !analysis.parsed().diagnostics().is_empty() {
        return;
    }
    let tree = analysis.parsed().parse().tree();
    let mut declarations: Vec<_> = SourceFile::cast(tree, tree.root())
        .unwrap()
        .items(tree)
        .map(|item| {
            let range = tree.byte_range(item.node(), analysis.parsed().lexed());
            &analysis.parsed().source()[range.start().to_usize()..range.end().to_usize()]
        })
        .collect();
    declarations.reverse();
    let reversed = check(&declarations.join("\n"));
    assert!(reversed.parsed().diagnostics().is_empty());
    assert_eq!(analysis.functions.len(), reversed.functions.len());
    for (a, b) in analysis
        .functions
        .iter()
        .zip(reversed.functions.iter().rev())
    {
        assert_eq!(
            a.name().map(|name| analysis.text(name)),
            b.name().map(|name| reversed.text(name))
        );
        assert_eq!(
            a.signature().map(|s| (&s.params, s.result)),
            b.signature().map(|s| (&s.params, s.result))
        );
        assert_eq!(a.ranges(), b.ranges());
        assert_eq!(a.body().is_some(), b.body().is_some());
        if b.body().is_some() {
            invariant(&reversed, b);
        }
    }
}

/// The graph's shape: inputs precede their readers; a function's run is
/// its entry, a node per parameter, and its body region; regions nest
/// inside their function's run and each other; every op reads what its
/// kind takes; and an accepted file has a type on every value and no hole.
fn graph_invariant(analysis: &Analysis) {
    let graph = analysis.graph();
    let nodes = graph.nodes();
    for id in graph.node_ids() {
        let node = graph.node(id);
        let inputs = graph.inputs(id);
        for input in inputs {
            assert!(
                input.index() < id.index(),
                "{id:?} reads {input:?} before it is defined"
            );
        }
        let arity = match node.op {
            Op::Int(_) | Op::Bool(_) | Op::Param(_) | Op::Entry => Some(0),
            Op::Unit | Op::Copy | Op::Neg | Op::Not | Op::Exactly(_) => Some(1),
            Op::And { .. } | Op::Or { .. } | Op::Join { .. } => Some(1),
            Op::Binary(_) | Op::Refine { .. } | Op::Then | Op::Else => Some(2),
            Op::Hole | Op::Call(_) => None,
        };
        if let Some(arity) = arity {
            assert_eq!(inputs.len(), arity, "{id:?} {:?}", node.op);
        }
        // A context is read only by what it gates: another context, or the
        // unit a tail-less block holds while it is live.
        for &input in inputs {
            if matches!(graph.node(input).op, Op::Entry | Op::Then | Op::Else) {
                assert!(
                    matches!(node.op, Op::Then | Op::Else | Op::Unit),
                    "{id:?} reads a context"
                );
            }
        }
        if node.name.is_some() {
            assert!(matches!(node.op, Op::Param(_) | Op::Copy | Op::Hole));
        }
        if analysis.is_valid() {
            assert!(
                !matches!(node.op, Op::Hole),
                "an accepted file has no holes"
            );
            if !matches!(node.op, Op::Entry | Op::Then | Op::Else) {
                assert!(node.ty.is_some(), "{id:?} {:?} has no type", node.op);
            }
        }
    }
    let mut owner = vec![None; nodes.len()];
    for (index, function) in analysis.functions().iter().enumerate() {
        let mut run = function.nodes();
        assert_eq!(run.next(), Some(function.entry()));
        assert!(matches!(graph.node(function.entry()).op, Op::Entry));
        for (position, param) in function.param_nodes().enumerate() {
            assert_eq!(run.next(), Some(param));
            assert!(matches!(graph.node(param).op, Op::Param(i) if i as usize == position));
        }
        let region = graph.region(function.region());
        assert_eq!(region.context, function.entry());
        for node in region.nodes() {
            assert_eq!(run.next(), Some(node));
        }
        // After the body: nothing, or the copy a declared result holds
        // the body's value in.
        match run.next() {
            None => assert_eq!(function.result(), region.result()),
            Some(copy) => {
                assert_eq!(copy, function.result());
                assert!(matches!(graph.node(copy).op, Op::Copy));
                assert_eq!(graph.inputs(copy), [region.result()]);
                assert_eq!(run.next(), None);
            }
        }
        for node in function.nodes() {
            owner[node.index()] = Some(index);
        }
    }
    let mut spans: Vec<(usize, usize)> = Vec::new();
    for id in graph.region_ids() {
        let region = graph.region(id);
        let result = region.result().index();
        assert!(
            !matches!(
                graph.node(region.result()).op,
                Op::Entry | Op::Then | Op::Else
            ),
            "{id:?} results in a context"
        );
        let owner_of = |index: usize| owner[index].expect("every node belongs to a function");
        assert_eq!(owner_of(region.context.index()), owner_of(result));
        // An empty region is a read of something defined outside it.
        let Some(first) = region.nodes().next() else {
            continue;
        };
        let (start, end) = (first.index(), first.index() + region.nodes().len());
        assert!(region.context.index() < start);
        assert!(result < end, "{id:?} results in a later node");
        for &(s, e) in &spans {
            let disjoint = end <= s || e <= start;
            let nested = (s <= start && end <= e) || (start <= s && e <= end);
            assert!(disjoint || nested, "{id:?} overlaps another region");
        }
        spans.push((start, end));
    }
}

fn invariant(analysis: &Analysis, function: &Function) {
    let body = function.body().unwrap();
    let signature = function.signature().unwrap();
    assert_eq!(body.params().len(), signature.params.len());
    assert_eq!(body.expression(body.root()).ty, signature.result);
    let mut parents = vec![0; body.exprs.len()];
    let mut declarations = vec![0; body.locals.len()];
    for (&param, &ty) in body.params().iter().zip(&signature.params) {
        assert_eq!(body.local(param).ty, ty);
        assert!(std::ptr::eq(
            body.local(param),
            &body.locals()[param.index()]
        ));
        declarations[param.index()] += 1;
    }
    for (index, expr) in body.exprs.iter().enumerate() {
        let mut edges = Vec::new();
        match &expr.kind {
            ExprKind::Int(_) => assert_eq!(expr.ty, Ty::Int),
            ExprKind::Bool(_) => assert_eq!(expr.ty, Ty::Bool),
            ExprKind::Local(local) => assert_eq!(expr.ty, body.locals[local.index()].ty),
            ExprKind::Neg(child) => {
                assert_eq!(body.expression(*child).ty, Ty::Int);
                assert_eq!(expr.ty, Ty::Int);
                edges.push(*child);
            }
            ExprKind::Not(child) => {
                assert_eq!(body.expression(*child).ty, Ty::Bool);
                assert_eq!(expr.ty, Ty::Bool);
                edges.push(*child);
            }
            ExprKind::Binary { op, lhs, rhs } => {
                use BinaryOp::*;
                let (operand, result) = match op {
                    Add | Sub | Mul | Div | Rem => (Ty::Int, Ty::Int),
                    Lt | Le | Gt | Ge => (Ty::Int, Ty::Bool),
                    Eq | Ne => {
                        let ty = body.expression(*lhs).ty;
                        assert!(matches!(ty, Ty::Int | Ty::Bool));
                        (ty, Ty::Bool)
                    }
                };
                assert_eq!(body.expression(*lhs).ty, operand);
                assert_eq!(body.expression(*rhs).ty, operand);
                assert_eq!(expr.ty, result);
                edges.extend([*lhs, *rhs]);
            }
            ExprKind::And { lhs, rhs } | ExprKind::Or { lhs, rhs } => {
                assert_eq!(body.expression(*lhs).ty, Ty::Bool);
                assert_eq!(body.expression(*rhs).ty, Ty::Bool);
                assert_eq!(expr.ty, Ty::Bool);
                edges.extend([*lhs, *rhs]);
            }
            ExprKind::Call { function, args, .. } => {
                let args = body.args(*args);
                let signature = analysis.function(*function).signature().unwrap();
                assert_eq!(expr.ty, signature.result);
                assert_eq!(args.len(), signature.params.len());
                for (&arg, &ty) in args.iter().zip(&signature.params) {
                    assert_eq!(body.expression(arg).ty, ty);
                }
                edges.extend_from_slice(args);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                assert_eq!(body.expression(*condition).ty, Ty::Bool);
                assert_eq!(body.expression(*then_branch).ty, expr.ty);
                assert_eq!(
                    else_branch.map_or(Ty::Unit, |id| body.expression(id).ty),
                    expr.ty
                );
                edges.extend([*condition, *then_branch]);
                edges.extend(else_branch);
            }
            ExprKind::Block { statements, tail } => {
                for statement in body.statements(*statements) {
                    edges.push(match statement.kind {
                        StatementKind::Let { local, initializer } => {
                            assert!(std::ptr::eq(
                                body.local(local),
                                &body.locals()[local.index()]
                            ));
                            declarations[local.index()] += 1;
                            assert_eq!(body.local(local).ty, body.expression(initializer).ty);
                            initializer
                        }
                        StatementKind::Eval(id) => id,
                    });
                }
                edges.extend(tail);
                assert_eq!(tail.map_or(Ty::Unit, |id| body.expression(id).ty), expr.ty);
            }
        }
        for edge in edges {
            assert!(std::ptr::eq(
                body.expression(edge),
                &body.expressions()[edge.index()]
            ));
            assert!(edge.index() < index);
            parents[edge.index()] += 1;
        }
    }
    assert!(std::ptr::eq(
        body.expression(body.root()),
        &body.expressions()[body.root().index()]
    ));
    for (index, count) in parents.into_iter().enumerate() {
        assert_eq!(count, usize::from(index != body.root().index()));
    }
    assert!(declarations.into_iter().all(|count| count == 1));
}

#[test]
fn scalar_bodies_and_forward_recursive_calls() {
    let analysis = clean(
        "fn answer() -> int = (twice)(21)\nfn twice(x: int) -> int {\n let y = x * 2\n y\n}\nfn spin(n: int) -> unit = if n > 0 { spin(n - 1) }\n",
    );
    let twice = analysis.functions[1].body().unwrap();
    assert_eq!(twice.exprs.len(), 5);
    assert_eq!(twice.locals.len(), 2);
    assert_eq!(twice.params, [LocalId::new(0)]);
    assert!(matches!(twice.exprs[0].kind, ExprKind::Local(id) if id.index() == 0));
    assert!(matches!(twice.exprs[3].kind, ExprKind::Local(id) if id.index() == 1));
    let answer = analysis.functions[0].body().unwrap();
    assert!(matches!(
        answer.expression(answer.root).kind,
        ExprKind::Call { function, .. } if function == FunctionId::new(1)
    ));
    clean(
        "fn start(n: int) -> bool = even(n)\nfn even(n: int) -> bool = if n == 0 { true } else { odd(n - 1) }\nfn odd(n: int) -> bool = if n == 0 { false } else { even(n - 1) }\n",
    );
}

#[test]
fn lexical_scopes_and_sequential_shadowing() {
    let a = clean(
        "fn shadow(x: int) -> int {\n let x = x + 1\n {\n let x = x * 2\n _ = x\n }\n x\n}\n",
    );
    let body = a.functions[0].body().unwrap();
    let reads: Vec<_> = body
        .exprs
        .iter()
        .filter_map(|e| match e.kind {
            ExprKind::Local(id) => Some(id.index()),
            _ => None,
        })
        .collect();
    assert_eq!(reads, [0, 1, 2, 1]);
    let a = check("fn f() -> int = 1\nfn g() -> int {\n let f = 2\n f()\n}\n");
    assert_eq!(codes(&a), [NOT_CALLABLE]);
    assert_eq!(a.diagnostics[0].secondary.len(), 1);
}

#[test]
fn lazy_structure_and_unit_policy() {
    let a = clean(
        "fn safe() -> bool = false && (1 / 0 == 0)\nfn choose() -> int = if true { 7 } else { 1 / 0 }\nfn ignore() {\n _ = choose()\n}\nfn maybe(b: bool) = if b { _ = choose() }\nfn either() -> bool = true || false\n",
    );
    let body = a.functions[0].body().unwrap();
    assert!(matches!(
        body.expression(body.root).kind,
        ExprKind::And { .. }
    ));
    for source in [
        "fn f() { 1 }",
        "fn f() = if true { 7 }",
        "fn f() -> bool = {} == {}",
        "fn f() -> int = if 1 { 2 } else { false }",
    ] {
        let a = check(source);
        assert!(!a.is_valid(), "{source}");
        assert!(codes(&a).contains(&TYPE_MISMATCH), "{source}");
    }
    let a =
        check("fn f() -> bool = true || missing\nfn g() -> int = if true { 1 } else { absent }\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME, UNKNOWN_NAME]);
}

#[test]
fn mismatch_labels_distinguish_branches_from_declarations() {
    for (source, expected) in [
        (
            "fn f() -> int = if true { 1 } else { false }",
            &["int here", "bool here"][..],
        ),
        ("fn f() -> bool = 1", &["declared here"]),
        ("fn f() { let x: bool = 1 }", &["declared here"]),
    ] {
        let a = check(source);
        assert_eq!(codes(&a), [TYPE_MISMATCH]);
        let labels: Vec<_> = a.diagnostics[0]
            .secondary
            .iter()
            .map(|label| label.message.as_deref().unwrap())
            .collect();
        assert_eq!(labels, expected, "{source}");
    }
}

/// A disagreement between branches is reported once, at the `if`, and
/// leaves the `if` undetermined: nothing that takes its type is held to a
/// type it never had, while the branches keep their own.
#[test]
fn disagreeing_branches_are_undetermined_not_the_first_branch() {
    for result in ["bool", "int"] {
        let a = check(&format!(
            "fn f(c: bool) -> {result} = {{ let x = if c {{ 1 }} else {{ true }}\n x }}"
        ));
        assert_eq!(codes(&a), [TYPE_MISMATCH], "{result}");
        assert_eq!(
            a.diagnostics[0].message.as_ref(),
            "if branches are int and bool"
        );
    }
    let a = check(
        "fn f() -> bool = { let a = 1\n let b = true\n _ = if a == 1 { a } else { b }\n !a }",
    );
    assert_eq!(codes(&a), [TYPE_MISMATCH, TYPE_MISMATCH]);
    assert_eq!(
        a.diagnostics[1].message.as_ref(),
        "expected bool, found int"
    );
}

#[test]
fn literals_of_any_size_fold_a_leading_minus() {
    for (expr, value) in [
        ("9223372036854775807", "9223372036854775807"),
        ("-9223372036854775808", "-9223372036854775808"),
        ("-((9223372036854775808))", "-9223372036854775808"),
        ("9223372036854775808", "9223372036854775808"),
        ("-9223372036854775809", "-9223372036854775809"),
        (
            "1234567890123456789012345678901234567890",
            "1234567890123456789012345678901234567890",
        ),
        (
            "-1234567890123456789012345678901234567890",
            "-1234567890123456789012345678901234567890",
        ),
    ] {
        let a = clean(&format!("fn f() -> int = {expr}"));
        let body = a.functions[0].body().unwrap();
        assert_eq!(body.exprs.len(), 1, "{expr}");
        let ExprKind::Int(literal) = &body.exprs[0].kind else {
            panic!("{expr} is one literal");
        };
        assert_eq!(literal, &value.parse::<Int>().unwrap(), "{expr}");
    }
    // Only a `-` directly on the literal folds; the rest is a negation.
    for expr in ["--9223372036854775808", "-(9223372036854775808 + 0)"] {
        let a = clean(&format!("fn f() -> int = {expr}"));
        let body = a.functions[0].body().unwrap();
        assert!(
            matches!(body.expression(body.root()).kind, ExprKind::Neg(_)),
            "{expr}"
        );
    }
    for expr in ["01", "1_000", "1u32"] {
        let a = check(&format!("fn f() -> int = {expr}"));
        assert!(!a.is_valid());
        assert!(a.functions[0].body().is_none());
        assert!(a.diagnostics.is_empty());
    }
}

#[test]
fn bad_calls_check_arguments_before_poisoning_binding() {
    let a = check(
        "fn probe() {\n let x = 1\n let x = missing(\n {\n let x = x + 1\n x + true\n },\n x + false\n )\n _ = x\n}\n",
    );
    assert!(a.parsed.diagnostics().is_empty());
    assert_eq!(codes(&a), [UNKNOWN_NAME, TYPE_MISMATCH, TYPE_MISMATCH]);
    assert!(a.functions[0].body().is_none());
    let a = check("fn f(x: int, y: bool) {}\nfn g() { _ = f(true, 1, absent) }\n");
    assert_eq!(
        codes(&a),
        [ARITY, TYPE_MISMATCH, TYPE_MISMATCH, UNKNOWN_NAME]
    );
}

#[test]
fn expression_results_stay_body_local_across_failed_bodies() {
    let a = check(
        "fn first() = (23 + 7)\nfn failed() = (missing)\nfn flag() = ((true))\nfn last() = -((17))",
    );
    assert_eq!(codes(&a), [UNKNOWN_NAME]);
    assert!(a.functions[1].body().is_none());
    for index in [0, 2, 3] {
        invariant(&a, &a.functions[index]);
    }
    let first = a.functions[0].body().unwrap();
    assert_eq!(first.exprs.len(), 3);
    assert!(matches!(&first.exprs[0].kind, ExprKind::Int(n) if *n == Int::from(23)));
    assert!(matches!(&first.exprs[1].kind, ExprKind::Int(n) if *n == Int::from(7)));
    let flag = a.functions[2].body().unwrap();
    assert_eq!(flag.exprs.len(), 1);
    assert!(matches!(
        flag.expression(flag.root()).kind,
        ExprKind::Bool(true)
    ));
    let last = a.functions[3].body().unwrap();
    assert_eq!(last.exprs.len(), 1);
    assert!(matches!(
        &last.expression(last.root()).kind,
        ExprKind::Int(n) if *n == Int::from(-17)
    ));
    reversed_declarations_preserve_types(&a);
}

/// The offset an argument carries is read through a chain of `let`s of
/// any length, since the walk keeps its own stack.
#[test]
fn a_measure_is_read_through_any_depth_of_lets() {
    use std::fmt::Write as _;
    let mut source = String::from("fn f(n: int) -> int {\n    let a0 = n - 1\n");
    for i in 1..400 {
        writeln!(source, "    let a{i} = a{} - 0", i - 1).unwrap();
    }
    source.push_str("    if a399 < 0 { 0 } else { f(a399) }\n}\nfn main() -> int = f(5)\n");
    let analysis = check(&source);
    assert!(
        analysis.diagnostics().is_empty(),
        "{:?}",
        analysis.diagnostics()
    );
    assert_eq!(analysis.depth_bound(FunctionId::new(1)), Some(7));
}

#[test]
fn call_arguments_keep_source_order() {
    let a = clean("fn select(a: int, b: int, c: int) -> int = b\nfn caller() = select(11, 29, 7)");
    let body = a.functions()[1].body().unwrap();
    let ExprKind::Call { args, .. } = &body.expression(body.root()).kind else {
        panic!("expected a call");
    };
    let args = body.args(*args);
    for (index, &value) in [11, 29, 7].iter().enumerate() {
        // Both evaluation order and the published argument positions matter.
        let value = Int::from(value);
        assert!(matches!(&body.exprs[index].kind, ExprKind::Int(n) if *n == value));
        assert!(matches!(&body.expression(args[index]).kind, ExprKind::Int(n) if *n == value));
    }
    assert_eq!(args.len(), 3);
}

#[test]
fn call_requirements_replay_in_argument_order() {
    let source = "fn unknown() = unknown()\nfn take(a: int, b: bool) {}\nfn caller() = { let x = unknown()\n take(x, (x)) }";
    let a = check(source);
    assert!(a.parsed.diagnostics().is_empty());
    let mismatches: Vec<_> = a
        .diagnostics()
        .iter()
        .filter(|d| d.code == TYPE_MISMATCH)
        .collect();
    assert_eq!(mismatches.len(), 1);
    assert_eq!(mismatches[0].message.as_ref(), "expected bool, found int");
    assert_eq!(
        mismatches[0].primary.location.start().to_usize(),
        source.rfind("(x)").unwrap()
    );

    let a = check("fn take(a: int, b: bool) {}\nfn caller() { take(missing, 23) }");
    assert_eq!(codes(&a), [UNKNOWN_NAME, TYPE_MISMATCH]);
}

#[test]
fn signatures_do_not_invent_missing_types_or_resolve_ambiguity() {
    for source in [
        "fn f(a:) -> { let x: = 1 }",
        "fn f() -> = 1",
        "fn f() == 1",
        "fn f() = = 1",
        "fn f(a: int, ) ->",
        "fn f(a) {}",
    ] {
        let a = check(source);
        assert!(!a.is_valid(), "{source}");
        assert!(a.functions[0].signature().is_none(), "{source}");
    }
    let a = check("fn f(x: mystery) {}\nfn g() { _ = f(unknown, 1) }\n");
    assert_eq!(codes(&a), [UNKNOWN_TYPE, UNKNOWN_NAME]);
    assert!(a.functions.iter().all(|f| f.body().is_none()));
    let a = check("fn f() {}\nfn f() {}\nfn g() = f()\n");
    assert_eq!(codes(&a), [DUPLICATE_NAME]);
    assert!(a.functions[2].body().is_none());
    let a = check("fn f(x: int, x: bool) {\n _ = !x\n _ = -x\n}\nfn g() = f(1, true)\n");
    assert_eq!(codes(&a), [DUPLICATE_NAME]);
    assert!(a.functions[0].signature().is_some());
    assert!(a.functions[0].body().is_none());
    assert!(a.functions[1].body().is_some());
}

#[test]
fn token_gaps_ignore_trivia_without_losing_semantics() {
    let a = clean(
        "fn inferred() // header\n = 7\nfn unit() // header\n {}\nfn local() = { let\tvalue = 3\n -value }\nfn boolean() = !false",
    );
    let results: Vec<_> = a
        .functions()
        .iter()
        .map(|f| f.signature().unwrap().result)
        .collect();
    assert_eq!(results, [Ty::Int, Ty::Unit, Ty::Int, Ty::Bool]);
    let body = a.functions()[2].body().unwrap();
    assert!(
        body.exprs
            .iter()
            .any(|e| matches!(e.kind, ExprKind::Neg(_)))
    );
    let body = a.functions()[3].body().unwrap();
    assert!(matches!(
        body.expression(body.root()).kind,
        ExprKind::Not(_)
    ));

    let a = check("fn f() = { let\tmut\tvalue = 3\n value }");
    assert!(a.parsed().diagnostics().is_empty());
    assert_eq!(codes(&a), [UNSUPPORTED]);
    assert!(a.functions()[0].body().is_none());
}

#[test]
fn invalid_parameters_do_not_hide_independent_result_errors() {
    for (parameter, expected) in [
        ("x: mystery", &[UNKNOWN_TYPE, TYPE_MISMATCH][..]),
        // Missing annotations are already diagnosed by the parser.
        ("x", &[TYPE_MISMATCH][..]),
    ] {
        let a = check(&format!(
            "fn broken({parameter}) -> int = true\nfn independent() -> int = 42\n"
        ));
        assert!(!a.is_valid());
        assert_eq!(codes(&a), expected);
        assert!(a.functions[0].signature().is_none());
        assert!(a.functions[0].body().is_none());
        invariant(&a, &a.functions[1]);
    }
}

#[test]
fn damaged_and_unsupported_declarations_hide_old_bindings() {
    for binding in [
        "let x =",
        "let x: = 1",
        "let mut x = true",
        "let x: mystery = true",
        "let x = absent",
    ] {
        let a = check(&format!(
            "fn f() {{\n let x = true\n {binding}\n _ = x + 1\n _ = missing\n}}\nfn intact() -> int = 3\n"
        ));
        assert!(!a.is_valid(), "{binding}");
        assert!(
            !codes(&a).contains(&TYPE_MISMATCH),
            "{binding}: {:?}",
            a.diagnostics
        );
        assert!(a.diagnostics.last().unwrap().message.contains("missing"));
        assert!(a.functions[0].body().is_none());
        assert!(a.functions[1].body().is_some());
    }
    for source in [
        "fn f() { let = x }",
        "fn f() { let _ = 1 }",
        "fn f() -> int { 1 ; }",
        "fn f() -> int { 1",
        "fn f()",
        "fn f() {\n let x = 1\n _ = missing\n",
    ] {
        let a = check(source);
        assert!(!a.is_valid(), "{source}");
        assert!(a.functions[0].body().is_none(), "{source}");
    }
    let a = check("fn f() {\n _ = missing\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME]);
    for source in [
        "fn f() { return }",
        "fn f() { let x = 1\n x = 2 }",
        "fn f() { let g = fn() = 1 }",
        "fn f() = \"hello\"",
        "fn f() = (if true { 1 } else { 2 })()",
    ] {
        let a = check(source);
        assert!(a.parsed.diagnostics().is_empty(), "{source}");
        assert!(!a.is_valid());
        assert!(codes(&a).contains(&UNSUPPORTED), "{source}");
    }
}

#[test]
fn syntax_diagnostics_are_preserved_and_always_reject() {
    for source in ["fn f() -> int = 01", "fn f() {}\r"] {
        let parsed = parse_source(FileId::new(17), source.into()).unwrap();
        assert!(!parsed.diagnostics().is_empty());
        let tree = parsed.parse().tree();
        assert!(!tree.has_error(tree.root()), "{source}");
        let before = parsed.diagnostics().to_vec();
        let a = analyze(parsed);
        assert!(!a.is_valid());
        assert_eq!(a.parsed.diagnostics(), before);
    }
}

#[test]
fn unused_values_are_semantic_errors_without_complete_bodies() {
    let a = check("fn f() -> int { 1\n 2 }");
    assert!(a.parsed.diagnostics().is_empty());
    assert_eq!(codes(&a), [UNUSED_VALUE]);
    assert!(!a.is_valid());
    assert!(a.functions[0].body().is_none());
    clean("fn f() -> int { let u = {}\n u\n _ = 1\n 2 }");

    // The two unused values share an inferred type and produce distinct errors.
    let a = check("fn f() = { let x = value()\n x\n x\n 0 }\nfn value() = 3");
    assert_eq!(codes(&a), [UNUSED_VALUE, UNUSED_VALUE]);
    assert!(a.diagnostics[0].primary.location.start() < a.diagnostics[1].primary.location.start());
    assert!(a.functions[0].body().is_none());
}

#[test]
fn blocks_preserve_statement_order_and_only_the_last_child_is_a_tail() {
    let a = clean("fn f() = { let x = 11\n _ = 29\n {}\n 7 }\nfn g() = { _ = 5 }\nfn h() = {}");
    let body = a.functions[0].body().unwrap();
    let ExprKind::Block { statements, tail } = &body.expression(body.root()).kind else {
        panic!("expected a block");
    };
    let texts: Vec<_> = body
        .statements(*statements)
        .iter()
        .map(|statement| {
            let range = statement.origin.range();
            &a.parsed.source()[range.start().to_usize()..range.end().to_usize()]
        })
        .collect();
    assert_eq!(texts, ["let x = 11", "_ = 29", "{}"]);
    assert!(matches!(
        &body.expression(tail.unwrap()).kind,
        ExprKind::Int(n) if *n == Int::from(7)
    ));
    for (function, count) in [(1, 1), (2, 0)] {
        let body = a.functions[function].body().unwrap();
        let ExprKind::Block { statements, tail } = &body.expression(body.root()).kind else {
            panic!("expected a block");
        };
        assert_eq!(body.statements(*statements).len(), count);
        assert!(tail.is_none());
    }
}

#[test]
fn nested_blocks_consume_only_their_own_statements() {
    let source = "fn f() = { let a = 11\n let b = { _ = a\n 29 }\n { _ = b }\n _ = 7\n b }";
    let a = clean(source);
    let body = a.functions[0].body().unwrap();
    let blocks: Vec<Vec<&str>> = body
        .exprs
        .iter()
        .filter_map(|expr| {
            let ExprKind::Block { statements, .. } = &expr.kind else {
                return None;
            };
            Some(
                body.statements(*statements)
                    .iter()
                    .map(|statement| {
                        let range = statement.origin.range();
                        &source[range.start().to_usize()..range.end().to_usize()]
                    })
                    .collect(),
            )
        })
        .collect();
    assert_eq!(
        blocks,
        [
            vec!["_ = a"],
            vec!["_ = b"],
            vec!["let a = 11", "let b = { _ = a\n 29 }", "{ _ = b }", "_ = 7"],
        ]
    );

    // A failed inner tail must still drain the inner statement, and must
    // not disturb checking the rest of the outer block or the next body.
    let a = check(&format!(
        "{}\nfn g() = {{ _ = 5\n 3 }}",
        source.replace("29", "missing")
    ));
    assert_eq!(codes(&a), [UNKNOWN_NAME]);
    assert!(a.functions[0].body().is_none());
    invariant(&a, &a.functions[1]);
}

#[test]
fn source_origins_are_utf8_byte_ranges() {
    let a = clean("// café\nfn f(e: int) -> int = e + 1");
    let body = a.functions[0].body().unwrap();
    let origin = body.exprs[0].origin;
    assert_eq!(origin.file(), FileId::new(17));
    assert_eq!(
        &a.parsed.source()[origin.range().start().to_usize()..origin.range().end().to_usize()],
        "e"
    );
    let a = check("// café\nfn f() -> int = absent");
    assert_eq!(
        a.diagnostics[0].primary.location.start().to_usize(),
        "// café\nfn f() -> int = ".len()
    );
}

#[test]
fn duplicate_functions_keep_the_first_origin_and_poison_calls() {
    let a = check("fn K() = 1\nfn K() = true\nfn caller() = K()");
    assert!(a.parsed().diagnostics().is_empty());
    assert_eq!(codes(&a), [DUPLICATE_NAME]);
    for diagnostic in a.diagnostics() {
        assert_eq!(diagnostic.secondary.len(), 1);
        let origin = diagnostic.secondary[0].location.span().range();
        assert_eq!(origin.start().to_usize(), 3);
        assert_eq!(origin.end().to_usize(), 4);
    }
    assert!(a.functions()[2].signature().is_none());
    assert!(a.functions()[2].body().is_none());
}

#[test]
fn long_chains_are_stack_safe_even_when_rejected() {
    let chain = std::iter::repeat_n("1", 20_000)
        .collect::<Vec<_>>()
        .join(" + ");
    let a = clean(&format!("fn f() -> int = {chain}"));
    assert_eq!(a.functions[0].body().unwrap().exprs.len(), 39_999);
    let a = check(&format!(
        "fn f() -> int = {chain} + true + missing\nfn g() -> int = absent\n"
    ));
    assert_eq!(codes(&a), [TYPE_MISMATCH, UNKNOWN_NAME, UNKNOWN_NAME]);
}

#[test]
fn scalar_operator_type_matrix() {
    let values = [("1", "int"), ("true", "bool"), ("{}", "unit")];
    for (op, eager) in [
        ("+", Some(BinaryOp::Add)),
        ("-", Some(BinaryOp::Sub)),
        ("*", Some(BinaryOp::Mul)),
        ("/", Some(BinaryOp::Div)),
        ("%", Some(BinaryOp::Rem)),
        ("<", Some(BinaryOp::Lt)),
        ("<=", Some(BinaryOp::Le)),
        (">", Some(BinaryOp::Gt)),
        (">=", Some(BinaryOp::Ge)),
        ("==", Some(BinaryOp::Eq)),
        ("!=", Some(BinaryOp::Ne)),
        ("&&", None),
        ("||", None),
    ] {
        for (lhs, left_ty) in values {
            for (rhs, right_ty) in values {
                let (accepted, result) = match op {
                    "+" | "-" | "*" | "/" | "%" => (left_ty == "int" && right_ty == "int", "int"),
                    "<" | "<=" | ">" | ">=" => (left_ty == "int" && right_ty == "int", "bool"),
                    "==" | "!=" => (left_ty == right_ty && left_ty != "unit", "bool"),
                    _ => (left_ty == "bool" && right_ty == "bool", "bool"),
                };
                let source = format!("fn f() -> {result} = {lhs} {op} {rhs}");
                let a = check(&source);
                assert!(a.parsed.diagnostics().is_empty(), "{source}");
                assert_eq!(a.is_valid(), accepted, "{source}");
                if accepted {
                    let body = a.functions[0].body().unwrap();
                    invariant(&a, &a.functions[0]);
                    match body.expression(body.root()).kind {
                        ExprKind::Binary { op, .. } => assert_eq!(Some(op), eager),
                        ExprKind::And { .. } => assert_eq!(op, "&&"),
                        ExprKind::Or { .. } => assert_eq!(op, "||"),
                        _ => panic!("expected a binary operation: {source}"),
                    }
                } else {
                    assert!(codes(&a).contains(&TYPE_MISMATCH), "{source}");
                }
            }
        }
    }
    clean(
        "fn f(x: int) -> int = -x\nfn g(x: bool) -> bool = !x\nfn h() -> bool = true != false\nfn u(x: unit) -> unit { let y: unit = x\n y }\n",
    );
    for source in ["fn f() -> int = -true", "fn f() -> bool = !1"] {
        assert_eq!(codes(&check(source)), [TYPE_MISMATCH]);
    }
    clean("fn f(x: int) -> bool = x // comparison\n <= 1\n");
}

#[test]
fn binary_requirements_survive_a_failed_operand() {
    for expression in [
        "missing + true",
        "missing < false",
        "1 && missing",
        "missing == {}",
    ] {
        let a = check(&format!("fn f() {{ _ = {expression} }}"));
        let mut actual = codes(&a);
        actual.sort_unstable_by_key(|code| code.name());
        assert_eq!(actual, [TYPE_MISMATCH, UNKNOWN_NAME], "{expression}");
        assert!(a.functions[0].body().is_none());
    }
}

#[test]
fn recovery_does_not_expose_functions_or_leak_argument_scopes() {
    let a = check("fn f() -> int = 1\nfn g() {\n let f =\n _ = f()\n _ = absent\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME]);
    assert!(a.diagnostics[0].message.contains("absent"));
    let a = check("fn f() {\n _ = missing({ let x = 1\n x }, x)\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME, UNKNOWN_NAME]);
    let a = check("fn f() {\n let x = absent\n let x = true\n _ = x + 1\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME, TYPE_MISMATCH]);
    let a = check("fn f() -> int {\n _ = absent\n 1\n}\n");
    assert!(a.functions[0].body().is_none());
    clean("fn f() -> int {\n let x =\n 1\n x\n}\n");
}

#[test]
fn existing_corpus_never_panics_or_silently_rejects() {
    let mut directories = vec![std::path::PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/corpus"
    ))];
    let mut count = 0;
    while let Some(directory) = directories.pop() {
        for entry in std::fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                directories.push(path);
            } else if path.file_name().unwrap() == "case.sumi" {
                let a = check(&std::fs::read_to_string(&path).unwrap());
                reversed_declarations_preserve_types(&a);
                graph_invariant(&a);
                for function in &a.functions {
                    if function.body().is_some() {
                        invariant(&a, function);
                    }
                }
                count += 1;
            }
        }
    }
    assert!(count > 100);
}

#[test]
fn inferred_results_and_recursive_constraints() {
    for (source, expected) in [
        ("fn value() = 1", vec![Ty::Int]),
        ("fn value() -> int = 1", vec![Ty::Int]),
        ("fn value() = { 1 }", vec![Ty::Int]),
        ("fn value() = {}", vec![Ty::Unit]),
        ("fn f() = g()\nfn g() = 1", vec![Ty::Int, Ty::Int]),
        ("fn f() = if true { 1 } else { f() }", vec![Ty::Int]),
        ("fn f() = if false { f() } else { 1 }", vec![Ty::Int]),
        // A type flows through a cycle of calls even when the call that
        // closes the cycle can never run.
        (
            "fn f() -> int = if true { 1 } else { g() }\nfn g() = f()",
            vec![Ty::Int, Ty::Int],
        ),
        (
            "fn a() = { if false { _ = b() }\n1 }\nfn b() = { _ = a()\ntrue }",
            vec![Ty::Int, Ty::Bool],
        ),
        (
            "fn f() = { let x = g()\n let x = x + 1\n x }\nfn g() = 1",
            vec![Ty::Int, Ty::Int],
        ),
        ("fn K() = 1\nfn f() = K()", vec![Ty::Int, Ty::Int]),
    ] {
        let a = clean(source);
        let actual: Vec<_> = a
            .functions
            .iter()
            .map(|f| f.signature().unwrap().result)
            .collect();
        assert_eq!(actual, expected, "{source}");
        reversed_declarations_preserve_types(&a);
    }
}

#[test]
fn callers_cannot_solve_providers_or_publish_incomplete_calls() {
    let a = check(
        "fn spin() = spin()\nfn consumer() -> int = spin()\nfn grounded() = spin() + 1\nfn recovered() = grounded()\n",
    );
    // `spin` is both unresolvable and unbounded, each reported once.
    assert_eq!(codes(&a), [CANNOT_INFER, UNBOUNDED_RECURSION]);
    assert!(a.functions[0].signature().is_none());
    for function in &a.functions[1..] {
        assert_eq!(function.signature().unwrap().result, Ty::Int);
    }
    assert!(a.functions[..3].iter().all(|f| f.body().is_none()));
    invariant(&a, &a.functions[3]);
    let a = check("fn spin(x: int) = spin(x)\nfn caller() = spin(true, missing)\nfn intact() = 42");
    assert_eq!(
        codes(&a),
        [
            CANNOT_INFER,
            UNBOUNDED_RECURSION,
            ARITY,
            TYPE_MISMATCH,
            UNKNOWN_NAME
        ]
    );
    invariant(&a, &a.functions[2]);
}

#[test]
fn inferred_conflicts_and_deferred_scalar_rules() {
    for definitions in [
        vec![
            "fn a() = if true { 1 } else { b() }",
            "fn b() = if true { true } else { a() }",
        ],
        vec![
            "fn a() = b()",
            "fn b() = if true { integer() } else { boolean() }",
            "fn integer() = 1",
            "fn boolean() = true",
        ],
    ] {
        for reverse in [false, true] {
            let mut definitions = definitions.clone();
            if reverse {
                definitions.reverse();
            }
            let a = check(&definitions.join("\n"));
            assert!(!a.is_valid());
            for function in &a.functions {
                if matches!(function.name().map(|name| a.text(name)), Some("a" | "b")) {
                    assert!(function.signature().is_none());
                    assert!(function.body().is_none());
                } else {
                    invariant(&a, function);
                }
            }
        }
    }
    for (source, expected) in [
        ("fn f() { g()\n _ = 1 }\nfn g() = 1", UNUSED_VALUE),
        ("fn f() = g() == g()\nfn g() = {}", TYPE_MISMATCH),
        ("fn f() -> bool = g()\nfn g() = 1", TYPE_MISMATCH),
        (
            "fn f() = if true { g() } else { false }\nfn g() = 1",
            TYPE_MISMATCH,
        ),
        (
            "fn f() = { let x: bool = g()\n x }\nfn g() = 1",
            TYPE_MISMATCH,
        ),
    ] {
        let a = check(source);
        assert_eq!(codes(&a), [expected], "{source}");
        assert!(a.functions[0].body().is_none());
        invariant(&a, &a.functions[1]);
    }
    clean("fn f() { g()\n _ = 1 }\nfn g() = {}");
}

#[test]
fn inference_preserves_resolution_poison_and_annotation_boundaries() {
    for (source, expected) in [
        ("fn f() = 1\nfn g() = { let f = true\n f() }", NOT_CALLABLE),
        (
            "fn f() = 1\nfn F() = 2\nfn F() = 3\nfn g() = F()",
            DUPLICATE_NAME,
        ),
        (
            "fn f() = 1\nfn g() = { let f = absent\n f() }",
            UNKNOWN_NAME,
        ),
        ("fn f() = 1\nfn g() = { let mut f = 1\n f() }", UNSUPPORTED),
    ] {
        let a = check(source);
        assert_eq!(codes(&a), [expected]);
        assert!(a.functions.last().unwrap().body().is_none());
        invariant(&a, &a.functions[0]);
    }
    for declaration in [
        "fn f() -> = 1",
        "fn f() -> mystery = 1",
        "fn f(x) = 1",
        "fn f() -> = { 1 }",
    ] {
        let a = check(declaration);
        assert!(a.functions[0].signature().is_none(), "{declaration}");
        assert!(a.functions[0].body().is_none());
        assert!(!codes(&a).contains(&CANNOT_INFER));
    }
}

#[test]
fn large_definition_chains_and_cycles_are_stack_safe() {
    use std::fmt::Write;
    const COUNT: usize = 10_000;
    // A chain of calls that is grounded, grounded through a cycle, an
    // unresolved cycle, or a cycle that claims two types at its ends.
    for (cycle, grounded, conflict) in [
        (false, true, false),
        (true, true, false),
        (true, false, false),
        (true, false, true),
    ] {
        for reverse in [false, true] {
            let mut definitions = Vec::new();
            for i in 0..COUNT - 1 {
                let body = if conflict && i == 0 {
                    "if true { true } else { f1() }".to_owned()
                } else {
                    format!("f{}()", i + 1)
                };
                definitions.push(format!("fn f{i}() = {body}"));
            }
            let mut last = format!("fn f{}() = ", COUNT - 1);
            last.push_str(match (cycle, grounded, conflict) {
                (false, _, _) => "1",
                (true, true, _) | (true, false, true) => "if true { 1 } else { f0() }",
                (true, false, false) => "f0()",
            });
            definitions.push(last);
            if reverse {
                definitions.reverse();
            }
            let mut source = String::new();
            for declaration in definitions {
                writeln!(source, "{declaration}").unwrap();
            }
            let a = check(&source);
            assert_eq!(a.is_valid(), grounded);
            if grounded {
                for function in &a.functions {
                    invariant(&a, function);
                }
            } else {
                // A conflict is reported once at each end that claims a
                // type; every function between inherits it silently. A live
                // cycle with no ground is also a recursion with no measure,
                // reported once.
                let recursion = usize::from(!conflict);
                assert_eq!(
                    a.diagnostics.len(),
                    if conflict { 2 } else { COUNT + recursion }
                );
                assert_eq!(
                    a.diagnostics
                        .iter()
                        .filter(|d| d.code == UNBOUNDED_RECURSION)
                        .count(),
                    recursion
                );
                assert!(
                    a.diagnostics
                        .iter()
                        .all(|d| d.code == CANNOT_INFER || d.code == UNBOUNDED_RECURSION)
                );
                assert!(
                    a.functions
                        .iter()
                        .all(|f| f.signature().is_none() && f.body().is_none())
                );
            }
        }
    }
}

proptest::proptest! {
    #[test]
    fn declaration_order_does_not_choose_inferred_signatures(
        choices in proptest::collection::vec((0usize..20, 0u8..6, proptest::num::u32::ANY), 1..20)
    ) {
        let definitions: Vec<_> = choices.iter().enumerate().map(|(i, &(target, shape, _))| {
            let target = target % choices.len();
            let body = match shape {
                0 => "1".to_owned(),
                1 => "true".to_owned(),
                2 => format!("f{target}()"),
                3 => format!("if true {{ 1 }} else {{ f{target}() }}"),
                4 => format!("{{ _ = f{target}()\ntrue }}"),
                _ => format!("f{target}() + 1"),
            };
            format!("fn f{i}() = {body}")
        }).collect();
        let a = check(&definitions.join("\n"));
        let mut order: Vec<_> = (0..choices.len()).collect();
        order.sort_by_key(|&i| choices[i].2);
        let b = check(&order.iter().map(|&i| definitions[i].as_str()).collect::<Vec<_>>().join("\n"));
        for (analysis, other) in [(&a, &b), (&b, &a)] {
            for function in &analysis.functions {
                let name = function.name().map(|name| analysis.text(name));
                let counterpart = other.functions.iter().find(|f| f.name().map(|n| other.text(n)) == name).unwrap();
                proptest::prop_assert_eq!(function.signature().map(|s| s.result), counterpart.signature().map(|s| s.result));
                proptest::prop_assert_eq!(function.body().is_some(), counterpart.body().is_some());
                if function.body().is_some() { invariant(analysis, function); }
            }
        }
    }

    #[test]
    fn damaged_token_sequences_do_not_panic(tokens in proptest::collection::vec(
        proptest::sample::select(vec!["fn", "let", "mut", "x", "int", "bool", "unit", "if", "else", "return", "_", "=", "->", ":", "(", ")", "{", "}", ",", "1", "true", "+", "-", "&&", "\n"]), 0..100)) {
        let source = format!("fn f(x: int) -> int {{ {} }}\nfn g() -> int = 1", tokens.join(" "));
        let a = check(&source);
        assert_eq!(a.is_valid(), !a.parsed.diagnostics().iter().chain(&a.diagnostics).any(|d| d.severity == Severity::Error));
        graph_invariant(&a);
        for function in &a.functions { if function.body().is_some() { invariant(&a, function); } }
    }

    #[test]
    fn arbitrary_source_has_diagnostic_backed_acceptance(source in ".{0,256}") {
        let a = check(&source);
        reversed_declarations_preserve_types(&a);
        graph_invariant(&a);
        let errors = a.parsed.diagnostics().iter().chain(&a.diagnostics).any(|d| d.severity == Severity::Error);
        proptest::prop_assert_eq!(a.is_valid(), !errors);
        for d in &a.diagnostics {
            for label in std::iter::once(&d.primary).chain(d.secondary.iter()) {
                proptest::prop_assert_eq!(label.location.file, a.parsed.file());
                proptest::prop_assert!(source.is_char_boundary(label.location.start().to_usize()));
                proptest::prop_assert!(source.is_char_boundary(label.location.end().to_usize()));
            }
        }
        for function in &a.functions { if function.body().is_some() { invariant(&a, function); } }
    }
}
