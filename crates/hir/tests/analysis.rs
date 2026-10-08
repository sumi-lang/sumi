use sumi_frontend::{Diagnostic, DiagnosticCode, parse_source};
use sumi_hir::codes::*;
use sumi_hir::{
    Analysis, ArithOp, BinaryOp, BindingId, BindingKind, CmpOp, DeadCause, Function, FunctionId,
    Int, NodeId, Op, Symbol, Ty, analyze,
};
use sumi_test::{check, corpus};
use sumi_text::{TextRange, TextSize};

fn analyzed(source: &str) -> Analysis {
    analyze(parse_source(source.into()).unwrap())
}

fn clean(source: &str) -> Analysis {
    let analysis = analyzed(source);
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    assert!(analysis.functions().iter().all(Function::is_complete));
    check::semantics(&analysis);
    analysis
}

/// Not `Run::result`, which is the declared-result copy when there is one.
fn value(analysis: &Analysis, function: usize) -> NodeId {
    let graph = analysis.graph();
    graph
        .region(graph.run(FunctionId::new(function)).region())
        .result()
}

fn op(analysis: &Analysis, node: NodeId) -> &Op {
    &analysis.graph().node(node).op
}

fn body(analysis: &Analysis, function: usize) -> Vec<NodeId> {
    let graph = analysis.graph();
    graph
        .region(graph.run(FunctionId::new(function)).region())
        .nodes()
        .collect()
}

fn text(analysis: &Analysis, range: TextRange) -> &str {
    analysis.text(range)
}

fn semantic(analysis: &Analysis) -> Vec<&Diagnostic> {
    analysis.semantic_diagnostics().collect()
}

fn codes(analysis: &Analysis) -> Vec<DiagnosticCode> {
    semantic(analysis).iter().map(|d| d.code).collect()
}

#[test]
fn disagreeing_branches_are_undetermined_not_the_first_branch() {
    for result in ["bool", "int"] {
        let a = analyzed(&format!(
            "fn f(c: bool) -> {result} = {{ let x = if c {{ 1 }} else {{ true }}\n x }}"
        ));
        assert_eq!(codes(&a), [TYPE_MISMATCH], "{result}");
        assert_eq!(
            semantic(&a)[0].message.as_ref(),
            "if branches are int and bool"
        );
    }
    let a = analyzed(
        "fn f() -> bool = { let a = 1\n let b = true\n _ = if a == 1 { a } else { b }\n !a }",
    );
    assert_eq!(codes(&a), [TYPE_MISMATCH, TYPE_MISMATCH]);
    assert_eq!(semantic(&a)[1].message.as_ref(), "expected bool, found int");
}

#[test]
fn completing_inputs_are_not_scalar_reads() {
    for source in [
        "fn f() -> int = 10 + { return 16 }",
        "fn f() -> int = 10 + { return 16\n false }",
        "fn f() -> int = -{ return 16 }",
        "fn f() -> int = ({ return 16 })",
        "fn f() -> int { _ = false && { return 4\n true }\n 5 }",
        "fn f() -> int { let x: bool = { return 7 } }",
        "fn f(b: bool) -> int = if b { return 8 } else { return 9 }",
        "fn f() -> int = { return 10 } && { return 11 }",
        "fn id(x: int) -> int = x\nfn f() -> int = id({ return 12 })",
    ] {
        clean(source);
    }

    assert_eq!(codes(&analyzed("fn f() -> int = 10 + {}")), [TYPE_MISMATCH]);
}

#[test]
fn completing_paths_do_not_erase_a_live_unit_fallthrough() {
    for source in [
        "fn f(b: bool) -> int { if b { return 6 }\n _ = 1 }",
        "fn f() -> int { _ = false && { return 6\n true } }",
    ] {
        let analysis = analyzed(source);
        assert_eq!(codes(&analysis), [TYPE_MISMATCH], "{source}");
        assert_eq!(
            semantic(&analysis)[0].message.as_ref(),
            "expected int, found unit",
            "{source}"
        );
        assert!(!analysis.functions()[0].is_complete(), "{source}");
        check::semantics(&analysis);
    }
}

#[test]
fn a_wholly_returning_body_has_no_unit_fallthrough() {
    clean("fn f() -> int { return 1 }");
}

#[test]
fn an_inferred_unit_fallthrough_conflicts_with_a_return() {
    let source = "fn f(b: bool) = { if b { return 6 }\n _ = 1 }";
    let analysis = analyzed(source);
    assert_eq!(codes(&analysis), [CANNOT_INFER]);
    assert_eq!(
        semantic(&analysis)[0].message.as_ref(),
        "function result is both unit and int; add a return type annotation"
    );
    assert!(!analysis.functions()[0].is_complete());
    check::semantics(&analysis);
}

#[test]
fn damaged_values_with_completing_inputs_remain_incomplete() {
    for (source, function) in [
        (
            "fn id(x: int) = met8\nfn f() -> int { id({ return 4 }) }",
            1,
        ),
        (
            "fn id(x: int) = id(x)\nfn f() -> int { id({ return 4 }) }",
            1,
        ),
        ("fn f() -> int { let u: ud = { return 3 } }", 0),
    ] {
        let analysis = analyzed(source);
        assert!(!analysis.is_valid(), "{source}");
        assert!(!analysis.functions()[function].is_complete(), "{source}");
        check::semantics(&analysis);
    }
}

#[test]
fn validity_and_completion_are_independent() {
    for (lhs, rhs, valid) in [
        ("1", "2", true),
        ("1", "{ return 3 }", true),
        ("absent", "2", false),
        ("absent", "{ return 3 }", false),
    ] {
        let source = format!("fn f() -> int = {lhs} + {rhs}");
        let analysis = analyzed(&source);
        assert_eq!(analysis.is_valid(), valid, "{source}");
        assert_eq!(analysis.functions()[0].is_complete(), valid, "{source}");
        check::semantics(&analysis);
    }
}

#[test]
fn damaged_completion_propagates_through_expression_forms() {
    for (source, function) in [
        ("fn f() -> int = ({ _ = absent\n return 1 })", 0),
        ("fn f() -> int = -{ _ = absent\n return 1 }", 0),
        ("fn f() -> int = absent + { return 1 }", 0),
        ("fn f() -> int = false && { _ = absent\n return true }", 0),
        (
            "fn f() -> int = if true { _ = absent\n return 1 } else { return 2 }",
            0,
        ),
        ("fn f() -> int { _ = { _ = absent\n return 1 } }", 0),
        (
            "fn id(x: int) -> int = x\nfn f() -> int = id({ _ = absent\n return 1 })",
            1,
        ),
    ] {
        let analysis = analyzed(source);
        assert!(!analysis.is_valid(), "{source}");
        assert!(!analysis.functions()[function].is_complete(), "{source}");
        check::semantics(&analysis);
    }
}

#[test]
fn completing_conditions_do_not_hide_errors_inside_branches() {
    let analysis = analyzed(
        "fn arms() -> int = if { return 1 } { true + false } else { false + true }
fn no_else() -> int = if { return 2 } { true + false }",
    );
    assert_eq!(codes(&analysis), [TYPE_MISMATCH; 6]);
    assert!(
        semantic(&analysis)
            .iter()
            .all(|diagnostic| diagnostic.message.as_ref() == "expected int, found bool")
    );
    check::semantics(&analysis);
}

#[test]
fn forwarded_return_paths_keep_their_static_types() {
    for (source, message) in [
        (
            "fn f() -> int { if false { return 1 }\n true }\nfn entry() -> int = f() + 1",
            "expected int, found bool",
        ),
        (
            "fn f() -> int { let _x: bool = if false { return 1 } else { 2 }\n 3 }",
            "expected bool, found int",
        ),
        (
            "fn f() -> int { return 1\n false }",
            "expected int, found bool",
        ),
    ] {
        let analysis = analyzed(source);
        assert_eq!(codes(&analysis), [TYPE_MISMATCH], "{source}");
        assert_eq!(semantic(&analysis)[0].message.as_ref(), message, "{source}");
        check::semantics(&analysis);
    }
}

#[test]
fn stale_boolean_guards_do_not_refine_new_versions() {
    let analysis = analyzed(
        "fn and_case() -> int {
    let mut b = true
    if b && { b = false\n true } {
        if b { 1 } else { 1 / 0 }
    } else { 1 }
}
fn or_case() -> int {
    let mut b = false
    if b || { b = true\n false } {
        1
    } else if b { 1 / 0 } else { 1 }
}",
    );
    check::semantics(&analysis);
    assert_eq!(
        analysis
            .semantic_diagnostics()
            .filter(|diagnostic| diagnostic.code == DIVISION_BY_ZERO)
            .count(),
        2
    );
}

#[test]
fn recursive_delta_shares_repeated_phi_diamonds() {
    let forks = "    _ = if b { x = x - 1 } else { x = x - 2 }\n".repeat(30);
    let source = format!(
        "fn descend(n: int, b: bool) -> int {{
    if n <= 100 {{ return 0 }}
    let mut x = n
{forks}    descend(x, b)
}}
fn entry() -> int = descend(160, true) + descend(160, false)"
    );
    let analysis = clean(&source);
    assert_eq!(
        analysis.ranges(FunctionId::new(0)).unwrap().params[1].bools,
        sumi_hir::Bools::BOTH
    );
    assert!(
        analysis.functions()[0]
            .depth_bound()
            .is_some_and(|depth| depth > 1)
    );
    check::run(analysis.program().unwrap());
}

#[test]
fn nested_mutation_retires_shadowed_locals_and_restores_outer_versions() {
    let analysis = clean(
        "fn choose(b: bool) -> int {
    let mut x = 3
    let mut y = 11
    if b {
        y = y + 5
        _ = if true { let mut x = 100\n x = x + 7 }
        x = x + 2
    } else {
        x = x - 1
        if x > 0 { y = x + 1 } else { return -99 }
    }
    x * 100 + y
}
fn main() -> int = choose(true) + choose(false)",
    );
    let program = analysis.program().unwrap();
    assert_eq!(
        program.evaluate(program.function_named("main").unwrap(), &[]),
        sumi_hir::Value::Int(719.into())
    );
    check::run(program);
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
        let nodes = body(&a, 0);
        assert_eq!(nodes.len(), 1, "{expr}");
        let Op::Int(literal) = op(&a, nodes[0]) else {
            panic!("{expr} is one literal");
        };
        assert_eq!(literal, &value.parse::<Int>().unwrap(), "{expr}");
    }
    for expr in ["--9223372036854775808", "-(9223372036854775808 + 0)"] {
        let a = clean(&format!("fn f() -> int = {expr}"));
        assert!(matches!(op(&a, value(&a, 0)), Op::Neg), "{expr}");
    }
    for expr in ["01", "1_000", "1u32"] {
        let a = analyzed(&format!("fn f() -> int = {expr}"));
        assert!(!a.is_valid());
        assert!(!a.functions()[0].is_complete());
        assert!(semantic(&a).is_empty());
    }
}

#[test]
fn a_measure_is_read_through_any_depth_of_lets() {
    use std::fmt::Write as _;
    let mut source = String::from("fn f(n: int) -> int {\n    let a0 = n - 1\n");
    for i in 1..400 {
        writeln!(source, "    let a{i} = a{} - 0", i - 1).unwrap();
    }
    source.push_str("    if a399 < 0 { 0 } else { f(a399) }\n}\nfn main() -> int = f(5)\n");
    let analysis = analyzed(&source);
    assert!(
        analysis.diagnostics().is_empty(),
        "{:?}",
        analysis.diagnostics()
    );
    assert_eq!(analysis.functions()[1].depth_bound(), Some(7));
}

#[test]
fn call_requirements_replay_in_argument_order() {
    let source = "fn unknown() = unknown()\nfn take(a: int, b: bool) {}\nfn caller() = { let x = unknown()\n take(x, (x)) }";
    let a = analyzed(source);
    assert!(a.parsed().diagnostics().is_empty());
    let mismatches: Vec<_> = a
        .diagnostics()
        .iter()
        .filter(|d| d.code == TYPE_MISMATCH)
        .collect();
    assert_eq!(mismatches.len(), 1);
    assert_eq!(mismatches[0].message.as_ref(), "expected bool, found int");
    assert_eq!(
        mismatches[0].primary.start().to_usize(),
        source.rfind("(x)").unwrap()
    );

    let a = analyzed("fn take(_a: int, _b: bool) {}\nfn caller() { take(missing, 23) }");
    assert_eq!(codes(&a), [UNKNOWN_NAME, TYPE_MISMATCH]);
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
    assert!(
        body(&a, 2)
            .into_iter()
            .any(|node| matches!(op(&a, node), Op::Neg))
    );
    assert!(matches!(op(&a, value(&a, 3)), Op::Not));

    let a = clean("fn f() = { let\tmut\tvalue = 3\n value }");
    assert!(a.parsed().diagnostics().is_empty());
    assert_eq!(a.functions()[0].signature().unwrap().result, Ty::Int);
}

#[test]
fn syntax_diagnostics_are_preserved_and_always_reject() {
    for source in ["fn f() -> int = 01", "fn f() {}\r"] {
        let parsed = parse_source(source.into()).unwrap();
        assert!(!parsed.diagnostics().is_empty());
        let tree = parsed.parse().tree();
        assert!(!tree.has_error(tree.root()), "{source}");
        let before = parsed.diagnostics().to_vec();
        let a = analyze(parsed);
        assert!(!a.is_valid());
        assert_eq!(a.parsed().diagnostics(), before);
        check::semantics(&a);
    }
}

#[test]
fn source_origins_are_utf8_byte_ranges() {
    let a = clean("// café\nfn f(e: int) -> int = e + 1");
    let sum = value(&a, 0);
    let origin = a.graph().node(sum).origin;
    assert_eq!(text(&a, origin), "e + 1");
    let e = a.graph().inputs(sum)[0];
    assert!(matches!(op(&a, e), Op::Param { index: 0, .. }));
    assert_eq!(text(&a, a.graph().node(e).name.unwrap()), "e");
    let a = analyzed("// café\nfn f() -> int = absent");
    assert_eq!(
        semantic(&a)[0].primary.start().to_usize(),
        "// café\nfn f() -> int = ".len()
    );
}

#[test]
fn long_chains_are_stack_safe_even_when_rejected() {
    let chain = std::iter::repeat_n("1", 20_000)
        .collect::<Vec<_>>()
        .join(" + ");
    let a = clean(&format!("fn f() -> int = {chain}"));
    assert_eq!(body(&a, 0).len(), 39_999);
    let a = analyzed(&format!(
        "fn f() -> int = {chain} + true + missing\nfn g() -> int = absent\n"
    ));
    assert_eq!(codes(&a), [TYPE_MISMATCH, UNKNOWN_NAME, UNKNOWN_NAME]);
}

#[test]
fn scalar_operator_type_matrix() {
    let values = [("1", "int"), ("true", "bool"), ("{}", "unit")];
    for (op, eager) in [
        ("+", Some(BinaryOp::Arith(ArithOp::Add))),
        ("-", Some(BinaryOp::Arith(ArithOp::Sub))),
        ("*", Some(BinaryOp::Arith(ArithOp::Mul))),
        ("/", Some(BinaryOp::Arith(ArithOp::Div))),
        ("%", Some(BinaryOp::Arith(ArithOp::Rem))),
        ("<", Some(BinaryOp::Cmp(CmpOp::Lt))),
        ("<=", Some(BinaryOp::Cmp(CmpOp::Le))),
        (">", Some(BinaryOp::Cmp(CmpOp::Gt))),
        (">=", Some(BinaryOp::Cmp(CmpOp::Ge))),
        ("==", Some(BinaryOp::Cmp(CmpOp::Eq))),
        ("!=", Some(BinaryOp::Cmp(CmpOp::Ne))),
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
                let a = analyzed(&source);
                assert!(a.parsed().diagnostics().is_empty(), "{source}");
                assert_eq!(a.is_valid(), accepted, "{source}");
                if accepted {
                    assert!(a.functions()[0].is_complete());
                    match *self::op(&a, value(&a, 0)) {
                        Op::Binary(found) => assert_eq!(Some(found), eager),
                        Op::And { .. } => assert_eq!(op, "&&"),
                        Op::Or { .. } => assert_eq!(op, "||"),
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
        assert_eq!(codes(&analyzed(source)), [TYPE_MISMATCH]);
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
        let a = analyzed(&format!("fn f() {{ _ = {expression} }}"));
        let mut actual = codes(&a);
        actual.sort_unstable_by_key(|code| code.name);
        assert_eq!(actual, [TYPE_MISMATCH, UNKNOWN_NAME], "{expression}");
        assert!(!a.functions()[0].is_complete());
    }
}

#[test]
fn recovery_does_not_expose_functions_or_leak_argument_scopes() {
    let a = analyzed("fn f() -> int = 1\nfn g() {\n let f =\n _ = f()\n _ = absent\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME]);
    assert!(semantic(&a)[0].message.contains("absent"));
    let a = analyzed("fn f() {\n _ = missing({ let x = 1\n x }, x)\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME, UNKNOWN_NAME]);
    let a = analyzed("fn f() {\n let x = absent\n let x = true\n _ = x + 1\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME, TYPE_MISMATCH]);
    let a = analyzed("fn f() -> int {\n _ = absent\n 1\n}\n");
    assert!(!a.functions()[0].is_complete());
    clean("fn f() -> int {\n let x =\n 1\n x\n}\n");
}

#[test]
fn existing_corpus_never_panics_or_silently_rejects() {
    let cases = corpus::cases();
    assert!(cases.len() > 100);
    for case in cases {
        let source = std::fs::read_to_string(case.join("case.su")).unwrap();
        check::semantics(&analyzed(&source));
    }
}

#[test]
fn large_definition_chains_and_cycles_are_stack_safe() {
    use std::fmt::Write;
    const COUNT: usize = 10_000;
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
            let a = analyzed(&source);
            assert_eq!(a.is_valid(), grounded);
            if grounded {
                assert!(a.functions().iter().all(Function::is_complete));
            } else {
                let recursion = usize::from(!conflict);
                assert_eq!(
                    semantic(&a).len(),
                    if conflict { 2 } else { COUNT + recursion }
                );
                assert_eq!(
                    semantic(&a)
                        .iter()
                        .filter(|d| d.code == UNBOUNDED_RECURSION)
                        .count(),
                    recursion
                );
                assert!(
                    semantic(&a)
                        .iter()
                        .all(|d| d.code == CANNOT_INFER || d.code == UNBOUNDED_RECURSION)
                );
                assert!(
                    a.functions()
                        .iter()
                        .all(|f| f.signature().is_none() && !f.is_complete())
                );
            }
        }
    }
}

#[test]
fn dead_code_carries_its_range_and_cause() {
    let a = clean(
        "fn branch() -> int = if false { 1 } else { 2 }
fn right(b: bool) -> bool = false && b
fn body() -> int {
    let mut total = 0
    for i in 5..5 {
        total = total + i
    }
    total
}
fn after() -> int {
    return 1
    let x = 2
    x
}
fn main() -> bool = right(true)",
    );
    let dead: Vec<_> = a
        .dead()
        .iter()
        .map(|dead| (text(&a, dead.range), dead.cause))
        .collect();
    assert_eq!(
        dead,
        [
            ("{ 1 }", DeadCause::Branch),
            ("b", DeadCause::RightOperand),
            ("{\n        total = total + i\n    }", DeadCause::LoopBody),
            ("let x = 2\n    x", DeadCause::AfterStop),
        ]
    );
}

#[test]
fn a_file_with_an_error_reports_no_dead_code() {
    let a = analyzed(
        "fn f() -> int {\n    return 1\n    true + 1\n}\nfn g() -> int = if false { 1 } else { 2 }",
    );
    assert!(!a.is_valid());
    assert!(a.dead().is_empty());
}

proptest::proptest! {
    #![proptest_config(sumi_test::regressions!("analysis.txt"))]
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
        let a = analyzed(&definitions.join("\n"));
        let mut order: Vec<_> = (0..choices.len()).collect();
        order.sort_by_key(|&i| choices[i].2);
        let b = analyzed(&order.iter().map(|&i| definitions[i].as_str()).collect::<Vec<_>>().join("\n"));
        for (analysis, other) in [(&a, &b), (&b, &a)] {
            for function in analysis.functions() {
                let name = function.name().map(|name| analysis.text(name));
                let counterpart = other.functions().iter().find(|f| f.name().map(|n| other.text(n)) == name).unwrap();
                proptest::prop_assert_eq!(function.signature().map(|s| s.result), counterpart.signature().map(|s| s.result));
                proptest::prop_assert_eq!(function.is_complete(), counterpart.is_complete());
            }
        }
    }

    #[test]
    fn damaged_token_sequences_do_not_panic(tokens in proptest::collection::vec(
        proptest::sample::select(vec!["fn", "let", "mut", "x", "int", "bool", "unit", "if", "else", "return", "_", "=", "->", ":", "(", ")", "{", "}", ",", "1", "true", "+", "-", "&&", "\n"]), 0..100)) {
        let source = format!("fn f(x: int) -> int {{ {} }}\nfn g() -> int = 1", tokens.join(" "));
        check::semantics(&analyzed(&source));
    }

    #[test]
    fn arbitrary_source_has_diagnostic_backed_acceptance(source in ".{0,256}") {
        check::semantics(&analyzed(&source));
    }
}

fn visible_names(analysis: &Analysis, offset: usize) -> Vec<&str> {
    analysis
        .visible_at(TextSize::new(offset as u32))
        .into_iter()
        .map(|binding| analysis.text(binding.name()))
        .collect()
}

#[test]
fn bindings_are_visible_after_their_declaration_to_the_end_of_their_block() {
    let source = "fn f(a: int, b: bool) -> int {
    let a = if b { a } else { 0 }
    let mut total = 0
    for i in 0..a {
        let step = i * 2
        total = total + step
    }
    total
}";
    let a = clean(source);
    let kinds: Vec<_> = a
        .bindings()
        .iter()
        .map(|b| (text(&a, b.name()), b.kind()))
        .collect();
    assert_eq!(
        kinds,
        [
            ("a", BindingKind::Param),
            ("b", BindingKind::Param),
            ("a", BindingKind::Let { is_mutable: false }),
            ("total", BindingKind::Let { is_mutable: true }),
            ("i", BindingKind::LoopIndex),
            ("step", BindingKind::Let { is_mutable: false }),
        ]
    );
    let param_a = &a.bindings()[0];
    let let_a = &a.bindings()[2];
    assert_eq!(a.ty(param_a.declaration()), Some(Ty::Int));
    assert_eq!(a.ty(a.bindings()[1].declaration()), Some(Ty::Bool));
    assert_eq!(a.ty(let_a.declaration()), Some(Ty::Int));
    assert_eq!(a.ty(a.bindings()[4].declaration()), Some(Ty::Int));
    assert_eq!(
        param_a.visible(),
        TextRange::new(TextSize::new(29), TextSize::new(source.len() as u32))
    );
    assert_eq!(
        visible_names(&a, source.find("-> int").unwrap()),
        Vec::<&str>::new()
    );
    let initializer_a = source.find("{ a }").unwrap() + 2;
    assert_eq!(visible_names(&a, initializer_a), ["a", "b"]);
    let shadowed = a.visible_at(TextSize::new(initializer_a as u32));
    assert_eq!(shadowed[0].kind(), BindingKind::Param);
    let after_let = source.find("let mut total").unwrap();
    assert_eq!(visible_names(&a, after_let), ["b", "a"]);
    assert_eq!(
        a.visible_at(TextSize::new(after_let as u32))[1].kind(),
        BindingKind::Let { is_mutable: false }
    );
    assert_eq!(
        visible_names(&a, source.find("0..a").unwrap()),
        ["b", "a", "total"]
    );
    let in_loop = source.find("total = total").unwrap();
    assert_eq!(visible_names(&a, in_loop), ["b", "a", "total", "i", "step"]);
    let after_loop = source.find("    }\n").unwrap() + 5;
    assert_eq!(visible_names(&a, after_loop), ["b", "a", "total"]);
    let tail = source.rfind("total").unwrap();
    assert_eq!(visible_names(&a, tail), ["b", "a", "total"]);
    assert_eq!(visible_names(&a, source.len()), Vec::<&str>::new());
    for binding in a.bindings() {
        assert_eq!(
            a.graph().node(binding.declaration()).name,
            Some(binding.name())
        );
    }
}

#[test]
fn bindings_survive_recovery_and_a_missing_body() {
    let source = "fn f(x: int) -> int {\n    let y = \n    let z = x +\n    ";
    let a = analyzed(source);
    assert!(!a.is_valid());
    let names: Vec<_> = a.bindings().iter().map(|b| text(&a, b.name())).collect();
    assert_eq!(names, ["x", "y", "z"]);
    let y = &a.bindings()[1];
    let let_y = source.find("let y =").unwrap();
    assert_eq!(y.visible().start().to_usize(), let_y + 7);
    assert_eq!(visible_names(&a, let_y + 6), ["x"]);
    assert_eq!(visible_names(&a, source.find("x +").unwrap()), ["x", "y"]);
    assert_eq!(visible_names(&a, source.len()), ["x", "y", "z"]);

    let source = "fn f(x: int) -> int {\n    if x > 0 { x }\n    ";
    let a = analyzed(source);
    assert_eq!(visible_names(&a, source.len()), ["x"]);

    let source = "fn f(x: int) -> int = ";
    let a = analyzed(source);
    assert_eq!(visible_names(&a, 5), Vec::<&str>::new());
    assert_eq!(visible_names(&a, source.len()), ["x"]);
    assert_eq!(visible_names(&a, source.len() - 1), ["x"]);
    let a = analyzed("fn f(x: int) -> int");
    assert_eq!(a.bindings()[0].visible().start().to_usize(), 19);
    assert_eq!(visible_names(&a, 19), ["x"]);
}

#[test]
fn a_cut_short_let_before_the_next_item_is_visible_up_to_it() {
    let a = analyzed("fn f() = {\n    let x =\nfn g() = x");
    let x = &a.bindings()[0];
    assert_eq!(
        x.visible(),
        TextRange::new(TextSize::new(22), TextSize::new(23))
    );
    assert_eq!(visible_names(&a, 22), ["x"]);
    assert_eq!(visible_names(&a, 23), Vec::<&str>::new());
}

#[test]
fn debug_output_lists_the_tables() {
    let shown = format!("{:?}", clean("fn f(x: int) -> int = x"));
    assert!(shown.contains("bindings: ["));
}

#[test]
fn references_resolve_reads_calls_and_assignments_to_their_symbol() {
    let source = "fn double(x: int) -> int = x + x
fn body(c: bool) -> int {
    let c = if c { 1 } else { 0 }
    let mut total = double(c)
    for i in 0..c {
        total = total + i
    }
    total
}";
    let a = clean(source);
    let at = |needle: &str, occurrence: usize| {
        let mut from = 0;
        for _ in 0..occurrence {
            from = source[from..].find(needle).unwrap() + from + needle.len();
        }
        let start = source[from..].find(needle).unwrap() + from;
        TextSize::new(start as u32)
    };
    let symbol = |needle: &str, occurrence: usize| {
        let offset = at(needle, occurrence);
        a.symbol_at(offset)
            .unwrap_or_else(|| panic!("no symbol at {offset:?} for {needle:?}"))
    };
    let param_x = symbol("x", 0);
    assert_eq!(param_x.symbol, Symbol::Local(BindingId::new(0)));
    assert_eq!(symbol("x + x", 0).symbol, param_x.symbol);
    let end_of_x = TextSize::new(at("x + x", 0).to_u32() + 1);
    assert_eq!(a.symbol_at(end_of_x).unwrap().symbol, param_x.symbol);
    assert_eq!(a.declaration(param_x.symbol), Some(param_x.range));
    let reads: Vec<_> = a
        .references_of(param_x.symbol)
        .map(|range| range.start().to_u32())
        .collect();
    assert_eq!(reads, [at("x + x", 0).to_u32(), at("x", 2).to_u32()]);
    let param_c = symbol("c: bool", 0).symbol;
    let let_c = symbol("c = if", 0);
    assert_eq!(let_c.symbol, Symbol::Local(BindingId::new(2)));
    assert_eq!(symbol("c { 1 }", 0).symbol, param_c);
    assert_eq!(symbol("c)", 0).symbol, let_c.symbol);
    assert_eq!(symbol("c {", 1).symbol, let_c.symbol);
    assert_eq!(a.references_of(param_c).count(), 1);
    assert_eq!(a.references_of(let_c.symbol).count(), 2);
    let double = symbol("double(c)", 0);
    assert_eq!(double.symbol, Symbol::Function(FunctionId::new(0)));
    assert_eq!(symbol("double(x", 0).range.start().to_u32(), 3);
    assert_eq!(
        a.declaration(double.symbol).map(|r| r.start().to_u32()),
        Some(3)
    );
    let total = symbol("total = double", 0).symbol;
    assert_eq!(a.references_of(total).count(), 3);
    assert_eq!(symbol("total = total", 0).symbol, total);
    assert_eq!(a.symbol_at(at("->", 0)), None);
    assert_eq!(a.symbol_at(at("0..c", 0)), None);
    let starts: Vec<_> = a.references().iter().map(|o| o.range.start()).collect();
    assert!(starts.windows(2).all(|pair| pair[0] < pair[1]));
    assert_eq!(starts.len(), 10);
}

#[test]
fn references_survive_errors() {
    let a = analyzed("fn f(x: int) -> int {\n    x = 1\n    g(x)\n    x(1)\n}");
    assert!(!a.is_valid());
    let x = Symbol::Local(BindingId::new(0));
    assert_eq!(a.references_of(x).count(), 3);
    assert_eq!(
        a.references()
            .iter()
            .filter(|o| matches!(o.symbol, Symbol::Function(_)))
            .count(),
        0
    );

    let a = analyzed("fn g() = 1\nfn f(n: int) -> int {\n    let h = g\n    g = 2\n    h + n\n}");
    let g = Symbol::Function(FunctionId::new(0));
    assert_eq!(a.references_of(g).count(), 2);

    let source = "fn g() = 1\nfn f(n: int) -> int {\n    let mut t = 0\n    for i in 0.. { t = t + n + g() }\n    let y = n && \n    t\n}";
    let a = analyzed(source);
    assert!(!a.is_valid());
    let n = Symbol::Local(BindingId::new(0));
    let loop_n = source.find("+ n").unwrap() + 2;
    let and_n = source.find("= n &&").unwrap() + 2;
    let texts: Vec<_> = a
        .references_of(n)
        .map(|range| range.start().to_usize())
        .collect();
    assert_eq!(texts, [loop_n, and_n]);
    assert_eq!(a.references_of(g).count(), 1);
    let i = source.find("{ t = t").unwrap();
    assert_eq!(
        a.symbol_at(TextSize::new(i as u32 + 2)).map(|o| o.symbol),
        Some(Symbol::Local(BindingId::new(1)))
    );
    assert_eq!(
        a.symbol_at(TextSize::new(source.find("for i").unwrap() as u32 + 4)),
        None
    );
    assert_eq!(a.unresolved(), []);

    let source = "fn f(n: int) -> int {\n    for n in 0.. { n + 1 }\n    n\n}";
    let a = analyzed(source);
    let n = Symbol::Local(BindingId::new(0));
    assert_eq!(a.references_of(n).count(), 1);
    let inner = source.find("n + 1").unwrap() as u32;
    assert_eq!(
        a.unresolved(),
        [TextRange::new(
            TextSize::new(inner),
            TextSize::new(inner + 1)
        )]
    );
}

#[test]
fn params_come_by_position_without_an_unnamed_one() {
    let a = clean("fn f(a: int, b: bool) -> int = if b { a } else { 0 }\nfn g() = 1");
    let names: Vec<_> = a
        .params(FunctionId::new(0))
        .map(|param| param.map(|binding| text(&a, binding.name())))
        .collect();
    assert_eq!(names, [Some("a"), Some("b")]);
    assert_eq!(a.params(FunctionId::new(1)).len(), 0);

    let a = analyzed("fn f(a: int, a: bool, : int) -> int = 1");
    let names: Vec<_> = a
        .params(FunctionId::new(0))
        .map(|param| param.map(|binding| text(&a, binding.name())))
        .collect();
    assert_eq!(names, [Some("a"), Some("a")]);
}
