use sumi_frontend::{Diagnostic, DiagnosticCode, parse_source};
use sumi_hir::codes::*;
use sumi_hir::{
    Analysis, ArithOp, BinaryOp, CmpOp, Function, FunctionId, Int, NodeId, Op, Ty, analyze,
};
use sumi_test::{check, corpus};
use sumi_text::TextRange;

fn analyzed(source: &str) -> Analysis {
    analyze(parse_source(source.into()).unwrap())
}

fn clean(source: &str) -> Analysis {
    let analysis = analyzed(source);
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    assert!(analysis.functions().iter().all(Function::complete));
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
        assert!(!analysis.functions()[0].complete(), "{source}");
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
    assert!(!analysis.functions()[0].complete());
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
        assert!(!analysis.functions()[function].complete(), "{source}");
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
        assert_eq!(analysis.functions()[0].complete(), valid, "{source}");
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
        assert!(!analysis.functions()[function].complete(), "{source}");
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
            "fn f() -> int { let x: bool = if false { return 1 } else { 2 }\n 3 }",
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
}}"
    );
    let analysis = clean(&source);
    assert!(analysis.functions()[0].depth_bound().is_some());
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
        assert!(!a.functions()[0].complete());
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

    let a = analyzed("fn take(a: int, b: bool) {}\nfn caller() { take(missing, 23) }");
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
                    assert!(a.functions()[0].complete());
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
        assert!(!a.functions()[0].complete());
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
    assert!(!a.functions()[0].complete());
    clean("fn f() -> int {\n let x =\n 1\n x\n}\n");
}

#[test]
fn existing_corpus_never_panics_or_silently_rejects() {
    let cases = corpus::cases();
    assert!(cases.len() > 100);
    for case in cases {
        let source = std::fs::read_to_string(case.join("case.sumi")).unwrap();
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
                assert!(a.functions().iter().all(Function::complete));
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
                        .all(|f| f.signature().is_none() && !f.complete())
                );
            }
        }
    }
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
                proptest::prop_assert_eq!(function.complete(), counterpart.complete());
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
