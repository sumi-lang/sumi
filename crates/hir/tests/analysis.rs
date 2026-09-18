//! The analysis held to its contracts: what the graph of a body is, which
//! files are accepted, and what each diagnostic says.

use sumi_frontend::{Diagnostic, DiagnosticCode, parse_source};
use sumi_hir::codes::*;
use sumi_hir::{Analysis, BinaryOp, Function, FunctionId, Int, NodeId, Op, Ty, analyze};
use sumi_test::{check, corpus};
use sumi_text::TextRange;

fn check(source: &str) -> Analysis {
    analyze(parse_source(source.into()).unwrap())
}

fn clean(source: &str) -> Analysis {
    let analysis = check(source);
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    assert!(analysis.functions().iter().all(Function::complete));
    check::semantics(&analysis);
    analysis
}

/// The value a function's body computes: its region's result, before the
/// copy a declared result holds it in.
fn value(analysis: &Analysis, function: usize) -> NodeId {
    let graph = analysis.graph();
    graph
        .region(graph.run(FunctionId::new(function)).region())
        .result()
}

fn op(analysis: &Analysis, node: NodeId) -> &Op {
    &analysis.graph().node(node).op
}

/// The nodes a function's body region defines, in definition order.
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

/// The checker's diagnostics, apart from the frontend's.
fn semantic(analysis: &Analysis) -> Vec<&Diagnostic> {
    analysis.semantic_diagnostics().collect()
}

fn codes(analysis: &Analysis) -> Vec<DiagnosticCode> {
    semantic(analysis).iter().map(|d| d.code).collect()
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
            semantic(&a)[0].message.as_ref(),
            "if branches are int and bool"
        );
    }
    let a = check(
        "fn f() -> bool = { let a = 1\n let b = true\n _ = if a == 1 { a } else { b }\n !a }",
    );
    assert_eq!(codes(&a), [TYPE_MISMATCH, TYPE_MISMATCH]);
    assert_eq!(semantic(&a)[1].message.as_ref(), "expected bool, found int");
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
    // Only a `-` directly on the literal folds; the rest is a negation.
    for expr in ["--9223372036854775808", "-(9223372036854775808 + 0)"] {
        let a = clean(&format!("fn f() -> int = {expr}"));
        assert!(matches!(op(&a, value(&a, 0)), Op::Neg), "{expr}");
    }
    for expr in ["01", "1_000", "1u32"] {
        let a = check(&format!("fn f() -> int = {expr}"));
        assert!(!a.is_valid());
        assert!(!a.functions()[0].complete());
        assert!(semantic(&a).is_empty());
    }
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
    assert_eq!(analysis.functions()[1].depth_bound(), Some(7));
}

#[test]
fn call_requirements_replay_in_argument_order() {
    let source = "fn unknown() = unknown()\nfn take(a: int, b: bool) {}\nfn caller() = { let x = unknown()\n take(x, (x)) }";
    let a = check(source);
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

    let a = check("fn take(a: int, b: bool) {}\nfn caller() { take(missing, 23) }");
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

    let a = check("fn f() = { let\tmut\tvalue = 3\n value }");
    assert!(a.parsed().diagnostics().is_empty());
    assert_eq!(codes(&a), [UNSUPPORTED]);
    assert!(!a.functions()[0].complete());
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
    assert!(matches!(op(&a, e), Op::Param(0)));
    assert_eq!(text(&a, a.graph().node(e).name.unwrap()), "e");
    let a = check("// café\nfn f() -> int = absent");
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
        actual.sort_unstable_by_key(|code| code.name);
        assert_eq!(actual, [TYPE_MISMATCH, UNKNOWN_NAME], "{expression}");
        assert!(!a.functions()[0].complete());
    }
}

#[test]
fn recovery_does_not_expose_functions_or_leak_argument_scopes() {
    let a = check("fn f() -> int = 1\nfn g() {\n let f =\n _ = f()\n _ = absent\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME]);
    assert!(semantic(&a)[0].message.contains("absent"));
    let a = check("fn f() {\n _ = missing({ let x = 1\n x }, x)\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME, UNKNOWN_NAME]);
    let a = check("fn f() {\n let x = absent\n let x = true\n _ = x + 1\n}\n");
    assert_eq!(codes(&a), [UNKNOWN_NAME, TYPE_MISMATCH]);
    let a = check("fn f() -> int {\n _ = absent\n 1\n}\n");
    assert!(!a.functions()[0].complete());
    clean("fn f() -> int {\n let x =\n 1\n x\n}\n");
}

#[test]
fn existing_corpus_never_panics_or_silently_rejects() {
    let cases = corpus::cases();
    assert!(cases.len() > 100);
    for case in cases {
        let source = std::fs::read_to_string(case.join("case.sumi")).unwrap();
        check::semantics(&check(&source));
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
                assert!(a.functions().iter().all(Function::complete));
            } else {
                // A conflict is reported once at each end that claims a
                // type; every function between inherits it silently. A live
                // cycle with no ground is also a recursion with no measure,
                // reported once.
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
        let a = check(&definitions.join("\n"));
        let mut order: Vec<_> = (0..choices.len()).collect();
        order.sort_by_key(|&i| choices[i].2);
        let b = check(&order.iter().map(|&i| definitions[i].as_str()).collect::<Vec<_>>().join("\n"));
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
        check::semantics(&check(&source));
    }

    #[test]
    fn arbitrary_source_has_diagnostic_backed_acceptance(source in ".{0,256}") {
        check::semantics(&check(&source));
    }
}
