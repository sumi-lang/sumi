use super::*;
use sumi_frontend::{FileId, parse_source};

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
    analysis
}

fn codes(analysis: &Analysis) -> Vec<&'static str> {
    analysis
        .diagnostics()
        .iter()
        .map(|d| d.code.name())
        .collect()
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
            ExprKind::Local(local) => assert_eq!(expr.ty, body.locals[local.0].ty),
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
                let signature = analysis.function(*function).signature().unwrap();
                assert_eq!(expr.ty, signature.result);
                assert_eq!(args.len(), signature.params.len());
                for (&arg, &ty) in args.iter().zip(&signature.params) {
                    assert_eq!(body.expression(arg).ty, ty);
                }
                edges.extend(args);
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
                for statement in statements {
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
        "fn answer() -> int = (twice)(21)\nfn twice(x: int) -> int {\n let y = x * 2\n y\n}\nfn spin() = spin()\n",
    );
    let twice = analysis.functions[1].body().unwrap();
    assert_eq!(twice.exprs.len(), 5);
    assert_eq!(twice.locals.len(), 2);
    assert_eq!(twice.params, [LocalId(0)]);
    assert!(matches!(twice.exprs[0].kind, ExprKind::Local(LocalId(0))));
    assert!(matches!(twice.exprs[3].kind, ExprKind::Local(LocalId(1))));
    let answer = analysis.functions[0].body().unwrap();
    assert!(matches!(
        answer.expression(answer.root).kind,
        ExprKind::Call {
            function: FunctionId(1),
            ..
        }
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
            ExprKind::Local(id) => Some(id.0),
            _ => None,
        })
        .collect();
    assert_eq!(reads, [0, 1, 2, 1]);
    let a = check("fn f() -> int = 1\nfn g() -> int {\n let f = 2\n f()\n}\n");
    assert_eq!(codes(&a), ["not-callable"]);
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
        "fn f() = 1",
        "fn f() = if true { 7 }",
        "fn f() -> bool = {} == {}",
        "fn f() -> int = if 1 { 2 } else { false }",
    ] {
        let a = check(source);
        assert!(!a.is_valid(), "{source}");
        assert!(codes(&a).contains(&"type-mismatch"), "{source}");
    }
    let a =
        check("fn f() -> bool = true || missing\nfn g() -> int = if true { 1 } else { absent }\n");
    assert_eq!(codes(&a), ["unknown-name", "unknown-name"]);
}

#[test]
fn mismatch_labels_distinguish_branches_from_declarations() {
    for (source, expected) in [
        (
            "fn f() -> int = if true { 1 } else { false }",
            "other branch determines expected type",
        ),
        ("fn f() -> bool = 1", "declared here"),
        ("fn f() { let x: bool = 1 }", "declared here"),
    ] {
        let a = check(source);
        assert_eq!(codes(&a), ["type-mismatch"]);
        let labels = &a.diagnostics[0].secondary;
        assert_eq!(labels.len(), 1);
        assert_eq!(labels[0].message.as_deref(), Some(expected));
    }
}

#[test]
fn signed_literal_envelopes() {
    for (expr, value) in [
        ("9223372036854775807", i64::MAX),
        ("-9223372036854775808", i64::MIN),
        ("-((9223372036854775808))", i64::MIN),
        ("-9_223_372_036_854_775_808", i64::MIN),
    ] {
        let a = clean(&format!("fn f() -> int = {expr}"));
        let body = a.functions[0].body().unwrap();
        assert_eq!(body.exprs.len(), 1);
        assert!(matches!(body.exprs[0].kind, ExprKind::Int(n) if n == value));
    }
    for expr in [
        "9223372036854775808",
        "-9223372036854775809",
        "-(9223372036854775808 + 0)",
        "0 - 9223372036854775808",
        "9_223_372_036_854_775_808",
    ] {
        let a = check(&format!("fn f() -> int = {expr}"));
        assert_eq!(codes(&a), ["integer-range"], "{expr}");
    }
    let a = clean("fn f() -> int = --9223372036854775808");
    assert!(matches!(
        a.functions[0].body().unwrap().exprs[1].kind,
        ExprKind::Neg(_)
    ));
    for expr in ["01", "1__0", "1u32"] {
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
    assert_eq!(
        codes(&a),
        ["unknown-name", "type-mismatch", "type-mismatch"]
    );
    assert!(a.functions[0].body().is_none());
    let a = check("fn f(x: int, y: bool) {}\nfn g() { _ = f(true, 1, absent) }\n");
    assert_eq!(
        codes(&a),
        ["arity", "type-mismatch", "type-mismatch", "unknown-name"]
    );
}

#[test]
fn signatures_do_not_invent_missing_types_or_resolve_ambiguity() {
    for source in [
        "fn f(a:) -> { let x: = 1 }",
        "fn f() -> = 1",
        "fn f(a: int, ) ->",
        "fn f(a) {}",
    ] {
        let a = check(source);
        assert!(!a.is_valid(), "{source}");
        assert!(a.functions[0].signature().is_none(), "{source}");
    }
    let a = check("fn f(x: mystery) {}\nfn g() { _ = f(unknown, 1) }\n");
    assert_eq!(codes(&a), ["unknown-type", "unknown-name"]);
    assert!(a.functions.iter().all(|f| f.body().is_none()));
    let a = check("fn f() {}\nfn f() {}\nfn g() = f()\n");
    assert_eq!(codes(&a), ["duplicate-name"]);
    assert!(a.functions[2].body().is_none());
    let a = check("fn f(x: int, x: bool) {\n _ = !x\n _ = -x\n}\nfn g() = f(1, true)\n");
    assert_eq!(codes(&a), ["duplicate-name"]);
    assert!(a.functions[0].signature().is_some());
    assert!(a.functions[0].body().is_none());
    assert!(a.functions[1].body().is_some());
}

#[test]
fn invalid_parameters_do_not_hide_independent_result_errors() {
    for (parameter, expected) in [
        ("x: mystery", &["unknown-type", "type-mismatch"][..]),
        // Missing annotations are already diagnosed by the parser.
        ("x", &["type-mismatch"][..]),
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
            !codes(&a).contains(&"type-mismatch"),
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
    assert_eq!(codes(&a), ["unknown-name"]);
    for source in [
        "fn f() { return }",
        "fn f() { let x = 1\n x = 2 }",
        "fn f() { let g = fn() = 1 }",
        "fn f() = 1.5",
        "fn f() = \"hello\"",
        "fn f() = 'x'",
        "fn f() = (if true { 1 } else { 2 })()",
    ] {
        let a = check(source);
        assert!(a.parsed.diagnostics().is_empty(), "{source}");
        assert!(!a.is_valid());
        assert!(codes(&a).contains(&"unsupported"), "{source}");
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
    assert_eq!(codes(&a), ["unused-value"]);
    assert!(!a.is_valid());
    assert!(a.functions[0].body().is_none());
    clean("fn f() -> int { let u = {}\n u\n _ = 1\n 2 }");
}

#[test]
fn source_origins_are_utf8_byte_ranges() {
    let a = clean("fn café(é: int) -> int = é + 1");
    let body = a.functions[0].body().unwrap();
    let origin = body.exprs[0].origin;
    assert_eq!(origin.file(), FileId::new(17));
    assert_eq!(
        &a.parsed.source()[origin.range().start().to_usize()..origin.range().end().to_usize()],
        "é"
    );
    let a = check("fn café() -> int = absent");
    assert_eq!(
        a.diagnostics[0].primary.location.start().to_usize(),
        "fn café() -> int = ".len()
    );
}

#[test]
fn identifier_identity_is_nfkc_without_rewriting_source() {
    assert_eq!(unicode_normalization::UNICODE_VERSION, (17, 0, 0));
    for (left, right, key) in [
        ("é", "e\u{301}", "é"),
        ("K", "K", "K"),
        ("Ａ", "A", "A"),
        ("ﬀ", "ff", "ff"),
    ] {
        for (declared, used) in [(left, right), (right, left)] {
            let source = format!("fn {declared}({declared}: int) -> int = {used}");
            let a = clean(&source);
            assert_eq!(a.parsed().source(), source);
            let body = a.functions()[0].body().unwrap();
            assert_eq!(a.functions()[0].name(), Some(key));
            let range = body.expression(body.root()).origin.range();
            assert_eq!(
                &source[range.start().to_usize()..range.end().to_usize()],
                used
            );
            clean(&format!(
                "fn {declared}() -> int = 1\nfn caller() -> int = {used}()"
            ));
        }
    }
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
    assert_eq!(codes(&a), ["type-mismatch", "unknown-name", "unknown-name"]);
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
                    assert!(codes(&a).contains(&"type-mismatch"), "{source}");
                }
            }
        }
    }
    clean(
        "fn f(x: int) -> int = -x\nfn g(x: bool) -> bool = !x\nfn h() -> bool = true != false\nfn u(x: unit) -> unit { let y: unit = x\n y }\n",
    );
    for source in ["fn f() -> int = -true", "fn f() -> bool = !1"] {
        assert_eq!(codes(&check(source)), ["type-mismatch"]);
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
        actual.sort_unstable();
        assert_eq!(actual, ["type-mismatch", "unknown-name"], "{expression}");
        assert!(a.functions[0].body().is_none());
    }
}

#[test]
fn recovery_does_not_expose_functions_or_leak_argument_scopes() {
    let a = check("fn f() -> int = 1\nfn g() {\n let f =\n _ = f()\n _ = absent\n}\n");
    assert_eq!(codes(&a), ["unknown-name"]);
    assert!(a.diagnostics[0].message.contains("absent"));
    let a = check("fn f() {\n _ = missing({ let x = 1\n x }, x)\n}\n");
    assert_eq!(codes(&a), ["unknown-name", "unknown-name"]);
    let a = check("fn f() {\n let x = absent\n let x = true\n _ = x + 1\n}\n");
    assert_eq!(codes(&a), ["unknown-name", "type-mismatch"]);
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

proptest::proptest! {
    #[test]
    fn damaged_token_sequences_do_not_panic(tokens in proptest::collection::vec(
        proptest::sample::select(vec!["fn", "let", "mut", "x", "int", "bool", "unit", "if", "else", "return", "_", "=", "->", ":", "(", ")", "{", "}", ",", "1", "true", "+", "-", "&&", "\n"]), 0..100)) {
        let source = format!("fn f(x: int) -> int {{ {} }}\nfn g() -> int = 1", tokens.join(" "));
        let a = check(&source);
        assert_eq!(a.is_valid(), !a.parsed.diagnostics().iter().chain(&a.diagnostics).any(|d| d.severity == Severity::Error));
        for function in &a.functions { if function.body().is_some() { invariant(&a, function); } }
    }

    #[test]
    fn arbitrary_source_has_diagnostic_backed_acceptance(source in ".{0,256}") {
        let a = check(&source);
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
