use std::fmt::Write;
use sumi_frontend::{ParsedSource, parse_source};
use sumi_hir::{Analysis, Ty};

pub const SIZES: [usize; 3] = [128, 1024, 8192];
pub const SHAPES: [&str; 13] = [
    "annotated-forward",
    "annotated-reverse",
    "inferred-forward",
    "inferred-reverse",
    "grounded-cycle",
    "unresolved-cycle",
    "conflict-cycle",
    "locals",
    "arguments",
    "branches",
    "scoped-mutation",
    "expression-chain",
    "call-block",
];

pub fn source(shape: &str, size: usize) -> String {
    assert!(SHAPES.contains(&shape));
    if shape == "expression-chain" {
        return format!("fn sum() -> int = 1{}", " + 2".repeat(size));
    }
    if shape == "call-block" {
        let mut source = String::from(
            "fn select(x: int, b: bool) -> int = if b { x } else { 0 }\nfn calls() -> int = {\n",
        );
        for i in 0..size {
            writeln!(source, "_ = select({i}, true)").unwrap();
        }
        source.push_str("7 }");
        return source;
    }
    if shape == "scoped-mutation" {
        let mut source = String::from("fn scoped() -> int {\n");
        for i in 0..size {
            writeln!(source, "_ = if true {{ let mut x{i} = 0\n x{i} = 1 }}").unwrap();
        }
        source.push_str("0 }");
        return source;
    }
    let mut declarations = Vec::with_capacity(size);
    for i in 0..size {
        let annotation = if shape.starts_with("annotated") {
            " -> int"
        } else {
            ""
        };
        let parameters = if shape == "arguments" {
            "x: int, b: bool"
        } else {
            ""
        };
        let mut declaration = format!("fn f{i}({parameters}){annotation} = ");
        if shape == "arguments" {
            if i + 1 < size {
                write!(declaration, "f{}(x + 1, !b)", i + 1).unwrap();
            } else {
                declaration.push_str("if b { x } else { 0 }");
            }
        } else if shape == "branches" {
            declaration.push_str("{ let x0 = 1\n");
            for j in 1..16 {
                writeln!(
                    declaration,
                    "let x{j} = if x{} > {j} {{ {j} }} else {{ x{} + 1 }}",
                    j - 1,
                    j - 1
                )
                .unwrap();
            }
            declaration.push_str("x15 }");
        } else if shape == "locals" {
            declaration.push_str("{ let x0 = 1\n");
            for j in 1..16 {
                writeln!(declaration, "let x{j} = x{} + 1", j - 1).unwrap();
            }
            declaration.push_str("x15 }");
        } else if shape == "conflict-cycle" && i == 0 {
            declaration.push_str("if true { true } else { f1() }");
        } else if i + 1 < size {
            write!(declaration, "f{}()", i + 1).unwrap();
        } else {
            declaration.push_str(match shape {
                "grounded-cycle" | "conflict-cycle" => "if true { 1 } else { f0() }",
                "unresolved-cycle" => "f0()",
                _ => "1",
            });
        }
        declarations.push(declaration);
    }
    if shape.ends_with("reverse") {
        declarations.reverse();
    }
    declarations.join("\n")
}

pub fn parse(source: &str) -> ParsedSource {
    let parsed = parse_source(source.into()).unwrap();
    assert!(parsed.diagnostics().is_empty());
    parsed
}

pub fn validate(shape: &str, size: usize, analysis: &Analysis) {
    let functions = match shape {
        "expression-chain" | "scoped-mutation" => 1,
        "call-block" => 2,
        _ => size,
    };
    assert_eq!(analysis.functions().len(), functions);
    if matches!(shape, "unresolved-cycle" | "conflict-cycle") {
        assert!(!analysis.is_valid());
        // unresolved-cycle: one report per function, plus one recursion with no measure since its
        // cycle is live. conflict-cycle: one report at each endpoint, the rest inherit silently;
        // its cycle is dead under `if true`, so no recursion report.
        let reports = if shape == "conflict-cycle" {
            2
        } else {
            size + 1
        };
        assert_eq!(analysis.diagnostics().len(), reports);
        assert!(
            analysis
                .functions()
                .iter()
                .all(|f| f.signature().is_none() && !f.complete())
        );
    } else {
        assert!(analysis.is_valid());
        let graph = analysis.graph();
        for (index, function) in analysis.functions().iter().enumerate() {
            assert_eq!(function.signature().unwrap().result, Ty::Int);
            assert!(function.complete());
            let result = graph.run(sumi_hir::FunctionId::new(index)).result();
            assert_eq!(analysis.ty(result), Some(Ty::Int));
        }
    }
}
