use std::fmt::Write;

use sumi_frontend::{ParsedSource, parse_source};
use sumi_hir::{Analysis, Ty};

const SHAPES: [&str; 5] = [
    "inferred-reverse",
    "unresolved-cycle",
    "branches",
    "nested-mutation",
    "caller-guards",
];

pub fn source(shape: &str, size: usize) -> String {
    assert!(SHAPES.contains(&shape));
    if shape == "nested-mutation" {
        let mut source = String::from("fn mutate(b: bool) -> int {\nlet mut x = 0\n");
        for _ in 0..size {
            source.push_str("if b { if b { x = x + 1 } else { x = x + 2 } } else { x = x + 3 }\n");
        }
        source.push_str("x }\nfn main() -> int = mutate(true)");
        return source;
    }
    if shape == "caller-guards" {
        let mut source = String::new();
        for i in 0..size {
            writeln!(
                source,
                "fn g{i}(n: int) -> int = if n < 0 {{ 0 - n }} else {{ n + 1 }}\nfn c{i}() -> int = g{i}({i})"
            )
            .unwrap();
        }
        return source;
    }

    let mut declarations = Vec::with_capacity(size);
    for i in 0..size {
        let mut declaration = format!("fn f{i}() = ");
        if shape == "branches" {
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
        } else if i + 1 < size {
            write!(declaration, "f{}()", i + 1).unwrap();
        } else if shape == "unresolved-cycle" {
            declaration.push_str("f0()");
        } else {
            declaration.push('1');
        }
        declarations.push(declaration);
    }
    if shape == "inferred-reverse" {
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
        "nested-mutation" => 2,
        "caller-guards" => 2 * size,
        _ => size,
    };
    assert_eq!(analysis.functions().len(), functions);
    if shape == "unresolved-cycle" {
        assert!(!analysis.is_valid());
        assert_eq!(analysis.diagnostics().len(), size + 1);
        assert!(
            analysis
                .functions()
                .iter()
                .all(|function| function.signature().is_none() && !function.complete())
        );
        return;
    }

    assert!(analysis.is_valid());
    if shape == "caller-guards" {
        assert!(
            analysis.diagnostics().is_empty(),
            "a guard its callers decide is not reported"
        );
    }
    let graph = analysis.graph();
    for (index, function) in analysis.functions().iter().enumerate() {
        assert_eq!(function.signature().unwrap().result, Ty::Int);
        assert!(function.complete());
        let result = graph.run(sumi_hir::FunctionId::new(index)).result();
        assert_eq!(analysis.ty(result), Some(Ty::Int));
    }
    if shape == "nested-mutation" {
        let program = analysis.program().unwrap();
        let main = program.function_named("main").unwrap();
        assert_eq!(
            program.evaluate(main, &[]),
            sumi_hir::Value::Int((size as i64).into())
        );
    }
}
