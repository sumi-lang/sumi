use std::fmt::Write;
use sumi_frontend::parse_source;
use sumi_hir::{Analysis, Value, analyze};

pub const CASES: &[(&str, &[usize])] = &[
    ("independent", &[128, 1024, 8192]),
    ("dense", &[8, 32, 128]),
    ("mixed", &[32, 128, 512]),
    ("shared", &[32, 128, 512]),
];

pub fn source(shape: &str, size: usize) -> String {
    let mut source = String::new();
    let functions = if shape == "shared" { 1 } else { size };
    for i in 0..functions {
        writeln!(source, "fn f{i}(n: int) -> int = if n <= 0 {{ 7 }} else {{").unwrap();
        match shape {
            "independent" => writeln!(source, "f{i}(n - 1)").unwrap(),
            "dense" | "mixed" => {
                let start = if shape == "mixed" { i / 8 * 8 } else { 0 };
                let end = if shape == "mixed" { start + 8 } else { size };
                for j in start..end {
                    writeln!(source, "_ = f{j}(n - 1)").unwrap();
                }
                if start > 0 {
                    writeln!(source, "_ = f{}(n - 1)", start - 1).unwrap();
                }
                source.push_str("7\n");
            }
            "shared" => {
                source.push_str("let x0 = n - 1\n");
                for j in 1..size {
                    writeln!(source, "let x{j} = x{} + 0", j - 1).unwrap();
                }
                for _ in 0..size {
                    writeln!(source, "_ = f0(x{})", size - 1).unwrap();
                }
                source.push_str("7\n");
            }
            _ => unreachable!(),
        }
        source.push_str("}\n");
    }
    source.push_str("fn main() -> int {\n");
    for i in 0..functions {
        writeln!(source, "_ = f{i}(1)").unwrap();
    }
    source.push_str("7 }");
    source
}

pub fn validate(shape: &str, size: usize, analysis: &Analysis) {
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    let program = analysis.program().unwrap();
    let main = program.function_named("main").unwrap();
    assert_eq!(program.evaluate(main, &[]), Value::Int(7.into()));
    let components = if shape == "mixed" { size / 8 } else { 1 };
    assert_eq!(
        analysis.functions().last().unwrap().depth_bound(),
        Some(2 * components as u64 + 1)
    );
}

pub fn checked(shape: &str, size: usize) {
    validate(
        shape,
        size,
        &analyze(parse_source(source(shape, size).into()).unwrap()),
    );
}
