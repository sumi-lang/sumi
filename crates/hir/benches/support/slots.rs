use std::fmt::Write;
use sumi_hir::{Analysis, Value};

pub fn source(shape: &str, width: usize, depth: usize) -> String {
    let mut source = String::from(if shape == "outlined" {
        "fn base(seed: int) -> int {\nlet x0 = seed\n"
    } else {
        "fn work(n: int, seed: int) -> int {\nlet x0 = seed\n"
    });
    for i in 1..=width {
        writeln!(source, "let x{i} = x{} + 1", i - 1).unwrap();
    }
    let base = if shape == "outlined" {
        write!(
            source,
            "x{width}\n}}\nfn work(n: int, seed: int) -> int {{\n"
        )
        .unwrap();
        "base(seed)".to_owned()
    } else {
        format!("x{width}")
    };
    let recurse = if shape == "tail" {
        "work(n - 1, seed + 1)"
    } else {
        "1 + work(n - 1, seed)"
    };
    write!(
        source,
        "if n <= 0 {{ {base} }} else {{ {recurse} }}\n}}\nfn main() -> int = work({depth}, 7)"
    )
    .unwrap();
    source
}

pub fn validate(analysis: &Analysis, width: usize, depth: usize) {
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    let program = analysis.program().unwrap();
    let main = program.function_named("main").unwrap();
    assert_eq!(
        program.machine(main, &[]).run(),
        Ok(Value::Int((width as i64 + depth as i64 + 7).into()))
    );
    assert_eq!(
        program.evaluate(main, &[]),
        Value::Int((width as i64 + depth as i64 + 7).into())
    );
}
