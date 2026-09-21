use std::fmt::Write;
use sumi_hir::{Analysis, Bools, Value};

pub const SHAPES: &[&str] = &["int", "bool", "unit", "large-int", "varying"];
pub const WIDTHS: &[usize] = &[0, 256, 8192];

pub fn source(shape: &str, width: usize) -> String {
    let (ty, result) = match shape {
        "int" => ("int", "7"),
        "bool" => ("bool", "true"),
        "unit" => ("unit", "{}"),
        "large-int" => ("int", "9223372036854775808"),
        "varying" => ("int", "if b { 11 } else { 29 }"),
        _ => unreachable!(),
    };
    let mut source = format!("fn entry(b: bool) -> {ty} {{\n");
    for i in 0..width {
        writeln!(source, "let x{i} = {i}").unwrap();
    }
    write!(
        source,
        "{result}\n}}\nfn yes() -> {ty} = entry(true)\nfn no() -> {ty} = entry(false)"
    )
    .unwrap();
    source
}

pub fn expected(shape: &str, b: bool) -> Value {
    match shape {
        "int" => Value::Int(7.into()),
        "bool" => Value::Bool(true),
        "unit" => Value::Unit,
        "large-int" => Value::Int("9223372036854775808".parse().unwrap()),
        "varying" => Value::Int((if b { 11 } else { 29 }).into()),
        _ => unreachable!(),
    }
}

pub fn validate(shape: &str, analysis: &Analysis) {
    let program = analysis.program().unwrap();
    let entry = program.function_named("entry").unwrap();
    assert_eq!(program.ranges(entry).params[0].bools, Bools::BOTH);
    for b in [false, true] {
        let args = [Value::Bool(b)];
        assert_eq!(program.evaluate(entry, &args), expected(shape, b));
        assert_eq!(program.machine(entry, &args).run(), Ok(expected(shape, b)));
    }
}
