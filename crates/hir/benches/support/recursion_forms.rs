use sumi_hir::{Analysis, Value};

pub const SIZES: &[usize] = &[16, 128, 1024];
pub const SHAPES: &[&str] = &[
    "sum",
    "sum-accumulator",
    "sum-unroll4",
    "product",
    "product-accumulator",
    "generic-step",
    "specialized-step",
    "affine-closed",
    "known-int",
    "known-bool",
    "known-unit",
    "known-observed",
];

pub fn source(shape: &str, size: usize) -> String {
    let (body, call, ty) = match shape {
        "sum" => (
            "fn f(n: int) -> int = if n <= 0 { 0 } else { n + f(n - 1) }".into(),
            format!("f({size})"),
            "int",
        ),
        "sum-accumulator" => (
            "fn f(n: int, a: int) -> int = if n <= 0 { a } else { f(n - 1, a + n) }".into(),
            format!("f({size}, 0)"),
            "int",
        ),
        "sum-unroll4" => {
            let mut body = "f(n - 4)".to_owned();
            for offset in (0..4).rev() {
                body = format!("if n <= {offset} {{ 0 }} else {{ n - {offset} + ({body}) }}");
            }
            (format!("fn f(n: int) -> int = {body}"), format!("f({size})"), "int")
        }
        "product" => (
            "fn f(n: int) -> int = if n <= 0 { 1 } else { n * f(n - 1) }".into(),
            format!("f({size})"),
            "int",
        ),
        "product-accumulator" => (
            "fn f(n: int, a: int) -> int = if n <= 0 { a } else { f(n - 1, a * n) }".into(),
            format!("f({size}, 1)"),
            "int",
        ),
        "generic-step" => (
            "fn f(n: int, step: int, positive: bool) -> int = if n <= 0 { 7 } else { if positive { step + f(n - 1, step, positive) } else { -step + f(n - 1, step, positive) } }".into(),
            format!("f({size}, 3, true)"),
            "int",
        ),
        "specialized-step" => (
            "fn f(n: int) -> int = if n <= 0 { 7 } else { 3 + f(n - 1) }".into(),
            format!("f({size})"),
            "int",
        ),
        "affine-closed" => (
            "fn f(n: int) -> int = if n <= 0 { 7 } else { 7 + 3 * n }".into(),
            format!("f({size})"),
            "int",
        ),
        "known-int" => (
            "fn f(n: int) -> int = if n <= 0 { 7 } else { f(n - 1) }".into(),
            format!("f({size})"),
            "int",
        ),
        "known-bool" => (
            "fn f(n: int) -> bool = if n <= 0 { true } else { f(n - 1) }".into(),
            format!("f({size})"),
            "bool",
        ),
        "known-unit" => (
            "fn f(n: int) -> unit { if n > 0 { _ = f(n - 1) } }".into(),
            format!("f({size})"),
            "unit",
        ),
        "known-observed" => (
            "fn f(n: int) -> int = if n <= 0 { 7 } else { f(n - 1) }".into(),
            format!("{{ _ = f({size})\n 23 }}"),
            "int",
        ),
        _ => unreachable!(),
    };
    format!("{body}\nfn main() -> {ty} = {call}")
}

pub fn expected(shape: &str, size: usize) -> Value {
    match shape {
        "known-bool" => Value::Bool(true),
        "known-unit" => Value::Unit,
        "product" | "product-accumulator" => {
            let mut digits = vec![1_usize];
            for factor in 1..=size {
                let mut carry = 0;
                for digit in &mut digits {
                    let product = *digit * factor + carry;
                    *digit = product % 10;
                    carry = product / 10;
                }
                while carry != 0 {
                    digits.push(carry % 10);
                    carry /= 10;
                }
            }
            let decimal: String = digits
                .into_iter()
                .rev()
                .map(|digit| char::from(b'0' + digit as u8))
                .collect();
            Value::Int(decimal.parse().unwrap())
        }
        _ => Value::Int(
            match shape {
                "sum" | "sum-accumulator" | "sum-unroll4" => (size * (size + 1) / 2) as i64,
                "generic-step" | "specialized-step" | "affine-closed" => (3 * size + 7) as i64,
                "known-int" => 7,
                "known-observed" => 23,
                _ => unreachable!(),
            }
            .into(),
        ),
    }
}

pub fn evaluate(analysis: &Analysis) -> Value {
    let program = analysis.program().unwrap();
    program.evaluate(program.function_named("main").unwrap(), &[])
}

pub fn validate(shape: &str, size: usize, analysis: &Analysis) {
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    assert_eq!(evaluate(analysis), expected(shape, size));
}
