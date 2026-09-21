use sumi_frontend::{ParsedSource, parse_source};
use sumi_hir::{Analysis, Value};

pub const CASES: &[(&str, &str, i64)] = &[
    ("fibonacci", include_str!("programs/fibonacci.sumi"), 6765),
    ("sum", include_str!("programs/sum.sumi"), 20100),
    ("gcd", include_str!("programs/gcd.sumi"), 21),
    ("mutation", include_str!("programs/mutation.sumi"), 5050),
    (
        "short-circuit",
        include_str!("programs/short-circuit.sumi"),
        100,
    ),
    ("big-int", include_str!("programs/big-int.sumi"), 100),
];

pub fn parse(source: &str) -> ParsedSource {
    parse_source(source.into()).unwrap()
}

pub fn validate(analysis: &Analysis, expected: i64) {
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    let program = analysis.program().unwrap();
    let main = program.function_named("main").unwrap();
    assert_eq!(program.evaluate(main, &[]), Value::Int(expected.into()));
}
