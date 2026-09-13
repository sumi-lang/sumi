use super::*;
use sumi_frontend::{FileId, parse_source};
use sumi_hir::analyze;

fn analysis(source: &str) -> Analysis {
    analyze(parse_source(FileId::new(0), source.into()).unwrap())
}

fn int(value: i64) -> Value {
    Value::Int(value.into())
}

/// Run the nullary function `name` of `source`.
fn run(source: &str, name: &str) -> Value {
    let analysis = analysis(source);
    let program = Program::new(&analysis).expect("a valid file");
    program.evaluate(program.function_named(name).expect("a function"), &[])
}

#[test]
fn invalid_files_never_run() {
    for source in [
        "fn f() -> int = true",
        "fn f(",
        "fn f() = g()",
        // What used to trap is a static error, so it never reaches here.
        "fn f() -> int = 1 / 0",
        "fn f() -> int = 7 % (2 - 2)",
        "fn f() -> int = f()",
        "fn f(n: int) -> int = f(n + 1)\nfn g() -> int = f(0)",
        "fn f() -> bool = true && 1 / 0 == 0",
        "fn f() -> bool = false || 1 % 0 == 0",
    ] {
        assert!(Program::new(&analysis(source)).is_none(), "{source}");
    }
}

#[test]
fn scalars_and_operators() {
    let source = "fn arithmetic() -> int = (1 + 2) * 3 - 10 / 3 % 2
fn negated() -> int = -(-3)
fn logic() -> bool = !(1 < 2 && 2 <= 2 && 3 > 2 && 3 >= 3) || true == !false && 1 != 2
fn bools() -> bool = true == true && !(false != false)
fn nothing() = {}
fn remainder() -> int = -7 % 3
fn quotient() -> int = -7 / 2";
    assert_eq!(run(source, "arithmetic"), int(8));
    assert_eq!(run(source, "negated"), int(3));
    assert_eq!(run(source, "logic"), Value::Bool(true));
    assert_eq!(run(source, "bools"), Value::Bool(true));
    assert_eq!(run(source, "nothing"), Value::Unit);
    // Truncating division; the remainder takes the dividend's sign.
    assert_eq!(run(source, "remainder"), int(-1));
    assert_eq!(run(source, "quotient"), int(-3));
}

#[test]
fn locals_blocks_and_branches() {
    let source = "fn shadow(x: int) -> int {
    let x = x + 1
    {
        let x = x * 2
        _ = x
    }
    x
}
fn entry() -> int = shadow(1)
fn branches(n: int) -> int = if n < 0 { -1 } else if n == 0 { 0 } else { 1 }
fn all() -> int = branches(-5) * 100 + branches(0) * 10 + branches(7)
fn no_else(b: bool) = if b { _ = 1 }
fn unit_if() = no_else(true)
fn empty() = {}";
    assert_eq!(run(source, "entry"), int(2));
    assert_eq!(run(source, "all"), int(-99));
    assert_eq!(run(source, "unit_if"), Value::Unit);
    assert_eq!(run(source, "empty"), Value::Unit);
}

#[test]
fn calls_and_recursion() {
    let source = "fn fib(n: int) -> int = if n < 2 { n } else { fib(n - 1) + fib(n - 2) }
fn twenty() -> int = fib(20)
fn sub(a: int, b: int) -> int = a - b
fn ordered() -> int = sub(sub(10, 3), sub(2, 1))
fn even(n: int) -> bool = if n == 0 { true } else { odd(n - 1) }
fn odd(n: int) -> bool = if n == 0 { false } else { even(n - 1) }
fn parity() -> bool = even(1000) && !even(999)";
    assert_eq!(run(source, "twenty"), int(6765));
    assert_eq!(run(source, "ordered"), int(6));
    assert_eq!(run(source, "parity"), Value::Bool(true));
}

#[test]
fn guarded_divisions_run() {
    let source = "fn safe(n: int, d: int) -> int = if d != 0 { n / d } else { 0 }
fn signed() -> int = safe(10, 3) + safe(10, -3) + safe(10, 0)
fn dead() -> int = if false { 1 / 0 } else { 1 }
fn lazy() -> bool = false && 1 / 0 == 0 || true || 1 % 0 == 0";
    assert_eq!(run(source, "signed"), int(0));
    assert_eq!(run(source, "dead"), int(1));
    assert_eq!(run(source, "lazy"), Value::Bool(true));
}

#[test]
fn integers_have_no_width() {
    let max = i64::MAX;
    let min = i64::MIN;
    let source = format!(
        "fn add() -> int = {max} + 1
fn sub() -> int = -{max} - 2
fn mul() -> int = {max} * 2
fn neg() -> int = -{min}
fn div() -> int = {min} / -1
fn rem() -> int = {min} % -1
fn back() -> int = ({max} + 1) - 1
fn wide() -> int = 1234567890123456789012345678901234567890 * -1000000000000000000000
fn narrow() -> int = 1234567890123456789012345678901234567890 / 1000000000000000000000
fn fine() -> int = {max} + -1 + 1"
    );
    let source = source.as_str();
    for (name, value) in [
        ("add", "9223372036854775808"),
        ("sub", "-9223372036854775809"),
        ("mul", "18446744073709551614"),
        ("neg", "9223372036854775808"),
        ("div", "9223372036854775808"),
        ("rem", "0"),
        ("back", "9223372036854775807"),
        (
            "wide",
            "-1234567890123456789012345678901234567890000000000000000000000",
        ),
        ("narrow", "1234567890123456789"),
        ("fine", "9223372036854775807"),
    ] {
        assert_eq!(
            run(source, name),
            Value::Int(value.parse().unwrap()),
            "{name}"
        );
    }
}

#[test]
fn call_depth_is_the_machines_and_the_analysis_bounds_it() {
    let source = "fn count(n: int) -> int = if n == 0 { 0 } else { 1 + count(n - 1) }
fn deep() -> int = count(60000)
fn twice(x: int) -> int = x * 2
fn shallow() -> int = twice(twice(1))";
    let analysis = analysis(source);
    let program = Program::new(&analysis).unwrap();
    // Recursion consumes the machine's stack, never the host's, however
    // deep, and the analysis claimed exactly the depth the run reaches.
    let mut machine = Machine::new(program, program.function_named("deep").unwrap(), &[]);
    assert_eq!(machine.depth_bound(), Some(60002));
    let value = machine.run_to_end();
    assert_eq!(value, int(60000));
    assert_eq!(machine.max_depth(), 60002);
    let mut machine = Machine::new(program, program.function_named("shallow").unwrap(), &[]);
    assert_eq!(machine.depth_bound(), Some(2));
    assert_eq!(machine.run_to_end(), int(4));
    assert_eq!(machine.max_depth(), 2);
}

#[test]
fn stepping_is_observable_and_idempotent_at_the_end() {
    let source = "fn twice(x: int) -> int = x * 2\nfn entry() -> int = twice(twice(1))";
    let analysis = analysis(source);
    let program = Program::new(&analysis).unwrap();
    let mut machine = Machine::new(program, program.function_named("entry").unwrap(), &[]);
    assert_eq!(
        (machine.steps(), machine.depth(), machine.max_depth()),
        (0, 1, 1)
    );
    let mut seen_depth_two = false;
    let value = loop {
        if let Some(value) = machine.step() {
            break value;
        }
        seen_depth_two |= machine.depth() == 2;
    };
    assert_eq!(value, int(4));
    assert!(seen_depth_two);
    assert_eq!((machine.depth(), machine.max_depth()), (0, 2));
    let steps = machine.steps();
    assert!(steps > 0);
    assert_eq!(machine.step(), Some(int(4)));
    assert_eq!(machine.steps(), steps);
    // Arguments reach parameters in order.
    let sub = program.function_named("twice").unwrap();
    assert_eq!(program.evaluate(sub, &[int(21)]), int(42));
}

#[test]
#[should_panic(expected = "arguments must match the signature")]
fn arguments_must_match_the_signature() {
    let analysis = analysis("fn f(x: int) -> int = x");
    let program = Program::new(&analysis).unwrap();
    Machine::new(
        program,
        program.function_named("f").unwrap(),
        &[Value::Bool(true)],
    );
}

#[test]
fn values_display_as_source_spells_them() {
    assert_eq!(int(-7).to_string(), "-7");
    assert_eq!(
        Value::Int("-9223372036854775809".parse().unwrap()).to_string(),
        "-9223372036854775809"
    );
    assert_eq!(Value::Bool(true).to_string(), "true");
    assert_eq!(Value::Unit.to_string(), "unit");
    assert_eq!(Value::Unit.ty(), Ty::Unit);
}

impl Machine<'_> {
    /// Step in place until the run ends, keeping the machine.
    fn run_to_end(&mut self) -> Value {
        loop {
            if let Some(value) = self.step() {
                return value;
            }
        }
    }
}
