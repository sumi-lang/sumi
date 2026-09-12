use super::*;
use sumi_frontend::{FileId, parse_source};
use sumi_hir::analyze;

fn analysis(source: &str) -> Analysis {
    analyze(parse_source(FileId::new(0), source.into()).unwrap())
}

/// Run the nullary function `name` of `source`.
fn run(source: &str, name: &str) -> Result<Value, Trap> {
    let analysis = analysis(source);
    let program = Program::new(&analysis).expect("a valid file");
    program.evaluate(program.function_named(name).expect("a function"), &[])
}

/// A trap's kind and the source text at its origin.
fn trap_of(source: &str, result: Result<Value, Trap>) -> (TrapKind, &str) {
    let trap = result.expect_err("a trap");
    let range = trap.origin.range();
    (
        trap.kind,
        &source[range.start().to_usize()..range.end().to_usize()],
    )
}

#[test]
fn invalid_files_never_run() {
    for source in ["fn f() -> int = true", "fn f(", "fn f() = g()"] {
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
    assert_eq!(run(source, "arithmetic"), Ok(Value::Int(8)));
    assert_eq!(run(source, "negated"), Ok(Value::Int(3)));
    assert_eq!(run(source, "logic"), Ok(Value::Bool(true)));
    assert_eq!(run(source, "bools"), Ok(Value::Bool(true)));
    assert_eq!(run(source, "nothing"), Ok(Value::Unit));
    // Truncating division; the remainder takes the dividend's sign.
    assert_eq!(run(source, "remainder"), Ok(Value::Int(-1)));
    assert_eq!(run(source, "quotient"), Ok(Value::Int(-3)));
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
    assert_eq!(run(source, "entry"), Ok(Value::Int(2)));
    assert_eq!(run(source, "all"), Ok(Value::Int(-99)));
    assert_eq!(run(source, "unit_if"), Ok(Value::Unit));
    assert_eq!(run(source, "empty"), Ok(Value::Unit));
}

#[test]
fn calls_recursion_and_evaluation_order() {
    let source = "fn fib(n: int) -> int = if n < 2 { n } else { fib(n - 1) + fib(n - 2) }
fn twenty() -> int = fib(20)
fn sub(a: int, b: int) -> int = a - b
fn ordered() -> int = sub(sub(10, 3), sub(2, 1))
fn args_left_first() -> int = sub(1 / 0, 9223372036854775807 + 1)
fn operands_left_first() -> int = (1 % 0) + (9223372036854775807 * 2)
fn args_before_the_call() -> int = sub(9223372036854775807 + 1, forever(0))
fn forever(n: int) -> int = forever(n + 1)
fn even(n: int) -> bool = if n == 0 { true } else { odd(n - 1) }
fn odd(n: int) -> bool = if n == 0 { false } else { even(n - 1) }
fn parity() -> bool = even(1000) && !even(999)";
    assert_eq!(run(source, "twenty"), Ok(Value::Int(6765)));
    assert_eq!(run(source, "ordered"), Ok(Value::Int(6)));
    // Competing traps: the left one happens, so the right one never does.
    assert_eq!(
        trap_of(source, run(source, "args_left_first")),
        (TrapKind::DivisionByZero, "1 / 0")
    );
    assert_eq!(
        trap_of(source, run(source, "operands_left_first")),
        (TrapKind::DivisionByZero, "1 % 0")
    );
    assert_eq!(
        trap_of(source, run(source, "args_before_the_call")),
        (TrapKind::Overflow, "9223372036854775807 + 1")
    );
    assert_eq!(run(source, "parity"), Ok(Value::Bool(true)));
}

#[test]
fn short_circuits_skip_traps() {
    let source = "fn safe() -> bool = false && (1 / 0 == 0) || true || (1 % 0 == 0)
fn unsafe_and() -> bool = true && 1 / 0 == 0
fn unsafe_or() -> bool = false || 1 % 0 == 0";
    assert_eq!(run(source, "safe"), Ok(Value::Bool(true)));
    assert_eq!(
        trap_of(source, run(source, "unsafe_and")),
        (TrapKind::DivisionByZero, "1 / 0")
    );
    assert_eq!(
        trap_of(source, run(source, "unsafe_or")),
        (TrapKind::DivisionByZero, "1 % 0")
    );
}

#[test]
fn arithmetic_traps_locate_the_operation() {
    let max = i64::MAX;
    let min = i64::MIN;
    let source = format!(
        "fn add() -> int = {max} + 1
fn sub() -> int = -{max} - 2
fn mul() -> int = {max} * 2
fn neg() -> int = --{min}
fn div() -> int = {min} / -1
fn rem() -> int = {min} % -1
fn div_zero() -> int = 1 / (1 - 1)
fn rem_zero() -> int = 1 % 0
fn fine() -> int = {max} + -1 + 1"
    );
    let source = source.as_str();
    assert_eq!(run(source, "fine"), Ok(Value::Int(max)));
    for (name, kind, origin) in [
        ("add", TrapKind::Overflow, format!("{max} + 1")),
        ("sub", TrapKind::Overflow, format!("-{max} - 2")),
        ("mul", TrapKind::Overflow, format!("{max} * 2")),
        // The literal already is the minimum; the inner negation overflows.
        ("neg", TrapKind::Overflow, format!("-{min}")),
        ("div", TrapKind::Overflow, format!("{min} / -1")),
        ("rem", TrapKind::Overflow, format!("{min} % -1")),
        (
            "div_zero",
            TrapKind::DivisionByZero,
            "1 / (1 - 1)".to_owned(),
        ),
        ("rem_zero", TrapKind::DivisionByZero, "1 % 0".to_owned()),
    ] {
        let result = run(source, name);
        assert_eq!(trap_of(source, result), (kind, origin.as_str()), "{name}");
        assert_eq!(result.unwrap_err().to_string(), kind.message());
    }
}

#[test]
fn call_depth_is_bounded_by_the_machine_not_the_host() {
    let source = "fn forever(n: int) -> int = forever(n + 1)
fn entry() -> int = forever(0)
fn count(n: int) -> int = if n == 0 { 0 } else { 1 + count(n - 1) }
fn deep() -> int = count(60000)";
    let trap = run(source, "entry").expect_err("a depth trap");
    assert_eq!(trap.kind, TrapKind::CallDepth);
    // The call that would nest too deep, inside `forever`.
    let range = trap.origin.range();
    assert_eq!(
        &source[range.start().to_usize()..range.end().to_usize()],
        "forever(n + 1)"
    );
    // Recursion short of the limit completes, however deep.
    assert_eq!(run(source, "deep"), Ok(Value::Int(60000)));
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
    let outcome = loop {
        if let Some(outcome) = machine.step() {
            break outcome;
        }
        seen_depth_two |= machine.depth() == 2;
    };
    assert_eq!(outcome, Ok(Value::Int(4)));
    assert!(seen_depth_two);
    assert_eq!((machine.depth(), machine.max_depth()), (0, 2));
    let steps = machine.steps();
    assert!(steps > 0);
    assert_eq!(machine.step(), Some(Ok(Value::Int(4))));
    assert_eq!(machine.steps(), steps);
    // Arguments reach parameters in order.
    let sub = program.function_named("twice").unwrap();
    assert_eq!(program.evaluate(sub, &[Value::Int(21)]), Ok(Value::Int(42)));
}

#[test]
fn a_trapped_machine_keeps_reporting_its_trap() {
    let source = "fn boom() -> int = inner(1) + 2\nfn inner(x: int) -> int = x / 0";
    let analysis = analysis(source);
    let program = Program::new(&analysis).unwrap();
    let mut machine = Machine::new(program, program.function_named("boom").unwrap(), &[]);
    let outcome = machine.run_to_end();
    assert_eq!(
        trap_of(source, outcome),
        (TrapKind::DivisionByZero, "x / 0")
    );
    let steps = machine.steps();
    for _ in 0..3 {
        assert_eq!(machine.step(), Some(outcome));
    }
    assert_eq!(machine.steps(), steps);
    // The frames stay where the trap happened.
    assert_eq!(machine.depth(), 2);
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
    assert_eq!(Value::Int(-7).to_string(), "-7");
    assert_eq!(Value::Bool(true).to_string(), "true");
    assert_eq!(Value::Unit.to_string(), "unit");
    assert_eq!(Value::Unit.ty(), Ty::Unit);
    assert_eq!(TrapKind::CallDepth.code(), "eval/call-depth");
}

impl Machine<'_> {
    /// Step in place until the run ends, keeping the machine.
    fn run_to_end(&mut self) -> Result<Value, Trap> {
        loop {
            if let Some(outcome) = self.step() {
                return outcome;
            }
        }
    }
}
