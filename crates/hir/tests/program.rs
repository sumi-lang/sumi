//! A valid file as a program: what runs, what it computes, and what a run
//! costs, through the checker's proof and the graph's machine.

use sumi_frontend::parse_source;
use sumi_hir::{Analysis, Ty, Value, analyze};
use sumi_text::FileId;

fn analysis(source: &str) -> Analysis {
    analyze(parse_source(FileId::new(0), source.into()).unwrap())
}

fn int(value: i64) -> Value {
    Value::Int(value.into())
}

/// Run the nullary function `name` of `source`.
fn run(source: &str, name: &str) -> Value {
    let analysis = analysis(source);
    let program = analysis.program().expect("a valid file");
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
        assert!(analysis(source).program().is_none(), "{source}");
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
    // Truncating: the remainder takes the dividend's sign.
    assert_eq!(run(source, "remainder"), int(-1));
    assert_eq!(run(source, "quotient"), int(-3));
}

#[test]
fn locals_blocks_and_branches() {
    let source = "fn shadow(x: int) -> int {
    let y = x + 1
    let x = y * 2
    let y = { let x = x + 1\n x }
    x + y
}
fn entry() -> int = shadow(1)
fn branches(n: int) -> int = if n < 0 { -1 } else if n == 0 { 0 } else { 1 }
fn all() -> int = branches(-5) * 100 + branches(0) * 10 + branches(7)
fn no_else(b: bool) = if b { _ = 1 }
fn unit_if() = no_else(true)
fn empty() = {}";
    assert_eq!(run(source, "entry"), int(9));
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
    let program = analysis.program().unwrap();
    // Recursion consumes the machine's stack, never the host's, however
    // deep, and the analysis claimed exactly the depth the run reaches.
    let deep = program.function_named("deep").unwrap();
    assert_eq!(program.function(deep).depth_bound(), Some(60002));
    let mut machine = program.machine(deep, &[]);
    while !machine.step() {}
    assert_eq!(machine.outcome(), Some(&Ok(int(60000))));
    assert_eq!(machine.max_depth(), 60002);
    let shallow = program.function_named("shallow").unwrap();
    assert_eq!(program.function(shallow).depth_bound(), Some(2));
    let mut machine = program.machine(shallow, &[]);
    while !machine.step() {}
    assert_eq!(machine.outcome(), Some(&Ok(int(4))));
    assert_eq!(machine.max_depth(), 2);
}

/// A run computes what its result depends on: a discarded call is never
/// entered, and a `let` read twice is computed once.
#[test]
fn only_what_the_result_needs_is_computed() {
    let source = "fn costly(n: int) -> int = if n == 0 { 0 } else { costly(n - 1) }
fn dropped() -> int {
    _ = costly(100)
    1
}
fn shared() -> int {
    let x = costly(3)
    x + x
}";
    let analysis = analysis(source);
    let program = analysis.program().unwrap();
    let mut machine = program.machine(program.function_named("dropped").unwrap(), &[]);
    while !machine.step() {}
    assert_eq!(machine.outcome(), Some(&Ok(int(1))));
    assert_eq!(
        machine.max_depth(),
        1,
        "the discarded call is never entered"
    );
    let mut machine = program.machine(program.function_named("shared").unwrap(), &[]);
    while !machine.step() {}
    assert_eq!(machine.outcome(), Some(&Ok(int(0))));
    // Four frames of `costly` and the sum: the second read of `x` costs
    // nothing.
    assert_eq!(machine.max_depth(), 5);
    let once = machine.steps();
    let mut machine = program.machine(program.function_named("shared").unwrap(), &[]);
    while !machine.step() {}
    assert_eq!(machine.steps(), once);
}

#[test]
fn stepping_is_observable_and_idempotent_at_the_end() {
    let source = "fn twice(x: int) -> int = x * 2\nfn entry() -> int = twice(twice(1))";
    let analysis = analysis(source);
    let program = analysis.program().unwrap();
    let mut machine = program.machine(program.function_named("entry").unwrap(), &[]);
    assert_eq!(
        (machine.steps(), machine.depth(), machine.max_depth()),
        (0, 1, 1)
    );
    assert_eq!(machine.outcome(), None);
    let mut seen_depth_two = false;
    let mut values = Vec::new();
    while !machine.step() {
        seen_depth_two |= machine.depth() == 2;
        values.extend(machine.latest().cloned());
    }
    assert_eq!(machine.outcome(), Some(&Ok(int(4))));
    assert!(seen_depth_two);
    assert_eq!((machine.depth(), machine.max_depth()), (1, 2));
    // Every value the run made appeared once as it was made: the literal
    // 1; in the inner frame the literal 2, the product, and the declared
    // result's copy; the call's value; then the same three in the outer
    // frame, the call's value, and the entry's own copy.
    let trace = [1, 2, 2, 2, 2, 2, 4, 4, 4, 4].map(int);
    assert_eq!(values, trace);
    let steps = machine.steps();
    assert_eq!(steps, values.len() as u64);
    assert!(machine.step());
    assert_eq!(machine.steps(), steps);
    // Arguments reach parameters in order.
    let sub = program.function_named("twice").unwrap();
    assert_eq!(program.evaluate(sub, &[int(21)]), int(42));
}

#[test]
#[should_panic(expected = "arguments must match the signature")]
fn arguments_must_match_the_signature() {
    let analysis = analysis("fn f(x: int) -> int = x");
    let program = analysis.program().unwrap();
    program.machine(program.function_named("f").unwrap(), &[Value::Bool(true)]);
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

/// The proof is what makes a run whole: a `Program` is only had for a
/// valid file, and a machine on the bare graph of an invalid one refuses
/// what the checker would have caught.
#[test]
fn the_bare_graph_refuses_what_the_checker_rejects() {
    use sumi_hir::{FunctionId, Machine, Refusal};
    let rejected = analysis("fn f() -> int = 1 / 0");
    assert!(rejected.program().is_none());
    let machine = Machine::new(rejected.graph(), FunctionId::new(0), &[], None);
    assert!(matches!(machine.run(), Err(Refusal::Division(_))));
    let holed = analysis("fn f() -> int = missing");
    let machine = Machine::new(holed.graph(), FunctionId::new(0), &[], None);
    assert!(matches!(machine.run(), Err(Refusal::Hole(_))));
    let endless = analysis("fn f(n: int) -> int = f(n)\nfn g() -> int = f(1)");
    let machine = Machine::new(endless.graph(), FunctionId::new(1), &[], Some(4));
    assert!(matches!(machine.run(), Err(Refusal::Depth(_))));
    for source in [
        "fn f() -> int = if 1 { 2 } else { 3 }",
        "fn f() -> int = -true",
        "fn f() -> int = 1 + true",
        "fn f() -> bool = !1",
        "fn f() -> bool = true && 1",
        "fn f() -> bool = 1 == true",
    ] {
        let typed = analysis(source);
        assert!(typed.program().is_none(), "{source}");
        let machine = Machine::new(typed.graph(), FunctionId::new(0), &[], None);
        assert!(matches!(machine.run(), Err(Refusal::Type(_))), "{source}");
    }
}
