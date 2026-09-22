//! The analysis held to the machine: generated programs the checker should accept, run by
//! `check::run` inside the sets it proved and held to its claims. A rejected program only has to
//! not crash the checker.

use std::collections::HashSet;

use proptest::prelude::*;
use sumi_frontend::parse_source;
use sumi_hir::analyze;
use sumi_test::check;
use sumi_test::check::Runs;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        // The state must be nonzero: zero is xorshift's fixed point.
        let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        Self((z ^ (z >> 31)) | 1)
    }

    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: u64) -> u64 {
        (self.next() >> 33) % n
    }

    fn between(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }

    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len() as u64) as usize]
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Int,
    Bool,
}

#[derive(Clone, Copy)]
struct Recursion {
    callee: usize,
    base: i64,
    step: i64,
}

struct Signature {
    params: Vec<Kind>,
    result: Kind,
    recursion: Option<Recursion>,
}

struct Gen<'a> {
    rng: Rng,
    functions: &'a [Signature],
    current: usize,
    scope: Vec<(String, Kind, bool)>,
    fresh: usize,
    /// The bool is whether `n` is positive in that arm.
    arm: Option<(Recursion, bool)>,
    owed: bool,
    /// The cap is two per arm, one when the call passes `n` along; otherwise a run goes
    /// exponential.
    calls: u32,
}

const GUARDS_THEN: &[&str] = &[
    "{x} != 0",
    "0 != {x}",
    "!({x} == 0)",
    "{x} > 0",
    "{x} < 0",
    "{x} >= 1",
    "{x} <= -1",
    "1 <= {x}",
    "-1 >= {x}",
    "{x} != 0 && ({b})",
    "({b}) && {x} != 0",
    "!({x} == 0 || ({b}))",
];

const GUARDS_ELSE: &[&str] = &[
    "{x} == 0",
    "0 == {x}",
    "!({x} != 0)",
    "({x} == 0)",
    "!!({x} == 0)",
    "{x} == 0 || ({b})",
    "({b}) || {x} == 0",
    "!({x} != 0 && ({b}))",
];

impl Gen<'_> {
    fn fresh(&mut self, kind: Kind) -> String {
        let name = format!(
            "{}{}",
            if kind == Kind::Int { "v" } else { "p" },
            self.fresh
        );
        self.fresh += 1;
        name
    }

    fn locals(&self, kind: Kind) -> Vec<String> {
        let mut seen = HashSet::new();
        self.scope
            .iter()
            .rev()
            .filter(|(name, _, _)| seen.insert(name.as_str()))
            .filter(|(_, k, _)| *k == kind)
            .map(|(name, _, _)| name.clone())
            .collect()
    }

    fn mutable_locals(&self) -> Vec<(String, Kind)> {
        let mut seen = HashSet::new();
        self.scope
            .iter()
            .rev()
            .filter(|(name, _, _)| seen.insert(name.as_str()))
            .filter(|(_, _, mutable)| *mutable)
            .map(|(name, kind, _)| (name.clone(), *kind))
            .collect()
    }

    fn callable(&self, kind: Kind) -> Vec<usize> {
        let partner = self.functions[self.current]
            .recursion
            .map(|recursion| recursion.callee);
        (0..self.current)
            .filter(|&f| Some(f) != partner && self.functions[f].result == kind)
            .filter(|&f| {
                self.functions[f]
                    .recursion
                    .is_none_or(|recursion| recursion.callee != self.current)
            })
            .collect()
    }

    fn literal(&mut self, kind: Kind) -> String {
        match kind {
            Kind::Int => self.rng.between(-9, 9).to_string(),
            Kind::Bool => self.rng.pick(&["true", "false"]).to_string(),
        }
    }

    fn expr(&mut self, kind: Kind, fuel: u32) -> String {
        match kind {
            Kind::Int => self.int(fuel),
            Kind::Bool => self.bool(fuel),
        }
    }

    fn leaf(&mut self, kind: Kind) -> String {
        let locals = self.locals(kind);
        if !locals.is_empty() && self.rng.chance(1, 2) {
            return self.rng.pick(&locals).clone();
        }
        if self.rng.chance(1, 4) {
            let callable = self.callable(kind);
            if !callable.is_empty() {
                let callee = *self.rng.pick(&callable);
                return self.call(callee, 0);
            }
        }
        self.literal(kind)
    }

    fn call(&mut self, callee: usize, fuel: u32) -> String {
        let params = self.functions[callee].params.clone();
        let args: Vec<String> = params.iter().map(|&kind| self.expr(kind, fuel)).collect();
        format!("f{callee}({})", args.join(", "))
    }

    fn recursive_call(&mut self, recursion: Recursion, fuel: u32) -> String {
        self.owed = false;
        self.calls += 1;
        let params = self.functions[recursion.callee].params.clone();
        let first = if recursion.step == 0 {
            "n".to_owned()
        } else if self.rng.chance(1, 3) {
            format!("(n - {})", recursion.step)
        } else {
            format!("n - {}", recursion.step)
        };
        let mut args = vec![first];
        args.extend(params[1..].iter().map(|&kind| self.expr(kind, fuel)));
        format!("f{}({})", recursion.callee, args.join(", "))
    }

    fn nonzero(&mut self) -> String {
        if let Some((_, positive)) = self.arm
            && positive
            && self.rng.chance(1, 2)
        {
            return "n".to_owned();
        }
        let value = self.rng.between(1, 5);
        if self.rng.chance(1, 2) {
            format!("-{value}")
        } else {
            value.to_string()
        }
    }

    fn guarded(&mut self, fuel: u32) -> Option<String> {
        let locals = self.locals(Kind::Int);
        if locals.is_empty() {
            return None;
        }
        let x = self.rng.pick(&locals).clone();
        let then = self.rng.chance(2, 3);
        let guard = self
            .rng
            .pick(if then { GUARDS_THEN } else { GUARDS_ELSE })
            .to_string();
        let b = self.bool(fuel.saturating_sub(2));
        let guard = guard.replace("{x}", &x).replace("{b}", &b);
        let divisor = if self.rng.chance(1, 4) {
            let copy = self.fresh(Kind::Int);
            self.scope.push((copy.clone(), Kind::Int, false));
            Some((copy, x.clone()))
        } else {
            None
        };
        let op = self.rng.pick(&["/", "%"]).to_string();
        let dividend = self.operand(Kind::Int, fuel - 1);
        let division = match &divisor {
            Some((copy, _)) => format!("{dividend} {op} {copy}"),
            None => format!("{dividend} {op} {x}"),
        };
        let inside = match divisor {
            Some((copy, from)) => {
                let tail = self.int_after(&division, fuel - 1);
                self.scope.pop();
                format!("{{\nlet {copy} = {from}\n{tail}\n}}")
            }
            None => {
                let tail = self.int_after(&division, fuel - 1);
                format!("{{ {tail} }}")
            }
        };
        let other = self.int(fuel - 1);
        let other = format!("{{ {other} }}");
        Some(if then {
            format!("if {guard} {inside} else {other}")
        } else {
            format!("if {guard} {other} else {inside}")
        })
    }

    fn int_after(&mut self, division: &str, fuel: u32) -> String {
        if self.rng.chance(1, 2) {
            let other = self.operand(Kind::Int, fuel);
            let op = self.rng.pick(&["+", "-", "*"]);
            format!("({division}) {op} {other}")
        } else {
            division.to_owned()
        }
    }

    fn operand(&mut self, kind: Kind, fuel: u32) -> String {
        if fuel == 0 || self.rng.chance(1, 2) {
            self.leaf(kind)
        } else {
            format!("({})", self.expr(kind, fuel))
        }
    }

    fn int(&mut self, fuel: u32) -> String {
        if let Some((recursion, _)) = self.arm
            && self.functions[recursion.callee].result == Kind::Int
            && fuel > 0
            && self.calls < if recursion.step == 0 { 1 } else { 2 }
            && self.rng.chance(1, if self.owed { 3 } else { 4 })
        {
            let call = self.recursive_call(recursion, fuel - 1);
            return if self.rng.chance(1, 2) {
                call
            } else {
                let other = self.operand(Kind::Int, fuel - 1);
                let op = self.rng.pick(&["+", "-", "*"]);
                format!("{call} {op} {other}")
            };
        }
        if fuel == 0 {
            return self.leaf(Kind::Int);
        }
        match self.rng.below(10) {
            0 | 1 => {
                let lhs = self.operand(Kind::Int, fuel - 1);
                let rhs = self.operand(Kind::Int, fuel - 1);
                let op = self.rng.pick(&["+", "-", "*"]);
                format!("{lhs} {op} {rhs}")
            }
            2 => {
                let operand = self.operand(Kind::Int, fuel - 1);
                format!("-{operand}")
            }
            3 => {
                let condition = self.bool(fuel - 1);
                let then = self.int(fuel - 1);
                let otherwise = self.int(fuel - 1);
                format!("if {condition} {{ {then} }} else {{ {otherwise} }}")
            }
            4 => self.block(Kind::Int, fuel - 1),
            5 | 6 => self.guarded(fuel).unwrap_or_else(|| self.leaf(Kind::Int)),
            7 => {
                let dividend = self.operand(Kind::Int, fuel - 1);
                let divisor = self.nonzero();
                let op = self.rng.pick(&["/", "%"]);
                format!("{dividend} {op} {divisor}")
            }
            8 => {
                let callable = self.callable(Kind::Int);
                if callable.is_empty() {
                    self.leaf(Kind::Int)
                } else {
                    let callee = *self.rng.pick(&callable);
                    self.call(callee, fuel - 1)
                }
            }
            _ => self.leaf(Kind::Int),
        }
    }

    fn bool(&mut self, fuel: u32) -> String {
        if let Some((recursion, _)) = self.arm
            && self.functions[recursion.callee].result == Kind::Bool
            && fuel > 0
            && self.calls < if recursion.step == 0 { 1 } else { 2 }
            && self.rng.chance(1, if self.owed { 3 } else { 4 })
        {
            let call = self.recursive_call(recursion, fuel - 1);
            return if self.rng.chance(1, 2) {
                call
            } else {
                let other = self.operand(Kind::Bool, fuel - 1);
                let op = self.rng.pick(&["&&", "||", "==", "!="]);
                format!("{call} {op} {other}")
            };
        }
        if fuel == 0 {
            return self.leaf(Kind::Bool);
        }
        match self.rng.below(9) {
            0 | 1 => {
                let lhs = self.operand(Kind::Int, fuel - 1);
                let rhs = self.operand(Kind::Int, fuel - 1);
                let op = self.rng.pick(&["<", "<=", ">", ">=", "==", "!="]);
                format!("{lhs} {op} {rhs}")
            }
            2 => {
                let lhs = self.operand(Kind::Bool, fuel - 1);
                let rhs = self.operand(Kind::Bool, fuel - 1);
                let op = self.rng.pick(&["&&", "||", "==", "!="]);
                format!("{lhs} {op} {rhs}")
            }
            3 => {
                let operand = self.operand(Kind::Bool, fuel - 1);
                format!("!{operand}")
            }
            4 => {
                let condition = self.bool(fuel - 1);
                let then = self.bool(fuel - 1);
                let otherwise = self.bool(fuel - 1);
                format!("if {condition} {{ {then} }} else {{ {otherwise} }}")
            }
            5 => self.block(Kind::Bool, fuel - 1),
            6 => {
                let callable = self.callable(Kind::Bool);
                if callable.is_empty() {
                    self.leaf(Kind::Bool)
                } else {
                    let callee = *self.rng.pick(&callable);
                    self.call(callee, fuel - 1)
                }
            }
            _ => self.leaf(Kind::Bool),
        }
    }

    fn block(&mut self, kind: Kind, fuel: u32) -> String {
        let depth = self.scope.len();
        let mut lines = Vec::new();
        for _ in 0..self.rng.between(1, 3) {
            let line = match self.rng.below(11) {
                10 if fuel > 0 => {
                    let name = self.fresh(Kind::Int);
                    let start = self.rng.between(-2, 2);
                    let end = start + self.rng.between(-1, 3);
                    let scope = self.scope.len();
                    self.scope.push((name.clone(), Kind::Int, false));
                    let body = self.block(kind, fuel - 1);
                    self.scope.truncate(scope);
                    format!("for {name} in {start}..{end} {{ _ = {body} }}")
                }
                0..=2 => {
                    let kind = if self.rng.chance(3, 4) {
                        Kind::Int
                    } else {
                        Kind::Bool
                    };
                    let value = self.expr(kind, fuel);
                    // The recursive call refers to `n` literally; a shadowed local would break it.
                    let bindings: Vec<String> = self
                        .locals(kind)
                        .into_iter()
                        .filter(|name| name.starts_with(['v', 'p']))
                        .collect();
                    let name = if !bindings.is_empty() && self.rng.chance(1, 4) {
                        self.rng.pick(&bindings).clone()
                    } else {
                        self.fresh(kind)
                    };
                    let mutable = self.rng.chance(1, 3);
                    self.scope.push((name.clone(), kind, mutable));
                    format!("let {}{name} = {value}", if mutable { "mut " } else { "" })
                }
                3 => {
                    let value = self.expr(Kind::Int, fuel);
                    format!("_ = {value}")
                }
                4 => {
                    let condition = self.bool(fuel);
                    if self.rng.chance(1, 2) {
                        let result = self.functions[self.current].result;
                        let value = self.expr(result, fuel);
                        format!("if {condition} {{ return {value} }}")
                    } else {
                        let value = self.expr(Kind::Int, fuel);
                        format!("if {condition} {{ _ = {value} }}")
                    }
                }
                5 => {
                    let value = self.expr(Kind::Bool, fuel);
                    format!("_ = {value}")
                }
                6 => {
                    let result = self.functions[self.current].result;
                    let value = self.expr(result, fuel);
                    format!("return {value}")
                }
                7 => {
                    let locals = self.mutable_locals();
                    if let Some((name, kind)) =
                        (!locals.is_empty()).then(|| self.rng.pick(&locals).clone())
                    {
                        let value = self.expr(kind, fuel);
                        format!("{name} = {value}")
                    } else {
                        format!("_ = {}", self.expr(Kind::Int, fuel))
                    }
                }
                8 => {
                    let locals = self.mutable_locals();
                    if let Some((name, kind)) =
                        (!locals.is_empty()).then(|| self.rng.pick(&locals).clone())
                    {
                        let condition = self.bool(fuel);
                        let then = self.expr(kind, fuel);
                        let otherwise = self.expr(kind, fuel);
                        format!(
                            "_ = if {condition} {{ {name} = {then} }} else {{ {name} = {otherwise} }}"
                        )
                    } else {
                        format!("_ = {}", self.expr(Kind::Bool, fuel))
                    }
                }
                _ => {
                    let locals = self.mutable_locals();
                    if let Some((name, kind)) =
                        (!locals.is_empty()).then(|| self.rng.pick(&locals).clone())
                    {
                        let condition = self.bool(fuel);
                        let value = self.expr(kind, fuel);
                        format!("_ = {condition} && {{ {name} = {value}\ntrue }}")
                    } else {
                        format!("_ = {}", self.expr(Kind::Bool, fuel))
                    }
                }
            };
            lines.push(line);
        }
        let tail = self.expr(kind, fuel);
        self.scope.truncate(depth);
        format!("{{\n{}\n{tail}\n}}", lines.join("\n"))
    }

    fn body(&mut self) -> String {
        let signature = &self.functions[self.current];
        let result = signature.result;
        match signature.recursion {
            Some(recursion) => {
                let base = self.expr(result, 2);
                self.arm = Some((recursion, recursion.base >= 0));
                self.owed = true;
                self.calls = 0;
                let mut arm = self.expr(result, 3);
                if self.owed {
                    let call = self.recursive_call(recursion, 1);
                    arm = format!("{{\nlet r0 = {call}\n{arm}\n}}");
                }
                self.arm = None;
                format!(
                    " = if n <= {} {{ {base} }} else {{ {arm} }}",
                    recursion.base
                )
            }
            None => {
                if self.rng.chance(1, 2) {
                    let body = self.expr(result, 3);
                    format!(" = {body}")
                } else {
                    let body = self.block(result, 2);
                    format!(" {body}")
                }
            }
        }
    }
}

fn program(seed: u64) -> String {
    let mut rng = Rng::new(seed);
    let count = rng.between(2, 6) as usize;
    let mut functions: Vec<Signature> = Vec::with_capacity(count);
    let mut index = 0;
    while index < count {
        let last = index + 1 == count;
        // The last function takes no parameters, so it is live and runs even when no call reaches
        // the others.
        let arity = if last { 0 } else { rng.between(0, 2) as usize };
        let params: Vec<Kind> = (0..arity)
            .map(|i| {
                if i == 0 || rng.chance(4, 5) {
                    Kind::Int
                } else {
                    Kind::Bool
                }
            })
            .collect();
        let result = if rng.chance(1, 4) {
            Kind::Bool
        } else {
            Kind::Int
        };
        let mutual = arity > 0 && index + 2 < count && rng.chance(1, 5);
        let recursion = if mutual {
            Some(Recursion {
                callee: index + 1,
                base: rng.between(-2, 3),
                step: if rng.chance(1, 3) {
                    0
                } else {
                    rng.between(1, 3)
                },
            })
        } else if arity > 0 && rng.chance(1, 3) {
            Some(Recursion {
                callee: index,
                base: rng.between(-2, 3),
                step: rng.between(1, 3),
            })
        } else {
            None
        };
        functions.push(Signature {
            params,
            result,
            recursion,
        });
        index += 1;
        if mutual {
            let partner_arity = rng.between(1, 2) as usize;
            let params: Vec<Kind> = (0..partner_arity)
                .map(|i| {
                    if i == 0 || rng.chance(4, 5) {
                        Kind::Int
                    } else {
                        Kind::Bool
                    }
                })
                .collect();
            let result = if rng.chance(1, 4) {
                Kind::Bool
            } else {
                Kind::Int
            };
            functions.push(Signature {
                params,
                result,
                recursion: Some(Recursion {
                    callee: index - 1,
                    base: rng.between(-2, 3),
                    step: rng.between(1, 3),
                }),
            });
            index += 1;
        }
    }
    let mut text = String::new();
    for current in 0..functions.len() {
        let signature = &functions[current];
        let mut body = Gen {
            rng: Rng::new(rng.next()),
            functions: &functions,
            current,
            scope: Vec::new(),
            fresh: 0,
            arm: None,
            owed: false,
            calls: 0,
        };
        let names = ["n", "a", "b"];
        let params: Vec<String> = signature
            .params
            .iter()
            .enumerate()
            .map(|(i, &kind)| {
                body.scope.push((names[i].to_owned(), kind, false));
                format!(
                    "{}: {}",
                    names[i],
                    if kind == Kind::Int { "int" } else { "bool" }
                )
            })
            .collect();
        let result = if signature.result == Kind::Int {
            "int"
        } else {
            "bool"
        };
        let body = body.body();
        text.push_str(&format!(
            "fn f{current}({}) -> {result}{body}\n",
            params.join(", ")
        ));
    }
    text
}

fn runs_of(source: &str) -> Option<Runs> {
    let analysis = std::panic::catch_unwind(|| analyze(parse_source(source.into()).unwrap()))
        .unwrap_or_else(|_| panic!("analysis panicked for:\n{source}"));
    analysis.program().map(check::run)
}

/// No shrinking: a shrunk seed draws an unrelated program.
fn config() -> ProptestConfig {
    ProptestConfig {
        cases: 256,
        max_shrink_iters: 0,
        ..sumi_test::regressions!("machine.txt")
    }
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn accepted_programs_run_within_their_claims(seed in any::<u64>()) {
        runs_of(&program(seed));
    }

    #[test]
    fn counted_loops_match_the_reference(
        start in -4i64..6,
        end in -4i64..6,
        a in -9i64..10,
        b in -9i64..10,
        stop in -4i64..6,
        early in any::<bool>(),
    ) {
        let source = format!("fn id(x: int) -> int = x
fn main() -> int {{
    let mut a = {a}
    let mut b = {b}
    let mut end = {end}
    let mut total = 3
    for i in {start}..end {{
        let old = a
        a = b
        b = id(old + i)
        end = end + 1
        for j in -2..i {{ total = total + a * 7 + b + j }}
        if {early} && i == {stop} {{ return total - 1000 }}
    }}
    total + a * 100 + b * 10 + end
}}");
        let (mut ra, mut rb, mut bound, mut total) = (a, b, end, 3);
        let mut returned = None;
        for i in start..end {
            (ra, rb) = (rb, ra + i);
            bound += 1;
            for j in -2..i {
                total += ra * 7 + rb + j;
            }
            if early && i == stop {
                returned = Some(total - 1000);
                break;
            }
        }
        let expected = sumi_hir::Value::Int(returned.unwrap_or(total + ra * 100 + rb * 10 + bound).into());
        let analysis = analyze(parse_source(source.clone().into()).unwrap());
        prop_assert!(analysis.is_valid(), "{}\n{:?}", source, analysis.diagnostics());
        check::semantics(&analysis);
        let program = analysis.program().unwrap();
        let main = program.function_named("main").unwrap();
        let runs = check::run(program);
        prop_assert_eq!(runs.abandoned, 0);
        prop_assert_eq!(program.machine(main, &[]).run(), Ok(expected.clone()), "{}", source);
        prop_assert_eq!(program.evaluate(main, &[]), expected, "{}", source);
    }
}

#[test]
fn discarded_loops_evaluate_both_bounds_once() {
    for (start, end) in [(101, 103), (107, 107), (113, 109)] {
        let source = format!("fn main() -> int {{ for i in {start}..{end} {{}}\n 42 }}");
        let analysis = analyze(parse_source(source.into()).unwrap());
        assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
        let program = analysis.program().unwrap();
        let mut machine = program.machine(program.function_named("main").unwrap(), &[]);
        let mut bounds = Vec::new();
        while machine.step().is_none() {
            if let Some(sumi_hir::Value::Int(value)) = machine.latest()
                && (*value == start.into() || *value == end.into())
            {
                bounds.push(value.clone());
            }
        }
        assert_eq!(
            machine.outcome(),
            Some(&Ok(sumi_hir::Value::Int(42.into())))
        );
        assert_eq!(bounds, [start.into(), end.into()], "{start}..{end}");
    }
}

#[test]
fn start_bound_is_evaluated_before_a_returning_end() {
    let source = "fn main() -> int { for i in 101..{ return 42 } {} }";
    let analysis = analyze(parse_source(source.into()).unwrap());
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    let program = analysis.program().unwrap();
    let mut machine = program.machine(program.function_named("main").unwrap(), &[]);
    let mut values = Vec::new();
    while machine.step().is_none() {
        values.extend(machine.latest().cloned());
    }
    assert_eq!(
        machine.outcome(),
        Some(&Ok(sumi_hir::Value::Int(42.into())))
    );
    assert_eq!(values.first(), Some(&sumi_hir::Value::Int(101.into())));
    assert_eq!(
        values
            .iter()
            .filter(|value| **value == sumi_hir::Value::Int(101.into()))
            .count(),
        1
    );
}

#[test]
fn execution_budget_bounds_loops_with_memoized_bodies() {
    let analysis = analyze(
        parse_source(
            "fn main() { let u = {}\n for i in 0..100000000000000000000 { u }\n {} }".into(),
        )
        .unwrap(),
    );
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    let runs = check::run(analysis.program().unwrap());
    assert_eq!(runs.finished, 0);
    assert_eq!(runs.abandoned, 1);
}

#[test]
fn most_generated_programs_are_accepted_and_run_to_the_end() {
    let seeds = 400u64;
    let mut accepted = 0u64;
    let mut returning = 0usize;
    let mut mutating = 0usize;
    let mut looping = 0usize;
    let mut runs = Runs::default();
    for seed in 0..seeds {
        let source = program(seed);
        let source_returns = source.matches("return ").count();
        if let Some(outcome) = runs_of(&source) {
            accepted += 1;
            returning += usize::from(source_returns != 0 && outcome.finished != 0);
            looping += usize::from(source.contains("for ") && outcome.finished != 0);
            mutating += usize::from(
                source.contains("let mut ")
                    && source.lines().any(|line| {
                        let line = line.trim_start();
                        line.starts_with(['v', 'p']) && line.contains(" = ")
                    })
                    && outcome.finished != 0,
            );
            runs.finished += outcome.finished;
            runs.abandoned += outcome.abandoned;
        }
    }
    assert_ne!(
        returning, 0,
        "no accepted return-bearing program ran to the end"
    );
    assert_ne!(
        mutating, 0,
        "no accepted mutation-bearing program ran to the end"
    );
    assert_ne!(
        looping, 0,
        "no accepted loop-bearing program ran to the end"
    );
    assert!(
        accepted * 10 >= seeds * 9,
        "only {accepted} of {seeds} generated programs were accepted"
    );
    assert!(
        runs.abandoned * 50 <= runs.finished,
        "{} of {} runs were abandoned",
        runs.abandoned,
        runs.finished + runs.abandoned
    );
}
