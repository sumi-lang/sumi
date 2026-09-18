//! The analysis held to the machine. A generator draws programs the checker
//! should accept: scalar functions with typed parameters, guarded
//! divisions, and recursions that decrease a parameter under a bound. Each
//! accepted program runs on every live function at points inside the
//! parameter sets the analysis proved, and the run is checked against the
//! claims: the value lies in the result set, the call depth stays within
//! the bound, and no divisor is zero, which the machine refuses. A rejected
//! program only has to leave the checker standing. The check is
//! `sumi-test`'s, which the fuzz `run` target samples over arbitrary text.

use proptest::prelude::*;
use sumi_frontend::parse_source;
use sumi_hir::analyze;
use sumi_test::check;
use sumi_test::check::Runs;

/// xorshift64*: enough to draw a program from, and one word of state so a
/// failing seed names its program.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        // splitmix64 spreads the seed, so neighbouring seeds draw nothing
        // alike; the state only has to be nonzero.
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

    /// An integer in `lo..=hi`.
    fn between(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }

    /// True `num` times in `den`.
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

/// How a function recurses, if it does: its first parameter is `n`, its
/// body is `if n <= base { … } else { … }`, and the else arm calls
/// `callee` with `n - step` first.
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

/// One program's functions and the scope of the body being generated.
struct Gen<'a> {
    rng: Rng,
    functions: &'a [Signature],
    /// The function whose body is being generated.
    current: usize,
    /// Locals in scope, innermost last.
    scope: Vec<(String, Kind)>,
    fresh: usize,
    /// Inside the else arm of a recursive body: the call it must make, and
    /// whether `n` is known to be positive there.
    arm: Option<(Recursion, bool)>,
    /// Calls the else arm still owes: the recursion happens at least once.
    owed: bool,
    /// Recursive calls the arm has made: two per arm keeps a run a few
    /// thousand frames rather than exponential, and one where the call
    /// passes `n` along, since its partner's calls multiply with it.
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
        self.scope
            .iter()
            .filter(|(_, k)| *k == kind)
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// Functions the body may call freely: those declared before it, its
    /// recursion partner excluded, so the call graph is acyclic apart from
    /// the recursions the generator shapes.
    fn callable(&self, kind: Kind) -> Vec<usize> {
        let partner = self.functions[self.current]
            .recursion
            .map(|recursion| recursion.callee);
        (0..self.current)
            .filter(|&f| Some(f) != partner && self.functions[f].result == kind)
            .filter(|&f| {
                // A callee that recurses with this one must not be reached
                // by any other call.
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

    /// A leaf of `kind`: a literal, a local, or a call with leaf arguments.
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

    /// The call a recursive else arm makes: `n - step` first, then
    /// whatever the callee's other parameters take.
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

    /// A divisor the checker can see is not zero: a literal, or `n` inside a
    /// recursive arm whose bound keeps it positive.
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

    /// A division under a guard on a local: the guard holds where the
    /// division runs, or its negation does.
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
            // The guard narrows what the local is; a copy of it inside the
            // branch is the narrowed value.
            let copy = self.fresh(Kind::Int);
            self.scope.push((copy.clone(), Kind::Int));
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

    /// `division` combined into a larger expression, or as it is.
    fn int_after(&mut self, division: &str, fuel: u32) -> String {
        if self.rng.chance(1, 2) {
            let other = self.operand(Kind::Int, fuel);
            let op = self.rng.pick(&["+", "-", "*"]);
            format!("({division}) {op} {other}")
        } else {
            division.to_owned()
        }
    }

    /// An operand of a binary operator: a leaf, or a parenthesized
    /// expression, so precedence never surprises.
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

    /// A block of a few statements and a tail of `kind`: bindings, which
    /// shadow freely, discards, and an `if` without an else as a statement.
    fn block(&mut self, kind: Kind, fuel: u32) -> String {
        let depth = self.scope.len();
        let mut lines = Vec::new();
        for _ in 0..self.rng.between(1, 3) {
            let line = match self.rng.below(6) {
                0..=2 => {
                    let kind = if self.rng.chance(3, 4) {
                        Kind::Int
                    } else {
                        Kind::Bool
                    };
                    let value = self.expr(kind, fuel);
                    // Shadow a binding now and then, never a parameter: a
                    // recursion reads `n` as declared.
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
                    self.scope.push((name.clone(), kind));
                    format!("let {name} = {value}")
                }
                3 => {
                    let value = self.expr(Kind::Int, fuel);
                    format!("_ = {value}")
                }
                4 => {
                    let condition = self.bool(fuel);
                    let value = self.expr(Kind::Int, fuel);
                    format!("if {condition} {{ _ = {value} }}")
                }
                _ => {
                    let value = self.expr(Kind::Bool, fuel);
                    format!("_ = {value}")
                }
            };
            lines.push(line);
        }
        let tail = self.expr(kind, fuel);
        self.scope.truncate(depth);
        format!("{{\n{}\n{tail}\n}}", lines.join("\n"))
    }

    /// The body of the current function: a recursive shape or an
    /// expression, either as `= expr` or as a block.
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
                    // The arm never reached a call: make one its tail.
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

/// A program of two to six functions the checker should accept. Every
/// function is named `f` and its index; parameters are `n` first, then
/// `a`, `b`; the last function takes no parameters, so something runs.
fn program(seed: u64) -> String {
    let mut rng = Rng::new(seed);
    let count = rng.between(2, 6) as usize;
    let mut functions: Vec<Signature> = Vec::with_capacity(count);
    let mut index = 0;
    while index < count {
        let last = index + 1 == count;
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
                // One call of a pair may pass `n` along; the other decreases.
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
                body.scope.push((names[i].to_owned(), kind));
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

/// Run `source` inside what the analysis proved; `None` for a rejected
/// program.
fn check(source: &str) -> Option<Runs> {
    let analysis = analyze(parse_source(source.into()).unwrap());
    analysis.program().map(check::run)
}

/// Shrinking a seed draws an unrelated program, so none is attempted: a
/// failing seed already names its program.
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
        check(&program(seed));
    }
}

/// The generator earns its keep only while the checker accepts most of
/// what it draws and most runs end: a drop in either means the generator
/// or the analysis lost precision, or a recursion the checker accepted
/// never ends, and each is worth knowing.
#[test]
fn most_generated_programs_are_accepted_and_run_to_the_end() {
    let seeds = 400u64;
    let mut accepted = 0u64;
    let mut runs = Runs::default();
    for seed in 0..seeds {
        if let Some(outcome) = check(&program(seed)) {
            accepted += 1;
            runs.finished += outcome.finished;
            runs.abandoned += outcome.abandoned;
        }
    }
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
