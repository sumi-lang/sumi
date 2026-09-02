//! A generator for well-formed programs: grammar-directed, with the spacing
//! and line-break rules built in, so the parser must accept every output.

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};

fn name() -> BoxedStrategy<String> {
    prop::sample::select(&["a", "b", "foo", "x1", "Δ"][..])
        .prop_map(str::to_owned)
        .boxed()
}

fn literal() -> BoxedStrategy<String> {
    prop::sample::select(
        &[
            "0", "42", "1_000", "1.5", "2.5e-3", "\"s\"", "'c'", "r\"a\"", "true", "false",
        ][..],
    )
    .prop_map(str::to_owned)
    .boxed()
}

/// A binary operator applied left to right over `operands`, spaced, with
/// each operator either on the line or leading the next one.
fn chain(
    operand: BoxedStrategy<String>,
    ops: &'static [&'static str],
    max: usize,
) -> BoxedStrategy<String> {
    (
        operand.clone(),
        prop::collection::vec((prop::sample::select(ops), any::<bool>(), operand), 0..max),
    )
        .prop_map(|(first, rest)| {
            let mut text = first;
            for (op, leading, operand) in rest {
                text.push_str(if leading { "\n  " } else { " " });
                text.push_str(op);
                text.push(' ');
                text.push_str(&operand);
            }
            text
        })
        .boxed()
}

/// An expression that fits in a hole of a string literal: on one line, so
/// it never reaches the hole's end.
fn hole_expr() -> BoxedStrategy<String> {
    prop_oneof![
        3 => name(),
        2 => literal(),
        1 => (name(), name()).prop_map(|(callee, arg)| format!("{callee}({arg})")),
        1 => (name(), literal()).prop_map(|(a, b)| format!("{a} + {b}")),
        1 => name().prop_map(|n| format!("\"{{{n}}}\"")),
    ]
    .boxed()
}

/// A string literal with holes, `"…"` or `"""`, around expressions that
/// stay on their line.
fn string_with_holes() -> BoxedStrategy<String> {
    prop_oneof![
        3 => (hole_expr(), prop::option::of(hole_expr())).prop_map(|(first, second)| match second {
            Some(second) => format!("\"{{{first}}} and {{{second}}}\""),
            None => format!("\"a {{{first}}} b\""),
        }),
        1 => hole_expr().prop_map(|e| format!("\"\"\"\n  line {{{e}}}\n  \"\"\"")),
    ]
    .boxed()
}

fn expr() -> BoxedStrategy<String> {
    let leaf = prop_oneof![name(), literal()];
    leaf.prop_recursive(3, 24, 3, |expr| {
        let atom = prop_oneof![
            4 => name(),
            4 => literal(),
            1 => string_with_holes(),
            1 => expr.clone().prop_map(|e| format!("({e})")),
            1 => (name(), prop::collection::vec(expr.clone(), 0..3), any::<bool>(), any::<bool>())
                .prop_map(|(callee, args, trailing, multiline)| {
                    let comma = if trailing && !args.is_empty() { "," } else { "" };
                    if multiline && !args.is_empty() {
                        format!("{callee}(\n  {}{comma}\n)", args.join(",\n  "))
                    } else {
                        format!("{callee}({}{comma})", args.join(", "))
                    }
                }),
            1 => (expr.clone(), block(expr.clone()), prop::option::of(block(expr.clone())))
                .prop_map(|(condition, then, otherwise)| match otherwise {
                    Some(otherwise) => format!("if {condition} {then} else {otherwise}"),
                    None => format!("if {condition} {then}"),
                }),
            1 => block(expr.clone()),
        ]
        .boxed();
        // Prefix operators are glued to their operand.
        let unary = prop_oneof![
            6 => atom.clone(),
            1 => (prop::sample::select(&["-", "!"][..]), atom).prop_map(|(op, e)| format!("{op}{e}")),
        ]
        .boxed();
        // At most one operator per tier: five tiers already compound, and
        // program size is what generation time and shrinking scale with —
        // three operands per tier made the average program 6 KB.
        let product = chain(unary, &["*", "/", "%"], 2);
        let sum = chain(product, &["+", "-"], 2);
        // Comparisons never chain.
        let comparison = chain(sum, &["==", "!=", "<", "<=", ">", ">="], 2);
        let conjunction = chain(comparison, &["&&"], 2);
        chain(conjunction, &["||"], 2)
    })
    .boxed()
}

/// A statement, and whether it is a bare expression, which may only end
/// its block: before another statement its value would go nowhere, which
/// is an error.
fn statement(expr: BoxedStrategy<String>) -> BoxedStrategy<(String, bool)> {
    prop_oneof![
        3 => expr.clone().prop_map(|e| (e, true)),
        2 => (any::<bool>(), name(), any::<bool>(), expr.clone()).prop_map(|(mutable, name, typed, init)| {
            let mutable = if mutable { "mut " } else { "" };
            let ty = if typed { ": int" } else { "" };
            (format!("let {mutable}{name}{ty} = {init}"), false)
        }),
        2 => (expr.clone(), expr.clone()).prop_map(|(target, value)| (format!("{target} = {value}"), false)),
        1 => expr.clone().prop_map(|e| (format!("_ = {e}"), false)),
        1 => prop::option::of(expr).prop_map(|value| match value {
            Some(value) => (format!("return {value}"), false),
            None => ("return".to_owned(), false),
        }),
    ]
    .boxed()
}

/// A block: one statement per line, or a single expression on the braces'
/// line, or nothing. A bare expression before another statement is
/// discarded explicitly, so the block stays well-formed.
fn block(expr: BoxedStrategy<String>) -> BoxedStrategy<String> {
    prop_oneof![
        1 => Just("{}".to_owned()),
        2 => expr.clone().prop_map(|e| format!("{{ {e} }}")),
        3 => prop::collection::vec((statement(expr), any::<bool>()), 1..4).prop_map(|statements| {
            let last = statements.len() - 1;
            let lines: Vec<String> = statements
                .into_iter()
                .enumerate()
                .map(|(index, ((statement, bare), comment))| {
                    let statement = if bare && index < last { format!("_ = {statement}") } else { statement };
                    if comment { format!("{statement} // c") } else { statement }
                })
                .collect();
            format!("{{\n{}\n}}", lines.join("\n"))
        }),
    ]
    .boxed()
}

/// A well-formed program: zero to three function items.
pub fn program() -> BoxedStrategy<String> {
    let item = (
        name(),
        prop::collection::vec(name(), 0..3),
        any::<bool>(),
        any::<bool>(),
        block(expr()),
    )
        .prop_map(|(name, params, trailing, returns, body)| {
            let params: Vec<String> = params.into_iter().map(|p| format!("{p}: int")).collect();
            let comma = if trailing && !params.is_empty() {
                ","
            } else {
                ""
            };
            let returns = if returns { " -> int" } else { "" };
            format!("fn {name}({}{comma}){returns} {body}", params.join(", "))
        });
    (any::<bool>(), prop::collection::vec(item, 0..3))
        .prop_map(|(comment, items)| {
            let mut text = if comment {
                "// file\n".to_owned()
            } else {
                String::new()
            };
            text.push_str(&items.join("\n\n"));
            text.push('\n');
            text
        })
        .boxed()
}

/// A deterministic, endless sequence of programs drawn from [`program`],
/// for harnesses that need seeded values outside a proptest runner.
pub struct Programs {
    strategy: BoxedStrategy<String>,
    runner: TestRunner,
}

impl Programs {
    pub fn new(seed: u64) -> Self {
        let mut bytes = [0u8; 32];
        bytes[..8].copy_from_slice(&seed.to_le_bytes());
        Self {
            strategy: program(),
            runner: TestRunner::new_with_rng(
                Config::default(),
                TestRng::from_seed(RngAlgorithm::ChaCha, &bytes),
            ),
        }
    }
}

impl Iterator for Programs {
    type Item = String;

    fn next(&mut self) -> Option<String> {
        Some(
            self.strategy
                .new_tree(&mut self.runner)
                .expect("program generation never rejects")
                .current(),
        )
    }
}
