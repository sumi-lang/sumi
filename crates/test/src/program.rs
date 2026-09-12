//! A generator for well-formed programs: grammar-directed, with the spacing
//! and line-break rules built in, so the parser must accept every output.

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};

fn name() -> BoxedStrategy<String> {
    prop::sample::select(&["a", "b", "foo", "x1"][..])
        .prop_map(str::to_owned)
        .boxed()
}

fn literal() -> BoxedStrategy<String> {
    prop::sample::select(&["0", "42", "1000", "\"s\"", "true", "false"][..])
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

/// A parameter list on one line: names, each typed unless `inferred` lets
/// it go bare, with or without a trailing comma.
fn param_list(inferred: bool) -> BoxedStrategy<String> {
    (
        prop::collection::vec((name(), any::<bool>()), 0..3),
        any::<bool>(),
    )
        .prop_map(move |(params, trailing)| {
            let params: Vec<String> = params
                .into_iter()
                .map(|(param, typed)| {
                    if typed || !inferred {
                        format!("{param}: int")
                    } else {
                        param
                    }
                })
                .collect();
            let comma = if trailing && !params.is_empty() {
                ","
            } else {
                ""
            };
            format!("({}{comma})", params.join(", "))
        })
        .boxed()
}

/// What follows a parameter list, for items and closures alike: an
/// optional return type, then a block or `=` and an expression, and
/// whether it was the expression.
fn signature_tail(
    block: BoxedStrategy<String>,
    body: BoxedStrategy<String>,
) -> BoxedStrategy<(String, bool)> {
    let body = prop_oneof![
        2 => block.prop_map(|body| (format!(" {body}"), false)),
        1 => body.prop_map(|body| (format!(" = {body}"), true)),
    ];
    (any::<bool>(), body)
        .prop_map(|(returns, (body, bare))| {
            let returns = if returns { " -> int" } else { "" };
            (format!("{returns}{body}"), bare)
        })
        .boxed()
}

/// An expression that nothing follows: an initializer, a returned value,
/// or a body. Only there may a closure take an expression body bare, since
/// that body absorbs every operator and argument list after it.
fn tail_expr(expr: BoxedStrategy<String>) -> BoxedStrategy<String> {
    let closure =
        (param_list(true), any::<bool>(), expr.clone()).prop_map(|(params, returns, body)| {
            let returns = if returns { " -> int" } else { "" };
            format!("fn{params}{returns} = {body}")
        });
    prop_oneof![5 => expr, 1 => closure].boxed()
}

fn expr() -> BoxedStrategy<String> {
    let leaf = prop_oneof![name(), literal()];
    leaf.prop_recursive(3, 24, 3, |expr| {
        // An `else` takes a block or one more `if`, which takes no `else`
        // of its own: one link witnesses the chain.
        let otherwise = prop_oneof![
            2 => block(expr.clone()),
            1 => (expr.clone(), block(expr.clone()))
                .prop_map(|(condition, then)| format!("if {condition} {then}")),
        ];
        let atom = prop_oneof![
            4 => name(),
            4 => literal(),
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
            1 => (expr.clone(), block(expr.clone()), prop::option::of(otherwise))
                .prop_map(|(condition, then, otherwise)| match otherwise {
                    Some(otherwise) => format!("if {condition} {then} else {otherwise}"),
                    None => format!("if {condition} {then}"),
                }),
            1 => block(expr.clone()),
            // Where an operator may follow, an expression body is
            // parenthesized with its closure.
            1 => (param_list(true), signature_tail(block(expr.clone()), expr.clone()))
                .prop_map(|(params, (tail, bare))| {
                    if bare { format!("(fn{params}{tail})") } else { format!("fn{params}{tail}") }
                }),
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

/// A statement, and whether it is a bare expression. The generator uses
/// explicit discards outside tail position without relying on its type.
fn statement(expr: BoxedStrategy<String>) -> BoxedStrategy<(String, bool)> {
    prop_oneof![
        3 => expr.clone().prop_map(|e| (e, true)),
        2 => (any::<bool>(), name(), any::<bool>(), tail_expr(expr.clone())).prop_map(|(mutable, name, typed, init)| {
            let mutable = if mutable { "mut " } else { "" };
            let ty = if typed { ": int" } else { "" };
            (format!("let {mutable}{name}{ty} = {init}"), false)
        }),
        2 => (expr.clone(), expr.clone()).prop_map(|(target, value)| (format!("{target} = {value}"), false)),
        1 => tail_expr(expr.clone()).prop_map(|e| (format!("_ = {e}"), false)),
        1 => prop::option::of(tail_expr(expr)).prop_map(|value| match value {
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

/// A well-formed program: zero to three function items, each with typed
/// parameters.
pub fn program() -> BoxedStrategy<String> {
    let item = (
        name(),
        param_list(false),
        signature_tail(block(expr()), tail_expr(expr())),
    )
        .prop_map(|(name, params, (tail, _))| format!("fn {name}{params}{tail}"));
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
