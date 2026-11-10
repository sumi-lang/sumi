//! Generated programs; the parser accepts every output with no evidence.

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};

fn name() -> BoxedStrategy<String> {
    prop::sample::select(&["a", "b", "foo", "x1"][..])
        .prop_map(str::to_owned)
        .boxed()
}

fn literal() -> BoxedStrategy<String> {
    prop::sample::select(&["0", "42", "1000", "true", "false"][..])
        .prop_map(str::to_owned)
        .boxed()
}

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

/// A type list, or nothing: `elements` between `<` and `>`, the last with a comma when `trailing`.
fn type_list(elements: BoxedStrategy<String>) -> BoxedStrategy<String> {
    prop::option::of((prop::collection::vec(elements, 0..3), any::<bool>()))
        .prop_map(|list| match list {
            Some((elements, trailing)) => {
                let comma = if trailing && !elements.is_empty() {
                    ","
                } else {
                    ""
                };
                format!("<{}{comma}>", elements.join(", "))
            }
            None => String::new(),
        })
        .boxed()
}

fn type_params() -> BoxedStrategy<String> {
    type_list(
        prop::sample::select(&["T", "U"][..])
            .prop_map(str::to_owned)
            .boxed(),
    )
}

fn type_item() -> BoxedStrategy<String> {
    let field = (name(), type_text()).prop_map(|(name, ty)| format!("{name}: {ty}"));
    (
        (prop::sample::select(&["P", "Q"][..]), type_params())
            .prop_map(|(name, params)| format!("{name}{params}")),
        prop::collection::vec(field, 0..3),
        any::<bool>(),
        any::<bool>(),
    )
        .prop_map(|(name, fields, trailing, multiline)| {
            let comma = if trailing && !fields.is_empty() {
                ","
            } else {
                ""
            };
            if fields.is_empty() {
                format!("type {name} {{}}")
            } else if multiline {
                format!("type {name} {{\n  {}{comma}\n}}", fields.join(",\n  "))
            } else {
                format!("type {name} {{ {}{comma} }}", fields.join(", "))
            }
        })
        .boxed()
}

fn type_text() -> BoxedStrategy<String> {
    prop::sample::select(
        &[
            "int",
            "bool",
            "P",
            "T",
            "P | Q",
            "P | Q | int",
            "P<int>",
            "Q<T, bool,>",
            "P<> | Q<P<U> | Q>",
        ][..],
    )
    .prop_map(str::to_owned)
    .boxed()
}

fn param_list() -> BoxedStrategy<String> {
    (
        prop::collection::vec((any::<bool>(), name(), type_text()), 0..3),
        any::<bool>(),
    )
        .prop_map(move |(params, trailing)| {
            let params: Vec<String> = params
                .into_iter()
                .map(|(mutable, param, ty)| {
                    let mutable = if mutable { "mut " } else { "" };
                    format!("{mutable}{param}: {ty}")
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

fn signature_tail(
    block: BoxedStrategy<String>,
    body: BoxedStrategy<String>,
) -> BoxedStrategy<(String, bool)> {
    let body = prop_oneof![
        2 => block.prop_map(|body| (format!(" {body}"), false)),
        1 => body.prop_map(|body| (format!(" = {body}"), true)),
    ];
    (prop::option::of(type_text()), body)
        .prop_map(|(returns, (body, bare))| {
            let returns = returns.map_or(String::new(), |ty| format!(" -> {ty}"));
            (format!("{returns}{body}"), bare)
        })
        .boxed()
}

fn expr() -> BoxedStrategy<String> {
    let leaf = prop_oneof![name(), literal()];
    leaf.prop_recursive(3, 24, 3, |expr| {
        let otherwise = prop_oneof![
            2 => block(expr.clone()),
            1 => (expr.clone(), block(expr.clone()))
                .prop_map(|(condition, then)| format!("if {condition} {then}")),
        ];
        let atom = prop_oneof![
            4 => name(),
            4 => literal(),
            1 => expr.clone().prop_map(|e| format!("({e})")),
            2 => (
                (name(), type_list(type_text()))
                    .prop_map(|(callee, type_args)| format!("{callee}{type_args}")),
                prop::collection::vec(
                    (prop::option::of(name()), any::<bool>(), expr.clone()),
                    0..3,
                ),
                any::<bool>(),
                any::<bool>(),
            )
                .prop_map(|(callee, args, trailing, multiline)| {
                    let args: Vec<String> = args
                        .into_iter()
                        .map(|(label, mutable, value)| {
                            let mutable = if mutable { "mut " } else { "" };
                            match label {
                                Some(label) => format!("{label}: {mutable}{value}"),
                                None => format!("{mutable}{value}"),
                            }
                        })
                        .collect();
                    let comma = if trailing && !args.is_empty() { "," } else { "" };
                    if multiline && !args.is_empty() {
                        format!("{callee}(\n  {}{comma}\n)", args.join(",\n  "))
                    } else {
                        format!("{callee}({}{comma})", args.join(", "))
                    }
                }),
            1 => (name(), prop::collection::vec(name(), 1..3))
                .prop_map(|(base, fields)| format!("{base}.{}", fields.join("."))),
            2 => (
                expr.clone(),
                prop::collection::vec(
                    (
                        (prop::sample::select(&["P", "Q"][..]), type_list(type_text()))
                            .prop_map(|(member, type_args)| format!("{member}{type_args}")),
                        prop::option::of(name()),
                        expr.clone(),
                    ),
                    0..3,
                ),
                prop::option::of(expr.clone()),
                any::<bool>(),
                any::<bool>(),
            )
                .prop_map(|(scrutinee, arms, rest, trailing, multiline)| {
                    let mut arms: Vec<String> = arms
                        .into_iter()
                        .map(|(member, binding, value)| match binding {
                            Some(binding) => format!("{member}({binding}) => {value}"),
                            None => format!("{member} => {value}"),
                        })
                        .collect();
                    if let Some(rest) = rest {
                        arms.push(format!("_ => {rest}"));
                    }
                    let comma = if trailing && !arms.is_empty() { "," } else { "" };
                    if arms.is_empty() {
                        format!("match {scrutinee} {{}}")
                    } else if multiline {
                        format!("match {scrutinee} {{\n  {}{comma}\n}}", arms.join(",\n  "))
                    } else {
                        format!("match {scrutinee} {{ {}{comma} }}", arms.join(", "))
                    }
                }),
            1 => (expr.clone(), block(expr.clone()), prop::option::of(otherwise))
                .prop_map(|(condition, then, otherwise)| match otherwise {
                    Some(otherwise) => format!("if {condition} {then} else {otherwise}"),
                    None => format!("if {condition} {then}"),
                }),
            2 => (name(), expr.clone(), expr.clone(), block(expr.clone()))
                .prop_map(|(name, start, end, body)| format!("for {name} in {start}..{end} {body}")),
            1 => block(expr.clone()),
        ]
        .boxed();
        let unary = prop_oneof![
            6 => atom.clone(),
            1 => (prop::sample::select(&["-", "!"][..]), atom).prop_map(|(op, e)| format!("{op}{e}")),
        ]
        .boxed();
        let product = chain(unary.clone(), &["*", "/", "%"], 2);
        let sum = chain(product, &["+", "-"], 2);
        // A chained comparison is a parse violation.
        let comparison = chain(sum, &["==", "!=", "<", "<=", ">", ">="], 2);
        let conjunction = chain(comparison, &["&&"], 2);
        prop_oneof![unary, chain(conjunction, &["||"], 2)].boxed()
    })
    .boxed()
}

fn statement(expr: BoxedStrategy<String>) -> BoxedStrategy<(String, bool)> {
    prop_oneof![
        3 => expr.clone().prop_map(|e| (e, true)),
        2 => (any::<bool>(), name(), prop::option::of(type_text()), expr.clone()).prop_map(|(mutable, name, typed, init)| {
            let mutable = if mutable { "mut " } else { "" };
            let ty = typed.map_or(String::new(), |ty| format!(": {ty}"));
            (format!("let {mutable}{name}{ty} = {init}"), false)
        }),
        2 => (
            expr.clone(),
            prop::sample::select(&["=", "+=", "-=", "*=", "/=", "%="][..]),
            expr.clone(),
        )
            .prop_map(|(target, op, value)| (format!("{target} {op} {value}"), false)),
        1 => expr.clone().prop_map(|e| (format!("_ = {e}"), false)),
        1 => prop::option::of(expr).prop_map(|value| match value {
            Some(value) => (format!("return {value}"), false),
            None => ("return".to_owned(), false),
        }),
    ]
    .boxed()
}

/// A bare value before the last statement is `unused-value`; it is discarded.
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

pub fn program() -> BoxedStrategy<String> {
    let function = (
        name(),
        type_params(),
        param_list(),
        signature_tail(block(expr()), expr()),
    )
        .prop_map(|(name, type_params, params, (tail, _))| {
            format!("fn {name}{type_params}{params}{tail}")
        });
    let item = prop_oneof![3 => function, 1 => type_item()];
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

/// Programs from [`program`], seeded; the iterator never ends.
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
