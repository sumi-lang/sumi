//! Property tests: cook and ParserInput invariants over generated sources
//! instead of the hand-written corpus in `cook.rs` and `input.rs`.

mod common;

use std::collections::HashSet;

use proptest::prelude::*;
use sumi_lexer::{LexedFile, RawKind, lex};
use sumi_syntax::{CookedFile, NodeKind, Parse, ParserInput, SyntaxKind, SyntaxTree, cook, parse};

/// Source fragments, valid and pathological; concatenation composes the
/// adjacencies goldens cannot enumerate.
const FRAGMENTS: &[&str] = &[
    "fn",
    "let",
    "if",
    "else",
    "return",
    "true",
    "false",
    "mut",
    "x",
    "foo",
    "_",
    "Δx",
    "0",
    "123",
    "1_000",
    "1.5",
    "2.5e-3",
    "1e",
    "1e+05",
    "0123",
    "1u32",
    "0x1F",
    "\"abc\"",
    "\"a\\nb\"",
    "\"a\nb\"",
    "\"open",
    "'a'",
    "'ab'",
    "r\"a\"",
    "r##\"a\"#",
    "(",
    ")",
    "{",
    "}",
    ",",
    ":",
    ".",
    "=",
    "<",
    ">",
    "!",
    "+",
    "-",
    "*",
    "/",
    "%",
    "&",
    "|",
    ";",
    "[",
    " ",
    "\t",
    "\n",
    "\r\n",
    "\r",
    "// c",
    "/// d",
    "\u{feff}",
    "€",
];

/// Fragments free of `)` and `}` (each would close the wrapping paren), of
/// `{` (it would restore termination), and of a lone `(` (it would take
/// the wrapping paren's closer, leaving the wrapper unclosed and suspending
/// nothing) — nested parens come closed — for
/// [`newlines_inside_parens_never_terminate`].
const PAREN_SAFE: &[&str] = &[
    "fn", "let", "if", "else", "return", "true", "x", "foo", "0", "1.5", "2.5e-3", "1e", "\"s\"",
    "'a'", "r\"a\"", "(x)", "(\nx\n)", ",", ":", ".", "=", "<", ">", "!", "+", "-", "*", "/", "%",
    "&", "|", " ", "\t", "\n", "\r\n", "// c\n",
];

fn fragment() -> impl Strategy<Value = String> {
    prop_oneof![
        9 => prop::sample::select(FRAGMENTS).prop_map(str::to_owned),
        1 => proptest::collection::vec(any::<char>(), 0..4)
            .prop_map(|chars| chars.into_iter().collect::<String>()),
    ]
}

fn soup() -> impl Strategy<Value = String> {
    proptest::collection::vec(fragment(), 0..64).prop_map(|fragments| fragments.concat())
}

fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
    )
}

proptest! {
    #[test]
    fn cook_is_total_and_one_to_one(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let cooked = cook(&source, &lexed);
        prop_assert_eq!(cooked.len(), lexed.len(), "cooking must stay 1:1");

        for error in cooked.errors() {
            prop_assert!((error.token as usize) < cooked.len());
            // Diagnostic ownership does not overlap: a token the lexer
            // reported gets no further errors from the cook.
            prop_assert!(
                !lexed.errors().iter().any(|lex_error| lex_error.token == error.token),
                "token {} has both a lex and a cook error", error.token
            );
        }

        // The parser handles `Error` tokens silently because an earlier
        // phase owns their diagnostics, so every one must have that evidence.
        for index in 0..cooked.len() {
            if cooked.kind(index) == SyntaxKind::Error {
                let token = index as u32;
                prop_assert!(
                    lexed.errors().iter().any(|error| error.token == token)
                        || cooked.errors().iter().any(|error| error.token == token),
                    "error token {} has no lex or cook error", token
                );
            }
        }
    }

    #[test]
    fn parser_input_invariants(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let cooked = cook(&source, &lexed);
        let input = ParserInput::new(&cooked);

        prop_assert!(input.len() <= cooked.len());
        prop_assert_eq!(input.get(input.len()), None);

        let mut previous: Option<usize> = None;
        let mut open: Vec<usize> = Vec::new();
        for index in 0..input.len() {
            let token = input.token(index) as usize;
            let kind = input.get(index).expect("indices below len are present");
            if let Some(previous) = previous {
                prop_assert!(previous < token, "token mappings must strictly increase");
            }
            prop_assert_eq!(kind, cooked.kind(token), "kinds must come from the cook");
            prop_assert!(!is_trivia(kind), "token {} is trivia", index);

            // Everything skipped between kept tokens must be trivia, and the
            // newline fact must match what was skipped.
            let skipped = previous.map_or(0, |previous| previous + 1)..token;
            let newline = skipped.clone().any(|j| cooked.kind(j) == SyntaxKind::Newline);
            for j in skipped {
                prop_assert!(is_trivia(cooked.kind(j)), "token {} was dropped", j);
            }
            prop_assert_eq!(input.newline_before(index), newline);

            // Jointness is adjacency, checked through ranges rather than
            // token indices.
            if index + 1 < input.len() {
                let next = input.token(index + 1) as usize;
                let adjacent = lexed.range(token).end() == lexed.range(next).start();
                prop_assert_eq!(input.is_joint(index), adjacent);
            } else {
                prop_assert!(!input.is_joint(index));
            }

            if input.boundary_before(index) {
                prop_assert!(index > 0, "no boundary before the first token");
                prop_assert!(input.newline_before(index), "boundaries need a newline");
            }

            // Partners are mutual, of matching kinds, and nest: an opener
            // whose partner lies ahead is pushed, and a closer must close
            // the innermost open pair.
            if let Some(partner) = input.partner(index) {
                prop_assert!(partner < input.len());
                prop_assert_eq!(input.partner(partner), Some(index), "partners must be mutual");
                let (opener, closer) = if index < partner { (index, partner) } else { (partner, index) };
                prop_assert!(
                    matches!(
                        (input.get(opener), input.get(closer)),
                        (Some(SyntaxKind::LParen), Some(SyntaxKind::RParen))
                            | (Some(SyntaxKind::LBrace), Some(SyntaxKind::RBrace))
                    ),
                    "tokens {} and {} are partners but not a matching pair", opener, closer
                );
                if partner > index {
                    open.push(index);
                } else {
                    prop_assert_eq!(open.pop(), Some(partner), "pairs must nest");
                }
            }
            previous = Some(token);
        }
        prop_assert!(open.is_empty(), "every pushed opener must have been closed");

        // Nothing significant may be dropped after the last kept token.
        for j in previous.map_or(0, |previous| previous + 1)..cooked.len() {
            prop_assert!(is_trivia(cooked.kind(j)), "token {} was dropped", j);
        }
    }

    #[test]
    fn widening_space_runs_changes_nothing(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let mut widened = String::new();
        for index in 0..lexed.len() {
            widened.push_str(lexed.text(&source, index));
            if lexed.kind(index) == RawKind::HorizontalSpace {
                widened.push(' ');
            }
        }

        // Widening an existing space run merges back into the same token, so
        // everything but the ranges is untouched: kinds, jointness, newline
        // facts, and boundaries.
        let widened_lexed = lex(&widened).expect("widened sources fit in u32");
        prop_assert_eq!(widened_lexed.len(), lexed.len());

        let cooked = cook(&source, &lexed);
        let widened_cooked = cook(&widened, &widened_lexed);
        for index in 0..cooked.len() {
            prop_assert_eq!(cooked.kind(index), widened_cooked.kind(index));
        }

        let input = ParserInput::new(&cooked);
        let widened_input = ParserInput::new(&widened_cooked);
        prop_assert_eq!(input.len(), widened_input.len());
        for index in 0..input.len() {
            prop_assert_eq!(input.token(index), widened_input.token(index));
            prop_assert_eq!(input.is_joint(index), widened_input.is_joint(index));
            prop_assert_eq!(input.newline_before(index), widened_input.newline_before(index));
            prop_assert_eq!(input.boundary_before(index), widened_input.boundary_before(index));
        }
    }

    #[test]
    fn newlines_inside_parens_never_terminate(
        pieces in proptest::collection::vec(
            prop::sample::select(PAREN_SAFE).prop_map(str::to_owned),
            0..32,
        ),
    ) {
        let source = format!("f({})", pieces.concat());
        let lexed = lex(&source).expect("generated sources fit in u32");
        let input = ParserInput::new(&cook(&source, &lexed));
        // Pieces can form a `//` that hides the wrapping paren's closer;
        // only a `(` the stream closes suspends termination.
        prop_assume!(input.partner(1) == Some(input.len() - 1));
        for index in 0..input.len() {
            prop_assert!(
                !input.boundary_before(index),
                "boundary before token {} in {:?}", index, source
            );
        }
    }
}

/// Walk `tree` and check every structural invariant: extents partition the
/// nodes; children are ordered, disjoint, and inside their parent; every
/// node but the root covers at least one token and starts and ends on a
/// significant one; the root covers the whole buffer.
fn check_tree(tree: &SyntaxTree, cooked: &sumi_syntax::CookedFile) -> Result<(), TestCaseError> {
    let raw_len = cooked.len() as u32;
    prop_assert_eq!(tree.kind(0), NodeKind::SourceFile);
    prop_assert_eq!((tree.first_token(0), tree.end_token(0)), (0, raw_len));

    let mut visited = 0usize;
    let mut pending = vec![0usize];
    while let Some(node) = pending.pop() {
        visited += 1;
        let (first, end) = (tree.first_token(node), tree.end_token(node));
        if node != 0 {
            prop_assert!(first < end, "node {} is empty", node);
            prop_assert!(
                !is_trivia(cooked.kind(first as usize)),
                "node {} starts on trivia",
                node
            );
            prop_assert!(
                !is_trivia(cooked.kind(end as usize - 1)),
                "node {} ends on trivia",
                node
            );
        }
        let mut previous_end = first;
        for child in tree.children(node) {
            prop_assert!(
                tree.first_token(child) >= previous_end,
                "children of {} overlap",
                node
            );
            prop_assert!(
                tree.end_token(child) <= end,
                "child {} escapes {}",
                child,
                node
            );
            previous_end = tree.end_token(child);
            pending.push(child);
        }
    }
    prop_assert_eq!(visited, tree.len(), "extents must partition the tree");
    Ok(())
}

proptest! {
    #[test]
    fn parse_is_total_and_trees_are_well_formed(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let cooked = cook(&source, &lexed);
        let input = ParserInput::new(&cooked);
        let parse = parse(&input);
        let tree = parse.tree();
        check_tree(tree, &cooked)?;

        // The parser attaches no token to the root itself: every significant
        // token lies in some item or top-level error node.
        let mut children = tree.children(0).peekable();
        for index in 0..input.len() {
            let token = input.token(index);
            while children.peek().is_some_and(|&child| tree.end_token(child) <= token) {
                children.next();
            }
            prop_assert!(
                children.peek().is_some_and(|&child| tree.first_token(child) <= token),
                "token {} is attached to the root", token
            );
        }

        // Errors sit in range, in source order, at most one per position,
        // and never on a token with no meaning, whose report the lexer or
        // cook owns. (A malformed literal keeps its kind and may carry both a
        // cook error and a structural one: independent problems.)
        let mut previous: Option<u32> = None;
        for error in parse.errors() {
            prop_assert!(error.token <= cooked.len() as u32);
            if let Some(previous) = previous {
                prop_assert!(previous < error.token, "errors must strictly advance");
            }
            if (error.token as usize) < cooked.len() {
                prop_assert_ne!(cooked.kind(error.token as usize), SyntaxKind::Error);
            }
            previous = Some(error.token);
        }
    }

    #[test]
    fn well_formed_programs_parse_without_errors(source in program()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        prop_assert!(lexed.errors().is_empty(), "lexer errors in {:?}", source);
        let cooked = cook(&source, &lexed);
        prop_assert!(cooked.errors().is_empty(), "cook errors in {:?}", source);
        let parse = parse(&ParserInput::new(&cooked));
        check_tree(parse.tree(), &cooked)?;
        prop_assert!(
            parse.errors().is_empty(),
            "parse errors {:?} in {:?}", parse.errors(), source
        );
    }
}

// A generator for well-formed programs: grammar-directed, with the spacing
// and line-break rules built in, so the parser must accept every output.

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

fn expr() -> BoxedStrategy<String> {
    let leaf = prop_oneof![name(), literal()];
    leaf.prop_recursive(3, 24, 3, |expr| {
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

fn statement(expr: BoxedStrategy<String>) -> BoxedStrategy<String> {
    prop_oneof![
        3 => expr.clone(),
        2 => (any::<bool>(), name(), any::<bool>(), expr.clone()).prop_map(|(mutable, name, typed, init)| {
            let mutable = if mutable { "mut " } else { "" };
            let ty = if typed { ": int" } else { "" };
            format!("let {mutable}{name}{ty} = {init}")
        }),
        1 => expr.clone().prop_map(|e| format!("_ = {e}")),
        1 => prop::option::of(expr).prop_map(|value| match value {
            Some(value) => format!("return {value}"),
            None => "return".to_owned(),
        }),
    ]
    .boxed()
}

/// A block: one statement per line, or a single expression on the braces'
/// line, or nothing.
fn block(expr: BoxedStrategy<String>) -> BoxedStrategy<String> {
    prop_oneof![
        1 => Just("{}".to_owned()),
        2 => expr.clone().prop_map(|e| format!("{{ {e} }}")),
        3 => prop::collection::vec((statement(expr), any::<bool>()), 1..4).prop_map(|statements| {
            let lines: Vec<String> = statements
                .into_iter()
                .map(|(statement, comment)| if comment { format!("{statement} // c") } else { statement })
                .collect();
            format!("{{\n{}\n}}", lines.join("\n"))
        }),
    ]
    .boxed()
}

fn program() -> BoxedStrategy<String> {
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

// Recovery quality, measured. The tests above prove the parser is total and
// accepts every well-formed program; these bound how badly it does on a
// well-formed program after one edit. Non-delimiter edits must be local at
// the statement level; delimiter edits have a weaker item-level locality
// contract because they can legitimately reparent nearby syntax.

/// A non-delimiter mistake and at most three local consequences.
const MAX_ERRORS_PER_NON_DELIMITER_EDIT: usize = 4;
/// A delimiter mistake and a few consequences when it closes a distant list.
const MAX_ERRORS_PER_DELIMITER_EDIT: usize = 5;

/// One edit to a well-formed program, made at a significant token.
#[derive(Clone, Copy, Debug)]
enum Edit {
    /// Remove the token.
    Delete,
    /// Insert a spaced copy of the token after it.
    Duplicate,
    /// Exchange the token with its neighbour, keeping the trivia between.
    Swap,
    /// Insert this text, spaced, before the token.
    Insert(&'static str),
}

/// Tokens to insert: brackets above all, then keywords and operators that
/// start or continue something.
const INSERTS: &[&str] = &[
    "(", ")", "{", "}", ",", "=", "fn", "let", "else", "x", "0", "+", "-",
];

fn edit() -> impl Strategy<Value = Edit> {
    prop_oneof![
        3 => Just(Edit::Delete),
        2 => Just(Edit::Duplicate),
        2 => Just(Edit::Swap),
        3 => prop::sample::select(INSERTS).prop_map(Edit::Insert),
    ]
}

fn is_delimiter(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::LParen | SyntaxKind::RParen | SyntaxKind::LBrace | SyntaxKind::RBrace
    )
}

/// Whether `edit` inserts, removes, duplicates, or moves a delimiter.
fn changes_delimiter(input: &ParserInput, index: usize, edit: Edit) -> bool {
    match edit {
        Edit::Delete | Edit::Duplicate => input.get(index).is_some_and(is_delimiter),
        Edit::Insert(inserted) => matches!(inserted, "(" | ")" | "{" | "}"),
        Edit::Swap => {
            let left = if index + 1 < input.len() {
                index
            } else {
                index - 1
            };
            input.get(left).is_some_and(is_delimiter)
                || input.get(left + 1).is_some_and(is_delimiter)
        }
    }
}

/// Every front-end product for one source.
struct Front {
    lexed: LexedFile,
    cooked: CookedFile,
    input: ParserInput,
    parse: Parse,
}

fn front(source: &str) -> Front {
    let lexed = lex(source).expect("test sources fit in u32");
    let cooked = cook(source, &lexed);
    let input = ParserInput::new(&cooked);
    let parse = parse(&input);
    Front {
        lexed,
        cooked,
        input,
        parse,
    }
}

impl Front {
    /// The byte spans of the significant tokens.
    fn spans(&self) -> Vec<(usize, usize)> {
        (0..self.input.len())
            .map(|index| {
                let range = self.lexed.range(self.input.token(index) as usize);
                (range.start().to_usize(), range.end().to_usize())
            })
            .collect()
    }

    /// The byte span of a node.
    fn node_span(&self, node: usize) -> (usize, usize) {
        let tree = self.parse.tree();
        let (first, end) = (tree.first_token(node), tree.end_token(node));
        let start = common::start_byte(&self.lexed, first) as usize;
        let stop = if end > first {
            self.lexed.range(end as usize - 1).end().to_usize()
        } else {
            start
        };
        (start, stop)
    }

    /// A node's text and the shape of its subtree: kinds with byte spans
    /// relative to the node, in preorder.
    fn shape(&self, source: &str, node: usize) -> (String, Vec<(NodeKind, usize, usize)>) {
        let tree = self.parse.tree();
        let (base, stop) = self.node_span(node);
        let mut nodes = Vec::new();
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            let (start, end) = self.node_span(node);
            nodes.push((tree.kind(node), start - base, end - base));
            let children: Vec<usize> = tree.children(node).collect();
            pending.extend(children.into_iter().rev());
        }
        (source[base..stop].to_owned(), nodes)
    }

    /// The items, and the statements of their bodies, that cover none of
    /// the raw tokens in `touched`: what an edit there must leave alone.
    /// The statements of a body whose `{` is among the raw tokens in
    /// `moved` are not among them: an edit that removes or moves the
    /// delimiter they sit inside necessarily reparents them.
    fn guarded(&self, touched: &[u32], moved: &[u32]) -> Vec<usize> {
        let tree = self.parse.tree();
        let mut nodes = Vec::new();
        for item in tree.children(0) {
            nodes.push(item);
            for child in tree.children(item) {
                if tree.kind(child) == NodeKind::Block && !moved.contains(&tree.first_token(child))
                {
                    nodes.extend(tree.children(child));
                }
            }
        }
        nodes.retain(|&node| {
            !touched
                .iter()
                .any(|&token| tree.first_token(node) <= token && token < tree.end_token(node))
        });
        nodes
    }
}

/// A well-formed program with at least two significant tokens, the index of
/// one of them, and an edit to make there.
fn edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    program()
        .prop_filter("an edit needs two tokens", |source| {
            front(source).input.len() >= 2
        })
        .prop_flat_map(|source| {
            let count = front(&source).input.len();
            (Just(source), 0..count, edit())
        })
}

fn non_delimiter_edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    edited_program().prop_filter("the edit changes no delimiter", |(source, index, edit)| {
        !changes_delimiter(&front(source).input, *index, *edit)
    })
}

fn delimiter_edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    edited_program().prop_filter("the edit changes a delimiter", |(source, index, edit)| {
        changes_delimiter(&front(source).input, *index, *edit)
    })
}

/// The replaced byte interval in the original and where it ends afterward.
#[derive(Clone, Copy)]
struct EditSpan {
    start: usize,
    old_end: usize,
    new_end: usize,
}

impl EditSpan {
    /// Map a span disjoint from the edit into the edited source.
    fn map(self, (start, end): (usize, usize)) -> (usize, usize) {
        if end <= self.start {
            return (start, end);
        }
        assert!(start >= self.old_end, "a guarded node overlaps the edit");
        let shift = self.new_end as isize - self.old_end as isize;
        (
            start
                .checked_add_signed(shift)
                .expect("mapped start is in range"),
            end.checked_add_signed(shift)
                .expect("mapped end is in range"),
        )
    }
}

/// Apply `edit` at significant token `index` of `source`: the edited text,
/// the significant indices the edit touches, those it removes or moves, and
/// the replaced byte interval for mapping unaffected nodes.
///
/// The touched indices include two tokens on either side of the edit: an
/// inserted token joins whatever it lands next to — a leading operator or
/// `else` continues the statement above, a `(` after a name makes a call —
/// and a deleted token can leave a dangling operator that takes the next
/// line as its operand. Jointness can change the arity of that neighbouring
/// operator and therefore the boundary after the token before it. Those are
/// the language's rules, not recovery, so this local context is the edit's
/// own business.
fn apply(
    source: &str,
    spans: &[(usize, usize)],
    index: usize,
    edit: Edit,
) -> (String, Vec<usize>, Vec<usize>, EditSpan) {
    let (start, end) = spans[index];
    let text = &source[start..end];
    let (edited, left, right, impact) = match edit {
        Edit::Delete => (
            format!("{}{}", &source[..start], &source[end..]),
            index,
            index,
            EditSpan {
                start,
                old_end: end,
                new_end: start,
            },
        ),
        Edit::Duplicate => (
            format!("{} {text}{}", &source[..end], &source[end..]),
            index,
            index,
            EditSpan {
                start: end,
                old_end: end,
                new_end: end + 1 + text.len(),
            },
        ),
        Edit::Insert(inserted) => (
            format!("{}{inserted} {}", &source[..start], &source[start..]),
            index,
            index,
            EditSpan {
                start,
                old_end: start,
                new_end: start + inserted.len() + 1,
            },
        ),
        Edit::Swap => {
            let (left, right) = if index + 1 < spans.len() {
                (index, index + 1)
            } else {
                (index - 1, index)
            };
            let ((ls, le), (rs, re)) = (spans[left], spans[right]);
            let edited = format!(
                "{}{}{}{}{}",
                &source[..ls],
                &source[rs..re],
                &source[le..rs],
                &source[ls..le],
                &source[re..]
            );
            (
                edited,
                left,
                right,
                EditSpan {
                    start: ls,
                    old_end: re,
                    new_end: re,
                },
            )
        }
    };
    let touched = (left.saturating_sub(2)..=(right + 2).min(spans.len() - 1)).collect();
    let moved = match edit {
        Edit::Delete => vec![index],
        Edit::Swap => vec![left, right],
        Edit::Duplicate | Edit::Insert(_) => Vec::new(),
    };
    (edited, touched, moved, impact)
}

proptest! {
    #[test]
    fn a_single_edit_costs_few_errors(
        (source, index, edit) in edited_program()
    ) {
        let original = front(&source);
        let (edited, _, _, _) = apply(&source, &original.spans(), index, edit);
        let after = front(&edited);
        check_tree(after.parse.tree(), &after.cooked)?;
        let max_errors = if changes_delimiter(&original.input, index, edit) {
            MAX_ERRORS_PER_DELIMITER_EDIT
        } else {
            MAX_ERRORS_PER_NON_DELIMITER_EDIT
        };
        let errors: Vec<_> = after.parse.errors().iter().map(|error| error.kind).collect();
        let positioned: Vec<_> = after
            .parse
            .errors()
            .iter()
            .map(|error| (common::start_byte(&after.lexed, error.token), error.kind))
            .collect();
        let recovery = errors.iter().filter(|kind| kind.is_recovery()).count();
        prop_assert!(
            recovery <= max_errors,
            "{:?} at token {} ({:?}) costs {} errors (maximum {}) {:?}\n--- original ---\n{}\n--- edited ---\n{}",
            edit, index, original.input.get(index), recovery, max_errors, positioned, source, edited
        );
    }

    #[test]
    fn a_single_non_delimiter_edit_disturbs_only_where_it_lands(
        (source, index, edit) in non_delimiter_edited_program()
    ) {
        let original = front(&source);
        let (edited, touched, moved, impact) = apply(&source, &original.spans(), index, edit);
        let touched: Vec<u32> = touched.iter().map(|&index| original.input.token(index)).collect();
        let moved: Vec<u32> = moved.iter().map(|&index| original.input.token(index)).collect();
        let after = front(&edited);
        let survivors: HashSet<_> = (0..after.parse.tree().len())
            .map(|node| (after.node_span(node), after.shape(&edited, node)))
            .collect();
        for node in original.guarded(&touched, &moved) {
            let shape = original.shape(&source, node);
            let span = impact.map(original.node_span(node));
            prop_assert!(
                survivors.contains(&(span, shape.clone())),
                "{:?} at token {} ({:?}) disturbs the {:?} {:?}\n--- original ---\n{}\n--- edited ---\n{}\nerrors: {:?}",
                edit, index, original.input.get(index), original.parse.tree().kind(node), shape.0,
                source, edited, after.parse.errors()
            );
        }
    }

    #[test]
    fn a_single_delimiter_edit_preserves_unaffected_items(
        (source, index, edit) in delimiter_edited_program()
    ) {
        let original = front(&source);
        let (edited, touched, _, impact) = apply(&source, &original.spans(), index, edit);
        let touched: Vec<u32> = touched.iter().map(|&index| original.input.token(index)).collect();
        let after = front(&edited);
        let tree = after.parse.tree();
        let survivors: HashSet<_> = tree
            .children(0)
            .filter(|&node| tree.kind(node) == NodeKind::FnItem)
            .map(|node| (after.node_span(node), after.shape(&edited, node)))
            .collect();

        let tree = original.parse.tree();
        for item in tree.children(0).filter(|&node| {
            tree.kind(node) == NodeKind::FnItem
                && !touched.iter().any(|&token| {
                    tree.first_token(node) <= token && token < tree.end_token(node)
                })
        }) {
            let shape = original.shape(&source, item);
            let span = impact.map(original.node_span(item));
            prop_assert!(
                survivors.contains(&(span, shape.clone())),
                "{:?} at token {} ({:?}) disturbs the item {:?}\n--- original ---\n{}\n--- edited ---\n{}\nerrors: {:?}",
                edit, index, original.input.get(index), shape.0, source, edited,
                after.parse.errors()
            );
        }
    }
}
