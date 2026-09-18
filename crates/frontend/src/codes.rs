//! Stable codes for `syntax` diagnostics.
//!
//! A code is spelled `group/name`, both kebab-case, and is stable: never
//! renamed or reused for something else. Every code is shown by a case
//! under `tests/corpus/`, which `crates/hir/tests/codes.rs` checks.

use crate::{DiagnosticCode, DiagnosticGroup};

/// Reported by the frontend: what the lexer rejects, where the parser
/// recovers, and the layout rules the parser checks. Every one is an
/// error. The tree is still built around it, and a fix is attached where
/// the repair is a token: a closer or a canonical literal. A layout rule
/// carries none; `sumi fmt` repairs every one it can.
pub const SYNTAX: DiagnosticGroup = DiagnosticGroup("syntax");

/// A string literal reaches the end of its line without a closing `"`. The
/// literal ends at the line break, so nothing after that line is affected.
pub const UNTERMINATED_STRING: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "unterminated-string",
};

/// A carriage return not followed by a line feed. A line ends with `\n` or
/// `\r\n`.
pub const LONE_CARRIAGE_RETURN: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "lone-carriage-return",
};

/// A character with no meaning in Sumi source outside a string or comment.
/// Names are ASCII letters, digits, and `_`.
pub const UNKNOWN_CHARACTER: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "unknown-character",
};

/// Identifier characters attached to an integer literal, as in `1u32`,
/// `1e5`, or `1_000`. Literals take no suffix, exponent, or separator.
pub const UNKNOWN_SUFFIX: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "unknown-suffix",
};

/// An integer literal with leading zeros, as in `007`. The fix removes
/// them.
pub const NONCANONICAL_NUMBER: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "noncanonical-number",
};

/// A backslash in a string literal beginning none of the escapes `\n`,
/// `\r`, `\t`, `\\`, `\"`, and `\0`.
pub const UNKNOWN_ESCAPE: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "unknown-escape",
};

/// Punctuation with no role in the language, such as `;`, `[`, or `@`.
pub const UNKNOWN_PUNCTUATION: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "unknown-punctuation",
};

/// Something other than a function item at the top level of the file.
pub const EXPECTED_ITEM: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-item",
};

/// A token that cannot begin a statement where a block's next statement
/// should start.
pub const EXPECTED_STATEMENT: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-statement",
};

/// An expression is required, after an operator, `=`, or `(` for instance,
/// and the next token cannot begin one.
pub const EXPECTED_EXPRESSION: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-expression",
};

/// The name a `fn`, `let`, or parameter declares is missing.
pub const EXPECTED_NAME: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-name",
};

/// A type is required after `:` or `->` and none follows.
pub const EXPECTED_TYPE: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-type",
};

/// One particular token is required and the message names it: a closing
/// bracket, a `,` between list elements, or the `(` of a parameter list.
/// For a missing closer, a label points at the opener and the fix inserts
/// the closer.
pub const EXPECTED_TOKEN: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-token",
};

/// A function signature is followed by neither a block nor `=` and an
/// expression.
pub const EXPECTED_BODY: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-body",
};

/// Two statements share a line. A line break ends a statement; there is no
/// `;`.
pub const EXPECTED_BOUNDARY: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "expected-boundary",
};

/// A token inside an expression that neither continues nor ends it. The
/// parser skips to where it can resume and labels what it skipped.
pub const UNEXPECTED_SYNTAX: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "unexpected-syntax",
};

/// Expressions nest deeper than the parser's limit of 256 levels, which
/// keeps parsing on a bounded stack.
pub const NESTING_TOO_DEEP: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "nesting-too-deep",
};

/// A binary operator glued to an operand, as in `a+b` or `a<b`. Binary
/// operators are spaced on both sides; glued, `<` opens type arguments and
/// `*` and `&` are reserved for prefix operators. `sumi fmt` spaces it.
pub const UNSPACED_BINARY_OPERATOR: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "unspaced-binary-operator",
};

/// A prefix operator separated from its operand, as in `- x`. Prefix
/// operators are glued; `sumi fmt` removes the space.
pub const SPACED_PREFIX_OPERATOR: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "spaced-prefix-operator",
};

/// A space between a function name or callee and its `(`, which
/// `sumi fmt` removes.
pub const SPACED_LIST_OPENER: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "spaced-list-opener",
};

/// A function item's name on the line after its `fn`. `sumi fmt` moves
/// the name onto the `fn` line.
pub const FUNCTION_NAME_ON_NEXT_LINE: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "function-name-on-next-line",
};

/// A function item beginning on the line where the previous one ended.
/// `sumi fmt` moves it onto a line of its own.
pub const FUNCTION_ITEM_ON_SAME_LINE: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "function-item-on-same-line",
};

/// A binding's name on the line after its `let`. `sumi fmt` moves the
/// name onto the `let` line.
pub const BINDING_NAME_ON_NEXT_LINE: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "binding-name-on-next-line",
};

/// Comparisons chained, as in `a < b < c`. A comparison yields a boolean
/// that no comparison accepts; write two comparisons joined by `&&`.
pub const CHAINED_COMPARISON: DiagnosticCode = DiagnosticCode {
    group: SYNTAX,
    name: "chained-comparison",
};

/// Every code of the group, in declaration order.
pub const ALL: [DiagnosticCode; 24] = [
    UNTERMINATED_STRING,
    LONE_CARRIAGE_RETURN,
    UNKNOWN_CHARACTER,
    UNKNOWN_SUFFIX,
    NONCANONICAL_NUMBER,
    UNKNOWN_ESCAPE,
    UNKNOWN_PUNCTUATION,
    EXPECTED_ITEM,
    EXPECTED_STATEMENT,
    EXPECTED_EXPRESSION,
    EXPECTED_NAME,
    EXPECTED_TYPE,
    EXPECTED_TOKEN,
    EXPECTED_BODY,
    EXPECTED_BOUNDARY,
    UNEXPECTED_SYNTAX,
    NESTING_TOO_DEEP,
    UNSPACED_BINARY_OPERATOR,
    SPACED_PREFIX_OPERATOR,
    SPACED_LIST_OPENER,
    FUNCTION_NAME_ON_NEXT_LINE,
    FUNCTION_ITEM_ON_SAME_LINE,
    BINDING_NAME_ON_NEXT_LINE,
    CHAINED_COMPARISON,
];
