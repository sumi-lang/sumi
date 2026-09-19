//! Stable codes for `syntax` diagnostics.
//!
//! A code is spelled `group/name`, both kebab-case, and is stable: never
//! renamed or reused for something else. Every code is shown by a case
//! under `tests/corpus/`, which `crates/hir/tests/codes.rs` checks.

crate::codes! {
    /// Reported by the frontend: what the lexer rejects, where the parser
    /// recovers, and the layout rules the parser checks. Every one is an
    /// error. The tree is still built around it, and a fix is attached where
    /// the repair is a token: a closer or a canonical literal. A layout rule
    /// carries none; `sumi fmt` repairs every one it can.
    SYNTAX = "syntax";

    /// A string literal reaches the end of its line without a closing `"`. The
    /// literal ends at the line break, so nothing after that line is affected.
    UNTERMINATED_STRING = "unterminated-string";

    /// A carriage return not followed by a line feed. A line ends with `\n` or
    /// `\r\n`.
    LONE_CARRIAGE_RETURN = "lone-carriage-return";

    /// A character with no meaning in Sumi source outside a string or comment.
    /// Names are ASCII letters, digits, and `_`.
    UNKNOWN_CHARACTER = "unknown-character";

    /// Identifier characters attached to an integer literal, as in `1u32`,
    /// `1e5`, or `1_000`. Literals take no suffix, exponent, or separator.
    UNKNOWN_SUFFIX = "unknown-suffix";

    /// An integer literal with leading zeros, as in `007`. The fix removes
    /// them.
    NONCANONICAL_NUMBER = "noncanonical-number";

    /// A backslash in a string literal beginning none of the escapes `\n`,
    /// `\r`, `\t`, `\\`, `\"`, and `\0`.
    UNKNOWN_ESCAPE = "unknown-escape";

    /// Punctuation with no role in the language, such as `;`, `[`, or `@`.
    UNKNOWN_PUNCTUATION = "unknown-punctuation";

    /// Something other than a function item at the top level of the file.
    EXPECTED_ITEM = "expected-item";

    /// A token that cannot begin a statement where a block's next statement
    /// should start.
    EXPECTED_STATEMENT = "expected-statement";

    /// An expression is required, after an operator, `=`, or `(` for instance,
    /// and the next token cannot begin one.
    EXPECTED_EXPRESSION = "expected-expression";

    /// The name a `fn`, `let`, or parameter declares is missing.
    EXPECTED_NAME = "expected-name";

    /// A type is required after `:` or `->` and none follows.
    EXPECTED_TYPE = "expected-type";

    /// One particular token is required and the message names it: a closing
    /// bracket, a `,` between list elements, or the `(` of a parameter list.
    /// For a missing closer, a label points at the opener and the fix inserts
    /// the closer.
    EXPECTED_TOKEN = "expected-token";

    /// A function signature is followed by neither a block nor `=` and an
    /// expression.
    EXPECTED_BODY = "expected-body";

    /// Two statements share a line. A line break ends a statement; there is no
    /// `;`.
    EXPECTED_BOUNDARY = "expected-boundary";

    /// A token inside an expression that neither continues nor ends it. The
    /// parser skips to where it can resume and labels what it skipped.
    UNEXPECTED_SYNTAX = "unexpected-syntax";

    /// Expressions nest deeper than the parser's limit of 256 levels, which
    /// keeps parsing on a bounded stack.
    NESTING_TOO_DEEP = "nesting-too-deep";

    /// A binary operator glued to an operand, as in `a+b` or `a<b`. Binary
    /// operators are spaced on both sides; glued, `<` opens type arguments and
    /// `*` and `&` are reserved for prefix operators. `sumi fmt` spaces it.
    UNSPACED_BINARY_OPERATOR = "unspaced-binary-operator";

    /// A prefix operator separated from its operand, as in `- x`. Prefix
    /// operators are glued; `sumi fmt` removes the space.
    SPACED_PREFIX_OPERATOR = "spaced-prefix-operator";

    /// A space between a function name or callee and its `(`, which
    /// `sumi fmt` removes.
    SPACED_LIST_OPENER = "spaced-list-opener";

    /// A function item's name on the line after its `fn`. `sumi fmt` moves
    /// the name onto the `fn` line.
    FUNCTION_NAME_ON_NEXT_LINE = "function-name-on-next-line";

    /// A function item beginning on the line where the previous one ended.
    /// `sumi fmt` moves it onto a line of its own.
    FUNCTION_ITEM_ON_SAME_LINE = "function-item-on-same-line";

    /// A binding's name on the line after its `let`. `sumi fmt` moves the
    /// name onto the `let` line.
    BINDING_NAME_ON_NEXT_LINE = "binding-name-on-next-line";

    /// Comparisons chained, as in `a < b < c`. A comparison yields a boolean
    /// that no comparison accepts; write two comparisons joined by `&&`.
    CHAINED_COMPARISON = "chained-comparison";
}
