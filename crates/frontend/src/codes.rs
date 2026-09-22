//! The frontend's diagnostic codes: what the lexer rejects, where the parser recovers, and the
//! layout rules. A code is never renamed or reused.

crate::codes! {
    SYNTAX = "syntax";

    /// A string literal reaches the end of its line without a closing `"`.
    UNTERMINATED_STRING: Error = "unterminated-string";

    /// A carriage return not followed by a line feed.
    LONE_CARRIAGE_RETURN: Error = "lone-carriage-return";

    /// A character with no meaning in Sumi source outside a string or comment.
    UNKNOWN_CHARACTER: Error = "unknown-character";

    /// Identifier characters attached to an integer literal, as in `1u32`.
    UNKNOWN_SUFFIX: Error = "unknown-suffix";

    /// An integer literal with leading zeros, as in `007`.
    NONCANONICAL_NUMBER: Error = "noncanonical-number";

    /// A string escape other than `\n`, `\r`, `\t`, `\\`, `\"`, or `\0`.
    UNKNOWN_ESCAPE: Error = "unknown-escape";

    /// Punctuation with no role in the language, such as `;`, `[`, or `@`.
    UNKNOWN_PUNCTUATION: Error = "unknown-punctuation";

    /// Something other than a function item at the top level of the file.
    EXPECTED_ITEM: Error = "expected-item";

    /// A token that cannot begin a statement where a block expects one.
    EXPECTED_STATEMENT: Error = "expected-statement";

    /// A token that cannot begin an expression where one is required.
    EXPECTED_EXPRESSION: Error = "expected-expression";

    /// The name a `fn`, `let`, or parameter declares is missing.
    EXPECTED_NAME: Error = "expected-name";

    /// A type is required after `:` or `->` and none follows.
    EXPECTED_TYPE: Error = "expected-type";

    /// One particular token is required and missing; the message names it.
    EXPECTED_TOKEN: Error = "expected-token";

    /// A function signature followed by neither `{` nor `=`.
    EXPECTED_BODY: Error = "expected-body";

    /// Two statements share a line.
    EXPECTED_BOUNDARY: Error = "expected-boundary";

    /// A token inside an expression that neither continues nor ends it.
    UNEXPECTED_SYNTAX: Error = "unexpected-syntax";

    /// Expressions nest deeper than the parser's limit.
    NESTING_TOO_DEEP: Error = "nesting-too-deep";

    /// A binary operator glued to an operand, as in `a+b`.
    UNSPACED_BINARY_OPERATOR: Error = "unspaced-binary-operator";

    /// A prefix operator separated from its operand, as in `- x`.
    SPACED_PREFIX_OPERATOR: Error = "spaced-prefix-operator";

    /// A space between a function name or callee and its `(`.
    SPACED_LIST_OPENER: Error = "spaced-list-opener";

    /// A function item's name on the line after its `fn`.
    FUNCTION_NAME_ON_NEXT_LINE: Error = "function-name-on-next-line";

    /// A function item beginning on the line where the previous one ended.
    FUNCTION_ITEM_ON_SAME_LINE: Error = "function-item-on-same-line";

    /// A binding's name on the line after its `let`.
    BINDING_NAME_ON_NEXT_LINE: Error = "binding-name-on-next-line";

    /// Comparisons chained, as in `a < b < c`.
    CHAINED_COMPARISON: Error = "chained-comparison";
}
