//! The frontend's diagnostic codes: what the lexer rejects, where the parser recovers, and the
//! layout rules. A code is never renamed or reused.

crate::codes! {
    SYNTAX = "syntax";

    /// A string literal reaches the end of its line without a closing `"`.
    UNTERMINATED_STRING = "unterminated-string";

    /// A carriage return not followed by a line feed.
    LONE_CARRIAGE_RETURN = "lone-carriage-return";

    /// A character with no meaning in Sumi source outside a string or comment.
    UNKNOWN_CHARACTER = "unknown-character";

    /// Identifier characters attached to an integer literal, as in `1u32`.
    UNKNOWN_SUFFIX = "unknown-suffix";

    /// An integer literal with leading zeros, as in `007`.
    NONCANONICAL_NUMBER = "noncanonical-number";

    /// A string escape other than `\n`, `\r`, `\t`, `\\`, `\"`, or `\0`.
    UNKNOWN_ESCAPE = "unknown-escape";

    /// Punctuation with no role in the language, such as `;`, `[`, or `@`.
    UNKNOWN_PUNCTUATION = "unknown-punctuation";

    /// Something other than a function item at the top level of the file.
    EXPECTED_ITEM = "expected-item";

    /// A token that cannot begin a statement where a block expects one.
    EXPECTED_STATEMENT = "expected-statement";

    /// A token that cannot begin an expression where one is required.
    EXPECTED_EXPRESSION = "expected-expression";

    /// The name a `fn`, `let`, or parameter declares is missing.
    EXPECTED_NAME = "expected-name";

    /// A type is required after `:` or `->` and none follows.
    EXPECTED_TYPE = "expected-type";

    /// One particular token is required and missing; the message names it.
    EXPECTED_TOKEN = "expected-token";

    /// A function signature followed by neither `{` nor `=`.
    EXPECTED_BODY = "expected-body";

    /// Two statements share a line.
    EXPECTED_BOUNDARY = "expected-boundary";

    /// A token inside an expression that neither continues nor ends it.
    UNEXPECTED_SYNTAX = "unexpected-syntax";

    /// Expressions nest deeper than the parser's limit.
    NESTING_TOO_DEEP = "nesting-too-deep";

    /// A binary operator glued to an operand, as in `a+b`.
    UNSPACED_BINARY_OPERATOR = "unspaced-binary-operator";

    /// A prefix operator separated from its operand, as in `- x`.
    SPACED_PREFIX_OPERATOR = "spaced-prefix-operator";

    /// A space between a function name or callee and its `(`.
    SPACED_LIST_OPENER = "spaced-list-opener";

    /// A function item's name on the line after its `fn`.
    FUNCTION_NAME_ON_NEXT_LINE = "function-name-on-next-line";

    /// A function item beginning on the line where the previous one ended.
    FUNCTION_ITEM_ON_SAME_LINE = "function-item-on-same-line";

    /// A binding's name on the line after its `let`.
    BINDING_NAME_ON_NEXT_LINE = "binding-name-on-next-line";

    /// Comparisons chained, as in `a < b < c`.
    CHAINED_COMPARISON = "chained-comparison";
}
