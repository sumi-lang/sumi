//! Codes for `semantic` diagnostics; a code is never renamed or reused.

sumi_frontend::codes! {
    /// A function with a syntax error in its body reports nothing here.
    SEMANTIC = "semantic";

    /// A type reference naming none of `int`, `bool`, and `unit`.
    UNKNOWN_TYPE = "unknown-type";

    /// A name with no declaration in scope.
    UNKNOWN_NAME = "unknown-name";

    /// Two functions in a file, or two parameters of a function, with the same name.
    DUPLICATE_NAME = "duplicate-name";

    /// A call whose callee is a parameter or binding.
    NOT_CALLABLE = "not-callable";

    /// A call whose argument count differs from the callee's parameter count.
    ARITY = "arity";

    /// An assignment whose target is not a local name.
    INVALID_ASSIGNMENT_TARGET = "invalid-assignment-target";

    /// An assignment to a parameter or a local declared without `mut`.
    IMMUTABLE_ASSIGNMENT = "immutable-assignment";

    /// An expression of one type where another is required.
    TYPE_MISMATCH = "type-mismatch";

    /// A statement's expression, other than a block's last, with a value that is not unit.
    UNUSED_VALUE = "unused-value";

    /// A function with no return type whose result is used as two types or fixed by nothing.
    CANNOT_INFER = "cannot-infer";

    /// A `/` or `%` that can run with a divisor whose range includes zero.
    DIVISION_BY_ZERO = "division-by-zero";

    /// A cycle of calls in which no parameter strictly moves toward a bound.
    UNBOUNDED_RECURSION = "unbounded-recursion";

    /// A construct the checker does not handle; the function is left unchecked.
    UNSUPPORTED = "unsupported";
}
