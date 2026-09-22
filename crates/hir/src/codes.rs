//! Codes for `semantic` diagnostics; a code is never renamed or reused.

sumi_frontend::codes! {
    /// A function with a syntax error in its body reports nothing here.
    SEMANTIC = "semantic";

    /// A type reference naming none of `int`, `bool`, and `unit`.
    UNKNOWN_TYPE: Error = "unknown-type";

    /// A name with no declaration in scope.
    UNKNOWN_NAME: Error = "unknown-name";

    /// Two functions in a file, or two parameters of a function, with the same name.
    DUPLICATE_NAME: Error = "duplicate-name";

    /// A call whose callee is a parameter or binding.
    NOT_CALLABLE: Error = "not-callable";

    /// A call whose argument count differs from the callee's parameter count.
    ARITY: Error = "arity";

    /// An assignment whose target is not a local name.
    INVALID_ASSIGNMENT_TARGET: Error = "invalid-assignment-target";

    /// An assignment to a parameter or a local declared without `mut`.
    IMMUTABLE_ASSIGNMENT: Error = "immutable-assignment";

    /// An expression of one type where another is required.
    TYPE_MISMATCH: Error = "type-mismatch";

    /// A statement's expression, other than a block's last, with a value that is not unit.
    UNUSED_VALUE: Error = "unused-value";

    /// A function with no return type whose result is used as two types or fixed by nothing.
    CANNOT_INFER: Error = "cannot-infer";

    /// A `/` or `%` that can run with a divisor whose range includes zero.
    DIVISION_BY_ZERO: Error = "division-by-zero";

    /// A cycle of calls in which no parameter strictly moves toward a bound.
    UNBOUNDED_RECURSION: Error = "unbounded-recursion";

    /// A construct the checker does not handle; the function is left unchecked.
    UNSUPPORTED: Error = "unsupported";

    /// A parameter or local never read whose name does not begin with `_`, in a function that
    /// lowers whole.
    UNUSED_NAME: Warning = "unused-name";
}
