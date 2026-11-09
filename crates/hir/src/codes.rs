//! Codes for `semantic` diagnostics; a code is never renamed or reused.

sumi_frontend::codes! {
    /// A function with a syntax error in its body reports nothing here.
    SEMANTIC = "semantic";

    /// A type reference naming no declared type and none of `int`, `bool`, and `unit`.
    UNKNOWN_TYPE: Error = "unknown-type";

    /// A name with no declaration in scope.
    UNKNOWN_NAME: Error = "unknown-name";

    /// Two items in a file, two parameters or type parameters of an item, or two fields of a type
    /// with the same name, or an item or type parameter named like a built-in type.
    DUPLICATE_NAME: Error = "duplicate-name";

    /// A call whose callee is a parameter, a binding, or a type parameter.
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

    /// A function, type, or type parameter name used where a value is required.
    NOT_A_VALUE: Error = "not-a-value";

    /// A field read or label naming no field of the type it is applied to.
    UNKNOWN_FIELD: Error = "unknown-field";

    /// A construction leaving a field of its type without a value.
    MISSING_FIELD: Error = "missing-field";

    /// A construction giving one field twice.
    DUPLICATE_FIELD: Error = "duplicate-field";

    /// A construction argument without a field label.
    UNLABELED_FIELD: Error = "unlabeled-field";

    /// A function call argument with a label.
    LABELED_ARGUMENT: Error = "labeled-argument";

    /// A type holding a value of its own type through its fields.
    RECURSIVE_TYPE: Error = "recursive-type";

    /// A union member, or a `match` arm, naming a scalar type or a type parameter.
    INVALID_UNION_MEMBER: Error = "invalid-union-member";

    /// A `match` with no arm for a member its scrutinee may hold, whatever the arguments.
    NON_EXHAUSTIVE_MATCH: Error = "non-exhaustive-match";

    /// A type or function named with other than one type argument per type parameter it declares.
    TYPE_ARGUMENTS: Error = "type-arguments";

    /// A type argument that grows with every call around a cycle of generic functions.
    POLYMORPHIC_RECURSION: Error = "polymorphic-recursion";

    /// A file naming more instances of its generic types and functions than the limit.
    TOO_MANY_INSTANCES: Error = "too-many-instances";

    /// A parameter or local never read whose name does not begin with `_`, in a function that
    /// lowers whole.
    UNUSED_NAME: Warning = "unused-name";

    /// An `if` condition, `&&` or `||` operand, or always-empty loop range, alike for any argument.
    CONSTANT_CONDITION: Warning = "constant-condition";

    /// Statements after one that never completes for any argument.
    UNREACHABLE_CODE: Warning = "unreachable-code";

    /// A function with parameters that no call from a parameterless or `_`-named function reaches.
    UNUSED_FUNCTION: Warning = "unused-function";
}
