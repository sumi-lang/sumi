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

    /// An assignment target or `mut` argument that is no place: a name, or a field under one.
    INVALID_ASSIGNMENT_TARGET: Error = "invalid-assignment-target";

    /// A place under a parameter or a local declared without `mut`.
    IMMUTABLE_ASSIGNMENT: Error = "immutable-assignment";

    /// An argument written `mut` to a field or a parameter that is not, or without it to one that is.
    MUT_ARGUMENT: Error = "mut-argument";

    /// Two `mut` arguments of one call that name one place, or one a part of the other.
    OVERLAPPING_PLACES: Error = "overlapping-places";

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

    /// An index not proven inside its sequence, or a last element of one not proven to hold any.
    INDEX_OUT_OF_BOUNDS: Error = "index-out-of-bounds";

    /// A subscript on a value that is no sequence, or whose type is not known.
    NOT_A_SEQUENCE: Error = "not-a-sequence";

    /// A method call naming no method of its receiver's type.
    UNKNOWN_METHOD: Error = "unknown-method";

    /// `self` in a function that is in no `impl`, or anywhere but first among its parameters.
    INVALID_SELF: Error = "invalid-self";

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

    /// A type or function named with other than one type argument per type parameter it declares,
    /// or with none where its arguments, or the type an arm matches, do not decide them.
    TYPE_ARGUMENTS: Error = "type-arguments";

    /// A type argument that grows around a cycle of generic functions, or of generic types.
    POLYMORPHIC_RECURSION: Error = "polymorphic-recursion";

    /// A file naming more instances of its generic types and functions than the limit.
    TOO_MANY_INSTANCES: Error = "too-many-instances";

    /// An instance of a generic type whose type arguments name more types than the limit.
    TYPE_SIZE: Error = "type-size";

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
