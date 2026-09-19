//! Stable codes for `semantic` diagnostics.
//!
//! A code is spelled `group/name`, both kebab-case, and is stable: never
//! renamed or reused for something else. Every code is shown by a case
//! under `tests/corpus/`, which `crates/hir/tests/codes.rs` checks.

sumi_frontend::codes! {
    /// Reported by semantic checking over every function whose syntax is
    /// complete: names, the scalar types `int`, `bool`, and `unit`, and calls.
    /// A function with a syntax error in its body is not checked, and every
    /// code here is an error.
    SEMANTIC = "semantic";

    /// A type reference naming none of `int`, `bool`, and `unit`.
    UNKNOWN_TYPE = "unknown-type";

    /// A name with no declaration in scope: no parameter or binding for a
    /// value, no function item for a call.
    UNKNOWN_NAME = "unknown-name";

    /// Two function items of one file, or two parameters of one function, with
    /// the same name. A label points at the first.
    DUPLICATE_NAME = "duplicate-name";

    /// A call whose callee is a parameter or binding. Only function items are
    /// callable, since every local holds a scalar.
    NOT_CALLABLE = "not-callable";

    /// A call passing a different number of arguments than the function
    /// declares parameters. A label points at the declaration.
    ARITY = "arity";

    /// An expression of one type where another is required: an operand, a
    /// condition, an initializer against its annotation, an argument, a
    /// result against its return type, or `if` branches that disagree.
    TYPE_MISMATCH = "type-mismatch";

    /// A statement's expression, other than a block's last, has a value that
    /// is not unit. Write `_ =` before it to say the value is dropped; a run
    /// then never computes it, since nothing reads it.
    UNUSED_VALUE = "unused-value";

    /// A function without a return type whose result cannot be determined: its
    /// result is used as two types, or nothing fixes it. Add a return type
    /// annotation.
    CANNOT_INFER = "cannot-infer";

    /// A `/` or `%` whose divisor may be zero where the division can run: the
    /// values that reach the divisor, the hull of every argument and operand
    /// that flows into it, include zero. Labels name the values that put it
    /// there. A guard such as `if d != 0` narrows the divisor inside its
    /// branch, and a division no path reaches is not checked.
    DIVISION_BY_ZERO = "division-by-zero";

    /// A cycle of calls with no argument that moves toward a bound: on every
    /// call around the cycle some one parameter of each function must be
    /// passed a value that never moves the wrong way and, often enough that
    /// no cycle of calls only passes it along, strictly decreases (or strictly
    /// increases), with the values it can take bounded on that side. An
    /// argument counts when it is a parameter of the caller plus or minus a
    /// value, read through `let`s, blocks, and the arms of an `if` that can
    /// run; a constant argument moves nothing, so a cycle that resets a
    /// parameter is reported even where its guard would end it. Labels name
    /// the recursive calls and what each does to the parameter that came
    /// closest.
    UNBOUNDED_RECURSION = "unbounded-recursion";

    /// A construct scalar checking does not handle yet, such as a closure, a
    /// string literal, or a call through anything but a function name. The
    /// function is left unchecked.
    UNSUPPORTED = "unsupported";
}
