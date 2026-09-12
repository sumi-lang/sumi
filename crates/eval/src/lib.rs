//! The definitional interpreter: what a Sumi program means, run directly
//! over the HIR of a valid file.
//!
//! The machine is explicit about its state: a control stack of pending
//! work, a value stack, and a call stack of frames whose locals live in one
//! shared slab. Nothing recurses on the host stack, so a Sumi program's
//! recursion depth is bounded by [`MAX_CALL_DEPTH`] alone, and every
//! [`Machine::step`] is one unit of work an instrument can observe.
//!
//! Integer arithmetic is signed 64-bit and never wraps: an overflow, like a
//! division by zero or a call past the depth limit, is a [`Trap`] that ends
//! the run where it happened.

mod machine;

#[cfg(test)]
mod tests;

use std::fmt;

use sumi_hir::{Analysis, Function, FunctionId, Signature, Ty};
use sumi_text::Span;

pub use machine::{MAX_CALL_DEPTH, Machine};

/// A scalar value, one per [`Ty`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Unit,
}

impl Value {
    pub fn ty(self) -> Ty {
        match self {
            Self::Int(_) => Ty::Int,
            Self::Bool(_) => Ty::Bool,
            Self::Unit => Ty::Unit,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(value) => write!(f, "{value}"),
            Self::Bool(value) => write!(f, "{value}"),
            Self::Unit => f.write_str("unit"),
        }
    }
}

/// Why a run stopped short of a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrapKind {
    /// `/` or `%` with a zero divisor.
    DivisionByZero,
    /// An arithmetic result outside the signed 64-bit range: `+`, `-`, `*`,
    /// negation, and the minimum divided by `-1`.
    Overflow,
    /// A call that would nest deeper than [`MAX_CALL_DEPTH`] frames.
    CallDepth,
}

impl TrapKind {
    /// The code a driver reports, in the form diagnostics use.
    pub fn code(self) -> &'static str {
        match self {
            Self::DivisionByZero => "eval/division-by-zero",
            Self::Overflow => "eval/overflow",
            Self::CallDepth => "eval/call-depth",
        }
    }
    pub fn message(self) -> &'static str {
        match self {
            Self::DivisionByZero => "division by zero",
            Self::Overflow => "integer overflow",
            Self::CallDepth => "call nesting exceeds the depth limit",
        }
    }
}

/// A run that stopped at `origin`: the operation that trapped, or the call
/// that would have nested too deep.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Trap {
    pub kind: TrapKind,
    pub origin: Span,
}

impl fmt::Display for Trap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.kind.message())
    }
}

/// A valid analysis: every function has a signature and a complete typed
/// body, and no diagnostic is an error. Only such a file runs, so the
/// machine has no path for an ill-typed operation.
#[derive(Clone, Copy, Debug)]
pub struct Program<'a> {
    analysis: &'a Analysis,
}

impl<'a> Program<'a> {
    /// `None` when the analysis reports any error.
    pub fn new(analysis: &'a Analysis) -> Option<Self> {
        analysis.is_valid().then_some(Self { analysis })
    }
    pub fn analysis(self) -> &'a Analysis {
        self.analysis
    }
    pub fn function(self, id: FunctionId) -> &'a Function {
        self.analysis.function(id)
    }
    /// A function's contract; every function of a valid file has one.
    pub fn signature(self, id: FunctionId) -> &'a Signature {
        self.function(id)
            .signature()
            .expect("a valid file's functions have signatures")
    }
    /// Every function with its ID, in declaration order.
    pub fn functions(self) -> impl Iterator<Item = (FunctionId, &'a Function)> {
        self.analysis
            .function_ids()
            .map(|id| (id, self.analysis.function(id)))
    }
    /// The function item named `name`, if any.
    pub fn function_named(self, name: &str) -> Option<FunctionId> {
        self.functions()
            .find(|(_, function)| {
                function
                    .name()
                    .is_some_and(|span| self.analysis.text(span) == name)
            })
            .map(|(id, _)| id)
    }
    /// Run `function` on `args` to completion. The arguments must match the
    /// signature in count and type.
    pub fn evaluate(self, function: FunctionId, args: &[Value]) -> Result<Value, Trap> {
        Machine::new(self, function, args).run()
    }
}
