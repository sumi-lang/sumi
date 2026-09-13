//! The definitional interpreter: what a Sumi program means, run directly
//! over the HIR of a valid file.
//!
//! The machine is explicit about its state: a control stack of pending
//! work, a value stack, and a call stack of frames whose locals live in one
//! shared slab. Nothing recurses on the host stack, and every
//! [`Machine::step`] is one unit of work an instrument can observe.
//!
//! Nothing here can fail. Integers are mathematical, so arithmetic is
//! total; the checker proved every reachable divisor non-zero and every
//! recursion finite, so a zero divisor or a call past the analysis's depth
//! bound is a checker bug the machine refuses, never a program error.

mod machine;

#[cfg(test)]
mod tests;

use std::fmt;

use sumi_hir::{Analysis, Function, FunctionId, Int, Signature, Ty};

pub use machine::Machine;

/// A scalar value, one per [`Ty`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(Int),
    Bool(bool),
    Unit,
}

impl Value {
    pub fn ty(&self) -> Ty {
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

/// A valid analysis: every function has a signature and a complete typed
/// body, and no diagnostic is an error. Only such a file runs, so the
/// machine has no path for an ill-typed operation, a zero divisor, or a
/// recursion without end.
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
    pub fn evaluate(self, function: FunctionId, args: &[Value]) -> Value {
        Machine::new(self, function, args).run()
    }
}
