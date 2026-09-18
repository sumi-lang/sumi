//! What a Sumi program means, apart from whether it is valid: the scalar
//! types, the mathematical integer, the graph of every definition a
//! file's bodies make, and the machine that evaluates the graph in a
//! domain of values. The checker above builds the graph and decides what
//! is wrong with it; nothing here depends on the checker.

mod graph;
mod int;
mod machine;
mod value;

use std::fmt;

pub use graph::{Graph, Node, NodeId, Op, Region, RegionId, Run};
pub use int::{Int, OutOfRange, ParseIntError};
pub use machine::{Machine, Outcome, Refusal};
pub use value::{Domain, Value};

/// Eager scalar operators. `&&` and `||` are not among them: their right
/// operand is a region, so they are [`Op::And`] and [`Op::Or`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Int,
    Bool,
    Unit,
}

impl Ty {
    /// Every scalar type, in the order diagnostics list them.
    pub const ALL: [Self; 3] = [Self::Int, Self::Bool, Self::Unit];

    /// The type's name as written in source, and as diagnostics spell it.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::Bool => "bool",
            Self::Unit => "unit",
        }
    }

    /// The type a source name denotes.
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|ty| ty.as_str() == name)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A function of the file, by its position among the file's functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionId(u32);

impl FunctionId {
    /// The function at `index` in the file: an ID from one analysis names
    /// nothing in another.
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("function count fits u32"))
    }

    /// The function's position among the file's functions, in declaration
    /// order.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
