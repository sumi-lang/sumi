//! What a program means apart from whether it is valid: the scalar types, `Int`, the `Graph`, its
//! domains, and the `Machine`. Nothing here depends on the checker.

mod graph;
mod int;
mod machine;
mod may;
mod value;

use std::fmt;

pub use graph::{Graph, Node, NodeId, Op, Region, RegionId, Run};
pub use int::{Int, OutOfRange, ParseIntError};
pub use machine::{Machine, Refusal};
pub use may::{Bools, Ints, May, Thresholds};
pub use value::{Domain, Fault, Value};

/// Eager operators only; `&&` and `||` take a region as right operand and are [`Op::And`] and
/// [`Op::Or`].
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

impl BinaryOp {
    pub fn result(self) -> Ty {
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::Div | Self::Rem => Ty::Int,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge => Ty::Bool,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Int,
    Bool,
    Unit,
}

impl Ty {
    pub const ALL: [Self; 3] = [Self::Int, Self::Bool, Self::Unit];

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::Bool => "bool",
            Self::Unit => "unit",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|ty| ty.as_str() == name)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A function's index in its file, in declaration order; an ID from one analysis names nothing in
/// another.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionId(u32);

impl FunctionId {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("function count fits u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}
