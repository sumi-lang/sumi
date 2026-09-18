//! The values a run computes: the domain an evaluation runs in, and the
//! concrete one, a scalar per type.

use std::fmt;

use crate::{BinaryOp, Int, Op, Ty};

/// A domain of values an evaluation of the graph runs in: what each leaf
/// is, what each operator does, and which way a condition goes. The
/// concrete domain is [`Value`]; an abstract one answers the same
/// questions about sets of values.
pub trait Domain: Clone {
    fn int(value: &Int) -> Self;
    fn bool(value: bool) -> Self;
    fn unit() -> Self;
    fn neg(&self) -> Self;
    fn not(&self) -> Self;
    /// An eager operator over two values: `None` for a division by zero,
    /// the one operation with no value.
    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Option<Self>;
    /// Which way a condition goes.
    fn truth(&self) -> bool;
}

impl Op {
    /// The value of a data node from the values of the inputs it reads:
    /// `None` for a zero divisor. A narrowed read, a copy, and unit are
    /// what they read; a parameter, a hole, a context, and a node with a
    /// region are the machine's to evaluate, not the operator's.
    pub fn apply<D: Domain>(&self, inputs: &[D]) -> Option<D> {
        Some(match self {
            Self::Int(value) => D::int(value),
            Self::Bool(value) => D::bool(*value),
            Self::Unit => D::unit(),
            Self::Copy | Self::Refine { .. } | Self::Exactly(_) => inputs[0].clone(),
            Self::Neg => inputs[0].neg(),
            Self::Not => inputs[0].not(),
            Self::Binary(op) => return D::binary(*op, &inputs[0], &inputs[1]),
            Self::Param(_)
            | Self::Hole
            | Self::And { .. }
            | Self::Or { .. }
            | Self::Entry
            | Self::Then
            | Self::Else
            | Self::Join { .. }
            | Self::Call(_) => unreachable!("{self:?} is not a data operator"),
        })
    }
}

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

impl Domain for Value {
    fn int(value: &Int) -> Self {
        Self::Int(value.clone())
    }

    fn bool(value: bool) -> Self {
        Self::Bool(value)
    }

    fn unit() -> Self {
        Self::Unit
    }

    fn neg(&self) -> Self {
        match self {
            Self::Int(value) => Self::Int(-value),
            other => unreachable!("negating {other:?}"),
        }
    }

    fn not(&self) -> Self {
        match self {
            Self::Bool(value) => Self::Bool(!value),
            other => unreachable!("negating {other:?}"),
        }
    }

    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Option<Self> {
        Some(match (op, lhs, rhs) {
            (BinaryOp::Eq, lhs, rhs) => Self::Bool(lhs == rhs),
            (BinaryOp::Ne, lhs, rhs) => Self::Bool(lhs != rhs),
            (op, Self::Int(lhs), Self::Int(rhs)) => match op {
                BinaryOp::Add => Self::Int(lhs + rhs),
                BinaryOp::Sub => Self::Int(lhs - rhs),
                BinaryOp::Mul => Self::Int(lhs * rhs),
                // Truncating: the quotient rounds toward zero and the
                // remainder takes the dividend's sign.
                BinaryOp::Div => Self::Int(lhs.checked_div(rhs)?),
                BinaryOp::Rem => Self::Int(lhs.checked_rem(rhs)?),
                BinaryOp::Lt => Self::Bool(lhs < rhs),
                BinaryOp::Le => Self::Bool(lhs <= rhs),
                BinaryOp::Gt => Self::Bool(lhs > rhs),
                BinaryOp::Ge => Self::Bool(lhs >= rhs),
                BinaryOp::Eq | BinaryOp::Ne => unreachable!("handled for every type"),
            },
            (op, lhs, rhs) => unreachable!("{op:?} over {lhs:?} and {rhs:?}"),
        })
    }

    fn truth(&self) -> bool {
        match self {
            Self::Bool(value) => *value,
            other => unreachable!("branching on {other:?}"),
        }
    }
}
