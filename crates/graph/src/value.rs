//! The values a run computes: the domain an evaluation runs in, and the
//! concrete one, a scalar per type.

use std::fmt;

use crate::{BinaryOp, Int, Op, Ty};

/// Why an operation has no value: the two ways a graph the checker did
/// not prove can ask for one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    /// A division by zero.
    Division,
    /// An operator over a value of the wrong type.
    Type,
}

/// A domain of values an evaluation of the graph runs in: what each leaf
/// is, what each operator does, and which way a condition goes. The
/// concrete domain is [`Value`]. An operation faults rather than
/// panics, so a graph the checker rejected still runs to a refusal.
pub trait Domain: Clone {
    fn int(value: &Int) -> Self;
    fn bool(value: bool) -> Self;
    fn unit() -> Self;
    fn neg(&self) -> Result<Self, Fault>;
    fn not(&self) -> Result<Self, Fault>;
    /// An eager operator over two values.
    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Result<Self, Fault>;
    /// Which way a condition goes.
    fn truth(&self) -> Result<bool, Fault>;
}

impl Op {
    /// How many of the node's inputs, from the first, are values it
    /// computes from. The rest are what the graph records beside them: a
    /// guard's other operand, a context. A call reads every argument.
    pub fn reads(&self, inputs: usize) -> usize {
        match self {
            Self::Int(_) | Self::Bool(_) | Self::Param(_) | Self::Unit | Self::Hole => 0,
            Self::Entry | Self::Then | Self::Else => 0,
            Self::Copy { .. } | Self::Refine { .. } | Self::Exactly(_) | Self::Neg | Self::Not => 1,
            Self::And { .. } | Self::Or { .. } | Self::Join { .. } => 1,
            Self::Binary(_) => 2,
            Self::Call(_) => inputs,
        }
    }

    /// The value of a data node from the values of the inputs it reads,
    /// as [`Op::reads`] counts them. A narrowed read and a copy are what
    /// they read; unit is unit. A parameter, a hole, a context, and a
    /// node with a region are the machine's to evaluate, not the
    /// operator's.
    pub fn apply<D: Domain>(&self, inputs: &[&D]) -> Result<D, Fault> {
        Ok(match self {
            Self::Int(value) => D::int(value),
            Self::Bool(value) => D::bool(*value),
            Self::Unit => D::unit(),
            Self::Copy { .. } | Self::Refine { .. } | Self::Exactly(_) => inputs[0].clone(),
            Self::Neg => inputs[0].neg()?,
            Self::Not => inputs[0].not()?,
            Self::Binary(op) => D::binary(*op, inputs[0], inputs[1])?,
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

    fn neg(&self) -> Result<Self, Fault> {
        match self {
            Self::Int(value) => Ok(Self::Int(-value)),
            _ => Err(Fault::Type),
        }
    }

    fn not(&self) -> Result<Self, Fault> {
        match self {
            Self::Bool(value) => Ok(Self::Bool(!value)),
            _ => Err(Fault::Type),
        }
    }

    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Result<Self, Fault> {
        Ok(match (op, lhs, rhs) {
            (BinaryOp::Eq, lhs, rhs) if lhs.ty() == rhs.ty() => Self::Bool(lhs == rhs),
            (BinaryOp::Ne, lhs, rhs) if lhs.ty() == rhs.ty() => Self::Bool(lhs != rhs),
            (op, Self::Int(lhs), Self::Int(rhs)) => match op {
                BinaryOp::Add => Self::Int(lhs + rhs),
                BinaryOp::Sub => Self::Int(lhs - rhs),
                BinaryOp::Mul => Self::Int(lhs * rhs),
                // Truncating: the quotient rounds toward zero and the
                // remainder takes the dividend's sign.
                BinaryOp::Div => Self::Int(lhs.checked_div(rhs).ok_or(Fault::Division)?),
                BinaryOp::Rem => Self::Int(lhs.checked_rem(rhs).ok_or(Fault::Division)?),
                BinaryOp::Lt => Self::Bool(lhs < rhs),
                BinaryOp::Le => Self::Bool(lhs <= rhs),
                BinaryOp::Gt => Self::Bool(lhs > rhs),
                BinaryOp::Ge => Self::Bool(lhs >= rhs),
                BinaryOp::Eq | BinaryOp::Ne => unreachable!("handled for every type"),
            },
            _ => return Err(Fault::Type),
        })
    }

    fn truth(&self) -> Result<bool, Fault> {
        match self {
            Self::Bool(value) => Ok(*value),
            _ => Err(Fault::Type),
        }
    }
}
