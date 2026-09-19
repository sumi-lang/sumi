//! The domains a graph is read in; `Value` is the concrete one, a scalar per type.

use std::fmt;

use crate::{BinaryOp, Int, Op, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    Division,
    Type,
}

/// One reading of every leaf and operator. An operation faults instead of panicking, so a graph the
/// checker did not prove still runs to a refusal.
pub trait Domain: Clone {
    fn int(value: &Int) -> Self;
    fn bool(value: bool) -> Self;
    fn unit() -> Self;
    fn neg(&self) -> Result<Self, Fault>;
    fn not(&self) -> Result<Self, Fault>;
    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Result<Self, Fault>;
    /// `&&` when `and`, else `||`. The short circuit is the graph's, so both operands have run.
    fn lazy(and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Fault>;
    /// `self` narrowed to where `self op other` (`other op self` unless `local_is_lhs`) is `sense`.
    fn refine(&self, op: BinaryOp, local_is_lhs: bool, sense: bool, other: &Self) -> Self;
    /// `self` narrowed to where it is `value`.
    fn exactly(&self, value: bool) -> Self;
}

impl Op {
    /// Panics unless `self` is a data operator; the rest are the reader's to evaluate.
    pub fn apply<D: Domain>(&self, inputs: &[&D]) -> Result<D, Fault> {
        Ok(match self {
            Self::Int(value) => D::int(value),
            Self::Bool(value) => D::bool(*value),
            Self::Copy { .. } => inputs[0].clone(),
            Self::Refine {
                op,
                local_is_lhs,
                sense,
            } => inputs[0].refine(*op, *local_is_lhs, *sense, inputs[1]),
            Self::Exactly(value) => inputs[0].exactly(*value),
            Self::Neg => inputs[0].neg()?,
            Self::Not => inputs[0].not()?,
            Self::Binary(op) => D::binary(*op, inputs[0], inputs[1])?,
            Self::Param(_)
            | Self::Unit
            | Self::Unused
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

    pub fn truth(&self) -> Result<bool, Fault> {
        match self {
            Self::Bool(value) => Ok(*value),
            _ => Err(Fault::Type),
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

    fn lazy(and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Fault> {
        match (lhs, rhs) {
            (Self::Bool(lhs), Self::Bool(rhs)) => {
                Ok(Self::Bool(if and { *lhs && *rhs } else { *lhs || *rhs }))
            }
            _ => Err(Fault::Type),
        }
    }

    fn refine(&self, _: BinaryOp, _: bool, _: bool, _: &Self) -> Self {
        self.clone()
    }

    fn exactly(&self, _: bool) -> Self {
        self.clone()
    }
}
