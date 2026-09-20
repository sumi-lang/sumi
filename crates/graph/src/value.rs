//! The domains a graph is read in; `Value` is the concrete one, a scalar per type.

use std::fmt;

use crate::{ArithOp, BinaryOp, CmpOp, Int, Op, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    Division,
    Type,
}

/// One reading of every leaf and operator. An operation faults instead of panicking, so a graph the
/// checker did not prove still runs to a refusal.
pub trait Domain: Clone {
    /// `Infallible` where no operation faults.
    type Fault;
    fn int(value: &Int) -> Self;
    fn bool(value: bool) -> Self;
    fn unit() -> Self;
    fn neg(&self) -> Result<Self, Self::Fault>;
    fn not(&self) -> Result<Self, Self::Fault>;
    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Result<Self, Self::Fault>;
    /// `&&` when `and`, else `||`. The short circuit is the graph's, so both operands have run.
    fn lazy(and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Self::Fault>;
    /// `self` narrowed to where `self op other` (`other op self` unless `local_is_lhs`) is `sense`.
    fn refine(&self, op: CmpOp, local_is_lhs: bool, sense: bool, other: &Self) -> Self;
    /// `self` narrowed to where it is `value`.
    fn exactly(&self, value: bool) -> Self;
}

impl Op {
    /// Panics unless `self` is a data operator; the rest are the reader's to evaluate.
    pub fn apply<D: Domain>(&self, inputs: &[&D]) -> Result<D, D::Fault> {
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
            Self::Param { .. }
            | Self::Unit
            | Self::Unused
            | Self::Hole
            | Self::And { .. }
            | Self::Or { .. }
            | Self::Entry
            | Self::Then
            | Self::Else
            | Self::Join { .. }
            | Self::Return { .. }
            | Self::Sequence
            | Self::Observe { .. }
            | Self::After
            | Self::Result { .. }
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
    type Fault = Fault;

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
            (BinaryOp::Cmp(op), Self::Int(lhs), Self::Int(rhs)) => Self::Bool(match op {
                CmpOp::Eq => lhs == rhs,
                CmpOp::Ne => lhs != rhs,
                CmpOp::Lt => lhs < rhs,
                CmpOp::Le => lhs <= rhs,
                CmpOp::Gt => lhs > rhs,
                CmpOp::Ge => lhs >= rhs,
            }),
            (BinaryOp::Cmp(op @ (CmpOp::Eq | CmpOp::Ne)), lhs, rhs) if lhs.ty() == rhs.ty() => {
                Self::Bool((lhs == rhs) == (op == CmpOp::Eq))
            }
            (BinaryOp::Arith(op), Self::Int(lhs), Self::Int(rhs)) => Self::Int(match op {
                ArithOp::Add => lhs + rhs,
                ArithOp::Sub => lhs - rhs,
                ArithOp::Mul => lhs * rhs,
                ArithOp::Div => lhs.checked_div(rhs).ok_or(Fault::Division)?,
                ArithOp::Rem => lhs.checked_rem(rhs).ok_or(Fault::Division)?,
            }),
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

    fn refine(&self, _: CmpOp, _: bool, _: bool, _: &Self) -> Self {
        self.clone()
    }

    fn exactly(&self, _: bool) -> Self {
        self.clone()
    }
}
