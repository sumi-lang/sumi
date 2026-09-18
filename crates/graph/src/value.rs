//! The values a graph is read in: the domain every operator has one
//! semantics in, and the concrete one, a scalar per type. The may-domain
//! beside it, a set per type, is [`May`](crate::May).

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

/// A domain of values the graph is read in: what each leaf is and what
/// each operator does, once, for every reader. The concrete domain is
/// [`Value`], one value per type, in which an operation faults rather
/// than panics, so a graph the checker rejected still runs to a refusal.
/// The may-domain is [`May`](crate::May), a set of values per type, in
/// which every operator contains the concrete one on every member of its
/// operands and none faults.
pub trait Domain: Clone {
    fn int(value: &Int) -> Self;
    fn bool(value: bool) -> Self;
    fn unit() -> Self;
    fn neg(&self) -> Result<Self, Fault>;
    fn not(&self) -> Result<Self, Fault>;
    /// An eager operator over two values.
    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Result<Self, Fault>;
    /// `&&` when `and`, else `||`, over both operands' values: what the
    /// operator is once its right operand has run.
    fn lazy(and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Fault>;
    /// A read of `self` where `self op other`, or `other op self` when
    /// the local is not the left operand, holds in `sense`. One value is
    /// itself; a set is narrowed to where the comparison holds.
    fn refine(&self, op: BinaryOp, local_is_lhs: bool, sense: bool, other: &Self) -> Self;
    /// A read of the boolean `self` where it is `value`.
    fn exactly(&self, value: bool) -> Self;
}

/// A domain in which every value is one value, so a condition goes one
/// way and a run in it takes one path. The may-domain is not one: the
/// solver takes every path a set allows.
pub trait Concrete: Domain {
    /// Which way a condition goes.
    fn truth(&self) -> Result<bool, Fault>;
}

impl Op {
    /// How many of the node's inputs, from the first, are values it
    /// computes from. The rest is the context recorded beside them. A
    /// call reads every argument.
    pub fn reads(&self, inputs: usize) -> usize {
        match self {
            Self::Int(_) | Self::Bool(_) | Self::Param(_) | Self::Unit | Self::Hole => 0,
            Self::Entry | Self::Then | Self::Else => 0,
            Self::Copy { .. } | Self::Exactly(_) | Self::Neg | Self::Not => 1,
            Self::And { .. } | Self::Or { .. } | Self::Join { .. } => 1,
            Self::Binary(_) | Self::Refine { .. } => 2,
            Self::Call(_) => inputs,
        }
    }

    /// The value of a data node from the values of the inputs it reads,
    /// as [`Op::reads`] counts them. A copy is what it reads, a narrowed
    /// read is what the domain makes of the guard, and unit is unit. A
    /// parameter, a hole, a context, and a node with a region are the
    /// reader's to evaluate, not the operator's.
    pub fn apply<D: Domain>(&self, inputs: &[&D]) -> Result<D, Fault> {
        Ok(match self {
            Self::Int(value) => D::int(value),
            Self::Bool(value) => D::bool(*value),
            Self::Unit => D::unit(),
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

impl Concrete for Value {
    fn truth(&self) -> Result<bool, Fault> {
        match self {
            Self::Bool(value) => Ok(*value),
            _ => Err(Fault::Type),
        }
    }
}
