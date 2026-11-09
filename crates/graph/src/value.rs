//! The domains a graph is read in; `Value` is the concrete one.

use std::fmt;
use std::sync::Arc;

use crate::{ArithOp, BinaryOp, Case, CmpOp, Decl, DeclId, FieldName, Int, Names, Op, Ty, Unions};

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
    /// `&&` when `is_and`, else `||`. The short circuit is the graph's, so both operands have run.
    fn lazy(is_and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Self::Fault>;
    /// `self` narrowed to where `self op other` (`other op self` unless `local_is_lhs`) is `sense`.
    fn refine(&self, op: CmpOp, local_is_lhs: bool, sense: bool, other: &Self) -> Self;
    /// `self` narrowed to where it is `value`.
    fn exactly(&self, value: bool) -> Self;
    /// A value of `decl` from its fields, in declaration order.
    fn make(decl: DeclId, fields: Vec<Self>) -> Self;
    /// The field `name` of `self`, which faults on a value with no such field.
    fn field(&self, name: FieldName, decls: &[Decl], unions: &Unions) -> Result<Self, Self::Fault>;
    /// `self` narrowed to the values of `ty`.
    fn narrow(&self, ty: Ty, unions: &Unions) -> Self;
}

impl Op {
    /// Panics unless `self` is a data operator; the rest are the reader's to evaluate.
    pub fn apply<D: Domain>(
        &self,
        inputs: &[&D],
        decls: &[Decl],
        unions: &Unions,
    ) -> Result<D, D::Fault> {
        Ok(match self {
            Self::Int(value) => D::int(value),
            Self::Bool(value) => D::bool(*value),
            Self::Copy { .. } | Self::Assign => inputs[0].clone(),
            Self::Refine {
                op,
                local_is_lhs,
                sense,
            } => inputs[0].refine(*op, *local_is_lhs, *sense, inputs[1]),
            Self::Exactly(value) => inputs[0].exactly(*value),
            Self::Narrow(ty) => inputs[0].narrow(*ty, unions),
            Self::Neg => inputs[0].neg()?,
            Self::Not => inputs[0].not()?,
            Self::Binary(op) => D::binary(*op, inputs[0], inputs[1])?,
            Self::Make(decl) => D::make(*decl, inputs.iter().map(|&input| input.clone()).collect()),
            Self::Field(name) => inputs[0].field(*name, decls, unions)?,
            Self::Param { .. }
            | Self::LoopIndex
            | Self::Carry
            | Self::Loop { .. }
            | Self::LoopValue
            | Self::Unit
            | Self::Unused
            | Self::Hole
            | Self::And { .. }
            | Self::Or { .. }
            | Self::Entry
            | Self::Arm(_)
            | Self::Switch { .. }
            | Self::Return
            | Self::Sequence
            | Self::Observe { .. }
            | Self::After
            | Self::Result { .. }
            | Self::Phi
            | Self::Call(_) => unreachable!("{self:?} is not a data operator"),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(Int),
    Bool(bool),
    Unit,
    Decl(Record),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record(Arc<RecordData>);

#[derive(Debug, PartialEq, Eq)]
struct RecordData {
    decl: DeclId,
    fields: Box<[Value]>,
}

impl Record {
    pub fn decl(&self) -> DeclId {
        self.0.decl
    }

    /// The fields in declaration order.
    pub fn fields(&self) -> &[Value] {
        &self.0.fields
    }
}

impl Value {
    pub fn record(decl: DeclId, fields: Vec<Value>) -> Self {
        Self::Decl(Record(Arc::new(RecordData {
            decl,
            fields: fields.into_boxed_slice(),
        })))
    }

    pub fn ty(&self) -> Ty {
        match self {
            Self::Int(_) => Ty::INT,
            Self::Bool(_) => Ty::BOOL,
            Self::Unit => Ty::UNIT,
            Self::Decl(record) => Ty::decl(record.decl()),
        }
    }

    pub fn shown<'a>(&'a self, names: &'a dyn Names) -> ShownValue<'a> {
        ShownValue(self, names)
    }

    pub fn truth(&self) -> Result<bool, Fault> {
        match self {
            Self::Bool(value) => Ok(*value),
            _ => Err(Fault::Type),
        }
    }

    /// Whether `case` selects `self`; a case of another type faults.
    pub fn selects(&self, case: Case, unions: &Unions) -> Result<bool, Fault> {
        match (case, self) {
            (Case::Bool(wanted), Self::Bool(value)) => Ok(*value == wanted),
            (Case::Is(_) | Case::Not(_) | Case::Any, Self::Decl(record)) => {
                Ok(case.selects_decl(record.decl(), unions))
            }
            _ => Err(Fault::Type),
        }
    }
}

/// A value as the source would write it.
pub struct ShownValue<'a>(&'a Value, &'a dyn Names);

impl fmt::Display for ShownValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Value::Int(value) => write!(f, "{value}"),
            Value::Bool(value) => write!(f, "{value}"),
            Value::Unit => f.write_str("unit"),
            Value::Decl(record) => {
                write!(f, "{}(", Ty::decl(record.decl()).shown(self.1))?;
                for (index, field) in record.fields().iter().enumerate() {
                    if index > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", field.shown(self.1))?;
                }
                f.write_str(")")
            }
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

    fn lazy(is_and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Fault> {
        match (lhs, rhs) {
            (Self::Bool(lhs), Self::Bool(rhs)) => {
                Ok(Self::Bool(if is_and { *lhs && *rhs } else { *lhs || *rhs }))
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

    fn make(decl: DeclId, fields: Vec<Self>) -> Self {
        Self::record(decl, fields)
    }

    fn field(&self, name: FieldName, decls: &[Decl], _: &Unions) -> Result<Self, Fault> {
        match self {
            Self::Decl(record) => decls[record.decl().index()]
                .index_of(name)
                .map(|index| record.fields()[index].clone())
                .ok_or(Fault::Type),
            _ => Err(Fault::Type),
        }
    }

    fn narrow(&self, _: Ty, _: &Unions) -> Self {
        self.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn value_slots_stay_two_words() {
        assert_eq!(size_of::<Value>(), 16);
        assert_eq!(size_of::<Option<Value>>(), 16);
    }
}
