//! What a program means apart from whether it is valid: the types, `Int`, the `Graph`, its
//! domains, and the `Machine`. Nothing here depends on the checker.

mod graph;
mod int;
mod machine;
mod may;
mod value;

use std::fmt;
use std::num::NonZeroU32;

pub use graph::{
    Carried, Decl, Graph, GraphBuilder, Node, NodeId, Op, OpenRun, References, Region, RegionId,
    Role, Run,
};
pub use int::{Int, OutOfRange, ParseIntError};
pub use machine::{Machine, Refusal};
pub use may::{Bools, Decls, Fields, Ints, May, Shown, Thresholds};
pub use value::{Domain, Fault, ShownValue, Value};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[cfg(test)]
impl ArithOp {
    pub const ALL: [Self; 5] = [Self::Add, Self::Sub, Self::Mul, Self::Div, Self::Rem];
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[cfg(test)]
impl CmpOp {
    pub const ALL: [Self; 6] = [Self::Eq, Self::Ne, Self::Lt, Self::Le, Self::Gt, Self::Ge];
}

impl CmpOp {
    /// The comparison with its operands exchanged.
    pub(crate) fn flip(self) -> Self {
        match self {
            Self::Lt => Self::Gt,
            Self::Le => Self::Ge,
            Self::Gt => Self::Lt,
            Self::Ge => Self::Le,
            Self::Eq | Self::Ne => self,
        }
    }

    /// The comparison that holds when this one does not.
    pub(crate) fn negate(self) -> Self {
        match self {
            Self::Lt => Self::Ge,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
            Self::Ge => Self::Lt,
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
        }
    }
}

/// Eager operators only; `&&` and `||` take a region as right operand and are [`Op::And`] and
/// [`Op::Or`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    Cmp(CmpOp),
    Arith(ArithOp),
}

impl BinaryOp {
    pub fn result(self) -> Ty {
        match self {
            Self::Cmp(_) => Ty::BOOL,
            Self::Arith(_) => Ty::INT,
        }
    }
}

/// A type: a scalar or a declared one, packed into one word so a node holding one stays four.
/// Match on [`kind`](Self::kind).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ty(NonZeroU32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    Int,
    Bool,
    Unit,
    Decl(DeclId),
}

impl Ty {
    pub const INT: Self = Self(NonZeroU32::new(1).unwrap());
    pub const BOOL: Self = Self(NonZeroU32::new(2).unwrap());
    pub const UNIT: Self = Self(NonZeroU32::new(3).unwrap());
    const FIRST_DECL: u32 = 4;
    pub const SCALARS: [Self; 3] = [Self::INT, Self::BOOL, Self::UNIT];

    pub fn decl(id: DeclId) -> Self {
        let packed =
            id.0.checked_add(Self::FIRST_DECL)
                .expect("declared type count fits u32");
        Self(NonZeroU32::new(packed).expect("a declared type packs above the scalars"))
    }

    pub fn kind(self) -> TyKind {
        match self {
            Self::INT => TyKind::Int,
            Self::BOOL => TyKind::Bool,
            Self::UNIT => TyKind::Unit,
            Self(packed) => TyKind::Decl(DeclId(packed.get() - Self::FIRST_DECL)),
        }
    }

    /// The declared type this is, if not a scalar.
    pub fn as_decl(self) -> Option<DeclId> {
        match self.kind() {
            TyKind::Decl(id) => Some(id),
            _ => None,
        }
    }

    /// The scalar's name; none for a declared type, whose name is the source's.
    pub fn scalar_name(self) -> Option<&'static str> {
        Some(match self.kind() {
            TyKind::Int => "int",
            TyKind::Bool => "bool",
            TyKind::Unit => "unit",
            TyKind::Decl(_) => return None,
        })
    }

    pub fn scalar(name: &str) -> Option<Self> {
        Self::SCALARS
            .into_iter()
            .find(|ty| ty.scalar_name() == Some(name))
    }

    pub fn shown(self, names: &dyn Names) -> ShownTy<'_> {
        ShownTy(self, names)
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Decl(id) => write!(f, "Decl({})", id.index()),
            scalar => write!(f, "{scalar:?}"),
        }
    }
}

/// A type as the source names it.
pub struct ShownTy<'a>(Ty, &'a dyn Names);

impl fmt::Display for ShownTy<'_> {
    fn fmt(&self, f: &'_ mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.kind() {
            TyKind::Decl(id) => f.write_str(self.1.decl(id)),
            _ => f.write_str(self.0.scalar_name().expect("a scalar has a name")),
        }
    }
}

/// What the source calls a declared type and its fields.
pub trait Names {
    fn decl(&self, id: DeclId) -> &str;
    fn field(&self, name: FieldName) -> &str;
}

/// A declared type's index in its file, in declaration order; an ID from one analysis names
/// nothing in another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclId(u32);

impl DeclId {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("declared type count fits u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A field name, one per distinct spelling in the file, so a read names a field of whatever type
/// reaches it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldName(u32);

impl FieldName {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("field name count fits u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
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
