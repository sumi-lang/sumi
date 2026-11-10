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
    Arms, Carried, Case, Decl, Graph, GraphBuilder, Node, NodeId, Op, OpenRun, Operand, Rebuild,
    References, Region, RegionId, Role, Run, Unions,
};
pub use int::{Int, OutOfRange, ParseIntError};
pub use machine::{Machine, Refusal};
pub use may::{Bools, Decls, Fields, Ints, May, Shown, Thresholds};
pub use value::{Domain, Fault, Record, ShownValue, Value};

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

/// A type: a scalar, a declared one, or a union of declared ones, packed into one word so a node
/// holding one stays four. Match on [`kind`](Self::kind).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ty(NonZeroU32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TyKind {
    Int,
    Bool,
    Unit,
    Decl(DeclId),
    Union(UnionId),
}

impl Ty {
    pub const INT: Self = Self(NonZeroU32::new(1).unwrap());
    pub const BOOL: Self = Self(NonZeroU32::new(2).unwrap());
    pub const UNIT: Self = Self(NonZeroU32::new(3).unwrap());
    const FIRST_DECL: u32 = 4;
    const UNION: u32 = 1 << 31;
    pub const SCALARS: [Self; 3] = [Self::INT, Self::BOOL, Self::UNIT];

    pub fn decl(id: DeclId) -> Self {
        let packed =
            id.0.checked_add(Self::FIRST_DECL)
                .expect("declared type count fits u32");
        assert!(
            packed < Self::UNION,
            "declared type count fits below the union bit"
        );
        Self(NonZeroU32::new(packed).expect("a declared type packs above the scalars"))
    }

    pub fn union(id: UnionId) -> Self {
        assert!(id.0 < Self::UNION, "union count fits below the union bit");
        Self(NonZeroU32::new(id.0 | Self::UNION).expect("the union bit is set"))
    }

    pub fn kind(self) -> TyKind {
        match self {
            Self::INT => TyKind::Int,
            Self::BOOL => TyKind::Bool,
            Self::UNIT => TyKind::Unit,
            Self(packed) if packed.get() & Self::UNION != 0 => {
                TyKind::Union(UnionId(packed.get() & !Self::UNION))
            }
            Self(packed) => TyKind::Decl(DeclId(packed.get() - Self::FIRST_DECL)),
        }
    }

    /// The declared type this is, if not a scalar or a union.
    pub fn as_decl(self) -> Option<DeclId> {
        match self.kind() {
            TyKind::Decl(id) => Some(id),
            _ => None,
        }
    }

    /// Whether values of the type are declared ones: of one declared type or a union of them.
    pub fn is_declared(self) -> bool {
        matches!(self.kind(), TyKind::Decl(_) | TyKind::Union(_))
    }

    /// The scalar's name; none for a declared type or a union, which the source names.
    pub fn scalar_name(self) -> Option<&'static str> {
        Some(match self.kind() {
            TyKind::Int => "int",
            TyKind::Bool => "bool",
            TyKind::Unit => "unit",
            TyKind::Decl(_) | TyKind::Union(_) => return None,
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
            TyKind::Union(id) => write!(f, "Union({})", id.index()),
            scalar => write!(f, "{scalar:?}"),
        }
    }
}

/// A type as the source names it: a declared type with its type arguments, and a union as its
/// members joined by ` | `, in name order, which no declaration order changes.
pub struct ShownTy<'a>(Ty, &'a dyn Names);

impl ShownTy<'_> {
    /// The most type names one type spells out; an argument past them reads `…`, since an
    /// argument that names its own twice doubles with each nesting.
    const NAMES: usize = 32;

    fn write(ty: Ty, names: &dyn Names, left: &mut usize, out: &mut String) {
        if *left == 0 {
            out.push('…');
            return;
        }
        *left -= 1;
        match ty.kind() {
            TyKind::Decl(id) if names.decl(id) == ARRAY => {
                out.push('[');
                match names.type_args(id) {
                    [element] => Self::write(*element, names, left, out),
                    _ => out.push('…'),
                }
                out.push(']');
            }
            TyKind::Decl(id) => {
                out.push_str(names.decl(id));
                let args = names.type_args(id);
                if !args.is_empty() {
                    out.push('<');
                    for (index, &arg) in args.iter().enumerate() {
                        if index > 0 {
                            out.push_str(", ");
                        }
                        Self::write(arg, names, left, out);
                    }
                    out.push('>');
                }
            }
            TyKind::Union(id) => {
                let mut members: Vec<String> = names
                    .members(id)
                    .iter()
                    .map(|&member| {
                        let mut shown = String::new();
                        Self::write(Ty::decl(member), names, left, &mut shown);
                        shown
                    })
                    .collect();
                members.sort_unstable();
                out.push_str(&members.join(" | "));
            }
            TyKind::Int | TyKind::Bool | TyKind::Unit => {
                out.push_str(ty.scalar_name().expect("a scalar has a name"));
            }
        }
    }
}

impl fmt::Display for ShownTy<'_> {
    fn fmt(&self, f: &'_ mut fmt::Formatter<'_>) -> fmt::Result {
        let mut shown = String::new();
        Self::write(self.0, self.1, &mut { Self::NAMES }, &mut shown);
        f.write_str(&shown)
    }
}

/// What the built-in sequence type is called, which no source name can be: it is written `[T]`.
pub const ARRAY: &str = "[]";

/// What the source calls a declared type and its fields, and what a union holds.
pub trait Names {
    /// The name the type is declared with, which every instance of a generic one shares.
    fn decl(&self, id: DeclId) -> &str;
    /// The type arguments `id` is its generic type's instance at; none for a type that takes none.
    fn type_args(&self, id: DeclId) -> &[Ty];
    fn field(&self, name: FieldName) -> &str;
    /// Owned, so a table behind a cell can answer.
    fn members(&self, id: UnionId) -> Vec<DeclId>;
}

/// A union's index in its table; an ID from one analysis names nothing in another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnionId(u32);

impl UnionId {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("union count fits u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunctionId(u32);

impl FunctionId {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("function count fits u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}
