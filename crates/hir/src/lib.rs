//! Single-file scalar semantic analysis. The immutable syntax frontend is unchanged.
//!
//! Analysis retains successful typed bodies and independent diagnostics, not a
//! rejected-body IR. Handles are relative to their program or body, not persistent
//! identities. All source locations refer to the owned snapshot.

mod check;
mod infer;

pub mod codes;

#[cfg(test)]
mod tests;

use std::{fmt, num::NonZeroU32};
use sumi_frontend::{Diagnostic, ParsedSource, Severity};
use sumi_text::Span;

pub use check::analyze;

/// Eager scalar operators. Short-circuiting operators have separate expression kinds.
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
    const ALL: [Self; 3] = [Self::Int, Self::Bool, Self::Unit];

    /// The type's name as written in source, and as diagnostics spell it.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Int => "int",
            Self::Bool => "bool",
            Self::Unit => "unit",
        }
    }

    /// The type a source name denotes.
    pub(crate) fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|ty| ty.as_str() == name)
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionId(usize);
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct ExprId(NonZeroU32);
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct LocalId(NonZeroU32);

impl ExprId {
    fn new(index: usize) -> Self {
        // Each expression comes from a distinct syntax node; the tree's total
        // node count fits u32. Store one-based IDs so None needs no extra word.
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("expression count fits u32")).unwrap())
    }

    /// Index into the owning body's `expressions()` slice, not another body's.
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl fmt::Debug for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ExprId").field(&self.index()).finish()
    }
}

impl LocalId {
    fn new(index: usize) -> Self {
        // Parameters and let bindings each own a distinct syntax node.
        Self(NonZeroU32::new(u32::try_from(index + 1).expect("local count fits u32")).unwrap())
    }

    /// Index into the owning body's `locals()` slice, not another body's.
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl fmt::Debug for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("LocalId").field(&self.index()).finish()
    }
}

#[derive(Debug)]
pub struct Analysis {
    parsed: ParsedSource,
    functions: Vec<Function>,
    diagnostics: Vec<Diagnostic>,
}

impl Analysis {
    pub fn parsed(&self) -> &ParsedSource {
        &self.parsed
    }
    /// Semantic diagnostics only, in source order. Syntax diagnostics remain in `parsed`.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
    /// An ID must come from this analysis, not another source revision.
    pub fn function(&self, id: FunctionId) -> &Function {
        &self.functions[id.0]
    }
    pub fn is_valid(&self) -> bool {
        !self
            .parsed
            .diagnostics()
            .iter()
            .chain(&self.diagnostics)
            .any(|d| d.severity == Severity::Error)
            && self
                .functions
                .iter()
                .all(|f| f.signature.is_some() && f.body.is_some())
    }
}

#[derive(Debug)]
pub struct Function {
    name: Option<Box<str>>,
    origin: Span,
    signature: Option<Signature>,
    body: Option<Body>,
}

impl Function {
    /// The name as written.
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
    pub fn origin(&self) -> Span {
        self.origin
    }
    /// A concrete declaration contract, not a guarantee that its body is valid.
    /// Expression bodies (`=`, including `= { ... }`) infer an omitted result;
    /// bare block bodies default to unit. Callers never determine this result.
    pub fn signature(&self) -> Option<&Signature> {
        self.signature.as_ref()
    }
    /// A complete typed body is not permission to execute an invalid file.
    pub fn body(&self) -> Option<&Body> {
        self.body.as_ref()
    }
}

#[derive(Debug)]
pub struct Signature {
    pub params: Box<[Ty]>,
    pub result: Ty,
}

#[derive(Debug)]
pub struct Body {
    params: Vec<LocalId>,
    locals: Vec<Local>,
    exprs: Vec<Expr>,
    root: ExprId,
}

impl Body {
    pub fn params(&self) -> &[LocalId] {
        &self.params
    }
    pub fn locals(&self) -> &[Local] {
        &self.locals
    }
    pub fn expressions(&self) -> &[Expr] {
        &self.exprs
    }
    pub fn root(&self) -> ExprId {
        self.root
    }
    /// The ID must belong to this body.
    pub fn expression(&self, id: ExprId) -> &Expr {
        &self.exprs[id.index()]
    }
    /// The ID must belong to this body.
    pub fn local(&self, id: LocalId) -> &Local {
        &self.locals[id.index()]
    }
}

#[derive(Debug)]
pub struct Local {
    /// The name as written; `origin` is its range in the source.
    pub name: Box<str>,
    pub origin: Span,
    pub ty: Ty,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub origin: Span,
    pub ty: Ty,
}

#[derive(Debug)]
pub enum ExprKind {
    Int(i64),
    Bool(bool),
    Local(LocalId),
    Neg(ExprId),
    Not(ExprId),
    /// Eager scalar operation.
    Binary {
        op: BinaryOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    And {
        lhs: ExprId,
        rhs: ExprId,
    },
    Or {
        lhs: ExprId,
        rhs: ExprId,
    },
    Call {
        function: FunctionId,
        args: Vec<ExprId>,
        callee: Span,
    },
    If {
        condition: ExprId,
        then_branch: ExprId,
        else_branch: Option<ExprId>,
    },
    Block {
        statements: Vec<Statement>,
        tail: Option<ExprId>,
    },
}

impl ExprKind {
    pub(crate) fn binary(op: sumi_syntax::BinaryOp, lhs: ExprId, rhs: ExprId) -> Self {
        use sumi_syntax::BinaryOp::*;

        let op = match op {
            Add => BinaryOp::Add,
            Sub => BinaryOp::Sub,
            Mul => BinaryOp::Mul,
            Div => BinaryOp::Div,
            Rem => BinaryOp::Rem,
            Eq => BinaryOp::Eq,
            Ne => BinaryOp::Ne,
            Lt => BinaryOp::Lt,
            Le => BinaryOp::Le,
            Gt => BinaryOp::Gt,
            Ge => BinaryOp::Ge,
            And => return Self::And { lhs, rhs },
            Or => return Self::Or { lhs, rhs },
        };
        Self::Binary { op, lhs, rhs }
    }
}

#[derive(Debug)]
pub struct Statement {
    pub origin: Span,
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {
    Let { local: LocalId, initializer: ExprId },
    Eval(ExprId),
}
