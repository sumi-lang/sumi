//! Single-file scalar semantic analysis. The immutable syntax frontend is unchanged.
//!
//! Analysis retains successful typed bodies and independent diagnostics, not a
//! rejected-body IR. Handles are relative to their program or body, not persistent
//! identities. All source locations refer to the owned snapshot.

mod check;

#[cfg(test)]
mod tests;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionId(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExprId(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalId(usize);

impl ExprId {
    /// Index into the owning body's `expressions()` slice, not another body's.
    pub fn index(self) -> usize {
        self.0
    }
}

impl LocalId {
    /// Index into the owning body's `locals()` slice, not another body's.
    pub fn index(self) -> usize {
        self.0
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
    /// The NFKC-normalized name; original spelling remains in the parsed source.
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
    pub fn origin(&self) -> Span {
        self.origin
    }
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
        &self.exprs[id.0]
    }
    /// The ID must belong to this body.
    pub fn local(&self, id: LocalId) -> &Local {
        &self.locals[id.0]
    }
}

#[derive(Debug)]
pub struct Local {
    /// The NFKC-normalized name; `origin` retains the source spelling's range.
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
