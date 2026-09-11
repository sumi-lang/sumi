//! Stable codes for semantic diagnostics.

use sumi_frontend::{DiagnosticCode, DiagnosticGroup};

pub const SEMANTIC: DiagnosticGroup = DiagnosticGroup::new("semantic");

pub const UNKNOWN_TYPE: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "unknown-type");
pub const UNKNOWN_NAME: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "unknown-name");
pub const DUPLICATE_NAME: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "duplicate-name");
pub const MISSING_TYPE: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "missing-type");
pub const NOT_CALLABLE: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "not-callable");
pub const ARITY: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "arity");
pub const TYPE_MISMATCH: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "type-mismatch");
pub const UNUSED_VALUE: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "unused-value");
pub const CANNOT_INFER: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "cannot-infer");
pub const INTEGER_RANGE: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "integer-range");
pub const UNSUPPORTED: DiagnosticCode = DiagnosticCode::new(SEMANTIC, "unsupported");
