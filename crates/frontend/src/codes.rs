//! Stable codes for syntax diagnostics.

use sumi_diagnostics::{DiagnosticCode, DiagnosticGroup};

pub const SYNTAX: DiagnosticGroup = DiagnosticGroup::new("syntax");

pub const UNTERMINATED_STRING: DiagnosticCode = DiagnosticCode::new(SYNTAX, "unterminated-string");
pub const UNTERMINATED_BLOCK_STRING: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "unterminated-block-string");
pub const LONE_CARRIAGE_RETURN: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "lone-carriage-return");
pub const MISPLACED_BOM: DiagnosticCode = DiagnosticCode::new(SYNTAX, "misplaced-bom");
pub const UNKNOWN_CHARACTER: DiagnosticCode = DiagnosticCode::new(SYNTAX, "unknown-character");
pub const RESERVED_IDENTIFIER: DiagnosticCode = DiagnosticCode::new(SYNTAX, "reserved-identifier");

pub const UNKNOWN_SUFFIX: DiagnosticCode = DiagnosticCode::new(SYNTAX, "unknown-suffix");
pub const NONCANONICAL_NUMBER: DiagnosticCode = DiagnosticCode::new(SYNTAX, "noncanonical-number");
pub const UNKNOWN_ESCAPE: DiagnosticCode = DiagnosticCode::new(SYNTAX, "unknown-escape");
pub const UNKNOWN_PUNCTUATION: DiagnosticCode = DiagnosticCode::new(SYNTAX, "unknown-punctuation");
pub const BLOCK_STRING_OPENER_CONTENT: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "block-string-opener-content");
pub const BLOCK_STRING_CLOSER_CONTENT: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "block-string-closer-content");
pub const BLOCK_STRING_INDENTATION: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "block-string-indentation");
pub const UNCLOSED_HOLE: DiagnosticCode = DiagnosticCode::new(SYNTAX, "unclosed-hole");

pub const EXPECTED_ITEM: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-item");
pub const EXPECTED_STATEMENT: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-statement");
pub const EXPECTED_EXPRESSION: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-expression");
pub const EXPECTED_NAME: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-name");
pub const EXPECTED_TYPE: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-type");
pub const EXPECTED_TOKEN: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-token");
pub const EXPECTED_BODY: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-body");
pub const EXPECTED_BOUNDARY: DiagnosticCode = DiagnosticCode::new(SYNTAX, "expected-boundary");
pub const UNEXPECTED_SYNTAX: DiagnosticCode = DiagnosticCode::new(SYNTAX, "unexpected-syntax");
pub const NESTING_TOO_DEEP: DiagnosticCode = DiagnosticCode::new(SYNTAX, "nesting-too-deep");
pub const UNSPACED_BINARY_OPERATOR: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "unspaced-binary-operator");
pub const SPACED_PREFIX_OPERATOR: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "spaced-prefix-operator");
pub const SPACED_LIST_OPENER: DiagnosticCode = DiagnosticCode::new(SYNTAX, "spaced-list-opener");
pub const FUNCTION_NAME_ON_NEXT_LINE: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "function-name-on-next-line");
pub const FUNCTION_ITEM_ON_SAME_LINE: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "function-item-on-same-line");
pub const BINDING_NAME_ON_NEXT_LINE: DiagnosticCode =
    DiagnosticCode::new(SYNTAX, "binding-name-on-next-line");
pub const CHAINED_COMPARISON: DiagnosticCode = DiagnosticCode::new(SYNTAX, "chained-comparison");
