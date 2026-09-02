//! Shared (program, edit) machinery for recovery tests and harnesses.
//!
//! The generator emits well-formed programs the parser must accept without
//! evidence; the edit machinery damages one significant token and maps what
//! an edit must leave alone into the edited source. The recovery property
//! tests in `sumi-syntax` assert quality over these pairs, and any harness
//! measuring it must draw from the same distributions; the recovery
//! scorecard in `xtask` is one. Nothing here ships in the compiler:
//! production crates must not depend on this one, and it depends on
//! nothing above the parser.

pub mod corpus;
mod edit;
mod front;
mod program;

pub use edit::{
    Edit, EditSpan, INSERTS, apply, changes_delimiter, delimiter_edited_program, edit,
    edited_program, non_delimiter_edited_program,
};
pub use front::{Front, front, start_byte};
pub use program::{Programs, program};
