//! Shared (program, edit) machinery for recovery tests and harnesses.
//!
//! The generator emits well-formed programs the parser must accept without
//! evidence; the edit machinery damages one significant token and maps what
//! an edit must leave alone into the edited source. The recovery property
//! tests in `sumi-syntax` assert quality over these pairs, and any harness
//! measuring it must draw from the same distributions; the recovery
//! scorecard in `sumi-scorecard` is one. The layout perturbation rewrites a
//! program's trivia in every way a formatter must ignore, for its
//! canonical-form property. The coverage account says whether a body of
//! trees, the corpus or the generator's, reaches everything the grammar
//! allows. Nothing here ships in the compiler:
//! production crates must not depend on this one, and it depends on
//! nothing above the parser.

pub mod corpus;
pub mod coverage;
mod edit;
mod front;
mod generated;
mod perturb;
mod program;

pub use edit::{
    Edit, EditSpan, INSERTS, apply, changes_delimiter, delimiter_edited_program, edit,
    edited_program, non_delimiter_edited_program,
};
pub use front::{Front, front, start_byte};
pub use perturb::{perturb, perturbed_program};
pub use program::{Programs, program};
