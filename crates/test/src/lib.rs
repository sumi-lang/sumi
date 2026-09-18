//! What the tests share: generators, edits, and the invariants.
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
//! allows. The checks state each layer's invariants once, for the property
//! tests and the fuzz targets alike. Nothing here ships: this crate sits
//! above every other, and production crates must not depend on it.

pub mod check;
pub mod corpus;
pub mod coverage;
mod edit;
mod front;
mod perturb;
mod program;

use proptest::test_runner::{Config, FileFailurePersistence};

pub use edit::{
    Edit, EditSpan, INSERTS, apply, changes_delimiter, delimiter_edited_program, edit,
    edited_program, non_delimiter_edited_program,
};
pub use front::{Front, front};
pub use perturb::perturbed_program;
pub use program::{Programs, program};

/// The configuration of a property test under `tests/`: every failing
/// seed is recorded in `file`, the crate's tracked `proptest-regressions/`
/// file, which each later run replays before generating anything new, so
/// a failure found once stays found. Proptest's default location is found
/// by walking up from the test file to a `lib.rs`, which a test under
/// `tests/` never reaches.
pub fn regressions(file: &'static str) -> Config {
    Config {
        failure_persistence: Some(Box::new(FileFailurePersistence::Direct(file))),
        ..Config::default()
    }
}
