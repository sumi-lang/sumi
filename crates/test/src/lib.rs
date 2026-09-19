//! What the tests share: generators, edits, layout perturbation, the coverage account, the
//! invariant checks, and the corpus runner. Nothing ships it: it sits above every crate, so no
//! production crate may depend on it.

pub mod bench;
pub mod check;
pub mod corpus;
pub mod coverage;
mod edit;
mod front;
mod perturb;
mod program;

use proptest::test_runner::{Config, FileFailurePersistence};

pub use edit::{
    Edit, EditSpan, INSERTS, apply, changes_delimiter, delimiter_edited_program, edit, edit_input,
    edit_seeds, edited_program, non_delimiter_edited_program,
};
pub use front::{Front, evidence_name, front};
pub use perturb::perturbed_program;
pub use program::{Programs, program};

/// Property-test config persisting failures to `file` in the caller's `proptest-regressions/`;
/// proptest's default path never resolves from `tests/`.
#[macro_export]
macro_rules! regressions {
    ($file:literal) => {
        $crate::regressions(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/proptest-regressions/",
            $file
        ))
    };
}

#[doc(hidden)]
pub fn regressions(file: &'static str) -> Config {
    Config {
        failure_persistence: Some(Box::new(FileFailurePersistence::Direct(file))),
        ..Config::default()
    }
}
