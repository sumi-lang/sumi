//! Generators and edits for the recovery, formatting, and coverage
//! properties, and the corpora the harnesses measure. Nothing here ships,
//! and it depends on nothing above the parser.

pub mod corpus;
pub mod coverage;
mod edit;
mod front;
mod perturb;
mod program;

pub use edit::{
    Edit, EditSpan, INSERTS, apply, changes_delimiter, delimiter_edited_program, edit,
    edited_program, non_delimiter_edited_program,
};
pub use front::{Front, front, start_byte};
pub use perturb::perturbed_program;
pub use program::{Programs, program};
