//! Recovery after one edit, over arbitrary well-formed sources: the
//! recovery properties of `sumi-syntax` with the fuzzer in place of the
//! program generator. `edit_input` reads the edit, the significant token it
//! lands on, and the source from the bytes. A source the parser does not
//! accept without evidence has no recovery to measure and returns early;
//! coverage feedback is what leads the fuzzer past that gate, since every
//! input that reaches the check covers code no rejected one does.

#![no_main]

use libfuzzer_sys::fuzz_target;
use sumi_test::{check, edit_input, front};

fuzz_target!(|data: &[u8]| {
    let Some((edit, index, source)) = edit_input(data) else {
        return;
    };
    let original = front(source);
    if !original.lexed.errors().is_empty() || !original.parse.evidence().is_empty() {
        return;
    }
    let count = original.parse.input().len();
    if count < 2 {
        return;
    }
    check::recovery(source, &original, usize::from(index) % count, edit);
});
