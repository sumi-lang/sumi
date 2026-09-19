//! Fuzzes single-edit recovery in `sumi-syntax`, feeding `sumi-test`'s recovery check arbitrary
//! bytes in place of the program generator.

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
