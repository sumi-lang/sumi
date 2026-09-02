//! Recovery after one edit, over arbitrary well-formed sources: the
//! recovery properties of `sumi-syntax` with the fuzzer in place of the
//! program generator. The first byte picks the edit, the next two the
//! significant token it lands on, and the rest is the source. A source the
//! parser does not accept without evidence, or an edit that touches a part
//! of a string literal, has no recovery to measure and returns early;
//! coverage feedback is what leads the fuzzer past that gate, since every
//! input that reaches the check covers code no rejected one does.

#![no_main]

use libfuzzer_sys::fuzz_target;
use sumi_test::{Edit, INSERTS, front, touches_literal};

fuzz_target!(|data: &[u8]| {
    let [kind, low, high, source @ ..] = data else {
        return;
    };
    let Ok(source) = std::str::from_utf8(source) else {
        return;
    };
    let original = front(source);
    if !original.lexed.errors().is_empty() || !original.parse.evidence().is_empty() {
        return;
    }
    let count = original.input.len();
    if count < 2 {
        return;
    }

    let index = usize::from(u16::from_le_bytes([*low, *high])) % count;
    let edit = match kind % 4 {
        0 => Edit::Delete,
        1 => Edit::Duplicate,
        2 => Edit::Swap,
        _ => Edit::Insert(INSERTS[usize::from(kind / 4) % INSERTS.len()]),
    };
    if touches_literal(&original.input, index, edit) {
        return;
    }
    sumi_fuzz::check_recovery(source, &original, index, edit);
});
