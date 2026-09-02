//! The lexer over arbitrary text: total, and a partition of its input.
//! Cheap enough to run an order of magnitude faster than `parse`, which
//! matters for the byte-level literal and number logic this exercises.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };
    let lexed = sumi_lexer::lex(source).expect("fuzz inputs fit in u32");
    sumi_fuzz::check_lexed(source, &lexed);
});
