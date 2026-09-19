//! Fuzzes the lexer over arbitrary bytes.

#![no_main]

use libfuzzer_sys::fuzz_target;
use sumi_test::check;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };
    let lexed = sumi_lexer::lex(source).expect("fuzz inputs fit in u32");
    check::lexed(source, &lexed);
});
