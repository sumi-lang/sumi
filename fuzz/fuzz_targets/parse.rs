//! The whole frontend over arbitrary text: every syntactic product is
//! built and every structural invariant of the token stream, the tree, the
//! evidence, the diagnostics, and formatting is checked.

#![no_main]

use libfuzzer_sys::fuzz_target;
use sumi_frontend::parse_source;
use sumi_test::check;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };
    let parsed = parse_source(source.into()).expect("fuzz inputs fit in u32");
    let lexed = parsed.lexed();
    let parse = parsed.parse();

    check::lexed(source, lexed);
    check::input(lexed, parse.input());
    check::widening(source, lexed, parse.input());
    check::parse(source, lexed, parse);
    check::diagnostics(&parsed);
    check::format(source);
});
