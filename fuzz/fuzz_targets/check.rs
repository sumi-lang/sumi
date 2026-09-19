//! Scalar analysis over arbitrary text, including damaged syntax.
#![no_main]

use libfuzzer_sys::fuzz_target;
use sumi_test::check;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };
    let parsed = sumi_frontend::parse_source(source.into()).expect("fuzz inputs fit in u32");
    check::semantics(&sumi_hir::analyze(parsed));
});
