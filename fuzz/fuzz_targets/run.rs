//! Every accepted file run inside what the analysis proved.
#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };
    let parsed = sumi_frontend::parse_source(source.into()).expect("fuzz inputs fit in u32");
    sumi_fuzz::check_run(parsed);
});
