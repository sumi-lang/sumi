//! The whole frontend over arbitrary text: every syntactic product is
//! built and every structural invariant of the token stream, the tree, the
//! evidence, the diagnostics, and normalization is checked.

#![no_main]

use libfuzzer_sys::fuzz_target;
use sumi_frontend::parse_source;
use sumi_syntax::ParserInput;

fuzz_target!(|data: &[u8]| {
    let Ok(source) = std::str::from_utf8(data) else {
        return;
    };
    let parsed = parse_source(sumi_fuzz::FILE, source.into()).expect("fuzz inputs fit in u32");
    let lexed = parsed.lexed();
    let parse = parsed.parse();
    let input = ParserInput::new(lexed);

    sumi_fuzz::check_lexed(source, lexed);
    sumi_fuzz::check_input(lexed, &input);
    sumi_fuzz::check_tree(parse.tree(), lexed);
    sumi_fuzz::check_parse(source, lexed, &input, parse);
    sumi_fuzz::check_diagnostics(&parsed);
    sumi_fuzz::check_normalize(source, lexed, parse);
    sumi_fuzz::check_widening(source, lexed, &input);
});
