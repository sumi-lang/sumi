//! Positional token lookup: `token_at` and `token_before`.

use sumi_lexer::lex;
use sumi_text::TextSize;

#[test]
fn every_byte_maps_to_the_token_containing_it() {
    let source = "let x = \"a b\" + 12";
    let file = lex(source).expect("test sources fit in u32");
    for offset in 0..source.len() as u32 {
        let index = file
            .token_at(TextSize::new(offset))
            .expect("every byte lies in a token");
        let range = file.range(index);
        assert!(
            range.start().to_u32() <= offset && offset < range.end().to_u32(),
            "offset {offset} landed in token {index} at {range:?}"
        );
    }
}

#[test]
fn boundaries_are_right_biased_and_token_before_is_left_biased() {
    let source = "ab cd";
    let file = lex(source).expect("test sources fit in u32");
    // The boundary at 2 sits between `ab` (token 0) and the space (token 1).
    let boundary = TextSize::new(2);
    assert_eq!(file.token_at(boundary), Some(1));
    assert_eq!(file.token_before(boundary), Some(0));
    // Inside a token the two biases agree.
    let inside = TextSize::new(1);
    assert_eq!(file.token_at(inside), Some(0));
    assert_eq!(file.token_before(inside), Some(0));
}

#[test]
fn the_edges_of_the_source_have_one_sided_answers() {
    let source = "xy";
    let file = lex(source).expect("test sources fit in u32");
    assert_eq!(file.token_at(TextSize::new(0)), Some(0));
    assert_eq!(file.token_before(TextSize::new(0)), None);
    assert_eq!(file.token_at(TextSize::new(2)), None);
    assert_eq!(file.token_before(TextSize::new(2)), Some(0));
    assert_eq!(file.token_at(TextSize::new(9)), None);
    assert_eq!(file.token_before(TextSize::new(9)), None);
}

#[test]
fn an_empty_source_has_no_tokens_to_find() {
    let file = lex("").expect("test sources fit in u32");
    assert_eq!(file.token_at(TextSize::new(0)), None);
    assert_eq!(file.token_before(TextSize::new(0)), None);
}
