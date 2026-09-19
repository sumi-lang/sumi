//! Formatting properties over generated token soup and well-formed programs.

use proptest::prelude::*;
use sumi_format::rep;
use sumi_syntax::SyntaxKind;
use sumi_test::{Front, check, front};

const EXTRA_FRAGMENTS: &[&str] = &[
    "x", "foo", "x = y", "0", "123", "1.5", "1e", "0123", "1u32", "\"abc\"", "\"open", ";", "[",
    " ", "\t", "\n", "\r\n", "\r", "// c", "€",
];

/// Bare soup parses only items; the half wrapped in a body reaches the expression parser, where
/// most violations are recorded.
fn soup() -> impl Strategy<Value = String> {
    let fragments: Vec<&'static str> = SyntaxKind::ALL
        .iter()
        .filter_map(|kind| kind.text())
        .chain(EXTRA_FRAGMENTS.iter().copied())
        .collect();
    let fragments = proptest::collection::vec(prop::sample::select(fragments), 0..48)
        .prop_map(|fragments| fragments.concat());
    prop_oneof![
        1 => fragments.clone(),
        1 => fragments.prop_map(|soup| format!("fn f() {{ {soup} }}")),
    ]
}

fn layout_free<'s>(source: &'s str, front: &Front) -> sumi_format::Rep<'s> {
    rep(source, &front.lexed, &front.parse)
}

proptest! {
    #![proptest_config(sumi_test::regressions!("prop.txt"))]
    #[test]
    fn format_keeps_the_rep_and_settles(source in soup()) {
        check::format(&source);
    }

    #[test]
    fn formatted_lines_fit_the_width(source in sumi_test::program()) {
        let formatted = check::format(&source);
        for line in formatted.text.lines() {
            // A trailing comment may run past the width; code may not.
            let code = line.find(" //").map_or(line, |at| &line[..at]);
            prop_assert!(
                code.chars().count() <= sumi_format::WIDTH,
                "a line of {:?} -> {:?} is wider than {}: {:?}",
                source,
                formatted.text,
                sumi_format::WIDTH,
                line
            );
        }
    }

    #[test]
    fn a_layout_perturbation_formats_to_the_same_text(
        (source, perturbed) in sumi_test::perturbed_program()
    ) {
        let original = front(&source);
        let changed = front(&perturbed);
        prop_assert_eq!(
            layout_free(&perturbed, &changed),
            layout_free(&source, &original),
            "the perturbation of {:?} -> {:?} changed the rep",
            source,
            perturbed
        );
        let formatted = check::format(&source);
        let perturbed_formatted = check::format(&perturbed);
        prop_assert_eq!(
            perturbed_formatted.text,
            formatted.text,
            "formatting {:?} differs from formatting {:?}",
            perturbed,
            source
        );
    }

    #[test]
    fn well_formed_programs_format_without_reverting(source in sumi_test::program()) {
        let formatted = check::format(&source);
        prop_assert_eq!(formatted.reverted, 0, "reverted items in {:?}", source);
        let after = front(&formatted.text);
        prop_assert!(
            after.parse.evidence().is_empty(),
            "formatted {:?} -> {:?} has evidence {:?}",
            source,
            formatted.text,
            after.parse.evidence()
        );
    }
}
