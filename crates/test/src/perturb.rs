//! Layout perturbation of a well-formed program: every rewrite of its
//! trivia that keeps what the formatter must keep — the tokens, the tree,
//! the comments where they stand, and the blank lines at statement and
//! item boundaries — so a formatter with a canonical form must print the
//! perturbed program exactly as the original.
//!
//! A gap that separates two glued tokens stays glued, since gluing is
//! grammar. Every other gap may change its horizontal whitespace, and a
//! gap where the newline rule ends nothing may gain or lose a line break,
//! with any indentation and a blank line after, unless a line break there
//! would separate a keyword from the name it introduces or a `(` from its
//! owner, which the parser reports. A gap holding a comment keeps its
//! line breaks and varies only the whitespace around them. The comma
//! before a list closer is a layout token and comes or goes.

use proptest::prelude::*;
use sumi_syntax::{NodeKind, SigIdx, SyntaxKind};

use crate::front::front;
use crate::program::program;

/// A well-formed program and a layout perturbation of it.
pub fn perturbed_program() -> impl Strategy<Value = (String, String)> {
    program()
        .prop_flat_map(|source| {
            let gaps = front(&source).input.len() + 1;
            (Just(source), prop::collection::vec(any::<u32>(), gaps))
        })
        .prop_map(|(source, choices)| {
            let perturbed = perturb(&source, &choices);
            (source, perturbed)
        })
}

/// Rewrite the trivia of `source`, a well-formed program, as `choices`
/// says, one per gap between significant tokens, the file's edges
/// included.
pub fn perturb(source: &str, choices: &[u32]) -> String {
    let products = front(source);
    let lexed = &products.lexed;
    let input = &products.input;
    let tree = products.parse.tree();
    let n = input.len();
    assert_eq!(choices.len(), n + 1, "one choice per gap");

    // The closer gap of every valid, nonempty list, and whether a comma
    // precedes its closer.
    let mut closers: Vec<Option<bool>> = vec![None; n + 1];
    for node in tree.nodes() {
        if !matches!(tree.kind(node), NodeKind::ArgList | NodeKind::ParamList)
            || tree.has_error(node)
            || tree.children(node).next().is_none()
        {
            continue;
        }
        let closer = lexed.range(tree.end_token(node) - 1);
        let closer = input
            .indices()
            .find(|&sig| lexed.range(input.token(sig)) == closer)
            .expect("a list closer is significant");
        let has_comma = input.get(closer - 1) == Some(SyntaxKind::Comma);
        closers[closer.to_usize()] = Some(has_comma);
    }

    let raw_of = |sig: usize| input.token(SigIdx::new(sig as u32));
    let mut out = String::new();
    for gap in 0..=n {
        let choice = choices[gap];
        let toggle_comma = choice & 1 == 1;
        // A trailing comma the choice removes: the closer gap's choice.
        if gap < n
            && closers.get(gap + 1).copied().flatten() == Some(true)
            && choices[gap + 1] & 1 == 1
        {
            continue;
        }
        let start = if gap == 0 {
            0
        } else {
            (raw_of(gap - 1) + 1).to_usize()
        };
        let end = if gap == n {
            lexed.len()
        } else {
            raw_of(gap).to_usize()
        };
        let trivia: Vec<_> = (start..end)
            .map(|raw| sumi_lexer::RawIdx::new(raw as u32))
            .collect();
        let has_comment = trivia
            .iter()
            .any(|&raw| lexed.kind(raw) == SyntaxKind::LineComment);
        let prev = (gap > 0).then(|| input.get(SigIdx::new(gap as u32 - 1)).expect("in range"));
        let next = (gap < n).then(|| input.get(SigIdx::new(gap as u32)).expect("in range"));

        if let Some(false) = closers[gap]
            && toggle_comma
        {
            out.push(',');
        }

        let boundary = gap < n && gap > 0 && input.boundary_before(SigIdx::new(gap as u32));
        let keep = gap == 0 || gap == n || trivia.is_empty();
        if keep {
            for &raw in &trivia {
                out.push_str(lexed.text(source, raw));
            }
        } else if has_comment || boundary {
            // Line breaks stay; the whitespace around them varies.
            let mut after_newline = false;
            for &raw in &trivia {
                match lexed.kind(raw) {
                    SyntaxKind::Whitespace => {
                        out.push_str(&whitespace(choice, after_newline));
                    }
                    SyntaxKind::Newline => {
                        out.push_str(lexed.text(source, raw));
                        after_newline = true;
                    }
                    _ => out.push_str(lexed.text(source, raw)),
                }
            }
        } else {
            let may_break = !input.would_end_statement(SigIdx::new(gap as u32))
                && next != Some(SyntaxKind::LParen)
                && !matches!(
                    prev,
                    Some(SyntaxKind::FnKw | SyntaxKind::LetKw | SyntaxKind::MutKw)
                );
            match (choice >> 1) % 4 {
                1 if may_break => {
                    out.push('\n');
                    out.push_str(&whitespace(choice, true));
                }
                2 if may_break => {
                    out.push_str(&whitespace(choice, false));
                    out.push_str("\n\n");
                    out.push_str(&whitespace(choice >> 4, true));
                }
                _ => out.push_str(&whitespace(choice, false)),
            }
        }

        if gap < n {
            out.push_str(lexed.text(source, raw_of(gap)));
        }
    }
    out
}

/// Horizontal whitespace drawn from `choice`: at least one space between
/// tokens on a line, any amount at the start of one.
fn whitespace(choice: u32, indentation: bool) -> String {
    let bits = (choice >> 8) & 0xf;
    let count = if indentation {
        (bits % 9) as usize
    } else {
        1 + (bits % 3) as usize
    };
    if bits & 0x8 != 0 && count > 0 {
        "\t".repeat(count.div_ceil(2))
    } else {
        " ".repeat(count)
    }
}
