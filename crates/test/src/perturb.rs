//! Layout perturbation of a well-formed program. A rewrite keeps the tokens, tree, comments, and
//! boundary blank lines, so the formatter returns the original.

use proptest::prelude::*;
use sumi_syntax::{NodeKind, SigIdx, SyntaxKind};

use crate::front::front;
use crate::program::program;

/// A well-formed program and a layout perturbation of it.
pub fn perturbed_program() -> impl Strategy<Value = (String, String)> {
    program()
        .prop_flat_map(|source| {
            let gaps = front(&source).input().len() + 1;
            (Just(source), prop::collection::vec(any::<u32>(), gaps))
        })
        .prop_map(|(source, choices)| {
            let perturbed = perturb(&source, &choices);
            (source, perturbed)
        })
}

fn perturb(source: &str, choices: &[u32]) -> String {
    let products = front(source);
    let lexed = &products.lexed;
    let input = products.input();
    let tree = products.parse.tree();
    let n = input.len();
    assert_eq!(choices.len(), n + 1, "one choice per gap");

    // Indexed by gap; at a valid, nonempty list's closer, whether a comma precedes it. The trailing
    // comma is layout to `rep`, so it comes or goes.
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
            // A break between a keyword and its name is parse evidence, and a `(` on a new line
            // opens no list or call.
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
