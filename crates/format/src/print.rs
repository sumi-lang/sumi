//! The printer: one left-to-right pass over the gaps of a [`Plan`],
//! deciding each group where it opens and emitting each gap's separator,
//! as the edits that turn the source into the formatted text.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{ParserInput, SigIdx};
use sumi_text::{TextEdit, TextRange};

use crate::plan::{Flat, INDENT, Plan, WIDTH};
use crate::trivia::signal;

/// One gap's edit: the gap it came from, so a caller can tell which item
/// it lies in, and the edit.
pub(crate) struct GapEdit {
    pub(crate) gap: usize,
    pub(crate) edit: TextEdit,
}

pub(crate) fn print(
    source: &str,
    lexed: &LexedFile,
    input: &ParserInput,
    plan: &Plan,
) -> Vec<GapEdit> {
    let n = input.len();
    let raw_of = |sig: usize| input.token(SigIdx::new(sig as u32));
    let token_text = |sig: usize| lexed.text(source, raw_of(sig));
    let width = |text: &str| text.chars().count();

    // Hard gaps up to each index, so a group's forcing is one subtraction.
    let mut hard_before = vec![0u32; n + 2];
    for gap in 0..=n {
        hard_before[gap + 1] = hard_before[gap] + u32::from(plan.gaps[gap].hard);
    }
    let forced = |first: u32, end: u32| hard_before[end as usize] > hard_before[first as usize];

    // The trivia of gap `gap`, merged with the gap before a layout comma.
    let trivia_range = |gap: usize| -> (RawIdx, RawIdx) {
        let end = if gap == n { lexed.end() } else { raw_of(gap) };
        let mut start = if gap == 0 {
            RawIdx::new(0)
        } else {
            raw_of(gap - 1) + 1
        };
        if gap > 0 && plan.layout_comma[gap - 1] {
            start = if gap >= 2 {
                raw_of(gap - 2) + 1
            } else {
                RawIdx::new(0)
            };
        }
        (start, end)
    };
    let trivia_tokens = |gap: usize| {
        let (start, end) = trivia_range(gap);
        let comma = (gap > 0 && plan.layout_comma[gap - 1]).then(|| raw_of(gap - 1));
        start.until(end).filter(move |&raw| Some(raw) != comma)
    };
    let flat_trivia_width = |gap: usize| -> usize {
        let (start, end) = trivia_range(gap);
        start
            .until(end)
            .map(|raw| width(lexed.text(source, raw)))
            .sum()
    };

    let mut broken = vec![false; plan.groups.len()];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_group = 0;
    let mut column = 0usize;
    let mut edits = Vec::new();

    for gap in 0..=n {
        while stack
            .last()
            .is_some_and(|&g| plan.groups[g].end <= gap as u32)
        {
            stack.pop();
        }
        while next_group < plan.groups.len() && plan.groups[next_group].first == gap as u32 {
            let g = next_group;
            next_group += 1;
            let group = plan.groups[g];
            broken[g] = forced(group.first, group.end) || {
                // Measure from here, every undecided gap flat, to the first
                // gap that will break after the group.
                let mut w = 0usize;
                let mut fits = true;
                let mut k = gap;
                loop {
                    let plan_gap = plan.gaps[k];
                    if plan_gap.hard {
                        break;
                    }
                    if k as u32 >= group.end && plan_gap.breakable {
                        let enclosing = stack
                            .iter()
                            .rev()
                            .find(|&&open| plan.groups[open].end > k as u32);
                        if enclosing.is_some_and(|&open| broken[open]) {
                            break;
                        }
                    }
                    w += if plan_gap.frozen {
                        flat_trivia_width(k)
                    } else {
                        usize::from(plan_gap.flat == Flat::Space)
                    };
                    if k == n {
                        break;
                    }
                    if !plan.layout_comma[k] {
                        w += width(token_text(k));
                    }
                    if column + w > WIDTH {
                        fits = false;
                        break;
                    }
                    k += 1;
                }
                !fits || column + w > WIDTH
            };
            stack.push(g);
        }

        // A layout comma and the gap before it belong to the closer gap.
        if gap < n && plan.layout_comma[gap] {
            continue;
        }
        let plan_gap = plan.gaps[gap];
        let (start, end) = trivia_range(gap);
        let input_range = TextRange::new(lexed.boundary(start), lexed.boundary(end));
        let input_text = input_range.text(source);
        let text: String = if plan_gap.frozen {
            input_text.to_owned()
        } else {
            let breaks = plan_gap.hard
                || (plan_gap.breakable && stack.last().is_some_and(|&open| broken[open]));
            let sig = signal(source, lexed, input, gap, trivia_tokens(gap));
            let mut out = String::new();
            if plan_gap.closer && breaks {
                out.push(',');
            }
            let indent = |out: &mut String, level: u32| {
                for _ in 0..level {
                    out.push_str(INDENT);
                }
            };
            for (k, comment) in sig.comments.iter().enumerate() {
                if comment.trailing {
                    out.push(' ');
                } else {
                    if gap > 0 || k > 0 {
                        out.push('\n');
                    }
                    if comment.blank_before {
                        out.push('\n');
                    }
                    indent(&mut out, plan_gap.comment_level);
                }
                out.push_str(comment.text);
            }
            if gap == n {
                if n > 0 || !sig.comments.is_empty() {
                    out.push('\n');
                }
            } else if !sig.comments.is_empty() || breaks {
                if gap > 0 || !sig.comments.is_empty() {
                    out.push('\n');
                }
                if sig.blank_before_token {
                    out.push('\n');
                }
                indent(&mut out, plan_gap.level);
            } else if plan_gap.flat == Flat::Space {
                out.push(' ');
            }
            out
        };
        match text.rfind('\n') {
            Some(at) => column = width(&text[at + 1..]),
            None => column += width(&text),
        }
        if text != input_text {
            edits.push(GapEdit {
                gap,
                edit: TextEdit::new(input_range, text),
            });
        }
        if gap < n && !plan.layout_comma[gap] {
            column += width(token_text(gap));
        }
    }
    edits
}
