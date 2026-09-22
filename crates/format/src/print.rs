//! The printer: one pass over a [`Plan`]'s gaps, deciding each group where it opens and emitting
//! the edits that format the source.

use std::ops::Range;

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{ParserInput, SigIdx};
use sumi_text::{TextEdit, TextRange};

use crate::plan::{Breaks, Closer, Flat, Group, INDENT, Plan, WIDTH};
use crate::trivia::{GapSignal, marks, signal};

/// `gap` indexes the plan's gaps.
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
    let width = |text: &str| {
        if text.is_ascii() {
            text.len()
        } else {
            text.chars().count()
        }
    };

    let token_width: Vec<u32> = (0..n).map(|sig| width(token_text(sig)) as u32).collect();
    let mut hard_before = vec![0u32; n + 2];
    for gap in 0..=n {
        hard_before[gap + 1] = hard_before[gap] + u32::from(plan.gaps[gap].breaks == Breaks::Hard);
    }
    let hard_in = |from: u32, to: u32| hard_before[to as usize] > hard_before[from as usize];
    let forced = |group: &Group| match group.tail {
        Some((from, to)) => hard_in(group.first, from) || hard_in(to, group.end),
        None => hard_in(group.first, group.end),
    };

    let trivia_range = |gap: usize| -> Range<RawIdx> {
        let mut range = input.trivia_before(SigIdx::new(gap as u32));
        if gap > 0 && plan.layout_comma[gap - 1] {
            range.start = input.trivia_before(SigIdx::new(gap as u32 - 1)).start;
        }
        range
    };
    let trivia_tokens = |gap: usize| {
        let range = trivia_range(gap);
        let comma = (gap > 0 && plan.layout_comma[gap - 1]).then(|| raw_of(gap - 1));
        range
            .start
            .until(range.end)
            .filter(move |&raw| Some(raw) != comma)
    };
    let flat_trivia_width = |gap: usize| -> usize {
        let range = trivia_range(gap);
        range
            .start
            .until(range.end)
            .map(|raw| width(lexed.text(source, raw)))
            .sum()
    };

    let marks = marks(lexed, input);
    let mut broken = vec![false; plan.groups.len()];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_group = 0;
    let mut column = 0usize;
    let mut edits = Vec::new();
    let mut out = String::new();

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
            broken[g] = forced(&group) || {
                let mut w = 0usize;
                let mut fits = true;
                let mut k = gap;
                loop {
                    let plan_gap = plan.gaps[k];
                    let comma = usize::from(plan_gap.closer == Some(Closer::List));
                    if plan_gap.breaks == Breaks::Hard {
                        w += comma;
                        break;
                    }
                    let soft = plan_gap.breaks == Breaks::Soft;
                    if soft && group.in_tail(k as u32) {
                        break;
                    }
                    if k as u32 >= group.end && soft {
                        let enclosing = stack
                            .iter()
                            .rev()
                            .find(|&&open| plan.groups[open].end > k as u32);
                        if enclosing.is_some_and(|&open| broken[open]) {
                            w += comma;
                            break;
                        }
                        if enclosing.is_some_and(|&open| plan.groups[open].in_tail(k as u32)) {
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
                        w += token_width[k] as usize;
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

        if gap < n && plan.layout_comma[gap] {
            continue;
        }
        let plan_gap = plan.gaps[gap];
        let trivia = trivia_range(gap);
        let input_range = TextRange::new(lexed.boundary(trivia.start), lexed.boundary(trivia.end));
        let input_text = input_range.text(source);
        let text: &str = if plan_gap.frozen {
            input_text
        } else {
            let breaks = match plan_gap.breaks {
                Breaks::Never => false,
                Breaks::Soft => stack.last().is_some_and(|&open| broken[open]),
                Breaks::Hard => true,
            };
            let merged = if gap > 0 && plan.layout_comma[gap - 1] {
                marks[gap - 1]
            } else {
                0
            };
            let sig = if marks[gap].saturating_add(merged) >= 2 {
                signal(source, lexed, input, gap, trivia_tokens(gap))
            } else {
                GapSignal::default()
            };
            out.clear();
            if plan_gap.closer == Some(Closer::List) && breaks {
                out.push(',');
            }
            let extra = || {
                stack
                    .iter()
                    .filter(|&&open| broken[open] && plan.groups[open].in_tail(gap as u32))
                    .count() as u32
            };
            let indent = |out: &mut String, level: u32| {
                for _ in 0..level + extra() {
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
                    indent(&mut out, plan_gap.comment_level());
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
            &out
        };
        match text.rfind('\n') {
            Some(at) => column = width(&text[at + 1..]),
            None => column += width(text),
        }
        if text != input_text {
            edits.push(GapEdit {
                gap,
                edit: TextEdit::new(input_range, text.to_owned()),
            });
        }
        if gap < n && !plan.layout_comma[gap] {
            column += token_width[gap] as usize;
        }
    }
    edits
}
