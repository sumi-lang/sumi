//! What each operation needs of its operands to run, held to what is known of them.

use std::borrow::Cow;
use std::collections::HashSet;

use sumi_frontend::DiagnosticCode;
use sumi_graph::{Domain, Graph, Int, Ints, NodeId};

use crate::check::explain;
use crate::codes;
use crate::lower::{Lowered, Need, Obligation, Source};
use crate::spans::Spans;
use crate::typing::Typing;

/// One side of a comparison an operation needs: a node's integer, the length of the sequence a
/// node holds, or zero.
#[derive(Clone, Copy)]
enum Term {
    Value(NodeId),
    Len(NodeId),
    Zero,
}

/// How one side of a comparison an operation needs stands to the other.
#[derive(Clone, Copy)]
enum Rel {
    Below,
    AtMost,
    /// Of zero alone.
    Not,
}

#[derive(Clone, Copy)]
struct Owed {
    lhs: Term,
    rel: Rel,
    rhs: Term,
}

impl Need {
    fn owed(self) -> [Option<Owed>; 2] {
        let owed = |lhs, rel, rhs| Some(Owed { lhs, rel, rhs });
        let value = Term::Value;
        match self {
            Self::Divisor(divisor) => [owed(value(divisor), Rel::Not, Term::Zero), None],
            Self::Element { array, index } => [
                owed(Term::Zero, Rel::AtMost, value(index)),
                owed(value(index), Rel::Below, Term::Len(array)),
            ],
            Self::Last(array) => [owed(Term::Zero, Rel::Below, Term::Len(array)), None],
        }
    }

    fn code(self) -> DiagnosticCode {
        match self {
            Self::Divisor(_) => codes::DIVISION_BY_ZERO,
            Self::Element { .. } | Self::Last(_) => codes::INDEX_OUT_OF_BOUNDS,
        }
    }
}

fn ints(typing: &Typing, term: Term) -> Cow<'_, Ints> {
    match term {
        Term::Value(node) => Cow::Borrowed(&typing.may(node).ints),
        Term::Len(node) => {
            let Ok(len) = typing.may(node).length();
            Cow::Owned(len.ints)
        }
        Term::Zero => Cow::Owned(Ints::from(Int::ZERO)),
    }
}

fn fits(lhs: &Ints, rel: Rel, rhs: &Ints) -> bool {
    match rel {
        Rel::Below => lhs.hi().zip(rhs.lo()).is_some_and(|(hi, lo)| hi < lo),
        Rel::AtMost => lhs.hi().zip(rhs.lo()).is_some_and(|(hi, lo)| hi <= lo),
        Rel::Not => rhs.is_zero() && !lhs.contains_zero(),
    }
}

/// Whether the values that may reach its operands meet what is owed; none where an operand has
/// no value, in an operation that never runs.
fn is_met(typing: &Typing, owed: Owed) -> Option<bool> {
    let (lhs, rhs) = (ints(typing, owed.lhs), ints(typing, owed.rhs));
    (!lhs.is_empty() && !rhs.is_empty()).then(|| fits(&lhs, owed.rel, &rhs))
}

pub(crate) fn check(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    lowered: &Lowered,
    failed: &[bool],
) {
    // A place read and then written, and each instance of its function, needs its indices
    // inside once.
    let mut reported = HashSet::new();
    for obligation in &lowered.obligations {
        if failed[obligation.owner as usize] || !typing.may(obligation.context).is_live() {
            continue;
        }
        let mut owed = obligation.need.owed().into_iter().flatten();
        let is_unmet = owed.try_fold(false, |is_unmet, owed| {
            is_met(typing, owed).map(|is_met| is_unmet || !is_met)
        });
        let is_once =
            matches!(obligation.need, Need::Divisor(_)) || !reported.contains(&obligation.at);
        if is_unmet == Some(true) && is_once {
            report(source, graph, spans, typing, lowered, obligation);
            reported.insert(obligation.at);
        }
    }
}

fn report(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    lowered: &Lowered,
    obligation: &Obligation,
) {
    let calls = &lowered.calls;
    let trace =
        |start, relevant: &dyn Fn(&Ints) -> bool, describe: &dyn Fn(&Ints, &str) -> String| {
            let values = typing.values();
            explain(graph, spans, values, Some(calls), start, relevant, describe)
        };
    let (message, labels) = match obligation.need {
        Need::Divisor(divisor) => {
            let divisor_ints = &typing.may(divisor).ints;
            let message = if divisor_ints.is_zero() {
                "division by zero"
            } else {
                "divisor may be zero"
            };
            let labels = trace(divisor, &Ints::contains_zero, &|ints, where_| {
                if ints.is_zero() {
                    format!("is 0{where_}")
                } else {
                    format!("may be 0{where_}: {ints}")
                }
            });
            (message.to_owned(), labels)
        }
        Need::Last(array) => {
            let len = ints(typing, Term::Len(array));
            let message = if len.is_zero() {
                "the sequence is empty, and has no last element".to_owned()
            } else {
                format!("the sequence may be empty: its length is {len}")
            };
            (message, Vec::new())
        }
        Need::Element { array, index } => {
            let len = ints(typing, Term::Len(array));
            let index_ints = &typing.may(index).ints;
            let least = len.lo().unwrap_or(Int::ZERO);
            // Outside every length the sequence may have, or only some.
            let is_never = index_ints.hi().is_some_and(|hi| hi < Int::ZERO)
                || index_ints
                    .lo()
                    .zip(len.hi())
                    .is_some_and(|(lo, most)| lo >= most);
            let may = if is_never { "is" } else { "may be" };
            let message = format!(
                "index {may} outside the sequence: it is {index_ints}, and the length is {len}"
            );
            let outside = |ints: &Ints| {
                ints.lo().is_none_or(|lo| lo < Int::ZERO) || ints.hi().is_none_or(|hi| hi >= least)
            };
            let labels = trace(index, &outside, &|ints, where_| {
                format!("is {ints}{where_}")
            });
            (message, labels)
        }
    };
    source.report(obligation.at, obligation.need.code(), message, labels);
}
