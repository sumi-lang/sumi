//! Warnings about what holds whatever a function is called with: a condition that always decides
//! the same way, code after a statement that never completes, and a function no call reaches.

use std::collections::HashSet;
use std::fmt;

use sumi_graph::{BinaryOp, Bools, Graph, Ints, NodeId, Op, RegionId};
use sumi_text::TextRange;

use crate::check::explain;
use crate::codes;
use crate::flows::{self, Arguments};
use crate::lower::{Header, Lowered, Source, Statement};
use crate::typing::Typing;

/// Code a reachability warning calls dead: no run reaches it, whatever the arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Dead {
    pub range: TextRange,
    pub cause: DeadCause,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeadCause {
    /// An `if` branch its condition never selects.
    Branch,
    /// The right side of `&&` or `||` its left side always decides.
    RightOperand,
    LoopBody,
    /// The statements after one that never completes, to the end of their block.
    AfterStop,
}

impl fmt::Display for DeadCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Branch => "this branch never runs",
            Self::RightOperand => "the right side never runs",
            Self::LoopBody => "the loop body never runs",
            Self::AfterStop => "unreachable code",
        })
    }
}

enum Site {
    If {
        then: RegionId,
        else_: Option<RegionId>,
    },
    /// The left operand of `&&` when `is_and`, else of `||`.
    Left {
        operator: NodeId,
        is_and: bool,
        rhs: RegionId,
    },
    Right {
        operator: NodeId,
    },
    /// Reported only when always empty; a range that always runs is the ordinary case.
    Range {
        body: RegionId,
    },
}

struct Condition {
    value: NodeId,
    /// The context the condition is evaluated in.
    parent: NodeId,
    at: TextRange,
    site: Site,
}

/// `delivered` is the solve over the live call sites' arguments; `headers` redraws the graph with
/// every argument its parameter's type admits. Returns the dead code reported, in source order.
pub(crate) fn warn(
    source: &mut Source<'_>,
    graph: &Graph,
    delivered: &Typing,
    lowered: &Lowered,
    headers: &[Header],
) -> Vec<Dead> {
    unused_functions(source, graph, lowered, headers);
    // A site is reported only where the program reaches it and both solves decide it, so whether
    // the second solve runs never changes what is reported.
    let conditions: Vec<_> = conditions(graph)
        .into_iter()
        .filter(|condition| {
            delivered.may(condition.parent).is_live()
                && delivered.may(condition.value).bools != Bools::BOTH
                && !is_open_on_its_face(graph, condition.value)
        })
        .collect();
    let mut statements: Vec<_> = lowered.statements.iter().collect();
    statements.sort_by_key(|statement| (statement.block.to_usize(), statement.range.start()));
    let stops = |[before, after]: [&Statement; 2], typing: &Typing| {
        before.block == after.block
            && typing.may(before.context).is_live()
            && !typing.may(after.context).is_live()
    };
    let stops_delivered: Vec<bool> = statements
        .windows(2)
        .map(|pair| stops([pair[0], pair[1]], delivered))
        .collect();
    let closed = closed(graph, lowered);
    // Runs are contiguous in declaration order.
    let open = |node: NodeId| {
        !closed[graph
            .runs()
            .partition_point(|run| run.entry().index() <= node.index())
            - 1]
    };
    let any = (conditions.iter().any(|condition| open(condition.value))
        || statements
            .windows(2)
            .zip(&stops_delivered)
            .any(|(pair, &stops)| stops && open(pair[1].context)))
    .then(|| {
        let (mut any, thresholds, _) = flows::draw(graph, lowered, headers, Arguments::Any);
        any.solve(&thresholds);
        any
    });
    let facts = |node: NodeId| match &any {
        Some(any) if open(node) => any,
        _ => delivered,
    };

    let decided: Vec<Option<bool>> = conditions
        .iter()
        .map(|condition| {
            let facts = facts(condition.value);
            let bools = facts.may(condition.value).bools;
            (facts.may(condition.parent).is_live() && bools.may_true() != bools.may_false())
                .then_some(bools.may_true())
        })
        .collect();
    // An operand of a decided condition is reported with it, not on its own.
    let subsumed: HashSet<NodeId> = conditions
        .iter()
        .zip(&decided)
        .filter(|(_, decided)| decided.is_some())
        .map(|(condition, _)| condition.value)
        .collect();
    let mut deads = Vec::new();
    for (condition, &truth) in conditions.iter().zip(&decided) {
        let Some(truth) = truth else {
            continue;
        };
        if let Site::Left { operator, .. } | Site::Right { operator } = condition.site
            && subsumed.contains(&operator)
        {
            continue;
        }
        let region_origin = |region: RegionId| graph.node(graph.region(region).context).origin;
        let (message, dead) = match condition.site {
            Site::If { then, else_ } => (
                format!("condition is always {truth}"),
                if truth { else_ } else { Some(then) }
                    .map(|region| (region_origin(region), DeadCause::Branch)),
            ),
            Site::Left { is_and, rhs, .. } => (
                format!("condition is always {truth}"),
                (truth != is_and).then(|| (region_origin(rhs), DeadCause::RightOperand)),
            ),
            Site::Right { .. } => (format!("condition is always {truth}"), None),
            Site::Range { .. } if truth => continue,
            Site::Range { body } => (
                "range is always empty".to_owned(),
                Some((region_origin(body), DeadCause::LoopBody)),
            ),
        };
        let dead = dead.map(|(range, cause)| Dead { range, cause });
        let mut labels: Vec<(TextRange, Box<str>)> = dead
            .map(|dead| (dead.range, dead.cause.to_string().into()))
            .into_iter()
            .collect();
        labels.extend(operands(graph, facts(condition.value), condition.value));
        source.report(condition.at, codes::CONSTANT_CONDITION, message, labels);
        deads.extend(dead);
    }

    for (index, pair) in statements.windows(2).enumerate() {
        let [before, after] = [pair[0], pair[1]];
        if !stops_delivered[index] || !stops([before, after], facts(after.context)) {
            continue;
        }
        let last = statements[index + 1..]
            .iter()
            .take_while(|statement| statement.block == after.block)
            .last()
            .expect("the dead statement is in its block");
        let dead = Dead {
            range: TextRange::new(after.range.start(), last.range.end()),
            cause: DeadCause::AfterStop,
        };
        source.report(
            dead.range,
            codes::UNREACHABLE_CODE,
            dead.cause.to_string(),
            [(before.range, Box::from("no path continues past this"))],
        );
        deads.push(dead);
    }
    deads.sort_by_key(|dead| (dead.range.start(), dead.range.end()));
    deads
}

/// A function with parameters that no chain of calls from a parameterless or `_`-named one
/// reaches. A call in a branch that never runs still counts, so the verdict never rests on values.
fn unused_functions(source: &mut Source<'_>, graph: &Graph, lowered: &Lowered, headers: &[Header]) {
    let names: Vec<&str> = headers
        .iter()
        .map(|header| {
            let name = header.name.expect("a valid file names its functions");
            name.text(source.parsed.source())
        })
        .collect();
    let mut reached: Vec<bool> = graph
        .runs()
        .iter()
        .zip(&names)
        .map(|(run, name)| run.params().len() == 0 || name.starts_with('_'))
        .collect();
    let mut callees = vec![Vec::new(); reached.len()];
    // Whether anything but the function itself calls it.
    let mut called = vec![false; reached.len()];
    let mut recursive = vec![false; reached.len()];
    for call in &lowered.calls {
        let (caller, callee) = (call.caller.index(), call.callee.index());
        callees[caller].push(callee);
        if caller == callee {
            recursive[callee] = true;
        } else {
            called[callee] = true;
        }
    }
    let mut queue: Vec<usize> = (0..reached.len()).filter(|&f| reached[f]).collect();
    while let Some(function) = queue.pop() {
        for &callee in &callees[function] {
            if !reached[callee] {
                reached[callee] = true;
                queue.push(callee);
            }
        }
    }
    for (index, header) in headers.iter().enumerate() {
        if reached[index] {
            continue;
        }
        let name = names[index];
        let message = match (called[index], recursive[index]) {
            (true, _) => format!("function `{name}` is only called from functions never called"),
            (false, true) => format!("function `{name}` is only called by itself"),
            (false, false) => format!("function `{name}` is never called"),
        };
        source.report(
            header.name.expect("a valid file names its functions"),
            codes::UNUSED_FUNCTION,
            message,
            [],
        );
    }
}

/// Per function, whether neither it nor anything it calls, transitively, takes parameters: its
/// facts are then the same under any arguments.
fn closed(graph: &Graph, lowered: &Lowered) -> Vec<bool> {
    let mut closed: Vec<bool> = graph
        .runs()
        .iter()
        .map(|run| run.params().len() == 0)
        .collect();
    let mut callers = vec![Vec::new(); closed.len()];
    for call in &lowered.calls {
        callers[call.callee.index()].push(call.caller.index());
    }
    let mut opened: Vec<usize> = (0..closed.len()).filter(|&f| !closed[f]).collect();
    while let Some(function) = opened.pop() {
        for &caller in &callers[function] {
            if closed[caller] {
                closed[caller] = false;
                opened.push(caller);
            }
        }
    }
    closed
}

/// Whether any arguments leave `value` open whatever the solve finds: a parameter read as passed,
/// or compared with a literal.
fn is_open_on_its_face(graph: &Graph, value: NodeId) -> bool {
    let param = |node: NodeId| matches!(graph.node(node).op, Op::Param { .. });
    let literal = |node: NodeId| matches!(graph.node(node).op, Op::Int(_) | Op::Bool(_));
    match graph.node(value).op {
        Op::Param { .. } => true,
        Op::Binary(BinaryOp::Cmp(_)) => match *graph.inputs(value) {
            [lhs, rhs] => (param(lhs) && literal(rhs)) || (literal(lhs) && param(rhs)),
            _ => false,
        },
        _ => false,
    }
}

fn conditions(graph: &Graph) -> Vec<Condition> {
    let mut conditions = Vec::new();
    let parent = |region: RegionId| graph.inputs(graph.region(region).context)[1];
    for node in graph.node_ids() {
        let inputs = graph.inputs(node);
        let values = graph.input_values(node);
        match graph.node(node).op {
            Op::Join { then, else_ } if values[0] => conditions.push(Condition {
                value: inputs[0],
                parent: parent(then),
                at: graph.reads(node)[0],
                site: Site::If { then, else_ },
            }),
            ref op @ (Op::And { rhs } | Op::Or { rhs }) if values[0] => {
                conditions.push(Condition {
                    value: inputs[0],
                    parent: parent(rhs),
                    at: graph.reads(node)[0],
                    site: Site::Left {
                        operator: node,
                        is_and: matches!(op, Op::And { .. }),
                        rhs,
                    },
                });
                let region = graph.region(rhs);
                if region.result_has_value() {
                    conditions.push(Condition {
                        value: region.result(),
                        parent: region.context,
                        at: region.result_read(),
                        site: Site::Right { operator: node },
                    });
                }
            }
            Op::Loop(id) => {
                let body = graph.loop_(id).body;
                let context = graph.region(body).context;
                let [condition, parent] = *graph.inputs(context) else {
                    unreachable!("a loop body's context reads its condition and parent")
                };
                if graph.input_values(condition).iter().all(|&value| value) {
                    conditions.push(Condition {
                        value: condition,
                        parent,
                        at: graph.node(condition).origin,
                        site: Site::Range { body },
                    });
                }
            }
            _ => {}
        }
    }
    conditions
}

/// Where a comparison's integer operands get their ranges; a literal operand says it itself.
fn operands(graph: &Graph, typing: &Typing, value: NodeId) -> Vec<(TextRange, Box<str>)> {
    let Op::Binary(BinaryOp::Cmp(_)) = graph.node(value).op else {
        return Vec::new();
    };
    if !graph.input_values(value).iter().all(|&value| value) {
        return Vec::new();
    }
    let mut labels = Vec::new();
    for &operand in graph.inputs(value) {
        if matches!(graph.node(operand).op, Op::Int(_)) {
            continue;
        }
        labels.extend(explain(
            graph,
            typing,
            None,
            operand,
            |ints| !ints.is_empty(),
            describe,
        ));
    }
    labels
}

fn describe(ints: &Ints, where_: &str) -> String {
    match (ints.lo(), ints.hi()) {
        (Some(lo), Some(hi)) if lo == hi => format!("is {lo}{where_}"),
        _ => format!("∈ {ints}{where_}"),
    }
}
