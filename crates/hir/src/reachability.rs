//! Warnings about what holds whatever a function is called with: a condition that always decides
//! the same way, and code after a statement that never completes.

use std::collections::HashSet;

use sumi_graph::{BinaryOp, Bools, Graph, Ints, NodeId, Op, RegionId};
use sumi_text::TextRange;

use crate::check::explain;
use crate::codes;
use crate::flows::{self, Arguments};
use crate::lower::{Header, Lowered, Source, Statement};
use crate::typing::Typing;

enum Site {
    If {
        then: RegionId,
        else_: Option<RegionId>,
    },
    /// The left operand of `&&` when `and`, else of `||`.
    Left {
        operator: NodeId,
        and: bool,
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
/// every argument its parameter's type admits.
pub(crate) fn warn(
    source: &mut Source<'_>,
    graph: &Graph,
    delivered: &Typing,
    lowered: &Lowered,
    headers: &[Header],
) {
    // A site is reported only where the program reaches it and both solves decide it, so whether
    // the second solve runs never changes what is reported.
    let conditions: Vec<_> = conditions(graph)
        .into_iter()
        .filter(|condition| {
            delivered.may(condition.parent).live()
                && delivered.may(condition.value).bools != Bools::BOTH
                && !open_on_its_face(graph, condition.value)
        })
        .collect();
    let mut statements: Vec<_> = lowered.statements.iter().collect();
    statements.sort_by_key(|statement| (statement.block.to_usize(), statement.range.start()));
    let stops = |[before, after]: [&Statement; 2], typing: &Typing| {
        before.block == after.block
            && typing.may(before.context).live()
            && !typing.may(after.context).live()
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
            (facts.may(condition.parent).live() && bools.may_true() != bools.may_false())
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
                    .map(|region| (region_origin(region), "this branch never runs")),
            ),
            Site::Left { and, rhs, .. } => (
                format!("condition is always {truth}"),
                (truth != and).then(|| (region_origin(rhs), "the right side never runs")),
            ),
            Site::Right { .. } => (format!("condition is always {truth}"), None),
            Site::Range { .. } if truth => continue,
            Site::Range { body } => (
                "range is always empty".to_owned(),
                Some((region_origin(body), "the loop body never runs")),
            ),
        };
        let mut labels: Vec<(TextRange, Box<str>)> = dead
            .map(|(at, text)| (at, Box::from(text)))
            .into_iter()
            .collect();
        labels.extend(operands(graph, facts(condition.value), condition.value));
        source.report(condition.at, codes::CONSTANT_CONDITION, message, labels);
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
        source.report(
            TextRange::new(after.range.start(), last.range.end()),
            codes::UNREACHABLE_CODE,
            "unreachable code",
            [(before.range, Box::from("no path continues past this"))],
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
fn open_on_its_face(graph: &Graph, value: NodeId) -> bool {
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
                        and: matches!(op, Op::And { .. }),
                        rhs,
                    },
                });
                let region = graph.region(rhs);
                if region.result_has_value() {
                    conditions.push(Condition {
                        value: region.result(),
                        parent: region.context,
                        at: graph.node(region.context).origin,
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
                    let reads = graph.reads(condition);
                    conditions.push(Condition {
                        value: condition,
                        parent,
                        at: TextRange::new(reads[0].start(), reads[1].end()),
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
