//! Semantic checking of one file, over the graph lowering built. Demands replay in walk order
//! against the solved evidence, so a conflict is blamed on the first demand that raised it, and an
//! expression the conflict left undetermined satisfies every later demand silently.

use sumi_frontend::{Diagnostic, ParsedSource};
use sumi_graph::{FunctionId, Graph, GraphBuilder, NodeId, Op, Ty};
use sumi_syntax::ast::{self, View};
use sumi_text::TextRange;

use crate::codes;
use crate::flows::{Declared, Demand, DemandKind};
use crate::lower::{self, Call, HeaderResult, Lowered, Source};
use crate::spans::Spans;
use crate::typing::{Expected, Replay, Typing};
use crate::{Analysis, Function, Ints, Signature, flows};
use crate::{reachability, recursion};

pub fn analyze(parsed: ParsedSource) -> Analysis {
    let mut source = Source::new(&parsed);
    let tree = source.tree;
    let items: Vec<_> = ast::SourceFile::cast(tree, tree.root())
        .unwrap()
        .items(tree)
        .collect();
    let mut graph = GraphBuilder::new(tree.len());
    let declared = lower::declare(&mut source, &items, &mut graph);
    let (graph, spans, lowered) = lower::lower(&mut source, &items, &declared, graph);
    let headers = declared.headers;
    let (mut typing, thresholds, demands) = flows::draw(
        &graph,
        &spans,
        &lowered,
        &headers,
        flows::Arguments::Delivered,
    );
    typing.solve(&thresholds);
    let failed = replay(&mut source, &typing, &demands, headers.len());
    let mut functions: Vec<Function> = headers
        .iter()
        .map(|header| Function {
            name: header.name,
            origin: source.range(header.item),
            signature: None,
            is_complete: false,
            depth: None,
        })
        .collect();
    signatures(
        &mut source,
        &graph,
        &typing,
        &lowered,
        &headers,
        &failed,
        &mut functions,
    );
    divisions(&mut source, &graph, &spans, &typing, &lowered, &failed);
    bounds(
        &mut source,
        &graph,
        &spans,
        &typing,
        &lowered,
        &failed,
        &mut functions,
    );
    complete(&graph, &typing, &lowered, &failed, &mut functions);
    // A rejected file's holes and dropped bodies distort the ranges these warnings rest on.
    let dead = if source
        .diagnostics
        .iter()
        .chain(parsed.diagnostics())
        .any(Diagnostic::is_error)
    {
        Vec::new()
    } else {
        reachability::warn(&mut source, &graph, &spans, &typing, &lowered, &headers)
    };
    let mut diagnostics = source.diagnostics;
    diagnostics.splice(0..0, parsed.diagnostics().iter().cloned());
    diagnostics.sort_by_key(|d| d.primary.start());
    let analysis = Analysis {
        parsed,
        graph,
        spans,
        settled: typing.settle(),
        functions,
        bindings: lowered.bindings,
        references: lowered.references,
        unresolved: lowered.unresolved,
        diagnostics,
        dead,
    };
    assert!(
        !analysis.is_valid() || analysis.functions.iter().all(|f| f.is_complete),
        "incomplete semantic analysis without an error"
    );
    analysis
}

fn replay(
    source: &mut Source<'_>,
    typing: &Typing,
    demands: &[Demand],
    functions: usize,
) -> Vec<bool> {
    let mut replay = typing.replay();
    let mut failed = vec![false; functions];
    for demand in demands {
        if !holds(source, typing, &mut replay, demand) {
            failed[demand.owner as usize] = true;
        }
    }
    failed
}

fn holds(source: &mut Source<'_>, typing: &Typing, replay: &mut Replay, demand: &Demand) -> bool {
    let actual_class = demand.actual;
    let actual = replay.resolve(actual_class);
    match demand.kind {
        DemandKind::Type { expected, declared } => {
            let expected_ty = match expected {
                Expected::Ty(ty) => Some(ty),
                Expected::Peer(peer) => replay.resolve(peer),
            };
            match (actual, expected_ty) {
                (Some(actual), Some(expected)) if actual != expected => {
                    let related = declared.map(|declared| match declared {
                        Declared::Written(at) => (at, "declared here"),
                        Declared::Omitted(at) => {
                            (at, "returns unit, since no result type is written")
                        }
                    });
                    source.type_mismatch(demand.at, expected, actual, related);
                }
                _ => {
                    replay.expect(actual_class, expected);
                    return true;
                }
            }
        }
        DemandKind::Unused => match actual {
            Some(ty) if ty != Ty::Unit => source.report(
                demand.at,
                codes::UNUSED_VALUE,
                format!("unused value of type {ty}; use `_ =` to discard it"),
                [],
            ),
            _ => {
                replay.expect(actual_class, Expected::Ty(Ty::Unit));
                return true;
            }
        },
        DemandKind::Comparable => {
            if actual != Some(Ty::Unit) {
                return true;
            }
            source.report(
                demand.at,
                codes::TYPE_MISMATCH,
                "unit values cannot be compared",
                [],
            );
        }
        DemandKind::Agree { branches, at } => {
            // An arm is labeled where its value is read, whatever its claim's own origin.
            let [then, else_] = [0, 1].map(|arm| replay.resolve(branches[arm]).zip(Some(at[arm])));
            for branch in branches {
                replay.branch(branch, actual_class);
            }
            let evidence = *replay.evidence(actual_class);
            if !evidence.is_conflict() {
                return true;
            }
            let message = |types| format!("if branches are {types}");
            let claims = evidence.claims();
            match (then, else_) {
                // The arms alone made the conflict; a third type has come in by aliasing.
                (Some((then, then_at)), Some((else_, else_at)))
                    if then != else_ && claims.len() == 2 =>
                {
                    let arms = vec![(then, Some(then_at)), (else_, Some(else_at))];
                    source.conflict_at(demand.at, codes::TYPE_MISMATCH, arms, message);
                }
                _ => source.conflict(demand.at, codes::TYPE_MISMATCH, typing, &claims, message),
            }
        }
    }
    false
}

fn signatures(
    source: &mut Source<'_>,
    graph: &Graph,
    typing: &Typing,
    lowered: &Lowered,
    headers: &[lower::Header],
    failed: &[bool],
    functions: &mut [Function],
) {
    for (index, header) in headers.iter().enumerate() {
        let run = graph.run(FunctionId::new(index));
        let evidence =
            (!matches!(header.result, HeaderResult::None)).then(|| *typing.evidence(run.result()));
        let result = evidence.and_then(|evidence| evidence.ty());
        if let (Some(callee), Some(result)) = (header.callee, result) {
            let params = graph.callable(callee).params.clone();
            functions[index].signature = Some(Signature { params, result });
        }
        // A failed demand, a hole, or the callee this inherits from, already reports it.
        if let (HeaderResult::Inferred, Some(evidence), None) = (header.result, evidence, result)
            && lowered.built[index]
            && !failed[index]
            && !evidence.is_unknown()
            && !evidence.is_inherited()
        {
            if evidence.is_conflict() {
                source.conflict(
                    source.range(header.item),
                    codes::CANNOT_INFER,
                    typing,
                    &evidence.claims(),
                    |types| {
                        format!("function result is both {types}; add a return type annotation")
                    },
                );
            } else {
                source.error(
                    header.item,
                    codes::CANNOT_INFER,
                    "cannot infer function result; add a return type annotation",
                    None,
                );
            }
        }
    }
}

fn divisions(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    lowered: &Lowered,
    failed: &[bool],
) {
    for obligation in &lowered.obligations {
        if failed[obligation.owner as usize] {
            continue;
        }
        let divisor = typing.may(obligation.divisor);
        if !typing.may(obligation.context).is_live() || !divisor.ints.contains_zero() {
            continue;
        }
        let message = if divisor.ints.is_zero() {
            "division by zero"
        } else {
            "divisor may be zero"
        };
        let labels = explain(
            graph,
            spans,
            typing,
            Some(&lowered.calls),
            obligation.divisor,
            Ints::contains_zero,
            |ints, where_| {
                if ints.is_zero() {
                    format!("is 0{where_}")
                } else {
                    format!("may be 0{where_}: {ints}")
                }
            },
        );
        source.report(
            source.range(obligation.node),
            codes::DIVISION_BY_ZERO,
            message,
            labels,
        );
    }
}

/// Labels where `start`'s integers come from, crossing at most `HOPS` flows and none into a node
/// whose integers `relevant` rejects. A parameter leads to its callers' arguments only with `calls`.
pub(crate) fn explain(
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    calls: Option<&[Call]>,
    start: NodeId,
    relevant: impl Fn(&Ints) -> bool,
    describe: impl Fn(&Ints, &str) -> String,
) -> Vec<(TextRange, Box<str>)> {
    use std::collections::{HashSet, VecDeque};

    const LABELS: usize = 4;
    const HOPS: usize = 6;
    let mut labels: Vec<(TextRange, Box<str>)> = Vec::new();
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([(start, 0)]);
    while let Some((node, hops)) = queue.pop_front() {
        if labels.len() >= LABELS || !seen.insert(node) {
            continue;
        }
        let may = typing.may(node);
        if !relevant(&may.ints) {
            continue;
        }
        let entry = graph.node(node);
        let inputs = graph.inputs(node);
        let follow = |queue: &mut VecDeque<(NodeId, usize)>, next: NodeId, cost: usize| {
            if hops + cost <= HOPS {
                queue.push_back((next, hops + cost));
            }
        };
        match entry.op {
            Op::Int(_) | Op::Neg | Op::Binary(_) => {
                labels.push((spans.origin(node), describe(&may.ints, "").into()));
            }
            Op::Copy { .. } | Op::Assign => follow(&mut queue, inputs[0], 0),
            Op::LoopIndex | Op::Carry => {
                labels.push((
                    spans.name(node).unwrap_or(spans.origin(node)),
                    describe(&may.ints, " on a loop iteration").into(),
                ));
            }
            Op::LoopValue => {
                let (header, next) = graph.carry(node);
                let [continuation, empty] = graph.loop_contexts(inputs[0]);
                if typing.may(empty).is_live() {
                    follow(&mut queue, graph.inputs(header)[0], 1);
                }
                if typing.may(continuation).is_live() {
                    follow(&mut queue, next, 1);
                }
            }
            Op::Phi => {
                for ((&value, context), &role) in inputs[1..]
                    .iter()
                    .zip(graph.phi_contexts(node))
                    .zip(&graph.input_roles(node)[1..])
                {
                    if role.is_value() && typing.may(context).is_live() {
                        follow(&mut queue, value, 1);
                    }
                }
            }
            Op::Refine { .. } => {
                if may.ints != typing.may(inputs[0]).ints {
                    labels.push((
                        spans.origin(node),
                        describe(&may.ints, " under this guard").into(),
                    ));
                }
                follow(&mut queue, inputs[0], 1);
            }
            Op::Join { then, else_ } => {
                for region in std::iter::once(then).chain(else_) {
                    let region = graph.region(region);
                    if region.result_has_value() && typing.may(region.context).is_live() {
                        follow(&mut queue, region.result(), 1);
                    }
                }
            }
            Op::Call(callee) => {
                let function = graph.callable(callee).function;
                follow(&mut queue, graph.run(function).result(), 1);
            }
            Op::Return => {
                if graph.input_roles(node)[0].is_value() && typing.may(inputs[1]).is_live() {
                    follow(&mut queue, inputs[0], 0);
                }
            }
            Op::Sequence => follow(&mut queue, inputs[1], 0),
            Op::Result { .. } => {
                if graph.input_roles(node)[0].is_value() {
                    follow(&mut queue, inputs[0], 0);
                }
                for &returned in &inputs[1..] {
                    let returned_inputs = graph.inputs(returned);
                    if graph.input_roles(returned)[0].is_value()
                        && typing.may(returned_inputs[1]).is_live()
                    {
                        follow(&mut queue, returned_inputs[0], 1);
                    }
                }
            }
            Op::Param { index, .. } => {
                let Some(calls) = calls else {
                    continue;
                };
                // Runs are contiguous in declaration order.
                let callee = graph
                    .runs()
                    .partition_point(|run| run.entry().index() <= node.index())
                    - 1;
                let callee = FunctionId::new(callee);
                for call in calls.iter().filter(|call| call.callee == callee) {
                    if labels.len() >= LABELS {
                        break;
                    }
                    if !typing.may(call.context).is_live() {
                        continue;
                    }
                    let arg = graph.inputs(call.node)[index as usize];
                    let delivered = typing.may(arg);
                    if relevant(&delivered.ints) {
                        labels.push((
                            spans.reads(call.node)[index as usize],
                            format!("argument {}", describe(&delivered.ints, "")).into(),
                        ));
                    }
                }
            }
            Op::Bool(_)
            | Op::Unit
            | Op::Loop { .. }
            | Op::Unused
            | Op::Hole
            | Op::Not
            | Op::And { .. }
            | Op::Or { .. }
            | Op::Exactly(_)
            | Op::Entry
            | Op::Then
            | Op::Else
            | Op::Observe { .. }
            | Op::After => {}
        }
    }
    labels.sort_by_key(|(range, _)| range.start());
    labels
}

fn bounds(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    lowered: &Lowered,
    failed: &[bool],
    functions: &mut [Function],
) {
    let out_of_scope: Vec<bool> = failed
        .iter()
        .zip(&lowered.built)
        .map(|(&failed, &built)| failed || !built)
        .collect();
    let recursion = recursion::check(graph, spans, lowered, typing, &out_of_scope);
    for failure in recursion.failures {
        let diagnostic = failure.report(functions, source.parsed.source());
        source.diagnostics.push(diagnostic);
    }
    debug_assert_eq!(recursion.depth.len(), functions.len());
    for (function, depth) in functions.iter_mut().zip(recursion.depth) {
        function.depth = depth;
    }
}

fn complete(
    graph: &Graph,
    typing: &Typing,
    lowered: &Lowered,
    failed: &[bool],
    functions: &mut [Function],
) {
    for index in 0..functions.len() {
        if failed[index] || !lowered.built[index] || functions[index].signature.is_none() {
            continue;
        }
        let run = graph.run(FunctionId::new(index));
        let is_complete = run.nodes().all(|node| match graph.node(node).op {
            // No value, so nothing to resolve.
            Op::Entry
            | Op::Then
            | Op::Else
            | Op::Unused
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After => true,
            Op::Hole => false,
            // A caller's demand can resolve the call without the callee resolving.
            Op::Call(callee) => functions[graph.callable(callee).function.index()]
                .signature
                .as_ref()
                .is_some_and(|signature| Some(signature.result) == typing.resolve(node)),
            _ if !graph.input_roles(node).iter().all(|role| role.is_value()) => true,
            Op::Join {
                then,
                else_: Some(else_),
            } if !graph.region(then).result_has_value()
                && !graph.region(else_).result_has_value() =>
            {
                true
            }
            _ => typing.resolve(node).is_some(),
        });
        functions[index].is_complete = is_complete;
    }
}
