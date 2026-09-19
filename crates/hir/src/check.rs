//! Semantic checking of one file, over the graph lowering built. Demands replay in walk order
//! against the solved evidence, so a conflict is blamed on the first demand that raised it, and an
//! expression the conflict left undetermined satisfies every later demand silently.

use sumi_frontend::ParsedSource;
use sumi_graph::{FunctionId, Graph, GraphBuilder, NodeId, Op, Ty};
use sumi_syntax::ast::{self, View};
use sumi_text::TextRange;

use crate::codes;
use crate::flows::{Demand, DemandKind};
use crate::lower::{self, HeaderResult, Lowered, Source};
use crate::recursion;
use crate::typing::{Expected, Replay, Typing};
use crate::{Analysis, Function, Signature, flows};

pub fn analyze(parsed: ParsedSource) -> Analysis {
    let mut source = Source::new(&parsed);
    let tree = source.tree;
    let items: Vec<_> = ast::SourceFile::cast(tree, tree.root())
        .unwrap()
        .items(tree)
        .collect();
    let mut graph = GraphBuilder::new(tree.len());
    let declared = lower::declare(&mut source, &items, &mut graph);
    let (graph, lowered) = lower::lower(&mut source, &items, &declared, graph);
    let headers = declared.headers;
    let (mut typing, thresholds, demands) = flows::draw(&graph, &lowered, &headers);
    typing.solve(&thresholds);
    let failed = replay(&mut source, &typing, &demands, headers.len());
    let mut functions: Vec<Function> = headers
        .iter()
        .map(|header| Function {
            name: header.name,
            origin: source.range(header.item),
            signature: None,
            complete: false,
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
    divisions(&mut source, &graph, &typing, &lowered, &failed);
    bounds(
        &mut source,
        &graph,
        &typing,
        &lowered,
        &failed,
        &mut functions,
    );
    complete(&graph, &typing, &lowered, &failed, &mut functions);
    let mut diagnostics = source.diagnostics;
    diagnostics.splice(0..0, parsed.diagnostics().iter().cloned());
    diagnostics.sort_by_key(|d| d.primary.start());
    let analysis = Analysis {
        parsed,
        graph,
        settled: typing.settle(),
        input_values: lowered.values,
        result_values: lowered.results,
        functions,
        diagnostics,
    };
    assert!(
        !analysis.is_valid() || analysis.functions.iter().all(|f| f.complete),
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
                    let related = declared.map(|at| (at, "declared here"));
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
        DemandKind::Agree { branches } => {
            for branch in branches {
                replay.branch(branch, actual_class);
            }
            let evidence = *replay.evidence(actual_class);
            if !evidence.is_conflict() {
                return true;
            }
            source.conflict(
                demand.at,
                codes::TYPE_MISMATCH,
                typing,
                &evidence.claims(),
                |types| format!("if branches are {types}"),
            );
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
        // A failed demand, or the callee this inherits from, already reports it.
        if let (HeaderResult::Inferred, Some(evidence), None) = (header.result, evidence, result)
            && lowered.built[index]
            && !failed[index]
            && !evidence.inherited()
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
    typing: &Typing,
    lowered: &Lowered,
    failed: &[bool],
) {
    for obligation in &lowered.obligations {
        if failed[obligation.owner as usize] {
            continue;
        }
        let divisor = typing.may(obligation.divisor);
        if !typing.may(obligation.context).live() || !divisor.ints.contains_zero() {
            continue;
        }
        let message = if divisor.ints.is_zero() {
            "division by zero"
        } else {
            "divisor may be zero"
        };
        let labels = explain_zero(graph, typing, lowered, obligation.divisor);
        source.report(
            source.range(obligation.node),
            codes::DIVISION_BY_ZERO,
            message,
            labels,
        );
    }
}

fn explain_zero(
    graph: &Graph,
    typing: &Typing,
    lowered: &Lowered,
    divisor: NodeId,
) -> Vec<(TextRange, Box<str>)> {
    use std::collections::{HashSet, VecDeque};

    use crate::Ints;

    const LABELS: usize = 4;
    const HOPS: usize = 6;
    let describe = |ints: &Ints, where_: &str| {
        if ints.is_zero() {
            format!("is 0{where_}")
        } else {
            format!("may be 0{where_}: {ints}")
        }
    };
    let mut labels: Vec<(TextRange, Box<str>)> = Vec::new();
    let mut seen = HashSet::new();
    let mut queue = VecDeque::from([(divisor, 0)]);
    while let Some((node, hops)) = queue.pop_front() {
        if labels.len() >= LABELS || !seen.insert(node) {
            continue;
        }
        let may = typing.may(node);
        if !may.ints.contains_zero() {
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
                labels.push((entry.origin, describe(&may.ints, "").into()));
            }
            Op::Copy { .. } => follow(&mut queue, inputs[0], 0),
            Op::Refine { .. } => {
                if may.ints != typing.may(inputs[0]).ints {
                    labels.push((
                        entry.origin,
                        describe(&may.ints, " under this guard").into(),
                    ));
                }
                follow(&mut queue, inputs[0], 1);
            }
            Op::Join { then, else_, .. } => {
                for region in std::iter::once(then).chain(else_) {
                    let region = graph.region(region);
                    if typing.may(region.context).live() {
                        follow(&mut queue, region.result(), 1);
                    }
                }
            }
            Op::Call(callee) => {
                let function = graph.callable(callee).function;
                follow(&mut queue, graph.run(function).result(), 1);
            }
            Op::Param { index, .. } => {
                // Runs are contiguous in declaration order.
                let callee = graph
                    .runs()
                    .partition_point(|run| run.entry().index() <= node.index())
                    - 1;
                let callee = FunctionId::new(callee);
                for call in lowered.calls.iter().filter(|call| call.callee == callee) {
                    if labels.len() >= LABELS {
                        break;
                    }
                    if !typing.may(call.context).live() {
                        continue;
                    }
                    let arg = graph.inputs(call.node)[index as usize];
                    let delivered = typing.may(arg);
                    if delivered.ints.contains_zero() {
                        labels.push((
                            graph.reads(call.node)[index as usize],
                            format!("argument {}", describe(&delivered.ints, "")).into(),
                        ));
                    }
                }
            }
            Op::Bool(_)
            | Op::Unit
            | Op::Unused
            | Op::Hole
            | Op::Not
            | Op::And { .. }
            | Op::Or { .. }
            | Op::Exactly(_)
            | Op::Entry
            | Op::Then
            | Op::Else
            | Op::Return { .. }
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After
            | Op::Result { .. } => {}
        }
    }
    labels.sort_by_key(|(range, _)| range.start());
    labels
}

fn bounds(
    source: &mut Source<'_>,
    graph: &Graph,
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
    let recursion = recursion::check(graph, lowered, typing, &out_of_scope);
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
        let complete = run.nodes().all(|node| match graph.node(node).op {
            // No value, so nothing to resolve.
            Op::Entry
            | Op::Then
            | Op::Else
            | Op::Unused
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After => true,
            _ if lowered.values[node.index()].iter().any(|&value| !value) => true,
            Op::And {
                lhs_value: false, ..
            }
            | Op::Or {
                lhs_value: false, ..
            }
            | Op::Return { value: false } => true,
            Op::Join {
                values: [false, false],
                ..
            } => true,
            // A caller's demand can resolve the call without the callee resolving.
            Op::Call(callee) => functions[graph.callable(callee).function.index()]
                .signature
                .as_ref()
                .is_some_and(|signature| Some(signature.result) == typing.resolve(node)),
            _ => typing.resolve(node).is_some(),
        });
        functions[index].complete = complete;
    }
}
