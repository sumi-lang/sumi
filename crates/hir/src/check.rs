//! Semantic checking of one file: the verdicts on what lowering built.
//!
//! The headers are read, the bodies lowered to the graph, and the
//! classes, facts, and flows drawn from it by `flows::draw`, the demands
//! joined in, and the typing solves once. Signatures are read off result
//! classes, independent of declaration order; what may reach each
//! parameter and result is read off the kept evidence whenever asked.
//! Demands are then checked in walk order against the final evidence, so
//! a disagreement is blamed on the first demand that raised it. Every
//! expression has one context, so it is held to one demand; an expression
//! whose type is undetermined, because its branches or its callee
//! disagree, satisfies any demand silently, and the disagreement is
//! reported where it arose. A body is complete when its walk succeeded,
//! none of its demands failed, every value in it resolved, and every call
//! agrees with its callee's signature.

use sumi_syntax::ast::{self, AstNode};

use crate::codes;
use crate::lower::{self, DemandKind, HeaderResult, Lowered, Source};
use crate::recursion;
use crate::typing::{Expected, Replay, Typing};
use crate::{flows, *};

pub fn analyze(parsed: ParsedSource) -> Analysis {
    let mut source = Source::new(&parsed);
    let tree = source.tree;
    let items: Vec<_> = ast::SourceFile::cast(tree, tree.root())
        .unwrap()
        .items(tree)
        .collect();
    let declared = lower::declare(&mut source, &items);
    let (graph, lowered) = lower::lower(&mut source, &items, &declared);
    let headers = declared.headers;
    let (mut typing, thresholds) =
        flows::draw(&graph, &lowered, &headers, |node| source.span(node));
    typing.solve(&thresholds);
    let failed = replay(&mut source, &typing, &lowered);
    let mut functions: Vec<Function> = headers
        .iter()
        .map(|header| Function {
            name: header.name,
            origin: source.span(header.item),
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
        headers,
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
    // One list, in source order: a syntactic diagnostic first where both
    // stand at one position, then the checker's in the order it made them.
    let mut diagnostics = source.diagnostics;
    diagnostics.splice(0..0, parsed.diagnostics().iter().cloned());
    diagnostics.sort_by_key(|d| d.primary.start());
    let analysis = Analysis {
        parsed,
        graph,
        settled: typing.settle(),
        functions,
        diagnostics,
    };
    assert!(
        analysis.is_valid() || !analysis.diagnostics.is_empty(),
        "incomplete semantic analysis without an error"
    );
    analysis
}

/// Every demand checked in the order the walk made it, against the
/// evidence it left: which functions failed one.
fn replay(source: &mut Source<'_>, typing: &Typing, lowered: &Lowered) -> Vec<bool> {
    let mut replay = typing.replay();
    let mut failed = vec![false; lowered.built.len()];
    for demand in &lowered.demands {
        if !holds(source, typing, &mut replay, demand) {
            failed[demand.owner as usize] = true;
        }
    }
    failed
}

/// Whether `demand` holds of the evidence so far, which it joins when it
/// does; reported where it was made when it does not.
fn holds(
    source: &mut Source<'_>,
    typing: &Typing,
    replay: &mut Replay,
    demand: &lower::Demand,
) -> bool {
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
                    let related = declared.map(|node| (source.span(node), "declared here"));
                    source.type_mismatch(demand.node, expected, actual, related);
                }
                _ => {
                    replay.expect(actual_class, expected);
                    return true;
                }
            }
        }
        DemandKind::Unused => match actual {
            Some(ty) if ty != Ty::Unit => source.error(
                demand.node,
                codes::UNUSED_VALUE,
                format!("unused value of type {ty}; use `_ =` to discard it"),
                None,
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
            source.error(
                demand.node,
                codes::TYPE_MISMATCH,
                "unit values cannot be compared",
                None,
            );
        }
        // Each branch delivers what it is so far, and only that: a
        // conflict on the `if` is the branches disagreeing, and nothing
        // else. The `if` then resolves to nothing, so whatever takes its
        // type is held to no type it never had.
        DemandKind::Agree { branches } => {
            for branch in branches {
                replay.branch(branch, actual_class);
            }
            let evidence = *replay.evidence(actual_class);
            if !evidence.is_conflict() {
                return true;
            }
            source.conflict(
                demand.node,
                codes::TYPE_MISMATCH,
                typing,
                &evidence.claims(),
                |types| format!("if branches are {types}"),
            );
        }
    }
    false
}

/// Every signature the result classes give, and a result to infer that
/// did not resolve, reported unless a demand in the body already
/// explained it or the trouble arrived whole from a callee, which reports
/// it at its own declaration.
fn signatures(
    source: &mut Source<'_>,
    graph: &Graph,
    typing: &Typing,
    lowered: &Lowered,
    headers: Vec<lower::Header>,
    failed: &[bool],
    functions: &mut [Function],
) {
    for (index, header) in headers.into_iter().enumerate() {
        let run = graph.run(FunctionId::new(index));
        // The result's evidence: the declared copy's, or the body's
        // value's, when the header says which.
        let evidence =
            (!matches!(header.result, HeaderResult::None)).then(|| *typing.evidence(run.result()));
        let result = evidence.and_then(|evidence| evidence.ty());
        if let (Some(params), Some(result)) = (header.params, result) {
            functions[index].signature = Some(Signature { params, result });
        }
        if let (HeaderResult::Inferred, Some(evidence), None) = (header.result, evidence, result)
            && lowered.built[index]
            && !failed[index]
            && !evidence.inherited()
        {
            if evidence.is_conflict() {
                source.conflict(
                    header.item,
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

/// Every reachable division excludes zero.
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
        let labels = explain_zero(source, graph, typing, lowered, obligation.divisor);
        source.report(
            source.span(obligation.node),
            codes::DIVISION_BY_ZERO,
            message,
            labels,
        );
    }
}

/// Labels for the values that put zero into `divisor`: what it reads,
/// followed through the copies, narrowed reads, branches, calls, and
/// arguments that pass a value along until a literal or an operator
/// produced it.
fn explain_zero(
    source: &Source<'_>,
    graph: &Graph,
    typing: &Typing,
    lowered: &Lowered,
    divisor: NodeId,
) -> Vec<(Span, Box<str>)> {
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
    let mut labels: Vec<(Span, Box<str>)> = Vec::new();
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
            // A `let` passes the value on unchanged, at no distance.
            Op::Copy { .. } => follow(&mut queue, inputs[0], 0),
            // A guard that narrowed the local is where the zero was
            // singled out, and the local is where it came from.
            Op::Refine { .. } => {
                if may.ints != typing.may(inputs[0]).ints {
                    labels.push((
                        entry.origin,
                        describe(&may.ints, " under this guard").into(),
                    ));
                }
                follow(&mut queue, inputs[0], 1);
            }
            Op::Join { then, else_ } => {
                for region in std::iter::once(then).chain(else_) {
                    let region = graph.region(region);
                    if typing.may(region.context).live() {
                        follow(&mut queue, region.result(), 1);
                    }
                }
            }
            Op::Call(callee) => follow(&mut queue, graph.run(callee).result(), 1),
            Op::Param(index) => {
                // Runs are contiguous in declaration order: the parameter's
                // function is the last whose entry precedes it.
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
                        let written = lowered.arguments(call)[index as usize];
                        labels.push((
                            source.span(written),
                            format!("argument {}", describe(&delivered.ints, "")).into(),
                        ));
                    }
                }
            }
            Op::Bool(_)
            | Op::Unit
            | Op::Hole
            | Op::Not
            | Op::And { .. }
            | Op::Or { .. }
            | Op::Exactly(_)
            | Op::Entry
            | Op::Then
            | Op::Else => {}
        }
    }
    labels.sort_by_key(|(span, _)| span.range().start());
    labels
}

/// Every recursion is bounded, and the call depth each function is
/// proved to reach. A function whose body did not build is out of scope
/// like one that failed a verdict.
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

/// A body is complete when it built, none of its demands failed, every
/// value in it resolved, and every call agrees with its callee's
/// signature: a caller's demands can resolve its call's class without
/// resolving the callee, and that is not a complete call.
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
            Op::Entry | Op::Then | Op::Else => true,
            Op::Call(callee) => functions[callee.index()]
                .signature
                .as_ref()
                .is_some_and(|signature| Some(signature.result) == typing.resolve(node)),
            _ => typing.resolve(node).is_some(),
        });
        functions[index].complete = complete;
    }
}
