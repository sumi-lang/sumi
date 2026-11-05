//! Semantic checking of one file, over the graph lowering built. Demands replay in walk order
//! against the solved evidence, so a conflict is blamed on the first demand that raised it, and an
//! expression the conflict left undetermined satisfies every later demand silently.

use sumi_frontend::{Diagnostic, ParsedSource};
use sumi_graph::{DeclId, FunctionId, Graph, GraphBuilder, NodeId, Op, Ty};
use sumi_syntax::ast::{self, View};
use sumi_text::TextRange;

use crate::codes;
use crate::flows::{Declared, Demand, DemandKind};
use crate::lower::{self, Call, HeaderResult, Lowered, Source};
use crate::spans::Spans;
use crate::typing::{Expected, Replay, Typing};
use crate::{Analysis, FieldDecl, Function, Ints, Occurrence, Symbol, TypeDecl, flows};
use crate::{reachability, recursion};

pub fn analyze(parsed: ParsedSource) -> Analysis {
    let mut source = Source::new(&parsed);
    let tree = source.tree;
    let items: Vec<_> = ast::SourceFile::cast(tree, tree.root())
        .unwrap()
        .items(tree)
        .collect();
    let functions: Vec<_> = items
        .iter()
        .filter_map(|item| match item {
            ast::Item::FnItem(item) => Some(*item),
            ast::Item::TypeItem(_) => None,
        })
        .collect();
    let mut graph = GraphBuilder::new(tree.len());
    let declared = lower::declare(&mut source, &items, &mut graph);
    let (graph, spans, lowered) = lower::lower(&mut source, &functions, &declared, graph);
    let headers = declared.headers;
    let types = declared.types;
    let (mut typing, cx, demands) = flows::draw(
        &graph,
        &spans,
        &lowered,
        &headers,
        &types,
        flows::Arguments::Delivered,
        source.unions.clone(),
    );
    typing.solve(&cx);
    let failed = replay(&mut source, &graph, &typing, &demands, headers.len());
    let mut functions: Vec<Function> = headers
        .iter()
        .map(|header| Function {
            name: header.name,
            origin: source.range(header.item),
            result: None,
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
    exhaustive(
        &mut source,
        &graph,
        &spans,
        &lowered,
        &headers,
        &types,
        &failed,
    );
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
        reachability::warn(
            &mut source,
            &graph,
            &spans,
            &typing,
            &lowered,
            &headers,
            &types,
        )
    };
    let decls = types
        .iter()
        .zip(&source.decls)
        .map(|(header, names)| TypeDecl {
            name: header.name,
            origin: source.range(header.item),
            fields: names
                .fields
                .iter()
                .zip(&header.fields)
                .map(|(&(name, _), &range)| FieldDecl {
                    name: range,
                    text: name.into(),
                })
                .collect(),
        })
        .collect();
    let field_names = source.field_names.iter().map(|&name| name.into()).collect();
    let settled = typing.settle();
    let unions = settled.unions().clone();
    let mut references = lowered.references;
    let sorted = references.len();
    for &(node, range) in &lowered.field_reads {
        let base = graph.inputs(node)[0];
        if let Some(decl) = settled.resolve(base).and_then(Ty::as_decl)
            && let Op::Field(name) = graph.node(node).op
            && let Some(index) = graph.decl(decl).index_of(name)
        {
            references.push(Occurrence {
                range,
                symbol: Symbol::Field(decl, index as u32),
                is_write: false,
            });
        }
    }
    if references.len() > sorted {
        references.sort_unstable_by_key(|occurrence| occurrence.range.start());
    }
    let mut diagnostics = source.diagnostics;
    diagnostics.splice(0..0, parsed.diagnostics().iter().cloned());
    diagnostics.sort_by_key(|d| d.primary.start());
    let analysis = Analysis {
        parsed,
        graph,
        spans,
        settled,
        functions,
        decls,
        field_names,
        unions,
        bindings: lowered.bindings,
        references,
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
    graph: &Graph,
    typing: &Typing,
    demands: &[Demand],
    functions: usize,
) -> Vec<bool> {
    let mut replay = typing.replay();
    let mut failed = vec![false; functions];
    for demand in demands {
        if !holds(source, graph, typing, &mut replay, demand) {
            failed[demand.owner as usize] = true;
        }
    }
    failed
}

fn holds(
    source: &mut Source<'_>,
    graph: &Graph,
    typing: &Typing,
    replay: &mut Replay,
    demand: &Demand,
) -> bool {
    let actual_class = demand.actual;
    let actual = replay.resolve(actual_class);
    match &demand.kind {
        &DemandKind::Field(name) => {
            let Some(ty) = actual else {
                return true;
            };
            if let Some(decl) = ty.as_decl()
                && graph.decl(decl).index_of(name).is_some()
            {
                return true;
            }
            let declared = ty.as_decl().and_then(|decl| {
                let decl = &source.decls[decl.index()];
                decl.name_node
                    .map(|node| (source.range(node), "declared here"))
            });
            source.report(
                demand.at,
                codes::UNKNOWN_FIELD,
                format!(
                    "`{}` has no field `{}`",
                    source.show(ty),
                    source.field_names[name.index()]
                ),
                declared.map(|(range, message)| (range, Box::from(message))),
            );
        }
        DemandKind::Matched => {
            let Some(ty) = actual.filter(|ty| !ty.is_declared()) else {
                return true;
            };
            source.report(
                demand.at,
                codes::TYPE_MISMATCH,
                format!(
                    "cannot match on {} values; `match` takes a value of a declared type",
                    source.show(ty)
                ),
                [],
            );
        }
        &DemandKind::Member(member) => {
            let Some(ty) = actual.filter(|ty| ty.is_declared() && !typing.fits(member, *ty)) else {
                return true;
            };
            source.report(
                demand.at,
                codes::TYPE_MISMATCH,
                format!(
                    "`{}` is no member of `{}`",
                    source.show(member),
                    source.show(ty)
                ),
                [],
            );
        }
        &DemandKind::Type { expected, declared } => {
            let expected_ty = match expected {
                Expected::Ty(ty) => Some(ty),
                Expected::Peer(peer) => replay.resolve(peer),
            };
            match (actual, expected_ty) {
                (Some(actual), Some(expected)) if !typing.fits(actual, expected) => {
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
            Some(ty) if ty != Ty::UNIT => source.report(
                demand.at,
                codes::UNUSED_VALUE,
                format!(
                    "unused value of type {}; use `_ =` to discard it",
                    source.show(ty)
                ),
                [],
            ),
            _ => {
                replay.expect(actual_class, Expected::Ty(Ty::UNIT));
                return true;
            }
        },
        DemandKind::Comparable => {
            let Some(ty) = actual.filter(|ty| *ty == Ty::UNIT || ty.is_declared()) else {
                return true;
            };
            source.report(
                demand.at,
                codes::TYPE_MISMATCH,
                format!("{} values cannot be compared", source.show(ty)),
                [],
            );
        }
        DemandKind::Agree { branches, at } => {
            // An arm is labeled where its value is read, whatever its claim's own origin.
            let arms: Vec<Option<(Ty, TextRange)>> = branches
                .iter()
                .zip(at)
                .map(|(&branch, &at)| replay.resolve(branch).zip(Some(at)))
                .collect();
            for &branch in branches {
                replay.branch(branch, actual_class);
            }
            let evidence = replay.evidence(actual_class).clone();
            if !evidence.is_conflict() {
                return true;
            }
            let what = if is_boolean_switch(graph, actual_class) {
                "if branches"
            } else {
                "match arms"
            };
            let message = |types| format!("{what} are {types}");
            let claims = evidence.claims();
            let resolved: Vec<(Ty, Option<TextRange>)> = arms
                .iter()
                .flatten()
                .map(|&(ty, at)| (ty, Some(at)))
                .collect();
            let mut distinct: Vec<Ty> = resolved.iter().map(|&(ty, _)| ty).collect();
            distinct.sort_unstable();
            distinct.dedup();
            // The arms alone made the conflict; another type has come in by aliasing otherwise.
            if resolved.len() == arms.len() && distinct.len() == claims.len() && distinct.len() > 1
            {
                source.conflict_at(demand.at, codes::TYPE_MISMATCH, resolved, message);
            } else {
                source.conflict(demand.at, codes::TYPE_MISMATCH, typing, &claims, message);
            }
        }
    }
    false
}

/// Whether the switch at `node` selects on a boolean.
fn is_boolean_switch(graph: &Graph, node: NodeId) -> bool {
    match graph.node(node).op {
        Op::Switch { arms } => arms.iter().all(|arm| {
            matches!(
                graph.case(graph.region(arm).context),
                sumi_graph::Case::Bool(_)
            )
        }),
        _ => false,
    }
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
            (!matches!(header.result, HeaderResult::None)).then(|| typing.evidence(run.result()));
        let result = evidence.and_then(|_| typing.resolve(run.result()));
        if run.param_types().is_some() {
            functions[index].result = result;
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

/// A `match` covers every member its scrutinee may hold whatever the arguments: the solve with
/// every parameter at every value of its type decides, so no caller changes the verdict.
fn exhaustive(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    lowered: &Lowered,
    headers: &[lower::Header],
    types: &[lower::TypeHeader],
    failed: &[bool],
) {
    let mut switches: Vec<(NodeId, sumi_graph::Arms)> = Vec::new();
    for (index, run) in graph.runs().iter().enumerate() {
        if failed[index] || !lowered.built[index] {
            continue;
        }
        for node in run.nodes() {
            if let Op::Switch { arms } = graph.node(node).op
                && !is_boolean_switch(graph, node)
                && graph.input_roles(node)[0].is_value()
            {
                switches.push((node, arms));
            }
        }
    }
    if switches.is_empty() {
        return;
    }
    let (mut any, cx, _) = flows::draw(
        graph,
        spans,
        lowered,
        headers,
        types,
        flows::Arguments::Any,
        source.unions.clone(),
    );
    any.solve(&cx);
    let unions = graph.unions();
    for (node, arms) in switches {
        let scrutinee = graph.inputs(node)[0];
        let fact = any.may(scrutinee);
        let mut missing: Vec<DeclId> = Vec::new();
        for (decl, _) in fact.decls.iter() {
            let covered = arms
                .iter()
                .any(|arm| match graph.case(graph.region(arm).context) {
                    sumi_graph::Case::Is(ty) => unions.admits(ty, decl),
                    sumi_graph::Case::Not(_) | sumi_graph::Case::Any => true,
                    sumi_graph::Case::Bool(_) => false,
                });
            if !covered {
                missing.push(decl);
            }
        }
        if missing.is_empty() {
            continue;
        }
        let names: Vec<String> = missing
            .iter()
            .map(|&decl| format!("`{}`", source.decls[decl.index()].name))
            .collect();
        source.report(
            spans.origin(node),
            codes::NON_EXHAUSTIVE_MATCH,
            format!("match has no arm for {}", lower::join(&names)),
            [],
        );
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
            Op::Int(_) | Op::Neg | Op::Binary(_) | Op::Field(_) => {
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
                for ((&value, &context), &role) in inputs[1..]
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
            Op::Switch { arms } => {
                for arm in arms.iter() {
                    let region = graph.region(arm);
                    if region.result_has_value() && typing.may(region.context).is_live() {
                        follow(&mut queue, region.result(), 1);
                    }
                }
            }
            Op::Narrow(_) => follow(&mut queue, inputs[0], 0),
            Op::Call(callee) => {
                let function = callee;
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
            | Op::Make(_)
            | Op::Loop { .. }
            | Op::Unused
            | Op::Hole
            | Op::Not
            | Op::And { .. }
            | Op::Or { .. }
            | Op::Exactly(_)
            | Op::Entry
            | Op::Arm(_)
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
        if failed[index] || !lowered.built[index] || functions[index].result.is_none() {
            continue;
        }
        let run = graph.run(FunctionId::new(index));
        let is_complete = run.nodes().all(|node| match graph.node(node).op {
            // No value, so nothing to resolve.
            Op::Entry | Op::Arm(_) | Op::Unused | Op::Sequence | Op::Observe { .. } | Op::After => {
                true
            }
            Op::Hole => false,
            // A caller's demand can resolve the call without the callee resolving.
            Op::Call(callee) => functions[callee.index()]
                .result
                .is_some_and(|result| Some(result) == typing.resolve(node)),
            _ if !graph.input_roles(node).iter().all(|role| role.is_value()) => true,
            Op::Switch { arms } if arms.iter().all(|arm| !graph.region(arm).result_has_value()) => {
                true
            }
            _ => typing.resolve(node).is_some(),
        });
        functions[index].is_complete = is_complete;
    }
}
