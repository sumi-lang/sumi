//! Semantic checking of one file, over the graph lowering built: the types, then the values over
//! them, then the verdicts that read both.

use std::collections::HashSet;

use sumi_frontend::{Diagnostic, ParsedSource};
use sumi_graph::{DeclId, FunctionId, Graph, GraphBuilder, NodeId, Op, Ty};
use sumi_syntax::ast::{self, View};
use sumi_text::TextRange;

use crate::codes;
use crate::flows::{AnyValues, Values};
use crate::lower::{self, Call, Lowered, Source};
use crate::spans::Spans;
use crate::summary::Summaries;
use crate::typing::{self, Typing};
use crate::{Analysis, FieldDecl, Function, Ints, Occurrence, Symbol, TypeDecl, flows};
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
    let (graph, spans, lowered, declared) = lower::lower(&mut source, declared, graph);
    let headers = declared.headers;
    let mut functions: Vec<Function> = headers
        .iter()
        .zip(&declared.type_args)
        .map(|(header, type_args)| Function {
            name: header.name,
            origin: source.range(header.item),
            generic: header.generic,
            type_args: type_args.iter().copied().collect(),
            result: None,
            is_complete: false,
            depth: None,
        })
        .collect();
    let checked = typing::check(
        &mut source,
        &graph,
        &spans,
        &lowered,
        &headers,
        &mut functions,
    );
    let failed = checked.failed;
    let sound = failed
        .iter()
        .zip(&lowered.built)
        .map(|(&failed, &built)| built && !failed);
    let sound: Vec<bool> = sound.collect();
    let summaries = Summaries::new(&graph, &lowered, &sound);
    let values = Values::delivered(&graph, &lowered, &summaries);
    let any = AnyValues::new(&graph, &lowered, &summaries);
    let typing = Typing::new(checked.types, values);
    divisions(&mut source, &graph, &spans, &typing, &lowered, &failed);
    exhaustive(
        &mut source,
        &graph,
        &spans,
        &lowered,
        &headers,
        &failed,
        &any,
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
            &any,
        )
    };
    drop(any);
    let decls: Vec<TypeDecl> = source
        .decls
        .iter()
        .enumerate()
        .map(|(index, names)| TypeDecl {
            is_param: source.params.holds(DeclId::new(index)),
            name: names.name_node.map(|node| source.range(node)),
            origin: source.range(names.origin),
            fields: names
                .fields
                .iter()
                .map(|&(name, node)| FieldDecl {
                    name: source.range(node),
                    text: name.into(),
                })
                .collect(),
            generic: names.item,
            type_args: names.args.iter().copied().collect(),
        })
        .collect();
    let field_names = source.field_names.iter().map(|&name| name.into()).collect();
    let unions = source.unions.borrow().clone();
    let mut references = lowered.references;
    let sorted = references.len();
    for &(node, range) in &lowered.field_reads {
        let base = graph.inputs(node)[0];
        if let Some(decl) = typing.resolve(base).and_then(Ty::as_decl)
            && let Op::Field(name) = graph.node(node).op
            && let Some(index) = graph.decl(decl).index_of(name)
        {
            references.push(Occurrence {
                range,
                symbol: Symbol::Field(decls[decl.index()].generic, index as u32),
                is_write: false,
            });
        }
    }
    if references.len() > sorted {
        references.sort_unstable_by_key(|occurrence| occurrence.range.start());
    }
    // Two instances of one generic function may each prove the same of its body.
    let mut reported = HashSet::new();
    let mut diagnostics = source.diagnostics;
    diagnostics.retain(|diagnostic| reported.insert(diagnostic.clone()));
    diagnostics.splice(0..0, parsed.diagnostics().iter().cloned());
    diagnostics.sort_by_key(|d| d.primary.start());
    let analysis = Analysis {
        parsed,
        graph,
        spans,
        typing,
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

/// A `match` covers every member its scrutinee may hold whatever the arguments: the solve with
/// every parameter at every value of its type decides, so no caller changes the verdict.
fn exhaustive(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    lowered: &Lowered,
    headers: &[lower::Header],
    failed: &[bool],
    any: &AnyValues<'_>,
) {
    let mut switches: Vec<(NodeId, sumi_graph::Arms)> = Vec::new();
    for (index, run) in graph.runs().iter().enumerate() {
        // An instance's arms are its item's, which answers for them at its own parameters.
        let is_instance = headers[index].generic.index() != index;
        if failed[index] || !lowered.built[index] || is_instance {
            continue;
        }
        for node in run.nodes() {
            if let Op::Switch { arms } = graph.node(node).op
                && !flows::selection(graph, arms).boolean
                && graph.input_roles(node)[0].is_value()
            {
                switches.push((node, arms));
            }
        }
    }
    if switches.is_empty() {
        return;
    }
    let any = any.get();
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
            .map(|&decl| format!("`{}`", source.show(Ty::decl(decl))))
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
            typing.values(),
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
    values: &Values,
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
        let may = values.may(node);
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
                if values.may(empty).is_live() {
                    follow(&mut queue, graph.inputs(header)[0], 1);
                }
                if values.may(continuation).is_live() {
                    follow(&mut queue, next, 1);
                }
            }
            Op::Phi => {
                for ((&value, &context), &role) in inputs[1..]
                    .iter()
                    .zip(graph.phi_contexts(node))
                    .zip(&graph.input_roles(node)[1..])
                {
                    if role.is_value() && values.may(context).is_live() {
                        follow(&mut queue, value, 1);
                    }
                }
            }
            Op::Refine { .. } => {
                if may.ints != values.may(inputs[0]).ints {
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
                    if region.result_has_value() && values.may(region.context).is_live() {
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
                if graph.input_roles(node)[0].is_value() && values.may(inputs[1]).is_live() {
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
                        && values.may(returned_inputs[1]).is_live()
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
                    if !values.may(call.context).is_live() {
                        continue;
                    }
                    let arg = graph.inputs(call.node)[index as usize];
                    let delivered = values.may(arg);
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
