//! The typing drawn from the graph: a class for every node, a fact for
//! every node that knows something on its own account, and a flow for
//! every edge that carries evidence, in one pass over the table.
//!
//! Within a function every input precedes its reader, so one pass in node
//! order draws each node's facts and flows as it reaches the node; only a
//! call reaches forward, to a callee whose run may come later in the file,
//! so the flows of calls are drawn once every run is passed. Demands are
//! joined into the evidence last, in the order the walk recorded them,
//! which is the order the verdict pass replays them in.

use std::collections::HashSet;

use rustc_hash::FxBuildHasher;
use sumi_graph::{Domain, Graph, Int, May, NodeId, Op, Thresholds, Ty, Value};
use sumi_syntax::NodeIdx;
use sumi_text::TextRange;

use crate::lattice::Edge;
use crate::lower::{DemandKind, Header, Lowered};
use crate::typing::Typing;

/// The typing of the graph, one class per node at the node's index, and
/// the thresholds of the file's constants. A node the walk gave no value
/// has a class nothing flows into. A constant is an integer the file
/// spells, or an operator over constants, which is the constant the
/// machine would compute; each is kept once, in the order first seen.
pub(crate) fn draw(
    graph: &Graph,
    lowered: &Lowered,
    headers: &[Header],
    span: impl Fn(NodeIdx) -> TextRange,
) -> (Typing, Thresholds) {
    let mut typing = Typing::for_nodes(graph.nodes().len());
    let typed = |node: NodeId| lowered.typed[node.index()];
    let mut constants: Vec<Int> = Vec::new();
    let mut seen: HashSet<Int, FxBuildHasher> = HashSet::default();
    // The constant each node of the run folds to, by slot.
    let mut folded: Vec<Option<Int>> = Vec::new();

    for (index, run) in graph.runs().iter().enumerate() {
        let header = &headers[index];
        folded.clear();
        folded.resize(run.nodes().len(), None);
        for node in run.nodes() {
            if !typed(node) {
                continue;
            }
            let entry = graph.node(node);
            let origin = entry.origin;
            let inputs = graph.inputs(node);
            let constant = |index: usize| folded[run.slot(inputs[index])].as_ref();
            let mut folds = None;
            match &entry.op {
                Op::Int(value) => {
                    typing.literal(node, Ty::Int, May::int(value), origin);
                    folds = Some(value.clone());
                }
                Op::Bool(value) => typing.literal(node, Ty::Bool, May::bool(*value), origin),
                Op::Param(position) => {
                    let ty = header.param_types[*position as usize].expect("a typed parameter");
                    typing.known(node, ty, entry.name.unwrap_or(origin));
                }
                Op::Entry => {
                    typing.entry(node, header.params.is_some() && run.params().len() == 0);
                }
                // A context under a condition nothing follows is live as
                // its parent is.
                Op::Then | Op::Else if !typed(inputs[0]) => {
                    typing.flow(inputs[1], node, Edge::Values);
                }
                Op::Then | Op::Else => {
                    let edge = if matches!(entry.op, Op::Then) {
                        Edge::Then
                    } else {
                        Edge::Else
                    };
                    typing.derive(inputs[0], inputs[1], node, edge);
                }
                Op::Refine {
                    op,
                    local_is_lhs,
                    sense,
                } => typing.derive(
                    inputs[0],
                    inputs[1],
                    node,
                    Edge::Refine {
                        op: *op,
                        local_is_lhs: *local_is_lhs,
                        sense: *sense,
                    },
                ),
                Op::Exactly(value) => typing.flow(inputs[0], node, Edge::Exactly(*value)),
                Op::Join {
                    then,
                    else_: Some(else_),
                } => {
                    for region in [*then, *else_] {
                        let region = graph.region(region);
                        typing.derive(region.result(), region.context, node, Edge::Branch);
                    }
                }
                // Unit while the `if` itself can run: the context its
                // branch's context derives from.
                Op::Join { then, else_: None } => {
                    typing.known(node, Ty::Unit, origin);
                    let parent = graph.inputs(graph.region(*then).context)[1];
                    typing.flow(parent, node, Edge::Enter);
                }
                Op::Unit => {
                    typing.known(node, Ty::Unit, origin);
                    typing.flow(inputs[0], node, Edge::Enter);
                }
                // A declared copy holds what flows in, when something does.
                Op::Copy {
                    declared: Some((ty, at)),
                } => {
                    typing.known(node, *ty, *at);
                    if typed(inputs[0]) {
                        typing.flow(inputs[0], node, Edge::Values);
                    }
                }
                // An unannotated `let` is its initializer.
                Op::Copy { declared: None } => typing.flow(inputs[0], node, Edge::Bind),
                Op::Neg => {
                    typing.known(node, Ty::Int, origin);
                    typing.flow(inputs[0], node, Edge::Neg);
                    folds = constant(0).map(|value| -value);
                }
                Op::Not => {
                    typing.known(node, Ty::Bool, origin);
                    typing.flow(inputs[0], node, Edge::Not);
                }
                Op::Binary(op) => {
                    typing.known(node, op.result(), origin);
                    typing.derive(inputs[0], inputs[1], node, Edge::Binary(*op));
                    if let (Some(lhs), Some(rhs)) = (constant(0), constant(1)) {
                        let (lhs, rhs) = (Value::Int(lhs.clone()), Value::Int(rhs.clone()));
                        if let Ok(Value::Int(value)) = Op::Binary(*op).apply(&[&lhs, &rhs]) {
                            folds = Some(value);
                        }
                    }
                }
                Op::And { rhs } | Op::Or { rhs } => {
                    typing.known(node, Ty::Bool, origin);
                    let rhs = graph.region(*rhs).result();
                    typing.derive(
                        inputs[0],
                        rhs,
                        node,
                        Edge::Lazy {
                            and: matches!(entry.op, Op::And { .. }),
                        },
                    );
                }
                // A call's flows are drawn below, once every run is passed.
                Op::Call(_) => {}
                Op::Hole => unreachable!("a hole has no value"),
            }
            if let Some(value) = folds {
                if seen.insert(value.clone()) {
                    constants.push(value.clone());
                }
                folded[run.slot(node)] = Some(value);
            }
        }
    }
    // Every call reaches its callee's entry; a whole one delivers its
    // arguments to the parameters while its context is live, and learns
    // its callee's result.
    for &(context, callee) in &lowered.entered {
        let entry = graph.run(callee).entry();
        typing.flow(context, entry, Edge::Enter);
    }
    for call in &lowered.calls {
        let run = graph.run(call.callee);
        for (&arg, param) in graph.inputs(call.node).iter().zip(run.params()) {
            typing.derive(arg, call.context, param, Edge::Argument);
        }
        if typed(call.node) {
            typing.call(run.result(), call.node, graph.node(call.node).origin);
        }
    }
    for demand in &lowered.demands {
        if let DemandKind::Type { expected, .. } = demand.kind {
            typing.expect(demand.actual, expected, span(demand.node));
        }
    }
    (typing, constants.into_iter().collect())
}
