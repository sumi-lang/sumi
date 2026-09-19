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

use sumi_graph::{Domain, Graph, May, NodeId, Op, Ty};
use sumi_syntax::NodeIdx;
use sumi_text::Span;

use crate::check::{Demand, DemandKind, Header, Placed};
use crate::lattice::Edge;
use crate::typing::Typing;

/// The typing of the graph: one class per node, at the node's index. A
/// node the walk gave no value has a class nothing flows into.
pub(crate) fn draw(
    graph: &Graph,
    placed: &Placed,
    headers: &[Header],
    demands: &[Demand],
    span: impl Fn(NodeIdx) -> Span,
) -> Typing {
    let mut typing = Typing::for_nodes(graph.nodes().len());
    let typed = |node: NodeId| placed.typed[node.index()];

    // Facts and the flows within a function, in one pass in node order:
    // every input precedes its reader, and a region's context and result
    // precede the node that reads them. Only a call reaches forward, to a
    // callee whose run may come later, so calls flow last.
    for (index, run) in graph.runs().iter().enumerate() {
        let header = &headers[index];
        for node in run.nodes() {
            if !typed(node) {
                continue;
            }
            let entry = graph.node(node);
            let origin = entry.origin;
            let inputs = graph.inputs(node);
            match &entry.op {
                Op::Int(value) => typing.literal(node, Ty::Int, May::int(value), origin),
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
                }
                Op::Not => {
                    typing.known(node, Ty::Bool, origin);
                    typing.flow(inputs[0], node, Edge::Not);
                }
                Op::Binary(op) => {
                    typing.known(node, op.result(), origin);
                    typing.derive(inputs[0], inputs[1], node, Edge::Binary(*op));
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
                // A call learns its callee's result once every run is
                // passed.
                Op::Call(_) => {}
                Op::Hole => unreachable!("a hole has no value"),
            }
        }
    }
    // Every call reaches its callee's entry; a whole one delivers its
    // arguments to the parameters while its context is live, and learns
    // its callee's result, whichever comes first in the file.
    for &(context, callee) in &placed.entered {
        let entry = graph.run(callee).entry();
        typing.flow(context, entry, Edge::Enter);
    }
    for call in placed.calls() {
        let run = graph.run(call.callee);
        for (&arg, param) in graph.inputs(call.node).iter().zip(run.params()) {
            typing.derive(arg, call.context, param, Edge::Argument);
        }
        if typed(call.node) {
            typing.call(run.result(), call.node, graph.node(call.node).origin);
        }
    }
    // Demands, in the order the walk made them.
    for demand in demands {
        if let DemandKind::Type { expected, .. } = demand.kind {
            typing.expect(demand.actual, expected, span(demand.node));
        }
    }
    typing
}
