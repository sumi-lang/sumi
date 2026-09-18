//! The typing drawn from the graph: a class for every node, a fact for
//! every node that knows something on its own account, and a flow for
//! every edge that carries evidence, in one pass over the table. The
//! typing is opened with a class per node, so a node and its class share
//! an index by construction and no map stands between them.
//!
//! Within a function every input precedes its reader, so one pass in node
//! order draws each node's facts and flows as it reaches the node; only a
//! call reaches forward, to a callee whose run may come later in the file,
//! so the flows of calls are drawn once every run is passed. Demands are
//! joined into the evidence last, in the order the walk recorded them,
//! which is the order the verdict pass replays them in.

use sumi_graph::{BinaryOp, Domain, Graph, NodeId, Op, Ty};
use sumi_syntax::NodeIdx;
use sumi_text::Span;

use crate::May;
use crate::check::{Demand, DemandKind, Header, Placed};
use crate::lattice::Edge;
use crate::solver::Var;
use crate::typing::Typing;

/// The class of `node`: the one at its index, since the typing has one
/// class per node.
pub(crate) fn var(node: NodeId) -> Var {
    Var::new(node.index())
}

/// The values that may reach `node`: none for a node nothing flows to.
pub(crate) fn may(typing: &Typing, node: NodeId) -> &May {
    typing.may(var(node))
}

/// Whether the context `node`, or a value at it, is live.
pub(crate) fn live(typing: &Typing, node: NodeId) -> bool {
    may(typing, node).live()
}

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
    let class = var;

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
            let this = class(node);
            match &entry.op {
                Op::Int(value) => typing.literal(this, Ty::Int, May::int(value), origin),
                Op::Bool(value) => typing.literal(this, Ty::Bool, May::bool(*value), origin),
                Op::Param(position) => {
                    let ty = header.param_types[*position as usize].expect("a typed parameter");
                    typing.known(this, ty, entry.name.unwrap_or(origin));
                }
                Op::Entry => {
                    typing.entry(this, header.params.is_some() && run.params().len() == 0);
                }
                // A context under a condition nothing follows is live as
                // its parent is.
                Op::Then | Op::Else if !typed(inputs[0]) => {
                    typing.flow(class(inputs[1]), this, Edge::Copy);
                }
                Op::Then | Op::Else => {
                    let edge = if matches!(entry.op, Op::Then) {
                        Edge::Then
                    } else {
                        Edge::Else
                    };
                    typing.derive(class(inputs[0]), class(inputs[1]), this, edge);
                }
                Op::Refine {
                    op,
                    local_is_lhs,
                    sense,
                } => typing.derive(
                    class(inputs[0]),
                    class(inputs[1]),
                    this,
                    Edge::Refine {
                        op: *op,
                        local_is_lhs: *local_is_lhs,
                        sense: *sense,
                    },
                ),
                Op::Exactly(value) => typing.flow(class(inputs[0]), this, Edge::Exactly(*value)),
                Op::Join {
                    then,
                    else_: Some(else_),
                } => {
                    for region in [*then, *else_] {
                        let region = graph.region(region);
                        typing.derive(
                            class(region.result()),
                            class(region.context),
                            this,
                            Edge::Branch,
                        );
                    }
                }
                // Unit while the `if` itself can run: the context its
                // branch's context derives from.
                Op::Join { then, else_: None } => {
                    typing.known(this, Ty::Unit, origin);
                    let parent = graph.inputs(graph.region(*then).context)[1];
                    typing.flow(class(parent), this, Edge::Enter);
                }
                Op::Unit => {
                    typing.known(this, Ty::Unit, origin);
                    typing.flow(class(inputs[0]), this, Edge::Enter);
                }
                // A declared copy holds what flows in, when something does.
                Op::Copy {
                    declared: Some((ty, at)),
                } => {
                    typing.known(this, *ty, *at);
                    if typed(inputs[0]) {
                        typing.flow(class(inputs[0]), this, Edge::Copy);
                    }
                }
                // An unannotated `let` is its initializer.
                Op::Copy { declared: None } => typing.flow(class(inputs[0]), this, Edge::Bind),
                Op::Neg => {
                    typing.known(this, Ty::Int, origin);
                    typing.flow(class(inputs[0]), this, Edge::Neg);
                }
                Op::Not => {
                    typing.known(this, Ty::Bool, origin);
                    typing.flow(class(inputs[0]), this, Edge::Not);
                }
                Op::Binary(op) => {
                    let ty = match op {
                        BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::Div
                        | BinaryOp::Rem => Ty::Int,
                        BinaryOp::Eq
                        | BinaryOp::Ne
                        | BinaryOp::Lt
                        | BinaryOp::Le
                        | BinaryOp::Gt
                        | BinaryOp::Ge => Ty::Bool,
                    };
                    typing.known(this, ty, origin);
                    typing.derive(class(inputs[0]), class(inputs[1]), this, Edge::Binary(*op));
                }
                Op::And { rhs } | Op::Or { rhs } => {
                    typing.known(this, Ty::Bool, origin);
                    let rhs = graph.region(*rhs).result();
                    typing.derive(
                        class(inputs[0]),
                        class(rhs),
                        this,
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
        typing.flow(class(context), class(entry), Edge::Enter);
    }
    for call in placed.calls() {
        let run = graph.run(call.callee);
        for (&arg, param) in graph.inputs(call.node).iter().zip(run.params()) {
            typing.derive(
                class(arg),
                class(call.context),
                class(param),
                Edge::Argument,
            );
        }
        if typed(call.node) {
            typing.call(
                class(run.result()),
                class(call.node),
                graph.node(call.node).origin,
            );
        }
    }
    // Demands, in the order the walk made them.
    for demand in demands {
        if let DemandKind::Type { expected, .. } = demand.kind {
            typing.expect(class(demand.actual), expected, span(demand.node));
        }
    }
    typing
}
