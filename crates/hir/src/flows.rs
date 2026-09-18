//! The typing drawn from the graph: a class for every node, a fact for
//! every node that knows something on its own account, and a flow for
//! every edge that carries evidence, in one pass over the table. Classes
//! are opened in node order, so a node and its class share an index and
//! no map stands between them.
//!
//! Within a function every input precedes its reader, so one pass in node
//! order draws each node's class and flows as it reaches the node; only a
//! call reaches forward, to a callee whose run may come later in the file,
//! so the flows of calls are drawn once every run is passed. Demands are
//! joined into the evidence last, in the order the walk recorded them,
//! which is the order the verdict pass replays them in.

use sumi_graph::{BinaryOp, Graph, NodeId, Op, Ty};
use sumi_syntax::NodeIdx;
use sumi_text::Span;

use crate::check::{Demand, DemandKind, Header, Placed, Want};
use crate::ranges::{May, RangeEdge, UnaryOp};
use crate::solver::Var;
use crate::typing::{Expected, Typing};

/// The class of `node`: the one opened for it, since every node has a
/// class and they are opened in node order.
pub(crate) fn var(node: NodeId) -> Var {
    Var::new(node.index())
}

/// The typing of the graph: one class per node, in node order, so a node
/// and its class have one index. A node the walk gave no value has a
/// class nothing flows into.
pub(crate) fn draw(
    graph: &Graph,
    placed: &Placed,
    headers: &[Header],
    demands: &[Demand],
    span: impl Fn(NodeIdx) -> Span,
) -> Typing {
    let nodes = graph.nodes().len();
    let mut typing = Typing::for_nodes(nodes);
    let typed = |node: NodeId| placed.typed[node.index()];
    let class = var;

    // Classes, facts, and the flows within a function, in one pass in node
    // order: every input precedes its reader, and a region's context and
    // result precede the node that reads them. Only a call reaches
    // forward, to a callee whose run may come later, so calls flow last.
    for (index, run) in graph.runs().iter().enumerate() {
        let header = &headers[index];
        for node in run.nodes() {
            if !typed(node) {
                let opened = typing.fresh();
                debug_assert_eq!(opened, class(node));
                continue;
            }
            let entry = graph.node(node);
            let origin = entry.origin;
            let inputs = graph.inputs(node);
            let opened = match &entry.op {
                Op::Int(value) => typing.literal(Ty::Int, May::int(value.clone()), origin),
                Op::Bool(value) => typing.literal(Ty::Bool, May::bool(*value), origin),
                Op::Param(position) => {
                    let ty = header.param_types[*position as usize].expect("a typed parameter");
                    typing.known(ty, entry.name.unwrap_or(origin))
                }
                Op::Entry => typing.entry(header.params.is_some() && run.params().len() == 0),
                // A context under a condition nothing follows is live as
                // its parent is.
                Op::Then | Op::Else if !typed(inputs[0]) => {
                    let context = typing.fresh();
                    typing.flow(class(inputs[1]), context, RangeEdge::Copy);
                    context
                }
                Op::Then | Op::Else => {
                    let context = typing.fresh();
                    let edge = if matches!(entry.op, Op::Then) {
                        RangeEdge::Then
                    } else {
                        RangeEdge::Else
                    };
                    typing.derive(class(inputs[0]), class(inputs[1]), context, edge);
                    context
                }
                Op::Refine {
                    op,
                    local_is_lhs,
                    sense,
                } => {
                    let read = typing.fresh();
                    typing.refine(
                        class(inputs[0]),
                        class(inputs[1]),
                        read,
                        RangeEdge::Refine {
                            op: *op,
                            local_is_lhs: *local_is_lhs,
                            sense: *sense,
                        },
                    );
                    read
                }
                Op::Exactly(value) => {
                    let read = typing.fresh();
                    typing.refine_bool(class(inputs[0]), read, *value);
                    read
                }
                Op::Join {
                    then,
                    else_: Some(else_),
                } => {
                    let join = typing.fresh();
                    for region in [*then, *else_] {
                        let region = graph.region(region);
                        typing.branch(class(region.result()), class(region.context), join);
                    }
                    join
                }
                // Unit while the `if` itself can run: the context its
                // branch's context derives from.
                Op::Join { then, else_: None } => {
                    let unit = typing.known(Ty::Unit, origin);
                    let parent = graph.inputs(graph.region(*then).context)[1];
                    typing.flow(class(parent), unit, RangeEdge::Enter);
                    unit
                }
                Op::Unit => {
                    let unit = typing.known(Ty::Unit, origin);
                    typing.flow(class(inputs[0]), unit, RangeEdge::Enter);
                    unit
                }
                // A declared copy holds what flows in, when something does.
                Op::Copy {
                    declared: Some((ty, at)),
                } => {
                    let copy = typing.known(*ty, *at);
                    if typed(inputs[0]) {
                        typing.flow(class(inputs[0]), copy, RangeEdge::Copy);
                    }
                    copy
                }
                // An unannotated `let` is its initializer.
                Op::Copy { declared: None } => {
                    let copy = typing.fresh();
                    typing.copy(class(inputs[0]), copy);
                    copy
                }
                Op::Neg => {
                    let result = typing.known(Ty::Int, origin);
                    typing.flow(class(inputs[0]), result, RangeEdge::Unary(UnaryOp::Neg));
                    result
                }
                Op::Not => {
                    let result = typing.known(Ty::Bool, origin);
                    typing.flow(class(inputs[0]), result, RangeEdge::Unary(UnaryOp::Not));
                    result
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
                    let result = typing.known(ty, origin);
                    typing.derive(
                        class(inputs[0]),
                        class(inputs[1]),
                        result,
                        RangeEdge::Binary(*op),
                    );
                    result
                }
                Op::And { rhs } | Op::Or { rhs } => {
                    let result = typing.known(Ty::Bool, origin);
                    let rhs = graph.region(*rhs).result();
                    typing.derive(
                        class(inputs[0]),
                        class(rhs),
                        result,
                        RangeEdge::Lazy {
                            and: matches!(entry.op, Op::And { .. }),
                        },
                    );
                    result
                }
                Op::Call(_) => typing.fresh(),
                Op::Hole => unreachable!("a hole has no value"),
            };
            debug_assert_eq!(opened, class(node), "one class per node, in order");
        }
    }
    // Every call reaches its callee's entry; a whole one delivers its
    // arguments to the parameters while its context is live, and learns
    // its callee's result, whichever comes first in the file.
    for &(context, callee) in &placed.entered {
        let entry = graph.run(callee).entry();
        typing.flow(class(context), class(entry), RangeEdge::Enter);
    }
    for call in placed.calls() {
        let run = graph.run(call.callee);
        for (&arg, param) in graph.inputs(call.node).iter().zip(run.params()) {
            typing.derive(
                class(arg),
                class(call.context),
                class(param),
                RangeEdge::Argument,
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
        let DemandKind::Type { expected, .. } = demand.kind else {
            continue;
        };
        let expected = self::expected(expected);
        let actual = class(demand.actual);
        if expected == Expected::Peer(actual) {
            continue;
        }
        typing.expect(actual, expected, span(demand.node));
    }
    typing
}

/// What a demand asks, as the typing states it.
pub(crate) fn expected(want: Want) -> Expected {
    match want {
        Want::Ty(ty) => Expected::Ty(ty),
        Want::Peer(peer) => Expected::Peer(var(peer)),
    }
}
