//! The typing drawn from the graph: a class for every node the walk gave a
//! value, a fact for every node that knows something on its own account,
//! and a flow for every edge that carries evidence, in one pass over the
//! table.
//!
//! Within a function every input precedes its reader, so one pass in node
//! order draws each node's class and flows as it reaches the node; only a
//! call reaches forward, to a callee whose run may come later in the file,
//! so the flows of calls are drawn once every run is passed. Demands are
//! joined into the evidence last, in the order the walk recorded them,
//! which is the order the verdict pass replays them in.

use sumi_graph::{Graph, NodeId, Op, Ty};
use sumi_syntax::NodeIdx;
use sumi_text::Span;

use crate::check::{Demand, DemandKind, Header, Placed, Want};
use crate::ranges::{May, RangeEdge, UnaryOp};
use crate::solver::Var;
use crate::typing::{Expected, Typing};

/// The typing of every node in `placed.classes`, and the result class of
/// every function that has one: a declared result's copy, or a class of
/// its own for a result to infer, which the body's value is one with.
pub(crate) fn draw(
    graph: &Graph,
    placed: &mut Placed,
    headers: &[Header],
    demands: &[Demand],
    span: impl Fn(NodeIdx) -> Span,
) -> (Typing, Vec<Option<Var>>) {
    let nodes = graph.nodes().len();
    let mut typing = Typing::for_nodes(nodes);
    let mut classes: Vec<Option<Var>> = vec![None; nodes];
    let mut results: Vec<Option<Var>> = vec![None; headers.len()];
    let typed = |node: NodeId| placed.typed[node.index()];

    // Classes, facts, and the flows within a function, in one pass in node
    // order: every input precedes its reader, and a region's context and
    // result precede the node that reads them. Only a call reaches
    // forward, to a callee whose run may come later, so calls flow last.
    for (index, run) in graph.runs().iter().enumerate() {
        let header = &headers[index];
        for node in run.nodes() {
            if !typed(node) {
                continue;
            }
            let entry = graph.node(node);
            let origin = entry.origin;
            let inputs = graph.inputs(node);
            let class = |node: NodeId| classes[node.index()].expect("an input has its class");
            let class = match &entry.op {
                Op::Int(value) => typing.literal(Ty::Int, May::int(value.clone()), origin),
                Op::Bool(value) => typing.literal(Ty::Bool, May::bool(*value), origin),
                Op::Param(position) => {
                    let ty = header.param_types[*position as usize].expect("a typed parameter");
                    typing.known(ty, entry.name.unwrap_or(origin))
                }
                Op::Entry => typing.entry(header.params.is_some() && run.params().len() == 0),
                // A context under a condition nothing follows is its parent's.
                Op::Then | Op::Else if !typed(inputs[0]) => class(inputs[1]),
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
                Op::Copy { declared: Some(ty) } => {
                    let copy = typing.known(*ty, origin);
                    if typed(inputs[0]) {
                        typing.flow(class(inputs[0]), copy, RangeEdge::Copy);
                    }
                    copy
                }
                // An unannotated `let` is its initializer.
                Op::Copy { declared: None } => class(inputs[0]),
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
                        sumi_graph::BinaryOp::Add
                        | sumi_graph::BinaryOp::Sub
                        | sumi_graph::BinaryOp::Mul
                        | sumi_graph::BinaryOp::Div
                        | sumi_graph::BinaryOp::Rem => Ty::Int,
                        _ => Ty::Bool,
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
            classes[node.index()] = Some(class);
        }
        results[index] = if !header.has_result {
            None
        } else if header.declared.is_some() {
            classes[run.result().index()]
        } else {
            Some(typing.fresh())
        };
    }
    let class = |node: NodeId| classes[node.index()].expect("a typed node has a class");
    // A call learns its callee's result, whichever comes first in the file.
    for call in placed.calls() {
        if !typed(call.node) {
            continue;
        }
        let result =
            results[call.callee.index()].expect("a call with a value has a callee with one");
        typing.call(result, class(call.node), graph.node(call.node).origin);
    }
    // Every call reaches its callee's entry; a whole one delivers its
    // arguments to the parameters while its context is live.
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
    }
    // Demands, in the order the walk made them.
    for demand in demands {
        let DemandKind::Type { expected, .. } = demand.kind else {
            continue;
        };
        let expected = match expected {
            Want::Ty(ty) => Expected::Ty(ty),
            Want::Result(function) => {
                Expected::Class(results[function.index()].expect("a result to infer"))
            }
            Want::Peer(peer) => Expected::Peer(class(peer)),
        };
        let actual = class(demand.actual);
        if expected == Expected::Class(actual) || expected == Expected::Peer(actual) {
            continue;
        }
        typing.expect(actual, expected, span(demand.node));
    }
    placed.classes = classes;
    (typing, results)
}
