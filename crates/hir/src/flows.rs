//! The typing drawn from the graph: a class per node, a fact or flow per node that knows or passes
//! on a type, and a demand per typed read. Demands are joined into the evidence last, in node
//! order, the order the verdict pass replays them in.

use std::collections::HashSet;

use rustc_hash::FxBuildHasher;
use sumi_graph::{
    BinaryOp, CmpOp, Domain, Graph, Int, May, Node, NodeId, Op, Thresholds, Ty, Value,
};
use sumi_text::TextRange;

use crate::lattice::{Edge, Pair};
use crate::lower::{Fallthrough, Header, Lowered};
use crate::typing::{Expected, Typing};

pub(crate) enum DemandKind {
    Type {
        expected: Expected,
        declared: Option<TextRange>,
    },
    Unused,
    Comparable,
    /// `actual` is the `if`; `branches` are the results of its two arms.
    Agree {
        branches: [NodeId; 2],
    },
}

pub(crate) struct Demand {
    pub owner: u32,
    pub at: TextRange,
    pub actual: NodeId,
    pub kind: DemandKind,
}

struct Demands<'a> {
    graph: &'a Graph,
    typed: &'a [bool],
    fallthroughs: &'a [Option<Fallthrough>],
    made: Vec<Demand>,
}

impl Demands<'_> {
    fn of(
        &mut self,
        owner: u32,
        node: NodeId,
        entry: &Node,
        inputs: &[NodeId],
        reads: &[TextRange],
    ) {
        let graph = self.graph;
        let typed = |node: NodeId| self.typed[node.index()];
        let value = |index: usize| graph.input_values(node)[index];
        let fallthrough = self.fallthroughs[owner as usize];
        let made = &mut self.made;
        let mut demand = |at: TextRange, actual: NodeId, kind: DemandKind| {
            made.push(Demand {
                owner,
                at,
                actual,
                kind,
            });
        };
        let mut require = |at: TextRange, actual: NodeId, expected: Expected, declared| {
            if typed(actual) && expected != Expected::Peer(actual) {
                demand(at, actual, DemandKind::Type { expected, declared });
            }
        };
        let region = |region| {
            let region = graph.region(region);
            (graph.node(region.context).origin, region.result())
        };
        match &entry.op {
            Op::Neg if value(0) => require(reads[0], inputs[0], Expected::Ty(Ty::Int), None),
            Op::Not if value(0) => require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None),
            Op::Neg | Op::Not => {}
            Op::Binary(BinaryOp::Cmp(CmpOp::Eq | CmpOp::Ne)) => {
                if let Some(operand) = inputs
                    .iter()
                    .enumerate()
                    .find_map(|(index, &input)| (value(index) && typed(input)).then_some(input))
                {
                    for (index, (&at, &input)) in reads.iter().zip(inputs).enumerate() {
                        if value(index) {
                            require(at, input, Expected::Peer(operand), None);
                        }
                    }
                    demand(entry.origin, operand, DemandKind::Comparable);
                }
            }
            Op::Binary(_) => {
                for (index, (&at, &input)) in reads.iter().zip(inputs).enumerate() {
                    if value(index) {
                        require(at, input, Expected::Ty(Ty::Int), None);
                    }
                }
            }
            Op::And { rhs } | Op::Or { rhs } => {
                if value(0) {
                    require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None);
                }
                let rhs_region = *rhs;
                let (at, rhs) = region(rhs_region);
                if graph.region(rhs_region).result_has_value() {
                    require(at, rhs, Expected::Ty(Ty::Bool), None);
                }
            }
            Op::Join { then, else_ } => {
                if value(0) {
                    require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None);
                }
                match else_ {
                    None => {
                        let then_region = *then;
                        let (at, result) = region(then_region);
                        if value(0) && graph.region(then_region).result_has_value() {
                            require(at, result, Expected::Ty(Ty::Unit), None);
                        }
                    }
                    Some(else_)
                        if typed(node)
                            && value(0)
                            && graph.region(*then).result_has_value()
                            && graph.region(*else_).result_has_value() =>
                    {
                        let branches = [region(*then).1, region(*else_).1];
                        demand(entry.origin, node, DemandKind::Agree { branches });
                    }
                    Some(_) => {}
                }
            }
            Op::Loop(id) => {
                let body = graph.loop_(*id).body;
                let (at, result) = region(body);
                if value(0) && value(1) && graph.region(body).result_has_value() {
                    require(at, result, Expected::Ty(Ty::Unit), None);
                }
            }
            Op::Copy {
                declared: Some((ty, at)),
            } if value(0) => require(reads[0], inputs[0], Expected::Ty(*ty), Some(*at)),
            Op::Copy { declared: Some(_) } => {}
            Op::Assign { declaration } if value(0) => require(
                reads[0],
                inputs[0],
                Expected::Peer(*declaration),
                graph.node(*declaration).name,
            ),
            Op::Assign { .. } => {}
            Op::Call(callee) => {
                let callable = graph.callable(*callee);
                let declared = graph.node(graph.run(callable.function).entry()).origin;
                for (index, ((&at, &input), &ty)) in
                    reads.iter().zip(inputs).zip(&callable.params).enumerate()
                {
                    if value(index) {
                        require(at, input, Expected::Ty(ty), Some(declared));
                    }
                }
            }
            Op::Unused => {
                if value(0) && typed(inputs[0]) {
                    demand(reads[0], inputs[0], DemandKind::Unused);
                }
            }
            Op::Return if value(0) => require(reads[0], inputs[0], Expected::Peer(node), None),
            Op::Return => {}
            Op::Result { declared } => {
                let expected = declared.map_or(Expected::Peer(node), |(ty, _)| Expected::Ty(ty));
                if let Some(fallthrough) = fallthrough {
                    require(
                        fallthrough.at,
                        fallthrough.value,
                        expected,
                        declared.map(|(_, at)| at),
                    );
                } else if value(0) {
                    require(reads[0], inputs[0], expected, declared.map(|(_, at)| at));
                }
                for (&at, &input) in reads[1..].iter().zip(&inputs[1..]) {
                    require(at, input, expected, declared.map(|(_, at)| at));
                }
            }
            Op::Int(_)
            | Op::Bool(_)
            | Op::Param { .. }
            | Op::Unit
            | Op::Hole
            | Op::Copy { declared: None }
            | Op::Phi { .. }
            | Op::LoopIndex
            | Op::Carry { .. }
            | Op::LoopValue { .. }
            | Op::Refine { .. }
            | Op::Exactly(_)
            | Op::Entry
            | Op::Then
            | Op::Else
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After => {}
        }
    }
}

/// The thresholds are every integer the file spells or folds from constants, each once. A node the
/// walk gave no value has a class nothing flows into.
pub(crate) fn draw(
    graph: &Graph,
    lowered: &Lowered,
    headers: &[Header],
) -> (Typing, Thresholds, Vec<Demand>) {
    let mut typing = Typing::for_nodes(graph.nodes().len());
    let typed = |node: NodeId| lowered.typed[node.index()];
    let mut constants: Vec<Int> = Vec::new();
    let mut seen: HashSet<Int, FxBuildHasher> = HashSet::default();
    let mut folded: Vec<Option<Int>> = Vec::new();
    let mut demands = Demands {
        graph,
        typed: &lowered.typed,
        fallthroughs: &lowered.fallthroughs,
        made: Vec::with_capacity(graph.nodes().len() / 2),
    };

    for (index, run) in graph.runs().iter().enumerate() {
        let header = &headers[index];
        let owner = u32::try_from(index).expect("function count fits u32");
        folded.clear();
        folded.resize(run.nodes().len(), None);
        for node in run.nodes() {
            let entry = graph.node(node);
            let inputs = graph.inputs(node);
            demands.of(owner, node, entry, inputs, graph.reads(node));
            if !typed(node) {
                continue;
            }
            let origin = entry.origin;
            let constant = |index: usize| folded[run.slot(inputs[index])].as_ref();
            let mut folds = None;
            match &entry.op {
                Op::Int(value) => {
                    typing.literal(node, Ty::Int, May::int(value), origin);
                    folds = Some(value.clone());
                }
                Op::Bool(value) => typing.literal(node, Ty::Bool, May::bool(*value), origin),
                Op::Param { ty: Some(ty), .. } => {
                    typing.known(node, *ty, entry.name.unwrap_or(origin));
                }
                // No value to type.
                Op::Param { ty: None, .. } | Op::Hole | Op::Unused => {}
                Op::Entry => {
                    typing.entry(node, header.callee.is_some() && run.params().len() == 0);
                }
                // An untyped condition decides nothing; the context is live as its parent is.
                Op::Then | Op::Else if !typed(inputs[0]) => {
                    typing.flow(inputs[1], node, Edge::Values);
                }
                Op::Then | Op::Else => {
                    let edge = if matches!(entry.op, Op::Then) {
                        Pair::Then
                    } else {
                        Pair::Else
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
                    Pair::Refine {
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
                    let regions = [*then, *else_];
                    let values = regions.map(|region| graph.region(region).result_has_value());
                    let pair = if values.into_iter().filter(|&value| value).count() == 1 {
                        Pair::Forward
                    } else {
                        Pair::Branch
                    };
                    for (region, value) in regions.into_iter().zip(values) {
                        let region = graph.region(region);
                        if !graph.input_values(node)[0] || !value {
                            continue;
                        }
                        typing.derive(region.result(), region.context, node, pair);
                    }
                }
                Op::Join { then, else_: None } => {
                    typing.known(node, Ty::Unit, origin);
                    let parent = graph.inputs(graph.region(*then).context)[1];
                    typing.flow(parent, node, Edge::Enter);
                }
                Op::Unit => {
                    typing.known(node, Ty::Unit, origin);
                    typing.flow(inputs[0], node, Edge::Enter);
                }
                Op::Copy {
                    declared: Some((ty, at)),
                } => {
                    typing.known(node, *ty, *at);
                    if typed(inputs[0]) {
                        typing.flow(inputs[0], node, Edge::Values);
                    }
                }
                Op::Copy { declared: None } => typing.flow(inputs[0], node, Edge::Bind),
                Op::Assign { declaration } => {
                    typing.flow(*declaration, node, Edge::TypeBind);
                    if graph.input_values(node)[0] {
                        typing.flow(inputs[0], node, Edge::Values);
                    }
                }
                Op::Phi {
                    declaration,
                    contexts,
                } => {
                    typing.flow(*declaration, node, Edge::TypeBind);
                    if graph.input_values(node)[0] {
                        for ((&value, &context), has_value) in inputs[1..]
                            .iter()
                            .zip(contexts)
                            .zip(&graph.input_values(node)[1..])
                        {
                            if *has_value {
                                typing.derive(value, context, node, Pair::Outcome);
                            }
                        }
                    }
                }
                Op::LoopIndex => {
                    typing.known(node, Ty::Int, entry.name.unwrap_or(origin));
                    typing.derive(inputs[0], inputs[1], node, Pair::Range);
                }
                Op::Carry { declaration } => {
                    typing.flow(*declaration, node, Edge::TypeBind);
                }
                Op::Loop(id) => {
                    let loop_ = graph.loop_(*id);
                    typing.known(node, Ty::Unit, origin);
                    typing.flow(loop_.empty, node, Edge::Enter);
                    typing.flow(loop_.continuation, node, Edge::Enter);
                    for &(header, next) in &loop_.carried {
                        typing.derive(
                            graph.inputs(header)[0],
                            graph.region(loop_.body).context,
                            header,
                            Pair::Outcome,
                        );
                        typing.derive(next, loop_.continuation, header, Pair::Backedge);
                    }
                }
                Op::LoopValue { loop_, index } => {
                    let loop_ = graph.loop_(*loop_);
                    let (header, next) = loop_.carried[*index as usize];
                    typing.flow(header, node, Edge::TypeBind);
                    typing.derive(graph.inputs(header)[0], loop_.empty, node, Pair::Outcome);
                    typing.derive(next, loop_.continuation, node, Pair::Outcome);
                }
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
                    typing.derive(inputs[0], inputs[1], node, Pair::Binary(*op));
                    if let (Some(lhs), Some(rhs)) = (constant(0), constant(1)) {
                        let (lhs, rhs) = (Value::Int(lhs.clone()), Value::Int(rhs.clone()));
                        if let Ok(Value::Int(value)) = Op::Binary(*op).apply(&[&lhs, &rhs]) {
                            folds = Some(value);
                        }
                    }
                }
                Op::And { rhs } | Op::Or { rhs } if graph.input_values(node)[0] => {
                    typing.known(node, Ty::Bool, origin);
                    let region = graph.region(*rhs);
                    let rhs = region.result();
                    let and = matches!(entry.op, Op::And { .. });
                    if region.result_has_value() {
                        typing.derive(inputs[0], rhs, node, Pair::Lazy { and });
                    } else {
                        typing.flow(inputs[0], node, Edge::Exactly(!and));
                    }
                }
                Op::And { .. } | Op::Or { .. } => {}
                Op::Return if graph.input_values(node)[0] => {
                    typing.flow(inputs[0], node, Edge::Types)
                }
                Op::Return => {}
                Op::Sequence => typing.derive(inputs[1], inputs[0], node, Pair::Branch),
                Op::Observe { then, else_ } => {
                    let parent = inputs[1];
                    if let Some(region) = then {
                        let region = graph.region(*region);
                        typing.flow(
                            region.control().unwrap_or(region.context),
                            node,
                            Edge::Values,
                        );
                    } else {
                        typing.derive(inputs[0], parent, node, Pair::Then);
                    }
                    if let Some(region) = else_ {
                        let region = graph.region(*region);
                        typing.flow(
                            region.control().unwrap_or(region.context),
                            node,
                            Edge::Values,
                        );
                    } else {
                        typing.derive(inputs[0], parent, node, Pair::Else);
                    }
                }
                Op::After => typing.derive(inputs[1], inputs[0], node, Pair::Branch),
                Op::Result { declared } => {
                    if let Some((ty, at)) = declared {
                        typing.known(node, *ty, *at);
                    }
                    let edge = if declared.is_some() {
                        Edge::Values
                    } else {
                        Edge::Bind
                    };
                    if graph.input_values(node)[0] {
                        typing.flow(inputs[0], node, edge);
                    }
                    for &returned in &inputs[1..] {
                        let returned_inputs = graph.inputs(returned);
                        typing.derive(
                            returned_inputs[0],
                            returned_inputs[1],
                            node,
                            if declared.is_some() {
                                Pair::Outcome
                            } else {
                                Pair::Branch
                            },
                        );
                    }
                }
                // Drawn once every run is passed; the callee's run may come later.
                Op::Call(_) => {}
            }
            if let Some(value) = folds {
                if seen.insert(value.clone()) {
                    constants.push(value.clone());
                }
                folded[run.slot(node)] = Some(value);
            }
        }
    }
    for &(context, callee) in &lowered.entered {
        let entry = graph.run(callee).entry();
        typing.flow(context, entry, Edge::Enter);
    }
    for call in &lowered.calls {
        let run = graph.run(call.callee);
        for (&arg, param) in graph.inputs(call.node).iter().zip(run.params()) {
            typing.derive(arg, call.context, param, Pair::Argument);
        }
        if typed(call.node) {
            typing.call(run.result(), call.node, graph.node(call.node).origin);
        }
    }
    let demands = demands.made;
    for demand in &demands {
        if let DemandKind::Type { expected, .. } = demand.kind {
            typing.expect(demand.actual, expected, demand.at);
        }
    }
    (typing, constants.into_iter().collect(), demands)
}
