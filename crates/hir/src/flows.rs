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
use crate::lower::{Header, Lowered};
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
    values: &'a [Box<[bool]>],
    results: &'a [Box<[bool]>],
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
        let value = |index: usize| self.values[node.index()][index];
        let result = |index: usize| self.results[node.index()][index];
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
            Op::And { rhs, .. } | Op::Or { rhs, .. } => {
                if value(0) {
                    require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None);
                }
                let (at, rhs) = region(*rhs);
                if result(0) {
                    require(at, rhs, Expected::Ty(Ty::Bool), None);
                }
            }
            Op::Join { then, else_, .. } => {
                if value(0) {
                    require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None);
                }
                match else_ {
                    None => {
                        let (at, then) = region(*then);
                        if result(0) {
                            require(at, then, Expected::Ty(Ty::Unit), None);
                        }
                    }
                    Some(else_) if typed(node) && self.results[node.index()].iter().all(|&r| r) => {
                        let branches = [region(*then).1, region(*else_).1];
                        demand(entry.origin, node, DemandKind::Agree { branches });
                    }
                    Some(_) => {}
                }
            }
            Op::Copy {
                declared: Some((ty, at)),
            } if value(0) => require(reads[0], inputs[0], Expected::Ty(*ty), Some(*at)),
            Op::Copy { declared: Some(_) } => {}
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
            Op::Return { .. } if value(0) => {
                require(reads[0], inputs[0], Expected::Peer(node), None)
            }
            Op::Return { .. } => {}
            Op::Result {
                declared,
                falls_through,
            } => {
                let first = usize::from(!falls_through);
                for (&at, &input) in reads[first..].iter().zip(&inputs[first..]) {
                    let expected =
                        declared.map_or(Expected::Peer(node), |(ty, _)| Expected::Ty(ty));
                    require(at, input, expected, declared.map(|(_, at)| at));
                }
            }
            Op::Int(_)
            | Op::Bool(_)
            | Op::Param { .. }
            | Op::Unit
            | Op::Hole
            | Op::Copy { declared: None }
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
        values: &lowered.values,
        results: &lowered.results,
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
                    ..
                } => {
                    for (index, region) in [*then, *else_].into_iter().enumerate() {
                        if !lowered.results[node.index()][index] {
                            continue;
                        }
                        let region = graph.region(region);
                        typing.derive(region.result(), region.context, node, Pair::Branch);
                    }
                }
                Op::Join {
                    then, else_: None, ..
                } => {
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
                Op::And {
                    rhs,
                    lhs_value: true,
                }
                | Op::Or {
                    rhs,
                    lhs_value: true,
                } => {
                    typing.known(node, Ty::Bool, origin);
                    let rhs = graph.region(*rhs).result();
                    let and = matches!(entry.op, Op::And { .. });
                    if lowered.results[node.index()][0] {
                        typing.derive(inputs[0], rhs, node, Pair::Lazy { and });
                    } else {
                        typing.flow(inputs[0], node, Edge::Exactly(!and));
                    }
                }
                Op::And {
                    lhs_value: false, ..
                }
                | Op::Or {
                    lhs_value: false, ..
                } => {}
                Op::Return { value: true } => typing.flow(inputs[0], node, Edge::Types),
                Op::Return { value: false } => {}
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
                Op::Result {
                    declared,
                    falls_through,
                } => {
                    if let Some((ty, at)) = declared {
                        typing.known(node, *ty, *at);
                    }
                    let edge = if declared.is_some() {
                        Edge::Values
                    } else {
                        Edge::Bind
                    };
                    if *falls_through {
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
