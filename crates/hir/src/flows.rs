//! The typing drawn from the graph: a class for every node, a fact for
//! every node that knows something on its own account, a flow for every
//! edge that carries evidence, and a demand for every read an operator
//! holds to a type, in one pass over the table.
//!
//! Within a function every input precedes its reader, so one pass in node
//! order draws each node's facts and flows as it reaches the node; only a
//! call reaches forward, to a callee whose run may come later in the file,
//! so the flows of calls are drawn once every run is passed. Demands are
//! joined into the evidence last, in node order, which is the order the
//! verdict pass replays them in.

use std::collections::HashSet;

use rustc_hash::FxBuildHasher;
use sumi_graph::{BinaryOp, Domain, Graph, Int, May, Node, NodeId, Op, Thresholds, Ty, Value};
use sumi_text::TextRange;

use crate::lattice::Edge;
use crate::lower::{Header, Lowered};
use crate::typing::{Expected, Typing};

/// What a node requires of a value it reads, checked after solving.
pub(crate) enum DemandKind {
    /// The value must have the expected type, which a declaration may
    /// have set: a called function, a result annotation, or a binding's
    /// annotation.
    Type {
        expected: Expected,
        declared: Option<TextRange>,
    },
    /// An expression statement's value must be unit.
    Unused,
    /// The operands of `==` and `!=` must not be unit.
    Comparable,
    /// The branches of an `if` must agree on one type: the value is the
    /// `if`, and each branch delivers its type to it first.
    Agree { branches: [NodeId; 2] },
}

/// One demand, kept small: the verdict pass reads every one, and a body
/// makes one per operand, argument, branch, and statement.
pub(crate) struct Demand {
    /// The function the demand is made in.
    pub owner: u32,
    /// Where the value is read: where a failure is reported.
    pub at: TextRange,
    pub actual: NodeId,
    pub kind: DemandKind,
}

/// The demands drawn so far, and what they are drawn from.
struct Demands<'a> {
    graph: &'a Graph,
    headers: &'a [Header],
    typed: &'a [bool],
    made: Vec<Demand>,
}

impl Demands<'_> {
    /// The demands the node `node` of the function `owner`, which is
    /// `entry` reading `inputs` at `reads`, makes of what it reads: one
    /// per typed operand, argument, branch, and statement, in operand
    /// order. A read of a hole is held to nothing; an untyped node still
    /// holds its typed operands.
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
        // A region's value is read where the region is entered: at its
        // context.
        let region = |region| {
            let region = graph.region(region);
            (graph.node(region.context).origin, region.result())
        };
        match &entry.op {
            Op::Neg => require(reads[0], inputs[0], Expected::Ty(Ty::Int), None),
            Op::Not => require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None),
            // `==` and `!=` compare like with like: whichever operand exists
            // sets the other's expectation, and neither may be unit.
            Op::Binary(BinaryOp::Eq | BinaryOp::Ne) => {
                if let Some(&operand) = inputs.iter().find(|&&input| typed(input)) {
                    for (&at, &input) in reads.iter().zip(inputs) {
                        require(at, input, Expected::Peer(operand), None);
                    }
                    demand(entry.origin, operand, DemandKind::Comparable);
                }
            }
            Op::Binary(_) => {
                for (&at, &input) in reads.iter().zip(inputs) {
                    require(at, input, Expected::Ty(Ty::Int), None);
                }
            }
            Op::And { rhs } | Op::Or { rhs } => {
                require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None);
                let (at, rhs) = region(*rhs);
                require(at, rhs, Expected::Ty(Ty::Bool), None);
            }
            Op::Join { then, else_ } => {
                require(reads[0], inputs[0], Expected::Ty(Ty::Bool), None);
                match else_ {
                    // Without an else, the then branch is unit, and so is the
                    // `if`.
                    None => {
                        let (at, then) = region(*then);
                        require(at, then, Expected::Ty(Ty::Unit), None);
                    }
                    // Each branch decides the `if` and learns nothing from the
                    // other, so branches that disagree leave the `if`
                    // undetermined, conflicted on its own class, and keep their
                    // own types. The verdict pass reports it there.
                    Some(else_) if typed(node) => {
                        let branches = [region(*then).1, region(*else_).1];
                        demand(entry.origin, node, DemandKind::Agree { branches });
                    }
                    Some(_) => {}
                }
            }
            Op::Copy {
                declared: Some((ty, at)),
            } => require(reads[0], inputs[0], Expected::Ty(*ty), Some(*at)),
            // Every argument there is, arity aside, is held to its parameter,
            // on the strength of the declaration, which is where the callee's
            // entry stands.
            Op::Call(callee) => {
                let params = self.headers[callee.index()]
                    .params
                    .as_deref()
                    .expect("a call names a whole callee");
                let declared = graph.node(graph.run(*callee).entry()).origin;
                for ((&at, &input), &ty) in reads.iter().zip(inputs).zip(params) {
                    require(at, input, Expected::Ty(ty), Some(declared));
                }
            }
            Op::Unused => {
                if typed(inputs[0]) {
                    demand(reads[0], inputs[0], DemandKind::Unused);
                }
            }
            Op::Int(_)
            | Op::Bool(_)
            | Op::Param(_)
            | Op::Unit
            | Op::Hole
            | Op::Copy { declared: None }
            | Op::Refine { .. }
            | Op::Exactly(_)
            | Op::Entry
            | Op::Then
            | Op::Else => {}
        }
    }
}

/// The typing of the graph, one class per node at the node's index, the
/// thresholds of the file's constants, and the demands, in node order. A
/// node the walk gave no value has a class nothing flows into. A constant
/// is an integer the file spells, or an operator over constants, which is
/// the constant the machine would compute; each is kept once, in the
/// order first seen.
pub(crate) fn draw(
    graph: &Graph,
    lowered: &Lowered,
    headers: &[Header],
) -> (Typing, Thresholds, Vec<Demand>) {
    let mut typing = Typing::for_nodes(graph.nodes().len());
    let typed = |node: NodeId| lowered.typed[node.index()];
    let mut constants: Vec<Int> = Vec::new();
    let mut seen: HashSet<Int, FxBuildHasher> = HashSet::default();
    // The constant each node of the run folds to, by slot.
    let mut folded: Vec<Option<Int>> = Vec::new();
    let mut demands = Demands {
        graph,
        headers,
        typed: &lowered.typed,
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
                Op::Hole | Op::Unused => unreachable!("a hole or a statement is no value"),
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
    let demands = demands.made;
    for demand in &demands {
        if let DemandKind::Type { expected, .. } = demand.kind {
            typing.expect(demand.actual, expected, demand.at);
        }
    }
    (typing, constants.into_iter().collect(), demands)
}
