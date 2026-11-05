//! The typing drawn from the graph: a class per node, a fact or flow per node that knows or passes
//! on a type, and a demand per typed read. Demands are joined into the evidence last, in node
//! order, the order the verdict pass replays them in.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_graph::{
    Arms, BinaryOp, Case, CmpOp, Domain, FieldName, FunctionId, Graph, Int, May, Node, NodeId, Op,
    RegionId, Thresholds, Ty, Unions, Value,
};
use sumi_text::TextRange;

use crate::lattice::{Context, Edge, Many, Pair};
use crate::lower::{Fallthrough, Header, HeaderResult, Lowered, TypeHeader};
use crate::spans::Spans;
use crate::typing::{Expected, Typing};

/// Where a demanded type was declared.
#[derive(Clone, Copy)]
pub(crate) enum Declared {
    Written(TextRange),
    /// A result left unwritten, which declares `unit` at the parameter list.
    Omitted(TextRange),
}

pub(crate) enum DemandKind {
    Type {
        expected: Expected,
        declared: Option<Declared>,
    },
    Unused,
    Comparable,
    /// `actual` is the switch; `branches` are the results of its arms, read at `at`.
    Agree {
        branches: Box<[NodeId]>,
        at: Box<[TextRange]>,
    },
    /// `actual` is the base of a read of the field.
    Field(FieldName),
    /// `actual` is a `match` scrutinee, which holds a declared value.
    Matched,
    /// `actual` is a `match` scrutinee, among whose type's members the arm's type is.
    Member(Ty),
}

pub(crate) struct Demand {
    pub owner: u32,
    pub at: TextRange,
    pub actual: NodeId,
    pub kind: DemandKind,
}

struct Demands<'a> {
    graph: &'a Graph,
    spans: &'a Spans,
    typed: &'a [bool],
    fallthroughs: &'a [Option<Fallthrough>],
    headers: &'a [Header],
    types: &'a [TypeHeader],
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
        let value = |index: usize| graph.input_roles(node)[index].is_value();
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
        let written = |at: TextRange| Some(Declared::Written(at));
        // What the run's result holds the body to: only there can a declaration be omitted.
        let held = |at: TextRange| {
            let is_omitted = matches!(
                self.headers[owner as usize].result,
                HeaderResult::Omitted(_)
            );
            Some(if is_omitted {
                Declared::Omitted(at)
            } else {
                Declared::Written(at)
            })
        };
        let spans = self.spans;
        let region = |id: RegionId| (spans.result_read(id), graph.region(id).result());
        match &entry.op {
            Op::Neg if value(0) => require(reads[0], inputs[0], Expected::Ty(Ty::INT), None),
            Op::Not if value(0) => require(reads[0], inputs[0], Expected::Ty(Ty::BOOL), None),
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
                    demand(spans.origin(node), operand, DemandKind::Comparable);
                }
            }
            Op::Binary(_) => {
                for (index, (&at, &input)) in reads.iter().zip(inputs).enumerate() {
                    if value(index) {
                        require(at, input, Expected::Ty(Ty::INT), None);
                    }
                }
            }
            Op::And { rhs } | Op::Or { rhs } => {
                if value(0) {
                    require(reads[0], inputs[0], Expected::Ty(Ty::BOOL), None);
                }
                let rhs_region = *rhs;
                let (at, rhs) = region(rhs_region);
                if graph.region(rhs_region).result_has_value() {
                    require(at, rhs, Expected::Ty(Ty::BOOL), None);
                }
            }
            Op::Switch { arms } => {
                let expect = |ty| DemandKind::Type {
                    expected: Expected::Ty(ty),
                    declared: None,
                };
                let selection = selection(graph, *arms);
                if value(0) && selection.boolean {
                    if typed(inputs[0]) {
                        demand(reads[0], inputs[0], expect(Ty::BOOL));
                    }
                } else if value(0) && typed(inputs[0]) {
                    demand(reads[0], inputs[0], DemandKind::Matched);
                    for arm in arms.iter() {
                        let context = graph.region(arm).context;
                        if let Case::Is(ty) = graph.case(context) {
                            demand(spans.origin(context), inputs[0], DemandKind::Member(ty));
                        }
                    }
                }
                let valued = || {
                    arms.iter()
                        .filter(|&arm| graph.region(arm).result_has_value())
                };
                if !value(0) {
                } else if !selection.total {
                    // What falls through is unit, so every arm is.
                    for arm in valued() {
                        let (at, result) = region(arm);
                        if typed(result) {
                            demand(at, result, expect(Ty::UNIT));
                        }
                    }
                } else if typed(node) && valued().count() == arms.len() {
                    let agree = DemandKind::Agree {
                        at: valued().map(|arm| region(arm).0).collect(),
                        branches: valued().map(|arm| region(arm).1).collect(),
                    };
                    demand(spans.origin(node), node, agree);
                }
            }
            Op::Loop { body } => {
                let (at, result) = region(*body);
                if value(0) && value(1) && graph.region(*body).result_has_value() {
                    require(at, result, Expected::Ty(Ty::UNIT), None);
                }
            }
            Op::Copy { declared: Some(ty) } if value(0) => {
                let at = spans
                    .annotation(node)
                    .expect("a copy declared with a type has its annotation");
                let run = graph.run(FunctionId::new(owner as usize));
                let declared = if node == run.result() {
                    held(at)
                } else {
                    written(at)
                };
                require(reads[0], inputs[0], Expected::Ty(*ty), declared);
            }
            Op::Copy { declared: Some(_) } => {}
            Op::Assign if value(0) => {
                let declaration = graph.declaration(node);
                require(
                    reads[0],
                    inputs[0],
                    Expected::Peer(declaration),
                    spans.name(declaration).and_then(written),
                )
            }
            Op::Assign => {}
            Op::Call(function) => {
                let run = graph.run(*function);
                let types = run.param_types().expect("a callee has parameter types");
                for (index, (((&at, &input), &ty), param)) in reads
                    .iter()
                    .zip(inputs)
                    .zip(types)
                    .zip(run.params())
                    .enumerate()
                {
                    if value(index) {
                        let declared = written(spans.origin(param));
                        require(at, input, Expected::Ty(ty), declared);
                    }
                }
            }
            Op::Make(decl) => {
                let fields = graph.decl(*decl).fields();
                let names = &self.types[decl.index()].fields;
                for (index, (((&at, &input), &(_, ty)), &name)) in
                    reads.iter().zip(inputs).zip(fields).zip(names).enumerate()
                {
                    if value(index)
                        && let Some(ty) = ty
                    {
                        require(at, input, Expected::Ty(ty), written(name));
                    }
                }
            }
            Op::Field(name) => {
                if value(0) && typed(inputs[0]) {
                    demand(spans.origin(node), inputs[0], DemandKind::Field(*name));
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
                let expected = declared.map_or(Expected::Peer(node), Expected::Ty);
                let declared = declared.and_then(|_| {
                    held(
                        spans
                            .annotation(node)
                            .expect("a result declared with a type has its annotation"),
                    )
                });
                if let Some(fallthrough) = fallthrough {
                    require(fallthrough.at, fallthrough.value, expected, declared);
                } else if value(0) {
                    require(reads[0], inputs[0], expected, declared);
                }
                for (&at, &input) in reads[1..].iter().zip(&inputs[1..]) {
                    require(at, input, expected, declared);
                }
            }
            Op::Int(_)
            | Op::Bool(_)
            | Op::Param { .. }
            | Op::Unit
            | Op::Hole
            | Op::Copy { declared: None }
            | Op::Phi
            | Op::LoopIndex
            | Op::Carry
            | Op::LoopValue
            | Op::Refine { .. }
            | Op::Exactly(_)
            | Op::Narrow(_)
            | Op::Entry
            | Op::Arm(_)
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After => {}
        }
    }
}

/// Whether every arm's case is a boolean.
/// What a switch's arms select on, read once per switch.
#[derive(Clone, Copy)]
struct Selection {
    /// Every arm is a boolean.
    boolean: bool,
    /// Some arm takes every scrutinee: both booleans, or members, which the checker holds to cover
    /// the scrutinee's type, so the switch never falls through to unit.
    total: bool,
}

fn selection(graph: &Graph, arms: Arms) -> Selection {
    let (mut boolean, mut on_true, mut on_false) = (true, false, false);
    for arm in arms.iter() {
        match graph.case(graph.region(arm).context) {
            Case::Bool(true) => on_true = true,
            Case::Bool(false) => on_false = true,
            Case::Is(_) | Case::Not(_) | Case::Any => boolean = false,
        }
    }
    let total = if boolean {
        on_true && on_false
    } else {
        !arms.is_empty()
    };
    Selection { boolean, total }
}

/// Where a parameter's values come from.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Arguments {
    /// The live call sites' arguments; a function no live call site enters is dead.
    Delivered,
    /// Every value of the parameter's type, in every function with a whole header.
    Any,
}

/// The thresholds are every integer the file spells or folds from constants, each once. A node the
/// walk gave no value has a class nothing flows into.
pub(crate) fn draw(
    graph: &Graph,
    spans: &Spans,
    lowered: &Lowered,
    headers: &[Header],
    types: &[TypeHeader],
    arguments: Arguments,
    unions: Rc<RefCell<Unions>>,
) -> (Typing, Context, Vec<Demand>) {
    let mut typing = Typing::for_nodes(graph.nodes().len(), unions);
    let typed = |node: NodeId| lowered.typed[node.index()];
    let mut constants: Vec<Int> = Vec::new();
    let mut cases: Vec<Case> = Vec::new();
    let mut seen: HashSet<Int, FxBuildHasher> = HashSet::default();
    let mut folded: Vec<Option<Int>> = Vec::new();
    let mut demands = Demands {
        graph,
        spans,
        typed: &lowered.typed,
        fallthroughs: &lowered.fallthroughs,
        headers,
        types,
        made: Vec::with_capacity(graph.nodes().len() / 2),
    };

    for (index, run) in graph.runs().iter().enumerate() {
        let owner = u32::try_from(index).expect("function count fits u32");
        folded.clear();
        folded.resize(run.nodes().len(), None);
        for node in run.nodes() {
            let entry = graph.node(node);
            let inputs = graph.inputs(node);
            demands.of(owner, node, entry, inputs, spans.reads(node));
            if !typed(node) {
                // A result a hole decided is unknown to every caller, not empty.
                if node == run.result() {
                    typing.unknown(node);
                }
                continue;
            }
            let origin = spans.origin(node);
            let constant = |index: usize| folded[run.slot(inputs[index])].as_ref();
            let mut folds = None;
            match &entry.op {
                Op::Int(value) => {
                    typing.literal(node, Ty::INT, May::int(value), origin);
                    folds = Some(value.clone());
                }
                Op::Bool(value) => typing.literal(node, Ty::BOOL, May::bool(*value), origin),
                Op::Param { ty: Some(ty), .. } => {
                    let origin = spans.name(node).unwrap_or(origin);
                    match arguments {
                        Arguments::Delivered => typing.known(node, *ty, origin),
                        Arguments::Any => {
                            typing.literal(node, *ty, May::every(*ty, graph.unions()), origin)
                        }
                    }
                }
                // No value to type.
                Op::Param { ty: None, .. } | Op::Hole | Op::Unused => {}
                Op::Entry => typing.entry(
                    node,
                    run.param_types().is_some()
                        && (arguments == Arguments::Any || run.params().len() == 0),
                ),
                // An untyped scrutinee decides nothing; the context is live as its parent is.
                Op::Arm(_) if !typed(inputs[0]) => {
                    typing.flow(inputs[1], node, Edge::Values);
                }
                Op::Arm(Case::Bool(wanted)) => {
                    typing.derive(inputs[0], inputs[1], node, Pair::Bool(*wanted));
                }
                Op::Arm(case) => {
                    let index = cases
                        .iter()
                        .position(|known| known == case)
                        .unwrap_or_else(|| {
                            cases.push(*case);
                            cases.len() - 1
                        });
                    let index = u16::try_from(index).expect("distinct case count fits u16");
                    typing.derive(inputs[0], inputs[1], node, Pair::Arm(index));
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
                Op::Narrow(ty) => {
                    typing.known(node, *ty, origin);
                    typing.flow(inputs[0], node, Edge::Narrow(*ty));
                }
                Op::Switch { arms } if selection(graph, *arms).total => {
                    let valued = arms
                        .iter()
                        .filter(|&arm| graph.region(arm).result_has_value())
                        .count();
                    let pair = if valued == 1 {
                        Pair::Forward
                    } else {
                        Pair::Branch
                    };
                    for arm in arms.iter() {
                        let region = graph.region(arm);
                        if !graph.input_roles(node)[0].is_value() || !region.result_has_value() {
                            continue;
                        }
                        typing.derive(region.result(), region.context, node, pair);
                    }
                }
                // What falls through is unit, and so is every arm.
                Op::Switch { arms } => {
                    typing.known(node, Ty::UNIT, origin);
                    let first = arms.iter().next().expect("a switch has an arm");
                    let parent = graph.inputs(graph.region(first).context)[1];
                    typing.flow(parent, node, Edge::Enter);
                }
                Op::Unit => {
                    typing.known(node, Ty::UNIT, origin);
                    typing.flow(inputs[0], node, Edge::Enter);
                }
                Op::Copy { declared: Some(ty) } => {
                    let at = spans
                        .annotation(node)
                        .expect("a copy declared with a type has its annotation");
                    typing.known(node, *ty, at);
                    if typed(inputs[0]) {
                        typing.flow(inputs[0], node, Edge::Values);
                    }
                }
                Op::Copy { declared: None } => typing.flow(inputs[0], node, Edge::Bind),
                Op::Assign => {
                    typing.flow(graph.declaration(node), node, Edge::TypeBind);
                    if graph.input_roles(node)[0].is_value() {
                        typing.flow(inputs[0], node, Edge::Values);
                    }
                }
                Op::Phi => {
                    typing.flow(graph.declaration(node), node, Edge::TypeBind);
                    if graph.input_roles(node)[0].is_value() {
                        for ((&value, &context), role) in inputs[1..]
                            .iter()
                            .zip(graph.phi_contexts(node))
                            .zip(&graph.input_roles(node)[1..])
                        {
                            if role.is_value() {
                                typing.derive(value, context, node, Pair::Outcome);
                            }
                        }
                    }
                }
                Op::LoopIndex => {
                    typing.known(node, Ty::INT, spans.name(node).unwrap_or(origin));
                    typing.derive(inputs[0], inputs[1], node, Pair::Range);
                }
                Op::Carry => {
                    typing.flow(graph.declaration(node), node, Edge::TypeBind);
                }
                Op::Loop { body } => {
                    let [continuation, empty] = graph.loop_contexts(node);
                    typing.known(node, Ty::UNIT, origin);
                    typing.flow(empty, node, Edge::Enter);
                    typing.flow(continuation, node, Edge::Enter);
                    for (header, next) in graph.carried(node) {
                        typing.derive(
                            graph.inputs(header)[0],
                            graph.region(*body).context,
                            header,
                            Pair::Outcome,
                        );
                        typing.derive(next, continuation, header, Pair::Backedge);
                    }
                }
                Op::LoopValue => {
                    let (header, next) = graph.carry(node);
                    let [continuation, empty] = graph.loop_contexts(inputs[0]);
                    typing.flow(header, node, Edge::TypeBind);
                    typing.derive(graph.inputs(header)[0], empty, node, Pair::Outcome);
                    typing.derive(next, continuation, node, Pair::Outcome);
                }
                Op::Neg => {
                    typing.known(node, Ty::INT, origin);
                    typing.flow(inputs[0], node, Edge::Neg);
                    folds = constant(0).map(|value| -value);
                }
                Op::Not => {
                    typing.known(node, Ty::BOOL, origin);
                    typing.flow(inputs[0], node, Edge::Not);
                }
                Op::Binary(op) => {
                    typing.known(node, op.result(), origin);
                    typing.derive(inputs[0], inputs[1], node, Pair::Binary(*op));
                    if let (Some(lhs), Some(rhs)) = (constant(0), constant(1)) {
                        let (lhs, rhs) = (Value::Int(lhs.clone()), Value::Int(rhs.clone()));
                        if let Ok(Value::Int(value)) =
                            Op::Binary(*op).apply(&[&lhs, &rhs], graph.decls(), graph.unions())
                        {
                            folds = Some(value);
                        }
                    }
                }
                Op::And { rhs } | Op::Or { rhs } if graph.input_roles(node)[0].is_value() => {
                    typing.known(node, Ty::BOOL, origin);
                    let region = graph.region(*rhs);
                    let rhs = region.result();
                    let is_and = matches!(entry.op, Op::And { .. });
                    if region.result_has_value() {
                        typing.derive(inputs[0], rhs, node, Pair::Lazy { is_and });
                    } else {
                        typing.flow(inputs[0], node, Edge::Exactly(!is_and));
                    }
                }
                Op::And { .. } | Op::Or { .. } => {}
                Op::Return if graph.input_roles(node)[0].is_value() => {
                    typing.flow(inputs[0], node, Edge::Types)
                }
                Op::Return => {}
                Op::Sequence => typing.derive(inputs[1], inputs[0], node, Pair::Branch),
                // Live where a selected arm's control is, or where no arm selects: the parent
                // gated by the complement of the arms, which for a partial boolean switch is the
                // other boolean.
                Op::Observe { arms } => {
                    for arm in arms.iter() {
                        let region = graph.region(arm);
                        typing.flow(
                            region.control().unwrap_or(region.context),
                            node,
                            Edge::Values,
                        );
                    }
                    if !selection(graph, *arms).total {
                        let first = arms.iter().next().expect("an observe has an arm");
                        let Case::Bool(taken) = graph.case(graph.region(first).context) else {
                            unreachable!("a partial switch is boolean")
                        };
                        typing.derive(inputs[0], inputs[1], node, Pair::Bool(!taken));
                    }
                }
                Op::After => typing.derive(inputs[1], inputs[0], node, Pair::Branch),
                Op::Result { declared } => {
                    if let Some(ty) = declared {
                        let at = spans
                            .annotation(node)
                            .expect("a result declared with a type has its annotation");
                        typing.known(node, *ty, at);
                    }
                    let edge = if declared.is_some() {
                        Edge::Values
                    } else {
                        Edge::Bind
                    };
                    if graph.input_roles(node)[0].is_value() {
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
                Op::Make(decl) => match inputs.split_first() {
                    Some((&first, others)) => {
                        typing.known(node, Ty::decl(*decl), origin);
                        typing.derive_many(first, others, node, Many::Make(*decl));
                    }
                    // A value with no fields is a literal.
                    None => {
                        typing.literal(node, Ty::decl(*decl), May::make(*decl, Vec::new()), origin)
                    }
                },
                Op::Field(name) => typing.flow(inputs[0], node, Edge::Field(*name)),
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
    if arguments == Arguments::Delivered {
        for &(context, callee) in &lowered.entered {
            let entry = graph.run(callee).entry();
            typing.flow(context, entry, Edge::Enter);
        }
    }
    if arguments == Arguments::Delivered {
        for call in &lowered.calls {
            let run = graph.run(call.callee);
            for (&arg, param) in graph.inputs(call.node).iter().zip(run.params()) {
                typing.derive(arg, call.context, param, Pair::Argument);
            }
        }
    }
    for &(call, callee) in &lowered.called {
        typing.call(graph.run(callee).result(), call, spans.origin(call));
    }
    let demands = demands.made;
    for demand in &demands {
        if let DemandKind::Type { expected, .. } = demand.kind {
            typing.expect(demand.actual, expected, demand.at);
        }
    }
    let cx = Context {
        thresholds: constants.into_iter().collect::<Thresholds>(),
        decls: graph.decls().into(),
        unions: graph.unions().clone(),
        cases: cases.into_boxed_slice(),
    };
    (typing, cx, demands)
}
