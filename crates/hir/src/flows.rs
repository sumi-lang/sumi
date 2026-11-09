//! The value flows drawn from the graph: a class per node and a flow per edge a value crosses,
//! solved to the values that may reach each node.

use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};

use rustc_hash::FxBuildHasher;
use sumi_graph::{Arms, Case, Domain, Graph, Int, May, NodeId, Op, Thresholds, Value};

use crate::lattice::{Arm, Context, Edge, Many, Pair};
use crate::lower::Lowered;
use crate::solver::Builder;
use crate::summary::Summaries;

/// The values that may reach each node, from one solve.
pub(crate) struct Values(Box<[May]>);

impl Values {
    /// The solve over the live call sites' arguments; a function no live call site enters is dead.
    pub fn delivered(graph: &Graph, lowered: &Lowered, summaries: &Summaries) -> Self {
        solve(graph, lowered, summaries, Arguments::Delivered)
    }

    pub fn may(&self, node: NodeId) -> &May {
        &self.0[node.index()]
    }
}

/// The solve with every value of each parameter's type, in every function with a whole header,
/// made the first time it is read, so the verdicts that need it share one.
pub(crate) struct AnyValues<'g> {
    graph: &'g Graph,
    lowered: &'g Lowered,
    summaries: &'g Summaries,
    values: OnceCell<Values>,
}

impl<'g> AnyValues<'g> {
    pub fn new(graph: &'g Graph, lowered: &'g Lowered, summaries: &'g Summaries) -> Self {
        Self {
            graph,
            lowered,
            summaries,
            values: OnceCell::new(),
        }
    }

    pub fn get(&self) -> &Values {
        self.values
            .get_or_init(|| solve(self.graph, self.lowered, self.summaries, Arguments::Any))
    }
}

/// What a switch's arms select on, read once per switch.
#[derive(Clone, Copy)]
pub(crate) struct Selection {
    /// Every arm is a boolean.
    pub boolean: bool,
    /// Some arm takes every scrutinee: both booleans, or members, which the checker holds to cover
    /// the scrutinee's type, so the switch never falls through to unit.
    pub total: bool,
}

pub(crate) fn selection(graph: &Graph, arms: Arms) -> Selection {
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Arguments {
    Delivered,
    Any,
}

fn solve(graph: &Graph, lowered: &Lowered, summaries: &Summaries, arguments: Arguments) -> Values {
    // A node the walk gives no value has a class nothing flows into.
    let mut values: Builder<'_, May> = Builder::with_classes(graph.nodes().len());
    let typed = |node: NodeId| lowered.typed[node.index()];
    let mut constants: Vec<Int> = Vec::new();
    let mut cases: Vec<Arm> = Vec::new();
    let mut case_ids: HashMap<Arm, u16, FxBuildHasher> = HashMap::default();
    let mut arm_cases: HashMap<NodeId, u16, FxBuildHasher> = HashMap::default();
    for entry in graph.nodes() {
        let Op::Switch { arms } = entry.op else {
            continue;
        };
        if selection(graph, arms).boolean {
            continue;
        }
        let mut previous = None;
        let mut seen: HashSet<Case, FxBuildHasher> = HashSet::default();
        for region in arms.iter() {
            let context = graph.region(region).context;
            let arm = Arm {
                case: graph.case(context),
                previous,
            };
            let index = *case_ids.entry(arm).or_insert_with(|| {
                let index = u16::try_from(cases.len()).expect("distinct arm count fits u16");
                cases.push(arm);
                index
            });
            arm_cases.insert(context, index);
            if seen.insert(arm.case) {
                previous = Some(index);
            }
        }
    }
    let mut seen: HashSet<Int, FxBuildHasher> = HashSet::default();
    let mut folded: Vec<Option<Int>> = Vec::new();

    for run in graph.runs() {
        folded.clear();
        folded.resize(run.nodes().len(), None);
        for node in run.nodes() {
            if !typed(node) {
                continue;
            }
            let entry = graph.node(node);
            let inputs = graph.inputs(node);
            let constant = |index: usize| folded[run.slot(inputs[index])].as_ref();
            let mut folds = None;
            match &entry.op {
                Op::Int(value) => {
                    values.expect(node, &May::int(value));
                    folds = Some(value.clone());
                }
                Op::Bool(value) => values.expect(node, &May::bool(*value)),
                Op::Param { ty: Some(ty), .. } => {
                    if arguments == Arguments::Any {
                        values.expect(node, &May::every(*ty, graph.unions()));
                    }
                }
                // No value to type.
                Op::Param { ty: None, .. } | Op::Hole | Op::Unused => {}
                // Liveness is not a type claim: a run with parameters is entered by its calls.
                Op::Entry => {
                    if run.param_types().is_some()
                        && (arguments == Arguments::Any || run.params().len() == 0)
                    {
                        values.expect(node, &May::unit());
                    }
                }
                // An untyped scrutinee decides nothing; the context is live as its parent is.
                Op::Arm(_) if !typed(inputs[0]) => {
                    values.flow(inputs[1], node, Edge::Values);
                }
                Op::Arm(Case::Bool(wanted)) => {
                    values.derive(inputs[0], inputs[1], node, Pair::Bool(*wanted));
                }
                Op::Arm(_) => {
                    values.derive(inputs[0], inputs[1], node, Pair::Arm(arm_cases[&node]));
                }
                Op::Refine {
                    op,
                    local_is_lhs,
                    sense,
                } => values.derive(
                    inputs[0],
                    inputs[1],
                    node,
                    Pair::Refine {
                        op: *op,
                        local_is_lhs: *local_is_lhs,
                        sense: *sense,
                    },
                ),
                Op::Exactly(value) => values.flow(inputs[0], node, Edge::Exactly(*value)),
                Op::Narrow(ty) => values.flow(inputs[0], node, Edge::Narrow(*ty)),
                Op::Switch { arms } if selection(graph, *arms).total => {
                    for arm in arms.iter() {
                        let region = graph.region(arm);
                        if !graph.input_roles(node)[0].is_value() || !region.result_has_value() {
                            continue;
                        }
                        values.derive(region.result(), region.context, node, Pair::Branch);
                    }
                }
                // What falls through is unit, and so is every arm.
                Op::Switch { arms } => {
                    let first = arms.iter().next().expect("a switch has an arm");
                    let parent = graph.inputs(graph.region(first).context)[1];
                    values.flow(parent, node, Edge::Enter);
                }
                Op::Unit => values.flow(inputs[0], node, Edge::Enter),
                Op::Copy { declared: Some(_) } => {
                    if typed(inputs[0]) {
                        values.flow(inputs[0], node, Edge::Values);
                    }
                }
                Op::Copy { declared: None } => values.flow(inputs[0], node, Edge::Values),
                Op::Assign => {
                    if graph.input_roles(node)[0].is_value() {
                        values.flow(inputs[0], node, Edge::Values);
                    }
                }
                Op::Phi => {
                    if graph.input_roles(node)[0].is_value() {
                        for ((&value, &context), role) in inputs[1..]
                            .iter()
                            .zip(graph.phi_contexts(node))
                            .zip(&graph.input_roles(node)[1..])
                        {
                            if role.is_value() {
                                values.derive(value, context, node, Pair::Branch);
                            }
                        }
                    }
                }
                Op::LoopIndex => values.derive(inputs[0], inputs[1], node, Pair::Range),
                Op::Carry => {}
                Op::Loop { body } => {
                    let [continuation, empty] = graph.loop_contexts(node);
                    values.flow(empty, node, Edge::Enter);
                    values.flow(continuation, node, Edge::Enter);
                    for (header, next) in graph.carried(node) {
                        values.derive(
                            graph.inputs(header)[0],
                            graph.region(*body).context,
                            header,
                            Pair::Branch,
                        );
                        values.derive(next, continuation, header, Pair::Backedge);
                    }
                }
                Op::LoopValue => {
                    let (header, next) = graph.carry(node);
                    let [continuation, empty] = graph.loop_contexts(inputs[0]);
                    values.derive(graph.inputs(header)[0], empty, node, Pair::Branch);
                    values.derive(next, continuation, node, Pair::Branch);
                }
                Op::Neg => {
                    values.flow(inputs[0], node, Edge::Neg);
                    folds = constant(0).map(|value| -value);
                }
                Op::Not => values.flow(inputs[0], node, Edge::Not),
                Op::Binary(op) => {
                    values.derive(inputs[0], inputs[1], node, Pair::Binary(*op));
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
                    let region = graph.region(*rhs);
                    let rhs = region.result();
                    let is_and = matches!(entry.op, Op::And { .. });
                    if region.result_has_value() {
                        values.derive(inputs[0], rhs, node, Pair::Lazy { is_and });
                    } else {
                        values.flow(inputs[0], node, Edge::ShortCircuit(!is_and));
                    }
                }
                Op::And { .. } | Op::Or { .. } | Op::Return => {}
                Op::Sequence => values.derive(inputs[1], inputs[0], node, Pair::Branch),
                // Live where a selected arm's control is, or where no arm selects: the parent
                // gated by the complement of the arms, which for a partial boolean switch is the
                // other boolean.
                Op::Observe { arms } => {
                    for arm in arms.iter() {
                        let region = graph.region(arm);
                        values.flow(
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
                        values.derive(inputs[0], inputs[1], node, Pair::Bool(!taken));
                    }
                }
                Op::After => values.derive(inputs[1], inputs[0], node, Pair::Branch),
                Op::Result { .. } => {
                    if graph.input_roles(node)[0].is_value() {
                        values.flow(inputs[0], node, Edge::Values);
                    }
                    for &returned in &inputs[1..] {
                        let returned_inputs = graph.inputs(returned);
                        values.derive(returned_inputs[0], returned_inputs[1], node, Pair::Branch);
                    }
                }
                Op::Make(decl) => match inputs.split_first() {
                    Some((&first, others)) => {
                        values.derive_many(first, others, node, Many::Make(*decl));
                    }
                    // A value with no fields is a literal.
                    None => values.expect(node, &May::make(*decl, Vec::new())),
                },
                Op::Field(name) => values.flow(inputs[0], node, Edge::Field(*name)),
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
            values.flow(context, entry, Edge::Enter);
        }
        for call in &lowered.calls {
            let run = graph.run(call.callee);
            for (&arg, param) in graph.inputs(call.node).iter().zip(run.params()) {
                values.derive(arg, call.context, param, Pair::Argument);
            }
        }
    }
    for &(call, callee) in &lowered.called {
        let result = graph.run(callee).result();
        match summaries.callee(call) {
            Some(callee) => {
                values.derive_many(result, graph.inputs(call), call, Many::Call(callee));
            }
            None => values.flow(result, call, Edge::Call),
        }
    }
    let cx = Context {
        // Every integer the file spells or folds from constants, each once.
        thresholds: constants.into_iter().collect::<Thresholds>(),
        decls: graph.decls().into(),
        unions: graph.unions().clone(),
        cases: cases.into_boxed_slice(),
        results: summaries.results(),
    };
    Values(values.solve(&cx).into_boxed_slice())
}
