//! The middle end: rewrites a proven graph into a smaller one that computes the same values, for
//! whichever backend runs it. The result is a graph like the analysis's, contexts and all.

use sumi_graph::{Arms, Case, Graph, May, NodeId, Op, Operand, Rebuild, References, RegionId};

/// A rewritten graph and the node of the original each of its nodes computes.
pub struct Optimized {
    pub graph: Graph,
    origins: Box<[NodeId]>,
}

impl Optimized {
    pub fn origin(&self, node: NodeId) -> NodeId {
        self.origins[node.index()]
    }
}

/// Rewrites values and control while preserving every run covered by `facts`. Each fact must
/// contain every value computed at its node on those runs.
pub fn optimize<'a>(graph: &Graph, facts: impl Fn(NodeId) -> &'a May) -> Optimized {
    let plan = plan(graph, facts);
    let kept = marks(graph, &plan);
    emit(graph, &plan, &kept)
}

enum Rewrite {
    Keep,
    Alias(NodeId),
    Literal(Op),
    // The replacement retains the original operands and their order, and no reference.
    Replace(Op),
}

struct Exit {
    result: NodeId,
    value: bool,
    control: Option<NodeId>,
}

struct Plan {
    nodes: Vec<Rewrite>,
    exits: Vec<Exit>,
}

impl Plan {
    fn op<'a>(&'a self, graph: &'a Graph, node: NodeId) -> &'a Op {
        match &self.nodes[node.index()] {
            Rewrite::Replace(op) | Rewrite::Literal(op) => op,
            _ => &graph.node(node).op,
        }
    }

    fn target(&self, mut node: NodeId) -> NodeId {
        while let Rewrite::Alias(to) = self.nodes[node.index()] {
            node = to;
        }
        node
    }

    /// The edges the node keeps: all of them, or a replacement's operands alone.
    fn edges<'a>(&self, graph: &'a Graph, node: NodeId) -> &'a [NodeId] {
        match self.nodes[node.index()] {
            Rewrite::Replace(_) => graph.inputs(node),
            _ => graph.edges(node),
        }
    }

    fn literal(&self, node: NodeId) -> Option<&Op> {
        match &self.nodes[node.index()] {
            Rewrite::Literal(op) => Some(op),
            _ => None,
        }
    }

    fn operands<'a>(
        &'a self,
        graph: &'a Graph,
        node: NodeId,
        kept: &'a [bool],
    ) -> impl Iterator<Item = Operand> + 'a {
        let returns = matches!(self.op(graph, node), Op::Result { .. });
        graph
            .operands(node)
            .enumerate()
            .filter_map(move |(position, input)| {
                // Explicit returns survive only when a retained control reaches them.
                (!returns || position == 0 || kept[self.target(input.node()).index()])
                    .then_some(input)
            })
    }

    fn exit(&self, region: RegionId) -> &Exit {
        &self.exits[region.index()]
    }
}

fn plan<'a>(graph: &Graph, facts: impl Fn(NodeId) -> &'a May) -> Plan {
    let mut plan = Plan {
        nodes: graph.node_ids().map(|_| Rewrite::Keep).collect(),
        exits: graph
            .region_ids()
            .map(|id| {
                let region = graph.region(id);
                Exit {
                    result: region.result(),
                    value: region.result_has_value(),
                    control: region.control(),
                }
            })
            .collect(),
    };
    for exit in &mut plan.exits {
        if let Some(control) = exit.control
            && !facts(control).is_live()
        {
            exit.result = control;
            exit.value = false;
        }
    }
    let unions = graph.unions();
    // Whether the case selects the scrutinee: for every value, for none, or undecided.
    let decided = |scrutinee: NodeId, case: Case| {
        let fact = facts(scrutinee);
        if fact.must_select(case, unions) {
            Some(true)
        } else if !fact.may_select(case, unions) {
            Some(false)
        } else {
            None
        }
    };
    // The arm taken, when the facts decide it: the first whose case always selects, past those
    // whose case never does.
    let taken = |scrutinee: NodeId, contexts: &mut dyn Iterator<Item = NodeId>| {
        for (index, context) in contexts.enumerate() {
            match decided(scrutinee, graph.case(context)) {
                Some(true) => return Some(Some(index)),
                Some(false) => continue,
                None => return None,
            }
        }
        Some(None)
    };
    let taken_arm = |scrutinee: NodeId, arms: Arms| {
        taken(
            scrutinee,
            &mut arms.iter().map(|arm| graph.region(arm).context),
        )
        .map(|index| index.map(|index| arms.iter().nth(index).expect("an arm taken exists")))
    };
    let valued = |region: RegionId| {
        let exit = &plan.exits[region.index()];
        exit.value.then_some(exit.result)
    };
    let returning = returning(graph);
    for node in graph.node_ids() {
        let inputs = graph.inputs(node);
        let roles = graph.input_roles(node);
        let value = |index: usize| roles[index].is_value();
        let rewrite = match graph.node(node).op {
            Op::Sequence | Op::Loop { .. } if !facts(inputs[0]).is_live() => {
                Rewrite::Alias(inputs[0])
            }
            Op::Loop { .. } if !facts(inputs[1]).is_live() => Rewrite::Replace(Op::Sequence),
            Op::Copy { .. } | Op::Assign | Op::Refine { .. } | Op::Exactly(_) | Op::Narrow(_)
                if value(0) =>
            {
                Rewrite::Alias(inputs[0])
            }
            // An arm its case always selects runs wherever its parent does.
            Op::Arm(case) if value(0) && decided(inputs[0], case) == Some(true) => {
                Rewrite::Alias(inputs[1])
            }
            Op::Switch { arms } if value(0) => match taken_arm(inputs[0], arms) {
                Some(Some(arm)) => valued(arm).map_or(Rewrite::Keep, Rewrite::Alias),
                Some(None) | None => Rewrite::Keep,
            },
            Op::Phi if value(0) => {
                match taken(inputs[0], &mut graph.phi_contexts(node).iter().copied()) {
                    Some(Some(index)) if value(1 + index) => Rewrite::Alias(inputs[1 + index]),
                    _ => Rewrite::Keep,
                }
            }
            Op::Observe { arms } if value(0) => match taken_arm(inputs[0], arms) {
                Some(taken) => match taken.and_then(|arm| plan.exits[arm.index()].control) {
                    Some(control) => Rewrite::Alias(control),
                    None => Rewrite::Literal(Op::Unit),
                },
                None => Rewrite::Keep,
            },
            ref op @ (Op::And { rhs } | Op::Or { rhs }) if value(0) => {
                let is_and = matches!(op, Op::And { .. });
                let left = decided(inputs[0], Case::Bool(true));
                match left {
                    Some(left) if left != is_and => Rewrite::Literal(Op::Bool(left)),
                    Some(_) => valued(rhs).map_or(Rewrite::Keep, Rewrite::Alias),
                    None => Rewrite::Keep,
                }
            }
            // The loop is its statement's control, so its bounds' returns run when it does.
            Op::Loop { body }
                if !facts(graph.region(body).context).is_live()
                    && !graph
                        .carried(node)
                        .any(|(carry, _)| returning[graph.inputs(carry)[0].index()])
                    && !inputs.iter().any(|&bound| returning[bound.index()]) =>
            {
                Rewrite::Literal(Op::Unit)
            }
            Op::LoopValue => {
                let (carry, _) = graph.carry(node);
                let Op::Loop { body } = graph.node(inputs[0]).op else {
                    unreachable!("a loop value reads its loop")
                };
                let is_empty = !facts(graph.region(body).context).is_live();
                (is_empty && graph.input_roles(carry)[0].is_value())
                    .then(|| graph.inputs(carry)[0])
                    .map_or(Rewrite::Keep, Rewrite::Alias)
            }
            _ => Rewrite::Keep,
        };
        let is_foldable = matches!(
            graph.node(node).op,
            Op::Neg
                | Op::Not
                | Op::Binary(_)
                | Op::Call(_)
                | Op::Field(_)
                | Op::Switch { .. }
                | Op::Phi
                | Op::And { .. }
                | Op::Or { .. }
                | Op::LoopValue
        );
        plan.nodes[node.index()] = match rewrite {
            Rewrite::Keep if is_foldable && !returning[node.index()] => {
                single(facts(node)).map_or(Rewrite::Keep, Rewrite::Literal)
            }
            rewrite => rewrite,
        };
    }
    for node in graph.node_ids() {
        if matches!(plan.nodes[node.index()], Rewrite::Alias(_)) {
            plan.nodes[node.index()] = Rewrite::Alias(plan.target(node));
        }
    }
    plan
}

/// The literal for the one value `may` holds, if it holds one; a declared value has no literal.
fn single(may: &May) -> Option<Op> {
    if !may.decls.is_empty() {
        return None;
    }
    let bools = may.bools;
    match (may.ints.lo(), may.ints.hi()) {
        (Some(lo), Some(hi)) if lo == hi && bools.is_empty() && !may.has_unit => Some(Op::Int(lo)),
        _ if !may.ints.is_empty() => None,
        _ if bools.may_true() != bools.may_false() && !may.has_unit => {
            Some(Op::Bool(bools.may_true()))
        }
        _ if bools.is_empty() && may.has_unit => Some(Op::Unit),
        _ => None,
    }
}

/// Per node, whether evaluating it can reach a return: through a control it sequences or runs, or
/// through a value it reads.
fn returning(graph: &Graph) -> Vec<bool> {
    let mut returning = vec![false; graph.nodes().len()];
    for node in graph.node_ids() {
        // Inputs precede their readers; one that does not is taken to return.
        let reads = |input: NodeId| input.index() >= node.index() || returning[input.index()];
        let region = |region: RegionId| reads(graph.region(region).result());
        let own = match graph.node(node).op {
            Op::Return | Op::Sequence | Op::Observe { .. } | Op::Result { .. } => true,
            Op::Loop { body } => {
                graph.region(body).control().is_some()
                    || region(body)
                    || graph
                        .carried(node)
                        .any(|(carry, next)| reads(graph.inputs(carry)[0]) || reads(next))
            }
            Op::Switch { arms } => arms.iter().any(region),
            Op::And { rhs } | Op::Or { rhs } => region(rhs),
            _ => false,
        };
        returning[node.index()] = own
            || graph
                .inputs(node)
                .iter()
                .any(|&input| !is_context(&graph.node(input).op) && reads(input));
    }
    returning
}

fn is_context(op: &Op) -> bool {
    matches!(op, Op::Entry | Op::Arm(_) | Op::After)
}

fn kept_regions(graph: &Graph, plan: &Plan, kept: &[bool]) -> Vec<bool> {
    let mut regions = vec![false; graph.region_ids().len()];
    for run in graph.runs() {
        regions[run.region().index()] = true;
    }
    for node in graph
        .node_ids()
        .filter(|&node| kept[node.index()] && plan.literal(node).is_none())
    {
        for region in plan.op(graph, node).regions() {
            regions[region.index()] = true;
        }
    }
    regions
}

/// What survives: whatever a run's result can demand, and every node the survivors reference,
/// which keeps the graph as well formed as the analysis's.
fn marks(graph: &Graph, plan: &Plan) -> Vec<bool> {
    let mut kept = vec![false; graph.nodes().len()];
    let mut stack: Vec<NodeId> = Vec::new();
    let region = |stack: &mut Vec<NodeId>, region: RegionId| {
        let exit = plan.exit(region);
        stack.push(graph.region(region).context);
        stack.push(exit.result);
        stack.extend(exit.control);
    };
    for run in graph.runs() {
        stack.push(run.entry());
        stack.extend(run.params());
        stack.push(run.result());
        region(&mut stack, run.region());
    }
    while let Some(node) = stack.pop() {
        let node = plan.target(node);
        if kept[node.index()] {
            continue;
        }
        kept[node.index()] = true;
        if plan.literal(node).is_some() {
            continue;
        }
        let op = plan.op(graph, node);
        match *op {
            Op::Unused | Op::Int(_) | Op::Bool(_) | Op::Hole => {}
            // Explicit returns reach the result only through a kept control.
            Op::Result { .. } => stack.push(graph.inputs(node)[0]),
            _ => stack.extend_from_slice(plan.edges(graph, node)),
        }
        for owned in op.regions() {
            region(&mut stack, owned);
        }
    }
    kept
}

fn emit(graph: &Graph, plan: &Plan, kept: &[bool]) -> Optimized {
    let regions = kept_regions(graph, plan, kept);
    let nodes = || graph.node_ids().filter(|node| kept[node.index()]);
    let mut contextual = false;
    let edges = nodes()
        .map(|node| match &plan.nodes[node.index()] {
            Rewrite::Literal(Op::Unit) => {
                contextual = true;
                1
            }
            Rewrite::Literal(_) => 0,
            Rewrite::Replace(_) => graph.inputs(node).len(),
            _ if matches!(graph.node(node).op, Op::Result { .. }) => {
                plan.operands(graph, node, kept).count()
            }
            _ => graph.edges(node).len(),
        })
        .sum();
    let mut rebuild = Rebuild::new(graph, kept, &regions, edges, |node| plan.target(node));
    let mut ordered = Vec::new();
    for id in graph.region_ids().filter(|id| regions[id.index()]) {
        let exit = plan.exit(id);
        rebuild.region(id, exit.result, exit.value, exit.control);
        if contextual && graph.region(id).nodes().len() != 0 {
            ordered.push(id);
        }
    }
    ordered.sort_by_key(|&id| {
        let region = graph.region(id);
        (
            region.start(),
            std::cmp::Reverse(region.nodes().len()),
            id.index(),
        )
    });
    let mut regions = ordered.into_iter().peekable();
    let mut enclosing: Vec<RegionId> = Vec::new();
    for node in nodes() {
        while enclosing.last().is_some_and(|&id| {
            let region = graph.region(id);
            region.start() + region.nodes().len() <= node.index()
        }) {
            enclosing.pop();
        }
        while let Some(id) = regions.next_if(|&id| graph.region(id).start() <= node.index()) {
            let region = graph.region(id);
            if region.start() + region.nodes().len() > node.index() {
                enclosing.push(id);
            }
        }
        if let Some(literal) = plan.literal(node) {
            let context = matches!(literal, Op::Unit).then(|| {
                graph
                    .region(*enclosing.last().expect("a literal has an enclosing region"))
                    .context
            });
            rebuild.push(
                node,
                literal.clone(),
                context.map(Operand::Value),
                References::None,
            );
            continue;
        }
        let op = plan.op(graph, node);
        let inputs = plan.operands(graph, node, kept);
        let references = match plan.nodes[node.index()] {
            Rewrite::Replace(_) => References::None,
            _ => graph.references(node),
        };
        rebuild.push(node, op.clone(), inputs, references);
    }
    let (graph, origins) = rebuild.finish();
    Optimized { graph, origins }
}
