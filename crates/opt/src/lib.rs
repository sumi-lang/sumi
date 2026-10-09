//! The middle end: rewrites a proven graph into a smaller one that computes the same values, for
//! whichever backend runs it. The result is a graph like the analysis's, contexts and all.

use sumi_graph::{FunctionId, Graph, GraphBuilder, May, NodeId, Op, References, RegionId, Role};

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
    let decided = |node: NodeId| {
        let bools = facts(node).bools;
        (bools.may_true() != bools.may_false()).then_some(bools.may_true())
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
            Op::Copy { .. } | Op::Assign | Op::Refine { .. } | Op::Exactly(_) if value(0) => {
                Rewrite::Alias(inputs[0])
            }
            // A branch its condition always takes runs wherever its parent does.
            Op::Then if value(0) && decided(inputs[0]) == Some(true) => Rewrite::Alias(inputs[1]),
            Op::Else if value(0) && decided(inputs[0]) == Some(false) => Rewrite::Alias(inputs[1]),
            Op::Join { then, else_ } if value(0) => {
                let to = match (decided(inputs[0]), else_) {
                    (Some(true), _) => valued(then),
                    (Some(false), Some(else_)) => valued(else_),
                    _ => None,
                };
                to.map_or(Rewrite::Keep, Rewrite::Alias)
            }
            Op::Phi if value(0) => match decided(inputs[0]) {
                Some(truth) => {
                    let taken = if truth { 1 } else { 2 };
                    value(taken)
                        .then_some(inputs[taken])
                        .map_or(Rewrite::Keep, Rewrite::Alias)
                }
                None => Rewrite::Keep,
            },
            Op::Observe { then, else_ } if value(0) => match decided(inputs[0]) {
                Some(truth) => {
                    let taken = if truth { then } else { else_ };
                    match taken.and_then(|region| plan.exits[region.index()].control) {
                        Some(control) => Rewrite::Alias(control),
                        None => Rewrite::Literal(Op::Unit),
                    }
                }
                None => Rewrite::Keep,
            },
            ref op @ (Op::And { rhs } | Op::Or { rhs }) if value(0) => {
                let is_and = matches!(op, Op::And { .. });
                match decided(inputs[0]) {
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
                | Op::Join { .. }
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

/// The literal for the one value `may` holds, if it holds one.
fn single(may: &May) -> Option<Op> {
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
            Op::Join { then, else_ } => region(then) || else_.is_some_and(region),
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
    matches!(op, Op::Entry | Op::Then | Op::Else | Op::After)
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
    let mut builder = GraphBuilder::new(kept.iter().filter(|&&kept| kept).count());
    for run in graph.runs() {
        builder.function(run.param_types().map(Box::from));
    }
    let mut new_of: Vec<Option<NodeId>> = vec![None; graph.nodes().len()];
    let mut new_region: Vec<Option<RegionId>> = vec![None; regions.len()];
    let mut origins = Vec::new();
    let mut run_regions: Vec<Vec<RegionId>> = vec![Vec::new(); graph.runs().len()];
    for region in graph.region_ids().filter(|region| regions[region.index()]) {
        let context = graph.region(region).context.index();
        // Runs are contiguous in declaration order.
        let run = graph
            .runs()
            .partition_point(|run| run.entry().index() <= context)
            - 1;
        run_regions[run].push(region);
    }

    let mut inputs = Vec::new();
    let mut completes = Vec::new();
    let mut carried = Vec::new();
    for (index, run) in graph.runs().iter().enumerate() {
        let open = builder.open_run(FunctionId::new(index));
        let first = run.entry().index();
        let end = first + run.nodes().len();
        // (where, whether it closes or enters there, region), in the order the builder takes. An
        // empty region closes as it enters, so a sibling entered at the same place stays innermost.
        let mut events: Vec<(usize, u8, RegionId)> = Vec::new();
        for &region in &run_regions[index] {
            let start = graph.region(region).start();
            let stop = start + graph.region(region).nodes().len();
            events.push((start, 1, region));
            if stop > start {
                events.push((stop, 0, region));
            }
        }
        events.sort_by_key(|&(at, order, region)| (at, order, region.index()));
        let mut events = events.into_iter().peekable();
        // The contexts of the regions open here, innermost last.
        let mut contexts: Vec<NodeId> = Vec::new();
        for at in first..=end {
            while let Some((_, order, region)) = events.next_if(|&(event, _, _)| event == at) {
                let map = |node: NodeId| {
                    new_of[plan.target(node).index()].expect("a kept region's nodes are kept")
                };
                let old = graph.region(region);
                let exit = plan.exit(region);
                let close = |builder: &mut GraphBuilder, new: RegionId| {
                    builder.close_with_control(
                        new,
                        map(exit.result),
                        exit.value,
                        exit.control.map(map),
                    );
                };
                if order == 1 {
                    let context = map(old.context);
                    let new = builder.open(context);
                    builder.enter(new);
                    new_region[region.index()] = Some(new);
                    if old.nodes().len() == 0 {
                        close(&mut builder, new);
                    } else {
                        contexts.push(context);
                    }
                } else {
                    close(
                        &mut builder,
                        new_region[region.index()].expect("a region closes after it opens"),
                    );
                    contexts.pop();
                }
            }
            if at == end || !kept[at] {
                continue;
            }
            let node = NodeId::new(at);
            let map = |node: NodeId| {
                new_of[plan.target(node).index()].expect("what a kept node names is kept")
            };
            if let Some(literal) = plan.literal(node) {
                let context = *contexts.last().expect("a node runs in its run's region");
                let inputs: &[NodeId] = match literal {
                    Op::Unit => &[context],
                    _ => &[],
                };
                new_of[at] =
                    Some(builder.push(literal.clone(), inputs.iter().copied(), References::None));
                origins.push(node);
                continue;
            }
            let op = plan.op(graph, node).clone().with_regions(|region| {
                new_region[region.index()].expect("a kept op's regions are kept")
            });
            let returns = matches!(op, Op::Result { .. });
            inputs.clear();
            completes.clear();
            for (position, (&input, &role)) in graph
                .inputs(node)
                .iter()
                .zip(graph.input_roles(node))
                .enumerate()
            {
                let new = match new_of[plan.target(input).index()] {
                    Some(new) => new,
                    // A return no kept control reaches never runs.
                    None if returns && position > 0 => continue,
                    None => panic!("{input:?}, an input of kept {node:?}, is kept"),
                };
                if role == Role::Completes {
                    completes.push(inputs.len());
                }
                inputs.push(new);
            }
            let references = match plan.nodes[node.index()] {
                Rewrite::Replace(_) => References::None,
                _ => graph.references(node).map(&mut carried, map),
            };
            let new = builder.push(op, inputs.iter().copied(), references);
            for &position in &completes {
                builder.complete_input(new, position);
            }
            new_of[at] = Some(new);
            origins.push(node);
        }
        let result = new_of[plan.target(run.result()).index()].expect("a run's result is kept");
        let region = new_region[run.region().index()].expect("a run's region is kept");
        builder.close_run(open, region, result);
    }
    Optimized {
        graph: builder.finish(),
        origins: origins.into_boxed_slice(),
    }
}
