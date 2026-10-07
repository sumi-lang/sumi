//! The middle end: rewrites a proven graph into a smaller one that computes the same values, for
//! whichever backend runs it. The result is a graph like the analysis's, contexts and all.

use sumi_graph::{FunctionId, Graph, GraphBuilder, Loop, LoopId, May, NodeId, Op, RegionId};

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
    // The replacement retains the original input edges and their order.
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
            && !facts(control).live()
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
        let values = graph.input_values(node);
        let rewrite = match graph.node(node).op {
            Op::Sequence | Op::Loop(_) if !facts(inputs[0]).live() => Rewrite::Alias(inputs[0]),
            Op::Loop(_) if !facts(inputs[1]).live() => Rewrite::Replace(Op::Sequence),
            Op::Copy { .. } | Op::Assign { .. } | Op::Refine { .. } | Op::Exactly(_)
                if values[0] =>
            {
                Rewrite::Alias(inputs[0])
            }
            // A branch its condition always takes runs wherever its parent does.
            Op::Then if values[0] && decided(inputs[0]) == Some(true) => Rewrite::Alias(inputs[1]),
            Op::Else if values[0] && decided(inputs[0]) == Some(false) => Rewrite::Alias(inputs[1]),
            Op::Join { then, else_ } if values[0] => {
                let to = match (decided(inputs[0]), else_) {
                    (Some(true), _) => valued(then),
                    (Some(false), Some(else_)) => valued(else_),
                    _ => None,
                };
                to.map_or(Rewrite::Keep, Rewrite::Alias)
            }
            Op::Phi { .. } if values[0] => match decided(inputs[0]) {
                Some(truth) => {
                    let taken = if truth { 1 } else { 2 };
                    values[taken]
                        .then_some(inputs[taken])
                        .map_or(Rewrite::Keep, Rewrite::Alias)
                }
                None => Rewrite::Keep,
            },
            Op::Observe { then, else_ } if values[0] => match decided(inputs[0]) {
                Some(truth) => {
                    let taken = if truth { then } else { else_ };
                    match taken.and_then(|region| plan.exits[region.index()].control) {
                        Some(control) => Rewrite::Alias(control),
                        None => Rewrite::Literal(Op::Unit),
                    }
                }
                None => Rewrite::Keep,
            },
            ref op @ (Op::And { rhs } | Op::Or { rhs }) if values[0] => {
                let and = matches!(op, Op::And { .. });
                match decided(inputs[0]) {
                    Some(left) if left != and => Rewrite::Literal(Op::Bool(left)),
                    Some(_) => valued(rhs).map_or(Rewrite::Keep, Rewrite::Alias),
                    None => Rewrite::Keep,
                }
            }
            // The loop is its statement's control, so its bounds' returns run when it does.
            Op::Loop(id)
                if !facts(graph.region(graph.loop_(id).body).context).live()
                    && !graph
                        .loop_(id)
                        .carried
                        .iter()
                        .any(|&(carry, _)| returning[graph.inputs(carry)[0].index()])
                    && !inputs.iter().any(|&bound| returning[bound.index()]) =>
            {
                Rewrite::Literal(Op::Unit)
            }
            Op::LoopValue { loop_, index } => {
                let loop_ = graph.loop_(loop_);
                let carry = loop_.carried[index as usize].0;
                let empty = !facts(graph.region(loop_.body).context).live();
                (empty && graph.input_values(carry)[0])
                    .then(|| graph.inputs(carry)[0])
                    .map_or(Rewrite::Keep, Rewrite::Alias)
            }
            _ => Rewrite::Keep,
        };
        let foldable = matches!(
            graph.node(node).op,
            Op::Neg
                | Op::Not
                | Op::Binary(_)
                | Op::Call(_)
                | Op::Join { .. }
                | Op::Phi { .. }
                | Op::And { .. }
                | Op::Or { .. }
                | Op::LoopValue { .. }
        );
        plan.nodes[node.index()] = match rewrite {
            Rewrite::Keep if foldable && !returning[node.index()] => {
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
        (Some(lo), Some(hi)) if lo == hi && bools.is_empty() && !may.unit => Some(Op::Int(lo)),
        _ if !may.ints.is_empty() => None,
        _ if bools.may_true() != bools.may_false() && !may.unit => Some(Op::Bool(bools.may_true())),
        _ if bools.is_empty() && may.unit => Some(Op::Unit),
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
            Op::Loop(id) => {
                let loop_ = graph.loop_(id);
                graph.region(loop_.body).control().is_some()
                    || region(loop_.body)
                    || loop_
                        .carried
                        .iter()
                        .any(|&(carry, next)| reads(graph.inputs(carry)[0]) || reads(next))
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

fn owned(op: &Op, graph: &Graph) -> Vec<RegionId> {
    match *op {
        Op::Join { then, else_ } => [Some(then), else_].into_iter().flatten().collect(),
        Op::Observe { then, else_ } => [then, else_].into_iter().flatten().collect(),
        Op::And { rhs } | Op::Or { rhs } => vec![rhs],
        Op::Loop(id) => vec![graph.loop_(id).body],
        _ => Vec::new(),
    }
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
        for region in owned(plan.op(graph, node), graph) {
            regions[region.index()] = true;
        }
    }
    regions
}

/// What survives: whatever a run's result can demand, and the contexts and declarations the
/// survivors name, which keep the graph as well formed as the analysis's.
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
        let inputs = graph.inputs(node);
        match *plan.op(graph, node) {
            Op::Unused | Op::Int(_) | Op::Bool(_) | Op::Hole => {}
            Op::Result { .. } => stack.push(inputs[0]),
            Op::Phi {
                declaration,
                contexts,
            } => {
                stack.extend_from_slice(inputs);
                stack.push(declaration);
                stack.extend(contexts);
            }
            Op::Assign { declaration } | Op::Carry { declaration } => {
                stack.extend_from_slice(inputs);
                stack.push(declaration);
            }
            Op::Loop(id) => {
                let loop_ = graph.loop_(id);
                stack.extend_from_slice(inputs);
                stack.extend([loop_.index, loop_.continuation, loop_.empty]);
                for &(carry, next) in &loop_.carried {
                    stack.extend([carry, next]);
                }
            }
            _ => stack.extend_from_slice(inputs),
        }
        for owned in owned(plan.op(graph, node), graph) {
            region(&mut stack, owned);
        }
    }
    kept
}

fn emit(graph: &Graph, plan: &Plan, kept: &[bool]) -> Optimized {
    let regions = kept_regions(graph, plan, kept);
    let mut builder = GraphBuilder::new(kept.iter().filter(|&&kept| kept).count());
    for _ in graph.runs() {
        builder.function();
    }
    for callable in graph.callables() {
        builder.declare(callable.function, callable.params.clone());
    }
    let mut new_of: Vec<Option<NodeId>> = vec![None; graph.nodes().len()];
    let mut new_region: Vec<Option<RegionId>> = vec![None; regions.len()];
    let mut new_loop: Vec<Option<LoopId>> = vec![None; graph.loop_ids().len()];
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
                        (map(exit.result), old.result_read()),
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
            let entry = graph.node(node);
            if let Some(literal) = plan.literal(node) {
                let context = *contexts.last().expect("a node runs in its run's region");
                let inputs: &[_] = match literal {
                    Op::Unit => &[(context, entry.origin)],
                    _ => &[],
                };
                new_of[at] = Some(builder.push(literal.clone(), inputs, entry.origin, None));
                origins.push(node);
                continue;
            }
            let op = match plan.op(graph, node).clone() {
                Op::Join { then, else_ } => Op::Join {
                    then: new_region[then.index()].unwrap(),
                    else_: else_.map(|region| new_region[region.index()].unwrap()),
                },
                Op::Observe { then, else_ } => Op::Observe {
                    then: then.map(|region| new_region[region.index()].unwrap()),
                    else_: else_.map(|region| new_region[region.index()].unwrap()),
                },
                Op::And { rhs } => Op::And {
                    rhs: new_region[rhs.index()].unwrap(),
                },
                Op::Or { rhs } => Op::Or {
                    rhs: new_region[rhs.index()].unwrap(),
                },
                Op::Loop(id) => {
                    let loop_ = graph.loop_(id);
                    let new = builder.push_loop(Loop {
                        body: new_region[loop_.body.index()].unwrap(),
                        index: map(loop_.index),
                        carried: loop_
                            .carried
                            .iter()
                            .map(|&(carry, next)| (map(carry), map(next)))
                            .collect(),
                        continuation: map(loop_.continuation),
                        empty: map(loop_.empty),
                    });
                    new_loop[id.index()] = Some(new);
                    Op::Loop(new)
                }
                Op::LoopValue { loop_, index } => Op::LoopValue {
                    loop_: new_loop[loop_.index()].unwrap(),
                    index,
                },
                Op::Phi {
                    declaration,
                    contexts,
                } => Op::Phi {
                    declaration: map(declaration),
                    contexts: contexts.map(map),
                },
                Op::Assign { declaration } => Op::Assign {
                    declaration: map(declaration),
                },
                Op::Carry { declaration } => Op::Carry {
                    declaration: map(declaration),
                },
                op => op,
            };
            let returns = matches!(op, Op::Result { .. });
            let mut inputs = Vec::new();
            let mut completes = Vec::new();
            for (position, ((&input, &read), &value)) in graph
                .inputs(node)
                .iter()
                .zip(graph.reads(node))
                .zip(graph.input_values(node))
                .enumerate()
            {
                let new = match new_of[plan.target(input).index()] {
                    Some(new) => new,
                    // A return no kept control reaches never runs.
                    None if returns && position > 0 => continue,
                    None => panic!("{input:?}, an input of kept {node:?}, is kept"),
                };
                if !value {
                    completes.push(inputs.len());
                }
                inputs.push((new, read));
            }
            let new = builder.push(op, &inputs, entry.origin, entry.name);
            for position in completes {
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
