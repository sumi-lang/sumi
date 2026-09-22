//! The middle end: rewrites a proven graph into a smaller one that computes the same values, for
//! whichever backend runs it. The result is a graph like the analysis's, contexts and all.

use sumi_graph::{FunctionId, Graph, GraphBuilder, Loop, LoopId, NodeId, Op, RegionId};

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

/// Keeps what each run's result can demand, reading through copies and narrowed reads, which
/// compute nothing.
pub fn optimize(graph: &Graph) -> Optimized {
    let forward = forwards(graph);
    let kept = marks(graph, &forward);
    emit(graph, &forward, &kept)
}

/// Per node, the node whose value it has.
fn forwards(graph: &Graph) -> Vec<NodeId> {
    let mut forward: Vec<NodeId> = graph.node_ids().collect();
    for node in graph.node_ids() {
        let identity = matches!(
            graph.node(node).op,
            Op::Copy { .. } | Op::Assign { .. } | Op::Refine { .. } | Op::Exactly(_)
        );
        if identity && graph.input_values(node)[0] {
            forward[node.index()] = graph.inputs(node)[0];
        }
    }
    for index in 0..forward.len() {
        let mut target = forward[index];
        while forward[target.index()] != target {
            target = forward[target.index()];
        }
        forward[index] = target;
    }
    forward
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

/// The regions whose owner survives, and every run's own.
fn kept_regions(graph: &Graph, kept: &[bool]) -> Vec<bool> {
    let mut regions = vec![false; graph.region_ids().len()];
    for run in graph.runs() {
        regions[run.region().index()] = true;
    }
    for node in graph.node_ids().filter(|node| kept[node.index()]) {
        for region in owned(&graph.node(node).op, graph) {
            regions[region.index()] = true;
        }
    }
    regions
}

/// What survives: whatever a run's result can demand, and the contexts and declarations the
/// survivors name, which keep the graph as well formed as the analysis's.
fn marks(graph: &Graph, forward: &[NodeId]) -> Vec<bool> {
    let mut kept = vec![false; graph.nodes().len()];
    let mut stack: Vec<NodeId> = Vec::new();
    let region = |stack: &mut Vec<NodeId>, region: RegionId| {
        let region = graph.region(region);
        stack.push(region.context);
        stack.push(region.result());
        stack.extend(region.control());
    };
    for run in graph.runs() {
        stack.push(run.entry());
        stack.extend(run.params());
        stack.push(run.result());
        region(&mut stack, run.region());
    }
    while let Some(node) = stack.pop() {
        let node = forward[node.index()];
        if kept[node.index()] {
            continue;
        }
        kept[node.index()] = true;
        let inputs = graph.inputs(node);
        match graph.node(node).op {
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
        for owned in owned(&graph.node(node).op, graph) {
            region(&mut stack, owned);
        }
    }
    kept
}

fn emit(graph: &Graph, forward: &[NodeId], kept: &[bool]) -> Optimized {
    let regions = kept_regions(graph, kept);
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
        // (where, whether it enters or closes there, region), in the order the builder takes.
        let mut events: Vec<(usize, u8, RegionId)> = Vec::new();
        for &region in &run_regions[index] {
            let start = graph.region(region).start();
            let stop = start + graph.region(region).nodes().len();
            events.push((start, 1, region));
            events.push((stop, if stop == start { 2 } else { 0 }, region));
        }
        events.sort_by_key(|&(at, order, region)| (at, order, region.index()));
        let mut events = events.into_iter().peekable();
        for at in first..=end {
            while let Some((_, order, region)) = events.next_if(|&(event, _, _)| event == at) {
                let map = |node: NodeId| {
                    new_of[forward[node.index()].index()].expect("a kept region's nodes are kept")
                };
                let old = graph.region(region);
                if order == 1 {
                    let context = map(old.context);
                    let new = builder.open(context);
                    builder.enter(new);
                    new_region[region.index()] = Some(new);
                } else {
                    builder.close_with_control(
                        new_region[region.index()].expect("a region closes after it opens"),
                        map(old.result()),
                        old.result_has_value(),
                        old.control().map(map),
                    );
                }
            }
            if at == end || !kept[at] {
                continue;
            }
            let node = NodeId::new(at);
            let map = |node: NodeId| {
                new_of[forward[node.index()].index()].expect("what a kept node names is kept")
            };
            let entry = graph.node(node);
            let op = match entry.op.clone() {
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
                let new = match new_of[forward[input.index()].index()] {
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
        let result = new_of[forward[run.result().index()].index()].expect("a run's result is kept");
        let region = new_region[run.region().index()].expect("a run's region is kept");
        builder.close_run(open, region, result);
    }
    Optimized {
        graph: builder.finish(),
        origins: origins.into_boxed_slice(),
    }
}
