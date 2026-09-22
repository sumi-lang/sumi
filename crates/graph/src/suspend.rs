//! Call-continuation liveness for consuming runs. A layout applies only to its exact pending stack.

use super::Control;
use crate::{Graph, NodeId, Op, RegionId, Run};

const WORK: usize = 65_536;

#[derive(Debug)]
pub(super) struct Suspensions {
    calls: Vec<(NodeId, Option<Layout>)>,
    budget: usize,
}

#[derive(Debug)]
struct Layout {
    after: Box<[Control]>,
    slots: Box<[usize]>,
}

impl Suspensions {
    pub(super) fn new() -> Self {
        Self {
            calls: Vec::new(),
            budget: WORK,
        }
    }

    pub(super) fn slots<'a>(
        &'a mut self,
        graph: &Graph,
        run: &Run,
        node: NodeId,
        after: &[Control],
    ) -> Option<&'a [usize]> {
        let index = match self
            .calls
            .binary_search_by_key(&node.index(), |(node, _)| node.index())
        {
            Ok(index) => index,
            Err(index) => {
                self.budget = self.budget.checked_sub(run.nodes().len())?;
                let layout = Layout::new(graph, run, node, after, &mut self.budget);
                self.calls.insert(index, (node, layout));
                index
            }
        };
        let layout = self.calls[index].1.as_ref()?;
        (layout.after.as_ref() == after).then_some(&layout.slots)
    }

    pub(super) fn saved(&self, node: NodeId) -> &[usize] {
        let index = self
            .calls
            .binary_search_by_key(&node.index(), |(node, _)| node.index())
            .unwrap();
        &self.calls[index].1.as_ref().unwrap().slots
    }
}

impl Layout {
    fn new(
        graph: &Graph,
        run: &Run,
        call: NodeId,
        after: &[Control],
        budget: &mut usize,
    ) -> Option<Self> {
        let width = run.nodes().len();
        if after.len() > width {
            return None;
        }
        // Pending writes cut dependency walks: their inputs, not their old results, survive.
        let mut produced = vec![false; width];
        produced[run.slot(call)] = true;
        let mut roots = Vec::new();
        let mut repeating = Vec::new();
        let region = |region: RegionId, control: bool| {
            if control {
                graph.region(region).control()
            } else {
                Some(graph.region(region).result())
            }
        };
        for &control in after {
            if roots.len() >= *budget {
                return None;
            }
            let output = match control {
                Control::LoopBounds(node)
                | Control::LoopStart(node)
                | Control::LoopNext(node)
                | Control::LoopRebind(node) => {
                    repeating.push(node);
                    node
                }
                Control::LoopValue { node, from } => {
                    roots.push(from);
                    roots.extend_from_slice(graph.inputs(node));
                    node
                }
                Control::Eval(node) => {
                    roots.push(node);
                    continue;
                }
                Control::Apply(node) | Control::Enter { node, .. } | Control::Phi(node) => {
                    if graph.inputs(node).len() > *budget - roots.len() {
                        return None;
                    }
                    roots.extend_from_slice(graph.inputs(node));
                    node
                }
                Control::Take { node, from } => {
                    roots.push(from);
                    node
                }
                Control::Combine { node, from, .. } => {
                    roots.push(from);
                    roots.push(graph.inputs(node)[0]);
                    node
                }
                Control::Sequence { node, value } | Control::ResultBody { node, body: value } => {
                    roots.push(value);
                    node
                }
                Control::Lazy { node, rhs, .. } => {
                    roots.push(graph.inputs(node)[0]);
                    roots.extend(region(rhs, false));
                    node
                }
                Control::Branch { node, then, else_ } => {
                    roots.push(graph.inputs(node)[0]);
                    roots.extend(region(then, false));
                    roots.extend(else_.and_then(|r| region(r, false)));
                    node
                }
                Control::Observe { node, then, else_ } => {
                    roots.push(graph.inputs(node)[0]);
                    roots.extend(then.and_then(|r| region(r, true)));
                    roots.extend(else_.and_then(|r| region(r, true)));
                    node
                }
                Control::CompleteObserve(node) => node,
                Control::Return(value) => {
                    roots.push(value);
                    run.result()
                }
                Control::ResumeCaller(_) | Control::ResumePackedCaller(_) => return None,
            };
            produced[run.slot(output)] = true;
            if roots.len() > *budget {
                return None;
            }
        }
        let mut seen = vec![false; width];
        // Later iterations read dependencies across pending writes in this iteration.
        for (mut roots, repeating) in [(repeating, true), (roots, false)] {
            while let Some(node) = roots.pop() {
                *budget = budget.checked_sub(1)?;
                let slot = run.slot(node);
                if (!repeating && produced[slot]) || seen[slot] {
                    continue;
                }
                seen[slot] = true;
                let inputs = graph.inputs(node);
                if roots.len() + inputs.len() > *budget {
                    return None;
                }
                roots.extend_from_slice(inputs);
                match graph.node(node).op {
                    Op::Loop(id) => {
                        let loop_ = graph.loop_(id);
                        roots.push(loop_.index);
                        roots.extend(
                            loop_
                                .carried
                                .iter()
                                .flat_map(|&(carry, next)| [carry, next]),
                        );
                        roots.extend(region(loop_.body, false));
                        roots.extend(region(loop_.body, true));
                    }
                    Op::LoopValue { loop_, index } => {
                        roots.push(graph.loop_(loop_).carried[index as usize].0);
                    }
                    Op::Join { then, else_ } => {
                        roots.extend(region(then, false));
                        roots.extend(else_.and_then(|r| region(r, false)));
                    }
                    Op::Observe { then, else_ } => {
                        roots.extend(then.and_then(|r| region(r, true)));
                        roots.extend(else_.and_then(|r| region(r, true)));
                    }
                    Op::And { rhs } | Op::Or { rhs } => roots.extend(region(rhs, false)),
                    Op::Result { .. } => roots.extend(region(run.region(), true)),
                    _ => {}
                }
                if roots.len() > *budget {
                    return None;
                }
            }
        }
        let slots: Box<_> = seen
            .into_iter()
            .enumerate()
            .filter_map(|(slot, live)| live.then_some(slot))
            .collect();
        if slots.len() * 4 >= width {
            return None;
        }
        Some(Self {
            after: after.into(),
            slots,
        })
    }
}
