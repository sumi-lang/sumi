//! Call-continuation liveness for consuming runs. A layout applies only to its exact pending stack.

use super::Control;
use crate::{Graph, NodeId, Op, RegionId, Role, Run};

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
        let region = |region: RegionId, wants_control: bool| {
            if wants_control {
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
                let edges = graph.edges(node);
                if roots.len() + edges.len() > *budget {
                    return None;
                }
                // Declarations and contexts hold no value a later read takes.
                roots.extend(
                    edges
                        .iter()
                        .zip(graph.roles(node))
                        .filter(|(_, role)| !matches!(role, Role::Declaration | Role::Context))
                        .map(|(&edge, _)| edge),
                );
                let op = &graph.node(node).op;
                let wants_control = matches!(op, Op::Observe { .. });
                for owned in op.regions() {
                    roots.extend(region(owned, wants_control));
                    if matches!(op, Op::Loop { .. }) {
                        roots.extend(region(owned, true));
                    }
                }
                if matches!(op, Op::Result { .. }) {
                    roots.extend(region(run.region(), true));
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
