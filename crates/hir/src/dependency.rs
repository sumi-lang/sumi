//! Compact dependency rows and strongly connected components, numbered with successors first.

pub(crate) struct Rows {
    starts: Vec<u32>,
    entries: Vec<u32>,
}

impl Rows {
    pub fn new<I: Iterator<Item = (usize, u32)>>(rows: usize, entries: impl Fn() -> I) -> Self {
        // The spare leading boundary makes the fill cursors become the row ends.
        let mut starts = vec![0; rows + 2];
        entries().for_each(|(row, _)| {
            starts[row + 2] += 1;
        });
        for row in 0..=rows {
            starts[row + 1] += starts[row];
        }
        let mut values = vec![0; starts[rows + 1] as usize];
        entries().for_each(|(row, value)| {
            let next = &mut starts[row + 1];
            values[*next as usize] = value;
            *next += 1;
        });
        starts.pop();
        Self {
            starts,
            entries: values,
        }
    }

    pub fn len(&self) -> usize {
        self.starts.len() - 1
    }

    pub fn get(&self, row: usize) -> &[u32] {
        &self.entries[self.starts[row] as usize..self.starts[row + 1] as usize]
    }
}

pub(crate) struct Components {
    pub of: Vec<u32>,
    nodes: Vec<u32>,
    ends: Vec<u32>,
}

#[derive(Default)]
pub(crate) struct Traversal {
    walk: Vec<Visit>,
}

struct Visit {
    node: u32,
    low: u32,
    remaining: std::ops::Range<u32>,
}

impl Components {
    pub fn new(edges: &Rows, target: impl Fn(u32) -> usize) -> Self {
        Self::filtered(
            edges,
            0..edges.len(),
            |_, edge| Some(target(edge)),
            &mut Traversal::default(),
        )
    }

    /// Roots and accepted edges describe a closed subgraph; omitted nodes have no component.
    pub fn filtered(
        edges: &Rows,
        roots: impl IntoIterator<Item = usize>,
        target: impl Fn(usize, u32) -> Option<usize>,
        scratch: &mut Traversal,
    ) -> Self {
        let n = edges.len();
        // Open states are one-based pending positions; completed IDs count down from n,
        // so every completed state exceeds the pending length.
        let mut state = vec![0; n];
        // Pending nodes grow from the front; completed components occupy the suffix.
        let mut nodes = vec![0; n];
        let mut pending = 0;
        let mut completed = n;
        let mut ends = Vec::with_capacity(n + 1);
        ends.push(n as u32);
        let walk = &mut scratch.walk;
        walk.clear();
        let visit = |node: usize, low| Visit {
            node: node as u32,
            low,
            remaining: edges.starts[node]..edges.starts[node + 1],
        };

        for root in roots {
            if state[root] != 0 {
                continue;
            }
            state[root] = pending as u32 + 1;
            walk.push(visit(root, state[root]));
            nodes[pending] = root as u32;
            pending += 1;
            while let Some(frame) = walk.last_mut() {
                if let Some(edge) = frame.remaining.next() {
                    let Some(successor) = target(frame.node as usize, edges.entries[edge as usize])
                    else {
                        continue;
                    };
                    if state[successor] == 0 {
                        state[successor] = pending as u32 + 1;
                        walk.push(visit(successor, state[successor]));
                        nodes[pending] = successor as u32;
                        pending += 1;
                    } else if state[successor] <= pending as u32 {
                        frame.low = frame.low.min(state[successor]);
                    }
                    continue;
                }
                let frame = walk.pop().expect("the frame just visited");
                if frame.low == state[frame.node as usize] {
                    let component = (ends.len() - 1) as u32;
                    loop {
                        pending -= 1;
                        let member = nodes[pending];
                        state[member as usize] = n as u32 - component;
                        completed -= 1;
                        nodes[completed] = member;
                        if member == frame.node {
                            break;
                        }
                    }
                    ends.push(completed as u32);
                }
                if let Some(parent) = walk.last_mut() {
                    parent.low = parent.low.min(frame.low);
                }
            }
        }
        for component in &mut state {
            *component = if *component == 0 {
                u32::MAX
            } else {
                n as u32 - *component
            };
        }
        Self {
            of: state,
            nodes,
            ends,
        }
    }

    pub fn count(&self) -> usize {
        self.ends.len() - 1
    }

    /// Members start at their traversal root until sorted.
    pub fn members(&self, component: usize) -> &[u32] {
        &self.nodes[self.ends[component + 1] as usize..self.ends[component] as usize]
    }

    pub fn members_mut(&mut self, component: usize) -> &mut [u32] {
        &mut self.nodes[self.ends[component + 1] as usize..self.ends[component] as usize]
    }

    pub fn sort_members(&mut self) {
        for ends in self.ends.windows(2) {
            self.nodes[ends[1] as usize..ends[0] as usize].sort_unstable();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn components_are_mutually_reachable_and_successors_finish_first() {
        for n in 0..=4 {
            for bits in 0u32..1 << (n * n) {
                let edges = Rows::new(n, || {
                    (0..n).flat_map(|from| {
                        (0..n).filter_map(move |to| {
                            (bits & (1 << (from * n + to)) != 0).then_some((from, to as u32))
                        })
                    })
                });
                let components = Components::new(&edges, |node| node as usize);
                let mut reaches = vec![vec![false; n]; n];
                for (from, row) in reaches.iter_mut().enumerate() {
                    row[from] = true;
                    for &to in edges.get(from) {
                        row[to as usize] = true;
                        assert!(components.of[from] >= components.of[to as usize]);
                    }
                }
                for via in 0..n {
                    for from in 0..n {
                        for to in 0..n {
                            reaches[from][to] |= reaches[from][via] && reaches[via][to];
                        }
                    }
                }
                for (from, from_reaches) in reaches.iter().enumerate() {
                    for (to, to_reaches) in reaches.iter().enumerate() {
                        assert_eq!(
                            components.of[from] == components.of[to],
                            from_reaches[to] && to_reaches[from]
                        );
                    }
                }
                let mut listed = vec![false; n];
                for component in 0..components.count() {
                    assert!(!components.members(component).is_empty());
                    for &member in components.members(component) {
                        assert_eq!(components.of[member as usize] as usize, component);
                        assert!(!std::mem::replace(&mut listed[member as usize], true));
                    }
                }
                assert!(listed.into_iter().all(|listed| listed));
            }
        }
    }

    #[test]
    fn deep_dependencies_use_no_call_stack() {
        let n = 32_768;
        for cycle in [false, true] {
            let edges = Rows::new(n, || {
                (0..n - 1)
                    .map(|node| (node, node as u32 + 1))
                    .chain(cycle.then_some((n - 1, 0)))
            });
            let components = Components::new(&edges, |node| node as usize);
            assert_eq!(components.count(), if cycle { 1 } else { n });
            if cycle {
                assert_eq!(components.members(0).len(), n);
            } else {
                for node in 0..n {
                    assert_eq!(components.of[node] as usize, n - 1 - node);
                }
            }
        }
    }

    #[test]
    fn filtered_components_omit_gates_and_nodes_outside_the_roots() {
        let arcs = [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2), (3, 4), (4, 3)];
        let edges = Rows::new(6, || arcs.into_iter());
        let mut scratch = Traversal::default();
        for roots in [vec![0, 1, 2], vec![3], vec![], vec![0]] {
            let components = Components::filtered(
                &edges,
                roots.iter().copied(),
                |from, to| ((from, to) != (2, 1)).then_some(to as usize),
                &mut scratch,
            );
            let included = |node| match node {
                0..=2 => roots.contains(&0),
                3..=4 => roots.contains(&3),
                _ => false,
            };
            for node in 0..6 {
                assert_eq!(components.of[node] != u32::MAX, included(node));
            }
            if included(0) {
                assert_eq!(components.of[0], components.of[1]);
                assert!(components.of[1] > components.of[2]);
                assert_eq!(components.count(), 2);
            }
            if included(3) {
                assert_eq!(components.of[3], components.of[4]);
                assert_eq!(components.count(), 1);
            }
        }
    }
}
