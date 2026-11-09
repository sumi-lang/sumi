use crate::dependency::{Components, Rows, Traversal};

use super::{Carry, Flows, Lattice};

pub(super) struct Schedule {
    pub components: Components,
    pub cyclic: Vec<bool>,
    pub growth: Option<Growth>,
}

pub(super) struct Growth {
    pub nodes: Vec<bool>,
    pub flows: Vec<bool>,
    pub incoming: Rows,
}

impl Schedule {
    pub fn new<L: Lattice>(flows: &Flows<'_, L>, outgoing: &Rows) -> Self {
        let mut scratch = Traversal::default();
        let mut components = Components::filtered(
            outgoing,
            0..outgoing.len(),
            |_, flow| Some(flows.entries[flow as usize].consumer.index()),
            &mut scratch,
        );
        let mut cyclic = vec![false; components.count()];
        let mut candidates = None;
        for flow in &flows.entries {
            let component = components.of[flow.consumer.index()];
            flow.providers(&flows.others).for_each(|(carry, provider)| {
                if components.of[provider.index()] == component {
                    cyclic[component as usize] = true;
                    if carry == Carry::Grows {
                        candidates.get_or_insert_with(|| vec![false; components.count()])
                            [component as usize] = true;
                    }
                }
            });
        }
        let growth = candidates.and_then(|candidates| {
            Growth::new(flows, outgoing, &components, &candidates, &mut scratch)
        });
        if let Some(growth) = &growth {
            // Narrowing follows dependency paths from the component's traversal root.
            let mut reached = vec![false; outgoing.len()];
            let mut order = Vec::new();
            for component in 0..components.count() {
                let members = components.members(component);
                if !members.iter().any(|&member| growth.nodes[member as usize]) {
                    continue;
                }
                order.clear();
                order.push(members[0]);
                reached[members[0] as usize] = true;
                let mut at = 0;
                while at < order.len() {
                    let member = order[at] as usize;
                    at += 1;
                    for &index in outgoing.get(member) {
                        let consumer = flows.entries[index as usize].consumer.index();
                        if components.of[consumer] as usize == component && !reached[consumer] {
                            reached[consumer] = true;
                            order.push(consumer as u32);
                        }
                    }
                }
                components.members_mut(component).copy_from_slice(&order);
            }
        }
        Self {
            components,
            cyclic,
            growth,
        }
    }
}

impl Growth {
    fn new<L: Lattice>(
        flows: &Flows<'_, L>,
        outgoing: &Rows,
        dependencies: &Components,
        candidates: &[bool],
        scratch: &mut Traversal,
    ) -> Option<Self> {
        let roots = (0..dependencies.count())
            .filter(|&c| candidates[c])
            .flat_map(|c| dependencies.members(c).iter().map(|&node| node as usize));
        // A gating dependency closes no value cycle; both views borrow the same flow index.
        let values = Components::filtered(
            outgoing,
            roots,
            |provider, index| {
                let flow = &flows.entries[index as usize];
                let consumer = flow.consumer.index();
                (dependencies.of[provider] == dependencies.of[consumer]
                    && flow.carry_from(provider, &flows.others) >= Carry::Passes)
                    .then_some(consumer)
            },
            scratch,
        );
        let carries = |flow: &super::Flow<L>, target, least| {
            flow.providers(&flows.others)
                .any(|(carry, provider)| carry >= least && values.of[provider.index()] == target)
        };
        let mut growing = vec![false; values.count()];
        for flow in &flows.entries {
            let target = values.of[flow.consumer.index()];
            if target != u32::MAX && carries(flow, target, Carry::Grows) {
                growing[target as usize] = true;
            }
        }
        if !growing.contains(&true) {
            return None;
        }
        let nodes: Vec<bool> = values
            .of
            .iter()
            .map(|&c| c != u32::MAX && growing[c as usize])
            .collect();
        let cyclic = flows
            .entries
            .iter()
            .map(|flow| {
                let consumer = flow.consumer.index();
                nodes[consumer] && carries(flow, values.of[consumer], Carry::Passes)
            })
            .collect();
        // Each flow occurs once, including repeated providers and providers outside the component.
        let incoming = Rows::new(outgoing.len(), || {
            flows
                .entries
                .iter()
                .enumerate()
                .filter_map(|(index, flow)| {
                    nodes[flow.consumer.index()].then_some((flow.consumer.index(), index as u32))
                })
        });
        Some(Self {
            nodes,
            flows: cyclic,
            incoming,
        })
    }
}
