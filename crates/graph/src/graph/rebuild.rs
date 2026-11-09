//! Reconstruction in original node order. Retention counts map identities and interval boundaries;
//! operands and references are read from source slices and mapped directly into the output.

use std::ops::Range;

use super::{Graph, NodeId, Op, Operand, References, Region, RegionId, Run, Store};

struct Selection {
    before: Vec<u32>,
}

impl Selection {
    fn new(kept: &[bool]) -> Self {
        let mut before = Vec::with_capacity(kept.len() + 1);
        before.push(0);
        for &keep in kept {
            before.push(before.last().unwrap() + u32::from(keep));
        }
        Self { before }
    }

    fn len(&self) -> usize {
        *self.before.last().unwrap() as usize
    }

    fn index(&self, index: usize) -> usize {
        let before = self.before[index];
        assert!(before < self.before[index + 1], "a named item is retained");
        before as usize
    }

    fn interval(&self, range: Range<u32>) -> Range<u32> {
        self.before[range.start as usize]..self.before[range.end as usize]
    }
}

/// A graph's retained nodes and regions, with replacements expressed in its original IDs.
/// Run entries and parameters stay unchanged; named nodes resolve to survivors and arms stay whole.
pub struct Rebuild<'a, F> {
    source: &'a Graph,
    resolve: F,
    node_map: Selection,
    region_map: Selection,
    store: Store,
    origins: Vec<NodeId>,
    regions: Vec<Region>,
}

impl<'a, F: Fn(NodeId) -> NodeId> Rebuild<'a, F> {
    /// The masks select one entry per source node and region; `edges` sizes the output edge buffers.
    pub fn new(
        source: &'a Graph,
        nodes: &[bool],
        regions: &[bool],
        edges: usize,
        resolve: F,
    ) -> Self {
        assert_eq!(nodes.len(), source.nodes().len());
        assert_eq!(regions.len(), source.region_ids().len());
        let node_map = Selection::new(nodes);
        let region_map = Selection::new(regions);
        let store = Store {
            nodes: Vec::with_capacity(node_map.len()),
            edges: Vec::with_capacity(edges),
            roles: Vec::with_capacity(edges),
        };
        Self {
            source,
            resolve,
            origins: Vec::with_capacity(node_map.len()),
            regions: Vec::with_capacity(region_map.len()),
            node_map,
            region_map,
            store,
        }
    }

    fn node(&self, node: NodeId) -> NodeId {
        NodeId::new(self.node_map.index((self.resolve)(node).index()))
    }

    /// Each selected node must be pushed once, in source order.
    pub fn push(
        &mut self,
        origin: NodeId,
        op: Op,
        inputs: impl IntoIterator<Item = Operand>,
        references: References<'_>,
    ) {
        assert_eq!(self.node_map.index(origin.index()), self.store.nodes.len());
        let op = op.with_regions(|id| RegionId::new(self.region_map.index(id.index())));
        let node_map = &self.node_map;
        let resolve = &self.resolve;
        self.store.push(op, inputs, references, |id| {
            NodeId::new(node_map.index(resolve(id).index()))
        });
        self.origins.push(origin);
    }

    /// Each selected region must be supplied once, in source order, with its replacement exit.
    pub fn region(
        &mut self,
        id: RegionId,
        result: NodeId,
        result_has_value: bool,
        control: Option<NodeId>,
    ) {
        assert_eq!(self.region_map.index(id.index()), self.regions.len());
        let original = self.source.region(id);
        self.regions.push(Region {
            context: self.node(original.context),
            nodes: self.node_map.interval(original.nodes.clone()),
            result: self.node(result),
            result_has_value,
            control: control.map(|id| self.node(id)),
        });
    }

    /// The compacted graph and the original ID of each node in output order.
    pub fn finish(self) -> (Graph, Box<[NodeId]>) {
        assert_eq!(self.store.nodes.len(), self.node_map.len());
        assert_eq!(self.regions.len(), self.region_map.len());
        let runs = self
            .source
            .runs()
            .iter()
            .map(|run| Run {
                nodes: self.node_map.interval(run.nodes.clone()),
                arity: run.arity,
                region: RegionId::new(self.region_map.index(run.region.index())),
                result: self.node(run.result),
                params: run.params.clone(),
            })
            .collect();
        let graph = Graph {
            store: self.store,
            regions: self.regions,
            runs,
            built: self.source.built.clone(),
            decls: self.source.decls.clone(),
            unions: self.source.unions.clone(),
        };
        (graph, self.origins.into_boxed_slice())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Case, GraphBuilder, Machine, Role, Ty, Value};

    #[test]
    fn compaction_preserves_nested_intervals_empty_arms_and_completing_reads() {
        let mut builder = GraphBuilder::new(20);
        let choose = builder.function(Some(Box::new([Ty::BOOL])));
        let returning = builder.function(Some(Box::new([])));
        let run = builder.open_run(choose);
        let entry = builder.push(Op::Entry, [], References::None);
        let param = builder.push(
            Op::Param {
                index: 0,
                ty: Some(Ty::BOOL),
            },
            [],
            References::None,
        );
        let outer = builder.open(entry);
        builder.enter(outer);
        let discarded = builder.open(entry);
        builder.enter(discarded);
        builder.close(discarded, param);
        let dead = builder.push(Op::And { rhs: discarded }, [param], References::None);
        let yes = builder.push(Op::Arm(Case::Bool(true)), [param, entry], References::None);
        let no = builder.push(Op::Arm(Case::Bool(false)), [param, entry], References::None);
        let arms = builder.open_arms(&[yes, no]);
        let mut branches = arms.iter();
        let first = branches.next().unwrap();
        let second = branches.next().unwrap();
        builder.enter(first);
        let alias = builder.push(Op::Copy { declared: None }, [param], References::None);
        builder.close(first, alias);
        builder.enter(second);
        let rhs = builder.open(no);
        builder.enter(rhs);
        let not = builder.push(Op::Not, [alias], References::None);
        builder.close(rhs, not);
        let lazy = builder.push(Op::Or { rhs }, [param], References::None);
        builder.close(second, lazy);
        let switch = builder.push(Op::Switch { arms }, [param], References::None);
        builder.close(outer, switch);
        builder.close_run(run, outer, switch);

        let run = builder.open_run(returning);
        let entry = builder.push(Op::Entry, [], References::None);
        let region = builder.open(entry);
        builder.enter(region);
        let seven = builder.push(Op::Int(7.into()), [], References::None);
        let ret = builder.push(Op::Return, [seven, entry], References::None);
        let neg = builder.push(Op::Neg, [ret], References::None);
        builder.complete_input(neg, 0);
        builder.close_with_control(region, neg, false, Some(ret));
        builder.close_run(run, region, neg);
        let source = builder.finish();

        let kept: Vec<_> = source
            .node_ids()
            .map(|id| id != dead && id != alias)
            .collect();
        let regions: Vec<_> = source.region_ids().map(|id| id != discarded).collect();
        let edges = source
            .node_ids()
            .filter(|id| kept[id.index()])
            .map(|id| source.edges(id).len())
            .sum();
        let mut rebuild = Rebuild::new(&source, &kept, &regions, edges, |id| {
            if id == alias { param } else { id }
        });
        for id in source.region_ids().filter(|&id| id != discarded) {
            let region = source.region(id);
            rebuild.region(
                id,
                region.result(),
                region.result_has_value(),
                region.control(),
            );
        }
        for id in source.node_ids().filter(|&id| id != dead && id != alias) {
            rebuild.push(
                id,
                source.node(id).op.clone(),
                source.operands(id),
                source.references(id),
            );
        }
        let (graph, origins) = rebuild.finish();
        assert_eq!(graph.store.nodes.capacity(), origins.len());
        assert_eq!(graph.store.edges.capacity(), edges);
        assert_eq!(graph.store.roles.capacity(), edges);
        assert_eq!(graph.regions.capacity(), graph.region_ids().len());
        let mapped = |old| NodeId::new(origins.iter().position(|&id| id == old).unwrap());
        let mapped_region = |old| {
            RegionId::new(
                source
                    .region_ids()
                    .filter(|&id| id != discarded)
                    .position(|id| id == old)
                    .unwrap(),
            )
        };
        assert_eq!(origins.len(), source.nodes().len() - 2);
        assert_eq!(graph.region_ids().len(), source.region_ids().len() - 1);
        assert_eq!(
            graph.node(mapped(lazy)).op,
            Op::Or {
                rhs: mapped_region(rhs)
            }
        );
        let Op::Switch { arms: mapped_arms } = graph.node(mapped(switch)).op else {
            panic!()
        };
        assert!(mapped_arms.iter().eq(arms.iter().map(mapped_region)));
        assert_eq!(graph.region(mapped_region(first)).nodes().len(), 0);
        assert_eq!(
            graph.region(mapped_region(first)).start(),
            graph.region(mapped_region(second)).start()
        );
        assert_eq!(graph.region(mapped_region(first)).result(), mapped(param));
        assert_eq!(
            graph.region(mapped_region(rhs)).nodes().collect::<Vec<_>>(),
            [mapped(not)]
        );
        assert_eq!(
            graph
                .region(mapped_region(second))
                .nodes()
                .collect::<Vec<_>>(),
            [mapped(not), mapped(lazy)]
        );
        assert_eq!(graph.inputs(mapped(not)), [mapped(param)]);
        assert_eq!(graph.input_roles(mapped(neg)), [Role::Completes]);
        assert_eq!(
            graph.region(mapped_region(region)).control(),
            Some(mapped(ret))
        );
        assert!(!graph.region(mapped_region(region)).result_has_value());
        assert_eq!(graph.run(returning).entry(), mapped(entry));
        for value in [false, true] {
            assert_eq!(
                Machine::new(&graph, choose, &[Value::Bool(value)], None).run(),
                Ok(Value::Bool(true))
            );
        }
        assert_eq!(
            Machine::new(&graph, returning, &[], None).run(),
            Ok(Value::Int(7.into()))
        );
    }
}
