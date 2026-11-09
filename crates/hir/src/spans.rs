//! Where the graph's nodes and regions come from in the source. The graph carries no position; this
//! holds one entry per node and per region, in the order the builder made them.

use sumi_graph::{Graph, NodeId, RegionId};
use sumi_text::TextRange;

pub struct Spans {
    nodes: Box<[NodeSpan]>,
    reads: Box<[TextRange]>,
    /// By node, ascending.
    annotations: Box<[(NodeId, TextRange)]>,
    result_reads: Box<[TextRange]>,
}

#[derive(Clone, Copy)]
struct NodeSpan {
    origin: TextRange,
    name: Option<TextRange>,
    /// Where the node's reads begin in `reads`; they end where the next node's begin.
    reads: u32,
}

fn reads<'a>(nodes: &[NodeSpan], reads: &'a [TextRange], node: NodeId) -> &'a [TextRange] {
    let start = nodes[node.index()].reads as usize;
    let end = nodes
        .get(node.index() + 1)
        .map_or(reads.len(), |next| next.reads as usize);
    &reads[start..end]
}

/// `annotations` ascend by node.
fn annotation(annotations: &[(NodeId, TextRange)], node: NodeId) -> Option<TextRange> {
    let index = annotations
        .binary_search_by_key(&node.index(), |(node, _)| node.index())
        .ok()?;
    Some(annotations[index].1)
}

impl Spans {
    /// The syntax that built the node.
    pub fn origin(&self, node: NodeId) -> TextRange {
        self.nodes[node.index()].origin
    }

    /// The name a declaration carries.
    pub fn name(&self, node: NodeId) -> Option<TextRange> {
        self.nodes[node.index()].name
    }

    /// Where the node reads each input, parallel to the graph's inputs: the read's range, not the
    /// definition's.
    pub fn reads(&self, node: NodeId) -> &[TextRange] {
        reads(&self.nodes, &self.reads, node)
    }

    /// The type annotation a `Copy` or `Result` is declared with.
    pub fn annotation(&self, node: NodeId) -> Option<TextRange> {
        annotation(&self.annotations, node)
    }

    /// Where a region's result is read: a block's tail, or the expression itself.
    pub fn result_read(&self, region: RegionId) -> TextRange {
        self.result_reads[region.index()]
    }
}

/// Collects the spans beside a `GraphBuilder`: one `push` per node the builder pushes, in the
/// same order, and one `close` per region. What is pushed reads as the finished spans do.
pub(crate) struct SpansBuilder {
    nodes: Vec<NodeSpan>,
    reads: Vec<TextRange>,
    annotations: Vec<(NodeId, TextRange)>,
    /// By region; none until it closes.
    result_reads: Vec<Option<TextRange>>,
}

impl SpansBuilder {
    pub fn new(nodes: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(nodes),
            reads: Vec::with_capacity(nodes),
            annotations: Vec::new(),
            result_reads: Vec::new(),
        }
    }

    pub fn origin(&self, node: NodeId) -> TextRange {
        self.nodes[node.index()].origin
    }

    pub fn name(&self, node: NodeId) -> Option<TextRange> {
        self.nodes[node.index()].name
    }

    pub fn reads(&self, node: NodeId) -> &[TextRange] {
        reads(&self.nodes, &self.reads, node)
    }

    pub fn annotation(&self, node: NodeId) -> Option<TextRange> {
        annotation(&self.annotations, node)
    }

    /// Of a region already closed.
    pub fn result_read(&self, region: RegionId) -> TextRange {
        self.result_reads[region.index()].expect("a region read is closed")
    }

    /// `reads` is where the node reads each input, in input order.
    pub fn push(
        &mut self,
        origin: TextRange,
        name: Option<TextRange>,
        reads: impl Iterator<Item = TextRange>,
    ) {
        self.nodes.push(NodeSpan {
            origin,
            name,
            reads: u32::try_from(self.reads.len()).expect("read count fits u32"),
        });
        self.reads.extend(reads);
    }

    /// `node` is the last pushed.
    pub fn annotate(&mut self, node: NodeId, at: TextRange) {
        assert_eq!(
            node.index() + 1,
            self.nodes.len(),
            "an annotation names the last node"
        );
        self.annotations.push((node, at));
    }

    pub fn close(&mut self, region: RegionId, at: TextRange) {
        if self.result_reads.len() <= region.index() {
            self.result_reads.resize(region.index() + 1, None);
        }
        self.result_reads[region.index()] = Some(at);
    }

    /// `graph` is the one built alongside.
    pub fn finish(self, graph: &Graph) -> Spans {
        assert_eq!(self.nodes.len(), graph.nodes().len(), "a span per node");
        assert_eq!(
            self.result_reads.len(),
            graph.region_ids().len(),
            "a result read per region"
        );
        Spans {
            nodes: self.nodes.into_boxed_slice(),
            reads: self.reads.into_boxed_slice(),
            annotations: self.annotations.into_boxed_slice(),
            result_reads: self
                .result_reads
                .into_iter()
                .map(|at| at.expect("a result read per region"))
                .collect(),
        }
    }
}
