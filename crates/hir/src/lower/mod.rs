//! Lowering of one file to the graph: names, structure, and holes. Name and syntax failures become
//! holes rather than graph nodes.

mod body;
mod declare;
mod source;
mod versions;

use sumi_graph::{FunctionId, NodeId};
use sumi_syntax::NodeIdx;
use sumi_text::TextRange;

pub(crate) use body::lower;
pub(crate) use declare::{Header, HeaderResult, declare};
pub(crate) use source::{Params, Source, diagnostic};

use crate::{Binding, Occurrence};

/// A division whose divisor must exclude zero under `context`.
pub(crate) struct Obligation {
    pub owner: u32,
    pub node: NodeIdx,
    pub divisor: NodeId,
    pub context: NodeId,
}

pub(crate) struct Call {
    pub node: NodeId,
    pub caller: FunctionId,
    pub callee: FunctionId,
    pub context: NodeId,
}

/// A block's statement and the context it runs in, which is dead after one that never completes.
pub(crate) struct Statement {
    pub owner: FunctionId,
    pub block: NodeIdx,
    pub range: TextRange,
    pub context: NodeId,
}

#[derive(Clone, Copy)]
pub(crate) struct Fallthrough {
    pub value: NodeId,
    pub at: TextRange,
}

pub(crate) struct Lowered {
    /// By function.
    pub built: Vec<bool>,
    /// By node.
    pub typed: Vec<bool>,
    /// Whole calls only, in definition order.
    pub calls: Vec<Call>,
    /// Every typed call and its callee, whole or not: the result flows into a call missing an
    /// argument too.
    pub called: Vec<(NodeId, FunctionId)>,
    /// (context, callee) of every call whose callee has a whole parameter list, whole call or not.
    pub entered: Vec<(NodeId, FunctionId)>,
    pub obligations: Vec<Obligation>,
    pub fallthroughs: Vec<Option<Fallthrough>>,
    pub bindings: Vec<Binding>,
    /// In source order once `lower` returns.
    pub references: Vec<Occurrence>,
    /// Names under a hole that a declaration under the same hole may bind, so nothing resolves
    /// them; in source order once `lower` returns.
    pub unresolved: Vec<TextRange>,
    /// In source order within each block.
    pub statements: Vec<Statement>,
    /// Each field read and its name's range; which field it names is the typing's to say.
    pub field_reads: Vec<(NodeId, TextRange)>,
}

/// `a`, `a and b`, or `a, b, and c`.
pub(crate) fn join(types: &[String]) -> String {
    match types.split_last() {
        None => unreachable!("a list of types names one"),
        Some((only, [])) => only.clone(),
        Some((last, [first])) => format!("{first} and {last}"),
        Some((last, rest)) => format!("{}, and {last}", rest.join(", ")),
    }
}
