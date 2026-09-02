//! Matching a node's children to the typed fields its grammar rule
//! declares, for the generated views in [`crate::ast`].
//!
//! A rule lists its children in order, each with a type and a cardinality.
//! A parsed tree is error-tolerant, so a node may lack any of them, and a
//! child's type alone does not always say which field it fills: the body
//! block of an `if` whose condition is missing looks exactly like a block
//! condition. [`assign`] therefore enumerates every reading of the children
//! that respects the rule's order and types, and answers a field only when
//! every reading agrees on it. On a node without an error the grammar
//! guarantees the shape, so the reading is unique; on a node with one, a
//! child that could fill two fields fills neither, and an accessor never
//! names a child that might belong to another.

use crate::index::NodeIdx;
use crate::tree::SyntaxTree;

/// One single-valued field of a node rule: the test for a child that fits
/// it, and whether the rule requires it.
pub struct FieldSpec {
    pub fits: fn(&SyntaxTree, NodeIdx) -> bool,
    pub required: bool,
}

/// The child each field of `node` receives, or `None` where no child does
/// or where the readings disagree.
///
/// A reading gives every child that fits some field to one field, each
/// field at most one child, in source order. On a node without an error it
/// must also fill every required field, which the grammar promises is
/// possible. The scan reads the tree's own child order and keeps at most
/// `N` candidates on the stack, so it allocates nothing; more fitting
/// children than fields is a shape no reading can place.
pub fn assign<const N: usize>(
    tree: &SyntaxTree,
    node: NodeIdx,
    specs: &[FieldSpec; N],
) -> [Option<NodeIdx>; N] {
    // TODO: every single-valued accessor runs this over all of its node's
    // children, so a consumer reading several fields of one node repeats
    // the scan and the enumeration for each. A generated combined accessor
    // per node kind, answering every field from one call, would take one
    // scan per node instead; the `ast` benchmark measures the views against
    // a raw walk, so add the combined form once a consumer exists to
    // measure it against.
    //
    // The fitting children, last first as the tree yields them.
    let mut children = [None; N];
    let mut count = 0;
    for child in tree.children(node) {
        if specs.iter().any(|spec| (spec.fits)(tree, child)) {
            if count == N {
                return [None; N];
            }
            children[count] = Some(child);
            count += 1;
        }
    }
    let mut search = Search {
        tree,
        specs,
        strict: !tree.has_error(node),
        current: [None; N],
        agreed: [None; N],
        disputed: [false; N],
        readings: 0,
    };
    search.place(&children[..count], 0, N);
    let mut fields = [None; N];
    for (field, slot) in fields.iter_mut().enumerate() {
        if search.readings > 0 && !search.disputed[field] {
            *slot = search.agreed[field];
        }
    }
    fields
}

/// The enumeration of readings: children are placed last first into fields
/// from the last down, so that source order is kept by construction.
struct Search<'a, const N: usize> {
    tree: &'a SyntaxTree,
    specs: &'a [FieldSpec; N],
    /// Whether every required field must be filled: the node has no error.
    strict: bool,
    current: [Option<NodeIdx>; N],
    /// What every reading so far gave each field.
    agreed: [Option<NodeIdx>; N],
    disputed: [bool; N],
    readings: usize,
}

impl<const N: usize> Search<'_, N> {
    /// Place `children[next..]` into fields below `limit`.
    fn place(&mut self, children: &[Option<NodeIdx>], next: usize, limit: usize) {
        if next == children.len() {
            let unfilled = self.specs[..limit].iter().any(|spec| spec.required);
            if !(self.strict && unfilled) {
                self.record();
            }
            return;
        }
        let child = children[next].expect("gathered children are present");
        let mut field = limit;
        while field > 0 {
            field -= 1;
            if (self.specs[field].fits)(self.tree, child) {
                self.current[field] = Some(child);
                self.place(children, next + 1, field);
                self.current[field] = None;
            }
            // Passing a field leaves it empty for good: every remaining
            // child comes earlier in the source and fills a lower field.
            if self.strict && self.specs[field].required {
                break;
            }
        }
    }

    fn record(&mut self) {
        for field in 0..N {
            if self.readings == 0 {
                self.agreed[field] = self.current[field];
            } else if self.agreed[field] != self.current[field] {
                self.disputed[field] = true;
            }
        }
        self.readings += 1;
    }
}
