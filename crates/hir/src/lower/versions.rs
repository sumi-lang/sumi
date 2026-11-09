//! Versions of locals across regions: the node each local's reads see, taken back when the region
//! that assigned it closes, and the refinements a guard gives a version inside its region.

use sumi_graph::NodeId;

use super::body::LocalId;

/// A local, the version of it a guard narrows, and the node reads of that version see.
pub(super) type Refinement = (LocalId, NodeId, NodeId);

pub(super) struct Versions {
    /// By local, the version its reads see outside any refinement.
    current: Vec<NodeId>,
    /// By local; only a mutable's refinements are a region's state, since no other is merged.
    is_mutable: Vec<bool>,
    /// In open regions, innermost last.
    refinements: Vec<Refinement>,
    /// Versions replaced inside open regions, with the ones they replaced, innermost last.
    undo: Vec<(LocalId, NodeId)>,
    /// Open forks, innermost last.
    forks: Vec<Fork>,
}

/// Where a region began: assignments and refinements past these are its own, and a local
/// declared past `locals` is not undone, since nothing outside reads it.
#[derive(Clone, Copy)]
struct Fork {
    undo: usize,
    refinements: usize,
    locals: usize,
}

/// What a closed region did to the versions: each local it assigned, with the version before it
/// and the node its reads saw at the close, and the refinements of mutables that held inside.
pub(super) struct RegionState {
    pub changes: Vec<(LocalId, NodeId, NodeId)>,
    pub refinements: Vec<Refinement>,
    pub context: NodeId,
}

impl Versions {
    pub fn new() -> Self {
        Self {
            current: Vec::new(),
            is_mutable: Vec::new(),
            refinements: Vec::new(),
            undo: Vec::new(),
            forks: Vec::new(),
        }
    }

    pub fn clear(&mut self) {
        self.current.clear();
        self.is_mutable.clear();
        self.refinements.clear();
        self.undo.clear();
        self.forks.clear();
    }

    /// The next local, declared at `node`.
    pub fn declare(&mut self, node: NodeId, is_mutable: bool) -> LocalId {
        self.current.push(node);
        self.is_mutable.push(is_mutable);
        LocalId::new(self.current.len() - 1)
    }

    pub fn is_mutable(&self, local: LocalId) -> bool {
        self.is_mutable[local.index()]
    }

    /// The version itself, which a refinement is of.
    pub fn version(&self, local: LocalId) -> NodeId {
        self.current[local.index()]
    }

    /// The node a read of `local` sees: its version, refined by the innermost guard on it.
    pub fn read(&self, local: LocalId) -> NodeId {
        let version = self.current[local.index()];
        self.refinements
            .iter()
            .rev()
            .find(|&&(refined, source, _)| refined == local && source == version)
            .map_or(version, |&(_, _, node)| node)
    }

    /// Assigns `version`; inside a region, the one it replaces comes back when the region closes.
    pub fn set(&mut self, local: LocalId, version: NodeId) {
        if let Some(fork) = self.forks.last()
            && local.index() < fork.locals
        {
            self.undo.push((local, self.current[local.index()]));
        }
        self.current[local.index()] = version;
    }

    /// Reads of `local` at `version` see `read` until the region closes.
    pub fn refine(&mut self, local: LocalId, version: NodeId, read: NodeId) {
        self.refinements.push((local, version, read));
    }

    /// Opens a region.
    pub fn fork(&mut self) {
        self.forks.push(Fork {
            undo: self.undo.len(),
            refinements: self.refinements.len(),
            locals: self.current.len(),
        });
    }

    /// Closes the innermost region, undoing its assignments, as its state under `context`.
    pub fn join(&mut self, context: NodeId) -> RegionState {
        let fork = self.forks.pop().expect("a region forks before it joins");
        let mut changed: Vec<LocalId> = self.undo[fork.undo..]
            .iter()
            .map(|&(local, _)| local)
            .collect();
        changed.sort_unstable_by_key(|local| local.index());
        changed.dedup();
        let state = self.state(&changed, fork.refinements, context);
        for (local, version) in self.undo.drain(fork.undo..).rev() {
            self.current[local.index()] = version;
        }
        self.refinements.truncate(fork.refinements);
        state
    }

    /// Where refinements stand, for a guard that opens no region.
    pub fn mark(&self) -> usize {
        self.refinements.len()
    }

    /// The state of a guard that assigned nothing: its refinements since `mark`, then dropped.
    pub fn guarded(&mut self, mark: usize, context: NodeId) -> RegionState {
        let state = self.state(&[], mark, context);
        self.refinements.truncate(mark);
        state
    }

    /// The refinements since `mark`, taken out to hold again wherever their guard does.
    pub fn take(&mut self, mark: usize) -> Vec<Refinement> {
        self.refinements.split_off(mark)
    }

    /// Holds `refinements` again, in their order, until the region closes or they are taken.
    pub fn hold(&mut self, refinements: &[Refinement]) {
        self.refinements.extend_from_slice(refinements);
    }

    fn state(&self, changed: &[LocalId], since: usize, context: NodeId) -> RegionState {
        RegionState {
            changes: changed
                .iter()
                .map(|&local| (local, self.version(local), self.read(local)))
                .collect(),
            refinements: self.refinements[since..]
                .iter()
                .copied()
                .filter(|&(local, _, _)| self.is_mutable(local))
                .collect(),
            context,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(index: usize) -> NodeId {
        NodeId::new(index)
    }

    #[test]
    fn a_region_undoes_what_it_assigned_and_reports_it_as_its_state() {
        let mut versions = Versions::new();
        let x = versions.declare(node(1), true);
        let y = versions.declare(node(2), true);
        versions.fork();
        versions.set(x, node(10));
        versions.set(x, node(11));
        let inner = versions.declare(node(12), true);
        versions.set(inner, node(13));
        let state = versions.join(node(99));
        assert_eq!(state.context, node(99));
        assert_eq!(state.changes, [(x, node(11), node(11))]);
        assert_eq!(versions.version(x), node(1));
        assert_eq!(versions.version(y), node(2));
        assert_eq!(versions.version(inner), node(13));
    }

    #[test]
    fn a_refinement_is_read_for_its_version_alone_and_ends_with_its_region() {
        let mut versions = Versions::new();
        let x = versions.declare(node(1), true);
        let c = versions.declare(node(2), false);
        versions.fork();
        versions.refine(x, node(1), node(20));
        versions.refine(c, node(2), node(21));
        assert_eq!(versions.read(x), node(20));
        assert_eq!(versions.read(c), node(21));
        versions.set(x, node(30));
        assert_eq!(versions.read(x), node(30));
        let state = versions.join(node(99));
        assert_eq!(state.refinements, [(x, node(1), node(20))]);
        assert_eq!(state.changes, [(x, node(30), node(30))]);
        assert_eq!(versions.read(x), node(1));
    }

    #[test]
    fn a_guard_without_a_region_keeps_only_its_refinements() {
        let mut versions = Versions::new();
        let x = versions.declare(node(1), true);
        let mark = versions.mark();
        versions.refine(x, node(1), node(5));
        let state = versions.guarded(mark, node(9));
        assert!(state.changes.is_empty());
        assert_eq!(state.refinements, [(x, node(1), node(5))]);
        assert_eq!(versions.read(x), node(1));
    }

    #[test]
    fn a_guard_taken_out_holds_again_in_each_region_it_guards() {
        let mut versions = Versions::new();
        let x = versions.declare(node(1), true);
        let mark = versions.mark();
        versions.refine(x, node(1), node(5));
        let guard = versions.take(mark);
        assert_eq!(versions.read(x), node(1));
        for context in [node(8), node(9)] {
            versions.fork();
            versions.hold(&guard);
            assert_eq!(versions.read(x), node(5));
            let state = versions.join(context);
            assert_eq!(state.refinements, guard);
            assert_eq!(versions.read(x), node(1));
        }
        let mark = versions.mark();
        versions.hold(&guard);
        versions.refine(x, node(1), node(6));
        assert_eq!(
            versions.take(mark),
            [(x, node(1), node(5)), (x, node(1), node(6))]
        );
        assert_eq!(versions.read(x), node(1));
    }
}
