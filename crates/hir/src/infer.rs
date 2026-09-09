//! Private scalar equality solving. Equality is local to a declaration; imports
//! propagate evidence in one direction and never unify caller and callee.
//!
//! The checker owns constraint origins, name/structural poison, and draft HIR.
//! This context owns only terms, equality classes, and directed imports. Build
//! once, solve once, then replay local obligations with final imports for stable
//! diagnostics. Only finalized concrete types cross into public HIR.
//!
//! Fixed annotations export a constant independently of body checking. Inferred
//! results export their root class, even when an unrelated body obligation fails.
//! Unknown imports are not defaulted; conflicting evidence is never retracted.
//! No SCC scheduling is needed: every class changes a bounded number of times.
//!
//! This is equality solving, not subtyping or generic instantiation. Structural
//! types will need structural unification (and occurs checks), replacing scalar
//! evidence here, not adding unknown types to public HIR or another syntax walk.
use std::collections::VecDeque;
use std::num::NonZeroUsize;

use crate::Ty;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Term {
    Known(Ty),
    Var(usize),
}

impl From<Ty> for Term {
    fn from(ty: Ty) -> Self {
        Self::Known(ty)
    }
}

// A join preserves all evidence, rather than choosing the first arriving type.
// Empty is unresolved, singleton is solved, multiple bits mean conflict.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
struct Evidence(u8);

impl Evidence {
    fn known(ty: Ty) -> Self {
        Self(match ty {
            Ty::Int => 1,
            Ty::Bool => 2,
            Ty::Unit => 4,
        })
    }

    fn ty(self) -> Option<Ty> {
        match self.0 {
            1 => Some(Ty::Int),
            2 => Some(Ty::Bool),
            4 => Some(Ty::Unit),
            _ => None,
        }
    }
}

#[derive(Default)]
pub(super) struct Inference {
    parent: Vec<usize>,
    size: Vec<usize>,
    evidence: Vec<Evidence>,
    imports: Vec<(Term, Term)>,
}

impl Inference {
    pub fn fresh(&mut self) -> Term {
        let id = self.parent.len();
        self.parent.push(id);
        self.size.push(1);
        self.evidence.push(Evidence::default());
        Term::Var(id)
    }

    fn root(&self, mut id: usize) -> usize {
        while self.parent[id] != id {
            id = self.parent[id];
        }
        id
    }

    fn compress(&mut self, mut id: usize) -> usize {
        let root = self.root(id);
        while self.parent[id] != id {
            let next = self.parent[id];
            self.parent[id] = root;
            id = next;
        }
        root
    }

    fn evidence(&self, term: Term) -> Evidence {
        match term {
            Term::Known(ty) => Evidence::known(ty),
            Term::Var(id) => self.evidence[self.root(id)],
        }
    }

    pub fn resolve(&self, term: Term) -> Option<Ty> {
        self.evidence(term).ty()
    }

    pub fn conflicted(&self, term: Term) -> bool {
        self.evidence(term).0.count_ones() > 1
    }

    pub fn equal(&mut self, lhs: Term, rhs: Term) {
        match (lhs, rhs) {
            (Term::Known(_), Term::Known(_)) => {}
            (Term::Var(id), Term::Known(ty)) | (Term::Known(ty), Term::Var(id)) => {
                let root = self.compress(id);
                self.evidence[root].0 |= Evidence::known(ty).0;
            }
            (Term::Var(a), Term::Var(b)) => {
                let (mut a, mut b) = (self.compress(a), self.compress(b));
                if a == b {
                    return;
                }
                if self.size[a] < self.size[b] {
                    std::mem::swap(&mut a, &mut b);
                }
                self.parent[b] = a;
                self.size[a] += self.size[b];
                self.evidence[a].0 |= self.evidence[b].0;
            }
        }
    }

    pub fn import(&mut self, provider: Term) -> Term {
        let consumer = self.fresh();
        self.imports.push((provider, consumer));
        consumer
    }

    /// Diagnose the recorded local constraints once, with final imports, not
    /// provisional worklist values. Poisoned/unresolved imports add no evidence.
    pub fn replay(&self) -> Self {
        let n = self.parent.len();
        let mut replay = Self {
            parent: (0..n).collect(),
            size: vec![1; n],
            evidence: vec![Evidence::default(); n],
            imports: Vec::new(),
        };
        for &(provider, consumer) in &self.imports {
            if let Some(ty) = self.resolve(provider) {
                replay.equal(consumer, ty.into());
            }
        }
        replay
    }

    /// All equalities are collected before this fixed point. Each class gains
    /// at most three bits, so even long recursive import graphs take linear work.
    pub fn solve(&mut self) {
        for id in 0..self.parent.len() {
            self.compress(id);
        }
        let mut outgoing = vec![None; self.parent.len()];
        let mut edges = Vec::with_capacity(
            self.imports
                .iter()
                .filter(|(provider, _)| matches!(provider, Term::Var(_)))
                .count(),
        );
        // One-based links keep None compact. Prepending in reverse preserves
        // each provider's original consumer order.
        for &(provider, consumer) in self.imports.iter().rev() {
            let Term::Var(consumer) = consumer else {
                unreachable!()
            };
            let consumer = self.root(consumer);
            match provider {
                Term::Known(ty) => self.evidence[consumer].0 |= Evidence::known(ty).0,
                Term::Var(provider) => {
                    let provider = self.root(provider);
                    edges.push((consumer, outgoing[provider]));
                    outgoing[provider] = NonZeroUsize::new(edges.len());
                }
            }
        }
        let mut queue: VecDeque<_> = (0..self.parent.len())
            .filter(|&id| self.parent[id] == id && self.evidence[id].0 != 0)
            .collect();
        while let Some(provider) = queue.pop_front() {
            let mut edge = outgoing[provider];
            while let Some(index) = edge {
                let (consumer, next) = edges[index.get() - 1];
                edge = next;
                let before = self.evidence[consumer];
                self.evidence[consumer].0 |= self.evidence[provider].0;
                if before != self.evidence[consumer] {
                    queue.push_back(consumer);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn imports_do_not_export_consumer_expectations() {
        let mut ctx = Inference::default();
        let provider = ctx.fresh();
        let call = ctx.import(provider);
        ctx.equal(call, Ty::Int.into());
        ctx.solve();
        assert_eq!(ctx.resolve(provider), None);
        assert_eq!(ctx.resolve(call), Some(Ty::Int));
    }

    #[test]
    fn conflicts_propagate_in_either_import_order() {
        for reverse in [false, true] {
            let mut ctx = Inference::default();
            let result = ctx.fresh();
            let types = if reverse {
                [Ty::Bool, Ty::Int]
            } else {
                [Ty::Int, Ty::Bool]
            };
            for ty in types {
                let call = ctx.import(ty.into());
                ctx.equal(result, call);
            }
            let downstream = ctx.import(result);
            ctx.solve();
            assert!(ctx.conflicted(result));
            assert!(ctx.conflicted(downstream));
            assert_eq!(ctx.resolve(result), None);
        }
    }

    #[test]
    fn replay_resets_equalities_and_only_imports_singletons() {
        let mut ctx = Inference::default();
        let result = ctx.fresh();
        let call = ctx.import(Ty::Int.into());
        ctx.equal(result, call);
        let unknown = ctx.fresh();
        let unknown_call = ctx.import(unknown);
        let conflict = ctx.fresh();
        ctx.equal(conflict, Ty::Bool.into());
        ctx.equal(conflict, Ty::Unit.into());
        let conflict_call = ctx.import(conflict);
        ctx.solve();
        let mut replay = ctx.replay();
        assert_eq!(replay.parent, (0..ctx.parent.len()).collect::<Vec<_>>());
        assert_eq!(replay.resolve(result), None);
        assert_eq!(replay.resolve(call), Some(Ty::Int));
        assert_eq!(replay.resolve(unknown_call), None);
        assert_eq!(replay.resolve(conflict_call), None);
        assert!(!replay.conflicted(conflict_call));
        replay.equal(result, call);
        assert_eq!(replay.resolve(result), Some(Ty::Int));
    }

    proptest::proptest! {
        #[test]
        fn worklist_matches_full_scan(
            operations in proptest::collection::vec((0u8..4, 0usize..64, 0usize..64), 0..128),
            reverse in proptest::bool::ANY,
        ) {
            let mut ctx = Inference::default();
            for _ in 0..8 {
                ctx.fresh();
            }
            for (kind, a, b) in operations {
                let a = Term::Var(a % ctx.parent.len());
                let b = Term::Var(b % ctx.parent.len());
                match kind {
                    0 => ctx.equal(a, b),
                    1 => { ctx.import(a); }
                    _ => {
                        let Term::Var(id) = b else { unreachable!() };
                        let ty = [Ty::Int, Ty::Bool, Ty::Unit][id % 3];
                        if kind == 2 {
                            ctx.equal(a, ty.into());
                        } else {
                            let call = ctx.import(ty.into());
                            ctx.equal(a, call);
                        }
                    }
                }
            }
            // Deliberately no adjacency structure or worklist in the reference.
            // Compare every evidence bit: resolve() conflates unknown/conflict.
            let mut expected = ctx.evidence.clone();
            loop {
                let mut changed = false;
                for &(provider, consumer) in &ctx.imports {
                    let evidence = match provider {
                        Term::Known(ty) => Evidence::known(ty),
                        Term::Var(id) => expected[ctx.root(id)],
                    };
                    let Term::Var(id) = consumer else { unreachable!() };
                    let root = ctx.root(id);
                    let before = expected[root];
                    expected[root].0 |= evidence.0;
                    changed |= before != expected[root];
                }
                if !changed { break; }
            }
            if reverse { ctx.imports.reverse(); }
            ctx.solve();
            for id in 0..ctx.parent.len() {
                proptest::prop_assert_eq!(ctx.evidence(Term::Var(id)), expected[ctx.root(id)]);
            }
        }
    }
}
