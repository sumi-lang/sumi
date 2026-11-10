//! Type checking of one file: a class per node, joined where a value passes between nodes
//! unchanged, and every read checked in node order, so a disagreement is blamed on the first read
//! that raised it, and a class the conflict left undetermined satisfies every later read silently.
//! A body is checked as it is built, so lowering reads the type of what it has built: after the
//! callees whose inferred results it reads, and again with its group where those infer theirs
//! from one another.

use std::collections::VecDeque;

use sumi_graph::{
    Arms, BinaryOp, Case, CmpOp, DeclId, FieldName, FunctionId, GraphBuilder, May, NodeId, Op,
    Operand, RegionId, Ty, TyKind, Unions,
};
use sumi_text::TextRange;

use crate::codes;
use crate::flows::{Values, selection};
use crate::lower::{Declarations, HeaderResult, Lowered, Order, Params, RESULT, Source};
use crate::spans::SpansBuilder;

/// What the analysis settled about every node: its type and the values that may reach it.
pub(crate) struct Typing {
    types: Box<[Option<Ty>]>,
    values: Values,
}

impl Typing {
    pub fn new(types: Box<[Option<Ty>]>, values: Values) -> Self {
        Self { types, values }
    }

    /// None for a node that is no value, whose class conflicted, or that only a hole decided.
    pub fn resolve(&self, node: NodeId) -> Option<Ty> {
        self.types[node.index()]
    }

    pub fn may(&self, node: NodeId) -> &May {
        self.values.may(node)
    }

    pub fn values(&self) -> &Values {
        &self.values
    }
}

/// What lowering reads of the type of a node it has built.
pub(crate) enum Read {
    Ty(Ty),
    /// Left undetermined by what is reported elsewhere, or by a result yet to settle.
    Unknown,
    /// Claimed by nothing: the node yields no value.
    Unclaimed,
}

/// The checked types by node and, by function, its result type and whether a read in its body
/// failed.
pub(crate) struct Checked {
    pub types: Box<[Option<Ty>]>,
    /// Resolved only for a function with parameter types.
    pub results: Vec<Option<Ty>>,
    pub failed: Vec<bool>,
}

/// The classes of every node checked so far and what each function's result delivers; a
/// [`Checker`] reads and extends it beside the graph under construction.
#[derive(Default)]
pub(crate) struct Types {
    parent: Vec<u32>,
    /// By class root.
    sets: Vec<Set>,
    /// By function item, once a walk of it settled its result.
    exports: Vec<Option<Export>>,
    /// By function.
    results: Vec<Option<Ty>>,
    failed: Vec<bool>,
    /// The group of the function being walked.
    current: u32,
    /// The result of the body being walked, once it is built.
    result: Option<NodeId>,
    /// The first node of the body being built that no walk has reached.
    next: usize,
    /// Whether every read of the walk beside the body being built held.
    held: bool,
    /// Whether the walk beside the body being built reports and settles it, not its group.
    is_final: bool,
    /// Whether the body being built read a result its group has yet to settle.
    is_pending: bool,
}

impl Types {
    /// `items` is the count of function items.
    pub fn new(items: usize) -> Self {
        Self {
            exports: vec![None; items],
            ..Self::default()
        }
    }

    /// Whether the walk beside the body being built has reached `node`, which then must not change.
    pub fn has_walked(&self, node: NodeId) -> bool {
        node.index() < self.next
    }

    pub fn is_pending(&self) -> bool {
        self.is_pending
    }

    fn root(&mut self, node: NodeId) -> usize {
        let mut id = node.index();
        while self.parent[id] as usize != id {
            let parent = self.parent[id] as usize;
            self.parent[id] = self.parent[parent];
            id = parent;
        }
        id
    }

    /// `functions` is the count of them, and `source` the one every body was checked against.
    pub fn finish(mut self, source: &Source<'_>, functions: usize) -> Checked {
        let types = (0..self.parent.len())
            .map(|node| {
                let root = self.root(NodeId::new(node));
                self.sets[root].ty(&mut source.unions.borrow_mut(), source.params)
            })
            .collect();
        self.results.resize(functions, None);
        self.failed.resize(functions, false);
        Checked {
            types,
            results: self.results,
            failed: self.failed,
        }
    }
}

/// Most walks of a recursive group's member while the group settles: a result moves only when a
/// type reaches it, out of the few a body names, so a group still moving past this is reported as is.
const WALKS: usize = 16;

/// The bit of a rank crossing a call: a claim the class holds on a callee's say-so.
const IMPORTED: u32 = 1 << 31;
/// The rank of a type a read demanded and the class accepted: imported, since the class holds it
/// on the read's say-so, and with no origin, since nothing reports it.
const DEMANDED: u32 = u32::MAX;

/// A claim that a class has a type; the lowest rank is the earliest claim in the walk, every
/// local claim ranking before every imported one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Member {
    ty: Ty,
    rank: u32,
    origin: Option<TextRange>,
}

/// The types a class holds, each with its earliest claim. A class a hole decided is unknown: with
/// no claim beside it, it resolves to no type and no read of it disagrees.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Set {
    is_unknown: bool,
    /// Two inline, since a class rarely holds more; the rest spill.
    inline: [Option<Member>; 2],
    more: Vec<Member>,
}

impl Set {
    fn members(&self) -> impl Iterator<Item = Member> + '_ {
        self.inline.iter().flatten().chain(&self.more).copied()
    }

    /// Keeps `member` if its type is new or it outranks the claim held for the type.
    fn offer(&mut self, member: Member) {
        for slot in &mut self.inline {
            match slot {
                Some(held) if held.ty == member.ty => {
                    if member.rank < held.rank {
                        *held = member;
                    }
                    return;
                }
                Some(_) => {}
                None => {
                    *slot = Some(member);
                    return;
                }
            }
        }
        match self.more.iter_mut().find(|held| held.ty == member.ty) {
            Some(held) => {
                if member.rank < held.rank {
                    *held = member;
                }
            }
            None => self.more.push(member),
        }
    }

    fn absorb(&mut self, other: Set) {
        self.is_unknown |= other.is_unknown;
        for member in other.members() {
            self.offer(member);
        }
    }

    /// The types the class resolves among: a claim outranks the unknown, which outranks a
    /// demanded type, so a read never widens what it read and a holed class answers no read.
    fn types(&self) -> impl Iterator<Item = Member> + '_ {
        let demanded_only =
            !self.is_unknown && self.members().all(|member| member.rank == DEMANDED);
        self.members()
            .filter(move |member| demanded_only || member.rank != DEMANDED)
    }

    /// The type claimed: the one claim, or the union of claims that are all of types a union
    /// holds, which `unions` interns. None for a conflict, or a class only a hole or reads decided.
    fn ty(&self, unions: &mut Unions, params: Params) -> Option<Ty> {
        let mut types = self.types();
        let first = types.next()?;
        if types.next().is_none() {
            return Some(first.ty);
        }
        if !self.types().all(|member| params.joins(member.ty)) {
            return None;
        }
        let mut decls: Vec<DeclId> = Vec::new();
        for member in self.types() {
            match member.ty.kind() {
                TyKind::Decl(decl) => decls.push(decl),
                TyKind::Union(id) => decls.extend_from_slice(unions.get(id)),
                TyKind::Int | TyKind::Bool | TyKind::Unit => unreachable!("declared types only"),
            }
        }
        let union = unions.intern(decls.iter().copied());
        Some(union.map_or_else(|| Ty::decl(decls[0]), Ty::union))
    }

    /// Never for claims of types a union holds alone, which are a union.
    fn is_conflict(&self, params: Params) -> bool {
        self.types().nth(1).is_some() && !self.types().all(|member| params.joins(member.ty))
    }

    /// A conflict one call delivered whole: it is reported at the callee.
    fn is_inherited(&self, params: Params) -> bool {
        self.is_conflict(params)
            && self.types().all(|member| member.rank & IMPORTED != 0)
            && self
                .types()
                .map(|member| member.rank)
                .all(|rank| rank == self.types().next().map_or(rank, |first| first.rank))
    }

    /// Every claim the class resolves among, earliest first.
    fn claims(&self) -> Vec<(Ty, Option<TextRange>)> {
        let mut members: Vec<Member> = self.types().collect();
        members.sort_by_key(|member| member.rank);
        members
            .into_iter()
            .map(|member| (member.ty, member.origin))
            .collect()
    }
}

/// What a function's result delivers to its calls.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Export {
    is_unknown: bool,
    /// Sorted, so equal sets compare equal.
    types: Vec<Ty>,
}

impl Export {
    fn is_conflict(&self, params: Params) -> bool {
        self.types.len() > 1 && !self.types.iter().all(|&ty| params.joins(ty))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Expected {
    Ty(Ty),
    /// Each learns the other's type.
    Peer(NodeId),
}

/// Where a demanded type was declared.
#[derive(Clone, Copy)]
enum Declared {
    Written(TextRange),
    /// A result left unwritten, which declares `unit` at the parameter list.
    Omitted(TextRange),
}

/// One reading of the graph under construction: every borrow a walk needs, made anew for each.
pub(crate) struct Checker<'a, 's> {
    pub types: &'a mut Types,
    pub source: &'a mut Source<'s>,
    pub graph: &'a GraphBuilder,
    pub spans: &'a SpansBuilder,
    pub lowered: &'a Lowered,
    pub declared: &'a Declarations<'s>,
    pub order: &'a Order,
}

impl Checker<'_, '_> {
    fn typed(&self, node: NodeId) -> bool {
        self.lowered.typed[node.index()]
    }

    fn set(&mut self, node: NodeId) -> &Set {
        let root = self.types.root(node);
        &self.types.sets[root]
    }

    fn claim(&mut self, node: NodeId, member: Member) {
        let root = self.types.root(node);
        self.types.sets[root].offer(member);
    }

    fn unknown(&mut self, node: NodeId) {
        let root = self.types.root(node);
        self.types.sets[root].is_unknown = true;
    }

    fn fact(&mut self, node: NodeId, ty: Ty, origin: TextRange) {
        self.claim(
            node,
            Member {
                ty,
                rank: node.index() as u32,
                origin: Some(origin),
            },
        );
    }

    fn alias(&mut self, a: NodeId, b: NodeId) {
        let (a, b) = (self.types.root(a), self.types.root(b));
        if a == b {
            return;
        }
        self.types.parent[b] = a as u32;
        let absorbed = std::mem::take(&mut self.types.sets[b]);
        self.types.sets[a].absorb(absorbed);
    }

    /// The type of a node of the body being built, walked as far as the last node built.
    pub fn read(&mut self, owner: FunctionId, node: NodeId) -> Read {
        self.advance(owner);
        let params = self.source.params;
        let set = self.set(node);
        if set.is_unknown || set.is_conflict(params) {
            return Read::Unknown;
        }
        self.resolve(node).map_or(Read::Unclaimed, Read::Ty)
    }

    fn resolve(&mut self, node: NodeId) -> Option<Ty> {
        let root = self.types.root(node);
        self.types.sets[root].ty(&mut self.source.unions.borrow_mut(), self.source.params)
    }

    fn fits(&self, actual: Ty, expected: Ty) -> bool {
        self.source.unions.borrow().fits(actual, expected)
    }

    /// The group of `function`'s item among those that infer their results from one another.
    fn group(&self, function: FunctionId) -> u32 {
        self.order
            .group(self.declared.headers[function.index()].generic)
    }

    /// The function `node` calls, where that returns a product.
    fn product(&self, node: NodeId) -> Option<FunctionId> {
        let Op::Call(callee) = self.graph.node(node).op else {
            return None;
        };
        self.declared.headers[callee.index()]
            .product
            .map(|_| callee)
    }

    /// The position of the field `name` in `decl`, with its type when that resolved.
    fn field_of(&mut self, decl: DeclId, name: FieldName) -> Option<(usize, Option<Ty>)> {
        let fields = self.source.fields(decl);
        let index = fields.iter().position(|&(field, _)| field == name)?;
        Some((index, fields[index].1))
    }

    /// The callee's declared result, or what its item's walk inferred, at the callee's type
    /// arguments. A conflict inferred outside the caller's group is the unknown, reported there.
    fn import(&mut self, call: NodeId, callee: FunctionId) {
        let header = self.declared.headers[callee.index()];
        let origin = Some(self.spans.origin(call));
        let rank = call.index() as u32 | IMPORTED;
        if let Some((ty, _)) = header.result.declared() {
            self.claim(call, Member { ty, rank, origin });
            return;
        }
        let item = header.generic;
        let is_grouped = self.order.group(item) == self.types.current;
        let Some(export) = self.types.exports[item.index()].clone() else {
            assert!(is_grouped, "an item outside the group is settled");
            // Beside the body, lowering must not take what the call has so far for its type.
            if self.types.result.is_none() {
                self.types.is_pending = true;
                self.unknown(call);
            }
            return;
        };
        if !is_grouped && export.is_conflict(self.source.params) {
            self.unknown(call);
            return;
        }
        if export.is_unknown {
            self.unknown(call);
        }
        let params = &self.declared.type_args[item.index()];
        let args = &self.declared.type_args[callee.index()];
        let at = self.spans.origin(call);
        for ty in export.types {
            match self.source.substitute(ty, params, args, at) {
                Some(ty) => self.claim(call, Member { ty, rank, origin }),
                None => self.unknown(call),
            }
        }
    }

    /// The read claims its field's type where its base resolves to one declared type with it. A
    /// read reported elsewhere is unknown, so nothing after it is blamed: by its own demand, by
    /// the base's conflict where that arose, or at the field's damaged type.
    fn field(&mut self, read: NodeId, base: NodeId, name: FieldName) {
        let params = self.source.params;
        let set = self.set(base);
        let (is_unknown, is_conflict) = (set.is_unknown, set.is_conflict(params));
        let resolved = self.resolve(base);
        let field = resolved
            .and_then(Ty::as_decl)
            .and_then(|decl| self.field_of(decl, name))
            .map(|(_, ty)| ty);
        if let Some(Some(ty)) = field {
            self.fact(read, ty, self.spans.origin(read));
        }
        if is_unknown || is_conflict || (resolved.is_some() && !matches!(field, Some(Some(_)))) {
            self.unknown(read);
        }
    }

    /// Delivers what `from` resolves among to `to`, one way.
    fn deliver(&mut self, from: NodeId, to: NodeId, at: TextRange) {
        let delivered = self.delivered(from, at);
        let root = self.types.root(to);
        self.types.sets[root].absorb(delivered);
    }

    /// What `from` resolves among; a type a read demanded of it is its own claim, read at `at`.
    fn delivered(&mut self, from: NodeId, at: TextRange) -> Set {
        let source = self.set(from).clone();
        let mut delivered = Set {
            is_unknown: source.is_unknown,
            ..Set::default()
        };
        for member in source.types() {
            let member = if member.rank == DEMANDED {
                Member {
                    ty: member.ty,
                    rank: from.index() as u32,
                    origin: Some(at),
                }
            } else {
                member
            };
            delivered.offer(member);
        }
        delivered
    }

    /// The function's result as its exits give it: joined like an inferred result's outcomes
    /// where each exit returns it inside a product.
    fn result(&mut self, owner: FunctionId, result: NodeId) -> Set {
        let header = self.declared.headers[owner.index()];
        if header.product.is_none() {
            return self.set(result).clone();
        }
        let mut joined = Set::default();
        // A declared result is the function's whatever its exits, each of which is held to it.
        if let Some((ty, annotation)) = header.result.declared() {
            joined.offer(Member {
                ty,
                rank: result.index() as u32,
                origin: Some(self.source.range(annotation)),
            });
            return joined;
        }
        for index in 0..self.lowered.exits[owner.index()].len() {
            let (exit, at) = self.lowered.exits[owner.index()][index];
            if self.typed(exit) {
                let delivered = self.delivered(exit, at);
                joined.absorb(delivered);
            } else {
                joined.is_unknown = true;
            }
        }
        joined
    }

    /// Reports and settles the built bodies of `group`, whose members infer their results from one
    /// another: each is walked, muted, until none changes, a change re-walking its callers there.
    pub fn settle(&mut self, group: usize) {
        let order = self.order;
        let members = order.members(group);
        let mut queued = vec![false; self.types.exports.len()];
        let mut queue: VecDeque<u32> = members.iter().copied().collect();
        for &member in members {
            queued[member as usize] = true;
        }
        let mut budget = members.len() * WALKS;
        while let Some(member) = queue.pop_front() {
            queued[member as usize] = false;
            let before = self.types.exports[member as usize].take();
            let after = self.walk(FunctionId::new(member as usize), false);
            budget = budget.saturating_sub(1);
            if before.as_ref() == Some(&after) || budget == 0 {
                continue;
            }
            for &caller in order.callers(member as usize) {
                if !queued[caller as usize] {
                    queued[caller as usize] = true;
                    queue.push_back(caller);
                }
            }
        }
        for &member in members {
            self.walk(FunctionId::new(member as usize), true);
        }
    }

    /// Runs `walk` with its reports kept only when `is_final`.
    fn reporting<T>(&mut self, is_final: bool, walk: impl FnOnce(&mut Self) -> T) -> T {
        let was_muted = self.source.is_muted;
        self.source.is_muted |= !is_final;
        let result = walk(self);
        self.source.is_muted = was_muted;
        result
    }

    /// One pass over a built body, reporting and settling the function when `is_final`. Returns
    /// what the result delivers to calls.
    fn walk(&mut self, owner: FunctionId, is_final: bool) -> Export {
        let run = self.graph.run(owner);
        self.grow();
        for node in run.nodes() {
            self.types.parent[node.index()] = node.index() as u32;
            self.types.sets[node.index()] = Set::default();
        }
        self.types.current = self.group(owner);
        self.types.result = Some(run.result());
        self.types.held = true;
        self.reporting(is_final, |checker| {
            for node in run.nodes() {
                checker.visit(owner, node);
            }
            checker.finish(owner, run.result(), is_final)
        })
    }

    /// A class of its own for every node built that has none.
    fn grow(&mut self) {
        for node in self.types.parent.len()..self.graph.nodes().len() {
            self.types.parent.push(node as u32);
            self.types.sets.push(Set::default());
        }
    }

    /// Begins the walk beside the body `owner`'s run is about to hold, which reports and settles
    /// the function when `is_final`.
    pub fn open(&mut self, owner: FunctionId, is_final: bool) {
        self.types.current = self.group(owner);
        self.types.result = None;
        self.types.next = self.graph.nodes().len();
        self.types.held = true;
        self.types.is_final = is_final;
        self.types.is_pending = false;
    }

    /// Walks the nodes built since the last call. A node is walked once nothing built later
    /// changes what the walk reads of it: here, where a later node or the body's end asks.
    fn advance(&mut self, owner: FunctionId) {
        self.grow();
        let end = self.graph.nodes().len();
        let next = std::mem::replace(&mut self.types.next, end);
        self.reporting(self.types.is_final, |checker| {
            for node in next..end {
                checker.visit(owner, NodeId::new(node));
            }
        });
    }

    /// Ends a final walk [`open`](Self::open) began, once the run is closed with `result`.
    pub fn close(&mut self, owner: FunctionId, result: NodeId) {
        self.types.result = Some(result);
        self.advance(owner);
        self.reporting(true, |checker| checker.finish(owner, result, true));
    }

    fn visit(&mut self, owner: FunctionId, node: NodeId) {
        if self.typed(node) {
            self.facts(owner, node);
        }
        let held = self.demands(owner, node);
        self.types.held &= held;
    }

    /// What a walk leaves of the function: what its result delivers and, when `is_final`,
    /// whether a read failed and the result's type.
    fn finish(&mut self, owner: FunctionId, result: NodeId, is_final: bool) -> Export {
        if !self.typed(result) {
            self.unknown(result);
        }
        let result = self.result(owner, result);
        if is_final {
            let index = owner.index();
            if self.types.failed.len() <= index {
                self.types.failed.resize(index + 1, false);
                self.types.results.resize(index + 1, None);
            }
            self.types.failed[index] = !self.types.held;
            self.signature(owner, &result);
        }
        let mut types: Vec<Ty> = result.types().map(|member| member.ty).collect();
        types.sort_unstable();
        let export = Export {
            is_unknown: result.is_unknown,
            types,
        };
        // An instance delivers what its item's own walk settled.
        if self.declared.headers[owner.index()].generic == owner {
            self.types.exports[owner.index()] = Some(export.clone());
        }
        export
    }

    /// A failed read, a hole, or the call this inherits from, already reports what a result that
    /// resolves to nothing lacks.
    fn signature(&mut self, owner: FunctionId, result: &Set) {
        let header = self.declared.headers[owner.index()];
        let params = self.source.params;
        let resolved = if matches!(header.result, HeaderResult::None) {
            None
        } else {
            result.ty(&mut self.source.unions.borrow_mut(), params)
        };
        if self.graph.param_types(owner).is_some() {
            self.types.results[owner.index()] = resolved;
        }
        if let (Some(product), Some(resolved)) = (header.product, resolved) {
            self.source.set_result(product, resolved);
        }
        if !matches!(header.result, HeaderResult::Inferred)
            || resolved.is_some()
            || !self.lowered.built[owner.index()]
            || self.types.failed[owner.index()]
            || result.is_inherited(params)
        {
            return;
        }
        if result.is_conflict(params) {
            self.source.conflict_at(
                self.source.range(header.item),
                codes::CANNOT_INFER,
                result.claims(),
                |types| format!("function result is both {types}; add a return type annotation"),
            );
        } else if !result.is_unknown {
            self.source.error(
                header.item,
                codes::CANNOT_INFER,
                "cannot infer function result; add a return type annotation",
                None,
            );
        }
    }

    /// What the node knows of its own type and the class it shares.
    fn facts(&mut self, owner: FunctionId, node: NodeId) {
        let graph = self.graph;
        let spans = self.spans;
        let inputs = graph.inputs(node);
        let origin = spans.origin(node);
        let value = |index: usize| graph.input_roles(node)[index].is_value();
        let annotation = || {
            spans
                .annotation(node)
                .expect("a node declared with a type has its annotation")
        };
        match &graph.node(node).op {
            Op::Int(_) => self.fact(node, Ty::INT, origin),
            Op::Bool(_) => self.fact(node, Ty::BOOL, origin),
            Op::Param { ty: Some(ty), .. } => {
                self.fact(node, *ty, spans.name(node).unwrap_or(origin));
            }
            Op::Param { ty: None, .. }
            | Op::Hole
            | Op::Unused
            | Op::Entry
            | Op::Arm(_)
            | Op::Observe { .. }
            | Op::After
            | Op::Return => {}
            Op::Refine { .. } | Op::Exactly(_) => self.alias(node, inputs[0]),
            Op::Narrow(ty) => self.fact(node, *ty, origin),
            // Arms that agree deliver their type when the switch's demand checks them.
            Op::Switch { arms } if selection(graph.cases(*arms)).total => {
                let mut valued = arms.iter().filter_map(|arm| match graph.result(arm) {
                    Operand::Value(result) => Some(result),
                    Operand::Completes(_) => None,
                });
                if let (true, Some(result), None) = (value(0), valued.next(), valued.next()) {
                    self.alias(node, result);
                }
            }
            // What falls through is unit, and so is every arm.
            Op::Switch { .. } => self.fact(node, Ty::UNIT, origin),
            Op::Unit | Op::Loop { .. } => self.fact(node, Ty::UNIT, origin),
            Op::Copy { declared: Some(ty) } => self.fact(node, *ty, annotation()),
            Op::Copy { declared: None } => self.alias(node, inputs[0]),
            Op::Assign | Op::Phi | Op::Carry => self.alias(node, graph.declaration(node)),
            Op::LoopIndex => self.fact(node, Ty::INT, spans.name(node).unwrap_or(origin)),
            Op::LoopValue => {
                let (header, _) = graph.carry(node);
                self.alias(node, header);
            }
            Op::Neg => self.fact(node, Ty::INT, origin),
            Op::Not => self.fact(node, Ty::BOOL, origin),
            Op::Binary(op) => self.fact(node, op.result(), origin),
            Op::And { .. } | Op::Or { .. } => {
                if value(0) {
                    self.fact(node, Ty::BOOL, origin);
                }
            }
            Op::Sequence => {
                if self.typed(inputs[1]) {
                    self.alias(node, inputs[1]);
                }
            }
            Op::Result { declared: Some(ty) } => self.fact(node, *ty, annotation()),
            // An inferred result joins its outcomes, each a peer of the others: a conflict among
            // them is the function's to report, not any one outcome's.
            Op::Result { declared: None } => {
                if let Some(fallthrough) = self.lowered.fallthroughs[owner.index()] {
                    self.deliver(fallthrough.value, node, fallthrough.at);
                } else if value(0) {
                    self.deliver(inputs[0], node, spans.reads(node)[0]);
                }
                for (&returned, &at) in inputs[1..].iter().zip(&spans.reads(node)[1..]) {
                    self.deliver(returned, node, at);
                }
            }
            Op::Make(decl) => self.fact(node, Ty::decl(*decl), origin),
            // A product's result is its function's, which a call imports.
            Op::Field(name) => match self.product(inputs[0]) {
                Some(callee) if *name == self.source.field_name(RESULT) => {
                    self.import(node, callee);
                }
                _ => self.field(node, inputs[0], *name),
            },
            Op::Call(callee) => match self.declared.headers[callee.index()].product {
                Some(product) => self.fact(node, Ty::decl(product), origin),
                None => self.import(node, *callee),
            },
        }
    }

    /// What the node reads must hold; false if a read failed.
    fn demands(&mut self, owner: FunctionId, node: NodeId) -> bool {
        let graph = self.graph;
        let spans = self.spans;
        let inputs = graph.inputs(node);
        let reads = spans.reads(node);
        let value = |index: usize| graph.input_roles(node)[index].is_value();
        let written = |at: TextRange| Some(Declared::Written(at));
        // What the run's result holds the body to: only there can a declaration be omitted.
        let is_omitted = matches!(
            self.declared.headers[owner.index()].result,
            HeaderResult::Omitted(_)
        );
        let held = |at: TextRange| {
            Some(if is_omitted {
                Declared::Omitted(at)
            } else {
                Declared::Written(at)
            })
        };
        let annotation = || {
            spans
                .annotation(node)
                .expect("a node declared with a type has its annotation")
        };
        let region = |id: RegionId| (spans.result_read(id), graph.result(id).node());
        let has_value = |id: RegionId| matches!(graph.result(id), Operand::Value(_));
        let mut ok = true;
        match &graph.node(node).op {
            Op::Neg if value(0) => {
                ok &= self.require(reads[0], inputs[0], Expected::Ty(Ty::INT), None);
            }
            Op::Not if value(0) => {
                ok &= self.require(reads[0], inputs[0], Expected::Ty(Ty::BOOL), None);
            }
            Op::Neg | Op::Not => {}
            Op::Binary(BinaryOp::Cmp(CmpOp::Eq | CmpOp::Ne)) => {
                let operand = inputs.iter().enumerate().find_map(|(index, &input)| {
                    (value(index) && self.typed(input)).then_some(input)
                });
                if let Some(operand) = operand {
                    for (index, (&at, &input)) in reads.iter().zip(inputs).enumerate() {
                        if value(index) {
                            ok &= self.require(at, input, Expected::Peer(operand), None);
                        }
                    }
                    ok &= self.comparable(spans.origin(node), operand);
                }
            }
            Op::Binary(_) => {
                for (index, (&at, &input)) in reads.iter().zip(inputs).enumerate() {
                    if value(index) {
                        ok &= self.require(at, input, Expected::Ty(Ty::INT), None);
                    }
                }
            }
            Op::And { rhs } | Op::Or { rhs } => {
                if value(0) {
                    ok &= self.require(reads[0], inputs[0], Expected::Ty(Ty::BOOL), None);
                }
                let (at, result) = region(*rhs);
                if has_value(*rhs) {
                    ok &= self.require(at, result, Expected::Ty(Ty::BOOL), None);
                }
            }
            Op::Switch { arms } => {
                let selection = selection(graph.cases(*arms));
                if value(0) && selection.boolean {
                    ok &= self.require(reads[0], inputs[0], Expected::Ty(Ty::BOOL), None);
                } else if value(0) && self.typed(inputs[0]) {
                    ok &= self.matched(reads[0], inputs[0]);
                    for arm in arms.iter() {
                        let context = graph.context(arm);
                        if let Case::Is(ty) = graph.case(context) {
                            ok &= self.member(spans.origin(context), inputs[0], ty);
                        }
                    }
                }
                let valued = || arms.iter().filter(|&arm| has_value(arm));
                if !value(0) {
                } else if !selection.total {
                    // What falls through is unit, so every arm is.
                    for arm in valued() {
                        let (at, result) = region(arm);
                        ok &= self.require(at, result, Expected::Ty(Ty::UNIT), None);
                    }
                } else if self.typed(node) && valued().count() > 1 {
                    ok &= self.agree(spans.origin(node), node, *arms, selection.boolean);
                }
            }
            Op::Loop { body } => {
                let (at, result) = region(*body);
                if value(0) && value(1) && has_value(*body) {
                    ok &= self.require(at, result, Expected::Ty(Ty::UNIT), None);
                }
            }
            Op::Copy { declared: Some(ty) } if value(0) => {
                let at = annotation();
                let exits = &self.lowered.exits[owner.index()];
                let is_result = exits.iter().any(|&(exit, _)| exit == node);
                let declared = if is_result || self.types.result == Some(node) {
                    held(at)
                } else {
                    written(at)
                };
                ok &= self.require(reads[0], inputs[0], Expected::Ty(*ty), declared);
            }
            Op::Copy { declared: Some(_) } => {}
            Op::Assign if value(0) => {
                let declaration = graph.declaration(node);
                ok &= self.require(
                    reads[0],
                    inputs[0],
                    Expected::Peer(declaration),
                    spans.name(declaration).and_then(written),
                );
            }
            Op::Assign => {}
            Op::Call(function) => {
                let types = graph
                    .param_types(*function)
                    .expect("a callee has parameter types");
                let params = &self.declared.parameters[function.index()];
                for (index, (((&at, &input), &ty), param)) in
                    reads.iter().zip(inputs).zip(types).zip(params).enumerate()
                {
                    if value(index) {
                        let declared = written(self.source.range(param.node));
                        ok &= self.require(at, input, Expected::Ty(ty), declared);
                    }
                }
            }
            Op::Make(decl) => {
                let names = self.source.decls[decl.index()].fields.clone();
                for (index, ((&at, &input), &(_, name))) in
                    reads.iter().zip(inputs).zip(names.iter()).enumerate()
                {
                    if value(index)
                        && let (_, Some(ty)) = self.source.fields(*decl)[index]
                    {
                        let declared = written(self.source.range(name));
                        ok &= self.require(at, input, Expected::Ty(ty), declared);
                    }
                }
            }
            Op::Field(name) => {
                if value(0) && self.typed(inputs[0]) {
                    ok &= self.has_field(spans.origin(node), inputs[0], *name);
                }
            }
            Op::Unused => {
                if value(0) && self.typed(inputs[0]) {
                    ok &= self.unused(reads[0], inputs[0]);
                }
            }
            Op::Return if value(0) => {
                ok &= self.require(reads[0], inputs[0], Expected::Peer(node), None);
            }
            Op::Return => {}
            Op::Result { declared: Some(ty) } => {
                let expected = Expected::Ty(*ty);
                let declared = held(annotation());
                if let Some(fallthrough) = self.lowered.fallthroughs[owner.index()] {
                    ok &= self.require(fallthrough.at, fallthrough.value, expected, declared);
                } else if value(0) {
                    ok &= self.require(reads[0], inputs[0], expected, declared);
                }
                for (&at, &input) in reads[1..].iter().zip(&inputs[1..]) {
                    ok &= self.require(at, input, expected, declared);
                }
            }
            Op::Int(_)
            | Op::Bool(_)
            | Op::Param { .. }
            | Op::Unit
            | Op::Hole
            | Op::Copy { declared: None }
            | Op::Result { declared: None }
            | Op::Phi
            | Op::LoopIndex
            | Op::Carry
            | Op::LoopValue
            | Op::Refine { .. }
            | Op::Exactly(_)
            | Op::Narrow(_)
            | Op::Entry
            | Op::Arm(_)
            | Op::Sequence
            | Op::Observe { .. }
            | Op::After => {}
        }
        ok
    }

    /// A read of `actual` as `expected`: a disagreement is reported and changes nothing, so a
    /// wrong read is blamed without unsettling what it read; otherwise the class accepts it.
    fn require(
        &mut self,
        at: TextRange,
        actual: NodeId,
        expected: Expected,
        declared: Option<Declared>,
    ) -> bool {
        if !self.typed(actual) || expected == Expected::Peer(actual) {
            return true;
        }
        let actual_ty = self.resolve(actual);
        let expected_ty = match expected {
            Expected::Ty(ty) => Some(ty),
            Expected::Peer(peer) => self.resolve(peer),
        };
        if let (Some(actual_ty), Some(expected_ty)) = (actual_ty, expected_ty)
            && !self.fits(actual_ty, expected_ty)
        {
            let related = declared.map(|declared| match declared {
                Declared::Written(at) => (at, "declared here"),
                Declared::Omitted(at) => (at, "returns unit, since no result type is written"),
            });
            self.source
                .type_mismatch(at, expected_ty, actual_ty, related);
            return false;
        }
        let demanded = |ty| Member {
            ty,
            rank: DEMANDED,
            origin: None,
        };
        // Peers typed on both sides fit and stay apart, since a value fits a wider type without
        // becoming it; one typed side types the other; two untyped ones are one class until
        // either is typed.
        match (expected, actual_ty, expected_ty) {
            (Expected::Ty(ty), _, _) => self.claim(actual, demanded(ty)),
            (Expected::Peer(_), Some(_), Some(_)) => {}
            (Expected::Peer(_), None, Some(ty)) => self.claim(actual, demanded(ty)),
            (Expected::Peer(peer), Some(ty), None) => self.claim(peer, demanded(ty)),
            (Expected::Peer(peer), None, None) => self.alias(actual, peer),
        }
        true
    }

    fn unused(&mut self, at: TextRange, actual: NodeId) -> bool {
        match self.resolve(actual) {
            Some(ty) if ty != Ty::UNIT => {
                let message = format!(
                    "unused value of type {}; use `_ =` to discard it",
                    self.source.show(ty)
                );
                self.source.report(at, codes::UNUSED_VALUE, message, []);
                false
            }
            _ => self.require(at, actual, Expected::Ty(Ty::UNIT), None),
        }
    }

    fn comparable(&mut self, at: TextRange, operand: NodeId) -> bool {
        let Some(ty) = self
            .resolve(operand)
            .filter(|ty| *ty == Ty::UNIT || ty.is_declared())
        else {
            return true;
        };
        let message = format!("{} values cannot be compared", self.source.show(ty));
        self.source.report(at, codes::TYPE_MISMATCH, message, []);
        false
    }

    fn matched(&mut self, at: TextRange, scrutinee: NodeId) -> bool {
        let params = self.source.params;
        let Some(ty) = self.resolve(scrutinee).filter(|&ty| !params.joins(ty)) else {
            return true;
        };
        let message = format!(
            "cannot match on {} values; `match` takes a value of a declared type",
            self.source.show(ty)
        );
        self.source.report(at, codes::TYPE_MISMATCH, message, []);
        false
    }

    fn member(&mut self, at: TextRange, scrutinee: NodeId, member: Ty) -> bool {
        let Some(ty) = self
            .resolve(scrutinee)
            .filter(|ty| ty.is_declared() && !self.fits(member, *ty))
        else {
            return true;
        };
        let message = format!(
            "`{}` is no member of `{}`",
            self.source.show(member),
            self.source.show(ty)
        );
        self.source.report(at, codes::TYPE_MISMATCH, message, []);
        false
    }

    fn has_field(&mut self, at: TextRange, base: NodeId, name: FieldName) -> bool {
        let Some(ty) = self.resolve(base) else {
            return true;
        };
        if let Some(decl) = ty.as_decl()
            && self.field_of(decl, name).is_some()
        {
            return true;
        }
        let declared = ty.as_decl().and_then(|decl| {
            let decl = &self.source.decls[decl.index()];
            decl.name_node
                .map(|node| (self.source.range(node), Box::from("declared here")))
        });
        let name = self.source.field_names[name.index()];
        let item = ty
            .as_decl()
            .map(|decl| self.source.decls[decl.index()].item);
        let is_method = item.is_some_and(|item| self.declared.methods.contains_key(&(item, name)));
        let message = if is_method {
            format!(
                "`{name}` is a method of `{}`: a call of it takes `()`",
                self.source.show(ty)
            )
        } else {
            format!("`{}` has no field `{name}`", self.source.show(ty))
        };
        self.source
            .report(at, codes::UNKNOWN_FIELD, message, declared);
        false
    }

    /// The valued arms deliver their types to the switch; a conflict among them is reported at
    /// the switch, labeled where each arm's value is read when the arms alone made it.
    fn agree(&mut self, at: TextRange, switch: NodeId, arms: Arms, is_boolean: bool) -> bool {
        let graph = self.graph;
        let valued: Vec<(RegionId, NodeId)> = arms
            .iter()
            .filter_map(|arm| match graph.result(arm) {
                Operand::Value(result) => Some((arm, result)),
                Operand::Completes(_) => None,
            })
            .collect();
        let resolved: Vec<(Ty, Option<TextRange>)> = valued
            .iter()
            .filter_map(|&(region, result)| {
                let ty = self.resolve(result)?;
                Some((ty, Some(self.spans.result_read(region))))
            })
            .collect();
        for &(region, result) in &valued {
            self.deliver(result, switch, self.spans.result_read(region));
        }
        let set = self.set(switch).clone();
        if !set.is_conflict(self.source.params) || set.is_inherited(self.source.params) {
            return true;
        }
        let what = if is_boolean {
            "if branches"
        } else {
            "match arms"
        };
        let message = |types: String| format!("{what} are {types}");
        let claims = set.claims();
        let mut distinct: Vec<Ty> = resolved.iter().map(|&(ty, _)| ty).collect();
        distinct.sort_unstable();
        distinct.dedup();
        // The arms alone made the conflict; another type has come in by aliasing otherwise.
        if resolved.len() == valued.len() && distinct.len() == claims.len() && distinct.len() > 1 {
            self.source
                .conflict_at(at, codes::TYPE_MISMATCH, resolved, message);
        } else {
            self.source
                .conflict_at(at, codes::TYPE_MISMATCH, claims, message);
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(offset: u32) -> TextRange {
        use sumi_text::TextSize;
        TextRange::new(TextSize::new(offset), TextSize::new(offset + 1))
    }

    fn member(ty: Ty, rank: u32) -> Member {
        Member {
            ty,
            rank,
            origin: Some(at(rank & !IMPORTED)),
        }
    }

    #[test]
    fn a_set_keeps_the_earliest_claim_of_each_type() {
        let mut set = Set::default();
        set.offer(member(Ty::INT, 5));
        set.offer(member(Ty::INT, 2));
        set.offer(member(Ty::INT, 9));
        set.offer(member(Ty::BOOL, 7));
        set.offer(member(Ty::UNIT, 8));
        set.offer(member(Ty::UNIT, 1));
        assert_eq!(
            set.claims(),
            [
                (Ty::UNIT, Some(at(1))),
                (Ty::INT, Some(at(2))),
                (Ty::BOOL, Some(at(7)))
            ]
        );
        assert!(set.is_conflict(Params::default()));
        assert_eq!(set.ty(&mut Unions::new(), Params::default()), None);
    }

    #[test]
    fn declared_claims_resolve_to_their_union_and_scalars_conflict() {
        let (a, b) = (DeclId::new(0), DeclId::new(1));
        let mut unions = Unions::new();
        let mut set = Set::default();
        set.offer(member(Ty::decl(a), 1));
        assert_eq!(set.ty(&mut unions, Params::default()), Some(Ty::decl(a)));
        set.offer(member(Ty::decl(b), 2 | IMPORTED));
        assert!(!set.is_conflict(Params::default()));
        let union = set
            .ty(&mut unions, Params::default())
            .expect("two declared types are a union");
        assert_eq!(unions.members(union), [a, b]);
        set.offer(Member {
            ty: Ty::INT,
            rank: DEMANDED,
            origin: None,
        });
        assert_eq!(set.ty(&mut unions, Params::default()), Some(union));
        assert_eq!(set.claims().len(), 2);
        set.offer(member(Ty::INT, 3 | IMPORTED));
        assert!(set.is_conflict(Params::default()));
        assert_eq!(set.ty(&mut unions, Params::default()), None);
    }

    #[test]
    fn a_claim_outranks_the_unknown_which_outranks_a_demand() {
        let mut set = Set::default();
        set.offer(member(Ty::INT, 4 | IMPORTED));
        set.offer(member(Ty::BOOL, 4 | IMPORTED));
        assert!(set.is_conflict(Params::default()));
        let mut other = Set {
            is_unknown: true,
            ..Set::default()
        };
        assert_eq!(other.ty(&mut Unions::new(), Params::default()), None);
        other.offer(Member {
            ty: Ty::BOOL,
            rank: DEMANDED,
            origin: None,
        });
        assert_eq!(other.ty(&mut Unions::new(), Params::default()), None);
        other.offer(member(Ty::UNIT, 1));
        assert_eq!(
            other.ty(&mut Unions::new(), Params::default()),
            Some(Ty::UNIT)
        );
        set.absorb(other);
        assert!(set.is_unknown && set.is_conflict(Params::default()));
        assert_eq!(set.claims().len(), 3);
    }

    #[test]
    fn a_set_spills_past_two_types_without_losing_any() {
        let mut set = Set::default();
        for index in 0..5u32 {
            set.offer(member(Ty::decl(DeclId::new(index as usize)), 10 - index));
        }
        set.offer(member(Ty::decl(DeclId::new(4)), 1));
        let claims = set.claims();
        assert_eq!(claims.len(), 5);
        assert_eq!(claims[0], (Ty::decl(DeclId::new(4)), Some(at(1))));
    }
}
