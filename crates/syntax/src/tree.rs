//! The syntax tree: flat, postorder, token-anchored.
//!
//! A [`SyntaxTree`] stores structure only. Each node is a kind, its grammatical
//! field when recovery would otherwise leave that ambiguous, a subtree
//! extent, and a half-open range of raw token indices; text, spans, and
//! trivia stay in the token buffers, so the tree holds no second copy of the
//! source. Nodes lie in postorder — the order they complete in, children
//! before parents — so node `index`'s subtree occupies
//! `index + 1 - extent..=index` and children are found by walking extents
//! backward from `index - 1`, last child first. The root is the last node,
//! and because a node completes only as the cursor passes its last token,
//! `end_token` is non-decreasing across the array: the node covering a
//! token is found by binary search on it.
//!
//! A node's range runs from its first significant token to just past its
//! last one, and every node but the root covers at least one token, so a
//! child's range lies inside its parent's and siblings never overlap. Trivia
//! between two children belongs to the parent, and trivia at the edges of
//! the file belongs to the root, which always covers every token: comment
//! attachment is a consumer's policy, not a tree property. Each node also
//! records whether the parser recovered inside it, so a consumer can skip
//! a construct it cannot trust without walking it.
//!
//! # Building
//!
//! Trees come only from [`Parse::build`], which lends the root as a
//! [`Marker`]: an open node, and the parser's cursor into the input.
//! Starting a child reborrows the parent marker for as long as the child is
//! open, so the borrow checker holds the stack of open nodes. A parent
//! cannot take a token, start a sibling, or complete while a child is open;
//! the root, only ever lent, cannot complete at all; and completing a
//! marker is the one way to close its node. A [`CompletedMarker`] is plain
//! data — holding one borrows nothing — and is wrapped after the fact from
//! the marker that contained it. What types cannot express stays a run-time
//! check, raised where the parser went wrong: a node is preceded only from
//! the node that contained it, every node covers at least one token, no
//! node wraps one of its own kind over exactly its tokens (a debug-build
//! check; the parser never does), a marker dropped uncompleted panics where it drops, and `build` rejects a
//! token past the input horizon or tokens left over.
//!
//! The build records nodes as they complete, and completion order is the
//! stored order. That is what lets a parser choose a node's kind after its
//! children exist, and wrap a node it has already completed: a wrapper's
//! subtree is simply everything completed since the wrapped node began —
//! how a Pratt parser wraps an already-parsed left operand into a binary
//! expression.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_text::{TextRange, TextSize};

use crate::generated::{
    BRACKET_PAIRS, NodeKind, SyntaxKind, encloses_statements, opener, pair_index,
};
use crate::index::{NodeIdx, SigIdx};
use crate::input::{ParserInput, Slot};
use crate::parser::{
    ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind, ParseViolation,
    ParseViolationKind, RawGap, RawTokenRange,
};

/// The byte offset where raw token `raw` begins, or the end of the source
/// for the boundary one past the last token: how the raw token indices in
/// trees and parse evidence project into the file. `lexed` must be the file
/// the indices came from.
pub fn raw_boundary(lexed: &LexedFile, raw: RawIdx) -> TextSize {
    if raw == lexed.end() {
        lexed.source_len()
    } else {
        lexed.range(raw).start()
    }
}

/// One node: its kind, whether the parser recovered inside it, its subtree
/// extent (self included), and the half-open range of raw token indices it
/// covers.
#[derive(Clone, Copy, Debug)]
struct Node {
    kind: NodeKind,
    has_error: bool,
    /// The typed field this node fills in its immediate parent, plus one;
    /// zero means that kind and order settle the field without a hint.
    field: u8,
    extent: u32,
    first_token: RawIdx,
    end_token: RawIdx,
}

const _: () = assert!(size_of::<Node>() == 16, "nodes stay sixteen bytes");

/// A parsed file: its nodes in postorder.
#[derive(Clone, Debug)]
pub struct SyntaxTree {
    nodes: Box<[Node]>,
    /// Whether any accessor may need a parser-retained field role.
    may_need_field_hints: bool,
}

impl SyntaxTree {
    /// The number of nodes: at least one, the root.
    #[expect(clippy::len_without_is_empty, reason = "a tree always has its root")]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// The root, which completes last: the last node.
    pub fn root(&self) -> NodeIdx {
        node_idx(self.nodes.len() - 1)
    }

    /// Every node's index, in postorder.
    pub fn nodes(&self) -> impl DoubleEndedIterator<Item = NodeIdx> + ExactSizeIterator {
        NodeIdx::new(0).until(node_idx(self.nodes.len()))
    }

    pub fn kind(&self, index: NodeIdx) -> NodeKind {
        self.nodes[index.to_usize()].kind
    }

    /// Whether node `index` contains a syntax error: it is an `Error` node,
    /// or the parser recovered — skipped tokens, or found syntax missing —
    /// while it was open, anywhere in its subtree. Layout violations are
    /// not errors here: the syntax under them is complete. A consumer that
    /// needs a whole construct, a semantic phase lowering a body or a fix
    /// rewriting one, checks this bit and skips what it cannot trust.
    pub fn has_error(&self, index: NodeIdx) -> bool {
        self.nodes[index.to_usize()].has_error
    }

    /// The typed field `index` fills in its parent, when the parser retained
    /// the role because recovery would not leave it evident from kind and
    /// order alone.
    pub(crate) fn field(&self, index: NodeIdx) -> Option<usize> {
        self.nodes[index.to_usize()]
            .field
            .checked_sub(1)
            .map(usize::from)
    }

    /// Whether structural recovery or an `Error` node occurred anywhere in
    /// the file, so typed accessors must consider parser-retained roles.
    pub(crate) fn may_need_field_hints(&self) -> bool {
        self.may_need_field_hints
    }

    /// The raw index of the first token node `index` covers.
    pub fn first_token(&self, index: NodeIdx) -> RawIdx {
        self.nodes[index.to_usize()].first_token
    }

    /// One past the raw index of the last token node `index` covers. Only
    /// the root can be empty, over an empty file.
    pub fn end_token(&self, index: NodeIdx) -> RawIdx {
        self.nodes[index.to_usize()].end_token
    }

    /// The byte range node `index` covers: from the start of its first
    /// token to the end of its last one. `lexed` must be the file this tree
    /// was parsed from. Only the root can be empty, over an empty file.
    pub fn byte_range(&self, index: NodeIdx, lexed: &LexedFile) -> TextRange {
        let node = &self.nodes[index.to_usize()];
        let start = raw_boundary(lexed, node.first_token);
        let end = if node.end_token > node.first_token {
            lexed.range(node.end_token - 1).end()
        } else {
            start
        };
        TextRange::new(start, end)
    }

    /// The direct children of node `index`, last child first — the order a
    /// stack walk wants: popping a node and pushing its children visits the
    /// tree in preorder. Collect and reverse for source order.
    pub fn children(&self, index: NodeIdx) -> impl Iterator<Item = NodeIdx> + '_ {
        // Nodes of the subtree still unvisited, all below `child`.
        let mut remaining = self.nodes[index.to_usize()].extent as usize - 1;
        let mut child = index.to_usize();
        std::iter::from_fn(move || {
            (remaining > 0).then(|| {
                child -= 1;
                let size = self.nodes[child].extent as usize;
                remaining -= size;
                let current = child;
                child -= size - 1;
                node_idx(current)
            })
        })
    }

    /// The direct children of node `index` in source order. The tree keeps
    /// children last first, so this collects them: the typed views read
    /// through it, while a walk over whole subtrees should take
    /// [`children`](Self::children) and its stack order instead.
    pub fn children_in_order(
        &self,
        index: NodeIdx,
    ) -> impl DoubleEndedIterator<Item = NodeIdx> + ExactSizeIterator + use<> {
        let mut children: Vec<NodeIdx> = self.children(index).collect();
        children.reverse();
        children.into_iter()
    }

    /// The innermost node covering raw token `token`, which must lie in the
    /// file. A token attached to no node — trivia between two children —
    /// resolves to the nearest node whose range spans it, at worst the root.
    pub fn covering(&self, token: RawIdx) -> NodeIdx {
        self.covering_chain(token)
            .next()
            .expect("the root covers every token in the file")
    }

    /// The nodes covering raw token `token`, innermost first: the node
    /// [`covering`](Self::covering) answers, then each enclosing node out
    /// to the root — every node's parent is the entry after it. Never
    /// empty, since the root covers every token; `token` must lie in the
    /// file. The chain sifts every completion from the covering node to
    /// the root, so a consumer resolving many positions builds
    /// [`parents`](Self::parents) once instead.
    pub fn covering_chain(&self, token: RawIdx) -> impl Iterator<Item = NodeIdx> + '_ {
        assert!(
            token < self.nodes[self.root().to_usize()].end_token,
            "token must be within the file"
        );
        // TODO: descending from the root instead — hopping over later
        // siblings by extent at each level — would visit only the path and
        // its siblings, several times faster and no longer growing with
        // file size; take that trade once a consumer feels this scan.
        //
        // `end_token` is non-decreasing in completion order, so everything
        // ending at or before `token` drops out by binary search. Of the
        // rest, a node either covers `token` or lies wholly past it, and
        // covering nodes — an ancestor chain — complete innermost first.
        let from = self.nodes.partition_point(|node| node.end_token <= token);
        (from..self.nodes.len())
            .filter(move |&index| self.nodes[index].first_token <= token)
            .map(node_idx)
    }

    /// The parent of every node, one entry per node from one reverse pass;
    /// the root names itself. The tree stores no parent links — the
    /// covering chain answers parents for positional queries — so a
    /// consumer needing random-access parents builds this table on demand.
    pub fn parents(&self) -> Vec<NodeIdx> {
        let mut parents = vec![NodeIdx::new(0); self.nodes.len()];
        // The open ancestors, innermost last: node index and where its
        // subtree begins. Reverse postorder reaches a parent before its
        // children, and leaves a subtree exactly when the index drops
        // below its start.
        let mut stack: Vec<(NodeIdx, usize)> = Vec::new();
        for index in (0..self.nodes.len()).rev() {
            while stack.last().is_some_and(|&(_, start)| start > index) {
                stack.pop();
            }
            let node = node_idx(index);
            parents[index] = stack.last().map_or(node, |&(parent, _)| parent);
            stack.push((node, index + 1 - self.nodes[index].extent as usize));
        }
        parents
    }

    /// The pointer naming node `index`: its kind and byte range, which is
    /// what a later phase keeps to find the node again. `lexed` must be the
    /// file this tree was parsed from.
    pub fn ptr(&self, index: NodeIdx, lexed: &LexedFile) -> NodePtr {
        NodePtr {
            kind: self.kind(index),
            range: self.byte_range(index, lexed),
        }
    }

    /// The node `ptr` names in this tree: the one of its kind over exactly
    /// its byte range and text, if there is one. `ptr_source` must be the
    /// source the pointer came from; `lexed` and `source` must be the file
    /// this tree was parsed from. A pointer taken from another parse
    /// resolves here when the node it named still stands at the same bytes
    /// with the same text — a reparse of the same text, or of text edited
    /// only after the node — and answers `None` once the node has moved,
    /// changed, or gone. A pointer names at most one node: the parser never
    /// wraps a node in one of its own kind over exactly the same tokens, and
    /// debug builds reject a hand-built tree that does.
    pub fn resolve(
        &self,
        ptr: NodePtr,
        ptr_source: &str,
        lexed: &LexedFile,
        source: &str,
    ) -> Option<NodeIdx> {
        let root = self.root();
        if ptr.range.start() == ptr.range.end() {
            // Only the root of an empty file is empty.
            let empty_root = lexed.is_empty() && ptr.kind == self.kind(root);
            return empty_root.then_some(root);
        }
        // The range must begin and end on token boundaries.
        let first = lexed.token_at(ptr.range.start())?;
        let last = lexed.token_before(ptr.range.end())?;
        if lexed.range(first).start() != ptr.range.start()
            || lexed.range(last).end() != ptr.range.end()
        {
            return None;
        }
        let end = last + 1;
        // `end_token` is non-decreasing in postorder, so the nodes ending
        // at `end` are contiguous; among them the kind and the first token
        // pick the node.
        let from = self.nodes.partition_point(|node| node.end_token < end);
        let node = self.nodes[from..]
            .iter()
            .take_while(|node| node.end_token == end)
            .position(|node| node.first_token == first && node.kind == ptr.kind)
            .map(|offset| node_idx(from + offset));
        node.filter(|_| ptr.range.text(ptr_source) == ptr.range.text(source))
    }
}

/// A node's identity independent of the tree that holds it: its kind and
/// byte range, which name at most one node in any parsed tree when paired
/// with the source snapshot it came from. Semantic phases keep pointers,
/// not indices, so their results can point back into a tree that has since
/// been reparsed; [`SyntaxTree::resolve`] finds the node again while it
/// stands at the same bytes with the same text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodePtr {
    pub kind: NodeKind,
    pub range: TextRange,
}

/// A parsed file: its tree and the evidence observed while building it.
#[derive(Clone, Debug)]
pub struct Parse {
    tree: SyntaxTree,
    evidence: Box<[ParseEvidence]>,
}

impl Parse {
    /// Build a tree over the significant tokens of `input`, in source
    /// order: open the root, run `body` inside it, and close it. `body`
    /// must attach every significant token.
    pub(crate) fn build<'a>(
        input: &'a ParserInput,
        body: impl FnOnce(&mut Marker<'_, 'a>),
    ) -> Self {
        let mut builder = Builder {
            input,
            nodes: Vec::new(),
            position: SigIdx::new(0),
            slots: input.slots(),
            opened: 1,
            recoveries: 0,
            error_nodes: 0,
            last_recovery_evidence: None,
            evidence: Vec::new(),
        };
        body(&mut Marker {
            builder: &mut builder,
            first: NodeIdx::new(0),
            start: SigIdx::new(0),
            recoveries: 0,
            error_nodes: 0,
            id: 0,
            parent: 0,
            depth: 0,
            open: [None; BRACKET_PAIRS.len()],
            closer: None,
            enclosing_closer: None,
            // Closed here once `body` returns, never by `complete`.
            completed: true,
        });
        assert_eq!(
            builder.position,
            input.end(),
            "every significant token must be consumed"
        );
        // The root closes last, over every token: edge trivia included,
        // keeping the tree lossless end to end. It alone may be empty, over
        // an empty file.
        builder.nodes.push(Node {
            kind: NodeKind::SourceFile,
            has_error: builder.recoveries > 0 || builder.error_nodes > 0,
            field: 0,
            extent: to_u32(builder.nodes.len() + 1),
            first_token: RawIdx::new(0),
            end_token: input.raw_len(),
        });
        let may_need_field_hints = builder.recoveries > 0 || builder.error_nodes > 0;
        Self {
            tree: SyntaxTree {
                nodes: builder.nodes.into_boxed_slice(),
                may_need_field_hints,
            },
            evidence: builder
                .evidence
                .into_iter()
                .map(EvidenceBuilder::finish)
                .collect(),
        }
    }

    pub fn tree(&self) -> &SyntaxTree {
        &self.tree
    }

    /// Parser facts in observation order. Multiple independent facts may
    /// share an anchor.
    pub fn evidence(&self) -> &[ParseEvidence] {
        &self.evidence
    }
}

/// A build in progress.
struct Builder<'a> {
    input: &'a ParserInput,
    /// Completed nodes, children before parents.
    nodes: Vec<Node>,
    /// The next significant token to attach.
    position: SigIdx,
    /// The slots up to the input horizon: lookahead reads this prefix of
    /// the input's slots, so nothing can be seen or consumed at or past
    /// its end. `source_file` moves the horizon from one item start to the
    /// next, which makes recovery inside an item unable to take another
    /// item's tokens — there is no rule to get wrong.
    slots: &'a [Slot],
    /// Nodes opened so far, numbering the next one; the root is 0.
    opened: u32,
    /// Structural recovery facts recorded while building the tree.
    recoveries: u32,
    /// Completed `Error` nodes. A violation can produce one without a
    /// structural recovery, and open ancestors must still inherit its error.
    error_nodes: u32,
    /// The evidence index of the cursor-nearest structural recovery.
    last_recovery_evidence: Option<usize>,
    evidence: Vec<EvidenceBuilder>,
}

impl Builder<'_> {
    fn open(&mut self) -> u32 {
        let id = self.opened;
        self.opened += 1;
        id
    }

    /// The nonempty raw range covered by significant positions `start..end`.
    fn raw_range(&self, start: SigIdx, end: SigIdx) -> RawTokenRange {
        assert!(start < end && end <= self.input.end());
        RawTokenRange::new(self.input.token(start), self.input.token(end - 1) + 1)
    }

    /// The raw trivia interval at significant position `position`.
    fn raw_gap(&self, position: SigIdx) -> RawGap {
        assert!(position <= self.input.end());
        let trivia_start = match position.checked_sub(1) {
            Some(previous) => self.input.token(previous) + 1,
            None => RawIdx::new(0),
        };
        let trivia_end = if position == self.input.end() {
            self.input.raw_len()
        } else {
            self.input.token(position)
        };
        RawGap::new(trivia_start, trivia_end)
    }
}

enum EvidenceBuilder {
    Recovery {
        kind: ParseRecoveryKind,
        anchor: ParseAnchor,
        skipped: Vec<RawTokenRange>,
    },
    Violation(ParseViolation),
}

impl EvidenceBuilder {
    fn finish(self) -> ParseEvidence {
        match self {
            Self::Recovery {
                kind,
                anchor,
                skipped,
            } => ParseEvidence::Recovery(ParseRecovery {
                kind,
                anchor,
                skipped: skipped.into_boxed_slice(),
            }),
            Self::Violation(violation) => ParseEvidence::Violation(violation),
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct RecoveryCheckpoint(u32);

#[derive(Clone, Copy)]
pub(crate) struct RecoveryHandle(usize);

/// An open node: the root, lent by [`Parse::build`], or a child from
/// [`start`](Self::start) or [`precede`](Self::precede). Tokens attach to
/// the innermost open node. A child reborrows its parent for as long as it
/// is open, so the parent is untouchable until the child completes: the
/// stack of open nodes is a chain of borrows on the parser's own stack.
/// Completing a marker is the only way to close its node; dropping it
/// instead is a parser bug and panics on the spot.
///
/// Within the crate, the marker is also the parser's view of the input:
/// lookahead, the stream facts (jointness, newlines, boundaries, bracket
/// partners) at the cursor, and evidence recording, so one cursor serves
/// building and reading alike.
///
/// Completing the outer of two open nodes is a borrow error:
///
/// ```compile_fail,E0505
/// use sumi_lexer::lex;
/// use sumi_syntax::{NodeKind, Parse, ParserInput};
///
/// let input = ParserInput::new(&lex("x y").unwrap());
/// Parse::build(&input, |root| {
///     let mut outer = root.start();
///     outer.token();
///     let mut inner = outer.start();
///     inner.token();
///     outer.complete(NodeKind::LetStmt); // `outer` is borrowed by `inner`
///     inner.complete(NodeKind::NameRef);
/// });
/// ```
///
/// So is completing the root, which is only ever lent:
///
/// ```compile_fail,E0507
/// use sumi_lexer::lex;
/// use sumi_syntax::{NodeKind, Parse, ParserInput};
///
/// let input = ParserInput::new(&lex("x").unwrap());
/// Parse::build(&input, |root| {
///     root.token();
///     root.complete(NodeKind::SourceFile); // cannot move out of `*root`
/// });
/// ```
#[must_use = "a started node must be completed"]
pub(crate) struct Marker<'p, 'a> {
    builder: &'p mut Builder<'a>,
    /// Where the node's subtree begins among the completed nodes: every
    /// node completed since is inside it.
    first: NodeIdx,
    /// The significant position the node opens at.
    start: SigIdx,
    /// The structural recoveries recorded before the node opened: any more
    /// by the time it completes happened inside it.
    recoveries: u32,
    /// The `Error` nodes completed before this node opened. Like recoveries,
    /// any more by completion occurred inside its subtree.
    error_nodes: u32,
    /// Identity, so a completed node can name the node that contained it.
    id: u32,
    parent: u32,
    /// How many open nodes enclose this one; the root is at 0.
    depth: u32,
    /// The innermost open bracket construct of each pair, by the
    /// significant position of its opener and in [`BRACKET_PAIRS`] order:
    /// what a closer of that kind may belong to.
    open: [Option<SigIdx>; BRACKET_PAIRS.len()],
    /// The closer the stream pairs with the innermost bracket construct
    /// entered around this node — this node itself, once it has entered
    /// one — by significant position; `None` when the stream closes none.
    /// A closed construct owns everything up to its closer, so a `fn`
    /// inside it is garbage there, not the next item.
    closer: Option<SigIdx>,
    /// The nearest known closer outside `closer`. Entering an unclosed
    /// construct retains this limit, so local recovery can take matched
    /// groups whole without crossing a parser-owned enclosing closer.
    enclosing_closer: Option<SigIdx>,
    completed: bool,
}

impl<'a> Marker<'_, 'a> {
    /// Attach the next significant token to this node.
    pub(crate) fn token(&mut self) {
        assert!(
            self.builder.position.to_usize() < self.builder.slots.len(),
            "token past the input horizon"
        );
        self.builder.position += 1;
    }

    /// Attach the next token and, when it opens a matched bracket pair,
    /// every token through the pair's closer.
    pub(crate) fn group(&mut self) {
        let index = self.builder.position;
        self.token();
        if let Some(partner) = self.builder.input.partner(index)
            && partner > index
        {
            self.builder.position = partner + 1;
        }
    }

    /// Attach the next token and its matched bracket group only when that
    /// group closes strictly inside the nearest parser-owned construct. An
    /// opener paired with that construct's closer is malformed here and
    /// must not carry recovery past it. With no known closer, only a group
    /// contained on the malformed statement's line is certainly local;
    /// recovery keeps it atomic without swallowing later statements.
    pub(crate) fn group_inside(&mut self) {
        let index = self.builder.position;
        let partner = self
            .builder
            .input
            .partner(index)
            .filter(|&partner| partner > index);
        let limit = self.next_parser_closer();
        let whole = partner.is_some_and(|partner| match limit {
            Some(closer) => partner < closer,
            None => !self.builder.input.boundary_in(index + 1..partner + 1),
        });
        self.token();
        if let Some(partner) = partner.filter(|_| whole) {
            self.builder.position = partner + 1;
        }
    }

    /// Open a child at the next token; its kind is chosen when it
    /// completes.
    #[inline]
    pub(crate) fn start(&mut self) -> Marker<'_, 'a> {
        let first = NodeIdx::new(to_u32(self.builder.nodes.len()));
        let start = self.builder.position;
        let recoveries = self.builder.recoveries;
        let error_nodes = self.builder.error_nodes;
        let id = self.builder.open();
        Marker {
            builder: self.builder,
            first,
            start,
            recoveries,
            error_nodes,
            id,
            parent: self.id,
            depth: self.depth + 1,
            open: self.open,
            closer: self.closer,
            enclosing_closer: self.enclosing_closer,
            completed: false,
        }
    }

    /// Open a child wrapping `completed` — which must have completed
    /// directly inside this node — and everything attached since; its kind
    /// is chosen when it completes.
    #[inline]
    pub(crate) fn precede(&mut self, completed: CompletedMarker) -> Marker<'_, 'a> {
        assert_eq!(
            completed.parent, self.id,
            "a node is preceded only from the node that contained it"
        );
        let id = self.builder.open();
        Marker {
            builder: self.builder,
            first: completed.first,
            start: completed.start,
            recoveries: completed.recoveries,
            error_nodes: completed.error_nodes,
            id,
            parent: self.id,
            depth: self.depth + 1,
            open: self.open,
            closer: self.closer,
            enclosing_closer: self.enclosing_closer,
            completed: false,
        }
    }

    /// Retain which typed field a completed direct child fills. Most fields
    /// need no hint: their kind and order are enough. Recovery can remove a
    /// same-typed sibling or leave a subtype in either of two positions;
    /// those are marked where the parser has already settled their role.
    pub(crate) fn field(&mut self, completed: &CompletedMarker, field: u8) {
        assert_eq!(
            completed.parent, self.id,
            "a field is assigned only from the node that contains it"
        );
        self.set_field(completed.node, field);
    }

    /// The index of a completed direct child, retained across [`precede`]
    /// when its field cannot be known until the wrapper's other child parses.
    pub(crate) fn completed_node(&self, completed: &CompletedMarker) -> NodeIdx {
        assert_eq!(
            completed.parent, self.id,
            "a completed node belongs to its containing node"
        );
        completed.node
    }

    /// Retain the field of the child this marker wrapped with [`precede`].
    pub(crate) fn wrapped_field(&mut self, node: NodeIdx, field: u8) {
        let child = &self.builder.nodes[node.to_usize()];
        let first = node.to_usize() + 1 - child.extent as usize;
        assert_eq!(
            NodeIdx::new(to_u32(first)),
            self.first,
            "a wrapped field belongs to the subtree this node wraps"
        );
        self.set_field(node, field);
    }

    fn set_field(&mut self, node: NodeIdx, field: u8) {
        let child = &mut self.builder.nodes[node.to_usize()];
        // Error nodes stand where typed syntax was required but implement no
        // typed field. Retaining their position must not make them a field.
        if child.kind == NodeKind::Error {
            return;
        }
        assert_eq!(child.field, 0, "a node receives its field only once");
        child.field = field
            .checked_add(1)
            .expect("a typed field index fits below 255");
    }

    /// Whether structural recovery occurred since this node opened.
    pub(crate) fn recovered_inside(&self) -> bool {
        self.builder.recoveries > self.recoveries
    }

    /// Whether `completed` is an untyped error node.
    pub(crate) fn is_error(&self, completed: &CompletedMarker) -> bool {
        self.builder.nodes[completed.node.to_usize()].kind == NodeKind::Error
    }

    /// Close the node as `kind`; it must cover at least one token.
    #[inline]
    pub(crate) fn complete(mut self, kind: NodeKind) -> CompletedMarker {
        let builder = &mut *self.builder;
        assert!(
            builder.position > self.start,
            "a node must cover at least one token"
        );
        // An `Error` node can be the effect of a recovery recorded before it
        // opened or of a violation. Any other node has an error when recovery
        // happened or an `Error` node completed inside it, descendants
        // included.
        let is_error = kind == NodeKind::Error;
        let has_error = is_error
            || builder.recoveries > self.recoveries
            || builder.error_nodes > self.error_nodes;
        builder.error_nodes += u32::from(is_error);
        let first_token = builder.input.token(self.start);
        let end_token = builder.input.token(builder.position - 1) + 1;
        // A node wrapping one of its own kind over exactly its tokens would
        // be indistinguishable from it by kind and range, which is how a
        // [`NodePtr`] names a node. The parser never builds one, and debug
        // builds — every test run, the property tests over garbage input
        // included — reject the shape; in release the two compares per node
        // measured two percent of the parser, so it trusts the parser. Such
        // a chain is sole children all the way down, so it hangs off the
        // last node, and only a last child over the same tokens needs the
        // walk.
        if cfg!(debug_assertions)
            && let Some(child) = builder
                .nodes
                .get(self.first.to_usize()..)
                .and_then(<[Node]>::last)
            && child.first_token == first_token
            && child.end_token == end_token
        {
            reject_same_kind_chain(&builder.nodes[self.first.to_usize()..], kind);
        }
        let node = NodeIdx::new(to_u32(builder.nodes.len()));
        builder.nodes.push(Node {
            kind,
            has_error,
            field: 0,
            extent: to_u32(builder.nodes.len() - self.first.to_usize() + 1),
            first_token,
            end_token,
        });
        self.completed = true;
        CompletedMarker {
            node,
            first: self.first,
            start: self.start,
            recoveries: self.recoveries,
            error_nodes: self.error_nodes,
            parent: self.parent,
        }
    }

    /// How many open nodes enclose this one: the parser's nesting depth.
    pub(crate) fn depth(&self) -> u32 {
        self.depth
    }

    /// The kind of the next significant token, or `None` at end of input —
    /// the input horizon included: past it, lookahead reports the input
    /// exhausted, and every recovery unwinds exactly as it does at the end
    /// of the file.
    pub(crate) fn current(&self) -> Option<SyntaxKind> {
        self.nth(0)
    }

    /// The kind of the significant token `n` past the next one; `None` at
    /// or past the input horizon.
    pub(crate) fn nth(&self, n: usize) -> Option<SyntaxKind> {
        let index = self.builder.position.checked_add(n as u32)?;
        self.builder
            .slots
            .get(index.to_usize())
            .map(|slot| slot.kind)
    }

    pub(crate) fn at(&self, kind: SyntaxKind) -> bool {
        self.current() == Some(kind)
    }

    /// Whether the next token is glued to the one after it.
    pub(crate) fn joint(&self) -> bool {
        self.nth_joint(0)
    }

    /// Whether the significant token `n` past the next one is glued to the
    /// one after it.
    pub(crate) fn nth_joint(&self, n: usize) -> bool {
        self.builder
            .position
            .checked_add(n as u32)
            .is_some_and(|index| {
                index.to_usize() < self.builder.input.len() && self.builder.input.is_joint(index)
            })
    }

    /// Whether the next token is glued to the previous one.
    pub(crate) fn joint_before(&self) -> bool {
        self.builder
            .position
            .checked_sub(1)
            .is_some_and(|previous| self.builder.input.is_joint(previous))
    }

    /// Whether a line break precedes the next token.
    pub(crate) fn newline(&self) -> bool {
        self.nth_newline(0)
    }

    /// Whether a line break precedes the significant token `n` past the
    /// next one.
    pub(crate) fn nth_newline(&self, n: usize) -> bool {
        self.builder
            .position
            .checked_add(n as u32)
            .is_some_and(|index| {
                index.to_usize() < self.builder.input.len()
                    && self.builder.input.newline_before(index)
            })
    }

    /// Whether a statement boundary precedes the next token.
    pub(crate) fn boundary(&self) -> bool {
        self.nth_boundary(0)
    }

    /// Whether a statement boundary precedes the significant token `n` past
    /// the next one.
    pub(crate) fn nth_boundary(&self, n: usize) -> bool {
        self.builder
            .position
            .checked_add(n as u32)
            .is_some_and(|index| {
                index.to_usize() < self.builder.input.len()
                    && self.builder.input.boundary_before(index)
            })
    }

    /// Whether the next token begins an expression. Whatever parses an
    /// expression where this holds takes at least that token.
    pub(crate) fn starts_expression(&self) -> bool {
        self.current()
            .is_some_and(crate::generated::starts_expression)
    }

    /// Whether the next token is a bracket the stream pairs with another,
    /// ahead or behind.
    pub(crate) fn partnered(&self) -> bool {
        let position = self.builder.position;
        position.to_usize() < self.builder.input.len()
            && self.builder.input.partner(position).is_some()
    }

    /// The offset from the next token of the bracket matching the
    /// significant token `n` past it, when that bracket lies ahead.
    pub(crate) fn nth_partner(&self, n: usize) -> Option<usize> {
        let index = self.builder.position.checked_add(n as u32)?;
        if index.to_usize() >= self.builder.input.len() {
            return None;
        }
        let partner = self.builder.input.partner(index)?;
        partner
            .to_u32()
            .checked_sub(self.builder.position.to_u32())
            .map(|offset| offset as usize)
    }

    /// Whether the next token is the closer this bracket construct owns:
    /// the one the stream pairs with its opener, or an orphan available as
    /// a recovery closer, since recovery may have skipped the closer that
    /// pairing originally chose. One paired with any other opener belongs
    /// to another construct.
    pub(crate) fn owns_closer(&self) -> bool {
        let closer = self
            .builder
            .input
            .get(self.start)
            .and_then(crate::generated::closer)
            .unwrap_or_else(|| unreachable!("only a bracket construct owns a closer"));
        self.at(closer)
            && self
                .builder
                .input
                .partner(self.builder.position)
                .is_none_or(|partner| partner == self.start)
    }

    /// Whether the next token is a closer of kind `closer` that a construct
    /// of its kind still open around this node can own: one paired with
    /// that construct's opener or with an opener outside it, or an orphan.
    /// One paired with an opener the parser has already left behind is
    /// garbage instead.
    pub(crate) fn closes_open(&self, closer: SyntaxKind) -> bool {
        let Some(open) = pair_index(closer).and_then(|pair| self.open[pair]) else {
            return false;
        };
        self.at(closer)
            && self
                .builder
                .input
                .partner(self.builder.position)
                .is_none_or(|partner| partner <= open)
    }

    /// Whether the next token is a closer of a pair that suspends the
    /// newline rule — `)`, and every kind like it — which a construct still
    /// open around this node can own. Where a block or an expression
    /// stands, such a closer ends it and is left to its owner.
    pub(crate) fn closes_open_bracket(&self) -> bool {
        self.current().is_some_and(|kind| {
            opener(kind).is_some_and(|opener| !encloses_statements(opener))
                && self.closes_open(kind)
        })
    }

    /// Mark this node as a bracket construct whose opener is its first
    /// token: it and the children opened from now on know whether the
    /// stream closes it, and that a construct of its kind is open.
    pub(crate) fn enter(&mut self) {
        self.enclosing_closer = self.closer.or(self.enclosing_closer);
        self.closer = self.builder.input.partner(self.start);
        let pair = self
            .builder
            .input
            .get(self.start)
            .and_then(pair_index)
            .unwrap_or_else(|| unreachable!("an entered construct opens with a bracket"));
        self.open[pair] = Some(self.start);
    }

    /// Hide the bracket constructs open around this node from what is
    /// parsed inside it, its own excepted. A hole's code is confined to the
    /// hole: no closer inside it belongs to a construct outside, so none is
    /// left for one, and no recovery inside reaches past the hole's end.
    pub(crate) fn seal(&mut self) {
        let own = self.builder.input.get(self.start).and_then(pair_index);
        for (pair, open) in self.open.iter_mut().enumerate() {
            if Some(pair) != own {
                *open = None;
            }
        }
        self.enclosing_closer = None;
    }

    /// Whether the stream closes the innermost bracket construct entered
    /// around this node.
    pub(crate) fn closed(&self) -> bool {
        self.closer.is_some()
    }

    /// Whether the closer the stream pairs with the innermost bracket
    /// construct entered around this node lies ahead of the next token.
    pub(crate) fn closer_ahead(&self) -> bool {
        self.closer
            .is_some_and(|closer| closer > self.builder.position)
    }

    /// The nearest closer ahead which this or an enclosing parser construct
    /// owns. A construct whose mechanical closer recovery already passed
    /// yields to the nearest enclosing one retained when it was entered.
    fn next_parser_closer(&self) -> Option<SigIdx> {
        [self.closer, self.enclosing_closer]
            .into_iter()
            .flatten()
            .filter(|&closer| closer >= self.builder.position)
            .min()
    }

    /// The number of top-level items the input stream found.
    pub(crate) fn item_count(&self) -> usize {
        self.builder.input.item_starts().len()
    }

    /// Where item `index` starts, or the end of the input for the position
    /// one past the last item: the horizon for the segment before it.
    pub(crate) fn item_limit(&self, index: usize) -> SigIdx {
        self.builder
            .input
            .item_starts()
            .get(index)
            .map_or(self.builder.input.end(), |&start| start)
    }

    /// Move the input horizon. Only `source_file` does, once per item
    /// segment; the horizon never moves back past the cursor or beyond the
    /// input.
    pub(crate) fn set_limit(&mut self, limit: SigIdx) {
        debug_assert!(self.builder.position <= limit);
        self.builder.slots = &self.builder.input.slots()[..limit.to_usize()];
    }

    /// Attach the next token if it is `kind` and no statement boundary
    /// precedes it; otherwise record that `kind` was expected and leave the
    /// token where it is.
    pub(crate) fn expect(&mut self, kind: SyntaxKind) -> bool {
        if self.at(kind) && !self.boundary() {
            self.token();
            true
        } else {
            self.missing(ParseExpected::Token(kind));
            false
        }
    }

    /// The current structural recovery epoch.
    pub(crate) fn recovery_checkpoint(&self) -> RecoveryCheckpoint {
        RecoveryCheckpoint(self.builder.recoveries)
    }

    /// Whether structural recovery has happened since `checkpoint`.
    pub(crate) fn recovered_since(&self, checkpoint: RecoveryCheckpoint) -> bool {
        self.builder.recoveries > checkpoint.0
    }

    /// The cursor-nearest structural recovery since `checkpoint`.
    pub(crate) fn latest_recovery_since(
        &self,
        checkpoint: RecoveryCheckpoint,
    ) -> Option<RecoveryHandle> {
        (self.builder.recoveries > checkpoint.0).then(|| {
            RecoveryHandle(
                self.builder
                    .last_recovery_evidence
                    .expect("every recovery has evidence"),
            )
        })
    }

    /// Record syntax missing in the raw trivia gap at the cursor.
    pub(crate) fn missing(&mut self, expected: ParseExpected) -> RecoveryHandle {
        let anchor = ParseAnchor::Gap(self.builder.raw_gap(self.builder.position));
        self.record_recovery(ParseRecoveryKind::Expected(expected), anchor)
    }

    /// Record a closing delimiter missing from the cursor gap, retaining
    /// the opening delimiter at this node's first token as its counterpart.
    pub(crate) fn missing_closer(&mut self) -> RecoveryHandle {
        let kind = self
            .builder
            .input
            .get(self.start)
            .and_then(crate::generated::closer)
            .unwrap_or_else(|| unreachable!("a missing closer belongs to a bracket node"));
        let opener = self.builder.raw_range(self.start, self.start + 1);
        self.missing(ParseExpected::Closer { kind, opener })
    }

    /// Record structural recovery over `width` significant tokens at the
    /// cursor.
    pub(crate) fn recover_tokens(
        &mut self,
        kind: ParseRecoveryKind,
        width: usize,
    ) -> RecoveryHandle {
        let range = self.raw_token_range(width);
        self.recover_range(kind, range)
    }

    /// Record structural recovery over an already known raw token range.
    pub(crate) fn recover_range(
        &mut self,
        kind: ParseRecoveryKind,
        range: RawTokenRange,
    ) -> RecoveryHandle {
        let anchor = ParseAnchor::Tokens(range);
        self.record_recovery(kind, anchor)
    }

    /// Record a rule broken by `width` significant tokens which the parser
    /// accepts structurally.
    pub(crate) fn violation(&mut self, kind: ParseViolationKind, width: usize) {
        let range = self.raw_token_range(width);
        self.builder
            .evidence
            .push(EvidenceBuilder::Violation(ParseViolation { kind, range }));
    }

    /// Attach a raw range skipped during `recovery`.
    pub(crate) fn skipped(&mut self, recovery: RecoveryHandle, range: RawTokenRange) {
        let EvidenceBuilder::Recovery { skipped, .. } = &mut self.builder.evidence[recovery.0]
        else {
            unreachable!("a recovery handle names recovery evidence")
        };
        skipped.push(range);
    }

    /// The nonempty raw range consumed since this marker opened.
    pub(crate) fn covered_range(&self) -> RawTokenRange {
        self.builder.raw_range(self.start, self.builder.position)
    }

    fn raw_token_range(&self, width: usize) -> RawTokenRange {
        self.builder.raw_range(
            self.builder.position,
            self.builder
                .position
                .checked_add(width as u32)
                .expect("raw token range width does not overflow"),
        )
    }

    fn record_recovery(&mut self, kind: ParseRecoveryKind, anchor: ParseAnchor) -> RecoveryHandle {
        let evidence = self.builder.evidence.len();
        self.builder.evidence.push(EvidenceBuilder::Recovery {
            kind,
            anchor,
            skipped: Vec::new(),
        });
        self.builder.recoveries += 1;
        self.builder.last_recovery_evidence = Some(evidence);
        RecoveryHandle(evidence)
    }
}

impl Drop for Marker<'_, '_> {
    fn drop(&mut self) {
        // Stay quiet while unwinding, or the original panic is lost to an
        // abort.
        if !self.completed && !std::thread::panicking() {
            panic!("a started node was dropped without being completed");
        }
    }
}

/// A completed node, held so a wrapper can be opened around it from the
/// node that contained it. Plain data: holding one borrows nothing.
pub(crate) struct CompletedMarker {
    /// This completed node's own index.
    node: NodeIdx,
    /// Where the node's subtree begins among the completed nodes.
    first: NodeIdx,
    /// The significant position the node opened at.
    start: SigIdx,
    /// The structural recoveries recorded before it opened.
    recoveries: u32,
    /// The `Error` nodes completed before it opened.
    error_nodes: u32,
    /// Identity of the node it completed inside.
    parent: u32,
}

/// Panic if the chain of nodes covering exactly the same tokens as the
/// node being completed — `subtree`'s last node and its sole children down
/// from it — contains `kind`. Out of the completion path: a last child
/// over the same tokens is rare, and the walk is shorter than it.
#[cold]
#[inline(never)]
fn reject_same_kind_chain(subtree: &[Node], kind: NodeKind) {
    let last = subtree.len() - 1;
    let (first_token, end_token) = (subtree[last].first_token, subtree[last].end_token);
    let mut index = last;
    loop {
        let child = subtree[index];
        if child.first_token != first_token || child.end_token != end_token {
            break;
        }
        assert!(
            child.kind != kind,
            "a node must not wrap a node of its own kind over the same tokens"
        );
        if child.extent == 1 || index == 0 {
            break;
        }
        index -= 1;
    }
}

/// Node counts are stored as `u32`; nothing bounds them by the source
/// length the way token indices are, so the narrowing is checked.
#[inline]
fn to_u32(count: usize) -> u32 {
    u32::try_from(count).expect("count fits in u32")
}

/// A node index from a position in the node array. The array's length was
/// checked to fit `u32` as it grew, so the narrowing cannot truncate, and
/// the positional queries skip a check per node.
#[inline]
fn node_idx(index: usize) -> NodeIdx {
    NodeIdx::new(index as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    use sumi_lexer::{LexedFile, lex};

    use crate::NodeKind::*;

    #[test]
    fn parser_evidence_retains_same_position_facts() {
        let lexed = lex("x").expect("test source fits in u32");
        let input = ParserInput::new(&lexed);
        let parse = Parse::build(&input, |root| {
            let checkpoint = root.recovery_checkpoint();
            root.violation(ParseViolationKind::SpacedPrefixOperator, 1);
            assert!(!root.recovered_since(checkpoint));

            root.recover_tokens(ParseRecoveryKind::Expected(ParseExpected::Expression), 1);
            assert!(root.recovered_since(checkpoint));
            root.token();
        });

        let [violation, recovery] = parse.evidence() else {
            panic!("both same-position facts must be retained")
        };
        assert!(matches!(violation, ParseEvidence::Violation(_)));
        assert!(matches!(recovery, ParseEvidence::Recovery(_)));
    }

    // The tree builder, exercised by hand: how nodes and markers nest, what
    // `precede` wraps, which node owns interior trivia, and where a misuse
    // panics. The builder is the parser's, and crate-private; a hand-built
    // tree records no parser evidence, and may take shapes the parser never
    // would, to pin the boundaries the parsed goldens cannot.
    /// Open a child of `parent`, run `body` inside it, and complete it as
    /// `kind`.
    fn node(
        parent: &mut Marker<'_, '_>,
        kind: NodeKind,
        body: impl FnOnce(&mut Marker<'_, '_>),
    ) -> CompletedMarker {
        let mut child = parent.start();
        body(&mut child);
        child.complete(kind)
    }

    /// A node over exactly the next token.
    fn leaf(parent: &mut Marker<'_, '_>, kind: NodeKind) -> CompletedMarker {
        node(parent, kind, |m| m.token())
    }

    /// Attach the next `count` tokens to `marker`.
    fn tokens(marker: &mut Marker<'_, '_>, count: usize) {
        for _ in 0..count {
            marker.token();
        }
    }

    /// Lex `source` and build a tree over it by running `build` inside the
    /// root, then dump it.
    fn dump(source: &str, build: impl FnOnce(&mut Marker<'_, '_>)) -> Vec<String> {
        let lexed = lex(source).expect("test sources fit in u32");
        let input = ParserInput::new(&lexed);
        let parse = Parse::build(&input, build);
        assert!(
            parse.evidence().is_empty(),
            "hand-built trees record no parser evidence"
        );
        render_tree(parse.tree(), &lexed, source)
    }

    #[track_caller]
    fn check(source: &str, build: impl FnOnce(&mut Marker<'_, '_>), expected: &[&str]) {
        assert_eq!(dump(source, build), expected, "for source {source:?}");
    }

    #[test]
    fn empty_source_builds_an_empty_root() {
        check("", |_| {}, &[r#"SourceFile 0..0 """#]);
    }

    #[test]
    fn the_root_owns_edge_trivia() {
        check("  \n", |_| {}, &[r#"SourceFile 0..3 "  \n""#]);
    }

    #[test]
    fn statements_nest_and_trivia_stays_interior() {
        check(
            "let x = 1",
            |b| {
                node(b, LetStmt, |b| {
                    tokens(b, 3); // let x =
                    leaf(b, LiteralExpr);
                });
            },
            &[
                "SourceFile 0..9",
                "  LetStmt 0..9",
                r#"    LiteralExpr 8..9 "1""#,
            ],
        );
    }

    #[test]
    fn precede_wraps_the_left_operand() {
        check(
            "a + b",
            |b| {
                let lhs = leaf(b, NameRef);
                let mut m = b.precede(lhs);
                m.token(); // +
                leaf(&mut m, NameRef);
                m.complete(BinaryExpr);
            },
            &[
                "SourceFile 0..5",
                "  BinaryExpr 0..5",
                r#"    NameRef 0..1 "a""#,
                r#"    NameRef 4..5 "b""#,
            ],
        );
    }

    #[test]
    fn precede_wraps_everything_attached_since_completion() {
        // The operator is attached before the wrapper opens, yet lands inside
        // it: the wrapper opens where the wrapped node did.
        check(
            "a + b",
            |b| {
                let lhs = leaf(b, NameRef);
                b.token(); // +
                let mut m = b.precede(lhs);
                leaf(&mut m, NameRef);
                m.complete(BinaryExpr);
            },
            &[
                "SourceFile 0..5",
                "  BinaryExpr 0..5",
                r#"    NameRef 0..1 "a""#,
                r#"    NameRef 4..5 "b""#,
            ],
        );
    }

    #[test]
    fn precede_encloses_siblings_completed_since() {
        check(
            "a + b",
            |b| {
                let lhs = leaf(b, NameRef);
                node(b, Error, |b| tokens(b, 2)); // + b
                b.precede(lhs).complete(BinaryExpr);
            },
            &[
                "SourceFile 0..5",
                "  BinaryExpr 0..5",
                r#"    NameRef 0..1 "a""#,
                r#"    Error 2..5 "+ b""#,
            ],
        );
    }

    #[test]
    fn precede_chains_for_left_associativity() {
        check(
            "a + b + c",
            |b| {
                let mut lhs = leaf(b, NameRef);
                for _ in 0..2 {
                    let mut m = b.precede(lhs);
                    m.token(); // +
                    leaf(&mut m, NameRef);
                    lhs = m.complete(BinaryExpr);
                }
            },
            &[
                "SourceFile 0..9",
                "  BinaryExpr 0..9",
                "    BinaryExpr 0..5",
                r#"      NameRef 0..1 "a""#,
                r#"      NameRef 4..5 "b""#,
                r#"    NameRef 8..9 "c""#,
            ],
        );
    }

    #[test]
    fn function_items_nest() {
        check(
            "fn f(a: int) -> int { a }",
            |b| {
                node(b, FnItem, |b| {
                    tokens(b, 2); // fn f
                    node(b, ParamList, |b| {
                        b.token(); // (
                        node(b, Param, |b| {
                            tokens(b, 2); // a:
                            leaf(b, TypeRef); // int
                        });
                        b.token(); // )
                    });
                    tokens(b, 2); // ->
                    leaf(b, TypeRef); // int
                    node(b, Block, |b| {
                        b.token(); // {
                        leaf(b, NameRef);
                        b.token(); // }
                    });
                });
            },
            &[
                "SourceFile 0..25",
                "  FnItem 0..25",
                "    ParamList 4..12",
                "      Param 5..11",
                r#"        TypeRef 8..11 "int""#,
                r#"    TypeRef 16..19 "int""#,
                "    Block 20..25",
                r#"      NameRef 22..23 "a""#,
            ],
        );
    }

    #[test]
    fn statement_kinds_cover_their_tokens() {
        check(
            "let x = -1\nx = 2\n_ = f((x))\ng(x)\nreturn",
            |b| {
                node(b, LetStmt, |b| {
                    tokens(b, 3); // let x =
                    node(b, PrefixExpr, |b| {
                        b.token(); // -
                        leaf(b, LiteralExpr);
                    });
                });
                node(b, AssignStmt, |b| {
                    leaf(b, NameRef);
                    b.token(); // =
                    leaf(b, LiteralExpr);
                });
                node(b, DiscardStmt, |b| {
                    tokens(b, 2); // _ =
                    let callee = leaf(b, NameRef);
                    let mut m = b.precede(callee);
                    node(&mut m, ArgList, |b| {
                        b.token(); // (
                        node(b, ParenExpr, |b| {
                            b.token(); // (
                            leaf(b, NameRef);
                            b.token(); // )
                        });
                        b.token(); // )
                    });
                    m.complete(CallExpr);
                });
                // An expression in statement position is a bare child: with no
                // `;`, statement or tail is a matter of position.
                let callee = leaf(b, NameRef);
                let mut m = b.precede(callee);
                node(&mut m, ArgList, |b| {
                    b.token(); // (
                    leaf(b, NameRef);
                    b.token(); // )
                });
                m.complete(CallExpr);
                node(b, ReturnStmt, |b| b.token());
            },
            &[
                "SourceFile 0..39",
                "  LetStmt 0..10",
                "    PrefixExpr 8..10",
                r#"      LiteralExpr 9..10 "1""#,
                "  AssignStmt 11..16",
                r#"    NameRef 11..12 "x""#,
                r#"    LiteralExpr 15..16 "2""#,
                "  DiscardStmt 17..27",
                "    CallExpr 21..27",
                r#"      NameRef 21..22 "f""#,
                "      ArgList 22..27",
                "        ParenExpr 23..26",
                r#"          NameRef 24..25 "x""#,
                "  CallExpr 28..32",
                r#"    NameRef 28..29 "g""#,
                "    ArgList 29..32",
                r#"      NameRef 30..31 "x""#,
                r#"  ReturnStmt 33..39 "return""#,
            ],
        );
    }

    #[test]
    fn if_expressions_and_error_nodes() {
        check(
            "if c { a } else { b } €",
            |b| {
                node(b, IfExpr, |b| {
                    b.token(); // if
                    leaf(b, NameRef);
                    node(b, Block, |b| {
                        b.token(); // {
                        leaf(b, NameRef);
                        b.token(); // }
                    });
                    b.token(); // else
                    node(b, Block, |b| {
                        b.token(); // {
                        leaf(b, NameRef);
                        b.token(); // }
                    });
                });
                leaf(b, Error);
            },
            &[
                "SourceFile 0..25",
                "  IfExpr 0..21",
                r#"    NameRef 3..4 "c""#,
                "    Block 5..10",
                r#"      NameRef 7..8 "a""#,
                "    Block 16..21",
                r#"      NameRef 18..19 "b""#,
                r#"  Error 22..25 "€""#,
            ],
        );
    }

    #[test]
    fn covering_finds_the_innermost_node() {
        let source = "let x = 1\ny";
        let lexed = lex(source).expect("test sources fit in u32");
        let input = ParserInput::new(&lexed);
        let parse = Parse::build(&input, |b| {
            node(b, LetStmt, |b| {
                tokens(b, 3); // let x =
                leaf(b, LiteralExpr);
            });
            leaf(b, NameRef);
        });
        let tree = parse.tree();
        assert_eq!(tree.kind(tree.root()), SourceFile);

        let kind_at = |token| tree.kind(tree.covering(RawIdx::new(token)));
        assert_eq!(kind_at(0), LetStmt); // `let`, attached to the statement
        assert_eq!(kind_at(1), LetStmt); // trivia inside the statement
        assert_eq!(kind_at(6), LiteralExpr); // `1`, under the statement
        assert_eq!(kind_at(7), SourceFile); // the newline between children
        assert_eq!(kind_at(8), NameRef); // `y`
    }

    // What the types cannot rule out is checked at run time. (What they can —
    // completing a parent before its child, completing the root — is pinned by
    // the `compile_fail` examples on `Marker`.)

    #[test]
    #[should_panic(expected = "at least one token")]
    fn an_empty_node_panics_at_completion() {
        dump("x", |b| {
            leaf(b, NameRef);
            node(b, Error, |_| {});
        });
    }

    #[test]
    #[should_panic(expected = "receives its field only once")]
    fn assigning_a_child_field_twice_panics() {
        dump("x", |root| {
            let child = leaf(root, NameRef);
            root.field(&child, 0);
            root.field(&child, 0);
        });
    }

    #[test]
    #[should_panic(expected = "preceded only from the node that contained it")]
    fn preceding_after_the_containing_node_closed_panics() {
        dump("x y", |b| {
            let mut stmt = b.start();
            let name = leaf(&mut stmt, NameRef);
            stmt.complete(LetStmt);
            let _wrapper = b.precede(name);
        });
    }

    #[test]
    #[should_panic(expected = "preceded only from the node that contained it")]
    fn preceding_from_a_sibling_panics() {
        dump("a + b", |b| {
            let lhs = leaf(b, NameRef);
            let mut rest = b.start();
            tokens(&mut rest, 2); // + b
            let _wrapper = rest.precede(lhs);
        });
    }

    #[test]
    #[should_panic(expected = "dropped without being completed")]
    fn a_dropped_marker_panics_where_it_drops() {
        dump("x", |b| {
            let mut marker = b.start();
            marker.token();
        });
    }

    #[test]
    #[should_panic(expected = "token past the input horizon")]
    fn a_token_past_the_end_panics() {
        dump("x", |b| tokens(b, 2));
    }

    #[test]
    #[should_panic(expected = "every significant token must be consumed")]
    fn leftover_tokens_panic_at_build() {
        dump("x y", |b| b.token());
    }

    #[test]
    #[should_panic(expected = "wrap a node of its own kind over the same tokens")]
    fn wrapping_a_node_of_its_own_kind_over_its_tokens_panics() {
        dump("x", |b| {
            let name = leaf(b, NameRef);
            b.precede(name).complete(NameRef);
        });
    }

    #[test]
    fn wrapping_a_node_of_another_kind_over_its_tokens_is_fine() {
        check(
            "x",
            |b| {
                let name = leaf(b, NameRef);
                b.precede(name).complete(ParenExpr);
            },
            &[
                "SourceFile 0..1",
                "  ParenExpr 0..1",
                r#"    NameRef 0..1 "x""#,
            ],
        );
    }

    /// Build `let x = 1` by hand and probe the boundaries the parsed goldens
    /// cannot pin: interior trivia answers the innermost node spanning it.
    #[test]
    fn trivia_between_children_belongs_to_the_spanning_node() {
        let source = "let x = 1 // c";
        let lexed = lex(source).expect("test sources fit in u32");
        let input = ParserInput::new(&lexed);
        let built = Parse::build(&input, |root| {
            node(root, LetStmt, |stmt| {
                stmt.token(); // let
                node(stmt, NameRef, |name| name.token());
                stmt.token(); // =
                node(stmt, LiteralExpr, |literal| literal.token());
            });
        });
        let tree = built.tree();
        // Nodes complete in postorder: NameRef 0, LiteralExpr 1, LetStmt 2,
        // the root 3. Tokens: `let` ` ` `x` ` ` `=` ` ` `1` ` ` `// c`.
        let chain = |token| {
            tree.covering_chain(RawIdx::new(token))
                .map(NodeIdx::to_usize)
                .collect::<Vec<_>>()
        };
        assert_eq!(chain(0), [2, 3]); // `let` — the statement
        assert_eq!(chain(1), [2, 3]); // the space inside it too
        assert_eq!(chain(2), [0, 2, 3]); // `x` — out from the name
        assert_eq!(chain(6), [1, 2, 3]); // `1` — out from the literal
        assert_eq!(chain(7), [3]); // trailing trivia — the root only
        assert_eq!(chain(8), [3]);
        assert_eq!(tree.covering(RawIdx::new(6)).to_usize(), 1);
    }

    #[test]
    #[should_panic(expected = "token must be within the file")]
    fn covering_a_token_past_the_file_panics() {
        let source = "x";
        let lexed = lex(source).expect("test sources fit in u32");
        let input = ParserInput::new(&lexed);
        let built = Parse::build(&input, |root| {
            node(root, NameRef, |name| name.token());
        });
        built.tree().covering(RawIdx::new(1));
    }

    /// Assert the tree invariants and render one line per node: `Kind
    /// start..end` byte ranges, indented by depth, with the text of childless
    /// nodes appended.
    /// Assert the tree invariants and render one line per node: `Kind
    /// start..end` byte ranges, indented by depth, with the text of childless
    /// nodes appended.
    fn render_tree(tree: &SyntaxTree, lexed: &LexedFile, source: &str) -> Vec<String> {
        let mut lines = Vec::new();
        let mut visited = 0usize;
        render(
            tree,
            lexed,
            source,
            tree.root(),
            0,
            &mut lines,
            &mut visited,
        );
        assert_eq!(visited, tree.len(), "extents must partition the tree");
        lines
    }

    fn render(
        tree: &SyntaxTree,
        lexed: &LexedFile,
        source: &str,
        node: NodeIdx,
        depth: usize,
        lines: &mut Vec<String>,
        visited: &mut usize,
    ) {
        *visited += 1;
        let first = tree.first_token(node);
        let end = tree.end_token(node);
        assert!(first <= end, "node {node:?} has a backwards token range");

        let range = tree.byte_range(node, lexed);
        let (from, to) = (range.start().to_u32(), range.end().to_u32());
        let mut line = format!(
            "{:indent$}{:?} {from}..{to}",
            "",
            tree.kind(node),
            indent = depth * 2
        );
        if tree.children(node).next().is_none() {
            line.push_str(&format!(" {:?}", &source[from as usize..to as usize]));
        }
        lines.push(line);

        // The tree yields children last first; the dump reads in source order.
        let mut children: Vec<NodeIdx> = tree.children(node).collect();
        children.reverse();
        let mut previous_end = first;
        for child in children {
            assert!(
                tree.first_token(child) >= previous_end,
                "children must be ordered and disjoint"
            );
            assert!(
                tree.end_token(child) <= end,
                "a child must stay inside its parent"
            );
            previous_end = tree.end_token(child);
            render(tree, lexed, source, child, depth + 1, lines, visited);
        }
    }
}
