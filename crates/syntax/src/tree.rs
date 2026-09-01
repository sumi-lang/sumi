//! The syntax tree: flat, postorder, token-anchored.
//!
//! A [`SyntaxTree`] stores structure only. Each node is a kind, a subtree
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
//! attachment is a consumer's policy, not a tree property.
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
//! the node that contained it, every node covers at least one token, a
//! marker dropped uncompleted panics where it drops, and `build` rejects a
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

use crate::generated::{NodeKind, SyntaxKind};
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

/// One node: its kind, its subtree extent (self included), and the
/// half-open range of raw token indices it covers.
#[derive(Clone, Copy, Debug)]
struct Node {
    kind: NodeKind,
    extent: u32,
    first_token: RawIdx,
    end_token: RawIdx,
}

/// A parsed file: its nodes in postorder.
#[derive(Clone, Debug)]
pub struct SyntaxTree {
    nodes: Box<[Node]>,
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
    pub fn build<'a>(input: &'a ParserInput, body: impl FnOnce(&mut Marker<'_, 'a>)) -> Self {
        let mut builder = Builder {
            input,
            nodes: Vec::new(),
            position: SigIdx::new(0),
            slots: input.slots(),
            opened: 1,
            recoveries: 0,
            last_recovery_evidence: None,
            evidence: Vec::new(),
        };
        body(&mut Marker {
            builder: &mut builder,
            first: NodeIdx::new(0),
            start: SigIdx::new(0),
            id: 0,
            parent: 0,
            depth: 0,
            paren: None,
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
            extent: to_u32(builder.nodes.len() + 1),
            first_token: RawIdx::new(0),
            end_token: input.raw_len(),
        });
        Self {
            tree: SyntaxTree {
                nodes: builder.nodes.into_boxed_slice(),
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
    recoveries: usize,
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
pub(crate) struct RecoveryCheckpoint(usize);

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
pub struct Marker<'p, 'a> {
    builder: &'p mut Builder<'a>,
    /// Where the node's subtree begins among the completed nodes: every
    /// node completed since is inside it.
    first: NodeIdx,
    /// The significant position the node opens at.
    start: SigIdx,
    /// Identity, so a completed node can name the node that contained it.
    id: u32,
    parent: u32,
    /// How many open nodes enclose this one; the root is at 0.
    depth: u32,
    /// The innermost parenthesized construct still open around this node,
    /// by the significant position of its `(`.
    paren: Option<SigIdx>,
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
    pub fn token(&mut self) {
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
    pub fn start(&mut self) -> Marker<'_, 'a> {
        let first = NodeIdx::new(to_u32(self.builder.nodes.len()));
        let start = self.builder.position;
        let id = self.builder.open();
        Marker {
            builder: self.builder,
            first,
            start,
            id,
            parent: self.id,
            depth: self.depth + 1,
            paren: self.paren,
            closer: self.closer,
            enclosing_closer: self.enclosing_closer,
            completed: false,
        }
    }

    /// Open a child wrapping `completed` — which must have completed
    /// directly inside this node — and everything attached since; its kind
    /// is chosen when it completes.
    pub fn precede(&mut self, completed: CompletedMarker) -> Marker<'_, 'a> {
        assert_eq!(
            completed.parent, self.id,
            "a node is preceded only from the node that contained it"
        );
        let id = self.builder.open();
        Marker {
            builder: self.builder,
            first: completed.first,
            start: completed.start,
            id,
            parent: self.id,
            depth: self.depth + 1,
            paren: self.paren,
            closer: self.closer,
            enclosing_closer: self.enclosing_closer,
            completed: false,
        }
    }

    /// Close the node as `kind`; it must cover at least one token.
    pub fn complete(mut self, kind: NodeKind) -> CompletedMarker {
        let builder = &mut *self.builder;
        assert!(
            builder.position > self.start,
            "a node must cover at least one token"
        );
        builder.nodes.push(Node {
            kind,
            extent: to_u32(builder.nodes.len() - self.first.to_usize() + 1),
            first_token: builder.input.token(self.start),
            end_token: builder.input.token(builder.position - 1) + 1,
        });
        self.completed = true;
        CompletedMarker {
            first: self.first,
            start: self.start,
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

    /// Whether the next two tokens are `first` glued to `second`: a
    /// compound such as `->`.
    pub(crate) fn at_glued(&self, first: SyntaxKind, second: SyntaxKind) -> bool {
        self.at(first) && self.joint() && self.nth(1) == Some(second)
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

    /// Whether the next token is a `)` a parenthesized construct still open
    /// around this node can own. A mechanically paired `)` belongs here only
    /// when its opener is that construct or one outside it; an orphan `)`
    /// also belongs here, since recovery may have skipped the closer that
    /// pairing originally chose. One paired with a paren the parser already
    /// closed is garbage instead.
    pub(crate) fn closes_open_paren(&self) -> bool {
        let Some(paren) = self.paren else {
            return false;
        };
        self.at(SyntaxKind::RParen)
            && self
                .builder
                .input
                .partner(self.builder.position)
                .is_none_or(|partner| partner <= paren)
    }

    /// Whether the next token is the `)` owned by the innermost
    /// parenthesized construct the parser still has open: its mechanically
    /// paired closer, or an orphan available as a recovery closer. A `)`
    /// paired with an earlier opener belongs to an enclosing construct.
    pub(crate) fn owns_rparen(&self) -> bool {
        let Some(paren) = self.paren else {
            return false;
        };
        self.at(SyntaxKind::RParen)
            && self
                .builder
                .input
                .partner(self.builder.position)
                .is_none_or(|partner| partner == paren)
    }

    /// Mark this node as a bracket construct whose opener is its first
    /// token: it and the children opened from now on know whether the
    /// stream closes it.
    pub(crate) fn enter(&mut self) {
        self.enclosing_closer = self.closer.or(self.enclosing_closer);
        self.closer = self.builder.input.partner(self.start);
    }

    /// [Enter](Self::enter) a parenthesized construct whose `(` is its
    /// first token: children opened from now on also know it is open.
    pub(crate) fn enter_parens(&mut self) {
        self.enter();
        self.paren = Some(self.start);
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
pub struct CompletedMarker {
    /// Where the node's subtree begins among the completed nodes.
    first: NodeIdx,
    /// The significant position the node opened at.
    start: SigIdx,
    /// Identity of the node it completed inside.
    parent: u32,
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

    use sumi_lexer::lex;

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
}
