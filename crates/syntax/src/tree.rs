//! The syntax tree: nodes in preorder, each a kind, a subtree extent, and a half-open raw-token
//! range; text and trivia stay in the token buffers. `first_token` is non-decreasing across the
//! array, so the node covering a token is a binary search.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_text::TextRange;

use crate::ast::NodeKind;
use crate::grammar::{BRACKET_PAIRS, SyntaxKind, encloses_statements, opener, pair_index};
use crate::index::{NodeIdx, SigIdx};
use crate::input::{ParserInput, Slot};
use crate::parser::{
    ParseAnchor, ParseEvidence, ParseRecovery, ParseRecoveryKind, ParseViolation,
    ParseViolationKind, RawGap, RawTokenRange,
};

#[derive(Clone, Copy, Debug)]
struct Node {
    kind: NodeKind,
    has_error: bool,
    /// The parent's typed field this node fills, plus one; zero for none.
    field: u8,
    extent: u32,
    first_token: RawIdx,
    end_token: RawIdx,
}

const _: () = assert!(size_of::<Node>() == 16, "nodes stay sixteen bytes");

#[derive(Clone, Debug)]
pub struct SyntaxTree {
    nodes: Box<[Node]>,
}

impl SyntaxTree {
    #[expect(clippy::len_without_is_empty, reason = "a tree always has its root")]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn root(&self) -> NodeIdx {
        NodeIdx::new(0)
    }

    pub fn nodes(&self) -> impl DoubleEndedIterator<Item = NodeIdx> + ExactSizeIterator {
        NodeIdx::new(0).until(node_idx(self.nodes.len()))
    }

    pub fn kind(&self, index: NodeIdx) -> NodeKind {
        self.nodes[index.to_usize()].kind
    }

    /// Whether `index` is an `Error` node or the parser recovered anywhere in its subtree.
    /// Violations do not count: the syntax under them is complete.
    pub fn has_error(&self, index: NodeIdx) -> bool {
        self.nodes[index.to_usize()].has_error
    }

    /// `field` is the slot the typed views declare.
    pub fn child_in_field(&self, node: NodeIdx, field: u8) -> Option<NodeIdx> {
        self.children(node)
            .find(|child| self.nodes[child.to_usize()].field == field + 1)
    }

    pub fn first_token(&self, index: NodeIdx) -> RawIdx {
        self.nodes[index.to_usize()].first_token
    }

    /// Only the root can be empty, over an empty file.
    pub fn end_token(&self, index: NodeIdx) -> RawIdx {
        self.nodes[index.to_usize()].end_token
    }

    /// Counts `index` itself: the subtree is `index..index + subtree_len`.
    pub fn subtree_len(&self, index: NodeIdx) -> usize {
        self.nodes[index.to_usize()].extent as usize
    }

    /// `lexed` must be the file this tree was parsed from.
    pub fn byte_range(&self, index: NodeIdx, lexed: &LexedFile) -> TextRange {
        let node = &self.nodes[index.to_usize()];
        TextRange::new(
            lexed.boundary(node.first_token),
            lexed.boundary(node.end_token),
        )
    }

    /// `lexed` and `source` must be the file and text the tree was parsed from.
    pub fn reprint(&self, lexed: &LexedFile, source: &str) -> String {
        let mut out = String::with_capacity(source.len());
        let mut print = |from: RawIdx, to: RawIdx| {
            for token in from.until(to) {
                out.push_str(lexed.text(source, token));
            }
        };
        let mut open: Vec<(usize, RawIdx, RawIdx)> = Vec::new();
        for node in self.nodes() {
            while let Some(&(end, end_token, cursor)) = open.last()
                && node.to_usize() >= end
            {
                print(cursor, end_token);
                open.pop();
            }
            if let Some((_, _, cursor)) = open.last_mut() {
                print(*cursor, self.first_token(node));
                *cursor = self.end_token(node);
            }
            open.push((
                node.to_usize() + self.subtree_len(node),
                self.end_token(node),
                self.first_token(node),
            ));
        }
        while let Some((_, end_token, cursor)) = open.pop() {
            print(cursor, end_token);
        }
        out
    }

    pub fn children(&self, index: NodeIdx) -> impl Iterator<Item = NodeIdx> + '_ {
        let end = index.to_usize() + self.nodes[index.to_usize()].extent as usize;
        let mut child = index.to_usize() + 1;
        std::iter::from_fn(move || {
            (child < end).then(|| {
                let current = child;
                child += self.nodes[child].extent as usize;
                node_idx(current)
            })
        })
    }

    /// The innermost node whose range spans `token`, which must lie in the file; trivia resolves to
    /// the node around it, at worst the root.
    #[inline]
    pub fn covering(&self, token: RawIdx) -> NodeIdx {
        assert!(
            token < self.end_token(self.root()),
            "token must be within the file"
        );
        let until = self.nodes.partition_point(|node| node.first_token <= token);
        (0..until)
            .rfind(|&index| token < self.nodes[index].end_token)
            .map(node_idx)
            .expect("the root covers every token in the file")
    }
}

#[derive(Clone, Debug)]
pub struct Parse {
    input: ParserInput,
    tree: SyntaxTree,
    evidence: Box<[ParseEvidence]>,
}

impl Parse {
    /// `body` runs inside the root and must attach every significant token.
    pub(crate) fn build(
        input: ParserInput,
        body: impl for<'a> FnOnce(&mut Marker<'_, 'a>),
    ) -> Self {
        let mut builder = Builder {
            input: &input,
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
            // The root never completes; `build` closes it below.
            completed: true,
        });
        assert_eq!(
            builder.position,
            input.end(),
            "every significant token must be consumed"
        );
        builder.nodes.push(Node {
            kind: NodeKind::SourceFile,
            has_error: builder.recoveries > 0 || builder.error_nodes > 0,
            field: 0,
            extent: to_u32(builder.nodes.len() + 1),
            first_token: RawIdx::new(0),
            end_token: input.raw_len(),
        });
        let Builder {
            nodes, evidence, ..
        } = builder;
        Self {
            input,
            tree: SyntaxTree {
                nodes: preorder(&nodes),
            },
            evidence: evidence.into_iter().map(EvidenceBuilder::finish).collect(),
        }
    }

    pub fn input(&self) -> &ParserInput {
        &self.input
    }

    pub fn tree(&self) -> &SyntaxTree {
        &self.tree
    }

    /// In observation order; several facts may share an anchor.
    pub fn evidence(&self) -> &[ParseEvidence] {
        &self.evidence
    }
}

struct Builder<'a> {
    input: &'a ParserInput,
    /// In completion order: children before parents.
    nodes: Vec<Node>,
    position: SigIdx,
    /// The input's slots up to the horizon; lookahead reads only these.
    slots: &'a [Slot],
    opened: u32,
    recoveries: u32,
    /// Apart from `recoveries`: a violation makes an `Error` node without one.
    error_nodes: u32,
    last_recovery_evidence: Option<usize>,
    evidence: Vec<EvidenceBuilder>,
}

impl Builder<'_> {
    fn open(&mut self) -> u32 {
        let id = self.opened;
        self.opened += 1;
        id
    }

    fn raw_range(&self, start: SigIdx, end: SigIdx) -> RawTokenRange {
        assert!(start < end && end <= self.input.end());
        RawTokenRange::new(self.input.token(start), self.input.token(end - 1) + 1)
    }

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

/// Dropping a marker before it completes panics.
#[must_use = "a started node must be completed"]
pub(crate) struct Marker<'p, 'a> {
    builder: &'p mut Builder<'a>,
    /// The subtree's start in `builder.nodes`; every node completed since is inside it.
    first: NodeIdx,
    start: SigIdx,
    /// `builder.recoveries` when the node opened; any more at completion happened inside it.
    recoveries: u32,
    /// `builder.error_nodes` when the node opened, likewise.
    error_nodes: u32,
    id: u32,
    parent: u32,
    depth: u32,
    /// Per bracket pair, the opener of the innermost construct entered around this node.
    open: [Option<SigIdx>; BRACKET_PAIRS.len()],
    /// The stream's closer for the innermost construct entered around this node; `None` when the
    /// stream closes none.
    closer: Option<SigIdx>,
    /// The nearest closer outside `closer`. Entering an unclosed construct keeps it, so recovery
    /// still has a limit.
    enclosing_closer: Option<SigIdx>,
    completed: bool,
}

impl<'a> Marker<'_, 'a> {
    pub(crate) fn token(&mut self) {
        assert!(
            self.builder.position.to_usize() < self.builder.slots.len(),
            "token past the input horizon"
        );
        self.builder.position += 1;
    }

    /// `token`, then through the partner when the next token opens a matched pair.
    pub(crate) fn group(&mut self) {
        let index = self.builder.position;
        self.token();
        if let Some(partner) = self.builder.input.partner(index)
            && partner > index
        {
            self.builder.position = partner + 1;
        }
    }

    /// `group` only when the pair closes before the nearest parser-owned closer, or, with none
    /// known, spans no boundary: recovery must not cross either.
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

    /// Open a child wrapping `completed`, which must be a direct child of this node, and everything
    /// attached since.
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

    /// `completed` must be a direct child; `field` is the slot the typed views declare.
    pub(crate) fn field(&mut self, completed: &CompletedMarker, field: u8) {
        assert_eq!(
            completed.parent, self.id,
            "a field is assigned only from the node that contains it"
        );
        self.set_field(completed.node, field);
    }

    /// `completed` must be a direct child.
    pub(crate) fn completed_node(&self, completed: &CompletedMarker) -> NodeIdx {
        assert_eq!(
            completed.parent, self.id,
            "a completed node belongs to its containing node"
        );
        completed.node
    }

    /// `node` must be the child this marker wrapped with `precede`.
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
        assert_eq!(child.field, 0, "a node receives its field only once");
        child.field = field
            .checked_add(1)
            .expect("a typed field index fits below 255");
    }

    /// The node must cover at least one token.
    #[inline]
    pub(crate) fn complete(mut self, kind: NodeKind) -> CompletedMarker {
        let builder = &mut *self.builder;
        assert!(
            builder.position > self.start,
            "a node must cover at least one token"
        );
        let is_error = kind == NodeKind::Error;
        let has_error = is_error
            || builder.recoveries > self.recoveries
            || builder.error_nodes > self.error_nodes;
        builder.error_nodes += u32::from(is_error);
        let first_token = builder.input.token(self.start);
        let end_token = builder.input.token(builder.position - 1) + 1;
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

    pub(crate) fn depth(&self) -> u32 {
        self.depth
    }

    pub(crate) fn current(&self) -> Option<SyntaxKind> {
        self.nth(0)
    }

    /// The token `n` past the next one; `None` at or past the horizon.
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

    pub(crate) fn joint(&self) -> bool {
        self.nth_joint(0)
    }

    /// Whether token `n` past the next one is glued to the one after it.
    pub(crate) fn nth_joint(&self, n: usize) -> bool {
        self.builder
            .position
            .checked_add(n as u32)
            .is_some_and(|index| {
                index.to_usize() < self.builder.input.len() && self.builder.input.is_joint(index)
            })
    }

    pub(crate) fn previous(&self) -> Option<SyntaxKind> {
        let previous = self.builder.position.checked_sub(1)?;
        self.builder.input.get(previous)
    }

    /// Read on the whole input, not the horizon: no token of the shape can start an item.
    pub(crate) fn at_headless_signature(&self) -> bool {
        let position = self.builder.position;
        position.to_usize() < self.builder.input.len()
            && self.builder.input.headless_signature_at(position)
    }

    pub(crate) fn joint_before(&self) -> bool {
        self.builder
            .position
            .checked_sub(1)
            .is_some_and(|previous| self.builder.input.is_joint(previous))
    }

    pub(crate) fn newline(&self) -> bool {
        self.nth_newline(0)
    }

    pub(crate) fn in_matched_delimiters(&self) -> bool {
        let index = self.builder.position;
        index.to_usize() < self.builder.input.len()
            && self.builder.input.in_matched_delimiters(index)
    }

    pub(crate) fn nth_newline(&self, n: usize) -> bool {
        self.builder
            .position
            .checked_add(n as u32)
            .is_some_and(|index| {
                index.to_usize() < self.builder.input.len()
                    && self.builder.input.newline_before(index)
            })
    }

    pub(crate) fn boundary(&self) -> bool {
        self.nth_boundary(0)
    }

    pub(crate) fn nth_boundary(&self, n: usize) -> bool {
        self.builder
            .position
            .checked_add(n as u32)
            .is_some_and(|index| {
                index.to_usize() < self.builder.input.len()
                    && self.builder.input.boundary_before(index)
            })
    }

    /// Where this holds, parsing an expression takes at least one token.
    pub(crate) fn starts_expression(&self) -> bool {
        self.current()
            .is_some_and(crate::grammar::starts_expression)
    }

    pub(crate) fn partnered(&self) -> bool {
        let position = self.builder.position;
        position.to_usize() < self.builder.input.len()
            && self.builder.input.partner(position).is_some()
    }

    /// The offset from the next token of the partner of token `n` past it; `None` unless that
    /// partner lies ahead.
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

    /// Whether the next token is this construct's closer: paired with its opener, or an orphan,
    /// since recovery may have skipped the paired one.
    pub(crate) fn owns_closer(&self) -> bool {
        let closer = self
            .builder
            .input
            .get(self.start)
            .and_then(crate::grammar::closer)
            .unwrap_or_else(|| unreachable!("only a bracket construct owns a closer"));
        self.at(closer)
            && self
                .builder
                .input
                .partner(self.builder.position)
                .is_none_or(|partner| partner == self.start)
    }

    /// Whether the next token is a `closer` some construct still open around this node can own:
    /// paired with its opener or one outside, or an orphan.
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

    /// `closes_open` for a pair that does not enclose statements.
    pub(crate) fn closes_open_bracket(&self) -> bool {
        self.current().is_some_and(|kind| {
            opener(kind).is_some_and(|opener| !encloses_statements(opener))
                && self.closes_open(kind)
        })
    }

    /// Mark this node a bracket construct; its first token must be the opener.
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

    pub(crate) fn closed(&self) -> bool {
        self.closer.is_some()
    }

    pub(crate) fn closer_ahead(&self) -> bool {
        self.closer
            .is_some_and(|closer| closer > self.builder.position)
    }

    fn next_parser_closer(&self) -> Option<SigIdx> {
        [self.closer, self.enclosing_closer]
            .into_iter()
            .flatten()
            .filter(|&closer| closer >= self.builder.position)
            .min()
    }

    pub(crate) fn item_anchor_count(&self) -> usize {
        self.builder.input.item_anchors().len()
    }

    /// Past the last anchor, the end of input.
    pub(crate) fn item_anchor(&self, index: usize) -> SigIdx {
        self.builder
            .input
            .item_anchors()
            .get(index)
            .map_or(self.builder.input.end(), |&start| start)
    }

    /// Move the horizon; `limit` is never behind the cursor or past the input.
    pub(crate) fn set_limit(&mut self, limit: SigIdx) {
        debug_assert!(self.builder.position <= limit);
        self.builder.slots = &self.builder.input.slots()[..limit.to_usize()];
    }

    /// Attach `kind` unless a statement boundary precedes it; otherwise record it missing.
    pub(crate) fn expect(&mut self, kind: SyntaxKind) -> bool {
        if self.at(kind) && !self.boundary() {
            self.token();
            true
        } else {
            self.missing(ParseRecoveryKind::Token(kind));
            false
        }
    }

    pub(crate) fn recovery_checkpoint(&self) -> RecoveryCheckpoint {
        RecoveryCheckpoint(self.builder.recoveries)
    }

    pub(crate) fn recovered_since(&self, checkpoint: RecoveryCheckpoint) -> bool {
        self.builder.recoveries > checkpoint.0
    }

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

    pub(crate) fn missing(&mut self, kind: ParseRecoveryKind) -> RecoveryHandle {
        let anchor = ParseAnchor::Gap(self.builder.raw_gap(self.builder.position));
        self.record_recovery(kind, anchor)
    }

    /// This node's first token must be the opener.
    pub(crate) fn missing_closer(&mut self) -> RecoveryHandle {
        let kind = self
            .builder
            .input
            .get(self.start)
            .and_then(crate::grammar::closer)
            .unwrap_or_else(|| unreachable!("a missing closer belongs to a bracket node"));
        let opener = self.builder.raw_range(self.start, self.start + 1);
        self.missing(ParseRecoveryKind::Closer { kind, opener })
    }

    pub(crate) fn recover_tokens(
        &mut self,
        kind: ParseRecoveryKind,
        width: usize,
    ) -> RecoveryHandle {
        let range = self.raw_token_range(width);
        self.recover_range(kind, range)
    }

    pub(crate) fn recover_range(
        &mut self,
        kind: ParseRecoveryKind,
        range: RawTokenRange,
    ) -> RecoveryHandle {
        let anchor = ParseAnchor::Tokens(range);
        self.record_recovery(kind, anchor)
    }

    pub(crate) fn violation(&mut self, kind: ParseViolationKind, width: usize) {
        let range = self.raw_token_range(width);
        self.builder
            .evidence
            .push(EvidenceBuilder::Violation(ParseViolation { kind, range }));
    }

    pub(crate) fn skipped(&mut self, recovery: RecoveryHandle, range: RawTokenRange) {
        let EvidenceBuilder::Recovery { skipped, .. } = &mut self.builder.evidence[recovery.0]
        else {
            unreachable!("a recovery handle names recovery evidence")
        };
        skipped.push(range);
    }

    pub(crate) fn covered_range(&self) -> RawTokenRange {
        self.builder.raw_range(self.start, self.builder.position)
    }

    /// `width` counts significant tokens from the cursor.
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
        // A panic while unwinding aborts and loses the original.
        if !self.completed && !std::thread::panicking() {
            panic!("a started node was dropped without being completed");
        }
    }
}

pub(crate) struct CompletedMarker {
    node: NodeIdx,
    first: NodeIdx,
    start: SigIdx,
    recoveries: u32,
    error_nodes: u32,
    parent: u32,
}

#[inline]
fn to_u32(count: usize) -> u32 {
    u32::try_from(count).expect("count fits in u32")
}

/// The array grew through `to_u32`, so the cast cannot truncate.
#[inline]
fn node_idx(index: usize) -> NodeIdx {
    NodeIdx::new(index as u32)
}

/// `completed` lies children before parents, root last.
fn preorder(completed: &[Node]) -> Box<[Node]> {
    let root = completed.len() - 1;
    let mut nodes = completed.to_vec();
    nodes[0] = completed[root];
    let mut open: Vec<(usize, usize)> = vec![(completed.len(), root)];
    for index in (0..root).rev() {
        let node = completed[index];
        let extent = node.extent as usize;
        while let Some(&(_, 0)) = open.last() {
            open.pop();
        }
        let (end, remaining) = open
            .last_mut()
            .expect("every node but the root has a parent");
        *end -= extent;
        *remaining -= extent;
        let slot = *end;
        nodes[slot] = node;
        if extent > 1 {
            open.push((slot + extent, extent - 1));
        }
    }
    nodes.into_boxed_slice()
}

#[cfg(test)]
mod tests {
    use super::*;

    use sumi_lexer::{LexedFile, lex};

    use crate::NodeKind::*;

    #[test]
    fn parser_evidence_retains_same_position_facts() {
        let lexed = lex("x").expect("test source fits in u32");
        let parse = Parse::build(ParserInput::new(&lexed), |root| {
            let checkpoint = root.recovery_checkpoint();
            root.violation(ParseViolationKind::SpacedPrefixOperator, 1);
            assert!(!root.recovered_since(checkpoint));

            root.recover_tokens(ParseRecoveryKind::Expression, 1);
            assert!(root.recovered_since(checkpoint));
            root.token();
        });

        let [violation, recovery] = parse.evidence() else {
            panic!("both same-position facts must be retained")
        };
        assert!(matches!(violation, ParseEvidence::Violation(_)));
        assert!(matches!(recovery, ParseEvidence::Recovery(_)));
    }

    fn node(
        parent: &mut Marker<'_, '_>,
        kind: NodeKind,
        body: impl FnOnce(&mut Marker<'_, '_>),
    ) -> CompletedMarker {
        let mut child = parent.start();
        body(&mut child);
        child.complete(kind)
    }

    fn leaf(parent: &mut Marker<'_, '_>, kind: NodeKind) -> CompletedMarker {
        node(parent, kind, |m| m.token())
    }

    fn tokens(marker: &mut Marker<'_, '_>, count: usize) {
        for _ in 0..count {
            marker.token();
        }
    }

    fn dump(source: &str, build: impl FnOnce(&mut Marker<'_, '_>)) -> Vec<String> {
        let lexed = lex(source).expect("test sources fit in u32");
        let parse = Parse::build(ParserInput::new(&lexed), build);
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
                    tokens(b, 3);
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
                m.token();
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
        check(
            "a + b",
            |b| {
                let lhs = leaf(b, NameRef);
                b.token();
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
                node(b, Error, |b| tokens(b, 2));
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
                    m.token();
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
                    tokens(b, 2);
                    node(b, ParamList, |b| {
                        b.token();
                        node(b, Param, |b| {
                            tokens(b, 2);
                            leaf(b, TypeRef);
                        });
                        b.token();
                    });
                    tokens(b, 2);
                    leaf(b, TypeRef);
                    node(b, Block, |b| {
                        b.token();
                        leaf(b, NameRef);
                        b.token();
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
                    tokens(b, 3);
                    node(b, PrefixExpr, |b| {
                        b.token();
                        leaf(b, LiteralExpr);
                    });
                });
                node(b, AssignStmt, |b| {
                    leaf(b, NameRef);
                    b.token();
                    leaf(b, LiteralExpr);
                });
                node(b, DiscardStmt, |b| {
                    tokens(b, 2);
                    let callee = leaf(b, NameRef);
                    let mut m = b.precede(callee);
                    node(&mut m, ArgList, |b| {
                        b.token();
                        node(b, ParenExpr, |b| {
                            b.token();
                            leaf(b, NameRef);
                            b.token();
                        });
                        b.token();
                    });
                    m.complete(CallExpr);
                });
                let callee = leaf(b, NameRef);
                let mut m = b.precede(callee);
                node(&mut m, ArgList, |b| {
                    b.token();
                    leaf(b, NameRef);
                    b.token();
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
                    b.token();
                    leaf(b, NameRef);
                    node(b, Block, |b| {
                        b.token();
                        leaf(b, NameRef);
                        b.token();
                    });
                    b.token();
                    node(b, Block, |b| {
                        b.token();
                        leaf(b, NameRef);
                        b.token();
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
        let parse = Parse::build(ParserInput::new(&lexed), |b| {
            node(b, LetStmt, |b| {
                tokens(b, 3);
                leaf(b, LiteralExpr);
            });
            leaf(b, NameRef);
        });
        let tree = parse.tree();
        assert_eq!(tree.kind(tree.root()), SourceFile);

        let kind_at = |token| tree.kind(tree.covering(RawIdx::new(token)));
        assert_eq!(kind_at(0), LetStmt);
        assert_eq!(kind_at(1), LetStmt);
        assert_eq!(kind_at(6), LiteralExpr);
        assert_eq!(kind_at(7), SourceFile);
        assert_eq!(kind_at(8), NameRef);
    }

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
            tokens(&mut rest, 2);
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
    fn edge_and_interior_trivia_answer_the_spanning_node() {
        let source = "let x = 1 // c";
        let lexed = lex(source).expect("test sources fit in u32");
        let built = Parse::build(ParserInput::new(&lexed), |root| {
            node(root, LetStmt, |stmt| {
                stmt.token();
                node(stmt, NameRef, |name| name.token());
                stmt.token();
                node(stmt, LiteralExpr, |literal| literal.token());
            });
        });
        let tree = built.tree();
        let kind_at = |token| tree.kind(tree.covering(RawIdx::new(token)));
        assert_eq!(kind_at(1), LetStmt);
        assert_eq!(kind_at(2), NameRef);
        assert_eq!(kind_at(7), SourceFile);
        assert_eq!(kind_at(8), SourceFile);
    }

    #[test]
    #[should_panic(expected = "token must be within the file")]
    fn covering_a_token_past_the_file_panics() {
        let source = "x";
        let lexed = lex(source).expect("test sources fit in u32");
        let built = Parse::build(ParserInput::new(&lexed), |root| {
            node(root, NameRef, |name| name.token());
        });
        built.tree().covering(RawIdx::new(1));
    }

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

        let mut previous_end = first;
        for child in tree.children(node) {
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
