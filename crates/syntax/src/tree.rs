//! The syntax tree: flat, preorder, token-anchored.
//!
//! A [`SyntaxTree`] stores structure only. Each node is a kind, a subtree
//! extent, and a half-open range of raw token indices; text, spans, and
//! trivia stay in the token buffers, so the tree holds no second copy of the
//! source. Nodes lie in preorder — node `index`'s subtree occupies
//! `index..index + extent` — so children are found by walking extents and
//! dumps read in source order. Node 0 is the root.
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
//! token past the end of input or tokens left over.
//!
//! Internally the build records nodes as they complete, children before
//! parents, and permutes them into preorder once the root closes. That is
//! what lets a parser choose a node's kind after its children exist, and
//! wrap a node it has already completed: a wrapper's subtree is simply
//! everything completed since the wrapped node began — how a Pratt parser
//! wraps an already-parsed left operand into a binary expression.

use crate::input::ParserInput;
use crate::kind::{NodeKind, SyntaxKind};
use crate::parser::{ParseError, ParseErrorKind};

/// One node: its kind, its subtree extent (self included), and the
/// half-open range of raw token indices it covers.
#[derive(Clone, Copy, Debug)]
struct Node {
    kind: NodeKind,
    extent: u32,
    first_token: u32,
    end_token: u32,
}

/// A parsed file: its nodes in preorder.
#[derive(Clone, Debug)]
pub struct SyntaxTree {
    nodes: Box<[Node]>,
}

impl SyntaxTree {
    /// The number of nodes: at least one, the root at index 0.
    #[expect(clippy::len_without_is_empty, reason = "a tree always has its root")]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn kind(&self, index: usize) -> NodeKind {
        self.nodes[index].kind
    }

    /// The raw index of the first token node `index` covers.
    pub fn first_token(&self, index: usize) -> u32 {
        self.nodes[index].first_token
    }

    /// One past the raw index of the last token node `index` covers. Only
    /// the root can be empty, over an empty file.
    pub fn end_token(&self, index: usize) -> u32 {
        self.nodes[index].end_token
    }

    /// The direct children of node `index`, in source order.
    pub fn children(&self, index: usize) -> impl Iterator<Item = usize> + '_ {
        let end = index + self.nodes[index].extent as usize;
        let mut child = index + 1;
        std::iter::from_fn(move || {
            (child < end).then(|| {
                let current = child;
                child += self.nodes[child].extent as usize;
                current
            })
        })
    }
}

/// A parsed file: the tree, and the errors met while building it.
#[derive(Clone, Debug)]
pub struct Parse {
    tree: SyntaxTree,
    errors: Box<[ParseError]>,
}

impl Parse {
    /// Build a tree over the significant tokens of `input`, in source
    /// order: open the root, run `body` inside it, and close it. `body`
    /// must attach every significant token.
    pub fn build<'a>(input: &'a ParserInput, body: impl FnOnce(&mut Marker<'_, 'a>)) -> Self {
        let mut builder = Builder {
            input,
            nodes: Vec::new(),
            position: 0,
            opened: 1,
            errors: Vec::new(),
        };
        body(&mut Marker {
            builder: &mut builder,
            first: 0,
            start: 0,
            id: 0,
            parent: 0,
            depth: 0,
            paren: None,
            closer: None,
            // Closed here once `body` returns, never by `complete`.
            completed: true,
        });
        assert_eq!(
            builder.position,
            input.len(),
            "every significant token must be consumed"
        );
        // The root closes last, over every token: edge trivia included,
        // keeping the tree lossless end to end. It alone may be empty, over
        // an empty file.
        builder.nodes.push(Node {
            kind: NodeKind::SourceFile,
            extent: to_u32(builder.nodes.len() + 1),
            first_token: 0,
            end_token: input.raw_len(),
        });
        Self {
            tree: SyntaxTree {
                nodes: preorder(builder.nodes),
            },
            errors: builder.errors.into_boxed_slice(),
        }
    }

    pub fn tree(&self) -> &SyntaxTree {
        &self.tree
    }

    /// The errors in source order, at most one per position.
    pub fn errors(&self) -> &[ParseError] {
        &self.errors
    }
}

/// A build in progress.
struct Builder<'a> {
    input: &'a ParserInput,
    /// Completed nodes, children before parents.
    nodes: Vec<Node>,
    /// The next significant token to attach.
    position: usize,
    /// Nodes opened so far, numbering the next one; the root is 0.
    opened: u32,
    errors: Vec<ParseError>,
}

impl Builder<'_> {
    fn open(&mut self) -> u32 {
        let id = self.opened;
        self.opened += 1;
        id
    }

    /// The raw index of the next significant token, or one past the last
    /// raw token at end of input.
    fn raw_position(&self) -> u32 {
        if self.position < self.input.len() {
            self.input.token(self.position)
        } else {
            self.input.raw_len()
        }
    }
}

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
/// partners) at the cursor, and error recording, so one cursor serves
/// building and reading alike.
///
/// Completing the outer of two open nodes is a borrow error:
///
/// ```compile_fail,E0505
/// use sumi_lexer::lex;
/// use sumi_syntax::{NodeKind, Parse, ParserInput, cook};
///
/// let input = ParserInput::new(&cook("x y", &lex("x y").unwrap()));
/// Parse::build(&input, |root| {
///     let mut outer = root.start();
///     outer.token();
///     let mut inner = outer.start();
///     inner.token();
///     outer.complete(NodeKind::LetStmt); // `outer` is borrowed by `inner`
///     inner.complete(NodeKind::NameExpr);
/// });
/// ```
///
/// So is completing the root, which is only ever lent:
///
/// ```compile_fail,E0507
/// use sumi_lexer::lex;
/// use sumi_syntax::{NodeKind, Parse, ParserInput, cook};
///
/// let input = ParserInput::new(&cook("x", &lex("x").unwrap()));
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
    first: usize,
    /// The significant position the node opens at.
    start: usize,
    /// Identity, so a completed node can name the node that contained it.
    id: u32,
    parent: u32,
    /// How many open nodes enclose this one; the root is at 0.
    depth: u32,
    /// The innermost parenthesized construct still open around this node,
    /// by the significant position of its `(`.
    paren: Option<usize>,
    /// The closer the stream pairs with the innermost bracket construct
    /// entered around this node — this node itself, once it has entered
    /// one — by significant position; `None` when the stream closes none.
    /// A closed construct owns everything up to its closer, so a `fn`
    /// inside it is garbage there, not the next item.
    closer: Option<usize>,
    completed: bool,
}

impl<'a> Marker<'_, 'a> {
    /// Attach the next significant token to this node.
    pub fn token(&mut self) {
        assert!(
            self.builder.position < self.builder.input.len(),
            "token past end of input"
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

    /// Open a child at the next token; its kind is chosen when it
    /// completes.
    pub fn start(&mut self) -> Marker<'_, 'a> {
        let first = self.builder.nodes.len();
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
            extent: to_u32(builder.nodes.len() - self.first + 1),
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

    /// The kind of the next significant token, or `None` at end of input.
    pub(crate) fn current(&self) -> Option<SyntaxKind> {
        self.nth(0)
    }

    /// The kind of the significant token `n` past the next one.
    pub(crate) fn nth(&self, n: usize) -> Option<SyntaxKind> {
        let index = self.builder.position.checked_add(n)?;
        self.builder.input.get(index)
    }

    pub(crate) fn at(&self, kind: SyntaxKind) -> bool {
        self.current() == Some(kind)
    }

    /// Whether the next two tokens are `first` glued to `second`: a
    /// compound operator such as `==` or `->`.
    pub(crate) fn at_glued(&self, first: SyntaxKind, second: SyntaxKind) -> bool {
        self.nth_glued(0, first, second)
    }

    /// Whether the significant tokens `n` and `n + 1` past the next one are
    /// `first` glued to `second`.
    pub(crate) fn nth_glued(&self, n: usize, first: SyntaxKind, second: SyntaxKind) -> bool {
        self.nth(n) == Some(first) && self.nth_joint(n) && self.nth(n + 1) == Some(second)
    }

    /// Whether the next token is glued to the one after it.
    pub(crate) fn joint(&self) -> bool {
        self.nth_joint(0)
    }

    /// Whether the significant token `n` past the next one is glued to the
    /// one after it.
    pub(crate) fn nth_joint(&self, n: usize) -> bool {
        self.builder.position.checked_add(n).is_some_and(|index| {
            index < self.builder.input.len() && self.builder.input.is_joint(index)
        })
    }

    /// Whether the next token is glued to the previous one.
    pub(crate) fn joint_before(&self) -> bool {
        self.builder.position > 0 && self.builder.input.is_joint(self.builder.position - 1)
    }

    /// Whether a line break precedes the next token.
    pub(crate) fn newline(&self) -> bool {
        self.nth_newline(0)
    }

    /// Whether a line break precedes the significant token `n` past the
    /// next one.
    pub(crate) fn nth_newline(&self, n: usize) -> bool {
        self.builder.position.checked_add(n).is_some_and(|index| {
            index < self.builder.input.len() && self.builder.input.newline_before(index)
        })
    }

    /// Whether a statement boundary precedes the next token.
    pub(crate) fn boundary(&self) -> bool {
        let index = self.builder.position;
        index < self.builder.input.len() && self.builder.input.boundary_before(index)
    }

    /// Whether the next token is a bracket the stream judged a stray: no
    /// bracket at all, garbage where it stands.
    pub(crate) fn stray(&self) -> bool {
        let position = self.builder.position;
        position < self.builder.input.len() && self.builder.input.is_stray(position)
    }

    /// Whether the next token begins an expression: one of the kinds that
    /// can, and not a bracket the stream judged a stray. Whatever parses an
    /// expression where this holds takes at least that token.
    pub(crate) fn starts_expression(&self) -> bool {
        self.current().is_some_and(SyntaxKind::starts_expression) && !self.stray()
    }

    /// Whether the next token is a bracket the stream pairs with another,
    /// ahead or behind.
    pub(crate) fn partnered(&self) -> bool {
        let position = self.builder.position;
        position < self.builder.input.len() && self.builder.input.partner(position).is_some()
    }

    /// The offset from the next token of the bracket matching the
    /// significant token `n` past it, when that bracket lies ahead.
    pub(crate) fn nth_partner(&self, n: usize) -> Option<usize> {
        let index = self.builder.position.checked_add(n)?;
        if index >= self.builder.input.len() {
            return None;
        }
        self.builder
            .input
            .partner(index)?
            .checked_sub(self.builder.position)
    }

    /// Whether the next token is a `)` closing a parenthesized construct
    /// still open around this node — the innermost, or one outside it — as
    /// the stream pairs brackets. A `)` the stream pairs with a paren the
    /// parser has already closed is garbage here: nothing is waiting for
    /// it, so it is not a closer to yield to.
    pub(crate) fn closes_open_paren(&self) -> bool {
        let Some(paren) = self.paren else {
            return false;
        };
        self.at(SyntaxKind::RParen)
            && self
                .builder
                .input
                .partner(self.builder.position)
                .is_some_and(|partner| partner <= paren)
    }

    /// Mark this node as a bracket construct whose opener is its first
    /// token: it and the children opened from now on know whether the
    /// stream closes it.
    pub(crate) fn enter(&mut self) {
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

    /// Whether the next token is a `fn` beginning the next item: one that
    /// no bracket construct the stream closes still encloses — its closer,
    /// if it had one, lies behind, taken by something unclosed inside it.
    /// Recovery never takes such a `fn`; whatever lost its closer ends
    /// there instead.
    pub(crate) fn at_item(&self) -> bool {
        !self.closer_ahead() && self.at(SyntaxKind::FnKw)
    }

    /// Attach the next token if it is `kind` and no statement boundary
    /// precedes it; otherwise record that `kind` was expected and leave the
    /// token where it is.
    pub(crate) fn expect(&mut self, kind: SyntaxKind) -> bool {
        if self.at(kind) && !self.boundary() {
            self.token();
            true
        } else {
            self.error(ParseErrorKind::Expected(kind));
            false
        }
    }

    /// Record `kind` at the next token, or at end of input. Nothing is
    /// recorded at a token with no meaning — a [`SyntaxKind::Error`], which
    /// the lexer or cook reported — since a structural complaint about it
    /// adds nothing; a malformed literal keeps its kind and is ordinary
    /// here, its two problems being independent. Nor is anything recorded
    /// at a position that has an error already: one diagnostic per position
    /// keeps a single mistake from cascading.
    /// How many errors have been reported so far.
    pub(crate) fn reported(&self) -> usize {
        self.builder.errors.len()
    }

    /// Whether recovery has reported anything since there were `reported`
    /// errors: something missing, or a token that could not be taken. A
    /// rule broken by syntax taken as it was does not count.
    pub(crate) fn reported_since(&self, reported: usize) -> bool {
        self.builder.errors[reported..]
            .iter()
            .any(|error| error.kind.is_recovery())
    }

    pub(crate) fn error(&mut self, kind: ParseErrorKind) {
        if self.at(SyntaxKind::Error) {
            return;
        }
        let token = self.builder.raw_position();
        if self
            .builder
            .errors
            .last()
            .is_some_and(|last| last.token == token)
        {
            return;
        }
        self.builder.errors.push(ParseError { token, kind });
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
    first: usize,
    /// The significant position the node opened at.
    start: usize,
    /// Identity of the node it completed inside.
    parent: u32,
}

/// Permute `nodes` from completion order, children before parents with the
/// root last, into preorder.
fn preorder(nodes: Vec<Node>) -> Box<[Node]> {
    let root = nodes.len() - 1;
    let mut ordered = vec![nodes[root]; nodes.len()];
    // Nodes still to place: index in `nodes`, slot in `ordered`.
    let mut pending = vec![(root, 0usize)];
    while let Some((node, slot)) = pending.pop() {
        ordered[slot] = nodes[node];
        let extent = nodes[node].extent as usize;
        // A node's children lie just below it, last child first, each
        // ending where the previous one begins; they take the slots after
        // the node, handed out from the end of its range.
        let bottom = node + 1 - extent;
        let (mut child, mut end) = (node, slot + extent);
        while child > bottom {
            child -= 1;
            let size = nodes[child].extent as usize;
            end -= size;
            pending.push((child, end));
            child -= size - 1;
        }
    }
    ordered.into_boxed_slice()
}

/// Node counts are stored as `u32`; nothing bounds them by the source
/// length the way token indices are, so the narrowing is checked.
fn to_u32(count: usize) -> u32 {
    u32::try_from(count).expect("count fits in u32")
}
