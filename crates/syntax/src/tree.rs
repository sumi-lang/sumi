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
//! Trees come only from [`SyntaxTree::build`], which lends the root as a
//! [`Marker`]: an open node. Starting a child reborrows the parent marker
//! for as long as the child is open, so the borrow checker holds the stack
//! of open nodes. A parent cannot take a token, start a sibling, or
//! complete while a child is open; the root, only ever lent, cannot
//! complete at all; and completing a marker is the one way to close its
//! node. A [`CompletedMarker`] is plain data — holding one borrows nothing —
//! and is wrapped after the fact from the marker that contained it. What
//! types cannot express stays a run-time check, raised where the parser
//! went wrong: a node is preceded only from the node that contained it,
//! every node covers at least one token, a marker dropped uncompleted
//! panics where it drops, and `build` rejects a token past the end of
//! input or tokens left over.
//!
//! Internally the build records nodes as they complete, children before
//! parents, and permutes them into preorder once the root closes. That is
//! what lets a parser choose a node's kind after its children exist, and
//! wrap a node it has already completed: a wrapper's subtree is simply
//! everything completed since the wrapped node began — how a Pratt parser
//! wraps an already-parsed left operand into a binary expression.

use crate::input::ParserInput;
use crate::kind::NodeKind;

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
    /// Build a tree over the significant tokens of `input`, in source
    /// order: open the root, run `body` inside it, and close it. `body`
    /// must attach every significant token.
    pub fn build<'a>(input: &'a ParserInput, body: impl FnOnce(&mut Marker<'_, 'a>)) -> Self {
        let mut builder = Builder {
            input,
            nodes: Vec::new(),
            position: 0,
            opened: 1,
        };
        body(&mut Marker {
            builder: &mut builder,
            first: 0,
            start: 0,
            id: 0,
            parent: 0,
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
            nodes: preorder(builder.nodes),
        }
    }

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

/// A build in progress.
struct Builder<'a> {
    input: &'a ParserInput,
    /// Completed nodes, children before parents.
    nodes: Vec<Node>,
    /// The next significant token to attach.
    position: usize,
    /// Nodes opened so far, numbering the next one; the root is 0.
    opened: u32,
}

impl Builder<'_> {
    fn open(&mut self) -> u32 {
        let id = self.opened;
        self.opened += 1;
        id
    }
}

/// An open node: the root, lent by [`SyntaxTree::build`], or a child from
/// [`start`](Self::start) or [`precede`](Self::precede). Tokens attach to
/// the innermost open node. A child reborrows its parent for as long as it
/// is open, so the parent is untouchable until the child completes: the
/// stack of open nodes is a chain of borrows on the parser's own stack.
/// Completing a marker is the only way to close its node; dropping it
/// instead is a parser bug and panics on the spot.
///
/// Completing the outer of two open nodes is a borrow error:
///
/// ```compile_fail,E0505
/// use sumi_lexer::lex;
/// use sumi_syntax::{NodeKind, ParserInput, SyntaxTree, cook};
///
/// let input = ParserInput::new(&cook("x y", &lex("x y").unwrap()));
/// SyntaxTree::build(&input, |root| {
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
/// use sumi_syntax::{NodeKind, ParserInput, SyntaxTree, cook};
///
/// let input = ParserInput::new(&cook("x", &lex("x").unwrap()));
/// SyntaxTree::build(&input, |root| {
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
