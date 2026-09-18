//! The layout plan: one separator per gap between adjacent significant
//! tokens, and the groups that decide which separators break.
//!
//! With the tokens fixed, formatting has one degree of freedom per gap:
//! nothing, a space, or a line break at some indentation. The rules here
//! walk the tree and fill a [`Gap`] per gap with its flat form, its break
//! form, and whether it may break at all; a [`Group`] is a range of gaps
//! that break together when the group does not fit. Gaps the parser
//! recovered around are frozen and keep their trivia as written.
//!
//! Legality comes from the parser's own stream: a break that would end a
//! statement, by [`ParserInput::would_end_statement`], is never offered
//! inside one, so a mistaken rule widens a line instead of changing the
//! program.

use sumi_lexer::{LexedFile, RawIdx, SyntaxKind};
use sumi_syntax::{
    NodeIdx, NodeKind, Parse, ParseAnchor, ParseEvidence, ParserInput, SigIdx, SyntaxTree,
    binary_operator,
};

/// The line width the printer fits groups into.
pub const WIDTH: usize = 100;
/// One level of indentation.
pub(crate) const INDENT: &str = "    ";

/// The separator of a gap that does not break.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Flat {
    Glue,
    Space,
}

/// When a gap breaks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Breaks {
    Never,
    /// When its group does.
    Soft,
    /// Always: a statement or item boundary, a comment, or frozen trivia
    /// holding a line break.
    Hard,
}

/// The closer a gap precedes, whose comments sit one level in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Closer {
    Block,
    /// A comma precedes the gap's break.
    List,
}

/// One gap's plan: the rule's choice, then what the post-passes learn.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Gap {
    pub(crate) flat: Flat,
    /// The indentation level of the token after the gap when it breaks.
    pub(crate) level: u32,
    pub(crate) breaks: Breaks,
    pub(crate) closer: Option<Closer>,
    /// The gap's trivia is emitted as written.
    pub(crate) frozen: bool,
}

impl Gap {
    fn new(flat: Flat, level: u32, breaks: Breaks, closer: Option<Closer>) -> Self {
        Self {
            flat,
            level,
            breaks,
            closer,
            frozen: false,
        }
    }

    /// Nothing.
    fn glue(level: u32) -> Self {
        Self::new(Flat::Glue, level, Breaks::Never, None)
    }

    /// A space.
    fn space(level: u32) -> Self {
        Self::new(Flat::Space, level, Breaks::Never, None)
    }

    /// A space, or a break at the level.
    fn soft(level: u32) -> Self {
        Self::new(Flat::Space, level, Breaks::Soft, None)
    }

    /// Nothing, or a break at the level.
    fn soft_glue(level: u32) -> Self {
        Self::new(Flat::Glue, level, Breaks::Soft, None)
    }

    /// A break at the level.
    fn hard(level: u32) -> Self {
        Self::new(Flat::Space, level, Breaks::Hard, None)
    }

    /// Nothing, or `closer`'s break at the level.
    fn closer(closer: Closer, level: u32, breaks: Breaks) -> Self {
        Self::new(Flat::Glue, level, breaks, Some(closer))
    }

    /// The indentation level of comments on their own line in the gap.
    pub(crate) fn comment_level(&self) -> u32 {
        self.level + u32::from(self.closer.is_some())
    }
}

/// A range of gaps, `first..end`, that break together. A group may name
/// a tail, the gaps inside its last element, which decide for themselves.
/// The group is forced only by hard gaps outside its tail, it fits when
/// the text up to the tail's first break opportunity does, and when it
/// breaks it indents its tail one level: so `let x = foo(` keeps the call
/// on the binding's line with the arguments breaking inside, and moves
/// the value to the next line only when even its head does not fit.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Group {
    pub(crate) first: u32,
    pub(crate) end: u32,
    /// The tail's gaps, `from..to`, inside `first..end`.
    pub(crate) tail: Option<(u32, u32)>,
}

impl Group {
    /// Whether `gap` lies in the tail.
    pub(crate) fn in_tail(&self, gap: u32) -> bool {
        self.tail.is_some_and(|(from, to)| from <= gap && gap < to)
    }
}

pub(crate) struct Plan {
    /// One per gap: gap `i` precedes significant token `i`, and gap `n`
    /// ends the file.
    pub(crate) gaps: Vec<Gap>,
    /// In preorder: by first gap, then the widest first.
    pub(crate) groups: Vec<Group>,
    /// The significant tokens that are layout commas, emitted only when
    /// the gap after them breaks.
    pub(crate) layout_comma: Vec<bool>,
}

/// One element of a node in significant-index space.
#[derive(Clone, Copy)]
enum El {
    Tok(u32, SyntaxKind),
    Node(NodeIdx, NodeKind),
}

pub(crate) fn plan(lexed: &LexedFile, parse: &Parse) -> Plan {
    let input = parse.input();
    let n = input.len();
    let mut planner = Planner {
        tree: parse.tree(),
        input,
        gaps: vec![Gap::glue(0); n + 1],
        groups: Vec::new(),
        layout_comma: vec![false; n],
    };
    planner.source_file();
    planner.freeze(lexed, parse);

    for gap in 0..=n {
        let g = &mut planner.gaps[gap];
        let holds = |kind| holds(lexed, input, gap, kind);
        if g.frozen {
            g.breaks = if holds(SyntaxKind::Newline) {
                Breaks::Hard
            } else {
                Breaks::Never
            };
            continue;
        }
        if gap == n && n > 0 {
            g.breaks = Breaks::Hard;
            g.level = 0;
        }
        // A comment ends its line.
        if holds(SyntaxKind::LineComment) {
            g.breaks = Breaks::Hard;
        }
    }
    // Inside a statement, a break that would end it is not a layout. The
    // rule reads whether the token after the gap is glued to its
    // successor, which is the plan's to decide, not the source's: a frozen
    // gap keeps the source's spacing, and every other gap the plan's.
    for gap in 1..n {
        if planner.gaps[gap].breaks != Breaks::Soft {
            continue;
        }
        let next = planner.gaps[gap + 1];
        let glued = if next.frozen {
            input.is_joint(SigIdx::new(gap as u32))
        } else {
            next.flat == Flat::Glue && next.breaks != Breaks::Hard
        };
        let glued_kind = glued
            .then(|| input.get(SigIdx::new(gap as u32 + 1)))
            .flatten();
        if input.would_end_statement_if(SigIdx::new(gap as u32), glued_kind) {
            planner.gaps[gap].breaks = Breaks::Never;
        }
    }
    for sig in 0..n {
        if planner.layout_comma[sig] && planner.gaps[sig + 1].frozen {
            planner.layout_comma[sig] = false;
        }
    }
    planner
        .groups
        .sort_by_key(|group| (group.first, std::cmp::Reverse(group.end)));
    Plan {
        gaps: planner.gaps,
        groups: planner.groups,
        layout_comma: planner.layout_comma,
    }
}

/// Whether the trivia of gap `gap` holds a token of `kind`.
fn holds(lexed: &LexedFile, input: &ParserInput, gap: usize, kind: SyntaxKind) -> bool {
    let trivia = input.trivia_before(SigIdx::new(gap as u32));
    trivia
        .start
        .until(trivia.end)
        .any(|raw| lexed.kind(raw) == kind)
}

struct Planner<'a> {
    tree: &'a SyntaxTree,
    input: &'a ParserInput,
    gaps: Vec<Gap>,
    groups: Vec<Group>,
    layout_comma: Vec<bool>,
}

impl Planner<'_> {
    fn first_sig(&self, node: NodeIdx) -> u32 {
        crate::first_sig(self.tree, self.input, node)
    }

    fn end_sig(&self, node: NodeIdx) -> u32 {
        crate::end_sig(self.tree, self.input, node)
    }

    fn start(&self, el: El) -> u32 {
        match el {
            El::Tok(sig, _) => sig,
            El::Node(node, _) => self.first_sig(node),
        }
    }

    /// The direct tokens and children of `node`, in source order.
    fn elements(&self, node: NodeIdx) -> Vec<El> {
        let mut els = Vec::new();
        let mut cursor = self.first_sig(node);
        let end = self.end_sig(node);
        for child in self.tree.children(node) {
            let first = self.first_sig(child);
            while cursor < first {
                els.push(self.tok(cursor));
                cursor += 1;
            }
            els.push(El::Node(child, self.tree.kind(child)));
            cursor = self.end_sig(child);
        }
        while cursor < end {
            els.push(self.tok(cursor));
            cursor += 1;
        }
        els
    }

    fn tok(&self, sig: u32) -> El {
        El::Tok(
            sig,
            self.input
                .get(SigIdx::new(sig))
                .expect("a significant token in range"),
        )
    }

    fn set(&mut self, gap: u32, sep: Gap) {
        self.gaps[gap as usize] = sep;
    }

    /// The gaps `first..end` break together; a last element `tail`
    /// decides for itself.
    fn group(&mut self, first: u32, end: u32, tail: Option<NodeIdx>) {
        if first < end {
            let tail = tail
                .map(|tail| (self.first_sig(tail) + 1, self.end_sig(tail)))
                .filter(|&(from, to)| from < to);
            self.groups.push(Group { first, end, tail });
        }
    }

    /// Lay out the value after `=` of a binding or an expression body:
    /// the tail of the group from the gap after `=` to the end of `node`,
    /// unless it is an operator chain, which reads better moved whole to
    /// the next line before it breaks at its operators.
    fn value(&mut self, node: NodeIdx, eq: u32, value: NodeIdx, level: u32) {
        let chain = self.tree.kind(value) == NodeKind::BinaryExpr;
        self.group(eq + 1, self.end_sig(node), (!chain).then_some(value));
        self.node(value, if chain { level + 1 } else { level });
    }

    /// Lay out `node` at indentation `level`, the level of the line it
    /// begins on.
    fn node(&mut self, node: NodeIdx, level: u32) {
        let kind = self.tree.kind(node);
        if kind == NodeKind::Error {
            return;
        }
        let els = self.elements(node);
        match kind {
            NodeKind::SourceFile => unreachable!("the root is laid out by source_file"),
            NodeKind::FnItem | NodeKind::ClosureExpr => self.function(node, &els, level),
            NodeKind::ParamList | NodeKind::ArgList => self.list(node, &els, level),
            NodeKind::Block => self.block(&els, level),
            NodeKind::LetStmt | NodeKind::AssignStmt | NodeKind::DiscardStmt => {
                self.binding(node, &els, level);
            }
            NodeKind::BinaryExpr => self.binary(node, &els, level, None),
            NodeKind::ParenExpr => {
                self.pairs(&els, |a, b| match (a, b) {
                    (El::Tok(_, SyntaxKind::LParen), El::Tok(_, SyntaxKind::RParen)) => {
                        Gap::glue(level)
                    }
                    (El::Tok(_, SyntaxKind::LParen), _) => Gap::soft_glue(level + 1),
                    (_, El::Tok(_, SyntaxKind::RParen)) => Gap::soft_glue(level),
                    _ => Gap::space(level + 1),
                });
                self.group(self.first_sig(node) + 1, self.end_sig(node), None);
                self.children(&els, level + 1);
            }
            NodeKind::Param => {
                self.pairs(&els, |_, b| match b {
                    El::Tok(_, SyntaxKind::Colon) => Gap::glue(level),
                    _ => Gap::space(level),
                });
                self.children(&els, level);
            }
            NodeKind::PrefixExpr | NodeKind::CallExpr => {
                self.pairs(&els, |_, _| Gap::glue(level));
                self.children(&els, level);
            }
            NodeKind::ReturnStmt | NodeKind::IfExpr => {
                self.pairs(&els, |_, _| Gap::space(level));
                self.children(&els, level);
            }
            NodeKind::Name
            | NodeKind::TypeRef
            | NodeKind::NameRef
            | NodeKind::LiteralExpr
            | NodeKind::Error => {
                self.pairs(&els, |_, _| Gap::space(level));
                self.children(&els, level);
            }
        }
    }

    fn pairs(&mut self, els: &[El], rule: impl Fn(El, El) -> Gap) {
        for pair in els.windows(2) {
            let gap = self.start(pair[1]);
            self.set(gap, rule(pair[0], pair[1]));
        }
    }

    fn children(&mut self, els: &[El], level: u32) {
        for &el in els {
            if let El::Node(child, _) = el {
                self.node(child, level);
            }
        }
    }

    /// Items on their own lines; the gaps between them keep blank lines.
    fn source_file(&mut self) {
        let root = self.tree.root();
        let items: Vec<NodeIdx> = self.tree.children(root).collect();
        for pair in items.windows(2) {
            let gap = self.first_sig(pair[1]);
            self.set(gap, Gap::hard(0));
        }
        for item in items {
            self.node(item, 0);
        }
    }

    /// A function item or closure: the head on one line, and the body a
    /// block after a space or an expression after `=`, laid out as a
    /// binding's value.
    fn function(&mut self, node: NodeIdx, els: &[El], level: u32) {
        self.pairs(els, |a, b| match (a, b) {
            (El::Tok(_, SyntaxKind::FnKw), El::Node(_, NodeKind::ParamList)) => Gap::glue(level),
            (El::Node(_, NodeKind::Name), El::Node(_, NodeKind::ParamList)) => Gap::glue(level),
            (El::Tok(_, SyntaxKind::Minus), El::Tok(_, SyntaxKind::Gt)) => Gap::glue(level),
            (El::Tok(_, SyntaxKind::Eq), El::Node(..)) => Gap::soft(level + 1),
            _ => Gap::space(level),
        });
        self.head_and_value(node, els, level);
    }

    /// Lay out the children of a construct whose `=`, if any, is followed
    /// by its value.
    fn head_and_value(&mut self, node: NodeIdx, els: &[El], level: u32) {
        let mut eq = None;
        for &el in els {
            match el {
                El::Tok(sig, SyntaxKind::Eq) => eq = Some(sig),
                El::Node(child, _) => match eq {
                    Some(eq) => self.value(node, eq, child, level),
                    None => self.node(child, level),
                },
                El::Tok(..) => {}
            }
        }
    }

    /// A parameter or argument list: glued to its owner, elements spaced
    /// after commas, and one element per line with a trailing comma when
    /// the list breaks.
    fn list(&mut self, node: NodeIdx, els: &[El], level: u32) {
        self.pairs(els, |a, b| match (a, b) {
            (El::Tok(_, SyntaxKind::LParen), El::Tok(_, SyntaxKind::RParen)) => Gap::glue(level),
            (El::Tok(_, SyntaxKind::LParen), _) => Gap::soft_glue(level + 1),
            (_, El::Tok(_, SyntaxKind::Comma)) => Gap::glue(level + 1),
            (_, El::Tok(_, SyntaxKind::RParen)) => Gap::closer(Closer::List, level, Breaks::Soft),
            (El::Tok(_, SyntaxKind::Comma), _) => Gap::soft(level + 1),
            _ => Gap::space(level + 1),
        });
        // A list the parser recovered in keeps its comma and its shape.
        let sound = !self.tree.has_error(node);
        if sound {
            // The comma before the closer is a layout token: dropped when
            // the list is flat.
            for pair in els.windows(2) {
                if let (El::Tok(sig, SyntaxKind::Comma), El::Tok(_, SyntaxKind::RParen)) =
                    (pair[0], pair[1])
                {
                    self.layout_comma[sig as usize] = true;
                }
            }
        }
        // The last element hugs the closer when it opens a block: it is the
        // group's tail and, flat, sits at this level; broken, it is one
        // level in like the rest, through the tail's indentation.
        let last = els.iter().rev().find_map(|&el| match el {
            El::Node(child, _) => Some(child),
            El::Tok(..) => None,
        });
        let hug = last.filter(|&last| sound && self.opens_block(last));
        if sound && els.len() > 2 {
            self.group(self.first_sig(node) + 1, self.end_sig(node), hug);
        }
        for &el in els {
            if let El::Node(child, _) = el {
                let child_level = if Some(child) == hug { level } else { level + 1 };
                self.node(child, child_level);
            }
        }
    }

    /// Whether `node` begins a block on its line: a block, an `if`, or a
    /// closure with a block body. Such a last element hugs a list.
    fn opens_block(&self, node: NodeIdx) -> bool {
        match self.tree.kind(node) {
            NodeKind::Block | NodeKind::IfExpr => true,
            NodeKind::ClosureExpr => self
                .tree
                .children(node)
                .last()
                .is_some_and(|last| self.tree.kind(last) == NodeKind::Block),
            _ => false,
        }
    }

    /// A block: statements one per line, one level in.
    fn block(&mut self, els: &[El], level: u32) {
        self.pairs(els, |a, b| match (a, b) {
            (El::Tok(_, SyntaxKind::LBrace), El::Tok(_, SyntaxKind::RBrace)) => {
                Gap::closer(Closer::Block, level, Breaks::Never)
            }
            (_, El::Tok(_, SyntaxKind::RBrace)) => Gap::closer(Closer::Block, level, Breaks::Hard),
            _ => Gap::hard(level + 1),
        });
        self.children(els, level + 1);
    }

    /// A binding or assignment: the head on one line, and the value after
    /// `=` as the tail of the binding's group.
    fn binding(&mut self, node: NodeIdx, els: &[El], level: u32) {
        self.pairs(els, |a, b| match (a, b) {
            (_, El::Tok(_, SyntaxKind::Colon)) => Gap::glue(level),
            (El::Tok(_, SyntaxKind::Eq), El::Node(..)) => Gap::soft(level + 1),
            _ => Gap::space(level),
        });
        self.head_and_value(node, els, level);
    }

    /// A binary expression: operators spaced, and a chain of one
    /// precedence breaking before each operator, one level in. `chain` is
    /// the continuation level of the chain this node extends, if any.
    fn binary(&mut self, node: NodeIdx, els: &[El], level: u32, chain: Option<u32>) {
        let cont = chain.unwrap_or(level + 1);
        self.pairs(els, |a, b| match (a, b) {
            (El::Node(..), El::Tok(..)) => Gap::soft(cont),
            (El::Tok(..), El::Tok(..)) => Gap::glue(cont),
            _ => Gap::space(cont),
        });
        if chain.is_none() {
            self.group(self.first_sig(node) + 1, self.end_sig(node), None);
        }
        let power = self.power(els);
        let mut first = true;
        for &el in els {
            if let El::Node(child, child_kind) = el {
                if first {
                    first = false;
                    if child_kind == NodeKind::BinaryExpr && self.power_of(child) == power {
                        let child_els = self.elements(child);
                        self.binary(child, &child_els, level, Some(cont));
                        continue;
                    }
                    self.node(child, level);
                } else {
                    self.node(child, cont);
                }
            }
        }
    }

    /// The left binding power of the operator among `els`.
    fn power(&self, els: &[El]) -> Option<u8> {
        let mut tokens = els.iter().filter_map(|el| match el {
            El::Tok(sig, kind) => Some((*sig, *kind)),
            El::Node(..) => None,
        });
        let (sig, first) = tokens.next()?;
        let glued = tokens
            .next()
            .filter(|&(next, _)| next == sig + 1 && self.input.is_joint(SigIdx::new(sig)))
            .map(|(_, kind)| kind);
        binary_operator(first, glued).map(|(op, _)| op.binding_power().0)
    }

    fn power_of(&self, node: NodeIdx) -> Option<u8> {
        self.power(&self.elements(node))
    }

    /// Freeze every gap the parser recovered around: the anchor of every
    /// recovery, and the inside and edges of every skipped range and every
    /// `Error` node. Recovery is layout-sensitive, but it reads nothing of
    /// a gap beyond whether a line break stands in it, so an edge gap that
    /// holds a line break the rules keep is reindented rather than frozen.
    fn freeze(&mut self, lexed: &LexedFile, parse: &Parse) {
        // The gap before the first significant token at or after `raw`:
        // a range may end at a trivia token.
        let gap_at = |planner: &Self, raw: RawIdx| planner.input.sig_at_or_after(raw).to_usize();
        let mut anchors: Vec<usize> = Vec::new();
        let mut ranges: Vec<(usize, usize)> = Vec::new();
        for evidence in parse.evidence() {
            let ParseEvidence::Recovery(recovery) = evidence else {
                continue;
            };
            match recovery.anchor {
                ParseAnchor::Gap(gap) => anchors.push(gap_at(self, gap.trivia_end())),
                ParseAnchor::Tokens(range) => {
                    ranges.push((gap_at(self, range.start()), gap_at(self, range.end())));
                }
            }
            for &range in &recovery.skipped {
                ranges.push((gap_at(self, range.start()), gap_at(self, range.end())));
            }
        }
        for node in self.tree.nodes() {
            if self.tree.kind(node) == NodeKind::Error {
                ranges.push((
                    gap_at(self, self.tree.first_token(node)),
                    gap_at(self, self.tree.end_token(node)),
                ));
            }
        }
        for gap in anchors {
            self.gaps[gap].frozen = true;
        }
        for (start, end) in ranges {
            for gap in start + 1..end {
                self.gaps[gap].frozen = true;
            }
            for edge in [start, end] {
                let kept_break = self.gaps[edge].breaks == Breaks::Hard
                    && holds(lexed, self.input, edge, SyntaxKind::Newline);
                if !kept_break {
                    self.gaps[edge].frozen = true;
                }
            }
        }
    }
}
