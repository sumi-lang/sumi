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

use sumi_lexer::{LexedFile, RawIdx, SyntaxKind, TokenFlags};
use sumi_syntax::{
    NodeIdx, NodeKind, Parse, ParseAnchor, ParseEvidence, ParserInput, SigIdx, SyntaxTree,
    binary_operator,
};

use crate::rep::sig_of_raw;

/// The line width the printer fits groups into.
pub const WIDTH: usize = 100;
/// One level of indentation.
pub const INDENT: &str = "    ";

/// The separator of a gap that does not break.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Flat {
    Glue,
    Space,
}

/// One gap's plan.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Gap {
    pub(crate) flat: Flat,
    /// The indentation level of the token after the gap when it breaks.
    pub(crate) level: u32,
    /// The indentation level of comments on their own line in the gap.
    pub(crate) comment_level: u32,
    /// The gap may break when its group does.
    pub(crate) breakable: bool,
    /// The gap always breaks: a statement or item boundary, a comment, or
    /// frozen trivia holding a line break.
    pub(crate) hard: bool,
    /// The gap's trivia is emitted as written.
    pub(crate) frozen: bool,
    /// The gap before a list closer: a comma precedes its break form.
    pub(crate) closer: bool,
}

/// A range of gaps, `first..end`, that break together.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Group {
    pub(crate) first: u32,
    pub(crate) end: u32,
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

/// A rule's choice for one gap.
#[derive(Clone, Copy)]
enum Sep {
    Glue,
    Space,
    /// A space, or a break at the level.
    Soft(u32),
    /// Nothing, or a break at the level.
    SoftGlue(u32),
    /// A break at the level.
    Hard(u32),
    /// A break before a block's closer: comments inside sit one level in.
    HardClose(u32),
    /// Nothing, or a comma and a break at the level, before a list closer.
    Closer(u32),
}

/// One element of a node in significant-index space.
#[derive(Clone, Copy)]
enum El {
    Tok(u32, SyntaxKind),
    Node(NodeIdx, NodeKind),
}

pub(crate) fn plan(lexed: &LexedFile, input: &ParserInput, parse: &Parse) -> Plan {
    let n = input.len();
    let mut planner = Planner {
        tree: parse.tree(),
        input,
        sig_of_raw: sig_of_raw(input, lexed),
        gaps: vec![
            Gap {
                flat: Flat::Space,
                level: 0,
                comment_level: 0,
                breakable: false,
                hard: false,
                frozen: false,
                closer: false,
            };
            n + 1
        ],
        groups: Vec::new(),
        layout_comma: vec![false; n],
    };
    planner.source_file();
    planner.freeze(lexed, parse);
    planner.gaps[0].flat = Flat::Glue;

    for gap in 0..=n {
        let g = &mut planner.gaps[gap];
        if g.frozen {
            let start = if gap == 0 {
                RawIdx::new(0)
            } else {
                input.token(SigIdx::new(gap as u32 - 1)) + 1
            };
            let end = if gap == n {
                lexed.end()
            } else {
                input.token(SigIdx::new(gap as u32))
            };
            g.breakable = false;
            g.hard = start
                .until(end)
                .any(|raw| lexed.kind(raw) == SyntaxKind::Newline);
            continue;
        }
        if gap == n && n > 0 {
            g.hard = true;
            g.level = 0;
        }
        // A line break ends every hole open on its line and discards the
        // brackets opened inside. So a break is never added while a hole
        // is open, and one that closed a hole is kept.
        let start = if gap == 0 {
            RawIdx::new(0)
        } else {
            input.token(SigIdx::new(gap as u32 - 1)) + 1
        };
        let end = if gap == n {
            lexed.end()
        } else {
            input.token(SigIdx::new(gap as u32))
        };
        let hole_open_after = |raw: RawIdx| lexed.flags(raw).contains(TokenFlags::HOLE_AFTER);
        if gap < n && end.checked_sub(1).is_some_and(hole_open_after) {
            g.breakable = false;
            g.hard = false;
        } else if gap > 0
            && hole_open_after(start - 1)
            && start
                .until(end)
                .any(|raw| lexed.kind(raw) == SyntaxKind::Newline)
        {
            g.hard = true;
        }
        // A comment ends its line.
        if start
            .until(end)
            .any(|raw| lexed.kind(raw) == SyntaxKind::LineComment)
        {
            g.hard = true;
        }
    }
    // Inside a statement, a break that would end it is not a layout. The
    // rule reads whether the token after the gap is glued to its
    // successor, which is the plan's to decide, not the source's: a frozen
    // gap keeps the source's spacing, and every other gap the plan's.
    for gap in 1..n {
        let g = planner.gaps[gap];
        if g.hard || !g.breakable {
            continue;
        }
        let next = planner.gaps[gap + 1];
        let glued = if next.frozen {
            input.is_joint(SigIdx::new(gap as u32))
        } else {
            next.flat == Flat::Glue && !next.hard
        };
        let glued_kind = glued
            .then(|| input.get(SigIdx::new(gap as u32 + 1)))
            .flatten();
        if input.would_end_statement_if(SigIdx::new(gap as u32), glued_kind) {
            planner.gaps[gap].breakable = false;
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

struct Planner<'a> {
    tree: &'a SyntaxTree,
    input: &'a ParserInput,
    sig_of_raw: Vec<u32>,
    gaps: Vec<Gap>,
    groups: Vec<Group>,
    layout_comma: Vec<bool>,
}

impl Planner<'_> {
    fn first_sig(&self, node: NodeIdx) -> u32 {
        self.sig_of_raw[self.tree.first_token(node).to_usize()]
    }

    fn end_sig(&self, node: NodeIdx) -> u32 {
        let end = self.tree.end_token(node);
        if end == self.tree.first_token(node) {
            self.first_sig(node)
        } else {
            self.sig_of_raw[end.to_usize() - 1] + 1
        }
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
        for child in self.tree.children_in_order(node) {
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

    fn set(&mut self, gap: u32, sep: Sep, flat: bool) {
        let g = &mut self.gaps[gap as usize];
        g.flat = Flat::Space;
        g.breakable = false;
        g.hard = false;
        g.closer = false;
        match sep {
            Sep::Glue => g.flat = Flat::Glue,
            Sep::Space => {}
            Sep::Soft(level) | Sep::SoftGlue(level) => {
                g.flat = if matches!(sep, Sep::Soft(_)) {
                    Flat::Space
                } else {
                    Flat::Glue
                };
                if !flat {
                    g.breakable = true;
                    g.level = level;
                    g.comment_level = level;
                }
            }
            Sep::Hard(level) | Sep::HardClose(level) => {
                if !flat {
                    g.hard = true;
                    g.level = level;
                    g.comment_level = if matches!(sep, Sep::HardClose(_)) {
                        level + 1
                    } else {
                        level
                    };
                }
            }
            Sep::Closer(level) => {
                g.flat = Flat::Glue;
                g.level = level;
                g.comment_level = level + 1;
                if !flat {
                    g.breakable = true;
                    g.closer = true;
                }
            }
        }
    }

    fn group(&mut self, first: u32, end: u32) {
        if first < end {
            self.groups.push(Group { first, end });
        }
    }

    /// Lay out `node` at indentation `level`, the level of the line it
    /// begins on; `flat` inside a hole, where nothing may break.
    fn node(&mut self, node: NodeIdx, level: u32, flat: bool) {
        let kind = self.tree.kind(node);
        if kind == NodeKind::Error {
            return;
        }
        let els = self.elements(node);
        match kind {
            NodeKind::SourceFile => unreachable!("the root is laid out by source_file"),
            NodeKind::FnItem | NodeKind::ClosureExpr => self.function(node, &els, level, flat),
            NodeKind::ParamList | NodeKind::ArgList => self.list(node, &els, level, flat),
            NodeKind::Block => self.block(&els, level, flat),
            NodeKind::LetStmt | NodeKind::AssignStmt | NodeKind::DiscardStmt => {
                self.binding(node, &els, level, flat);
            }
            NodeKind::BinaryExpr => self.binary(node, &els, level, flat, None),
            NodeKind::ParenExpr => {
                self.pairs(&els, flat, |a, b| match (a, b) {
                    (El::Tok(_, SyntaxKind::LParen), El::Tok(_, SyntaxKind::RParen)) => Sep::Glue,
                    (El::Tok(_, SyntaxKind::LParen), _) => Sep::SoftGlue(level + 1),
                    (_, El::Tok(_, SyntaxKind::RParen)) => Sep::SoftGlue(level),
                    _ => Sep::Space,
                });
                if !flat {
                    self.group(self.first_sig(node) + 1, self.end_sig(node));
                }
                self.children(&els, level + 1, flat);
            }
            NodeKind::Param => {
                self.pairs(&els, flat, |_, b| match b {
                    El::Tok(_, SyntaxKind::Colon) => Sep::Glue,
                    _ => Sep::Space,
                });
                self.children(&els, level, flat);
            }
            NodeKind::PrefixExpr | NodeKind::CallExpr | NodeKind::InterpolatedString => {
                self.pairs(&els, flat, |_, _| Sep::Glue);
                self.children(&els, level, flat);
            }
            NodeKind::Hole => {
                self.pairs(&els, true, |_, _| Sep::Glue);
                self.children(&els, level, true);
            }
            NodeKind::ReturnStmt | NodeKind::IfExpr => {
                self.pairs(&els, flat, |_, _| Sep::Space);
                self.children(&els, level, flat);
            }
            NodeKind::Name
            | NodeKind::TypeRef
            | NodeKind::NameRef
            | NodeKind::LiteralExpr
            | NodeKind::Error => {
                self.pairs(&els, flat, |_, _| Sep::Space);
                self.children(&els, level, flat);
            }
        }
    }

    fn pairs(&mut self, els: &[El], flat: bool, rule: impl Fn(El, El) -> Sep) {
        for pair in els.windows(2) {
            let gap = self.start(pair[1]);
            self.set(gap, rule(pair[0], pair[1]), flat);
        }
    }

    fn children(&mut self, els: &[El], level: u32, flat: bool) {
        for &el in els {
            if let El::Node(child, _) = el {
                self.node(child, level, flat);
            }
        }
    }

    /// Items on their own lines; the gaps between them keep blank lines.
    fn source_file(&mut self) {
        let root = self.tree.root();
        let items: Vec<NodeIdx> = self.tree.children_in_order(root).collect();
        for pair in items.windows(2) {
            let gap = self.first_sig(pair[1]);
            self.set(gap, Sep::Hard(0), false);
        }
        for item in items {
            self.node(item, 0, false);
        }
    }

    /// A function item or closure: the head on one line, and the body a
    /// block after a space or an expression after `=`, which may move to
    /// the next line, one level in, when the whole does not fit.
    fn function(&mut self, node: NodeIdx, els: &[El], level: u32, flat: bool) {
        let body_hugs = els.last().is_some_and(|&el| hugs(self.tree, el));
        self.pairs(els, flat, |a, b| match (a, b) {
            (El::Tok(_, SyntaxKind::FnKw), El::Node(_, NodeKind::ParamList)) => Sep::Glue,
            (El::Node(_, NodeKind::Name), El::Node(_, NodeKind::ParamList)) => Sep::Glue,
            (El::Tok(_, SyntaxKind::Minus), El::Tok(_, SyntaxKind::Gt)) => Sep::Glue,
            (El::Tok(_, SyntaxKind::Eq), El::Node(..)) if !body_hugs => Sep::Soft(level + 1),
            _ => Sep::Space,
        });
        let mut after_eq = false;
        for &el in els {
            match el {
                El::Tok(sig, SyntaxKind::Eq) => {
                    after_eq = true;
                    if !flat && !body_hugs {
                        self.group(sig + 1, self.end_sig(node));
                    }
                }
                El::Node(child, _) => {
                    let child_level = if after_eq && !body_hugs {
                        level + 1
                    } else {
                        level
                    };
                    self.node(child, child_level, flat);
                }
                El::Tok(..) => {}
            }
        }
    }

    /// A parameter or argument list: glued to its owner, elements spaced
    /// after commas, and one element per line with a trailing comma when
    /// the list breaks.
    fn list(&mut self, node: NodeIdx, els: &[El], level: u32, flat: bool) {
        self.pairs(els, flat, |a, b| match (a, b) {
            (El::Tok(_, SyntaxKind::LParen), El::Tok(_, SyntaxKind::RParen)) => Sep::Glue,
            (El::Tok(_, SyntaxKind::LParen), _) => Sep::SoftGlue(level + 1),
            (_, El::Tok(_, SyntaxKind::Comma)) => Sep::Glue,
            (_, El::Tok(_, SyntaxKind::RParen)) => Sep::Closer(level),
            (El::Tok(_, SyntaxKind::Comma), _) => Sep::Soft(level + 1),
            _ => Sep::Space,
        });
        if !flat && !self.tree.has_error(node) {
            for pair in els.windows(2) {
                if let (El::Tok(sig, SyntaxKind::Comma), El::Tok(_, SyntaxKind::RParen)) =
                    (pair[0], pair[1])
                {
                    self.layout_comma[sig as usize] = true;
                }
            }
            if els.len() > 2 {
                self.group(self.first_sig(node) + 1, self.end_sig(node));
            }
        }
        self.children(els, level + 1, flat);
    }

    /// A block: statements one per line, one level in.
    fn block(&mut self, els: &[El], level: u32, flat: bool) {
        self.pairs(els, flat, |a, b| match (a, b) {
            (El::Tok(_, SyntaxKind::LBrace), El::Tok(_, SyntaxKind::RBrace)) => Sep::Glue,
            (_, El::Tok(_, SyntaxKind::RBrace)) => Sep::HardClose(level),
            _ => Sep::Hard(level + 1),
        });
        if let [
            El::Tok(_, SyntaxKind::LBrace),
            El::Tok(close, SyntaxKind::RBrace),
        ] = els
        {
            self.gaps[*close as usize].comment_level = level + 1;
        }
        self.children(els, level + 1, flat);
    }

    /// A binding or assignment: the head on one line, and the value after
    /// `=`, which may move to the next line, one level in, unless it
    /// begins a block on the same line.
    fn binding(&mut self, node: NodeIdx, els: &[El], level: u32, flat: bool) {
        let value_hugs = els.last().is_some_and(|&el| hugs(self.tree, el));
        self.pairs(els, flat, |a, b| match (a, b) {
            (_, El::Tok(_, SyntaxKind::Colon)) => Sep::Glue,
            (El::Tok(_, SyntaxKind::Eq), El::Node(..)) if !value_hugs => Sep::Soft(level + 1),
            _ => Sep::Space,
        });
        let mut after_eq = false;
        for &el in els {
            match el {
                El::Tok(sig, SyntaxKind::Eq) => {
                    after_eq = true;
                    if !flat && !value_hugs {
                        self.group(sig + 1, self.end_sig(node));
                    }
                }
                El::Node(child, _) => {
                    let child_level = if after_eq && !value_hugs {
                        level + 1
                    } else {
                        level
                    };
                    self.node(child, child_level, flat);
                }
                El::Tok(..) => {}
            }
        }
    }

    /// A binary expression: operators spaced, and a chain of one
    /// precedence breaking before each operator, one level in. `chain` is
    /// the continuation level of the chain this node extends, if any.
    fn binary(&mut self, node: NodeIdx, els: &[El], level: u32, flat: bool, chain: Option<u32>) {
        let cont = chain.unwrap_or(level + 1);
        self.pairs(els, flat, |a, b| match (a, b) {
            (El::Node(..), El::Tok(..)) => Sep::Soft(cont),
            (El::Tok(..), El::Tok(..)) => Sep::Glue,
            _ => Sep::Space,
        });
        if chain.is_none() && !flat {
            self.group(self.first_sig(node) + 1, self.end_sig(node));
        }
        let power = self.power(els);
        let mut first = true;
        for &el in els {
            if let El::Node(child, child_kind) = el {
                if first {
                    first = false;
                    if child_kind == NodeKind::BinaryExpr && self.power_of(child) == power {
                        let child_els = self.elements(child);
                        self.binary(child, &child_els, level, flat, Some(cont));
                        continue;
                    }
                    self.node(child, level, flat);
                } else {
                    self.node(child, cont, flat);
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
        let gap_at = |planner: &Self, raw: RawIdx| -> usize {
            planner
                .input
                .indices()
                .collect::<Vec<_>>()
                .partition_point(|&sig| planner.input.token(sig) < raw)
        };
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
        let n = self.input.len();
        let has_newline = |planner: &Self, gap: usize| {
            let start = if gap == 0 {
                RawIdx::new(0)
            } else {
                planner.input.token(SigIdx::new(gap as u32 - 1)) + 1
            };
            let end = if gap == n {
                lexed.end()
            } else {
                planner.input.token(SigIdx::new(gap as u32))
            };
            start
                .until(end)
                .any(|raw| lexed.kind(raw) == SyntaxKind::Newline)
        };
        for gap in anchors {
            self.gaps[gap].frozen = true;
        }
        for (start, end) in ranges {
            for gap in start + 1..end {
                self.gaps[gap].frozen = true;
            }
            for edge in [start, end] {
                if !(self.gaps[edge].hard && has_newline(self, edge)) {
                    self.gaps[edge].frozen = true;
                }
            }
        }
    }
}

/// Whether an element stays on the line of the `=` before it and breaks
/// inside itself instead: a block, an `if`, a closure with a block body,
/// a call, or a parenthesized expression. This stands in for a tail rule
/// that would measure whether the value's head fits.
fn hugs(tree: &SyntaxTree, el: El) -> bool {
    match el {
        El::Node(
            _,
            NodeKind::Block | NodeKind::IfExpr | NodeKind::CallExpr | NodeKind::ParenExpr,
        ) => true,
        El::Node(node, NodeKind::ClosureExpr) => tree
            .children(node)
            .next()
            .is_some_and(|last| tree.kind(last) == NodeKind::Block),
        _ => false,
    }
}
