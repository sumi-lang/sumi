//! The parser's token stream: significant tokens plus the stream facts the
//! grammar needs once trivia is gone.
//!
//! Construction strips whitespace, newlines, and comments, and precomputes
//! four per-token facts:
//!
//! - **jointness**: no trivia separates the token from its successor. The
//!   parser glues compound operators (`==`, `->`) from joint pairs, and the
//!   spacing rules for operator arity (unary glued, binary spaced) read the
//!   same bit.
//! - **newline before**: at least one line break sits in the trivia before
//!   the token.
//! - **boundary before**: that line break ends a statement under the newline
//!   rule below.
//! - **partner**: for a bracket, the index of the bracket matching it, if
//!   one does. Brackets pair the way the newline rule nests them: a closer
//!   with a match is a synchronization point, discarding unmatched openers
//!   above its match, so an opener a stray closer discards partners with
//!   nothing; a closer with no match is an orphan and discards nothing.
//!   The `{` at the bottom of the stack — an item's body — pairs with the
//!   last `}` to reach it before the next `fn` or the end of the file,
//!   except that of several such `}` with nothing but closers between
//!   them, the first is the closer and the rest are strays: a `}` with
//!   statements and another `}` after it is a stray inside the body, while
//!   a doubled `}` is the body's end and a stray after it. The parser's
//!   recovery takes a matched pair whole, and a block yields a `)` that
//!   closes a paren still open around it.
//! - **stray**: a bracket its neighbours show to be no bracket at all —
//!   and one too many of its kind in its item, a bracket with a match to
//!   be had being no stray however its neighbours look. A
//!   closer in the middle of a line, wrong on both sides — after a token
//!   that cannot end a statement and before one that starts an operand —
//!   is a stray, as is one before an `=` or `:`, which nothing closed can
//!   precede; so is a `(` after a `}` and before a token nothing opened
//!   can precede, such as `else` or `:`; and so is a `{` inside an open
//!   `(` that a binary operator follows, the expression around it running
//!   straight through it.
//!   Pairing never sees a stray, so it discards and shifts nothing; the
//!   parser skips it as garbage. A closer wrong on one side only — `x = }`
//!   at the end of a line, as an editor leaves it while the line is typed,
//!   or one at the start of a line — stays a closer.
//!
//! # The newline rule
//!
//! Sumi has no `;`; statements end at line breaks. A newline is a statement
//! boundary iff all of:
//!
//! 1. it is not inside parentheses the stream closes — `(...)` suspends
//!    termination, and a `{...}` within restores it; a `(` never closed
//!    suspends nothing, so the line ends the statement it would otherwise
//!    swallow;
//! 2. the token before it can end a statement: an identifier or `_`, a
//!    literal, `true`/`false`, `return`, `)`, or `}`;
//! 3. the token after it cannot continue one: `else` and binary operators
//!    continue the previous line; everything else starts fresh. The set
//!    mirrors the grammar — a leading `.` joins it with member access.
//!
//! The bits record where statements end; the bans that keep the rule
//! unambiguous (trailing operators, unglued unary operators) are enforced by
//! the parser, where the grammar position gives diagnostics their context.

use std::num::NonZeroU32;

use crate::cook::CookedFile;
use crate::kind::SyntaxKind;

const JOINT: u8 = 1 << 0;
const NEWLINE_BEFORE: u8 = 1 << 1;
const BOUNDARY_BEFORE: u8 = 1 << 2;
const STRAY: u8 = 1 << 3;

/// The significant tokens of one cooked file, with jointness and statement
/// boundaries precomputed.
#[derive(Clone, Debug)]
pub struct ParserInput {
    kinds: Box<[SyntaxKind]>,
    /// For each significant token, its index in the underlying token buffer.
    tokens: Box<[u32]>,
    flags: Box<[u8]>,
    /// For each significant token, the index of its matching bracket plus
    /// one, so the slot has a niche; `None` for anything that is not a
    /// matched bracket.
    partners: Box<[Option<NonZeroU32>]>,
    /// The length of the underlying token buffer.
    raw_len: u32,
}

impl ParserInput {
    pub fn new(cooked: &CookedFile) -> Self {
        let mut kinds: Vec<SyntaxKind> = Vec::new();
        let mut tokens: Vec<u32> = Vec::new();
        let mut flags: Vec<u8> = Vec::new();

        let mut newline = false;
        for index in 0..cooked.len() {
            let kind = cooked.kind(index);
            match kind {
                SyntaxKind::Whitespace | SyntaxKind::LineComment => continue,
                SyntaxKind::Newline => {
                    newline = true;
                    continue;
                }
                _ => {}
            }

            if tokens.last().is_some_and(|&last| last + 1 == index as u32) {
                *flags.last_mut().expect("flags stay parallel to tokens") |= JOINT;
            }
            kinds.push(kind);
            tokens.push(index as u32);
            flags.push(if newline { NEWLINE_BEFORE } else { 0 });
            newline = false;
        }

        // Boundaries look at the following token's jointness and at the
        // brackets open around them — whether an open `(` is ever closed —
        // so they need the stream fully built and paired: a pairing pass,
        // then a boundary pass over its result.
        let balances = balances(&kinds);
        let mut item = 0;
        for index in 0..kinds.len() {
            if kinds[index] == SyntaxKind::FnKw {
                item += 1;
            }
            if stray_bracket(&kinds, &flags, index, balances[item]) {
                flags[index] |= STRAY;
            }
        }
        let mut pairing = Pairing::new(kinds.len());
        let mut item = 0;
        for (index, &kind) in kinds.iter().enumerate() {
            if kind == SyntaxKind::FnKw {
                item += 1;
            }
            if flags[index] & STRAY != 0 {
                pairing.token();
                continue;
            }
            match kind {
                SyntaxKind::LBrace
                    if pairing.parens > 0
                        && balances[item].braces > 0
                        && operator_after(&kinds, &flags, index) =>
                {
                    flags[index] |= STRAY;
                    pairing.token();
                }
                SyntaxKind::LParen | SyntaxKind::LBrace => pairing.open(index, kind),
                SyntaxKind::RParen => pairing.close(index, SyntaxKind::LParen),
                SyntaxKind::RBrace => pairing.close(index, SyntaxKind::LBrace),
                SyntaxKind::FnKw => pairing.settle(),
                _ => pairing.token(),
            }
        }
        pairing.settle();
        let partners = pairing.partners;

        // The brackets open before each token, replayed from the pairs: an
        // opener is open until its partner closes it, which discards
        // whatever opened inside and never closed; an orphan closer opens
        // and closes nothing. Only a `(` the stream closes suspends
        // termination — one it never closes would suspend it to the end of
        // the file, so the line ends the statement instead.
        let mut open: Vec<usize> = Vec::new();
        for index in 0..kinds.len() {
            if index > 0
                && flags[index] & NEWLINE_BEFORE != 0
                && !open.last().is_some_and(|&opener| {
                    kinds[opener] == SyntaxKind::LParen && partners[opener].is_some()
                })
                && can_end_statement(kinds[index - 1])
                && !continues_statement(&kinds, &flags, index)
            {
                flags[index] |= BOUNDARY_BEFORE;
            }
            match kinds[index] {
                _ if flags[index] & STRAY != 0 => {}
                SyntaxKind::LParen | SyntaxKind::LBrace => open.push(index),
                SyntaxKind::RParen | SyntaxKind::RBrace => {
                    if let Some(partner) = partners[index] {
                        let opener = partner.get() as usize - 1;
                        while open.pop().is_some_and(|popped| popped != opener) {}
                    }
                }
                _ => {}
            }
        }

        Self {
            kinds: kinds.into_boxed_slice(),
            tokens: tokens.into_boxed_slice(),
            flags: flags.into_boxed_slice(),
            partners: partners.into_boxed_slice(),
            raw_len: cooked.len() as u32,
        }
    }

    /// The number of significant tokens.
    pub fn len(&self) -> usize {
        self.kinds.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kinds.is_empty()
    }

    /// The kind of significant token `index`, or `None` past the end. End of
    /// input is the end of the buffer, never a sentinel kind.
    pub fn get(&self, index: usize) -> Option<SyntaxKind> {
        self.kinds.get(index).copied()
    }

    /// The index of significant token `index` in the lexed and cooked token
    /// buffers, for ranges, text, and flags.
    pub fn token(&self, index: usize) -> u32 {
        self.tokens[index]
    }

    /// The number of tokens in the underlying buffer: one past the last raw
    /// index, where ranges that run to end of input stop.
    pub(crate) fn raw_len(&self) -> u32 {
        self.raw_len
    }

    /// Whether token `index` is glued to token `index + 1`: no trivia
    /// between them.
    pub fn is_joint(&self, index: usize) -> bool {
        self.flags[index] & JOINT != 0
    }

    /// Whether at least one line break sits between token `index` and the
    /// previous significant token.
    pub fn newline_before(&self, index: usize) -> bool {
        self.flags[index] & NEWLINE_BEFORE != 0
    }

    /// Whether a statement boundary immediately precedes token `index` under
    /// the newline rule. Never true for the first token.
    pub fn boundary_before(&self, index: usize) -> bool {
        self.flags[index] & BOUNDARY_BEFORE != 0
    }

    /// Whether the significant token `index` is a bracket the stream judged
    /// a stray: no bracket at all, paired with nothing.
    pub fn is_stray(&self, index: usize) -> bool {
        self.flags[index] & STRAY != 0
    }

    /// The index of the bracket matching significant token `index`: an
    /// opener's closer or a closer's opener. `None` for an unmatched
    /// bracket, and for anything that is not one.
    pub fn partner(&self, index: usize) -> Option<usize> {
        self.partners[index].map(|partner| partner.get() as usize - 1)
    }
}

/// Bracket pairing over the significant tokens: a stack of open brackets,
/// with two departures from plain matching that read the likelier intent
/// of malformed nesting.
///
/// A closer with a match is a synchronization point: it discards the
/// unmatched openers above its match, which then partner with nothing. A
/// closer with no match open is an orphan and discards nothing: whatever
/// is open may yet be closed. And the `{` at the bottom
/// of the stack — an item's body — does not pair with the first `}` to
/// reach it: it pairs with the last one before the next `fn` or the end,
/// except that of several with nothing but closers between them the first
/// is the closer and the rest are strays. A `}` with statements and a
/// later `}` after it is likelier a stray inside the body than the body's
/// end with garbage between items; a doubled `}` is the end and a stray
/// after it; and the only `}` to reach the body is its end whatever
/// follows, garbage between items being likelier than a stray with the
/// real closer missing.
///
/// Every opener is pushed once and popped at most once, the bottom `{`
/// aside, so pairing is linear even over long runs of opposite delimiters.
struct Pairing {
    partners: Vec<Option<NonZeroU32>>,
    /// The brackets still open, innermost last.
    openers: Vec<(usize, SyntaxKind)>,
    /// How many of them are `(`, and how many `{`, so an orphan closer is
    /// known without a search.
    parens: usize,
    braces: usize,
    /// The `}` the bottom `{` will pair with so far: the latest to reach
    /// it, or the first of the run of them that only closers separate.
    candidate: Option<usize>,
    /// Whether only closers have come since `candidate`, so that the next
    /// `}` to reach the bottom joins its run rather than replacing it.
    trailing: bool,
}

impl Pairing {
    fn new(len: usize) -> Self {
        Self {
            partners: vec![None; len],
            openers: Vec::new(),
            parens: 0,
            braces: 0,
            candidate: None,
            trailing: false,
        }
    }

    /// A token that is neither a bracket nor `fn`.
    fn token(&mut self) {
        self.trailing = false;
    }

    fn count(&mut self, kind: SyntaxKind) -> &mut usize {
        if kind == SyntaxKind::LParen {
            &mut self.parens
        } else {
            &mut self.braces
        }
    }

    fn open(&mut self, index: usize, kind: SyntaxKind) {
        self.openers.push((index, kind));
        *self.count(kind) += 1;
        self.trailing = false;
    }

    /// Close the innermost open `expected`, discarding the openers above
    /// it — or defer, when it is the bottom `{`.
    /// A closer with none open is an orphan and discards nothing.
    fn close(&mut self, index: usize, expected: SyntaxKind) {
        if *self.count(expected) == 0 {
            return;
        }
        while let Some((opener, kind)) = self.openers.pop() {
            *self.count(kind) -= 1;
            if kind != expected {
                continue;
            }
            if self.openers.is_empty() && kind == SyntaxKind::LBrace {
                self.openers.push((opener, kind));
                self.braces += 1;
                if !self.trailing {
                    self.candidate = Some(index);
                    self.trailing = true;
                }
            } else {
                self.pair(opener, index);
            }
            return;
        }
    }

    /// Pair the bottom `{` with its candidate, if any — whatever followed
    /// the candidate: the last `}` to reach the body is its end, and what
    /// came after is garbage between items — and forget whatever opened
    /// after that: the next item starts clean.
    fn settle(&mut self) {
        if let Some(closer) = self.candidate.take() {
            let (opener, _) = self.openers[0];
            self.pair(opener, closer);
            self.openers.clear();
            self.parens = 0;
            self.braces = 0;
            self.trailing = false;
        }
    }

    fn pair(&mut self, opener: usize, closer: usize) {
        self.partners[opener] = NonZeroU32::new(closer as u32 + 1);
        self.partners[closer] = NonZeroU32::new(opener as u32 + 1);
    }
}

/// Openers less closers of each kind in one item — the tokens from one
/// `fn` to the next. A stray is one too many of its kind: a bracket with a
/// match to be had is no stray however its neighbours look.
#[derive(Clone, Copy, Default)]
struct Balance {
    parens: i32,
    braces: i32,
}

/// The [`Balance`] of every item, the tokens before the first `fn` first.
fn balances(kinds: &[SyntaxKind]) -> Vec<Balance> {
    let mut balances = vec![Balance::default()];
    for &kind in kinds {
        let balance = balances.last_mut().expect("one item at least");
        match kind {
            SyntaxKind::FnKw => balances.push(Balance::default()),
            SyntaxKind::LParen => balance.parens += 1,
            SyntaxKind::RParen => balance.parens -= 1,
            SyntaxKind::LBrace => balance.braces += 1,
            SyntaxKind::RBrace => balance.braces -= 1,
            _ => {}
        }
    }
    balances
}

/// Whether the bracket at `index` is a stray: one too many of its kind in
/// its item, and judged so by its neighbours. A closer is one when in the
/// middle of a line and wrong on both sides — after a token that cannot
/// end a statement, an opener and a `,` before a `)` aside, and before a
/// token on the same line that starts an operand — or when before an `=`
/// or `:`, which nothing closed can precede. A `(` is one after a `}` and
/// before a token nothing opened can precede, such as `else`, `mut`, an
/// `=` or a `:` — a call on a block is no call; after a name, garbage
/// inside a real call is the likelier reading. A bracket wrong on one side
/// only stays a bracket: `x = }` at the end of a line is how an editor
/// leaves a block while its last line is typed, and one at the start of a
/// line stands where a bracket is put.
fn stray_bracket(kinds: &[SyntaxKind], flags: &[u8], index: usize, balance: Balance) -> bool {
    let surplus = match kinds[index] {
        SyntaxKind::LParen => balance.parens > 0,
        SyntaxKind::RParen => balance.parens < 0,
        SyntaxKind::RBrace => balance.braces < 0,
        _ => return false,
    };
    if !surplus || flags[index] & NEWLINE_BEFORE != 0 {
        return false;
    }
    let Some(&next) = kinds
        .get(index + 1)
        .filter(|_| flags[index + 1] & NEWLINE_BEFORE == 0)
    else {
        return false;
    };
    // `==` and `!=` are operators, which may well follow a bracket.
    let glued_to_eq =
        flags[index + 1] & JOINT != 0 && kinds.get(index + 2) == Some(&SyntaxKind::Eq);
    let lone_eq = next == SyntaxKind::Eq && !glued_to_eq;
    match kinds[index] {
        SyntaxKind::LParen => {
            let previous = index.checked_sub(1).map(|index| kinds[index]);
            let after_wrong = lone_eq
                || matches!(
                    next,
                    SyntaxKind::ElseKw
                        | SyntaxKind::MutKw
                        | SyntaxKind::LetKw
                        | SyntaxKind::ReturnKw
                        | SyntaxKind::FnKw
                        | SyntaxKind::Colon
                        | SyntaxKind::Dot
                );
            previous == Some(SyntaxKind::RBrace) && after_wrong
        }
        _ => {
            if lone_eq || next == SyntaxKind::Colon {
                return true;
            }
            let before_wrong = index > 0 && {
                let previous = kinds[index - 1];
                let fine = can_end_statement(previous)
                    || matches!(previous, SyntaxKind::LParen | SyntaxKind::LBrace)
                    || (previous == SyntaxKind::Comma && kinds[index] == SyntaxKind::RParen);
                !fine
            };
            before_wrong && starts_operand(next) && !(next == SyntaxKind::Bang && glued_to_eq)
        }
    }
}

/// Whether a binary operator follows the `{` at `index` on its line: the
/// expression around the `{` runs straight through it.
fn operator_after(kinds: &[SyntaxKind], flags: &[u8], index: usize) -> bool {
    let Some(&next) = kinds
        .get(index + 1)
        .filter(|_| flags[index + 1] & NEWLINE_BEFORE == 0)
    else {
        return false;
    };
    let joint_to_eq =
        flags[index + 1] & JOINT != 0 && kinds.get(index + 2) == Some(&SyntaxKind::Eq);
    let doubled = flags[index + 1] & JOINT != 0 && kinds.get(index + 2) == Some(&next);
    match next {
        SyntaxKind::Plus
        | SyntaxKind::Star
        | SyntaxKind::Slash
        | SyntaxKind::Percent
        | SyntaxKind::Lt
        | SyntaxKind::Gt => true,
        // Only `&&` and `||` are operators.
        SyntaxKind::Amp | SyntaxKind::Pipe => doubled,
        // Glued to its operand, `-` or `!` starts a statement instead.
        SyntaxKind::Minus => flags[index + 1] & JOINT == 0,
        SyntaxKind::Bang | SyntaxKind::Eq => joint_to_eq,
        _ => false,
    }
}

/// Whether a token of this kind starts an operand and could not follow a
/// closer: the expression starts other than `-`, which may be binary, `(`,
/// which may make a call, and `{`, which may be an `if`'s block.
fn starts_operand(kind: SyntaxKind) -> bool {
    kind.starts_expression()
        && !matches!(
            kind,
            SyntaxKind::Minus | SyntaxKind::LParen | SyntaxKind::LBrace
        )
}

/// Whether a statement can end after a token of this kind: values and
/// closers can; operators, openers, and introducer keywords need more.
fn can_end_statement(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Ident
            | SyntaxKind::Underscore
            | SyntaxKind::TrueKw
            | SyntaxKind::FalseKw
            | SyntaxKind::ReturnKw
            | SyntaxKind::IntLiteral
            | SyntaxKind::FloatLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::RawStringLiteral
            | SyntaxKind::CharLiteral
            | SyntaxKind::RParen
            | SyntaxKind::RBrace
            | SyntaxKind::Error
    )
}

/// Whether the token at `index` continues a statement left open on the
/// previous line.
///
/// Continuation tokens are ones that can never start a statement: `else`
/// and binary operators, compounds included. `-` is binary exactly when it
/// is not glued to what follows — `- b` continues, `-b` opens a negation,
/// and the `->` of an arrow never continues. `(` could not start a
/// statement either, but deliberately does not continue: arguments must not
/// attach to a callee across a line break. The set mirrors the grammar: a
/// leading `.` joins it with member access.
fn continues_statement(kinds: &[SyntaxKind], flags: &[u8], index: usize) -> bool {
    let joint_to =
        |kind: SyntaxKind| flags[index] & JOINT != 0 && kinds.get(index + 1) == Some(&kind);
    match kinds[index] {
        SyntaxKind::ElseKw
        | SyntaxKind::Plus
        | SyntaxKind::Star
        | SyntaxKind::Slash
        | SyntaxKind::Percent
        | SyntaxKind::Lt
        | SyntaxKind::Gt => true,
        SyntaxKind::Minus => flags[index] & JOINT == 0,
        SyntaxKind::Eq | SyntaxKind::Bang => joint_to(SyntaxKind::Eq),
        SyntaxKind::Amp => joint_to(SyntaxKind::Amp),
        SyntaxKind::Pipe => joint_to(SyntaxKind::Pipe),
        _ => false,
    }
}
