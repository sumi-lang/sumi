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
//!   one does. Pairing is mechanical: a closer pairs with the nearest open
//!   bracket of its kind, discarding unmatched openers above that match; an
//!   orphan closer discards nothing. Grammar decides whether a bracket is
//!   meaningful where it appears. The parser's recovery takes a matched
//!   pair whole only where the surrounding construct owns it.
//!
//! Construction also emits the **item segments**: the indices where
//! top-level items start — a `fn`, or the headless signature shape
//! [`starts_item`] recognizes, outside every matched bracket pair. A `fn`
//! inside a matched pair belongs to whatever construct owns the pair; one
//! outside begins the next item wherever the grammar stands, so the parser
//! turns each start into a hard end limit for the item before it.
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
use std::ops::Range;

use crate::cook::CookedFile;
use crate::kind::SyntaxKind;

const JOINT: u8 = 1 << 0;
const NEWLINE_BEFORE: u8 = 1 << 1;
const BOUNDARY_BEFORE: u8 = 1 << 2;

/// The significant tokens of one cooked file, with jointness and statement
/// boundaries precomputed.
#[derive(Clone, Debug)]
pub struct ParserInput {
    kinds: Box<[SyntaxKind]>,
    /// For each significant token, its index in the underlying token buffer.
    tokens: Box<[u32]>,
    flags: Box<[u8]>,
    /// Prefix sums of the boundary bits: entry `index` counts the statement
    /// boundaries before tokens `0..index`, so any-boundary-in-range is two
    /// lookups however long the range.
    boundaries: Box<[u32]>,
    /// For each significant token, the index of its matching bracket plus
    /// one, so the slot has a niche; `None` for anything that is not a
    /// matched bracket.
    partners: Box<[Option<NonZeroU32>]>,
    /// The significant indices where top-level items start, in order.
    items: Box<[u32]>,
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
        let partners = pair(&kinds).partners;

        // The brackets open before each token, replayed from the pairs: an
        // opener is open until its partner closes it, which discards
        // whatever opened inside and never closed; an orphan closer opens
        // and closes nothing. Only a `(` the stream closes suspends
        // termination — one it never closes would suspend it to the end of
        // the file, so the line ends the statement instead.
        //
        // The same replay finds the item starts: a matched opener encloses
        // everything up to its closer, so item starts exist only while
        // `matched` is zero. An unmatched opener encloses nothing for good
        // and hides no item.
        let mut open: Vec<usize> = Vec::new();
        let mut boundaries: Vec<u32> = Vec::with_capacity(kinds.len() + 1);
        let mut boundary_count: u32 = 0;
        let mut items: Vec<u32> = Vec::new();
        let mut matched = 0usize;
        for index in 0..kinds.len() {
            boundaries.push(boundary_count);
            if index > 0
                && flags[index] & NEWLINE_BEFORE != 0
                && !open.last().is_some_and(|&opener| {
                    kinds[opener] == SyntaxKind::LParen && partners[opener].is_some()
                })
                && can_end_statement(kinds[index - 1])
                && !continues_statement(&kinds, &flags, index)
            {
                flags[index] |= BOUNDARY_BEFORE;
                boundary_count += 1;
            }
            if matched == 0 && starts_item(&kinds, &flags, &partners, index) {
                items.push(index as u32);
            }
            match kinds[index] {
                SyntaxKind::LParen | SyntaxKind::LBrace => {
                    open.push(index);
                    if partners[index].is_some() {
                        matched += 1;
                    }
                }
                SyntaxKind::RParen | SyntaxKind::RBrace => {
                    if let Some(partner) = partners[index] {
                        let opener = partner.get() as usize - 1;
                        while open.pop().is_some_and(|popped| popped != opener) {}
                        matched -= 1;
                    }
                }
                _ => {}
            }
        }
        boundaries.push(boundary_count);

        Self {
            kinds: kinds.into_boxed_slice(),
            tokens: tokens.into_boxed_slice(),
            flags: flags.into_boxed_slice(),
            boundaries: boundaries.into_boxed_slice(),
            partners: partners.into_boxed_slice(),
            items: items.into_boxed_slice(),
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

    /// Whether a statement boundary precedes any token in `range`. Answered
    /// from the boundary prefix sums, so the cost does not grow with the
    /// range; recovery leans on this to reject a bracket group spanning a
    /// boundary without rescanning its interior. `range.end` may be `len()`.
    pub fn boundary_in(&self, range: Range<usize>) -> bool {
        self.boundaries[range.end] > self.boundaries[range.start]
    }

    /// The index of the bracket matching significant token `index`: an
    /// opener's closer or a closer's opener. `None` for an unmatched
    /// bracket, and for anything that is not one.
    pub fn partner(&self, index: usize) -> Option<usize> {
        self.partners[index].map(|partner| partner.get() as usize - 1)
    }

    /// The significant indices where top-level items start, in order: a
    /// `fn`, or the headless signature shape, outside every matched
    /// bracket pair.
    pub fn item_starts(&self) -> &[u32] {
        &self.items
    }

    /// The significant token kinds as a slice, so the parser can hold a
    /// prefix of it as its input horizon.
    pub(crate) fn kinds(&self) -> &[SyntaxKind] {
        &self.kinds
    }
}

/// Whether a top-level item starts at significant token `index`: `fn`, or
/// a signature missing it — a name, a parenthesized list, and a body or
/// return type after the list on its line, which nothing else at the top
/// level looks like. A misplaced call has neither after its list, and
/// stays garbage. The caller has established that no matched bracket pair
/// encloses `index`.
fn starts_item(
    kinds: &[SyntaxKind],
    flags: &[u8],
    partners: &[Option<NonZeroU32>],
    index: usize,
) -> bool {
    if kinds[index] == SyntaxKind::FnKw {
        return true;
    }
    (index == 0 || flags[index] & BOUNDARY_BEFORE != 0)
        && kinds[index] == SyntaxKind::Ident
        && kinds.get(index + 1) == Some(&SyntaxKind::LParen)
        && partners[index + 1].is_some_and(|partner| {
            // The partner encoding is the closer's index plus one: exactly
            // the token after the list.
            let after = partner.get() as usize;
            after < kinds.len()
                && flags[after] & NEWLINE_BEFORE == 0
                && (kinds[after] == SyntaxKind::LBrace
                    || (kinds[after] == SyntaxKind::Minus
                        && flags[after] & JOINT != 0
                        && kinds.get(after + 1) == Some(&SyntaxKind::Gt)))
        })
}

/// Mechanical bracket pairing over the significant tokens. A closer with a
/// compatible opener discards unmatched openers above its nearest match; an
/// orphan closer changes nothing. Every opener is pushed and popped at most
/// once, so pairing is linear even over long runs of opposite delimiters.
struct Pairing {
    partners: Vec<Option<NonZeroU32>>,
    /// The brackets still open, innermost last.
    openers: Vec<(usize, SyntaxKind)>,
    /// How many of them are `(`, and how many `{`, so an orphan closer is
    /// known without a search.
    parens: usize,
    braces: usize,
}

fn pair(kinds: &[SyntaxKind]) -> Pairing {
    let mut pairing = Pairing::new(kinds.len());
    for (index, &kind) in kinds.iter().enumerate() {
        match kind {
            SyntaxKind::LParen | SyntaxKind::LBrace => pairing.open(index, kind),
            SyntaxKind::RParen => pairing.close(index, SyntaxKind::LParen),
            SyntaxKind::RBrace => pairing.close(index, SyntaxKind::LBrace),
            _ => {}
        }
    }
    pairing
}

impl Pairing {
    fn new(len: usize) -> Self {
        Self {
            partners: vec![None; len],
            openers: Vec::new(),
            parens: 0,
            braces: 0,
        }
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
    }

    /// Close the innermost open `expected`, discarding openers above it.
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
            self.pair(opener, index);
            return;
        }
    }

    fn pair(&mut self, opener: usize, closer: usize) {
        self.partners[opener] = NonZeroU32::new(closer as u32 + 1);
        self.partners[closer] = NonZeroU32::new(opener as u32 + 1);
    }
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
