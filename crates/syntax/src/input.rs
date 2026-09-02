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
//! [`item_starts_at`] recognizes, outside every matched bracket pair. A `fn`
//! inside a matched pair belongs to whatever construct owns the pair; one
//! outside begins the next item wherever the grammar stands, so the parser
//! turns each start into a hard end limit for the item before it.
//!
//! # The newline rule
//!
//! Sumi has no `;`; statements end at line breaks. A newline is a statement
//! boundary iff all of:
//!
//! 1. it is not inside a bracket pair the stream closes whose kind does not
//!    enclose statements — `(...)` suspends termination, and a `{...}`
//!    within restores it; a `(` never closed suspends nothing, so the line
//!    ends the statement it would otherwise swallow;
//! 2. the token before it can end a statement: an identifier or `_`, a
//!    literal, `true`/`false`, `return`, `)`, or `}`;
//! 3. the token after it cannot continue one: `else` and binary operators
//!    continue the previous line; everything else starts fresh. Both sets
//!    are the grammar's, generated from `sumi.grammar`.
//!
//! The bits record where statements end; the bans that keep the rule
//! unambiguous (trailing operators, unglued unary operators) are enforced by
//! the parser, where the grammar position gives diagnostics their context.

use std::num::NonZeroU32;
use std::ops::Range;

use crate::generated::{
    BRACKET_PAIRS, SyntaxKind, can_end_statement, continues_statement, encloses_statements,
    is_closer, is_opener, opener, pair_index, starts_item,
};
use crate::index::SigIdx;
use sumi_lexer::{LexedFile, RawIdx, RawKind};

const JOINT: u8 = 1 << 0;
const NEWLINE_BEFORE: u8 = 1 << 1;
const BOUNDARY_BEFORE: u8 = 1 << 2;

/// One significant token's stream facts, packed so the kind, flags, raw
/// index, and partner the parser reads at one cursor position share a cache
/// line instead of four allocations.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Slot {
    pub(crate) kind: SyntaxKind,
    flags: u8,
    /// The token's index in the underlying token buffer.
    token: RawIdx,
    /// The index of the bracket matching this one plus one, so the field
    /// has a niche; `None` for anything that is not a matched bracket.
    partner: Option<NonZeroU32>,
}

/// The significant tokens of one lexed file, with jointness and statement
/// boundaries precomputed.
#[derive(Clone, Debug)]
pub struct ParserInput {
    slots: Box<[Slot]>,
    /// Prefix sums of the boundary bits: entry `index` counts the statement
    /// boundaries before tokens `0..index`, so any-boundary-in-range is two
    /// lookups however long the range.
    boundaries: Box<[u32]>,
    /// The significant indices where top-level items start, in order.
    items: Box<[SigIdx]>,
    /// The index one past the last token of the underlying buffer.
    raw_len: RawIdx,
}

impl ParserInput {
    pub fn new(lexed: &LexedFile) -> Self {
        // Sized exactly and filled once: counting the significant tokens
        // first is one cheap scan, and spares both the doubling
        // reallocations of a growing vector and a final shrink.
        let significant = lexed.kinds().filter(|kind| !kind.is_trivia()).count();
        let mut build = Build {
            lexed,
            slots: Vec::with_capacity(significant),
            openers: Vec::new(),
            open_counts: [0; BRACKET_PAIRS.len()],
            holes: Vec::new(),
            literals: Vec::new(),
        };

        // One pass strips trivia and pairs brackets as their closers
        // arrive. Boundaries and item starts replay the same opener stack
        // but need pairs whose closers lie ahead — whether an open `(` is
        // ever closed — so they wait for the second pass below.
        let mut newline = false;
        for (raw, kind) in lexed.indices().zip(lexed.kinds()) {
            if kind.is_trivia() {
                newline |= kind == SyntaxKind::Newline;
                continue;
            }
            build.push(kind, raw, newline);
            newline = false;
        }

        // The brackets open before each token, replayed from the pairs: an
        // opener is open until its partner closes it, which discards
        // whatever opened inside and never closed; an orphan closer opens
        // and closes nothing. Only an opener the stream closes suspends
        // termination, and only one whose pair does not enclose statements
        // — one never closed would suspend it to the end of the file, so
        // the line ends the statement instead.
        //
        // The same replay finds the item starts: a matched opener encloses
        // everything up to its closer, so item starts exist only while
        // `matched` is zero. An unmatched opener encloses nothing for good
        // and hides no item.
        let Build {
            mut slots,
            openers: mut open,
            ..
        } = build;
        open.clear();
        let mut boundaries: Vec<u32> = Vec::with_capacity(slots.len() + 1);
        let mut boundary_count: u32 = 0;
        let mut items: Vec<SigIdx> = Vec::new();
        let mut matched = 0usize;
        for index in 0..slots.len() {
            boundaries.push(boundary_count);
            let slot = slots[index];
            if index > 0
                && slot.flags & NEWLINE_BEFORE != 0
                && !open.last().is_some_and(|&opener| {
                    let opener = slots[opener as usize];
                    !encloses_statements(opener.kind) && opener.partner.is_some()
                })
                && can_end_statement(slots[index - 1].kind)
                && !continues_line(&slots, index)
            {
                slots[index].flags |= BOUNDARY_BEFORE;
                boundary_count += 1;
            }
            if matched == 0 && item_starts_at(&slots, index) {
                items.push(SigIdx::new(index as u32));
            }
            if is_opener(slot.kind) {
                open.push(index as u32);
                if slot.partner.is_some() {
                    matched += 1;
                }
            } else if is_closer(slot.kind)
                && let Some(partner) = slot.partner
            {
                let opener = partner.get() - 1;
                while open.pop().is_some_and(|popped| popped != opener) {}
                matched -= 1;
            }
        }
        boundaries.push(boundary_count);

        Self {
            slots: slots.into_boxed_slice(),
            boundaries: boundaries.into_boxed_slice(),
            items: items.into_boxed_slice(),
            raw_len: lexed.end(),
        }
    }

    /// The number of significant tokens.
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// The index one past the last significant token: where a range running
    /// to the end of the input stops.
    pub fn end(&self) -> SigIdx {
        SigIdx::new(self.slots.len() as u32)
    }

    /// Every significant token's index, in order.
    pub fn indices(&self) -> impl DoubleEndedIterator<Item = SigIdx> + ExactSizeIterator {
        SigIdx::new(0).until(self.end())
    }

    /// The kind of significant token `index`, or `None` past the end. End of
    /// input is the end of the buffer, never a sentinel kind.
    pub fn get(&self, index: SigIdx) -> Option<SyntaxKind> {
        self.slots.get(index.to_usize()).map(|slot| slot.kind)
    }

    /// The index of significant token `index` in the raw lexed token
    /// buffer, for ranges, text, and flags.
    pub fn token(&self, index: SigIdx) -> RawIdx {
        self.slots[index.to_usize()].token
    }

    /// The index one past the last token of the underlying buffer, where
    /// ranges that run to end of input stop.
    pub(crate) fn raw_len(&self) -> RawIdx {
        self.raw_len
    }

    /// Whether token `index` is glued to token `index + 1`: no trivia
    /// between them.
    pub fn is_joint(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & JOINT != 0
    }

    /// Whether at least one line break sits between token `index` and the
    /// previous significant token.
    pub fn newline_before(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & NEWLINE_BEFORE != 0
    }

    /// Whether a statement boundary immediately precedes token `index` under
    /// the newline rule. Never true for the first token.
    pub fn boundary_before(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & BOUNDARY_BEFORE != 0
    }

    /// Whether a statement boundary precedes any token in `range`. Answered
    /// from the boundary prefix sums, so the cost does not grow with the
    /// range; recovery leans on this to reject a bracket group spanning a
    /// boundary without rescanning its interior. `range.end` may be
    /// [`end`](Self::end).
    pub fn boundary_in(&self, range: Range<SigIdx>) -> bool {
        self.boundaries[range.end.to_usize()] > self.boundaries[range.start.to_usize()]
    }

    /// The index of the bracket matching significant token `index`: an
    /// opener's closer or a closer's opener. `None` for an unmatched
    /// bracket, and for anything that is not one.
    pub fn partner(&self, index: SigIdx) -> Option<SigIdx> {
        self.slots[index.to_usize()]
            .partner
            .map(|partner| SigIdx::new(partner.get() - 1))
    }

    /// The significant indices where top-level items start, in order: a
    /// `fn`, or the headless signature shape, outside every matched
    /// bracket pair.
    pub fn item_starts(&self) -> &[SigIdx] {
        &self.items
    }

    /// The significant token slots as a slice, so the parser can hold a
    /// prefix of it as its input horizon.
    pub(crate) fn slots(&self) -> &[Slot] {
        &self.slots
    }
}

/// The build in progress: the slots so far, and mechanical bracket pairing
/// threaded through the same pass. A closer with a compatible opener
/// discards unmatched openers above its nearest match; an orphan closer
/// changes nothing. Every opener is pushed and popped at most once, so
/// pairing is linear even over long runs of opposite delimiters.
///
/// A hole in a string literal confines the brackets inside it: the lexer
/// closes a hole only from inside its literal, and a hole ends with its
/// line, so a bracket left open in a hole the lexer left open is discarded
/// where the hole ended — at the literal's next part, or at the line break
/// — and never pairs with a closer outside the literal.
struct Build<'a> {
    lexed: &'a LexedFile,
    slots: Vec<Slot>,
    /// The brackets still open, innermost last, by slot index.
    openers: Vec<u32>,
    /// How many of them belong to each pair, in [`BRACKET_PAIRS`] order, so
    /// an orphan closer is known without a search.
    open_counts: [usize; BRACKET_PAIRS.len()],
    /// The holes still open, innermost last: the slot of each one's `{`,
    /// and the open counts of the brackets around it, set aside while the
    /// hole's code pairs among itself. A closer in a hole finds no opener
    /// outside it, and an opener in a hole no closer outside it.
    holes: Vec<(u32, [usize; BRACKET_PAIRS.len()])>,
    /// The string literals with holes whose end is still ahead, innermost
    /// last: how many holes were open when each began, and whether it is
    /// a `"""` literal, whose text goes on past a line break.
    literals: Vec<(usize, bool)>,
}

impl Build<'_> {
    /// Append one significant token: glue it to a raw-adjacent predecessor,
    /// and pair it if it is a bracket. The bookkeeping of string literals
    /// with holes stays off the path every other token takes.
    fn push(&mut self, kind: SyntaxKind, raw: RawIdx, newline: bool) {
        if let Some(last) = self.slots.last_mut()
            && last.token + 1 == raw
        {
            last.flags |= JOINT;
        }
        // A line break ends every open hole; the check is the newline
        // tokens' alone.
        if newline && !self.holes.is_empty() {
            self.line_break();
        }
        if is_literal_token(kind) {
            self.literal_token(kind, raw);
        }
        let index = self.slots.len() as u32;
        let partner = if is_opener(kind) {
            self.open(index, kind);
            None
        } else {
            opener(kind).and_then(|expected| self.close(index, expected))
        };
        if kind == SyntaxKind::HoleClose
            && let Some(partner) = partner
        {
            self.hole_closed(partner.get() - 1);
        }
        self.slots.push(Slot {
            kind,
            flags: if newline { NEWLINE_BEFORE } else { 0 },
            token: raw,
            partner,
        });
    }

    /// The bookkeeping a string literal's token asks for before the token
    /// pairs: a literal's parts begin and end it and end the holes it left
    /// open, and a hole's `{` sets the brackets around it aside.
    #[inline(never)]
    fn literal_token(&mut self, kind: SyntaxKind, raw: RawIdx) {
        let index = self.slots.len() as u32;
        let block = self.lexed.raw_kind(raw) == RawKind::BlockString;
        match kind {
            SyntaxKind::StringStart => self.literals.push((self.holes.len(), block)),
            SyntaxKind::StringMiddle => self.literal_part(block, false),
            SyntaxKind::StringEnd => self.literal_part(block, true),
            SyntaxKind::HoleOpen => self
                .holes
                .push((index, std::mem::take(&mut self.open_counts))),
            _ => {}
        }
    }

    /// A hole's `}` paired with the `{` at `opener`: the brackets set aside
    /// at the `{` are the open ones again.
    #[inline(never)]
    fn hole_closed(&mut self, opener: u32) {
        while let Some(&(hole, _)) = self.holes.last()
            && hole >= opener
        {
            let (_, counts) = self.holes.pop().expect("a hole is open");
            self.open_counts = counts;
        }
    }

    /// A line break ends every open hole, and the `"…"` literals around
    /// them: whatever a hole left open is discarded.
    #[inline(never)]
    fn line_break(&mut self) {
        while let Some((hole, counts)) = self.holes.pop() {
            self.discard_from(hole);
            self.open_counts = counts;
        }
        while self.literals.last().is_some_and(|&(_, block)| !block) {
            self.literals.pop();
        }
    }

    /// A part of a string literal after a hole ends every hole opened since
    /// the literal began and not closed. A `"…"` literal nested in a `"""`
    /// literal's hole ended with the hole, before the `"""` literal's part.
    fn literal_part(&mut self, block: bool, end: bool) {
        while self
            .literals
            .last()
            .is_some_and(|&(_, is_block)| is_block != block)
        {
            self.literals.pop();
        }
        let Some(&(base, _)) = self.literals.last() else {
            return;
        };
        while self.holes.len() > base {
            let (hole, counts) = self.holes.pop().expect("more holes than the base");
            self.discard_from(hole);
            self.open_counts = counts;
        }
        if end {
            self.literals.pop();
        }
    }

    /// Discard the opener at slot `from` and every one opened after it.
    fn discard_from(&mut self, from: u32) {
        while let Some(&opener) = self.openers.last()
            && opener >= from
        {
            self.openers.pop();
            let kind = self.slots[opener as usize].kind;
            *self.count(kind) -= 1;
        }
    }

    /// The open count of the pair `opener` begins.
    fn count(&mut self, opener: SyntaxKind) -> &mut usize {
        let pair = pair_index(opener).expect("only openers are counted");
        &mut self.open_counts[pair]
    }

    fn open(&mut self, index: u32, kind: SyntaxKind) {
        self.openers.push(index);
        *self.count(kind) += 1;
    }

    /// Close the innermost open `expected`, discarding openers above it,
    /// and hand back the closer's own partner value. A closer with none
    /// open is an orphan and discards nothing.
    fn close(&mut self, closer: u32, expected: SyntaxKind) -> Option<NonZeroU32> {
        if *self.count(expected) == 0 {
            return None;
        }
        while let Some(opener) = self.openers.pop() {
            let kind = self.slots[opener as usize].kind;
            *self.count(kind) -= 1;
            if kind != expected {
                continue;
            }
            self.slots[opener as usize].partner = NonZeroU32::new(closer + 1);
            return NonZeroU32::new(opener + 1);
        }
        unreachable!("a nonzero count keeps a matching opener on the stack")
    }
}

/// Whether a top-level item starts at significant token `index`: `fn`, or
/// a signature missing it — a name, a parenthesized list, and a body,
/// a return type, or an expression body's `=` after the list on its line,
/// which nothing else at the top level looks like. A misplaced call has neither after its list, and
/// stays garbage. The caller has established that no matched bracket pair
/// encloses `index`.
fn item_starts_at(slots: &[Slot], index: usize) -> bool {
    if starts_item(slots[index].kind) {
        return true;
    }
    (index == 0 || slots[index].flags & BOUNDARY_BEFORE != 0)
        && slots[index].kind == SyntaxKind::Ident
        && slots.get(index + 1).map(|slot| slot.kind) == Some(SyntaxKind::LParen)
        && slots[index + 1].partner.is_some_and(|partner| {
            // The partner encoding is the closer's index plus one: exactly
            // the token after the list.
            let after = partner.get() as usize;
            slots.get(after).is_some_and(|next| {
                next.flags & NEWLINE_BEFORE == 0
                    && (next.kind == SyntaxKind::LBrace
                        || next.kind == SyntaxKind::Eq
                        || (next.kind == SyntaxKind::Minus
                            && next.flags & JOINT != 0
                            && slots.get(after + 1).map(|slot| slot.kind) == Some(SyntaxKind::Gt)))
            })
        })
}

/// Whether a token of this kind belongs to a string literal with holes:
/// its text, or a hole's brace.
fn is_literal_token(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::StringStart
            | SyntaxKind::StringMiddle
            | SyntaxKind::StringEnd
            | SyntaxKind::HoleOpen
            | SyntaxKind::HoleClose
    )
}

/// Whether the token at `index` continues the statement left open on the
/// previous line: the grammar's [`continues_statement`] over its kind and
/// the kind it is glued to. `(` could not start a statement either, but
/// deliberately does not continue: arguments must not attach to a callee
/// across a line break.
fn continues_line(slots: &[Slot], index: usize) -> bool {
    let glued = if slots[index].flags & JOINT != 0 {
        slots.get(index + 1).map(|slot| slot.kind)
    } else {
        None
    };
    continues_statement(slots[index].kind, glued)
}
