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

/// One significant token's stream facts, packed so the kind, flags, raw
/// index, and partner the parser reads at one cursor position share a cache
/// line instead of four allocations.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Slot {
    pub(crate) kind: SyntaxKind,
    flags: u8,
    /// The token's index in the underlying token buffer.
    token: u32,
    /// The index of the bracket matching this one plus one, so the field
    /// has a niche; `None` for anything that is not a matched bracket.
    partner: Option<NonZeroU32>,
}

/// The significant tokens of one cooked file, with jointness and statement
/// boundaries precomputed.
#[derive(Clone, Debug)]
pub struct ParserInput {
    slots: Box<[Slot]>,
    /// Prefix sums of the boundary bits: entry `index` counts the statement
    /// boundaries before tokens `0..index`, so any-boundary-in-range is two
    /// lookups however long the range.
    boundaries: Box<[u32]>,
    /// The significant indices where top-level items start, in order.
    items: Box<[u32]>,
    /// The length of the underlying token buffer.
    raw_len: u32,
}

impl ParserInput {
    pub fn new(cooked: &CookedFile) -> Self {
        // Sized exactly and filled once: counting the significant tokens
        // first is one cheap scan, and spares both the doubling
        // reallocations of a growing vector and a final shrink.
        let kinds = cooked.kinds();
        let significant = kinds.iter().filter(|&&kind| !is_trivia(kind)).count();
        let mut build = Build {
            slots: Vec::with_capacity(significant),
            openers: Vec::new(),
            parens: 0,
            braces: 0,
        };

        // One pass strips trivia and pairs brackets as their closers
        // arrive. Boundaries and item starts replay the same opener stack
        // but need pairs whose closers lie ahead — whether an open `(` is
        // ever closed — so they wait for the second pass below.
        let mut newline = false;
        for (raw, &kind) in kinds.iter().enumerate() {
            match kind {
                SyntaxKind::Whitespace | SyntaxKind::LineComment => continue,
                SyntaxKind::Newline => {
                    newline = true;
                    continue;
                }
                _ => {}
            }
            build.push(kind, raw as u32, newline);
            newline = false;
        }

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
        let Build {
            mut slots,
            openers: mut open,
            ..
        } = build;
        open.clear();
        let mut boundaries: Vec<u32> = Vec::with_capacity(slots.len() + 1);
        let mut boundary_count: u32 = 0;
        let mut items: Vec<u32> = Vec::new();
        let mut matched = 0usize;
        for index in 0..slots.len() {
            boundaries.push(boundary_count);
            let slot = slots[index];
            if index > 0
                && slot.flags & NEWLINE_BEFORE != 0
                && !open.last().is_some_and(|&opener| {
                    let opener = slots[opener as usize];
                    opener.kind == SyntaxKind::LParen && opener.partner.is_some()
                })
                && can_end_statement(slots[index - 1].kind)
                && !continues_statement(&slots, index)
            {
                slots[index].flags |= BOUNDARY_BEFORE;
                boundary_count += 1;
            }
            if matched == 0 && starts_item(&slots, index) {
                items.push(index as u32);
            }
            match slot.kind {
                SyntaxKind::LParen | SyntaxKind::LBrace => {
                    open.push(index as u32);
                    if slot.partner.is_some() {
                        matched += 1;
                    }
                }
                SyntaxKind::RParen | SyntaxKind::RBrace => {
                    if let Some(partner) = slot.partner {
                        let opener = partner.get() - 1;
                        while open.pop().is_some_and(|popped| popped != opener) {}
                        matched -= 1;
                    }
                }
                _ => {}
            }
        }
        boundaries.push(boundary_count);

        Self {
            slots: slots.into_boxed_slice(),
            boundaries: boundaries.into_boxed_slice(),
            items: items.into_boxed_slice(),
            raw_len: cooked.len() as u32,
        }
    }

    /// The number of significant tokens.
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// The kind of significant token `index`, or `None` past the end. End of
    /// input is the end of the buffer, never a sentinel kind.
    pub fn get(&self, index: usize) -> Option<SyntaxKind> {
        self.slots.get(index).map(|slot| slot.kind)
    }

    /// The index of significant token `index` in the lexed and cooked token
    /// buffers, for ranges, text, and flags.
    pub fn token(&self, index: usize) -> u32 {
        self.slots[index].token
    }

    /// The number of tokens in the underlying buffer: one past the last raw
    /// index, where ranges that run to end of input stop.
    pub(crate) fn raw_len(&self) -> u32 {
        self.raw_len
    }

    /// Whether token `index` is glued to token `index + 1`: no trivia
    /// between them.
    pub fn is_joint(&self, index: usize) -> bool {
        self.slots[index].flags & JOINT != 0
    }

    /// Whether at least one line break sits between token `index` and the
    /// previous significant token.
    pub fn newline_before(&self, index: usize) -> bool {
        self.slots[index].flags & NEWLINE_BEFORE != 0
    }

    /// Whether a statement boundary immediately precedes token `index` under
    /// the newline rule. Never true for the first token.
    pub fn boundary_before(&self, index: usize) -> bool {
        self.slots[index].flags & BOUNDARY_BEFORE != 0
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
        self.slots[index]
            .partner
            .map(|partner| partner.get() as usize - 1)
    }

    /// The significant indices where top-level items start, in order: a
    /// `fn`, or the headless signature shape, outside every matched
    /// bracket pair.
    pub fn item_starts(&self) -> &[u32] {
        &self.items
    }

    /// The significant token slots as a slice, so the parser can hold a
    /// prefix of it as its input horizon.
    pub(crate) fn slots(&self) -> &[Slot] {
        &self.slots
    }
}

fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
    )
}

/// The build in progress: the slots so far, and mechanical bracket pairing
/// threaded through the same pass. A closer with a compatible opener
/// discards unmatched openers above its nearest match; an orphan closer
/// changes nothing. Every opener is pushed and popped at most once, so
/// pairing is linear even over long runs of opposite delimiters.
struct Build {
    slots: Vec<Slot>,
    /// The brackets still open, innermost last, by slot index.
    openers: Vec<u32>,
    /// How many of them are `(`, and how many `{`, so an orphan closer is
    /// known without a search.
    parens: usize,
    braces: usize,
}

impl Build {
    /// Append one significant token: glue it to a raw-adjacent predecessor,
    /// and pair it if it is a bracket.
    fn push(&mut self, kind: SyntaxKind, raw: u32, newline: bool) {
        if let Some(last) = self.slots.last_mut()
            && last.token + 1 == raw
        {
            last.flags |= JOINT;
        }
        let index = self.slots.len() as u32;
        let partner = match kind {
            SyntaxKind::LParen | SyntaxKind::LBrace => {
                self.open(index, kind);
                None
            }
            SyntaxKind::RParen => self.close(index, SyntaxKind::LParen),
            SyntaxKind::RBrace => self.close(index, SyntaxKind::LBrace),
            _ => None,
        };
        self.slots.push(Slot {
            kind,
            flags: if newline { NEWLINE_BEFORE } else { 0 },
            token: raw,
            partner,
        });
    }

    fn count(&mut self, kind: SyntaxKind) -> &mut usize {
        if kind == SyntaxKind::LParen {
            &mut self.parens
        } else {
            &mut self.braces
        }
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
/// a signature missing it — a name, a parenthesized list, and a body or
/// return type after the list on its line, which nothing else at the top
/// level looks like. A misplaced call has neither after its list, and
/// stays garbage. The caller has established that no matched bracket pair
/// encloses `index`.
fn starts_item(slots: &[Slot], index: usize) -> bool {
    if slots[index].kind == SyntaxKind::FnKw {
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
                        || (next.kind == SyntaxKind::Minus
                            && next.flags & JOINT != 0
                            && slots.get(after + 1).map(|slot| slot.kind) == Some(SyntaxKind::Gt)))
            })
        })
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
fn continues_statement(slots: &[Slot], index: usize) -> bool {
    let joint_to = |kind: SyntaxKind| {
        slots[index].flags & JOINT != 0 && slots.get(index + 1).map(|slot| slot.kind) == Some(kind)
    };
    match slots[index].kind {
        SyntaxKind::ElseKw
        | SyntaxKind::Plus
        | SyntaxKind::Star
        | SyntaxKind::Slash
        | SyntaxKind::Percent
        | SyntaxKind::Lt
        | SyntaxKind::Gt => true,
        SyntaxKind::Minus => slots[index].flags & JOINT == 0,
        SyntaxKind::Eq | SyntaxKind::Bang => joint_to(SyntaxKind::Eq),
        SyntaxKind::Amp => joint_to(SyntaxKind::Amp),
        SyntaxKind::Pipe => joint_to(SyntaxKind::Pipe),
        _ => false,
    }
}
