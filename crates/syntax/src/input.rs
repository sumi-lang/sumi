//! The parser's token stream: the significant tokens of a lexed file, with jointness, bracket
//! partners, statement boundaries, and item anchors precomputed. A line break ends a statement iff
//! no closed pair that does not enclose statements surrounds it, the token before it can end one,
//! and the token after it cannot continue one.

use std::num::NonZeroU32;
use std::ops::Range;

use crate::grammar::{
    Pair, Side, SyntaxKind, bracket, can_end_statement, continues_statement, starts_expression,
    starts_item,
};
use crate::index::SigIdx;
use sumi_lexer::{LexedFile, RawIdx};

const JOINT: u8 = 1 << 0;
const NEWLINE_BEFORE: u8 = 1 << 1;
const BOUNDARY_BEFORE: u8 = 1 << 2;
const IN_EXPRESSION_DELIMITERS: u8 = 1 << 3;
const IN_MATCHED_DELIMITERS: u8 = 1 << 4;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Slot {
    pub(crate) kind: SyntaxKind,
    flags: u8,
    token: RawIdx,
    /// The matching bracket's slot index plus one.
    partner: Option<NonZeroU32>,
}

#[derive(Clone, Debug)]
pub struct ParserInput {
    slots: Box<[Slot]>,
    /// Tokens with a boundary before them, ascending.
    boundaries: Box<[SigIdx]>,
    item_anchors: Box<[SigIdx]>,
    /// One entry per raw index, plus a final entry past the end of the buffer.
    sig_at_or_after: Box<[SigIdx]>,
}

impl ParserInput {
    pub fn new(lexed: &LexedFile) -> Self {
        let significant = lexed.kinds().filter(|kind| !kind.is_trivia()).count();
        let mut build = Build {
            slots: Vec::with_capacity(significant),
            openers: Vec::new(),
            tops: [None; Pair::ALL.len()],
        };

        // Boundaries and anchors need to know which openers are ever closed, so they wait for the
        // second pass.
        let mut newline = false;
        let mut sig_at_or_after = Vec::with_capacity(lexed.end().to_usize() + 1);
        for (raw, kind) in lexed.indices().zip(lexed.kinds()) {
            sig_at_or_after.push(SigIdx::new(build.slots.len() as u32));
            if kind.is_trivia() {
                newline |= kind == SyntaxKind::Newline;
                continue;
            }
            build.push(kind, raw, newline);
            newline = false;
        }
        sig_at_or_after.push(SigIdx::new(build.slots.len() as u32));

        // Only an opener the stream closes suspends termination; one never closed would suspend it
        // to the end of the file.
        let Build { mut slots, .. } = build;
        let mut boundaries = Vec::new();
        let mut item_anchors: Vec<SigIdx> = Vec::new();
        let mut matched = 0usize;
        let mut context = 0u8;
        for index in 0..slots.len() {
            let slot = slots[index];
            slots[index].flags |= context | (u8::from(matched != 0) * IN_MATCHED_DELIMITERS);
            if slot.flags & NEWLINE_BEFORE != 0 && would_end_statement_at(&slots, index) {
                slots[index].flags |= BOUNDARY_BEFORE;
                boundaries.push(SigIdx::new(index as u32));
            }
            if matched == 0 && item_anchor_at(&slots, index) {
                item_anchors.push(SigIdx::new(index as u32));
            }
            match bracket(slot.kind) {
                Some((pair, Side::Open)) => {
                    context = u8::from(!pair.encloses_statements() && slot.partner.is_some())
                        * IN_EXPRESSION_DELIMITERS;
                    if slot.partner.is_some() {
                        matched += 1;
                    }
                }
                Some((_, Side::Close)) => {
                    if let Some(partner) = slot.partner {
                        // The opener's bit is its parent's context, so restoring it also discards
                        // unmatched inner openers.
                        let opener = (partner.get() - 1) as usize;
                        context = slots[opener].flags & IN_EXPRESSION_DELIMITERS;
                        matched -= 1;
                    }
                }
                None => {}
            }
        }

        Self {
            slots: slots.into_boxed_slice(),
            boundaries: boundaries.into_boxed_slice(),
            item_anchors: item_anchors.into_boxed_slice(),
            sig_at_or_after: sig_at_or_after.into_boxed_slice(),
        }
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// One past the last significant token.
    pub fn end(&self) -> SigIdx {
        SigIdx::new(self.slots.len() as u32)
    }

    pub fn indices(&self) -> impl DoubleEndedIterator<Item = SigIdx> + ExactSizeIterator {
        SigIdx::new(0).until(self.end())
    }

    pub fn get(&self, index: SigIdx) -> Option<SyntaxKind> {
        self.slots.get(index.to_usize()).map(|slot| slot.kind)
    }

    pub fn token(&self, index: SigIdx) -> RawIdx {
        self.slots[index.to_usize()].token
    }

    /// [`end`](Self::end) when no significant token follows `raw`.
    pub fn sig_at_or_after(&self, raw: RawIdx) -> SigIdx {
        self.sig_at_or_after[raw.to_usize()]
    }

    /// `index` may be [`end`](Self::end), for the trivia after the last token.
    pub fn trivia_before(&self, index: SigIdx) -> Range<RawIdx> {
        let start = match index.checked_sub(1) {
            Some(previous) => self.token(previous) + 1,
            None => RawIdx::new(0),
        };
        let end = if index == self.end() {
            self.raw_len()
        } else {
            self.token(index)
        };
        start..end
    }

    pub(crate) fn raw_len(&self) -> RawIdx {
        RawIdx::new(self.sig_at_or_after.len() as u32 - 1)
    }

    /// No trivia between token `index` and `index + 1`.
    pub fn is_joint(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & JOINT != 0
    }

    pub fn newline_before(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & NEWLINE_BEFORE != 0
    }

    /// The nearest opener enclosing `index` is matched and does not enclose statements; a bracket
    /// at `index` does not enclose itself.
    pub fn in_expression_delimiters(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & IN_EXPRESSION_DELIMITERS != 0
    }

    /// Some matched pair encloses `index`; a bracket at `index` does not enclose itself.
    pub fn in_matched_delimiters(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & IN_MATCHED_DELIMITERS != 0
    }

    pub fn boundary_before(&self, index: SigIdx) -> bool {
        self.slots[index.to_usize()].flags & BOUNDARY_BEFORE != 0
    }

    /// A signature missing its `fn` begins at `index`.
    pub fn headless_signature_at(&self, index: SigIdx) -> bool {
        headless_signature_at(&self.slots, index.to_usize())
    }

    /// [`boundary_before`](Self::boundary_before) as if a line break stood before `index`.
    pub fn would_end_statement(&self, index: SigIdx) -> bool {
        would_end_statement_at(&self.slots, index.to_usize())
    }

    /// [`would_end_statement`](Self::would_end_statement) with `glued` as the token joint to
    /// `index`, or none, in place of the source's spacing.
    pub fn would_end_statement_if(&self, index: SigIdx, glued: Option<SyntaxKind>) -> bool {
        would_end_statement_if(&self.slots, index.to_usize(), glued)
    }

    /// A boundary before any token in `range`, its first included.
    pub fn boundary_in(&self, range: Range<SigIdx>) -> bool {
        let first = self
            .boundaries
            .partition_point(|&boundary| boundary < range.start);
        self.boundaries
            .get(first)
            .is_some_and(|&boundary| boundary < range.end)
    }

    pub fn partner(&self, index: SigIdx) -> Option<SigIdx> {
        self.slots[index.to_usize()]
            .partner
            .map(|partner| SigIdx::new(partner.get() - 1))
    }

    /// Tokens beginning `fn name` or a headless signature outside every matched pair, ascending;
    /// not every item has one.
    pub fn item_anchors(&self) -> &[SigIdx] {
        &self.item_anchors
    }

    pub(crate) fn slots(&self) -> &[Slot] {
        &self.slots
    }
}

/// Per pair, the position in `openers` of its innermost opener, plus one.
type Tops = [Option<NonZeroU32>; Pair::ALL.len()];

/// An opener still open, with `tops` as it stood below it: a closer matches the innermost opener of
/// its pair and drops every opener above it.
struct Opener {
    slot: u32,
    tops: Tops,
}

struct Build {
    slots: Vec<Slot>,
    /// Innermost last.
    openers: Vec<Opener>,
    tops: Tops,
}

impl Build {
    fn push(&mut self, kind: SyntaxKind, raw: RawIdx, newline: bool) {
        if let Some(last) = self.slots.last_mut()
            && last.token + 1 == raw
        {
            last.flags |= JOINT;
        }
        let index = self.slots.len() as u32;
        let partner = match bracket(kind) {
            Some((pair, Side::Open)) => {
                self.open(index, pair);
                None
            }
            Some((pair, Side::Close)) => self.close(index, pair),
            None => None,
        };
        self.slots.push(Slot {
            kind,
            flags: if newline { NEWLINE_BEFORE } else { 0 },
            token: raw,
            partner,
        });
    }

    fn open(&mut self, slot: u32, pair: Pair) {
        self.openers.push(Opener {
            slot,
            tops: self.tops,
        });
        self.tops[pair.index()] = NonZeroU32::new(self.openers.len() as u32);
    }

    fn close(&mut self, closer: u32, pair: Pair) -> Option<NonZeroU32> {
        let position = (self.tops[pair.index()]?.get() - 1) as usize;
        let opener = &self.openers[position];
        let slot = opener.slot;
        self.tops = opener.tops;
        self.openers.truncate(position);
        self.slots[slot as usize].partner = NonZeroU32::new(closer + 1);
        NonZeroU32::new(slot + 1)
    }
}

/// No matched pair may enclose `index`. A headless signature after a boundary counts because
/// nothing else at file level looks like one.
fn item_anchor_at(slots: &[Slot], index: usize) -> bool {
    if starts_item(slots[index].kind) {
        // `_` is an invalid name but still marks a declaration head.
        return slots
            .get(index + 1)
            .is_some_and(|next| matches!(next.kind, SyntaxKind::Ident | SyntaxKind::Underscore));
    }
    (index == 0 || slots[index].flags & BOUNDARY_BEFORE != 0) && headless_signature_at(slots, index)
}

/// This matches exactly what the parser takes after the list; anything looser promises an item that
/// then parses as garbage.
fn headless_signature_at(slots: &[Slot], index: usize) -> bool {
    let kind = |index: usize| slots.get(index).map(|slot| slot.kind);
    let arrow = |index: usize| {
        kind(index) == Some(SyntaxKind::Minus)
            && slots[index].flags & JOINT != 0
            && kind(index + 1) == Some(SyntaxKind::Gt)
    };
    kind(index) == Some(SyntaxKind::Ident)
        && kind(index + 1) == Some(SyntaxKind::LParen)
        && slots[index + 1].flags & NEWLINE_BEFORE == 0
        && slots[index + 1].partner.is_some_and(|partner| {
            // The partner is the closer plus one, so this is the token after the list.
            let after = partner.get() as usize;
            match kind(after) {
                Some(SyntaxKind::LBrace) => true,
                Some(SyntaxKind::Eq) => {
                    kind(after + 1).is_some_and(starts_expression) && !arrow(after + 1)
                }
                _ => arrow(after),
            }
        })
}

fn would_end_statement_if(slots: &[Slot], index: usize, glued: Option<SyntaxKind>) -> bool {
    index > 0
        && index < slots.len()
        && slots[index].flags & IN_EXPRESSION_DELIMITERS == 0
        && can_end_statement(slots[index - 1].kind)
        && !continues_statement(slots[index].kind, glued)
}

fn would_end_statement_at(slots: &[Slot], index: usize) -> bool {
    let glued = slots
        .get(index)
        .filter(|slot| slot.flags & JOINT != 0)
        .and_then(|_| slots.get(index + 1))
        .map(|slot| slot.kind);
    would_end_statement_if(slots, index, glued)
}
