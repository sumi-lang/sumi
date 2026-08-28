//! The parser's token stream: significant tokens plus the stream facts the
//! grammar needs once trivia is gone.
//!
//! Construction strips whitespace, newlines, and comments, and precomputes
//! three per-token facts:
//!
//! - **jointness**: no trivia separates the token from its successor. The
//!   parser glues compound operators (`==`, `->`) from joint pairs, and the
//!   spacing rules for operator arity (unary glued, binary spaced) read the
//!   same bit.
//! - **newline before**: at least one line break sits in the trivia before
//!   the token.
//! - **boundary before**: that line break ends a statement under the newline
//!   rule below.
//!
//! # The newline rule
//!
//! Jolt has no `;`; statements end at line breaks. A newline is a statement
//! boundary iff all of:
//!
//! 1. it is not inside parentheses — `(...)` suspends termination, and a
//!    `{...}` within restores it;
//! 2. the token before it can end a statement: an identifier, a literal,
//!    `true`/`false`, `return`, `)`, or `}`;
//! 3. the token after it cannot continue one: `.`, `else`, and binary
//!    operators continue the previous line; everything else starts fresh.
//!
//! The bits record where statements end; the bans that keep the rule
//! unambiguous (trailing operators, unglued unary operators) are enforced by
//! the parser, where the grammar position gives diagnostics their context.

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

        // Boundaries look at the following token's jointness, so they need
        // the fully built stream: a second pass.
        let mut brackets: Vec<SyntaxKind> = Vec::new();
        for index in 0..kinds.len() {
            if index > 0
                && flags[index] & NEWLINE_BEFORE != 0
                && brackets.last() != Some(&SyntaxKind::LParen)
                && can_end_statement(kinds[index - 1])
                && !continues_statement(&kinds, &flags, index)
            {
                flags[index] |= BOUNDARY_BEFORE;
            }

            // Every closer is a synchronization point: discard openers until
            // its match or the bottom of the stack. This keeps malformed
            // nesting from wedging termination and makes recovery linear even
            // for long runs of opposite delimiters.
            match kinds[index] {
                SyntaxKind::LParen | SyntaxKind::LBrace => brackets.push(kinds[index]),
                SyntaxKind::RParen | SyntaxKind::RBrace => {
                    let expected = if kinds[index] == SyntaxKind::RParen {
                        SyntaxKind::LParen
                    } else {
                        SyntaxKind::LBrace
                    };
                    while let Some(opener) = brackets.pop() {
                        if opener == expected {
                            break;
                        }
                    }
                }
                _ => {}
            }
        }

        Self {
            kinds: kinds.into_boxed_slice(),
            tokens: tokens.into_boxed_slice(),
            flags: flags.into_boxed_slice(),
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
}

/// Whether a statement can end after a token of this kind: values and
/// closers can; operators, openers, and introducer keywords need more.
fn can_end_statement(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Ident
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
/// Continuation tokens are ones that can never start a statement: `.`,
/// `else`, and binary operators, compounds included. `-` is binary exactly
/// when it is not glued to what follows — `- b` continues, `-b` opens a
/// negation, and the `->` of an arrow never continues. `(` could not start a
/// statement either, but deliberately does not continue: arguments must not
/// attach to a callee across a line break.
fn continues_statement(kinds: &[SyntaxKind], flags: &[u8], index: usize) -> bool {
    let joint_to =
        |kind: SyntaxKind| flags[index] & JOINT != 0 && kinds.get(index + 1) == Some(&kind);
    match kinds[index] {
        SyntaxKind::Dot
        | SyntaxKind::ElseKw
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
