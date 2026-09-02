use sumi_text::TextSize;

use crate::file::LexErrorKind;
use crate::generated::SyntaxKind;
use crate::token::{RawKind, RawToken, TokenFlags};

/// The delimiter of a multi-line string literal, both ends.
const BLOCK_DELIMITER: &str = "\"\"\"";

/// A string literal whose text the scan has left for the code of a hole.
/// The scan resumes its text at the `}` that closes the hole, or at the
/// line break that leaves it open.
struct Frame {
    /// The literal's `StringStart`, as its index among the tokens emitted.
    start: u32,
    /// The hole's `{`, likewise: where a hole left open is reported.
    hole: u32,
    /// Braces opened in the hole's code and not yet closed; the `}` at
    /// depth zero closes the hole.
    depth: u32,
    /// Whether the literal is a `"""` one, whose text resumes after a hole
    /// left open, rather than a `"…"` one, which ends with the hole's line.
    block: bool,
}

/// A string literal whose text the scan is in between tokens: after a
/// hole's `}`, the next token is more of its text, its next hole's `{`, or
/// its end.
#[derive(Clone, Copy)]
struct Text {
    start: u32,
    block: bool,
}

/// Where the text of a string literal stopped.
enum Stop {
    /// At a `{`, not consumed: a hole opens.
    Hole,
    /// At the closing quotes, consumed.
    Closer,
    /// At the line break, or the end of input for a `"""` literal, not
    /// consumed: the literal is unterminated.
    End,
}

/// An error known only after its token was emitted: a hole left open at its
/// line break, or a literal with holes never closed, reported at its
/// opener as a whole literal is.
pub(crate) struct LateError {
    /// The token's index among those emitted.
    pub(crate) token: u32,
    /// How many of the token's leading bytes the error covers, or the
    /// whole token.
    pub(crate) prefix: Option<usize>,
    pub(crate) kind: LexErrorKind,
}

const fn is_ascii_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

fn is_ident_continue(ch: char) -> bool {
    ch == '_'
        || ch.is_ascii_alphanumeric()
        || (!ch.is_ascii() && unicode_ident::is_xid_continue(ch))
}

pub(crate) struct Lexer<'src> {
    source: &'src str,
    position: usize,
    /// The literals whose holes the scan is inside, innermost last.
    frames: Vec<Frame>,
    /// The literal whose text the next token continues, if any.
    text: Option<Text>,
    /// Whether either is set: the one load the scan of every token makes.
    in_literal: bool,
    /// Whether a hole was opened, so a later pass knows whether any is
    /// there to find; and whether one was in a `"""` literal, so the
    /// collector knows whether any is left to judge.
    holes: bool,
    block_holes: bool,
    /// The tokens emitted so far: the index the next one takes.
    emitted: u32,
    late: Vec<LateError>,
}
impl<'src> Lexer<'src> {
    /// The caller must have validated that `source.len()` fits in `u32`.
    pub(crate) const fn new(source: &'src str) -> Self {
        Self {
            source,
            position: 0,
            frames: Vec::new(),
            text: None,
            in_literal: false,
            holes: false,
            block_holes: false,
            emitted: 0,
            late: Vec::new(),
        }
    }

    /// Whether a hole's `{` was emitted.
    pub(crate) fn holes(&self) -> bool {
        self.holes
    }

    /// Whether a `"""` literal with holes was emitted.
    pub(crate) fn block_holes(&self) -> bool {
        self.block_holes
    }

    fn sync(&mut self) {
        self.in_literal = self.text.is_some() || !self.frames.is_empty();
    }

    fn set_text(&mut self, text: Option<Text>) {
        self.text = text;
        self.sync();
    }

    fn take_text(&mut self) -> Option<Text> {
        let text = self.text.take();
        self.sync();
        text
    }

    fn push_frame(&mut self, frame: Frame) {
        self.frames.push(frame);
        self.sync();
    }

    fn pop_frame(&mut self) -> Option<Frame> {
        let frame = self.frames.pop();
        self.sync();
        frame
    }

    /// The errors known only after their tokens were emitted, once the
    /// scan has reached the end of input.
    pub(crate) fn into_late_errors(self) -> Vec<LateError> {
        debug_assert_eq!(self.position, self.source.len());
        self.late
    }

    fn remaining(&self) -> &'src str {
        &self.source[self.position..]
    }

    fn peek_byte(&self) -> Option<u8> {
        self.source.as_bytes().get(self.position).copied()
    }

    fn peek_byte_at(&self, offset: usize) -> Option<u8> {
        self.source.as_bytes().get(self.position + offset).copied()
    }

    fn bump_ascii(&mut self) -> u8 {
        let byte = self.source.as_bytes()[self.position];
        debug_assert!(byte.is_ascii());
        self.position += 1;
        byte
    }

    fn bump_char(&mut self) -> char {
        let ch = self.remaining().chars().next().expect("cannot bump at EOF");
        self.position += ch.len_utf8();
        ch
    }

    fn scan_token(&mut self) -> RawToken {
        let start = self.position;

        // Inside a literal with holes — its text to resume, or a hole's code
        // — the literal owes tokens before any other; the check is two
        // loads, and the rest stays off the path every other token takes.
        let literal = if self.in_literal {
            self.scan_literal_token()
        } else {
            None
        };
        let (kind, raw, flags) = if let Some(token) = literal {
            token
        } else if self.position == 0 && self.remaining().starts_with('\u{feff}') {
            self.bump_char();
            // The BOM is ignorable trivia to every downstream phase; its
            // identity stays recoverable through the raw kind.
            (SyntaxKind::Whitespace, RawKind::Bom, TokenFlags::EMPTY)
        } else {
            match self.peek_byte().expect("scan_token called at EOF") {
                b' ' | b'\t' => {
                    self.scan_horizontal_space();
                    (
                        SyntaxKind::Whitespace,
                        RawKind::HorizontalSpace,
                        TokenFlags::EMPTY,
                    )
                }
                b'\n' | b'\r' => (SyntaxKind::Newline, RawKind::Newline, self.scan_newline()),
                b'/' if self.remaining().starts_with("//") => (
                    SyntaxKind::LineComment,
                    RawKind::LineComment,
                    self.scan_line_comment(),
                ),
                b'0'..=b'9' => {
                    let (kind, flags) = self.scan_number();
                    (kind, RawKind::Number, flags)
                }
                b'"' if self.remaining().starts_with(BLOCK_DELIMITER) => self.scan_string(true),
                b'"' => self.scan_string(false),
                b'\'' => (
                    SyntaxKind::CharLiteral,
                    RawKind::Char,
                    self.scan_line_literal(b'\''),
                ),
                b'r' if self.remaining()[1..].starts_with(BLOCK_DELIMITER) => (
                    SyntaxKind::RawBlockStringLiteral,
                    RawKind::RawBlockString,
                    self.scan_block_string(1 + BLOCK_DELIMITER.len()),
                ),
                b'r' if self.looks_like_raw_string() => (
                    SyntaxKind::RawStringLiteral,
                    RawKind::RawString,
                    self.scan_raw_string(),
                ),
                byte if is_ascii_ident_start(byte) => {
                    self.scan_ident();
                    (
                        self.classify_ident(start),
                        RawKind::Ident,
                        TokenFlags::EMPTY,
                    )
                }
                byte if byte.is_ascii_punctuation() => {
                    self.bump_ascii();
                    let kind = SyntaxKind::from_punct(byte).unwrap_or(SyntaxKind::Error);
                    (kind, RawKind::Punct, TokenFlags::EMPTY)
                }
                byte if !byte.is_ascii() => self.scan_unicode(start),
                _ => {
                    self.bump_ascii();
                    (SyntaxKind::Error, RawKind::Unknown, TokenFlags::EMPTY)
                }
            }
        };

        let len = self.position - start;
        debug_assert!(len > 0, "scan_token must always make progress");

        RawToken {
            kind,
            raw,
            len: TextSize::new(u32::try_from(len).expect("source length fits in u32")),
            flags,
        }
    }

    fn scan_horizontal_space(&mut self) {
        while matches!(self.peek_byte(), Some(b' ' | b'\t')) {
            self.position += 1;
        }
    }

    fn scan_newline(&mut self) -> TokenFlags {
        match self.bump_ascii() {
            b'\n' => TokenFlags::EMPTY,
            b'\r' if self.peek_byte() == Some(b'\n') => {
                self.bump_ascii();
                TokenFlags::EMPTY
            }
            b'\r' => TokenFlags::LONE_CR,
            _ => unreachable!("scan_newline called off a newline byte"),
        }
    }

    fn scan_line_comment(&mut self) -> TokenFlags {
        self.bump_ascii();
        self.bump_ascii();

        let flags = match (self.peek_byte(), self.peek_byte_at(1)) {
            // `///` is an outer doc comment, but `////...` is decoration.
            (Some(b'/'), next) if next != Some(b'/') => TokenFlags::DOC_OUTER,
            (Some(b'!'), _) => TokenFlags::DOC_INNER,
            _ => TokenFlags::EMPTY,
        };

        let rest = self.remaining();
        let line_end = rest.find(['\n', '\r']).unwrap_or(rest.len());
        self.position += line_end;

        flags
    }

    /// Scan a number and classify it as an int or float literal. The scan
    /// also decides whether the token breaks a literal rule, so canonical
    /// numbers — the overwhelming majority — never get re-scanned by the
    /// collector.
    fn scan_number(&mut self) -> (SyntaxKind, TokenFlags) {
        let start = self.position;
        let first = self.bump_ascii();
        debug_assert!(first.is_ascii_digit());

        let mut malformed = false;
        self.eat_decimal_digits(&mut malformed);

        // A leading zero is a literal error (`0123` means octal in several
        // other languages); `0_` alone is only a misplaced underscore.
        if first == b'0'
            && self.source.as_bytes()[start + 1..self.position]
                .iter()
                .any(u8::is_ascii_digit)
        {
            malformed = true;
        }

        let mut is_float = false;

        // A `.` continues the number only when a digit follows, so `1..2`
        // and `1.foo` leave the dot to punctuation.
        if self.peek_byte() == Some(b'.')
            && self
                .peek_byte_at(1)
                .is_some_and(|byte| byte.is_ascii_digit())
        {
            is_float = true;
            self.bump_ascii();
            self.eat_decimal_digits(&mut malformed);
        }

        // An exponent needs a digit after the optional sign; otherwise the
        // `e` is left to the suffix, as in `1em`.
        let mut has_exponent = false;
        if matches!(self.peek_byte(), Some(b'e' | b'E')) {
            has_exponent = match (self.peek_byte_at(1), self.peek_byte_at(2)) {
                (Some(byte), _) if byte.is_ascii_digit() => true,
                (Some(b'+' | b'-'), Some(byte)) => byte.is_ascii_digit(),
                _ => false,
            };
            if has_exponent {
                is_float = true;
                // The shape munches `1E5` and `1e+5` so the token stays
                // whole; an uppercase marker or a `+` sign is an error.
                if self.bump_ascii() == b'E' {
                    malformed = true;
                }
                if matches!(self.peek_byte(), Some(b'+' | b'-')) && self.bump_ascii() == b'+' {
                    malformed = true;
                }
                let exponent_start = self.position;
                self.eat_decimal_digits(&mut malformed);
                let digits = &self.source.as_bytes()[exponent_start..self.position];
                if digits[0] == b'0' && digits[1..].iter().any(u8::is_ascii_digit) {
                    malformed = true;
                }
            }
        }

        // Trailing identifier characters attach as a literal suffix (`1u32`)
        // for the collector to reject. An `e`-leading suffix on a number with
        // no exponent is a broken exponent, and the intended shape was a
        // float.
        let suffix_start = self.position;
        self.eat_ident_continue();
        if self.position > suffix_start {
            malformed = true;
            if !has_exponent && matches!(self.source.as_bytes()[suffix_start], b'e' | b'E') {
                is_float = true;
            }
        }

        (
            if is_float {
                SyntaxKind::FloatLiteral
            } else {
                SyntaxKind::IntLiteral
            },
            if malformed {
                TokenFlags::MALFORMED_NUMBER
            } else {
                TokenFlags::EMPTY
            },
        )
    }

    /// Advance over a digit run, flagging any `_` that is not surrounded by
    /// digits on both sides: grouping style is free, but `1_`, `1__0`, and
    /// `1_.5` are typo-shaped.
    fn eat_decimal_digits(&mut self, malformed: &mut bool) {
        while let Some(byte) = self.peek_byte() {
            match byte {
                b'0'..=b'9' => self.position += 1,
                b'_' => {
                    // A number's first byte is a digit, so `position - 1`
                    // stays inside the token.
                    let digit_before = self.source.as_bytes()[self.position - 1].is_ascii_digit();
                    let digit_after = self
                        .peek_byte_at(1)
                        .is_some_and(|byte| byte.is_ascii_digit());
                    if !(digit_before && digit_after) {
                        *malformed = true;
                    }
                    self.position += 1;
                }
                _ => break,
            }
        }
    }

    /// The token a string literal with holes owes before any other: inside
    /// a hole, the braces, the line break, and the quotes belong to the
    /// literal around the hole; between a hole and the next, its text.
    #[inline(never)]
    fn scan_literal_token(&mut self) -> Option<(SyntaxKind, RawKind, TokenFlags)> {
        if let Some(text) = self.take_text()
            && let Some(token) = self.scan_text_token(text)
        {
            return Some(token);
        }
        let frame = self.frames.last_mut()?;
        match self.source.as_bytes().get(self.position)? {
            b'{' => {
                frame.depth += 1;
                self.position += 1;
                Some((SyntaxKind::LBrace, RawKind::Punct, TokenFlags::EMPTY))
            }
            b'}' if frame.depth > 0 => {
                frame.depth -= 1;
                self.position += 1;
                Some((SyntaxKind::RBrace, RawKind::Punct, TokenFlags::EMPTY))
            }
            b'}' => {
                let frame = self.pop_frame().expect("a frame is open");
                self.set_text(Some(Text {
                    start: frame.start,
                    block: frame.block,
                }));
                self.position += 1;
                Some((SyntaxKind::HoleClose, RawKind::Punct, TokenFlags::EMPTY))
            }
            // A hole ends with its line. The `"…"` literals around it end
            // there too; the innermost `"""` one takes the break as text.
            b'\n' | b'\r' => {
                self.leave_holes();
                let text = self.take_text()?;
                self.scan_text_token(text)
            }
            b'"' => Some(self.scan_quote_in_hole()),
            // The `"""` after an `r` closes the literal around the hole,
            // or the first quote of it does: the `r` is a name.
            b'r' if self.remaining()[1..].starts_with(BLOCK_DELIMITER) => {
                let start = self.position;
                self.scan_ident();
                Some((
                    self.classify_ident(start),
                    RawKind::Ident,
                    TokenFlags::EMPTY,
                ))
            }
            _ => None,
        }
    }

    /// Leave every hole the scan is inside, each reported at its `{`. The
    /// `"…"` literals around them end with the line; the innermost `"""`
    /// literal, if any, has its text resume.
    fn leave_holes(&mut self) {
        while let Some(frame) = self.pop_frame() {
            self.late.push(LateError {
                token: frame.hole,
                prefix: Some(1),
                kind: LexErrorKind::UnclosedHole,
            });
            if frame.block {
                self.set_text(Some(Text {
                    start: frame.start,
                    block: true,
                }));
                return;
            }
        }
    }

    /// Leave the holes and the literal text the scan is inside at the end
    /// of input: every hole is left open, and a `"""` literal or a `"…"`
    /// one between holes is unterminated.
    fn finish(&mut self) {
        while let Some(frame) = self.pop_frame() {
            self.late.push(LateError {
                token: frame.hole,
                prefix: Some(1),
                kind: LexErrorKind::UnclosedHole,
            });
            if frame.block {
                self.late.push(LateError {
                    token: frame.start,
                    prefix: Some(BLOCK_DELIMITER.len()),
                    kind: LexErrorKind::UnterminatedBlockString,
                });
            }
        }
        if let Some(text) = self.take_text() {
            self.late.push(unterminated(text));
        }
    }

    /// A quote inside a hole: a `"…"` literal of the hole's code, or the end
    /// of the literal around the hole. No hole holds a `"""` literal, so a
    /// `"""` inside a `"""` literal's hole closes that literal, and inside
    /// a `"…"` literal's hole a `"…"` literal that its line never closes,
    /// or that would close on the first quote of a `"""`, is that
    /// literal's closer instead. Either leaves the hole open.
    fn scan_quote_in_hole(&mut self) -> (SyntaxKind, RawKind, TokenFlags) {
        let block = self.frames.last().expect("a frame is open").block;
        if block && self.remaining().starts_with(BLOCK_DELIMITER) {
            self.leave_hole_at_closer();
            self.position += BLOCK_DELIMITER.len();
            return (
                SyntaxKind::StringEnd,
                RawKind::BlockString,
                TokenFlags::EMPTY,
            );
        }
        let quote = self.position;
        self.position += 1;
        let (stop, flags) = self.scan_string_text::<false>();
        match stop {
            Stop::Closer if block || !self.remaining().starts_with("\"\"") => {
                (SyntaxKind::StringLiteral, RawKind::String, flags)
            }
            Stop::Hole => {
                self.set_text(Some(Text {
                    start: self.emitted,
                    block: false,
                }));
                (SyntaxKind::StringStart, RawKind::String, flags)
            }
            Stop::End if block => (
                SyntaxKind::StringLiteral,
                RawKind::String,
                flags | TokenFlags::UNTERMINATED,
            ),
            Stop::End | Stop::Closer => {
                self.position = quote + 1;
                self.leave_hole_at_closer();
                (SyntaxKind::StringEnd, RawKind::String, TokenFlags::EMPTY)
            }
        }
    }

    /// Leave the innermost hole at its literal's closer, which leaves the
    /// hole open.
    fn leave_hole_at_closer(&mut self) {
        let frame = self.pop_frame().expect("a frame is open");
        self.late.push(LateError {
            token: frame.hole,
            prefix: Some(1),
            kind: LexErrorKind::UnclosedHole,
        });
    }

    /// Scan a `"…"` or `"""` literal from its opener: whole, when it has no
    /// hole, and otherwise up to its first `{`, as its start, with its text
    /// to resume after the hole. Out of line, so that the token loop stays
    /// small enough for the scans of every other token to inline into it.
    #[inline(never)]
    fn scan_string(&mut self, block: bool) -> (SyntaxKind, RawKind, TokenFlags) {
        let (raw, whole) = if block {
            (RawKind::BlockString, SyntaxKind::BlockStringLiteral)
        } else {
            (RawKind::String, SyntaxKind::StringLiteral)
        };
        let (stop, flags) = if block {
            self.position += BLOCK_DELIMITER.len();
            self.scan_string_text::<true>()
        } else {
            self.position += 1;
            self.scan_string_text::<false>()
        };
        match stop {
            Stop::Closer => (whole, raw, flags),
            Stop::End => (whole, raw, flags | TokenFlags::UNTERMINATED),
            Stop::Hole => {
                self.block_holes |= block;
                self.set_text(Some(Text {
                    start: self.emitted,
                    block,
                }));
                (SyntaxKind::StringStart, raw, flags)
            }
        }
    }

    /// The next token of a literal's text after a hole: the next hole's
    /// `{`, more text up to one, or the text through the closer. `None` at
    /// the line break, or the end of input, that leaves a `"…"` literal or
    /// a `"""` one unterminated with no text to take: the literal is
    /// reported and the break lexes as usual.
    fn scan_text_token(&mut self, text: Text) -> Option<(SyntaxKind, RawKind, TokenFlags)> {
        let raw = if text.block {
            RawKind::BlockString
        } else {
            RawKind::String
        };
        if self.peek_byte() == Some(b'{') {
            self.position += 1;
            self.holes = true;
            self.push_frame(Frame {
                start: text.start,
                hole: self.emitted,
                depth: 0,
                block: text.block,
            });
            return Some((SyntaxKind::HoleOpen, RawKind::Punct, TokenFlags::EMPTY));
        }
        let start = self.position;
        let (stop, flags) = if text.block {
            self.scan_string_text::<true>()
        } else {
            self.scan_string_text::<false>()
        };
        match stop {
            Stop::Hole => {
                self.set_text(Some(text));
                Some((SyntaxKind::StringMiddle, raw, flags))
            }
            Stop::Closer => Some((SyntaxKind::StringEnd, raw, flags)),
            Stop::End => {
                self.late.push(unterminated(text));
                (self.position > start).then_some((
                    SyntaxKind::StringEnd,
                    raw,
                    flags | TokenFlags::UNTERMINATED,
                ))
            }
        }
    }

    /// Scan the text of a `"…"` or `"""` literal from the current position
    /// to its first unescaped `{`, its closer, or its end: the line break
    /// for a `"…"` literal, which is line-bounded, and the end of input for
    /// a `"""` one. A `\` protects the byte after it, so an escaped quote
    /// never closes and an escaped brace opens nothing. The literal's form
    /// is a constant, so each form's loop tests only its own delimiters.
    fn scan_string_text<const BLOCK: bool>(&mut self) -> (Stop, TokenFlags) {
        let mut flags = TokenFlags::EMPTY;
        loop {
            match self.peek_byte() {
                None => return (Stop::End, flags),
                Some(b'\n' | b'\r') if !BLOCK => return (Stop::End, flags),
                Some(b'"') if BLOCK => {
                    if self.remaining().starts_with(BLOCK_DELIMITER) {
                        self.position += BLOCK_DELIMITER.len();
                        return (Stop::Closer, flags);
                    }
                    self.position += 1;
                }
                Some(b'"') => {
                    self.position += 1;
                    return (Stop::Closer, flags);
                }
                Some(b'{') => return (Stop::Hole, flags),
                Some(b'\\') => {
                    flags |= TokenFlags::HAS_ESCAPE;
                    self.bump_ascii();
                    match self.peek_byte() {
                        // An escaped line break joins two lines of a `"""`
                        // literal; the break stays for the arm below, so a
                        // lone `\r` is still flagged.
                        None | Some(b'\n' | b'\r') => {}
                        // The braces of a `\u{…}` escape are its own: its
                        // payload is taken through the `}`, as far as it is
                        // hex digits, and opens no hole.
                        Some(b'u') if self.peek_byte_at(1) == Some(b'{') => {
                            self.position += 2;
                            while self
                                .peek_byte()
                                .is_some_and(|byte| byte.is_ascii_hexdigit())
                            {
                                self.position += 1;
                            }
                            if self.peek_byte() == Some(b'}') {
                                self.position += 1;
                            }
                        }
                        Some(_) => {
                            self.bump_char();
                        }
                    }
                }
                Some(b'\r') => {
                    self.bump_ascii();
                    if self.peek_byte() == Some(b'\n') {
                        self.bump_ascii();
                    } else {
                        flags |= TokenFlags::LONE_CR;
                    }
                }
                // Only ASCII delimiters are inspected, so a byte-wise skip
                // cannot leave the final position mid-character.
                Some(_) => self.position += 1,
            }
        }
    }

    /// Scan a `'…'` literal. It is line-bounded: an unterminated one ends
    /// at the line break, so the rest of the line lexes normally and a
    /// stray delimiter never reaches the next line.
    fn scan_line_literal(&mut self, close: u8) -> TokenFlags {
        self.bump_ascii();

        let mut flags = TokenFlags::EMPTY;
        loop {
            match self.peek_byte() {
                None | Some(b'\n' | b'\r') => {
                    flags |= TokenFlags::UNTERMINATED;
                    break;
                }
                Some(byte) if byte == close => {
                    self.bump_ascii();
                    break;
                }
                Some(b'\\') => {
                    flags |= TokenFlags::HAS_ESCAPE;
                    self.bump_ascii();
                    if !matches!(self.peek_byte(), None | Some(b'\n' | b'\r')) {
                        self.bump_char();
                    }
                }
                // Only ASCII delimiters are inspected, so a byte-wise skip
                // cannot leave the final position mid-character.
                Some(_) => self.position += 1,
            }
        }
        flags
    }

    /// Scan a raw multi-line literal from its `r"""` to the next `"""`.
    /// Line breaks are content and nothing is escaped. Layout — what shares
    /// the opener's line and the closer's, and how the content is indented
    /// — is the collector's to judge.
    fn scan_block_string(&mut self, opener: usize) -> TokenFlags {
        self.position += opener;

        let mut flags = TokenFlags::EMPTY;
        loop {
            match self.peek_byte() {
                None => {
                    flags |= TokenFlags::UNTERMINATED;
                    break;
                }
                Some(b'"') if self.remaining().starts_with(BLOCK_DELIMITER) => {
                    self.position += BLOCK_DELIMITER.len();
                    break;
                }
                Some(b'\r') => {
                    self.bump_ascii();
                    if self.peek_byte() == Some(b'\n') {
                        self.bump_ascii();
                    } else {
                        flags |= TokenFlags::LONE_CR;
                    }
                }
                Some(_) => self.position += 1,
            }
        }
        flags
    }

    fn looks_like_raw_string(&self) -> bool {
        let bytes = &self.source.as_bytes()[self.position..];
        debug_assert_eq!(bytes.first(), Some(&b'r'));

        let mut index = 1;
        while bytes.get(index) == Some(&b'#') {
            index += 1;
        }
        bytes.get(index) == Some(&b'"')
    }

    /// Scan an `r"…"` literal, closed by a quote and as many `#` as opened
    /// it. Line-bounded like `"…"`.
    fn scan_raw_string(&mut self) -> TokenFlags {
        self.bump_ascii();

        let mut hashes = 0usize;
        while self.peek_byte() == Some(b'#') {
            self.position += 1;
            hashes += 1;
        }

        debug_assert_eq!(self.peek_byte(), Some(b'"'));
        self.bump_ascii();

        let bytes = self.source.as_bytes();
        loop {
            match bytes.get(self.position) {
                None | Some(b'\n' | b'\r') => return TokenFlags::UNTERMINATED,
                Some(b'"') => {
                    let closing = &bytes[self.position + 1..];
                    if closing.len() >= hashes && closing[..hashes].iter().all(|&byte| byte == b'#')
                    {
                        self.position += 1 + hashes;
                        return TokenFlags::EMPTY;
                    }
                    self.position += 1;
                }
                Some(_) => self.position += 1,
            }
        }
    }

    fn scan_ident(&mut self) {
        self.bump_char();
        self.eat_ident_continue();
    }

    /// Classify the identifier just scanned from `start`, while its bytes
    /// are still cache-hot: a reserved word — `_` included — or a plain
    /// identifier.
    fn classify_ident(&self, start: usize) -> SyntaxKind {
        SyntaxKind::from_keyword(&self.source[start..self.position]).unwrap_or(SyntaxKind::Ident)
    }

    fn eat_ident_continue(&mut self) {
        while let Some(ch) = self.remaining().chars().next() {
            if !is_ident_continue(ch) {
                break;
            }
            self.position += ch.len_utf8();
        }
    }

    fn scan_unicode(&mut self, start: usize) -> (SyntaxKind, RawKind, TokenFlags) {
        let ch = self
            .remaining()
            .chars()
            .next()
            .expect("scan_unicode called at EOF");
        debug_assert!(!ch.is_ascii());

        if unicode_ident::is_xid_start(ch) {
            self.scan_ident();
            (
                self.classify_ident(start),
                RawKind::Ident,
                TokenFlags::EMPTY,
            )
        } else {
            self.bump_char();
            (SyntaxKind::Error, RawKind::Unknown, TokenFlags::EMPTY)
        }
    }
}

/// The error for a literal with holes that its text never closes,
/// reported at its opener as a whole literal is.
fn unterminated(text: Text) -> LateError {
    if text.block {
        LateError {
            token: text.start,
            prefix: Some(BLOCK_DELIMITER.len()),
            kind: LexErrorKind::UnterminatedBlockString,
        }
    } else {
        LateError {
            token: text.start,
            prefix: None,
            kind: LexErrorKind::UnterminatedString,
        }
    }
}

impl Lexer<'_> {
    /// The next token. `Some` always consumes at least one byte; `None`
    /// means the cursor reached `source.len()`. Malformed input never ends
    /// the scan early. An inherent method rather than an `Iterator`: the
    /// collector calls it directly, with no adapter between.
    pub(crate) fn next_token(&mut self) -> Option<RawToken> {
        if self.position == self.source.len() {
            self.finish();
            return None;
        }

        let start = self.position;
        let token = self.scan_token();
        self.emitted += 1;

        debug_assert!(self.position > start);
        debug_assert!(self.position <= self.source.len());

        Some(token)
    }
}
