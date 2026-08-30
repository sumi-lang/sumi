//! The grammar: recursive descent over a [`ParserInput`], building a
//! [`Parse`] through [`Marker`]s.
//!
//! Every function is total and makes progress: no input panics, each loop
//! either consumes a token or returns to a caller that will, and nesting is
//! bounded — past [`MAX_DEPTH`] open nodes the rest of the expression is
//! skipped with one error, so stack use is bounded too. Recovery skips into
//! `Error` nodes and resynchronizes at statement boundaries, `}`, list
//! separators, or the next `fn`. Where an expression is required and
//! garbage stands in its place on the line, the garbage is taken and the
//! expression tried once more. Each construct owns the recovery up to its
//! following delimiter; missing pieces are absent, never empty nodes, and
//! the [`ParseError`] carries the position.
//!
//! Expressions are parsed by precedence climbing over the stream facts the
//! [`ParserInput`] precomputed: a statement boundary ends an expression, a
//! binary operator must be spaced on both sides and must not end its line,
//! a prefix operator must be glued to its operand, and comparisons do not
//! chain. Each violation is one error, recovered as the evident intent.

use crate::input::ParserInput;
use crate::kind::{NodeKind as N, SyntaxKind as T};
use crate::tree::{CompletedMarker, Marker, Parse};

/// Parse one file.
pub fn parse(input: &ParserInput) -> Parse {
    Parse::build(input, source_file)
}

/// A parse error, attached to the token where the parser noticed it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParseError {
    /// Index of the token in the file's token buffer, or one past the last
    /// token for an error at end of input.
    pub token: u32,
    pub kind: ParseErrorKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ParseErrorKind {
    /// Something other than a `fn` item at the top level.
    ExpectedItem,
    /// A token that cannot start a statement.
    ExpectedStatement,
    ExpectedExpression,
    ExpectedName,
    ExpectedType,
    /// A specific token, such as `)` or `=`.
    Expected(T),
    /// A statement starts on the line of the previous one.
    ExpectedBoundary,
    /// A block opens on the line after what it belongs to.
    BlockOnNewLine,
    /// A binary operator without spaces on both sides, as in `a-b`.
    UnspacedBinaryOperator,
    /// A binary operator at the end of a line; operators lead the
    /// continuation line instead.
    TrailingOperator,
    /// A prefix operator separated from its operand, as in `- x`.
    SpacedPrefixOperator,
    /// A comparison applied to a comparison, as in `a < b < c`.
    ChainedComparison,
    /// Expressions nested more than [`MAX_DEPTH`] deep; the rest of the
    /// expression is skipped.
    NestingTooDeep,
    /// A token inside an expression that neither continues nor ends it,
    /// skipped so that the expression can go on past it.
    Unexpected,
}

impl ParseErrorKind {
    /// Whether recovery reported this — something was missing, or a token
    /// could not be taken — rather than a rule being broken by syntax the
    /// parser took as it was, such as an unspaced operator.
    pub fn is_recovery(self) -> bool {
        !matches!(
            self,
            Self::UnspacedBinaryOperator
                | Self::TrailingOperator
                | Self::SpacedPrefixOperator
                | Self::ChainedComparison
                | Self::BlockOnNewLine
        )
    }
}

/// The most open nodes an expression may sit inside. Every level of
/// nesting opens at least one node and costs a few stack frames, so this
/// bounds the parser's stack; real code nests a few dozen deep at most.
pub const MAX_DEPTH: u32 = 256;

fn source_file(p: &mut Marker<'_, '_>) {
    while p.current().is_some() {
        if starts_item(p) {
            fn_item(p);
        } else {
            p.error(ParseErrorKind::ExpectedItem);
            skip_all(p, starts_item);
        }
    }
}

/// Whether an item starts at the next token: `fn`, or a signature missing
/// it — a name, a parenthesized list, and a body or return type after the
/// list on its line, which nothing else at the top level looks like. A
/// misplaced call has neither after its list, and stays garbage.
fn starts_item(p: &Marker<'_, '_>) -> bool {
    if p.at(T::FnKw) {
        return true;
    }
    (p.at_start() || p.boundary())
        && p.at(T::Ident)
        && p.nth(1) == Some(T::LParen)
        && p.nth_partner(1).is_some_and(|close| {
            !p.nth_newline(close + 1)
                && (p.nth(close + 1) == Some(T::LBrace) || p.nth_glued(close + 1, T::Minus, T::Gt))
        })
}

/// Take the next token and every following one into an `Error` node, up to
/// `stop` or end of input. The caller has reported what it expected there;
/// the run itself adds no diagnostic. A matched bracket pair is taken
/// whole, as the token stream pairs them, so `stop` is never consulted
/// inside one. A closer met after the first token has no opener in the run:
/// one the stream pairs belongs to something enclosing and ends the run,
/// while an orphan belongs to nothing and is garbage like the rest. A `fn`
/// that no closed construct owns ends the run too: it begins the next
/// item, which no recovery may swallow.
fn skip(p: &mut Marker<'_, '_>, stop: impl Fn(&Marker<'_, '_>) -> bool) -> CompletedMarker {
    let mut m = p.start();
    m.group();
    while let Some(kind) = m.current() {
        let closer = matches!(kind, T::RParen | T::RBrace) && m.partnered();
        if closer || m.at_item() || stop(&m) {
            break;
        }
        m.group();
    }
    m.complete(N::Error)
}

/// Take one token into an `Error` node without following a bracket partner.
/// Used when grammar context, rather than pairing, has established that the
/// token itself is garbage.
fn skip_token(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    m.complete(N::Error)
}

/// Take the rest of a malformed statement's line, leaving an enclosing
/// closer, the next item, or the next line to its owner. Matched groups
/// wholly inside the enclosing construct stay whole; an opener paired with
/// that construct's closer is taken alone.
fn skip_statement_garbage(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.group_inside();
    while !(m.current().is_none()
        || m.boundary()
        || begins_recovery_statement(&m)
        || (m.at(T::RBrace) && !m.closer_ahead())
        || m.closes_open_paren()
        || m.at_item())
    {
        m.group_inside();
    }
    m.complete(N::Error)
}

/// Skip into `Error` nodes until `stop` or end of input, closers included:
/// where nothing encloses the run — the top level, a signature — a closer
/// is garbage like anything else, so a run that ends at one is followed by
/// another. One recovery episode, however many runs.
fn skip_all(p: &mut Marker<'_, '_>, stop: impl Fn(&Marker<'_, '_>) -> bool) {
    while p.current().is_some() && !stop(p) {
        skip(p, &stop);
    }
}

/// A function item. Each part of the signature is taken where it belongs
/// or reported where it is missing, and garbage in its place is skipped up
/// to the next part, so a malformed signature is recovered as the evident
/// intent and the body is kept. Nothing is searched for past the end of
/// the line: a declaration ends where its line does.
fn fn_item(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    if m.at(T::FnKw) {
        m.token();
    } else {
        m.error(ParseErrorKind::Expected(T::FnKw));
    }
    let mut reported = false;
    if !m.at(T::Ident) && !m.at(T::Underscore) {
        missing(&mut m, ParseErrorKind::ExpectedName, &mut reported);
        signature_garbage(&mut m, |m| {
            m.at(T::Ident) || m.at(T::Underscore) || m.at(T::LParen)
        });
    }
    if m.at(T::Ident) || m.at(T::Underscore) {
        name(&mut m);
    }
    // The parameter list stays on the name's line: `(` never continues one.
    if !m.at(T::LParen) || m.newline() {
        missing(&mut m, ParseErrorKind::Expected(T::LParen), &mut reported);
        signature_garbage(&mut m, |m| m.at(T::LParen) || m.at_glued(T::Minus, T::Gt));
    }
    if m.at(T::LParen) && !m.newline() {
        param_list(&mut m);
    }
    // A return type on the line of the signature: a leading `->` never
    // continues a line.
    let at_arrow = |m: &Marker<'_, '_>| m.at_glued(T::Minus, T::Gt) && !m.newline();
    if !m.at(T::LBrace) && !at_arrow(&m) {
        missing(&mut m, ParseErrorKind::Expected(T::LBrace), &mut reported);
        signature_garbage(&mut m, at_arrow);
    }
    if at_arrow(&m) {
        m.token();
        m.token();
        type_ref(&mut m);
        if !m.at(T::LBrace) {
            missing(&mut m, ParseErrorKind::Expected(T::LBrace), &mut reported);
            signature_garbage(&mut m, |_| false);
        }
    }
    if m.at(T::LBrace) {
        block_here(&mut m);
    }
    m.complete(N::FnItem);
}

/// Report a part of a signature missing at the cursor — unless the line
/// has ended and a part was reported already: the rest are missing because
/// the line ended, and the first report covers them.
fn missing(m: &mut Marker<'_, '_>, kind: ParseErrorKind, reported: &mut bool) {
    if !(*reported && m.newline()) {
        m.error(kind);
    }
    *reported = true;
}

/// Skip garbage in a signature — tokens that belong to none of its parts —
/// into `Error` nodes, up to `resume`, a body, the next item, or the end
/// of the line. Nothing is skipped when already at one of those. A `{`
/// counts as a body only when the stream pairs it with a `}`: an unclosed
/// one where a part of the signature was expected is garbage, not the body
/// that follows it.
fn signature_garbage(m: &mut Marker<'_, '_>, resume: impl Fn(&Marker<'_, '_>) -> bool) {
    skip_all(m, |m| {
        resume(m) || m.at(T::FnKw) || m.newline() || (m.at(T::LBrace) && m.partnered())
    });
}

/// A declared name. `_` is taken with an error: it reads as a name but
/// binds nothing.
fn name(p: &mut Marker<'_, '_>) {
    if p.at(T::Ident) {
        p.token();
    } else {
        p.error(ParseErrorKind::ExpectedName);
        if p.at(T::Underscore) {
            p.token();
        }
    }
}

/// A type: a builtin name, until types grow a shape of their own.
fn type_ref(p: &mut Marker<'_, '_>) {
    if p.at(T::Ident) {
        p.token();
    } else {
        p.error(ParseErrorKind::ExpectedType);
    }
}

fn param_list(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token(); // (
    // A list the stream closes owns everything up to its `)`: whatever is
    // in the way is garbage in the list. One it does not close ends at
    // enclosing syntax — the body, an enclosing block's end, or the next
    // item — a brace being that only when the stream pairs it.
    m.enter_parens();
    loop {
        match m.current() {
            None => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::RParen) if m.owns_rparen() => {
                m.token();
                break;
            }
            Some(T::RParen) if m.closes_open_paren() => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::LBrace | T::RBrace)
                if !m.closed() && m.partnered() && !displaced_closer(&m) =>
            {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::FnKw) if m.at_item() => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::Ident | T::Underscore) => param(&mut m),
            Some(T::Comma) => {
                m.error(ParseErrorKind::ExpectedName);
                m.token();
            }
            Some(_) => {
                m.error(ParseErrorKind::ExpectedName);
                skip(&mut m, |m| {
                    m.at(T::Comma)
                        || m.at(T::RParen)
                        || (!m.closed() && (m.boundary() || (m.at(T::LBrace) && m.partnered())))
                });
            }
        }
        // A boundary ends a list the stream never closes: its line has. One
        // the stream closes owns everything through its `)`, a boundary an
        // unclosed `{` inside it restores included.
        if !m.closed() && m.boundary() {
            m.error(ParseErrorKind::Expected(T::RParen));
            break;
        }
        if m.at(T::Comma) {
            m.token();
        } else if !matches!(
            m.current(),
            None | Some(T::RParen | T::LBrace | T::RBrace | T::FnKw)
        ) {
            m.error(ParseErrorKind::Expected(T::Comma));
        }
    }
    m.complete(N::ParamList);
}

fn param(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    name(&mut m);
    // A type right after the name is taken as the type of a `:` that was
    // forgotten.
    if m.expect(T::Colon) || m.at(T::Ident) {
        type_ref(&mut m);
    }
    m.complete(N::Param);
}

/// A block where one is required, on the line of what it belongs to.
fn block_here(p: &mut Marker<'_, '_>) {
    if !p.at(T::LBrace) {
        p.error(ParseErrorKind::Expected(T::LBrace));
        return;
    }
    if p.newline() {
        p.error(ParseErrorKind::BlockOnNewLine);
    }
    block(p);
}

fn block(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token(); // {
    // A block the stream never closes ends where the next item begins: its
    // `}` is missing, and an item is not a statement — nor is it any
    // recovery's to skip. One the stream does close keeps a misplaced `fn`
    // as the statement it is not, skipped.
    m.enter();
    loop {
        match m.current() {
            None => {
                m.error(ParseErrorKind::Expected(T::RBrace));
                break;
            }
            Some(T::RBrace) if !m.closer_ahead() => {
                m.token();
                break;
            }
            Some(T::FnKw) if m.at_item() => {
                m.error(ParseErrorKind::Expected(T::RBrace));
                break;
            }
            // A `)` closing a paren still open around this block belongs to
            // it: the block is unclosed, and the `)` is left to its owner.
            Some(T::RParen) if m.closes_open_paren() => {
                m.error(ParseErrorKind::Expected(T::RBrace));
                break;
            }
            Some(_) => {
                let recovery = m.recovery_checkpoint();
                let garbage = m.at(T::Error);
                statement(&mut m);
                let failed = garbage || m.recovered_since(recovery);
                // A statement following on the same line is missing its
                // boundary. Anything else begins a malformed suffix, which
                // the next round reports: a boundary would not make it a
                // statement.
                let ends = m.current().is_none()
                    || m.boundary()
                    || (m.at(T::RBrace) && !m.closer_ahead() && !(failed && displaced_closer(&m)))
                    || m.closes_open_paren()
                    || m.at_item();
                if !ends {
                    if failed && !begins_recovery_statement(&m) {
                        skip_statement_garbage(&mut m);
                    } else if !failed && m.current().is_some_and(T::starts_statement) {
                        m.error(ParseErrorKind::ExpectedBoundary);
                    }
                }
            }
        }
    }
    m.complete(N::Block)
}

/// A statement introducer strong enough to survive a failed statement on
/// the same line. Expression starts are ambiguous with a malformed suffix
/// and stay with the failed statement; declaration keywords begin a fresh
/// construct.
fn begins_recovery_statement(p: &Marker<'_, '_>) -> bool {
    p.current()
        .is_some_and(|kind| matches!(kind, T::LetKw | T::ReturnKw | T::Underscore | T::Error))
}

/// One statement: a binding, a discard, a return, or an expression, which
/// is a bare child of the block — with no `;`, statement or tail is a
/// matter of position.
fn statement(p: &mut Marker<'_, '_>) {
    match p.current() {
        Some(T::LetKw) => let_stmt(p),
        Some(T::Underscore) => discard_stmt(p),
        Some(T::ReturnKw) => return_stmt(p),
        // Reported by an earlier phase; absorb the run silently.
        Some(T::Error) => {
            let mut m = p.start();
            while m.at(T::Error) {
                m.token();
            }
            m.complete(N::Error);
        }
        _ => {
            if expr(p).is_none() {
                p.error(ParseErrorKind::ExpectedStatement);
                skip_statement_garbage(p);
            }
        }
    }
}

fn let_stmt(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token(); // let
    if m.at(T::MutKw) {
        m.token();
    }
    name(&mut m);
    // The annotation and initializer stay on the binding's line: `:` and
    // `=` never continue one.
    if m.at(T::Colon) && !m.boundary() {
        m.token();
        type_ref(&mut m);
    }
    if m.expect(T::Eq) {
        operand(&mut m, 0);
    }
    m.complete(N::LetStmt);
}

fn discard_stmt(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token(); // _
    if m.expect(T::Eq) {
        operand(&mut m, 0);
    }
    m.complete(N::DiscardStmt);
}

fn return_stmt(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token(); // return
    // A value only on the same line: `return` alone ends a statement.
    if !m.boundary() && m.starts_expression() {
        operand(&mut m, 0);
    }
    m.complete(N::ReturnStmt);
}

/// An expression where one is required. Garbage in its place on the same
/// line is taken as such — up to the line's end, a `,`, or the start of
/// an expression or statement — and the expression tried once more: one
/// report for the garbage, and the expression it displaced still parses.
/// A token the construct around this one is waiting for, or that begins
/// the next statement, is not garbage but the sign the expression is
/// missing; so is anything on the next line.
fn operand(p: &mut Marker<'_, '_>, min_bp: u8) {
    operand_before(p, min_bp, ExprFollow::Anything);
}

/// Parse an expression required before `follow`.
fn operand_before(p: &mut Marker<'_, '_>, min_bp: u8, follow: ExprFollow) {
    if expr_bp(p, min_bp, follow).is_some() {
        return;
    }
    p.error(ParseErrorKind::ExpectedExpression);
    if p.newline() || p.at_item() || !displaces_expression(p) {
        return;
    }
    skip(p, |p| p.newline() || p.at(T::Comma) || begins_statement(p));
    if !p.newline() && begins_expression(p) {
        expr_bp(p, min_bp, follow);
    }
}

/// Whether the next token begins an expression a garbage run should end
/// at: one that starts an expression, an opener the stream never closes
/// excepted — it began nothing, and is garbage like the rest.
fn begins_expression(p: &Marker<'_, '_>) -> bool {
    p.current().is_some_and(|kind| {
        kind.starts_expression() && (!matches!(kind, T::LParen | T::LBrace) || p.partnered())
    })
}

/// Whether the next token begins a statement a garbage run should end at.
fn begins_statement(p: &Marker<'_, '_>) -> bool {
    begins_expression(p)
        || p.current()
            .is_some_and(|kind| matches!(kind, T::LetKw | T::ReturnKw | T::Underscore | T::Error))
}

/// Whether the next token, found where an expression is required, is
/// garbage in its place, rather than the end of the construct around it or
/// the start of the statement after it.
fn displaces_expression(p: &Marker<'_, '_>) -> bool {
    if matches!(p.current(), Some(T::RParen | T::RBrace)) {
        if p.at(T::RParen) && p.closes_open_paren() {
            return false;
        }
        return displaced_closer(p) || (p.at(T::RParen) && !p.partnered());
    }
    p.current().is_some_and(|kind| {
        !kind.starts_expression()
            && !matches!(
                kind,
                T::RBrace | T::Comma | T::LetKw | T::ReturnKw | T::Underscore
            )
    })
}

/// Whether a closer stands where grammar context says an operand continues:
/// before `=` or `:`, or before an operand on the same line. An expected
/// closer is consumed by its construct before this question is asked.
fn displaced_closer(p: &Marker<'_, '_>) -> bool {
    if !matches!(p.current(), Some(T::RParen | T::RBrace)) || p.nth_newline(1) {
        return false;
    }
    // `==` and `!=` are ordinary binary operators after a closer. A lone
    // `=` or a prefix `!` followed by an operand cannot be.
    if p.nth_glued(1, T::Eq, T::Eq) || p.nth_glued(1, T::Bang, T::Eq) {
        return false;
    }
    p.nth(1).is_some_and(|next| {
        matches!(
            next,
            T::Eq | T::Colon | T::LetKw | T::ReturnKw | T::Underscore | T::Error
        ) || (next.starts_expression() && !matches!(next, T::Minus | T::LParen | T::LBrace))
    })
}

/// Whether the next token, found after a complete operand, is garbage in
/// the middle of the expression: neither an operator to continue it nor
/// anything that ends it — a closer, a `,`, an `else`, an item's `fn`, or
/// the start of a statement — nor an expression's own start.
fn garbage_in_expression(p: &Marker<'_, '_>, follow: ExprFollow) -> bool {
    p.at(T::Error)
        || (p.at(T::RParen) && !p.closes_open_paren())
        || (follow == ExprFollow::Anything && p.at(T::LBrace))
        || p.current().is_some_and(|kind| {
            !kind.starts_statement()
                && !matches!(kind, T::RParen | T::RBrace | T::Comma | T::ElseKw | T::FnKw)
                && binary_op(p, 0).is_none()
        })
}

fn expr(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    expr_bp(p, 0, ExprFollow::Anything)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExprFollow {
    Anything,
    Block,
}

/// Operands of a prefix operator: tighter than every binary operator, so
/// only a call binds closer.
const PREFIX_BP: u8 = 11;

fn expr_bp(p: &mut Marker<'_, '_>, min_bp: u8, follow: ExprFollow) -> Option<CompletedMarker> {
    if follow == ExprFollow::Block && p.at(T::LBrace) && !block_starts_condition(p) {
        return None;
    }
    let mut lhs = prefix_or_atom(p, follow)?;
    // Whether `lhs` is a comparison made here: another would chain it.
    let mut comparison = false;
    loop {
        // A boundary ends the expression; the stream has applied the
        // newline rule already, so a leading operator continues and a glued
        // `-` or a `(` on a new line starts fresh.
        if p.boundary() {
            break;
        }
        if follow == ExprFollow::Block && p.at(T::LBrace) {
            break;
        }
        // Arguments stay on the callee's line even inside parentheses, where
        // boundaries are suspended: a `(` on a new line is never a call.
        if p.at(T::LParen) && !p.newline() {
            let mut m = p.precede(lhs);
            arg_list(&mut m);
            lhs = m.complete(N::CallExpr);
            comparison = false;
            continue;
        }
        // One malformed token between the operand and what continues or
        // ends the expression — an operator, a closer, a `,` — all on one line,
        // is garbage in the way: taken as such, with one report, and the
        // expression goes on. An operator is spaced on its left if anything
        // separated the garbage from either side.
        let mut joint_left = p.joint_before();
        if !p.newline()
            && garbage_in_expression(p, follow)
            && !p.nth_newline(1)
            && (binary_op(p, 1).is_some()
                || matches!(p.nth(1), Some(T::RParen | T::RBrace | T::Comma)))
        {
            p.error(ParseErrorKind::Unexpected);
            skip_token(p);
            joint_left = joint_left && p.joint_before();
        }
        let Some((op, width)) = binary_op(p, 0) else {
            break;
        };
        let (left_bp, right_bp) = op.binding_power();
        if left_bp < min_bp {
            break;
        }
        if joint_left || p.nth_joint(width - 1) {
            p.error(ParseErrorKind::UnspacedBinaryOperator);
        }
        if p.nth_newline(width) {
            p.error(ParseErrorKind::TrailingOperator);
        }
        let chained = comparison && op.is_comparison();
        if chained {
            p.error(ParseErrorKind::ChainedComparison);
        }
        let mut m = p.precede(lhs);
        for _ in 0..width {
            m.token();
        }
        operand_before(&mut m, right_bp, follow);
        lhs = m.complete(if chained { N::Error } else { N::BinaryExpr });
        comparison = op.is_comparison() && !chained;
    }
    Some(lhs)
}

/// Whether a block at the start of an `if` condition is demonstrably the
/// condition rather than the required body: its closer is followed by
/// syntax that continues the expression, with a body or call on the same
/// line as required by their grammar.
fn block_starts_condition(p: &Marker<'_, '_>) -> bool {
    p.nth_partner(0).is_some_and(|close| {
        let next = close + 1;
        !p.nth_boundary(next)
            && ((!p.nth_newline(next) && matches!(p.nth(next), Some(T::LParen | T::LBrace)))
                || binary_op(p, next).is_some())
    })
}

/// When the next expression would open a node past [`MAX_DEPTH`] — after
/// `ahead` nodes the caller opens first — take the rest of the expression
/// as one `Error` node instead of recursing: it ends at a boundary, a `,`,
/// an enclosing closer, or the next item.
fn too_deep(p: &mut Marker<'_, '_>, ahead: u32) -> Option<CompletedMarker> {
    (p.depth() + ahead >= MAX_DEPTH).then(|| {
        p.error(ParseErrorKind::NestingTooDeep);
        skip(p, |p| p.boundary() || p.at(T::Comma))
    })
}

fn prefix_or_atom(p: &mut Marker<'_, '_>, follow: ExprFollow) -> Option<CompletedMarker> {
    // Settle that an expression starts here before the depth check: its
    // recovery takes the next token, which must be an expression's.
    if !p.starts_expression() {
        return None;
    }
    let kind = p.current()?;
    if let Some(skipped) = too_deep(p, 0) {
        return Some(skipped);
    }
    Some(match kind {
        T::Minus | T::Bang => {
            let mut m = p.start();
            // Spacing is a complaint about an operand that exists; a missing
            // one is reported as such below.
            if !m.joint() && m.nth(1).is_some_and(T::starts_expression) {
                m.error(ParseErrorKind::SpacedPrefixOperator);
            }
            m.token();
            operand_before(&mut m, PREFIX_BP, follow);
            m.complete(N::PrefixExpr)
        }
        T::Ident => leaf(p, N::NameExpr),
        T::IntLiteral
        | T::FloatLiteral
        | T::StringLiteral
        | T::RawStringLiteral
        | T::CharLiteral
        | T::TrueKw
        | T::FalseKw => leaf(p, N::LiteralExpr),
        T::LParen => {
            let mut m = p.start();
            m.token(); // (
            m.enter_parens();
            operand(&mut m, 0);
            // Take only this paren's mechanical closer or an orphan recovery
            // closer. One paired with an earlier opener belongs to that
            // enclosing construct.
            if m.owns_rparen() {
                m.token();
            } else {
                m.error(ParseErrorKind::Expected(T::RParen));
            }
            m.complete(N::ParenExpr)
        }
        T::LBrace => block(p),
        T::IfKw => if_expr(p),
        _ => return None,
    })
}

/// A node over exactly the next token.
fn leaf(p: &mut Marker<'_, '_>, kind: N) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    m.complete(kind)
}

fn if_expr(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token(); // if
    operand_before(&mut m, 0, ExprFollow::Block);
    if_block(&mut m);
    if m.at(T::ElseKw) {
        m.token();
        if !m.at(T::IfKw) {
            if_block(&mut m);
        } else if too_deep(&mut m, 1).is_none() {
            // The nested `if` opens one node, and its condition another:
            // cut the chain before a condition trips and leaves a headless
            // `if`.
            if_expr(&mut m);
        }
    }
    m.complete(N::IfExpr)
}

/// Parse a required `if` or `else` block. If another token displaced the
/// block on the same line, keep that garbage inside the `if` and resume at
/// the `{`; a line or enclosing delimiter belongs to the caller instead.
fn if_block(p: &mut Marker<'_, '_>) {
    if p.at(T::LBrace) && !p.newline() {
        block_here(p);
        return;
    }
    p.error(ParseErrorKind::Expected(T::LBrace));
    if p.current().is_none()
        || p.at_item()
        || p.at(T::RParen)
        || p.at(T::RBrace)
        || p.at(T::ElseKw)
        || p.newline()
    {
        return;
    }
    skip(p, |p| {
        p.at(T::LBrace) || p.at(T::RParen) || p.at(T::RBrace) || p.at(T::ElseKw) || p.newline()
    });
    if p.at(T::LBrace) {
        block_here(p);
    }
}

fn arg_list(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token(); // (
    // A list the stream closes owns everything up to its `)`; one it does
    // not close ends at enclosing syntax: an enclosing block's end, or the
    // next item.
    m.enter_parens();
    loop {
        match m.current() {
            None => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::RParen) if m.owns_rparen() => {
                m.token();
                break;
            }
            Some(T::RParen) if m.closes_open_paren() => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::RBrace | T::FnKw) if !m.closed() && !displaced_closer(&m) => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::Comma) => {
                m.error(ParseErrorKind::ExpectedExpression);
                m.token();
            }
            Some(T::LBrace) if !m.partnered() && m.nth(1) == Some(T::RParen) => {
                m.error(ParseErrorKind::ExpectedExpression);
                skip_token(&mut m);
            }
            Some(_) if m.starts_expression() => operand(&mut m, 0),
            Some(_) => {
                m.error(ParseErrorKind::ExpectedExpression);
                skip(&mut m, |m| {
                    m.at(T::Comma)
                        || m.at(T::RParen)
                        || (!m.closed() && m.boundary())
                        || begins_expression(m)
                });
                // The garbage displaced an argument, not the `,` after one.
                if begins_expression(&m) {
                    continue;
                }
            }
        }
        // A boundary ends a list the stream never closes: its line has. One
        // the stream closes owns everything through its `)`, a boundary an
        // unclosed `{` inside it restores included.
        if !m.closed() && m.boundary() {
            m.error(ParseErrorKind::Expected(T::RParen));
            break;
        }
        if m.at(T::Comma) {
            m.token();
        } else if !matches!(m.current(), None | Some(T::RParen | T::RBrace | T::FnKw)) {
            m.error(ParseErrorKind::Expected(T::Comma));
        }
    }
    m.complete(N::ArgList);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BinaryOp {
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl BinaryOp {
    /// Left and right binding powers. Left-associative operators bind
    /// tighter on the right; comparisons too, so a chain parses left to
    /// right and is then rejected.
    fn binding_power(self) -> (u8, u8) {
        match self {
            Self::Or => (1, 2),
            Self::And => (3, 4),
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge => (5, 6),
            Self::Add | Self::Sub => (7, 8),
            Self::Mul | Self::Div | Self::Rem => (9, 10),
        }
    }

    fn is_comparison(self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge
        )
    }
}

/// The binary operator `n` significant tokens past the next one, if one
/// starts there, and its width in tokens. Compound operators are glued
/// pairs. A lone `=` is not an operator; a `-` here is subtraction,
/// whatever its spacing, which the caller checks.
fn binary_op(p: &Marker<'_, '_>, n: usize) -> Option<(BinaryOp, usize)> {
    Some(match p.nth(n)? {
        T::Pipe if p.nth_glued(n, T::Pipe, T::Pipe) => (BinaryOp::Or, 2),
        T::Amp if p.nth_glued(n, T::Amp, T::Amp) => (BinaryOp::And, 2),
        T::Eq if p.nth_glued(n, T::Eq, T::Eq) => (BinaryOp::Eq, 2),
        T::Bang if p.nth_glued(n, T::Bang, T::Eq) => (BinaryOp::Ne, 2),
        T::Lt if p.nth_glued(n, T::Lt, T::Eq) => (BinaryOp::Le, 2),
        T::Gt if p.nth_glued(n, T::Gt, T::Eq) => (BinaryOp::Ge, 2),
        T::Lt => (BinaryOp::Lt, 1),
        T::Gt => (BinaryOp::Gt, 1),
        T::Plus => (BinaryOp::Add, 1),
        T::Minus => (BinaryOp::Sub, 1),
        T::Star => (BinaryOp::Mul, 1),
        T::Slash => (BinaryOp::Div, 1),
        T::Percent => (BinaryOp::Rem, 1),
        _ => return None,
    })
}
