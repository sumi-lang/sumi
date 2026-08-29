//! The grammar: recursive descent over a [`ParserInput`], building a
//! [`Parse`] through [`Marker`]s.
//!
//! Every function is total and makes progress: no input panics, each loop
//! either consumes a token or returns to a caller that will, and nesting is
//! bounded — past [`MAX_DEPTH`] open nodes the rest of the expression is
//! skipped with one error, so stack use is bounded too. Recovery skips into
//! `Error` nodes and resynchronizes at statement boundaries, `}`, list
//! separators, or the next `fn`. Missing pieces are absent, never empty
//! nodes; the [`ParseError`] carries the position.
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
}

/// The most open nodes an expression may sit inside. Every level of
/// nesting opens at least one node and costs a few stack frames, so this
/// bounds the parser's stack; real code nests a few dozen deep at most.
pub const MAX_DEPTH: u32 = 256;

fn source_file(p: &mut Marker<'_, '_>) {
    while p.current().is_some() {
        if p.at(T::FnKw) {
            fn_item(p);
        } else {
            p.error(ParseErrorKind::ExpectedItem);
            skip(p, |p| p.at(T::FnKw));
        }
    }
}

/// Take the next token and every following one into an `Error` node, up to
/// `stop` or end of input. The caller has reported what it expected there;
/// the run itself adds no diagnostic. Brackets inside the run are matched
/// the way the token stream matches them, so `stop` is consulted only
/// outside them, and a closer with no opener in the run belongs to
/// something enclosing: it is never taken.
fn skip(p: &mut Marker<'_, '_>, stop: impl Fn(&Marker<'_, '_>) -> bool) -> CompletedMarker {
    let mut m = p.start();
    let mut brackets = Brackets::default();
    loop {
        match m.current() {
            Some(opener @ (T::LParen | T::LBrace)) => brackets.push(opener),
            Some(T::RParen) => brackets.close(T::LParen),
            Some(T::RBrace) => brackets.close(T::LBrace),
            _ => {}
        }
        m.token();
        let stops = match m.current() {
            None => true,
            Some(T::RParen) => brackets.parens == 0,
            Some(T::RBrace) => brackets.braces == 0,
            Some(_) => brackets.stack.is_empty() && stop(&m),
        };
        if stops {
            break;
        }
    }
    m.complete(N::Error)
}

/// The unclosed openers of a skipped run, counted by kind so that whether
/// a closer has anything to close is answered without a scan.
#[derive(Default)]
struct Brackets {
    stack: Vec<T>,
    parens: usize,
    braces: usize,
}

impl Brackets {
    fn push(&mut self, opener: T) {
        match opener {
            T::LParen => self.parens += 1,
            _ => self.braces += 1,
        }
        self.stack.push(opener);
    }

    /// Pop openers until `opener` or the bottom: every closer is a
    /// synchronization point, as in the token stream's boundary rule.
    fn close(&mut self, opener: T) {
        while let Some(top) = self.stack.pop() {
            match top {
                T::LParen => self.parens -= 1,
                _ => self.braces -= 1,
            }
            if top == opener {
                break;
            }
        }
    }
}

fn fn_item(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token(); // fn
    name(&mut m);
    // The parameter list stays on the name's line: `(` never continues one.
    if m.at(T::LParen) && !m.boundary() {
        param_list(&mut m);
    } else {
        m.error(ParseErrorKind::Expected(T::LParen));
    }
    // A return type on the line of the signature: a leading `->` never
    // continues a line.
    if m.at_glued(T::Minus, T::Gt) && !m.boundary() {
        m.token();
        m.token();
        type_ref(&mut m);
    }
    block_here(&mut m);
    m.complete(N::FnItem);
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
    m.enter_parens();
    loop {
        match m.current() {
            None => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::RParen) => {
                m.token();
                break;
            }
            // The body, the enclosing block's end, or the next item follows
            // an unclosed list: enclosing syntax, left where it is.
            Some(T::LBrace | T::RBrace | T::FnKw) => {
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
                    m.at(T::Comma) || m.at(T::RParen) || m.at(T::LBrace) || m.at(T::FnKw)
                });
            }
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
    loop {
        match m.current() {
            None => {
                m.error(ParseErrorKind::Expected(T::RBrace));
                break;
            }
            Some(T::RBrace) => {
                m.token();
                break;
            }
            // Inside parentheses, a `)` belongs to the construct around this
            // block: the block is unclosed, and the `)` is left to its owner.
            Some(T::RParen) if m.in_parens() => {
                m.error(ParseErrorKind::Expected(T::RBrace));
                break;
            }
            Some(_) => {
                statement(&mut m);
                let ends = m.boundary() || m.at(T::RBrace) || (m.at(T::RParen) && m.in_parens());
                if !ends && m.current().is_some() {
                    m.error(ParseErrorKind::ExpectedBoundary);
                }
            }
        }
    }
    m.complete(N::Block)
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
                skip(p, |p| p.boundary() || p.at(T::RBrace));
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
    if !m.boundary() && m.current().is_some_and(starts_expression) {
        operand(&mut m, 0);
    }
    m.complete(N::ReturnStmt);
}

fn starts_expression(kind: T) -> bool {
    matches!(
        kind,
        T::Ident
            | T::IntLiteral
            | T::FloatLiteral
            | T::StringLiteral
            | T::RawStringLiteral
            | T::CharLiteral
            | T::TrueKw
            | T::FalseKw
            | T::Minus
            | T::Bang
            | T::LParen
            | T::LBrace
            | T::IfKw
    )
}

/// An expression where one is required.
fn operand(p: &mut Marker<'_, '_>, min_bp: u8) {
    if expr_bp(p, min_bp).is_none() {
        p.error(ParseErrorKind::ExpectedExpression);
    }
}

fn expr(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    expr_bp(p, 0)
}

/// Operands of a prefix operator: tighter than every binary operator, so
/// only a call binds closer.
const PREFIX_BP: u8 = 11;

fn expr_bp(p: &mut Marker<'_, '_>, min_bp: u8) -> Option<CompletedMarker> {
    let mut lhs = prefix_or_atom(p)?;
    // Whether `lhs` is a comparison made here: another would chain it.
    let mut comparison = false;
    loop {
        // A boundary ends the expression; the stream has applied the
        // newline rule already, so a leading operator continues and a glued
        // `-` or a `(` on a new line starts fresh.
        if p.boundary() {
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
        let Some((op, width)) = binary_op(p) else {
            break;
        };
        let (left_bp, right_bp) = op.binding_power();
        if left_bp < min_bp {
            break;
        }
        if p.joint_before() || p.nth_joint(width - 1) {
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
        operand(&mut m, right_bp);
        lhs = m.complete(if chained { N::Error } else { N::BinaryExpr });
        comparison = op.is_comparison() && !chained;
    }
    Some(lhs)
}

/// When the next expression would open a node past [`MAX_DEPTH`] — after
/// `ahead` nodes the caller opens first — take the rest of the expression
/// as one `Error` node instead of recursing: it ends at a boundary, a `,`,
/// or an enclosing closer.
fn too_deep(p: &mut Marker<'_, '_>, ahead: u32) -> Option<CompletedMarker> {
    (p.depth() + ahead >= MAX_DEPTH).then(|| {
        p.error(ParseErrorKind::NestingTooDeep);
        skip(p, |p| p.boundary() || p.at(T::Comma))
    })
}

fn prefix_or_atom(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    // Settle that an expression starts here before the depth check: its
    // recovery takes the next token, which must be an expression's.
    let kind = p.current().filter(|&kind| starts_expression(kind))?;
    if let Some(skipped) = too_deep(p, 0) {
        return Some(skipped);
    }
    Some(match kind {
        T::Minus | T::Bang => {
            let mut m = p.start();
            // Spacing is a complaint about an operand that exists; a missing
            // one is reported as such below.
            if !m.joint() && m.nth(1).is_some_and(starts_expression) {
                m.error(ParseErrorKind::SpacedPrefixOperator);
            }
            m.token();
            operand(&mut m, PREFIX_BP);
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
            // The owning paren takes its closer whatever precedes it: a
            // block inside may have restored boundaries.
            if m.at(T::RParen) {
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
    operand(&mut m, 0);
    block_here(&mut m);
    if m.at(T::ElseKw) {
        m.token();
        if !m.at(T::IfKw) {
            block_here(&mut m);
        } else if too_deep(&mut m, 1).is_none() {
            // The nested `if` opens one node, and its condition another:
            // cut the chain before a condition trips and leaves a headless
            // `if`.
            if_expr(&mut m);
        }
    }
    m.complete(N::IfExpr)
}

fn arg_list(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token(); // (
    m.enter_parens();
    loop {
        match m.current() {
            None => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::RParen) => {
                m.token();
                break;
            }
            // The enclosing block's end, or the next item, follows an
            // unclosed list: enclosing syntax, left where it is.
            Some(T::RBrace | T::FnKw) => {
                m.error(ParseErrorKind::Expected(T::RParen));
                break;
            }
            Some(T::Comma) => {
                m.error(ParseErrorKind::ExpectedExpression);
                m.token();
            }
            Some(kind) if starts_expression(kind) => operand(&mut m, 0),
            Some(_) => {
                m.error(ParseErrorKind::ExpectedExpression);
                skip(&mut m, |m| {
                    m.at(T::Comma) || m.at(T::RParen) || m.at(T::FnKw)
                });
            }
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

/// The binary operator at the next token, if any, and how many tokens it
/// spans: compound operators are glued pairs. A lone `=` is not an
/// operator; a `-` here is subtraction, whatever its spacing, which the
/// caller checks.
fn binary_op(p: &Marker<'_, '_>) -> Option<(BinaryOp, usize)> {
    Some(match p.current()? {
        T::Pipe if p.at_glued(T::Pipe, T::Pipe) => (BinaryOp::Or, 2),
        T::Amp if p.at_glued(T::Amp, T::Amp) => (BinaryOp::And, 2),
        T::Eq if p.at_glued(T::Eq, T::Eq) => (BinaryOp::Eq, 2),
        T::Bang if p.at_glued(T::Bang, T::Eq) => (BinaryOp::Ne, 2),
        T::Lt if p.at_glued(T::Lt, T::Eq) => (BinaryOp::Le, 2),
        T::Gt if p.at_glued(T::Gt, T::Eq) => (BinaryOp::Ge, 2),
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
