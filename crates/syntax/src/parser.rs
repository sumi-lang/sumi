//! Recursive descent over a [`ParserInput`], building a [`Parse`] through [`Marker`]s. Every rule
//! is total and makes progress, and the input horizon sits at the next item's start while an item
//! parses, so no rule or recovery reads past it.

use sumi_lexer::RawIdx;

use crate::ast::NodeKind as N;
use crate::grammar::{
    BinaryOp, PREFIX_BP, SyntaxKind as T, binary_operator, can_end_statement, closer,
    encloses_statements, introduces_statement, is_closer, is_literal, is_opener,
    is_prefix_operator, opener, starts_expression, starts_item, starts_statement,
};
use crate::input::ParserInput;
use crate::tree::{CompletedMarker, Marker, Parse, RecoveryHandle};

pub fn parse(input: ParserInput) -> Parse {
    Parse::build(input, source_file)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ParseEvidence {
    Recovery(ParseRecovery),
    Violation(ParseViolation),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParseRecovery {
    pub kind: ParseRecoveryKind,
    pub anchor: ParseAnchor,
    pub skipped: Box<[RawTokenRange]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ParseRecoveryKind {
    Item,
    Statement,
    Expression,
    Name,
    Type,
    Body,
    Token(T),
    /// The anchor is the gap where the closer is missing.
    Closer {
        kind: T,
        opener: RawTokenRange,
    },
    Boundary,
    /// Garbage between an operand and what continues or ends its expression.
    Unexpected,
    NestingTooDeep,
    /// Skipped lexer `Error` tokens; the diagnostic is the lexer's.
    PriorPhaseError,
}

/// A rule broken by syntax the parser took as written, with no recovery.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParseViolation {
    pub kind: ParseViolationKind,
    pub range: RawTokenRange,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ParseViolationKind {
    UnspacedBinaryOperator,
    SpacedPrefixOperator,
    SpacedListOpener,
    FunctionNameOnNextLine,
    FunctionItemOnSameLine,
    BindingNameOnNextLine,
    ChainedComparison,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ParseAnchor {
    Gap(RawGap),
    Tokens(RawTokenRange),
}

/// Half-open and nonempty: `start < end`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RawTokenRange {
    start: RawIdx,
    end: RawIdx,
}

impl RawTokenRange {
    pub(crate) fn new(start: RawIdx, end: RawIdx) -> Self {
        assert!(start < end, "a raw token range must be nonempty");
        Self { start, end }
    }

    pub fn start(self) -> RawIdx {
        self.start
    }

    pub fn end(self) -> RawIdx {
        self.end
    }

    pub fn iter(self) -> impl DoubleEndedIterator<Item = RawIdx> + ExactSizeIterator {
        self.start.until(self.end)
    }
}

/// The trivia between two adjacent significant tokens, possibly empty; at a file edge, the leading
/// or trailing trivia.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RawGap {
    trivia_start: RawIdx,
    trivia_end: RawIdx,
}

impl RawGap {
    pub(crate) fn new(trivia_start: RawIdx, trivia_end: RawIdx) -> Self {
        assert!(trivia_start <= trivia_end, "a raw gap cannot run backwards");
        Self {
            trivia_start,
            trivia_end,
        }
    }

    pub fn trivia_start(self) -> RawIdx {
        self.trivia_start
    }

    pub fn trivia_end(self) -> RawIdx {
        self.trivia_end
    }
}

/// The most open nodes an expression may sit inside; past it the rest is skipped, which bounds the
/// parser's stack.
pub const MAX_DEPTH: u32 = 256;

fn source_file(p: &mut Marker<'_, '_>) {
    let item_candidate = |p: &Marker<'_, '_>| {
        (p.at(T::FnKw) || begins_headless_item(p)) && !p.in_matched_delimiters()
    };
    let mut item_ends_here = false;
    for anchor in 0..=p.item_anchor_count() {
        p.set_limit(p.item_anchor(anchor));
        if anchor > 0 {
            // An anchor is an item's head, with or without its `fn`.
            let has_fn = p.at(T::FnKw);
            if item_ends_here && has_fn && !p.newline() {
                p.violation(ParseViolationKind::FunctionItemOnSameLine, 1);
            }
            fn_item(p);
            item_ends_here = has_fn;
        }
        while p.current().is_some() {
            if item_candidate(p) {
                fn_item(p);
                item_ends_here = false;
            } else {
                let recovery = p.recover_tokens(ParseRecoveryKind::Item, 1);
                skip_all(p, recovery, item_candidate);
                item_ends_here = false;
            }
        }
    }
}

/// Takes at least one token. A matched bracket pair is taken whole, so `stop` is never asked inside
/// one.
fn skip(
    p: &mut Marker<'_, '_>,
    recovery: RecoveryHandle,
    stop: impl Fn(&Marker<'_, '_>) -> bool,
) -> CompletedMarker {
    let mut m = p.start();
    m.group();
    while let Some(kind) = m.current() {
        let closer = is_closer(kind) && m.partnered();
        if closer || stop(&m) {
            break;
        }
        m.group();
    }
    let skipped = m.covered_range();
    m.skipped(recovery, skipped);
    m.complete(N::Error)
}

fn skip_token(p: &mut Marker<'_, '_>, recovery: RecoveryHandle) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    let skipped = m.covered_range();
    m.skipped(recovery, skipped);
    m.complete(N::Error)
}

fn skip_statement_garbage(p: &mut Marker<'_, '_>, recovery: RecoveryHandle) -> CompletedMarker {
    let mut m = p.start();
    m.group_inside();
    while !(m.current().is_none()
        || m.boundary()
        || m.current().is_some_and(introduces_statement)
        || (m.at(T::RBrace) && !m.closer_ahead())
        || m.closes_open_bracket())
    {
        m.group_inside();
    }
    let skipped = m.covered_range();
    m.skipped(recovery, skipped);
    m.complete(N::Error)
}

/// `skip` repeated past the partnered closers it stops at: nothing encloses the run here, so they
/// are garbage too.
fn skip_all(
    p: &mut Marker<'_, '_>,
    recovery: RecoveryHandle,
    stop: impl Fn(&Marker<'_, '_>) -> bool,
) {
    while p.current().is_some() && !stop(p) {
        skip(p, recovery, &stop);
    }
}

fn fn_item(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    let has_fn = m.at(T::FnKw);
    if has_fn {
        m.token();
    } else {
        m.missing(ParseRecoveryKind::Token(T::FnKw));
    }
    if !m.at(T::Ident) && !m.at(T::Underscore) {
        let recovery = m.missing(ParseRecoveryKind::Name);
        signature_garbage(&mut m, Signature::Item, recovery, |m| {
            m.at(T::Ident) || m.at(T::Underscore) || m.at(T::LParen)
        });
    }
    let name_missing = if m.at(T::Ident) || m.at(T::Underscore) {
        if has_fn && m.at(T::Ident) && m.newline() {
            m.violation(ParseViolationKind::FunctionNameOnNextLine, 1);
        }
        name(&mut m);
        if m.at(T::LParen) && !m.newline() && !m.joint_before() {
            m.violation(ParseViolationKind::SpacedListOpener, 1);
        }
        false
    } else {
        true
    };
    signature_tail(&mut m, ExprFollow::Anything, Signature::Item, name_missing);
    m.complete(N::FnItem);
}

/// A `fn` with no signature part after it on its line is garbage, not a closure. A name counts as
/// one: garbage where the list belongs, but a closure was meant.
fn closure_expr(p: &mut Marker<'_, '_>, follow: ExprFollow) -> CompletedMarker {
    let next = p.nth(1);
    let signature_follows = p.nth_newline(1)
        || next.is_none_or(|next| {
            matches!(
                next,
                T::LParen | T::Ident | T::Underscore | T::Eq | T::LBrace
            )
        })
        || nth_arrow(p, 1);
    if !signature_follows {
        let recovery = p.recover_tokens(ParseRecoveryKind::Expression, 1);
        return skip_token(p, recovery);
    }
    let mut m = p.start();
    m.token();
    signature_tail(&mut m, follow, Signature::Closure, false);
    m.complete(N::ClosureExpr)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Signature {
    Item,
    Closure,
}

fn signature_tail(
    m: &mut Marker<'_, '_>,
    follow: ExprFollow,
    signature: Signature,
    name_missing: bool,
) {
    let first_field = u8::from(signature == Signature::Item);
    let allow_list_newline = name_missing;
    if !m.at(T::LParen) || (m.newline() && !allow_list_newline) {
        let recovery = m.missing(ParseRecoveryKind::Token(T::LParen));
        signature_garbage(m, signature, recovery, |m| {
            m.at(T::LParen) || nth_arrow(m, 0)
        });
    }
    let mut complete = false;
    if m.at(T::LParen) && (!m.newline() || allow_list_newline) {
        match signature {
            Signature::Item => delimited_list::<Params<true>>(m, first_field),
            Signature::Closure => delimited_list::<Params<false>>(m, first_field),
        }
        complete = true;
    }
    let body_begins =
        |m: &Marker<'_, '_>, complete: bool| m.at(T::LBrace) || at_expression_body(m, complete);
    if !body_begins(m, complete) && !nth_arrow(m, 0) {
        let recovery = m.missing(ParseRecoveryKind::Body);
        signature_garbage(m, signature, recovery, |m| {
            nth_arrow(m, 0) || at_expression_body(m, complete)
        });
    }
    if nth_arrow(m, 0) {
        m.token();
        m.token();
        complete = m.at(T::Ident);
        type_ref(m, first_field + 1);
        if !body_begins(m, complete) {
            let recovery = m.missing(ParseRecoveryKind::Body);
            signature_garbage(m, signature, recovery, |m| at_expression_body(m, complete));
        }
    }
    if at_expression_body(m, complete) {
        m.token();
        if let Some(body) = operand_before(m, 0, follow) {
            m.field(&body, first_field + 2);
        }
    } else if m.at(T::LBrace) {
        let body = block(m);
        m.field(&body, first_field + 2);
    }
}

/// `return` can end a statement, but a signature right after it is its value, not an item.
fn begins_headless_item(m: &Marker<'_, '_>) -> bool {
    m.previous()
        .is_none_or(|previous| can_end_statement(previous) && previous != T::ReturnKw)
        && m.at_headless_signature()
}

/// `complete`: a signature part stands right before. Elsewhere in a signature a `=` is garbage, so
/// it never makes an expression body of what follows it.
fn at_expression_body(m: &Marker<'_, '_>, complete: bool) -> bool {
    complete && m.at(T::Eq) && m.nth(1).is_some_and(starts_expression) && !nth_arrow(m, 1)
}

fn nth_arrow(m: &Marker<'_, '_>, n: usize) -> bool {
    m.nth(n) == Some(T::Minus) && m.nth_joint(n) && m.nth(n + 1) == Some(T::Gt)
}

/// A `{` the stream never pairs, where a signature part was expected, is garbage, not the body.
fn signature_garbage(
    m: &mut Marker<'_, '_>,
    signature: Signature,
    recovery: RecoveryHandle,
    resume: impl Fn(&Marker<'_, '_>) -> bool,
) {
    let stop = |m: &Marker<'_, '_>| resume(m) || m.newline() || (m.at(T::LBrace) && m.partnered());
    match signature {
        Signature::Item => skip_all(m, recovery, stop),
        Signature::Closure => {
            let stop = |m: &Marker<'_, '_>| {
                stop(m)
                    || m.at(T::Comma)
                    || m.closes_open_bracket()
                    || (m.current().is_some_and(is_closer) && m.partnered())
            };
            if m.current().is_some() && !stop(m) {
                skip(m, recovery, stop);
            }
        }
    }
}

/// `_` is a `Name` with a recovery inside: it reads as a name and binds nothing.
fn name(p: &mut Marker<'_, '_>) {
    if p.at(T::Ident) {
        let name = leaf(p, N::Name);
        p.field(&name, 0);
    } else if p.at(T::Underscore) {
        let mut m = p.start();
        m.recover_tokens(ParseRecoveryKind::Name, 1);
        m.token();
        let name = m.complete(N::Name);
        p.field(&name, 0);
    } else {
        p.missing(ParseRecoveryKind::Name);
    }
}

fn type_ref(p: &mut Marker<'_, '_>, field: u8) {
    if p.at(T::Ident) {
        let mut m = p.start();
        m.token();
        let ty = m.complete(N::TypeRef);
        p.field(&ty, field);
    } else {
        p.missing(ParseRecoveryKind::Type);
    }
}

trait ListRule {
    const NODE: N;
    const ELEMENT: ParseRecoveryKind;
    const RESUMES_AT_ELEMENT: bool;
    fn starts_element(m: &Marker<'_, '_>) -> bool;
    fn parse_element(m: &mut Marker<'_, '_>);
    fn follows(m: &Marker<'_, '_>) -> bool;
    /// Whether this kind may follow an element with no `,` before it.
    fn tolerated(kind: T) -> bool;
}

struct Params<const TYPED: bool>;

impl<const TYPED: bool> ListRule for Params<TYPED> {
    const NODE: N = N::ParamList;
    const ELEMENT: ParseRecoveryKind = ParseRecoveryKind::Name;
    // A name in the garbage is likelier the body's, after a `{` standing where the `)` should, than
    // a parameter's.
    const RESUMES_AT_ELEMENT: bool = false;

    fn starts_element(m: &Marker<'_, '_>) -> bool {
        m.at(T::Ident) || m.at(T::Underscore)
    }

    fn parse_element(m: &mut Marker<'_, '_>) {
        param(m, TYPED);
    }

    /// A brace the stream never pairs is garbage in the list, not what follows it.
    fn follows(m: &Marker<'_, '_>) -> bool {
        ((m.at(T::LBrace) || m.at(T::RBrace)) && m.partnered()) || (!TYPED && m.at(T::Eq))
    }

    fn tolerated(kind: T) -> bool {
        kind == T::LBrace
    }
}

struct Args;

impl ListRule for Args {
    const NODE: N = N::ArgList;
    const ELEMENT: ParseRecoveryKind = ParseRecoveryKind::Expression;
    const RESUMES_AT_ELEMENT: bool = true;

    fn starts_element(m: &Marker<'_, '_>) -> bool {
        m.starts_expression()
    }

    fn parse_element(m: &mut Marker<'_, '_>) {
        operand(m);
    }

    fn follows(m: &Marker<'_, '_>) -> bool {
        m.at(T::RBrace)
    }

    fn tolerated(_: T) -> bool {
        false
    }
}

fn delimited_list<R: ListRule>(p: &mut Marker<'_, '_>, field: u8) {
    let close = p
        .current()
        .and_then(closer)
        .expect("a list opens at its opener");
    let mut m = p.start();
    m.token();
    m.enter();
    loop {
        match m.current() {
            None => {
                m.missing_closer();
                break;
            }
            Some(kind) if kind == close && m.owns_closer() => {
                m.token();
                break;
            }
            Some(kind) if kind == close && m.closes_open(close) => {
                m.missing_closer();
                break;
            }
            Some(_) if !m.closed() && R::follows(&m) && !displaced_closer(&m) => {
                m.missing_closer();
                break;
            }
            Some(T::Comma) => {
                m.missing(R::ELEMENT);
                m.token();
            }
            // Parsed as an element, an unpaired opener would take the closer with it.
            Some(kind) if is_opener(kind) && !m.partnered() && m.nth(1) == Some(close) => {
                let recovery = m.recover_tokens(R::ELEMENT, 1);
                skip_token(&mut m, recovery);
            }
            Some(_) if R::starts_element(&m) => R::parse_element(&mut m),
            Some(_) => {
                let recovery = m.recover_tokens(R::ELEMENT, 1);
                skip(&mut m, recovery, |m| {
                    m.at(T::Comma)
                        || m.at(close)
                        || (!m.closed() && (m.boundary() || R::follows(m)))
                        || (R::RESUMES_AT_ELEMENT && begins_element::<R>(m))
                });
                // The garbage stood where an element should, so no `,` is missing.
                if R::RESUMES_AT_ELEMENT && begins_element::<R>(&m) {
                    continue;
                }
            }
        }
        // A list the stream closes owns every boundary through its closer; only an unclosed one
        // ends at its line.
        if !m.closed() && m.boundary() {
            m.missing_closer();
            break;
        }
        if m.at(T::Comma) {
            m.token();
        } else if !m
            .current()
            .is_none_or(|kind| is_closer(kind) || starts_item(kind) || R::tolerated(kind))
        {
            m.missing(ParseRecoveryKind::Token(T::Comma));
        }
    }
    let list = m.complete(R::NODE);
    p.field(&list, field);
}

/// An opener the stream never closes began nothing and is garbage like the rest.
fn begins_element<R: ListRule>(m: &Marker<'_, '_>) -> bool {
    R::starts_element(m)
        && m.current()
            .is_some_and(|kind| !is_opener(kind) || m.partnered())
}

fn param(p: &mut Marker<'_, '_>, typed: bool) {
    let mut m = p.start();
    name(&mut m);
    if m.at(T::Colon) && !m.boundary() {
        m.token();
        type_ref(&mut m, 1);
    } else if typed || m.at(T::Ident) {
        m.missing(ParseRecoveryKind::Token(T::Colon));
        if m.at(T::Ident) {
            type_ref(&mut m, 1);
        }
    }
    m.complete(N::Param);
}

fn block(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    m.enter();
    loop {
        match m.current() {
            None => {
                m.missing_closer();
                break;
            }
            Some(T::RBrace) if !m.closer_ahead() => {
                m.token();
                break;
            }
            Some(_) if m.closes_open_bracket() => {
                m.missing_closer();
                break;
            }
            Some(_) => {
                let recovery = m.recovery_checkpoint();
                statement(&mut m);
                let failed = m.recovered_since(recovery);
                let ends = m.current().is_none()
                    || m.boundary()
                    || (m.at(T::RBrace) && !m.closer_ahead() && !(failed && displaced_closer(&m)))
                    || m.closes_open_bracket();
                if !ends {
                    // After a failed statement, an expression start on its line is ambiguous with
                    // the statement's suffix; only an introducer is new.
                    if failed && !m.current().is_some_and(introduces_statement) {
                        let recovery = m
                            .latest_recovery_since(recovery)
                            .expect("a failed statement has recovery evidence");
                        skip_statement_garbage(&mut m, recovery);
                    } else if !failed && m.current().is_some_and(starts_statement) {
                        m.missing(ParseRecoveryKind::Boundary);
                    }
                }
            }
        }
    }
    m.complete(N::Block)
}

fn statement(p: &mut Marker<'_, '_>) {
    match p.current() {
        Some(T::LetKw) => let_stmt(p),
        Some(T::Underscore) => discard_stmt(p),
        Some(T::ReturnKw) => return_stmt(p),
        // `fn name` where a statement belongs is an item, not a closure missing its list.
        Some(T::FnKw)
            if !p.nth_newline(1) && matches!(p.nth(1), Some(T::Ident | T::Underscore)) =>
        {
            let recovery = p.recover_tokens(ParseRecoveryKind::Statement, 1);
            skip_statement_garbage(p, recovery);
        }
        Some(T::Error) => {
            let mut m = p.start();
            while m.at(T::Error) {
                m.token();
            }
            let skipped = m.covered_range();
            let recovery = m.recover_range(ParseRecoveryKind::PriorPhaseError, skipped);
            m.skipped(recovery, skipped);
            m.complete(N::Error);
        }
        _ => {
            let recovery = p.recovery_checkpoint();
            if let Some(lhs) = expr_bp(p, 0, ExprFollow::Anything) {
                if !p.recovered_since(recovery) && p.at(T::Eq) && !p.boundary() {
                    let lhs_node = p.completed_node(&lhs);
                    let mut m = p.precede(lhs);
                    m.token();
                    let value = operand(&mut m);
                    m.wrapped_field(lhs_node, 0);
                    if let Some(value) = &value {
                        m.field(value, 1);
                    }
                    m.complete(N::AssignStmt);
                }
            } else {
                let recovery = p.recover_tokens(ParseRecoveryKind::Statement, 1);
                skip_statement_garbage(p, recovery);
            }
        }
    }
}

fn let_stmt(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token();
    let mut split_head = m.newline();
    if m.at(T::MutKw) {
        m.token();
        split_head |= m.newline();
    }
    if split_head && m.at(T::Ident) {
        m.violation(ParseViolationKind::BindingNameOnNextLine, 1);
    }
    name(&mut m);
    if m.at(T::Colon) && !m.boundary() {
        m.token();
        type_ref(&mut m, 1);
    }
    if m.expect(T::Eq)
        && let Some(initializer) = operand(&mut m)
    {
        m.field(&initializer, 2);
    }
    m.complete(N::LetStmt);
}

fn discard_stmt(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token();
    if m.expect(T::Eq)
        && let Some(value) = operand(&mut m)
    {
        m.field(&value, 0);
    }
    m.complete(N::DiscardStmt);
}

fn return_stmt(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token();
    if !m.boundary()
        && m.starts_expression()
        && let Some(value) = operand(&mut m)
    {
        m.field(&value, 0);
    }
    m.complete(N::ReturnStmt);
}

fn operand(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    operand_before(p, 0, ExprFollow::Anything)
}

fn operand_before(
    p: &mut Marker<'_, '_>,
    min_bp: u8,
    follow: ExprFollow,
) -> Option<CompletedMarker> {
    if let Some(expression) = expr_bp(p, min_bp, follow) {
        return Some(expression);
    }
    let displaced = !p.newline() && displaces_expression(p);
    let recovery = if displaced {
        p.recover_tokens(ParseRecoveryKind::Expression, 1)
    } else {
        p.missing(ParseRecoveryKind::Expression)
    };
    if !displaced {
        return None;
    }
    skip(p, recovery, |p| {
        p.newline() || p.at(T::Comma) || begins_statement(p)
    });
    if !p.newline() && begins_expression(p) {
        expr_bp(p, min_bp, follow)
    } else {
        None
    }
}

fn closes_expression_bracket(kind: T) -> bool {
    opener(kind).is_some_and(|opener| !encloses_statements(opener))
}

/// An opener the stream never closes began nothing and is garbage like the rest.
fn begins_expression(p: &Marker<'_, '_>) -> bool {
    p.current()
        .is_some_and(|kind| starts_expression(kind) && (!is_opener(kind) || p.partnered()))
}

fn begins_statement(p: &Marker<'_, '_>) -> bool {
    begins_expression(p) || p.current().is_some_and(introduces_statement)
}

fn displaces_expression(p: &Marker<'_, '_>) -> bool {
    if p.current().is_some_and(is_closer) {
        if p.closes_open_bracket() {
            return false;
        }
        return displaced_closer(p)
            || (p.current().is_some_and(closes_expression_bracket) && !p.partnered());
    }
    p.current()
        .is_some_and(|kind| kind == T::Error || !(starts_statement(kind) || kind == T::Comma))
}

/// Asked only after the enclosing construct has taken its own expected closer.
fn displaced_closer(p: &Marker<'_, '_>) -> bool {
    if !p.current().is_some_and(is_closer) || p.nth_newline(1) {
        return false;
    }
    if binary_op(p, 1).is_some() {
        return false;
    }
    // An opener may continue the operand instead: a call, or a body.
    p.nth(1).is_some_and(|next| {
        matches!(next, T::Eq | T::Colon)
            || introduces_statement(next)
            || (starts_expression(next) && !is_opener(next))
    })
}

fn garbage_in_expression(p: &Marker<'_, '_>, follow: ExprFollow) -> bool {
    p.at(T::Error)
        || (p.current().is_some_and(closes_expression_bracket) && !p.closes_open_bracket())
        || (follow == ExprFollow::Anything && p.at(T::LBrace))
        || p.current().is_some_and(|kind| {
            !starts_statement(kind)
                && !matches!(kind, T::Eq | T::Comma | T::ElseKw)
                && !is_closer(kind)
                && !starts_item(kind)
                && binary_op(p, 0).is_none()
        })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExprFollow {
    Anything,
    Block,
}

fn expr_bp(p: &mut Marker<'_, '_>, min_bp: u8, follow: ExprFollow) -> Option<CompletedMarker> {
    if follow == ExprFollow::Block && p.at(T::LBrace) && !block_starts_condition(p) {
        return None;
    }
    let mut lhs = prefix_or_atom(p, follow)?;
    let mut comparison = false;
    loop {
        // The stream has applied the newline rule: a leading operator is no boundary, and a glued
        // `-` or a `(` on a new line is one.
        if p.boundary() {
            break;
        }
        if follow == ExprFollow::Block && p.at(T::LBrace) {
            break;
        }
        // `newline`, not `boundary`: parentheses suspend boundaries, but a `(` on a new line is
        // still never a call.
        if p.at(T::LParen) && !p.newline() {
            if !p.joint_before() {
                p.violation(ParseViolationKind::SpacedListOpener, 1);
            }
            let callee = p.completed_node(&lhs);
            let mut m = p.precede(lhs);
            m.wrapped_field(callee, 0);
            delimited_list::<Args>(&mut m, 1);
            lhs = m.complete(N::CallExpr);
            comparison = false;
            continue;
        }
        let mut joint_left = p.joint_before();
        if !p.newline()
            && garbage_in_expression(p, follow)
            && !p.nth_newline(1)
            && (binary_op(p, 1).is_some()
                || p.nth(1)
                    .is_some_and(|next| is_closer(next) || next == T::Comma))
        {
            let recovery = p.recover_tokens(ParseRecoveryKind::Unexpected, 1);
            skip_token(p, recovery);
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
            p.violation(ParseViolationKind::UnspacedBinaryOperator, width);
        }
        let chained = comparison && op.is_comparison();
        if chained {
            p.violation(ParseViolationKind::ChainedComparison, width);
        }
        let lhs_node = p.completed_node(&lhs);
        let mut m = p.precede(lhs);
        for _ in 0..width {
            m.token();
        }
        let rhs = operand_before(&mut m, right_bp, follow);
        m.wrapped_field(lhs_node, 0);
        if let Some(rhs) = &rhs {
            m.field(rhs, 1);
        }
        lhs = m.complete(if chained { N::Error } else { N::BinaryExpr });
        comparison = op.is_comparison() && !chained;
    }
    Some(lhs)
}

fn block_starts_condition(p: &Marker<'_, '_>) -> bool {
    p.nth_partner(0).is_some_and(|close| {
        let next = close + 1;
        p.nth(next) == Some(T::LBrace)
            || (!p.nth_boundary(next)
                && ((!p.nth_newline(next) && p.nth(next) == Some(T::LParen))
                    || binary_op(p, next).is_some()))
    })
}

/// `ahead`: the nodes the caller opens before the next expression.
fn too_deep(p: &mut Marker<'_, '_>, ahead: u32) -> Option<CompletedMarker> {
    (p.depth() + ahead >= MAX_DEPTH).then(|| {
        let recovery = p.recover_tokens(ParseRecoveryKind::NestingTooDeep, 1);
        skip(p, recovery, |p| p.boundary() || p.at(T::Comma))
    })
}

fn prefix_or_atom(p: &mut Marker<'_, '_>, follow: ExprFollow) -> Option<CompletedMarker> {
    // The depth check comes second: its recovery takes the next token, which must be an
    // expression's.
    if !p.starts_expression() {
        return None;
    }
    let kind = p.current()?;
    if let Some(skipped) = too_deep(p, 0) {
        return Some(skipped);
    }
    Some(match kind {
        _ if is_prefix_operator(kind) => {
            let mut m = p.start();
            // A missing operand is reported below, not as spacing.
            if !m.joint() && m.nth(1).is_some_and(starts_expression) {
                m.violation(ParseViolationKind::SpacedPrefixOperator, 1);
            }
            m.token();
            if let Some(operand) = operand_before(&mut m, PREFIX_BP, follow) {
                m.field(&operand, 0);
            }
            m.complete(N::PrefixExpr)
        }
        T::Ident => leaf(p, N::NameRef),
        _ if is_literal(kind) => leaf(p, N::LiteralExpr),
        T::LParen => {
            let mut m = p.start();
            m.token();
            m.enter();
            if let Some(inner) = operand(&mut m) {
                m.field(&inner, 0);
            }
            if m.owns_closer() {
                m.token();
            } else {
                m.missing_closer();
            }
            m.complete(N::ParenExpr)
        }
        T::LBrace => block(p),
        T::IfKw => if_expr(p),
        T::FnKw => closure_expr(p, follow),
        _ => return None,
    })
}

fn leaf(p: &mut Marker<'_, '_>, kind: N) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    m.complete(kind)
}

fn if_expr(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    let condition = operand_before(&mut m, 0, ExprFollow::Block);
    let then_branch = if_block(&mut m);
    let else_branch = if m.at(T::ElseKw) {
        m.token();
        if !m.at(T::IfKw) {
            if_block(&mut m)
        } else if too_deep(&mut m, 1).is_none() {
            // Checked here, one node ahead: a condition that tripped would leave a headless `if`.
            Some(if_expr(&mut m))
        } else {
            None
        }
    } else {
        None
    };
    for (field, child) in [condition, then_branch, else_branch].iter().enumerate() {
        if let Some(child) = child {
            m.field(child, field as u8);
        }
    }
    m.complete(N::IfExpr)
}

fn if_block(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    if p.at(T::LBrace) {
        return Some(block(p));
    }
    let displaced = !(p.current().is_none_or(is_closer) || p.at(T::ElseKw) || p.newline());
    let recovery = if displaced {
        p.recover_tokens(ParseRecoveryKind::Token(T::LBrace), 1)
    } else {
        p.missing(ParseRecoveryKind::Token(T::LBrace))
    };
    if !displaced {
        return None;
    }
    skip(p, recovery, |p| {
        p.at(T::LBrace) || p.current().is_some_and(is_closer) || p.at(T::ElseKw) || p.newline()
    });
    if p.at(T::LBrace) {
        Some(block(p))
    } else {
        None
    }
}

/// The width is in tokens. A `-` is subtraction whatever its spacing; the caller checks the
/// spacing.
fn binary_op(p: &Marker<'_, '_>, n: usize) -> Option<(BinaryOp, usize)> {
    let glued = if p.nth_joint(n) { p.nth(n + 1) } else { None };
    binary_operator(p.nth(n)?, glued)
}
