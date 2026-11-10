//! Recursive descent over a [`ParserInput`], building a [`Parse`] through [`Marker`]s. Every rule
//! is total and makes progress, and the input horizon sits at the next item's start while an item
//! parses, so no rule or recovery reads past it.

use sumi_lexer::RawIdx;

use crate::ast::NodeKind as N;
use crate::grammar::{
    AssignOp, BinaryOp, PREFIX_BP, Pair, Side, SyntaxKind as T, TokenField, binary_operator,
    bracket, can_end_statement, introduces_statement, is_closer, is_literal, is_opener,
    is_prefix_operator, starts_expression, starts_item, starts_statement,
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
    /// `..`, which the lexer yields as two joint `.` tokens.
    RangeOperator,
    /// `=>`, which the lexer yields as joint `=` and `>` tokens.
    ArmArrow,
    /// The anchor is the gap where the closer is missing.
    Closer {
        pair: Pair,
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
    ItemOnSameLine,
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
        (p.current().is_some_and(starts_item) || begins_headless_item(p))
            && !p.is_in_matched_delimiters()
    };
    let mut item_ends_here = false;
    for anchor in 0..=p.item_anchor_count() {
        p.set_limit(p.item_anchor(anchor));
        if anchor > 0 {
            // An anchor is an item's head, with or without its keyword.
            let has_keyword = p.current().is_some_and(starts_item);
            if item_ends_here && has_keyword && !p.is_after_newline() {
                p.violation(ParseViolationKind::ItemOnSameLine, 1);
            }
            item(p);
            item_ends_here = has_keyword;
        }
        while p.current().is_some() {
            if item_candidate(p) {
                item(p);
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
        let is_at_closer = is_closer(kind) && m.has_partner();
        if is_at_closer || stop(&m) {
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
        || m.is_at_boundary()
        || m.current().is_some_and(introduces_statement)
        || (m.at(T::RBrace) && !m.has_closer_ahead())
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

fn item(p: &mut Marker<'_, '_>) {
    if p.at(T::TypeKw) {
        type_item(p);
    } else if p.at(T::ImplKw) {
        impl_item(p);
    } else {
        fn_item(p);
    }
}

fn impl_item(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token();
    if !m.at(T::Ident) {
        let recovery = m.missing(ParseRecoveryKind::Name);
        signature_garbage(&mut m, recovery, |m| m.at(T::Ident) || m.at(T::LBrace));
    }
    if m.at(T::Ident) {
        let target = leaf(&mut m, N::NameRef);
        m.field(&target, 0);
        type_params(&mut m);
    }
    if !m.at(T::LBrace) {
        let recovery = m.missing(ParseRecoveryKind::Token(T::LBrace));
        signature_garbage(&mut m, recovery, |m| m.at(T::LBrace));
    }
    if m.at(T::LBrace) {
        let methods = method_list(&mut m);
        m.field(&methods, 2);
    }
    m.complete(N::ImplItem);
}

/// Within braces the stream pairs, a `fn` begins a method; what is none is skipped up to the next.
fn method_list(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.open(Pair::Brace);
    loop {
        match m.current() {
            None => {
                m.missing_closer(Pair::Brace);
                break;
            }
            Some(T::RBrace) if !m.has_closer_ahead() => {
                m.token();
                break;
            }
            Some(_) if m.closes_open_bracket() => {
                m.missing_closer(Pair::Brace);
                break;
            }
            Some(T::FnKw) => fn_item(&mut m),
            Some(_) => {
                let recovery = m.recover_tokens(ParseRecoveryKind::Item, 1);
                // A `}` with the list's own still ahead is garbage like any other.
                skip_all(&mut m, recovery, |m| {
                    m.at(T::FnKw)
                        || (m.at(T::RBrace) && !m.has_closer_ahead())
                        || m.closes_open_bracket()
                });
            }
        }
    }
    m.complete(N::MethodList)
}

fn type_item(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    m.token();
    if !m.at(T::Ident) && !m.at(T::Underscore) {
        let recovery = m.missing(ParseRecoveryKind::Name);
        signature_garbage(&mut m, recovery, |m| {
            m.at(T::Ident) || m.at(T::Underscore) || m.at(T::LBrace)
        });
    }
    if m.at(T::Ident) || m.at(T::Underscore) {
        name(&mut m);
        type_params(&mut m);
    }
    if !m.at(T::LBrace) {
        let recovery = m.missing(ParseRecoveryKind::Token(T::LBrace));
        signature_garbage(&mut m, recovery, |m| m.at(T::LBrace));
    }
    if m.at(T::LBrace) {
        delimited_list::<Fields>(&mut m, 2);
    }
    m.complete(N::TypeItem);
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
        signature_garbage(&mut m, recovery, |m| {
            m.at(T::Ident) || m.at(T::Underscore) || m.at(T::LParen)
        });
    }
    let is_name_missing = if m.at(T::Ident) || m.at(T::Underscore) {
        if has_fn && m.at(T::Ident) && m.is_after_newline() {
            m.violation(ParseViolationKind::FunctionNameOnNextLine, 1);
        }
        name(&mut m);
        type_params(&mut m);
        if m.at(T::LParen) && !m.is_after_newline() && !m.is_joint_before() {
            m.violation(ParseViolationKind::SpacedListOpener, 1);
        }
        false
    } else {
        true
    };
    signature_tail(&mut m, is_name_missing);
    m.complete(N::FnItem);
}

fn signature_tail(m: &mut Marker<'_, '_>, is_name_missing: bool) {
    let allow_list_newline = is_name_missing;
    if !m.at(T::LParen) || (m.is_after_newline() && !allow_list_newline) {
        let recovery = m.missing(ParseRecoveryKind::Token(T::LParen));
        signature_garbage(m, recovery, |m| m.at(T::LParen) || is_nth_arrow(m, 0));
    }
    let mut is_complete = false;
    if m.at(T::LParen) && (!m.is_after_newline() || allow_list_newline) {
        delimited_list::<Params>(m, 2);
        is_complete = true;
    }
    let body_begins = |m: &Marker<'_, '_>, is_complete: bool| {
        m.at(T::LBrace) || is_at_expression_body(m, is_complete)
    };
    if !body_begins(m, is_complete) && !is_nth_arrow(m, 0) {
        let recovery = m.missing(ParseRecoveryKind::Body);
        signature_garbage(m, recovery, |m| {
            is_nth_arrow(m, 0) || is_at_expression_body(m, is_complete)
        });
    }
    if is_nth_arrow(m, 0) {
        m.token();
        m.token();
        if !starts_type(m) {
            let recovery = m.missing(ParseRecoveryKind::Type);
            signature_garbage(m, recovery, starts_type);
        }
        is_complete = starts_type(m);
        if is_complete {
            type_ref(m, 3);
        }
        if !body_begins(m, is_complete) {
            let recovery = m.missing(ParseRecoveryKind::Body);
            signature_garbage(m, recovery, |m| is_at_expression_body(m, is_complete));
        }
    }
    if is_at_expression_body(m, is_complete) {
        m.token();
        if let Some(body) = operand_before(m, 0, ExprFollow::Anything) {
            m.field(&body, 4);
        }
    } else if m.at(T::LBrace) {
        let body = block(m);
        m.field(&body, 4);
    }
}

/// `return` can end a statement, but a signature right after it is its value, not an item.
fn begins_headless_item(m: &Marker<'_, '_>) -> bool {
    m.previous()
        .is_none_or(|previous| can_end_statement(previous) && previous != T::ReturnKw)
        && m.is_at_headless_signature()
}

/// `is_complete`: a signature part stands right before. Elsewhere in a signature a `=` is garbage, so
/// it never makes an expression body of what follows it.
fn is_at_expression_body(m: &Marker<'_, '_>, is_complete: bool) -> bool {
    is_complete && m.at(T::Eq) && m.nth(1).is_some_and(starts_expression) && !is_nth_arrow(m, 1)
}

fn is_nth_arrow(m: &Marker<'_, '_>, n: usize) -> bool {
    m.nth(n) == Some(T::Minus) && m.is_nth_joint(n) && m.nth(n + 1) == Some(T::Gt)
}

fn is_nth_arm_arrow(m: &Marker<'_, '_>, n: usize) -> bool {
    m.nth(n) == Some(T::Eq) && m.is_nth_joint(n) && m.nth(n + 1) == Some(T::Gt)
}

/// A `{` the stream never pairs, where a signature part was expected, is garbage, not the body.
fn signature_garbage(
    m: &mut Marker<'_, '_>,
    recovery: RecoveryHandle,
    resume: impl Fn(&Marker<'_, '_>) -> bool,
) {
    let stop = |m: &Marker<'_, '_>| {
        resume(m) || m.is_after_newline() || (m.at(T::LBrace) && m.has_partner())
    };
    skip_all(m, recovery, stop);
}

/// `_` is a `Name` with a recovery inside: it reads as a name and binds nothing.
fn name(p: &mut Marker<'_, '_>) {
    name_in(p, 0);
}

fn name_in(p: &mut Marker<'_, '_>, field: u8) {
    if let Some(name) = bare_name(p) {
        p.field(&name, field);
    }
}

/// A name in no field of its parent.
fn bare_name(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    if p.at(T::Ident) {
        Some(leaf(p, N::Name))
    } else if p.at(T::Underscore) {
        let mut m = p.start();
        m.recover_tokens(ParseRecoveryKind::Name, 1);
        m.token();
        Some(m.complete(N::Name))
    } else {
        p.missing(ParseRecoveryKind::Name);
        None
    }
}

fn type_ref(p: &mut Marker<'_, '_>, field: u8) {
    if let Some(ty) = ty(p) {
        p.field(&ty, field);
    }
}

/// A type in no field of its parent: a name with its arguments, or such names joined by `|`, which
/// is never the `||` operator's first token.
fn ty(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    let mut lhs = match p.current() {
        Some(T::Ident) => named_type(p),
        Some(T::LBracket) if p.depth() + 2 >= MAX_DEPTH => {
            skip_deep_type(p);
            return None;
        }
        Some(T::LBracket) => {
            let mut m = p.open(Pair::Bracket);
            type_ref(&mut m, 0);
            if m.owns_closer(Pair::Bracket) {
                m.token();
            } else {
                m.missing_closer(Pair::Bracket);
            }
            m.complete(N::ArrayType)
        }
        _ => {
            p.missing(ParseRecoveryKind::Type);
            return None;
        }
    };
    while is_union_bar(p) {
        let lhs_node = p.completed_node(&lhs);
        let mut m = p.precede(lhs);
        m.wrapped_field(lhs_node, 0);
        m.token();
        if is_before_displaced_member(&m) {
            let recovery = m.recover_tokens(ParseRecoveryKind::Type, 1);
            skip_token(&mut m, recovery);
        }
        if m.at(T::Ident) {
            let rhs = named_type(&mut m);
            m.field(&rhs, 1);
        } else {
            m.missing(ParseRecoveryKind::Type);
        }
        lhs = m.complete(N::UnionType);
    }
    Some(lhs)
}

/// Whether the next token begins a type: a name, or a sequence type's `[`.
fn starts_type(p: &Marker<'_, '_>) -> bool {
    p.at(T::Ident) || p.at(T::LBracket)
}

fn named_type(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    type_args(&mut m, 0);
    m.complete(N::TypeRef)
}

/// The type parameters after an item's name, where a `<` begins nothing else.
fn type_params(p: &mut Marker<'_, '_>) {
    if opens_type_list(p) {
        type_list(p, N::TypeParamList, 1);
    }
}

/// The type arguments after a name, where a `<` begins nothing else.
fn type_args(p: &mut Marker<'_, '_>, field: u8) {
    if opens_type_list(p) {
        type_list(p, N::TypeArgList, field);
    }
}

fn opens_type_list(p: &mut Marker<'_, '_>) -> bool {
    let opens = p.at(T::Lt) && !p.is_after_newline();
    if opens && !p.is_joint_before() {
        p.violation(ParseViolationKind::SpacedListOpener, 1);
    }
    opens
}

/// A type past the nesting limit, skipped through the lists it opens, so those around it still
/// close.
fn skip_deep_type(p: &mut Marker<'_, '_>) {
    let recovery = p.recover_tokens(ParseRecoveryKind::NestingTooDeep, 1);
    let mut m = p.start();
    let (mut open, mut brackets) = (0u32, u32::from(m.at(T::LBracket)));
    m.token();
    while !m.is_at_boundary() || (brackets > 0 && m.at(T::RBracket)) {
        match m.current() {
            Some(T::Lt) => open += 1,
            Some(T::Gt) if open > 0 => open -= 1,
            Some(T::LBracket) => brackets += 1,
            Some(T::RBracket) if brackets > 0 => brackets -= 1,
            Some(T::Ident | T::Pipe) => {}
            Some(T::Comma) if open > 0 => {}
            _ => break,
        }
        m.token();
    }
    let skipped = m.covered_range();
    m.skipped(recovery, skipped);
    m.complete(N::Error);
}

/// A `TypeParamList` or a `TypeArgList`, from its `<`. No pair of the stream closes it, so it ends
/// at its `>` or before the first token that neither begins nor separates its elements.
fn type_list(p: &mut Marker<'_, '_>, kind: N, field: u8) {
    let is_params = kind == N::TypeParamList;
    let element = if is_params {
        ParseRecoveryKind::Name
    } else {
        ParseRecoveryKind::Type
    };
    let starts_element = |m: &Marker<'_, '_>| {
        m.at(T::Ident)
            || if is_params {
                m.at(T::Underscore)
            } else {
                m.at(T::LBracket)
            }
    };
    let mut m = p.start();
    m.token();
    loop {
        if m.is_at_boundary() {
            m.missing(ParseRecoveryKind::Token(T::Gt));
            break;
        }
        match m.current() {
            Some(T::Gt) => {
                m.token();
                break;
            }
            Some(T::Comma) => {
                m.missing(element);
                m.token();
                continue;
            }
            Some(_) if starts_element(&m) => {
                if is_params {
                    bare_name(&mut m);
                } else if m.depth() + 2 >= MAX_DEPTH {
                    skip_deep_type(&mut m);
                } else {
                    ty(&mut m);
                }
            }
            _ => {
                m.missing(ParseRecoveryKind::Token(T::Gt));
                break;
            }
        }
        if m.is_at_boundary() {
            continue;
        }
        if m.at(T::Comma) {
            m.token();
        } else if starts_element(&m) {
            m.missing(ParseRecoveryKind::Token(T::Comma));
        }
    }
    let list = m.complete(kind);
    p.field(&list, field);
}

/// A `=` after a union's bar stands before the member when a name follows it and, on the same
/// line, what follows a member and no expression: another bar, or the block of a body.
fn is_before_displaced_member(p: &Marker<'_, '_>) -> bool {
    let continues_type = match p.nth(2) {
        Some(T::LBrace) => p.nth_partner(2).is_some(),
        Some(T::Pipe) => !(p.is_nth_joint(2) && p.nth(3) == Some(T::Pipe)),
        _ => false,
    };
    p.at(T::Eq)
        && !p.is_after_newline()
        && p.nth(1) == Some(T::Ident)
        && continues_type
        && !p.is_nth_after_newline(1)
        && !p.is_nth_after_newline(2)
}

fn is_union_bar(p: &Marker<'_, '_>) -> bool {
    p.at(T::Pipe) && !p.is_at_boundary() && !(p.is_joint() && p.nth(1) == Some(T::Pipe))
}

trait ListRule {
    const NODE: N;
    const PAIR: Pair;
    const ELEMENT: ParseRecoveryKind;
    const RESUMES_AT_ELEMENT: bool;
    fn starts_element(m: &Marker<'_, '_>) -> bool;
    fn parse_element(m: &mut Marker<'_, '_>);
    fn follows(m: &Marker<'_, '_>) -> bool;
    /// Whether this kind may follow an element with no `,` before it.
    fn is_tolerated(kind: T) -> bool;
}

struct Params;

impl ListRule for Params {
    const NODE: N = N::ParamList;
    const PAIR: Pair = Pair::Paren;
    const ELEMENT: ParseRecoveryKind = ParseRecoveryKind::Name;
    // A name in the garbage is likelier the body's, after a `{` standing where the `)` should, than
    // a parameter's.
    const RESUMES_AT_ELEMENT: bool = false;

    fn starts_element(m: &Marker<'_, '_>) -> bool {
        m.at(T::Ident) || m.at(T::Underscore) || m.at(T::MutKw) || m.at(T::SelfKw)
    }

    fn parse_element(m: &mut Marker<'_, '_>) {
        let after_mut = usize::from(m.at(T::MutKw));
        if m.nth(after_mut) == Some(T::SelfKw) {
            let mut m = m.start();
            for _ in 0..=after_mut {
                m.token();
            }
            m.complete(N::SelfParam);
        } else {
            typed_name(m, N::Param);
        }
    }

    /// A brace the stream never pairs is garbage in the list, not what follows it.
    fn follows(m: &Marker<'_, '_>) -> bool {
        (m.at(T::LBrace) || m.at(T::RBrace)) && m.has_partner()
    }

    fn is_tolerated(kind: T) -> bool {
        kind == T::LBrace
    }
}

struct Fields;

impl ListRule for Fields {
    const NODE: N = N::FieldList;
    const PAIR: Pair = Pair::Brace;
    const ELEMENT: ParseRecoveryKind = ParseRecoveryKind::Name;
    const RESUMES_AT_ELEMENT: bool = true;

    fn starts_element(m: &Marker<'_, '_>) -> bool {
        m.at(T::Ident) || m.at(T::Underscore)
    }

    fn parse_element(m: &mut Marker<'_, '_>) {
        typed_name(m, N::Field);
    }

    fn follows(_: &Marker<'_, '_>) -> bool {
        false
    }

    fn is_tolerated(_: T) -> bool {
        false
    }
}

struct ArmsRule;

impl ListRule for ArmsRule {
    const NODE: N = N::ArmList;
    const PAIR: Pair = Pair::Brace;
    const ELEMENT: ParseRecoveryKind = ParseRecoveryKind::Name;
    const RESUMES_AT_ELEMENT: bool = true;

    fn starts_element(m: &Marker<'_, '_>) -> bool {
        m.at(T::Ident) || m.at(T::Underscore)
    }

    fn parse_element(m: &mut Marker<'_, '_>) {
        match_arm(m);
    }

    fn follows(_: &Marker<'_, '_>) -> bool {
        false
    }

    fn is_tolerated(_: T) -> bool {
        false
    }
}

struct Elements;

impl ListRule for Elements {
    const NODE: N = N::ArrayExpr;
    const PAIR: Pair = Pair::Bracket;
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

    fn is_tolerated(_: T) -> bool {
        false
    }
}

struct Args;

impl ListRule for Args {
    const NODE: N = N::ArgList;
    const PAIR: Pair = Pair::Paren;
    const ELEMENT: ParseRecoveryKind = ParseRecoveryKind::Expression;
    const RESUMES_AT_ELEMENT: bool = true;

    fn starts_element(m: &Marker<'_, '_>) -> bool {
        m.starts_expression() || m.at(T::MutKw)
    }

    fn parse_element(m: &mut Marker<'_, '_>) {
        arg(m);
    }

    fn follows(m: &Marker<'_, '_>) -> bool {
        m.at(T::RBrace)
    }

    fn is_tolerated(_: T) -> bool {
        false
    }
}

fn delimited_list<R: ListRule>(p: &mut Marker<'_, '_>, field: u8) {
    let list = delimited::<R>(p);
    p.field(&list, field);
}

fn delimited<R: ListRule>(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let close = R::PAIR.closer().kind();
    let mut m = p.open(R::PAIR);
    loop {
        match m.current() {
            None => {
                m.missing_closer(R::PAIR);
                break;
            }
            Some(kind) if kind == close && m.owns_closer(R::PAIR) => {
                m.token();
                break;
            }
            Some(kind) if kind == close && m.closes_open(R::PAIR) => {
                m.missing_closer(R::PAIR);
                break;
            }
            Some(_) if !m.is_closed() && R::follows(&m) && !is_displaced_closer(&m) => {
                m.missing_closer(R::PAIR);
                break;
            }
            Some(T::Comma) => {
                m.missing(R::ELEMENT);
                m.token();
            }
            // Parsed as an element, an unpaired opener would take the closer with it.
            Some(kind) if is_opener(kind) && !m.has_partner() && m.nth(1) == Some(close) => {
                let recovery = m.recover_tokens(R::ELEMENT, 1);
                skip_token(&mut m, recovery);
            }
            Some(_) if R::starts_element(&m) => R::parse_element(&mut m),
            Some(_) => {
                let recovery = m.recover_tokens(R::ELEMENT, 1);
                skip(&mut m, recovery, |m| {
                    m.at(T::Comma)
                        || m.at(close)
                        || (!m.is_closed() && (m.is_at_boundary() || R::follows(m)))
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
        if !m.is_closed() && m.is_at_boundary() {
            m.missing_closer(R::PAIR);
            break;
        }
        if m.at(T::Comma) {
            m.token();
        } else if !m
            .current()
            .is_none_or(|kind| is_closer(kind) || starts_item(kind) || R::is_tolerated(kind))
        {
            m.missing(ParseRecoveryKind::Token(T::Comma));
        }
    }
    m.complete(R::NODE)
}

/// An opener the stream never closes began nothing and is garbage like the rest.
fn begins_element<R: ListRule>(m: &Marker<'_, '_>) -> bool {
    R::starts_element(m)
        && m.current()
            .is_some_and(|kind| !is_opener(kind) || m.has_partner())
}

/// A `Param` or a `Field`: `Name ':' TypeRef`, a `Param` after its `mut` if it has one.
fn typed_name(p: &mut Marker<'_, '_>, kind: N) {
    let mut m = p.start();
    if kind == N::Param && m.at(T::MutKw) {
        m.token();
    }
    name(&mut m);
    if m.at(T::Colon) && !m.is_at_boundary() {
        m.token();
        type_ref(&mut m, 1);
    } else {
        m.missing(ParseRecoveryKind::Token(T::Colon));
        if starts_type(&m) {
            type_ref(&mut m, 1);
        }
    }
    m.complete(kind);
}

fn arg(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    if m.at(T::Ident) && m.nth(1) == Some(T::Colon) {
        let label = leaf(&mut m, N::NameRef);
        m.field(&label, 0);
        m.token();
    }
    if m.at(T::MutKw) {
        m.token();
    }
    if let Some(value) = operand(&mut m) {
        m.field(&value, 1);
    }
    m.complete(N::Arg);
}

fn block(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.open(Pair::Brace);
    loop {
        match m.current() {
            None => {
                m.missing_closer(Pair::Brace);
                break;
            }
            Some(T::RBrace) if !m.has_closer_ahead() => {
                m.token();
                break;
            }
            Some(_) if m.closes_open_bracket() => {
                m.missing_closer(Pair::Brace);
                break;
            }
            Some(_) => {
                let recovery = m.recovery_checkpoint();
                statement(&mut m);
                let failed = m.recovered_since(recovery);
                let ends = m.current().is_none()
                    || m.is_at_boundary()
                    || (m.at(T::RBrace)
                        && !m.has_closer_ahead()
                        && !(failed && is_displaced_closer(&m)))
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
        // A named function or type where a statement belongs is an item, not a statement.
        Some(T::FnKw | T::TypeKw | T::ImplKw)
            if !p.is_nth_after_newline(1) && matches!(p.nth(1), Some(T::Ident | T::Underscore)) =>
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
                let width = assign_op(p, 0).filter(|_| !p.is_at_boundary());
                if let (false, Some(width)) = (p.recovered_since(recovery), width) {
                    let lhs_node = p.completed_node(&lhs);
                    let mut m = p.precede(lhs);
                    for _ in 0..width {
                        m.token();
                    }
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
    let mut should_split_head = m.is_after_newline();
    if m.at(T::MutKw) {
        m.token();
        should_split_head |= m.is_after_newline();
    }
    if should_split_head && m.at(T::Ident) {
        m.violation(ParseViolationKind::BindingNameOnNextLine, 1);
    }
    name(&mut m);
    if m.at(T::Colon) && !m.is_at_boundary() {
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
    if !m.is_at_boundary()
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
    if follow == ExprFollow::Range && p.at(T::Dot) {
        p.missing(ParseRecoveryKind::Expression);
        return None;
    }
    if let Some(expression) = expr_bp(p, min_bp, follow) {
        return Some(expression);
    }
    let is_displaced = !p.is_after_newline() && displaces_expression(p);
    let recovery = if is_displaced {
        p.recover_tokens(ParseRecoveryKind::Expression, 1)
    } else {
        p.missing(ParseRecoveryKind::Expression)
    };
    if !is_displaced {
        return None;
    }
    skip(p, recovery, |p| {
        p.is_after_newline() || p.at(T::Comma) || begins_statement(p)
    });
    if !p.is_after_newline() && begins_expression(p) {
        expr_bp(p, min_bp, follow)
    } else {
        None
    }
}

fn closes_expression_bracket(kind: T) -> bool {
    matches!(bracket(kind), Some((pair, Side::Close)) if !pair.encloses_statements())
}

/// An opener the stream never closes began nothing and is garbage like the rest.
fn begins_expression(p: &Marker<'_, '_>) -> bool {
    p.current()
        .is_some_and(|kind| starts_expression(kind) && (!is_opener(kind) || p.has_partner()))
}

fn begins_statement(p: &Marker<'_, '_>) -> bool {
    begins_expression(p) || p.current().is_some_and(introduces_statement)
}

fn displaces_expression(p: &Marker<'_, '_>) -> bool {
    if p.current().is_some_and(is_closer) {
        if p.closes_open_bracket() {
            return false;
        }
        return is_displaced_closer(p)
            || (p.current().is_some_and(closes_expression_bracket) && !p.has_partner());
    }
    p.current()
        .is_some_and(|kind| kind == T::Error || !(starts_statement(kind) || kind == T::Comma))
}

/// Asked only after the enclosing construct has taken its own expected closer.
fn is_displaced_closer(p: &Marker<'_, '_>) -> bool {
    let Some((pair, Side::Close)) = p.current().and_then(bracket) else {
        return false;
    };
    // An edit that moves no bracket leaves the pairing whole, and its closers where they belong.
    if p.is_nth_after_newline(1) || !p.is_damaged_closer(pair) {
        return false;
    }
    if binary_op(p, 1).is_some() {
        return false;
    }
    // An opener may continue the operand instead: a call, or a body.
    p.nth(1).is_some_and(|next| {
        next == T::Colon
            || assign_op(p, 1).is_some()
            || introduces_statement(next)
            || (starts_expression(next) && !is_opener(next))
    })
}

fn is_garbage_in_expression(p: &Marker<'_, '_>, follow: ExprFollow) -> bool {
    p.at(T::Error)
        || (p.current().is_some_and(closes_expression_bracket) && !p.closes_open_bracket())
        || (follow == ExprFollow::Anything && p.at(T::LBrace))
        || p.current().is_some_and(|kind| {
            !starts_statement(kind)
                && !matches!(kind, T::Comma | T::ElseKw)
                && assign_op(p, 0).is_none()
                && !is_closer(kind)
                && !starts_item(kind)
                && binary_op(p, 0).is_none()
        })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExprFollow {
    Anything,
    Block,
    Range,
}

fn expr_bp(p: &mut Marker<'_, '_>, min_bp: u8, follow: ExprFollow) -> Option<CompletedMarker> {
    if follow != ExprFollow::Anything && p.at(T::LBrace) && !block_starts_head(p, follow) {
        return None;
    }
    let mut lhs = prefix_or_atom(p, follow)?;
    let mut was_comparison = false;
    loop {
        // The stream has applied the newline rule: a leading operator is no boundary, and a glued
        // `-` or a `(` on a new line is one.
        if p.is_at_boundary() {
            break;
        }
        if follow == ExprFollow::Block && p.at(T::LBrace) {
            break;
        }
        if begins_keywordless_match(p, &lhs, follow) {
            let scrutinee = p.completed_node(&lhs);
            let mut m = p.precede(lhs);
            m.missing_before(ParseRecoveryKind::Token(T::MatchKw));
            m.wrapped_field(scrutinee, 0);
            arm_list(&mut m);
            lhs = m.complete(N::MatchExpr);
            was_comparison = false;
            continue;
        }
        if p.at(T::Dot) && p.nth(1) == Some(T::Ident) {
            let base = p.completed_node(&lhs);
            let mut m = p.precede(lhs);
            m.wrapped_field(base, 0);
            m.token();
            let field = leaf(&mut m, N::NameRef);
            m.field(&field, 1);
            lhs = m.complete(N::FieldExpr);
            was_comparison = false;
            continue;
        }
        if follow == ExprFollow::Range && p.at(T::Dot) {
            break;
        }
        if p.at(T::LBracket) && !p.is_after_newline() {
            let base = p.completed_node(&lhs);
            let mut m = p.precede(lhs);
            m.wrapped_field(base, 0);
            if !m.is_joint_before() {
                m.violation(ParseViolationKind::SpacedListOpener, 1);
            }
            let subscript = subscript(&mut m);
            m.field(&subscript, 1);
            lhs = m.complete(N::IndexExpr);
            was_comparison = false;
            continue;
        }
        // A name is called; a field so written is a method of what it is read from.
        let call = match p.completed_kind(&lhs) {
            N::NameRef => Some(N::CallExpr),
            N::FieldExpr => Some(N::MethodCallExpr),
            _ => None,
        };
        if let Some(call) = call.filter(|_| begins_call(p) || begins_type_args(p)) {
            let callee = p.completed_node(&lhs);
            let mut m = p.precede(lhs);
            m.wrapped_field(callee, 0);
            if m.at(T::Lt) {
                type_list(&mut m, N::TypeArgList, 1);
            }
            if begins_call(&m) {
                if !m.is_joint_before() {
                    m.violation(ParseViolationKind::SpacedListOpener, 1);
                }
                delimited_list::<Args>(&mut m, 2);
            } else {
                m.missing(ParseRecoveryKind::Token(T::LParen));
            }
            lhs = m.complete(call);
            was_comparison = false;
            continue;
        }
        let mut is_joint_left = p.is_joint_before();
        if !p.is_after_newline()
            && is_garbage_in_expression(p, follow)
            && !p.is_nth_after_newline(1)
            && (binary_op(p, 1).is_some()
                || p.nth(1)
                    .is_some_and(|next| is_closer(next) || next == T::Comma))
        {
            let recovery = p.recover_tokens(ParseRecoveryKind::Unexpected, 1);
            skip_token(p, recovery);
            is_joint_left = is_joint_left && p.is_joint_before();
        }
        let Some((op, width)) = binary_op(p, 0) else {
            break;
        };
        let (left_bp, right_bp) = op.binding_power();
        if left_bp < min_bp {
            break;
        }
        if is_joint_left || p.is_nth_joint(width - 1) {
            p.violation(ParseViolationKind::UnspacedBinaryOperator, width);
        }
        let is_chained = was_comparison && op.is_comparison();
        if is_chained {
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
        lhs = m.complete(if is_chained { N::Error } else { N::BinaryExpr });
        was_comparison = op.is_comparison() && !is_chained;
    }
    Some(lhs)
}

/// Arms on the line of an operand are a `match` that lost its keyword, the operand its scrutinee.
/// A head's `{` may be the arms of the `match` the head belongs to, and in a range they must be
/// followed by what continues it, or they are the body; nor do arms stack on a match's own.
fn begins_keywordless_match(p: &Marker<'_, '_>, lhs: &CompletedMarker, follow: ExprFollow) -> bool {
    p.at(T::LBrace)
        && follow != ExprFollow::Block
        && !p.is_after_newline()
        && p.completed_kind(lhs) != N::MatchExpr
        && p.nth_partner(0).is_some_and(|close| {
            let next = close + 1;
            (follow == ExprFollow::Anything
                || p.nth(next) == Some(T::Dot)
                || (!p.is_nth_at_boundary(next) && binary_op(p, next).is_some()))
                && holds_arm(p, close)
        })
}

/// `is_after_newline`, not `is_at_boundary`: parentheses suspend boundaries, but a `(` on a new line
/// is still never a call.
fn begins_call(p: &Marker<'_, '_>) -> bool {
    p.at(T::LParen) && !p.is_after_newline()
}

/// A `<` after a name is a comparison unless a type list runs from it to a call's `(`.
fn begins_type_args(p: &Marker<'_, '_>) -> bool {
    p.at(T::Lt)
        && p.type_list_closer().is_some_and(|closer| {
            p.nth(closer + 1) == Some(T::LParen) && !p.is_nth_after_newline(closer + 1)
        })
}

fn block_starts_head(p: &Marker<'_, '_>, follow: ExprFollow) -> bool {
    p.nth_partner(0).is_some_and(|close| {
        let next = close + 1;
        (p.nth(next) == Some(T::LBrace)
            || (follow == ExprFollow::Range && p.nth(next) == Some(T::Dot))
            || (!p.is_nth_at_boundary(next) && binary_op(p, next).is_some()))
            && !holds_arm(p, close)
    })
}

/// Whether the `{` next, closed `close` tokens on, holds a `=>` of its own: those are a match's
/// arms, whose scrutinee is missing, and no block's statements write one.
fn holds_arm(p: &Marker<'_, '_>, close: usize) -> bool {
    let mut n = 1;
    while n < close {
        if is_nth_arm_arrow(p, n) {
            return true;
        }
        n = p.nth_partner(n).filter(|&partner| partner > n).unwrap_or(n) + 1;
    }
    false
}

/// `ahead`: the nodes the caller opens before the next expression.
fn too_deep(p: &mut Marker<'_, '_>, ahead: u32) -> Option<CompletedMarker> {
    (p.depth() + ahead >= MAX_DEPTH).then(|| {
        let recovery = p.recover_tokens(ParseRecoveryKind::NestingTooDeep, 1);
        skip(p, recovery, |p| p.is_at_boundary() || p.at(T::Comma))
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
            if !m.is_joint() && m.nth(1).is_some_and(starts_expression) {
                m.violation(ParseViolationKind::SpacedPrefixOperator, 1);
            }
            m.token();
            if let Some(operand) = operand_before(&mut m, PREFIX_BP, follow) {
                m.field(&operand, 0);
            }
            m.complete(N::PrefixExpr)
        }
        T::Ident => leaf(p, N::NameRef),
        T::SelfKw => leaf(p, N::SelfExpr),
        _ if is_literal(kind) => leaf(p, N::LiteralExpr),
        T::LParen => {
            let mut m = p.open(Pair::Paren);
            if let Some(inner) = operand(&mut m) {
                m.field(&inner, 0);
            }
            if m.owns_closer(Pair::Paren) {
                m.token();
            } else {
                m.missing_closer(Pair::Paren);
            }
            m.complete(N::ParenExpr)
        }
        T::LBracket => delimited::<Elements>(p),
        T::LBrace => block(p),
        T::IfKw => if_expr(p),
        T::MatchKw => match_expr(p),
        T::ForKw => for_expr(p),
        _ => return None,
    })
}

fn subscript(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.open(Pair::Bracket);
    if let Some(index) = operand(&mut m) {
        m.field(&index, 0);
    }
    if m.owns_closer(Pair::Bracket) {
        m.token();
    } else {
        m.missing_closer(Pair::Bracket);
    }
    m.complete(N::Subscript)
}

fn leaf(p: &mut Marker<'_, '_>, kind: N) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    m.complete(kind)
}

fn for_expr(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    name(&mut m);
    let written_in = m.at(T::InKw);
    if written_in {
        m.token();
    } else {
        m.missing(ParseRecoveryKind::Token(T::InKw));
    }
    let (start, end) = if m.at(T::LBrace) && !block_starts_head(&m, ExprFollow::Range) {
        // With `in` missing too, its evidence alone covers the absent range.
        if written_in {
            m.missing(ParseRecoveryKind::Expression);
        }
        (None, None)
    } else {
        range(&mut m)
    };
    let body = if_block(&mut m);
    for (field, child) in [start, end, body].iter().enumerate() {
        if let Some(child) = child {
            m.field(child, field as u8 + 1);
        }
    }
    m.complete(N::ForExpr)
}

fn range(p: &mut Marker<'_, '_>) -> (Option<CompletedMarker>, Option<CompletedMarker>) {
    let start = operand_before(p, 0, ExprFollow::Range);
    if p.at(T::Dot) && p.nth(1) == Some(T::Dot) && !p.is_joint() {
        p.recover_tokens(ParseRecoveryKind::Unexpected, 2);
    }
    if p.at(T::Dot) {
        p.token();
        p.expect(T::Dot);
    } else {
        p.missing(ParseRecoveryKind::RangeOperator);
        // Without the operator, a boundary ends the header and a `{` is the body: an end taken
        // from either would take the next statement, or the body, with it.
        if p.is_at_boundary() || p.at(T::LBrace) {
            return (start, None);
        }
    }
    (start, operand_before(p, 0, ExprFollow::Block))
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

fn match_expr(p: &mut Marker<'_, '_>) -> CompletedMarker {
    let mut m = p.start();
    m.token();
    if let Some(scrutinee) = operand_before(&mut m, 0, ExprFollow::Block) {
        m.field(&scrutinee, 0);
    }
    if m.at(T::LBrace) {
        arm_list(&mut m);
    } else {
        m.missing(ParseRecoveryKind::Token(T::LBrace));
    }
    m.complete(N::MatchExpr)
}

/// A `MatchExpr`'s arms, from its `{`.
fn arm_list(m: &mut Marker<'_, '_>) {
    delimited_list::<ArmsRule>(m, 1);
}

/// `Pattern '=>' Expr`; a pattern is `_` or a member name with optional type arguments and
/// `(binding)`.
fn match_arm(p: &mut Marker<'_, '_>) {
    let mut m = p.start();
    if m.at(T::Underscore) {
        let rest = leaf(&mut m, N::RestPattern);
        m.field(&rest, 0);
    } else {
        let mut pattern = m.start();
        let member = leaf(&mut pattern, N::NameRef);
        pattern.field(&member, 0);
        type_args(&mut pattern, 1);
        if pattern.at(T::LParen) && !pattern.is_after_newline() {
            pattern.token();
            name_in(&mut pattern, 2);
            if pattern.at(T::RParen) {
                pattern.token();
            } else {
                pattern.missing(ParseRecoveryKind::Token(T::RParen));
            }
        }
        let pattern = pattern.complete(N::MemberPattern);
        m.field(&pattern, 0);
    }
    if is_nth_arm_arrow(&m, 0) {
        m.token();
        m.token();
    } else {
        m.missing(ParseRecoveryKind::ArmArrow);
    }
    if let Some(value) = operand(&mut m) {
        m.field(&value, 1);
    }
    m.complete(N::MatchArm);
}

fn if_block(p: &mut Marker<'_, '_>) -> Option<CompletedMarker> {
    if p.at(T::LBrace) {
        return Some(block(p));
    }
    let is_displaced =
        !(p.current().is_none_or(is_closer) || p.at(T::ElseKw) || p.is_after_newline());
    let recovery = if is_displaced {
        p.recover_tokens(ParseRecoveryKind::Token(T::LBrace), 1)
    } else {
        p.missing(ParseRecoveryKind::Token(T::LBrace))
    };
    if !is_displaced {
        return None;
    }
    skip(p, recovery, |p| {
        p.at(T::LBrace)
            || p.current().is_some_and(is_closer)
            || p.at(T::ElseKw)
            || p.is_after_newline()
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
    let glued = if p.is_nth_joint(n) {
        p.nth(n + 1)
    } else {
        None
    };
    binary_operator(p.nth(n)?, glued)
}

/// The width in tokens of the assignment operator at the `n`th token.
fn assign_op(p: &Marker<'_, '_>, n: usize) -> Option<usize> {
    let glued = if p.is_nth_joint(n) {
        p.nth(n + 1)
    } else {
        None
    };
    let (_, is_glued) = AssignOp::read(p.nth(n)?, glued)?;
    Some(1 + usize::from(is_glued))
}
