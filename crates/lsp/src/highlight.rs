use lsp_types::{
    Position, SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokens,
    SemanticTokensDelta, SemanticTokensEdit, SemanticTokensFullDeltaResult, SemanticTokensLegend,
};
use sumi_frontend::ParsedSource;
use sumi_hir::{Analysis, BindingKind, Symbol};
use sumi_lexer::{RawIdx, SyntaxKind};
use sumi_syntax::NodeKind;
use sumi_syntax::ast::{self, AstNode, View};
use sumi_text::Encoding;

#[derive(Clone, Copy)]
#[repr(u32)]
enum Kind {
    Function,
    Parameter,
    Variable,
    Keyword,
    Type,
    Number,
    Comment,
    Operator,
    Boolean,
    Punctuation,
    Invalid,
}

const DECLARATION: u32 = 1 << 0;
const READONLY: u32 = 1 << 1;

pub(crate) fn legend() -> SemanticTokensLegend {
    SemanticTokensLegend {
        token_types: vec![
            SemanticTokenType::FUNCTION,
            SemanticTokenType::PARAMETER,
            SemanticTokenType::VARIABLE,
            SemanticTokenType::KEYWORD,
            SemanticTokenType::TYPE,
            SemanticTokenType::NUMBER,
            SemanticTokenType::COMMENT,
            SemanticTokenType::OPERATOR,
            SemanticTokenType::new("boolean"),
            SemanticTokenType::new("punctuation"),
            SemanticTokenType::new("invalid"),
        ],
        token_modifiers: vec![
            SemanticTokenModifier::DECLARATION,
            SemanticTokenModifier::READONLY,
        ],
    }
}

pub(crate) fn tokens(
    parsed: &ParsedSource,
    analysis: Option<&Analysis>,
    encoding: Encoding,
) -> SemanticTokens {
    let lexed = parsed.lexed();
    let tree = parsed.parse().tree();
    let raw = || RawIdx::new(0).until(RawIdx::new(lexed.len() as u32));
    let mut styles: Vec<_> = raw()
        .map(|token| {
            let kind = match lexed.kind(token) {
                SyntaxKind::Whitespace | SyntaxKind::Newline => return None,
                SyntaxKind::LineComment => Kind::Comment,
                SyntaxKind::Ident => Kind::Variable,
                SyntaxKind::IntLiteral if lexed.flags(token).is_empty() => Kind::Number,
                SyntaxKind::IntLiteral | SyntaxKind::Error => Kind::Invalid,
                SyntaxKind::TrueKw | SyntaxKind::FalseKw => Kind::Boolean,
                SyntaxKind::LParen
                | SyntaxKind::RParen
                | SyntaxKind::LBrace
                | SyntaxKind::RBrace
                | SyntaxKind::Comma => Kind::Punctuation,
                kind if kind
                    .text()
                    .is_some_and(|text| SyntaxKind::from_keyword(text).is_some()) =>
                {
                    Kind::Keyword
                }
                _ => Kind::Operator,
            };
            Some((kind, 0))
        })
        .collect();
    let mut name = |node, kind, modifiers| {
        if let Some(node) = node {
            let token = tree.first_token(node);
            if lexed.kind(token) == SyntaxKind::Ident {
                styles[token.to_usize()] = Some((kind, modifiers));
            }
        }
    };
    for node in tree.nodes() {
        match tree.kind(node) {
            NodeKind::FnItem => name(
                ast::FnItem::cast(tree, node)
                    .and_then(|item| item.name(tree))
                    .map(|name| name.node()),
                Kind::Function,
                DECLARATION,
            ),
            NodeKind::Param => name(
                ast::Param::cast(tree, node)
                    .and_then(|param| param.name(tree))
                    .map(|name| name.node()),
                Kind::Parameter,
                DECLARATION | READONLY,
            ),
            NodeKind::LetStmt => {
                let binding = ast::LetStmt::cast(tree, node).unwrap();
                name(
                    binding.name(tree).map(|name| name.node()),
                    Kind::Variable,
                    DECLARATION
                        | if binding.mutable(tree, lexed) {
                            0
                        } else {
                            READONLY
                        },
                );
            }
            NodeKind::ForExpr => name(
                ast::ForExpr::cast(tree, node)
                    .and_then(|expr| expr.name(tree))
                    .map(|name| name.node()),
                Kind::Variable,
                DECLARATION | READONLY,
            ),
            NodeKind::TypeRef => name(Some(node), Kind::Type, 0),
            NodeKind::CallExpr => name(
                ast::CallExpr::cast(tree, node)
                    .and_then(|call| call.callee(tree))
                    .map(|callee| callee.node()),
                Kind::Function,
                0,
            ),
            _ => {}
        }
    }
    if let Some(analysis) = analysis {
        for reference in analysis.references() {
            let style = match reference.symbol {
                Symbol::Function(_) => (Kind::Function, 0),
                Symbol::Local(id) => match analysis.binding(id).kind() {
                    BindingKind::Param => (Kind::Parameter, READONLY),
                    BindingKind::Let { is_mutable: true } => (Kind::Variable, 0),
                    BindingKind::Let { is_mutable: false } | BindingKind::LoopIndex => {
                        (Kind::Variable, READONLY)
                    }
                },
            };
            let token = lexed.token_at(reference.range.start()).unwrap();
            styles[token.to_usize()] = Some(style);
        }
    }
    let mut position = Position::new(0, 0);
    let mut previous = Position::new(0, 0);
    let data = raw()
        .filter_map(|token| {
            if lexed.kind(token) == SyntaxKind::Newline {
                position.line += 1;
                position.character = 0;
                return None;
            }
            let text = lexed.text(parsed.source(), token);
            let length = if encoding == Encoding::Utf8 || text.is_ascii() {
                text.len()
            } else {
                text.encode_utf16().count()
            } as u32;
            let start = position;
            position.character += length;
            let (kind, token_modifiers_bitset) = styles[token.to_usize()]?;
            let delta_line = start.line - previous.line;
            let delta_start = if delta_line == 0 {
                start.character - previous.character
            } else {
                start.character
            };
            previous = start;
            Some(SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type: kind as u32,
                token_modifiers_bitset,
            })
        })
        .collect();
    SemanticTokens {
        result_id: None,
        data,
    }
}

pub(crate) fn delta(
    previous: Option<&SemanticTokens>,
    current: &SemanticTokens,
    previous_result_id: Option<&str>,
) -> SemanticTokensFullDeltaResult {
    let Some(previous) = previous.filter(|previous| {
        previous_result_id.is_some() && previous.result_id.as_deref() == previous_result_id
    }) else {
        return SemanticTokensFullDeltaResult::Tokens(current.clone());
    };
    let prefix = previous
        .data
        .iter()
        .zip(&current.data)
        .take_while(|(old, new)| old == new)
        .count();
    let suffix = previous.data[prefix..]
        .iter()
        .rev()
        .zip(current.data[prefix..].iter().rev())
        .take_while(|(old, new)| old == new)
        .count();
    let inserted = &current.data[prefix..current.data.len() - suffix];
    let deleted = previous.data.len() - prefix - suffix;
    let edits = if inserted.is_empty() && deleted == 0 {
        Vec::new()
    } else {
        vec![SemanticTokensEdit {
            start: (prefix * 5) as u32,
            delete_count: (deleted * 5) as u32,
            data: (!inserted.is_empty()).then(|| inserted.to_vec()),
        }]
    };
    SemanticTokensFullDeltaResult::TokensDelta(SemanticTokensDelta {
        result_id: current.result_id.clone(),
        edits,
    })
}
