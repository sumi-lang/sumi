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
    Property,
    TypeParameter,
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
            SemanticTokenType::PROPERTY,
            SemanticTokenType::TYPE_PARAMETER,
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
            NodeKind::TypeItem => name(
                ast::TypeItem::cast(tree, node)
                    .and_then(|item| item.name(tree))
                    .map(|name| name.node()),
                Kind::Type,
                DECLARATION,
            ),
            NodeKind::TypeParamList => {
                for param in ast::TypeParamList::cast(tree, node).unwrap().params(tree) {
                    name(Some(param.node()), Kind::TypeParameter, DECLARATION);
                }
            }
            NodeKind::Param => name(
                ast::Param::cast(tree, node)
                    .and_then(|param| param.name(tree))
                    .map(|name| name.node()),
                Kind::Parameter,
                DECLARATION | READONLY,
            ),
            NodeKind::Field => name(
                ast::Field::cast(tree, node)
                    .and_then(|field| field.name(tree))
                    .map(|name| name.node()),
                Kind::Property,
                DECLARATION,
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
            NodeKind::MemberPattern => {
                let pattern = ast::MemberPattern::cast(tree, node).unwrap();
                name(
                    pattern.member(tree).map(|member| member.node()),
                    Kind::Type,
                    0,
                );
                name(
                    pattern.binding(tree).map(|name| name.node()),
                    Kind::Variable,
                    DECLARATION | READONLY,
                );
            }
            NodeKind::TypeRef => name(Some(node), Kind::Type, 0),
            // A constructor call reads as a function until the analysis resolves its callee.
            NodeKind::CallExpr => name(
                ast::CallExpr::cast(tree, node)
                    .and_then(|call| call.callee(tree))
                    .map(|callee| callee.node()),
                Kind::Function,
                0,
            ),
            NodeKind::Arg => name(
                ast::Arg::cast(tree, node)
                    .and_then(|arg| arg.label(tree))
                    .map(|label| label.node()),
                Kind::Property,
                0,
            ),
            NodeKind::FieldExpr => name(
                ast::FieldExpr::cast(tree, node)
                    .and_then(|expr| expr.field(tree))
                    .map(|field| field.node()),
                Kind::Property,
                0,
            ),
            _ => {}
        }
    }
    if let Some(analysis) = analysis {
        for reference in analysis.references() {
            let style = match reference.symbol {
                Symbol::Function(_) => (Kind::Function, 0),
                Symbol::Type(id) if analysis.decl(id).is_param() => (Kind::TypeParameter, 0),
                Symbol::Type(_) => (Kind::Type, 0),
                Symbol::Field(..) => (Kind::Property, 0),
                Symbol::Local(id) => match analysis.binding(id).kind() {
                    BindingKind::Param => (Kind::Parameter, READONLY),
                    BindingKind::Let { is_mutable: true } => (Kind::Variable, 0),
                    BindingKind::Let { is_mutable: false }
                    | BindingKind::LoopIndex
                    | BindingKind::Arm => (Kind::Variable, READONLY),
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

#[cfg(test)]
mod tests {
    use sumi_frontend::parse_source;
    use sumi_hir::analyze;
    use sumi_text::Encoding;

    use super::{DECLARATION, Kind, READONLY, tokens};

    const TYPES: &str = "type Point { x: int, y: int }
type Unit {}
fn origin() -> Point = Point(x: 1, y: 2)
fn pick(v: Point | Unit) -> int = match v { Point(p) => p.x, Unit => 0 }
fn main() -> int = pick(origin())
";

    /// Every named token as its text, kind, and modifiers, in source order.
    fn names(text: &str, refined: bool) -> Vec<(&str, u32, u32)> {
        let parsed = parse_source(text.into()).unwrap();
        let analysis = refined.then(|| analyze(parsed.clone()));
        let lines: Vec<&str> = text.lines().collect();
        let (mut line, mut column) = (0, 0);
        tokens(&parsed, analysis.as_ref(), Encoding::Utf8)
            .data
            .into_iter()
            .filter_map(|token| {
                line += token.delta_line as usize;
                column = if token.delta_line == 0 {
                    column + token.delta_start as usize
                } else {
                    token.delta_start as usize
                };
                let named = [
                    Kind::Function,
                    Kind::Parameter,
                    Kind::Variable,
                    Kind::Type,
                    Kind::Property,
                    Kind::TypeParameter,
                ];
                named
                    .iter()
                    .any(|&kind| kind as u32 == token.token_type)
                    .then(|| {
                        let text = &lines[line][column..column + token.length as usize];
                        (text, token.token_type, token.token_modifiers_bitset)
                    })
            })
            .collect()
    }

    #[test]
    fn type_parameters_are_named_where_declared_and_where_the_analysis_resolves_them() {
        let (function, parameter, ty, property, type_parameter) = (
            Kind::Function as u32,
            Kind::Parameter as u32,
            Kind::Type as u32,
            Kind::Property as u32,
            Kind::TypeParameter as u32,
        );
        let text = "type Box<T> { value: T }
fn id<T>(x: T) -> T = x
fn main() -> int = id<Box<int>>(Box<int>(value: 1)).value
";
        let declared = [
            ("Box", ty, DECLARATION),
            ("T", type_parameter, DECLARATION),
            ("value", property, DECLARATION),
        ];
        assert_eq!(names(text, false)[..3], declared);
        assert_eq!(names(text, false)[3], ("T", ty, 0));
        assert_eq!(
            names(text, true),
            [
                ("Box", ty, DECLARATION),
                ("T", type_parameter, DECLARATION),
                ("value", property, DECLARATION),
                ("T", type_parameter, 0),
                ("id", function, DECLARATION),
                ("T", type_parameter, DECLARATION),
                ("x", parameter, DECLARATION | READONLY),
                ("T", type_parameter, 0),
                ("T", type_parameter, 0),
                ("x", parameter, READONLY),
                ("main", function, DECLARATION),
                ("int", ty, 0),
                ("id", function, 0),
                ("Box", ty, 0),
                ("int", ty, 0),
                ("Box", ty, 0),
                ("int", ty, 0),
                ("value", property, 0),
                ("value", property, 0),
            ]
        );
    }

    #[test]
    fn declared_types_fields_and_arms_are_named_before_and_after_analysis() {
        let (function, parameter, variable, ty, property) = (
            Kind::Function as u32,
            Kind::Parameter as u32,
            Kind::Variable as u32,
            Kind::Type as u32,
            Kind::Property as u32,
        );
        let refined = names(TYPES, true);
        assert_eq!(
            refined,
            [
                ("Point", ty, DECLARATION),
                ("x", property, DECLARATION),
                ("int", ty, 0),
                ("y", property, DECLARATION),
                ("int", ty, 0),
                ("Unit", ty, DECLARATION),
                ("origin", function, DECLARATION),
                ("Point", ty, 0),
                ("Point", ty, 0),
                ("x", property, 0),
                ("y", property, 0),
                ("pick", function, DECLARATION),
                ("v", parameter, DECLARATION | READONLY),
                ("Point", ty, 0),
                ("Unit", ty, 0),
                ("int", ty, 0),
                ("v", parameter, READONLY),
                ("Point", ty, 0),
                ("p", variable, DECLARATION | READONLY),
                ("p", variable, READONLY),
                ("x", property, 0),
                ("Unit", ty, 0),
                ("main", function, DECLARATION),
                ("int", ty, 0),
                ("pick", function, 0),
                ("origin", function, 0),
            ]
        );
        let mut syntactic = refined.clone();
        syntactic[8] = ("Point", function, 0);
        syntactic[16] = ("v", variable, 0);
        syntactic[19] = ("p", variable, 0);
        assert_eq!(names(TYPES, false), syntactic);
    }
}
