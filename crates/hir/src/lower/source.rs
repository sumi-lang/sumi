//! What lowering reads and reports against: the file, its declared names, and its diagnostics.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_frontend::{Diagnostic, DiagnosticCode, Label, ParsedSource};
use sumi_graph::{DeclId, FieldName, ShownTy, Ty, UnionId};
use sumi_lexer::{LexedFile, RawIdx, SyntaxKind};
use sumi_syntax::{
    NodeIdx, SyntaxTree,
    ast::{self, AstNode, View},
};
use sumi_text::TextRange;

use super::join;
use crate::codes;
use crate::{Occurrence, Symbol};

pub(super) type NameMap<'s, V> = HashMap<&'s str, V, FxBuildHasher>;

/// A declared type by name, with its fields by name; both resolve names while lowering.
pub(crate) struct DeclNames<'s> {
    pub name: &'s str,
    pub name_node: Option<NodeIdx>,
    /// Per field in declaration order.
    pub fields: Vec<(&'s str, NodeIdx)>,
}

impl DeclNames<'_> {
    pub(super) fn index_of(&self, name: &str) -> Option<usize> {
        self.fields.iter().position(|&(field, _)| field == name)
    }
}

pub(crate) struct Source<'s> {
    pub parsed: &'s ParsedSource,
    pub tree: &'s SyntaxTree,
    pub diagnostics: Vec<Diagnostic>,
    /// By declared type ID.
    pub decls: Vec<DeclNames<'s>>,
    /// None for a name declared more than once, which resolves to nothing, like a function's.
    pub(super) type_names: NameMap<'s, Option<DeclId>>,
    /// By field name ID.
    pub field_names: Vec<&'s str>,
    field_ids: NameMap<'s, FieldName>,
    /// Type names resolved outside a body.
    pub references: Vec<Occurrence>,
    /// Written unions interned here, then the typing's, which mints those inference resolves to,
    /// so every union a message names is in it.
    pub unions: Rc<RefCell<sumi_graph::Unions>>,
}

impl<'s> Source<'s> {
    pub fn new(parsed: &'s ParsedSource) -> Self {
        Self {
            parsed,
            tree: parsed.parse().tree(),
            diagnostics: Vec::new(),
            decls: Vec::new(),
            type_names: NameMap::default(),
            field_names: Vec::new(),
            field_ids: NameMap::default(),
            references: Vec::new(),
            unions: Rc::new(RefCell::new(sumi_graph::Unions::new())),
        }
    }
    pub fn show(&self, ty: Ty) -> ShownTy<'_> {
        ty.shown(self)
    }
}

impl sumi_graph::Names for Source<'_> {
    fn decl(&self, id: DeclId) -> &str {
        self.decls[id.index()].name
    }

    fn field(&self, name: FieldName) -> &str {
        self.field_names[name.index()]
    }

    fn members(&self, id: UnionId) -> Vec<DeclId> {
        self.unions.borrow().get(id).to_vec()
    }
}

impl<'s> Source<'s> {
    /// The ID of the field name `text`, minted on first sight.
    pub(super) fn field_name(&mut self, text: &'s str) -> FieldName {
        *self.field_ids.entry(text).or_insert_with(|| {
            self.field_names.push(text);
            FieldName::new(self.field_names.len() - 1)
        })
    }
    pub fn lexed(&self) -> &'s LexedFile {
        self.parsed.lexed()
    }
    pub fn range(&self, node: NodeIdx) -> TextRange {
        self.tree.byte_range(node, self.lexed())
    }
    pub fn text(&self, node: NodeIdx) -> &'s str {
        self.tree
            .byte_range(node, self.lexed())
            .text(self.parsed.source())
    }
    pub(super) fn name(&self, name: Option<ast::Name>) -> Option<(&'s str, NodeIdx)> {
        let node = name?.clean(self.tree, self.lexed())?.node();
        Some((self.text(node), node))
    }
    pub fn error(
        &mut self,
        node: NodeIdx,
        code: DiagnosticCode,
        message: impl Into<Box<str>>,
        related: Option<(TextRange, &'static str)>,
    ) {
        let related = related.map(|(range, message)| (range, Box::from(message)));
        self.report(self.range(node), code, message, related);
    }
    pub fn report(
        &mut self,
        primary: TextRange,
        code: DiagnosticCode,
        message: impl Into<Box<str>>,
        related: impl IntoIterator<Item = (TextRange, Box<str>)>,
    ) {
        self.diagnostics
            .push(diagnostic(primary, code, message, related));
    }
    pub fn type_mismatch(
        &mut self,
        at: TextRange,
        expected: Ty,
        actual: Ty,
        related: Option<(TextRange, &'static str)>,
    ) {
        let related = related.map(|(range, message)| (range, Box::from(message)));
        self.report(
            at,
            codes::TYPE_MISMATCH,
            format!(
                "expected {}, found {}",
                self.show(expected),
                self.show(actual)
            ),
            related,
        );
    }
    /// `message` receives the two or more claimed types joined as a list, in source order. Types
    /// claimed at one origin share a label, since a call delivers all of its callee's.
    pub fn conflict_at(
        &mut self,
        at: TextRange,
        code: DiagnosticCode,
        mut claimed: Vec<(Ty, Option<TextRange>)>,
        message: impl FnOnce(String) -> String,
    ) {
        assert!(claimed.len() >= 2, "a conflict names two types");
        claimed.sort_by_key(|(_, origin)| origin.map(|range| (range.start(), range.end())));
        let types: Vec<_> = claimed
            .iter()
            .map(|(ty, _)| self.show(*ty).to_string())
            .collect();
        let mut labels: Vec<(TextRange, Vec<String>)> = Vec::new();
        for (ty, origin) in &claimed {
            let Some(origin) = origin else { continue };
            let ty = self.show(*ty).to_string();
            match labels.last_mut() {
                Some((labeled, types)) if labeled == origin => types.push(ty),
                _ => labels.push((*origin, vec![ty])),
            }
        }
        let labels = labels
            .into_iter()
            .map(|(origin, types)| (origin, format!("{} here", join(&types)).into()));
        self.report(at, code, message(join(&types)), labels);
    }
    pub(super) fn ty(&mut self, node: ast::Type) -> Option<Ty> {
        let union = match node {
            ast::Type::TypeRef(name) => return self.named_ty(name),
            ast::Type::UnionType(union) => union,
        };
        if self.tree.has_error(union.node()) {
            return None;
        }
        // Nested to the left: the leftmost name is deepest.
        let mut names = vec![union.rhs(self.tree)];
        let mut lhs = union.lhs(self.tree);
        while let Some(ast::Type::UnionType(inner)) = lhs {
            names.push(inner.rhs(self.tree));
            lhs = inner.lhs(self.tree);
        }
        if let Some(ast::Type::TypeRef(first)) = lhs {
            names.push(Some(first));
        }
        names.reverse();
        let mut members = Vec::new();
        let mut is_valid = true;
        for member in names {
            let Some(member) = member else {
                is_valid = false;
                continue;
            };
            match self.named_ty(member).map(|ty| (ty, ty.as_decl())) {
                Some((_, Some(decl))) => members.push(decl),
                Some((ty, None)) => {
                    self.error(
                        member.node(),
                        codes::INVALID_UNION_MEMBER,
                        format!(
                            "`{}` is no declared type, so no member of a union",
                            self.show(ty)
                        ),
                        None,
                    );
                    is_valid = false;
                }
                None => is_valid = false,
            }
        }
        if !is_valid {
            return None;
        }
        Some(self.union_of(&members))
    }
    /// The union of `members`, or the one member there is.
    pub(super) fn union_of(&mut self, members: &[DeclId]) -> Ty {
        match self.unions.borrow_mut().intern(members.iter().copied()) {
            Some(id) => Ty::union(id),
            None => Ty::decl(members[0]),
        }
    }
    pub(super) fn named_ty(&mut self, node: ast::TypeRef) -> Option<Ty> {
        if self.tree.has_error(node.node()) {
            return None;
        }
        let name = self.text(node.node());
        if let Some(ty) = Ty::scalar(name) {
            return Some(ty);
        }
        if let Some(&decl) = self.type_names.get(name) {
            let decl = decl?;
            self.references.push(Occurrence {
                range: self.range(node.node()),
                symbol: Symbol::Type(decl),
                is_write: false,
            });
            return Some(Ty::decl(decl));
        }
        self.error(
            node.node(),
            codes::UNKNOWN_TYPE,
            format!("unknown type `{name}`"),
            None,
        );
        None
    }
    pub(super) fn tokens(
        &self,
        start: RawIdx,
        end: RawIdx,
    ) -> impl Iterator<Item = SyntaxKind> + '_ {
        start
            .until(end)
            .map(|raw| self.lexed().kind(raw))
            .filter(|kind| !kind.is_trivia())
    }
    pub(super) fn peel(&self, mut expr: ast::Expr) -> ast::Expr {
        while let ast::Expr::ParenExpr(paren) = expr {
            let Some(paren) = paren.clean(self.tree, self.lexed()) else {
                break;
            };
            expr = paren.inner();
        }
        expr
    }
}

pub(crate) fn diagnostic(
    primary: TextRange,
    code: DiagnosticCode,
    message: impl Into<Box<str>>,
    related: impl IntoIterator<Item = (TextRange, Box<str>)>,
) -> Diagnostic {
    Diagnostic {
        code,
        message: message.into(),
        primary,
        labels: related
            .into_iter()
            .map(|(range, message)| Label { range, message })
            .collect(),
        fix: None,
    }
}
