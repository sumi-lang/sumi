//! What lowering reads and reports against: the file, its declared names, and its diagnostics.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_frontend::{Diagnostic, DiagnosticCode, Label, ParsedSource};
use sumi_graph::{DeclId, FieldName, ShownTy, Ty, TyKind, UnionId};
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

/// A declared type's fields as the graph takes them, each with its type when that resolved.
type Fields = Box<[(FieldName, Option<Ty>)]>;

/// The most instances of generic types and functions one file may name: instances multiply
/// with each generic item that names another at two types of its own.
pub(crate) const MAX_INSTANCES: usize = 1 << 16;

/// The declared types that are type parameters, which hold one range of IDs. A union holds values
/// of none of them.
#[derive(Clone, Copy, Default)]
pub(crate) struct Params {
    first: u32,
    end: u32,
}

impl Params {
    pub(super) fn new(first: DeclId, count: usize) -> Self {
        let first = u32::try_from(first.index()).expect("declared type count fits u32");
        let count = u32::try_from(count).expect("declared type count fits u32");
        Self {
            first,
            end: first + count,
        }
    }

    pub fn holds(self, decl: DeclId) -> bool {
        (self.first as usize..self.end as usize).contains(&decl.index())
    }

    /// Whether a union may hold values of `ty`: no scalar's, and no type parameter's.
    pub fn joins(self, ty: Ty) -> bool {
        match ty.kind() {
            TyKind::Decl(decl) => !self.holds(decl),
            TyKind::Union(_) => true,
            TyKind::Int | TyKind::Bool | TyKind::Unit => false,
        }
    }
}

/// A declared type by name, with its fields by name; both resolve names while lowering. A type
/// parameter is one with no fields.
pub(crate) struct DeclNames<'s> {
    /// The name an item declares, which its instances share.
    pub name: &'s str,
    pub name_node: Option<NodeIdx>,
    /// The item or the type parameter.
    pub origin: NodeIdx,
    /// Per field in declaration order.
    pub fields: Rc<[(&'s str, NodeIdx)]>,
    /// The item's instance at its own type parameters, which every symbol of the type names;
    /// itself for that instance and for a type parameter.
    pub item: DeclId,
    /// The type arguments of an instance of a generic item.
    pub args: Rc<[Ty]>,
}

impl DeclNames<'_> {
    pub(super) fn index_of(&self, name: &str) -> Option<usize> {
        self.fields.iter().position(|&(field, _)| field == name)
    }
}

/// A type item's parameters and the syntax its instances take their field types from.
pub(crate) struct TypeItem<'s> {
    pub params: Vec<&'s str>,
    /// Per field of the item's declared type, its type as written.
    pub field_types: Vec<Option<ast::Type>>,
}

pub(crate) struct Source<'s> {
    pub parsed: &'s ParsedSource,
    pub tree: &'s SyntaxTree,
    pub diagnostics: Vec<Diagnostic>,
    /// By declared type ID: the type items first, each as its instance at its own parameters,
    /// then every type parameter, then the other instances as they are named.
    pub decls: Vec<DeclNames<'s>>,
    pub params: Params,
    /// By type item, which its ID as a declared type indexes.
    pub(super) type_items: Vec<TypeItem<'s>>,
    /// By declared type ID, the fields the graph takes; none for an instance not yet settled.
    fields: Vec<Option<Fields>>,
    instances: HashMap<(DeclId, Rc<[Ty]>), DeclId, FxBuildHasher>,
    /// Instances whose fields are yet to resolve.
    unsettled: Vec<DeclId>,
    /// The instances declared so far, of types and of functions.
    pub(super) instance_count: usize,
    /// The type parameters in scope, each with the type it stands for.
    pub(super) scope: Vec<(&'s str, Ty)>,
    /// Whether what is resolved now repeats, at other types, what was reported and recorded at a
    /// generic item's own parameters.
    pub(super) is_muted: bool,
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
            params: Params::default(),
            type_items: Vec::new(),
            fields: Vec::new(),
            instances: HashMap::default(),
            unsettled: Vec::new(),
            instance_count: 0,
            scope: Vec::new(),
            is_muted: false,
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

    fn type_args(&self, id: DeclId) -> &[Ty] {
        &self.decls[id.index()].args
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
    /// The name a `TypeRef` or a `NameRef` begins with.
    pub(super) fn head(&self, node: NodeIdx) -> &'s str {
        self.lexed()
            .text(self.parsed.source(), self.tree.first_token(node))
    }
    pub(super) fn name(&self, name: Option<ast::Name>) -> Option<(&'s str, NodeIdx)> {
        let node = name?.clean(self.tree, self.lexed())?.node();
        Some((self.text(node), node))
    }
    /// The type the type parameter `name` stands for, when one of that name is in scope.
    pub(super) fn param(&self, name: &str) -> Option<Ty> {
        self.scope
            .iter()
            .find(|&&(param, _)| param == name)
            .map(|&(_, ty)| ty)
    }
    /// Declares a type of no instance: an item's own, or a type parameter.
    pub(super) fn declare(
        &mut self,
        name: &'s str,
        name_node: Option<NodeIdx>,
        origin: NodeIdx,
    ) -> DeclId {
        let id = DeclId::new(self.decls.len());
        self.decls.push(DeclNames {
            name,
            name_node,
            origin,
            fields: Rc::from([]),
            item: id,
            args: Rc::from([]),
        });
        self.fields.push(Some(Box::from([])));
        id
    }
    /// The fields of a type declared by [`declare`](Self::declare), and for a generic item the
    /// parameters its own instance is at.
    pub(super) fn define(
        &mut self,
        decl: DeclId,
        names: Vec<(&'s str, NodeIdx)>,
        fields: Vec<(FieldName, Option<Ty>)>,
        params: Vec<Ty>,
    ) {
        let args: Rc<[Ty]> = params.into();
        if !args.is_empty() {
            self.instances.insert((decl, args.clone()), decl);
        }
        let entry = &mut self.decls[decl.index()];
        entry.fields = names.into();
        entry.args = args;
        self.fields[decl.index()] = Some(fields.into());
    }
    /// Whether a field of an item's own type has its type.
    pub(super) fn has_field_type(&self, decl: DeclId, field: usize) -> bool {
        self.fields[decl.index()]
            .as_ref()
            .is_some_and(|fields| fields[field].1.is_some())
    }
    /// A field loses its type where the declaration is reported for it.
    pub(super) fn drop_field_type(&mut self, decl: DeclId, field: usize) {
        self.fields[decl.index()]
            .as_mut()
            .expect("an item's own type is settled where it is declared")[field]
            .1 = None;
    }
    /// The fields of `decl`, each with its type when that resolved.
    pub fn fields(&mut self, decl: DeclId) -> &[(FieldName, Option<Ty>)] {
        self.settle();
        self.fields[decl.index()]
            .as_deref()
            .expect("every instance is settled")
    }
    /// Every declared type's fields, in ID order, for the graph.
    pub(super) fn take_fields(&mut self) -> Vec<Fields> {
        self.settle();
        std::mem::take(&mut self.fields)
            .into_iter()
            .map(|fields| fields.expect("every instance is settled"))
            .collect()
    }
    /// Resolves the fields of every instance named since the last call, off a stack: a chain of
    /// generic types is as deep as it is long. Every type item is defined by then.
    pub(super) fn settle(&mut self) {
        while let Some(decl) = self.unsettled.pop() {
            let (item, args) = {
                let names = &self.decls[decl.index()];
                (names.item, names.args.clone())
            };
            let params = &self.type_items[item.index()].params;
            let scope: Vec<_> = params.iter().copied().zip(args.iter().copied()).collect();
            let scope = std::mem::replace(&mut self.scope, scope);
            let was_muted = std::mem::replace(&mut self.is_muted, true);
            let own = self.fields[item.index()]
                .clone()
                .expect("an item's own type is settled where it is declared");
            // A field with no type at the item's own parameters has none in any instance.
            let fields = own
                .iter()
                .enumerate()
                .map(|(index, &(name, ty))| {
                    let written = self.type_items[item.index()].field_types[index];
                    (
                        name,
                        written.filter(|_| ty.is_some()).and_then(|ty| self.ty(ty)),
                    )
                })
                .collect();
            self.scope = scope;
            self.is_muted = was_muted;
            self.fields[decl.index()] = Some(fields);
            // An instance named before its item's fields were takes their names here.
            self.decls[decl.index()].fields = self.decls[item.index()].fields.clone();
        }
    }
    /// The instance of the generic `item` at `args`, declared on first use; none past the limit
    /// on instances, which is reported once.
    pub(super) fn instantiate(&mut self, item: DeclId, args: Vec<Ty>) -> Option<DeclId> {
        let args: Rc<[Ty]> = args.into();
        if let Some(&decl) = self.instances.get(&(item, args.clone())) {
            return Some(decl);
        }
        let own = &self.decls[item.index()];
        let name = own.name;
        if !self.count_instance(self.range(own.name_node.unwrap_or(own.origin)), name) {
            return None;
        }
        let decl = DeclId::new(self.decls.len());
        let own = &self.decls[item.index()];
        self.decls.push(DeclNames {
            name,
            name_node: own.name_node,
            origin: own.origin,
            fields: own.fields.clone(),
            item,
            args: args.clone(),
        });
        self.fields.push(None);
        self.unsettled.push(decl);
        self.instances.insert((item, args), decl);
        Some(decl)
    }
    /// Counts one more instance, of the generic item `name` declared at `at`; false past the limit.
    pub(super) fn count_instance(&mut self, at: TextRange, name: &str) -> bool {
        if self.instance_count == MAX_INSTANCES {
            let message = format!(
                "`{name}` is one instance too many: a file names at most {MAX_INSTANCES} \
                 instances of generic types and functions"
            );
            self.diagnostics
                .push(diagnostic(at, codes::TOO_MANY_INSTANCES, message, []));
        }
        self.instance_count += 1;
        self.instance_count <= MAX_INSTANCES
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
        if !self.is_muted {
            self.diagnostics
                .push(diagnostic(primary, code, message, related));
        }
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
            let Some(ty) = self.named_ty(member) else {
                is_valid = false;
                continue;
            };
            match ty.as_decl() {
                Some(decl) if self.params.joins(ty) => members.push(decl),
                Some(_) => {
                    self.error(
                        member.node(),
                        codes::INVALID_UNION_MEMBER,
                        format!(
                            "`{}` is a type parameter, so no member of a union",
                            self.show(ty)
                        ),
                        None,
                    );
                    is_valid = false;
                }
                None => {
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
        let name = self.head(node.node());
        let list = node.type_args(self.tree);
        let at = TextRange::new(
            self.range(node.node()).start(),
            self.lexed().range(self.tree.first_token(node.node())).end(),
        );
        let scalar = Ty::scalar(name);
        let param = self.param(name).filter(|_| scalar.is_none());
        if let Some(ty) = scalar.or(param) {
            let (given, _) = self.type_args(list);
            if given > 0 {
                self.report(
                    at,
                    codes::TYPE_ARGUMENTS,
                    format!("`{name}` takes no type arguments"),
                    [],
                );
                return None;
            }
            if let Some(decl) = param.and_then(Ty::as_decl) {
                self.refer(at, Symbol::Type(decl));
            }
            return Some(ty);
        }
        if let Some(&item) = self.type_names.get(name) {
            let Some(item) = item else {
                self.type_args(list);
                return None;
            };
            self.refer(at, Symbol::Type(item));
            return self.apply(item, list, at, false).map(Ty::decl);
        }
        self.type_args(list);
        self.report(
            at,
            codes::UNKNOWN_TYPE,
            format!("unknown type `{name}`"),
            [],
        );
        None
    }
    fn refer(&mut self, range: TextRange, symbol: Symbol) {
        if !self.is_muted {
            self.references.push(Occurrence {
                range,
                symbol,
                is_write: false,
            });
        }
    }
    /// The count of type arguments written, and their types when every one resolved.
    pub(super) fn type_args(&mut self, list: Option<ast::TypeArgList>) -> (usize, Option<Vec<Ty>>) {
        let Some(list) = list else {
            return (0, Some(Vec::new()));
        };
        let args: Vec<Option<Ty>> = list.args(self.tree).map(|arg| self.ty(arg)).collect();
        (args.len(), args.into_iter().collect())
    }
    /// The type the item `item` is at the type arguments in `list`, one per type parameter; `at`
    /// is the name they follow. A list the parser recovered around is not yet the wrong length.
    pub(super) fn apply(
        &mut self,
        item: DeclId,
        list: Option<ast::TypeArgList>,
        at: TextRange,
        is_damaged: bool,
    ) -> Option<DeclId> {
        let (given, args) = self.type_args(list);
        let expected = self.type_items[item.index()].params.len();
        let declared = self.decls[item.index()]
            .name_node
            .map(|node| self.range(node));
        if !self.takes(expected, given, list, at, declared, is_damaged) {
            return None;
        }
        if expected == 0 {
            return Some(item);
        }
        self.instantiate(item, args?)
    }
    /// Whether `given` type arguments are the `expected` ones of an item declared at `declared`;
    /// reported at `list`, or at `at` where none is written, unless the parser recovered there.
    pub(super) fn takes(
        &mut self,
        expected: usize,
        given: usize,
        list: Option<ast::TypeArgList>,
        at: TextRange,
        declared: Option<TextRange>,
        is_damaged: bool,
    ) -> bool {
        if given != expected && !is_damaged {
            self.report(
                list.map_or(at, |list| self.range(list.node())),
                codes::TYPE_ARGUMENTS,
                format!("expected {expected} type arguments, found {given}"),
                declared.map(|declared| (declared, Box::from("declared here"))),
            );
        }
        given == expected
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
