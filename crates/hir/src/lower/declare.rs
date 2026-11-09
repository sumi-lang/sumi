//! The items of a file before any body: type declarations with their fields, and function headers
//! with their parameters and result.

use std::collections::hash_map::Entry;

use rustc_hash::FxBuildHasher;
use sumi_graph::{Decl, DeclId, FieldName, FunctionId, GraphBuilder, Ty};
use sumi_lexer::SyntaxKind;
use sumi_syntax::{
    NodeIdx,
    ast::{self, AstNode},
};
use sumi_text::TextRange;

use super::source::{DeclNames, NameMap, Source};
use crate::codes;

/// What an item name denotes.
#[derive(Clone, Copy)]
pub(super) enum Named {
    Function(FunctionId),
    Type(DeclId),
    /// Declared more than once, so a use of it is reported nowhere but at the declarations.
    Ambiguous,
}

/// A declared type as the source wrote it; the graph holds its field types.
pub(crate) struct TypeHeader {
    pub name: Option<TextRange>,
    pub item: NodeIdx,
    /// Per field in declaration order, its name's range.
    pub fields: Vec<TextRange>,
}

#[derive(Clone, Copy)]
pub(crate) struct Header {
    pub name: Option<TextRange>,
    pub result: HeaderResult,
    pub item: NodeIdx,
}

#[derive(Clone, Copy)]
pub(crate) enum HeaderResult {
    /// The declaration is damaged; an omitted annotation is never this.
    None,
    /// The node is the annotation.
    Declared(Ty, NodeIdx),
    /// A block body with no annotation declares `unit`; the node is the parameter list.
    Omitted(NodeIdx),
    Inferred,
}

impl HeaderResult {
    /// The type the body is held to and the node declaring it, written or omitted.
    pub(super) fn declared(self) -> Option<(Ty, NodeIdx)> {
        match self {
            Self::Declared(ty, node) => Some((ty, node)),
            Self::Omitted(node) => Some((Ty::UNIT, node)),
            Self::None | Self::Inferred => None,
        }
    }
}

pub(crate) struct Parameter<'s> {
    pub(super) node: NodeIdx,
    pub(super) name: Option<(&'s str, NodeIdx)>,
    pub(super) ty: Option<Ty>,
    pub(super) is_duplicate: bool,
}

pub(crate) struct Declarations<'s> {
    pub headers: Vec<Header>,
    pub types: Vec<TypeHeader>,
    pub(super) names: NameMap<'s, Named>,
    pub(super) parameters: Vec<Vec<Parameter<'s>>>,
}

/// Takes an item's name for `named`, reporting a second declaration of it.
fn claim_name<'s>(
    source: &mut Source<'s>,
    names: &mut NameMap<'s, Named>,
    declared_at: &mut NameMap<'s, NodeIdx>,
    (name, node): (&'s str, NodeIdx),
    named: Named,
    what: &str,
) {
    match names.entry(name) {
        Entry::Occupied(mut entry) => {
            let first = declared_at[name];
            source.error(
                node,
                codes::DUPLICATE_NAME,
                format!("duplicate {what} `{name}`"),
                Some((source.range(first), "declared here")),
            );
            *entry.get_mut() = Named::Ambiguous;
        }
        Entry::Vacant(entry) => {
            entry.insert(named);
            declared_at.insert(name, node);
        }
    }
}

/// The type items first, so a signature names any of them; the function items in their own order,
/// so a `FunctionId` indexes them.
pub(crate) fn declare<'s>(
    source: &mut Source<'s>,
    items: &[ast::Item],
    graph: &mut GraphBuilder,
) -> Declarations<'s> {
    let tree = source.tree;
    let mut names: NameMap<Named> = NameMap::with_capacity_and_hasher(items.len(), FxBuildHasher);
    let mut declared_at: NameMap<NodeIdx> = NameMap::default();
    let type_items: Vec<ast::TypeItem> = items
        .iter()
        .filter_map(|item| match item {
            ast::Item::TypeItem(item) => Some(*item),
            ast::Item::FnItem(_) => None,
        })
        .collect();
    for (index, item) in type_items.iter().enumerate() {
        let name = source.name(item.name(tree));
        let decl = DeclId::new(index);
        if let Some((text, node)) = name {
            if Ty::scalar(text).is_some() {
                source.error(
                    node,
                    codes::DUPLICATE_NAME,
                    format!("`{text}` is a built-in type"),
                    None,
                );
            } else {
                claim_name(
                    source,
                    &mut names,
                    &mut declared_at,
                    (text, node),
                    Named::Type(decl),
                    "type",
                );
                let resolved = match names.get(text) {
                    Some(Named::Type(_)) => Some(decl),
                    _ => None,
                };
                source.type_names.insert(text, resolved);
            }
        }
        source.decls.push(DeclNames {
            name: name.map_or("<missing>", |(name, _)| name),
            name_node: name.map(|(_, node)| node),
            fields: Vec::new(),
        });
    }
    let mut types = Vec::with_capacity(type_items.len());
    let mut decls: Vec<Vec<(FieldName, Option<Ty>)>> = Vec::with_capacity(type_items.len());
    for (index, item) in type_items.iter().enumerate() {
        let mut fields: Vec<(&'s str, NodeIdx)> = Vec::new();
        let mut field_types: Vec<(FieldName, Option<Ty>)> = Vec::new();
        let mut ranges = Vec::new();
        if let Some(list) = item.field_list(tree) {
            for field in list.fields(tree) {
                // A field without a type is a syntax error the parser already reported.
                let ty = field.type_ref(tree).and_then(|ty| source.ty(ty));
                let Some((name, node)) = source.name(field.name(tree)) else {
                    continue;
                };
                if let Some(&(_, first)) = fields.iter().find(|&&(earlier, _)| earlier == name) {
                    source.error(
                        node,
                        codes::DUPLICATE_NAME,
                        format!("duplicate field `{name}`"),
                        Some((source.range(first), "declared here")),
                    );
                    continue;
                }
                fields.push((name, node));
                field_types.push((source.field_name(name), ty));
                ranges.push(source.range(node));
            }
        }
        source.decls[index].fields = fields;
        decls.push(field_types);
        types.push(TypeHeader {
            name: source.decls[index].name_node.map(|node| source.range(node)),
            item: item.node(),
            fields: ranges,
        });
    }
    unfold_recursive_types(source, &mut decls);
    graph.declare(
        decls
            .into_iter()
            .map(|fields| Decl::new(fields.into_boxed_slice())),
    );
    let items: Vec<ast::FnItem> = items
        .iter()
        .filter_map(|item| match item {
            ast::Item::FnItem(item) => Some(*item),
            ast::Item::TypeItem(_) => None,
        })
        .collect();
    let mut parameters = Vec::with_capacity(items.len());
    let mut headers = Vec::with_capacity(items.len());
    for item in &items {
        let name = source.name(item.name(tree));
        let list = item.param_list(tree);
        let whole_list = list.filter(|list| !tree.has_error(list.node()));
        let mut params: Vec<Parameter> = Vec::new();
        if let Some(list) = list {
            for param in list.params(tree) {
                // A parameter without a type is a syntax error the parser already reported.
                let ty = param.type_ref(tree).and_then(|ty| source.ty(ty));
                let name = source.name(param.name(tree));
                let first = name.and_then(|(name, node)| {
                    let first = params
                        .iter()
                        .find_map(|p| p.name.filter(|(earlier, _)| *earlier == name))?;
                    Some((name, node, first.1))
                });
                if let Some((name, node, first)) = first {
                    source.error(
                        node,
                        codes::DUPLICATE_NAME,
                        format!("duplicate parameter `{name}`"),
                        Some((source.range(first), "declared here")),
                    );
                }
                params.push(Parameter {
                    node: param.node(),
                    name,
                    ty,
                    is_duplicate: first.is_some(),
                });
            }
        }
        let result = if let Some(ret) = item.ret(tree) {
            match source.ty(ret) {
                Some(ty) => HeaderResult::Declared(ty, ret.node()),
                None => HeaderResult::None,
            }
        } else {
            // A missing annotation may be damage: only an empty gap or the expression-body `=` says
            // it was left out.
            let gap = whole_list.map(|list| {
                let end = item
                    .body(tree)
                    .map_or(tree.end_token(item.node()), |e| tree.first_token(e.node()));
                let mut tokens = source.tokens(tree.end_token(list.node()), end);
                (list, tokens.next(), tokens.next())
            });
            match gap {
                Some((list, None, None)) => HeaderResult::Omitted(list.node()),
                Some((_, Some(SyntaxKind::Eq), None)) => HeaderResult::Inferred,
                _ => HeaderResult::None,
            }
        };
        // A whole list has every parameter typed, a repeated name aside.
        let types =
            whole_list.and_then(|_| params.iter().map(|p| p.ty).collect::<Option<Box<[Ty]>>>());
        let id = graph.function(types);
        if let Some(name) = name {
            claim_name(
                source,
                &mut names,
                &mut declared_at,
                name,
                Named::Function(id),
                "function",
            );
        }
        headers.push(Header {
            name: name.map(|(_, node)| source.range(node)),
            result,
            item: item.node(),
        });
        parameters.push(params);
    }
    Declarations {
        headers,
        types,
        names,
        parameters,
    }
}

/// A type holding its own values through fields never finishes: each such field loses its type,
/// so the table the graph takes is finite in depth.
fn unfold_recursive_types(source: &mut Source<'_>, decls: &mut [Vec<(FieldName, Option<Ty>)>]) {
    let unions = source.unions.borrow();
    let members = |ty: Ty| {
        ty.as_decl()
            .into_iter()
            .chain(unions.members(ty).iter().copied())
    };
    let reaches = |decls: &[Vec<(FieldName, Option<Ty>)>], from: Ty, target: DeclId| {
        let mut seen = vec![false; decls.len()];
        let mut stack: Vec<DeclId> = members(from).collect();
        while let Some(decl) = stack.pop() {
            if decl == target {
                return true;
            }
            if std::mem::replace(&mut seen[decl.index()], true) {
                continue;
            }
            stack.extend(
                decls[decl.index()]
                    .iter()
                    .filter_map(|&(_, ty)| ty)
                    .flat_map(members),
            );
        }
        false
    };
    let mut cut: Vec<(DeclId, usize)> = Vec::new();
    for index in 0..decls.len() {
        let decl = DeclId::new(index);
        for (field, &(_, ty)) in decls[index].iter().enumerate() {
            if let Some(through) = ty.filter(|ty| ty.is_declared())
                && reaches(decls, through, decl)
            {
                cut.push((decl, field));
            }
        }
    }
    drop(unions);
    for &(decl, field) in &cut {
        let names = &source.decls[decl.index()];
        let (field_name, field_node) = names.fields[field];
        let at = names.name_node.unwrap_or(field_node);
        source.error(
            at,
            codes::RECURSIVE_TYPE,
            format!(
                "type `{}` holds itself through field `{field_name}`",
                names.name
            ),
            Some((source.range(field_node), "this field")),
        );
    }
    for (decl, field) in cut {
        decls[decl.index()][field].1 = None;
    }
}
