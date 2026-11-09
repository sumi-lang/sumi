//! The items of a file before any body: type declarations with their fields, function headers with
//! their parameters and result, and the instances of the generic ones as they are named.

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::hash_map::Entry;
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_graph::{DeclId, FieldName, FunctionId, GraphBuilder, Ty, Unions};
use sumi_lexer::SyntaxKind;
use sumi_syntax::{
    NodeIdx, NodeKind,
    ast::{self, AstNode, View},
};
use sumi_text::TextRange;

use super::source::{NameMap, Source, TypeItem};
use crate::codes;
use crate::dependency::{Components, Rows};

/// What an item name denotes.
#[derive(Clone, Copy)]
pub(super) enum Named {
    Function(FunctionId),
    Type(DeclId),
    /// Declared more than once, so a use of it is reported nowhere but at the declarations.
    Ambiguous,
}

#[derive(Clone, Copy)]
pub(crate) struct Header {
    pub name: Option<TextRange>,
    pub result: HeaderResult,
    pub item: NodeIdx,
    /// The item's instance at its own type parameters, which every symbol of the function names;
    /// itself for that instance.
    pub generic: FunctionId,
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

pub(super) struct FnItem<'s> {
    pub item: ast::FnItem,
    pub params: Vec<&'s str>,
}

pub(crate) struct Declarations<'s> {
    /// By function: the function items first, each as its instance at its own type parameters,
    /// then the other instances as calls name them.
    pub headers: Vec<Header>,
    /// By function, the type arguments it is its item's instance at.
    pub type_args: Vec<Rc<[Ty]>>,
    pub(super) names: NameMap<'s, Named>,
    pub(super) parameters: Vec<Vec<Parameter<'s>>>,
    /// By function item, which its ID as a function indexes.
    pub(super) items: Vec<FnItem<'s>>,
    instances: HashMap<(FunctionId, Rc<[Ty]>), FunctionId, FxBuildHasher>,
    /// The calls no instance is made for: each would be at a type that grows without end.
    pub(super) unbounded: HashSet<NodeIdx, FxBuildHasher>,
}

impl<'s> Declarations<'s> {
    /// The instance of the generic function `generic` at `args`, declared on first use, so its
    /// body is lowered in its turn; none past the limit on instances.
    pub(super) fn instance(
        &mut self,
        source: &mut Source<'s>,
        graph: &mut GraphBuilder,
        generic: FunctionId,
        args: Vec<Ty>,
    ) -> Option<FunctionId> {
        let args: Rc<[Ty]> = args.into();
        if let Some(&function) = self.instances.get(&(generic, args.clone())) {
            return Some(function);
        }
        let own = self.headers[generic.index()];
        let item = &self.items[generic.index()];
        let name = own
            .name
            .map_or("<missing>", |name| name.text(source.parsed.source()));
        if !source.count_instance(own.name.unwrap_or(source.range(own.item)), name) {
            return None;
        }
        let scope = item.params.iter().copied().zip(args.iter().copied());
        let scope = std::mem::replace(&mut source.scope, scope.collect());
        let was_muted = std::mem::replace(&mut source.is_muted, true);
        let (mut header, parameters) = header(source, graph, item.item);
        source.scope = scope;
        source.is_muted = was_muted;
        header.generic = generic;
        let function = FunctionId::new(self.headers.len());
        self.headers.push(header);
        self.parameters.push(parameters);
        self.type_args.push(args.clone());
        self.instances.insert((generic, args), function);
        Some(function)
    }
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

/// The type parameters an item's head declares, each with its node; one named like a built-in type
/// or like another before it is reported and left out.
fn type_params<'s>(
    source: &mut Source<'s>,
    list: Option<ast::TypeParamList>,
) -> Vec<(&'s str, NodeIdx)> {
    let mut params: Vec<(&'s str, NodeIdx)> = Vec::new();
    let Some(list) = list else {
        return params;
    };
    for param in list.params(source.tree) {
        let Some((name, node)) = source.name(Some(param)) else {
            continue;
        };
        if Ty::scalar(name).is_some() {
            source.error(
                node,
                codes::DUPLICATE_NAME,
                format!("`{name}` is a built-in type"),
                None,
            );
        } else if let Some(&(_, first)) = params.iter().find(|&&(earlier, _)| earlier == name) {
            source.error(
                node,
                codes::DUPLICATE_NAME,
                format!("duplicate type parameter `{name}`"),
                Some((source.range(first), "declared here")),
            );
        } else {
            params.push((name, node));
        }
    }
    params
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
    let fn_items: Vec<ast::FnItem> = items
        .iter()
        .filter_map(|item| match item {
            ast::Item::FnItem(item) => Some(*item),
            ast::Item::TypeItem(_) => None,
        })
        .collect();
    for (index, item) in type_items.iter().enumerate() {
        let name = source.name(item.name(tree));
        let decl = source.declare(
            name.map_or("<missing>", |(name, _)| name),
            name.map(|(_, node)| node),
            item.node(),
        );
        debug_assert_eq!(decl.index(), index, "a type item's ID is its position");
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
    }
    // Every type parameter is declared before any type resolves, so one range of IDs holds them.
    let first_param = DeclId::new(type_items.len());
    let declare_params = |source: &mut Source<'s>, list: Option<ast::TypeParamList>| {
        type_params(source, list)
            .into_iter()
            .map(|(name, node)| (name, Ty::decl(source.declare(name, Some(node), node))))
            .collect::<Vec<_>>()
    };
    let type_scopes: Vec<Vec<(&'s str, Ty)>> = type_items
        .iter()
        .map(|item| declare_params(source, item.type_params(tree)))
        .collect();
    let fn_scopes: Vec<Vec<(&'s str, Ty)>> = fn_items
        .iter()
        .map(|item| declare_params(source, item.type_params(tree)))
        .collect();
    *source.unions.borrow_mut() =
        Unions::with_params(first_param, source.decls.len() - first_param.index());

    source.type_items = type_scopes
        .iter()
        .map(|scope| TypeItem {
            params: scope.iter().map(|&(name, _)| name).collect(),
            field_types: Vec::new(),
            recursive: Vec::new(),
        })
        .collect();
    // What each field's type names, where it resolved: a field without a type holds nothing.
    let mut mentions: Vec<Vec<Vec<DeclId>>> = Vec::with_capacity(type_items.len());
    for (index, (item, scope)) in type_items.iter().zip(&type_scopes).enumerate() {
        let params = source.type_items[index].params.clone();
        source.scope.clone_from(scope);
        let mut fields: Vec<(&'s str, NodeIdx)> = Vec::new();
        let mut field_types: Vec<(FieldName, Option<Ty>)> = Vec::new();
        let mut written: Vec<Option<ast::Type>> = Vec::new();
        let mut named: Vec<Vec<DeclId>> = Vec::new();
        if let Some(list) = item.field_list(tree) {
            for field in list.fields(tree) {
                // A field without a type is a syntax error the parser already reported.
                let annotation = field.type_ref(tree);
                let ty = annotation.and_then(|ty| source.ty(ty));
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
                written.push(annotation);
                named.push(match (annotation, ty) {
                    (Some(annotation), Some(_)) => source.mentions(annotation.node(), &params),
                    _ => Vec::new(),
                });
            }
        }
        source.type_items[index].recursive = vec![false; fields.len()];
        source.type_items[index].field_types = written;
        let args = scope.iter().map(|&(_, ty)| ty).collect();
        source.define(DeclId::new(index), fields, field_types, args);
        mentions.push(named);
    }
    source.scope.clear();
    drop_recursive_fields(source, &mentions);
    source.settle();

    let mut declarations = Declarations {
        headers: Vec::with_capacity(fn_items.len()),
        type_args: Vec::with_capacity(fn_items.len()),
        names,
        parameters: Vec::with_capacity(fn_items.len()),
        items: Vec::with_capacity(fn_items.len()),
        instances: HashMap::default(),
        unbounded: HashSet::default(),
    };
    for (item, scope) in fn_items.iter().zip(fn_scopes) {
        let name = source.name(item.name(tree));
        let args: Rc<[Ty]> = scope.iter().map(|&(_, ty)| ty).collect();
        source.scope = scope;
        let (header, parameters) = header(source, graph, *item);
        let id = header.generic;
        if let Some(name) = name {
            claim_name(
                source,
                &mut declarations.names,
                &mut declared_at,
                name,
                Named::Function(id),
                "function",
            );
        }
        if !args.is_empty() {
            declarations.instances.insert((id, args.clone()), id);
        }
        declarations.headers.push(header);
        declarations.type_args.push(args);
        declarations.parameters.push(parameters);
        declarations.items.push(FnItem {
            item: *item,
            params: source.scope.iter().map(|&(name, _)| name).collect(),
        });
    }
    source.scope.clear();
    declarations.unbounded = unbounded_calls(source, &declarations);
    declarations
}

/// The header of the next function, which is `item` at the type parameters in scope: its
/// parameters and result, as an instance of itself.
fn header<'s>(
    source: &mut Source<'s>,
    graph: &mut GraphBuilder,
    item: ast::FnItem,
) -> (Header, Vec<Parameter<'s>>) {
    let tree = source.tree;
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
    let types = whole_list.and_then(|_| params.iter().map(|p| p.ty).collect::<Option<Box<[Ty]>>>());
    let id = graph.function(types);
    let header = Header {
        name: name.map(|(_, node)| source.range(node)),
        result,
        item: item.node(),
        generic: id,
    };
    (header, params)
}

/// A type holding its own values through fields never finishes: each such field loses its type in
/// every instance, so the table the graph takes is finite in depth. `mentions` is, per type item
/// and field, the type items the field's type names.
fn drop_recursive_fields(source: &mut Source<'_>, mentions: &[Vec<Vec<DeclId>>]) {
    let reaches = |from: &[DeclId], target: DeclId| {
        let mut seen = vec![false; mentions.len()];
        let mut stack: Vec<DeclId> = from.to_vec();
        while let Some(decl) = stack.pop() {
            if decl == target {
                return true;
            }
            if std::mem::replace(&mut seen[decl.index()], true) {
                continue;
            }
            stack.extend(mentions[decl.index()].iter().flatten().copied());
        }
        false
    };
    let mut cut: Vec<(DeclId, usize)> = Vec::new();
    for (index, fields) in mentions.iter().enumerate() {
        let decl = DeclId::new(index);
        for (field, named) in fields.iter().enumerate() {
            if reaches(named, decl) {
                cut.push((decl, field));
            }
        }
    }
    for (decl, field) in cut {
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
        source.type_items[decl.index()].recursive[field] = true;
        source.drop_field_type(decl, field);
    }
}

/// The calls that would have no last instance. A call inside a generic function passes each of its
/// type parameters on, as written or inside a larger type; around a cycle of calls that passes one
/// on inside a larger type even once, the type grows with every turn.
fn unbounded_calls(
    source: &mut Source<'_>,
    declarations: &Declarations<'_>,
) -> HashSet<NodeIdx, FxBuildHasher> {
    struct Passed {
        from: usize,
        to: u32,
        /// The argument, when the parameter is passed inside a larger type.
        grows: Option<NodeIdx>,
        call: NodeIdx,
    }
    let tree = source.tree;
    let mut first: Vec<usize> = Vec::with_capacity(declarations.items.len() + 1);
    let mut count = 0;
    for item in &declarations.items {
        first.push(count);
        count += item.params.len();
    }
    let mut passed: Vec<Passed> = Vec::new();
    for (caller, item) in declarations.items.iter().enumerate() {
        if item.params.is_empty() {
            continue;
        }
        let node = item.item.node();
        let end = node.to_u32() + u32::try_from(tree.subtree_len(node)).expect("node count");
        for call in node.until(NodeIdx::new(end)) {
            let Some(call) = ast::CallExpr::cast(tree, call) else {
                continue;
            };
            let callee = call.callee(tree).map(|callee| source.head(callee.node()));
            let Some(Named::Function(callee)) =
                callee.and_then(|name| declarations.names.get(name))
            else {
                continue;
            };
            let args: Vec<ast::Type> = call
                .type_args(tree)
                .map(|list| list.args(tree).collect())
                .unwrap_or_default();
            if args.len() != declarations.items[callee.index()].params.len() {
                continue;
            }
            for (position, arg) in args.iter().enumerate() {
                let arg = arg.node();
                let end = arg.to_u32() + u32::try_from(tree.subtree_len(arg)).expect("node count");
                for inner in arg.until(NodeIdx::new(end)) {
                    if tree.kind(inner) != NodeKind::TypeRef {
                        continue;
                    }
                    let name = source.head(inner);
                    let Some(param) = item.params.iter().position(|&param| param == name) else {
                        continue;
                    };
                    passed.push(Passed {
                        from: first[caller] + param,
                        to: (first[callee.index()] + position) as u32,
                        grows: (inner != arg || tree.subtree_len(arg) > 1).then_some(arg),
                        call: call.node(),
                    });
                }
            }
        }
    }
    let rows = Rows::new(count, || passed.iter().map(|pass| (pass.from, pass.to)));
    let components = Components::new(&rows, |to| to as usize);
    let mut unbounded = HashSet::default();
    for pass in &passed {
        let Some(arg) = pass.grows else {
            continue;
        };
        if components.of[pass.from] != components.of[pass.to as usize] {
            continue;
        }
        if unbounded.insert(pass.call) {
            let message = format!(
                "type argument `{}` grows with every call around this cycle, so the calls have no \
                 last instance",
                source.text(arg)
            );
            source.error(arg, codes::POLYMORPHIC_RECURSION, message, None);
        }
    }
    unbounded
}
