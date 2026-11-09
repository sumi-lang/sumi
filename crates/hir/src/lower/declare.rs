//! The items of a file before any body: type declarations with their fields, function headers with
//! their parameters and result, and the instances of the generic ones as they are named.

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::hash_map::Entry;
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_graph::{DeclId, FieldName, FunctionId, GraphBuilder, Ty};
use sumi_lexer::SyntaxKind;
use sumi_syntax::{
    NodeIdx, NodeKind,
    ast::{self, AstNode, View},
};
use sumi_text::TextRange;

use super::body::GenericCall;
use super::source::{NameMap, Params, Source, TypeItem};
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
    pub fn declared(self) -> Option<(Ty, NodeIdx)> {
        match self {
            Self::Declared(ty, node) => Some((ty, node)),
            Self::Omitted(node) => Some((Ty::UNIT, node)),
            Self::None | Self::Inferred => None,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Parameter<'s> {
    pub node: NodeIdx,
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
    /// By function, its parameters as declared, whole list or not.
    pub parameters: Vec<Vec<Parameter<'s>>>,
    /// By function item, which its ID as a function indexes.
    pub(super) items: Vec<FnItem<'s>>,
    instances: HashMap<(FunctionId, Rc<[Ty]>), FunctionId, FxBuildHasher>,
    /// The calls no instance's body makes: each would be at a type that grows without end.
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

/// The order the function items' bodies are built in: grouped by the inferred results each reads,
/// a group after every group it reads. Items that read none keep their own order.
pub(crate) struct Order {
    groups: Components,
    /// By item, the members of its group whose bodies call it.
    callers: Rows,
}

impl Order {
    /// A call reads its callee's result by name: one a local shadows only groups more than it must.
    pub fn new(source: &Source<'_>, declarations: &Declarations<'_>) -> Self {
        let tree = source.tree;
        let items = &declarations.items;
        let inferred = |function: FunctionId| {
            matches!(
                declarations.headers[function.index()].result,
                HeaderResult::Inferred
            )
        };
        let mut reads: Vec<(usize, u32)> = Vec::new();
        if (0..items.len()).any(|item| inferred(FunctionId::new(item))) {
            for (caller, item) in items.iter().enumerate() {
                for call in under(source, item.item.node()) {
                    let Some(call) = ast::CallExpr::cast(tree, call) else {
                        continue;
                    };
                    let callee = call.callee(tree).map(|callee| source.head(callee.node()));
                    if let Some(Named::Function(callee)) =
                        callee.and_then(|name| declarations.names.get(name))
                        && inferred(*callee)
                    {
                        reads.push((caller, callee.index() as u32));
                    }
                }
            }
        }
        let rows = Rows::new(items.len(), || reads.iter().copied());
        let groups = Components::new(&rows, |callee| callee as usize);
        let callers = Rows::new(items.len(), || {
            reads.iter().filter_map(|&(caller, callee)| {
                (groups.of[caller] == groups.of[callee as usize])
                    .then_some((callee as usize, caller as u32))
            })
        });
        Self { groups, callers }
    }

    pub fn groups(&self) -> usize {
        self.groups.count()
    }

    pub fn members(&self, group: usize) -> &[u32] {
        self.groups.members(group)
    }

    pub fn group(&self, item: FunctionId) -> u32 {
        self.groups.of[item.index()]
    }

    pub fn callers(&self, item: usize) -> &[u32] {
        self.callers.get(item)
    }

    /// Whether a member of `group` reads the inferred result of one, itself or another.
    pub fn is_recursive(&self, group: usize) -> bool {
        self.members(group)
            .iter()
            .any(|&member| !self.callers(member as usize).is_empty())
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
    source.params = Params::new(first_param, source.decls.len() - first_param.index());

    source.type_items = type_scopes
        .iter()
        .map(|scope| TypeItem {
            params: scope.iter().map(|&(name, _)| name).collect(),
            field_types: Vec::new(),
        })
        .collect();
    // Per type item and field, its type as written where that resolved: one without a type holds
    // nothing and names no instance.
    let mut resolved: Vec<Vec<Option<ast::Type>>> = Vec::with_capacity(type_items.len());
    for (index, (item, scope)) in type_items.iter().zip(&type_scopes).enumerate() {
        source.scope.clone_from(scope);
        let mut fields: Vec<(&'s str, NodeIdx)> = Vec::new();
        let mut field_types: Vec<(FieldName, Option<Ty>)> = Vec::new();
        let mut written: Vec<Option<ast::Type>> = Vec::new();
        let mut typed: Vec<Option<ast::Type>> = Vec::new();
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
                typed.push(annotation.filter(|_| ty.is_some()));
            }
        }
        source.type_items[index].field_types = written;
        let args = scope.iter().map(|&(_, ty)| ty).collect();
        source.define(DeclId::new(index), fields, field_types, args);
        resolved.push(typed);
    }
    source.scope.clear();
    drop_recursive_fields(source, &resolved);
    drop_growing_fields(source, &resolved);
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
    // Most functions take no type parameter, and share the one list of none.
    let no_args: Rc<[Ty]> = Rc::from([]);
    for (item, scope) in fn_items.iter().zip(fn_scopes) {
        let name = source.name(item.name(tree));
        let args: Rc<[Ty]> = if scope.is_empty() {
            no_args.clone()
        } else {
            scope.iter().map(|&(_, ty)| ty).collect()
        };
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

/// The nodes of the syntax under `root`, itself first.
fn under(source: &Source<'_>, root: NodeIdx) -> impl Iterator<Item = NodeIdx> + use<> {
    let len = u32::try_from(source.tree.subtree_len(root)).expect("node count fits u32");
    root.until(NodeIdx::new(root.to_u32() + len))
}

/// What a value of the type `ty` holds: the type items into `items`, and into `own` the positions
/// in `params`, each through every type argument the item it is passed to holds.
fn held(
    source: &Source<'_>,
    ty: ast::Type,
    params: &[&str],
    holds: &[Vec<bool>],
    items: &mut Vec<DeclId>,
    own: &mut Vec<usize>,
) {
    let tree = source.tree;
    // A union nests to the left as deep as it is long; only a type argument is entered.
    let mut rest = Some(ty);
    while let Some(ty) = rest.take() {
        let named = match ty {
            ast::Type::TypeRef(named) => Some(named),
            ast::Type::UnionType(union) => {
                rest = union.lhs(tree);
                union.rhs(tree)
            }
        };
        let Some(named) = named else { continue };
        let name = source.head(named.node());
        if let Some(position) = params.iter().position(|&param| param == name) {
            own.push(position);
            continue;
        }
        let Some(&Some(item)) = source.type_names.get(name) else {
            continue;
        };
        items.push(item);
        let args = named
            .type_args(tree)
            .into_iter()
            .flat_map(|list| list.args(tree));
        for (position, arg) in args.enumerate() {
            if holds[item.index()].get(position) == Some(&true) {
                held(source, arg, params, holds, items, own);
            }
        }
    }
}

/// A type holding its own values through fields never finishes: each such field loses its type in
/// every instance, so the table the graph takes is finite in depth.
fn drop_recursive_fields(source: &mut Source<'_>, resolved: &[Vec<Option<ast::Type>>]) {
    let params = |item: usize| source.type_items[item].params.clone();
    // Per type item and parameter, whether a value of the item holds one of the parameter.
    let mut holds: Vec<Vec<bool>> = (0..resolved.len())
        .map(|item| vec![false; params(item).len()])
        .collect();
    let mut grew = true;
    while std::mem::take(&mut grew) {
        for (item, fields) in resolved.iter().enumerate() {
            let (mut items, mut own) = (Vec::new(), Vec::new());
            for &field in fields.iter().flatten() {
                held(source, field, &params(item), &holds, &mut items, &mut own);
            }
            for position in own {
                grew |= !std::mem::replace(&mut holds[item][position], true);
            }
        }
    }
    // Per type item and field, the type items a value of the field holds.
    let mentions: Vec<Vec<Vec<DeclId>>> = resolved
        .iter()
        .enumerate()
        .map(|(item, fields)| {
            let held_by = |field: &Option<ast::Type>| {
                let mut items = Vec::new();
                if let Some(field) = *field {
                    held(
                        source,
                        field,
                        &params(item),
                        &holds,
                        &mut items,
                        &mut Vec::new(),
                    );
                }
                items
            };
            fields.iter().map(held_by).collect()
        })
        .collect();
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
        source.drop_field_type(decl, field);
    }
}

/// A type parameter passed on in a type argument: to parameter `to` from parameter `from`, both
/// counted over every item's, with the argument where it is passed inside a larger type.
struct Passed {
    from: usize,
    to: usize,
    grows: Option<NodeIdx>,
}

/// Each parameter of `params` a type argument of `list` names: its position in `params`, the
/// argument's position, and the argument where it is more than the parameter.
fn passed_on(
    source: &Source<'_>,
    list: ast::TypeArgList,
    params: &[&str],
    mut pass: impl FnMut(usize, usize, Option<NodeIdx>),
) {
    let tree = source.tree;
    for (position, arg) in list.args(tree).enumerate() {
        let arg = arg.node();
        for inner in under(source, arg) {
            if tree.kind(inner) != NodeKind::TypeRef {
                continue;
            }
            let name = source.head(inner);
            if let Some(param) = params.iter().position(|&param| param == name) {
                let grows = inner != arg || tree.subtree_len(arg) > 1;
                pass(param, position, grows.then_some(arg));
            }
        }
    }
}

/// The passes with no last instance, by index: around a cycle that passes a parameter on inside a
/// larger type even once, the type grows with every turn.
fn growing(count: usize, passed: &[Passed]) -> impl Iterator<Item = (usize, NodeIdx)> + '_ {
    let rows = Rows::new(count, || {
        passed.iter().map(|pass| (pass.from, pass.to as u32))
    });
    let components = Components::new(&rows, |to| to as usize);
    passed.iter().enumerate().filter_map(move |(index, pass)| {
        let arg = pass.grows?;
        (components.of[pass.from] == components.of[pass.to]).then_some((index, arg))
    })
}

/// Per item, the count of type parameters of the items before it.
fn param_offsets(counts: impl Iterator<Item = usize>) -> (Vec<usize>, usize) {
    let mut total = 0;
    let offsets = counts
        .map(|count| {
            total += count;
            total - count
        })
        .collect();
    (offsets, total)
}

/// A field whose type names an instance that grows around a cycle of type items has no last
/// instance to settle, whether or not a value holds it, so it loses its type like a recursive one.
fn drop_growing_fields(source: &mut Source<'_>, resolved: &[Vec<Option<ast::Type>>]) {
    let tree = source.tree;
    let (first, count) = param_offsets(source.type_items.iter().map(|item| item.params.len()));
    let mut passed: Vec<Passed> = Vec::new();
    let mut sites: Vec<(DeclId, usize)> = Vec::new();
    for (item, fields) in resolved.iter().enumerate() {
        let params = &source.type_items[item].params;
        if params.is_empty() {
            continue;
        }
        for (field, annotation) in fields.iter().enumerate() {
            let typed = annotation.filter(|_| source.has_field_type(DeclId::new(item), field));
            let Some(annotation) = typed else { continue };
            for named in under(source, annotation.node()) {
                let Some(named) = ast::TypeRef::cast(tree, named) else {
                    continue;
                };
                let name = source.head(named.node());
                let applied = source.type_names.get(name).copied().flatten();
                let (Some(applied), false) = (applied, params.contains(&name)) else {
                    continue;
                };
                let Some(list) = named.type_args(tree) else {
                    continue;
                };
                passed_on(source, list, params, |param, position, grows| {
                    passed.push(Passed {
                        from: first[item] + param,
                        to: first[applied.index()] + position,
                        grows,
                    });
                    sites.push((DeclId::new(item), field));
                });
            }
        }
    }
    let mut reported: HashSet<NodeIdx, FxBuildHasher> = HashSet::default();
    for (index, arg) in growing(count, &passed) {
        let (decl, field) = sites[index];
        if reported.insert(arg) {
            let message = format!(
                "type argument `{}` grows with every type around this cycle, so the types have no \
                 last instance",
                source.text(arg)
            );
            source.error(arg, codes::POLYMORPHIC_RECURSION, message, None);
        }
        source.drop_field_type(decl, field);
    }
}

/// Marks the calls that would have no last instance: each passes a type parameter of its function
/// on inside a larger type, around a cycle of calls. `calls` are those every generic function's
/// own body makes, so an instance's body makes none of the ones marked.
pub(super) fn unbounded_calls(
    source: &mut Source<'_>,
    declarations: &mut Declarations<'_>,
    calls: &[GenericCall],
) {
    let (first, count) = param_offsets(declarations.items.iter().map(|item| item.params.len()));
    let mut passed: Vec<Passed> = Vec::new();
    let mut sites: Vec<(&GenericCall, usize)> = Vec::new();
    for call in calls {
        let params = &declarations.type_args[call.caller.index()];
        for (position, &arg) in call.args.iter().enumerate() {
            for (param, &ty) in params.iter().enumerate() {
                let decl = ty.as_decl().expect("a type parameter is a declared type");
                if !source.mentions(arg, decl) {
                    continue;
                }
                passed.push(Passed {
                    from: first[call.caller.index()] + param,
                    to: first[call.callee.index()] + position,
                    grows: (arg != ty).then_some(call.at),
                });
                sites.push((call, position));
            }
        }
    }
    for (index, _) in growing(count, &passed) {
        let (call, position) = sites[index];
        if declarations.unbounded.insert(call.call) {
            let message = format!(
                "type argument `{}` grows with every call around this cycle, so the calls have no \
                 last instance",
                source.show(call.args[position])
            );
            let written = call
                .list
                .and_then(|list| list.args(source.tree).nth(position));
            let at = written.map_or(call.at, |arg| arg.node());
            source.error(at, codes::POLYMORPHIC_RECURSION, message, None);
        }
    }
}
