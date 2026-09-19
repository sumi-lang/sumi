//! The node vocabulary and the typed views over the tree, from one
//! declaration: a struct per node kind, with an accessor for each child
//! the parser records, and an enum per category of kinds.
//!
//! A view is a [`NodeIdx`] with a type; every accessor takes the tree,
//! since a node carries no pointer back to it. Accessors answer `Option`
//! or an iterator whatever the grammar requires, because a parsed tree is
//! error-tolerant: a node whose [`SyntaxTree::has_error`] bit is set may
//! lack any child. A single-valued accessor reads the grammatical role the
//! parser recorded, by the slot the field's position in its declaration
//! gives it, which the parser's `field` calls must match. Missing children
//! and untyped error nodes answer `None`; no accessor reconstructs field
//! assignments from child types. The scan allocates nothing. A many-valued
//! accessor yields the children in source order, which is how the tree
//! stores them.

use crate::index::NodeIdx;
use crate::tree::SyntaxTree;

/// A typed view over one node: what every struct and enum here implements.
pub trait AstNode: Copy {
    /// The view over `node`, if it is of a fitting kind.
    fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self>;

    /// The node the view is over.
    fn node(self) -> NodeIdx;
}

/// One child a node kind's view declares, as the grammar's account of
/// itself: what a coverage check must see present, and absent where the
/// rule allows.
#[derive(Clone, Copy, Debug)]
pub struct Child {
    /// The accessor's name.
    pub name: &'static str,
    /// The field slot of a single child; `None` for a repeated one.
    pub slot: Option<u8>,
    /// Whether a node without an error may lack the child.
    pub optional: bool,
    /// Whether `node` has the child, as the accessor answers it: a slot
    /// holding a node of another kind than the view declares counts as
    /// lacking it. `false` for a node of another kind than the declaring
    /// one.
    pub present: fn(&SyntaxTree, NodeIdx) -> bool,
}

/// The number of `()` tokens, as a `u8`: the slot of a field is how many
/// single fields precede it.
macro_rules! count {
    () => { 0u8 };
    (() $($rest:tt)*) => { 1u8 + count!($($rest)*) };
}

/// Declares the grammar: `struct Kind { field: View, … }` for each node
/// kind, in the order [`NodeKind::ALL`] lists, and `enum Category { Kind,
/// … }` for each category of kinds, where a member may be a category
/// itself. A field is `name: View` when a node without an error always
/// has it, `name: Option<View>` when the rule leaves it optional, and
/// `name: [View]` for the one repeated child a kind may have; single
/// fields take slots in declaration order. The macro expands to
/// [`NodeKind`], with `Error` last, a view per declaration, and each
/// struct's [`CHILDREN`](SourceFile::CHILDREN).
macro_rules! grammar {
    // The last field is declared: the children table closes.
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*]) => {
        impl $name {
            /// The children the view declares, in declaration order.
            pub const CHILDREN: &[Child] = &[$($child)*];
        }
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*]
        $field:ident: Option<$ty:ident> $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("The `", stringify!($field), "` child, a `", stringify!($ty), "`, optional.")]
            pub fn $field(self, tree: &SyntaxTree) -> Option<$ty> {
                tree.child_in_field(self.0, count!($($slot)*))
                    .and_then(|node| $ty::cast(tree, node))
            }
        }
        grammar!(@fields $name [$($slot)* ()] [$($child)* Child {
            name: stringify!($field),
            slot: Some(count!($($slot)*)),
            optional: true,
            present: |tree, node| {
                $name::cast(tree, node).is_some_and(|view| view.$field(tree).is_some())
            },
        },] $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*]
        $field:ident: [$ty:ident] $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("The `", stringify!($field), "` children, each a `", stringify!($ty), "`, in source order.")]
            pub fn $field<'t>(self, tree: &'t SyntaxTree) -> impl Iterator<Item = $ty> + 't {
                tree.children(self.0)
                    .filter_map(move |child| $ty::cast(tree, child))
            }
        }
        grammar!(@fields $name [$($slot)*] [$($child)* Child {
            name: stringify!($field),
            slot: None,
            optional: true,
            present: |tree, node| {
                $name::cast(tree, node).is_some_and(|view| view.$field(tree).next().is_some())
            },
        },] $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*]
        $field:ident: $ty:ident $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("The `", stringify!($field), "` child, a `", stringify!($ty), "`, present on a node without an error.")]
            pub fn $field(self, tree: &SyntaxTree) -> Option<$ty> {
                tree.child_in_field(self.0, count!($($slot)*))
                    .and_then(|node| $ty::cast(tree, node))
            }
        }
        grammar!(@fields $name [$($slot)* ()] [$($child)* Child {
            name: stringify!($field),
            slot: Some(count!($($slot)*)),
            optional: false,
            present: |tree, node| {
                $name::cast(tree, node).is_some_and(|view| view.$field(tree).is_some())
            },
        },] $($($rest)*)?);
    };
    // One node kind: a variant for the kind, a view, and its accessors.
    (@nodes [$($variant:tt)*] [$($kind:ident)*]
        $(#[$doc:meta])* struct $name:ident { $($fields:tt)* } $($rest:tt)*) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(NodeIdx);

        impl AstNode for $name {
            fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
                (tree.kind(node) == NodeKind::$name).then_some(Self(node))
            }

            fn node(self) -> NodeIdx {
                self.0
            }
        }

        grammar!(@fields $name [] [] $($fields)*);
        grammar!(@nodes [$($variant)* $(#[$doc])* $name,] [$($kind)* $name] $($rest)*);
    };
    // One category: an enum over its members, cast by trying each in turn.
    (@nodes [$($variant:tt)*] [$($kind:ident)*]
        $(#[$doc:meta])* enum $name:ident { $($member:ident),* $(,)? } $($rest:tt)*) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum $name {
            $($member($member),)*
        }

        impl AstNode for $name {
            fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
                None$(.or_else(|| $member::cast(tree, node).map(Self::$member)))*
            }

            fn node(self) -> NodeIdx {
                match self {
                    $(Self::$member(inner) => inner.node(),)*
                }
            }
        }

        grammar!(@nodes [$($variant)*] [$($kind)*] $($rest)*);
    };
    // Every declaration is expanded: the kinds are known.
    (@nodes [$($variant:tt)*] [$($kind:ident)*]) => {
        /// The kind of a syntax tree node.
        ///
        /// A node is structure only, so this vocabulary is disjoint from
        /// [`SyntaxKind`](crate::SyntaxKind): a tree slot never holds a
        /// token kind, and a token buffer slot never holds a node kind.
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum NodeKind {
            $($variant)*
            /// Covers tokens the parser could not parse.
            Error,
        }

        impl NodeKind {
            /// Every kind, in declaration order, `Error` last.
            pub const ALL: &[Self] = &[$(Self::$kind,)* Self::Error];

            /// The children the kind's view declares; an `Error` node
            /// declares none.
            pub fn children(self) -> &'static [Child] {
                match self {
                    $(Self::$kind => $kind::CHILDREN,)*
                    Self::Error => &[],
                }
            }
        }
    };
    ($($declaration:tt)*) => {
        grammar!(@nodes [] [] $($declaration)*);
    };
}

grammar! {
    /// A source file contains function items, each beginning on a new line
    /// after the first: `FnItem*`.
    struct SourceFile { items: [FnItem] }

    /// A function item: `'fn' Name ParamList ('->' ret:TypeRef)? '='?
    /// body:Expr`. Its name begins on the same line as `fn`. The body is a
    /// block or `=` and an expression: `fn double(x: int) -> int = x * 2`.
    /// Signature components after the parameter list may begin on
    /// subsequent lines.
    struct FnItem { name: Name, param_list: ParamList, ret: Option<TypeRef>, body: Expr }

    /// `'(' (Param (',' Param)* ','?)? ')'`.
    struct ParamList { params: [Param] }

    /// A parameter: `Name (':' TypeRef)?`. An item's has a type; a
    /// closure's may leave it to be inferred.
    struct Param { name: Name, type_ref: Option<TypeRef> }

    /// A declaring occurrence of a name, `Ident`: what an item, a
    /// parameter, or a binding introduces. A use is a NameRef.
    struct Name {}

    /// A type reference, `Ident`: a name, until types grow more shapes.
    struct TypeRef {}

    /// `'{' Stmt* '}'`.
    struct Block { stmts: [Stmt] }

    /// One statement of a block; a line break ends it. Expression-statement
    /// type requirements are enforced by semantic checking, not this
    /// grammar.
    enum Stmt { LetStmt, AssignStmt, DiscardStmt, ReturnStmt, Expr }

    /// A binding statement: `'let' 'mut'? Name (':' TypeRef)? '='
    /// initializer:Expr`. Its `let`, optional `mut`, and name share one
    /// line.
    struct LetStmt { name: Name, type_ref: Option<TypeRef>, initializer: Expr }

    /// `target:Expr '=' value:Expr`.
    struct AssignStmt { target: Expr, value: Expr }

    /// `'_' '=' value:Expr`.
    struct DiscardStmt { value: Expr }

    /// `'return' value:Expr?`.
    struct ReturnStmt { value: Option<Expr> }

    enum Expr {
        NameRef,
        LiteralExpr,
        PrefixExpr,
        BinaryExpr,
        ParenExpr,
        CallExpr,
        IfExpr,
        ClosureExpr,
        Block,
    }

    /// A use of a name, `Ident`: a reference to what a Name declared.
    struct NameRef {}

    /// `IntLiteral | StringLiteral | 'true' | 'false'`.
    struct LiteralExpr {}

    /// `PrefixOperator operand:Expr`.
    struct PrefixExpr { operand: Expr }

    /// `lhs:Expr BinaryOperator rhs:Expr`.
    struct BinaryExpr { lhs: Expr, rhs: Expr }

    /// `'(' inner:Expr ')'`.
    struct ParenExpr { inner: Expr }

    /// `callee:Expr ArgList`.
    struct CallExpr { callee: Expr, arg_list: ArgList }

    /// `'(' (Expr (',' Expr)* ','?)? ')'`.
    struct ArgList { args: [Expr] }

    /// `'if' condition:Expr then_branch:Block ('else' else_branch:ElseBranch)?`.
    struct IfExpr { condition: Expr, then_branch: Block, else_branch: Option<ElseBranch> }

    /// The `else_branch` of an `IfExpr`: `IfExpr | Block`.
    enum ElseBranch { IfExpr, Block }

    /// A function without a name, as an expression: `'fn' ParamList ('->'
    /// ret:TypeRef)? '='? body:Expr`, with an item's parameter list, return
    /// type, and body forms: `fn(x) = x * 2`, or `fn(x: int) -> int { … }`.
    struct ClosureExpr { param_list: ParamList, ret: Option<TypeRef>, body: Expr }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Kinds index by discriminant, in the order `ALL` lists.
    #[test]
    fn kinds_index_by_discriminant() {
        for (index, kind) in NodeKind::ALL.iter().enumerate() {
            assert_eq!(*kind as usize, index);
        }
    }

    /// Single fields take consecutive slots from zero, and a repeated child
    /// shares its kind with no other.
    #[test]
    fn children_take_slots_in_order() {
        for kind in NodeKind::ALL {
            let slots: Vec<u8> = kind.children().iter().filter_map(|c| c.slot).collect();
            assert!(
                slots.iter().enumerate().all(|(i, &s)| s as usize == i),
                "{kind:?}"
            );
            let many = kind.children().iter().filter(|c| c.slot.is_none()).count();
            assert!(many == 0 || kind.children().len() == 1, "{kind:?}");
        }
        assert_eq!(NodeKind::FnItem.children()[2].name, "ret");
        assert_eq!(NodeKind::FnItem.children()[2].slot, Some(2));
        assert!(NodeKind::FnItem.children()[2].optional);
    }
}
