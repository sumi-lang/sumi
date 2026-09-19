//! The node vocabulary and the typed views over the tree, from one `grammar!` declaration. Single
//! fields take slots in declaration order, which the parser's `field` calls must match.

use std::fmt::Debug;
use std::hash::Hash;

use crate::index::NodeIdx;
use crate::tree::SyntaxTree;

pub trait AstNode: Copy {
    /// The same node with every required child in hand.
    type Clean: AstNode;

    fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self>;

    fn node(self) -> NodeIdx;

    /// `None` for a node with an error, which may lack a required child.
    fn clean(self, tree: &SyntaxTree) -> Option<Self::Clean>;
}

/// A kind with fields; its clean view is [`Clean`] over it.
pub trait Fields: AstNode<Clean = Clean<Self>> {
    /// The required children, in declaration order.
    type Required: Copy + Debug + Eq + Hash;

    fn required(self, tree: &SyntaxTree) -> Option<Self::Required>;
}

/// A node without an error, holding every child its kind requires.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Clean<N: Fields> {
    view: N,
    required: N::Required,
}

impl<N: Fields> Clean<N> {
    pub fn view(self) -> N {
        self.view
    }
}

impl<N: Fields> AstNode for Clean<N> {
    type Clean = Self;

    fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
        N::cast(tree, node)?.clean(tree)
    }

    fn node(self) -> NodeIdx {
        self.view.node()
    }

    fn clean(self, _: &SyntaxTree) -> Option<Self> {
        Some(self)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Child {
    /// The accessor's name.
    pub name: &'static str,
    /// The field slot of a single child; `None` for a repeated one.
    pub slot: Option<u8>,
    pub optional: bool,
    /// The accessor's answer for `node`; `false` on a node of another kind.
    pub present: fn(&SyntaxTree, NodeIdx) -> bool,
}

macro_rules! count {
    () => { 0u8 };
    (() $($rest:tt)*) => { 1u8 + count!($($rest)*) };
}

/// `@fields` carries the slots taken, the child table, the required children's types and names,
/// and the tuple indices left for them.
macro_rules! grammar {
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:ident)*]
        [$($index:tt)*]) => {
        impl $name {
            pub const CHILDREN: &[Child] = &[$($child)*];
        }

        impl Fields for $name {
            type Required = ($($required)*);

            fn required(self, _tree: &SyntaxTree) -> Option<Self::Required> {
                Some(($(self.$by(_tree)?,)*))
            }
        }
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:ident)*]
        [$($index:tt)*] $field:ident: Option<$ty:ident> $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("The `", stringify!($field), "` child, a `", stringify!($ty), "`, optional.")]
            pub fn $field(self, tree: &SyntaxTree) -> Option<$ty> {
                tree.child_in_field(self.0, count!($($slot)*))
                    .and_then(|node| $ty::cast(tree, node))
            }
        }

        impl Clean<$name> {
            #[doc = concat!("The `", stringify!($field), "` child, a `", stringify!($ty), "`, optional.")]
            pub fn $field(self, tree: &SyntaxTree) -> Option<$ty> {
                self.view.$field(tree)
            }
        }
        grammar!(@fields $name [$($slot)* ()] [$($child)* Child {
            name: stringify!($field),
            slot: Some(count!($($slot)*)),
            optional: true,
            present: |tree, node| {
                $name::cast(tree, node).is_some_and(|view| view.$field(tree).is_some())
            },
        },] [$($required)*] [$($by)*] [$($index)*] $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:ident)*]
        [$($index:tt)*] $field:ident: [$ty:ident] $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("The `", stringify!($field), "` children, each a `", stringify!($ty), "`, in source order.")]
            pub fn $field<'t>(self, tree: &'t SyntaxTree) -> impl Iterator<Item = $ty> + 't {
                tree.children(self.0)
                    .filter_map(move |child| $ty::cast(tree, child))
            }
        }

        impl Clean<$name> {
            #[doc = concat!("The `", stringify!($field), "` children, each a `", stringify!($ty), "`, in source order.")]
            pub fn $field<'t>(self, tree: &'t SyntaxTree) -> impl Iterator<Item = $ty> + 't {
                self.view.$field(tree)
            }
        }
        grammar!(@fields $name [$($slot)*] [$($child)* Child {
            name: stringify!($field),
            slot: None,
            optional: true,
            present: |tree, node| {
                $name::cast(tree, node).is_some_and(|view| view.$field(tree).next().is_some())
            },
        },] [$($required)*] [$($by)*] [$($index)*] $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:ident)*]
        [$index:tt $($next:tt)*] $field:ident: $ty:ident $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("The `", stringify!($field), "` child, a `", stringify!($ty), "`, present on a node without an error.")]
            pub fn $field(self, tree: &SyntaxTree) -> Option<$ty> {
                tree.child_in_field(self.0, count!($($slot)*))
                    .and_then(|node| $ty::cast(tree, node))
            }
        }

        impl Clean<$name> {
            #[doc = concat!("The `", stringify!($field), "` child, a `", stringify!($ty), "`.")]
            pub fn $field(self) -> $ty {
                self.required.$index
            }
        }
        grammar!(@fields $name [$($slot)* ()] [$($child)* Child {
            name: stringify!($field),
            slot: Some(count!($($slot)*)),
            optional: false,
            present: |tree, node| {
                $name::cast(tree, node).is_some_and(|view| view.$field(tree).is_some())
            },
        },] [$($required)* $ty,] [$($by)* $field] [$($next)*] $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:ident)*] []
        $field:ident: $ty:ident $(, $($rest:tt)*)?) => {
        compile_error!(concat!(
            "`", stringify!($name), "` holds more required children than `Clean` has indices for"
        ));
    };
    (@nodes [$($variant:tt)*] [$($kind:ident)*]
        $(#[$doc:meta])* struct $name:ident { $($fields:tt)* } $($rest:tt)*) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(NodeIdx);

        impl AstNode for $name {
            type Clean = Clean<Self>;

            fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
                (tree.kind(node) == NodeKind::$name).then_some(Self(node))
            }

            fn node(self) -> NodeIdx {
                self.0
            }

            fn clean(self, tree: &SyntaxTree) -> Option<Clean<Self>> {
                if tree.has_error(self.0) {
                    return None;
                }
                Some(Clean {
                    view: self,
                    required: self.required(tree)?,
                })
            }
        }

        grammar!(@fields $name [] [] [] [] [0 1 2 3 4 5 6 7] $($fields)*);
        grammar!(@nodes [$($variant)* $(#[$doc])* $name,] [$($kind)* $name] $($rest)*);
    };
    (@nodes [$($variant:tt)*] [$($kind:ident)*]
        $(#[$doc:meta])* enum $name:ident as $clean:ident { $($member:ident),* $(,)? }
        $($rest:tt)*) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum $name {
            $($member($member),)*
        }

        #[doc = concat!("[`", stringify!($name), "`] without an error.")]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum $clean {
            $($member(<$member as AstNode>::Clean),)*
        }

        impl AstNode for $name {
            type Clean = $clean;

            fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
                None$(.or_else(|| $member::cast(tree, node).map(Self::$member)))*
            }

            fn node(self) -> NodeIdx {
                match self {
                    $(Self::$member(inner) => inner.node(),)*
                }
            }

            fn clean(self, tree: &SyntaxTree) -> Option<$clean> {
                match self {
                    $(Self::$member(inner) => inner.clean(tree).map($clean::$member),)*
                }
            }
        }

        impl AstNode for $clean {
            type Clean = Self;

            fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
                $name::cast(tree, node)?.clean(tree)
            }

            fn node(self) -> NodeIdx {
                match self {
                    $(Self::$member(inner) => inner.node(),)*
                }
            }

            fn clean(self, _: &SyntaxTree) -> Option<Self> {
                Some(self)
            }
        }

        grammar!(@nodes [$($variant)*] [$($kind)*] $($rest)*);
    };
    (@nodes [$($variant:tt)*] [$($kind:ident)*]) => {
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum NodeKind {
            $($variant)*
            /// Tokens the parser could not parse.
            Error,
        }

        impl NodeKind {
            /// In discriminant order, so `ALL[kind as usize]` is `kind`.
            pub const ALL: &[Self] = &[$(Self::$kind,)* Self::Error];

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
    struct SourceFile { items: [FnItem] }

    /// `'fn' Name ParamList ('->' ret:TypeRef)? '='? body:Expr`.
    struct FnItem { name: Name, param_list: ParamList, ret: Option<TypeRef>, body: Expr }

    /// `'(' (Param (',' Param)* ','?)? ')'`.
    struct ParamList { params: [Param] }

    /// `Name (':' TypeRef)?`; only a closure's parameter may lack the type.
    struct Param { name: Name, type_ref: Option<TypeRef> }

    /// A declaring occurrence of a name, `Ident`; a use is a `NameRef`.
    struct Name {}

    /// `Ident`.
    struct TypeRef {}

    struct Block { stmts: [Stmt] }

    enum Stmt as CleanStmt { LetStmt, AssignStmt, DiscardStmt, ReturnStmt, Expr }

    /// `'let' 'mut'? Name (':' TypeRef)? '=' initializer:Expr`.
    struct LetStmt { name: Name, type_ref: Option<TypeRef>, initializer: Expr }

    struct AssignStmt { target: Expr, value: Expr }

    struct DiscardStmt { value: Expr }

    struct ReturnStmt { value: Option<Expr> }

    enum Expr as CleanExpr {
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

    /// A use of a name, `Ident`.
    struct NameRef {}

    /// `IntLiteral | StringLiteral | 'true' | 'false'`.
    struct LiteralExpr {}

    struct PrefixExpr { operand: Expr }

    struct BinaryExpr { lhs: Expr, rhs: Expr }

    struct ParenExpr { inner: Expr }

    struct CallExpr { callee: Expr, arg_list: ArgList }

    /// `'(' (Expr (',' Expr)* ','?)? ')'`.
    struct ArgList { args: [Expr] }

    /// `'if' condition:Expr then_branch:Block ('else' else_branch:ElseBranch)?`.
    struct IfExpr { condition: Expr, then_branch: Block, else_branch: Option<ElseBranch> }

    enum ElseBranch as CleanElseBranch { IfExpr, Block }

    /// `'fn' ParamList ('->' ret:TypeRef)? '='? body:Expr`.
    struct ClosureExpr { param_list: ParamList, ret: Option<TypeRef>, body: Expr }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kinds_index_by_discriminant() {
        for (index, kind) in NodeKind::ALL.iter().enumerate() {
            assert_eq!(*kind as usize, index);
        }
    }

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
