//! The node vocabulary and the typed views over the tree, from one `grammar!` declaration. Single
//! fields take slots in declaration order, which the parser's `field` calls must match.

use crate::index::NodeIdx;
use crate::tree::SyntaxTree;

pub trait AstNode: Copy {
    fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self>;

    fn node(self) -> NodeIdx;
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

macro_rules! grammar {
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*]) => {
        impl $name {
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

    enum Stmt { LetStmt, AssignStmt, DiscardStmt, ReturnStmt, Expr }

    /// `'let' 'mut'? Name (':' TypeRef)? '=' initializer:Expr`.
    struct LetStmt { name: Name, type_ref: Option<TypeRef>, initializer: Expr }

    struct AssignStmt { target: Expr, value: Expr }

    struct DiscardStmt { value: Expr }

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

    enum ElseBranch { IfExpr, Block }

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
