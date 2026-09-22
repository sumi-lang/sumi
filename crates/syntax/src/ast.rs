//! The node vocabulary and the typed views over the tree, from one `grammar!` declaration. Single
//! fields take slots in declaration order, which the parser's `field` calls must match; `tokens`
//! lists what a rule holds itself, a named one read as a value.

use std::fmt::{self, Debug};
use std::hash::Hash;

use sumi_lexer::LexedFile;

use crate::grammar::{BinaryOp, Literal, PrefixOp, SyntaxKind, TokenField};
use crate::index::NodeIdx;
use crate::tree::SyntaxTree;

pub trait AstNode: Copy {
    fn node(self) -> NodeIdx;
}

/// A view of a node as the tree records it, whatever its errors.
pub trait View: AstNode {
    /// The same node with every required child and token in hand.
    type Clean: AstNode;

    fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self>;

    /// `None` for a node with an error, which may lack a required child or token.
    fn clean(self, tree: &SyntaxTree, lexed: &LexedFile) -> Option<Self::Clean>;
}

/// A kind with fields; its clean view is [`Clean`] over it.
pub trait Fields: View<Clean = Clean<Self>> {
    /// The required children, then the named tokens, in declaration order.
    type Required: Copy + Debug + Eq + Hash;

    fn required(self, tree: &SyntaxTree, lexed: &LexedFile) -> Option<Self::Required>;
}

/// A node without an error, holding every child and token its kind requires.
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
    fn node(self) -> NodeIdx {
        self.view.node()
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

/// A token a rule holds itself.
#[derive(Clone, Copy, Debug)]
pub enum TokenRule {
    /// A token of kind `first`, with `glued` joint after it when given.
    Kind {
        first: SyntaxKind,
        glued: Option<SyntaxKind>,
        optional: bool,
    },
    /// Whether the node holds `kind`, read under `name`.
    Flag {
        name: &'static str,
        kind: SyntaxKind,
    },
    /// A value read under `name`, one of `variants`.
    Field {
        name: &'static str,
        variants: usize,
        variant: fn(usize) -> String,
        /// Whether a value is read at a token of the first kind, and spans the glued one.
        reads: fn(SyntaxKind, Option<SyntaxKind>) -> Option<bool>,
        /// Whether `node` reads the variant at the index; `false` on a node of another kind.
        present: fn(&SyntaxTree, &LexedFile, NodeIdx, usize) -> bool,
    },
}

impl fmt::Display for TokenRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Kind { first, glued, .. } => match (first.text(), glued.map(SyntaxKind::text)) {
                (Some(first), None) => write!(f, "'{first}'"),
                (Some(first), Some(Some(glued))) => write!(f, "'{first}{glued}'"),
                (_, None) => write!(f, "{first:?}"),
                (_, Some(_)) => write!(f, "{first:?} {glued:?}"),
            },
            Self::Flag { name, .. } | Self::Field { name, .. } => f.write_str(name),
        }
    }
}

fn read<T: TokenField>(tree: &SyntaxTree, lexed: &LexedFile, node: NodeIdx) -> Option<T> {
    tree.own_pairs(node, lexed)
        .find_map(|(first, glued)| T::read(first, glued))
        .map(|(value, _)| value)
}

macro_rules! count {
    () => { 0u8 };
    (() $($rest:tt)*) => { 1u8 + count!($($rest)*) };
}

/// `@fields` and `@tokens` carry the slots taken, the child and token tables, the required
/// values' types and how each is read, and the tuple indices left for them.
macro_rules! grammar {
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:tt)*]
        [$($index:tt)*] [$($tokens:tt)*]) => {
        impl $name {
            pub const CHILDREN: &[Child] = &[$($child)*];
        }

        grammar!(@tokens $name [] [$($required)*] [$($by)*] [$($index)*] $($tokens)*);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:tt)*]
        [$($index:tt)*] [$($tokens:tt)*] $field:ident: Option<$ty:ident> $(, $($rest:tt)*)?) => {
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
        },] [$($required)*] [$($by)*] [$($index)*] [$($tokens)*] $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:tt)*]
        [$($index:tt)*] [$($tokens:tt)*] $field:ident: [$ty:ident] $(, $($rest:tt)*)?) => {
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
        },] [$($required)*] [$($by)*] [$($index)*] [$($tokens)*] $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:tt)*]
        [$index:tt $($next:tt)*] [$($tokens:tt)*] $field:ident: $ty:ident $(, $($rest:tt)*)?) => {
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
        },] [$($required)* $ty,] [$($by)* (child $field)] [$($next)*] [$($tokens)*]
            $($($rest)*)?);
    };
    (@fields $name:ident [$($slot:tt)*] [$($child:tt)*] [$($required:tt)*] [$($by:tt)*] []
        [$($tokens:tt)*] $field:ident: $ty:ident $(, $($rest:tt)*)?) => {
        compile_error!(concat!(
            "`", stringify!($name), "` holds more required values than `Clean` has indices for"
        ));
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] [$($index:tt)*]) => {
        impl $name {
            pub const TOKENS: &[TokenRule] = &[$($token)*];
        }

        impl Fields for $name {
            type Required = ($($required)*);

            fn required(self, tree: &SyntaxTree, lexed: &LexedFile) -> Option<Self::Required> {
                let _ = (tree, lexed);
                Some(($(grammar!(@read self tree lexed $by),)*))
            }
        }
    };
    (@read $this:ident $tree:ident $lexed:ident (child $field:ident)) => {
        $this.$field($tree)?
    };
    (@read $this:ident $tree:ident $lexed:ident (flag $field:ident)) => {
        $this.$field($tree, $lexed)
    };
    (@read $this:ident $tree:ident $lexed:ident (field $field:ident)) => {
        $this.$field($tree, $lexed)?
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] [$($index:tt)*]
        [$first:ident, $glued:ident] $(, $($rest:tt)*)?) => {
        grammar!(@tokens $name [$($token)* TokenRule::Kind {
            first: SyntaxKind::$first,
            glued: Some(SyntaxKind::$glued),
            optional: false,
        },] [$($required)*] [$($by)*] [$($index)*] $($($rest)*)?);
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] [$($index:tt)*]
        [$first:ident, $glued:ident]? $(, $($rest:tt)*)?) => {
        grammar!(@tokens $name [$($token)* TokenRule::Kind {
            first: SyntaxKind::$first,
            glued: Some(SyntaxKind::$glued),
            optional: true,
        },] [$($required)*] [$($by)*] [$($index)*] $($($rest)*)?);
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] [$($index:tt)*]
        $kind:ident? $(, $($rest:tt)*)?) => {
        grammar!(@tokens $name [$($token)* TokenRule::Kind {
            first: SyntaxKind::$kind,
            glued: None,
            optional: true,
        },] [$($required)*] [$($by)*] [$($index)*] $($($rest)*)?);
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] [$($index:tt)*]
        $kind:ident $(, $($rest:tt)*)?) => {
        grammar!(@tokens $name [$($token)* TokenRule::Kind {
            first: SyntaxKind::$kind,
            glued: None,
            optional: false,
        },] [$($required)*] [$($by)*] [$($index)*] $($($rest)*)?);
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] [$index:tt $($next:tt)*]
        $field:ident: $kind:ident? $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("Whether the node holds `", stringify!($kind), "`.")]
            pub fn $field(self, tree: &SyntaxTree, lexed: &LexedFile) -> bool {
                tree.holds(self.0, lexed, SyntaxKind::$kind, None)
            }
        }

        impl Clean<$name> {
            #[doc = concat!("Whether the node holds `", stringify!($kind), "`.")]
            pub fn $field(self) -> bool {
                self.required.$index
            }
        }
        grammar!(@tokens $name [$($token)* TokenRule::Flag {
            name: stringify!($field),
            kind: SyntaxKind::$kind,
        },] [$($required)* bool,] [$($by)* (flag $field)] [$($next)*] $($($rest)*)?);
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] [$index:tt $($next:tt)*]
        $field:ident: $ty:ident $(, $($rest:tt)*)?) => {
        impl $name {
            #[doc = concat!("The `", stringify!($field), "` the node holds, a `", stringify!($ty), "`, present on a node without an error.")]
            pub fn $field(self, tree: &SyntaxTree, lexed: &LexedFile) -> Option<$ty> {
                read(tree, lexed, self.0)
            }
        }

        impl Clean<$name> {
            #[doc = concat!("The `", stringify!($field), "` the node holds, a `", stringify!($ty), "`.")]
            pub fn $field(self) -> $ty {
                self.required.$index
            }
        }
        grammar!(@tokens $name [$($token)* TokenRule::Field {
            name: stringify!($field),
            variants: <$ty as TokenField>::ALL.len(),
            variant: |index| <$ty as TokenField>::ALL[index].to_string(),
            reads: |first, glued| <$ty as TokenField>::read(first, glued).map(|(_, spans)| spans),
            present: |tree, lexed, node, index| {
                $name::cast(tree, node).is_some_and(|view| {
                    view.$field(tree, lexed) == Some(<$ty as TokenField>::ALL[index])
                })
            },
        },] [$($required)* $ty,] [$($by)* (field $field)] [$($next)*] $($($rest)*)?);
    };
    (@tokens $name:ident [$($token:tt)*] [$($required:tt)*] [$($by:tt)*] []
        $field:ident: $($rest:tt)*) => {
        compile_error!(concat!(
            "`", stringify!($name), "` holds more required values than `Clean` has indices for"
        ));
    };
    (@nodes [$($variant:tt)*] [$($kind:ident)*]
        $(#[$doc:meta])* struct $name:ident { $($fields:tt)* } tokens { $($tokens:tt)* }
        $($rest:tt)*) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(NodeIdx);

        impl AstNode for $name {
            fn node(self) -> NodeIdx {
                self.0
            }
        }

        impl View for $name {
            type Clean = Clean<Self>;

            fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
                (tree.kind(node) == NodeKind::$name).then_some(Self(node))
            }

            fn clean(self, tree: &SyntaxTree, lexed: &LexedFile) -> Option<Clean<Self>> {
                if tree.has_error(self.0) {
                    return None;
                }
                Some(Clean {
                    view: self,
                    required: self.required(tree, lexed)?,
                })
            }
        }

        grammar!(@fields $name [] [] [] [] [0 1 2 3 4 5 6 7] [$($tokens)*] $($fields)*);
        grammar!(@nodes [$($variant)* $(#[$doc])* $name,] [$($kind)* $name] $($rest)*);
    };
    (@nodes [$($variant:tt)*] [$($kind:ident)*]
        $(#[$doc:meta])* struct $name:ident { $($fields:tt)* } $($rest:tt)*) => {
        grammar!(@nodes [$($variant)*] [$($kind)*]
            $(#[$doc])* struct $name { $($fields)* } tokens {} $($rest)*);
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
            $($member(<$member as View>::Clean),)*
        }

        impl AstNode for $name {
            fn node(self) -> NodeIdx {
                match self {
                    $(Self::$member(inner) => inner.node(),)*
                }
            }
        }

        impl View for $name {
            type Clean = $clean;

            fn cast(tree: &SyntaxTree, node: NodeIdx) -> Option<Self> {
                None$(.or_else(|| $member::cast(tree, node).map(Self::$member)))*
            }

            fn clean(self, tree: &SyntaxTree, lexed: &LexedFile) -> Option<$clean> {
                match self {
                    $(Self::$member(inner) => inner.clean(tree, lexed).map($clean::$member),)*
                }
            }
        }

        impl AstNode for $clean {
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

            pub fn tokens(self) -> &'static [TokenRule] {
                match self {
                    $(Self::$kind => $kind::TOKENS,)*
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
    tokens { FnKw, [Minus, Gt]?, Eq? }

    /// `'(' (Param (',' Param)* ','?)? ')'`.
    struct ParamList { params: [Param] }
    tokens { LParen, Comma?, RParen }

    /// `Name (':' TypeRef)?`; only a closure's parameter may lack the type.
    struct Param { name: Name, type_ref: Option<TypeRef> }
    tokens { Colon? }

    /// A declaring occurrence of a name, `Ident`; a use is a `NameRef`.
    struct Name {}
    tokens { Ident }

    /// `Ident`.
    struct TypeRef {}
    tokens { Ident }

    struct Block { stmts: [Stmt] }
    tokens { LBrace, RBrace }

    enum Stmt as CleanStmt { LetStmt, AssignStmt, DiscardStmt, ReturnStmt, Expr }

    /// `'let' 'mut'? Name (':' TypeRef)? '=' initializer:Expr`.
    struct LetStmt { name: Name, type_ref: Option<TypeRef>, initializer: Expr }
    tokens { LetKw, mutable: MutKw?, Colon?, Eq }

    struct AssignStmt { target: Expr, value: Expr }
    tokens { Eq }

    struct DiscardStmt { value: Expr }
    tokens { Underscore, Eq }

    struct ReturnStmt { value: Option<Expr> }
    tokens { ReturnKw }

    enum Expr as CleanExpr {
        NameRef,
        LiteralExpr,
        PrefixExpr,
        BinaryExpr,
        ParenExpr,
        CallExpr,
        IfExpr,
        ForExpr,
        ClosureExpr,
        Block,
    }

    /// A use of a name, `Ident`.
    struct NameRef {}
    tokens { Ident }

    /// `IntLiteral | StringLiteral | 'true' | 'false'`.
    struct LiteralExpr {}
    tokens { value: Literal }

    struct PrefixExpr { operand: Expr }
    tokens { op: PrefixOp }

    struct BinaryExpr { lhs: Expr, rhs: Expr }
    tokens { op: BinaryOp }

    struct ParenExpr { inner: Expr }
    tokens { LParen, RParen }

    struct CallExpr { callee: Expr, arg_list: ArgList }

    /// `'(' (Expr (',' Expr)* ','?)? ')'`.
    struct ArgList { args: [Expr] }
    tokens { LParen, Comma?, RParen }

    /// `'if' condition:Expr then_branch:Block ('else' else_branch:ElseBranch)?`.
    struct IfExpr { condition: Expr, then_branch: Block, else_branch: Option<ElseBranch> }
    tokens { IfKw, ElseKw? }

    struct ForExpr { name: Name, start: Expr, end: Expr, body: Block }
    tokens { ForKw, InKw, [Dot, Dot] }

    enum ElseBranch as CleanElseBranch { IfExpr, Block }

    /// `'fn' ParamList ('->' ret:TypeRef)? '='? body:Expr`.
    struct ClosureExpr { param_list: ParamList, ret: Option<TypeRef>, body: Expr }
    tokens { FnKw, [Minus, Gt]?, Eq? }
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

    #[test]
    fn tokens_follow_the_declaration() {
        let [let_kw, mutable, colon, eq] = LetStmt::TOKENS else {
            panic!("four tokens")
        };
        assert!(matches!(
            let_kw,
            TokenRule::Kind {
                first: SyntaxKind::LetKw,
                glued: None,
                optional: false
            }
        ));
        assert!(matches!(
            mutable,
            TokenRule::Flag {
                name: "mutable",
                kind: SyntaxKind::MutKw
            }
        ));
        assert!(matches!(
            colon,
            TokenRule::Kind {
                first: SyntaxKind::Colon,
                optional: true,
                ..
            }
        ));
        assert_eq!(eq.to_string(), "'='");
        let [arrow] = &FnItem::TOKENS[1..2] else {
            panic!("an arrow")
        };
        assert!(matches!(
            arrow,
            TokenRule::Kind {
                first: SyntaxKind::Minus,
                glued: Some(SyntaxKind::Gt),
                optional: true
            }
        ));
        assert_eq!(arrow.to_string(), "'->'");
        let [op] = BinaryExpr::TOKENS else {
            panic!("one token")
        };
        let TokenRule::Field {
            name,
            variants,
            variant,
            reads,
            ..
        } = *op
        else {
            panic!("a field")
        };
        assert_eq!((name, variants), ("op", BinaryOp::ALL.len()));
        assert_eq!(variant(0), "`||`");
        assert_eq!(reads(SyntaxKind::Lt, Some(SyntaxKind::Eq)), Some(true));
        assert_eq!(reads(SyntaxKind::Lt, Some(SyntaxKind::Minus)), Some(false));
        assert_eq!(reads(SyntaxKind::Ident, None), None);
        assert!(CallExpr::TOKENS.is_empty());
    }
}
