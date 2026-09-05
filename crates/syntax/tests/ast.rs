//! The typed views generated from `sumi.grammar`: accessors over a parsed
//! tree, on clean and on erroneous syntax.

use sumi_lexer::{LexedFile, lex};
use sumi_syntax::ast::{AstNode, Block, ElseBranch, Expr, SourceFile, Stmt};
use sumi_syntax::{Parse, ParserInput, SyntaxTree, parse};

struct Parsed {
    source: &'static str,
    lexed: LexedFile,
    parse: Parse,
}

impl Parsed {
    fn new(source: &'static str) -> Self {
        let lexed = lex(source).expect("test sources fit in u32");
        let parse = parse(&ParserInput::new(&lexed));
        Self {
            source,
            lexed,
            parse,
        }
    }

    fn tree(&self) -> &SyntaxTree {
        self.parse.tree()
    }

    /// The source text of a view.
    fn text(&self, view: impl AstNode) -> &str {
        self.tree()
            .byte_range(view.node(), &self.lexed)
            .text(self.source)
    }

    /// The one item of the file.
    fn item(&self) -> sumi_syntax::ast::FnItem {
        let tree = self.tree();
        let file = SourceFile::cast(tree, tree.root()).expect("the root is a source file");
        let mut items = file.items(tree);
        let item = items.next().expect("one item");
        assert!(items.next().is_none(), "exactly one item");
        item
    }
}

/// The block a body is, on an item whose body is not an expression.
fn block(body: Option<Expr>) -> Block {
    match body {
        Some(Expr::Block(block)) => block,
        other => panic!("a block body, not {other:?}"),
    }
}

#[test]
fn expression_bodies_and_closures_have_views() {
    let parsed = Parsed::new("fn twice(x: Int) -> Int = apply(fn(y: Int) -> Int = y * 2, x)\n");
    let tree = parsed.tree();
    let item = parsed.item();
    assert!(!tree.has_error(item.node()));
    assert_eq!(parsed.text(item.ret(tree).expect("a return type")), "Int");
    let Some(Expr::CallExpr(call)) = item.body(tree) else {
        panic!("the body is a call")
    };
    let mut args = call.arg_list(tree).expect("arguments").args(tree);
    let Some(Expr::ClosureExpr(closure)) = args.next() else {
        panic!("the first argument is a closure")
    };
    let params: Vec<_> = closure
        .param_list(tree)
        .expect("parameters")
        .params(tree)
        .map(|param| parsed.text(param.name(tree).expect("a name")))
        .collect();
    assert_eq!(params, ["y"]);
    assert_eq!(
        parsed.text(closure.ret(tree).expect("a return type")),
        "Int"
    );
    let Some(Expr::BinaryExpr(body)) = closure.body(tree) else {
        panic!("the closure body is a product")
    };
    assert_eq!(parsed.text(body), "y * 2");
    assert!(matches!(args.next(), Some(Expr::NameRef(_))));
}

#[test]
fn views_walk_a_function_from_signature_to_leaves() {
    let parsed = Parsed::new(
        "fn add(a: Int, b: Int) -> Int {\n    let mut total = a + b\n    if total < 0 { return 0 } else { total }\n}\n",
    );
    let tree = parsed.tree();
    let item = parsed.item();
    assert!(!tree.has_error(item.node()));

    assert_eq!(parsed.text(item.name(tree).expect("named")), "add");
    let params: Vec<_> = item
        .param_list(tree)
        .expect("a parameter list")
        .params(tree)
        .map(|param| {
            (
                parsed.text(param.name(tree).expect("a name")),
                parsed.text(param.type_ref(tree).expect("a type")),
            )
        })
        .collect();
    assert_eq!(params, [("a", "Int"), ("b", "Int")]);
    assert_eq!(parsed.text(item.ret(tree).expect("a return type")), "Int");

    let body = block(item.body(tree));
    let stmts: Vec<Stmt> = body.stmts(tree).collect();
    assert_eq!(stmts.len(), 2);

    let Stmt::LetStmt(binding) = stmts[0] else {
        panic!("the first statement is a binding")
    };
    assert_eq!(parsed.text(binding.name(tree).expect("a name")), "total");
    assert!(binding.type_ref(tree).is_none());
    let Some(Expr::BinaryExpr(sum)) = binding.initializer(tree) else {
        panic!("the initializer is a sum")
    };
    assert_eq!(parsed.text(sum.lhs(tree).expect("lhs")), "a");
    assert_eq!(parsed.text(sum.rhs(tree).expect("rhs")), "b");

    let Stmt::Expr(Expr::IfExpr(branch)) = stmts[1] else {
        panic!("the second statement is an if expression")
    };
    assert_eq!(
        parsed.text(branch.condition(tree).expect("a condition")),
        "total < 0"
    );
    let then = branch.then_branch(tree).expect("a then branch");
    let Some(Stmt::ReturnStmt(ret)) = then.stmts(tree).next() else {
        panic!("the then branch returns")
    };
    assert_eq!(parsed.text(ret.value(tree).expect("a value")), "0");
    let Some(ElseBranch::Block(otherwise)) = branch.else_branch(tree) else {
        panic!("the else branch is a block")
    };
    let Some(Stmt::Expr(Expr::NameRef(name))) = otherwise.stmts(tree).next() else {
        panic!("the else branch yields a name")
    };
    assert_eq!(parsed.text(name), "total");
}

#[test]
fn a_block_condition_and_a_body_are_told_apart_by_order() {
    let parsed = Parsed::new("fn f() { if { a } { b } }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::IfExpr(branch))) = body.stmts(tree).next() else {
        panic!("the body is one if expression")
    };
    assert_eq!(
        parsed.text(branch.condition(tree).expect("a condition")),
        "{ a }"
    );
    assert_eq!(
        parsed.text(branch.then_branch(tree).expect("a body")),
        "{ b }"
    );
    assert!(branch.else_branch(tree).is_none());
}

#[test]
fn an_else_if_is_an_if_expression_branch() {
    let parsed = Parsed::new("fn f() { if a { 1 } else if b { 2 } else { 3 } }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::IfExpr(first))) = body.stmts(tree).next() else {
        panic!("one if expression")
    };
    let Some(ElseBranch::IfExpr(second)) = first.else_branch(tree) else {
        panic!("an else-if branch")
    };
    assert_eq!(
        parsed.text(second.condition(tree).expect("a condition")),
        "b"
    );
    assert!(matches!(
        second.else_branch(tree),
        Some(ElseBranch::Block(_))
    ));
}

#[test]
fn calls_and_arguments() {
    let parsed = Parsed::new("fn f() { g(1, h(2), 3) }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::CallExpr(call))) = body.stmts(tree).next() else {
        panic!("one call")
    };
    assert_eq!(parsed.text(call.callee(tree).expect("a callee")), "g");
    let args: Vec<&str> = call
        .arg_list(tree)
        .expect("arguments")
        .args(tree)
        .map(|arg| parsed.text(arg))
        .collect();
    assert_eq!(args, ["1", "h(2)", "3"]);
}

#[test]
fn missing_children_are_absent_and_the_node_is_flagged() {
    let parsed = Parsed::new("fn f() { let x = }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::LetStmt(binding)) = body.stmts(tree).next() else {
        panic!("one binding")
    };
    assert!(tree.has_error(binding.node()));
    assert_eq!(parsed.text(binding.name(tree).expect("a name")), "x");
    assert!(binding.initializer(tree).is_none());

    let parsed = Parsed::new("fn (a) {}");
    let tree = parsed.tree();
    let item = parsed.item();
    assert!(tree.has_error(item.node()));
    assert!(item.name(tree).is_none());
    assert!(item.param_list(tree).is_some());
}

#[test]
fn casts_refuse_other_kinds() {
    let parsed = Parsed::new("fn f() {}");
    let tree = parsed.tree();
    let item = parsed.item();
    assert!(SourceFile::cast(tree, item.node()).is_none());
    assert!(Expr::cast(tree, item.node()).is_none());
    assert_eq!(
        SourceFile::cast(tree, tree.root()).map(AstNode::node),
        Some(tree.root())
    );
}

#[test]
fn parser_known_roles_survive_recovery() {
    // `if {}` parses with the block as the body and the condition missing.
    // Although the block's type fits either field, the parser knows its role.
    let parsed = Parsed::new("fn f() { if {} }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::IfExpr(branch))) = body.stmts(tree).next() else {
        panic!("one if expression")
    };
    assert!(tree.has_error(branch.node()));
    assert!(branch.condition(tree).is_none());
    assert_eq!(
        parsed.text(branch.then_branch(tree).expect("the parsed body")),
        "{}"
    );
    assert!(branch.else_branch(tree).is_none());

    // Likewise, punctuation has already settled which side a lone operand
    // belongs to in assignments and binary expressions.
    let parsed = Parsed::new("fn f() { x = }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::AssignStmt(assignment)) = body.stmts(tree).next() else {
        panic!("one assignment")
    };
    assert!(tree.has_error(assignment.node()));
    assert_eq!(
        parsed.text(assignment.target(tree).expect("the parsed target")),
        "x"
    );
    assert!(assignment.value(tree).is_none());

    let parsed = Parsed::new("fn f() { x + }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::BinaryExpr(binary))) = body.stmts(tree).next() else {
        panic!("one binary expression")
    };
    assert!(tree.has_error(binary.node()));
    assert_eq!(parsed.text(binary.lhs(tree).expect("the parsed lhs")), "x");
    assert!(binary.rhs(tree).is_none());

    // A known right-hand role survives even when the left child is an
    // `Error`, which no typed expression field accepts.
    let parsed = Parsed::new("fn f() { fn + x }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::BinaryExpr(binary))) = body.stmts(tree).next() else {
        panic!("one recovered binary expression")
    };
    assert!(binary.lhs(tree).is_none());
    assert_eq!(parsed.text(binary.rhs(tree).expect("the parsed rhs")), "x");

    // Wrapping an existing binary expression gives that whole expression
    // the new wrapper's `lhs` role, not one inherited from its own children.
    let parsed = Parsed::new("fn f() { x + y + }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::BinaryExpr(outer))) = body.stmts(tree).next() else {
        panic!("one outer binary expression")
    };
    assert_eq!(
        parsed.text(outer.lhs(tree).expect("the parsed lhs")),
        "x + y"
    );
    assert!(outer.rhs(tree).is_none());

    // Missing neighboring fields do not hide an outer condition or else
    // branch whose role the parser settled.
    let parsed = Parsed::new("fn f() { if if a {} }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::IfExpr(outer))) = body.stmts(tree).next() else {
        panic!("one outer if expression")
    };
    assert!(matches!(outer.condition(tree), Some(Expr::IfExpr(_))));
    assert!(outer.then_branch(tree).is_none());

    let parsed = Parsed::new("fn f() { if x else {} }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::IfExpr(branch))) = body.stmts(tree).next() else {
        panic!("one if expression")
    };
    assert_eq!(parsed.text(branch.condition(tree).expect("condition")), "x");
    assert!(branch.then_branch(tree).is_none());
    assert!(matches!(
        branch.else_branch(tree),
        Some(ElseBranch::Block(_))
    ));

    // A chained comparison is retained as `Error`, but it still establishes
    // that the following expression is the assignment's value.
    let parsed = Parsed::new("fn f() { a < b < c = d }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::AssignStmt(assignment)) = body.stmts(tree).next() else {
        panic!("one recovered assignment")
    };
    assert!(!tree.has_error(assignment.node()));
    assert!(assignment.target(tree).is_none());
    assert_eq!(parsed.text(assignment.value(tree).expect("the value")), "d");
}

#[test]
fn a_child_of_one_possible_field_is_answered_despite_an_error() {
    // The name fits nothing but `name`, so the missing initializer does not
    // hide it; the return type fits nothing but `ret`.
    let parsed = Parsed::new("fn f() -> Int { let x: Int = }");
    let tree = parsed.tree();
    let item = parsed.item();
    assert!(tree.has_error(item.node()));
    assert_eq!(parsed.text(item.ret(tree).expect("a return type")), "Int");
    let body = block(item.body(tree));
    let Some(Stmt::LetStmt(binding)) = body.stmts(tree).next() else {
        panic!("one binding")
    };
    assert_eq!(parsed.text(binding.name(tree).expect("a name")), "x");
    assert_eq!(parsed.text(binding.type_ref(tree).expect("a type")), "Int");
    assert!(binding.initializer(tree).is_none());
}

#[test]
fn strings_with_holes_have_views() {
    let parsed = Parsed::new("fn f(n: Int) -> Str = \"{n} items, {\"{n}\"} nested\"\n");
    let tree = parsed.tree();
    let item = parsed.item();
    assert!(!tree.has_error(item.node()));
    let Some(Expr::InterpolatedString(string)) = item.body(tree) else {
        panic!("the body is a string with holes")
    };
    let holes: Vec<_> = string.holes(tree).collect();
    assert_eq!(holes.len(), 2);
    assert!(matches!(holes[0].value(tree), Some(Expr::NameRef(_))));
    let Some(Expr::InterpolatedString(nested)) = holes[1].value(tree) else {
        panic!("the second hole holds a string")
    };
    assert_eq!(parsed.text(nested), "\"{n}\"");
    assert_eq!(nested.holes(tree).count(), 1);
}
