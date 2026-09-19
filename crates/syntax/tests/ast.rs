use sumi_lexer::{LexedFile, lex};
use sumi_syntax::ast::{AstNode, Block, ElseBranch, Expr, SourceFile, Stmt};
use sumi_syntax::{NodeKind, Parse, ParserInput, SyntaxTree, parse};

struct Parsed {
    source: &'static str,
    lexed: LexedFile,
    parse: Parse,
}

impl Parsed {
    fn new(source: &'static str) -> Self {
        let lexed = lex(source).expect("test sources fit in u32");
        let parse = parse(ParserInput::new(&lexed));
        Self {
            source,
            lexed,
            parse,
        }
    }

    fn tree(&self) -> &SyntaxTree {
        self.parse.tree()
    }

    fn text(&self, view: impl AstNode) -> &str {
        self.tree()
            .byte_range(view.node(), &self.lexed)
            .text(self.source)
    }

    fn item(&self) -> sumi_syntax::ast::FnItem {
        let tree = self.tree();
        let file = SourceFile::cast(tree, tree.root()).expect("the root is a source file");
        let mut items = file.items(tree);
        let item = items.next().expect("one item");
        assert!(items.next().is_none(), "exactly one item");
        item
    }
}

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
fn missing_signature_fields_do_not_shift_later_roles() {
    for (source, has_return_type) in [("fn f -> int {}", true), ("fn f() -> {}", false)] {
        let parsed = Parsed::new(source);
        let tree = parsed.tree();
        let item = parsed.item();
        assert!(tree.has_error(item.node()));
        assert_eq!(parsed.text(item.name(tree).unwrap()), "f");
        assert_eq!(item.param_list(tree).is_some(), !has_return_type);
        assert_eq!(
            item.ret(tree).map(|ret| parsed.text(ret)),
            has_return_type.then_some("int")
        );
        assert_eq!(parsed.text(item.body(tree).unwrap()), "{}");
    }
    for (source, has_return_type) in [
        ("fn outer() = fn -> int {}", true),
        ("fn outer() = fn() -> {}", false),
    ] {
        let parsed = Parsed::new(source);
        let tree = parsed.tree();
        let Some(Expr::ClosureExpr(closure)) = parsed.item().body(tree) else {
            panic!("a recovered closure");
        };
        assert!(tree.has_error(closure.node()));
        assert_eq!(closure.param_list(tree).is_some(), !has_return_type);
        assert_eq!(
            closure.ret(tree).map(|ret| parsed.text(ret)),
            has_return_type.then_some("int")
        );
        assert_eq!(parsed.text(closure.body(tree).unwrap()), "{}");
    }
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
fn a_clean_view_holds_every_required_child() {
    use sumi_syntax::ast::{Clean, CleanExpr, CleanStmt, LetStmt};

    let parsed = Parsed::new("fn f() { let x: Int = 1 + 2 }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let stmt = body.stmts(tree).next().expect("one binding");
    let Some(CleanStmt::LetStmt(binding)) = stmt.clean(tree) else {
        panic!("a clean binding")
    };
    assert_eq!(parsed.text(binding.name()), "x");
    assert_eq!(
        parsed.text(binding.type_ref(tree).expect("annotated")),
        "Int"
    );
    let Some(CleanExpr::BinaryExpr(sum)) = binding.initializer().clean(tree) else {
        panic!("a clean sum")
    };
    assert_eq!(parsed.text(sum.lhs()), "1");
    assert_eq!(parsed.text(sum.rhs()), "2");
    assert_eq!(sum.view().node(), sum.node());
    assert_eq!(Clean::<LetStmt>::cast(tree, stmt.node()), Some(binding));
    assert_eq!(binding.clean(tree), Some(binding));

    let parsed = Parsed::new("fn f() { let x = }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let stmt = body.stmts(tree).next().expect("one binding");
    assert!(tree.has_error(stmt.node()));
    assert_eq!(stmt.clean(tree), None);
    assert_eq!(CleanStmt::cast(tree, stmt.node()), None);
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
fn declared_children_are_present_as_their_accessors_answer() {
    let parsed = Parsed::new("fn f(x) = x\n");
    let tree = parsed.tree();
    let item = parsed.item();
    let child = |name: &str| {
        *NodeKind::FnItem
            .children()
            .iter()
            .find(|child| child.name == name)
            .expect("a declared child")
    };
    assert!((child("name").present)(tree, item.node()));
    assert!((child("param_list").present)(tree, item.node()));
    assert!(!(child("ret").present)(tree, item.node()));
    assert!((child("body").present)(tree, item.node()));
    let param_list = item.param_list(tree).expect("a parameter list").node();
    assert!(!(child("name").present)(tree, param_list));
}

#[test]
fn multiline_if_blocks_keep_their_roles() {
    for source in [
        "fn f() = if { true }\n{ 1 }\nelse\n{ 2 }",
        "fn f() = if { true }\n\n// body\n{ 1 }\nelse\n{ 2 }",
    ] {
        let parsed = Parsed::new(source);
        let tree = parsed.tree();
        assert!(parsed.parse.evidence().is_empty());
        let Some(Expr::IfExpr(branch)) = parsed.item().body(tree) else {
            panic!("if body")
        };
        assert_eq!(parsed.text(branch.condition(tree).unwrap()), "{ true }");
        assert_eq!(parsed.text(branch.then_branch(tree).unwrap()), "{ 1 }");
        assert!(branch.else_branch(tree).is_some());
    }
    let parsed = Parsed::new("fn f() = if\n{}\nelse\n{}");
    let tree = parsed.tree();
    let Some(Expr::IfExpr(branch)) = parsed.item().body(tree) else {
        panic!("if body")
    };
    assert!(branch.condition(tree).is_none());
    assert_eq!(parsed.text(branch.then_branch(tree).unwrap()), "{}");
    assert!(branch.else_branch(tree).is_some());
}

#[test]
fn parser_known_roles_survive_recovery() {
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

    let parsed = Parsed::new("fn f() { fn + x }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::Expr(Expr::BinaryExpr(binary))) = body.stmts(tree).next() else {
        panic!("one recovered binary expression")
    };
    assert!(binary.lhs(tree).is_none());
    assert_eq!(parsed.text(binary.rhs(tree).expect("the parsed rhs")), "x");

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

    let parsed = Parsed::new("fn f() { a < b < c = d }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::AssignStmt(assignment)) = body.stmts(tree).next() else {
        panic!("one recovered assignment")
    };
    assert!(tree.has_error(assignment.node()));
    assert!(assignment.target(tree).is_none());
    assert_eq!(parsed.text(assignment.value(tree).expect("the value")), "d");

    let parsed = Parsed::new("fn f() { let x: Int = a < b < c }");
    let tree = parsed.tree();
    let body = block(parsed.item().body(tree));
    let Some(Stmt::LetStmt(binding)) = body.stmts(tree).next() else {
        panic!("one recovered binding")
    };
    assert!(tree.has_error(binding.node()));
    assert_eq!(parsed.text(binding.name(tree).expect("the name")), "x");
    assert_eq!(
        parsed.text(binding.type_ref(tree).expect("the type")),
        "Int"
    );
    assert!(binding.initializer(tree).is_none());
}

#[test]
fn a_child_of_one_possible_field_is_answered_despite_an_error() {
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
