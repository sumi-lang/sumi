//! The per-node error bit: whether the parser recovered inside a node.

use sumi_lexer::lex;
use sumi_syntax::{ParserInput, parse};

/// Every node of the parse in preorder, as `Kind`, or `Kind!` when the
/// node contains an error.
fn marked(source: &str) -> Vec<String> {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let tree = parse.tree();
    let mut nodes = Vec::new();
    let mut pending = vec![tree.root()];
    while let Some(node) = pending.pop() {
        let mark = if tree.has_error(node) { "!" } else { "" };
        nodes.push(format!("{:?}{mark}", tree.kind(node)));
        // Children come last first, so pushing them as yielded pops the
        // first child next: the walk stays preorder.
        pending.extend(tree.children(node));
    }
    nodes
}

#[test]
fn clean_syntax_sets_no_bit() {
    assert_eq!(
        marked("fn f(a: Int) -> Int {\n    let x = a + 1\n    x\n}\n"),
        [
            "SourceFile",
            "FnItem",
            "Name",
            "ParamList",
            "Param",
            "Name",
            "TypeRef",
            "TypeRef",
            "Block",
            "LetStmt",
            "Name",
            "BinaryExpr",
            "NameRef",
            "LiteralExpr",
            "NameRef",
        ]
    );
}

#[test]
fn layout_violations_are_not_errors() {
    assert_eq!(
        marked("fn f() { a-b }"),
        [
            "SourceFile",
            "FnItem",
            "Name",
            "ParamList",
            "Block",
            "BinaryExpr",
            "NameRef",
            "NameRef",
        ]
    );
}

#[test]
fn missing_syntax_marks_the_node_it_is_missing_from_and_its_ancestors() {
    assert_eq!(
        marked("fn f() { let x = }"),
        [
            "SourceFile!",
            "FnItem!",
            "Name",
            "ParamList",
            "Block!",
            "LetStmt!",
            "Name",
        ]
    );
}

#[test]
fn recovery_inside_a_name_marks_the_name() {
    assert_eq!(
        marked("fn _() {}"),
        ["SourceFile!", "FnItem!", "Name!", "ParamList", "Block"]
    );
}

#[test]
fn error_nodes_are_errors_and_their_siblings_are_not() {
    assert_eq!(
        marked("fn f() { x ) }"),
        [
            "SourceFile!",
            "FnItem!",
            "Name",
            "ParamList",
            "Block!",
            "NameRef",
            "Error!",
        ]
    );
}

#[test]
fn the_bit_stays_within_the_item_that_recovered() {
    assert_eq!(
        marked("fn f() { let x = }\nfn g() {}\n"),
        [
            "SourceFile!",
            "FnItem!",
            "Name",
            "ParamList",
            "Block!",
            "LetStmt!",
            "Name",
            "FnItem",
            "Name",
            "ParamList",
            "Block",
        ]
    );
}

#[test]
fn a_wrapped_operand_keeps_the_error_it_contained() {
    // The call wraps the parenthesized operand after it completed; the
    // recovery inside the parens belongs to the wrapper too.
    assert_eq!(
        marked("fn f() { (x }"),
        [
            "SourceFile!",
            "FnItem!",
            "Name",
            "ParamList",
            "Block!",
            "ParenExpr!",
            "NameRef",
        ]
    );
}
