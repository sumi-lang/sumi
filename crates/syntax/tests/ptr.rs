//! Node pointers: identity by kind, byte range, and source text, resolved
//! back into a tree — the same one, or a reparse where the node has not
//! moved or changed.

use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{NodeKind, NodePtr, Parse, ParserInput, parse};
use sumi_text::{TextRange, TextSize};

fn parsed(source: &str) -> (LexedFile, Parse) {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&lexed));
    (lexed, parse)
}

#[track_caller]
fn every_node_resolves_to_itself(source: &str) {
    let (lexed, parse) = parsed(source);
    let tree = parse.tree();
    for node in tree.nodes() {
        let ptr = tree.ptr(node, &lexed);
        assert_eq!(
            tree.resolve(ptr, source, &lexed, source),
            Some(node),
            "{ptr:?} in {source:?}"
        );
    }
}

#[test]
fn pointers_round_trip_through_their_own_tree() {
    every_node_resolves_to_itself(
        "fn f(a: Int) -> Int {\n    let x = a + 1\n    return x * 2\n}\n",
    );
    every_node_resolves_to_itself("// leading\nfn g() {\n    h(1, (2 + 3), \"s\")\n}\n// trailing");
    every_node_resolves_to_itself("fn f( {\n    let x = ((1 +\n}\n");
    every_node_resolves_to_itself("fn ; broken [ let = \n }} )\n");
    every_node_resolves_to_itself("");
    every_node_resolves_to_itself("  // only trivia\n");
}

#[test]
fn a_pointer_survives_a_reparse_and_an_edit_after_the_node() {
    let before = "fn f() { 1 }\nfn g() {}\n";
    let (lexed, parse) = parsed(before);
    let tree = parse.tree();
    let first = tree
        .children(tree.root())
        .last()
        .expect("the first item comes last from a reversed walk");
    assert_eq!(tree.kind(first), NodeKind::FnItem);
    let ptr = tree.ptr(first, &lexed);
    assert_eq!(ptr.range.text(before), "fn f() { 1 }");

    let after = "fn f() { 1 }\nfn g() { 2 + 3 }\n";
    let (lexed, parse) = parsed(after);
    let tree = parse.tree();
    let found = tree
        .resolve(ptr, before, &lexed, after)
        .expect("the untouched item still stands");
    assert_eq!(tree.kind(found), NodeKind::FnItem);
    assert_eq!(tree.byte_range(found, &lexed).text(after), "fn f() { 1 }");
}

#[test]
fn a_moved_node_does_not_resolve() {
    let before = "fn f() {}\nfn g() { 1 }\n";
    let (lexed, parse) = parsed(before);
    let tree = parse.tree();
    let last = tree.children(tree.root()).next().expect("two items");
    let ptr = tree.ptr(last, &lexed);
    assert_eq!(ptr.range.text(before), "fn g() { 1 }");

    // Lengthening the first item shifts the second: its old bytes are now
    // the middle of something else.
    let after = "fn f() { 0 }\nfn g() { 1 }\n";
    let (lexed, parse) = parsed(after);
    assert_eq!(parse.tree().resolve(ptr, before, &lexed, after), None);
}

#[test]
fn a_changed_node_at_the_same_range_does_not_resolve() {
    let before = "fn f() { x }";
    let (lexed, parse) = parsed(before);
    let tree = parse.tree();
    let item = tree.children(tree.root()).next().expect("one item");
    let ptr = tree.ptr(item, &lexed);

    // The replacement has the same lexical and syntactic shape. Kind and
    // range alone would resolve this pointer to semantically different text.
    let after = "fn f() { y }";
    let (lexed, parse) = parsed(after);
    assert_eq!(parse.tree().resolve(ptr, before, &lexed, after), None);
}

#[test]
fn the_kind_must_match() {
    let source = "fn f() { x }";
    let (lexed, parse) = parsed(source);
    let tree = parse.tree();
    let name = tree
        .nodes()
        .find(|&node| tree.kind(node) == NodeKind::Name)
        .expect("the item has a name");
    let ptr = tree.ptr(name, &lexed);
    assert_eq!(tree.resolve(ptr, source, &lexed, source), Some(name));
    let as_ref = NodePtr {
        kind: NodeKind::NameRef,
        ..ptr
    };
    assert_eq!(tree.resolve(as_ref, source, &lexed, source), None);
}

#[test]
fn a_range_off_token_boundaries_does_not_resolve() {
    let source = "fn f() {}";
    let (lexed, parse) = parsed(source);
    let tree = parse.tree();
    let inside = |start, end| NodePtr {
        kind: NodeKind::FnItem,
        range: TextRange::new(TextSize::new(start), TextSize::new(end)),
    };
    // The item and the root share these bytes; the kind tells them apart.
    let item = tree.children(tree.root()).next().expect("one item");
    assert_eq!(
        tree.resolve(inside(0, 9), source, &lexed, source),
        Some(item)
    );
    assert_eq!(tree.resolve(inside(1, 9), source, &lexed, source), None);
    assert_eq!(tree.resolve(inside(0, 8), source, &lexed, source), None);
    assert_eq!(tree.resolve(inside(0, 40), source, &lexed, source), None);
}

#[test]
fn an_empty_range_names_only_the_root_of_an_empty_file() {
    let empty = NodePtr {
        kind: NodeKind::SourceFile,
        range: TextRange::new(TextSize::new(0), TextSize::new(0)),
    };
    let (lexed, parse) = parsed("");
    assert_eq!(
        parse.tree().resolve(empty, "", &lexed, ""),
        Some(parse.tree().root())
    );
    let (lexed, parse) = parsed("fn f() {}");
    assert_eq!(parse.tree().resolve(empty, "", &lexed, "fn f() {}"), None);
}
