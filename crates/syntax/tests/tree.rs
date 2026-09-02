mod common;

use sumi_lexer::lex;
use sumi_syntax::NodeKind::{self, *};
use sumi_syntax::{CompletedMarker, Marker, Parse, ParserInput, RawIdx};

/// Open a child of `parent`, run `body` inside it, and complete it as
/// `kind`.
fn node(
    parent: &mut Marker<'_, '_>,
    kind: NodeKind,
    body: impl FnOnce(&mut Marker<'_, '_>),
) -> CompletedMarker {
    let mut child = parent.start();
    body(&mut child);
    child.complete(kind)
}

/// A node over exactly the next token.
fn leaf(parent: &mut Marker<'_, '_>, kind: NodeKind) -> CompletedMarker {
    node(parent, kind, |m| m.token())
}

/// Attach the next `count` tokens to `marker`.
fn tokens(marker: &mut Marker<'_, '_>, count: usize) {
    for _ in 0..count {
        marker.token();
    }
}

/// Lex `source` and build a tree over it by running `build` inside the
/// root, then dump it.
fn dump(source: &str, build: impl FnOnce(&mut Marker<'_, '_>)) -> Vec<String> {
    let lexed = lex(source).expect("test sources fit in u32");
    let input = ParserInput::new(&lexed);
    let parse = Parse::build(&input, build);
    assert!(
        parse.evidence().is_empty(),
        "hand-built trees record no parser evidence"
    );
    common::dump(parse.tree(), &lexed, source)
}

#[track_caller]
fn check(source: &str, build: impl FnOnce(&mut Marker<'_, '_>), expected: &[&str]) {
    assert_eq!(dump(source, build), expected, "for source {source:?}");
}

#[test]
fn empty_source_builds_an_empty_root() {
    check("", |_| {}, &[r#"SourceFile 0..0 """#]);
}

#[test]
fn the_root_owns_edge_trivia() {
    check("  \n", |_| {}, &[r#"SourceFile 0..3 "  \n""#]);
}

#[test]
fn statements_nest_and_trivia_stays_interior() {
    check(
        "let x = 1",
        |b| {
            node(b, LetStmt, |b| {
                tokens(b, 3); // let x =
                leaf(b, LiteralExpr);
            });
        },
        &[
            "SourceFile 0..9",
            "  LetStmt 0..9",
            r#"    LiteralExpr 8..9 "1""#,
        ],
    );
}

#[test]
fn precede_wraps_the_left_operand() {
    check(
        "a + b",
        |b| {
            let lhs = leaf(b, NameExpr);
            let mut m = b.precede(lhs);
            m.token(); // +
            leaf(&mut m, NameExpr);
            m.complete(BinaryExpr);
        },
        &[
            "SourceFile 0..5",
            "  BinaryExpr 0..5",
            r#"    NameExpr 0..1 "a""#,
            r#"    NameExpr 4..5 "b""#,
        ],
    );
}

#[test]
fn precede_wraps_everything_attached_since_completion() {
    // The operator is attached before the wrapper opens, yet lands inside
    // it: the wrapper opens where the wrapped node did.
    check(
        "a + b",
        |b| {
            let lhs = leaf(b, NameExpr);
            b.token(); // +
            let mut m = b.precede(lhs);
            leaf(&mut m, NameExpr);
            m.complete(BinaryExpr);
        },
        &[
            "SourceFile 0..5",
            "  BinaryExpr 0..5",
            r#"    NameExpr 0..1 "a""#,
            r#"    NameExpr 4..5 "b""#,
        ],
    );
}

#[test]
fn precede_encloses_siblings_completed_since() {
    check(
        "a + b",
        |b| {
            let lhs = leaf(b, NameExpr);
            node(b, Error, |b| tokens(b, 2)); // + b
            b.precede(lhs).complete(BinaryExpr);
        },
        &[
            "SourceFile 0..5",
            "  BinaryExpr 0..5",
            r#"    NameExpr 0..1 "a""#,
            r#"    Error 2..5 "+ b""#,
        ],
    );
}

#[test]
fn precede_chains_for_left_associativity() {
    check(
        "a + b + c",
        |b| {
            let mut lhs = leaf(b, NameExpr);
            for _ in 0..2 {
                let mut m = b.precede(lhs);
                m.token(); // +
                leaf(&mut m, NameExpr);
                lhs = m.complete(BinaryExpr);
            }
        },
        &[
            "SourceFile 0..9",
            "  BinaryExpr 0..9",
            "    BinaryExpr 0..5",
            r#"      NameExpr 0..1 "a""#,
            r#"      NameExpr 4..5 "b""#,
            r#"    NameExpr 8..9 "c""#,
        ],
    );
}

#[test]
fn function_items_nest() {
    check(
        "fn f(a: int) -> int { a }",
        |b| {
            node(b, FnItem, |b| {
                tokens(b, 2); // fn f
                node(b, ParamList, |b| {
                    b.token(); // (
                    node(b, Param, |b| {
                        tokens(b, 2); // a:
                        leaf(b, TypeRef); // int
                    });
                    b.token(); // )
                });
                tokens(b, 2); // ->
                leaf(b, TypeRef); // int
                node(b, Block, |b| {
                    b.token(); // {
                    leaf(b, NameExpr);
                    b.token(); // }
                });
            });
        },
        &[
            "SourceFile 0..25",
            "  FnItem 0..25",
            "    ParamList 4..12",
            "      Param 5..11",
            r#"        TypeRef 8..11 "int""#,
            r#"    TypeRef 16..19 "int""#,
            "    Block 20..25",
            r#"      NameExpr 22..23 "a""#,
        ],
    );
}

#[test]
fn statement_kinds_cover_their_tokens() {
    check(
        "let x = -1\nx = 2\n_ = f((x))\ng(x)\nreturn",
        |b| {
            node(b, LetStmt, |b| {
                tokens(b, 3); // let x =
                node(b, PrefixExpr, |b| {
                    b.token(); // -
                    leaf(b, LiteralExpr);
                });
            });
            node(b, AssignStmt, |b| {
                leaf(b, NameExpr);
                b.token(); // =
                leaf(b, LiteralExpr);
            });
            node(b, DiscardStmt, |b| {
                tokens(b, 2); // _ =
                let callee = leaf(b, NameExpr);
                let mut m = b.precede(callee);
                node(&mut m, ArgList, |b| {
                    b.token(); // (
                    node(b, ParenExpr, |b| {
                        b.token(); // (
                        leaf(b, NameExpr);
                        b.token(); // )
                    });
                    b.token(); // )
                });
                m.complete(CallExpr);
            });
            // An expression in statement position is a bare child: with no
            // `;`, statement or tail is a matter of position.
            let callee = leaf(b, NameExpr);
            let mut m = b.precede(callee);
            node(&mut m, ArgList, |b| {
                b.token(); // (
                leaf(b, NameExpr);
                b.token(); // )
            });
            m.complete(CallExpr);
            node(b, ReturnStmt, |b| b.token());
        },
        &[
            "SourceFile 0..39",
            "  LetStmt 0..10",
            "    PrefixExpr 8..10",
            r#"      LiteralExpr 9..10 "1""#,
            "  AssignStmt 11..16",
            r#"    NameExpr 11..12 "x""#,
            r#"    LiteralExpr 15..16 "2""#,
            "  DiscardStmt 17..27",
            "    CallExpr 21..27",
            r#"      NameExpr 21..22 "f""#,
            "      ArgList 22..27",
            "        ParenExpr 23..26",
            r#"          NameExpr 24..25 "x""#,
            "  CallExpr 28..32",
            r#"    NameExpr 28..29 "g""#,
            "    ArgList 29..32",
            r#"      NameExpr 30..31 "x""#,
            r#"  ReturnStmt 33..39 "return""#,
        ],
    );
}

#[test]
fn if_expressions_and_error_nodes() {
    check(
        "if c { a } else { b } €",
        |b| {
            node(b, IfExpr, |b| {
                b.token(); // if
                leaf(b, NameExpr);
                node(b, Block, |b| {
                    b.token(); // {
                    leaf(b, NameExpr);
                    b.token(); // }
                });
                b.token(); // else
                node(b, Block, |b| {
                    b.token(); // {
                    leaf(b, NameExpr);
                    b.token(); // }
                });
            });
            leaf(b, Error);
        },
        &[
            "SourceFile 0..25",
            "  IfExpr 0..21",
            r#"    NameExpr 3..4 "c""#,
            "    Block 5..10",
            r#"      NameExpr 7..8 "a""#,
            "    Block 16..21",
            r#"      NameExpr 18..19 "b""#,
            r#"  Error 22..25 "€""#,
        ],
    );
}

#[test]
fn covering_finds_the_innermost_node() {
    let source = "let x = 1\ny";
    let lexed = lex(source).expect("test sources fit in u32");
    let input = ParserInput::new(&lexed);
    let parse = Parse::build(&input, |b| {
        node(b, LetStmt, |b| {
            tokens(b, 3); // let x =
            leaf(b, LiteralExpr);
        });
        leaf(b, NameExpr);
    });
    let tree = parse.tree();
    assert_eq!(tree.kind(tree.root()), SourceFile);

    let kind_at = |token| tree.kind(tree.covering(RawIdx::new(token)));
    assert_eq!(kind_at(0), LetStmt); // `let`, attached to the statement
    assert_eq!(kind_at(1), LetStmt); // trivia inside the statement
    assert_eq!(kind_at(6), LiteralExpr); // `1`, under the statement
    assert_eq!(kind_at(7), SourceFile); // the newline between children
    assert_eq!(kind_at(8), NameExpr); // `y`
}

// What the types cannot rule out is checked at run time. (What they can —
// completing a parent before its child, completing the root — is pinned by
// the `compile_fail` examples on `Marker`.)

#[test]
#[should_panic(expected = "at least one token")]
fn an_empty_node_panics_at_completion() {
    dump("x", |b| {
        leaf(b, NameExpr);
        node(b, Error, |_| {});
    });
}

#[test]
#[should_panic(expected = "preceded only from the node that contained it")]
fn preceding_after_the_containing_node_closed_panics() {
    dump("x y", |b| {
        let mut stmt = b.start();
        let name = leaf(&mut stmt, NameExpr);
        stmt.complete(LetStmt);
        let _wrapper = b.precede(name);
    });
}

#[test]
#[should_panic(expected = "preceded only from the node that contained it")]
fn preceding_from_a_sibling_panics() {
    dump("a + b", |b| {
        let lhs = leaf(b, NameExpr);
        let mut rest = b.start();
        tokens(&mut rest, 2); // + b
        let _wrapper = rest.precede(lhs);
    });
}

#[test]
#[should_panic(expected = "dropped without being completed")]
fn a_dropped_marker_panics_where_it_drops() {
    dump("x", |b| {
        let mut marker = b.start();
        marker.token();
    });
}

#[test]
#[should_panic(expected = "token past the input horizon")]
fn a_token_past_the_end_panics() {
    dump("x", |b| tokens(b, 2));
}

#[test]
#[should_panic(expected = "every significant token must be consumed")]
fn leftover_tokens_panic_at_build() {
    dump("x y", |b| b.token());
}
