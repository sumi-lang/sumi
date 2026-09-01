use sumi_format::{Element, elements, layout_violation_edits, normalize, reprint};
use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{
    NodeKind, Parse, ParseEvidence, ParseViolationKind, ParserInput, SyntaxTree, parse,
};

struct Front {
    lexed: LexedFile,
    parse: Parse,
}

fn front(source: &str) -> Front {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&lexed));
    Front { lexed, parse }
}

/// The tree's shape: depth and kind per node, in preorder.
fn shape(tree: &SyntaxTree) -> Vec<(usize, NodeKind)> {
    let mut nodes = Vec::new();
    let mut pending = vec![(tree.root(), 0usize)];
    while let Some((node, depth)) = pending.pop() {
        nodes.push((depth, tree.kind(node)));
        // Children come last first, so pushing them as yielded pops the
        // first child next: the walk stays preorder.
        pending.extend(tree.children(node).map(|child| (child, depth + 1)));
    }
    nodes
}

fn violations(front: &Front) -> Vec<ParseViolationKind> {
    front
        .parse
        .evidence()
        .iter()
        .filter_map(|evidence| match evidence {
            ParseEvidence::Violation(violation) => Some(violation.kind),
            ParseEvidence::Recovery(_) => None,
        })
        .collect()
}

fn apply_edits(source: &str, edits: &[sumi_text::TextEdit]) -> String {
    let mut result = source.to_owned();
    for edit in edits.iter().rev() {
        let range = edit.range();
        result.replace_range(
            range.start().to_usize()..range.end().to_usize(),
            edit.replacement(),
        );
    }
    result
}

#[track_caller]
fn check_layout_edits(source: &str, kind: ParseViolationKind, expected: Option<&str>) {
    let front = front(source);
    let violation = front
        .parse
        .evidence()
        .iter()
        .find_map(|evidence| match evidence {
            ParseEvidence::Violation(violation) if violation.kind == kind => Some(*violation),
            _ => None,
        })
        .expect("source has the requested violation");
    let edits = layout_violation_edits(source, &front.lexed, violation);
    assert_eq!(
        edits.as_deref().map(|edits| apply_edits(source, edits)),
        expected.map(str::to_owned),
        "layout edits for {source:?}"
    );
    if let Some(edits) = edits {
        assert!(!edits.is_empty());
        assert!(
            edits
                .windows(2)
                .all(|pair| { pair[0].range().end() <= pair[1].range().start() })
        );
    }
}

/// Normalize `source`; assert the expected text, that no layout violation
/// survives, that the tree shape is unchanged, and that a second pass
/// changes nothing.
#[track_caller]
fn check_normalize(source: &str, expected: &str) {
    let before = front(source);
    let normalized = normalize(source, &before.lexed, &before.parse);
    assert_eq!(normalized, expected, "normalize of {source:?}");

    let after = front(&normalized);
    let remaining: Vec<_> = violations(&after)
        .into_iter()
        .filter(|&kind| kind != ParseViolationKind::ChainedComparison)
        .collect();
    assert_eq!(remaining, [], "violations survive normalize of {source:?}");
    assert_eq!(
        shape(after.parse.tree()),
        shape(before.parse.tree()),
        "normalize changed the shape of {source:?}"
    );

    let again = normalize(&normalized, &after.lexed, &after.parse);
    assert_eq!(
        again, normalized,
        "normalize of {source:?} is not idempotent"
    );
}

#[track_caller]
fn check_roundtrip(source: &str) {
    let front = front(source);
    assert_eq!(
        reprint(front.parse.tree(), &front.lexed, source),
        source,
        "reprint of {source:?}"
    );
}

/// Render a node's elements: token texts and child node kinds, in order.
fn render_elements(front: &Front, source: &str, node: usize) -> Vec<String> {
    elements(front.parse.tree(), node)
        .map(|element| match element {
            Element::Token(token) => format!("{:?}", front.lexed.text(source, token as usize)),
            Element::Node(child) => format!("{:?}", front.parse.tree().kind(child)),
        })
        .collect()
}

#[test]
fn elements_interleave_attached_tokens_and_children() {
    let source = "fn f(a: Int) { 1 } // tail\n";
    let front = front(source);
    let tree = front.parse.tree();

    // Edge trivia belongs to the root; the item is one subtree.
    assert_eq!(
        render_elements(&front, source, tree.root()),
        ["FnItem", "\" \"", "\"// tail\"", "\"\\n\""]
    );

    // Trivia between children belongs to the node between them.
    let item = tree.children(tree.root()).next().expect("one item");
    assert_eq!(
        render_elements(&front, source, item),
        ["\"fn\"", "\" \"", "\"f\"", "ParamList", "\" \"", "Block"]
    );
}

#[test]
fn elements_of_an_empty_file_are_empty() {
    let source = "";
    let front = front(source);
    let tree = front.parse.tree();
    assert_eq!(elements(tree, tree.root()).count(), 0);
}

#[test]
fn elements_of_a_trivia_only_file_all_attach_to_the_root() {
    let source = "  // note\n";
    let front = front(source);
    assert_eq!(
        render_elements(&front, source, front.parse.tree().root()),
        ["\"  \"", "\"// note\"", "\"\\n\""]
    );
}

#[test]
fn every_raw_token_attaches_to_exactly_one_node() {
    let source = "fn f(a b { // g\nlet x = ((1) }\n\"open";
    let front = front(source);
    let tree = front.parse.tree();
    let mut owner = vec![None; front.lexed.len()];
    for node in 0..tree.len() {
        for element in elements(tree, node) {
            if let Element::Token(token) = element {
                assert_eq!(
                    owner[token as usize], None,
                    "token {token} attached to two nodes"
                );
                owner[token as usize] = Some(node);
            }
        }
    }
    assert!(owner.iter().all(Option::is_some), "unattached raw tokens");
}

#[test]
fn reprint_is_the_identity_on_malformed_sources() {
    for source in [
        "",
        " \t\n",
        "\u{feff}fn f() {}",
        "fn f( { ) }",
        "fn f() { a==b }\n\u{20ac} ; [",
        "\"open string",
        "fn f() { 'ab' '' }",
        "0123 1e+05 1u32",
        "r##\"unterminated",
        "let x = 1\nfn g(,,) -> {",
        "fn f() {\r\n return 1 \r}",
        "fn f() { ((((( }",
        ": (x)",
        "// only a comment",
        "fn 0() fn",
    ] {
        check_roundtrip(source);
    }
}

#[test]
fn reprint_survives_the_nesting_recovery_limit() {
    let source = format!("fn f() {{ {}x }}", "(".repeat(400));
    check_roundtrip(&source);
}

#[test]
fn normalize_without_violations_is_the_identity() {
    check_normalize("fn f() { f(1) }\n", "fn f() { f(1) }\n");
}

#[test]
fn layout_violation_edits_are_atomic_and_source_ordered() {
    check_layout_edits(
        "fn f()\n{ 1 }",
        ParseViolationKind::BlockOnNewLine,
        Some("fn f() {\n 1 }"),
    );
    check_layout_edits(
        "fn f() { a==b }",
        ParseViolationKind::UnspacedBinaryOperator,
        Some("fn f() { a == b }"),
    );
    check_layout_edits(
        "fn f() { a +\n b }",
        ParseViolationKind::TrailingOperator,
        Some("fn f() { a \n + b }"),
    );
    check_layout_edits(
        "fn f() { - \t1 }",
        ParseViolationKind::SpacedPrefixOperator,
        Some("fn f() { -1 }"),
    );
}

#[test]
fn layout_violation_edits_reject_nonmechanical_candidates() {
    check_layout_edits(
        "fn f() { a +\n}",
        ParseViolationKind::TrailingOperator,
        None,
    );
    check_layout_edits(
        "fn f() { - // why\n 1 }",
        ParseViolationKind::SpacedPrefixOperator,
        None,
    );
    check_layout_edits(
        "fn f() { - \r1 }",
        ParseViolationKind::SpacedPrefixOperator,
        None,
    );
    check_layout_edits(
        "fn f() { a < b < c }",
        ParseViolationKind::ChainedComparison,
        None,
    );
}

#[test]
fn normalize_spaces_unspaced_binary_operators() {
    check_normalize("fn f() { a==b }", "fn f() { a == b }");
    check_normalize("fn f() { a +b }", "fn f() { a + b }");
    check_normalize("fn f() { a+ b }", "fn f() { a + b }");
    check_normalize("fn f() { a<=b*c }", "fn f() { a <= b * c }");
}

#[test]
fn normalize_moves_trailing_operators_to_the_continuation_line() {
    check_normalize("fn f() { let x = a +\n b }", "fn f() { let x = a \n + b }");
    check_normalize(
        "fn f() { let x = a && // why\n b }",
        "fn f() { let x = a  // why\n && b }",
    );
}

#[test]
fn normalize_leaves_a_trailing_operator_missing_its_operand() {
    // The parser records the violation before parsing the operand; moving
    // the operator in front of anything else would change the parse.
    for source in ["fn f() { a +\n: b }", "fn f() { a +\n}"] {
        let before = front(source);
        assert!(
            violations(&before).contains(&ParseViolationKind::TrailingOperator),
            "the trailing operator must be recorded for {source:?}"
        );
        let normalized = normalize(source, &before.lexed, &before.parse);
        assert_eq!(
            normalized, source,
            "an operandless trailing operator stays as written"
        );
    }
}

#[test]
fn normalize_yields_when_the_rewrite_would_change_the_parse() {
    // Recovery entangled with the operator: the continuation is a real
    // operand, but the garbage between the operands means the moved
    // operator hands recovery a different reading — which no check on the
    // tokens foresees. The reparse gate catches it and yields the source
    // as written. Found by the normalize property.
    let source = "fn f() { true&<\ntrue }";
    let before = front(source);
    let normalized = normalize(source, &before.lexed, &before.parse);
    assert_eq!(normalized, source, "an entangled rewrite stays as written");

    // When only the move is unsafe, the independent spacing edit still
    // lands and passes the gate.
    let source = "fn f() { true<\n) }";
    let before = front(source);
    let normalized = normalize(source, &before.lexed, &before.parse);
    assert_eq!(normalized, "fn f() { true <\n) }");
}

#[test]
fn normalize_glues_spaced_prefix_operators() {
    check_normalize("fn f() { let x = - 1 }", "fn f() { let x = -1 }");
    check_normalize("fn f() { let x = ! \t flag }", "fn f() { let x = !flag }");
}

#[test]
fn normalize_moves_blocks_to_their_owner_line() {
    check_normalize("fn f()\n{ 1 }", "fn f() {\n 1 }");
    check_normalize("fn f() -> Int\n    { 1 }", "fn f() -> Int {\n     1 }");
    // The gap's comment survives, after the `{`.
    check_normalize("fn f() // sig\n{ 1 }", "fn f() { // sig\n 1 }");
}

#[test]
fn normalize_applies_cooccurring_violations_on_one_operator() {
    check_normalize("fn f() { let x = a+\nb }", "fn f() { let x = a \n+ b }");
}

#[test]
fn normalize_leaves_chained_comparisons_as_written() {
    let source = "fn f() { let x = a < b < c }";
    let before = front(source);
    assert_eq!(
        violations(&before),
        [ParseViolationKind::ChainedComparison],
        "the chain is the only violation"
    );
    let normalized = normalize(source, &before.lexed, &before.parse);
    assert_eq!(normalized, source);
}

#[test]
fn normalize_never_deletes_a_comment_from_a_prefix_gap() {
    let source = "fn f() { let x = - // why\n 1 }";
    let before = front(source);
    assert_eq!(
        violations(&before),
        [ParseViolationKind::SpacedPrefixOperator]
    );
    let normalized = normalize(source, &before.lexed, &before.parse);
    assert_eq!(normalized, source, "a comment-blocked gap stays as written");
}
