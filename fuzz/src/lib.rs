//! The invariants the fuzz targets check, restated from the crates'
//! property tests over arbitrary input instead of generated sources. A
//! property test samples its generator a few hundred times; a fuzz target
//! runs these checks millions of times on inputs a coverage-guided mutator
//! steers toward code the corpus has not reached. Each check panics on the
//! invariant it finds broken, which libFuzzer records as a crash beside the
//! input that broke it.
//!
//! Nothing here ships: `sumi-fuzz` is a leaf above every crate, like
//! `sumi-scorecard`, and no production crate may depend on it.

use std::collections::HashSet;

use sumi_format::{normalize, reprint};
use sumi_frontend::{Applicability, FileId, ParsedSource, Place, Severity, codes, parse_source};
use sumi_lexer::{LexedFile, RawIdx, RawKind, SyntaxKind, TokenFlags, lex};
use sumi_syntax::{
    BRACKET_PAIRS, NodeIdx, NodeKind, Parse, ParseAnchor, ParseEvidence, ParserInput, SigIdx,
    SyntaxTree, parse,
};
use sumi_test::{Edit, Front, apply, changes_delimiter, front};

/// The file every fuzzed source stands for.
pub const FILE: FileId = FileId::new(0);

/// `lex` partitions the source: tokens are nonempty, contiguous, on
/// character boundaries, and reproduce it byte for byte; every lexical
/// error sits inside its token; every `Error` token has one; only a line
/// break or a multi-line literal spans lines; and a number is flagged
/// malformed exactly when it has an error.
pub fn check_lexed(source: &str, file: &LexedFile) {
    assert_eq!(file.source_len().to_usize(), source.len());

    let mut end = 0usize;
    for index in file.indices() {
        let range = file.range(index);
        let (start, stop) = (range.start().to_usize(), range.end().to_usize());
        assert!(start < stop, "token {index:?} is empty");
        assert_eq!(start, end, "token {index:?} is not contiguous");
        assert!(source.is_char_boundary(start));
        assert!(source.is_char_boundary(stop));
        end = stop;

        let text = file.text(source, index);
        if text.contains(['\n', '\r']) {
            assert!(
                matches!(
                    file.raw_kind(index),
                    RawKind::Newline | RawKind::BlockString | RawKind::RawBlockString
                ),
                "token {index:?} crosses a line break"
            );
        }
        if file.kind(index) == SyntaxKind::Error {
            assert!(
                file.errors().iter().any(|error| error.token == index),
                "error token {index:?} has no lexical error"
            );
        }
        if file.raw_kind(index) == RawKind::Number {
            let flagged = file.flags(index).contains(TokenFlags::MALFORMED_NUMBER);
            let has_error = file.errors().iter().any(|error| error.token == index);
            assert_eq!(
                flagged, has_error,
                "number {text:?} flagged={flagged} but has-error={has_error}"
            );
        }
    }
    assert_eq!(end, source.len(), "tokens must cover the source");

    for error in file.errors() {
        assert!(error.token < file.end());
        let token = file.range(error.token);
        assert!(token.start() <= error.range.start());
        assert!(error.range.end() <= token.end());
        assert!(source.is_char_boundary(error.range.start().to_usize()));
        assert!(source.is_char_boundary(error.range.end().to_usize()));
    }
}

/// The parser-facing stream keeps every significant token in order with
/// the scan's kinds, drops only trivia, records newlines and jointness
/// as the raw stream has them, puts boundaries only after a newline, and
/// pairs brackets mutually, by matching kinds, and nested.
pub fn check_input(lexed: &LexedFile, input: &ParserInput) {
    assert!(input.len() <= lexed.len());
    assert_eq!(input.get(input.end()), None);

    let mut previous: Option<RawIdx> = None;
    let mut open: Vec<SigIdx> = Vec::new();
    for index in input.indices() {
        let token = input.token(index);
        let kind = input.get(index).expect("indices below len are present");
        if let Some(previous) = previous {
            assert!(previous < token, "token mappings must strictly increase");
        }
        assert_eq!(kind, lexed.kind(token), "kinds must come from the scan");
        assert!(!kind.is_trivia(), "token {index:?} is trivia");

        let skipped = previous
            .map_or(RawIdx::new(0), |previous| previous + 1)
            .until(token);
        let newline = skipped
            .clone()
            .any(|j| lexed.kind(j) == SyntaxKind::Newline);
        for j in skipped {
            assert!(lexed.kind(j).is_trivia(), "token {j:?} was dropped");
        }
        assert_eq!(input.newline_before(index), newline);

        if index + 1 < input.end() {
            let next = input.token(index + 1);
            let adjacent = lexed.range(token).end() == lexed.range(next).start();
            assert_eq!(input.is_joint(index), adjacent);
        } else {
            assert!(!input.is_joint(index));
        }

        if input.boundary_before(index) {
            assert!(index > SigIdx::new(0), "no boundary before the first token");
            assert!(input.newline_before(index), "boundaries need a newline");
        }

        if let Some(partner) = input.partner(index) {
            assert!(partner < input.end());
            assert_eq!(
                input.partner(partner),
                Some(index),
                "partners must be mutual"
            );
            let (opener, closer) = if index < partner {
                (index, partner)
            } else {
                (partner, index)
            };
            assert!(
                input
                    .get(opener)
                    .zip(input.get(closer))
                    .is_some_and(|pair| BRACKET_PAIRS.contains(&pair)),
                "tokens {opener:?} and {closer:?} are partners but not a matching pair"
            );
            if partner > index {
                open.push(index);
            } else {
                assert_eq!(open.pop(), Some(partner), "pairs must nest");
            }
        }
        previous = Some(token);
    }
    assert!(open.is_empty(), "every pushed opener must have been closed");

    for j in previous
        .map_or(RawIdx::new(0), |previous| previous + 1)
        .until(lexed.end())
    {
        assert!(lexed.kind(j).is_trivia(), "token {j:?} was dropped");
    }
}

/// Widening every run of horizontal space by one column changes nothing
/// but the ranges: kinds, jointness, newline facts, and boundaries stay.
pub fn check_widening(source: &str, lexed: &LexedFile, input: &ParserInput) {
    let mut widened = String::with_capacity(source.len() + lexed.len());
    for index in lexed.indices() {
        widened.push_str(lexed.text(source, index));
        if lexed.raw_kind(index) == RawKind::HorizontalSpace {
            widened.push(' ');
        }
    }

    let widened_lexed = lex(&widened).expect("fuzz inputs fit in u32");
    assert_eq!(
        widened_lexed.len(),
        lexed.len(),
        "widening changed the token count"
    );
    for index in lexed.indices() {
        assert_eq!(lexed.kind(index), widened_lexed.kind(index));
    }

    let widened_input = ParserInput::new(&widened_lexed);
    assert_eq!(input.len(), widened_input.len());
    for index in input.indices() {
        assert_eq!(input.token(index), widened_input.token(index));
        assert_eq!(input.is_joint(index), widened_input.is_joint(index));
        assert_eq!(
            input.newline_before(index),
            widened_input.newline_before(index)
        );
        assert_eq!(
            input.boundary_before(index),
            widened_input.boundary_before(index)
        );
    }
}

/// Every structural invariant of a tree: extents partition the nodes;
/// children are ordered, disjoint, and inside their parent; every node
/// but the root covers at least one token and starts and ends on a
/// significant one; the root covers the whole buffer.
pub fn check_tree(tree: &SyntaxTree, lexed: &LexedFile) {
    let root = tree.root();
    assert_eq!(tree.first_token(root), RawIdx::new(0));
    assert_eq!(tree.end_token(root), lexed.end());

    let mut visited = 0usize;
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        visited += 1;
        let first = tree.first_token(node);
        let end = tree.end_token(node);
        assert!(first <= end, "node {node:?} has a backwards token range");
        assert!(end <= lexed.end(), "node {node:?} ends past the buffer");
        if node != root {
            assert!(first < end, "node {node:?} covers no token");
            assert!(
                !lexed.kind(first).is_trivia(),
                "node {node:?} starts on trivia"
            );
            assert!(
                !lexed.kind(end - 1).is_trivia(),
                "node {node:?} ends on trivia"
            );
        }

        // The tree yields children last first.
        let mut next_start = end;
        for child in tree.children(node) {
            assert!(
                tree.end_token(child) <= next_start,
                "children of {node:?} must be ordered and disjoint"
            );
            assert!(
                tree.first_token(child) >= first,
                "a child of {node:?} must stay inside its parent"
            );
            next_start = tree.first_token(child);
            pending.push(child);
        }
    }
    assert_eq!(visited, tree.len(), "extents must partition the tree");
}

/// The parse is lossless, attaches no significant token to the root
/// itself, and anchors every piece of evidence in bounds: present syntax
/// and skipped ranges are nonempty, and missing syntax names the exact
/// trivia interval between two significant tokens.
pub fn check_parse(source: &str, lexed: &LexedFile, input: &ParserInput, parse: &Parse) {
    let tree = parse.tree();
    assert_eq!(
        reprint(tree, lexed, source),
        source,
        "the tree is not lossless"
    );

    let mut items: Vec<NodeIdx> = tree.children(tree.root()).collect();
    items.reverse();
    let mut children = items.into_iter().peekable();
    for index in input.indices() {
        let token = input.token(index);
        while children
            .peek()
            .is_some_and(|&child| tree.end_token(child) <= token)
        {
            children.next();
        }
        assert!(
            children
                .peek()
                .is_some_and(|&child| tree.first_token(child) <= token),
            "token {token:?} is attached to the root"
        );
    }

    let raw_len = lexed.end();
    for evidence in parse.evidence() {
        let anchor = match evidence {
            ParseEvidence::Recovery(recovery) => {
                let mut previous_end = None;
                for skipped in &recovery.skipped {
                    assert!(skipped.start() < skipped.end());
                    assert!(skipped.end() <= raw_len);
                    if let Some(previous_end) = previous_end {
                        assert!(previous_end <= skipped.start());
                    }
                    previous_end = Some(skipped.end());
                }
                recovery.anchor
            }
            ParseEvidence::Violation(violation) => ParseAnchor::Tokens(violation.range),
        };
        match anchor {
            ParseAnchor::Tokens(range) => {
                assert!(range.start() < range.end());
                assert!(range.end() <= raw_len);
            }
            ParseAnchor::Gap(gap) => {
                assert!(gap.trivia_start() <= gap.trivia_end());
                assert!(gap.trivia_end() <= raw_len);
                if let Some(before) = gap.trivia_start().checked_sub(1) {
                    assert!(!lexed.kind(before).is_trivia());
                }
                for token in gap.trivia_start().until(gap.trivia_end()) {
                    assert!(lexed.kind(token).is_trivia());
                }
                if gap.trivia_end() < raw_len {
                    assert!(!lexed.kind(gap.trivia_end()).is_trivia());
                }
            }
        }
    }
}

/// Every canonical diagnostic is an error naming the parsed file, in
/// source order, with in-bounds labels on character boundaries, and a
/// safe fix of nonempty, ordered, disjoint edits; applying every
/// non-overlapping fix leaves a source the frontend still parses.
pub fn check_diagnostics(parsed: &ParsedSource) {
    let source = parsed.source();
    let mut previous = None;
    let mut edits = Vec::new();
    for diagnostic in parsed.diagnostics() {
        assert_eq!(diagnostic.severity, Severity::Error);
        let key = (
            diagnostic.primary.location.start().to_u32(),
            diagnostic.primary.location.end().to_u32(),
        );
        if let Some(previous) = previous {
            assert!(previous <= key, "diagnostics are not source sorted");
        }
        previous = Some(key);

        for label in std::iter::once(&diagnostic.primary).chain(&*diagnostic.secondary) {
            assert_eq!(label.location.file, parsed.file());
            let start = label.location.start().to_usize();
            let end = label.location.end().to_usize();
            assert!(start <= end && end <= source.len());
            assert!(source.is_char_boundary(start));
            assert!(source.is_char_boundary(end));
            if let Place::Point(point) = label.location.place {
                assert_eq!(point.to_usize(), start);
                assert_eq!(start, end);
            }
        }
        if let Some(fix) = &diagnostic.fix {
            assert_eq!(fix.applicability, Applicability::Safe);
            assert!(!fix.edits.is_empty());
            // Match the frontend property: each closer adds exactly its
            // code token and preserves all existing tokens and comments.
            // Nested same-kind repairs can legitimately be reoffered and
            // expose later errors, so do not compare global error counts.
            if diagnostic.code == codes::EXPECTED_TOKEN {
                assert_eq!(fix.edits.len(), 1);
                let edit = &fix.edits[0];
                assert_eq!(edit.range().start(), edit.range().end());
                let kind = match edit.replacement() {
                    ")" => SyntaxKind::RParen,
                    "}" => SyntaxKind::RBrace,
                    other => panic!("unexpected closer {other:?}"),
                };
                let mut fixed = source.to_owned();
                fixed.insert_str(edit.range().start().to_usize(), edit.replacement());
                let after = lex(&fixed).expect("fixed inputs fit in u32");
                let raw = after
                    .token_at(edit.range().start())
                    .expect("inserted token");
                assert_eq!(after.range(raw).start(), edit.range().start());
                assert_eq!(after.kind(raw), kind);
                assert_eq!(after.text(&fixed, raw), edit.replacement());
                let rank = after
                    .indices()
                    .take_while(|&token| token < raw)
                    .filter(|&token| !after.kind(token).is_trivia())
                    .count();
                let mut tokens = significant(&after, &fixed);
                tokens.remove(rank);
                assert_eq!(tokens, significant(parsed.lexed(), source));
                assert_eq!(comments(&after, &fixed), comments(parsed.lexed(), source));
            }
            let mut previous_end = None;
            for edit in &fix.edits {
                let range = edit.range();
                let start = range.start().to_usize();
                let end = range.end().to_usize();
                assert!(start <= end && end <= source.len());
                assert!(source.is_char_boundary(start));
                assert!(source.is_char_boundary(end));
                if let Some(previous_end) = previous_end {
                    assert!(previous_end <= start);
                }
                previous_end = Some(end);
                edits.push(edit);
            }
        }
    }

    // Apply every fix as the corpus runner does, dropping the later of two
    // that overlap, and parse what is left.
    edits.sort_by_key(|edit| (edit.range().start(), edit.range().end()));
    let mut fixed = source.to_owned();
    let mut applied_end = None;
    let mut applied = Vec::new();
    for edit in edits {
        if applied_end.is_some_and(|end| end > edit.range().start()) {
            continue;
        }
        applied_end = Some(edit.range().end());
        applied.push(edit);
    }
    for edit in applied.iter().rev() {
        let range = edit.range();
        fixed.replace_range(
            range.start().to_usize()..range.end().to_usize(),
            edit.replacement(),
        );
    }
    let reparsed = parse_source(parsed.file(), fixed.into()).expect("fixed inputs fit in u32");
    check_tree(reparsed.parse().tree(), reparsed.lexed());
}

/// Normalizing keeps every significant token and every comment, reparses
/// to the same shape, and settles in one pass.
pub fn check_normalize(source: &str, lexed: &LexedFile, parsed: &Parse) {
    let normalized = normalize(source, lexed, parsed);
    let after_lexed = lex(&normalized).expect("normalized inputs fit in u32");
    let after = parse(&ParserInput::new(&after_lexed));

    assert_eq!(
        significant(&after_lexed, &normalized),
        significant(lexed, source),
        "normalize rewrote tokens: {source:?} -> {normalized:?}"
    );
    assert_eq!(
        comments(&after_lexed, &normalized),
        comments(lexed, source),
        "normalize lost a comment: {source:?} -> {normalized:?}"
    );
    assert_eq!(
        shape(after.tree()),
        shape(parsed.tree()),
        "normalize changed the shape: {source:?} -> {normalized:?}"
    );

    let again = normalize(&normalized, &after_lexed, &after);
    assert_eq!(
        again, normalized,
        "normalize is not idempotent on {source:?}"
    );
}

/// The tree's shape: depth and kind per node, in preorder.
fn shape(tree: &SyntaxTree) -> Vec<(usize, NodeKind)> {
    let mut nodes = Vec::new();
    let mut pending = vec![(tree.root(), 0usize)];
    while let Some((node, depth)) = pending.pop() {
        nodes.push((depth, tree.kind(node)));
        pending.extend(tree.children(node).map(|child| (child, depth + 1)));
    }
    nodes
}

/// The significant tokens, kinds and texts in order.
fn significant<'src>(lexed: &LexedFile, source: &'src str) -> Vec<(SyntaxKind, &'src str)> {
    lexed
        .indices()
        .filter(|&index| !lexed.kind(index).is_trivia())
        .map(|index| (lexed.kind(index), lexed.text(source, index)))
        .collect()
}

/// The comments in order.
fn comments<'src>(lexed: &LexedFile, source: &'src str) -> Vec<&'src str> {
    lexed
        .indices()
        .filter(|&index| lexed.kind(index) == SyntaxKind::LineComment)
        .map(|index| lexed.text(source, index))
        .collect()
}

/// A well-formed program lexes without error and parses without evidence.
pub fn check_well_formed(source: &str, original: &Front) {
    assert!(
        original.lexed.errors().is_empty(),
        "lexer errors in {source:?}: {:?}",
        original.lexed.errors()
    );
    check_tree(original.parse.tree(), &original.lexed);
    assert!(
        original.parse.evidence().is_empty(),
        "parse evidence {:?} in {source:?}",
        original.parse.evidence()
    );
}

/// Recovery after one edit stays local: a non-delimiter edit disturbs
/// only the items and statements it lands in, and a delimiter edit
/// preserves every item it does not touch.
pub fn check_recovery(source: &str, original: &Front, index: usize, edit: Edit) {
    let sig = |index: usize| SigIdx::new(u32::try_from(index).expect("positions fit in u32"));
    let (edited, touched, moved, impact) = apply(source, &original.spans(), index, edit);
    let touched: Vec<RawIdx> = touched
        .iter()
        .map(|&index| original.input.token(sig(index)))
        .collect();
    let after = front(&edited);
    check_tree(after.parse.tree(), &after.lexed);

    if changes_delimiter(&original.input, index, edit) {
        let tree = after.parse.tree();
        let survivors: HashSet<_> = tree
            .children(tree.root())
            .filter(|&node| tree.kind(node) == NodeKind::FnItem)
            .map(|node| (after.node_span(node), after.shape(&edited, node)))
            .collect();
        let tree = original.parse.tree();
        for item in tree.children(tree.root()).filter(|&node| {
            tree.kind(node) == NodeKind::FnItem
                && !touched
                    .iter()
                    .any(|&token| tree.first_token(node) <= token && token < tree.end_token(node))
        }) {
            let shape = original.shape(source, item);
            let span = impact.map(original.node_span(item));
            assert!(
                survivors.contains(&(span, shape.clone())),
                "{edit:?} at token {index} ({:?}) disturbs the item {:?}\n--- original ---\n{source}\n--- edited ---\n{edited}\nevidence: {:?}",
                original.input.get(sig(index)),
                shape.0,
                after.parse.evidence()
            );
        }
    } else {
        let moved: Vec<RawIdx> = moved
            .iter()
            .map(|&index| original.input.token(sig(index)))
            .collect();
        let survivors: HashSet<_> = after
            .parse
            .tree()
            .nodes()
            .map(|node| (after.node_span(node), after.shape(&edited, node)))
            .collect();
        for node in original.guarded(&touched, &moved) {
            let shape = original.shape(source, node);
            let span = impact.map(original.node_span(node));
            assert!(
                survivors.contains(&(span, shape.clone())),
                "{edit:?} at token {index} ({:?}) disturbs the {:?} {:?}\n--- original ---\n{source}\n--- edited ---\n{edited}\nevidence: {:?}",
                original.input.get(sig(index)),
                original.parse.tree().kind(node),
                shape.0,
                after.parse.evidence()
            );
        }
    }
}
