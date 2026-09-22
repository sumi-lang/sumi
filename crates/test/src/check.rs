//! Every layer's invariants, each stated once, so a property test and a fuzz target share them. A
//! check panics on the invariant it finds broken.

use std::collections::HashSet;

use sumi_format::{Formatted, rep};
use sumi_frontend::{ParsedSource, codes, parse_source};
use sumi_hir::{Analysis, Program};
use sumi_lexer::{LexedFile, RawIdx, SyntaxKind, TokenFlags, lex};
use sumi_syntax::ast::TokenRule;
use sumi_syntax::{
    NodeKind, Parse, ParseAnchor, ParseEvidence, ParseRecoveryKind, ParserInput, Side, SigIdx,
    SyntaxTree, bracket,
};
use sumi_text::TextRange;

use crate::{Edit, Front, apply, changes_delimiter, front};

pub fn lexed(source: &str, file: &LexedFile) {
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
            assert_eq!(
                file.kind(index),
                SyntaxKind::Newline,
                "token {index:?} crosses a line break"
            );
        }
        if file.kind(index) == SyntaxKind::Error {
            assert!(
                file.errors().iter().any(|error| error.token == index),
                "error token {index:?} has no lexical error"
            );
        }
        if file.kind(index) == SyntaxKind::IntLiteral {
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

pub fn input(lexed: &LexedFile, input: &ParserInput) {
    assert!(input.len() <= lexed.len());
    assert_eq!(input.get(input.end()), None);

    let mut remaining_boundaries = input
        .indices()
        .filter(|&i| input.boundary_before(i))
        .count();
    assert!(!input.boundary_in(input.end()..input.end()));
    for index in input.indices() {
        assert!(!input.boundary_in(index..index));
        assert_eq!(
            input.boundary_in(index..index + 1),
            input.boundary_before(index)
        );
        assert_eq!(
            input.boundary_in(index..input.end()),
            remaining_boundaries != 0
        );
        remaining_boundaries -= usize::from(input.boundary_before(index));
    }

    let mut previous: Option<RawIdx> = None;
    let mut open: Vec<SigIdx> = Vec::new();
    let mut layout_open: Vec<SigIdx> = Vec::new();
    for index in input.indices() {
        let token = input.token(index);
        let kind = input.get(index).expect("indices below len are present");
        assert_eq!(input.in_matched_delimiters(index), !open.is_empty());
        let context = layout_open.last().is_some_and(|&opener| {
            let pair = input.get(opener).and_then(bracket);
            pair.is_some_and(|(pair, _)| !pair.encloses_statements())
                && input.partner(opener).is_some()
        });
        assert_eq!(input.in_expression_delimiters(index), context);
        if sumi_syntax::is_opener(kind) {
            layout_open.push(index);
        } else if let Some(partner) = input.partner(index).filter(|&p| p < index) {
            let position = layout_open.iter().rposition(|&p| p == partner).unwrap();
            layout_open.truncate(position);
        }
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
            let opens = input.get(opener).and_then(bracket);
            let closes = input.get(closer).and_then(bracket);
            assert!(
                matches!((opens, closes), (Some((a, Side::Open)), Some((b, Side::Close))) if a == b),
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

pub fn widening(source: &str, lexed: &LexedFile, input: &ParserInput) {
    let mut widened = String::with_capacity(source.len() + lexed.len());
    for index in lexed.indices() {
        widened.push_str(lexed.text(source, index));
        if lexed.kind(index) == SyntaxKind::Whitespace {
            widened.push(' ');
        }
    }

    let widened_lexed = lex(&widened).expect("widened sources fit in u32");
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

pub fn tree(tree: &SyntaxTree, lexed: &LexedFile) {
    let input = ParserInput::new(lexed);
    let root = tree.root();
    let item_starts: HashSet<_> = tree
        .children(root)
        .filter(|&node| tree.kind(node) == NodeKind::FnItem)
        .map(|node| tree.first_token(node))
        .collect();
    for index in input
        .indices()
        .filter(|&i| item_starts.contains(&input.token(i)))
    {
        assert!(
            !input.in_matched_delimiters(index),
            "root item starts inside a matched pair"
        );
    }
    assert_eq!(tree.kind(root), NodeKind::SourceFile);
    assert_eq!(tree.first_token(root), RawIdx::new(0));
    assert_eq!(tree.end_token(root), lexed.end());

    if !lexed.is_empty() {
        // Three tokens only: the reference is linear per query, so every token would be quadratic.
        for index in [0, lexed.len() / 2, lexed.len() - 1] {
            let token = RawIdx::new(index as u32);
            let innermost = tree
                .nodes()
                .filter(|&node| tree.first_token(node) <= token && token < tree.end_token(node))
                .min_by_key(|&node| tree.subtree_len(node));
            assert_eq!(Some(tree.covering(token)), innermost);
        }
    }

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

        // What a clean view rests on.
        if !tree.has_error(node) {
            let kind = tree.kind(node);
            for child in kind.children() {
                assert!(
                    child.optional || (child.present)(tree, node),
                    "{kind:?} {node:?} has no error but lacks its `{}`",
                    child.name
                );
            }
            for rule in kind.tokens() {
                let held = match *rule {
                    TokenRule::Kind {
                        first,
                        glued,
                        optional,
                    } => optional || tree.holds(node, lexed, first, glued),
                    TokenRule::Flag { .. } => true,
                    TokenRule::Field { reads, .. } => tree
                        .own_pairs(node, lexed)
                        .any(|(first, glued)| reads(first, glued).is_some()),
                };
                assert!(held, "{kind:?} {node:?} has no error but lacks its {rule}");
            }
            // And the converse: the grammar declares every token the rule holds.
            let mut spanned = false;
            for (first, glued) in tree.own_pairs(node, lexed) {
                if spanned {
                    spanned = false;
                    continue;
                }
                let declared = kind.tokens().iter().find_map(|rule| match *rule {
                    TokenRule::Kind {
                        first: kind,
                        glued: pair,
                        ..
                    } if kind == first && (pair.is_none() || pair == glued) => Some(pair.is_some()),
                    TokenRule::Flag { kind, .. } if kind == first => Some(false),
                    TokenRule::Field { reads, .. } => reads(first, glued),
                    _ => None,
                });
                let Some(spans) = declared else {
                    panic!("{kind:?} {node:?} holds {first:?}, which no rule of its kind declares");
                };
                spanned = spans;
            }
        }

        let mut previous_end = first;
        for child in tree.children(node) {
            assert!(
                tree.first_token(child) >= previous_end,
                "children of {node:?} must be ordered and disjoint"
            );
            assert!(
                tree.end_token(child) <= end,
                "a child of {node:?} must stay inside its parent"
            );
            previous_end = tree.end_token(child);
            pending.push(child);
        }
    }
    assert_eq!(visited, tree.len(), "extents must partition the tree");
}

pub fn parse(source: &str, lexed: &LexedFile, parse: &Parse) {
    let (input, tree) = (parse.input(), parse.tree());
    self::tree(tree, lexed);
    assert_eq!(
        tree.reprint(lexed, source),
        source,
        "the tree is not lossless"
    );

    let mut children = tree.children(tree.root()).peekable();
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
                // A missing closer names the one token that opened its pair.
                if let ParseRecoveryKind::Closer { pair, opener } = recovery.kind {
                    assert_eq!(opener.end(), opener.start() + 1);
                    assert_eq!(lexed.kind(opener.start()), pair.opener().kind());
                }
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

/// `source` lexes and parses without evidence; `index` is a position in its significant-token
/// stream.
pub fn recovery(source: &str, original: &Front, index: usize, edit: Edit) {
    let sig = |index: usize| SigIdx::new(u32::try_from(index).expect("positions fit in u32"));
    let (edited, touched, moved, impact) = apply(source, &original.spans(), index, edit);
    let touched: Vec<RawIdx> = touched
        .iter()
        .map(|&index| original.parse.input().token(sig(index)))
        .collect();
    let after = front(&edited);
    tree(after.parse.tree(), &after.lexed);

    // A bracket edit reparents nearby statements, so only the untouched items must survive.
    if changes_delimiter(original.parse.input(), index, edit) {
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
                original.parse.input().get(sig(index)),
                shape.0,
                after.parse.evidence()
            );
        }
    } else {
        let moved: Vec<RawIdx> = moved
            .iter()
            .map(|&index| original.parse.input().token(sig(index)))
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
                original.parse.input().get(sig(index)),
                original.parse.tree().kind(node),
                shape.0,
                after.parse.evidence()
            );
        }
    }
}

pub fn format(source: &str) -> Formatted {
    let before = front(source);
    let formatted = sumi_format::format(source, &before.lexed, &before.parse)
        .unwrap_or_else(|defect| panic!("format defect on {source:?}: {}", defect.rejected));
    assert_eq!(
        sumi_text::apply(source, &formatted.edits),
        formatted.text,
        "the edits are not the text: {source:?}"
    );
    let after = front(&formatted.text);
    assert_eq!(
        rep(&formatted.text, &after.lexed, &after.parse),
        rep(source, &before.lexed, &before.parse),
        "format changed the rep: {source:?} -> {:?}",
        formatted.text
    );
    let again =
        sumi_format::format(&formatted.text, &after.lexed, &after.parse).unwrap_or_else(|defect| {
            panic!("format defect on {:?}: {}", formatted.text, defect.rejected)
        });
    assert_eq!(
        again.text, formatted.text,
        "format is not idempotent on {source:?}"
    );
    formatted
}

fn ranges(diagnostic: &sumi_frontend::Diagnostic) -> impl Iterator<Item = TextRange> + '_ {
    std::iter::once(diagnostic.primary).chain(diagnostic.labels.iter().map(|label| label.range))
}

pub fn diagnostics(parsed: &ParsedSource) {
    let source = parsed.source();
    let mut previous = None;
    let mut edits = Vec::new();
    for diagnostic in parsed.diagnostics() {
        let key = (
            diagnostic.primary.start().to_u32(),
            diagnostic.primary.end().to_u32(),
        );
        if let Some(previous) = previous {
            assert!(previous <= key, "diagnostics are not source sorted");
        }
        previous = Some(key);

        for range in ranges(diagnostic) {
            let start = range.start().to_usize();
            let end = range.end().to_usize();
            assert!(end <= source.len());
            assert!(source.is_char_boundary(start));
            assert!(source.is_char_boundary(end));
        }
        if let Some(fix) = &diagnostic.fix {
            let edit = &fix.edit;
            // A repair exposes later errors, so the error count is no oracle; the token lists are.
            if diagnostic.code == codes::EXPECTED_TOKEN {
                assert_eq!(edit.range().start(), edit.range().end());
                let kind = match edit.replacement() {
                    ")" => SyntaxKind::RParen,
                    "}" => SyntaxKind::RBrace,
                    other => panic!("unexpected closer {other:?}"),
                };
                let mut fixed = source.to_owned();
                fixed.insert_str(edit.range().start().to_usize(), edit.replacement());
                let after = lex(&fixed).expect("fixed sources fit in u32");
                let raw = after
                    .token_at(edit.range().start())
                    .expect("inserted token");
                assert_eq!(after.range(raw).start(), edit.range().start());
                assert_eq!(after.kind(raw), kind);
                assert_eq!(after.text(&fixed, raw), edit.replacement());
                let rank = after
                    .indices()
                    .take_while(|&token| token < raw)
                    .filter(|&token| kept(after.kind(token)))
                    .count();
                let mut tokens = preserved(&after, &fixed);
                tokens.remove(rank);
                assert_eq!(tokens, preserved(parsed.lexed(), source), "{source:?}");
            }
            let range = edit.range();
            let start = range.start().to_usize();
            let end = range.end().to_usize();
            assert!(start <= end && end <= source.len());
            assert!(source.is_char_boundary(start));
            assert!(source.is_char_boundary(end));
            edits.push(edit);
        }
    }

    edits.sort_by_key(|edit| (edit.range().start(), edit.range().end()));
    let mut applied_end = None;
    let mut applied = Vec::new();
    for edit in edits {
        if applied_end.is_some_and(|end| end > edit.range().start()) {
            continue;
        }
        applied_end = Some(edit.range().end());
        applied.push(edit);
    }
    let fixed = sumi_text::apply(source, applied);
    let reparsed = parse_source(fixed.into()).expect("fixed sources fit in u32");
    tree(reparsed.parse().tree(), reparsed.lexed());
}

fn kept(kind: SyntaxKind) -> bool {
    !kind.is_trivia() || kind == SyntaxKind::LineComment
}

fn preserved(lexed: &LexedFile, source: &str) -> Vec<(SyntaxKind, String)> {
    lexed
        .indices()
        .filter(|&index| kept(lexed.kind(index)))
        .map(|index| (lexed.kind(index), lexed.text(source, index).to_owned()))
        .collect()
}

pub fn semantics(analysis: &Analysis) {
    use sumi_hir::FunctionId;
    let source = analysis.parsed().source();
    if analysis.parsed().diagnostics().is_empty() {
        use sumi_syntax::ast::{AstNode, SourceFile, View};
        let tree = analysis.parsed().parse().tree();
        let mut declarations: Vec<_> = SourceFile::cast(tree, tree.root())
            .unwrap()
            .items(tree)
            .map(|item| {
                tree.byte_range(item.node(), analysis.parsed().lexed())
                    .text(source)
            })
            .collect();
        declarations.reverse();
        let reversed = sumi_hir::analyze(parse_source(declarations.join("\n").into()).unwrap());
        assert!(reversed.parsed().diagnostics().is_empty());
        assert_eq!(analysis.functions().len(), reversed.functions().len());
        let count = analysis.functions().len();
        for (index, (a, b)) in analysis
            .functions()
            .iter()
            .zip(reversed.functions().iter().rev())
            .enumerate()
        {
            assert_eq!(
                a.name().map(|name| analysis.text(name)),
                b.name().map(|name| reversed.text(name))
            );
            assert_eq!(a.signature(), b.signature());
            assert_eq!(
                analysis.ranges(FunctionId::new(index)),
                reversed.ranges(FunctionId::new(count - 1 - index))
            );
            assert_eq!(a.complete(), b.complete());
        }
        graph(&reversed);
    }
    assert_eq!(
        analysis.is_valid(),
        !analysis.diagnostics().iter().any(|d| d.is_error())
    );
    let all = analysis.diagnostics();
    let syntactic: Vec<_> = all
        .iter()
        .filter(|d| !sumi_hir::Analysis::is_semantic(d))
        .collect();
    assert_eq!(syntactic.len(), analysis.parsed().diagnostics().len());
    assert!(
        syntactic
            .iter()
            .zip(analysis.parsed().diagnostics())
            .all(|(listed, own)| *listed == own)
    );
    assert!(all.is_sorted_by_key(|d| d.primary.start()));
    for pair in all.windows(2) {
        if pair[0].primary.start() == pair[1].primary.start() {
            assert!(
                !sumi_hir::Analysis::is_semantic(&pair[0])
                    || sumi_hir::Analysis::is_semantic(&pair[1])
            );
        }
    }
    for diagnostic in analysis.diagnostics() {
        for range in ranges(diagnostic) {
            assert!(source.is_char_boundary(range.start().to_usize()));
            assert!(source.is_char_boundary(range.end().to_usize()));
        }
    }
    graph(analysis);
}

fn typed(analysis: &Analysis) {
    use sumi_hir::{BinaryOp, CmpOp, FunctionId, NodeId, Op, Ty};
    let graph = analysis.graph();
    for (index, function) in analysis.functions().iter().enumerate() {
        if !function.complete() {
            continue;
        }
        let signature = function
            .signature()
            .expect("a complete function has a signature");
        let run = graph.run(FunctionId::new(index));
        let ty = |node: NodeId| analysis.ty(node);
        for node in run.nodes() {
            let entry = graph.node(node);
            let own = ty(node);
            let inputs = graph.inputs(node);
            let values = graph.input_values(node);
            match &entry.op {
                Op::Entry
                | Op::Then
                | Op::Else
                | Op::Return
                | Op::Sequence
                | Op::Observe { .. }
                | Op::After
                | Op::Result { .. } => continue,
                Op::Hole => panic!("a hole in a complete function"),
                Op::Int(_) => assert_eq!(own, Some(Ty::Int)),
                Op::LoopIndex => {
                    assert_eq!(own, Some(Ty::Int));
                    for (position, &input) in inputs.iter().enumerate() {
                        if values[position] {
                            assert_eq!(ty(input), Some(Ty::Int));
                        }
                    }
                }
                Op::Carry { declaration } => {
                    assert_eq!(own, ty(*declaration));
                    assert_eq!(own, ty(inputs[0]));
                }
                Op::Loop(id) => {
                    assert_eq!(own, Some(Ty::Unit));
                    let body = graph.region(graph.loop_(*id).body);
                    if values.iter().all(|&value| value) && body.result_has_value() {
                        assert_eq!(ty(body.result()), Some(Ty::Unit));
                    }
                }
                Op::LoopValue { loop_, index } => {
                    let (header, next) = graph.loop_(*loop_).carried[*index as usize];
                    assert_eq!(own, ty(header));
                    assert_eq!(own, ty(next));
                }
                Op::Bool(_) => assert_eq!(own, Some(Ty::Bool)),
                Op::Unit => assert_eq!(own, Some(Ty::Unit)),
                Op::Unused => {
                    if values[0] {
                        assert_eq!(ty(inputs[0]), Some(Ty::Unit));
                    }
                    assert_eq!(own, None);
                    continue;
                }
                Op::Param { index, ty } => {
                    assert_eq!(*ty, Some(signature.params[*index as usize]));
                    assert_eq!(own, *ty);
                }
                Op::Neg => {
                    if values[0] {
                        assert_eq!(ty(inputs[0]), Some(Ty::Int));
                    }
                    assert_eq!(own, Some(Ty::Int));
                }
                Op::Not => {
                    if values[0] {
                        assert_eq!(ty(inputs[0]), Some(Ty::Bool));
                    }
                    assert_eq!(own, Some(Ty::Bool));
                }
                Op::Binary(op) => {
                    assert_eq!(own, Some(op.result()));
                    match op {
                        BinaryOp::Cmp(CmpOp::Eq | CmpOp::Ne) => {
                            for (index, &input) in inputs.iter().enumerate() {
                                if values[index] {
                                    assert!(matches!(ty(input), Some(Ty::Int | Ty::Bool)));
                                }
                            }
                            if values.iter().all(|&value| value) {
                                assert_eq!(ty(inputs[0]), ty(inputs[1]));
                            }
                        }
                        _ => {
                            for (index, &input) in inputs.iter().enumerate() {
                                if values[index] {
                                    assert_eq!(ty(input), Some(Ty::Int));
                                }
                            }
                        }
                    }
                }
                Op::And { rhs } | Op::Or { rhs } => {
                    if values[0] {
                        assert_eq!(own, Some(Ty::Bool));
                        assert_eq!(ty(inputs[0]), Some(Ty::Bool));
                    } else {
                        assert_eq!(own, None);
                    }
                    if graph.region(*rhs).result_has_value() {
                        assert_eq!(ty(graph.region(*rhs).result()), Some(Ty::Bool));
                    }
                }
                Op::Copy { declared } => {
                    if values[0] {
                        assert_eq!(own, ty(inputs[0]));
                    }
                    if let Some((declared, _)) = declared {
                        assert_eq!(own, Some(*declared));
                    }
                }
                Op::Assign { declaration } => {
                    assert_eq!(own, ty(*declaration));
                    if values[0] {
                        assert_eq!(ty(inputs[0]), own);
                    }
                }
                Op::Phi {
                    declaration,
                    contexts: _,
                } => {
                    assert_eq!(own, ty(*declaration));
                    if values[0] {
                        assert_eq!(ty(inputs[0]), Some(Ty::Bool));
                    }
                    for (index, &input) in inputs[1..].iter().enumerate() {
                        if values[index + 1] {
                            assert_eq!(ty(input), own);
                        }
                    }
                }
                Op::Refine { .. } | Op::Exactly(_) => {
                    if values[0] {
                        assert_eq!(own, ty(inputs[0]));
                    }
                }
                Op::Join { then, else_ } => {
                    if values[0] {
                        assert_eq!(ty(inputs[0]), Some(Ty::Bool));
                    } else {
                        continue;
                    }
                    let then_value = graph.region(*then).result_has_value();
                    let else_value =
                        else_.is_none_or(|region| graph.region(region).result_has_value());
                    if !then_value && !else_value {
                        assert_eq!(own, None);
                        continue;
                    }
                    if then_value {
                        assert_eq!(ty(graph.region(*then).result()), own);
                    }
                    match else_ {
                        Some(else_) if graph.region(*else_).result_has_value() => {
                            assert_eq!(ty(graph.region(*else_).result()), own)
                        }
                        Some(_) => {}
                        None => assert_eq!(own, Some(Ty::Unit)),
                    }
                }
                Op::Call(callee) => {
                    let callable = graph.callable(*callee);
                    let signature = analysis
                        .function(callable.function)
                        .signature()
                        .expect("a called function has a signature");
                    assert_eq!(signature.params, callable.params);
                    assert_eq!(own, Some(signature.result));
                    assert_eq!(inputs.len(), callable.params.len());
                    for (index, (&input, &param)) in inputs.iter().zip(&callable.params).enumerate()
                    {
                        if values[index] {
                            assert_eq!(ty(input), Some(param));
                        }
                    }
                }
            }
            assert!(own.is_some() || values.iter().any(|&value| !value));
        }
        assert_eq!(ty(run.result()), Some(signature.result));
    }
}

fn graph(analysis: &Analysis) {
    use sumi_hir::{NodeId, Op};
    let graph = analysis.graph();
    for id in graph.node_ids() {
        let node = graph.node(id);
        let inputs = graph.inputs(id);
        for input in inputs {
            assert!(input.index() < id.index());
        }
        let arity = match node.op {
            Op::Int(_) | Op::Bool(_) | Op::Param { .. } | Op::Entry => Some(0),
            Op::Unit
            | Op::Unused
            | Op::Copy { .. }
            | Op::Assign { .. }
            | Op::Carry { .. }
            | Op::LoopValue { .. }
            | Op::Neg
            | Op::Not
            | Op::Exactly(_) => Some(1),
            Op::Phi { .. } => Some(3),
            Op::And { .. } | Op::Or { .. } | Op::Join { .. } => Some(1),
            Op::Observe { .. } => Some(2),
            Op::Binary(_)
            | Op::LoopIndex
            | Op::Loop(_)
            | Op::Refine { .. }
            | Op::Then
            | Op::Else
            | Op::Return
            | Op::Sequence
            | Op::After => Some(2),
            Op::Hole | Op::Call(_) | Op::Result { .. } => None,
        };
        if let Some(arity) = arity {
            assert_eq!(inputs.len(), arity);
        }
        for (index, &input) in inputs.iter().enumerate() {
            if matches!(
                graph.node(input).op,
                Op::Entry | Op::Then | Op::Else | Op::After
            ) {
                assert!(matches!(
                    (&node.op, index),
                    (Op::Unit, 0)
                        | (Op::Then | Op::Else | Op::Return | Op::Observe { .. }, 1)
                        | (Op::After, 0 | 1)
                ));
            }
        }
        if node.name.is_some() {
            assert!(matches!(
                node.op,
                Op::Param { .. } | Op::Copy { .. } | Op::Hole | Op::LoopIndex
            ));
        }
        if analysis.is_valid() {
            assert!(!matches!(node.op, Op::Hole));
            if !matches!(
                node.op,
                Op::Entry
                    | Op::Then
                    | Op::Else
                    | Op::Unused
                    | Op::Sequence
                    | Op::Observe { .. }
                    | Op::After
            ) && graph.input_values(id).iter().all(|&value| value)
                && !matches!(
                    node.op,
                    Op::Join {
                        then,
                        else_: Some(else_),
                    } if !graph.region(then).result_has_value()
                        && !graph.region(else_).result_has_value()
                )
            {
                assert!(analysis.ty(id).is_some());
            }
        }
    }
    typed(analysis);
    // A callable's parameters are its run's, a repeated name's type kept in the signature alone.
    for callable in graph.callables() {
        let run = graph.run(callable.function);
        assert_eq!(callable.params.len(), run.params().len());
        for (param, &declared) in run.params().zip(&callable.params) {
            let Op::Param { index, ty } = graph.node(param).op else {
                panic!("a run's parameters are parameter nodes")
            };
            assert_eq!(callable.params[index as usize], declared);
            assert!(ty.is_none_or(|ty| ty == declared));
        }
    }
    let mut owner = vec![None; graph.nodes().len()];
    assert_eq!(graph.runs().len(), analysis.functions().len());
    for (index, function) in graph.runs().iter().enumerate() {
        let mut run = function.nodes();
        assert_eq!(run.next(), Some(function.entry()));
        assert!(matches!(graph.node(function.entry()).op, Op::Entry));
        for (position, param) in function.params().enumerate() {
            assert_eq!(run.next(), Some(param));
            assert!(
                matches!(graph.node(param).op, Op::Param { index, .. } if index as usize == position)
            );
        }
        let region = graph.region(function.region());
        assert_eq!(region.context, function.entry());
        for node in region.nodes() {
            assert_eq!(run.next(), Some(node));
        }
        match run.next() {
            None => assert_eq!(function.result(), region.result()),
            Some(copy) => {
                assert_eq!(copy, function.result());
                match graph.node(copy).op {
                    Op::Copy { .. } => assert_eq!(graph.inputs(copy), [region.result()]),
                    Op::Result { .. } => {
                        let outcome = graph.inputs(copy)[0];
                        assert!(
                            outcome == region.result()
                                || matches!(graph.node(outcome).op, Op::Sequence)
                        );
                    }
                    _ => panic!("a run ends in its result wrapper"),
                }
                assert_eq!(run.next(), None);
            }
        }
        for node in function.nodes() {
            owner[node.index()] = Some(index);
        }
    }
    for node in graph.node_ids() {
        let check = |reference: NodeId| {
            assert!(reference.index() < node.index());
            assert_eq!(owner[reference.index()], owner[node.index()]);
        };
        match &graph.node(node).op {
            Op::Assign { declaration } | Op::Carry { declaration } => check(*declaration),
            Op::Phi {
                declaration,
                contexts,
            } => {
                check(*declaration);
                contexts.iter().copied().for_each(check);
            }
            _ => {}
        }
    }
    for id in graph.loop_ids() {
        let loop_ = graph.loop_(id);
        let body = graph.region(loop_.body);
        let nodes: Vec<_> = body.nodes().collect();
        assert!(nodes.contains(&loop_.index));
        assert!(matches!(graph.node(loop_.index).op, Op::LoopIndex));
        assert_eq!(
            owner[loop_.index.index()],
            owner[loop_.continuation.index()]
        );
        assert_eq!(owner[loop_.index.index()], owner[loop_.empty.index()]);
        for &(header, next) in &loop_.carried {
            assert!(nodes.contains(&header));
            assert!(matches!(graph.node(header).op, Op::Carry { .. }));
            assert_eq!(owner[header.index()], owner[next.index()]);
            assert_eq!(owner[header.index()], owner[loop_.index.index()]);
            assert_eq!(graph.inputs(header).len(), 1);
            assert!(graph.inputs(header)[0].index() < loop_.index.index());
        }
    }
    let mut spans: Vec<(usize, usize)> = Vec::new();
    for id in graph.region_ids() {
        let region = graph.region(id);
        let result = region.result().index();
        assert!(!matches!(
            graph.node(region.result()).op,
            Op::Entry | Op::Then | Op::Else | Op::Unused
        ));
        assert_eq!(owner[region.context.index()], owner[result]);
        assert!(owner[result].is_some());
        let Some(first) = region.nodes().next() else {
            continue;
        };
        let (start, end) = (first.index(), first.index() + region.nodes().len());
        assert!(region.context.index() < start);
        assert!(result < end);
        for &(s, e) in &spans {
            let disjoint = end <= s || e <= start;
            let nested = (s <= start && end <= e) || (start <= s && e <= end);
            assert!(disjoint || nested);
        }
        spans.push((start, end));
    }
}

#[derive(Default)]
pub struct Runs {
    pub finished: usize,
    pub abandoned: usize,
}

pub fn run(program: Program<'_>) -> Runs {
    use sumi_hir::{Bools, Int, Ints, Ty, Value};

    const STEPS: u64 = 1 << 17;
    /// The step budget is not enough: squaring along a recursion doubles the width every frame, and
    /// one multiplication then outlasts it.
    const DIGITS: usize = 300;
    const TUPLES: usize = 32;

    fn contains(ints: &Ints, value: &Int) -> bool {
        !ints.is_empty()
            && ints.lo().is_none_or(|lo| lo <= *value)
            && ints.hi().is_none_or(|hi| *value <= hi)
            && (*value != Int::from(0) || ints.contains_zero())
    }
    fn admits(bools: Bools, value: bool) -> bool {
        if value {
            bools.may_true()
        } else {
            bools.may_false()
        }
    }
    fn points(ints: &Ints) -> Vec<Int> {
        if ints.is_empty() {
            return Vec::new();
        }
        let far = Int::from(8);
        let (lo, hi) = match (ints.lo(), ints.hi()) {
            (Some(lo), Some(hi)) => (lo, hi),
            (Some(lo), None) => (lo.clone(), &lo + &far),
            (None, Some(hi)) => (&hi - &far, hi),
            (None, None) => (-&far, far),
        };
        let one = Int::from(1);
        let mut points = vec![
            lo.clone(),
            hi.clone(),
            &lo + &one,
            &hi - &one,
            Int::from(-1),
            Int::from(0),
            one,
        ];
        points.retain(|point| contains(ints, point));
        points.sort();
        points.dedup();
        points
    }

    let wide: Int = format!("1{}", "0".repeat(DIGITS)).parse().unwrap();
    let too_wide = |value: &Value| matches!(value, Value::Int(v) if *v > wide || *v < -&wide);
    let mut runs = Runs::default();
    for (id, _) in program.functions() {
        let signature = program.signature(id);
        let ranges = program.ranges(id);
        if !ranges.params.iter().all(|may| may.live()) {
            continue;
        }
        let mut tuples: Vec<Vec<Value>> = vec![Vec::new()];
        for (may, &ty) in ranges.params.iter().zip(&signature.params) {
            let values: Vec<Value> = match ty {
                Ty::Int => points(&may.ints).into_iter().map(Value::Int).collect(),
                Ty::Bool => [true, false]
                    .into_iter()
                    .filter(|&b| admits(may.bools, b))
                    .map(Value::Bool)
                    .collect(),
                Ty::Unit => vec![Value::Unit],
            };
            assert!(!values.is_empty(), "a live parameter has values");
            tuples = tuples
                .iter()
                .flat_map(|tuple| {
                    values.iter().map(|value| {
                        let mut tuple = tuple.clone();
                        tuple.push(value.clone());
                        tuple
                    })
                })
                .take(TUPLES)
                .collect();
        }
        for args in tuples {
            let mut machine = program.machine(id, &args);
            let mut remaining = STEPS;
            let outcome = loop {
                if let Some(outcome) = machine.step() {
                    break Some(outcome.clone());
                }
                remaining -= 1;
                if remaining == 0 || machine.latest().is_some_and(too_wide) {
                    break None;
                }
            };
            let Some(outcome) = outcome else {
                runs.abandoned += 1;
                continue;
            };
            runs.finished += 1;
            let value = match outcome {
                Ok(value) => value,
                Err(refusal) => panic!("f{} was refused: {refusal:?}", id.index()),
            };
            assert_eq!(program.machine(id, &args).run(), Ok(value.clone()));
            assert_eq!(program.evaluate(id, &args), value);
            assert_eq!(value.ty(), signature.result);
            let within = match &value {
                Value::Int(value) => contains(&ranges.result.ints, value),
                Value::Bool(value) => admits(ranges.result.bools, *value),
                Value::Unit => ranges.result.unit,
            };
            assert!(
                within,
                "f{}({args:?}) = {value} outside its result set",
                id.index()
            );
        }
    }
    runs
}
