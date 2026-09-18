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

use sumi_format::{format, rep};
use sumi_frontend::{ParsedSource, codes, parse_source};
use sumi_lexer::{LexedFile, RawIdx, SyntaxKind, lex};
use sumi_syntax::{
    BRACKET_PAIRS, NodeKind, Parse, ParseAnchor, ParseEvidence, ParserInput, SigIdx, parse,
};
use sumi_test::{Edit, Front, apply, changes_delimiter, front};
use sumi_text::{FileId, Span};

/// The file every fuzzed source stands for.
pub const FILE: FileId = FileId::new(0);

/// The HIR property's diagnostic-backed acceptance, source provenance, and
/// completeness, through the read-only public API.
pub fn check_semantics(parsed: ParsedSource) {
    use sumi_hir::FunctionId;
    let analysis = sumi_hir::analyze(parsed);
    let source = analysis.parsed().source();
    // Mirror the HIR property: declaration order cannot choose a public type
    // or make an incomplete body complete. Only reorder clean syntax.
    if analysis.parsed().diagnostics().is_empty() {
        use sumi_syntax::ast::{AstNode, SourceFile};
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
        let reversed =
            sumi_hir::analyze(parse_source(FILE, declarations.join("\n").into()).unwrap());
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
            assert_eq!(
                a.signature().map(|s| (&s.params, s.result)),
                b.signature().map(|s| (&s.params, s.result))
            );
            assert_eq!(
                analysis.ranges(FunctionId::new(index)),
                reversed.ranges(FunctionId::new(count - 1 - index))
            );
            assert_eq!(a.complete(), b.complete());
        }
    }
    assert_eq!(analysis.is_valid(), analysis.diagnostics().is_empty());
    // The frontend's diagnostics are among the analysis's, in source order,
    // the frontend's first where both stand at one position.
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
    assert!(all.is_sorted_by_key(|d| d.primary.range().start()));
    for pair in all.windows(2) {
        if pair[0].primary.range().start() == pair[1].primary.range().start() {
            assert!(
                !sumi_hir::Analysis::is_semantic(&pair[0])
                    || sumi_hir::Analysis::is_semantic(&pair[1])
            );
        }
    }
    check_graph(&analysis);
    for diagnostic in analysis.diagnostics() {
        for span in spans(diagnostic) {
            assert_eq!(span.file(), analysis.parsed().file());
            assert!(source.is_char_boundary(span.range().start().to_usize()));
            assert!(source.is_char_boundary(span.range().end().to_usize()));
        }
    }
    check_typed(&analysis);
}

/// The typed shape of every complete function, restating the HIR unit
/// tests' `typed_invariant`: each value has a type, no hole stands in it,
/// and each operator's type agrees with its inputs', a call's with its
/// callee's signature, a join's with its arms', and a copy's or a
/// narrowed read's with what it reads.
pub fn check_typed(analysis: &sumi_hir::Analysis) {
    use sumi_hir::{BinaryOp, FunctionId, NodeId, Op, Ty};
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
            match &entry.op {
                Op::Entry | Op::Then | Op::Else => continue,
                Op::Hole => panic!("a hole in a complete function"),
                Op::Int(_) => assert_eq!(own, Some(Ty::Int)),
                Op::Bool(_) => assert_eq!(own, Some(Ty::Bool)),
                Op::Unit => assert_eq!(own, Some(Ty::Unit)),
                Op::Param(position) => {
                    assert_eq!(own, Some(signature.params[*position as usize]));
                }
                Op::Neg => {
                    assert_eq!(ty(inputs[0]), Some(Ty::Int));
                    assert_eq!(own, Some(Ty::Int));
                }
                Op::Not => {
                    assert_eq!(ty(inputs[0]), Some(Ty::Bool));
                    assert_eq!(own, Some(Ty::Bool));
                }
                Op::Binary(op) => {
                    assert_eq!(own, Some(op.result()));
                    match op {
                        BinaryOp::Eq | BinaryOp::Ne => {
                            assert!(matches!(ty(inputs[0]), Some(Ty::Int | Ty::Bool)));
                            assert_eq!(ty(inputs[0]), ty(inputs[1]));
                        }
                        _ => {
                            assert_eq!(ty(inputs[0]), Some(Ty::Int));
                            assert_eq!(ty(inputs[1]), Some(Ty::Int));
                        }
                    }
                }
                Op::And { rhs } | Op::Or { rhs } => {
                    assert_eq!(own, Some(Ty::Bool));
                    assert_eq!(ty(inputs[0]), Some(Ty::Bool));
                    assert_eq!(ty(graph.region(*rhs).result()), Some(Ty::Bool));
                }
                Op::Copy { declared } => {
                    assert_eq!(own, ty(inputs[0]));
                    if let Some((declared, _)) = declared {
                        assert_eq!(own, Some(*declared));
                    }
                }
                Op::Refine { .. } | Op::Exactly(_) => assert_eq!(own, ty(inputs[0])),
                Op::Join { then, else_ } => {
                    assert_eq!(ty(inputs[0]), Some(Ty::Bool));
                    assert_eq!(ty(graph.region(*then).result()), own);
                    match else_ {
                        Some(else_) => assert_eq!(ty(graph.region(*else_).result()), own),
                        None => assert_eq!(own, Some(Ty::Unit)),
                    }
                }
                Op::Call(callee) => {
                    let callee = analysis
                        .function(*callee)
                        .signature()
                        .expect("a called function has a signature");
                    assert_eq!(own, Some(callee.result));
                    assert_eq!(inputs.len(), callee.params.len());
                    for (&input, &param) in inputs.iter().zip(&callee.params) {
                        assert_eq!(ty(input), Some(param));
                    }
                }
            }
            assert!(own.is_some());
        }
        assert_eq!(ty(run.result()), Some(signature.result));
    }
}

/// The graph's shape, restating the HIR unit tests' `graph_invariant`:
/// inputs precede their readers; a function's run is its entry, a node
/// per parameter, its body region, and a copy for a declared result;
/// regions nest; every op reads what its kind takes; an accepted file has
/// a type on every value and no hole.
pub fn check_graph(analysis: &sumi_hir::Analysis) {
    use sumi_hir::Op;
    let graph = analysis.graph();
    for id in graph.node_ids() {
        let node = graph.node(id);
        let inputs = graph.inputs(id);
        for input in inputs {
            assert!(input.index() < id.index());
        }
        let arity = match node.op {
            Op::Int(_) | Op::Bool(_) | Op::Param(_) | Op::Entry => Some(0),
            Op::Unit | Op::Copy { .. } | Op::Neg | Op::Not | Op::Exactly(_) => Some(1),
            Op::And { .. } | Op::Or { .. } | Op::Join { .. } => Some(1),
            Op::Binary(_) | Op::Refine { .. } | Op::Then | Op::Else => Some(2),
            Op::Hole | Op::Call(_) => None,
        };
        if let Some(arity) = arity {
            assert_eq!(inputs.len(), arity);
        }
        for &input in inputs {
            if matches!(graph.node(input).op, Op::Entry | Op::Then | Op::Else) {
                assert!(matches!(node.op, Op::Then | Op::Else | Op::Unit));
            }
        }
        if node.name.is_some() {
            assert!(matches!(node.op, Op::Param(_) | Op::Copy { .. } | Op::Hole));
        }
        if analysis.is_valid() {
            assert!(!matches!(node.op, Op::Hole));
            if !matches!(node.op, Op::Entry | Op::Then | Op::Else) {
                assert!(analysis.ty(id).is_some());
            }
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
            assert!(matches!(graph.node(param).op, Op::Param(i) if i as usize == position));
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
                assert!(matches!(graph.node(copy).op, Op::Copy { .. }));
                assert_eq!(graph.inputs(copy), [region.result()]);
                assert_eq!(run.next(), None);
            }
        }
        for node in function.nodes() {
            owner[node.index()] = Some(index);
        }
    }
    let mut spans: Vec<(usize, usize)> = Vec::new();
    for id in graph.region_ids() {
        let region = graph.region(id);
        let result = region.result().index();
        assert!(!matches!(
            graph.node(region.result()).op,
            Op::Entry | Op::Then | Op::Else
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

/// The machine property: every live function of an accepted file, run at a
/// few points inside the parameter sets the analysis proved, stays within
/// its claims. The value lies in the result set and has the signature's
/// type, and the machine refused nothing, since a zero divisor or a frame
/// past the depth bound would be a refusal. A run past the step budget, or
/// holding an integer too wide to keep multiplying, is abandoned;
/// everything before that was checked. Restates `machine.rs` in
/// `sumi-hir`'s tests.
pub fn check_run(parsed: ParsedSource) {
    use sumi_hir::{Bools, Int, Ints, Ty, Value};

    /// Values computed, abandoning past this many.
    const STEPS: u64 = 1 << 17;
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

    let analysis = sumi_hir::analyze(parsed);
    let Some(program) = analysis.program() else {
        return;
    };
    let wide: Int = format!("1{}", "0".repeat(DIGITS)).parse().unwrap();
    let too_wide = |value: &Value| matches!(value, Value::Int(v) if *v > wide || *v < -&wide);
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
            let finished = loop {
                if machine.step() {
                    break true;
                }
                if machine.steps() >= STEPS || machine.latest().is_some_and(too_wide) {
                    break false;
                }
            };
            if !finished {
                continue;
            }
            let value = match machine.outcome().expect("a finished run has its outcome") {
                Ok(value) => value.clone(),
                Err(refusal) => panic!("f{} was refused: {refusal:?}", id.index()),
            };
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
}

/// `lex` partitions the source: tokens are nonempty, contiguous, on
/// character boundaries, and reproduce it byte for byte; every lexical
/// error sits inside its token; every `Error` token has one; and only a
/// line break spans lines.
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
            input.get(opener) != Some(SyntaxKind::LBrace) && input.partner(opener).is_some()
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
        if lexed.kind(index) == SyntaxKind::Whitespace {
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
pub fn check_tree(parse: &Parse, lexed: &LexedFile) {
    let (input, tree) = (parse.input(), parse.tree());
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
    assert_eq!(tree.first_token(root), RawIdx::new(0));
    assert_eq!(tree.end_token(root), lexed.end());

    if !lexed.is_empty() {
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

/// The parse is lossless, attaches no significant token to the root
/// itself, and anchors every piece of evidence in bounds: present syntax
/// and skipped ranges are nonempty, and missing syntax names the exact
/// trivia interval between two significant tokens.
pub fn check_parse(source: &str, lexed: &LexedFile, parse: &Parse) {
    let (input, tree) = (parse.input(), parse.tree());
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

/// The primary span of `diagnostic` and every label's.
fn spans(diagnostic: &sumi_frontend::Diagnostic) -> impl Iterator<Item = Span> + '_ {
    std::iter::once(diagnostic.primary).chain(diagnostic.labels.iter().map(|label| label.span))
}

/// Every canonical diagnostic names the parsed file, in source order, with
/// in-bounds labels on character boundaries, and a fix of nonempty,
/// ordered, disjoint edits; applying every non-overlapping fix leaves a
/// source the frontend still parses.
pub fn check_diagnostics(parsed: &ParsedSource) {
    let source = parsed.source();
    let mut previous = None;
    let mut edits = Vec::new();
    for diagnostic in parsed.diagnostics() {
        let key = (
            diagnostic.primary.range().start().to_u32(),
            diagnostic.primary.range().end().to_u32(),
        );
        if let Some(previous) = previous {
            assert!(previous <= key, "diagnostics are not source sorted");
        }
        previous = Some(key);

        for span in spans(diagnostic) {
            assert_eq!(span.file(), parsed.file());
            let start = span.range().start().to_usize();
            let end = span.range().end().to_usize();
            assert!(end <= source.len());
            assert!(source.is_char_boundary(start));
            assert!(source.is_char_boundary(end));
        }
        if let Some(fix) = &diagnostic.fix {
            let edit = &fix.edit;
            // Match the frontend property: each closer adds exactly its
            // code token and preserves all existing tokens and comments.
            // Nested same-kind repairs can legitimately be reoffered and
            // expose later errors, so do not compare global error counts.
            if diagnostic.code == codes::EXPECTED_TOKEN {
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
            let range = edit.range();
            let start = range.start().to_usize();
            let end = range.end().to_usize();
            assert!(start <= end && end <= source.len());
            assert!(source.is_char_boundary(start));
            assert!(source.is_char_boundary(end));
            edits.push(edit);
        }
    }

    // Apply every fix as the corpus runner does, dropping the later of two
    // that overlap, and parse what is left.
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
    let reparsed = parse_source(parsed.file(), fixed.into()).expect("fixed inputs fit in u32");
    check_tree(reparsed.parse(), reparsed.lexed());
}

/// The formatter's contract: the rep is kept, the edits are the text, a
/// second pass changes nothing, and no defect. Restates the
/// `sumi-format` formatting properties.
pub fn check_format(source: &str, lexed: &LexedFile, parsed: &Parse) {
    let before = rep(source, lexed, parsed);
    let formatted = format(source, lexed, parsed)
        .unwrap_or_else(|defect| panic!("format defect on {source:?}: {}", defect.rejected));
    assert_eq!(
        sumi_text::apply(source, &formatted.edits),
        formatted.text,
        "the edits are not the text: {source:?}"
    );
    let after_lexed = lex(&formatted.text).expect("formatted inputs fit in u32");
    let after = parse(ParserInput::new(&after_lexed));
    assert_eq!(
        rep(&formatted.text, &after_lexed, &after),
        before,
        "format changed the rep: {source:?} -> {:?}",
        formatted.text
    );
    let again = format(&formatted.text, &after_lexed, &after).unwrap_or_else(|defect| {
        panic!("format defect on {:?}: {}", formatted.text, defect.rejected)
    });
    assert_eq!(
        again.text, formatted.text,
        "format is not idempotent on {source:?}"
    );
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
    check_tree(&original.parse, &original.lexed);
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
        .map(|&index| original.parse.input().token(sig(index)))
        .collect();
    let after = front(&edited);
    check_tree(&after.parse, &after.lexed);

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
