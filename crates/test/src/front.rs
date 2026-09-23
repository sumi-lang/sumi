//! The lexer's and parser's products for one test source, and the spelling of parse evidence the
//! snapshots and the parser tests share.

use sumi_lexer::{LexedFile, SyntaxKind, lex};
use sumi_syntax::{
    NodeIdx, NodeKind, Parse, ParseEvidence, ParseRecoveryKind, ParserInput, RawIdx, parse,
};

pub struct Front {
    pub lexed: LexedFile,
    pub parse: Parse,
}

pub fn front(source: &str) -> Front {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(ParserInput::new(&lexed));
    Front { lexed, parse }
}

impl Front {
    pub fn input(&self) -> &ParserInput {
        self.parse.input()
    }

    /// Byte spans of the significant tokens.
    pub fn spans(&self) -> Vec<(usize, usize)> {
        let input = self.input();
        input
            .indices()
            .map(|index| {
                let range = self.lexed.range(input.token(index));
                (range.start().to_usize(), range.end().to_usize())
            })
            .collect()
    }

    /// The byte span of a node.
    pub fn node_span(&self, node: NodeIdx) -> (usize, usize) {
        let range = self.parse.tree().byte_range(node, &self.lexed);
        (range.start().to_usize(), range.end().to_usize())
    }

    /// The node's text and its subtree in preorder, each kind with a byte span relative to the
    /// node's start.
    pub fn shape(&self, source: &str, node: NodeIdx) -> (String, Vec<(NodeKind, usize, usize)>) {
        let tree = self.parse.tree();
        let (base, stop) = self.node_span(node);
        let nodes = (node.to_usize()..node.to_usize() + tree.subtree_len(node))
            .map(|index| NodeIdx::new(index as u32))
            .map(|node| {
                let (start, end) = self.node_span(node);
                (tree.kind(node), start - base, end - base)
            })
            .collect();
        (source[base..stop].to_owned(), nodes)
    }

    /// The items, and their bodies' statements, that cover no token in `touched`. A block whose `{`
    /// is in `moved` contributes none, since the edit reparents them. Nor does a statement opening
    /// with `{` right after a touched one that is `takeable`: a required block may follow a line
    /// break, so an edited `if` or `for` can take that one's.
    pub fn guarded(
        &self,
        touched: &[RawIdx],
        moved: &[RawIdx],
        takeable: impl Fn(NodeIdx) -> bool,
    ) -> Vec<NodeIdx> {
        let tree = self.parse.tree();
        let covers = |node: NodeIdx| {
            touched
                .iter()
                .any(|&token| tree.first_token(node) <= token && token < tree.end_token(node))
        };
        let mut nodes = Vec::new();
        for item in tree.children(tree.root()) {
            nodes.push(item);
            for child in tree.children(item) {
                if tree.kind(child) == NodeKind::Block && !moved.contains(&tree.first_token(child))
                {
                    let mut after_touched = false;
                    for statement in tree.children(child) {
                        let opens_block =
                            self.lexed.kind(tree.first_token(statement)) == SyntaxKind::LBrace;
                        let taken = after_touched
                            && opens_block
                            && !covers(statement)
                            && takeable(statement);
                        if !taken {
                            nodes.push(statement);
                        }
                        after_touched = covers(statement);
                    }
                }
            }
        }
        nodes.retain(|&node| !covers(node));
        nodes
    }
}

pub fn evidence_name(evidence: &ParseEvidence) -> String {
    match evidence {
        ParseEvidence::Recovery(recovery) => match recovery.kind {
            ParseRecoveryKind::Token(kind) => format!("Expected({kind:?})"),
            ParseRecoveryKind::Closer { pair, .. } => {
                format!("Expected({:?})", pair.closer().kind())
            }
            kind @ (ParseRecoveryKind::Item
            | ParseRecoveryKind::Statement
            | ParseRecoveryKind::Expression
            | ParseRecoveryKind::Name
            | ParseRecoveryKind::Type
            | ParseRecoveryKind::Body
            | ParseRecoveryKind::Boundary
            | ParseRecoveryKind::RangeOperator) => format!("Expected{kind:?}"),
            kind => format!("{kind:?}"),
        },
        ParseEvidence::Violation(violation) => format!("{:?}", violation.kind),
    }
}
