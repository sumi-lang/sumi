//! Semantic analysis of one file over the frontend's snapshot. Handles and ranges are relative to
//! the analysis that made them.

mod check;
pub mod codes;
mod flows;
mod lattice;
mod lower;
mod recursion;
mod solver;
mod typing;

use std::fmt;

use sumi_frontend::{Diagnostic, ParsedSource};
use sumi_text::TextRange;

pub use check::analyze;
pub use sumi_graph::{
    BinaryOp, Bools, FunctionId, Graph, Int, Ints, Machine, May, NodeId, Op, Refusal, RegionId,
    Run, Ty, Value,
};

pub struct Analysis {
    parsed: ParsedSource,
    graph: Graph,
    settled: typing::Settled,
    functions: Vec<Function>,
    diagnostics: Vec<Diagnostic>,
}

impl fmt::Debug for Analysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Analysis")
            .field("parsed", &self.parsed)
            .field("graph", &self.graph)
            .field("functions", &self.functions)
            .field("diagnostics", &self.diagnostics)
            .finish_non_exhaustive()
    }
}

impl Analysis {
    pub fn parsed(&self) -> &ParsedSource {
        &self.parsed
    }
    /// Every body is in it, holed ones too.
    pub fn graph(&self) -> &Graph {
        &self.graph
    }
    /// None for a node that is no value, or whose class conflicted.
    pub fn ty(&self, node: NodeId) -> Option<Ty> {
        self.settled.resolve(node)
    }
    fn may(&self, node: NodeId) -> &May {
        self.settled.may(node)
    }
    /// In source order, a syntactic one first at a shared position.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
    pub fn is_semantic(diagnostic: &Diagnostic) -> bool {
        diagnostic.code.group == codes::SEMANTIC
    }
    pub fn semantic_diagnostics(&self) -> impl Iterator<Item = &Diagnostic> {
        self.diagnostics.iter().filter(|d| Self::is_semantic(d))
    }
    /// In declaration order.
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
    pub fn function(&self, id: FunctionId) -> &Function {
        &self.functions[id.index()]
    }
    /// None for a function without a signature.
    pub fn ranges(&self, id: FunctionId) -> Option<Ranges> {
        self.function(id).signature.as_ref()?;
        let run = self.graph.run(id);
        Some(Ranges {
            params: run.params().map(|param| self.may(param).clone()).collect(),
            result: if self.may(run.entry()).live() {
                self.may(run.result()).clone()
            } else {
                May::NONE
            },
        })
    }
    pub fn text(&self, range: TextRange) -> &str {
        range.text(self.parsed.source())
    }
    pub fn is_valid(&self) -> bool {
        self.diagnostics.is_empty()
    }
    pub fn program(&self) -> Option<Program<'_>> {
        self.is_valid().then_some(Program { analysis: self })
    }
}

/// An analysis with no diagnostic: every function has a signature and a complete body, and a
/// refusal from the machine is a checker bug.
#[derive(Clone, Copy, Debug)]
pub struct Program<'a> {
    analysis: &'a Analysis,
}

impl<'a> Program<'a> {
    pub fn function(self, id: FunctionId) -> &'a Function {
        self.analysis.function(id)
    }
    pub fn signature(self, id: FunctionId) -> &'a Signature {
        self.function(id)
            .signature()
            .expect("a valid file's functions have signatures")
    }
    pub fn ranges(self, id: FunctionId) -> Ranges {
        self.analysis
            .ranges(id)
            .expect("a valid file's functions have ranges")
    }
    pub fn functions(self) -> impl Iterator<Item = (FunctionId, &'a Function)> {
        self.analysis
            .functions
            .iter()
            .enumerate()
            .map(|(index, function)| (FunctionId::new(index), function))
    }
    /// A valid file names each function once.
    pub fn function_named(self, name: &str) -> Option<FunctionId> {
        self.functions()
            .find(|(_, function)| {
                function
                    .name()
                    .is_some_and(|range| self.analysis.text(range) == name)
            })
            .map(|(id, _)| id)
    }
    /// `args` must lie within `ranges(function).params`; only the match against the signature is
    /// asserted.
    pub fn machine(self, function: FunctionId, args: &[Value]) -> Machine<'a> {
        let signature = self.signature(function);
        assert!(
            args.len() == signature.params.len()
                && args
                    .iter()
                    .zip(&signature.params)
                    .all(|(arg, &param)| arg.ty() == param),
            "arguments must match the signature"
        );
        Machine::new(
            self.analysis.graph(),
            function,
            args,
            self.function(function).depth_bound(),
        )
    }
    pub fn evaluate(self, function: FunctionId, args: &[Value]) -> Value {
        self.machine(function, args)
            .run()
            .unwrap_or_else(|refusal| {
                unreachable!("the checker proved this run: it was refused with {refusal:?}")
            })
    }
}

#[derive(Debug)]
pub struct Function {
    name: Option<TextRange>,
    origin: TextRange,
    signature: Option<Signature>,
    complete: bool,
    depth: Option<u64>,
}

impl Function {
    pub fn name(&self) -> Option<TextRange> {
        self.name
    }
    pub fn origin(&self) -> TextRange {
        self.origin
    }
    /// Present when the declaration resolved; it says nothing of the body.
    pub fn signature(&self) -> Option<&Signature> {
        self.signature.as_ref()
    }
    /// The body built whole and every value in it resolved.
    pub fn complete(&self) -> bool {
        self.complete
    }
    /// Most frames a run from here holds at once, the entry included; none when a measure's hull is
    /// unbounded. A valid file's run is finite either way.
    pub fn depth_bound(&self) -> Option<u64> {
        self.depth
    }
}

/// The hull of every live call site's arguments, and the result over them; both empty for a
/// function no live call site reaches.
#[derive(Debug, PartialEq, Eq)]
pub struct Ranges {
    pub params: Box<[May]>,
    pub result: May,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Signature {
    pub params: Box<[Ty]>,
    pub result: Ty,
}
