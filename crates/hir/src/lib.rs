//! Semantic analysis of one file over the frontend's snapshot. Handles and ranges are relative to
//! the analysis that made them.

mod check;
pub mod codes;
mod flows;
mod lattice;
mod lower;
mod reachability;
mod recursion;
mod solver;
mod typing;

use std::fmt;

use sumi_frontend::{Diagnostic, ParsedSource};
use sumi_text::TextRange;

pub use check::analyze;
pub use sumi_graph::{
    ArithOp, BinaryOp, Bools, Callable, Callee, CmpOp, FunctionId, Graph, Int, Ints, Machine, May,
    NodeId, Op, Refusal, RegionId, Run, Ty, Value,
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
        !self.diagnostics.iter().any(Diagnostic::is_error)
    }
    pub fn program(&self) -> Option<Program<'_>> {
        self.is_valid().then_some(Program { analysis: self })
    }
}

/// An analysis with no error: every function has a signature and a complete body, and a
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
    pub fn analysis(self) -> &'a Analysis {
        self.analysis
    }
    /// Every value a run within `ranges` computes at `node` lies here.
    pub fn may(self, node: NodeId) -> &'a May {
        self.analysis.may(node)
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
    fn check_arguments(self, function: FunctionId, args: &[Value]) -> &'a Signature {
        let signature = self.signature(function);
        assert!(
            args.len() == signature.params.len()
                && args
                    .iter()
                    .zip(&signature.params)
                    .all(|(arg, &param)| arg.ty() == param),
            "arguments must match the signature"
        );
        signature
    }
    /// `args` must lie within `ranges(function).params`; only the match against the signature is
    /// asserted.
    pub fn machine(self, function: FunctionId, args: &[Value]) -> Machine<'a> {
        self.check_arguments(function, args);
        Machine::new(
            self.analysis.graph(),
            function,
            args,
            self.function(function).depth_bound(),
        )
    }
    /// Evaluate within `ranges(function).params`, without the machine's observable trace.
    pub fn evaluate(self, function: FunctionId, args: &[Value]) -> Value {
        self.check_arguments(function, args);
        self.known(function).unwrap_or_else(|| {
            finish(Machine::new(
                self.analysis.graph(),
                function,
                args,
                self.function(function).depth_bound(),
            ))
        })
    }
    /// The program through the middle end.
    pub fn compile(self) -> Compiled<'a> {
        Compiled {
            program: self,
            optimized: sumi_opt::optimize(self.analysis.graph()),
        }
    }
    /// The result when the analysis proved it a single value.
    fn known(self, function: FunctionId) -> Option<Value> {
        let run = self.analysis.graph.run(function);
        let may = self.analysis.may(run.result());
        match self.signature(function).result {
            Ty::Int => may.ints.lo().zip(may.ints.hi()).and_then(|(lo, hi)| {
                // Singleton detection stays constant-time even for large interval endpoints.
                (i64::try_from(&lo).is_ok() && lo == hi).then_some(Value::Int(lo))
            }),
            Ty::Bool if may.bools == Bools::from(true) => Some(Value::Bool(true)),
            Ty::Bool if may.bools == Bools::from(false) => Some(Value::Bool(false)),
            Ty::Unit if may.unit => Some(Value::Unit),
            _ => None,
        }
    }
}

fn finish(machine: Machine<'_>) -> Value {
    machine.run().unwrap_or_else(|refusal| {
        unreachable!("the checker proved this run: it was refused with {refusal:?}")
    })
}

/// A valid file through the middle end: the optimized graph a backend takes, each node's origin in
/// the analysis's graph, and the facts proved there. A run within `ranges` returns what the
/// analysis's graph does.
pub struct Compiled<'a> {
    program: Program<'a>,
    optimized: sumi_opt::Optimized,
}

impl<'a> Compiled<'a> {
    pub fn program(&self) -> Program<'a> {
        self.program
    }
    pub fn graph(&self) -> &Graph {
        &self.optimized.graph
    }
    /// The node of the analysis's graph that `node` computes.
    pub fn origin(&self, node: NodeId) -> NodeId {
        self.optimized.origin(node)
    }
    /// Every value a run within `ranges` computes at `node` lies here.
    pub fn may(&self, node: NodeId) -> &'a May {
        self.program.may(self.origin(node))
    }
    /// `args` must lie within `ranges(function).params`; only the match against the signature is
    /// asserted.
    pub fn machine(&self, function: FunctionId, args: &[Value]) -> Machine<'_> {
        self.program.check_arguments(function, args);
        Machine::new(
            &self.optimized.graph,
            function,
            args,
            self.program.function(function).depth_bound(),
        )
    }
    /// Evaluate within `ranges(function).params`, without the machine's observable trace.
    pub fn evaluate(&self, function: FunctionId, args: &[Value]) -> Value {
        self.program.check_arguments(function, args);
        self.program
            .known(function)
            .unwrap_or_else(|| finish(self.machine(function, args)))
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
