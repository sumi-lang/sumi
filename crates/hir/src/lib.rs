//! Single-file scalar semantic analysis. The immutable syntax frontend is unchanged.
//!
//! Analysis keeps the graph of every body, whole or holed, with what it
//! decided about each node, and independent diagnostics. Handles are
//! relative to their analysis, not persistent identities. All source
//! locations refer to the owned snapshot.

mod check;
mod flows;
mod ranges;
mod recursion;
mod solver;
mod typing;

mod generated;
pub use generated::codes;

#[cfg(test)]
mod tests;

use sumi_frontend::{Diagnostic, ParsedSource, Severity};
use sumi_text::Span;

pub use check::analyze;
pub use ranges::{Bools, Bound, Ints, May};
pub use sumi_graph::{
    BinaryOp, Domain, FunctionId, Graph, Int, Machine, Node, NodeId, Op, OutOfRange, Outcome,
    ParseIntError, Refusal, Region, RegionId, Run, Ty, Value,
};

#[derive(Debug)]
pub struct Analysis {
    parsed: ParsedSource,
    graph: Graph,
    functions: Vec<Function>,
    diagnostics: Vec<Diagnostic>,
    /// The call depth bound of each function as an entry, by index.
    depth: Vec<Option<u64>>,
}

impl Analysis {
    pub fn parsed(&self) -> &ParsedSource {
        &self.parsed
    }
    /// Every definition of every function, whole or holed.
    pub fn graph(&self) -> &Graph {
        &self.graph
    }
    /// Semantic diagnostics only, in source order. Syntax diagnostics remain in `parsed`.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
    /// Every function's ID, in declaration order: the index into `functions()`.
    pub fn function_ids(&self) -> impl ExactSizeIterator<Item = FunctionId> + use<> {
        (0..self.functions.len()).map(FunctionId::new)
    }
    /// An ID must come from this analysis, not another source revision.
    pub fn function(&self, id: FunctionId) -> &Function {
        &self.functions[id.index()]
    }
    /// The most call frames a run entered at `id` can hold at once, the
    /// entry included, when every recursion it can reach has a measure
    /// with a finite hull. A valid file's every recursion has a measure,
    /// so a run of it is finite either way.
    pub fn depth_bound(&self, id: FunctionId) -> Option<u64> {
        self.depth[id.index()]
    }
    /// The source text `span` covers: how a name in the HIR is read, since
    /// every name is kept as where it is written.
    pub fn text(&self, span: Span) -> &str {
        let range = span.range();
        &self.parsed.source()[range.start().to_usize()..range.end().to_usize()]
    }
    pub fn is_valid(&self) -> bool {
        !self
            .parsed
            .diagnostics()
            .iter()
            .chain(&self.diagnostics)
            .any(|d| d.severity == Severity::Error)
            && self.functions.iter().all(|f| f.complete)
    }
    /// The file as a program, when it is valid: `None` when any diagnostic
    /// is an error.
    pub fn program(&self) -> Option<Program<'_>> {
        self.is_valid().then_some(Program { analysis: self })
    }
}

/// A valid analysis: every function has a signature and a complete body,
/// and no diagnostic is an error. Only such a file runs, so a run of it
/// has no path to an ill-typed operation, a zero divisor, a hole, or a
/// recursion without end, and the machine's refusals are checker bugs.
#[derive(Clone, Copy, Debug)]
pub struct Program<'a> {
    analysis: &'a Analysis,
}

impl<'a> Program<'a> {
    pub fn analysis(self) -> &'a Analysis {
        self.analysis
    }
    pub fn function(self, id: FunctionId) -> &'a Function {
        self.analysis.function(id)
    }
    /// A function's contract; every function of a valid file has one.
    pub fn signature(self, id: FunctionId) -> &'a Signature {
        self.function(id)
            .signature()
            .expect("a valid file's functions have signatures")
    }
    /// What may reach a function's parameters and result; every function
    /// of a valid file has it.
    pub fn ranges(self, id: FunctionId) -> &'a Ranges {
        self.function(id)
            .ranges()
            .expect("a valid file's functions have ranges")
    }
    /// Every function with its ID, in declaration order.
    pub fn functions(self) -> impl Iterator<Item = (FunctionId, &'a Function)> {
        self.analysis
            .function_ids()
            .map(|id| (id, self.analysis.function(id)))
    }
    /// The function item named `name`, if any.
    pub fn function_named(self, name: &str) -> Option<FunctionId> {
        self.functions()
            .find(|(_, function)| {
                function
                    .name()
                    .is_some_and(|span| self.analysis.text(span) == name)
            })
            .map(|(id, _)| id)
    }
    /// A machine about to call `function` on `args`, which must match the
    /// signature in count and type and lie within the parameters' ranges,
    /// bounded by the depth the analysis proved.
    pub fn machine(self, function: FunctionId, args: &[Value]) -> Machine<'a, Value> {
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
            self.analysis.depth_bound(function),
        )
    }
    /// Run `function` on `args` to completion, as [`Program::machine`]
    /// takes them. The checker proved the run cannot be refused.
    pub fn evaluate(self, function: FunctionId, args: &[Value]) -> Value {
        match self.machine(function, args).run() {
            Outcome::Value(value) => value,
            Outcome::Refused(refusal) => {
                unreachable!("the checker proved this run: it was refused with {refusal:?}")
            }
        }
    }
}

#[derive(Debug)]
pub struct Function {
    name: Option<Span>,
    origin: Span,
    signature: Option<Signature>,
    ranges: Option<Ranges>,
    complete: bool,
}

impl Function {
    /// Where the name is written; [`Analysis::text`] reads it.
    pub fn name(&self) -> Option<Span> {
        self.name
    }
    pub fn origin(&self) -> Span {
        self.origin
    }
    /// A concrete declaration contract, not a guarantee that its body is valid.
    /// Expression bodies (`=`, including `= { ... }`) infer an omitted result;
    /// bare block bodies default to unit. Callers never determine this result.
    pub fn signature(&self) -> Option<&Signature> {
        self.signature.as_ref()
    }
    /// Whether the body built whole and every value in it resolved: what a
    /// run needs of it. A complete body is not permission to execute an
    /// invalid file.
    pub fn complete(&self) -> bool {
        self.complete
    }
    /// The values that may reach the parameters and the result, whenever
    /// the function has a signature.
    pub fn ranges(&self) -> Option<&Ranges> {
        self.ranges.as_ref()
    }
}

/// What may reach a function's parameters, the hull of its live call sites'
/// arguments, and what its result may be. A function no live call site
/// reaches holds nothing in either, and nothing in it is checked.
#[derive(Debug, PartialEq, Eq)]
pub struct Ranges {
    pub params: Box<[May]>,
    pub result: May,
}

#[derive(Debug)]
pub struct Signature {
    pub params: Box<[Ty]>,
    pub result: Ty,
}
