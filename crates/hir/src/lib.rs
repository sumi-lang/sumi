//! Semantic analysis of one file over the frontend's snapshot. Handles and ranges are relative to
//! the analysis that made them.

mod check;
pub mod codes;
mod dependency;
mod flows;
mod lattice;
mod lower;
mod reachability;
mod recursion;
mod solver;
mod spans;
mod summary;
mod typing;

use std::fmt;

use sumi_frontend::{Diagnostic, ParsedSource};
use sumi_text::{TextRange, TextSize};

pub use check::analyze;
pub use reachability::{Dead, DeadCause};
pub use spans::Spans;
pub use sumi_graph::{
    ArithOp, Arms, BinaryOp, Bools, Carried, Case, CmpOp, Decl, DeclId, Decls, FieldName, Fields,
    FunctionId, Graph, Int, Ints, Machine, May, Names, NodeId, Op, Record, References, Refusal,
    RegionId, Role, Run, Shown, ShownTy, ShownValue, Ty, TyKind, UnionId, Unions, Value,
};

pub struct Analysis {
    parsed: ParsedSource,
    graph: Graph,
    spans: Spans,
    typing: typing::Typing,
    functions: Vec<Function>,
    decls: Vec<TypeDecl>,
    /// By field name ID.
    field_names: Vec<Box<str>>,
    /// The graph's, and those inference minted.
    unions: Unions,
    bindings: Vec<Binding>,
    references: Vec<Occurrence>,
    unresolved: Vec<TextRange>,
    diagnostics: Vec<Diagnostic>,
    dead: Vec<Dead>,
}

impl fmt::Debug for Analysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Analysis")
            .field("parsed", &self.parsed)
            .field("graph", &self.graph)
            .field("functions", &self.functions)
            .field("bindings", &self.bindings)
            .field("references", &self.references)
            .field("unresolved", &self.unresolved)
            .field("diagnostics", &self.diagnostics)
            .field("dead", &self.dead)
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
    /// Where the graph's nodes and regions come from.
    pub fn spans(&self) -> &Spans {
        &self.spans
    }
    /// None for a node that is no value, whose class conflicted, or that only a hole decided.
    pub fn ty(&self, node: NodeId) -> Option<Ty> {
        self.typing.resolve(node)
    }
    pub fn show(&self, ty: Ty) -> ShownTy<'_> {
        ty.shown(self)
    }
    /// The type items in declaration order, then the type parameters and the instances named; the
    /// graph's table of the same types holds their field types.
    pub fn decls(&self) -> &[TypeDecl] {
        &self.decls
    }
    pub fn decl(&self, id: DeclId) -> &TypeDecl {
        &self.decls[id.index()]
    }
    /// Every union a type here names, the graph's and those inference minted.
    pub fn unions(&self) -> &Unions {
        &self.unions
    }
    fn may(&self, node: NodeId) -> &May {
        self.typing.may(node)
    }
    /// In source order, a syntactic one first at a shared position.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
    /// The code the reachability warnings call dead, in source order; empty, like those warnings,
    /// for a file with an error.
    pub fn dead(&self) -> &[Dead] {
        &self.dead
    }
    pub fn is_semantic(diagnostic: &Diagnostic) -> bool {
        diagnostic.code.group == codes::SEMANTIC
    }
    pub fn semantic_diagnostics(&self) -> impl Iterator<Item = &Diagnostic> {
        self.diagnostics.iter().filter(|d| Self::is_semantic(d))
    }
    /// The function items in declaration order, then the instances of the generic ones.
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
    pub fn function(&self, id: FunctionId) -> &Function {
        &self.functions[id.index()]
    }
    /// Every local a body declares, by the node that declares it, so in declaration order within
    /// a function; a failed body keeps those it reached.
    pub fn bindings(&self) -> &[Binding] {
        &self.bindings
    }
    pub fn binding(&self, id: BindingId) -> &Binding {
        &self.bindings[id.index()]
    }
    /// A function's parameters by position; one without a name is absent. An instance's are its
    /// item's, which declares them.
    pub fn params(&self, id: FunctionId) -> impl ExactSizeIterator<Item = Option<&Binding>> {
        let item = self.function(id).generic;
        self.graph.run(item).params().map(|node| {
            // Bindings are declared in node order, so the node's binding is where it would sort.
            let index = self
                .bindings
                .partition_point(|binding| binding.declaration.index() < node.index());
            self.bindings
                .get(index)
                .filter(|binding| binding.declaration == node)
        })
    }
    /// Every name that resolved to a local or a function, in source order; a declaration is not
    /// among them.
    pub fn references(&self) -> &[Occurrence] {
        &self.references
    }
    /// Names where the parser recovered that denote nothing known: a declaration under the same
    /// recovery may bind them, so a reference to a symbol of that name may be missing. In source
    /// order.
    pub fn unresolved(&self) -> &[TextRange] {
        &self.unresolved
    }
    /// A symbol's declared name; none for an item whose declaration lost its name.
    pub fn declaration(&self, symbol: Symbol) -> Option<TextRange> {
        match symbol {
            Symbol::Local(id) => Some(self.binding(id).name),
            Symbol::Function(id) => self.function(id).name,
            Symbol::Type(id) => self.decl(id).name,
            Symbol::Field(id, index) => Some(self.decl(id).fields()[index as usize].name),
        }
    }
    /// The declaration or reference at `offset`, which may sit at either end of the name.
    pub fn symbol_at(&self, offset: TextSize) -> Option<Occurrence> {
        let covers = |range: TextRange| range.start() <= offset && offset <= range.end();
        let reference = self
            .references
            .partition_point(|occurrence| occurrence.range.end() < offset);
        if let Some(occurrence) = self.references.get(reference).filter(|o| covers(o.range)) {
            return Some(*occurrence);
        }
        let mut declarations = self
            .bindings
            .iter()
            .enumerate()
            .map(|(index, binding)| Occurrence {
                range: binding.name,
                symbol: Symbol::Local(BindingId::new(index)),
                is_write: true,
            })
            .chain(
                self.functions
                    .iter()
                    .enumerate()
                    .filter_map(|(index, function)| {
                        Some(Occurrence {
                            range: function.name?,
                            symbol: Symbol::Function(FunctionId::new(index)),
                            is_write: true,
                        })
                    }),
            )
            .chain(self.decls.iter().enumerate().filter_map(|(index, decl)| {
                Some(Occurrence {
                    range: decl.name?,
                    symbol: Symbol::Type(DeclId::new(index)),
                    is_write: true,
                })
            }))
            .chain(self.decls.iter().enumerate().flat_map(|(index, decl)| {
                decl.fields()
                    .iter()
                    .enumerate()
                    .map(move |(position, field)| Occurrence {
                        range: field.name,
                        symbol: Symbol::Field(DeclId::new(index), position as u32),
                        is_write: true,
                    })
            }));
        declarations.find(|occurrence| covers(occurrence.range))
    }
    /// Every reference to `symbol`, in source order.
    pub fn references_of(&self, symbol: Symbol) -> impl Iterator<Item = TextRange> + '_ {
        self.references
            .iter()
            .filter(move |occurrence| occurrence.symbol == symbol)
            .map(|occurrence| occurrence.range)
    }
    /// The locals a name at `offset` can read, in declaration order, without those a later
    /// binding of the same name shadows there.
    pub fn visible_at(&self, offset: TextSize) -> Vec<&Binding> {
        let mut visible: Vec<&Binding> = Vec::new();
        for binding in self.bindings.iter().filter(|b| b.is_visible_at(offset)) {
            let name = self.text(binding.name);
            visible.retain(|earlier| self.text(earlier.name) != name);
            visible.push(binding);
        }
        visible
    }
    /// Present when the declaration resolved: the parameter list is whole and the result's type
    /// known. It says nothing of the body.
    pub fn signature(&self, id: FunctionId) -> Option<Signature<'_>> {
        Some(Signature {
            params: self.graph.run(id).param_types()?,
            result: self.function(id).result?,
            product: self.function(id).product,
        })
    }
    /// None for a function without a signature.
    pub fn ranges(&self, id: FunctionId) -> Option<Ranges> {
        self.signature(id)?;
        let run = self.graph.run(id);
        let returned = self.may(run.result());
        let result = match self.function(id).product {
            _ if !self.may(run.entry()).is_live() => May::NONE,
            None => returned.clone(),
            // The result is the product's first field.
            Some(product) => {
                let (name, _) = self.graph.decl(product).fields()[0];
                let Ok(result) = sumi_graph::Domain::field(
                    returned,
                    name,
                    self.graph.decls(),
                    self.graph.unions(),
                );
                result
            }
        };
        Some(Ranges {
            params: run.params().map(|param| self.may(param).clone()).collect(),
            result,
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
    pub fn signature(self, id: FunctionId) -> Signature<'a> {
        self.analysis
            .signature(id)
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
    /// A valid file names each function item once; a generic one is found as the instance at its
    /// own type parameters.
    pub fn function_named(self, name: &str) -> Option<FunctionId> {
        self.functions()
            .find(|&(id, function)| {
                function.generic == id
                    && function
                        .name()
                        .is_some_and(|range| self.analysis.text(range) == name)
            })
            .map(|(id, _)| id)
    }
    fn check_arguments(self, function: FunctionId, args: &[Value]) -> Signature<'a> {
        let signature = self.signature(function);
        assert!(
            args.len() == signature.params.len()
                && args
                    .iter()
                    .zip(signature.params)
                    .all(|(arg, &param)| self.analysis.unions.fits(arg.ty(), param)),
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
        let result = self.check_arguments(function, args).result;
        self.known(function, result).unwrap_or_else(|| {
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
            optimized: sumi_opt::optimize(self.analysis.graph(), |node| self.analysis.may(node)),
        }
    }
    /// The result when the analysis proved it a single scalar.
    fn known(self, function: FunctionId, result: Ty) -> Option<Value> {
        let run = self.analysis.graph.run(function);
        let may = self.analysis.may(run.result());
        match result.kind() {
            TyKind::Int => may.ints.lo().zip(may.ints.hi()).and_then(|(lo, hi)| {
                // Singleton detection stays constant-time even for large interval endpoints.
                (i64::try_from(&lo).is_ok() && lo == hi).then_some(Value::Int(lo))
            }),
            TyKind::Bool if may.bools == Bools::from(true) => Some(Value::Bool(true)),
            TyKind::Bool if may.bools == Bools::from(false) => Some(Value::Bool(false)),
            TyKind::Unit if may.has_unit => Some(Value::Unit),
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
        finish(self.machine(function, args))
    }
}

#[derive(Debug)]
pub struct Function {
    name: Option<TextRange>,
    origin: TextRange,
    generic: FunctionId,
    type_args: Box<[Ty]>,
    /// Resolved only for a function with parameter types.
    result: Option<Ty>,
    product: Option<DeclId>,
    is_complete: bool,
    depth: Option<u64>,
}

impl Function {
    pub fn name(&self) -> Option<TextRange> {
        self.name
    }
    pub fn origin(&self) -> TextRange {
        self.origin
    }
    /// The function item's instance at its own type parameters, which a `Symbol` names; itself
    /// for that instance, and for a function that takes none.
    pub fn generic(&self) -> FunctionId {
        self.generic
    }
    /// The type arguments this is its item's instance at, one per type parameter.
    pub fn type_args(&self) -> &[Ty] {
        &self.type_args
    }
    /// The body built whole and every value in it resolved.
    pub fn is_complete(&self) -> bool {
        self.is_complete
    }
    /// Most frames a run from here holds at once, the entry included; none when a measure's hull is
    /// unbounded. A valid file's run is finite either way.
    pub fn depth_bound(&self) -> Option<u64> {
        self.depth
    }
}

/// A binding's index in `Analysis::bindings`; an ID from one analysis names nothing in another.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BindingId(u32);

impl BindingId {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("binding count fits u32"))
    }
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl Names for Analysis {
    fn decl(&self, id: DeclId) -> &str {
        self.decl(id)
            .name
            .map_or("<missing>", |name| self.text(name))
    }

    fn type_args(&self, id: DeclId) -> &[Ty] {
        &self.decl(id).type_args
    }

    fn field(&self, name: FieldName) -> &str {
        &self.field_names[name.index()]
    }

    fn members(&self, id: UnionId) -> Vec<DeclId> {
        self.unions.get(id).to_vec()
    }
}

/// A declared type as the source wrote it: a type item at its own type parameters or at other
/// type arguments, or a type parameter, which has no fields. Its field types are the graph's.
#[derive(Debug)]
pub struct TypeDecl {
    name: Option<TextRange>,
    origin: TextRange,
    fields: Vec<FieldDecl>,
    is_param: bool,
    generic: DeclId,
    type_args: Box<[Ty]>,
}

impl TypeDecl {
    pub fn is_param(&self) -> bool {
        self.is_param
    }
    pub fn name(&self) -> Option<TextRange> {
        self.name
    }
    pub fn origin(&self) -> TextRange {
        self.origin
    }
    /// The type item's instance at its own type parameters, which a `Symbol` names; itself for
    /// that instance, for a type that takes none, and for a type parameter.
    pub fn generic(&self) -> DeclId {
        self.generic
    }
    /// The type arguments this is its item's instance at, one per type parameter.
    pub fn type_args(&self) -> &[Ty] {
        &self.type_args
    }
    /// In declaration order, parallel to the graph's; none for the product of a function with
    /// `mut` parameters, whose fields the source does not name.
    pub fn fields(&self) -> &[FieldDecl] {
        &self.fields
    }
}

#[derive(Debug)]
pub struct FieldDecl {
    name: TextRange,
    text: Box<str>,
}

impl FieldDecl {
    pub fn name(&self) -> TextRange {
        self.name
    }
    pub fn text(&self) -> &str {
        &self.text
    }
}

/// What a name in a body or a signature denotes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Symbol {
    Local(BindingId),
    /// A function item, as its instance at its own type parameters.
    Function(FunctionId),
    /// A type item, as its instance at its own type parameters, or a type parameter.
    Type(DeclId),
    /// A field of the type item, by position.
    Field(DeclId, u32),
}

/// A name in the source and the symbol it denotes; a declaration or an assignment target writes
/// it, a read does not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Occurrence {
    pub range: TextRange,
    pub symbol: Symbol,
    pub is_write: bool,
}

/// A local a body declares: a parameter, a `let`, a `for` index, or a `match` arm's binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Binding {
    name: TextRange,
    kind: BindingKind,
    declaration: NodeId,
    visible: TextRange,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingKind {
    /// A `mut` one is its caller's place, which its final value is written back to.
    Param {
        is_mutable: bool,
    },
    Let {
        is_mutable: bool,
    },
    LoopIndex,
    /// A `match` arm's binding of the narrowed scrutinee.
    Arm,
}

impl Binding {
    pub(crate) fn new(
        name: TextRange,
        kind: BindingKind,
        declaration: NodeId,
        visible: TextRange,
    ) -> Self {
        Self {
            name,
            kind,
            declaration,
            visible,
        }
    }
    pub fn name(&self) -> TextRange {
        self.name
    }
    pub fn kind(&self) -> BindingKind {
        self.kind
    }
    /// The node that carries the name and, through `Analysis::ty`, the binding's type.
    pub fn declaration(&self) -> NodeId {
        self.declaration
    }
    /// Where a read resolves to this binding or to one shadowing it: after the declaration, up to
    /// the closing brace of the enclosing block, or, past an unclosed one, up to the next
    /// significant token or one past the source's end. Empty for a name nothing can read yet.
    pub fn visible(&self) -> TextRange {
        self.visible
    }
    pub fn is_visible_at(&self, offset: TextSize) -> bool {
        self.visible.start() <= offset && offset < self.visible.end()
    }
}

/// The hull of every live call site's arguments, and the result over them; both empty for a
/// function no live call site reaches.
#[derive(Debug, PartialEq, Eq)]
pub struct Ranges {
    pub params: Box<[May]>,
    pub result: May,
}

/// A function's declared parameter types, the graph's, and its result type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Signature<'a> {
    pub params: &'a [Ty],
    pub result: Ty,
    /// What a function with `mut` parameters returns, and a call to it holds: a declared type
    /// with the result as its first field, then each such parameter's final value under its name.
    pub product: Option<DeclId>,
}

impl Signature<'_> {
    /// The type of the value a run of the function yields.
    pub fn returned(&self) -> Ty {
        self.product.map_or(self.result, Ty::decl)
    }
}
