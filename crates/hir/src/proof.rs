//! What each operation needs of its operands to run, held to what is known of them: the values
//! that may reach them, then what the body says relates them, then what its callers give it.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_frontend::DiagnosticCode;
use sumi_graph::{
    ArithOp, BinaryOp, Case, CmpOp, Domain, FunctionId, Graph, Int, Ints, May, NodeId, Op, Run,
    Value,
};
use sumi_text::TextRange;

use crate::check::explain;
use crate::dependency::{Components, Rows};
use crate::lower::{Call, Lowered, Need, Obligation, Source};
use crate::spans::Spans;
use crate::summary::{self, Form, Path, Root, Roots, Step, Summaries, Sym, Types};
use crate::typing::Typing;
use crate::{Function, codes};

/// The most a function asks of its callers; what is past it is held to the function alone.
const MAX_REQUIREMENTS: usize = 16;
/// The most guards a requirement is excused by.
const MAX_EXCUSES: usize = 3;
/// The most conditions a proof reads on the way to an operation, the nearest first.
const MAX_GUARDS: usize = 64;
/// The most times a recursive group is read for what its members need of one another.
const MAX_ROUNDS: usize = 4;
/// The most facts and bounds one claim is led through, one after another and in all.
const MAX_DEPTH: u32 = 4;
const MAX_STEPS: u32 = 256;

/// One side of a comparison an operation needs: a node's integer, the length of the sequence a
/// node holds, or zero.
#[derive(Clone, Copy)]
enum Term {
    Value(NodeId),
    Len(NodeId),
    Zero,
}

/// How one side of a comparison an operation needs stands to the other.
#[derive(Clone, Copy)]
enum Rel {
    Below,
    AtMost,
    Not,
}

#[derive(Clone, Copy)]
struct Owed {
    lhs: Term,
    rel: Rel,
    rhs: Term,
}

/// What an operation needs, as comparisons: each of one or two, or any of several.
enum Owes {
    Each([Option<Owed>; 2]),
    Any(Vec<Owed>),
}

impl Need {
    fn owes(&self) -> Owes {
        let owed = |lhs, rel, rhs| Some(Owed { lhs, rel, rhs });
        let value = Term::Value;
        match *self {
            Self::Divisor(divisor) => {
                Owes::Each([owed(value(divisor), Rel::Not, Term::Zero), None])
            }
            Self::Element { array, index } => Owes::Each([
                owed(Term::Zero, Rel::AtMost, value(index)),
                owed(value(index), Rel::Below, Term::Len(array)),
            ]),
            Self::Last(array) => Owes::Each([owed(Term::Zero, Rel::Below, Term::Len(array)), None]),
            Self::Apart { ref indices, .. } => {
                let apart = indices.iter().map(|&(a, b)| Owed {
                    lhs: value(a),
                    rel: Rel::Not,
                    rhs: value(b),
                });
                Owes::Any(apart.collect())
            }
        }
    }

    fn code(&self) -> DiagnosticCode {
        match self {
            Self::Divisor(_) => codes::DIVISION_BY_ZERO,
            Self::Element { .. } | Self::Last(_) => codes::INDEX_OUT_OF_BOUNDS,
            Self::Apart { .. } => codes::OVERLAPPING_PLACES,
        }
    }
}

fn ints(typing: &Typing, term: Term) -> Cow<'_, Ints> {
    match term {
        Term::Value(node) => Cow::Borrowed(&typing.may(node).ints),
        Term::Len(node) => {
            let Ok(len) = typing.may(node).length();
            Cow::Owned(len.ints)
        }
        Term::Zero => Cow::Owned(Ints::from(Int::ZERO)),
    }
}

fn fits(lhs: &Ints, rel: Rel, rhs: &Ints) -> bool {
    let below = |a: &Ints, b: &Ints| a.hi().zip(b.lo()).is_some_and(|(hi, lo)| hi < lo);
    match rel {
        Rel::Below => below(lhs, rhs),
        Rel::AtMost => lhs.hi().zip(rhs.lo()).is_some_and(|(hi, lo)| hi <= lo),
        Rel::Not => below(lhs, rhs) || below(rhs, lhs) || (rhs.is_zero() && !lhs.contains_zero()),
    }
}

/// Whether the values that may reach its operands meet what is owed; none where an operand has
/// no value, in an operation that never runs.
fn is_met(typing: &Typing, owed: Owed) -> Option<bool> {
    let (lhs, rhs) = (ints(typing, owed.lhs), ints(typing, owed.rhs));
    (!lhs.is_empty() && !rhs.is_empty()).then(|| fits(&lhs, owed.rel, &rhs))
}

/// What of `need` the values that may reach its operands do not meet, each a list one of which
/// would do; none in an operation that never runs.
fn unmet(typing: &Typing, need: &Need) -> Vec<Vec<Owed>> {
    let mut unmet = Vec::new();
    match need.owes() {
        Owes::Each(each) => {
            for owed in each.into_iter().flatten() {
                match is_met(typing, owed) {
                    None => return Vec::new(),
                    Some(true) => {}
                    Some(false) => unmet.push(vec![owed]),
                }
            }
        }
        Owes::Any(any) => {
            let mut is_any_met = false;
            for &owed in &any {
                match is_met(typing, owed) {
                    None => return Vec::new(),
                    Some(is_met) => is_any_met |= is_met,
                }
            }
            if !is_any_met {
                unmet.push(any);
            }
        }
    }
    unmet
}

/// Something of a form over paths: that it is at least zero, or that it is not zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Claim {
    AtLeastZero(Form),
    NotZero(Form),
}

impl Claim {
    /// `lhs` standing in `op` to `rhs`, each of which holds when it does; none past what a form
    /// holds.
    fn compared(lhs: &Form, op: CmpOp, rhs: &Form) -> Option<[Option<Self>; 2]> {
        let above = |low: &Form, high: &Form, by: i64| {
            let apart = high.plus_times(low, -1)?.shifted(-by);
            Some(Some(Self::AtLeastZero(apart)))
        };
        Some(match op {
            CmpOp::Lt => [above(lhs, rhs, 1)?, None],
            CmpOp::Le => [above(lhs, rhs, 0)?, None],
            CmpOp::Gt => [above(rhs, lhs, 1)?, None],
            CmpOp::Ge => [above(rhs, lhs, 0)?, None],
            CmpOp::Eq => [above(lhs, rhs, 0)?, above(rhs, lhs, 0)?],
            CmpOp::Ne => [Some(Self::NotZero(lhs.plus_times(rhs, -1)?)), None],
        })
    }

    fn form(&self) -> &Form {
        match self {
            Self::AtLeastZero(form) | Self::NotZero(form) => form,
        }
    }

    fn with(&self, form: Form) -> Self {
        match self {
            Self::AtLeastZero(_) => Self::AtLeastZero(form),
            Self::NotZero(_) => Self::NotZero(form),
        }
    }

    /// Whether the claim is of the function's parameters alone, and of one at least.
    fn is_given(&self) -> bool {
        let terms = self.form().terms();
        !terms.is_empty() && terms.iter().all(|(path, _)| path.is_given())
    }

    /// Whether no value its paths may hold makes the claim hold.
    fn never_holds(&self, body: &Body<'_>) -> bool {
        let among = self.form().among(body, body.types);
        among.is_some_and(|ints| match self {
            Self::AtLeastZero(_) => ints.hi().is_some_and(|hi| hi < Int::ZERO),
            Self::NotZero(_) => ints.is_zero(),
        })
    }

    fn holds(&self, args: &[Value], cx: Types<'_>) -> bool {
        match self {
            Self::AtLeastZero(form) => form.value(args, cx).is_some_and(|value| value >= Int::ZERO),
            Self::NotZero(form) => form.value(args, cx).is_some_and(|value| value != Int::ZERO),
        }
    }
}

/// What a function needs of its parameters for an operation under it to run: one claim of
/// `needs`, or one of `unless`, which would keep the function from the operation.
#[derive(Clone, Debug)]
pub(crate) struct Requirement {
    needs: Vec<Claim>,
    unless: Vec<Claim>,
    /// The operation, by its place among the obligations.
    origin: usize,
    /// Whether `needs` is what the operation itself needs, and not only enough for it.
    is_exact: bool,
}

impl Requirement {
    fn claims(&self) -> impl Iterator<Item = &Claim> {
        self.needs.iter().chain(&self.unless)
    }

    pub fn holds(&self, args: &[Value], cx: Types<'_>) -> bool {
        self.claims().any(|claim| claim.holds(args, cx))
    }
}

/// A function's body as a proof reads it: each node as the others name it.
struct Body<'a> {
    graph: &'a Graph,
    typing: &'a Typing,
    summaries: &'a Summaries,
    types: Types<'a>,
    run: &'a Run,
    syms: Vec<Sym>,
    /// By context, what `guards` answered.
    guards: RefCell<HashMap<NodeId, Rc<[Claim]>, FxBuildHasher>>,
}

impl Roots for Body<'_> {
    fn may(&self, root: Root) -> Option<&May> {
        match root {
            Root::Param(index) => {
                let param = self.run.params().nth(index as usize)?;
                Some(self.typing.may(param))
            }
            Root::Node(node) => Some(self.typing.may(node)),
        }
    }
}

impl<'a> Body<'a> {
    fn new(
        graph: &'a Graph,
        typing: &'a Typing,
        lowered: &Lowered,
        summaries: &'a Summaries,
        function: usize,
    ) -> Self {
        let types = Types {
            decls: graph.decls(),
            unions: graph.unions(),
        };
        let run = &graph.runs()[function];
        let ty = |node: NodeId| typing.resolve(node);
        let known = |call: NodeId| summaries.result(call);
        Self {
            graph,
            typing,
            summaries,
            types,
            run,
            syms: summary::pass(graph, lowered, run, known, types, Some(&ty)),
            guards: RefCell::default(),
        }
    }

    fn sym(&self, node: NodeId) -> &Sym {
        &self.syms[self.run.slot(node)]
    }

    fn form(&self, term: Term) -> Option<Form> {
        match term {
            Term::Value(node) => self.sym(node).exact().cloned(),
            Term::Len(node) => self.sym(node).length(self.types).exact().cloned(),
            Term::Zero => Some(Form::constant(Int::ZERO)),
        }
    }

    fn claim(&self, owed: Owed) -> Option<Claim> {
        let op = match owed.rel {
            Rel::Below => CmpOp::Lt,
            Rel::AtMost => CmpOp::Le,
            Rel::Not => CmpOp::Ne,
        };
        let [claim, _] = Claim::compared(&self.form(owed.lhs)?, op, &self.form(owed.rhs)?)?;
        claim
    }

    /// What holds wherever `context` is live, innermost first: the conditions on the way to it,
    /// the nearest `MAX_GUARDS` claims of them.
    fn guards(&self, context: NodeId) -> Rc<[Claim]> {
        if let Some(guards) = self.guards.borrow().get(&context) {
            return guards.clone();
        }
        let mut guards = Vec::new();
        let mut within = context;
        while guards.len() < MAX_GUARDS {
            let inputs = self.graph.inputs(within);
            match self.graph.node(within).op {
                Op::Arm(Case::Bool(taken)) => self.condition(inputs[0], taken, &mut guards),
                Op::Arm(_) => {}
                Op::After => self.completed(inputs[0], &mut guards),
                _ => break,
            }
            within = inputs[1];
        }
        guards.truncate(MAX_GUARDS);
        let guards: Rc<[Claim]> = guards.into();
        self.guards.borrow_mut().insert(context, guards.clone());
        guards
    }

    /// What holds once `control` has completed: of a condition, that no arm that never
    /// completes was the one taken.
    fn completed(&self, control: NodeId, guards: &mut Vec<Claim>) {
        let mut controls = vec![control];
        while let Some(control) = controls.pop() {
            let inputs = self.graph.inputs(control);
            match self.graph.node(control).op {
                Op::Sequence => controls.extend(inputs),
                Op::Observe { arms } => {
                    for arm in arms.iter() {
                        let region = self.graph.region(arm);
                        let exit = region.control().unwrap_or(region.context);
                        if let Case::Bool(taken) = self.graph.case(region.context)
                            && !self.typing.may(exit).is_live()
                        {
                            self.condition(inputs[0], !taken, guards);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// What the condition at `node` being `sense` says of the integers it compares.
    fn condition(&self, node: NodeId, sense: bool, guards: &mut Vec<Claim>) {
        let mut conditions = vec![(node, sense)];
        while let Some((node, sense)) = conditions.pop() {
            let inputs = self.graph.inputs(node);
            if !(self.graph.input_roles(node).iter()).all(|role| role.is_value()) {
                continue;
            }
            match self.graph.node(node).op {
                Op::Not => conditions.push((inputs[0], !sense)),
                Op::Copy { .. } | Op::Assign | Op::Exactly(_) => {
                    conditions.push((inputs[0], sense))
                }
                Op::And { rhs } | Op::Or { rhs }
                    if sense == matches!(self.graph.node(node).op, Op::And { .. }) =>
                {
                    let region = self.graph.region(rhs);
                    conditions.push((inputs[0], sense));
                    if region.result_has_value() {
                        conditions.push((region.result(), sense));
                    }
                }
                Op::Binary(BinaryOp::Cmp(op)) => {
                    let op = if sense { op } else { summary::negated(op) };
                    let (Some(lhs), Some(rhs)) =
                        (self.sym(inputs[0]).exact(), self.sym(inputs[1]).exact())
                    else {
                        continue;
                    };
                    if let Some(claims) = Claim::compared(lhs, op, rhs) {
                        guards.extend(claims.into_iter().flatten());
                    }
                }
                _ => {}
            }
        }
    }

    /// What bounds the integer `path` holds, as each value its root's node may be of bounds it:
    /// below by a form of each `lo` and above by one of each `hi`. None where nothing says.
    fn bounds(&self, path: &Path) -> Option<Vec<(Vec<Form>, Vec<Form>)>> {
        let Root::Node(node) = path.root() else {
            return None;
        };
        let inputs = self.graph.inputs(node);
        let is_live = |context: NodeId| self.typing.may(context).is_live();
        let exact = |node: NodeId| self.sym(node).exact();
        let mut sources: Vec<Cow<'_, Sym>> = Vec::new();
        match self.graph.node(node).op {
            Op::LoopIndex if path.steps().is_empty() => {
                let (start, end) = (exact(inputs[0])?, exact(inputs[1])?);
                return Some(vec![(vec![start.clone()], vec![end.shifted(-1)])]);
            }
            Op::Phi => {
                let values = inputs[1..].iter().zip(self.graph.phi_contexts(node));
                let roles = &self.graph.input_roles(node)[1..];
                for ((&value, &context), role) in values.zip(roles) {
                    if role.is_value() && is_live(context) {
                        sources.push(Cow::Borrowed(self.sym(value)));
                    }
                }
            }
            Op::Switch { arms } => {
                for region in arms.iter().map(|arm| self.graph.region(arm)) {
                    if region.result_has_value() && is_live(region.context) {
                        sources.push(Cow::Borrowed(self.sym(region.result())));
                    }
                }
            }
            Op::LoopValue => {
                let (header, next) = self.graph.carry(node);
                let [continuation, empty] = self.graph.loop_contexts(inputs[0]);
                if is_live(empty) {
                    sources.push(Cow::Borrowed(self.sym(self.graph.inputs(header)[0])));
                }
                if is_live(continuation) {
                    sources.push(Cow::Borrowed(self.sym(next)));
                }
            }
            Op::Call(_) => {
                let args: Vec<&Sym> = inputs.iter().map(|&arg| self.sym(arg)).collect();
                let result = self.summaries.result(node)?.at(&args, self.types);
                sources.push(Cow::Owned(result));
            }
            _ => return None,
        }
        let mut bounds = Vec::new();
        for source in sources {
            match source.through(path.steps(), self.types) {
                Sym::Int(cases) => {
                    let cases = cases.cases.iter();
                    bounds.extend(cases.map(|case| (case.lo.clone(), case.hi.clone())));
                }
                Sym::None => {}
                _ => return None,
            }
        }
        Some(bounds)
    }
}

/// A claim's proof, from what holds where it is owed.
struct Proof<'b, 'a> {
    body: &'b Body<'a>,
    /// What the conditions on the way there say, innermost first.
    guards: &'b [Claim],
    /// What the function needs of its callers anyway.
    given: &'b [Claim],
    /// Whether the values that may reach a path are read: without them, what is proved holds
    /// whatever the callers give.
    reads_values: bool,
    steps: Cell<u32>,
}

impl<'b, 'a> Proof<'b, 'a> {
    fn new(
        body: &'b Body<'a>,
        guards: &'b [Claim],
        given: &'b [Claim],
        reads_values: bool,
    ) -> Self {
        Self {
            body,
            guards,
            given,
            reads_values,
            steps: Cell::new(MAX_STEPS),
        }
    }
}

impl Proof<'_, '_> {
    fn facts(&self) -> impl Iterator<Item = &Claim> {
        self.guards.iter().chain(self.given)
    }

    fn holds(&self, claim: &Claim) -> bool {
        match claim {
            Claim::AtLeastZero(form) => self.at_least_zero(form, MAX_DEPTH),
            Claim::NotZero(form) => {
                let among = form.among(self.body, self.body.types);
                let negated = form.times(-1);
                among.is_none_or(|ints| !ints.contains_zero())
                    || self.facts().any(|fact| {
                        matches!(fact, Claim::NotZero(known)
                            if known == form || Some(known) == negated.as_ref())
                    })
                    || self.at_least_zero(&form.shifted(-1), MAX_DEPTH)
                    || negated.is_some_and(|form| self.at_least_zero(&form.shifted(-1), MAX_DEPTH))
            }
        }
    }

    /// Whether what holds here rules the claim out.
    fn refutes(&self, claim: &Claim) -> bool {
        let below = |form: &Form| form.times(-1).map(|negated| negated.shifted(-1));
        match claim {
            Claim::AtLeastZero(form) => {
                below(form).is_some_and(|form| self.at_least_zero(&form, MAX_DEPTH))
            }
            Claim::NotZero(form) => {
                let negated = form.times(-1);
                self.at_least_zero(form, MAX_DEPTH)
                    && negated.is_some_and(|form| self.at_least_zero(&form, MAX_DEPTH))
            }
        }
    }

    /// Lists of forms, `form` being at least zero where every form of one list is: each `form`
    /// less a fact, or with a path replaced by what bounds it in each case. With `is_open`,
    /// only its paths that are no parameter's are so taken from it.
    fn weakened(&self, form: &Form, depth: u32, is_open: bool) -> Vec<Vec<Form>> {
        let mut weaker = Vec::new();
        // A form that is not zero and at least minus one is at least zero.
        let above = form.shifted(1);
        let is_not_zero = |fact: &Claim| {
            matches!(fact, Claim::NotZero(known)
                if *known == above || above.times(-1).as_ref() == Some(known))
        };
        if !is_open && self.facts().any(is_not_zero) {
            weaker.push(vec![above.clone()]);
        }
        for (path, coefficient) in form.terms() {
            if is_open && path.is_given() {
                continue;
            }
            for fact in self.facts() {
                let Claim::AtLeastZero(fact) = fact else {
                    continue;
                };
                let known = fact.terms().iter().find(|(known, _)| known == path);
                let Some(&(_, by)) = known.filter(|(_, by)| (*by > 0) == (*coefficient > 0)) else {
                    continue;
                };
                let times = (coefficient.checked_rem(by) == Some(0))
                    .then(|| coefficient.checked_div(by)?.checked_neg());
                if let Some(rest) = times
                    .flatten()
                    .and_then(|times| form.plus_times(fact, times))
                {
                    weaker.push(vec![rest]);
                }
            }
            let without = coefficient
                .checked_neg()
                .and_then(|times| form.plus_times(&Form::path(path.clone()), times));
            let Some(without) = without else {
                continue;
            };
            weaker.extend(self.remainder(path, *coefficient, &without, depth));
            let Some(bounds) = self.body.bounds(path) else {
                continue;
            };
            // One list per choice of a bound for each case.
            let mut choices: Vec<Vec<Form>> = vec![Vec::new()];
            for (lo, hi) in &bounds {
                let side = if *coefficient > 0 { lo } else { hi };
                let rests: Vec<Form> = side
                    .iter()
                    .filter(|bound| !matches!(bound.terms(), [(only, 1)] if only == path))
                    .filter_map(|bound| without.plus_times(bound, *coefficient))
                    .collect();
                choices = choices
                    .iter()
                    .flat_map(|chosen| {
                        rests.iter().map(|rest| {
                            let mut chosen = chosen.clone();
                            chosen.push(rest.clone());
                            chosen
                        })
                    })
                    .take(MAX_STEPS as usize)
                    .collect();
            }
            weaker.extend(choices);
        }
        weaker
    }

    /// `weakened`, of `coefficient` times the remainder `path` holds plus `without`: a remainder
    /// is on its dividend's side of zero, and less far from it than a divisor that is never zero.
    fn remainder(
        &self,
        path: &Path,
        coefficient: i64,
        without: &Form,
        depth: u32,
    ) -> Vec<Vec<Form>> {
        let (Root::Node(node), []) = (path.root(), path.steps()) else {
            return Vec::new();
        };
        let graph = self.body.graph;
        let Op::Binary(BinaryOp::Arith(ArithOp::Rem)) = graph.node(node).op else {
            return Vec::new();
        };
        let exact = |node: NodeId| self.body.sym(node).exact();
        let (Some(of), Some(by)) = (exact(graph.inputs(node)[0]), exact(graph.inputs(node)[1]))
        else {
            return Vec::new();
        };
        // On the side the form needs the remainder kept from: the dividend's sign there, and
        // how far the remainder goes there at most.
        let toward = if coefficient > 0 { -1 } else { 1 };
        let (Some(of), Some(negated)) = (of.times(-toward), by.times(-1)) else {
            return Vec::new();
        };
        let mut weaker = vec![vec![of, without.clone()]];
        let most = if self.at_least_zero(&by.shifted(-1), depth) {
            by.shifted(-1)
        } else if self.at_least_zero(&negated.shifted(-1), depth) {
            negated.shifted(-1)
        } else {
            return weaker;
        };
        // Either way the remainder moves the form down by no more than the most it is.
        let down = coefficient.checked_abs().and_then(i64::checked_neg);
        let rest = down.and_then(|down| without.plus_times(&most, down));
        weaker.extend(rest.map(|rest| vec![rest]));
        weaker
    }

    fn at_least_zero(&self, form: &Form, depth: u32) -> bool {
        let is_proved = if self.reads_values {
            let among = form.among(self.body, self.body.types);
            among.is_none_or(|ints| ints.lo().is_some_and(|lo| lo >= Int::ZERO))
        } else {
            form.terms().is_empty() && *form.constant_term() >= Int::ZERO
        };
        if is_proved {
            return true;
        }
        if depth == 0 || self.steps.get() == 0 {
            return false;
        }
        self.steps.set(self.steps.get() - 1);
        let weaker = self.weakened(form, depth - 1, false);
        (weaker.iter()).any(|forms| forms.iter().all(|form| self.at_least_zero(form, depth - 1)))
    }

    /// A claim of the parameters alone that `claim` holds wherever it does, with no more taken
    /// from it than the paths that are no parameter's.
    fn given(&self, claim: &Claim, depth: u32) -> Option<Claim> {
        if claim.is_given() {
            return Some(claim.clone());
        }
        let Claim::AtLeastZero(form) = claim else {
            return None;
        };
        if depth == 0 {
            return None;
        }
        // Of the forms that must each be at least zero, the one that is not proved to be.
        let weaker = self.weakened(form, depth - 1, true);
        let mut open = weaker.iter().filter_map(|forms| {
            let mut open = forms
                .iter()
                .filter(|form| !self.at_least_zero(form, depth - 1));
            let only = open.next()?;
            open.next()
                .is_none()
                .then(|| Claim::AtLeastZero(only.clone()))
        });
        open.find_map(|claim| self.given(&claim, depth - 1))
    }
}

/// Whether the form sums lengths alone, each some times over, and no integer below zero: it is
/// then never below zero.
fn is_length_sum(form: &Form) -> bool {
    let mut terms = form.terms().iter();
    *form.constant_term() >= Int::ZERO
        && terms.all(|(path, by)| *by > 0 && matches!(path.steps().last(), Some(Step::Len)))
}

/// What became of something owed where a function's body could not prove it.
enum Passed {
    Up(Requirement),
    Nowhere,
}

/// What a diagnostic is reported once for: where, with which code, in which function when its
/// instances each report, and beside which other place.
type Once = (TextRange, &'static str, Option<u32>, Option<TextRange>);

struct Checker<'a, 's> {
    source: &'a mut Source<'s>,
    graph: &'a Graph,
    spans: &'a Spans,
    typing: &'a Typing,
    lowered: &'a Lowered,
    functions: &'a [Function],
    requires: Vec<Vec<Requirement>>,
    reported: HashSet<Once, FxBuildHasher>,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn check(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    lowered: &Lowered,
    summaries: &Summaries,
    failed: &[bool],
    functions: &[Function],
) -> Vec<Vec<Requirement>> {
    let count = graph.runs().len();
    let mut checker = Checker {
        source,
        graph,
        spans,
        typing,
        lowered,
        functions,
        requires: vec![Vec::new(); count],
        reported: HashSet::default(),
    };
    // By function, the obligations the values that may reach their operands leave open.
    let mut open: Vec<Vec<usize>> = vec![Vec::new(); count];
    let mut is_open = false;
    for (index, obligation) in lowered.obligations.iter().enumerate() {
        if failed[obligation.owner as usize] || !typing.may(obligation.context).is_live() {
            continue;
        }
        if !unmet(typing, &obligation.need).is_empty() {
            open[obligation.owner as usize].push(index);
            is_open = true;
        }
    }
    if !is_open {
        return checker.requires;
    }
    let is_live = |call: &&Call| {
        !failed[call.caller.index()]
            && !failed[call.callee.index()]
            && typing.may(call.context).is_live()
    };
    let mut calls: Vec<Vec<&Call>> = vec![Vec::new(); count];
    for call in lowered.calls.iter().filter(is_live) {
        calls[call.caller.index()].push(call);
    }
    let rows = Rows::new(count, || {
        let calls = calls.iter().flatten();
        calls.map(|call| (call.caller.index(), call.callee.index() as u32))
    });
    // Numbered callees first, so what a callee needs is known where its callers are read.
    let components = Components::new(&rows, |callee| callee as usize);
    for component in 0..components.count() {
        let members = components.members(component);
        let inside = |call: &Call| components.of[call.callee.index()] as usize == component;
        let mut bodies: HashMap<usize, Body<'_>, FxBuildHasher> = HashMap::default();
        let read = |member: usize| Body::new(graph, typing, lowered, summaries, member);
        // What a member of a recursive group needs goes round to the members that call it,
        // with nothing reported, until a round adds nothing or the rounds are spent.
        let is_recursive =
            (members.iter()).any(|&member| calls[member as usize].iter().any(|call| inside(call)));
        for _ in 0..if is_recursive { MAX_ROUNDS } else { 0 } {
            let mut grows = false;
            for &member in members {
                let member = member as usize;
                let needs = |call: &&&Call| !checker.requires[call.callee.index()].is_empty();
                let owing: Vec<&Call> = calls[member].iter().filter(needs).copied().collect();
                if open[member].is_empty() && owing.is_empty() {
                    continue;
                }
                let body = bodies.entry(member).or_insert_with(|| read(member));
                for &index in &open[member] {
                    grows |= checker.obligation(body, member, index, false);
                }
                for call in owing {
                    grows |= checker.call(body, call, true, false);
                }
            }
            if !grows {
                break;
            }
        }
        for &member in members {
            let member = member as usize;
            let needs = |call: &&&Call| !checker.requires[call.callee.index()].is_empty();
            let outward: Vec<&Call> = (calls[member].iter().filter(|call| !inside(call)))
                .filter(needs)
                .copied()
                .collect();
            if open[member].is_empty() && outward.is_empty() {
                continue;
            }
            let body = bodies.entry(member).or_insert_with(|| read(member));
            for &index in &open[member] {
                checker.obligation(body, member, index, true);
            }
            for call in outward {
                checker.call(body, call, true, true);
            }
        }
        // What is still owed at a call inside the group is proved where the call stands.
        for &member in members {
            let member = member as usize;
            for call in calls[member].iter().filter(|call| inside(call)) {
                if checker.requires[call.callee.index()].is_empty() {
                    continue;
                }
                let body = bodies.entry(member).or_insert_with(|| read(member));
                checker.call(body, call, false, true);
            }
        }
    }
    checker.requires
}

impl Checker<'_, '_> {
    /// The claims of `function` that hold whenever it is entered: each it needs of its callers
    /// with no other way out.
    fn given(&self, function: usize) -> Vec<Claim> {
        let single = self.requires[function].iter().filter_map(|requirement| {
            let mut claims = requirement.claims();
            let only = claims.next()?;
            claims.next().is_none().then(|| only.clone())
        });
        single.collect()
    }

    /// Proves one of `needs` or `unless` where `context` is live, or passes it to the function's
    /// callers when `passes` and some claim is of its parameters.
    #[allow(clippy::too_many_arguments)]
    fn owe(
        &self,
        body: &Body<'_>,
        function: usize,
        needs: &[Claim],
        unless: &[Claim],
        context: NodeId,
        origin: usize,
        is_exact: bool,
        passes: bool,
    ) -> Option<Passed> {
        let guards = body.guards(context);
        let mut given = self.given(function);
        // Of what the function needs one of, the one left where the rest are ruled out here.
        let left: Vec<Claim> = {
            let proof = Proof::new(body, &guards, &given, true);
            let several = self.requires[function].iter();
            let left = several.filter_map(|requirement| {
                let mut open = requirement.claims().filter(|claim| !proof.refutes(claim));
                let only = open.next()?;
                (requirement.claims().nth(1).is_some() && open.next().is_none())
                    .then(|| only.clone())
            });
            left.collect()
        };
        given.extend(left);
        let proof = |reads_values| Proof::new(body, &guards, &given, reads_values);
        let mut claims = needs.iter().chain(unless);
        if claims.clone().any(|claim| proof(true).holds(claim)) {
            return None;
        }
        // What the body rules out whatever it is given is no caller's to give.
        let passes = passes && !claims.all(|claim| proof(false).refutes(claim));
        if !passes || self.requires[function].len() >= MAX_REQUIREMENTS {
            return Some(Passed::Nowhere);
        }
        let proof = proof(true);
        let passed = |claims: &[Claim]| -> Vec<Claim> {
            let passed = claims
                .iter()
                .filter_map(|claim| proof.given(claim, MAX_DEPTH));
            passed.collect()
        };
        let is_exact = is_exact && needs.iter().all(Claim::is_given);
        let (needs, mut unless) = (passed(needs), passed(unless));
        if needs.is_empty() && unless.is_empty() {
            return Some(Passed::Nowhere);
        }
        // A guard that fails keeps the function from where the claim is owed: a form at least
        // zero that is less, or one that is zero, being at least and at most it, that is not.
        let mut excuses: Vec<Claim> = Vec::new();
        for guard in guards.iter().filter(|guard| guard.is_given()) {
            let Claim::AtLeastZero(form) = guard else {
                continue;
            };
            let Some(negated) = form.times(-1) else {
                continue;
            };
            let excuse = if guards.contains(&Claim::AtLeastZero(negated.clone())) {
                Claim::NotZero(form.clone().min(negated))
            } else {
                Claim::AtLeastZero(negated.shifted(-1))
            };
            // An excuse that holds only where a claim does excuses nothing.
            let is_implied = needs
                .iter()
                .chain(&unless)
                .any(|claim| match (claim, &excuse) {
                    (Claim::AtLeastZero(claim), Claim::AtLeastZero(excuse)) => {
                        (claim.plus_times(excuse, -1)).is_some_and(|apart| is_length_sum(&apart))
                    }
                    _ => claim == &excuse,
                });
            if !is_implied && !excuses.contains(&excuse) {
                excuses.push(excuse);
            }
        }
        unless.extend(excuses.into_iter().take(MAX_EXCUSES));
        Some(Passed::Up(Requirement {
            needs,
            unless,
            origin,
            is_exact,
        }))
    }

    /// Adds what `function` needs, unless it needs as much already: the same claims for an
    /// operation of the same kind, or one claim that a form over the same paths is at least zero
    /// where this one's is, of which the lesser form stays. Whether it now needs more.
    fn require(&mut self, function: usize, requirement: Requirement) -> bool {
        let obligations = &self.lowered.obligations;
        let code = |requirement: &Requirement| obligations[requirement.origin].need.code();
        let only =
            |requirement: &Requirement| match (&requirement.needs[..], &requirement.unless[..]) {
                ([Claim::AtLeastZero(form)], []) => Some(form.clone()),
                _ => None,
            };
        for known in &mut self.requires[function] {
            if code(known) != code(&requirement) {
                continue;
            }
            if known.needs == requirement.needs && known.unless == requirement.unless {
                return false;
            }
            if let (Some(mine), Some(theirs)) = (only(known), only(&requirement))
                && mine.terms() == theirs.terms()
            {
                let is_more = theirs.constant_term() < mine.constant_term();
                if is_more {
                    *known = requirement;
                }
                return is_more;
            }
        }
        self.requires[function].push(requirement);
        true
    }

    /// Whether what is owed at `at` is reported for the first time; `need` is the operation's.
    fn once(&mut self, at: TextRange, need: &Need, owner: u32) -> bool {
        let (per, other) = match *need {
            // Each instance of a generic function divides by what its own callers give it.
            Need::Divisor(_) => (Some(owner), None),
            Need::Element { .. } | Need::Last(_) => (None, None),
            Need::Apart { other, .. } => (None, Some(other)),
        };
        self.reported.insert((at, need.code().name, per, other))
    }

    /// Holds an operation to what it needs, reporting what is neither proved nor passed to
    /// the function's callers only if `reports`. Whether the function now needs more.
    fn obligation(
        &mut self,
        body: &Body<'_>,
        function: usize,
        index: usize,
        reports: bool,
    ) -> bool {
        let obligation = &self.lowered.obligations[index];
        let mut grows = false;
        for any in unmet(self.typing, &obligation.need) {
            let needs: Vec<Claim> = any.iter().filter_map(|&owed| body.claim(owed)).collect();
            let context = obligation.context;
            let passed = self.owe(body, function, &needs, &[], context, index, true, true);
            match passed {
                None => {}
                Some(Passed::Up(requirement)) => grows |= self.require(function, requirement),
                Some(Passed::Nowhere) if !reports => {}
                Some(Passed::Nowhere) => {
                    if self.once(obligation.at, &obligation.need, obligation.owner) {
                        self.report(obligation);
                    }
                    break;
                }
            }
        }
        grows
    }

    /// Holds a call to what its callee needs: each requirement where the parameters are the
    /// call's arguments. `reports` and the result are `obligation`'s.
    fn call(&mut self, body: &Body<'_>, call: &Call, passes: bool, reports: bool) -> bool {
        let caller = call.caller.index();
        let mut grows = false;
        let args: Vec<&Sym> = (self.graph.inputs(call.node).iter())
            .map(|&arg| body.sym(arg))
            .collect();
        'requirements: for requirement in self.requires[call.callee.index()].clone() {
            // The claims at the arguments, each a form there; a path of one that holds nothing
            // there is in an operation the call never reaches.
            let mut given = [Vec::new(), Vec::new()];
            for (claims, given) in [&requirement.needs, &requirement.unless]
                .iter()
                .zip(&mut given)
            {
                for claim in claims.iter() {
                    let form = claim.form().at(&args, body.types);
                    if form.is_none() {
                        continue 'requirements;
                    }
                    given.extend(form.exact().map(|form| claim.with(form.clone())));
                }
            }
            let [needs, unless] = given;
            let (origin, context) = (requirement.origin, call.context);
            // What the operation itself needs, with every claim read at the arguments.
            let is_exact =
                requirement.is_exact && needs.len() + unless.len() == requirement.claims().count();
            match self.owe(
                body, caller, &needs, &unless, context, origin, is_exact, passes,
            ) {
                None => {}
                Some(Passed::Up(requirement)) => grows |= self.require(caller, requirement),
                Some(Passed::Nowhere) if !reports => {}
                Some(Passed::Nowhere) => {
                    let code = self.lowered.obligations[origin].need.code();
                    let at = self.spans.origin(call.node);
                    if self
                        .reported
                        .insert((at, code.name, Some(caller as u32), None))
                    {
                        let mut claims = needs.iter().chain(&unless);
                        let is_never = is_exact && claims.all(|claim| claim.never_holds(body));
                        self.report_call(call, &requirement, is_never);
                    }
                }
            }
        }
        grows
    }

    fn report(&mut self, obligation: &Obligation) {
        let (graph, spans, typing) = (self.graph, self.spans, self.typing);
        let calls = &self.lowered.calls;
        let trace =
            |start, relevant: &dyn Fn(&Ints) -> bool, describe: &dyn Fn(&Ints, &str) -> String| {
                let values = typing.values();
                explain(graph, spans, values, Some(calls), start, relevant, describe)
            };
        let (message, labels) = match obligation.need {
            Need::Apart { ref indices, other } => {
                let point = |node: NodeId| {
                    let ints = &typing.may(node).ints;
                    ints.lo().zip(ints.hi()).filter(|(lo, hi)| lo == hi)
                };
                let is_one = |&(a, b): &(NodeId, NodeId)| {
                    a == b || point(a).is_some_and(|a| Some(a) == point(b))
                };
                let may = if indices.iter().all(is_one) {
                    "overlaps"
                } else {
                    "may overlap"
                };
                let message = format!("this place {may} another the call changes");
                (message, vec![(other, Box::from("also changed here"))])
            }
            Need::Divisor(divisor) => {
                let divisor_ints = &typing.may(divisor).ints;
                let message = if divisor_ints.is_zero() {
                    "division by zero"
                } else {
                    "divisor may be zero"
                };
                let labels = trace(divisor, &Ints::contains_zero, &|ints, where_| {
                    if ints.is_zero() {
                        format!("is 0{where_}")
                    } else {
                        format!("may be 0{where_}: {ints}")
                    }
                });
                (message.to_owned(), labels)
            }
            Need::Last(array) => {
                let len = ints(typing, Term::Len(array));
                let message = if len.is_zero() {
                    "the sequence is empty, and has no last element".to_owned()
                } else {
                    format!("the sequence may be empty: its length is {len}")
                };
                (message, Vec::new())
            }
            Need::Element { array, index } => {
                let len = ints(typing, Term::Len(array));
                let index_ints = &typing.may(index).ints;
                let least = len.lo().unwrap_or(Int::ZERO);
                // Outside every length the sequence may have, or only some.
                let is_never = index_ints.hi().is_some_and(|hi| hi < Int::ZERO)
                    || index_ints
                        .lo()
                        .zip(len.hi())
                        .is_some_and(|(lo, most)| lo >= most);
                let may = if is_never { "is" } else { "may be" };
                let message = format!(
                    "index {may} outside the sequence: it is {index_ints}, and the length is {len}"
                );
                let outside = |ints: &Ints| {
                    ints.lo().is_none_or(|lo| lo < Int::ZERO)
                        || ints.hi().is_none_or(|hi| hi >= least)
                };
                let labels = trace(index, &outside, &|ints, where_| {
                    format!("is {ints}{where_}")
                });
                (message, labels)
            }
        };
        self.source
            .report(obligation.at, obligation.need.code(), message, labels);
    }

    /// `is_never`: the call never gives what the operation itself needs.
    fn report_call(&mut self, call: &Call, requirement: &Requirement, is_never: bool) {
        let origin = &self.lowered.obligations[requirement.origin];
        let (what, here) = match (&origin.need, is_never) {
            (Need::Divisor(_), false) => ("divisor may be zero", "divided here"),
            (Need::Divisor(_), true) => ("division by zero", "divided here"),
            (Need::Element { .. }, false) => ("index may be outside the sequence", "indexed here"),
            (Need::Element { .. }, true) => ("index is outside the sequence", "indexed here"),
            (Need::Last(_), false) => (
                "the sequence may be empty",
                "its last element is taken here",
            ),
            (Need::Last(_), true) => ("the sequence is empty", "its last element is taken here"),
            (Need::Apart { .. }, false) => ("places a call changes may overlap", "changed here"),
            (Need::Apart { .. }, true) => ("places a call changes overlap", "changed here"),
        };
        let text = self.source.parsed.source();
        let callee = self.functions[call.callee.index()].name;
        let callee = callee.map_or("<missing>", |name| name.text(text));
        let shown = Shown {
            graph: self.graph,
            spans: self.spans,
            fields: &self.source.field_names,
            text,
            function: call.callee,
        };
        let claims: Vec<String> = (requirement.claims())
            .map(|claim| format!("`{}`", shown.claim(claim)))
            .collect();
        let message = format!("{what}: `{callee}` needs {}", claims.join(" or "));
        let mut labels = vec![(origin.at, Box::from(here))];
        // What the call gives each path the operation's own need reads.
        let types = Types {
            decls: self.graph.decls(),
            unions: self.graph.unions(),
        };
        let args = self.graph.inputs(call.node);
        let mays: Vec<&May> = args.iter().map(|&arg| self.typing.may(arg)).collect();
        let mut paths: Vec<&Path> = (requirement.needs.iter())
            .flat_map(|claim| claim.form().terms().iter().map(|(path, _)| path))
            .collect();
        paths.sort();
        paths.dedup();
        for path in paths {
            let Root::Param(index) = path.root() else {
                continue;
            };
            let ints = path.among(&mays[..], types).ints;
            let reads = self.spans.reads(call.node);
            let (Some(&at), false) = (reads.get(index as usize), ints.is_empty()) else {
                continue;
            };
            let is = match (ints.lo(), ints.hi()) {
                (Some(lo), Some(hi)) if lo == hi => lo.to_string(),
                _ => ints.to_string(),
            };
            labels.push((at, format!("`{}` is {is}", shown.path(path)).into()));
        }
        labels.sort_by_key(|(range, _)| range.start());
        let at = self.spans.origin(call.node);
        self.source.report(at, origin.need.code(), message, labels);
    }
}

/// Claims of a function's parameters, as its source names them.
struct Shown<'a> {
    graph: &'a Graph,
    spans: &'a Spans,
    fields: &'a [&'a str],
    text: &'a str,
    function: FunctionId,
}

impl Shown<'_> {
    fn path(&self, path: &Path) -> String {
        let param = match path.root() {
            Root::Param(index) => self.graph.run(self.function).params().nth(index as usize),
            Root::Node(_) => None,
        };
        let name = param.and_then(|param| self.spans.name(param));
        let mut shown = name.map_or("_", |name| name.text(self.text)).to_owned();
        for step in path.steps() {
            match step {
                Step::Field(name, _) => {
                    shown.push('.');
                    shown.push_str(self.fields[name.index()]);
                }
                Step::Element(index, _) => shown.push_str(&format!("[{}]", self.form(index))),
                Step::Len => shown.push_str(".len()"),
            }
        }
        shown
    }

    /// The paths `form` sums on the side `sign` is of, each with how many times.
    fn terms(&self, form: &Form, sign: i64) -> Vec<String> {
        let terms = form.terms().iter().filter(|(_, by)| by.signum() == sign);
        terms
            .map(|(path, by)| match by.unsigned_abs() {
                1 => self.path(path),
                by => format!("{by} * {}", self.path(path)),
            })
            .collect()
    }

    /// The whole of `form`, what it adds before what it takes away.
    fn form(&self, form: &Form) -> String {
        let (more, less) = (self.terms(form, 1), self.terms(form, -1));
        let mut shown = sum(&more, form.constant_term());
        if more.is_empty() && !less.is_empty() && *form.constant_term() == Int::ZERO {
            shown = format!("-{}", less.join(" - "));
        } else if !less.is_empty() {
            shown.push_str(&format!(" - {}", less.join(" - ")));
        }
        shown
    }

    fn claim(&self, claim: &Claim) -> String {
        let form = claim.form();
        let (more, less) = (self.terms(form, 1), self.terms(form, -1));
        let constant = form.constant_term();
        let zero = Int::ZERO;
        // The lesser side on the left: `less <= more + constant`.
        let (lhs, op, rhs) = match claim {
            Claim::AtLeastZero(_) if less.is_empty() => {
                (sum(&more, &zero), ">=", (-constant).to_string())
            }
            Claim::AtLeastZero(_) if more.is_empty() => {
                (sum(&less, &zero), "<=", constant.to_string())
            }
            Claim::AtLeastZero(_) if *constant == Int::from(-1) => {
                (sum(&less, &zero), "<", sum(&more, &zero))
            }
            Claim::AtLeastZero(_) if *constant < zero => {
                (sum(&less, &-constant), "<=", sum(&more, &zero))
            }
            Claim::AtLeastZero(_) => (sum(&less, &zero), "<=", sum(&more, constant)),
            Claim::NotZero(_) if less.is_empty() => {
                (sum(&more, &zero), "!=", (-constant).to_string())
            }
            Claim::NotZero(_) if more.is_empty() => (sum(&less, &zero), "!=", constant.to_string()),
            Claim::NotZero(_) if *constant < zero => {
                (sum(&less, &-constant), "!=", sum(&more, &zero))
            }
            Claim::NotZero(_) => (sum(&less, &zero), "!=", sum(&more, constant)),
        };
        format!("{lhs} {op} {rhs}")
    }
}

/// `terms` and `constant` as a sum, a zero left out beside a term.
fn sum(terms: &[String], constant: &Int) -> String {
    let mut shown = terms.join(" + ");
    if terms.is_empty() {
        shown = constant.to_string();
    } else if *constant > Int::ZERO {
        shown.push_str(&format!(" + {constant}"));
    } else if *constant < Int::ZERO {
        shown.push_str(&format!(" - {}", -constant));
    }
    shown
}
