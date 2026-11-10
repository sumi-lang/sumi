//! What each operation needs of its operands to run, held to what is known of them: the values
//! that may reach them, then what the body says relates them.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_frontend::DiagnosticCode;
use sumi_graph::{ArithOp, BinaryOp, Case, CmpOp, Domain, Graph, Int, Ints, May, NodeId, Op, Run};

use crate::check::explain;
use crate::codes;
use crate::lower::{Lowered, Need, Obligation, Source};
use crate::spans::Spans;
use crate::summary::{self, Form, Path, Root, Roots, Summaries, Sym, Types};
use crate::typing::Typing;

/// The most conditions a proof reads on the way to an operation, the nearest first.
const MAX_GUARDS: usize = 64;
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
    /// Of zero alone.
    Not,
}

#[derive(Clone, Copy)]
struct Owed {
    lhs: Term,
    rel: Rel,
    rhs: Term,
}

impl Need {
    fn owed(self) -> [Option<Owed>; 2] {
        let owed = |lhs, rel, rhs| Some(Owed { lhs, rel, rhs });
        let value = Term::Value;
        match self {
            Self::Divisor(divisor) => [owed(value(divisor), Rel::Not, Term::Zero), None],
            Self::Element { array, index } => [
                owed(Term::Zero, Rel::AtMost, value(index)),
                owed(value(index), Rel::Below, Term::Len(array)),
            ],
            Self::Last(array) => [owed(Term::Zero, Rel::Below, Term::Len(array)), None],
        }
    }

    fn code(self) -> DiagnosticCode {
        match self {
            Self::Divisor(_) => codes::DIVISION_BY_ZERO,
            Self::Element { .. } | Self::Last(_) => codes::INDEX_OUT_OF_BOUNDS,
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
    match rel {
        Rel::Below => lhs.hi().zip(rhs.lo()).is_some_and(|(hi, lo)| hi < lo),
        Rel::AtMost => lhs.hi().zip(rhs.lo()).is_some_and(|(hi, lo)| hi <= lo),
        Rel::Not => rhs.is_zero() && !lhs.contains_zero(),
    }
}

/// Whether the values that may reach its operands meet what is owed; none where an operand has
/// no value, in an operation that never runs.
fn is_met(typing: &Typing, owed: Owed) -> Option<bool> {
    let (lhs, rhs) = (ints(typing, owed.lhs), ints(typing, owed.rhs));
    (!lhs.is_empty() && !rhs.is_empty()).then(|| fits(&lhs, owed.rel, &rhs))
}

/// What of `need` the values that may reach its operands do not meet; none in an operation
/// that never runs.
fn unmet(typing: &Typing, need: Need) -> Vec<Owed> {
    let mut unmet = Vec::new();
    for owed in need.owed().into_iter().flatten() {
        match is_met(typing, owed) {
            None => return Vec::new(),
            Some(true) => {}
            Some(false) => unmet.push(owed),
        }
    }
    unmet
}

/// Something of a form over paths: that it is at least zero, or that it is not zero.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Claim {
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
    steps: Cell<u32>,
}

impl Proof<'_, '_> {
    fn holds(&self, claim: &Claim) -> bool {
        match claim {
            Claim::AtLeastZero(form) => self.at_least_zero(form, MAX_DEPTH),
            Claim::NotZero(form) => {
                let among = form.among(self.body, self.body.types);
                let negated = form.times(-1);
                among.is_none_or(|ints| !ints.contains_zero())
                    || self.guards.iter().any(|fact| {
                        matches!(fact, Claim::NotZero(known)
                            if known == form || Some(known) == negated.as_ref())
                    })
                    || self.at_least_zero(&form.shifted(-1), MAX_DEPTH)
                    || negated.is_some_and(|form| self.at_least_zero(&form.shifted(-1), MAX_DEPTH))
            }
        }
    }

    /// Lists of forms, `form` being at least zero where every form of one list is: each `form`
    /// less a fact, or with a path replaced by what bounds it in each case.
    fn weakened(&self, form: &Form, depth: u32) -> Vec<Vec<Form>> {
        let mut weaker = Vec::new();
        // A form that is not zero and at least minus one is at least zero.
        let above = form.shifted(1);
        let is_not_zero = |fact: &Claim| {
            matches!(fact, Claim::NotZero(known)
                if *known == above || above.times(-1).as_ref() == Some(known))
        };
        if self.guards.iter().any(is_not_zero) {
            weaker.push(vec![above.clone()]);
        }
        for (path, coefficient) in form.terms() {
            for fact in self.guards.iter() {
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
        let among = form.among(self.body, self.body.types);
        if among.is_none_or(|ints| ints.lo().is_some_and(|lo| lo >= Int::ZERO)) {
            return true;
        }
        if depth == 0 || self.steps.get() == 0 {
            return false;
        }
        self.steps.set(self.steps.get() - 1);
        let weaker = self.weakened(form, depth - 1);
        (weaker.iter()).any(|forms| forms.iter().all(|form| self.at_least_zero(form, depth - 1)))
    }
}

pub(crate) fn check(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    lowered: &Lowered,
    summaries: &Summaries,
    failed: &[bool],
) {
    // A place read and then written, and each instance of its function, needs its indices
    // inside once.
    let mut reported = HashSet::new();
    // The body of the function whose obligations are being read, once one is left open.
    let mut body: Option<(u32, Body<'_>)> = None;
    for obligation in &lowered.obligations {
        let owner = obligation.owner;
        if failed[owner as usize] || !typing.may(obligation.context).is_live() {
            continue;
        }
        let unmet = unmet(typing, obligation.need);
        if unmet.is_empty() {
            continue;
        }
        let (_, body) = match body.take() {
            Some(read) if read.0 == owner => body.insert(read),
            _ => {
                let read = Body::new(graph, typing, lowered, summaries, owner as usize);
                body.insert((owner, read))
            }
        };
        let proof = Proof {
            body,
            guards: &body.guards(obligation.context),
            steps: Cell::new(MAX_STEPS),
        };
        let is_proved = |owed: &Owed| body.claim(*owed).is_some_and(|claim| proof.holds(&claim));
        let is_once =
            matches!(obligation.need, Need::Divisor(_)) || !reported.contains(&obligation.at);
        if !unmet.iter().all(is_proved) && is_once {
            report(source, graph, spans, typing, lowered, obligation);
            reported.insert(obligation.at);
        }
    }
}

fn report(
    source: &mut Source<'_>,
    graph: &Graph,
    spans: &Spans,
    typing: &Typing,
    lowered: &Lowered,
    obligation: &Obligation,
) {
    let calls = &lowered.calls;
    let trace =
        |start, relevant: &dyn Fn(&Ints) -> bool, describe: &dyn Fn(&Ints, &str) -> String| {
            let values = typing.values();
            explain(graph, spans, values, Some(calls), start, relevant, describe)
        };
    let (message, labels) = match obligation.need {
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
                ints.lo().is_none_or(|lo| lo < Int::ZERO) || ints.hi().is_none_or(|hi| hi >= least)
            };
            let labels = trace(index, &outside, &|ints, where_| {
                format!("is {ints}{where_}")
            });
            (message, labels)
        }
    };
    source.report(obligation.at, obligation.need.code(), message, labels);
}
