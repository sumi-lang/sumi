//! The machine: an evaluation of the graph in a domain, driven by demand
//! from a function's result.
//!
//! A run computes what its result depends on and nothing else. Each frame
//! holds a slot per node of its function, filled the first time the node
//! is demanded, so a value shared through a `let` is computed once and a
//! region that is not chosen is never entered. The control stack is
//! explicit and every [`Machine::step`] is one unit of work an instrument
//! can observe, with the value it produced, if any, in [`Machine::latest`].
//!
//! The machine refuses rather than fails. A hole, a zero divisor, an
//! operator over a value of the wrong type, or a frame past the bound the
//! caller set ends the run with a [`Refusal`] that says which; on a graph
//! the checker proved, none can happen, and the checker's proof is what
//! turns a refusal into a bug. What the checker declared and did not
//! prove, a parameter's type on a graph it rejected, is not the machine's
//! to hold a value to.

use crate::{Concrete, Fault, FunctionId, Graph, NodeId, Op, RegionId};

/// One unit of pending work.
#[derive(Clone, Copy, Debug)]
enum Control {
    /// Demand the node's value.
    Eval(NodeId),
    /// Its inputs are in: apply the node's operator.
    Apply(NodeId),
    /// The left operand of `&&` or `||` is in: decide the right one.
    Lazy(NodeId),
    /// The condition of an `if` is in: choose a region.
    Branch(NodeId),
    /// The arguments of a call are in: enter the callee.
    Enter(NodeId),
    /// A region's result is in: it is the node's value.
    Take(NodeId, NodeId),
    /// The callee's result is in: leave its frame and it is the call's value.
    Return(NodeId),
}

#[derive(Debug)]
struct Frame {
    function: FunctionId,
    /// Where this frame's slots begin in the shared slab.
    base: usize,
    /// The first node of the function's run: its slot is the first.
    first: usize,
}

/// How a run ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome<D> {
    Value(D),
    Refused(Refusal),
}

/// What a run was asked to do that it will not: on a graph the checker
/// proved, none of these arise.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// A node that was never built.
    Hole(NodeId),
    /// A division whose divisor is zero.
    Division(NodeId),
    /// An operator over a value of the wrong type.
    Type(NodeId),
    /// A call that would open a frame past the bound.
    Depth(NodeId),
}

impl Refusal {
    fn of(fault: Fault, node: NodeId) -> Self {
        match fault {
            Fault::Division => Self::Division(node),
            Fault::Type => Self::Type(node),
        }
    }
}

/// A run in progress: [`Machine::step`] advances it one unit of work.
#[derive(Debug)]
pub struct Machine<'a, D> {
    graph: &'a Graph,
    control: Vec<Control>,
    /// A slot per node of every live frame, in frame order.
    slots: Vec<Option<D>>,
    frames: Vec<Frame>,
    steps: u64,
    max_depth: usize,
    /// The most frames the run may hold at once, the entry included.
    bound: Option<u64>,
    /// The slot the last step filled.
    latest: Option<usize>,
    outcome: Option<Outcome<D>>,
}

impl<'a, D: Concrete> Machine<'a, D> {
    /// A run about to call `function` on `args`, one per parameter, that
    /// will hold at most `bound` frames at once.
    pub fn new(graph: &'a Graph, function: FunctionId, args: &[D], bound: Option<u64>) -> Self {
        let run = graph.run(function);
        assert_eq!(args.len(), run.params().len(), "one argument per parameter");
        let mut machine = Self {
            graph,
            control: Vec::new(),
            slots: Vec::new(),
            frames: Vec::new(),
            steps: 0,
            max_depth: 0,
            bound,
            latest: None,
            outcome: None,
        };
        machine.enter(function, args);
        machine
    }

    /// Values computed so far: every node evaluated, in every frame, a
    /// parameter's binding not among them.
    pub fn steps(&self) -> u64 {
        self.steps
    }

    /// Frames live right now.
    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    /// The most frames live at once so far.
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// The value the last step produced, if it produced one: every value
    /// a run makes appears here once.
    pub fn latest(&self) -> Option<&D> {
        self.latest.and_then(|slot| self.slots[slot].as_ref())
    }

    /// How the run ended, once it has.
    pub fn outcome(&self) -> Option<&Outcome<D>> {
        self.outcome.as_ref()
    }

    /// Step until the run ends.
    pub fn run(mut self) -> Outcome<D> {
        while !self.step() {}
        self.outcome.expect("a finished run has its outcome")
    }

    /// Do one unit of work: whether the run has ended. A finished machine
    /// stays finished.
    pub fn step(&mut self) -> bool {
        if self.outcome.is_some() {
            return true;
        }
        self.latest = None;
        let Some(control) = self.control.pop() else {
            let frame = self.frames.last().expect("the entry frame stays");
            let result = self.graph.run(frame.function).result();
            let value = self
                .slot(result)
                .clone()
                .expect("a finished run has its value");
            self.outcome = Some(Outcome::Value(value));
            return true;
        };
        if let Err(refusal) = self.apply(control) {
            self.outcome = Some(Outcome::Refused(refusal));
            return true;
        }
        false
    }

    /// The slot of `node` in the current frame.
    fn index(&self, node: NodeId) -> usize {
        let frame = self.frames.last().expect("a running machine has a frame");
        debug_assert!(self.graph.run(frame.function).holds(node));
        frame.base + node.index() - frame.first
    }

    fn slot(&self, node: NodeId) -> &Option<D> {
        &self.slots[self.index(node)]
    }

    fn value(&self, node: NodeId) -> &D {
        self.slot(node)
            .as_ref()
            .expect("an input is evaluated before its reader")
    }

    fn fill(&mut self, node: NodeId, value: D) {
        let index = self.index(node);
        self.slots[index] = Some(value);
        self.latest = Some(index);
        self.steps += 1;
    }

    /// Open a frame for `function`, and demand its result. Its parameters
    /// are bound by the caller.
    fn open(&mut self, function: FunctionId) -> usize {
        let run = self.graph.run(function);
        let base = self.slots.len();
        self.slots.resize(base + run.nodes().len(), None);
        self.frames.push(Frame {
            function,
            base,
            first: run.entry().index(),
        });
        self.max_depth = self.max_depth.max(self.frames.len());
        self.control.push(Control::Eval(run.result()));
        base
    }

    /// Open a frame for `function` with its parameters bound to `args`.
    fn enter(&mut self, function: FunctionId, args: &[D]) {
        let base = self.open(function);
        let run = self.graph.run(function);
        for (param, arg) in run.params().zip(args) {
            self.slots[base + run.slot(param)] = Some(arg.clone());
        }
    }

    /// The value the region at `region` computes, as the value of `node`.
    fn demand_region(&mut self, node: NodeId, region: RegionId) {
        let result = self.graph.region(region).result();
        self.control.push(Control::Take(node, result));
        self.control.push(Control::Eval(result));
    }

    fn apply(&mut self, control: Control) -> Result<(), Refusal> {
        match control {
            Control::Eval(node) => {
                if self.slot(node).is_some() {
                    return Ok(());
                }
                let inputs = self.graph.inputs(node);
                let op = &self.graph.node(node).op;
                match op {
                    Op::Param(_) => unreachable!("a parameter is bound on entry"),
                    Op::Hole => return Err(Refusal::Hole(node)),
                    Op::Entry | Op::Then | Op::Else => unreachable!("a context is not a value"),
                    Op::And { .. } | Op::Or { .. } => {
                        self.control.push(Control::Lazy(node));
                        self.control.push(Control::Eval(inputs[0]));
                    }
                    Op::Join { .. } => {
                        self.control.push(Control::Branch(node));
                        self.control.push(Control::Eval(inputs[0]));
                    }
                    Op::Call(_) => {
                        self.control.push(Control::Enter(node));
                        for &arg in inputs.iter().rev() {
                            self.control.push(Control::Eval(arg));
                        }
                    }
                    // A data operator: its operands first, then itself.
                    _ => {
                        self.control.push(Control::Apply(node));
                        for &input in inputs[..op.reads(inputs.len())].iter().rev() {
                            self.control.push(Control::Eval(input));
                        }
                    }
                }
            }
            Control::Apply(node) => {
                let op = &self.graph.node(node).op;
                let inputs = self.graph.inputs(node);
                let value = match op.reads(inputs.len()) {
                    0 => op.apply(&[]),
                    1 => op.apply(&[self.value(inputs[0])]),
                    2 => op.apply(&[self.value(inputs[0]), self.value(inputs[1])]),
                    _ => unreachable!("a data operator reads at most two inputs"),
                };
                match value {
                    Ok(value) => self.fill(node, value),
                    Err(fault) => return Err(Refusal::of(fault, node)),
                }
            }
            Control::Lazy(node) => {
                let lhs = self
                    .value(self.graph.inputs(node)[0])
                    .truth()
                    .map_err(|fault| Refusal::of(fault, node))?;
                match self.graph.node(node).op {
                    Op::And { rhs } if lhs => self.demand_region(node, rhs),
                    Op::Or { rhs } if !lhs => self.demand_region(node, rhs),
                    _ => self.fill(node, D::bool(lhs)),
                }
            }
            Control::Branch(node) => {
                let condition = self
                    .value(self.graph.inputs(node)[0])
                    .truth()
                    .map_err(|fault| Refusal::of(fault, node))?;
                let Op::Join { then, else_ } = self.graph.node(node).op else {
                    unreachable!("a branch is an if")
                };
                match (condition, else_) {
                    (true, _) => self.demand_region(node, then),
                    (false, Some(else_)) => self.demand_region(node, else_),
                    (false, None) => self.fill(node, D::unit()),
                }
            }
            Control::Take(node, from) => {
                // A lazy operator whose right operand ran is the operator
                // over both operands; a branch is its arm's value.
                let value = match self.graph.node(node).op {
                    Op::And { .. } | Op::Or { .. } => {
                        let and = matches!(self.graph.node(node).op, Op::And { .. });
                        let lhs = self.value(self.graph.inputs(node)[0]);
                        D::lazy(and, lhs, self.value(from))
                            .map_err(|fault| Refusal::of(fault, node))?
                    }
                    _ => self.value(from).clone(),
                };
                self.fill(node, value);
            }
            Control::Enter(node) => {
                let Op::Call(function) = self.graph.node(node).op else {
                    unreachable!("a call is entered")
                };
                if self
                    .bound
                    .is_some_and(|bound| u64::try_from(self.frames.len()).unwrap() >= bound)
                {
                    return Err(Refusal::Depth(node));
                }
                // The arguments move from the caller's slots into the
                // callee's, by index, so no list of them is built.
                let from: Vec<usize> = self
                    .graph
                    .inputs(node)
                    .iter()
                    .map(|&arg| self.index(arg))
                    .collect();
                self.control.push(Control::Return(node));
                let base = self.open(function);
                let run = self.graph.run(function);
                for (param, from) in run.params().zip(from) {
                    let value = self.slots[from].clone();
                    self.slots[base + run.slot(param)] = value;
                }
            }
            Control::Return(node) => {
                let frame = self.frames.pop().expect("a return has a frame to leave");
                let result = self.graph.run(frame.function).result();
                let value = self.slots[frame.base + result.index() - frame.first]
                    .take()
                    .expect("a callee's result is in before it returns");
                self.slots.truncate(frame.base);
                self.fill(node, value);
            }
        }
        Ok(())
    }
}
