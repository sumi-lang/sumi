//! The machine: the graph evaluated in the concrete domain by demand from a function's result. It
//! refuses rather than fails: no [`Refusal`] arises on a graph the checker proved.

use crate::{Domain, Fault, FunctionId, Graph, NodeId, Op, RegionId, Run, Value};

#[derive(Clone, Copy, Debug)]
enum Control {
    Eval(NodeId),
    Apply(NodeId),
    /// `&&` when `and`, else `||`, once its left operand is in.
    Lazy {
        node: NodeId,
        and: bool,
        rhs: RegionId,
    },
    Branch {
        node: NodeId,
        then: RegionId,
        else_: Option<RegionId>,
    },
    Enter {
        node: NodeId,
        function: FunctionId,
    },
    Take {
        node: NodeId,
        from: NodeId,
    },
    /// `node`, a lazy operator, combines its left operand with `from`'s value.
    Combine {
        node: NodeId,
        from: NodeId,
        and: bool,
    },
    Return(NodeId),
}

fn bind(slots: &mut [Option<Value>], run: &Run, args: impl IntoIterator<Item = Value>) {
    for (param, arg) in run.params().zip(args) {
        slots[run.slot(param)] = Some(arg);
    }
}

#[derive(Debug)]
struct Frame<'a> {
    run: &'a Run,
    base: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    Hole(NodeId),
    Division(NodeId),
    Type(NodeId),
    /// A call with other than one argument per parameter.
    Arity(NodeId),
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

#[derive(Debug)]
pub struct Machine<'a> {
    graph: &'a Graph,
    control: Vec<Control>,
    /// Every live frame's slots, contiguous, in frame order.
    slots: Vec<Option<Value>>,
    frames: Vec<Frame<'a>>,
    steps: u64,
    max_depth: usize,
    bound: Option<u64>,
    latest: Option<usize>,
    outcome: Option<Result<Value, Refusal>>,
}

impl<'a> Machine<'a> {
    /// `args` is one per parameter, their types unchecked; `bound` caps [`Self::depth`].
    pub fn new(graph: &'a Graph, function: FunctionId, args: &[Value], bound: Option<u64>) -> Self {
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
        let base = machine.open(function);
        bind(&mut machine.slots[base..], run, args.iter().cloned());
        machine
    }

    /// Values computed so far, one per node evaluated per frame; binding a parameter is not one.
    pub fn steps(&self) -> u64 {
        self.steps
    }

    /// Frames live now, the entry counted.
    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// Every value a run computes appears here once.
    pub fn latest(&self) -> Option<&Value> {
        self.latest.and_then(|slot| self.slots[slot].as_ref())
    }

    pub fn outcome(&self) -> Option<&Result<Value, Refusal>> {
        self.outcome.as_ref()
    }

    pub fn run(mut self) -> Result<Value, Refusal> {
        if let Some(outcome) = self.outcome {
            return outcome;
        }
        loop {
            if let Some(outcome) = self.advance() {
                return outcome;
            }
        }
    }

    /// The outcome once the run has ended, and it stays ended.
    pub fn step(&mut self) -> Option<&Result<Value, Refusal>> {
        if self.outcome.is_none()
            && let Some(outcome) = self.advance()
        {
            self.outcome = Some(outcome);
        }
        self.outcome.as_ref()
    }

    /// One step of a run that has not ended; the outcome when this one ends it.
    fn advance(&mut self) -> Option<Result<Value, Refusal>> {
        self.latest = None;
        match self.control.pop() {
            None => {
                let result = self
                    .frames
                    .last()
                    .expect("the entry frame stays")
                    .run
                    .result();
                let index = self.index(result);
                let value = self.slots[index]
                    .take()
                    .expect("a finished run has its value");
                Some(Ok(value))
            }
            Some(control) => self.apply(control).err().map(Err),
        }
    }

    fn index(&self, node: NodeId) -> usize {
        let frame = self.frames.last().expect("a running machine has a frame");
        frame.base + frame.run.slot(node)
    }

    fn slot(&self, node: NodeId) -> &Option<Value> {
        &self.slots[self.index(node)]
    }

    fn value(&self, node: NodeId) -> &Value {
        self.slot(node)
            .as_ref()
            .expect("an input is evaluated before its reader")
    }

    fn fill(&mut self, node: NodeId, value: Value) {
        let index = self.index(node);
        self.slots[index] = Some(value);
        self.latest = Some(index);
        self.steps += 1;
    }

    fn open(&mut self, function: FunctionId) -> usize {
        let run = self.graph.run(function);
        let base = self.slots.len();
        self.slots.resize(base + run.nodes().len(), None);
        self.frames.push(Frame { run, base });
        self.max_depth = self.max_depth.max(self.frames.len());
        self.control.push(Control::Eval(run.result()));
        base
    }

    /// Evaluate `region`'s result, then `take` it.
    fn demand_region(&mut self, region: RegionId, take: impl FnOnce(NodeId) -> Control) {
        let from = self.graph.region(region).result();
        self.control.push(take(from));
        self.control.push(Control::Eval(from));
    }

    fn apply(&mut self, control: Control) -> Result<(), Refusal> {
        match control {
            Control::Eval(node) => {
                if self.slot(node).is_some() {
                    return Ok(());
                }
                let inputs = self.graph.inputs(node);
                match self.graph.node(node).op {
                    Op::Param { .. } => unreachable!("a parameter is bound on entry"),
                    Op::Hole => return Err(Refusal::Hole(node)),
                    Op::Entry | Op::Then | Op::Else | Op::Unused => {
                        unreachable!("a context or a statement is not a value")
                    }
                    Op::Unit => self.fill(node, Value::Unit),
                    ref op @ (Op::And { rhs } | Op::Or { rhs }) => {
                        let and = matches!(op, Op::And { .. });
                        self.control.push(Control::Lazy { node, and, rhs });
                        self.control.push(Control::Eval(inputs[0]));
                    }
                    Op::Join { then, else_ } => {
                        self.control.push(Control::Branch { node, then, else_ });
                        self.control.push(Control::Eval(inputs[0]));
                    }
                    Op::Call(callee) => {
                        let function = self.graph.callable(callee).function;
                        self.control.push(Control::Enter { node, function });
                        for &arg in inputs.iter().rev() {
                            self.control.push(Control::Eval(arg));
                        }
                    }
                    _ => {
                        self.control.push(Control::Apply(node));
                        for &input in inputs.iter().rev() {
                            self.control.push(Control::Eval(input));
                        }
                    }
                }
            }
            Control::Apply(node) => {
                let op = &self.graph.node(node).op;
                let value = match *self.graph.inputs(node) {
                    [] => op.apply(&[]),
                    [a] => op.apply(&[self.value(a)]),
                    [a, b] => op.apply(&[self.value(a), self.value(b)]),
                    _ => unreachable!("a data operator has at most two inputs"),
                };
                match value {
                    Ok(value) => self.fill(node, value),
                    Err(fault) => return Err(Refusal::of(fault, node)),
                }
            }
            Control::Lazy { node, and, rhs } => {
                let lhs = self
                    .value(self.graph.inputs(node)[0])
                    .truth()
                    .map_err(|fault| Refusal::of(fault, node))?;
                if lhs == and {
                    self.demand_region(rhs, |from| Control::Combine { node, from, and });
                } else {
                    self.fill(node, Value::Bool(lhs));
                }
            }
            Control::Branch { node, then, else_ } => {
                let condition = self
                    .value(self.graph.inputs(node)[0])
                    .truth()
                    .map_err(|fault| Refusal::of(fault, node))?;
                let take = |from| Control::Take { node, from };
                match (condition, else_) {
                    (true, _) => self.demand_region(then, take),
                    (false, Some(else_)) => self.demand_region(else_, take),
                    (false, None) => self.fill(node, Value::Unit),
                }
            }
            Control::Take { node, from } => {
                let value = self.value(from).clone();
                self.fill(node, value);
            }
            Control::Combine { node, from, and } => {
                let lhs = self.value(self.graph.inputs(node)[0]);
                let value = Value::lazy(and, lhs, self.value(from))
                    .map_err(|fault| Refusal::of(fault, node))?;
                self.fill(node, value);
            }
            Control::Enter { node, function } => {
                if self.graph.inputs(node).len() != self.graph.run(function).params().len() {
                    return Err(Refusal::Arity(node));
                }
                if self
                    .bound
                    .is_some_and(|bound| u64::try_from(self.frames.len()).unwrap() >= bound)
                {
                    return Err(Refusal::Depth(node));
                }
                let caller = self.frames.last().expect("a call has a caller");
                let (caller_base, caller_run) = (caller.base, caller.run);
                self.control.push(Control::Return(node));
                let base = self.open(function);
                let graph = self.graph;
                let (callers, callee) = self.slots.split_at_mut(base);
                let args = graph.inputs(node).iter().map(|&arg| {
                    callers[caller_base + caller_run.slot(arg)]
                        .clone()
                        .expect("an argument is evaluated before the call")
                });
                bind(callee, graph.run(function), args);
            }
            Control::Return(node) => {
                let frame = self.frames.pop().expect("a return has a frame to leave");
                let value = self.slots[frame.base + frame.run.slot(frame.run.result())]
                    .take()
                    .expect("a callee's result is in before it returns");
                self.slots.truncate(frame.base);
                self.fill(node, value);
            }
        }
        Ok(())
    }
}
