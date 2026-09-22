//! The machine: the graph evaluated in the concrete domain by demand from a function's result. It
//! refuses rather than fails: no [`Refusal`] arises on a graph the checker proved.

use crate::{Domain, Fault, FunctionId, Graph, NodeId, Op, RegionId, Run, Value};

#[path = "suspend.rs"]
mod suspend;
use suspend::Suspensions;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Control {
    Eval(NodeId),
    Apply(NodeId),
    LoopBounds(NodeId),
    LoopStart(NodeId),
    LoopNext(NodeId),
    LoopRebind(NodeId),
    LoopValue {
        node: NodeId,
        from: NodeId,
    },
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
    Phi(NodeId),
    Sequence {
        node: NodeId,
        value: NodeId,
    },
    Observe {
        node: NodeId,
        then: Option<RegionId>,
        else_: Option<RegionId>,
    },
    CompleteObserve(NodeId),
    ResultBody {
        node: NodeId,
        body: NodeId,
    },
    Return(NodeId),
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
    ResumeCaller(NodeId),
    ResumePackedCaller(NodeId),
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
    control_base: usize,
    /// Logical depth includes callers whose storage has been reused.
    depth: usize,
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
    /// The active frame is dense; suspended frames may hold only their continuation's live slots.
    slots: Vec<Option<Value>>,
    frames: Vec<Frame<'a>>,
    steps: u64,
    max_depth: usize,
    bound: Option<u64>,
    latest: Option<usize>,
    outcome: Option<Result<Value, Refusal>>,
    tail_args: Vec<Value>,
    suspensions: Suspensions,
    /// The active frame's slot for node `n` is `n.index() + offset`, wrapping.
    offset: usize,
}

impl<'a> Machine<'a> {
    /// `args` is one per parameter, their types unchecked; `bound` caps [`Self::depth`].
    pub fn new(graph: &'a Graph, function: FunctionId, args: &[Value], bound: Option<u64>) -> Self {
        let run = graph.run(function);
        assert_eq!(args.len(), run.params().len(), "one argument per parameter");
        let mut machine = Self {
            graph,
            control: Vec::with_capacity(64),
            slots: Vec::with_capacity(4 * run.nodes().len()),
            frames: Vec::with_capacity(8),
            steps: 0,
            max_depth: 0,
            bound,
            latest: None,
            outcome: None,
            tail_args: Vec::new(),
            suspensions: Suspensions::new(),
            offset: 0,
        };
        let base = machine.open(function);
        bind(&mut machine.slots[base..], run, args.iter().cloned());
        machine
    }

    /// Values computed so far; parameter, loop-index, and carry bindings are not computations.
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

    /// Consuming execution may reuse frame storage; both modes reuse loop-body slots each iteration.
    pub fn run(mut self) -> Result<Value, Refusal> {
        if let Some(outcome) = self.outcome {
            return outcome;
        }
        loop {
            if let Some(outcome) = self.advance::<true>() {
                return outcome;
            }
        }
    }

    /// The outcome once the run has ended, and it stays ended.
    pub fn step(&mut self) -> Option<&Result<Value, Refusal>> {
        if self.outcome.is_none()
            && let Some(outcome) = self.advance::<false>()
        {
            self.outcome = Some(outcome);
        }
        self.outcome.as_ref()
    }

    /// One step of a run that has not ended; the outcome when this one ends it.
    fn advance<const TAIL: bool>(&mut self) -> Option<Result<Value, Refusal>> {
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
            Some(control) => self.apply::<TAIL>(control).err().map(Err),
        }
    }

    fn index(&self, node: NodeId) -> usize {
        debug_assert!(
            self.frames
                .last()
                .is_some_and(|frame| frame.base + frame.run.slot(node)
                    == node.index().wrapping_add(self.offset)),
            "the offset tracks the active frame"
        );
        node.index().wrapping_add(self.offset)
    }

    fn refocus(&mut self) {
        if let Some(frame) = self.frames.last() {
            self.offset = frame.base.wrapping_sub(frame.run.entry().index());
        }
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
        let control_base = self.control.len();
        let depth = self.frames.last().map_or(1, |frame| frame.depth + 1);
        self.frames.push(Frame {
            run,
            base,
            control_base,
            depth,
        });
        self.refocus();
        self.max_depth = self.max_depth.max(depth);
        self.control.push(Control::Eval(run.result()));
        base
    }

    /// Evaluate `region`'s result, then `take` it.
    fn demand_region(&mut self, region: RegionId, take: impl FnOnce(NodeId) -> Control) {
        let from = self.graph.region(region).result();
        self.control.push(take(from));
        self.control.push(Control::Eval(from));
    }

    fn tail(&self, mut value: NodeId) -> bool {
        let frame = self.frames.last().expect("a call has a caller");
        for control in self.control[frame.control_base..].iter().rev() {
            match *control {
                Control::Take { node, from } if from == value => value = node,
                Control::Return(from) if from == value => return true,
                Control::Apply(node)
                    if matches!(
                        self.graph.node(node).op,
                        Op::Copy { .. } | Op::Assign { .. }
                    ) && self.graph.inputs(node)[0] == value =>
                {
                    value = node
                }
                _ => return false,
            }
        }
        value == frame.run.result()
    }

    /// `node` is a data operator whose inputs are all in.
    fn compute(&mut self, node: NodeId) -> Result<(), Refusal> {
        let op = &self.graph.node(node).op;
        let value = match *self.graph.inputs(node) {
            [] => op.apply(&[]),
            [a] => op.apply(&[self.value(a)]),
            [a, b] => op.apply(&[self.value(a), self.value(b)]),
            _ => unreachable!("a data operator has at most two inputs"),
        };
        let value = value.map_err(|fault| Refusal::of(fault, node))?;
        self.fill(node, value);
        Ok(())
    }

    fn demand(&mut self, node: NodeId) {
        if self.slot(node).is_none() {
            self.control.push(Control::Eval(node));
        }
    }

    fn apply<const TAIL: bool>(&mut self, control: Control) -> Result<(), Refusal> {
        match control {
            Control::Eval(node) => {
                if self.slot(node).is_some() {
                    return Ok(());
                }
                let inputs = self.graph.inputs(node);
                match self.graph.node(node).op {
                    Op::Param { .. } | Op::LoopIndex | Op::Carry { .. } => {
                        unreachable!("parameters and loop headers are bound on entry")
                    }
                    Op::Loop(_) => {
                        self.control.push(Control::LoopBounds(node));
                        for &input in inputs.iter().rev() {
                            self.demand(input);
                        }
                    }
                    Op::LoopValue { loop_, index } => {
                        let from = self.graph.loop_(loop_).carried[index as usize].0;
                        self.control.push(Control::LoopValue { node, from });
                        self.demand(inputs[0]);
                    }
                    Op::Hole => return Err(Refusal::Hole(node)),
                    Op::Entry | Op::Then | Op::Else | Op::Unused => {
                        unreachable!("a context or a statement is not a value")
                    }
                    Op::After => unreachable!("a continuation context is not a value"),
                    Op::Unit => self.fill(node, Value::Unit),
                    Op::Return => {
                        self.control.push(Control::Return(inputs[0]));
                        self.demand(inputs[0]);
                    }
                    Op::Sequence => {
                        self.control.push(Control::Sequence {
                            node,
                            value: inputs[1],
                        });
                        self.demand(inputs[0]);
                    }
                    Op::Observe { then, else_ } => {
                        self.control.push(Control::Observe { node, then, else_ });
                        self.demand(inputs[0]);
                    }
                    Op::Result { .. } => {
                        let body = inputs[0];
                        let region = self
                            .frames
                            .last()
                            .expect("a result has a frame")
                            .run
                            .region();
                        if let Some(control) = self.graph.region(region).control() {
                            self.control.push(Control::ResultBody { node, body });
                            self.demand(control);
                        } else {
                            self.control.push(Control::Take { node, from: body });
                            self.demand(body);
                        }
                    }
                    ref op @ (Op::And { rhs } | Op::Or { rhs }) => {
                        let and = matches!(op, Op::And { .. });
                        self.control.push(Control::Lazy { node, and, rhs });
                        self.demand(inputs[0]);
                    }
                    Op::Join { then, else_ } => {
                        self.control.push(Control::Branch { node, then, else_ });
                        self.demand(inputs[0]);
                    }
                    Op::Phi { .. } => {
                        self.control.push(Control::Phi(node));
                        self.demand(inputs[0]);
                    }
                    Op::Call(callee) => {
                        let function = self.graph.callable(callee).function;
                        self.control.push(Control::Enter { node, function });
                        for &arg in inputs.iter().rev() {
                            self.demand(arg);
                        }
                    }
                    _ => {
                        let pending = self.control.len();
                        self.control.push(Control::Apply(node));
                        for &input in inputs.iter().rev() {
                            self.demand(input);
                        }
                        if self.control.len() == pending + 1 {
                            self.control.pop();
                            return self.compute(node);
                        }
                    }
                }
            }
            Control::LoopBounds(node) => {
                let [start, end] = *self.graph.inputs(node) else {
                    unreachable!()
                };
                if !matches!(
                    (self.value(start), self.value(end)),
                    (Value::Int(_), Value::Int(_))
                ) {
                    return Err(Refusal::Type(node));
                }
                let Op::Loop(id) = self.graph.node(node).op else {
                    unreachable!()
                };
                self.control.push(Control::LoopStart(node));
                for &(carry, _) in self.graph.loop_(id).carried.iter().rev() {
                    self.control
                        .push(Control::Eval(self.graph.inputs(carry)[0]));
                }
            }
            Control::LoopStart(node) | Control::LoopRebind(node) => {
                let Op::Loop(id) = self.graph.node(node).op else {
                    unreachable!()
                };
                let loop_ = self.graph.loop_(id);
                let initial = matches!(control, Control::LoopStart(_));
                let Value::Int(index) = self.value(if initial {
                    self.graph.inputs(node)[0]
                } else {
                    loop_.index
                }) else {
                    unreachable!()
                };
                let index = if initial {
                    index.clone()
                } else {
                    index + &1.into()
                };
                let values: Vec<_> = loop_
                    .carried
                    .iter()
                    .map(|&(carry, next)| {
                        self.value(if initial {
                            self.graph.inputs(carry)[0]
                        } else {
                            next
                        })
                        .clone()
                    })
                    .collect();
                for body_node in self.graph.region(loop_.body).nodes() {
                    let slot = self.index(body_node);
                    self.slots[slot] = None;
                }
                for (&(carry, _), value) in loop_.carried.iter().zip(values) {
                    let slot = self.index(carry);
                    self.slots[slot] = Some(value);
                }
                let Value::Int(end) = self.value(self.graph.inputs(node)[1]) else {
                    unreachable!()
                };
                let more = index < *end;
                let slot = self.index(loop_.index);
                self.slots[slot] = Some(Value::Int(index));
                if more {
                    self.control.push(Control::LoopNext(node));
                    self.control
                        .push(Control::Eval(self.graph.region(loop_.body).result()));
                    if let Some(control) = self.graph.region(loop_.body).control() {
                        self.demand(control);
                    }
                } else {
                    self.fill(node, Value::Unit);
                }
            }
            Control::LoopNext(node) => {
                let Op::Loop(id) = self.graph.node(node).op else {
                    unreachable!()
                };
                let loop_ = self.graph.loop_(id);
                if self.value(self.graph.region(loop_.body).result()) != &Value::Unit {
                    return Err(Refusal::Type(node));
                }
                self.control.push(Control::LoopRebind(node));
                for &(_, next) in loop_.carried.iter().rev() {
                    self.demand(next);
                }
            }
            Control::LoopValue { node, from } => self.fill(node, self.value(from).clone()),
            Control::Apply(node) => return self.compute(node),
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
            Control::Phi(node) => {
                let inputs = self.graph.inputs(node);
                let condition = self
                    .value(inputs[0])
                    .truth()
                    .map_err(|fault| Refusal::of(fault, node))?;
                let from = inputs[if condition { 1 } else { 2 }];
                self.control.push(Control::Take { node, from });
                self.demand(from);
            }
            Control::Sequence { node, value } => {
                self.control.push(Control::Take { node, from: value });
                self.demand(value);
            }
            Control::Observe { node, then, else_ } => {
                let condition = self
                    .value(self.graph.inputs(node)[0])
                    .truth()
                    .map_err(|fault| Refusal::of(fault, node))?;
                let region = if condition { then } else { else_ };
                if let Some(control) = region.and_then(|region| self.graph.region(region).control())
                {
                    self.control.push(Control::CompleteObserve(node));
                    self.demand(control);
                } else {
                    self.fill(node, Value::Unit);
                }
            }
            Control::CompleteObserve(node) => self.fill(node, Value::Unit),
            Control::ResultBody { node, body } => {
                self.control.push(Control::Take { node, from: body });
                self.demand(body);
            }
            Control::Return(payload) => {
                let value = self.value(payload).clone();
                let frame = self.frames.last().expect("a return has a frame");
                self.control.truncate(frame.control_base);
                self.fill(frame.run.result(), value);
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
                if self.bound.is_some_and(|bound| {
                    self.frames.last().expect("a call has a caller").depth as u64 >= bound
                }) {
                    return Err(Refusal::Depth(node));
                }
                if TAIL && self.tail(node) {
                    let frame = self.frames.last().expect("a call has a caller");
                    for &arg in self.graph.inputs(node) {
                        self.tail_args.push(
                            self.slots[frame.base + frame.run.slot(arg)]
                                .clone()
                                .expect("an argument is evaluated before the call"),
                        );
                    }
                    let frame = self.frames.last_mut().expect("a call has a caller");
                    self.control.truncate(frame.control_base);
                    self.slots.truncate(frame.base);
                    frame.run = self.graph.run(function);
                    frame.depth += 1;
                    self.offset = frame.base.wrapping_sub(frame.run.entry().index());
                    self.max_depth = self.max_depth.max(frame.depth);
                    self.slots
                        .resize(frame.base + frame.run.nodes().len(), None);
                    bind(
                        &mut self.slots[frame.base..],
                        frame.run,
                        self.tail_args.drain(..),
                    );
                    self.control.push(Control::Eval(frame.run.result()));
                    return Ok(());
                }
                let caller = self.frames.last().expect("a call has a caller");
                let (caller_base, caller_run) = (caller.base, caller.run);
                if TAIL
                    && caller_run.nodes().len() * size_of::<Option<Value>>() >= 4096
                    && self
                        .bound
                        .is_none_or(|bound| bound.saturating_sub(caller.depth as u64) > 1)
                {
                    let layout = self.suspensions.slots(
                        self.graph,
                        caller_run,
                        node,
                        &self.control[caller.control_base..],
                    );
                    if let Some(layout) = layout {
                        for &arg in self.graph.inputs(node) {
                            self.tail_args.push(
                                self.slots[caller_base + caller_run.slot(arg)]
                                    .clone()
                                    .unwrap(),
                            );
                        }
                        for (packed, &slot) in layout.iter().enumerate() {
                            let value = self.slots[caller_base + slot].take();
                            self.slots[caller_base + packed] = value;
                        }
                        self.slots.truncate(caller_base + layout.len());
                        self.control.push(Control::ResumePackedCaller(node));
                        let base = self.open(function);
                        bind(
                            &mut self.slots[base..],
                            self.graph.run(function),
                            self.tail_args.drain(..),
                        );
                        return Ok(());
                    }
                }
                self.control.push(Control::ResumeCaller(node));
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
            Control::ResumeCaller(node) | Control::ResumePackedCaller(node) => {
                let frame = self.frames.pop().expect("a return has a frame to leave");
                self.refocus();
                let value = self.slots[frame.base + frame.run.slot(frame.run.result())]
                    .take()
                    .expect("a callee's result is in before it returns");
                self.slots.truncate(frame.base);
                if matches!(control, Control::ResumePackedCaller(_)) {
                    let caller = self.frames.last().unwrap();
                    let layout = self.suspensions.saved(node);
                    self.slots
                        .resize(caller.base + caller.run.nodes().len(), None);
                    for (packed, &slot) in layout.iter().enumerate().rev() {
                        let value = self.slots[caller.base + packed].take();
                        self.slots[caller.base + slot] = value;
                    }
                }
                self.fill(node, value);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ArithOp, BinaryOp, GraphBuilder};
    use sumi_text::{TextRange, TextSize};

    fn at() -> TextRange {
        TextRange::new(TextSize::new(0), TextSize::new(0))
    }

    fn push(builder: &mut GraphBuilder, op: Op, inputs: &[NodeId]) -> NodeId {
        let inputs = inputs.iter().map(|&node| (node, at())).collect::<Vec<_>>();
        builder.push(op, &inputs, at(), None)
    }

    #[test]
    fn loops_bind_simultaneously_and_survive_suspension() {
        for (start, end, expected) in [(2, 2, 29), (4, 2, 29), (2, 5, 92)] {
            for returning in [false, true] {
                let mut builder = GraphBuilder::new(400);
                let leaf = builder.function();
                let caller = builder.function();
                let callee = builder.declare(leaf, Box::new([crate::Ty::Int]));
                let run = builder.open_run(leaf);
                let entry = push(&mut builder, Op::Entry, &[]);
                let param = push(
                    &mut builder,
                    Op::Param {
                        index: 0,
                        ty: Some(crate::Ty::Int),
                    },
                    &[],
                );
                let region = builder.open(entry);
                builder.enter(region);
                builder.close(region, param);
                builder.close_run(run, region, param);
                let run = builder.open_run(caller);
                let entry = push(&mut builder, Op::Entry, &[]);
                let region = builder.open(entry);
                builder.enter(region);
                for _ in 0..300 {
                    push(&mut builder, Op::Int(0.into()), &[]);
                }
                let start = push(&mut builder, Op::Int(start.into()), &[]);
                let end = push(&mut builder, Op::Int(end.into()), &[]);
                let a = push(&mut builder, Op::Int(2.into()), &[]);
                let b = push(&mut builder, Op::Int(9.into()), &[]);
                let body = builder.open(entry);
                builder.enter(body);
                let index = push(&mut builder, Op::LoopIndex, &[start, end]);
                let ca = push(&mut builder, Op::Carry { declaration: a }, &[a]);
                let cb = push(&mut builder, Op::Carry { declaration: b }, &[b]);
                let next = push(&mut builder, Op::Call(callee), &[ca]);
                let unit = push(&mut builder, Op::Unit, &[entry]);
                let control = returning.then(|| push(&mut builder, Op::Return, &[index, entry]));
                builder.close_with_control(body, unit, true, control);
                let id = builder.push_loop(crate::Loop {
                    body,
                    index,
                    carried: Box::new([(ca, cb), (cb, next)]),
                    continuation: entry,
                    empty: entry,
                });
                let loop_node = push(&mut builder, Op::Loop(id), &[start, end]);
                let va = push(
                    &mut builder,
                    Op::LoopValue {
                        loop_: id,
                        index: 0,
                    },
                    &[loop_node],
                );
                let vb = push(
                    &mut builder,
                    Op::LoopValue {
                        loop_: id,
                        index: 1,
                    },
                    &[loop_node],
                );
                let ten = push(&mut builder, Op::Int(10.into()), &[]);
                let tens = push(
                    &mut builder,
                    Op::Binary(BinaryOp::Arith(ArithOp::Mul)),
                    &[va, ten],
                );
                let result = push(
                    &mut builder,
                    Op::Binary(BinaryOp::Arith(ArithOp::Add)),
                    &[tens, vb],
                );
                builder.close(region, result);
                builder.close_run(run, region, result);
                let graph = builder.finish();
                let mut stepped = Machine::new(&graph, caller, &[], None);
                let mut computed = 0;
                while stepped.step().is_none() {
                    computed += u64::from(stepped.latest().is_some());
                }
                assert_eq!(computed, stepped.steps());
                let expected = if returning && expected == 92 {
                    2
                } else {
                    expected
                };
                assert_eq!(stepped.outcome(), Some(&Ok(Value::Int(expected.into()))));
                let mut fast = Machine::new(&graph, caller, &[], None);
                let mut packed = false;
                let outcome = loop {
                    packed |= fast
                        .control
                        .iter()
                        .any(|c| matches!(c, Control::ResumePackedCaller(_)));
                    if let Some(outcome) = fast.advance::<true>() {
                        break outcome;
                    }
                };
                assert_eq!(stepped.outcome(), Some(&outcome));
                assert_eq!(stepped.steps(), fast.steps());
                assert_eq!(stepped.max_depth(), fast.max_depth());
                if expected == 92 {
                    assert!(packed);
                }
            }
        }
    }

    fn counting_loop(
        builder: &mut GraphBuilder,
        entry: NodeId,
        bounds: [NodeId; 2],
        nested: bool,
    ) -> NodeId {
        let zero = push(builder, Op::Int(0.into()), &[]);
        let body = builder.open(entry);
        builder.enter(body);
        let index = push(builder, Op::LoopIndex, &bounds);
        let carry = push(builder, Op::Carry { declaration: zero }, &[zero]);
        let increment = if nested {
            let two = push(builder, Op::Int(2.into()), &[]);
            counting_loop(builder, entry, [zero, two], false)
        } else {
            push(builder, Op::Int(1.into()), &[])
        };
        let next = push(
            builder,
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            &[carry, increment],
        );
        let unit = push(builder, Op::Unit, &[entry]);
        builder.close(body, unit);
        let id = builder.push_loop(crate::Loop {
            body,
            index,
            carried: Box::new([(carry, next)]),
            continuation: entry,
            empty: entry,
        });
        let node = push(builder, Op::Loop(id), &bounds);
        push(
            builder,
            Op::LoopValue {
                loop_: id,
                index: 0,
            },
            &[node],
        )
    }

    #[test]
    fn nested_loops_reset_only_their_body_and_use_mathematical_bounds() {
        let mut builder = GraphBuilder::new(40);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = push(&mut builder, Op::Entry, &[]);
        let region = builder.open(entry);
        builder.enter(region);
        let start = push(
            &mut builder,
            Op::Int("18446744073709551616".parse().unwrap()),
            &[],
        );
        let end = push(
            &mut builder,
            Op::Int("18446744073709551619".parse().unwrap()),
            &[],
        );
        let result = counting_loop(&mut builder, entry, [start, end], true);
        builder.close(region, result);
        builder.close_run(run, region, result);
        let graph = builder.finish();
        let mut stepped = Machine::new(&graph, function, &[], None);
        let mut bounds_seen = Vec::new();
        while stepped.step().is_none() {
            if let Some(Value::Int(value)) = stepped.latest()
                && value > &100.into()
            {
                bounds_seen.push(value.to_string());
            }
        }
        assert_eq!(
            bounds_seen,
            ["18446744073709551616", "18446744073709551619"]
        );
        assert_eq!(stepped.outcome(), Some(&Ok(Value::Int(6.into()))));
        assert_eq!(
            Machine::new(&graph, function, &[], None).run(),
            Ok(Value::Int(6.into()))
        );
    }

    #[test]
    fn loop_bounds_refuse_types_and_preserve_fault_order() {
        for ops in [
            [Op::Bool(false), Op::Int(2.into())],
            [Op::Int(0.into()), Op::Bool(true)],
            [Op::Hole, Op::Hole],
            [Op::Int(0.into()), Op::Hole],
        ] {
            let mut builder = GraphBuilder::new(20);
            let function = builder.function();
            let run = builder.open_run(function);
            let entry = push(&mut builder, Op::Entry, &[]);
            let region = builder.open(entry);
            builder.enter(region);
            let bounds = ops.clone().map(|op| push(&mut builder, op, &[]));
            let result = counting_loop(&mut builder, entry, bounds, false);
            builder.close(region, result);
            builder.close_run(run, region, result);
            let graph = builder.finish();
            let loop_node = graph.inputs(result)[0];
            let expected = ops
                .iter()
                .position(|op| matches!(op, Op::Hole))
                .map_or(Refusal::Type(loop_node), |index| {
                    Refusal::Hole(bounds[index])
                });
            let mut stepped = Machine::new(&graph, function, &[], None);
            while stepped.step().is_none() {}
            assert_eq!(stepped.outcome(), Some(&Err(expected)));
            assert_eq!(
                Machine::new(&graph, function, &[], None).run(),
                Err(expected)
            );
        }
    }

    #[test]
    fn tail_reuse_preserves_the_logical_depth_limit() {
        for tail in [false, true] {
            let mut builder = GraphBuilder::new(8);
            let functions = [builder.function(), builder.function()];
            let callees = functions.map(|function| builder.declare(function, Box::new([])));
            for (index, function) in functions.into_iter().enumerate() {
                let run = builder.open_run(function);
                let entry = push(&mut builder, Op::Entry, &[]);
                let region = builder.open(entry);
                builder.enter(region);
                let call = push(&mut builder, Op::Call(callees[1 - index]), &[]);
                let result = if tail {
                    push(&mut builder, Op::Copy { declared: None }, &[call])
                } else {
                    let one = push(&mut builder, Op::Int(1.into()), &[]);
                    push(
                        &mut builder,
                        Op::Binary(BinaryOp::Arith(ArithOp::Add)),
                        &[call, one],
                    )
                };
                builder.close(region, result);
                builder.close_run(run, region, result);
            }
            let graph = builder.finish();
            let mut stepped = Machine::new(&graph, functions[0], &[], Some(10_000));
            while stepped.step().is_none() {}
            let mut fast = Machine::new(&graph, functions[0], &[], Some(10_000));
            let mut frames = 1;
            let outcome = loop {
                frames = frames.max(fast.frames.len());
                if let Some(outcome) = fast.advance::<true>() {
                    break outcome;
                }
            };
            assert!(matches!(outcome, Err(Refusal::Depth(_))));
            assert_eq!(stepped.outcome(), Some(&outcome));
            assert_eq!(stepped.max_depth(), 10_000);
            assert_eq!(fast.max_depth(), 10_000);
            assert_eq!(frames, if tail { 1 } else { 10_000 });
        }
    }

    #[test]
    fn root_return_overrides_tail() {
        let mut builder = GraphBuilder::new(5);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = push(&mut builder, Op::Entry, &[]);
        let region = builder.open(entry);
        builder.enter(region);
        let tail = push(&mut builder, Op::Int(1.into()), &[]);
        let payload = push(&mut builder, Op::Int(2.into()), &[]);
        let return_ = push(&mut builder, Op::Return, &[payload, entry]);
        let result = push(
            &mut builder,
            Op::Result { declared: None },
            &[tail, return_],
        );
        builder.close_with_control(region, tail, false, Some(return_));
        builder.close_run(run, region, result);
        let graph = builder.finish();

        assert_eq!(
            Machine::new(&graph, function, &[], None).run(),
            Ok(Value::Int(2.into()))
        );
    }

    #[test]
    fn callee_return_resumes_caller_computation() {
        let mut builder = GraphBuilder::new(10);
        let callee = builder.function();
        let caller = builder.function();
        let callable = builder.declare(callee, Box::new([]));

        let run = builder.open_run(callee);
        let entry = push(&mut builder, Op::Entry, &[]);
        let region = builder.open(entry);
        builder.enter(region);
        let tail = push(&mut builder, Op::Int(9.into()), &[]);
        let payload = push(&mut builder, Op::Int(4.into()), &[]);
        let return_ = push(&mut builder, Op::Return, &[payload, entry]);
        let result = push(
            &mut builder,
            Op::Result { declared: None },
            &[tail, return_],
        );
        builder.close_with_control(region, tail, false, Some(return_));
        builder.close_run(run, region, result);

        let run = builder.open_run(caller);
        let entry = push(&mut builder, Op::Entry, &[]);
        let region = builder.open(entry);
        builder.enter(region);
        let call = push(&mut builder, Op::Call(callable), &[]);
        let one = push(&mut builder, Op::Int(1.into()), &[]);
        let sum = push(
            &mut builder,
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            &[call, one],
        );
        builder.close(region, sum);
        builder.close_run(run, region, sum);
        let graph = builder.finish();

        assert_eq!(
            Machine::new(&graph, caller, &[], None).run(),
            Ok(Value::Int(5.into()))
        );
    }

    #[test]
    fn observe_demands_only_selected_control() {
        let mut builder = GraphBuilder::new(9);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = push(&mut builder, Op::Entry, &[]);
        let then = builder.open(entry);
        let else_ = builder.open(entry);
        builder.enter(then);
        let selected = push(&mut builder, Op::Int(3.into()), &[]);
        let selected_return = push(&mut builder, Op::Return, &[selected, entry]);
        builder.close_with_control(then, selected, false, Some(selected_return));
        builder.enter(else_);
        let unselected = push(&mut builder, Op::Int(8.into()), &[]);
        let unselected_return = push(&mut builder, Op::Return, &[unselected, entry]);
        builder.close_with_control(else_, unselected, false, Some(unselected_return));
        let region = builder.open(entry);
        builder.enter(region);
        let condition = push(&mut builder, Op::Bool(true), &[]);
        let observe = push(
            &mut builder,
            Op::Observe {
                then: Some(then),
                else_: Some(else_),
            },
            &[condition, entry],
        );
        let tail = push(&mut builder, Op::Int(1.into()), &[]);
        let result = push(&mut builder, Op::Result { declared: None }, &[tail]);
        builder.close_with_control(region, tail, false, Some(observe));
        builder.close_run(run, region, result);
        let graph = builder.finish();

        assert_eq!(
            Machine::new(&graph, function, &[], None).run(),
            Ok(Value::Int(3.into()))
        );
    }

    #[test]
    fn phi_demands_only_its_selected_version() {
        let mut builder = GraphBuilder::new(9);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = push(&mut builder, Op::Entry, &[]);
        let region = builder.open(entry);
        builder.enter(region);
        let zero = push(&mut builder, Op::Int(0.into()), &[]);
        let declaration = push(&mut builder, Op::Copy { declared: None }, &[zero]);
        let seven = push(&mut builder, Op::Int(7.into()), &[]);
        let nine = push(&mut builder, Op::Int(9.into()), &[]);
        let hole = push(&mut builder, Op::Hole, &[]);
        let yes = push(&mut builder, Op::Bool(true), &[]);
        let no = push(&mut builder, Op::Bool(false), &[]);
        let from_true = push(
            &mut builder,
            Op::Phi {
                declaration,
                contexts: [entry; 2],
            },
            &[yes, seven, hole],
        );
        let from_false = push(
            &mut builder,
            Op::Phi {
                declaration,
                contexts: [entry; 2],
            },
            &[no, hole, nine],
        );
        let sum = push(
            &mut builder,
            Op::Binary(BinaryOp::Arith(ArithOp::Add)),
            &[from_true, from_false],
        );
        builder.close(region, sum);
        builder.close_run(run, region, sum);
        let graph = builder.finish();

        assert_eq!(
            Machine::new(&graph, function, &[], None).run(),
            Ok(Value::Int(16.into()))
        );
    }

    #[test]
    fn sequence_continues_after_an_unselected_return() {
        let mut builder = GraphBuilder::new(7);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = push(&mut builder, Op::Entry, &[]);
        let then = builder.open(entry);
        builder.enter(then);
        let payload = push(&mut builder, Op::Int(3.into()), &[]);
        let return_ = push(&mut builder, Op::Return, &[payload, entry]);
        builder.close_with_control(then, payload, false, Some(return_));
        let region = builder.open(entry);
        builder.enter(region);
        let condition = push(&mut builder, Op::Bool(false), &[]);
        let observe = push(
            &mut builder,
            Op::Observe {
                then: Some(then),
                else_: None,
            },
            &[condition, entry],
        );
        let tail = push(&mut builder, Op::Int(1.into()), &[]);
        let sequence = push(&mut builder, Op::Sequence, &[observe, tail]);
        builder.close(region, sequence);
        builder.close_run(run, region, sequence);
        let graph = builder.finish();

        assert_eq!(
            Machine::new(&graph, function, &[], None).run(),
            Ok(Value::Int(1.into()))
        );
    }

    #[test]
    fn nested_payload_return_wins() {
        let mut builder = GraphBuilder::new(6);
        let function = builder.function();
        let run = builder.open_run(function);
        let entry = push(&mut builder, Op::Entry, &[]);
        let region = builder.open(entry);
        builder.enter(region);
        let tail = push(&mut builder, Op::Int(0.into()), &[]);
        let payload = push(&mut builder, Op::Int(7.into()), &[]);
        let inner = push(&mut builder, Op::Return, &[payload, entry]);
        let outer = push(&mut builder, Op::Return, &[inner, entry]);
        let result = push(
            &mut builder,
            Op::Result { declared: None },
            &[tail, inner, outer],
        );
        builder.close_with_control(region, tail, false, Some(outer));
        builder.close_run(run, region, result);
        let graph = builder.finish();

        assert_eq!(
            Machine::new(&graph, function, &[], None).run(),
            Ok(Value::Int(7.into()))
        );
    }

    #[test]
    fn suspended_shared_values_preserve_steps_and_depth() {
        for padding in [0, 300] {
            let mut builder = GraphBuilder::new(padding + 10);
            let leaf = builder.function();
            let caller = builder.function();
            let callee = builder.declare(leaf, Box::new([crate::Ty::Int; 2]));
            let run = builder.open_run(leaf);
            let entry = push(&mut builder, Op::Entry, &[]);
            let params = [0, 1].map(|index| {
                push(
                    &mut builder,
                    Op::Param {
                        index,
                        ty: Some(crate::Ty::Int),
                    },
                    &[],
                )
            });
            let region = builder.open(entry);
            builder.enter(region);
            let difference = push(
                &mut builder,
                Op::Binary(BinaryOp::Arith(ArithOp::Sub)),
                &params,
            );
            builder.close(region, difference);
            builder.close_run(run, region, difference);
            let run = builder.open_run(caller);
            let entry = push(&mut builder, Op::Entry, &[]);
            let region = builder.open(entry);
            builder.enter(region);
            for _ in 0..padding {
                push(&mut builder, Op::Int(0.into()), &[]);
            }
            let value = push(&mut builder, Op::Int(4_294_967_296_i64.into()), &[]);
            let square = push(
                &mut builder,
                Op::Binary(BinaryOp::Arith(ArithOp::Mul)),
                &[value, value],
            );
            let call = push(&mut builder, Op::Call(callee), &[square, square]);
            let inner = push(
                &mut builder,
                Op::Binary(BinaryOp::Arith(ArithOp::Add)),
                &[call, square],
            );
            let result = push(
                &mut builder,
                Op::Binary(BinaryOp::Arith(ArithOp::Add)),
                &[square, inner],
            );
            builder.close(region, result);
            builder.close_run(run, region, result);
            let graph = builder.finish();
            for bound in [Some(1), Some(2), Some(8), None] {
                let mut reference = Machine::new(&graph, caller, &[], bound);
                while reference.step().is_none() {}
                let mut fast = Machine::new(&graph, caller, &[], bound);
                let outcome = loop {
                    if let Some(outcome) = fast.advance::<true>() {
                        break outcome;
                    }
                };
                assert_eq!(reference.outcome(), Some(&outcome));
                assert_eq!(fast.steps(), reference.steps());
                assert_eq!(fast.max_depth(), reference.max_depth());
                if bound == Some(1) {
                    assert_eq!(outcome, Err(Refusal::Depth(call)));
                    assert_eq!(fast.steps(), 2);
                } else {
                    assert_eq!(
                        outcome,
                        Ok(Value::Int("36893488147419103232".parse().unwrap()))
                    );
                    assert_eq!(fast.steps(), 6);
                    assert_eq!(fast.max_depth(), 2);
                }
            }
        }
    }
}
