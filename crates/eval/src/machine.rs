//! The abstract machine: an explicit control stack over one body's
//! expression arena, a value stack, and call frames.

use sumi_hir::{
    Args, BinaryOp, Body, ExprId, ExprKind, FunctionId, Int, LocalId, StatementKind, Statements,
};

use crate::{Program, Value};

/// One unit of pending work. `Eval` pushes an expression's value; the rest
/// consume values the stack already holds, or continue a block or call.
#[derive(Clone, Copy, Debug)]
enum Control {
    Eval(ExprId),
    Neg,
    Not,
    /// Combine the top two values.
    Binary(BinaryOp),
    /// Evaluate `rhs` if the top value is true, else keep the false.
    AndRhs(ExprId),
    /// Evaluate `rhs` if the top value is false, else keep the true.
    OrRhs(ExprId),
    /// Choose a branch by the top value; a missing else is unit.
    Branch {
        then_branch: ExprId,
        else_branch: Option<ExprId>,
    },
    /// Move the top value into a local of the current frame.
    Bind(LocalId),
    /// Discard the top value: an expression statement's.
    Drop,
    /// Run the statement at `next`, or the tail, or push unit.
    Block {
        statements: Statements,
        next: u32,
        tail: Option<ExprId>,
    },
    /// Evaluate the argument at `next`, or enter the function with the
    /// arguments on the value stack.
    Call {
        function: FunctionId,
        args: Args,
        next: u32,
    },
    /// Leave the current frame; its result is the top value.
    Return,
}

#[derive(Debug)]
struct Frame {
    function: FunctionId,
    /// Where this frame's locals begin in the shared slab.
    base: usize,
}

/// A run in progress: [`Machine::step`] advances it one unit of work.
#[derive(Debug)]
pub struct Machine<'a> {
    program: Program<'a>,
    control: Vec<Control>,
    values: Vec<Value>,
    frames: Vec<Frame>,
    /// Every live frame's locals, in frame order; a slot is empty until its
    /// parameter or `let` fills it.
    locals: Vec<Option<Value>>,
    steps: u64,
    max_depth: usize,
    /// The most frames the analysis proved this run can hold, when finite.
    bound: Option<u64>,
    /// Set once the run ends; every later step returns it unchanged.
    outcome: Option<Value>,
}

impl<'a> Machine<'a> {
    /// A machine about to call `function` on `args`, which must match the
    /// signature in count and type.
    pub fn new(program: Program<'a>, function: FunctionId, args: &[Value]) -> Self {
        let signature = program.signature(function);
        assert!(
            args.len() == signature.params.len()
                && args
                    .iter()
                    .zip(&signature.params)
                    .all(|(arg, &param)| arg.ty() == param),
            "arguments must match the signature"
        );
        let mut machine = Self {
            program,
            control: Vec::new(),
            values: args.to_vec(),
            frames: Vec::new(),
            locals: Vec::new(),
            steps: 0,
            max_depth: 0,
            bound: program.analysis().depth_bound(function),
            outcome: None,
        };
        machine.enter(function);
        machine
    }

    /// Units of work done so far.
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
    /// The most frames the analysis proved this run can hold at once, the
    /// entry included; `None` when a recursion it reaches has no finite
    /// hull, which still ends, since every recursion has a measure.
    pub fn depth_bound(&self) -> Option<u64> {
        self.bound
    }

    /// Step until the run ends.
    pub fn run(mut self) -> Value {
        loop {
            if let Some(value) = self.step() {
                return value;
            }
        }
    }

    /// Do one unit of work: `None` while the run continues, otherwise its
    /// value. A finished machine keeps returning the value.
    pub fn step(&mut self) -> Option<Value> {
        if self.outcome.is_some() {
            return self.outcome.clone();
        }
        let Some(control) = self.control.pop() else {
            let value = self
                .values
                .last()
                .cloned()
                .expect("a finished run has its value");
            self.outcome = Some(value);
            return self.outcome.clone();
        };
        self.steps += 1;
        self.apply(control);
        None
    }

    fn body(&self) -> &'a Body {
        let frame = self.frames.last().expect("a running machine has a frame");
        self.program
            .function(frame.function)
            .body()
            .expect("a valid file's functions have bodies")
    }

    fn pop(&mut self) -> Value {
        self.values
            .pop()
            .expect("the checker balanced the value stack")
    }
    fn pop_int(&mut self) -> Int {
        match self.pop() {
            Value::Int(value) => value,
            other => unreachable!("the checker typed an int operand; got {other:?}"),
        }
    }
    fn pop_bool(&mut self) -> bool {
        match self.pop() {
            Value::Bool(value) => value,
            other => unreachable!("the checker typed a bool operand; got {other:?}"),
        }
    }

    /// Push a frame for `function`, taking its arguments from the top of
    /// the value stack, and schedule its body.
    fn enter(&mut self, function: FunctionId) {
        assert!(
            self.bound
                .is_none_or(|bound| u64::try_from(self.frames.len()).unwrap() < bound),
            "the checker bounded this run's call depth to {:?} frames, and it is entering frame {}",
            self.bound,
            self.frames.len() + 1
        );
        let body = self
            .program
            .function(function)
            .body()
            .expect("a valid file's functions have bodies");
        let base = self.locals.len();
        self.locals.resize(base + body.locals().len(), None);
        let params = body.params();
        let args = self.values.split_off(self.values.len() - params.len());
        for (&param, arg) in params.iter().zip(args) {
            self.locals[base + param.index()] = Some(arg);
        }
        self.frames.push(Frame { function, base });
        self.max_depth = self.max_depth.max(self.frames.len());
        self.control.push(Control::Return);
        self.control.push(Control::Eval(body.root()));
    }

    fn apply(&mut self, control: Control) {
        let body = self.body();
        match control {
            Control::Eval(id) => self.eval(body, id),
            Control::Neg => {
                let operand = self.pop_int();
                self.values.push(Value::Int(-&operand));
            }
            Control::Not => {
                let operand = self.pop_bool();
                self.values.push(Value::Bool(!operand));
            }
            Control::Binary(op) => {
                let rhs = self.pop();
                let lhs = self.pop();
                self.values.push(binary(op, lhs, rhs));
            }
            Control::AndRhs(rhs) => {
                if self.pop_bool() {
                    self.control.push(Control::Eval(rhs));
                } else {
                    self.values.push(Value::Bool(false));
                }
            }
            Control::OrRhs(rhs) => {
                if self.pop_bool() {
                    self.values.push(Value::Bool(true));
                } else {
                    self.control.push(Control::Eval(rhs));
                }
            }
            Control::Branch {
                then_branch,
                else_branch,
            } => match (self.pop_bool(), else_branch) {
                (true, _) => self.control.push(Control::Eval(then_branch)),
                (false, Some(else_branch)) => self.control.push(Control::Eval(else_branch)),
                (false, None) => self.values.push(Value::Unit),
            },
            Control::Bind(local) => {
                let value = self.pop();
                let base = self
                    .frames
                    .last()
                    .expect("a running machine has a frame")
                    .base;
                self.locals[base + local.index()] = Some(value);
            }
            Control::Drop => {
                self.pop();
            }
            Control::Block {
                statements,
                next,
                tail,
            } => match body.statements(statements).get(next as usize) {
                Some(statement) => {
                    self.control.push(Control::Block {
                        statements,
                        next: next + 1,
                        tail,
                    });
                    match statement.kind {
                        StatementKind::Let { local, initializer } => {
                            self.control.push(Control::Bind(local));
                            self.control.push(Control::Eval(initializer));
                        }
                        StatementKind::Eval(expr) => {
                            self.control.push(Control::Drop);
                            self.control.push(Control::Eval(expr));
                        }
                    }
                }
                None => match tail {
                    Some(tail) => self.control.push(Control::Eval(tail)),
                    None => self.values.push(Value::Unit),
                },
            },
            Control::Call {
                function,
                args,
                next,
            } => match body.args(args).get(next as usize) {
                Some(&arg) => {
                    self.control.push(Control::Call {
                        function,
                        args,
                        next: next + 1,
                    });
                    self.control.push(Control::Eval(arg));
                }
                None => self.enter(function),
            },
            Control::Return => {
                let frame = self.frames.pop().expect("a return has a frame to leave");
                self.locals.truncate(frame.base);
            }
        }
    }

    fn eval(&mut self, body: &Body, id: ExprId) {
        match &body.expression(id).kind {
            ExprKind::Int(value) => self.values.push(Value::Int(value.clone())),
            ExprKind::Bool(value) => self.values.push(Value::Bool(*value)),
            ExprKind::Local(local) => {
                let base = self
                    .frames
                    .last()
                    .expect("a running machine has a frame")
                    .base;
                let value = self.locals[base + local.index()]
                    .clone()
                    .expect("the checker orders a let before its uses");
                self.values.push(value);
            }
            ExprKind::Neg(operand) => {
                self.control.push(Control::Neg);
                self.control.push(Control::Eval(*operand));
            }
            ExprKind::Not(operand) => {
                self.control.push(Control::Not);
                self.control.push(Control::Eval(*operand));
            }
            ExprKind::Binary { op, lhs, rhs } => {
                self.control.push(Control::Binary(*op));
                self.control.push(Control::Eval(*rhs));
                self.control.push(Control::Eval(*lhs));
            }
            ExprKind::And { lhs, rhs } => {
                self.control.push(Control::AndRhs(*rhs));
                self.control.push(Control::Eval(*lhs));
            }
            ExprKind::Or { lhs, rhs } => {
                self.control.push(Control::OrRhs(*rhs));
                self.control.push(Control::Eval(*lhs));
            }
            ExprKind::Call { function, args, .. } => self.control.push(Control::Call {
                function: *function,
                args: *args,
                next: 0,
            }),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.control.push(Control::Branch {
                    then_branch: *then_branch,
                    else_branch: *else_branch,
                });
                self.control.push(Control::Eval(*condition));
            }
            ExprKind::Block { statements, tail } => self.control.push(Control::Block {
                statements: *statements,
                next: 0,
                tail: *tail,
            }),
        }
    }
}

fn binary(op: BinaryOp, lhs: Value, rhs: Value) -> Value {
    match (op, lhs, rhs) {
        (BinaryOp::Eq, lhs, rhs) => Value::Bool(lhs == rhs),
        (BinaryOp::Ne, lhs, rhs) => Value::Bool(lhs != rhs),
        (op, Value::Int(lhs), Value::Int(rhs)) => match op {
            BinaryOp::Add => Value::Int(&lhs + &rhs),
            BinaryOp::Sub => Value::Int(&lhs - &rhs),
            BinaryOp::Mul => Value::Int(&lhs * &rhs),
            // Truncating: the quotient rounds toward zero and the remainder
            // takes the dividend's sign. The checker proved the divisor is
            // not zero wherever this can run.
            BinaryOp::Div => Value::Int(lhs.checked_div(&rhs).expect("a non-zero divisor")),
            BinaryOp::Rem => Value::Int(lhs.checked_rem(&rhs).expect("a non-zero divisor")),
            BinaryOp::Lt => Value::Bool(lhs < rhs),
            BinaryOp::Le => Value::Bool(lhs <= rhs),
            BinaryOp::Gt => Value::Bool(lhs > rhs),
            BinaryOp::Ge => Value::Bool(lhs >= rhs),
            BinaryOp::Eq | BinaryOp::Ne => unreachable!("handled for every type"),
        },
        (op, lhs, rhs) => {
            unreachable!("the checker typed {op:?} over ints; got {lhs:?} and {rhs:?}")
        }
    }
}
