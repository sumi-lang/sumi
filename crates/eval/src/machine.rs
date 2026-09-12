//! The abstract machine: an explicit control stack over one body's
//! expression arena, a value stack, and call frames.

use sumi_hir::{
    Args, BinaryOp, Body, ExprId, ExprKind, FunctionId, LocalId, StatementKind, Statements,
};
use sumi_text::Span;

use crate::{Program, Trap, TrapKind, Value};

/// The most call frames a run may hold at once, the entry included. The
/// limit is the machine's, not the host's: no Sumi call consumes host stack.
pub const MAX_CALL_DEPTH: usize = 1 << 16;

/// One unit of pending work. `Eval` pushes an expression's value; the rest
/// consume values the stack already holds, or continue a block or call.
#[derive(Clone, Copy, Debug)]
enum Control {
    Eval(ExprId),
    /// Negate the top value; `origin` is the negation.
    Neg(ExprId),
    Not,
    /// Combine the top two values; `origin` is the operation.
    Binary {
        op: BinaryOp,
        origin: ExprId,
    },
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
        origin: ExprId,
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
    /// Set once the run ends; every later step returns it unchanged.
    outcome: Option<Result<Value, Trap>>,
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

    /// Step until the run ends.
    pub fn run(mut self) -> Result<Value, Trap> {
        loop {
            if let Some(outcome) = self.step() {
                return outcome;
            }
        }
    }

    /// Do one unit of work: `None` while the run continues, otherwise its
    /// result. A finished machine keeps returning the result.
    pub fn step(&mut self) -> Option<Result<Value, Trap>> {
        if self.outcome.is_some() {
            return self.outcome;
        }
        let Some(control) = self.control.pop() else {
            let value = *self.values.last().expect("a finished run has its value");
            self.outcome = Some(Ok(value));
            return self.outcome;
        };
        self.steps += 1;
        if let Err(trap) = self.apply(control) {
            // The trap is the run's result from here on; the machine keeps
            // its state at the trap for inspection.
            self.control.clear();
            self.outcome = Some(Err(trap));
        }
        self.outcome
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
    fn pop_int(&mut self) -> i64 {
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
    /// the value stack, and schedule its body. `origin` locates a depth trap.
    fn call(&mut self, function: FunctionId, origin: Span) -> Result<(), Trap> {
        if self.frames.len() >= MAX_CALL_DEPTH {
            return Err(Trap {
                kind: TrapKind::CallDepth,
                origin,
            });
        }
        self.enter(function);
        Ok(())
    }

    fn enter(&mut self, function: FunctionId) {
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

    fn apply(&mut self, control: Control) -> Result<(), Trap> {
        let body = self.body();
        match control {
            Control::Eval(id) => self.eval(body, id),
            Control::Neg(origin) => {
                let operand = self.pop_int();
                let value = operand
                    .checked_neg()
                    .ok_or_else(|| self.trap(TrapKind::Overflow, origin))?;
                self.values.push(Value::Int(value));
            }
            Control::Not => {
                let operand = self.pop_bool();
                self.values.push(Value::Bool(!operand));
            }
            Control::Binary { op, origin } => {
                let rhs = self.pop();
                let lhs = self.pop();
                let value = self.binary(op, lhs, rhs, origin)?;
                self.values.push(value);
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
                origin,
            } => match body.args(args).get(next as usize) {
                Some(&arg) => {
                    self.control.push(Control::Call {
                        function,
                        args,
                        next: next + 1,
                        origin,
                    });
                    self.control.push(Control::Eval(arg));
                }
                None => self.call(function, body.expression(origin).origin)?,
            },
            Control::Return => {
                let frame = self.frames.pop().expect("a return has a frame to leave");
                self.locals.truncate(frame.base);
            }
        }
        Ok(())
    }

    fn eval(&mut self, body: &Body, id: ExprId) {
        match body.expression(id).kind {
            ExprKind::Int(value) => self.values.push(Value::Int(value)),
            ExprKind::Bool(value) => self.values.push(Value::Bool(value)),
            ExprKind::Local(local) => {
                let base = self
                    .frames
                    .last()
                    .expect("a running machine has a frame")
                    .base;
                let value = self.locals[base + local.index()]
                    .expect("the checker orders a let before its uses");
                self.values.push(value);
            }
            ExprKind::Neg(operand) => {
                self.control.push(Control::Neg(id));
                self.control.push(Control::Eval(operand));
            }
            ExprKind::Not(operand) => {
                self.control.push(Control::Not);
                self.control.push(Control::Eval(operand));
            }
            ExprKind::Binary { op, lhs, rhs } => {
                self.control.push(Control::Binary { op, origin: id });
                self.control.push(Control::Eval(rhs));
                self.control.push(Control::Eval(lhs));
            }
            ExprKind::And { lhs, rhs } => {
                self.control.push(Control::AndRhs(rhs));
                self.control.push(Control::Eval(lhs));
            }
            ExprKind::Or { lhs, rhs } => {
                self.control.push(Control::OrRhs(rhs));
                self.control.push(Control::Eval(lhs));
            }
            ExprKind::Call { function, args, .. } => self.control.push(Control::Call {
                function,
                args,
                next: 0,
                origin: id,
            }),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.control.push(Control::Branch {
                    then_branch,
                    else_branch,
                });
                self.control.push(Control::Eval(condition));
            }
            ExprKind::Block { statements, tail } => self.control.push(Control::Block {
                statements,
                next: 0,
                tail,
            }),
        }
    }

    fn trap(&self, kind: TrapKind, origin: ExprId) -> Trap {
        Trap {
            kind,
            origin: self.body().expression(origin).origin,
        }
    }

    fn binary(&self, op: BinaryOp, lhs: Value, rhs: Value, origin: ExprId) -> Result<Value, Trap> {
        let overflow = || self.trap(TrapKind::Overflow, origin);
        Ok(match (op, lhs, rhs) {
            (BinaryOp::Eq, lhs, rhs) => Value::Bool(lhs == rhs),
            (BinaryOp::Ne, lhs, rhs) => Value::Bool(lhs != rhs),
            (op, Value::Int(lhs), Value::Int(rhs)) => match op {
                BinaryOp::Add => Value::Int(lhs.checked_add(rhs).ok_or_else(overflow)?),
                BinaryOp::Sub => Value::Int(lhs.checked_sub(rhs).ok_or_else(overflow)?),
                BinaryOp::Mul => Value::Int(lhs.checked_mul(rhs).ok_or_else(overflow)?),
                BinaryOp::Div | BinaryOp::Rem => {
                    if rhs == 0 {
                        return Err(self.trap(TrapKind::DivisionByZero, origin));
                    }
                    let value = if op == BinaryOp::Div {
                        lhs.checked_div(rhs)
                    } else {
                        lhs.checked_rem(rhs)
                    };
                    Value::Int(value.ok_or_else(overflow)?)
                }
                BinaryOp::Lt => Value::Bool(lhs < rhs),
                BinaryOp::Le => Value::Bool(lhs <= rhs),
                BinaryOp::Gt => Value::Bool(lhs > rhs),
                BinaryOp::Ge => Value::Bool(lhs >= rhs),
                BinaryOp::Eq | BinaryOp::Ne => unreachable!("handled for every type"),
            },
            (op, lhs, rhs) => {
                unreachable!("the checker typed {op:?} over ints; got {lhs:?} and {rhs:?}")
            }
        })
    }
}
