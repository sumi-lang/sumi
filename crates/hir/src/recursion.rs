//! Termination of recursion, and the call depth it bounds. A cycle's measure is one parameter per
//! member, moved toward a bound by every call inside it.

use std::collections::HashMap;

use sumi_frontend::Diagnostic;
use sumi_text::TextRange;

use crate::lower::{self, Lowered};
use crate::solver::components;
use crate::typing::Typing;
use crate::{ArithOp, BinaryOp, Function, FunctionId, Graph, Int, Ints, NodeId, Op, codes};

pub(crate) struct Failure {
    pub members: Vec<FunctionId>,
    pub labels: Vec<(TextRange, Reason)>,
}

impl Failure {
    pub fn report(self, functions: &[Function], source: &str) -> Diagnostic {
        let text = |range: TextRange| range.text(source);
        let at = |id: FunctionId| {
            let function = &functions[id.index()];
            function.name.unwrap_or(function.origin)
        };
        let names: Vec<_> = self
            .members
            .iter()
            .take(4)
            .map(|&id| format!("`{}`", text(at(id))))
            .collect();
        let others = self.members.len() - names.len();
        let cycle = match names.as_slice() {
            [name] => format!("recursion in {name}"),
            [first, second] => format!("recursion between {first} and {second}"),
            [rest @ .., last] if others == 0 => {
                format!("recursion between {}, and {last}", rest.join(", "))
            }
            _ => format!("recursion between {}, and {others} more", names.join(", ")),
        };
        let message = format!("{cycle} has no argument that moves toward a bound on every call");
        let labels = self.labels.into_iter().take(8).map(|(call, reason)| {
            let text = match reason {
                Reason::Moves {
                    param,
                    direction,
                    bounded,
                } => {
                    let (moves, side) = direction.words();
                    let unbounded = if bounded {
                        String::new()
                    } else {
                        format!(", which is unbounded {side}")
                    };
                    format!("argument {moves} `{}`{unbounded}", text(param))
                }
                Reason::Passes { param } => format!("argument passes `{}` along", text(param)),
                Reason::Nothing => "no argument is a parameter moved by a constant".to_owned(),
            };
            (call, text.into())
        });
        lower::diagnostic(
            at(self.members[0]),
            codes::UNBOUNDED_RECURSION,
            message,
            labels,
        )
    }
}

/// What a call does to a parameter of its callee, `param` naming which.
pub(crate) enum Reason {
    Moves {
        param: TextRange,
        direction: Direction,
        bounded: bool,
    },
    Passes {
        param: TextRange,
    },
    Nothing,
}

pub(crate) struct Verdicts {
    pub failures: Vec<Failure>,
    /// Per function, the most frames a run entered there holds at once, or `None` unless every
    /// reachable cycle has a measure with a finite hull.
    pub depth: Vec<Option<u64>>,
}

/// `from` and `to` index the component's members, not the functions.
struct Call {
    from: usize,
    to: usize,
    origin: TextRange,
    /// Keyed by `(caller parameter, callee parameter)`.
    offsets: HashMap<(usize, usize), Ints>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Direction {
    Decreasing,
    Increasing,
}

impl Direction {
    pub fn words(self) -> (&'static str, &'static str) {
        match self {
            Self::Decreasing => ("decreases", "below"),
            Self::Increasing => ("increases", "above"),
        }
    }
}

/// `Some(strict)` when the offset never moves the wrong way, `None` when it may.
fn moves(offset: &Ints, direction: Direction) -> Option<bool> {
    if offset.is_empty() {
        // An empty set is an argument never evaluated, so the call never happens.
        return Some(true);
    }
    match direction {
        Direction::Decreasing => {
            let hi = offset.hi()?;
            (hi <= 0.into()).then(|| hi <= (-1).into())
        }
        Direction::Increasing => {
            let lo = offset.lo()?;
            (lo >= 0.into()).then(|| lo >= 1.into())
        }
    }
}

fn bounded(band: &Ints, direction: Direction) -> bool {
    band.is_empty()
        || match direction {
            Direction::Decreasing => band.lo().is_some(),
            Direction::Increasing => band.hi().is_some(),
        }
}

/// `failed` marks functions whose verdicts failed or whose body did not build; a cycle through one
/// is skipped, since its calls may be missing.
pub(crate) fn check(
    graph: &Graph,
    lowered: &Lowered,
    typing: &Typing,
    failed: &[bool],
) -> Verdicts {
    let count_functions = graph.runs().len();
    let live: Vec<&lower::Call> = lowered
        .calls
        .iter()
        .filter(|call| typing.may(call.context).live())
        .collect();
    let arcs: Vec<(u32, u32)> = live
        .iter()
        .map(|call| (call.caller.index() as u32, call.callee.index() as u32))
        .collect();
    let components = components(count_functions, &arcs);
    let component = &components.of;
    let count = components.count();
    let mut grouped: Vec<usize> = (0..count_functions).collect();
    grouped.sort_by_key(|&function| component[function]);
    let mut group_start = vec![0; count + 1];
    for &c in component {
        group_start[c as usize + 1] += 1;
    }
    for c in 0..count {
        group_start[c + 1] += group_start[c];
    }
    let mut cyclic = vec![false; count];
    let mut between = Vec::new();
    for &(caller, callee) in &arcs {
        let (from, to) = (
            component[caller as usize] as usize,
            component[callee as usize] as usize,
        );
        if from == to {
            cyclic[from] = true;
        } else {
            between.push((from, to));
        }
    }
    between.sort_unstable();
    between.dedup();
    let mut failures = Vec::new();
    let mut chain: Vec<Option<u64>> = vec![Some(1); count];
    for c in 0..count {
        if !cyclic[c] {
            continue;
        }
        let members = &grouped[group_start[c]..group_start[c + 1]];
        if members.iter().any(|&function| failed[function]) {
            chain[c] = None;
            continue;
        }
        let position: HashMap<usize, usize> =
            members.iter().enumerate().map(|(i, &f)| (f, i)).collect();
        let mut inside = Vec::new();
        for call in &live {
            let (Some(&from), Some(&to)) = (
                position.get(&call.caller.index()),
                position.get(&call.callee.index()),
            ) else {
                continue;
            };
            let mut offsets = HashMap::new();
            for (j, &arg) in graph.inputs(call.node).iter().enumerate() {
                if let Some((i, band)) = delta(graph, typing, arg) {
                    offsets.insert((i as usize, j), band);
                }
            }
            inside.push(Call {
                from,
                to,
                origin: graph.node(call.node).origin,
                offsets,
            });
        }
        let arity = |member: usize| graph.run(FunctionId::new(members[member])).params().len();
        let param_node = |member: usize, param: usize| {
            graph
                .run(FunctionId::new(members[member]))
                .params()
                .nth(param)
                .expect("a parameter of the member")
        };
        let band = |member: usize, param: usize| &typing.may(param_node(member, param)).ints;
        let mut found = None;
        let mut agreed: Option<(Direction, Vec<usize>, Vec<bool>)> = None;
        'directions: for direction in [Direction::Decreasing, Direction::Increasing] {
            'candidates: for first in 0..arity(0) {
                let mut choice: Vec<Option<usize>> = vec![None; members.len()];
                choice[0] = Some(first);
                let mut work = vec![0];
                while let Some(to) = work.pop() {
                    let j = choice[to].expect("queued once chosen");
                    for call in inside.iter().filter(|call| call.to == to) {
                        let forced = call.offsets.iter().find_map(|(&(i, k), offset)| {
                            (k == j && moves(offset, direction).is_some()).then_some(i)
                        });
                        match (forced, choice[call.from]) {
                            (Some(i), None) => {
                                choice[call.from] = Some(i);
                                work.push(call.from);
                            }
                            (Some(i), Some(chosen)) if i == chosen => {}
                            _ => continue 'candidates,
                        }
                    }
                }
                let choice: Vec<usize> = choice
                    .into_iter()
                    .collect::<Option<_>>()
                    .expect("every member of a component reaches its first");
                let strict: Vec<bool> = inside
                    .iter()
                    .map(|call| {
                        moves(
                            &call.offsets[&(choice[call.from], choice[call.to])],
                            direction,
                        )
                    })
                    .collect::<Option<_>>()
                    .expect("every call was checked while propagating");
                let bounded = members
                    .iter()
                    .enumerate()
                    .all(|(m, _)| bounded(band(m, choice[m]), direction));
                if bounded && lax_edges_are_acyclic(members.len(), &inside, &strict) {
                    found = Some((choice, strict.iter().any(|s| !s)));
                    break 'directions;
                }
                if agreed.is_none() {
                    agreed = Some((direction, choice, strict));
                }
            }
        }
        match found {
            Some((choice, lax)) => {
                let mut lo: Option<Int> = None;
                let mut hi: Option<Int> = None;
                let mut finite = true;
                for (m, &param) in choice.iter().enumerate() {
                    let band = band(m, param);
                    if band.is_empty() {
                        continue;
                    }
                    match (band.lo(), band.hi()) {
                        (Some(l), Some(h)) => {
                            lo = Some(lo.map_or(l.clone(), |lo| lo.min(l)));
                            hi = Some(hi.map_or(h.clone(), |hi| hi.max(h)));
                        }
                        _ => finite = false,
                    }
                }
                chain[c] = match (finite, lo, hi) {
                    (true, Some(lo), Some(hi)) => {
                        let values = &(&hi - &lo) + &1.into();
                        i64::try_from(&values)
                            .ok()
                            .and_then(|v| u64::try_from(v).ok())
                            .and_then(|v| v.checked_mul(if lax { members.len() as u64 } else { 1 }))
                    }
                    (true, None, None) => Some(0),
                    _ => None,
                };
            }
            None => {
                chain[c] = None;
                let param = |member: usize, j: usize| {
                    let node = graph.node(param_node(member, j));
                    node.name.unwrap_or(node.origin)
                };
                let labels = match &agreed {
                    Some((direction, choice, strict)) => inside
                        .iter()
                        .zip(strict)
                        .map(|(call, &strict)| {
                            let j = choice[call.to];
                            let reason = if strict {
                                Reason::Moves {
                                    param: param(call.to, j),
                                    direction: *direction,
                                    bounded: bounded(band(call.to, j), *direction),
                                }
                            } else {
                                Reason::Passes {
                                    param: param(call.to, j),
                                }
                            };
                            (call.origin, reason)
                        })
                        .collect(),
                    None => inside
                        .iter()
                        .map(|call| {
                            let mut offsets: Vec<_> = call.offsets.iter().collect();
                            // The map's iteration order varies between runs.
                            offsets.sort_by_key(|((_, j), _)| *j);
                            let strict = offsets.iter().find_map(|&(&(_, j), offset)| {
                                let direction =
                                    if moves(offset, Direction::Decreasing) == Some(true) {
                                        Direction::Decreasing
                                    } else if moves(offset, Direction::Increasing) == Some(true) {
                                        Direction::Increasing
                                    } else {
                                        return None;
                                    };
                                Some(Reason::Moves {
                                    param: param(call.to, j),
                                    direction,
                                    // No choice held, so no bound is at issue; the label says only
                                    // where the argument moves.
                                    bounded: true,
                                })
                            });
                            let reason = strict.unwrap_or_else(|| {
                                offsets.first().map_or(Reason::Nothing, |&(&(_, j), _)| {
                                    Reason::Passes {
                                        param: param(call.to, j),
                                    }
                                })
                            });
                            (call.origin, reason)
                        })
                        .collect(),
                };
                failures.push(Failure {
                    members: members.iter().map(|&f| FunctionId::new(f)).collect(),
                    labels,
                });
            }
        }
    }
    // Callees' components are numbered first, so `depth[to]` is set when read.
    let mut depth: Vec<Option<u64>> = vec![None; count];
    let mut edge = 0;
    for c in 0..count {
        let mut below = Some(0u64);
        while let Some(&(from, to)) = between.get(edge)
            && from == c
        {
            below = below.and_then(|most| depth[to].map(|d| most.max(d)));
            edge += 1;
        }
        depth[c] = match (chain[c], below) {
            (Some(chain), Some(below)) => chain.checked_add(below),
            _ => None,
        };
    }
    Verdicts {
        failures,
        depth: component.iter().map(|&c| depth[c as usize]).collect(),
    }
}

fn lax_edges_are_acyclic(members: usize, calls: &[Call], strict: &[bool]) -> bool {
    let mut adjacent = vec![Vec::new(); members];
    for (call, &strict) in calls.iter().zip(strict) {
        if !strict {
            adjacent[call.from].push(call.to);
        }
    }
    // 0 unvisited, 1 on the path, 2 done.
    let mut state = vec![0u8; members];
    let mut work = Vec::new();
    for root in 0..members {
        if state[root] != 0 {
            continue;
        }
        work.clear();
        work.push((root, 0));
        state[root] = 1;
        while let Some(&mut (node, ref mut position)) = work.last_mut() {
            if let Some(&next) = adjacent[node].get(*position) {
                *position += 1;
                match state[next] {
                    0 => {
                        state[next] = 1;
                        work.push((next, 0));
                    }
                    1 => return false,
                    _ => {}
                }
                continue;
            }
            state[node] = 2;
            work.pop();
        }
    }
    true
}

/// `Some((p, c))` when on every run the node's value is in parameter `p` plus `c`. The walk keeps
/// its own stack, since a nest can outgrow the call stack.
fn delta(graph: &Graph, typing: &Typing, node: NodeId) -> Option<(u32, Ints)> {
    let may = |node: NodeId| &typing.may(node).ints;
    enum Frame {
        AddLhs { lhs: NodeId, rhs: NodeId },
        AddRhs { lhs: NodeId },
        Sub { rhs: NodeId },
        Then { otherwise: NodeId },
        Else { then: (u32, Ints) },
    }
    let mut frames: Vec<Frame> = Vec::new();
    let mut next = Some(node);
    let mut result: Option<(u32, Ints)> = None;
    loop {
        if let Some(node) = next.take() {
            let inputs = graph.inputs(node);
            result = match graph.node(node).op {
                Op::Param { index, .. } => Some((index, Ints::from(Int::from(0)))),
                Op::Copy { .. } | Op::Refine { .. } | Op::Exactly(_) => {
                    next = Some(inputs[0]);
                    continue;
                }
                Op::Binary(BinaryOp::Arith(ArithOp::Add)) => {
                    frames.push(Frame::AddLhs {
                        lhs: inputs[0],
                        rhs: inputs[1],
                    });
                    next = Some(inputs[0]);
                    continue;
                }
                Op::Binary(BinaryOp::Arith(ArithOp::Sub)) => {
                    frames.push(Frame::Sub { rhs: inputs[1] });
                    next = Some(inputs[0]);
                    continue;
                }
                Op::Join {
                    then,
                    else_: Some(else_),
                    ..
                } => {
                    // An arm that cannot run contributes no value.
                    let (then, otherwise) = (graph.region(then), graph.region(else_));
                    let live = |context| typing.may(context).live();
                    match (live(then.context), live(otherwise.context)) {
                        (true, true) => {
                            frames.push(Frame::Then {
                                otherwise: otherwise.result(),
                            });
                            next = Some(then.result());
                            continue;
                        }
                        (true, false) => {
                            next = Some(then.result());
                            continue;
                        }
                        (false, true) => {
                            next = Some(otherwise.result());
                            continue;
                        }
                        (false, false) => None,
                    }
                }
                _ => None,
            };
        }
        let Some(frame) = frames.pop() else {
            return result;
        };
        match frame {
            Frame::AddLhs { lhs, rhs } => match result.take() {
                Some((p, c)) => result = Some((p, &c + may(rhs))),
                None => {
                    frames.push(Frame::AddRhs { lhs });
                    next = Some(rhs);
                }
            },
            Frame::AddRhs { lhs } => result = result.take().map(|(p, c)| (p, may(lhs) + &c)),
            Frame::Sub { rhs } => result = result.take().map(|(p, c)| (p, &c - may(rhs))),
            Frame::Then { otherwise } => match result.take() {
                Some(then) => {
                    frames.push(Frame::Else { then });
                    next = Some(otherwise);
                }
                None => result = None,
            },
            Frame::Else { then: (p, mut c) } => {
                result = match result.take() {
                    Some((q, d)) if p == q => {
                        c.join(&d);
                        Some((p, c))
                    }
                    _ => None,
                };
            }
        }
    }
}
