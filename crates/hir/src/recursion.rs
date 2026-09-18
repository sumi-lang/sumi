//! Termination of recursion, and the call depth it bounds.
//!
//! Every cycle of the call graph needs a measure: one parameter per member
//! function such that each call inside the cycle moves the callee's
//! measure from the caller's by a known offset, never in the wrong
//! direction, and strictly often enough that the calls which merely pass
//! it along form no cycle of their own. The measure's set is bounded on the
//! side it moves toward, so the sequence of its values along any chain of
//! calls is finite. This is size-change termination on one parameter per
//! function, which covers structural recursion, mutual recursion, and a
//! helper on the cycle; a lexicographic pair, as Ackermann's function
//! needs, is the extension.
//!
//! The offset comes from a small symbolic reading of an argument: `p + c`
//! for a parameter `p` and a band `c` taken from the may-sets of whatever
//! else the argument adds or subtracts, so `n - k` with `k ∈ [1, 5]` is a
//! strict decrease. With the sets settled, a chain through a component
//! visits at most as many frames as the measure has values, and the depth
//! of an entry is the longest path through the condensation, weighted by
//! each component's chain bound.

use std::collections::HashMap;

use sumi_text::Span;

use crate::check::{Placed, PlacedCall};
use crate::flows;
use crate::ranges::Ints;
use crate::solver::components;
use crate::typing::Typing;
use crate::{BinaryOp, FunctionId, Graph, Int, NodeId, Op};

/// A cycle with no measure: its members, and what each call inside it does
/// to the parameter that came closest to being the measure.
pub(crate) struct Failure {
    pub members: Vec<FunctionId>,
    pub labels: Vec<(Span, Reason)>,
}

/// What a call inside a cycle without a measure does to a parameter of its
/// callee, named by the parameter's declaration.
pub(crate) enum Reason {
    /// The argument moves the parameter in `direction`, and the parameter's
    /// set is unbounded on that side: the chosen measure fails here.
    Unbounded { param: Span, direction: Direction },
    /// The argument moves the parameter in `direction`; the cycle fails
    /// elsewhere, on another call's direction or on a bound.
    Moves { param: Span, direction: Direction },
    /// The argument passes the parameter along without moving it.
    Passes { param: Span },
    /// No argument is a parameter of the caller plus a constant.
    Nothing,
}

pub(crate) struct Outcome {
    pub failures: Vec<Failure>,
    /// The most frames a run entered at each function can hold at once,
    /// when every cycle it can reach has a measure with a finite hull.
    pub depth: Vec<Option<u64>>,
}

/// One call inside a component: from a member to a member, with the offset
/// each argument has from each parameter of the caller, when it has one.
struct Call {
    from: usize,
    to: usize,
    origin: Span,
    /// `(caller parameter, callee parameter) -> offset band`.
    offsets: HashMap<(usize, usize), Ints>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Direction {
    Decreasing,
    Increasing,
}

impl Direction {
    /// How an argument moves a measure this way, and the side it moves
    /// toward.
    pub fn words(self) -> (&'static str, &'static str) {
        match self {
            Self::Decreasing => ("decreases", "below"),
            Self::Increasing => ("increases", "above"),
        }
    }
}

/// Whether an offset moves the measure the right way, and strictly.
fn moves(offset: &Ints, direction: Direction) -> Option<bool> {
    if offset.is_empty() {
        // The argument is never evaluated: the call never happens.
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

/// Whether `band` is bounded on the side the measure moves toward.
fn bounded(band: &Ints, direction: Direction) -> bool {
    band.is_empty()
        || match direction {
            Direction::Decreasing => band.lo().is_some(),
            Direction::Increasing => band.hi().is_some(),
        }
}

/// Every whole call of the graph in a live context is an edge of the call
/// graph; a call whose context is dead never happens, and one that is not
/// whole is a hole, no call. A cycle through a function that `failed`
/// its verdicts, or whose body did not build, is out of scope: its
/// arguments may have no offsets and its calls may be missing, and what
/// it has is reported already.
pub(crate) fn check(graph: &Graph, placed: &Placed, typing: &Typing, failed: &[bool]) -> Outcome {
    let count_functions = graph.runs().len();
    let live: Vec<&PlacedCall> = placed
        .calls()
        .iter()
        .filter(|call| flows::live(typing, call.context))
        .collect();
    let arcs: Vec<(u32, u32)> = live
        .iter()
        .map(|call| (call.caller.index() as u32, call.callee.index() as u32))
        .collect();
    let components = components(count_functions, &arcs);
    let component = &components.of;
    let count = components.count();
    // Functions grouped by component, in declaration order within one.
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
    // Calls between components, as `(from, to)`, sorted.
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
        let band = |member: usize, param: usize| {
            let node = graph
                .run(FunctionId::new(members[member]))
                .params()
                .nth(param)
                .expect("a parameter of the member");
            &flows::may(typing, node).ints
        };
        let mut found = None;
        // The first choice every call agreed with, when the cycle fails on
        // a bound or on the calls that only pass the measure along.
        let mut agreed: Option<(Direction, Vec<usize>, Vec<bool>)> = None;
        // `delta` gives each callee parameter at most one source, so once a
        // member's parameter is chosen every call into it forces its caller's:
        // the component is strongly connected, so a choice for the first
        // member propagates backwards along the calls to every member, and
        // there are as many candidates as that member has parameters.
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
                // The parameter's name, where it is written.
                let param = |member: usize, j: usize| {
                    let node = graph
                        .run(FunctionId::new(members[member]))
                        .params()
                        .nth(j)
                        .expect("a parameter of the member");
                    let node = graph.node(node);
                    node.name.unwrap_or(node.origin)
                };
                let labels = match &agreed {
                    // Every call agreed with this choice, so the cycle
                    // failed on a bound, or on the calls that only pass
                    // the measure along forming a cycle of their own.
                    Some((direction, choice, strict)) => inside
                        .iter()
                        .zip(strict)
                        .map(|(call, &strict)| {
                            let j = choice[call.to];
                            let param = param(call.to, j);
                            let reason = if !strict {
                                Reason::Passes { param }
                            } else if bounded(band(call.to, j), *direction) {
                                Reason::Moves {
                                    param,
                                    direction: *direction,
                                }
                            } else {
                                Reason::Unbounded {
                                    param,
                                    direction: *direction,
                                }
                            };
                            (call.origin, reason)
                        })
                        .collect(),
                    // No choice satisfies every call: say what each call
                    // does, by callee parameter, so the labels do not
                    // follow the map's iteration order.
                    None => inside
                        .iter()
                        .map(|call| {
                            let mut offsets: Vec<_> = call.offsets.iter().collect();
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
    // Components complete callees first, so a callee's depth is known by
    // the time its caller's is computed.
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
    Outcome {
        failures,
        depth: component.iter().map(|&c| depth[c as usize]).collect(),
    }
}

/// Whether the calls that only pass the measure along form no cycle among
/// the members, so every cycle contains a strict step.
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

/// `Some((p, c))` when on every run the node's value is in `p + c` for
/// the parameter at `p`: through a `let`, a narrowed read, `+` and `-`
/// with the other operand's set, and an `if` whose live arms agree on the
/// parameter. The walk keeps its own stack, so a chain of `let`s or a
/// nest of operators of any depth is read.
fn delta(graph: &Graph, typing: &Typing, node: NodeId) -> Option<(u32, Ints)> {
    let may = |node: NodeId| &flows::may(typing, node).ints;
    /// What to do with the offset of the node being read.
    enum Frame {
        /// The left operand of `+`: `rhs` adds to its offset, or is read in
        /// turn when it has none.
        AddLhs { lhs: NodeId, rhs: NodeId },
        /// The right operand of `+`, the left having no offset: `lhs` adds.
        AddRhs { lhs: NodeId },
        /// The left operand of `-`: `rhs` subtracts.
        Sub { rhs: NodeId },
        /// The then arm of an `if` whose else arm `otherwise` runs too.
        Then { otherwise: NodeId },
        /// The else arm, `then` being the then arm's offset.
        Else { then: (u32, Ints) },
    }
    let mut frames: Vec<Frame> = Vec::new();
    let mut next = Some(node);
    let mut result: Option<(u32, Ints)> = None;
    loop {
        if let Some(node) = next.take() {
            let inputs = graph.inputs(node);
            result = match graph.node(node).op {
                Op::Param(index) => Some((index, Ints::from(Int::from(0)))),
                Op::Copy { .. } | Op::Refine { .. } | Op::Exactly(_) => {
                    next = Some(inputs[0]);
                    continue;
                }
                Op::Binary(BinaryOp::Add) => {
                    frames.push(Frame::AddLhs {
                        lhs: inputs[0],
                        rhs: inputs[1],
                    });
                    next = Some(inputs[0]);
                    continue;
                }
                Op::Binary(BinaryOp::Sub) => {
                    frames.push(Frame::Sub { rhs: inputs[1] });
                    next = Some(inputs[0]);
                    continue;
                }
                Op::Join {
                    then,
                    else_: Some(else_),
                } => {
                    // An arm that cannot run contributes no value.
                    let (then, otherwise) = (graph.region(then), graph.region(else_));
                    let live = |context| flows::live(typing, context);
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
        // An offset, or none, is in hand: the innermost frame takes it.
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
