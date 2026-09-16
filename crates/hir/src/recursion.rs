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

use crate::check::DraftBody;
use crate::ranges::Ints;
use crate::solver::{Var, components};
use crate::typing::Typing;
use crate::{BinaryOp, ExprId, ExprKind, FunctionId, Int, LocalId};

/// A cycle with no measure: its members, and for each call inside it the
/// best explanation of why it fails, as the parameter a candidate argument
/// moves and the direction, or nothing when no argument moves one.
pub(crate) struct Failure {
    pub members: Vec<FunctionId>,
    pub labels: Vec<(Span, Option<(Span, &'static str)>)>,
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
enum Direction {
    Decreasing,
    Increasing,
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
            (*hi <= 0.into()).then(|| *hi <= (-1).into())
        }
        Direction::Increasing => {
            let lo = offset.lo()?;
            (*lo >= 0.into()).then(|| *lo >= 1.into())
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

/// `calls` are every call as `(caller, callee, context)`; a call whose
/// context is dead never happens, so it is no edge of the call graph.
pub(crate) fn check(
    bodies: &[Option<DraftBody>],
    param_classes: &[&[Var]],
    typing: &Typing,
    calls: &[(FunctionId, FunctionId, Var)],
) -> Outcome {
    let arcs: Vec<_> = calls
        .iter()
        .filter(|&&(_, _, context)| typing.may(context).live())
        .map(|&(caller, callee, _)| (caller.index(), callee.index()))
        .collect();
    let component = components(bodies.len(), &arcs);
    let count = component.iter().map(|&c| c as usize + 1).max().unwrap_or(0);
    // Functions grouped by component, in declaration order within one.
    let mut grouped: Vec<usize> = (0..bodies.len()).collect();
    grouped.sort_by_key(|&function| component[function]);
    let mut group_start = vec![0; count + 1];
    for &c in &component {
        group_start[c as usize + 1] += 1;
    }
    for c in 0..count {
        group_start[c + 1] += group_start[c];
    }
    let mut cyclic = vec![false; count];
    // Calls between components, as `(from, to)`, sorted.
    let mut between = Vec::new();
    for &(caller, callee) in &arcs {
        let (from, to) = (component[caller] as usize, component[callee] as usize);
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
        let position: HashMap<usize, usize> =
            members.iter().enumerate().map(|(i, &f)| (f, i)).collect();
        let mut inside = Vec::new();
        for &function in members {
            let Some(body) = &bodies[function] else {
                continue;
            };
            let lets: HashMap<LocalId, ExprId> = body
                .statements
                .iter()
                .filter_map(|statement| match statement.kind {
                    crate::StatementKind::Let { local, initializer } => Some((local, initializer)),
                    _ => None,
                })
                .collect();
            let params: HashMap<LocalId, usize> = body
                .params
                .iter()
                .enumerate()
                .map(|(i, &p)| (p, i))
                .collect();
            for expr in &body.exprs {
                let ExprKind::Call {
                    function: callee,
                    args,
                    ..
                } = &expr.kind
                else {
                    continue;
                };
                let Some(&to) = position.get(&callee.index()) else {
                    continue;
                };
                let mut offsets = HashMap::new();
                for (j, &arg) in body.args[args.start as usize..args.end as usize]
                    .iter()
                    .enumerate()
                {
                    if let Some((param, band)) = delta(body, typing, &lets, arg, 0)
                        && let Some(&i) = params.get(&param)
                    {
                        offsets.insert((i, j), band);
                    }
                }
                inside.push(Call {
                    from: position[&function],
                    to,
                    origin: expr.origin,
                    offsets,
                });
            }
        }
        let arity = |member: usize| param_classes[members[member]].len();
        let band =
            |member: usize, param: usize| &typing.may(param_classes[members[member]][param]).ints;
        let mut found = None;
        'directions: for direction in [Direction::Decreasing, Direction::Increasing] {
            let mut choice: Vec<usize> = Vec::with_capacity(members.len());
            // Depth-first over the choices, checking every call whose ends
            // are both chosen as soon as they are.
            let mut position = vec![0; members.len()];
            loop {
                let k = choice.len();
                if k == members.len() {
                    let strict: Vec<bool> = inside
                        .iter()
                        .map(|call| {
                            moves(
                                &call.offsets[&(choice[call.from], choice[call.to])],
                                direction,
                            )
                            .expect("checked while choosing")
                        })
                        .collect();
                    let bounded = members
                        .iter()
                        .enumerate()
                        .all(|(m, _)| bounded(band(m, choice[m]), direction));
                    if bounded && lax_edges_are_acyclic(members.len(), &inside, &strict) {
                        found = Some((choice.clone(), strict.iter().any(|s| !s)));
                        break 'directions;
                    }
                    choice.pop();
                    continue;
                }
                let next = position[k];
                if next >= arity(k) {
                    position[k] = 0;
                    if choice.pop().is_none() {
                        break;
                    }
                    continue;
                }
                position[k] += 1;
                choice.push(next);
                let consistent = inside.iter().all(|call| {
                    let (Some(&i), Some(&j)) = (choice.get(call.from), choice.get(call.to)) else {
                        return true;
                    };
                    call.offsets
                        .get(&(i, j))
                        .is_some_and(|offset| moves(offset, direction).is_some())
                });
                if !consistent {
                    choice.pop();
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
                            lo = Some(lo.map_or(l.clone(), |lo| lo.min(l.clone())));
                            hi = Some(hi.map_or(h.clone(), |hi| hi.max(h.clone())));
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
                let labels = inside
                    .iter()
                    .map(|call| {
                        let callee = members[call.to];
                        let explanation = call.offsets.iter().find_map(|(&(_, j), offset)| {
                            let param = band(call.to, j);
                            let origin = bodies[callee].as_ref()?.locals
                                [bodies[callee].as_ref()?.params[j].index()]
                            .origin;
                            if offset.hi().is_some_and(|hi| *hi <= (-1).into())
                                && param.lo().is_none()
                            {
                                Some((origin, "decreases"))
                            } else if offset.lo().is_some_and(|lo| *lo >= 1.into())
                                && param.hi().is_none()
                            {
                                Some((origin, "increases"))
                            } else {
                                None
                            }
                        });
                        (call.origin, explanation)
                    })
                    .collect();
                failures.push(Failure {
                    members: members.iter().map(|&f| FunctionId(f as u32)).collect(),
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

/// `Some((p, c))` when on every run the expression's value is in `p + c`
/// for the parameter `p`.
fn delta(
    body: &DraftBody,
    typing: &Typing,
    lets: &HashMap<LocalId, ExprId>,
    expr: ExprId,
    depth: usize,
) -> Option<(LocalId, Ints)> {
    if depth > 256 {
        return None;
    }
    let may = |expr: ExprId| &typing.may(body.classes[expr.index()]).ints;
    match &body.exprs[expr.index()].kind {
        ExprKind::Local(local) => {
            if body.params.contains(local) {
                Some((*local, Ints::from(Int::from(0))))
            } else {
                delta(body, typing, lets, *lets.get(local)?, depth + 1)
            }
        }
        ExprKind::Binary {
            op: BinaryOp::Add,
            lhs,
            rhs,
        } => delta(body, typing, lets, *lhs, depth + 1)
            .map(|(p, c)| (p, &c + may(*rhs)))
            .or_else(|| {
                delta(body, typing, lets, *rhs, depth + 1).map(|(p, c)| (p, may(*lhs) + &c))
            }),
        ExprKind::Binary {
            op: BinaryOp::Sub,
            lhs,
            rhs,
        } => delta(body, typing, lets, *lhs, depth + 1).map(|(p, c)| (p, &c - may(*rhs))),
        ExprKind::If {
            then_branch,
            else_branch: Some(else_branch),
            ..
        } => {
            let (p, mut c) = delta(body, typing, lets, *then_branch, depth + 1)?;
            let (q, d) = delta(body, typing, lets, *else_branch, depth + 1)?;
            (p == q).then(|| {
                c.join(&d);
                (p, c)
            })
        }
        ExprKind::Block {
            tail: Some(tail), ..
        } => delta(body, typing, lets, *tail, depth + 1),
        _ => None,
    }
}
