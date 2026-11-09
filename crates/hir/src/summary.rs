//! A value as its function's parameters decide it: one pass over each body, callees first, so a
//! call takes its callee's result at its own arguments and not at every caller's.

use std::collections::HashMap;
use std::rc::Rc;

use rustc_hash::FxBuildHasher;
use sumi_graph::{
    ArithOp, BinaryOp, Case, CmpOp, Decl, DeclId, Domain, FieldName, FunctionId, Graph, Int, Ints,
    May, NodeId, Op, Run, Ty, Unions,
};

use crate::dependency::{Components, Rows};
use crate::flows::selection;
use crate::lower::Lowered;

/// The declared types a field read goes through and the unions a narrowing admits.
#[derive(Clone, Copy)]
pub(crate) struct Types<'a> {
    pub decls: &'a [Decl],
    pub unions: &'a Unions,
}

/// The most forms that bound one side of an integer; the ones over the fewest paths stay.
const MAX_FORMS: usize = 4;
/// The most paths one form sums.
const MAX_TERMS: usize = 3;
/// The most ways an integer is told apart before they are held as one.
const MAX_CASES: usize = 4;

/// A parameter of the enclosing function, or a field of one through fields. Each step carries the
/// type of what it holds, narrowed where an arm bound it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Path {
    param: u32,
    root: Ty,
    steps: Rc<[(FieldName, Ty)]>,
}

impl Path {
    fn ty(&self) -> Ty {
        self.steps.last().map_or(self.root, |&(_, ty)| ty)
    }

    fn with_ty(&self, ty: Ty) -> Self {
        let mut path = self.clone();
        match path.steps.split_last() {
            Some((&(name, _), rest)) => {
                path.steps = rest.iter().copied().chain([(name, ty)]).collect();
            }
            None => path.root = ty,
        }
        path
    }

    /// None unless the path holds values of one declared type with a typed field `name`.
    fn field(&self, name: FieldName, cx: Types<'_>) -> Option<Self> {
        let decl = &cx.decls[self.ty().as_decl()?.index()];
        let (_, ty) = decl.fields()[decl.index_of(name)?];
        Some(Self {
            param: self.param,
            root: self.root,
            steps: self.steps.iter().copied().chain([(name, ty?)]).collect(),
        })
    }

    /// What the path holds where the parameters hold `args`.
    fn at(&self, args: &[&Sym], cx: Types<'_>) -> Sym {
        let Some(arg) = args.get(self.param as usize) else {
            return Sym::Any;
        };
        let mut value = arg.narrowed(self.root, cx);
        for &(name, ty) in self.steps.iter() {
            value = value.field(name, cx).narrowed(ty, cx);
        }
        value
    }

    /// The values the path holds where the parameters hold `args`.
    fn among(&self, args: &[&May], cx: Types<'_>) -> May {
        let Some(arg) = args.get(self.param as usize) else {
            return May::NONE;
        };
        let mut value = arg.narrow(self.root, cx.unions);
        for &(name, ty) in self.steps.iter() {
            let Ok(field) = value.field(name, cx.decls, cx.unions);
            value = field.narrow(ty, cx.unions);
        }
        value
    }
}

/// `constant` plus each path times its coefficient: the terms sorted by path, no coefficient zero.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Form {
    terms: Vec<(Path, i64)>,
    constant: Int,
}

impl Form {
    fn constant(constant: Int) -> Self {
        Self {
            terms: Vec::new(),
            constant,
        }
    }

    fn path(path: Path) -> Self {
        Self {
            terms: vec![(path, 1)],
            constant: Int::from(0),
        }
    }

    /// None past `MAX_TERMS` or an `i64` coefficient.
    fn plus(&self, other: &Self) -> Option<Self> {
        let mut terms = Vec::with_capacity(self.terms.len() + other.terms.len());
        let (mut mine, mut theirs) = (self.terms.iter().peekable(), other.terms.iter().peekable());
        loop {
            let term = match (mine.peek(), theirs.peek()) {
                (None, None) => break,
                (Some(_), None) => mine.next()?.clone(),
                (None, Some(_)) => theirs.next()?.clone(),
                (Some((a, _)), Some((b, _))) if a < b => mine.next()?.clone(),
                (Some((a, _)), Some((b, _))) if a > b => theirs.next()?.clone(),
                (Some(_), Some(_)) => {
                    let ((path, a), (_, b)) = (mine.next()?, theirs.next()?);
                    (path.clone(), a.checked_add(*b)?)
                }
            };
            if term.1 != 0 {
                terms.push(term);
            }
        }
        (terms.len() <= MAX_TERMS).then(|| Self {
            terms,
            constant: &self.constant + &other.constant,
        })
    }

    /// `factor` is not zero; none past an `i64` coefficient.
    fn times(&self, factor: i64) -> Option<Self> {
        let terms = self
            .terms
            .iter()
            .map(|(path, coefficient)| Some((path.clone(), coefficient.checked_mul(factor)?)))
            .collect::<Option<_>>()?;
        Some(Self {
            terms,
            constant: &self.constant * &Int::from(factor),
        })
    }

    fn shifted(&self, by: i64) -> Self {
        Self {
            terms: self.terms.clone(),
            constant: &self.constant + &Int::from(by),
        }
    }

    /// The bounds `picked` gives the form on its lower side when `is_lower`, each path replaced by
    /// what bounds it there; none where nothing bounds one.
    fn with(&self, picked: &[(&Path, Option<&Bounds>)], is_lower: bool) -> Vec<Self> {
        let mut sums = vec![Self::constant(self.constant.clone())];
        for (path, coefficient) in &self.terms {
            let bounds = picked
                .iter()
                .find(|(picked, _)| *picked == path)
                .and_then(|&(_, bounds)| bounds);
            let Some(bounds) = bounds else {
                return Vec::new();
            };
            let side = if (*coefficient > 0) == is_lower {
                &bounds.lo
            } else {
                &bounds.hi
            };
            let next = sums.iter().flat_map(|sum| {
                side.iter()
                    .filter_map(|bound| sum.plus(&bound.times(*coefficient)?))
            });
            sums = strongest(next.collect(), is_lower);
        }
        sums
    }

    /// The values of the form where the parameters hold `args`; none where a path holds nothing.
    fn among(&self, args: &[&May], cx: Types<'_>) -> Option<Ints> {
        // A path alone keeps what its values lack, which sums and products do not.
        if let ([(path, 1)], true) = (self.terms.as_slice(), self.constant == Int::from(0)) {
            let held = path.among(args, cx).ints;
            return (!held.is_empty()).then_some(held);
        }
        let mut values = Ints::from(self.constant.clone());
        for (path, coefficient) in &self.terms {
            let held = path.among(args, cx).ints;
            if held.is_empty() {
                return None;
            }
            values = match coefficient {
                1 => &values + &held,
                -1 => &values - &held,
                _ => &values + &(&Ints::from(Int::from(*coefficient)) * &held),
            };
        }
        Some(values)
    }
}

/// One form per set of paths, the one with the strongest constant, in order; the first
/// `MAX_FORMS`.
fn strongest(mut forms: Vec<Form>, is_lower: bool) -> Vec<Form> {
    if forms.len() < 2 {
        return forms;
    }
    forms.sort_by(|a, b| {
        (a.terms.len(), &a.terms)
            .cmp(&(b.terms.len(), &b.terms))
            .then_with(|| {
                let order = a.constant.cmp(&b.constant);
                if is_lower { order.reverse() } else { order }
            })
    });
    forms.dedup_by(|later, first| later.terms == first.terms);
    forms.truncate(MAX_FORMS);
    forms
}

/// What bounds an integer: it is at least every form of `lo` and at most every form of `hi`, and
/// it is so bound only where each path of `needs` holds some value, as a `match` arm's member.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Bounds {
    lo: Vec<Form>,
    hi: Vec<Form>,
    needs: Vec<Path>,
}

/// Every path of either, sorted, each once.
fn all_needs(mine: &[Path], theirs: &[Path]) -> Vec<Path> {
    let mut needs: Vec<Path> = mine.iter().chain(theirs).cloned().collect();
    needs.sort();
    needs.dedup();
    needs
}

impl Bounds {
    fn exact(form: Form) -> Self {
        Self {
            lo: vec![form.clone()],
            hi: vec![form],
            needs: Vec::new(),
        }
    }

    /// The constant the integer is, where the bounds say so.
    fn point(&self) -> Option<&Int> {
        fn constant(forms: &[Form]) -> Option<&Int> {
            forms
                .first()
                .filter(|form| form.terms.is_empty())
                .map(|form| &form.constant)
        }
        constant(&self.lo).filter(|&lo| constant(&self.hi) == Some(lo))
    }

    /// What holds of an integer either bounds: the forms over the same paths in both, each with
    /// the weaker constant.
    fn either(&self, other: &Self) -> Self {
        let shared = |mine: &[Form], theirs: &[Form], is_lower: bool| {
            mine.iter()
                .filter_map(|form| {
                    let other = theirs.iter().find(|other| other.terms == form.terms)?;
                    let weaker = (form.constant < other.constant) == is_lower;
                    Some(if weaker { form } else { other }.clone())
                })
                .collect()
        };
        let needs = self.needs.iter().filter(|need| other.needs.contains(need));
        Self {
            lo: shared(&self.lo, &other.lo, true),
            hi: shared(&self.hi, &other.hi, false),
            needs: needs.cloned().collect(),
        }
    }

    fn plus(&self, other: &Self) -> Self {
        let sums = |mine: &[Form], theirs: &[Form], is_lower: bool| {
            let sums = mine
                .iter()
                .flat_map(|form| theirs.iter().filter_map(|other| form.plus(other)));
            strongest(sums.collect(), is_lower)
        };
        Self {
            lo: sums(&self.lo, &other.lo, true),
            hi: sums(&self.hi, &other.hi, false),
            needs: all_needs(&self.needs, &other.needs),
        }
    }

    fn times(&self, factor: i64) -> Self {
        if factor == 0 {
            return Self::exact(Form::constant(Int::from(0)));
        }
        let scaled = |forms: &[Form], is_lower: bool| {
            let scaled = forms.iter().filter_map(|form| form.times(factor));
            strongest(scaled.collect(), is_lower)
        };
        let needs = self.needs.clone();
        if factor > 0 {
            Self {
                lo: scaled(&self.lo, true),
                hi: scaled(&self.hi, false),
                needs,
            }
        } else {
            Self {
                lo: scaled(&self.hi, true),
                hi: scaled(&self.lo, false),
                needs,
            }
        }
    }

    /// The bounds where the integer stands in `op` to one `other` bounds.
    fn refined(&self, op: CmpOp, other: &Self) -> Self {
        fn shifted(forms: &[Form], by: i64) -> impl Iterator<Item = Form> + '_ {
            forms.iter().map(move |form| form.shifted(by))
        }
        let mut refined = self.clone();
        match op {
            CmpOp::Lt => refined.hi.extend(shifted(&other.hi, -1)),
            CmpOp::Le => refined.hi.extend(shifted(&other.hi, 0)),
            CmpOp::Gt => refined.lo.extend(shifted(&other.lo, 1)),
            CmpOp::Ge => refined.lo.extend(shifted(&other.lo, 0)),
            CmpOp::Eq => {
                refined.lo.extend(shifted(&other.lo, 0));
                refined.hi.extend(shifted(&other.hi, 0));
            }
            CmpOp::Ne => {}
        }
        Self {
            lo: strongest(refined.lo, true),
            hi: strongest(refined.hi, false),
            needs: all_needs(&self.needs, &other.needs),
        }
    }

    fn reads_params(&self) -> bool {
        let mut forms = self.lo.iter().chain(&self.hi);
        !self.needs.is_empty() || forms.any(|form| !form.terms.is_empty())
    }

    fn paths(&self) -> Vec<&Path> {
        let mut paths: Vec<&Path> = self
            .lo
            .iter()
            .chain(&self.hi)
            .flat_map(|form| form.terms.iter().map(|(path, _)| path))
            .collect();
        paths.sort();
        paths.dedup();
        paths
    }

    /// The bounds with each path replaced by what `picked` bounds it with, needing `needs` and
    /// what those bounds need.
    fn with(&self, picked: &[(&Path, Option<&Bounds>)], mut needs: Vec<Path>) -> Self {
        let bounds = |forms: &[Form], is_lower: bool| {
            let bounds = forms.iter().flat_map(|form| form.with(picked, is_lower));
            strongest(bounds.collect(), is_lower)
        };
        for (_, bounds) in picked {
            needs.extend(
                bounds
                    .iter()
                    .flat_map(|bounds| bounds.needs.iter().cloned()),
            );
        }
        needs.sort();
        needs.dedup();
        Self {
            lo: bounds(&self.lo, true),
            hi: bounds(&self.hi, false),
            needs,
        }
    }

    /// The integers within the bounds where the parameters hold `args`; none where there are none.
    fn among(&self, args: &[&May], cx: Types<'_>) -> Option<Ints> {
        if !self.needs.iter().all(|need| need.among(args, cx).is_live()) {
            return None;
        }
        // A form on both sides is the integer itself, whose values keep what bounds cannot say.
        let exact = self.lo.iter().find(|form| self.hi.contains(form));
        let mut band = match exact {
            Some(form) => form.among(args, cx)?,
            None => Ints::ALL,
        };
        for form in self.lo.iter().filter(|form| Some(*form) != exact) {
            band = band.refine(CmpOp::Ge, &form.among(args, cx)?);
        }
        for form in self.hi.iter().filter(|form| Some(*form) != exact) {
            band = band.refine(CmpOp::Le, &form.among(args, cx)?);
        }
        (!band.is_empty()).then_some(band)
    }
}

/// An integer as one of a few bounds, sorted, at least one. Past `MAX_CASES` they are held as the
/// one that holds of each, and stay so: `is_merged` absorbs, so a join is the same in any order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Cases {
    cases: Vec<Bounds>,
    is_merged: bool,
}

impl Cases {
    fn one(bounds: Bounds) -> Self {
        Self {
            cases: vec![bounds],
            is_merged: false,
        }
    }

    /// `cases` is not empty.
    fn of(mut cases: Vec<Bounds>, is_merged: bool) -> Self {
        if cases.len() > 1 {
            cases.sort();
            cases.dedup();
        }
        if !is_merged && cases.len() <= MAX_CASES {
            return Self { cases, is_merged };
        }
        let (first, rest) = cases.split_first().expect("an integer has bounds");
        let merged = rest
            .iter()
            .fold(first.clone(), |merged, bounds| merged.either(bounds));
        Self {
            cases: vec![merged],
            is_merged: true,
        }
    }

    fn joined(&self, other: &Self) -> Self {
        let cases = self.cases.iter().chain(&other.cases).cloned();
        Self::of(cases.collect(), self.is_merged || other.is_merged)
    }

    fn map(&self, f: impl Fn(&Bounds) -> Bounds) -> Self {
        Self::of(self.cases.iter().map(f).collect(), self.is_merged)
    }

    fn zip(&self, other: &Self, f: impl Fn(&Bounds, &Bounds) -> Bounds) -> Self {
        let cases = self
            .cases
            .iter()
            .flat_map(|mine| other.cases.iter().map(|theirs| f(mine, theirs)));
        Self::of(cases.collect(), self.is_merged || other.is_merged)
    }

    fn point(&self) -> Option<i64> {
        match self.cases.as_slice() {
            [only] => i64::try_from(only.point()?).ok(),
            _ => None,
        }
    }

    /// The integer where the parameters hold `args`: each case at each way its paths are bound.
    fn at(&self, args: &[&Sym], cx: Types<'_>) -> Sym {
        let mut cases = Vec::new();
        let mut is_merged = self.is_merged;
        'cases: for case in &self.cases {
            let mut needs = Vec::new();
            for need in &case.needs {
                match need.at(args, cx) {
                    Sym::None => continue 'cases,
                    Sym::Same(path) => needs.push(path),
                    Sym::Any | Sym::Int(_) | Sym::Made(_) => {}
                }
            }
            let mut held: Vec<(&Path, Option<Self>)> = Vec::new();
            for path in case.paths() {
                match path.at(args, cx) {
                    // The case reads a path that holds nothing there, so it is none of the ways.
                    Sym::None => continue 'cases,
                    Sym::Int(cases) => held.push((path, Some((*cases).clone()))),
                    Sym::Any | Sym::Same(_) | Sym::Made(_) => held.push((path, None)),
                }
            }
            let count = |held: &[(&Path, Option<Self>)]| {
                held.iter()
                    .filter_map(|(_, cases)| cases.as_ref())
                    .map(|cases| cases.cases.len())
                    .product::<usize>()
            };
            if count(&held) > MAX_CASES {
                is_merged = true;
                for (_, cases) in &mut held {
                    *cases = cases.take().map(|cases| Self::of(cases.cases, true));
                }
            }
            for choice in 0..count(&held) {
                let mut rest = choice;
                let picked: Vec<(&Path, Option<&Bounds>)> = held
                    .iter()
                    .map(|(path, cases)| {
                        let bounds = cases.as_ref().map(|cases| {
                            let index = rest % cases.cases.len();
                            rest /= cases.cases.len();
                            &cases.cases[index]
                        });
                        (*path, bounds)
                    })
                    .collect();
                cases.push(case.with(&picked, needs.clone()));
            }
        }
        if cases.is_empty() {
            return Sym::None;
        }
        Sym::int_of(Self::of(cases, is_merged))
    }
}

/// The comparison with its operands exchanged.
fn flipped(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Lt => CmpOp::Gt,
        CmpOp::Le => CmpOp::Ge,
        CmpOp::Gt => CmpOp::Lt,
        CmpOp::Ge => CmpOp::Le,
        CmpOp::Eq | CmpOp::Ne => op,
    }
}

/// The comparison that holds when `op` does not.
fn negated(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Lt => CmpOp::Ge,
        CmpOp::Le => CmpOp::Gt,
        CmpOp::Gt => CmpOp::Le,
        CmpOp::Ge => CmpOp::Lt,
        CmpOp::Eq => CmpOp::Ne,
        CmpOp::Ne => CmpOp::Eq,
    }
}

/// What the parameters of a node's function say of its value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Sym {
    /// No value reaches the node.
    None,
    /// Nothing relates the value to the parameters.
    Any,
    /// The value a path holds, of a type other than `int`.
    Same(Path),
    Int(Rc<Cases>),
    /// A value of one of these declared types, sorted, each with its fields in order.
    Made(Vec<(DeclId, Vec<Sym>)>),
}

impl Sym {
    pub fn param(index: u32, ty: Ty) -> Self {
        Self::of(Path {
            param: index,
            root: ty,
            steps: Rc::from([]),
        })
    }

    fn of(path: Path) -> Self {
        if path.ty() == Ty::INT {
            Self::int_of(Cases::one(Bounds::exact(Form::path(path))))
        } else {
            Self::Same(path)
        }
    }

    /// Bounds that say nothing are no relation to the parameters.
    fn int_of(cases: Cases) -> Self {
        match cases.cases.as_slice() {
            [only] if *only == Bounds::default() => Self::Any,
            _ => Self::Int(Rc::new(cases)),
        }
    }

    pub fn int(value: &Int) -> Self {
        Self::int_of(Cases::one(Bounds::exact(Form::constant(value.clone()))))
    }

    fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }

    /// A value the parameters say nothing of, where one reaches the node.
    fn live(&self) -> Self {
        if self.is_none() {
            Self::None
        } else {
            Self::Any
        }
    }

    fn joined(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::None, known) | (known, Self::None) => known.clone(),
            (Self::Int(a), Self::Int(b)) if Rc::ptr_eq(a, b) => self.clone(),
            (Self::Same(a), Self::Same(b)) if a == b => self.clone(),
            (Self::Int(a), Self::Int(b)) => Self::int_of(a.joined(b)),
            (Self::Made(a), Self::Made(b)) => {
                let mut made: Vec<(DeclId, Vec<Self>)> = a.clone();
                for (decl, fields) in b {
                    match made.binary_search_by_key(decl, |&(decl, _)| decl) {
                        Ok(index) if made[index].1.len() == fields.len() => {
                            for (mine, theirs) in made[index].1.iter_mut().zip(fields) {
                                *mine = mine.joined(theirs);
                            }
                        }
                        Ok(_) => return Self::Any,
                        Err(index) => made.insert(index, (*decl, fields.clone())),
                    }
                }
                Self::Made(made)
            }
            _ => Self::Any,
        }
    }

    fn field(&self, name: FieldName, cx: Types<'_>) -> Self {
        match self {
            Self::None => Self::None,
            Self::Same(path) => path.field(name, cx).map_or(Self::Any, Self::of),
            Self::Made(made) => {
                let mut field = Self::None;
                for (decl, fields) in made {
                    let held = cx.decls[decl.index()]
                        .index_of(name)
                        .and_then(|index| fields.get(index));
                    if let Some(held) = held {
                        field = field.joined(held);
                    }
                }
                field
            }
            Self::Any | Self::Int(_) => Self::Any,
        }
    }

    /// The value where it is one of `ty`: nothing where it cannot be.
    fn narrowed(&self, ty: Ty, cx: Types<'_>) -> Self {
        match self {
            Self::None => Self::None,
            Self::Any => Self::Any,
            Self::Int(_) if ty == Ty::INT => self.clone(),
            Self::Int(_) => Self::None,
            Self::Same(path) if path.ty() == ty => self.clone(),
            Self::Same(path) => match (path.ty().as_decl(), ty.as_decl()) {
                (_, Some(decl)) if cx.unions.admits(path.ty(), decl) => {
                    Self::Same(path.with_ty(ty))
                }
                (Some(decl), None) if cx.unions.admits(ty, decl) => self.clone(),
                (None, None) if path.ty().is_declared() && ty.is_declared() => self.clone(),
                _ => Self::None,
            },
            Self::Made(made) => {
                let made: Vec<_> = made
                    .iter()
                    .filter(|&&(decl, _)| cx.unions.admits(ty, decl))
                    .cloned()
                    .collect();
                if made.is_empty() {
                    Self::None
                } else {
                    Self::Made(made)
                }
            }
        }
    }

    fn arith(&self, op: ArithOp, other: &Self) -> Self {
        let (a, b) = match (self, other) {
            (Self::None, _) | (_, Self::None) => return Self::None,
            (Self::Int(a), Self::Int(b)) => (a, b),
            _ => return Self::Any,
        };
        Self::int_of(match op {
            ArithOp::Add => a.zip(b, Bounds::plus),
            ArithOp::Sub => a.zip(b, |a, b| a.plus(&b.times(-1))),
            ArithOp::Mul => match (a.point(), b.point()) {
                (_, Some(factor)) => a.map(|bounds| bounds.times(factor)),
                (Some(factor), None) => b.map(|bounds| bounds.times(factor)),
                (None, None) => return Self::Any,
            },
            ArithOp::Div | ArithOp::Rem => return Self::Any,
        })
    }

    fn reads_params(&self) -> bool {
        match self {
            Self::None | Self::Any => false,
            Self::Same(_) => true,
            Self::Int(cases) => cases.cases.iter().any(Bounds::reads_params),
            Self::Made(made) => made
                .iter()
                .any(|(_, fields)| fields.iter().any(Self::reads_params)),
        }
    }

    /// A callee's value where its parameters hold `args`, as the caller's parameters decide them.
    fn at(&self, args: &[&Self], cx: Types<'_>) -> Self {
        if !self.reads_params() {
            return self.clone();
        }
        match self {
            Self::None => Self::None,
            Self::Any => Self::Any,
            Self::Same(path) => path.at(args, cx),
            Self::Int(cases) => cases.at(args, cx),
            Self::Made(made) => Self::Made(
                made.iter()
                    .map(|(decl, fields)| {
                        (
                            *decl,
                            fields.iter().map(|field| field.at(args, cx)).collect(),
                        )
                    })
                    .collect(),
            ),
        }
    }

    /// Every value this allows where the parameters hold `args`; none where it allows any.
    pub fn among(&self, args: &[&May], cx: Types<'_>) -> Option<May> {
        match self {
            Self::None | Self::Any => None,
            Self::Same(path) => Some(path.among(args, cx)),
            Self::Int(cases) => {
                let mut ints = Ints::EMPTY;
                for band in cases.cases.iter().filter_map(|case| case.among(args, cx)) {
                    ints.join(&band);
                }
                Some(May::ints(ints))
            }
            Self::Made(made) => {
                let mut values = May::NONE;
                for (decl, fields) in made {
                    let types = cx.decls[decl.index()].fields();
                    let fields: Vec<May> = fields
                        .iter()
                        .zip(types)
                        .map(|(field, &(_, ty))| {
                            field.among(args, cx).unwrap_or_else(|| {
                                ty.map_or(May::NONE, |ty| May::every(ty, cx.unions))
                            })
                        })
                        .collect();
                    if fields.iter().all(May::is_live) {
                        values.join(&May::make(*decl, fields));
                    }
                }
                Some(values)
            }
        }
    }
}

impl Sym {
    fn negated(&self) -> Self {
        match self {
            Self::Int(cases) => Self::int_of(cases.map(|bounds| bounds.times(-1))),
            _ => self.live(),
        }
    }

    /// The value where it stands in `op` to `other`.
    fn refined(&self, op: CmpOp, other: &Self) -> Self {
        match (self, other) {
            (Self::None, _) | (_, Self::None) => Self::None,
            (Self::Int(a), Self::Int(b)) if op != CmpOp::Ne => {
                Self::int_of(a.zip(b, |a, b| a.refined(op, b)))
            }
            // What bounds the other side bounds an integer nothing else does.
            (Self::Any, Self::Int(b)) if op != CmpOp::Ne => {
                Self::int_of(b.map(|b| Bounds::default().refined(op, b)))
            }
            _ => self.clone(),
        }
    }

    /// The value, an integer's bounds holding only where `path` holds some value.
    fn needing(&self, path: &Path) -> Self {
        match self {
            Self::Int(cases) => Self::int_of(cases.map(|bounds| Bounds {
                needs: all_needs(&bounds.needs, std::slice::from_ref(path)),
                ..bounds.clone()
            })),
            _ => self.clone(),
        }
    }

    /// A loop index from `self` up to `end`.
    fn range(&self, end: &Self) -> Self {
        match (self, end) {
            (Self::None, _) | (_, Self::None) => Self::None,
            (Self::Int(start), Self::Int(end)) => Self::int_of(start.zip(end, |start, end| {
                let unbounded = Bounds {
                    lo: start.lo.clone(),
                    hi: Vec::new(),
                    needs: start.needs.clone(),
                };
                unbounded.refined(CmpOp::Lt, end)
            })),
            _ => Self::Any,
        }
    }
}

/// Per function whose body is whole and well typed, its result as its parameters decide it, and
/// the calls that take it so.
pub(crate) struct Summaries {
    results: Rc<[Sym]>,
    calls: HashMap<NodeId, FunctionId, FxBuildHasher>,
}

impl Summaries {
    /// `sound[function]`: every node of the body has its type.
    pub fn new(graph: &Graph, lowered: &Lowered, sound: &[bool]) -> Self {
        // A whole call between sound functions: its arguments are its callee's parameters.
        let mut calls: HashMap<NodeId, FunctionId, FxBuildHasher> = lowered
            .calls
            .iter()
            .filter(|call| {
                sound[call.caller.index()]
                    && sound[call.callee.index()]
                    && lowered.typed[call.node.index()]
            })
            .map(|call| (call.node, call.callee))
            .collect();
        let count = graph.runs().len();
        let rows = Rows::new(count, || {
            lowered
                .calls
                .iter()
                .map(|call| (call.caller.index(), call.callee.index() as u32))
        });
        let components = Components::new(&rows, |callee| callee as usize);
        let types = Types {
            decls: graph.decls(),
            unions: graph.unions(),
        };
        // A result no such call takes is read by nothing.
        let mut is_called = vec![false; count];
        for callee in calls.values() {
            is_called[callee.index()] = true;
        }
        let mut results = vec![Sym::Any; count];
        // Components are numbered callees first. A call inside one takes nothing of its callee, so
        // a recursive group's results are the same in whatever order its members are passed.
        for component in 0..components.count() {
            let members = components.members(component);
            let passed: Vec<Sym> = members
                .iter()
                .map(|&member| {
                    let member = member as usize;
                    if !sound[member] || !is_called[member] {
                        return Sym::Any;
                    }
                    let known = |call: NodeId| {
                        let callee = *calls.get(&call)?;
                        (components.of[callee.index()] as usize != component)
                            .then(|| &results[callee.index()])
                    };
                    result(graph, lowered, &graph.runs()[member], known, types)
                })
                .collect();
            for (&member, result) in members.iter().zip(passed) {
                results[member as usize] = result;
            }
        }
        // A result that reads no parameter is at every call what the callee's own fact holds.
        calls.retain(|_, callee| results[callee.index()].reads_params());
        Self {
            results: results.into(),
            calls,
        }
    }

    pub fn results(&self) -> Rc<[Sym]> {
        self.results.clone()
    }

    /// The callee whose result `call` takes as its own arguments decide it.
    pub fn callee(&self, call: NodeId) -> Option<FunctionId> {
        self.calls.get(&call).copied()
    }
}

/// The result of `run` as its parameters decide it. Every operand of a node precedes it but what a
/// loop carries round, which the pass takes as unknown; `known` answers a call's callee's result.
fn result<'a>(
    graph: &Graph,
    lowered: &Lowered,
    run: &Run,
    known: impl Fn(NodeId) -> Option<&'a Sym>,
    types: Types<'_>,
) -> Sym {
    let mut syms: Vec<Sym> = Vec::with_capacity(run.nodes().len());
    for node in run.nodes() {
        let inputs = graph.inputs(node);
        let roles = graph.input_roles(node);
        let at = |node: NodeId| &syms[run.slot(node)];
        let sym = match &graph.node(node).op {
            _ if !lowered.typed[node.index()] => Sym::Any,
            Op::Int(value) => Sym::int(value),
            Op::Param {
                index,
                ty: Some(ty),
            } => Sym::param(*index, *ty),
            Op::Copy { .. } | Op::Assign | Op::Exactly(_) => at(inputs[0]).clone(),
            Op::Sequence => at(inputs[1]).clone(),
            Op::Narrow(ty) => at(inputs[0]).narrowed(*ty, types),
            Op::Refine {
                op,
                local_is_lhs,
                sense,
            } => {
                let op = if *local_is_lhs { *op } else { flipped(*op) };
                let op = if *sense { op } else { negated(op) };
                at(inputs[0]).refined(op, at(inputs[1]))
            }
            Op::Neg => at(inputs[0]).negated(),
            Op::Binary(BinaryOp::Arith(op)) => at(inputs[0]).arith(*op, at(inputs[1])),
            Op::Make(decl) => {
                let fields = inputs.iter().zip(types.decls[decl.index()].fields()).map(
                    |(&field, &(_, ty))| ty.map_or(Sym::Any, |ty| at(field).narrowed(ty, types)),
                );
                Sym::Made(vec![(*decl, fields.collect())])
            }
            Op::Field(name) => at(inputs[0]).field(*name, types),
            Op::Phi if roles[0].is_value() => inputs[1..]
                .iter()
                .zip(&roles[1..])
                .filter(|(_, role)| role.is_value())
                .fold(Sym::None, |joined, (&value, _)| joined.joined(at(value))),
            Op::Switch { arms } if roles[0].is_value() && selection(graph.cases(*arms)).total => {
                arms.iter()
                    .map(|arm| graph.region(arm))
                    .filter(|region| region.result_has_value())
                    .fold(Sym::None, |joined, region| {
                        let result = at(region.result());
                        let Case::Is(member) = graph.case(region.context) else {
                            return joined.joined(result);
                        };
                        // An arm runs only where its member reaches the scrutinee.
                        match at(inputs[0]).narrowed(member, types) {
                            Sym::None => joined,
                            Sym::Same(path) => joined.joined(&result.needing(&path)),
                            Sym::Any | Sym::Int(_) | Sym::Made(_) => joined.joined(result),
                        }
                    })
            }
            Op::LoopIndex => at(inputs[0]).range(at(inputs[1])),
            Op::LoopValue => {
                let (header, next) = graph.carry(node);
                at(graph.inputs(header)[0]).joined(at(next))
            }
            Op::Result { .. } => {
                let fallthrough = if roles[0].is_value() {
                    at(inputs[0]).clone()
                } else {
                    Sym::None
                };
                inputs[1..]
                    .iter()
                    .filter(|&&returned| graph.input_roles(returned)[0].is_value())
                    .fold(fallthrough, |joined, &returned| {
                        joined.joined(at(graph.inputs(returned)[0]))
                    })
            }
            Op::Call(_) => match known(node) {
                Some(result) => {
                    let args: Vec<&Sym> = inputs.iter().map(|&arg| at(arg)).collect();
                    result.at(&args, types)
                }
                None => Sym::Any,
            },
            _ => Sym::Any,
        };
        syms.push(sym);
    }
    syms.swap_remove(run.slot(run.result()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn band(lo: i64, hi: i64) -> May {
        let mut band = May::int(&Int::from(lo));
        band.join(&May::int(&Int::from(hi)));
        band
    }

    fn no_types() -> (Vec<Decl>, Unions) {
        (Vec::new(), Unions::new())
    }

    /// `if a < b { a } else { b }` over the first two parameters.
    fn least() -> Sym {
        let (a, b) = (Sym::param(0, Ty::INT), Sym::param(1, Ty::INT));
        a.refined(CmpOp::Lt, &b).joined(&b.refined(CmpOp::Le, &a))
    }

    #[test]
    fn a_selection_is_bounded_by_what_each_branch_was_guarded_with() {
        let (decls, unions) = no_types();
        let types = Types {
            decls: &decls,
            unions: &unions,
        };
        let among = |a: May, b: May| least().among(&[&a, &b], types).map(|may| may.ints);
        assert_eq!(among(band(3, 8), band(5, 6)), Some(band(3, 6).ints));
        assert_eq!(among(band(7, 7), band(5, 5)), Some(band(5, 5).ints));
        // The branch that returns `a` needs `a < b`, which no value here meets.
        assert_eq!(among(band(9, 9), band(-2, 4)), Some(band(-2, 4).ints));
        assert_eq!(among(May::NONE, band(1, 1)), Some(Ints::EMPTY));
    }

    #[test]
    fn a_result_at_arguments_is_bounded_as_the_callers_parameters_bound_them() {
        let (decls, unions) = no_types();
        let types = Types {
            decls: &decls,
            unions: &unions,
        };
        // `least(n + 1, 10)` in a caller whose first parameter is `n`.
        let n = Sym::param(0, Ty::INT);
        let next = n.arith(ArithOp::Add, &Sym::int(&Int::from(1)));
        let ten = Sym::int(&Int::from(10));
        let called = least().at(&[&next, &ten], types);
        let among = |n: May| called.among(&[&n], types).map(|may| may.ints);
        assert_eq!(among(band(0, 3)), Some(band(1, 4).ints));
        assert_eq!(among(band(20, 30)), Some(band(10, 10).ints));
        assert_eq!(among(band(5, 15)), Some(band(6, 10).ints));
    }

    #[test]
    fn cases_past_the_limit_merge_and_stay_merged_in_any_order() {
        let point = |value: i64| Sym::int(&Int::from(value));
        let points: Vec<Sym> = (0..=MAX_CASES as i64).map(point).collect();
        let forward = points.iter().fold(Sym::None, |all, next| all.joined(next));
        let backward = points
            .iter()
            .rev()
            .fold(Sym::None, |all, next| all.joined(next));
        let halves = {
            let (left, right) = points.split_at(2);
            let left = left.iter().fold(Sym::None, |all, next| all.joined(next));
            let right = right.iter().fold(Sym::None, |all, next| all.joined(next));
            left.joined(&right)
        };
        assert_eq!(forward, backward);
        assert_eq!(forward, halves);
        let Sym::Int(cases) = &forward else {
            panic!("an integer")
        };
        assert!(cases.is_merged && cases.cases.len() == 1);
        assert_eq!(forward.joined(&point(2)), forward);
        let (decls, unions) = no_types();
        let types = Types {
            decls: &decls,
            unions: &unions,
        };
        let within = forward.among(&[], types).map(|may| may.ints);
        assert_eq!(within, Some(band(0, MAX_CASES as i64).ints));
    }

    #[test]
    fn an_arms_case_holds_only_where_its_member_reaches_the_scrutinee() {
        let (boxed, none) = (DeclId::new(0), DeclId::new(1));
        let value = FieldName::new(0);
        let decls = vec![
            Decl::new(Box::new([(value, Some(Ty::INT))])),
            Decl::new(Box::new([])),
        ];
        let mut unions = Unions::new();
        let either = Ty::union(unions.intern([boxed, none]).expect("two members"));
        let types = Types {
            decls: &decls,
            unions: &unions,
        };
        // `match v { Box(b) => b.value, None => fallback }`.
        let (v, fallback) = (Sym::param(0, either), Sym::param(1, Ty::INT));
        let Sym::Same(as_none) = v.narrowed(Ty::decl(none), types) else {
            panic!("the parameter, as its member")
        };
        let unwrapped = v
            .narrowed(Ty::decl(boxed), types)
            .field(value, types)
            .joined(&fallback.needing(&as_none));
        let among =
            |v: May, fallback: May| unwrapped.among(&[&v, &fallback], types).map(|may| may.ints);
        let some = May::make(boxed, vec![band(4, 4)]);
        let nothing = May::make(none, Vec::new());
        assert_eq!(among(some.clone(), band(0, 0)), Some(band(4, 4).ints));
        assert_eq!(among(nothing.clone(), band(2, 2)), Some(band(2, 2).ints));
        let mut both = some;
        both.join(&nothing);
        assert_eq!(among(both, band(0, 0)), Some(band(0, 4).ints));
    }
}
