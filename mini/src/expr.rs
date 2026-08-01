//! `Name`, `Level`, `Expr` — owned, de Bruijn, no arena.
//!
//! # Interface
//!
//! Port of `MiniKernel/Types.lean`, `MiniKernel/ExprUtils.lean` and the `Expr`
//! and `Level` helpers at the top of `MiniKernel/Kernel.lean`. Every function
//! here has a named original, and the correspondence is one-to-one on purpose:
//! this file is meant to be reviewed against the Lean side line by line.
//!
//! Two deliberate departures, both argued in MINI-DESIGN.md §2:
//!
//! * **No binder names.** Mini-lean carries a `Name` on `lam`/`forall`/`let`
//!   purely for printing. `Expr`'s derived `BEq` therefore compares them, but
//!   the only structural `Expr` comparisons the kernel performs are against
//!   `.bvar` nodes (`isValidIndApp`, `resType.getApp.2.contains (.bvar shift)`),
//!   so dropping the names cannot change a verdict.
//! * **No `Local` variant.** Mini is pure de Bruijn: the local context is a
//!   telescope, exactly as in the original.
//!
//! Nat literals are `u64`; the parser declines anything above 10 (mini-lean's
//! own guard), so the width is never load-bearing.

use std::fmt;
use std::rc::Rc;

// ─────────────────────────────────────────────────────────────── names ──

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Name {
    Anon,
    Str(Rc<Name>, Rc<str>),
    Num(Rc<Name>, u64),
}

impl Name {
    /// `Name.simple`: a one-component name.
    pub fn simple(s: &str) -> Name { Name::Str(Rc::new(Name::Anon), Rc::from(s)) }

    /// `Name.str`.
    pub fn str(pre: &Name, s: &str) -> Name { Name::Str(Rc::new(pre.clone()), Rc::from(s)) }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Anon => write!(f, "[anonymous]"),
            Name::Str(pre, s) => match **pre {
                Name::Anon => write!(f, "{s}"),
                _ => write!(f, "{pre}.{s}"),
            },
            Name::Num(pre, i) => match **pre {
                Name::Anon => write!(f, "{i}"),
                _ => write!(f, "{pre}.{i}"),
            },
        }
    }
}

// ────────────────────────────────────────────────────────────── levels ──

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Level {
    Zero,
    Succ(Rc<Level>),
    Max(Rc<Level>, Rc<Level>),
    IMax(Rc<Level>, Rc<Level>),
    Param(Name),
}

impl Level {
    pub fn succ(self) -> Level { Level::Succ(Rc::new(self)) }
    pub fn max(a: Level, b: Level) -> Level { Level::Max(Rc::new(a), Rc::new(b)) }
    pub fn imax(a: Level, b: Level) -> Level { Level::IMax(Rc::new(a), Rc::new(b)) }

    /// `Level.isZero`.
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Max(a, b) => a.is_zero() && b.is_zero(),
            Level::IMax(_, b) => b.is_zero(),
            Level::Succ(_) | Level::Param(_) => false,
        }
    }

    /// `Level.isNotZero`.
    pub fn is_not_zero(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Max(a, b) => a.is_not_zero() || b.is_not_zero(),
            Level::IMax(_, b) => b.is_not_zero(),
            Level::Succ(_) => true,
            Level::Param(_) => false,
        }
    }

    /// `Level.substLevel`.
    pub fn subst(&self, f: &dyn Fn(&Name) -> Level) -> Level {
        match self {
            Level::Param(n) => f(n),
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::Succ(Rc::new(l.subst(f))),
            Level::Max(a, b) => Level::Max(Rc::new(a.subst(f)), Rc::new(b.subst(f))),
            Level::IMax(a, b) => Level::IMax(Rc::new(a.subst(f)), Rc::new(b.subst(f))),
        }
    }

    /// `Level.substOneLevel`.
    pub fn subst_one(&self, n: &Name, l: &Level) -> Level {
        self.subst(&|m| if m == n { l.clone() } else { Level::Param(m.clone()) })
    }

    /// `Level.mkIMax` — the smart constructor keeping `imax`'s rhs a parameter.
    pub fn mk_imax(l1: &Level, l2: &Level) -> Level {
        match l2 {
            Level::Zero => Level::Zero,
            Level::Succ(_) => Level::max(l1.clone(), l2.clone()),
            Level::Max(a, b) => Level::max(Level::mk_imax(l1, a), Level::mk_imax(l1, b)),
            Level::IMax(a, b) => Level::mk_imax(&Level::max(l1.clone(), (**a).clone()), b),
            Level::Param(_) => Level::imax(l1.clone(), l2.clone()),
        }
    }

    /// `Level.simplify`.
    pub fn simplify(&self) -> Level {
        match self {
            Level::Zero => Level::Zero,
            Level::Succ(l) => Level::Succ(Rc::new(l.simplify())),
            Level::Max(a, b) => Level::max(a.simplify(), b.simplify()),
            Level::IMax(a, b) => Level::mk_imax(&a.simplify(), &b.simplify()),
            Level::Param(n) => Level::Param(n.clone()),
        }
    }

    /// `Level.byCases`.
    fn by_cases(p: &Name, l1: &Level, l2: &Level, balance: i64) -> bool {
        let succ_p = Level::Param(p.clone()).succ();
        Level::le(&l1.subst_one(p, &Level::Zero).simplify(), &l2.subst_one(p, &Level::Zero).simplify(), balance)
            && Level::le(&l1.subst_one(p, &succ_p).simplify(), &l2.subst_one(p, &succ_p).simplify(), balance)
    }

    /// `Level.le` — the balance algorithm, ported clause for clause and in the
    /// original's clause order. `LevelProofs.lean` proves it correct but
    /// incomplete; incompleteness only ever rejects, and every use on mini's
    /// hot path is at ground levels where it is exact (MINI-DESIGN.md §3).
    pub fn le(l1: &Level, l2: &Level, balance: i64) -> bool {
        // The rhs-is-a-parameter shape an `imax` must have after `simplify`.
        fn imax_param(l: &Level) -> Option<&Name> {
            match l {
                Level::IMax(_, r) => match &**r {
                    Level::Param(p) => Some(p),
                    _ => None,
                },
                _ => None,
            }
        }
        if let Level::Succ(a) = l1 {
            return Level::le(a, l2, balance - 1)
        }
        if let Level::Succ(b) = l2 {
            return Level::le(l1, b, balance + 1)
        }
        if let Level::Max(a, b) = l1 {
            return Level::le(a, l2, balance) && Level::le(b, l2, balance)
        }
        if let (Level::Param(n), Level::Param(m)) = (l1, l2) {
            return n == m && balance >= 0
        }
        if let Some(p) = imax_param(l1).or_else(|| imax_param(l2)) {
            return Level::by_cases(&p.clone(), l1, l2, balance)
        }
        // Unreachable by the simplification invariant, and `false` there too.
        if matches!(l1, Level::IMax(..)) || matches!(l2, Level::IMax(..)) {
            return false
        }
        if matches!(l1, Level::Param(_) | Level::Zero) {
            if let Level::Max(a, b) = l2 {
                return Level::le(l1, a, balance) || Level::le(l1, b, balance)
            }
        }
        if matches!(l1, Level::Zero) && balance >= 0 {
            return true
        }
        // Everything left — `(zero, zero|param)` at a negative balance and
        // `(param, zero)` — is `false` in the original.
        false
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Level::Zero => write!(f, "0"),
            Level::Succ(l) => write!(f, "({l}+1)"),
            Level::Max(a, b) => write!(f, "max({a},{b})"),
            Level::IMax(a, b) => write!(f, "imax({a},{b})"),
            Level::Param(n) => write!(f, "{n}"),
        }
    }
}

// ───────────────────────────────────────────────────────── expressions ──

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    Const(Name, Rc<[Level]>),
    BVar(u32),
    App(Rc<Expr>, Rc<Expr>),
    Lam { ty: Rc<Expr>, body: Rc<Expr> },
    Forall { ty: Rc<Expr>, body: Rc<Expr> },
    NatLit(u64),
    StrLit(Rc<str>),
    Sort(Level),
    Proj { ind: Name, idx: u32, s: Rc<Expr> },
    Let { ty: Rc<Expr>, val: Rc<Expr>, body: Rc<Expr> },
}

pub type E = Rc<Expr>;

pub fn bvar(i: u32) -> E { Rc::new(Expr::BVar(i)) }
pub fn sort(l: Level) -> E { Rc::new(Expr::Sort(l)) }
pub fn konst(n: Name, ls: Rc<[Level]>) -> E { Rc::new(Expr::Const(n, ls)) }
pub fn app(f: E, a: E) -> E { Rc::new(Expr::App(f, a)) }
pub fn lam(ty: E, body: E) -> E { Rc::new(Expr::Lam { ty, body }) }
pub fn forall(ty: E, body: E) -> E { Rc::new(Expr::Forall { ty, body }) }

/// `Expr.arrow` — a non-dependent `Π`. Note the original does **not** shift
/// `b`: callers (only `addQuot`) write the de Bruijn indices out by hand.
pub fn arrow(a: E, b: E) -> E { forall(a, b) }

/// `Expr.getApp`.
pub fn get_app(e: &E) -> (E, Vec<E>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let Expr::App(f, a) = &*cur.clone() {
        args.push(a.clone());
        cur = f.clone();
    }
    args.reverse();
    (cur, args)
}

/// `Expr.appN`.
pub fn app_n(f: E, args: &[E]) -> E {
    let mut out = f;
    for a in args {
        out = app(out, a.clone());
    }
    out
}

/// `Expr.shift`.
pub fn shift(e: &E, n: u32, d: u32) -> E {
    if d == 0 {
        return e.clone()
    }
    match &**e {
        Expr::BVar(i) => {
            if *i >= n {
                bvar(i + d)
            } else {
                e.clone()
            }
        }
        Expr::App(f, a) => app(shift(f, n, d), shift(a, n, d)),
        Expr::Lam { ty, body } => lam(shift(ty, n, d), shift(body, n + 1, d)),
        Expr::Forall { ty, body } => forall(shift(ty, n, d), shift(body, n + 1, d)),
        Expr::Let { ty, val, body } => Rc::new(Expr::Let {
            ty: shift(ty, n, d),
            val: shift(val, n, d),
            body: shift(body, n + 1, d),
        }),
        Expr::Proj { ind, idx, s } => {
            Rc::new(Expr::Proj { ind: ind.clone(), idx: *idx, s: shift(s, n, d) })
        }
        Expr::Const(..) | Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => e.clone(),
    }
}

/// `Expr.substs`. `s` is in *argument* order: `s[0]` replaces the outermost of
/// the substituted variables, `s[len-1]` replaces `bvar n`.
pub fn substs(e: &E, s: &[E], n: u32) -> E {
    let len = s.len() as u32;
    match &**e {
        Expr::BVar(i) => {
            let i = *i;
            if i >= n {
                if i < n + len {
                    shift(&s[(len - (i - n + 1)) as usize], 0, n)
                } else {
                    bvar(i - len)
                }
            } else {
                e.clone()
            }
        }
        Expr::Const(..) => e.clone(),
        Expr::App(f, a) => app(substs(f, s, n), substs(a, s, n)),
        Expr::Lam { ty, body } => lam(substs(ty, s, n), substs(body, s, n + 1)),
        Expr::Forall { ty, body } => forall(substs(ty, s, n), substs(body, s, n + 1)),
        Expr::Let { ty, val, body } => Rc::new(Expr::Let {
            ty: substs(ty, s, n),
            val: substs(val, s, n),
            body: substs(body, s, n + 1),
        }),
        Expr::Proj { ind, idx, s: x } => {
            Rc::new(Expr::Proj { ind: ind.clone(), idx: *idx, s: substs(x, s, n) })
        }
        Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => e.clone(),
    }
}

/// `Expr.subst`.
pub fn subst(e: &E, a: &E) -> E { substs(e, std::slice::from_ref(a), 0) }

/// `Expr.substLevel`.
pub fn subst_level(e: &E, f: &dyn Fn(&Name) -> Level) -> E {
    match &**e {
        Expr::Const(n, ls) => {
            konst(n.clone(), ls.iter().map(|l| l.subst(f)).collect::<Vec<_>>().into())
        }
        Expr::App(g, a) => app(subst_level(g, f), subst_level(a, f)),
        Expr::Lam { ty, body } => lam(subst_level(ty, f), subst_level(body, f)),
        Expr::Forall { ty, body } => forall(subst_level(ty, f), subst_level(body, f)),
        Expr::Let { ty, val, body } => Rc::new(Expr::Let {
            ty: subst_level(ty, f),
            val: subst_level(val, f),
            body: subst_level(body, f),
        }),
        Expr::Proj { ind, idx, s } => {
            Rc::new(Expr::Proj { ind: ind.clone(), idx: *idx, s: subst_level(s, f) })
        }
        Expr::Sort(l) => sort(l.subst(f)),
        Expr::BVar(..) | Expr::NatLit(..) | Expr::StrLit(..) => e.clone(),
    }
}

/// `Expr.hasBVar`.
pub fn has_bvar(e: &E, idx: u32) -> bool {
    match &**e {
        Expr::BVar(i) => *i == idx,
        Expr::App(f, a) => has_bvar(f, idx) || has_bvar(a, idx),
        Expr::Lam { ty, body } | Expr::Forall { ty, body } => {
            has_bvar(ty, idx) || has_bvar(body, idx + 1)
        }
        Expr::Let { ty, val, body } => {
            has_bvar(ty, idx) || has_bvar(val, idx) || has_bvar(body, idx + 1)
        }
        _ => false,
    }
}

/// `hasConst`. Note the original does *not* descend into `proj`'s name nor into
/// a `.const`'s level arguments, and neither does this.
pub fn has_const(n: &Name, e: &E) -> bool {
    match &**e {
        Expr::Const(name, _) => name == n,
        Expr::App(f, a) => has_const(n, f) || has_const(n, a),
        Expr::Lam { ty, body } | Expr::Forall { ty, body } => has_const(n, ty) || has_const(n, body),
        Expr::Let { ty, val, body } => {
            has_const(n, ty) || has_const(n, val) || has_const(n, body)
        }
        Expr::Proj { s, .. } => has_const(n, s),
        Expr::BVar(..) | Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => false,
    }
}

/// `Expr.bvars n d` = `#[bvar (n-1+d), …, bvar d]`.
pub fn bvars(n: u32, d: u32) -> Vec<E> { (0..n).rev().map(|i| bvar(i + d)).collect() }

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Const(n, ls) => {
                write!(f, "{n}")?;
                if !ls.is_empty() {
                    write!(f, ".{{")?;
                    for (i, l) in ls.iter().enumerate() {
                        if i > 0 {
                            write!(f, " ")?;
                        }
                        write!(f, "{l}")?;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
            }
            Expr::BVar(i) => write!(f, "#{i}"),
            Expr::App(g, a) => write!(f, "({g} {a})"),
            Expr::Lam { ty, body } => write!(f, "(fun _:{ty} => {body})"),
            Expr::Forall { ty, body } => write!(f, "(∀ _:{ty}, {body})"),
            Expr::NatLit(n) => write!(f, "{n}"),
            Expr::StrLit(s) => write!(f, "{s:?}"),
            Expr::Sort(l) => write!(f, "Sort {l}"),
            Expr::Proj { ind, idx, s } => write!(f, "{s}.{ind}.{idx}"),
            Expr::Let { ty, val, body } => write!(f, "(let _:{ty} := {val}; {body})"),
        }
    }
}
