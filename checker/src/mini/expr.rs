//! `Name`, `Level`, `Expr` — de Bruijn, hash-consed in [`crate::mini::arena`].
//!
//! # Interface
//!
//! Port of `MiniKernel/Types.lean`, `MiniKernel/ExprUtils.lean` and the `Expr`
//! and `Level` helpers at the top of `MiniKernel/Kernel.lean`. Every function
//! here has a named original, and the correspondence is one-to-one on purpose:
//! this file is meant to be reviewed against the Lean side line by line.
//!
//! **The three types are pointers into `checker`'s arena** (PIVOT.md §1.1) —
//! `NamePtr`, `LevelPtr`, `ExprPtr` — rather than the `Rc` trees they were.
//! All three are `Copy`, `==` is a `u32` comparison, and **pointer identity is
//! structural identity**. Reading is `view()`, which hands back an owned
//! `NameView`/`LevelView`/`Expr` whose variant names are still mini's own.
//! What did *not* move is the algebra: `Level`'s `le`, `mk_imax`, `simplify`
//! and the rest are still mini-lean's clauses in mini-lean's order, because
//! `checker`'s would be a different acceptance boundary.
//!
//! Two deliberate departures, both argued in MINI-DESIGN.md §2:
//!
//! * **No binder names.** Mini-lean carries a `Name` on `lam`/`forall`/`let`
//!   purely for printing. The only structural `Expr` comparisons the kernel
//!   performs are against `.bvar` nodes (`isValidIndApp`,
//!   `resType.getApp.2.contains (.bvar shift)`), so dropping the names cannot
//!   change a verdict.
//!
//!   **This is now enforced rather than merely true.** `checker` hash-conses
//!   `binder_name`, `binder_style` and `nondep` into the node, so equality
//!   *would* see them; [`lam`], [`forall`] and [`let_`] pin all three to one
//!   value and `convert::Cv::expr` puts every parsed expression into the same
//!   form on the way in. `crate::mini::arena` states the normal form and pins it
//!   with four tests. Without that discipline `==` on expressions would
//!   quietly become "was built by the same code path".
//! * **No `Local` variant.** Mini is pure de Bruijn: the local context is a
//!   telescope, exactly as in the original. `checker`'s `Expr` has one, and
//!   [`E::view`] panics on it rather than inventing a reading; `convert`
//!   declines any export that carries one, so it cannot arise.
//!
//! Nat literals are `u64`; the parser declines anything above 10 (mini-lean's
//! own guard), so the width is never load-bearing. De Bruijn indices are
//! `u32` here and `u16` in the arena — measured, the largest mini ever builds
//! over the whole corpus is 38, and `arena::bvar` is the one narrowing point
//! and panics rather than wrapping.

use crate::expr::Expr as CExpr;
use crate::level::Level as CLevel;
use crate::name::Name as CName;
use crate::util::{ExprPtr, LevelPtr, NamePtr};
use std::fmt;
use std::rc::Rc;

// ─────────────────────────────────────────────────────────────── names ──

/// A Lean name, as a pointer into [`crate::mini::arena`].
///
/// **A handle, not a tree.** It was `enum Name { Anon, Str(Rc<Name>,
/// Rc<str>), Num(Rc<Name>, u64) }`; it is now `checker`'s hash-consed
/// `NamePtr`, so it is `Copy`, equality is a `u32` comparison, and two
/// spellings of one name are one pointer. The migration kept both smart
/// constructors' signatures — [`Name::simple`] and [`Name::str`] are 382 of
/// the 419 call sites — so only the 37 sites that matched the variants
/// directly had to change, and they use [`Name::view`].
///
/// `Ord` is deliberately absent, as it was before: `crate::mini::dump` sorts by
/// *rendered* name, and a pointer order would be allocation order, which is
/// not stable across runs.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Name(pub NamePtr<'static>);

/// [`Name`] destructured one level. The `Rc<str>` is a copy out of the
/// arena — the component cannot be handed out by reference, because the
/// borrow of the context must not escape (`crate::mini::arena`'s `read`).
///
/// Every site that uses this is name *classification* — "is this
/// `Quot.sound`", "is this `T.rec._auxRule_3`" — on declaration names, not on
/// expression nodes, so the copy is off every hot path.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum NameView {
    Anon,
    Str(Name, Rc<str>),
    Num(Name, u64),
}

impl Name {
    /// `Name.anonymous`.
    pub fn anon() -> Name { Name(crate::mini::arena::name_anon()) }

    /// `Name.simple`: a one-component name.
    pub fn simple(s: &str) -> Name { Name(crate::mini::arena::name_str(crate::mini::arena::name_anon(), s)) }

    /// `Name.str`.
    pub fn str(pre: &Name, s: &str) -> Name { Name(crate::mini::arena::name_str(pre.0, s)) }

    /// `Name.num`.
    pub fn num(pre: &Name, i: u64) -> Name { Name(crate::mini::arena::name_num(pre.0, i)) }

    /// One level of structure. See [`NameView`].
    pub fn view(&self) -> NameView {
        match crate::mini::arena::read_name(self.0) {
            CName::Anon => NameView::Anon,
            CName::Str(pre, s, _) => NameView::Str(Name(pre), Rc::from(crate::mini::arena::read_string(s))),
            CName::Num(pre, i, _) => NameView::Num(Name(pre), i),
        }
    }

    /// Whether this is the anonymous name — the root test, written out
    /// because it is the commonest thing the old `**pre == Name::Anon`
    /// spelling said and it should not need a component copy.
    pub fn is_anon(&self) -> bool { self.0 == crate::mini::arena::name_anon() }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.view() {
            NameView::Anon => write!(f, "[anonymous]"),
            NameView::Str(pre, s) => {
                if pre.is_anon() {
                    write!(f, "{s}")
                } else {
                    write!(f, "{pre}.{s}")
                }
            }
            NameView::Num(pre, i) => {
                if pre.is_anon() {
                    write!(f, "{i}")
                } else {
                    write!(f, "{pre}.{i}")
                }
            }
        }
    }
}

/// Renders the name, not the pointer.
///
/// Not the derive: assertion messages across the suite say `{n:?}` — for
/// instance `convert`'s "a user-declared axiom passed as one of Lean's own" —
/// and a bare `Name(Ptr { raw: 41 })` would turn a diagnostic into a puzzle.
/// Quoted, so that a name with a dot *in a component* is still visibly one
/// component, which is exactly the distinction that test is about.
impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "`{self}`") }
}

// ────────────────────────────────────────────────────────────── levels ──

/// A Lean universe level, as a pointer into [`crate::mini::arena`].
///
/// **The representation is `checker`'s; the algebra is mini's, and that
/// separation is deliberate.** `checker` has its own `leq`, `simplify` and
/// `imax` smart constructor, and substituting them here would be a behaviour
/// change on the *acceptance* axis: everything below is a clause-for-clause
/// port of `mini-lean`'s `Level` helpers, in the original's clause order,
/// which is what `MINI-DESIGN.md` §3 and the mini-vs-nanoda gate are about.
/// So the nodes are shared and the decision procedure is not.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Level(pub LevelPtr<'static>);

/// [`Level`] destructured one level. `Copy`, so reading costs no allocation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LevelView {
    Zero,
    Succ(Level),
    Max(Level, Level),
    IMax(Level, Level),
    Param(Name),
}

impl Level {
    /// `Level.zero`.
    pub fn zero() -> Level { Level(crate::mini::arena::level_zero()) }

    /// `Level.param`.
    pub fn param(n: Name) -> Level { Level(crate::mini::arena::level_param(n.0)) }

    pub fn succ(self) -> Level { Level(crate::mini::arena::level_succ(self.0)) }

    /// `Level.max` — **the dumb constructor**, as in the original. `checker`'s
    /// `TcCtx::max` is dumb too; the simplifying one is [`Level::mk_imax`] and
    /// [`Level::simplify`], both ported below.
    pub fn max(a: Level, b: Level) -> Level { Level(crate::mini::arena::level_max(a.0, b.0)) }

    pub fn imax(a: Level, b: Level) -> Level { Level(crate::mini::arena::level_imax(a.0, b.0)) }

    /// One level of structure. See [`LevelView`].
    pub fn view(&self) -> LevelView {
        match crate::mini::arena::read_level(self.0) {
            CLevel::Zero => LevelView::Zero,
            CLevel::Succ(l, _) => LevelView::Succ(Level(l)),
            CLevel::Max(a, b, _) => LevelView::Max(Level(a), Level(b)),
            CLevel::IMax(a, b, _) => LevelView::IMax(Level(a), Level(b)),
            CLevel::Param(n, _) => LevelView::Param(Name(n)),
        }
    }

    /// **Whether this is literally the `zero` node.**
    ///
    /// Not [`Level::is_zero`], and the difference is load-bearing: that one is
    /// `Level.isZero`, which recurses through `max` and `imax` and answers
    /// `true` for `max 0 0`. This is what `matches!(l, Level::Zero)` used to
    /// say at the two sites that ask it — `census`'s `PiProp` row and
    /// `kernel`'s constructor-argument level check — and widening either to
    /// the recursive test would move an acceptance boundary. Hash-consing
    /// makes it a pointer comparison.
    pub fn is_zero_syntactically(&self) -> bool { self.0 == crate::mini::arena::level_zero() }

    /// `Level.isZero`.
    pub fn is_zero(&self) -> bool {
        match self.view() {
            LevelView::Zero => true,
            LevelView::Max(a, b) => a.is_zero() && b.is_zero(),
            LevelView::IMax(_, b) => b.is_zero(),
            LevelView::Succ(_) | LevelView::Param(_) => false,
        }
    }

    /// `Level.isNotZero`.
    pub fn is_not_zero(&self) -> bool {
        match self.view() {
            LevelView::Zero => false,
            LevelView::Max(a, b) => a.is_not_zero() || b.is_not_zero(),
            LevelView::IMax(_, b) => b.is_not_zero(),
            LevelView::Succ(_) => true,
            LevelView::Param(_) => false,
        }
    }

    /// `Level.substLevel`.
    pub fn subst(&self, f: &dyn Fn(&Name) -> Level) -> Level {
        match self.view() {
            LevelView::Param(n) => f(&n),
            LevelView::Zero => Level::zero(),
            LevelView::Succ(l) => l.subst(f).succ(),
            LevelView::Max(a, b) => Level::max(a.subst(f), b.subst(f)),
            LevelView::IMax(a, b) => Level::imax(a.subst(f), b.subst(f)),
        }
    }

    /// `Level.substOneLevel`.
    pub fn subst_one(&self, n: &Name, l: &Level) -> Level {
        self.subst(&|m| if m == n { *l } else { Level::param(*m) })
    }

    /// `Level.mkIMax` — the smart constructor keeping `imax`'s rhs a parameter.
    pub fn mk_imax(l1: &Level, l2: &Level) -> Level {
        match l2.view() {
            LevelView::Zero => Level::zero(),
            LevelView::Succ(_) => Level::max(*l1, *l2),
            LevelView::Max(a, b) => Level::max(Level::mk_imax(l1, &a), Level::mk_imax(l1, &b)),
            LevelView::IMax(a, b) => Level::mk_imax(&Level::max(*l1, a), &b),
            LevelView::Param(_) => Level::imax(*l1, *l2),
        }
    }

    /// `Level.simplify`.
    pub fn simplify(&self) -> Level {
        match self.view() {
            LevelView::Zero => Level::zero(),
            LevelView::Succ(l) => l.simplify().succ(),
            LevelView::Max(a, b) => Level::max(a.simplify(), b.simplify()),
            LevelView::IMax(a, b) => Level::mk_imax(&a.simplify(), &b.simplify()),
            LevelView::Param(n) => Level::param(n),
        }
    }

    /// `Level.byCases`.
    fn by_cases(p: &Name, l1: &Level, l2: &Level, balance: i64) -> bool {
        let succ_p = Level::param(*p).succ();
        let zero = Level::zero();
        Level::le(&l1.subst_one(p, &zero).simplify(), &l2.subst_one(p, &zero).simplify(), balance)
            && Level::le(
                &l1.subst_one(p, &succ_p).simplify(),
                &l2.subst_one(p, &succ_p).simplify(),
                balance,
            )
    }

    /// `Level.le` — the balance algorithm, ported clause for clause and in the
    /// original's clause order. `LevelProofs.lean` proves it correct but
    /// incomplete; incompleteness only ever rejects, and every use on mini's
    /// hot path is at ground levels where it is exact (MINI-DESIGN.md §3).
    pub fn le(l1: &Level, l2: &Level, balance: i64) -> bool {
        // The rhs-is-a-parameter shape an `imax` must have after `simplify`.
        fn imax_param(l: &Level) -> Option<Name> {
            match l.view() {
                LevelView::IMax(_, r) => match r.view() {
                    LevelView::Param(p) => Some(p),
                    _ => None,
                },
                _ => None,
            }
        }
        let (v1, v2) = (l1.view(), l2.view());
        if let LevelView::Succ(a) = v1 {
            return Level::le(&a, l2, balance - 1)
        }
        if let LevelView::Succ(b) = v2 {
            return Level::le(l1, &b, balance + 1)
        }
        if let LevelView::Max(a, b) = v1 {
            return Level::le(&a, l2, balance) && Level::le(&b, l2, balance)
        }
        if let (LevelView::Param(n), LevelView::Param(m)) = (v1, v2) {
            return n == m && balance >= 0
        }
        if let Some(p) = imax_param(l1).or_else(|| imax_param(l2)) {
            return Level::by_cases(&p, l1, l2, balance)
        }
        // Unreachable by the simplification invariant, and `false` there too.
        if matches!(v1, LevelView::IMax(..)) || matches!(v2, LevelView::IMax(..)) {
            return false
        }
        if matches!(v1, LevelView::Param(_) | LevelView::Zero) {
            if let LevelView::Max(a, b) = v2 {
                return Level::le(l1, &a, balance) || Level::le(l1, &b, balance)
            }
        }
        if matches!(v1, LevelView::Zero) && balance >= 0 {
            return true
        }
        // Everything left — `(zero, zero|param)` at a negative balance and
        // `(param, zero)` — is `false` in the original.
        false
    }
}

/// Renders the level, not the pointer — the argument [`Name`]'s `Debug` gives.
impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self}") }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.view() {
            LevelView::Zero => write!(f, "0"),
            LevelView::Succ(l) => write!(f, "({l}+1)"),
            LevelView::Max(a, b) => write!(f, "max({a},{b})"),
            LevelView::IMax(a, b) => write!(f, "imax({a},{b})"),
            LevelView::Param(n) => write!(f, "{n}"),
        }
    }
}

// ───────────────────────────────────────────────────────── expressions ──

/// A Lean expression, as a pointer into [`crate::mini::arena`].
///
/// **Hash-consed, so `==` is a `u32` comparison and pointer identity *is*
/// structural identity.** That equivalence is what the whole migration is
/// for, and it is conditional on one discipline: every binder mini builds
/// carries the anonymous name and the default style, and every parsed
/// expression is put into the same normal form by `arena::erase_binders` on
/// the way in. `crate::mini::arena`'s header argues why, and four tests there pin
/// it. Without that, a *generated* `∀ _ : A, B` and a *parsed* `∀ x : A, B`
/// would be different pointers for what this file has always treated as one
/// expression.
///
/// Reading is [`E::view`], which hands back an owned [`Expr`]; the old
/// `&**e` spelling becomes `&e.view()`, and the binding modes are unchanged
/// because `Rc<Expr>` and `E` are both what a pattern used to bind by
/// reference.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct E(pub ExprPtr<'static>);

/// [`E`] destructured one level.
///
/// The variant names and shapes are mini's own, not `checker`'s: `BVar` for
/// `Var`, `Forall` for `Pi`, `StrLit` for `StringLit`, and no `Local`. Mini
/// is pure de Bruijn — the local context is `Checker::lenv`, a telescope —
/// so a `Local` node cannot arise; `convert` declines any export carrying
/// one, and [`E::view`] panics rather than inventing a reading for it.
///
/// The binder metadata `checker` keeps on `Lambda`/`Pi`/`Let` is *absent
/// here on purpose*. It is pinned to one value at construction, so there is
/// nothing to report and nothing a caller could act on.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    Const(Name, Rc<[Level]>),
    BVar(u32),
    App(E, E),
    Lam { ty: E, body: E },
    Forall { ty: E, body: E },
    NatLit(u128),
    StrLit(Rc<str>),
    Sort(Level),
    Proj { ind: Name, idx: u32, s: E },
    Let { ty: E, val: E, body: E },
}

impl E {
    /// **How many enclosing binders this expression reaches out to**, read off
    /// the arena node in O(1) rather than walked.
    ///
    /// `checker`'s arena stores it on every node that can have one (`App`,
    /// `Pi`, `Lambda`, `Let`, `Proj`), exactly as Lean's `expr` header does.
    /// Zero means *closed*: the expression denotes the same judgement under
    /// every telescope, which is what
    /// [`Checker::defeq_cache`](crate::mini::kernel::Checker) keys on.
    ///
    /// Not [`has_bvar`], which is a recursive walk answering a different
    /// question (does index `i` occur) and which deliberately does not look
    /// inside a `Proj`.
    pub fn num_loose_bvars(&self) -> u16 {
        crate::mini::arena::read_expr(self.0).num_loose_bvars()
    }

    /// One level of structure.
    pub fn view(&self) -> Expr {
        match crate::mini::arena::read_expr(self.0) {
            CExpr::Var { dbj_idx, .. } => Expr::BVar(u32::from(dbj_idx)),
            CExpr::Sort { level, .. } => Expr::Sort(Level(level)),
            CExpr::Const { name, levels, .. } => {
                Expr::Const(Name(name), crate::mini::arena::levels_of(levels))
            }
            CExpr::App { fun, arg, .. } => Expr::App(E(fun), E(arg)),
            CExpr::Lambda { binder_type, body, .. } => {
                Expr::Lam { ty: E(binder_type), body: E(body) }
            }
            CExpr::Pi { binder_type, body, .. } => {
                Expr::Forall { ty: E(binder_type), body: E(body) }
            }
            CExpr::Let { binder_type, val, body, .. } => {
                Expr::Let { ty: E(binder_type), val: E(val), body: E(body) }
            }
            CExpr::Proj { ty_name, idx, structure, .. } => Expr::Proj {
                ind: Name(ty_name),
                // The arena's `idx` is a `usize` and mini's is a `u32`.
                // `convert` refuses a projection index that does not fit on
                // the way in, so this cannot be reached with one that does
                // not — and if it ever were, a wrap would silently project a
                // different field.
                idx: u32::try_from(idx).expect("projection index exceeds u32"),
                s: E(structure),
            },
            CExpr::NatLit { ptr, .. } => {
                let s = crate::mini::arena::read_nat_lit_decimal(ptr)
                    .expect("mini::arena: a nat literal with the nat extension off");
                // Mini declines anything above ten at the frontend, so every
                // literal that reaches here fits. `u64::MAX` keeps the old
                // `parse().unwrap_or(u64::MAX)` behaviour for the impossible
                // case rather than panicking in the middle of a walk.
                // `convert::literal_value` declines anything past the
                // type on the way in, so a parse failure here is not a value
                // this walk can meet.
                Expr::NatLit(s.parse().unwrap_or(u128::MAX))
            }
            CExpr::StringLit { ptr, .. } => {
                Expr::StrLit(Rc::from(crate::mini::arena::read_string(ptr)))
            }
            CExpr::Local { .. } => {
                panic!("mini has no Local: the local context is Checker::lenv, a telescope")
            }
        }
    }
}

pub fn bvar(i: u32) -> E { E(crate::mini::arena::bvar(i)) }
pub fn sort(l: Level) -> E { E(crate::mini::arena::sort(l.0)) }
pub fn konst(n: Name, ls: Rc<[Level]>) -> E {
    let ptrs: Vec<_> = ls.iter().map(|l| l.0).collect();
    E(crate::mini::arena::konst(n.0, crate::mini::arena::alloc_levels(&ptrs)))
}
pub fn app(f: E, a: E) -> E { E(crate::mini::arena::app(f.0, a.0)) }
pub fn lam(ty: E, body: E) -> E { E(crate::mini::arena::lam(ty.0, body.0)) }
pub fn forall(ty: E, body: E) -> E { E(crate::mini::arena::pi(ty.0, body.0)) }
pub fn let_(ty: E, val: E, body: E) -> E { E(crate::mini::arena::let_(ty.0, val.0, body.0)) }
pub fn proj(ind: Name, idx: u32, s: E) -> E {
    E(crate::mini::arena::proj(ind.0, idx as usize, s.0))
}
pub fn nat_lit(n: u128) -> E { E(crate::mini::arena::nat_lit(n)) }
pub fn str_lit(s: &str) -> E { E(crate::mini::arena::str_lit(s)) }

/// `Expr.arrow` — a non-dependent `Π`. Note the original does **not** shift
/// `b`: callers (only `addQuot`) write the de Bruijn indices out by hand.
pub fn arrow(a: E, b: E) -> E { forall(a, b) }

/// `Expr.getApp`.
pub fn get_app(e: &E) -> (E, Vec<E>) {
    let mut args = Vec::new();
    let mut cur = *e;
    while let Expr::App(f, a) = cur.view() {
        args.push(a);
        cur = f;
    }
    args.reverse();
    (cur, args)
}

/// `Expr.appN`.
pub fn app_n(f: E, args: &[E]) -> E {
    let mut out = f;
    for a in args {
        out = app(out, *a);
    }
    out
}

/// `Expr.shift`.
pub fn shift(e: &E, n: u32, d: u32) -> E {
    if d == 0 {
        return *e
    }
    match e.view() {
        Expr::BVar(i) => {
            if i >= n {
                bvar(i + d)
            } else {
                *e
            }
        }
        Expr::App(f, a) => app(shift(&f, n, d), shift(&a, n, d)),
        Expr::Lam { ty, body } => lam(shift(&ty, n, d), shift(&body, n + 1, d)),
        Expr::Forall { ty, body } => forall(shift(&ty, n, d), shift(&body, n + 1, d)),
        Expr::Let { ty, val, body } => {
            let_(shift(&ty, n, d), shift(&val, n, d), shift(&body, n + 1, d))
        }
        Expr::Proj { ind, idx, s } => proj(ind, idx, shift(&s, n, d)),
        Expr::Const(..) | Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => *e,
    }
}

/// `Expr.substs`. `s` is in *argument* order: `s[0]` replaces the outermost of
/// the substituted variables, `s[len-1]` replaces `bvar n`.
pub fn substs(e: &E, s: &[E], n: u32) -> E {
    let len = s.len() as u32;
    match e.view() {
        Expr::BVar(i) => {
            if i >= n {
                if i < n + len {
                    shift(&s[(len - (i - n + 1)) as usize], 0, n)
                } else {
                    bvar(i - len)
                }
            } else {
                *e
            }
        }
        Expr::Const(..) => *e,
        Expr::App(f, a) => app(substs(&f, s, n), substs(&a, s, n)),
        Expr::Lam { ty, body } => lam(substs(&ty, s, n), substs(&body, s, n + 1)),
        Expr::Forall { ty, body } => forall(substs(&ty, s, n), substs(&body, s, n + 1)),
        Expr::Let { ty, val, body } => {
            let_(substs(&ty, s, n), substs(&val, s, n), substs(&body, s, n + 1))
        }
        Expr::Proj { ind, idx, s: x } => proj(ind, idx, substs(&x, s, n)),
        Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => *e,
    }
}

/// `Expr.subst`.
pub fn subst(e: &E, a: &E) -> E { substs(e, std::slice::from_ref(a), 0) }

/// `Expr.substLevel`.
pub fn subst_level(e: &E, f: &dyn Fn(&Name) -> Level) -> E {
    match e.view() {
        Expr::Const(n, ls) => {
            konst(n, ls.iter().map(|l| l.subst(f)).collect::<Vec<_>>().into())
        }
        Expr::App(g, a) => app(subst_level(&g, f), subst_level(&a, f)),
        Expr::Lam { ty, body } => lam(subst_level(&ty, f), subst_level(&body, f)),
        Expr::Forall { ty, body } => forall(subst_level(&ty, f), subst_level(&body, f)),
        Expr::Let { ty, val, body } => {
            let_(subst_level(&ty, f), subst_level(&val, f), subst_level(&body, f))
        }
        Expr::Proj { ind, idx, s } => proj(ind, idx, subst_level(&s, f)),
        Expr::Sort(l) => sort(l.subst(f)),
        Expr::BVar(..) | Expr::NatLit(..) | Expr::StrLit(..) => *e,
    }
}

/// `Expr.hasBVar`.
pub fn has_bvar(e: &E, idx: u32) -> bool {
    match e.view() {
        Expr::BVar(i) => i == idx,
        Expr::App(f, a) => has_bvar(&f, idx) || has_bvar(&a, idx),
        Expr::Lam { ty, body } | Expr::Forall { ty, body } => {
            has_bvar(&ty, idx) || has_bvar(&body, idx + 1)
        }
        Expr::Let { ty, val, body } => {
            has_bvar(&ty, idx) || has_bvar(&val, idx) || has_bvar(&body, idx + 1)
        }
        _ => false,
    }
}

/// **`has_bvar`, and it also looks inside a `proj`'s subject** — the
/// dependency test §6.2's two `Π` clauses are chosen by, and *not* the port.
///
/// [`has_bvar`] is `Expr.hasBVar` and falls through `Expr::Proj` to `false`,
/// because mini-lean's does. That is fine where the original uses it — the
/// dependency guard in `infer_proj` is acceptance, and `085`/`087`–`089` in
/// `bad/tutorial/` are built around exactly the behaviour it has — and it is
/// **wrong for deciding which `Π` clause interprets a type**, for one reason:
///
/// ```text
/// ∀ self : PSigma α β, β (PSigma.fst α β self)      the declared type
/// ∀ self : PSigma α β, β (self.PSigma.0)            infer_proj's spelling
/// ```
///
/// are the same type, and `has_bvar` says the first is dependent and the second
/// is not. `⟦ty⟧` is built from the declared spelling and `⟦val⟧`'s innermost λ
/// from the inferred one, so the two sides classified one binder two ways and
/// the λ's typing was assembled at `fs` against a `dprod`. That is
/// `MINI-HANDOFF.md` §5's row — one type classified twice — at the λ/Π boundary
/// rather than at a conversion, and here the two classifications are **not**
/// both right: one of them is blind.
///
/// **Over-approximating is the safe direction and under-approximating is not.**
/// `dprod` is the general clause and `derived::ext::dprod_const_fibre_n` is the
/// bridge back to `fs`; there is no bridge the other way, because a `dprod`
/// whose fibre really does vary is not a function space.
///
/// Kept beside `has_bvar` rather than replacing it: changing the port would
/// move an acceptance boundary to make a certificate easier, which §5 says the
/// boundary wins.
pub fn has_bvar_in_proj(e: &E, idx: u32) -> bool {
    match e.view() {
        Expr::BVar(i) => i == idx,
        Expr::App(f, a) => has_bvar_in_proj(&f, idx) || has_bvar_in_proj(&a, idx),
        Expr::Lam { ty, body } | Expr::Forall { ty, body } => {
            has_bvar_in_proj(&ty, idx) || has_bvar_in_proj(&body, idx + 1)
        }
        Expr::Let { ty, val, body } => {
            has_bvar_in_proj(&ty, idx)
                || has_bvar_in_proj(&val, idx)
                || has_bvar_in_proj(&body, idx + 1)
        }
        Expr::Proj { s, .. } => has_bvar_in_proj(&s, idx),
        Expr::Const(..) | Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => false,
    }
}

/// `hasConst`. Note the original does *not* descend into `proj`'s name nor into
/// a `.const`'s level arguments, and neither does this.
pub fn has_const(n: &Name, e: &E) -> bool {
    match e.view() {
        Expr::Const(name, _) => name == *n,
        Expr::App(f, a) => has_const(n, &f) || has_const(n, &a),
        Expr::Lam { ty, body } | Expr::Forall { ty, body } => {
            has_const(n, &ty) || has_const(n, &body)
        }
        Expr::Let { ty, val, body } => {
            has_const(n, &ty) || has_const(n, &val) || has_const(n, &body)
        }
        Expr::Proj { s, .. } => has_const(n, &s),
        Expr::BVar(..) | Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => false,
    }
}

/// `Expr.bvars n d` = `#[bvar (n-1+d), …, bvar d]`.
pub fn bvars(n: u32, d: u32) -> Vec<E> { (0..n).rev().map(|i| bvar(i + d)).collect() }

/// Renders the expression, not the pointer — the argument [`Name`]'s `Debug`
/// gives. Error strings across the kernel interpolate an expression with
/// `{e}`, and `Gap`'s derived `Debug` reaches these too.
impl fmt::Debug for E {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self}") }
}

impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self.view()) }
}

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
