//! The **internal universe ladder** `lvl`: the recursion theorem instantiated
//! at the step `G := U(·)` and the base `c := ω`.
//!
//! # Interface
//!
//! Writing `lvl` for the 0-ary defined symbol's term ([`UTower::set`]) and
//! `app(lvl, t)` for the value at `t` ([`UTower::at`]), the exports are
//!
//! ```text
//! ⊢ app(lvl, ∅) = ω                                     [UTower::base]
//! ⊢ ∀n. (n ∈ ω → app(lvl, succ n) = U(app(lvl, n)))     [UTower::step]
//! ⊢ ∀n. (n ∈ ω → is_universe(app(lvl, succ n)))         [UTower::step_is_universe]
//! ⊢ ∀n. (n ∈ ω → app(lvl, n) ∈ app(lvl, succ n))        [UTower::climb]
//! ⊢ ∀n. (n ∈ ω → ω ∈ app(lvl, succ n))                  [UTower::omega_mem]
//! ⊢ app(lvl, succ ∅) = U(ω)                             [UTower::rung1_eq]
//! ⊢ app(lvl, succ succ ∅) = U(U(ω))                     [UTower::rung2_eq]
//! ```
//!
//! `∅` in the base is the numeral `0` — over one chain [`Rec`]'s `0` *is* its
//! `∅`, which is what makes the spelling unambiguous. The two rung equations
//! are the numeral bridges to [`crate::tower::Tower`]: when `U(·)` and `ω` are
//! the tower's own symbols, the right-hand sides are literally `Tower::u(1)`
//! and `Tower::u(2)`, so the internal ladder and the meta-level rung terms
//! agree at closed numerals.
//!
//! # Where each fact comes from
//!
//! `base` and `step` are [`crate::recursion::recursion`] at `g := U(·)`,
//! `c := ω`, `params = []` — a closed base makes `iter` a constant (see the
//! note in `theorem.rs`). `climb` is [`crate::universe::mem_least_universe`]
//! at `app(lvl,n)`, rewritten along the reversed step equation;
//! `step_is_universe` is the same rewrite applied to
//! [`crate::universe::least_universe_is_universe`]. `omega_mem` is an
//! induction: the base is `ω ∈ U(ω)` read through the base and step equations
//! at `0`, and the step is `ω ∈ app(lvl, succ n) ∈ U(app(lvl, succ n))`
//! closed by `C₁`-transitivity of `U(·)`
//! ([`crate::universe::least_universe_transitive`]).
//!
//! # Symbol identity
//!
//! `ω`, `∅`, `succ` and `app` are `r`'s; `U(·)` is the caller's `lu`. The
//! Cantor–Schröder–Bernstein prerequisites that `is_universe(U(x))` needs are
//! built here over `r`'s own pairing ([`crate::csb::Csb::with_apply`]), exactly
//! as [`crate::cumul::Paths`] builds them over the chain's — no second pairing
//! is minted. The power-set symbol and its axiom are taken from the caller for
//! the same reason: over a tower they must be the tower's `space.pow`, not
//! `OmegaCore`'s look-alike (see `cumul.rs`, "PRACTICALITIES").

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::csb::Csb;
use crate::recursion::{hyp_eq_symm, induction_scheme, recursion, Rec, Recursion};
use crate::universe as uni;
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, eq_trans, hyp_mp, inst_all, mpd_const, syl,
};

/// The internal universe ladder `lvl`, with everything proved about it.
pub struct UTower {
    /// The term `lvl` — the recursion's 0-ary `iter`, applied to nothing.
    pub set: Term,
    /// `⊢ app(lvl, ∅) = ω`.
    pub base: Thm,
    /// `⊢ ∀n. (n ∈ ω → app(lvl, succ n) = U(app(lvl, n)))`.
    pub step: Thm,
    /// `⊢ ∀n. (n ∈ ω → is_universe(app(lvl, succ n)))`.
    pub step_is_universe: Thm,
    /// `⊢ ∀n. (n ∈ ω → app(lvl, n) ∈ app(lvl, succ n))`.
    pub climb: Thm,
    /// `⊢ ∀n. (n ∈ ω → ω ∈ app(lvl, succ n))`.
    pub omega_mem: Thm,
    /// `⊢ app(lvl, succ ∅) = U(ω)`.
    pub rung1_eq: Thm,
    /// `⊢ app(lvl, succ succ ∅) = U(U(ω))`.
    pub rung2_eq: Thm,
    /// The `app` symbol, kept so [`UTower::at`] spells `app(lvl, n)` exactly
    /// as every theorem above does.
    app: FnSym,
}

impl UTower {
    /// The term `app(lvl, n)`.
    pub fn at(&self, n: Term) -> Term { Term::apply(self.app, vec![self.set.clone(), n]) }
}

/// Run the recursion at `G := U(·)`, base `ω`, and derive the ladder.
///
/// `ω`, `∅`, `succ` and `app` come from `r`; `lu`/`lu_ax` are the caller's
/// least-universe symbol and its characteristic axiom; `pow`/`pow_ax` a power
/// set over the same chain (a tower's `space.pow`), which
/// [`crate::universe::least_universe_is_universe`] spends on clause `C₃`.
pub fn utower(
    env: &mut Env,
    r: &Rec,
    lu: FnSym,
    lu_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> Option<UTower> {
    if lu.arity() != 1 {
        return None
    }
    let omega = r.omega();
    let rec = recursion(env, r, lu, &omega, &[])?;
    debug_assert_eq!(
        *rec.base.concl(),
        Formula::eq(r.apply(rec.set(), r.zero()), omega),
        "utower: the base equation has the wrong shape"
    );

    // The universe theory at `U(·)`. `is_universe(U(x))` needs the
    // Cantor–Schröder–Bernstein prerequisites; they are built over `r`'s own
    // pairing, exactly as `cumul::Paths` builds them over the chain's.
    let csb = Csb::with_apply(env, &r.ap).ok()?;
    let isu = uni::least_universe_is_universe(env, &csb, lu, lu_ax, pow, pow_ax).ok()?;
    let mem_lu = uni::mem_least_universe(env, lu, lu_ax).ok()?;
    let c1 = uni::least_universe_transitive(env, lu, lu_ax).ok()?;

    let step_is_universe = step_is_universe(env, r, &rec, lu, &isu)?;
    let climb = climb(env, r, &rec, lu, &mem_lu)?;
    let omega_mem = omega_mem(env, r, &rec, lu, &mem_lu, &c1)?;
    let rung1_eq = rung1(env, r, &rec, lu)?;
    let rung2_eq = rung2(env, r, &rec, lu, &rung1_eq)?;

    let app = r.ap.app;
    let Recursion { term, base, step, .. } = rec;
    Some(UTower { set: term, base, step, step_is_universe, climb, omega_mem, rung1_eq, rung2_eq, app })
}

/// `⊢ ∀n. (n ∈ ω → is_universe(app(lvl, succ n)))`.
///
/// [`crate::universe::least_universe_is_universe`] at `app(lvl,n)`, carried
/// across the reversed step equation by one Leibniz instance.
fn step_is_universe(env: &mut Env, r: &Rec, rec: &Recursion, lu: FnSym, isu: &Thm) -> Option<Thm> {
    let n = env.fresh_var();
    let tn = Term::var(n);
    let ln = r.apply(rec.set(), tn.clone());
    let lsn = r.apply(rec.set(), r.succ_of(tn.clone()));
    let uln = Term::apply(lu, vec![ln.clone()]);
    let h = Formula::mem(tn, r.omega());

    let h_eq = inst_all(&rec.step, std::slice::from_ref(&Term::var(n)))?;
    debug_assert_eq!(
        *h_eq.concl(),
        Formula::imp(h.clone(), Formula::eq(lsn.clone(), uln.clone())),
        "step_is_universe: the step equation has the wrong shape"
    );
    let h_sym = hyp_eq_symm(env, &h_eq)?;

    let w = env.fresh_var();
    let phi = uni::is_universe(env, &Term::var(w));
    let leib = Thm::eq_leibniz(uln, lsn.clone(), w, phi);
    let h_move = syl(&h_sym, &leib)?;
    let at = inst_all(isu, std::slice::from_ref(&ln))?;
    let body = hyp_mp(&h_move, &a1i(&at, h.clone()))?;
    debug_assert_eq!(
        *body.concl(),
        {
            let f = uni::is_universe(env, &lsn);
            Formula::imp(h, f)
        },
        "step_is_universe: unexpected shape"
    );
    Some(Thm::gen(n, &body))
}

/// `⊢ ∀n. (n ∈ ω → app(lvl, n) ∈ app(lvl, succ n))`.
///
/// `app(lvl,n) ∈ U(app(lvl,n))` is [`crate::universe::mem_least_universe`] at
/// `app(lvl,n)`; the right side is rewritten to `app(lvl, succ n)` along the
/// reversed step equation.
fn climb(env: &mut Env, r: &Rec, rec: &Recursion, lu: FnSym, mem_lu: &Thm) -> Option<Thm> {
    let n = env.fresh_var();
    let tn = Term::var(n);
    let ln = r.apply(rec.set(), tn.clone());
    let lsn = r.apply(rec.set(), r.succ_of(tn.clone()));
    let uln = Term::apply(lu, vec![ln.clone()]);
    let h = Formula::mem(tn, r.omega());

    let h_sym = hyp_eq_symm(env, &inst_all(&rec.step, std::slice::from_ref(&Term::var(n)))?)?;
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(uln, lsn.clone(), w, Formula::mem(ln.clone(), Term::var(w)));
    let at = inst_all(mem_lu, std::slice::from_ref(&ln))?;
    let body = hyp_mp(&syl(&h_sym, &leib)?, &a1i(&at, h.clone()))?;
    debug_assert_eq!(
        *body.concl(),
        Formula::imp(h, Formula::mem(ln, lsn)),
        "climb: unexpected shape"
    );
    Some(Thm::gen(n, &body))
}

/// `⊢ ∀n. (n ∈ ω → ω ∈ app(lvl, succ n))`, by induction on `n`.
///
/// Base: `ω ∈ U(ω)` spelled at `app(lvl, succ ∅)` through the base and step
/// equations at `0`. Step: `ω ∈ app(lvl, succ n) ∈ U(app(lvl, succ n))`, and
/// `C₁`-transitivity of `U(·)` moves `ω` up; the step equation at `succ n`
/// renames the target to `app(lvl, succ succ n)`.
fn omega_mem(
    env: &mut Env,
    r: &Rec,
    rec: &Recursion,
    lu: FnSym,
    mem_lu: &Thm,
    c1: &Thm,
) -> Option<Thm> {
    let lvl = rec.set();
    let omega = r.omega();
    let zero = r.zero();
    let nv = env.fresh_var();
    let tn = Term::var(nv);
    let at = |t: Term| r.apply(lvl.clone(), t);
    let phi = Formula::mem(omega.clone(), at(r.succ_of(tn.clone())));
    let h = Formula::mem(tn.clone(), omega.clone());
    let w = env.fresh_var();

    // ── Base: `ω ∈ app(lvl, succ ∅)` ─────────────────────────────────────────
    let l0 = at(zero.clone());
    let ls0 = at(r.succ_of(zero.clone()));
    let ul0 = Term::apply(lu, vec![l0.clone()]);
    let s0 = Thm::mp(&inst_all(&rec.step, std::slice::from_ref(&zero))?, &r.core().zero_mem)?;
    debug_assert_eq!(
        *s0.concl(),
        Formula::eq(ls0.clone(), ul0.clone()),
        "omega_mem: the step at 0 has the wrong shape"
    );
    // `app(lvl,0) ∈ U(app(lvl,0))`, then `ω` for the left along the base
    // equation, then `app(lvl, succ 0)` for the right along the reversed step.
    let mem0 = inst_all(mem_lu, std::slice::from_ref(&l0))?;
    let leib_l = Thm::eq_leibniz(l0, omega.clone(), w, Formula::mem(Term::var(w), ul0.clone()));
    let om_in_ul0 = Thm::mp(&Thm::mp(&leib_l, &rec.base)?, &mem0)?;
    let ul0_eq = Thm::mp(&eq_symm_imp(env, ls0.clone(), ul0.clone()), &s0)?;
    let leib_r = Thm::eq_leibniz(ul0, ls0, w, Formula::mem(omega.clone(), Term::var(w)));
    let base = Thm::mp(&Thm::mp(&leib_r, &ul0_eq)?, &om_in_ul0)?;
    debug_assert_eq!(*base.concl(), phi.subst(nv, &zero), "omega_mem: the base drifted");

    // ── Step, under `K := n ∈ ω ∧ φ(n)` ──────────────────────────────────────
    let k = Formula::and(h.clone(), phi.clone());
    let k_h = and_left(h.clone(), phi.clone());
    let k_phi = and_right(h.clone(), phi.clone());
    let sn = r.succ_of(tn.clone());
    let lsn = at(sn.clone());
    let lssn = at(r.succ_of(sn.clone()));
    let ulsn = Term::apply(lu, vec![lsn.clone()]);

    let k_sn_om = syl(&k_h, &inst_all(&r.core().succ_closed, std::slice::from_ref(&tn))?)?;
    let k_eq = syl(&k_sn_om, &inst_all(&rec.step, std::slice::from_ref(&sn))?)?;
    debug_assert_eq!(
        *k_eq.concl(),
        Formula::imp(k.clone(), Formula::eq(lssn.clone(), ulsn.clone())),
        "omega_mem: the step at succ n has the wrong shape"
    );
    let k_sym = hyp_eq_symm(env, &k_eq)?;

    // `C₁` at `U(app(lvl, succ n))` moves `ω ∈ app(lvl, succ n)` up one rung.
    let c1_at = inst_all(c1, &[lsn.clone(), lsn.clone()])?;
    let all_z = Thm::mp(&c1_at, &inst_all(mem_lu, std::slice::from_ref(&lsn))?)?;
    let om_step = inst_all(&all_z, std::slice::from_ref(&omega))?;
    let k_om_ulsn = hyp_mp(&a1i(&om_step, k.clone()), &k_phi)?;
    let leib = Thm::eq_leibniz(ulsn, lssn, w, Formula::mem(omega.clone(), Term::var(w)));
    let k_goal = hyp_mp(&syl(&k_sym, &leib)?, &k_om_ulsn)?;
    debug_assert_eq!(
        *k_goal.concl(),
        Formula::imp(k, phi.subst(nv, &sn)),
        "omega_mem: the step drifted"
    );

    let scheme = induction_scheme(env, r.core(), nv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(nv, &k_goal)))
}

/// `⊢ app(lvl, succ ∅) = U(ω)` — the first numeral bridge.
///
/// The step at `0` gives `app(lvl, succ ∅) = U(app(lvl, ∅))`; the base
/// equation under a `U(·)`-congruence closes it.
fn rung1(env: &mut Env, r: &Rec, rec: &Recursion, lu: FnSym) -> Option<Thm> {
    let zero = r.zero();
    let omega = r.omega();
    let l0 = r.apply(rec.set(), zero.clone());
    let l1 = r.apply(rec.set(), r.succ_of(zero.clone()));
    let ul0 = Term::apply(lu, vec![l0.clone()]);
    let uw = Term::apply(lu, vec![omega.clone()]);

    let s0 = Thm::mp(&inst_all(&rec.step, std::slice::from_ref(&zero))?, &r.core().zero_mem)?;
    let w = env.fresh_var();
    let congr = mpd_const(
        &Thm::eq_leibniz(
            l0,
            omega,
            w,
            Formula::eq(ul0.clone(), Term::apply(lu, vec![Term::var(w)])),
        ),
        &Thm::eq_refl(ul0),
    )?;
    let u_eq = Thm::mp(&congr, &rec.base)?;
    let out = eq_trans(env, &s0, &u_eq)?;
    debug_assert_eq!(*out.concl(), Formula::eq(l1, uw), "rung1: unexpected shape");
    Some(out)
}

/// `⊢ app(lvl, succ succ ∅) = U(U(ω))` — the second numeral bridge.
///
/// The step at `1̄ = succ ∅` (a natural by `succ`-closure) gives
/// `app(lvl, 2̄) = U(app(lvl, 1̄))`; [`rung1`] under a `U(·)`-congruence
/// closes it.
fn rung2(env: &mut Env, r: &Rec, rec: &Recursion, lu: FnSym, rung1_eq: &Thm) -> Option<Thm> {
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let l1 = r.apply(rec.set(), one.clone());
    let l2 = r.apply(rec.set(), r.succ_of(one.clone()));
    let uw = Term::apply(lu, vec![r.omega()]);
    let uuw = Term::apply(lu, vec![uw.clone()]);
    let ul1 = Term::apply(lu, vec![l1.clone()]);

    let one_mem =
        Thm::mp(&inst_all(&r.core().succ_closed, std::slice::from_ref(&zero))?, &r.core().zero_mem)?;
    let s1 = Thm::mp(&inst_all(&rec.step, std::slice::from_ref(&one))?, &one_mem)?;
    debug_assert_eq!(
        *s1.concl(),
        Formula::eq(l2.clone(), ul1.clone()),
        "rung2: the step at 1̄ has the wrong shape"
    );
    let w = env.fresh_var();
    let congr = mpd_const(
        &Thm::eq_leibniz(
            l1,
            uw,
            w,
            Formula::eq(ul1.clone(), Term::apply(lu, vec![Term::var(w)])),
        ),
        &Thm::eq_refl(ul1),
    )?;
    let u_eq = Thm::mp(&congr, rung1_eq)?;
    let out = eq_trans(env, &s1, &u_eq)?;
    debug_assert_eq!(*out.concl(), Formula::eq(l2, uuw), "rung2: unexpected shape");
    Some(out)
}
