//! `⟦Sort ·⟧` at a variable level: the **term builder**
//! `srt(n) := ite0(n, U₀, app(lvl, n))`, and what makes it a sort ladder.
//!
//! # Interface
//!
//! `srt(t)` is the term [`Srt::at`] builds — **literally the `ite0`
//! application, no new symbol** — with `U(·)` the tower's least universe,
//! `U₀ = {0,1}` its rung 0, and `lvl` the internal ladder
//! ([`crate::levels::utower`]). The exports are
//!
//! ```text
//! ⊢ srt(∅) = U₀                                     [Srt::at_zero]
//! ⊢ ∀n. (n ∈ ω → srt(succ n) = U(app(lvl, n)))      [Srt::at_succ]
//! ⊢ ∀n. (n ∈ ω → srt(n) ⊆ srt(succ n))              [Srt::step_sub]
//! ⊢ ∀n. (n ∈ ω → srt(n) ∈ srt(succ n))              [Srt::sort_in_sort]
//! ⊢ ∀n. (n ∈ ω → ∀m. (m ∈ n → srt(m) ⊆ srt(n)))     [Srt::mono_mem]
//! ⊢ ∀n. (n ∈ ω → ω ∈ srt(succ n))                   [Srt::omega_mem]
//! ⊢ ∀n. (n ∈ ω → U₀ ∈ srt(succ n))                  [Srt::u0_mem]
//! ⊢ ∀n. (n ∈ ω → ∅ ∈ srt(n))                        [Srt::empty_mem]
//! ⊢ ∀n. (n ∈ ω → ∀y. (y ∈ srt(n) →
//!                     ∀z. (z ∈ y → z ∈ srt(n))))    [Srt::transitive]
//! ```
//!
//! The last two are [`crate::tower::Rung`]'s `empty_mem` and `transitive` at a
//! **variable** rung, and they are the two facts a `COD` obligation spends. At
//! `succ n` they are the tower's own, read through [`Srt::at_succ`]; at `∅`
//! they are facts about `U₀ = {0,1}` specifically, because rung 0 is not a
//! universe. Both hold there: `0` **is** `∅` (`crate::sums`), so `∅ ∈ U₀` is
//! [`Tower::false_in_u0`] verbatim, and every member of a member of `{0,1}` is
//! `•`, which is `∅` again — [`Tower::u0_subsingleton`] is proof irrelevance
//! and doubles as `{0,1}`'s transitivity.
//!
//! where `⊆` is spelled [`kernel::thm::subset`] exactly. This is `⟦Sort ℓ⟧`
//! as one term of a variable level (`LEVELPOLY.md`): at the closed numeral `0`
//! it is `U₀` — Lean's `Prop` — and at every successor it is a genuine
//! universe, which is what the `ite0` guard is for.
//!
//! # Symbol identity
//!
//! `∅`, `succ`, `ω` and `app` are `r`'s, and they **must** be the ones both
//! the [`Ite0`] and the [`UTower`] were built over — `ite0`'s guard compares
//! against `r.ap.empty`, and the ladder equations speak about `r`'s `app` —
//! or every theorem here would be about the wrong constants. The `Tower`
//! supplies `U₀`, `u0_in`, `transitive` and `mem_u` over that same chain
//! (the test assembly rebuilds [`Rec`] from the tower's own `Apply` and
//! `Peano`, exactly as `levels_utower.rs` does). The constructor guards the
//! cheap identities and lets the kernel refuse the rest: a mismatched symbol
//! makes some composition below fail to line up, and the constructor returns
//! `None` rather than a theorem about look-alikes.
//!
//! # Where each fact comes from
//!
//! `at_zero` is `when_zero` discharged with `⊢ ∅ = ∅`; `at_succ` is
//! `when_nonzero` — the guard refuted by `succ_ne_zero` — chained with
//! [`UTower::step`]. `sort_in_sort` is an induction whose base transports
//! `U₀ ∈ U(ω)` along `at_zero` and the rung-1 equation, and whose step reads
//! `x ∈ U(x)` at `app(lvl, succ n)` through the step and `at_succ` equations
//! (the induction hypothesis is never used). `step_sub` reads `sort_in_sort`
//! through `C₁`-transitivity of `U(·)`; `mono_mem` is a second induction with
//! a case split on `z ∈ succ(n) ↔ (z ∈ n ∨ z = n)`, closed by
//! [`crate::cumul::subset_trans`]. `omega_mem` and `u0_mem` are the cited
//! tower facts rewritten along `at_succ` reversed.
//!
//! `empty_mem` and `transitive` are two further inductions, and **not the
//! `Order::cases` split they were sized at**: `crate::levels::order` is not a
//! parameter of this module and does not have to become one. `empty_mem`'s
//! step is [`step_sub`] applied to the induction hypothesis — the ladder only
//! grows, so a member stays a member. `transitive`'s step never reads its
//! hypothesis at all, exactly as `sort_in_sort`'s does not: every successor
//! rung is a universe outright, so [`Tower::transitive`] settles it and the
//! induction is doing nothing but the case analysis. What that buys over
//! `Order::cases` is the *existential* — `n = succ m` would have to be
//! eliminated and the equation carried through three occurrences of `srt(n)`,
//! where the induction hands the successor over already spelled.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::levels::ite0::Ite0;
use crate::levels::utower::{numeral, numeral_in_omega, UTower};
use crate::recursion::{hyp_eq_symm, hyp_eq_trans, induction_scheme, Rec};
use crate::tower::Tower;
use crate::{
    a1i, and_intro, and_intro_imp, and_left, and_right, eq_symm_imp, eq_trans, ex_falso, hyp_and,
    hyp_mp, hyp_or_elim, iff_mp, imp_mono_r, inst_all, mpd_const, syl, uncurry,
};

/// The sort ladder `srt(n) = ite0(n, U₀, app(lvl, n))`, with everything proved
/// about it. See the module header for the statements.
pub struct Srt {
    /// `⊢ srt(∅) = U₀`.
    pub at_zero: Thm,
    /// `⊢ ∀n. (n ∈ ω → srt(succ n) = U(app(lvl, n)))`.
    pub at_succ: Thm,
    /// `⊢ ∀n. (n ∈ ω → srt(n) ⊆ srt(succ n))`.
    pub step_sub: Thm,
    /// `⊢ ∀n. (n ∈ ω → srt(n) ∈ srt(succ n))`.
    pub sort_in_sort: Thm,
    /// `⊢ ∀n. (n ∈ ω → ∀m. (m ∈ n → srt(m) ⊆ srt(n)))`.
    pub mono_mem: Thm,
    /// `⊢ ∀n. (n ∈ ω → ω ∈ srt(succ n))`.
    pub omega_mem: Thm,
    /// `⊢ ∀n. (n ∈ ω → U₀ ∈ srt(succ n))`.
    pub u0_mem: Thm,
    /// `⊢ ∀n. (n ∈ ω → ∅ ∈ srt(n))` — [`crate::tower::Rung::empty_mem`] at a
    /// variable rung. At **every** rung, `∅` included, which is the half
    /// `u0_mem` does not cover.
    pub empty_mem: Thm,
    /// `⊢ ∀n. (n ∈ ω → ∀y. (y ∈ srt(n) → ∀z. (z ∈ y → z ∈ srt(n))))` —
    /// [`crate::tower::Rung::transitive`] at a variable rung.
    pub transitive: Thm,
    /// The `ite0` symbol, kept so [`Srt::at`] spells the application exactly
    /// as every theorem above does.
    ite0: FnSym,
    /// The `app` symbol of the chain, for the `app(lvl, n)` branch.
    app: FnSym,
    /// The ladder term `lvl`.
    lvl: Term,
    /// The rung-0 term `U₀ = {0,1}`.
    u0: Term,
}

impl Srt {
    /// The term `srt(n) = ite0(n, U₀, app(lvl, n))`. No new symbol: this is
    /// the `ite0` application itself.
    pub fn at(&self, n: Term) -> Term {
        let branch = Term::apply(self.app, vec![self.lvl.clone(), n.clone()]);
        Term::apply(self.ite0, vec![n, self.u0.clone(), branch])
    }

    /// The rung-0 term `U₀`, exactly as the theorems spell it.
    pub fn u0(&self) -> Term { self.u0.clone() }

    /// **The ground bridge: `⊢ srt(n̄) = Uₙ`** — the sort ladder at a closed
    /// numeral, equated with the meta-level rung term
    /// [`crate::tower::Tower::u`] builds.
    ///
    /// This is `LEVELPOLY.md` §1.2's bridge equation at a numeral, and it is
    /// what lets one vocabulary replace two: with `⟦Sort ℓ⟧ = srt(ℓ̂)` at
    /// *every* level, a `derived` library theorem stated over a rung —
    /// `x ∈ U(x)`, `U₀ ∈ U₁`, an inductive type's membership in `U(ω)` — is
    /// transported to the unified spelling by this equation and one Leibniz
    /// step, instead of being blinded by it.
    ///
    /// The two ladders agree everywhere but disagree in *shape* at the bottom,
    /// which is the whole content:
    ///
    /// ```text
    /// srt(0̄) = U₀            — the ite0 guard, not the ladder    [at_zero]
    /// srt(1̄) = U(ω)  = U₁    — at_succ at 0̄, then lvl(0̄) = ω
    /// srt(n̄) = U(U_{n-1}) = Uₙ  for n ≥ 2
    /// ```
    ///
    /// so rung 1 is seeded at `ω` and *not* at `U(U₀)` — the countermodel in
    /// [`crate::tower`] is why, and getting it wrong would make `⟦Type 0⟧` a
    /// set with no infinite member while `⟦N⟧` is infinite.
    ///
    /// `r`, `ut` and `lu` must be the ones this `Srt` was built over.
    /// Unconditional: the `n̄ ∈ ω` premises `at_succ` carries are discharged
    /// here by [`numeral_in_omega`], which needs no hypothesis.
    pub fn rung_eq(
        &self,
        env: &mut Env,
        r: &Rec,
        ut: &UTower,
        lu: FnSym,
        n: usize,
    ) -> Option<Thm> {
        if n == 0 {
            return Some(self.at_zero.clone())
        }
        let m = numeral(r, n - 1);
        let m_mem = numeral_in_omega(r, n - 1)?;
        // `⊢ srt(n̄) = U(app(lvl, (n-1)̄))`.
        let step = Thm::mp(&inst_all(&self.at_succ, std::slice::from_ref(&m))?, &m_mem)?;
        // `⊢ app(lvl, (n-1)̄) = ω` (n = 1) or `= U_{n-1}` (n ≥ 2).
        let below = ut.rung_eq(env, r, lu, n - 1)?;
        let (_, rhs_below) = below.concl().as_eq()?;
        let rhs_below = rhs_below.clone();
        let lm = ut.at(m);
        let ulm = Term::apply(lu, vec![lm.clone()]);
        let w = env.fresh_var();
        let congr = mpd_const(
            &Thm::eq_leibniz(
                lm,
                rhs_below,
                w,
                Formula::eq(ulm.clone(), Term::apply(lu, vec![Term::var(w)])),
            ),
            &Thm::eq_refl(ulm),
        )?;
        let u_eq = Thm::mp(&congr, &below)?;
        eq_trans(env, &step, &u_eq)
    }
}

/// Everything the derivations below share: the chain, the conditional, the
/// ladder, and the `U₀` term — bundled so each helper takes one context.
struct Cx<'a> {
    r: &'a Rec,
    i: &'a Ite0,
    ut: &'a UTower,
    u0: Term,
}

impl Cx<'_> {
    /// The term `srt(t)`.
    fn srt(&self, t: Term) -> Term { self.i.at(t.clone(), self.u0.clone(), self.ut.at(t)) }
}

/// Derive the sort ladder over the caller's chain.
///
/// `r`'s `∅`/`succ`/`ω`/`app` must be the ones `i` and `ut` were built over,
/// and `tower` the [`Tower`] whose `Apply` and `Peano` `r` was rebuilt from —
/// see the module header. Returns `None` on any symbol mismatch.
pub fn srt(env: &mut Env, r: &Rec, i: &Ite0, ut: &UTower, tower: &Tower) -> Option<Srt> {
    // The cheap identity guards; anything subtler fails a composition below.
    if i.empty != r.ap.empty || tower.sums.ap.empty != r.ap.empty {
        return None
    }
    if tower.omega() != r.omega() {
        return None
    }
    let probe = env.fresh_var();
    let tp = Term::var(probe);
    if ut.at(tp.clone()) != r.apply(ut.set.clone(), tp) {
        return None
    }

    let cx = Cx { r, i, ut, u0: tower.u0() };

    let at_zero = at_zero(&cx)?;
    let at_succ = at_succ(env, &cx)?;
    let sort_in_sort = sort_in_sort(env, &cx, &at_zero, &at_succ, &tower.u0_in, &tower.mem_u)?;
    let step_sub = step_sub(env, &cx, &at_succ, &sort_in_sort, &tower.transitive)?;
    let mono_mem = mono_mem(env, &cx, &step_sub)?;
    let omega_mem = omega_mem(env, &cx, &at_succ)?;
    let u0_mem = u0_mem(env, &cx, &at_succ, &tower.u0_in)?;
    let empty_mem = empty_mem(env, &cx, &at_zero, &step_sub, &tower.false_in_u0)?;
    let transitive = transitive(
        env,
        &cx,
        &at_zero,
        &at_succ,
        &tower.u0_subsingleton,
        &tower.false_in_u0,
        &tower.transitive,
    )?;

    let out = Srt {
        at_zero,
        at_succ,
        step_sub,
        sort_in_sort,
        mono_mem,
        omega_mem,
        u0_mem,
        empty_mem,
        transitive,
        ite0: i.sym,
        app: r.ap.app,
        lvl: ut.set.clone(),
        u0: cx.u0.clone(),
    };
    // `Srt::at` spells the term exactly as the derivations did.
    let probe2 = env.fresh_var();
    debug_assert_eq!(
        out.at(Term::var(probe2)),
        cx.srt(Term::var(probe2)),
        "srt: Srt::at does not rebuild the derivation's term"
    );
    Some(out)
}

/// `⊢ srt(∅) = U₀` — `when_zero` at `(∅, U₀, app(lvl,∅))`, its guard `∅ = ∅`
/// discharged by reflexivity.
fn at_zero(cx: &Cx) -> Option<Thm> {
    let zero = cx.r.zero();
    let wz = inst_all(&cx.i.when_zero, &[zero.clone(), cx.u0.clone(), cx.ut.at(zero.clone())])?;
    let out = Thm::mp(&wz, &Thm::eq_refl(zero.clone()))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(cx.srt(zero), cx.u0.clone()),
        "at_zero: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀n. (n ∈ ω → srt(succ n) = U(app(lvl, n)))`.
///
/// Under `n ∈ ω`: `succ_ne_zero` refutes the guard, so `when_nonzero` gives
/// `srt(succ n) = app(lvl, succ n)`, and [`UTower::step`] renames the right
/// side by one transitivity.
fn at_succ(env: &mut Env, cx: &Cx) -> Option<Thm> {
    let n = env.fresh_var();
    let tn = Term::var(n);
    let sn = cx.r.succ_of(tn.clone());
    let h = Formula::mem(tn.clone(), cx.r.omega());

    // `⊢ n ∈ ω → ¬(succ n = ∅)`, then the nonzero branch of the conditional.
    let h_ne = inst_all(&cx.r.peano.succ_ne_zero, std::slice::from_ref(&tn))?;
    let wn = inst_all(&cx.i.when_nonzero, &[sn.clone(), cx.u0.clone(), cx.ut.at(sn.clone())])?;
    let h_branch = syl(&h_ne, &wn)?;
    debug_assert_eq!(
        *h_branch.concl(),
        Formula::imp(h.clone(), Formula::eq(cx.srt(sn.clone()), cx.ut.at(sn.clone()))),
        "at_succ: the nonzero branch has an unexpected shape"
    );

    // `⊢ n ∈ ω → app(lvl, succ n) = U(app(lvl, n))`, and chain.
    let h_step = inst_all(&cx.ut.step, std::slice::from_ref(&tn))?;
    let body = hyp_eq_trans(env, &h_branch, &h_step)?;
    let (_, eq) = body.concl().as_imp()?;
    let (lhs, _) = eq.as_eq()?;
    debug_assert_eq!(lhs, cx.srt(sn), "at_succ: the left side drifted");
    Some(Thm::gen(n, &body))
}

/// `⊢ ∀n. (n ∈ ω → srt(n) ∈ srt(succ n))`, by induction on `n`.
///
/// Base: `U₀ ∈ U(ω)` ([`Tower::u0_in`] at `ω`), the left side rewritten to
/// `srt(∅)` along the reversed `at_zero` and the right to `srt(1̄)` along the
/// reversed `srt(1̄) = U(ω)` (the nonzero branch chained with
/// [`UTower::rung1_eq`]). Step: `x ∈ U(x)` at `app(lvl, succ n)`, both sides
/// read through the step and `at_succ` equations; the induction hypothesis is
/// never used.
fn sort_in_sort(
    env: &mut Env,
    cx: &Cx,
    at_zero: &Thm,
    at_succ: &Thm,
    u0_in: &Thm,
    mem_u: &Thm,
) -> Option<Thm> {
    let zero = cx.r.zero();
    let one = cx.r.succ_of(zero.clone());
    let omega = cx.r.omega();
    let nv = env.fresh_var();
    let tn = Term::var(nv);
    let sn = cx.r.succ_of(tn.clone());
    let h = Formula::mem(tn.clone(), omega.clone());
    let phi = Formula::mem(cx.srt(tn.clone()), cx.srt(sn.clone()));
    let w = env.fresh_var();

    // ── Base: `srt(∅) ∈ srt(succ ∅)` ─────────────────────────────────────────
    // `srt(1̄) = U(ω)`: the nonzero branch at `1̄`, chained with `rung1_eq`.
    let ne1 = Thm::mp(
        &inst_all(&cx.r.peano.succ_ne_zero, std::slice::from_ref(&zero))?,
        &cx.r.core().zero_mem,
    )?;
    let wn1 = inst_all(&cx.i.when_nonzero, &[one.clone(), cx.u0.clone(), cx.ut.at(one.clone())])?;
    let srt1_eq = eq_trans(env, &Thm::mp(&wn1, &ne1)?, &cx.ut.rung1_eq)?;
    let (srt1, uw) = srt1_eq.concl().as_eq()?;
    debug_assert_eq!(srt1, cx.srt(one.clone()), "sort_in_sort: srt(1̄) drifted");

    // `U₀ ∈ U(ω)`, then both sides carried to `srt`-terms.
    let u0_in_uw = inst_all(u0_in, std::slice::from_ref(&omega))?;
    debug_assert_eq!(
        *u0_in_uw.concl(),
        Formula::mem(cx.u0.clone(), uw.clone()),
        "sort_in_sort: u0_in at ω has an unexpected shape"
    );
    let srt0 = cx.srt(zero.clone());
    let sym0 = Thm::mp(&eq_symm_imp(env, srt0.clone(), cx.u0.clone()), at_zero)?;
    let leib_l = Thm::eq_leibniz(cx.u0.clone(), srt0.clone(), w, Formula::mem(Term::var(w), uw.clone()));
    let srt0_in_uw = Thm::mp(&Thm::mp(&leib_l, &sym0)?, &u0_in_uw)?;
    let sym1 = Thm::mp(&eq_symm_imp(env, srt1.clone(), uw.clone()), &srt1_eq)?;
    let leib_r = Thm::eq_leibniz(uw, srt1.clone(), w, Formula::mem(srt0.clone(), Term::var(w)));
    let base = Thm::mp(&Thm::mp(&leib_r, &sym1)?, &srt0_in_uw)?;
    debug_assert_eq!(*base.concl(), phi.subst(nv, &zero), "sort_in_sort: the base drifted");

    // ── Step, under `K := n ∈ ω ∧ φ(n)` (the IH conjunct goes unused) ────────
    let k = Formula::and(h.clone(), phi.clone());
    let k_h = and_left(h.clone(), phi.clone());
    let ssn = cx.r.succ_of(sn.clone());
    let k_sn = syl(&k_h, &inst_all(&cx.r.core().succ_closed, std::slice::from_ref(&tn))?)?;

    // The two `at_succ` equations and the step equation, all under `K`.
    let k_eq_n = syl(&k_h, &inst_all(at_succ, std::slice::from_ref(&tn))?)?;
    let k_eq_sn = syl(&k_sn, &inst_all(at_succ, std::slice::from_ref(&sn))?)?;
    let k_step = syl(&k_h, &inst_all(&cx.ut.step, std::slice::from_ref(&tn))?)?;
    let (_, eq_n) = k_eq_n.concl().as_imp()?;
    let (_, uln) = eq_n.as_eq()?;
    let (_, eq_sn) = k_eq_sn.concl().as_imp()?;
    let (_, ulsn) = eq_sn.as_eq()?;

    // `app(lvl, succ n) ∈ U(app(lvl, succ n))`, left side to `U(app(lvl,n))`
    // along the step equation.
    let lsn = cx.ut.at(sn.clone());
    let mem_at = inst_all(mem_u, std::slice::from_ref(&lsn))?;
    let leib1 = Thm::eq_leibniz(lsn, uln.clone(), w, Formula::mem(Term::var(w), ulsn.clone()));
    let k_un_ulsn = hyp_mp(&syl(&k_step, &leib1)?, &a1i(&mem_at, k.clone()))?;

    // Both sides along the reversed `at_succ` equations.
    let srt_sn = cx.srt(sn.clone());
    let srt_ssn = cx.srt(ssn);
    let k_sym_n = hyp_eq_symm(env, &k_eq_n)?;
    let leib2 = Thm::eq_leibniz(uln, srt_sn.clone(), w, Formula::mem(Term::var(w), ulsn.clone()));
    let k_srtsn_ulsn = hyp_mp(&syl(&k_sym_n, &leib2)?, &k_un_ulsn)?;
    let k_sym_sn = hyp_eq_symm(env, &k_eq_sn)?;
    let leib3 = Thm::eq_leibniz(ulsn, srt_ssn, w, Formula::mem(srt_sn, Term::var(w)));
    let k_goal = hyp_mp(&syl(&k_sym_sn, &leib3)?, &k_srtsn_ulsn)?;
    debug_assert_eq!(
        *k_goal.concl(),
        Formula::imp(k, phi.subst(nv, &sn)),
        "sort_in_sort: the step drifted"
    );

    let scheme = induction_scheme(env, cx.r.core(), nv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(nv, &k_goal)))
}

/// `⊢ ∀k. (k ∈ ω → srt(k) ⊆ srt(succ k))`.
///
/// `srt(k) ∈ srt(succ k)` with the right side read as `U(app(lvl,k))` along
/// `at_succ`; `C₁`-transitivity of `U(·)` turns the membership into
/// `srt(k) ⊆ U(app(lvl,k))`, and the reversed `at_succ` renames the bound.
fn step_sub(
    env: &mut Env,
    cx: &Cx,
    at_succ: &Thm,
    sort_in_sort: &Thm,
    transitive: &Thm,
) -> Option<Thm> {
    let kv = env.fresh_var();
    let tk = Term::var(kv);
    let sk = cx.r.succ_of(tk.clone());
    let h = Formula::mem(tk.clone(), cx.r.omega());
    let srt_k = cx.srt(tk.clone());
    let srt_sk = cx.srt(sk);

    let h_in = inst_all(sort_in_sort, std::slice::from_ref(&tk))?;
    let h_eq = inst_all(at_succ, std::slice::from_ref(&tk))?;
    let (_, eqf) = h_eq.concl().as_imp()?;
    let (_, ulk) = eqf.as_eq()?;

    // `srt(k) ∈ U(app(lvl,k))`, along the `at_succ` equation.
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(srt_sk.clone(), ulk.clone(), w, Formula::mem(srt_k.clone(), Term::var(w)));
    let h_mem_u = hyp_mp(&syl(&h_eq, &leib)?, &h_in)?;

    // `C₁` at `(app(lvl,k), srt(k))`: the membership becomes a subset.
    let tr_at = inst_all(transitive, &[cx.ut.at(tk.clone()), srt_k.clone()])?;
    let h_sub_u = hyp_mp(&a1i(&tr_at, h.clone()), &h_mem_u)?;
    debug_assert_eq!(
        *h_sub_u.concl(),
        {
            let sub = kernel::thm::subset(env, srt_k.clone(), ulk.clone());
            Formula::imp(h.clone(), sub)
        },
        "step_sub: C₁ did not produce the kernel's subset spelling"
    );

    // Rename the bound back to `srt(succ k)` along the reversed equation.
    let h_sym = hyp_eq_symm(env, &h_eq)?;
    let hole = env.fresh_var();
    let sub_hole = kernel::thm::subset(env, srt_k.clone(), Term::var(hole));
    let leib2 = Thm::eq_leibniz(ulk, srt_sk.clone(), hole, sub_hole);
    let body = hyp_mp(&syl(&h_sym, &leib2)?, &h_sub_u)?;
    debug_assert_eq!(
        *body.concl(),
        {
            let sub = kernel::thm::subset(env, srt_k, srt_sk);
            Formula::imp(h, sub)
        },
        "step_sub: unexpected shape"
    );
    Some(Thm::gen(kv, &body))
}

/// `⊢ ∀n. (n ∈ ω → ∀m. (m ∈ n → srt(m) ⊆ srt(n)))`, by induction on `n`.
///
/// Base: `m ∈ ∅` is refuted outright. Step at `succ n`: `m ∈ succ n` splits
/// into `m ∈ n` — the induction hypothesis plus [`step_sub`], closed by
/// [`crate::cumul::subset_trans`] — and `m = n`, where [`step_sub`] is the
/// statement itself up to one Leibniz rewrite.
fn mono_mem(env: &mut Env, cx: &Cx, step_sub: &Thm) -> Option<Thm> {
    let sub_tr = crate::cumul::subset_trans(env)?;
    let zero = cx.r.zero();
    let omega = cx.r.omega();
    let nv = env.fresh_var();
    let tn = Term::var(nv);
    let mv = env.fresh_var();
    let tm = Term::var(mv);
    let sn = cx.r.succ_of(tn.clone());
    let h = Formula::mem(tn.clone(), omega);

    let mem_mn = Formula::mem(tm.clone(), tn.clone());
    let sub_mn = kernel::thm::subset(env, cx.srt(tm.clone()), cx.srt(tn.clone()));
    let phi = Formula::forall(mv, Formula::imp(mem_mn.clone(), sub_mn));

    // ── Base: nothing is a member of `∅` ─────────────────────────────────────
    let not_in = inst_all(&cx.r.core().empty_ax, std::slice::from_ref(&tm))?;
    let sub_m0 = kernel::thm::subset(env, cx.srt(tm.clone()), cx.srt(zero.clone()));
    let base = Thm::gen(mv, &syl(&not_in, &ex_falso(sub_m0))?);
    debug_assert_eq!(*base.concl(), phi.subst(nv, &zero), "mono_mem: the base drifted");

    // ── Step, under `K := n ∈ ω ∧ φ(n)`, then `L := K ∧ m ∈ succ n` ──────────
    let k = Formula::and(h.clone(), phi.clone());
    let k_h = and_left(h.clone(), phi.clone());
    let k_phi = and_right(h.clone(), phi.clone());

    let msk = Formula::mem(tm.clone(), sn.clone());
    let sub_msn = kernel::thm::subset(env, cx.srt(tm.clone()), cx.srt(sn.clone()));
    let l = Formula::and(k.clone(), msk.clone());
    let l_k = and_left(k.clone(), msk.clone());
    let l_msk = and_right(k.clone(), msk.clone());

    // Shared tail: `L → srt(n) ⊆ srt(succ n)`, by [`step_sub`].
    let l_step_sub = syl(&syl(&l_k, &k_h)?, &inst_all(step_sub, std::slice::from_ref(&tn))?)?;

    // The successor membership condition splits `m ∈ succ n`.
    let succ_at = inst_all(&cx.r.core().succ_ax, &[tn.clone(), tm.clone()])?;
    let l_disj = syl(&l_msk, &iff_mp(&succ_at)?)?;

    // Case `m ∈ n`: IH gives `srt(m) ⊆ srt(n)`; transitivity closes it.
    let m1_l = and_left(l.clone(), mem_mn.clone());
    let m1_mn = and_right(l.clone(), mem_mn.clone());
    let m1_phi = syl(&m1_l, &syl(&l_k, &k_phi)?)?;
    let m1_ih = hyp_mp(&syl(&m1_phi, &Thm::ax_inst(phi.clone(), tm.clone())?)?, &m1_mn)?;
    let m1_pair = hyp_and(&m1_ih, &syl(&m1_l, &l_step_sub)?)?;
    let tr_at = inst_all(&sub_tr, &[cx.srt(tm.clone()), cx.srt(tn.clone()), cx.srt(sn.clone())])?;
    let case_mem = uncurry(&syl(&m1_pair, &tr_at)?)?;

    // Case `m = n`: [`step_sub`] with `n` rewritten to `m` on the left.
    let eq_mn = Formula::eq(tm.clone(), tn.clone());
    let m2 = Formula::and(l.clone(), eq_mn.clone());
    let m2_l = and_left(l.clone(), eq_mn.clone());
    let m2_nm = syl(&and_right(l.clone(), eq_mn), &eq_symm_imp(env, tm.clone(), tn.clone()))?;
    let hole = env.fresh_var();
    let sub_hole = kernel::thm::subset(env, cx.srt(Term::var(hole)), cx.srt(sn.clone()));
    let leib = Thm::eq_leibniz(tn.clone(), tm.clone(), hole, sub_hole);
    let m2_imp = hyp_mp(&a1i(&leib, m2), &m2_nm)?;
    let case_eq = uncurry(&hyp_mp(&m2_imp, &syl(&m2_l, &l_step_sub)?)?)?;

    let l_goal = hyp_or_elim(&l_disj, &case_mem, &case_eq)?;
    debug_assert_eq!(
        *l_goal.concl(),
        Formula::imp(l, sub_msn.clone()),
        "mono_mem: the case split drifted"
    );
    let k_imp = uncurry(&l_goal)?;
    let k_all = Thm::mp(
        &Thm::ax_dist(mv, k.clone(), Formula::imp(msk, sub_msn))?,
        &Thm::gen(mv, &k_imp),
    )?;
    debug_assert_eq!(
        *k_all.concl(),
        Formula::imp(k, phi.subst(nv, &sn)),
        "mono_mem: the step drifted"
    );

    let scheme = induction_scheme(env, cx.r.core(), nv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(nv, &k_all)))
}

/// `⊢ ∀n. (n ∈ ω → ω ∈ srt(succ n))`.
///
/// [`UTower::omega_mem`] gives `ω ∈ app(lvl, succ n)`; chaining the step
/// equation with the reversed `at_succ` gives `app(lvl, succ n) = srt(succ n)`,
/// and one Leibniz instance carries the membership across.
fn omega_mem(env: &mut Env, cx: &Cx, at_succ: &Thm) -> Option<Thm> {
    let n = env.fresh_var();
    let tn = Term::var(n);
    let sn = cx.r.succ_of(tn.clone());
    let h = Formula::mem(tn.clone(), cx.r.omega());
    let omega = cx.r.omega();
    let lsn = cx.ut.at(sn.clone());
    let srt_sn = cx.srt(sn.clone());

    let h_om = inst_all(&cx.ut.omega_mem, std::slice::from_ref(&tn))?;
    let h_step = inst_all(&cx.ut.step, std::slice::from_ref(&tn))?;
    let h_eq = inst_all(at_succ, std::slice::from_ref(&tn))?;
    // `app(lvl, succ n) = U(app(lvl,n)) = srt(succ n)`, under the hypothesis.
    let h_eq_rev = hyp_eq_symm(env, &h_eq)?;
    let h_chain = hyp_eq_trans(env, &h_step, &h_eq_rev)?;

    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(lsn, srt_sn.clone(), w, Formula::mem(omega.clone(), Term::var(w)));
    let body = hyp_mp(&syl(&h_chain, &leib)?, &h_om)?;
    debug_assert_eq!(
        *body.concl(),
        Formula::imp(h, Formula::mem(omega, srt_sn)),
        "omega_mem: unexpected shape"
    );
    Some(Thm::gen(n, &body))
}

/// `⊢ ∀n. (n ∈ ω → U₀ ∈ srt(succ n))`.
///
/// [`Tower::u0_in`] at `c := app(lvl, n)`, the universe renamed to
/// `srt(succ n)` along the reversed `at_succ`.
fn u0_mem(env: &mut Env, cx: &Cx, at_succ: &Thm, u0_in: &Thm) -> Option<Thm> {
    let n = env.fresh_var();
    let tn = Term::var(n);
    let sn = cx.r.succ_of(tn.clone());
    let h = Formula::mem(tn.clone(), cx.r.omega());
    let srt_sn = cx.srt(sn);

    let h_eq = inst_all(at_succ, std::slice::from_ref(&tn))?;
    let (_, eqf) = h_eq.concl().as_imp()?;
    let (_, uln) = eqf.as_eq()?;

    let at_ln = inst_all(u0_in, std::slice::from_ref(&cx.ut.at(tn.clone())))?;
    debug_assert_eq!(
        *at_ln.concl(),
        Formula::mem(cx.u0.clone(), uln.clone()),
        "u0_mem: u0_in did not land on at_succ's universe term"
    );

    let h_sym = hyp_eq_symm(env, &h_eq)?;
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(uln, srt_sn.clone(), w, Formula::mem(cx.u0.clone(), Term::var(w)));
    let body = hyp_mp(&syl(&h_sym, &leib)?, &a1i(&at_ln, h.clone()))?;
    debug_assert_eq!(
        *body.concl(),
        Formula::imp(h, Formula::mem(cx.u0.clone(), srt_sn)),
        "u0_mem: unexpected shape"
    );
    Some(Thm::gen(n, &body))
}

/// `⊢ ∀n. (n ∈ ω → ∅ ∈ srt(n))`, by induction on `n`.
///
/// Base: `srt(∅)` is `U₀ = {0,1}` and `0` **is** `∅` (`crate::sums` — the
/// point, falsity and the empty set are one term), so [`Tower::false_in_u0`]
/// transported along the reversed [`at_zero`] is the whole of it. Step:
/// [`step_sub`] instantiated at `∅` and applied to the induction hypothesis —
/// the ladder only grows, so a member stays one. This is the *one* fact of the
/// pair whose induction hypothesis does real work.
fn empty_mem(
    env: &mut Env,
    cx: &Cx,
    at_zero: &Thm,
    step_sub: &Thm,
    false_in_u0: &Thm,
) -> Option<Thm> {
    let zero = cx.r.zero();
    let nv = env.fresh_var();
    let tn = Term::var(nv);
    let sn = cx.r.succ_of(tn.clone());
    let h = Formula::mem(tn.clone(), cx.r.omega());
    let phi = Formula::mem(zero.clone(), cx.srt(tn.clone()));

    // ── Base: `∅ ∈ U₀`, read at `srt(∅)` ─────────────────────────────────────
    let srt0 = cx.srt(zero.clone());
    debug_assert_eq!(
        *false_in_u0.concl(),
        Formula::mem(zero.clone(), cx.u0.clone()),
        "empty_mem: `⊢ 0 ∈ U₀` is not about this `∅` and this `U₀`"
    );
    let w = env.fresh_var();
    let sym0 = Thm::mp(&eq_symm_imp(env, srt0.clone(), cx.u0.clone()), at_zero)?;
    let leib =
        Thm::eq_leibniz(cx.u0.clone(), srt0, w, Formula::mem(zero.clone(), Term::var(w)));
    let base = Thm::mp(&Thm::mp(&leib, &sym0)?, false_in_u0)?;
    debug_assert_eq!(*base.concl(), phi.subst(nv, &zero), "empty_mem: the base drifted");

    // ── Step, under `K := n ∈ ω ∧ φ(n)` ──────────────────────────────────────
    let k = Formula::and(h.clone(), phi.clone());
    let k_h = and_left(h.clone(), phi.clone());
    let k_phi = and_right(h.clone(), phi.clone());
    let k_sub = syl(&k_h, &inst_all(step_sub, std::slice::from_ref(&tn))?)?;
    // `srt(n) ⊆ srt(succ n)` is `∀z. (z ∈ srt(n) → z ∈ srt(succ n))`; take `z`
    // to be `∅` and the induction hypothesis is the antecedent.
    let sub = kernel::thm::subset(env, cx.srt(tn.clone()), cx.srt(sn.clone()));
    let at_zero_inst = Thm::ax_inst(sub, zero.clone())?;
    let k_goal = hyp_mp(&syl(&k_sub, &at_zero_inst)?, &k_phi)?;
    debug_assert_eq!(
        *k_goal.concl(),
        Formula::imp(k, phi.subst(nv, &sn)),
        "empty_mem: the step drifted"
    );

    let scheme = induction_scheme(env, cx.r.core(), nv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(nv, &k_goal)))
}

/// `⊢ ∀n. (n ∈ ω → ∀y. (y ∈ srt(n) → ∀z. (z ∈ y → z ∈ srt(n))))`, by induction
/// on `n`. **The induction hypothesis is never used** — see [`sort_in_sort`],
/// which has the same shape and the same reason: the induction is being spent
/// on the case analysis and on nothing else.
///
/// Base: `U₀ = {0,1}` is transitive, and that is proof irrelevance read
/// sideways. [`Tower::u0_subsingleton`] says every member of every member of
/// `{0,1}` is `•`; `•` is `∅` is `0`, and `0 ∈ {0,1}`. Step: `srt(succ n)` is
/// the universe `U(app(lvl,n))` by [`at_succ`], and [`Tower::transitive`] is
/// stated at every `U(·)` at once, so the whole statement transports along the
/// reversed equation in one Leibniz step — the hole occurs twice in it and
/// [`Thm::eq_leibniz`] rewrites both.
fn transitive(
    env: &mut Env,
    cx: &Cx,
    at_zero: &Thm,
    at_succ: &Thm,
    u0_subsingleton: &Thm,
    false_in_u0: &Thm,
    tower_transitive: &Thm,
) -> Option<Thm> {
    let zero = cx.r.zero();
    let nv = env.fresh_var();
    let tn = Term::var(nv);
    let sn = cx.r.succ_of(tn.clone());
    let h = Formula::mem(tn.clone(), cx.r.omega());
    let (yv, zv) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(yv), Term::var(zv));

    // `C₁(s)` — "`s` is transitive" — as a formula of the set, so that the two
    // transports below are each a single Leibniz step.
    let c1 = |s: &Term| {
        Formula::forall(
            yv,
            Formula::imp(
                Formula::mem(ty.clone(), s.clone()),
                Formula::forall(
                    zv,
                    Formula::imp(
                        Formula::mem(tz.clone(), ty.clone()),
                        Formula::mem(tz.clone(), s.clone()),
                    ),
                ),
            ),
        )
    };
    let phi = c1(&cx.srt(tn.clone()));
    let w = env.fresh_var();

    // ── Base: `C₁(U₀)`, then read at `srt(∅)` ────────────────────────────────
    let hy = Formula::mem(ty.clone(), cx.u0.clone());
    let hz = Formula::mem(tz.clone(), ty.clone());
    let goal = Formula::mem(tz.clone(), cx.u0.clone());
    // `(y ∈ U₀ ∧ z ∈ y) → z = •`, and `•` is `∅`.
    let irrel = inst_all(u0_subsingleton, &[ty.clone(), tz.clone()])?;
    debug_assert_eq!(
        *irrel.concl(),
        Formula::imp(Formula::and(hy.clone(), hz.clone()), Formula::eq(tz.clone(), zero.clone())),
        "transitive: proof irrelevance does not name this `•`"
    );
    // `z = ∅ → z ∈ U₀`, from `∅ ∈ U₀` by Leibniz in the reverse direction.
    let carry = mpd_const(
        &Thm::eq_leibniz(zero.clone(), tz.clone(), w, Formula::mem(Term::var(w), cx.u0.clone())),
        false_in_u0,
    )?;
    let z_in_u0 = syl(&eq_symm_imp(env, tz.clone(), zero.clone()), &carry)?;
    let and_imp = syl(&irrel, &z_in_u0)?;
    // Curry: `(hy ∧ hz) → goal` back to `hy → (hz → goal)`.
    let inner = syl(
        &and_intro_imp(hy.clone(), hz.clone()),
        &imp_mono_r(&and_imp, hz.clone())?,
    )?;
    let quantified =
        Thm::mp(&Thm::ax_dist(zv, hy.clone(), Formula::imp(hz, goal))?, &Thm::gen(zv, &inner))?;
    let u0_c1 = Thm::gen(yv, &quantified);
    debug_assert_eq!(*u0_c1.concl(), c1(&cx.u0), "transitive: `C₁(U₀)` has the wrong shape");

    let srt0 = cx.srt(zero.clone());
    let sym0 = Thm::mp(&eq_symm_imp(env, srt0.clone(), cx.u0.clone()), at_zero)?;
    let leib0 = Thm::eq_leibniz(cx.u0.clone(), srt0, w, c1(&Term::var(w)));
    let base = Thm::mp(&Thm::mp(&leib0, &sym0)?, &u0_c1)?;
    debug_assert_eq!(*base.concl(), phi.subst(nv, &zero), "transitive: the base drifted");

    // ── Step, under `K := n ∈ ω ∧ φ(n)` (the IH conjunct goes unused) ────────
    let k = Formula::and(h.clone(), phi.clone());
    let k_h = and_left(h.clone(), phi.clone());
    let k_eq = syl(&k_h, &inst_all(at_succ, std::slice::from_ref(&tn))?)?;
    let (_, eqf) = k_eq.concl().as_imp()?;
    let (_, uln) = eqf.as_eq()?;
    let uln = uln.clone();

    let at_ln = inst_all(tower_transitive, std::slice::from_ref(&cx.ut.at(tn.clone())))?;
    debug_assert_eq!(
        *at_ln.concl(),
        c1(&uln),
        "transitive: the tower's C₁ did not land on at_succ's universe term"
    );

    let srt_sn = cx.srt(sn.clone());
    let k_sym = hyp_eq_symm(env, &k_eq)?;
    let leib1 = Thm::eq_leibniz(uln, srt_sn, w, c1(&Term::var(w)));
    let k_goal = hyp_mp(&syl(&k_sym, &leib1)?, &a1i(&at_ln, k.clone()))?;
    debug_assert_eq!(
        *k_goal.concl(),
        Formula::imp(k, phi.subst(nv, &sn)),
        "transitive: the step drifted"
    );

    let scheme = induction_scheme(env, cx.r.core(), nv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(nv, &k_goal)))
}
