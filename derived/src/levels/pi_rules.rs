//! **Dependent Π-formation at a variable level** — the `dprod` twin of
//! [`crate::levels::rules::Rules::pi_imax`], with the Prop/Type split as the
//! same `ite0` inside the target term (`LEVELPOLY.md` §1.4, §6's "dependent
//! `dprod` form", derived here).
//!
//! # Interface
//!
//! For a fibre family symbol `b` of arity `k+1` packaged as a
//! [`crate::ext::DProdN`], writing `srt(t)` for
//! [`crate::levels::srt::Srt::at`]'s term, `imax(u,v) := ite0(v, ∅, u ∪ v)`
//! with `∪` the crate's binary union ([`crate::levels::order::Order::max`]),
//! `dprod(q⃗,A)` for the dependent product `Π(x:A). b(q⃗,x)`,
//! `fib(q⃗,A,s) := ∀x. (x ∈ A → b(q⃗,x) ∈ s)` spelled exactly as
//! [`crate::universe::fibres_in_n`] (so the `Π` rule composes without
//! reshaping), and `cndd` a fresh `(k+1)`-ary conditional-singleton symbol
//! (below), the export is
//!
//! ```text
//! ⊢ ∀q⃗ ∀u ∀v ∀A. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧ fib(q⃗,A,srt(v))))
//!       → ite0(v, cndd(q⃗,A), dprod(q⃗,A)) ∈ srt(imax(u,v)))    [PiRules::pi_imax_dep]
//! ```
//!
//! unconditional, the antecedent associated exactly as shown. This is Lean's
//! **dependent** Π-formation `α : Sort u, β : α → Sort v ⊢ (Π x:α. β x) :
//! Sort (imax u v)` as one theorem over variable levels: at `v = 0` the type
//! is the proposition `∀x ∈ A. • ∈ b(q⃗,x)` — reified as the conditional
//! singleton `cndd(q⃗,A)` ([`crate::prop::conditional_singleton`] at
//! `φ(q⃗,A) := ∀x. (x ∈ A → • ∈ b(q⃗,x))`, params `[q⃗, A]`, `•` the point `∅`)
//! — landing in `srt(0) = U₀`; at `v ≠ 0` it is the genuine dependent product
//! `dprod(q⃗,A)` landing in `srt(u ∪ v)`. [`PiRules::cndd`] and its
//! characteristic theorem [`PiRules::cndd_ax`],
//! `⊢ ∀q⃗ ∀A ∀z. (z ∈ cndd(q⃗,A) ↔ (z ∈ 1 ∧ φ(q⃗,A)))`, are exported so a
//! consumer (and the integration test) can spell the term and compute with
//! it.
//!
//! # Why this is assembly, not new mathematics
//!
//! [`crate::ext::dprod_in_universe_pair_n`] already states the Type clause at
//! a **quantified universe seed**:
//! `⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ fib(q⃗,A,U(c))) → dprod(q⃗,A) ∈ U(c))`. The
//! variable-rung instance is `c := app(lvl,q)` for the successor witness `q`
//! of `u ∪ v` — exactly where [`crate::levels::rules`]'s flagship instantiates
//! [`crate::tower::Tower::funspace`]. What is new here relative to the
//! flagship is one move: the fibres conjunct must be **raised pointwise under
//! its binder** from `srt(v)` to `srt(u∪v)` before the `Π` rule can fire, and
//! that is a fresh-witness `syl` chain closed by [`crate::prim::gen`] — the
//! same freshness discipline the flagship's successor witness uses.
//!
//! # Derivation route
//!
//! Mirrors [`crate::levels::rules`]'s `pi_imax` case split exactly
//! (hypotheses only through [`crate::discharge`], boundary rule I1). Case
//! `v = ∅`: both `ite0`s compute by `when_zero`,
//! `srt(imax(u,v)) = srt(∅) = U₀`, and `cndd(q⃗,A) ∈ U₀` is
//! [`crate::tower::Tower::cond_in_u0`] — no antecedent conjunct needed. Case
//! `¬(v = ∅)`: both `ite0`s compute by `when_nonzero`; `u ∪ v ≠ ∅` and the
//! successor witness `u ∪ v = succ q` exactly as in the flagship
//! (`zero_least`, `max_ub`, `cases`, `max_in_omega`);
//! `srt(u∪v) = U(app(lvl,q))` by `at_succ`; the base is raised by
//! [`crate::levels::rules::Rules::mono_sub`] over `max_ub`, the fibres by the
//! pointwise chain above; then `dprod_in_universe_pair_n` at
//! `c := app(lvl,q)` finishes and the equations ride back.
//!
//! # Symbol identity
//!
//! As in [`crate::levels::rules`]: the cheap identities are guarded in the
//! constructor — the shared `∅`/`ω`, the `srt` spelling, `at_succ` landing on
//! the tower's `U(·)` over `ut`'s ladder — and `pair` (the caller's
//! [`crate::ext::dprod_in_universe_pair_n`] output for this `dp`) is
//! **validated by probe**: instantiated at fresh variables and compared
//! against the rule's statement rebuilt from `dp.b`, `dp.dprod` and the
//! tower's `U(·)`. A stack over a different fibre, product or universe
//! operator is refused rather than silently described.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::discharge::under;
use crate::ext::DProdN;
use crate::levels::ite0::Ite0;
use crate::levels::order::Order;
use crate::levels::rules::Rules;
use crate::levels::srt::Srt;
use crate::levels::utower::UTower;
use crate::prop::conditional_singleton;
use crate::recursion::Rec;
use crate::sums::Sums;
use crate::tower::Tower;
use crate::universe::fibres_in_n;
use crate::{
    and_intro, and_left, and_right, clavius, com12, contrapos, eq_symm, eq_symm_imp, eq_trans,
    exists_elim_imp, gen_all, inst_all, notnot_elim, syl,
};

/// The dependent rule kit at a variable level. See the module header.
pub struct PiRules {
    /// The Prop-clause dependent-Π symbol:
    /// `cndd(q⃗,A) = { z ∈ 1 : ∀x. (x ∈ A → • ∈ b(q⃗,x)) }`.
    pub cndd: FnSym,
    /// `⊢ ∀q⃗ ∀A ∀z. (z ∈ cndd(q⃗,A) ↔ (z ∈ 1 ∧ ∀x. (x ∈ A → • ∈ b(q⃗,x))))`.
    pub cndd_ax: Thm,
    /// `⊢ ∀q⃗ ∀u ∀v ∀A. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧ fib(q⃗,A,srt(v))))
    /// → ite0(v, cndd(q⃗,A), dprod(q⃗,A)) ∈ srt(imax(u,v)))` — **dependent
    /// Π-formation at `imax`, both clauses in one theorem**.
    pub pi_imax_dep: Thm,
}

/// Everything the derivation shares, bundled so each helper takes one context.
struct Cx<'a> {
    r: &'a Rec,
    i: &'a Ite0,
    ord: &'a Order,
    ut: &'a UTower,
    s: &'a Srt,
    tower: &'a Tower,
    dp: &'a DProdN,
}

/// Derive the dependent kit over the caller's chain.
///
/// `r`'s `∅`/`succ`/`ω`/`app` must be the ones `i`, `ord`, `ut` and `s` were
/// built over, `tower` the [`Tower`] whose `Apply` and `Peano` `r` was rebuilt
/// from, `ru` the [`Rules`] kit over the same chain (its `mono_sub` is
/// consumed), `dp` a [`DProdN`] over `tower`'s own `Apply`/`Funspace`, and
/// `pair` the [`crate::ext::dprod_in_universe_pair_n`] theorem for exactly
/// that stack. Returns `None` on any mismatch.
#[allow(clippy::too_many_arguments)] // the whole chain, as `recarg` and `cantor::image` take it
pub fn pi_rules(
    env: &mut Env,
    r: &Rec,
    i: &Ite0,
    ord: &Order,
    ut: &UTower,
    s: &Srt,
    ru: &Rules,
    tower: &Tower,
    dp: &DProdN,
    pair: &Thm,
) -> Option<PiRules> {
    // The cheap identity guards, as in `rules`; anything subtler fails a
    // composition below or the probe check.
    if i.empty != r.ap.empty || tower.sums.ap.empty != r.ap.empty {
        return None
    }
    if tower.omega() != r.omega() {
        return None
    }
    if ord.sets.up != r.ap.sets.up || ord.sets.un != r.ap.sets.un {
        return None
    }
    let probe = env.fresh_var();
    let tp = Term::var(probe);
    if s.at(tp.clone()) != i.at(tp.clone(), tower.u0(), ut.at(tp.clone())) {
        return None
    }
    let at_succ_want = Formula::imp(
        Formula::mem(tp.clone(), r.omega()),
        Formula::eq(
            s.at(r.succ_of(tp.clone())),
            Term::apply(tower.space.lu, vec![ut.at(tp.clone())]),
        ),
    );
    if *inst_all(&s.at_succ, std::slice::from_ref(&tp))?.concl() != at_succ_want {
        return None
    }
    debug_assert_eq!(tower.sums.point(), r.zero(), "pi_rules: the point is not the chain's ∅");

    // `pair` validated by probe: `∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ fib(q⃗,A,U(c)))
    // → dprod(q⃗,A) ∈ U(c))`, rebuilt at fresh variables and compared.
    {
        let k = dp.k;
        let qs: Vec<_> = (0..k).map(|_| env.fresh_var()).collect();
        let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
        let (cv, av) = (env.fresh_var(), env.fresh_var());
        let (tc, ta) = (Term::var(cv), Term::var(av));
        let w = Term::apply(tower.space.lu, vec![tc]);
        let fib = fibres_in_n(env, dp.b, &qts, &ta, &w);
        let want = Formula::imp(
            Formula::and(Formula::mem(ta.clone(), w.clone()), fib),
            Formula::mem(dp.of(&qts, ta), w),
        );
        let mut args = qts;
        args.push(Term::var(cv));
        args.push(Term::var(av));
        if *inst_all(pair, &args)?.concl() != want {
            return None
        }
    }

    let cx = Cx { r, i, ord, ut, s, tower, dp };

    // The Prop-clause symbol: one conditional singleton over params [q⃗, A].
    let qs: Vec<_> = (0..dp.k).map(|_| env.fresh_var()).collect();
    let av = env.fresh_var();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let phi = pi_body_dep(env, &tower.sums, dp.b, &qts, &Term::var(av));
    let mut params = qs;
    params.push(av);
    let (cndd, cndd_ax) = conditional_singleton(env, &tower.sums, &params, &phi)?;

    let pi_imax_dep = pi_imax_dep(env, &cx, &ru.mono_sub, cndd, &cndd_ax, pair)?;

    Some(PiRules { cndd, cndd_ax, pi_imax_dep })
}

/// The Prop-clause dependent-Π body `φ(q⃗,A) := ∀x. (x ∈ A → • ∈ b(q⃗,x))`,
/// with `•` the point `∅` — the uniform-typing reading of `∀x:α. β x` at
/// sort 0 (`LEVELPOLY.md` §1.4).
fn pi_body_dep(env: &mut Env, sums: &Sums, b: FnSym, qts: &[Term], a: &Term) -> Formula {
    let x = env.fresh_var();
    let mut args = qts.to_vec();
    args.push(Term::var(x));
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(Term::var(x), a.clone()),
            Formula::mem(sums.point(), Term::apply(b, args)),
        ),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Sequent-style building blocks — the same four one-liners `rules` keeps
// privately, duplicated here under the one-construction-per-file rule.
// ─────────────────────────────────────────────────────────────────────────────

/// From `Γ ⊢ a = b` and `Δ ⊢ x ∈ a` infer `Γ ∪ Δ ⊢ x ∈ b`.
fn mem_set_rw(env: &mut Env, eq: &Thm, mem: &Thm) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let (x, a2) = mem.concl().as_mem()?;
    if a2 != a {
        return None
    }
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(a, b, w, Formula::mem(x, Term::var(w)));
    Thm::mp(&Thm::mp(&leib, eq)?, mem)
}

/// From `Γ ⊢ a = b` and `Δ ⊢ a ∈ y` infer `Γ ∪ Δ ⊢ b ∈ y`.
fn mem_elt_rw(env: &mut Env, eq: &Thm, mem: &Thm) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let (a2, y) = mem.concl().as_mem()?;
    if a2 != a {
        return None
    }
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(a, b, w, Formula::mem(Term::var(w), y));
    Thm::mp(&Thm::mp(&leib, eq)?, mem)
}

/// From `Γ ⊢ a = b` infer `Γ ⊢ srt(a) = srt(b)`.
fn srt_congr(env: &mut Env, s: &Srt, eq: &Thm) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let w = env.fresh_var();
    let phi = Formula::eq(s.at(a.clone()), s.at(Term::var(w)));
    let leib = Thm::eq_leibniz(a.clone(), b, w, phi);
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(s.at(a)))
}

// ─────────────────────────────────────────────────────────────────────────────
// The export.
// ─────────────────────────────────────────────────────────────────────────────

/// The dependent flagship. Classical cases on the guard `v = ∅`; see the
/// module header for the route.
fn pi_imax_dep(
    env: &mut Env,
    cx: &Cx,
    mono_sub: &Thm,
    cndd: FnSym,
    cndd_ax: &Thm,
    pair: &Thm,
) -> Option<Thm> {
    let k = cx.dp.k;
    let qs: Vec<_> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (uv, vv, av) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tv, ta) = (Term::var(uv), Term::var(vv), Term::var(av));
    let omega = cx.r.omega();
    let zero = cx.r.zero();

    let u_om = Formula::mem(tu.clone(), omega.clone());
    let v_om = Formula::mem(tv.clone(), omega.clone());
    let a_in = Formula::mem(ta.clone(), cx.s.at(tu.clone()));
    let fib_v = fibres_in_n(env, cx.dp.b, &qts, &ta, &cx.s.at(tv.clone()));
    let k12 = Formula::and(u_om.clone(), v_om.clone());
    let k34 = Formula::and(a_in.clone(), fib_v.clone());
    let kk = Formula::and(k12.clone(), k34.clone());

    let mut cndd_args = qts.clone();
    cndd_args.push(ta.clone());
    let cndd_qa = Term::apply(cndd, cndd_args.clone());
    let dp_t = cx.dp.of(&qts, ta.clone());
    let ite_t = cx.i.at(tv.clone(), cndd_qa.clone(), dp_t.clone());
    let bu = cx.ord.max(tu.clone(), tv.clone());
    let imax_t = cx.i.at(tv.clone(), zero.clone(), bu.clone());
    let goal = Formula::mem(ite_t, cx.s.at(imax_t.clone()));

    let p = Formula::eq(tv.clone(), zero.clone());
    let np = Formula::not(p.clone());
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let q_om = Formula::mem(tq.clone(), omega.clone());
    let bu_eq = Formula::eq(bu.clone(), cx.r.succ_of(tq.clone()));
    let e_body = Formula::and(q_om.clone(), bu_eq.clone());

    // ── Case `v = ∅`: the Prop clause. Needs none of the antecedents. ────────
    let case_z = under(p.clone(), |hp| {
        let wz_goal = Thm::mp(
            &inst_all(&cx.i.when_zero, &[tv.clone(), cndd_qa.clone(), dp_t.clone()])?,
            hp,
        )?;
        let wz_imax =
            Thm::mp(&inst_all(&cx.i.when_zero, &[tv.clone(), zero.clone(), bu.clone()])?, hp)?;
        let srt_imax_zero = srt_congr(env, cx.s, &wz_imax)?;
        let srt_eq = eq_trans(env, &srt_imax_zero, &cx.s.at_zero)?;
        // `cndd(q⃗,A) ∈ U₀`, unconditionally: a conditional singleton is a
        // truth value whatever φ(q⃗,A) turns out to be.
        let phi_qa = pi_body_dep(env, &cx.tower.sums, cx.dp.b, &qts, &ta);
        let chi = inst_all(cndd_ax, &cndd_args)?;
        let cndd_u0 = cx.tower.cond_in_u0(env, &phi_qa, &cndd_qa, &chi)?;
        debug_assert!(cndd_u0.hyps().is_empty(), "pi_imax_dep: cond_in_u0 assumed something");
        let srt_eq_rev = eq_symm(env, &srt_eq)?;
        let cndd_srt = mem_set_rw(env, &srt_eq_rev, &cndd_u0)?;
        let wz_goal_rev = eq_symm(env, &wz_goal)?;
        mem_elt_rw(env, &wz_goal_rev, &cndd_srt)
    })?;
    debug_assert!(case_z.hyps().is_empty(), "pi_imax_dep: the zero case leaked a hypothesis");
    debug_assert_eq!(
        *case_z.concl(),
        Formula::imp(p, goal.clone()),
        "pi_imax_dep: the zero case has an unexpected shape"
    );

    // ── The antecedent block, then the `¬(v = ∅)` case and the join ─────────
    let k_to_goal = under(kk.clone(), |hk| {
        let h12 = Thm::mp(&and_left(k12.clone(), k34.clone()), hk)?;
        let h34 = Thm::mp(&and_right(k12.clone(), k34.clone()), hk)?;
        let hu = Thm::mp(&and_left(u_om.clone(), v_om.clone()), &h12)?;
        let hv = Thm::mp(&and_right(u_om.clone(), v_om.clone()), &h12)?;
        let ha = Thm::mp(&and_left(a_in.clone(), fib_v.clone()), &h34)?;
        let hf = Thm::mp(&and_right(a_in.clone(), fib_v.clone()), &h34)?;
        let bu_om = Thm::mp(&inst_all(&cx.ord.max_in_omega, &[tu.clone(), tv.clone()])?, &h12)?;

        // The base lands in `srt(u∪v)`, and `srt(v) ⊆ srt(u∪v)` for the
        // fibres — `mono_sub` over the union's bounds, under {K} alone.
        let max_ub_at = inst_all(&cx.ord.max_ub, &[tu.clone(), tv.clone()])?;
        let u_sub = crate::and_elim_left(&max_ub_at)?; // ⊢ u ⊆ u∪v
        let v_sub = crate::and_elim_right(&max_ub_at)?; // ⊢ v ⊆ u∪v
        let ms_u =
            Thm::mp(&inst_all(mono_sub, &[tu.clone(), bu.clone()])?, &and_intro(&hu, &bu_om))?;
        let a_bu =
            Thm::mp(&inst_all(&Thm::mp(&ms_u, &u_sub)?, std::slice::from_ref(&ta))?, &ha)?;
        let ms_v =
            Thm::mp(&inst_all(mono_sub, &[tv.clone(), bu.clone()])?, &and_intro(&hv, &bu_om))?;
        let srt_v_sub = Thm::mp(&ms_v, &v_sub)?; // {K} ⊢ srt(v) ⊆ srt(u∪v)

        // ── Case `¬(v = ∅)`: the Type clause ─────────────────────────────────
        let g_nz = under(np.clone(), |hnp| {
            let wn_goal = Thm::mp(
                &inst_all(&cx.i.when_nonzero, &[tv.clone(), cndd_qa.clone(), dp_t.clone()])?,
                hnp,
            )?;
            let wn_imax = Thm::mp(
                &inst_all(&cx.i.when_nonzero, &[tv.clone(), zero.clone(), bu.clone()])?,
                hnp,
            )?;

            // `u ∪ v ≠ ∅`, exactly as in the flagship.
            let mem0v = Formula::mem(zero.clone(), tv.clone());
            let zl = Thm::mp(&inst_all(&cx.ord.zero_least, std::slice::from_ref(&tv))?, &hv)?;
            let to_eq = syl(&zl, &eq_symm_imp(env, zero.clone(), tv.clone()))?;
            let h0v = Thm::mp(&notnot_elim(mem0v), &Thm::mp(&contrapos(&to_eq)?, hnp)?)?;
            let h0bu = Thm::mp(&inst_all(&v_sub, std::slice::from_ref(&zero))?, &h0v)?;
            let wv = env.fresh_var();
            let leib_ne = Thm::eq_leibniz(
                bu.clone(),
                zero.clone(),
                wv,
                Formula::mem(zero.clone(), Term::var(wv)),
            );
            let step_ne = Thm::mp(&com12(&leib_ne)?, &h0bu)?;
            let ne = syl(&step_ne, &inst_all(&cx.r.core().empty_ax, std::slice::from_ref(&zero))?)?;

            // The successor witness: {K,¬p} ⊢ ∃q. (q ∈ ω ∧ u∪v = succ q).
            let cases_at = Thm::mp(&inst_all(&cx.ord.cases, std::slice::from_ref(&bu))?, &bu_om)?;
            let ex = Thm::mp(&cases_at, &ne)?;
            debug_assert_eq!(
                *ex.concl(),
                Formula::exists(qv, e_body.clone()),
                "pi_imax_dep: the case principle's existential drifted"
            );

            // Under E(q): compute `srt(u∪v)`, raise base and fibres, close
            // under the dependent product, ride back.
            let e_to_goal = under(e_body.clone(), |he| {
                let hq = Thm::mp(&and_left(q_om.clone(), bu_eq.clone()), he)?;
                let heq = Thm::mp(&and_right(q_om.clone(), bu_eq.clone()), he)?;
                let at_succ_q =
                    Thm::mp(&inst_all(&cx.s.at_succ, std::slice::from_ref(&tq))?, &hq)?;
                let srt_bu_succ = srt_congr(env, cx.s, &heq)?;
                let srt_bu_eq = eq_trans(env, &srt_bu_succ, &at_succ_q)?;
                let lm = cx.ut.at(tq.clone());
                let w_lm = Term::apply(cx.tower.space.lu, vec![lm.clone()]);

                // The base, raised and rewritten.
                let a_u = mem_set_rw(env, &srt_bu_eq, &a_bu)?;

                // The fibres, raised **pointwise under the binder**: a fresh
                // `x` — free in no open hypothesis, which is what lets
                // `prim::gen` close over it — chained through the subset and
                // the ladder equation.
                let xv = env.fresh_var();
                let tx = Term::var(xv);
                let mut b_args = qts.clone();
                b_args.push(tx);
                let b_x = Term::apply(cx.dp.b, b_args);
                let hf_x = inst_all(&hf, std::slice::from_ref(&Term::var(xv)))?;
                let sub_at_b = inst_all(&srt_v_sub, std::slice::from_ref(&b_x))?;
                let chain = syl(&hf_x, &sub_at_b)?; // x∈A → b(q⃗,x) ∈ srt(u∪v)
                let wv2 = env.fresh_var();
                let leib_bu = Thm::eq_leibniz(
                    cx.s.at(bu.clone()),
                    w_lm.clone(),
                    wv2,
                    Formula::mem(b_x, Term::var(wv2)),
                );
                let bu_to_lm = Thm::mp(&leib_bu, &srt_bu_eq)?;
                let chain_lm = syl(&chain, &bu_to_lm)?; // x∈A → b(q⃗,x) ∈ U(lm)
                let fib_u = crate::prim::gen(xv, &chain_lm).ok()?;
                debug_assert_eq!(
                    *fib_u.concl(),
                    fibres_in_n(env, cx.dp.b, &qts, &ta, &w_lm),
                    "pi_imax_dep: the raised fibres do not match the Π rule's conjunct"
                );

                // The dependent product, at the variable rung.
                let mut pargs = qts.clone();
                pargs.push(lm);
                pargs.push(ta.clone());
                let pair_at = inst_all(pair, &pargs)?;
                let dp_u = Thm::mp(&pair_at, &and_intro(&a_u, &fib_u))?;

                // Ride the equations back to the `srt`/`ite0` spelling.
                let srt_bu_rev = eq_symm(env, &srt_bu_eq)?;
                let dp_bu = mem_set_rw(env, &srt_bu_rev, &dp_u)?;
                let srt_imax_eq = srt_congr(env, cx.s, &wn_imax)?;
                let srt_imax_rev = eq_symm(env, &srt_imax_eq)?;
                let dp_imax = mem_set_rw(env, &srt_imax_rev, &dp_bu)?;
                let wn_goal_rev = eq_symm(env, &wn_goal)?;
                mem_elt_rw(env, &wn_goal_rev, &dp_imax)
            })?; // {K,¬p} ⊢ E(q) → goal

            let all_q = crate::prim::gen(qv, &e_to_goal).ok()?;
            Thm::mp(&exists_elim_imp(qv, &all_q, &goal)?, &ex)
        })?; // {K} ⊢ ¬(v=∅) → goal

        // ── Classical join ───────────────────────────────────────────────────
        let joined = syl(&contrapos(&case_z)?, &g_nz)?;
        Thm::mp(&clavius(goal.clone()), &joined)
    })?; // ⊢ K → goal

    let mut all = qs;
    all.push(uv);
    all.push(vv);
    all.push(av);
    let out = gen_all(&all, &k_to_goal);
    debug_assert!(out.hyps().is_empty(), "pi_imax_dep: an assumption survived discharge");
    Some(out)
}
