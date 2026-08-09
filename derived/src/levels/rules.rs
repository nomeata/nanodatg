//! Typing rules at a **variable** level — Π-formation at `imax` with the
//! Prop/Type split as an `ite0` *inside the target term* (`LEVELPOLY.md`
//! §1.4), plus cumulativity along `⊆` and two demonstrations.
//!
//! # Interface
//!
//! Writing `srt(t)` for [`crate::levels::srt::Srt::at`]'s term,
//! `imax(u,v) := ite0(v, ∅, u ∪ v)` with `∪` the crate's binary union
//! ([`crate::levels::order::Order::max`]), `fs` the tower's function-space
//! symbol, `1` the unit set `{∅}` ([`crate::sums::Sums::unit`]), and `cnd` a
//! fresh binary symbol (below), the exports are
//!
//! ```text
//! ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n → srt(m) ⊆ srt(n)))          [Rules::mono_sub]
//! ⊢ ∀u ∀v ∀A ∀b. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧ b ∈ srt(v)))
//!         → ite0(v, cnd(A,b), fs(A,b)) ∈ srt(imax(u,v)))          [Rules::pi_imax]
//! ⊢ ∀u ∀a. ((u ∈ ω ∧ a ∈ srt(succ u)) → fs(a,a) ∈ srt(succ u))    [Rules::fun_type_demo]
//! ⊢ ∀u. (u ∈ ω → 1 ∈ srt(u))                                      [Rules::punit_demo]
//! ```
//!
//! all unconditional, `⊆` spelled [`kernel::thm::subset`] exactly, and
//! `pi_imax`'s antecedent associated exactly as shown — the four conjuncts in
//! the briefed nesting `((u∈ω ∧ v∈ω) ∧ (A∈srt(u) ∧ b∈srt(v)))`.
//!
//! **`pi_imax` is the flagship** of the level-quantified design: Lean's
//! Π-formation rule `α : Sort u, β : Sort v ⊢ (∀x:α. β) : Sort (imax u v)` as
//! *one theorem* over variable levels, with the Prop/Type clause split carried
//! by the same conditional in both the term (`ite0(v, cnd, fs)`) and the level
//! (`ite0(v, ∅, u∪v)`). At `v = 0` the Π-type is the proposition
//! `∀x ∈ A. • ∈ b` — reified as the conditional singleton `cnd(A,b)`
//! ([`crate::prop::conditional_singleton`] at
//! `φ(A,b) := ∀x. (x ∈ A → • ∈ b)`, params `[A, b]`, `•` the point `∅`) —
//! landing in `srt(0) = U₀`; at `v ≠ 0` it is the function space `fs(A,b)`
//! landing in the genuine universe `srt(u ∪ v)`. [`Rules::cnd`] and its
//! characteristic theorem [`Rules::cnd_ax`],
//! `⊢ ∀A ∀b ∀z. (z ∈ cnd(A,b) ↔ (z ∈ 1 ∧ φ(A,b)))`, are exported so a
//! consumer (and the integration test) can spell the term and compute with it.
//!
//! `punit_demo` is the `PUnit`-shaped fact: the carrier `1` inhabits *every*
//! sort, one theorem for all levels. The ground checker mints a **0-ary symbol
//! per ground instantiation** of a declaration (`LEVELPOLY.md` §1.6); here the
//! per-instance facts `1 ∈ U₀`, `1 ∈ U(ω)`, … are `ax_inst`s of this single
//! quantified theorem — the "one theorem, many instantiations" economy the
//! quantified design buys.
//!
//! # Derivation style
//!
//! These derivations reason under hypotheses in the kernel's sequent
//! judgement, introduced and discharged **only** through [`crate::discharge`]
//! — the crate's one sanctioned introduction point (`ci/check-boundary.sh`
//! rule I1). Each hypothetical block is a [`crate::discharge::under`] /
//! [`crate::discharge::under_all`] call: the closure receives `{h} ⊢ h`, the
//! discharge is structural, and [`Thm::mp`] unions contexts underneath. The
//! one generalisation performed while hypotheses are still open (`pi_imax`'s
//! successor witness) goes through [`crate::prim::gen`], whose side condition
//! — the witness variable free in no open hypothesis — is exactly the
//! freshness the derivation arranged. This is what keeps a two-case,
//! one-existential argument like `pi_imax` readable: assume the antecedent
//! block once, split classically on the guard `v = ∅` (Clavius, as in
//! [`crate::levels::ite0`]), eliminate the successor-witness existential of
//! [`crate::levels::order::Order::cases`], and discharge on the way out.
//!
//! # Where each fact comes from
//!
//! `mono_sub` reads `m ⊆ n` through `⊆`-linearity
//! ([`crate::levels::order::Order::sub_iff`]): the `m ∈ n` disjunct is
//! cumulativity along `∈` ([`crate::levels::srt::Srt::mono_mem`]), the `m = n`
//! disjunct is subset-reflexivity ([`crate::cumul::subset_refl`]) carried
//! across the equation by Leibniz. `pi_imax`, case `v = ∅`: both `ite0`s
//! compute by `when_zero`, `srt(imax(u,v)) = srt(∅) = U₀` by Leibniz and
//! [`crate::levels::srt::Srt::at_zero`], and `cnd(A,b) ∈ U₀` is
//! [`crate::tower::Tower::cond_in_u0`] — this branch needs *none* of the four
//! antecedent conjuncts. Case `¬(v = ∅)`: both `ite0`s compute by
//! `when_nonzero`; `∅ ∈ v` ([`crate::levels::order::Order::zero_least`]
//! against the guard) puts `∅` in `u ∪ v` ([`Order::max_ub`]), so
//! `u ∪ v ≠ ∅` (else `∅ ∈ ∅`, against the empty-set axiom), and
//! [`Order::cases`] at `u ∪ v ∈ ω` ([`Order::max_in_omega`]) yields a
//! successor witness `u ∪ v = succ q`; then
//! `srt(u∪v) = srt(succ q) = U(app(lvl,q))`
//! ([`crate::levels::srt::Srt::at_succ`]), `A`, `b` land in `srt(u∪v)` by
//! `mono_sub` over [`Order::max_ub`], the tower's `∀c`-closure
//! [`crate::tower::Tower::funspace`] applies at `c := app(lvl,q)`, and the
//! equations ride back. `fun_type_demo` is `at_succ` + `funspace` at
//! `c := app(lvl,u)` — the owner's `a : Type u ⇝ ⟦a⟧ ∈ U(u)` sentence at a
//! variable `u`. `punit_demo` splits by `Order::cases`: at `∅`,
//! [`crate::tower::Tower::true_in_u0`] through the reversed `at_zero`; at
//! `succ m`, `1 ∈ U₀ ∈ U(app(lvl,m))` closed by `C₁`-transitivity
//! ([`crate::tower::Tower::transitive`]) and read back through `at_succ`.
//!
//! # Symbol identity
//!
//! Exactly as in [`crate::levels::srt`]: `∅`, `succ`, `ω`, `app` are `r`'s and
//! must be the ones `i`, `ord`, `ut`, `s` and the `tower` were built over. The
//! constructor guards the cheap identities — the shared `∅`, `ω`, the pairing
//! and union `ord`'s `max` is spelled with, the `srt` spelling, and that
//! `at_succ`'s universe is the tower's `U(·)` over `ut`'s ladder — and lets
//! the kernel refuse anything subtler by failing a composition.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::discharge::{under, under_all};
use crate::levels::ite0::Ite0;
use crate::levels::order::Order;
use crate::levels::srt::Srt;
use crate::levels::utower::UTower;
use crate::prop::conditional_singleton;
use crate::recursion::Rec;
use crate::sums::Sums;
use crate::tower::Tower;
use crate::{
    and_elim_left, and_elim_right, and_intro, and_left, and_right, clavius, com12, contrapos,
    eq_symm, eq_symm_imp, eq_trans, exists_elim_imp, gen_all, iff_mp, inst_all, mpd_const,
    notnot_elim, syl,
};

/// The rule kit at a variable level. See the module header for the statements.
pub struct Rules {
    /// The conditional-singleton symbol for the Prop-clause Π:
    /// `cnd(A,b) = { x ∈ 1 : ∀x. (x ∈ A → • ∈ b) }`.
    pub cnd: FnSym,
    /// `⊢ ∀A ∀b ∀z. (z ∈ cnd(A,b) ↔ (z ∈ 1 ∧ ∀x. (x ∈ A → • ∈ b)))`.
    pub cnd_ax: Thm,
    /// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n → srt(m) ⊆ srt(n)))`.
    pub mono_sub: Thm,
    /// `⊢ ∀u ∀v ∀A ∀b. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧ b ∈ srt(v))) →
    /// ite0(v, cnd(A,b), fs(A,b)) ∈ srt(imax(u,v)))` — **Π-formation at
    /// `imax`, both clauses in one theorem**.
    pub pi_imax: Thm,
    /// `⊢ ∀u ∀a. ((u ∈ ω ∧ a ∈ srt(succ u)) → fs(a,a) ∈ srt(succ u))`.
    pub fun_type_demo: Thm,
    /// `⊢ ∀u. (u ∈ ω → 1 ∈ srt(u))`.
    pub punit_demo: Thm,
}

/// Everything the derivations share, bundled so each helper takes one context.
struct Cx<'a> {
    r: &'a Rec,
    i: &'a Ite0,
    ord: &'a Order,
    ut: &'a UTower,
    s: &'a Srt,
    tower: &'a Tower,
}

/// Derive the kit over the caller's chain.
///
/// `r`'s `∅`/`succ`/`ω`/`app` must be the ones `i`, `ord`, `ut` and `s` were
/// built over, and `tower` the [`Tower`] whose `Apply` and `Peano` `r` was
/// rebuilt from — see the module header. Returns `None` on a symbol mismatch.
pub fn rules(
    env: &mut Env,
    r: &Rec,
    i: &Ite0,
    ord: &Order,
    ut: &UTower,
    s: &Srt,
    tower: &Tower,
) -> Option<Rules> {
    // The cheap identity guards; anything subtler fails a composition below.
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
    // `at_succ` must land on the tower's `U(·)` over `ut`'s ladder — that is
    // the universe `tower.funspace` and `tower.transitive` speak about.
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
    debug_assert_eq!(tower.sums.point(), r.zero(), "rules: the point is not the chain's ∅");

    let cx = Cx { r, i, ord, ut, s, tower };

    let mono_sub = mono_sub(env, &cx)?;

    // The Prop-clause Π symbol: one conditional singleton over params [A, b].
    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let phi = pi_body(env, &tower.sums, &Term::var(av), &Term::var(bv));
    let (cnd, cnd_ax) = conditional_singleton(env, &tower.sums, &[av, bv], &phi)?;

    let pi_imax = pi_imax(env, &cx, &mono_sub, cnd, &cnd_ax)?;
    let fun_type_demo = fun_type_demo(env, &cx)?;
    let punit_demo = punit_demo(env, &cx)?;

    Some(Rules { cnd, cnd_ax, mono_sub, pi_imax, fun_type_demo, punit_demo })
}

/// The Prop-clause Π body `φ(A,b) := ∀x. (x ∈ A → • ∈ b)`, with `•` the
/// point `∅` — the uniform-typing reading of `∀x:α. β` at sort 0
/// (`LEVELPOLY.md` §1.4).
fn pi_body(env: &mut Env, sums: &Sums, a: &Term, b: &Term) -> Formula {
    let x = env.fresh_var();
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(Term::var(x), a.clone()),
            Formula::mem(sums.point(), b.clone()),
        ),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Sequent-style building blocks. Each is one Leibniz instance or one classical
// figure; hypotheses union through `Thm::mp` underneath.
// ─────────────────────────────────────────────────────────────────────────────

/// From `Γ ⊢ a ∨ b`, `Δ ⊢ a → χ`, `Ε ⊢ b → χ` infer `Γ ∪ Δ ∪ Ε ⊢ χ` —
/// disjunction elimination, closed classically by Clavius (`∨` is `¬· → ·`).
fn or_elim(disj: &Thm, left: &Thm, right: &Thm) -> Option<Thm> {
    let (_, chi) = left.concl().as_imp()?;
    let nchi_na = contrapos(left)?; // ¬χ → ¬a
    let nchi_b = syl(&nchi_na, disj)?; // ¬χ → b
    let nchi_chi = syl(&nchi_b, right)?; // ¬χ → χ
    Thm::mp(&clavius(chi), &nchi_chi)
}

/// From `Γ ⊢ a = b` and `Δ ⊢ x ∈ a` infer `Γ ∪ Δ ⊢ x ∈ b` — the container
/// rewritten along the equation.
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

/// From `Γ ⊢ a = b` and `Δ ⊢ a ∈ y` infer `Γ ∪ Δ ⊢ b ∈ y` — the element
/// rewritten along the equation.
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

/// From `Γ ⊢ a = b` infer `Γ ⊢ srt(a) = srt(b)` — congruence for the `srt`
/// term former, by Leibniz over reflexivity.
fn srt_congr(env: &mut Env, s: &Srt, eq: &Thm) -> Option<Thm> {
    let (a, b) = eq.concl().as_eq()?;
    let w = env.fresh_var();
    let phi = Formula::eq(s.at(a.clone()), s.at(Term::var(w)));
    let leib = Thm::eq_leibniz(a.clone(), b, w, phi);
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(s.at(a)))
}

// ─────────────────────────────────────────────────────────────────────────────
// The four exports.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n → srt(m) ⊆ srt(n)))` —
/// **cumulativity along `⊆`**.
fn mono_sub(env: &mut Env, cx: &Cx) -> Option<Thm> {
    let sub_refl = crate::cumul::subset_refl(env)?;
    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let w = cx.r.omega();
    let m_om = Formula::mem(tm.clone(), w.clone());
    let n_om = Formula::mem(tn.clone(), w);
    let j = Formula::and(m_om.clone(), n_om.clone());
    let sub = kernel::thm::subset(env, tm.clone(), tn.clone());
    let goal = kernel::thm::subset(env, cx.s.at(tm.clone()), cx.s.at(tn.clone()));

    // `m = n`: subset-reflexivity carried across the equation. Closed, so it
    // is built before the hypothetical block.
    let refl_at = inst_all(&sub_refl, std::slice::from_ref(&cx.s.at(tm.clone())))?;
    let hole = env.fresh_var();
    let sub_hole = kernel::thm::subset(env, cx.s.at(tm.clone()), cx.s.at(Term::var(hole)));
    let leib = Thm::eq_leibniz(tm.clone(), tn.clone(), hole, sub_hole);
    let case_eq = mpd_const(&leib, &refl_at)?;

    let imp2 = under_all(&[j.clone(), sub.clone()], |hs| {
        let (hj, hsub) = (&hs[0], &hs[1]);
        // {J, m⊆n} ⊢ m ∈ n ∨ m = n, through `⊆`-linearity.
        let iff_at = Thm::mp(&inst_all(&cx.ord.sub_iff, &[tm.clone(), tn.clone()])?, hj)?;
        let disj = Thm::mp(&iff_mp(&iff_at)?, hsub)?;
        // `m ∈ n`: cumulativity along `∈`, at the container `n`.
        let hn = Thm::mp(&and_right(m_om.clone(), n_om.clone()), hj)?;
        let mono_at_n = Thm::mp(&inst_all(&cx.s.mono_mem, std::slice::from_ref(&tn))?, &hn)?;
        let case_mem = inst_all(&mono_at_n, std::slice::from_ref(&tm))?;
        or_elim(&disj, &case_mem, &case_eq)
    })?;
    let out = gen_all(&[m, n], &imp2);
    debug_assert!(out.hyps().is_empty(), "mono_sub: an assumption survived discharge");
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(m, Formula::forall(n, Formula::imp(j, Formula::imp(sub, goal)))),
        "mono_sub: unexpected shape"
    );
    Some(out)
}

/// The flagship: `⊢ ∀u ∀v ∀A ∀b. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧
/// b ∈ srt(v))) → ite0(v, cnd(A,b), fs(A,b)) ∈ srt(imax(u,v)))`.
///
/// Classical cases on the guard `v = ∅`; see the module header for the route.
fn pi_imax(env: &mut Env, cx: &Cx, mono_sub: &Thm, cnd: FnSym, cnd_ax: &Thm) -> Option<Thm> {
    let (uv, vv, av, bv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tv, ta, tb) = (Term::var(uv), Term::var(vv), Term::var(av), Term::var(bv));
    let omega = cx.r.omega();
    let zero = cx.r.zero();

    let u_om = Formula::mem(tu.clone(), omega.clone());
    let v_om = Formula::mem(tv.clone(), omega.clone());
    let a_in = Formula::mem(ta.clone(), cx.s.at(tu.clone()));
    let b_in = Formula::mem(tb.clone(), cx.s.at(tv.clone()));
    let k12 = Formula::and(u_om.clone(), v_om.clone());
    let k34 = Formula::and(a_in.clone(), b_in.clone());
    let k = Formula::and(k12.clone(), k34.clone());

    let cnd_ab = Term::apply(cnd, vec![ta.clone(), tb.clone()]);
    let fs_ab = cx.tower.sums.fs.of(ta.clone(), tb.clone());
    let ite_t = cx.i.at(tv.clone(), cnd_ab.clone(), fs_ab.clone());
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
        // Both conditionals compute: the term to `cnd(A,b)`, the level to `∅`.
        let wz_goal = Thm::mp(
            &inst_all(&cx.i.when_zero, &[tv.clone(), cnd_ab.clone(), fs_ab.clone()])?,
            hp,
        )?;
        let wz_imax =
            Thm::mp(&inst_all(&cx.i.when_zero, &[tv.clone(), zero.clone(), bu.clone()])?, hp)?;
        // {v=∅} ⊢ srt(imax(u,v)) = U₀, through `srt(∅) = U₀`.
        let srt_imax_zero = srt_congr(env, cx.s, &wz_imax)?;
        let srt_eq = eq_trans(env, &srt_imax_zero, &cx.s.at_zero)?;
        // `cnd(A,b) ∈ U₀`, unconditionally: the conditional singleton is a
        // truth value whatever φ(A,b) turns out to be.
        let phi_ab = pi_body(env, &cx.tower.sums, &ta, &tb);
        let chi = inst_all(cnd_ax, &[ta.clone(), tb.clone()])?;
        let cnd_u0 = cx.tower.cond_in_u0(env, &phi_ab, &cnd_ab, &chi)?;
        debug_assert!(cnd_u0.hyps().is_empty(), "pi_imax: cond_in_u0 assumed something");
        let srt_eq_rev = eq_symm(env, &srt_eq)?;
        let cnd_srt = mem_set_rw(env, &srt_eq_rev, &cnd_u0)?;
        let wz_goal_rev = eq_symm(env, &wz_goal)?;
        mem_elt_rw(env, &wz_goal_rev, &cnd_srt)
    })?;
    debug_assert!(case_z.hyps().is_empty(), "pi_imax: the zero case leaked a hypothesis");
    debug_assert_eq!(
        *case_z.concl(),
        Formula::imp(p, goal.clone()),
        "pi_imax: the zero case has an unexpected shape"
    );

    // ── The antecedent block, then the `¬(v = ∅)` case and the join under it ─
    let k_to_goal = under(k.clone(), |hk| {
        let h12 = Thm::mp(&and_left(k12.clone(), k34.clone()), hk)?;
        let h34 = Thm::mp(&and_right(k12.clone(), k34.clone()), hk)?;
        let hu = Thm::mp(&and_left(u_om.clone(), v_om.clone()), &h12)?;
        let hv = Thm::mp(&and_right(u_om.clone(), v_om.clone()), &h12)?;
        let ha = Thm::mp(&and_left(a_in.clone(), b_in.clone()), &h34)?;
        let hb = Thm::mp(&and_right(a_in.clone(), b_in.clone()), &h34)?;
        let bu_om = Thm::mp(&inst_all(&cx.ord.max_in_omega, &[tu.clone(), tv.clone()])?, &h12)?;

        // `A`, `b` land in `srt(u∪v)`: `mono_sub` over the union's bounds.
        // Derived under {K} alone, outside the case split.
        let max_ub_at = inst_all(&cx.ord.max_ub, &[tu.clone(), tv.clone()])?;
        let u_sub = and_elim_left(&max_ub_at)?; // ⊢ u ⊆ u∪v
        let v_sub = and_elim_right(&max_ub_at)?; // ⊢ v ⊆ u∪v
        let ms_u =
            Thm::mp(&inst_all(mono_sub, &[tu.clone(), bu.clone()])?, &and_intro(&hu, &bu_om))?;
        let a_bu =
            Thm::mp(&inst_all(&Thm::mp(&ms_u, &u_sub)?, std::slice::from_ref(&ta))?, &ha)?;
        let ms_v =
            Thm::mp(&inst_all(mono_sub, &[tv.clone(), bu.clone()])?, &and_intro(&hv, &bu_om))?;
        let b_bu =
            Thm::mp(&inst_all(&Thm::mp(&ms_v, &v_sub)?, std::slice::from_ref(&tb))?, &hb)?;

        // ── Case `¬(v = ∅)`: the Type clause ─────────────────────────────────
        let g_nz = under(np.clone(), |hnp| {
            let wn_goal = Thm::mp(
                &inst_all(&cx.i.when_nonzero, &[tv.clone(), cnd_ab.clone(), fs_ab.clone()])?,
                hnp,
            )?;
            let wn_imax = Thm::mp(
                &inst_all(&cx.i.when_nonzero, &[tv.clone(), zero.clone(), bu.clone()])?,
                hnp,
            )?;

            // `∅ ∈ v` from `zero_least` against the guard, hence `∅ ∈ u∪v`,
            // hence `¬(u∪v = ∅)` — else `∅ ∈ ∅`, against the empty-set axiom.
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
                "pi_imax: the case principle's existential drifted"
            );

            // Under E(q): compute `srt(u∪v)`, close under `fs`, ride back.
            let e_to_goal = under(e_body.clone(), |he| {
                let hq = Thm::mp(&and_left(q_om.clone(), bu_eq.clone()), he)?;
                let heq = Thm::mp(&and_right(q_om.clone(), bu_eq.clone()), he)?;
                let at_succ_q =
                    Thm::mp(&inst_all(&cx.s.at_succ, std::slice::from_ref(&tq))?, &hq)?;
                let srt_bu_succ = srt_congr(env, cx.s, &heq)?;
                let srt_bu_eq = eq_trans(env, &srt_bu_succ, &at_succ_q)?;

                let a_u = mem_set_rw(env, &srt_bu_eq, &a_bu)?;
                let b_u = mem_set_rw(env, &srt_bu_eq, &b_bu)?;
                let fs_u = Thm::mp(
                    &inst_all(&cx.tower.funspace, &[cx.ut.at(tq.clone()), ta.clone(), tb.clone()])?,
                    &and_intro(&a_u, &b_u),
                )?;
                let srt_bu_rev = eq_symm(env, &srt_bu_eq)?;
                let fs_bu = mem_set_rw(env, &srt_bu_rev, &fs_u)?;
                let srt_imax_eq = srt_congr(env, cx.s, &wn_imax)?;
                let srt_imax_rev = eq_symm(env, &srt_imax_eq)?;
                let fs_imax = mem_set_rw(env, &srt_imax_rev, &fs_bu)?;
                let wn_goal_rev = eq_symm(env, &wn_goal)?;
                mem_elt_rw(env, &wn_goal_rev, &fs_imax)
            })?; // {K,¬p} ⊢ E(q) → goal

            // Generalise the witness — fresh in every open hypothesis — and
            // eliminate the existential.
            let all_q = crate::prim::gen(qv, &e_to_goal).ok()?;
            Thm::mp(&exists_elim_imp(qv, &all_q, &goal)?, &ex)
        })?; // {K} ⊢ ¬(v=∅) → goal

        // ── Classical join ───────────────────────────────────────────────────
        let joined = syl(&contrapos(&case_z)?, &g_nz)?; // {K} ⊢ ¬goal → goal
        Thm::mp(&clavius(goal.clone()), &joined)
    })?; // ⊢ K → goal

    let out = gen_all(&[uv, vv, av, bv], &k_to_goal);
    debug_assert!(out.hyps().is_empty(), "pi_imax: an assumption survived discharge");
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(
            uv,
            Formula::forall(
                vv,
                Formula::forall(av, Formula::forall(bv, Formula::imp(k, goal))),
            ),
        ),
        "pi_imax: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀u ∀a. ((u ∈ ω ∧ a ∈ srt(succ u)) → fs(a,a) ∈ srt(succ u))` —
/// "`α : Type u ⊢ (α → α) : Type u`" at a variable `u`.
fn fun_type_demo(env: &mut Env, cx: &Cx) -> Option<Thm> {
    let (uv, av) = (env.fresh_var(), env.fresh_var());
    let (tu, ta) = (Term::var(uv), Term::var(av));
    let srt_su = cx.s.at(cx.r.succ_of(tu.clone()));
    let u_om = Formula::mem(tu.clone(), cx.r.omega());
    let a_in = Formula::mem(ta.clone(), srt_su.clone());
    let h = Formula::and(u_om.clone(), a_in.clone());
    let fs_aa = cx.tower.sums.fs.of(ta.clone(), ta.clone());

    let imp = under(h.clone(), |hh| {
        let hu = Thm::mp(&and_left(u_om.clone(), a_in.clone()), hh)?;
        let ha = Thm::mp(&and_right(u_om.clone(), a_in.clone()), hh)?;
        let eq = Thm::mp(&inst_all(&cx.s.at_succ, std::slice::from_ref(&tu))?, &hu)?;
        let a_u = mem_set_rw(env, &eq, &ha)?;
        let fs_u = Thm::mp(
            &inst_all(&cx.tower.funspace, &[cx.ut.at(tu.clone()), ta.clone(), ta.clone()])?,
            &and_intro(&a_u, &a_u),
        )?;
        let eq_rev = eq_symm(env, &eq)?;
        mem_set_rw(env, &eq_rev, &fs_u)
    })?;
    let out = gen_all(&[uv, av], &imp);
    debug_assert!(out.hyps().is_empty(), "fun_type_demo: an assumption survived discharge");
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(
            uv,
            Formula::forall(av, Formula::imp(h, Formula::mem(fs_aa, srt_su))),
        ),
        "fun_type_demo: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀u. (u ∈ ω → 1 ∈ srt(u))` — the `PUnit` carrier at every level, one
/// theorem where the ground checker mints a symbol per instantiation
/// (`LEVELPOLY.md` §1.6).
fn punit_demo(env: &mut Env, cx: &Cx) -> Option<Thm> {
    let uv = env.fresh_var();
    let tu = Term::var(uv);
    let omega = cx.r.omega();
    let zero = cx.r.zero();
    let one = cx.tower.sums.unit();
    let h = Formula::mem(tu.clone(), omega.clone());
    let goal = Formula::mem(one.clone(), cx.s.at(tu.clone()));

    // ── `u = ∅`: `1 ∈ U₀` through the reversed `at_zero`, then Leibniz ───────
    let at_zero_rev = eq_symm(env, &cx.s.at_zero)?;
    let one_srt0 = mem_set_rw(env, &at_zero_rev, &cx.tower.true_in_u0)?;
    let sym = eq_symm_imp(env, tu.clone(), zero.clone()); // ⊢ u = ∅ → ∅ = u
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(
        zero.clone(),
        tu.clone(),
        w,
        Formula::mem(one.clone(), cx.s.at(Term::var(w))),
    );
    let case_zero = syl(&sym, &mpd_const(&leib, &one_srt0)?)?; // ⊢ u = ∅ → 1 ∈ srt(u)

    // ── `u = succ m`: `1 ∈ U₀ ∈ U(app(lvl,m))`, closed by `C₁` ───────────────
    let mv = env.fresh_var();
    let tm = Term::var(mv);
    let m_om = Formula::mem(tm.clone(), omega);
    let u_eq = Formula::eq(tu.clone(), cx.r.succ_of(tm.clone()));
    let e_body = Formula::and(m_om.clone(), u_eq.clone());

    let e_to_goal = under(e_body.clone(), |he| {
        let hm = Thm::mp(&and_left(m_om.clone(), u_eq.clone()), he)?;
        let hueq = Thm::mp(&and_right(m_om.clone(), u_eq.clone()), he)?;

        let lm = cx.ut.at(tm.clone());
        let u0_in_lm = inst_all(&cx.tower.u0_in, std::slice::from_ref(&lm))?;
        let all_z = Thm::mp(&inst_all(&cx.tower.transitive, &[lm, cx.s.u0()])?, &u0_in_lm)?;
        let one_in_lm =
            Thm::mp(&inst_all(&all_z, std::slice::from_ref(&one))?, &cx.tower.true_in_u0)?;
        let at_succ_m = Thm::mp(&inst_all(&cx.s.at_succ, std::slice::from_ref(&tm))?, &hm)?;
        let at_succ_m_rev = eq_symm(env, &at_succ_m)?;
        let one_in_ssm = mem_set_rw(env, &at_succ_m_rev, &one_in_lm)?;
        // `srt(succ m) = srt(u)` along the reversed witness equation.
        let hueq_rev = eq_symm(env, &hueq)?;
        let srt_eq = srt_congr(env, cx.s, &hueq_rev)?;
        mem_set_rw(env, &srt_eq, &one_in_ssm)
    })?; // ⊢ E(m) → 1 ∈ srt(u), closed
    debug_assert!(e_to_goal.hyps().is_empty(), "punit_demo: the witness case leaked");
    let all_m = Thm::gen(mv, &e_to_goal);
    let case_succ = exists_elim_imp(mv, &all_m, &goal)?; // ⊢ (∃m. E) → 1 ∈ srt(u)

    let imp = under(h.clone(), |hh| {
        let disj = Thm::mp(&inst_all(&cx.ord.cases, std::slice::from_ref(&tu))?, hh)?;
        debug_assert_eq!(
            *disj.concl(),
            Formula::or(Formula::eq(tu.clone(), zero.clone()), Formula::exists(mv, e_body.clone())),
            "punit_demo: the case principle's shape drifted"
        );
        or_elim(&disj, &case_zero, &case_succ)
    })?;
    let out = Thm::gen(uv, &imp);
    debug_assert!(out.hyps().is_empty(), "punit_demo: an assumption survived discharge");
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(uv, Formula::imp(h, goal)),
        "punit_demo: unexpected shape"
    );
    Some(out)
}
