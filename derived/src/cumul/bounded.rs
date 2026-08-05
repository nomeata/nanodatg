//! **Finite branching**: a function out of a natural number lands in a *single*
//! stage.
//!
//! # Interface
//!
//! Writing `Vₚ` for `app(iter(S), p)`, `T` for `tower(S)` and `g(b)` for
//! `app(g,b)`, this file defines the formula
//!
//! ```text
//! bnd(k) := ∀g. ( (∀b. (b ∈ k → g(b) ∈ T))
//!                    → ∃p. (p ∈ ω ∧ ∀b. (b ∈ k → g(b) ∈ Vₚ)) )     [bounded_at]
//! ```
//!
//! and proves
//!
//! ```text
//! ⊢ ∀k. (k ∈ ω → bnd(k))                                           [bounded]
//! ```
//!
//! Callers need none of the derivation below. [`bnd`] is the same formula with
//! the three bound variables minted internally — which is all any caller wants,
//! because `Formula::forall` *closes* over its variable, so the formula does not
//! depend on which one was used to build it.
//!
//! # `bnd` is the finiteness predicate, not `k ∈ ω`
//!
//! `bnd(k)` is what [`super::tower_closed_bnd`] actually spends, and it is the
//! hypothesis carried by the general form of every statement downstream;
//! `k ∈ ω` is one *sufficient* condition for it, proved here, and the one
//! [`crate::wnat`] and [`crate::wlist`] happen to satisfy. See
//! [`mod@super::finite`] for the closure properties that make `bnd` usable at a
//! fibre which is not a von Neumann natural, and [`mod@super::finord`] for
//! `⊢ bnd(finord(m))`, the fibre the general inductive translation produces.
//!
//! # This is the finite-branching hypothesis, and it is not avoidable
//!
//! `T = ⋃ₙ Vₙ` is closed under `sup` exactly when every fibre `B(a)` has this
//! property: a function `f : B(a) → T` picks a stage per argument, and `⟨a,f⟩`
//! reaches `T` only if those stages have a common upper bound. For an *infinite*
//! fibre they need not — with `Nat`-branching there is a tree of rank `ω`, then
//! one of rank `ω·2`, and the ranks so reachable are cofinal in `ω₁`, so
//! `W ⊄ ⋃ₙ Vₙ` and no choice of step operator repairs it. So the restriction to
//! finitely branching W-types is not an artefact of this construction; it is
//! where the `ω`-tower stops being enough.
//!
//! # A Grothendieck universe does not serve, and **not** because it lacks closure
//!
//! This is the inference the paragraph above invites and it is wrong, so it is
//! answered here rather than left to be re-derived. The kernel's `ax_tarski` is
//! the five-clause Grothendieck statement, `crate::universe` derives `⋃`,
//! binary union, pairing, products, function spaces and Replacement for it, and
//! **the sup-closure of a universe is already a theorem of this library**:
//!
//! ```text
//! ⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ ∀a ∈ A. B(a) ∈ u))
//!                 → closed(A,B,u))          [crate::bound::universe_closed]
//! ⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a ∈ A. B(a) ∈ U(c))
//!                 → closed(A,B,U(c)))       [crate::bound::least_universe_closed]
//! ```
//!
//! Those carry **no condition on the fibres whatsoever** — no `bnd`, no
//! `B(a) ∈ ω`, nothing. A universe is closed under `sup` at a `Nat`-indexed
//! fibre exactly as it is at a two-element one. `bound.rs`'s header says so in
//! its first line, and `U(c)` is *already* what the W-type's **bound** is, here
//! and in `crate::inductive::carrier`.
//!
//! So `bnd` is not standing in for a closure property a universe would supply.
//! The two sets have different jobs:
//!
//! * the **bound** `U(c)` is the set `W` is separated out of, so `W ⊆ U(c)` is
//!   free and its sup-closure is the theorem above;
//! * the **catcher** `T` is a set with `W ⊆ T` **and `T ∈ U₁`**, which is what
//!   `C₂` turns into `⟦T⟧ ∈ U₁`. All of `cumul/` exists to build one, and `bnd`
//!   is the fibre condition its `sup`-closure costs.
//!
//! **A universe cannot be a catcher.** `u ∉ u` by Regularity, and the only
//! `U ∈ U` fact in the development is `crate::universe::tower_step`,
//! `⊢ ∀x. U(x) ∈ U(U(x))` — exactly one rung too high, so a universe catcher
//! places a `Type 0` inductive in `U₂` and translates no Lean. Nor is
//! `U(c) ∈ U₁` reachable: `is_universe(U(x))` is a theorem now
//! (`crate::universe::least_universe_is_universe`), but it does not help — it
//! says `U(c)` *is* a universe, not that it is a **member** of `U₁`, and `C₄` at
//! a rung is still only reached by transfer through the intersection. The sole
//! `⊆`-to-`∈` tool that transfer exposes is
//! [`crate::cantor::image_in_universe`] — which wants a **member** of `u`
//! surjecting onto the target. Producing that member is the whole of the work;
//! the universe supplies none of it.
//!
//! What a universe's set-indexed-union closure does buy is real and is
//! **already spent**: `Inside::tower_mem` gets `T ∈ U(c)` out of the
//! `ω`-indexed family `iter(S)` by exactly that closure. The index is `ω`, so
//! the catcher is `ω` tall, and no taller catcher is reachable that way.
//!
//! **That is no longer the end of the story.** [`crate::wpath`] proves
//! `W(A,B,u) ∈ U(d)` with **no fibre condition at all**, by giving
//! [`crate::cantor::image_in_universe`] the member it wants —
//! `𝒫(prod(T,A))` — and a single-valued relation from it onto `W`: the tree's
//! set of labelled finite paths. The `ω`-tower is still in that proof, but as
//! the set the **paths** live in ([`super::tower_amb`]), where `ω` height is
//! enough, and not as the catcher, where it is not. `bnd` is therefore not
//! repaired by anything: it is on its way out. See SCOPING.md §14.3 and §14.6
//! for what is still wired to it.
//!
//! The thesis's answer is the ordinal rank argument, via
//! `cf(λ) > sup_{x∈A}|B(x)|`. **It is not the only route and this file used to
//! say it was** — see SCOPING.md §14, which costs it against bounding `W` by its
//! path codes (`⋃ₙ Dⁿ` and one Replacement, no ordinals — the move
//! [`crate::wrec`] already made at the recursor).
//!
//! The section is **§6.2.1**, "Definition of W-types in ZFC", `thesis.txt:2148`.
//! This header and [`crate::tower`]'s used to cite different sections for the
//! same formula, §6.2.1 against §6.3; `thesis.txt` is committed now and settles
//! it — §6.3 is "Soundness" and contains no cofinality statement at all — so
//! [`crate::tower`]'s citation was the wrong one and has been corrected.
//!
//! The witnesses are `derived/tests/cumul_infinite_fibre.rs`, which measures
//! that the *universe* half of [`super::FibreFacts`] derives at an infinite
//! fibre and only this half does not, and
//! `mini/tests/fixtures/infinitary_branching.lean` end to end.
//!
//! What *is* a choice is the shape of "finite". This file proves `bnd` for the
//! **von Neumann naturals**, `k ∈ ω`, because that is the shape the fibres
//! actually have: [`crate::wnat`]'s family sends the two tags to `0` and `1`,
//! [`crate::wlist`]'s to `0` and `1`, and a constructor with two recursive
//! arguments would send its tag to `2`. A fibre that is merely *equinumerous*
//! to a natural — a sum of units, say — needs `bnd` transported along a
//! surjection, which is one more lemma and not this one.
//!
//! # The induction, and why it needs directedness rather than a maximum
//!
//! Induction on `k`. At `0` the bound is `0` and the claim is vacuous. At
//! `succ k` the hypothesis gives a stage `p` covering `g` on `k`, the extra
//! point `k ∈ succ k` gives a stage `n` covering `g(k)`, and
//! [`super::Stages::directed`] merges the two — no `max`, no order on `ω`. That
//! is the whole proof; the length below is the cost of moving three witnesses
//! through a Hilbert system.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funspace::discharge;
use crate::recursion::{induction_scheme, mem_succ_self, Rec};
use crate::separation::{hyp_syl, or_intro_left};
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, ex_falso, exists_intro, exists_intro_imp,
    hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl,
};

use super::stages::Stages;
use super::step::curry;

/// `bnd(k)` at a caller-supplied term, as a formula — see the module header.
///
/// `gv`, `bv` and `pv` are the bound variables it is built with; passing them
/// in is what lets a caller rebuild the *same* formula.
pub fn bounded_at(
    _env: &mut Env,
    r: &Rec,
    st: &Stages,
    k: &Term,
    gv: FreeVar,
    bv: FreeVar,
    pv: FreeVar,
) -> Formula {
    let (tg, tb, tp) = (Term::var(gv), Term::var(bv), Term::var(pv));
    let gb = r.apply(tg, tb.clone());
    let in_k = Formula::mem(tb, k.clone());
    let hyp = Formula::forall(
        bv,
        Formula::imp(in_k.clone(), Formula::mem(gb.clone(), st.tower_set())),
    );
    let concl = Formula::forall(
        bv,
        Formula::imp(in_k, Formula::mem(gb, st.v(r, tp.clone()))),
    );
    let ex = Formula::exists(
        pv,
        Formula::and(Formula::mem(tp, r.omega()), concl),
    );
    Formula::forall(gv, Formula::imp(hyp, ex))
}

/// `bnd(k)` at a caller-supplied term, with the three bound variables minted
/// here.
///
/// [`Formula::forall`] closes over the variable it is given, so the formula
/// this returns is the one [`bounded_at`] returns at *any* three variables —
/// which is why no caller has to thread a triple around to rebuild it. Use this
/// one unless the three variables are wanted for something else.
pub fn bnd(env: &mut Env, r: &Rec, st: &Stages, k: &Term) -> Formula {
    let (gv, bv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    bounded_at(env, r, st, k, gv, bv, pv)
}

/// `⊢ ∀k. (k ∈ ω → bnd(k))` — **a function out of a natural number lands in a
/// single stage**.
pub fn bounded(env: &mut Env, r: &Rec, st: &Stages) -> Option<Thm> {
    let (kv, gv, bv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (nv, qv) = (env.fresh_var(), env.fresh_var());
    let (tk, tg, tb, tp) = (Term::var(kv), Term::var(gv), Term::var(bv), Term::var(pv));
    let (tn, tq) = (Term::var(nv), Term::var(qv));
    let om = r.omega();
    let tower = st.tower_set();

    let phi = bounded_at(env, r, st, &tk, gv, bv, pv);
    let g_of = |t: Term| r.apply(tg.clone(), t);
    let v_of = |t: Term| st.v(r, t);

    // `H(x) := ∀b. (b ∈ x → g(b) ∈ T)` and `C(x,p) := ∀b. (b ∈ x → g(b) ∈ Vₚ)`.
    let h_of = |x: &Term| {
        Formula::forall(
            bv,
            Formula::imp(
                Formula::mem(tb.clone(), x.clone()),
                Formula::mem(g_of(tb.clone()), tower.clone()),
            ),
        )
    };
    let c_of = |x: &Term, p: &Term| {
        Formula::forall(
            bv,
            Formula::imp(
                Formula::mem(tb.clone(), x.clone()),
                Formula::mem(g_of(tb.clone()), v_of(p.clone())),
            ),
        )
    };

    // ── Base: the bound is `0`, and the claim is vacuous ────────────────────
    let zero = r.zero();
    let vacuous = {
        let no_mem = inst_all(&r.core().empty_ax, std::slice::from_ref(&tb))?;
        let body = syl(
            &no_mem,
            &ex_falso(Formula::mem(g_of(tb.clone()), v_of(zero.clone()))),
        )?;
        Thm::gen(bv, &body)
    };
    debug_assert_eq!(*vacuous.concl(), c_of(&zero, &zero), "bounded: the base claim drifted");
    let base_body = and_intro(&r.core().zero_mem, &vacuous);
    let ex_zero = Formula::and(Formula::mem(tp.clone(), om.clone()), c_of(&zero, &tp));
    let base_ex = exists_intro(pv, ex_zero.clone(), zero.clone(), &base_body)?;
    let base = Thm::gen(gv, &a1i(&base_ex, h_of(&zero)));
    debug_assert_eq!(*base.concl(), phi.subst(kv, &zero), "bounded: the base drifted");

    // ── Step ────────────────────────────────────────────────────────────────
    let succ_k = r.succ_of(tk.clone());
    let k_om = Formula::mem(tk.clone(), om.clone());
    let k = Formula::and(k_om.clone(), phi.clone());
    let h_sk = h_of(&succ_k);
    let j = Formula::and(k.clone(), h_sk.clone());

    let j_k = and_left(k.clone(), h_sk.clone());
    let j_h = and_right(k.clone(), h_sk.clone());

    // `H(succ k) → H(k)`, since `b ∈ k → b ∈ succ k`.
    let succ_at_b = inst_all(&r.core().succ_ax, &[tk.clone(), tb.clone()])?;
    let into_succ = syl(
        &or_intro_left(
            Formula::mem(tb.clone(), tk.clone()),
            Formula::eq(tb.clone(), tk.clone()),
        ),
        &iff_mpr(&succ_at_b)?,
    )?;
    let j_h_b = syl(&j_h, &Thm::ax_inst(h_sk.clone(), tb.clone())?)?;
    let j_h_k_b = hyp_syl(&a1i(&into_succ, j.clone()), &j_h_b)?;
    let j_h_k = Thm::mp(
        &Thm::ax_dist(
            bv,
            j.clone(),
            Formula::imp(
                Formula::mem(tb.clone(), tk.clone()),
                Formula::mem(g_of(tb.clone()), tower.clone()),
            ),
        )?,
        &Thm::gen(bv, &j_h_k_b),
    )?;
    debug_assert_eq!(*j_h_k.concl(), Formula::imp(j.clone(), h_of(&tk)));

    // The induction hypothesis, at this `g`.
    let j_phi = syl(&j_k, &and_right(k_om.clone(), phi.clone()))?;
    let j_inst = syl(&j_phi, &Thm::ax_inst(phi.clone(), tg.clone())?)?;
    let j_ex_p = hyp_mp(&j_inst, &j_h_k)?;

    // The extra point `k ∈ succ k`.
    let j_at_k = hyp_mp(
        &syl(&j_h, &Thm::ax_inst(h_sk.clone(), tk.clone())?)?,
        &a1i(&mem_succ_self(r.core(), &tk)?, j.clone()),
    )?;
    let members_at = inst_all(&st.tower.members, &[g_of(tk.clone())])?;
    let j_ex_n = syl(&j_at_k, &iff_mp(&members_at)?)?;

    // ── Three witnesses ─────────────────────────────────────────────────────
    let e1 = Formula::and(Formula::mem(tp.clone(), om.clone()), c_of(&tk, &tp));
    let e2 = Formula::and(
        Formula::mem(tn.clone(), om.clone()),
        Formula::mem(g_of(tk.clone()), v_of(tn.clone())),
    );
    let j1 = Formula::and(j.clone(), e1.clone());
    let j2 = Formula::and(j1.clone(), e2.clone());

    let goal = Formula::exists(
        pv,
        Formula::and(Formula::mem(tp.clone(), om.clone()), c_of(&succ_k, &tp)),
    );

    // Inside `J2`: the two stages, and the directedness that merges them.
    let j2_j1 = and_left(j1.clone(), e2.clone());
    let j2_e2 = and_right(j1.clone(), e2.clone());
    let j2_e1 = syl(&j2_j1, &and_right(j.clone(), e1.clone()))?;
    let j2_p = syl(&j2_e1, &and_left(Formula::mem(tp.clone(), om.clone()), c_of(&tk, &tp)))?;
    let j2_c = syl(&j2_e1, &and_right(Formula::mem(tp.clone(), om.clone()), c_of(&tk, &tp)))?;
    let j2_n = syl(
        &j2_e2,
        &and_left(
            Formula::mem(tn.clone(), om.clone()),
            Formula::mem(g_of(tk.clone()), v_of(tn.clone())),
        ),
    )?;
    let j2_gk = syl(
        &j2_e2,
        &and_right(
            Formula::mem(tn.clone(), om.clone()),
            Formula::mem(g_of(tk.clone()), v_of(tn.clone())),
        ),
    )?;

    let dir_at = inst_all(&st.directed, std::slice::from_ref(&tp))?;
    let j2_inner = hyp_mp(&a1i(&dir_at, j2.clone()), &j2_p)?;
    let (_, all_m) = j2_inner.concl().as_imp()?;
    let j2_dir = hyp_mp(&syl(&j2_inner, &Thm::ax_inst(all_m, tn.clone())?)?, &j2_n)?;
    let e3 = Formula::and(
        Formula::mem(tq.clone(), om.clone()),
        Formula::and(
            kernel::thm::subset(env, v_of(tp.clone()), v_of(tq.clone())),
            kernel::thm::subset(env, v_of(tn.clone()), v_of(tq.clone())),
        ),
    );
    debug_assert_eq!(
        *j2_dir.concl(),
        Formula::imp(j2.clone(), Formula::exists(qv, e3.clone())),
        "bounded: directedness has an unexpected shape"
    );

    // ── Inside `J3`: the merged stage covers `succ k` ───────────────────────
    let j3 = Formula::and(j2.clone(), e3.clone());
    let j3_j2 = and_left(j2.clone(), e3.clone());
    let j3_e3 = and_right(j2.clone(), e3.clone());
    let sub_pq = kernel::thm::subset(env, v_of(tp.clone()), v_of(tq.clone()));
    let sub_nq = kernel::thm::subset(env, v_of(tn.clone()), v_of(tq.clone()));
    let j3_q = syl(&j3_e3, &and_left(Formula::mem(tq.clone(), om.clone()), Formula::and(sub_pq.clone(), sub_nq.clone())))?;
    let j3_subs = syl(&j3_e3, &and_right(Formula::mem(tq.clone(), om.clone()), Formula::and(sub_pq.clone(), sub_nq.clone())))?;
    let j3_pq = syl(&j3_subs, &and_left(sub_pq.clone(), sub_nq.clone()))?;
    let j3_nq = syl(&j3_subs, &and_right(sub_pq.clone(), sub_nq.clone()))?;

    // `J4 := J3 ∧ b ∈ succ k`.
    let b_sk = Formula::mem(tb.clone(), succ_k.clone());
    let j4 = Formula::and(j3.clone(), b_sk.clone());
    let j4_j3 = and_left(j3.clone(), b_sk.clone());
    let j4_b = and_right(j3.clone(), b_sk.clone());
    let disj = hyp_mp(&a1i(&iff_mp(&succ_at_b)?, j4.clone()), &j4_b)?;

    // Case `b ∈ k`: through `Vₚ`.
    let j4_c = syl(&j4_j3, &syl(&j3_j2, &j2_c)?)?;
    let j4_c_b = syl(&j4_c, &Thm::ax_inst(c_of(&tk, &tp), tb.clone())?)?;
    let j4_pq = syl(&j4_j3, &j3_pq)?;
    let j4_pq_b = syl(&j4_pq, &Thm::ax_inst(sub_pq.clone(), g_of(tb.clone()))?)?;
    let left = hyp_syl(&j4_c_b, &j4_pq_b)?;

    // Case `b = k`: through `Vₙ`, then Leibniz.
    let j4_gk = syl(&j4_j3, &syl(&j3_j2, &j2_gk)?)?;
    let j4_nq_b = syl(
        &syl(&j4_j3, &j3_nq)?,
        &Thm::ax_inst(sub_nq.clone(), g_of(tk.clone()))?,
    )?;
    let j4_gk_q = hyp_mp(&j4_nq_b, &j4_gk)?;
    let wv = env.fresh_var();
    let leib = Thm::eq_leibniz(
        tk.clone(),
        tb.clone(),
        wv,
        Formula::mem(g_of(Term::var(wv)), v_of(tq.clone())),
    );
    let carry = syl(&eq_symm_imp(env, tb.clone(), tk.clone()), &leib)?;
    let swap = crate::com12_imp(
        Formula::eq(tb.clone(), tk.clone()),
        Formula::mem(g_of(tk.clone()), v_of(tq.clone())),
        Formula::mem(g_of(tb.clone()), v_of(tq.clone())),
    );
    let right = hyp_mp(
        &Thm::mp(&crate::imp_mono_r(&swap, j4.clone())?, &a1i(&carry, j4.clone()))?,
        &j4_gk_q,
    )?;

    let cases = crate::hyp_or_elim(&disj, &left, &right)?;
    let j3_c = Thm::mp(
        &Thm::ax_dist(
            bv,
            j3.clone(),
            Formula::imp(b_sk, Formula::mem(g_of(tb.clone()), v_of(tq.clone()))),
        )?,
        &Thm::gen(bv, &curry(&cases)?),
    )?;
    debug_assert_eq!(
        *j3_c.concl(),
        Formula::imp(j3.clone(), c_of(&succ_k, &tq)),
        "bounded: the merged claim drifted"
    );

    let witness_body =
        Formula::and(Formula::mem(tp.clone(), om.clone()), c_of(&succ_k, &tp));
    let j3_goal = syl(
        &hyp_and(&j3_q, &j3_c)?,
        &exists_intro_imp(pv, witness_body, tq.clone())?,
    )?;
    debug_assert_eq!(*j3_goal.concl(), Formula::imp(j3, goal.clone()));

    // ── Discharge the three witnesses, innermost first ──────────────────────
    let j2_goal = discharge(qv, &j2_dir, &j3_goal)?;
    let j1_ex_n = syl(&and_left(j.clone(), e1.clone()), &j_ex_n)?;
    let j1_goal = discharge(nv, &j1_ex_n, &j2_goal)?;
    let j_goal = discharge(pv, &j_ex_p, &j1_goal)?;

    let step_body = curry(&j_goal)?;
    let step = Thm::mp(
        &Thm::ax_dist(gv, k.clone(), Formula::imp(h_sk.clone(), goal))?,
        &Thm::gen(gv, &step_body),
    )?;
    debug_assert_eq!(
        *step.concl(),
        Formula::imp(k.clone(), phi.subst(kv, &succ_k)),
        "bounded: the step drifted"
    );

    let scheme = induction_scheme(env, r.core(), kv, &phi)?;
    Thm::mp(&scheme, &and_intro(&base, &Thm::gen(kv, &step)))
}
