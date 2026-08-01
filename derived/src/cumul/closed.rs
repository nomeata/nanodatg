//! **The tower is closed under `sup`** — step (b) of the route in
//! [`crate::cumul`], and the only step of it that is real mathematics.
//!
//! # Interface
//!
//! Writing `S` for the seed (a free variable, as everywhere in this module),
//! `T` for `tower(S)`, `B(a)` for `app(B,a)`, `bnd` for [`super::bounded::bnd`]
//! and `closed` for [`crate::wtype::closed`], the exports are
//!
//! ```text
//! ⊢ ∀A ∀B. ( (A ⊆ S ∧ ∀a. (a ∈ A → (B(a) ⊆ S ∧ bnd(B(a)))))
//!                → closed(A, B, T) )                      [tower_closed_bnd]
//!
//! ⊢ ∀A ∀B. ( (A ⊆ S ∧ ∀a. (a ∈ A → (B(a) ⊆ S ∧ B(a) ∈ ω)))
//!                → closed(A, B, T) )                          [tower_closed]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # One derivation, two hypotheses
//!
//! [`tower_closed_bnd`] is the derivation; [`tower_closed`] is it with the
//! fibre condition strengthened back to `B(a) ∈ ω` by [`mod@super::bounded`], and
//! is four lines. The two are kept **both** because the two consumers are
//! different: [`crate::wnat`] and [`crate::enums`] have von Neumann naturals as
//! fibres and should not pay for generality, while the general inductive
//! translation's fibre is `finord(m)`, a nest of binary sums with `m` elements
//! which is not a member of `ω` and cannot be made one.
//!
//! `bnd(B(a))` is the *weakest* fibre condition that carries this proof — it is
//! literally the one thing the derivation below asks of the fibre, at the one
//! place marked "Finite branching" — and it is not a hypothesis that could
//! smuggle an infinitely branching `W` past the argument: `bnd(k)` is a
//! statement about the tower with real content, refutable at `k := ω` (take
//! `g := iter(S)`, whose values `Vₙ` are members of `T` with no common stage),
//! and nothing here assumes it. See [`mod@super::bounded`].
//!
//! # The two hypotheses, and why they are hypotheses
//!
//! The closing note of [`crate::cumul`] proposed instantiating the seed at
//! `S := A ∪ ⋃⋃⋃B` and proving the two side conditions once and for all. That
//! is a *worse* deal than it looks: `B(a) ⊆ ⋃⋃⋃B` needs `⟨a,B(a)⟩ ∈ B`, i.e.
//! `B` has to be known to be a function with `A` in its domain — two more
//! hypotheses, of exactly the kind the seed was supposed to remove. So the seed
//! stays a free variable and the two facts the construction actually spends
//! stay antecedents:
//!
//! * `A ⊆ S` and `B(a) ⊆ S`, which put `a` and every `b ∈ B(a)` into
//!   `V₀ = S` and hence, by [`crate::cumul::Stages::zero_least`], into every
//!   stage;
//! * `B(a) ∈ ω`, which is finite branching — see [`mod@super::bounded`].
//!
//! At a concrete W-type both are one line each: [`super::witness`] discharges
//! them for [`crate::wnat`] at the seed `S := A ∪ 1`, which is a great deal
//! smaller than `A ∪ ⋃⋃⋃B`.
//!
//! # The shape of the argument
//!
//! Given `a ∈ A` and `f ∈ fs(B(a), T)`:
//!
//! ```text
//! ∀b ∈ B(a). f(b) ∈ T                       crate::ext::funspace_app_mem
//! ∃p ∈ ω. ∀b ∈ B(a). f(b) ∈ Vₚ              super::bounded, at k := B(a)
//! w ∈ f  →  w = ⟨q,r⟩, q ∈ B(a), r ∈ T      crate::bound::funspace_pairs
//! q ∈ B(a) ⊆ S = V₀ ⊆ Vₚ                    zero_least
//! r = f(q) ∈ Vₚ                             Rec::app_of_graph, single-valuedness
//! w ∈ V₍succ² p₎                            pair_in_stage
//! f ⊆ V₍succ² p₎  ⇒  f ∈ V₍succ³ p₎         sub_in_stage
//! a ∈ A ⊆ S = V₀ ⊆ V₍succ³ p₎               zero_least
//! ⟨a,f⟩ ∈ V₍succ⁵ p₎  ⇒  ⟨a,f⟩ ∈ T          pair_in_stage, mem_tower
//! ```
//!
//! The step the closing note called "the only real work" — reading "the members
//! of `f` are exactly the pairs `⟨b, f(b)⟩`" off `is_function` — turned out to
//! be **already proved**: [`crate::bound::funspace_pairs`] is precisely the
//! first half of it, and [`crate::recursion::Rec::app_of_graph`] the second.
//! Nothing new about functions had to be derived here.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funspace::discharge;
use crate::recursion::Rec;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, eq_symm, eq_symm_imp, gen_all, hyp_and, hyp_mp, iff_mp, inst_all,
    opair, syl,
};

use super::stages::Stages;
use super::step::curry;

/// From `⊢ H → ∀v₁ … ∀vₙ. φ` infer `⊢ H → φ[t₁ … tₙ]`.
fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])`.
fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, npsi) = inner.as_imp()?;
    let (psi, fls2) = npsi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// `Fin⁺(A,B) = A ⊆ S ∧ ∀a. (a ∈ A → (B(a) ⊆ S ∧ bnd(B(a))))` at
/// caller-supplied terms — the antecedent of [`tower_closed_bnd`] and, inside
/// one more conjunction, of [`super::WMem::w_in_universe_bnd`].
///
/// A consumer has to *prove* this formula, so it is exported rather than left
/// to be read off a theorem with `as_imp`. The two agree: `Formula::forall`
/// closes over the variable it is given, so the `∀a` built here is the one
/// [`tower_closed_bnd`] built.
///
/// `seed` is the term the consumer's seed *is*. Everything in [`crate::cumul`]
/// is stated at the free variable `st.seed`, so a consumer reaches its own seed
/// by `Thm::gen(st.seed, …)` and one instantiation — and the hypothesis it then
/// owes has that seed substituted throughout, including inside the tower and
/// the stages that `bnd` mentions. Passing `Term::var(st.seed)` gives the
/// hypothesis exactly as [`tower_closed_bnd`] states it.
pub fn fin_bnd(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    seed: &Term,
    a: &Term,
    b: &Term,
) -> Formula {
    // `A` and `B` go in *after* the seed, as placeholders, so that a caller
    // whose `A` or `B` happens to mention `st.seed` is not silently rewritten.
    let (av, pa, pb) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tpa, tpb) = (Term::var(av), Term::var(pa), Term::var(pb));
    let sv = Term::var(st.seed);
    let k = r.apply(tpb, ta.clone());
    let k_sub = kernel::thm::subset(env, k.clone(), sv.clone());
    let k_bnd = super::bounded::bnd(env, r, st, &k);
    let base = Formula::and(
        kernel::thm::subset(env, tpa.clone(), sv),
        Formula::forall(av, Formula::imp(Formula::mem(ta, tpa), Formula::and(k_sub, k_bnd))),
    );
    base.subst(st.seed, seed).subst(pa, a).subst(pb, b)
}

/// `⊢ ∀A ∀B. (Fin⁺(A,B) → closed(A,B,T))` — **the tower over `S` is closed
/// under `sup`**, at the weakest fibre condition that carries the argument.
///
/// `s` must share its [`crate::funcs::Apply`] with `r`, and `st` must have been
/// built over `r`; nothing checks that beyond the syntactic comparisons below,
/// which will fail if it is not so. The three caller-supplied theorems are
/// checked to rest on nothing — a hypothetical one has the same conclusion as
/// the real one and would ride through every `syl` below into a `Γ ⊢` that this
/// function's documentation advertises as a `⊢`.
#[allow(clippy::too_many_arguments)]
pub fn tower_closed_bnd(
    env: &mut Env,
    r: &Rec,
    s: &Sums,
    st: &Stages,
    mem_tower: &Thm,
    sub_in_stage: &Thm,
    pair_in_stage: &Thm,
) -> Option<Thm> {
    if [mem_tower, sub_in_stage, pair_in_stage].iter().any(|t| !t.hyps().is_empty()) {
        return None
    }
    let app_mem = crate::ext::funspace_app_mem(env, &s.ap, &s.prod, &s.fs, &r.app_of_graph)?;
    let fs_pairs = crate::bound::funspace_pairs(env, s)?;

    let om = r.omega();
    let tower = st.tower_set();
    let up = s.ap.sets.up;
    let seed = Term::var(st.seed);

    let (big_a, big_b) = (env.fresh_var(), env.fresh_var());
    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (pv, bv, wv, qv, rv, zv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta_big, tb_big) = (Term::var(big_a), Term::var(big_b));
    let (ta, tf) = (Term::var(av), Term::var(fv));
    let (tp, tb, tw) = (Term::var(pv), Term::var(bv), Term::var(wv));
    let (tq, tr, tz) = (Term::var(qv), Term::var(rv), Term::var(zv));

    let k = r.apply(tb_big.clone(), ta.clone());
    let v0 = st.v(r, r.zero());
    let vp = st.v(r, tp.clone());
    let sp = r.succ_of(tp.clone());
    let ssp = r.succ_of(sp.clone());
    let s3p = r.succ_of(ssp.clone());
    let s4p = r.succ_of(s3p.clone());
    let s5p = r.succ_of(s4p.clone());
    let vssp = st.v(r, ssp.clone());
    let pair_af = opair(up, ta.clone(), tf.clone());
    let goal = Formula::mem(pair_af.clone(), tower.clone());

    // ── The hypothesis ──────────────────────────────────────────────────────
    let a_sub_s = kernel::thm::subset(env, ta_big.clone(), seed.clone());
    let k_sub_s = kernel::thm::subset(env, k.clone(), seed.clone());
    let k_bnd = super::bounded::bnd(env, r, st, &k);
    let a_in = Formula::mem(ta.clone(), ta_big.clone());
    let fib = Formula::forall(
        av,
        Formula::imp(a_in.clone(), Formula::and(k_sub_s.clone(), k_bnd.clone())),
    );
    let h = Formula::and(a_sub_s.clone(), fib.clone());

    // ── J1 := H ∧ a ∈ A ─────────────────────────────────────────────────────
    let j1 = Formula::and(h.clone(), a_in.clone());
    let j1_h = and_left(h.clone(), a_in.clone());
    let j1_a = and_right(h.clone(), a_in.clone());
    let j1_asub = syl(&j1_h, &and_left(a_sub_s.clone(), fib.clone()))?;
    let j1_fib = hyp_mp(
        &hyp_inst(&syl(&j1_h, &and_right(a_sub_s.clone(), fib.clone()))?, std::slice::from_ref(&ta))?,
        &j1_a,
    )?;
    let j1_ksub = syl(&j1_fib, &and_left(k_sub_s.clone(), k_bnd.clone()))?;
    let j1_kbnd = syl(&j1_fib, &and_right(k_sub_s.clone(), k_bnd.clone()))?;

    // ── J2 := J1 ∧ f ∈ fs(B(a), T) ──────────────────────────────────────────
    let f_in = Formula::mem(tf.clone(), s.fs.of(k.clone(), tower.clone()));
    let j2 = Formula::and(j1.clone(), f_in.clone());
    let j2_j1 = and_left(j1.clone(), f_in.clone());
    let j2_f = and_right(j1.clone(), f_in.clone());

    // Every value of `f` is in `T`, from the function space alone.
    let app_at = inst_all(&app_mem, &[k.clone(), tower.clone(), tf.clone(), tb.clone()])?;
    let j2_at_b = syl(&j2_f, &curry(&app_at)?)?;
    let hf_body = Formula::imp(
        Formula::mem(tb.clone(), k.clone()),
        Formula::mem(r.apply(tf.clone(), tb.clone()), tower.clone()),
    );
    let j2_hf =
        Thm::mp(&Thm::ax_dist(bv, j2.clone(), hf_body.clone())?, &Thm::gen(bv, &j2_at_b))?;

    // Finite branching: one stage holds all of them. This is the *only* place
    // the fibre condition is used, which is what makes `bnd(B(a))` the weakest
    // hypothesis that carries the proof.
    let j2_bnd = syl(&j2_j1, &j1_kbnd)?;
    let j2_ex = hyp_mp(&hyp_inst(&j2_bnd, std::slice::from_ref(&tf))?, &j2_hf)?;

    let c_p = Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tb.clone(), k.clone()),
            Formula::mem(r.apply(tf.clone(), tb.clone()), vp.clone()),
        ),
    );
    let p_om = Formula::mem(tp.clone(), om.clone());
    let e1 = Formula::and(p_om.clone(), c_p.clone());
    if *j2_ex.concl() != Formula::imp(j2.clone(), Formula::exists(pv, e1.clone())) {
        return None
    }

    // ── J3 := J2 ∧ (p ∈ ω ∧ ∀b ∈ B(a). f(b) ∈ Vₚ) ───────────────────────────
    let j3 = Formula::and(j2.clone(), e1.clone());
    let j3_j2 = and_left(j2.clone(), e1.clone());
    let j3_e1 = and_right(j2.clone(), e1.clone());
    let j3_p = syl(&j3_e1, &and_left(p_om.clone(), c_p.clone()))?;
    let j3_c = syl(&j3_e1, &and_right(p_om, c_p.clone()))?;

    // ── J4 := J3 ∧ w ∈ f — reading a member of `f` apart ─────────────────────
    let w_in_f = Formula::mem(tw.clone(), tf.clone());
    let j4 = Formula::and(j3.clone(), w_in_f.clone());
    let j4_j3 = and_left(j3.clone(), w_in_f.clone());
    let j4_w = and_right(j3.clone(), w_in_f.clone());
    let j4_f = syl(&j4_j3, &syl(&j3_j2, &j2_f)?)?;

    let pairs_at = inst_all(&fs_pairs, &[k.clone(), tower.clone(), tf.clone()])?;
    let j4_pairs = hyp_mp(&hyp_inst(&syl(&j4_f, &pairs_at)?, std::slice::from_ref(&tw))?, &j4_w)?;

    let pair_qr = opair(up, tq.clone(), tr.clone());
    let r_in_t = Formula::mem(tr.clone(), tower.clone());
    let w_eq = Formula::eq(tw.clone(), pair_qr.clone());
    let inner_r = Formula::and(r_in_t.clone(), w_eq.clone());
    let q_in_k = Formula::mem(tq.clone(), k.clone());
    let ex_r = Formula::exists(rv, inner_r.clone());
    let e2 = Formula::and(q_in_k.clone(), ex_r.clone());
    if *j4_pairs.concl() != Formula::imp(j4.clone(), Formula::exists(qv, e2.clone())) {
        return None
    }

    // ── J5 := J4 ∧ e2,  J6 := J5 ∧ (r ∈ T ∧ w = ⟨q,r⟩) ──────────────────────
    let j5 = Formula::and(j4.clone(), e2.clone());
    let j5_j4 = and_left(j4.clone(), e2.clone());
    let j5_e2 = and_right(j4.clone(), e2.clone());
    let j5_q = syl(&j5_e2, &and_left(q_in_k.clone(), ex_r.clone()))?;
    let j5_ex_r = syl(&j5_e2, &and_right(q_in_k, ex_r))?;

    let j6 = Formula::and(j5.clone(), inner_r.clone());
    let j6_j5 = and_left(j5.clone(), inner_r.clone());
    let j6_inner = and_right(j5.clone(), inner_r.clone());
    let j6_eq = syl(&j6_inner, &and_right(r_in_t.clone(), w_eq.clone()))?;
    let j6_j4 = syl(&j6_j5, &j5_j4)?;
    let j6_j3 = syl(&j6_j4, &j4_j3)?;
    let j6_j2 = syl(&j6_j3, &j3_j2)?;
    let j6_q = syl(&j6_j5, &j5_q)?;
    let j6_f = syl(&j6_j4, &j4_f)?;

    // `q ∈ B(a) ⊆ S = V₀ ⊆ Vₚ`.
    let s_eq_v0 = eq_symm(env, &st.rec.base)?;
    let into_v0 = |t: &Term| {
        Thm::mp(
            &Thm::eq_leibniz(
                seed.clone(),
                v0.clone(),
                zv,
                Formula::mem(t.clone(), tz.clone()),
            ),
            &s_eq_v0,
        )
    };
    let j6_ksub = syl(&j6_j2, &syl(&j2_j1, &j1_ksub)?)?;
    let j6_qs = hyp_mp(&hyp_inst(&j6_ksub, std::slice::from_ref(&tq))?, &j6_q)?;
    let j6_qv0 = hyp_mp(&a1i(&into_v0(&tq)?, j6.clone()), &j6_qs)?;
    let j6_pom = syl(&j6_j3, &j3_p)?;
    let j6_zl = hyp_mp(&a1i(&inst_all(&st.zero_least, std::slice::from_ref(&tp))?, j6.clone()), &j6_pom)?;
    let j6_qvp = hyp_mp(&hyp_inst(&j6_zl, std::slice::from_ref(&tq))?, &j6_qv0)?;

    // `r = f(q) ∈ Vₚ`, through single-valuedness.
    let j6_wf = syl(&j6_j4, &j4_w)?;
    let to_pair = hyp_leibniz(&j6_eq, zv, &Formula::mem(tz.clone(), tf.clone()))?;
    let j6_pf = hyp_mp(&to_pair, &j6_wf)?;

    let fs_ax_at = inst_all(&s.fs.fs_ax, &[k.clone(), tower.clone(), tf.clone()])?;
    let to_isfun = iff_mp(&fs_ax_at)?;
    let (_, isfun) = to_isfun.concl().as_imp()?;
    let (sub_prod, graph) = split_and(&isfun)?;
    let (total, sv) = split_and(&graph)?;
    if sv != crate::funspace::is_single_valued(env, &s.ap.sets, &tf) {
        return None
    }
    let j6_sv = syl(
        &syl(&j6_f, &to_isfun)?,
        &syl(&and_right(sub_prod, graph.clone()), &and_right(total, sv))?,
    )?;

    let aog = inst_all(&r.app_of_graph, &[tf.clone(), tq.clone(), tr.clone()])?;
    let j6_appeq = hyp_mp(&hyp_mp(&a1i(&curry(&aog)?, j6.clone()), &j6_sv)?, &j6_pf)?;
    let j6_cp = syl(&j6_j3, &j3_c)?;
    let j6_appvp = hyp_mp(&hyp_inst(&j6_cp, std::slice::from_ref(&tq))?, &j6_q)?;
    let j6_rvp = hyp_mp(
        &hyp_leibniz(&j6_appeq, zv, &Formula::mem(tz.clone(), vp.clone()))?,
        &j6_appvp,
    )?;

    // Both components in `Vₚ`, so the pair — and hence `w` — is in `V₍succ² p₎`.
    let pis_at = inst_all(pair_in_stage, std::slice::from_ref(&tp))?;
    let j6_pis = hyp_inst(
        &hyp_mp(&a1i(&pis_at, j6.clone()), &j6_pom)?,
        &[tq.clone(), tr.clone()],
    )?;
    let j6_pair_in = hyp_mp(&j6_pis, &hyp_and(&j6_qvp, &j6_rvp)?)?;
    let j6_eqs = syl(&j6_eq, &eq_symm_imp(env, tw.clone(), pair_qr.clone()))?;
    let j6_wv = hyp_mp(
        &hyp_leibniz(&j6_eqs, zv, &Formula::mem(tz.clone(), vssp.clone()))?,
        &j6_pair_in,
    )?;

    // ── Discharge `r`, then `q`; `f` is a subset of one stage ───────────────
    let j5_wv = discharge(rv, &j5_ex_r, &j6_wv)?;
    let j4_wv = discharge(qv, &j4_pairs, &j5_wv)?;
    let j3_sub = Thm::mp(
        &Thm::ax_dist(
            wv,
            j3.clone(),
            Formula::imp(w_in_f, Formula::mem(tw.clone(), vssp.clone())),
        )?,
        &Thm::gen(wv, &curry(&j4_wv)?),
    )?;
    if *j3_sub.concl()
        != Formula::imp(j3.clone(), kernel::thm::subset(env, tf.clone(), vssp.clone()))
    {
        return None
    }

    // ── Up the stages: `f`, then `a`, then the pair, then the tower ─────────
    let up_one = |h_om: &Thm, t: &Term| -> Option<Thm> {
        hyp_mp(&a1i(&inst_all(&r.core().succ_closed, std::slice::from_ref(t))?, j3.clone()), h_om)
    };
    let j3_sp = up_one(&j3_p, &tp)?;
    let j3_ssp = up_one(&j3_sp, &sp)?;
    let j3_s3p = up_one(&j3_ssp, &ssp)?;
    let j3_s4p = up_one(&j3_s3p, &s3p)?;
    let j3_s5p = up_one(&j3_s4p, &s4p)?;

    let sis_at = inst_all(sub_in_stage, std::slice::from_ref(&ssp))?;
    let j3_fin = hyp_mp(
        &hyp_inst(&hyp_mp(&a1i(&sis_at, j3.clone()), &j3_ssp)?, std::slice::from_ref(&tf))?,
        &j3_sub,
    )?;

    let j3_a = syl(&j3_j2, &syl(&j2_j1, &j1_a)?)?;
    let j3_asub = syl(&j3_j2, &syl(&j2_j1, &j1_asub)?)?;
    let j3_as = hyp_mp(&hyp_inst(&j3_asub, std::slice::from_ref(&ta))?, &j3_a)?;
    let j3_av0 = hyp_mp(&a1i(&into_v0(&ta)?, j3.clone()), &j3_as)?;
    let j3_zl3 = hyp_mp(&a1i(&inst_all(&st.zero_least, std::slice::from_ref(&s3p))?, j3.clone()), &j3_s3p)?;
    let j3_a_in = hyp_mp(&hyp_inst(&j3_zl3, std::slice::from_ref(&ta))?, &j3_av0)?;

    let pis3 = inst_all(pair_in_stage, std::slice::from_ref(&s3p))?;
    let j3_pair = hyp_mp(
        &hyp_inst(
            &hyp_mp(&a1i(&pis3, j3.clone()), &j3_s3p)?,
            &[ta.clone(), tf.clone()],
        )?,
        &hyp_and(&j3_a_in, &j3_fin)?,
    )?;
    let mt = inst_all(mem_tower, std::slice::from_ref(&s5p))?;
    let j3_goal = hyp_mp(
        &hyp_inst(&hyp_mp(&a1i(&mt, j3.clone()), &j3_s5p)?, std::slice::from_ref(&pair_af))?,
        &j3_pair,
    )?;
    if *j3_goal.concl() != Formula::imp(j3, goal.clone()) {
        return None
    }

    // ── Discharge the stage, then close the two quantifiers ─────────────────
    let j2_goal = discharge(pv, &j2_ex, &j3_goal)?;
    let all_f = Formula::forall(fv, Formula::imp(f_in.clone(), goal.clone()));
    let j1_all_f = Thm::mp(
        &Thm::ax_dist(fv, j1.clone(), Formula::imp(f_in, goal))?,
        &Thm::gen(fv, &curry(&j2_goal)?),
    )?;
    let out = Thm::mp(
        &Thm::ax_dist(av, h.clone(), Formula::imp(a_in.clone(), all_f.clone()))?,
        &Thm::gen(av, &curry(&j1_all_f)?),
    )?;

    let expected = crate::wtype::closed(env, s, &ta_big, &tb_big, &tower);
    if *out.concl() != Formula::imp(h, expected) {
        return None
    }
    Some(gen_all(&[big_a, big_b], &out))
}

/// `⊢ ∀A ∀B. ((A ⊆ S ∧ ∀a. (a ∈ A → (B(a) ⊆ S ∧ B(a) ∈ ω))) → closed(A,B,T))`
/// — [`tower_closed_bnd`] at the fibre condition [`crate::wnat`] and
/// [`crate::enums`] satisfy.
///
/// The whole content is [`mod@super::bounded`] under a `∀a` and inside a
/// conjunction: `B(a) ∈ ω → bnd(B(a))`, so the `∈ ω` hypothesis is *stronger*
/// than the one the derivation needs and the implication composes.
///
/// `general` must be [`tower_closed_bnd`] over the same `st`, and `bounded`
/// must be [`mod@super::bounded`] over the same `r` and `st`. Both are pinned by
/// conclusion — `general`'s implicitly, since the antecedent this function
/// builds has to match it exactly — and both are checked to rest on nothing.
pub fn tower_closed(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    general: &Thm,
    bounded: &Thm,
) -> Option<Thm> {
    if !general.hyps().is_empty() || !bounded.hyps().is_empty() {
        return None
    }
    let om = r.omega();
    let seed = Term::var(st.seed);
    let (big_a, big_b, av) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta_big, tb_big, ta) = (Term::var(big_a), Term::var(big_b), Term::var(av));

    // `bounded` at its exact statement: `∀k. (k ∈ ω → bnd(k))`.
    let kv = env.fresh_var();
    let tk = Term::var(kv);
    if *bounded.concl()
        != Formula::forall(
            kv,
            Formula::imp(Formula::mem(tk.clone(), om.clone()), super::bounded::bnd(env, r, st, &tk)),
        )
    {
        return None
    }

    let general_at = inst_all(general, &[ta_big.clone(), tb_big.clone()])?;
    let (fin_bnd, concl) = general_at.concl().as_imp()?;

    let k = r.apply(tb_big.clone(), ta.clone());
    let k_sub_s = kernel::thm::subset(env, k.clone(), seed.clone());
    let k_om = Formula::mem(k.clone(), om.clone());
    let a_in = Formula::mem(ta.clone(), ta_big.clone());

    // `(B(a) ⊆ S ∧ B(a) ∈ ω) → (B(a) ⊆ S ∧ bnd(B(a)))`, then under `a ∈ A →`
    // and under `∀a`.
    let strengthen = hyp_and(
        &and_left(k_sub_s.clone(), k_om.clone()),
        &syl(
            &and_right(k_sub_s.clone(), k_om.clone()),
            &inst_all(bounded, std::slice::from_ref(&k))?,
        )?,
    )?;
    let under_a = crate::imp_mono_r(&strengthen, a_in.clone())?;
    let under_all = crate::forall_mono(av, &Thm::gen(av, &under_a))?;

    let a_sub_s = kernel::thm::subset(env, ta_big.clone(), seed);
    let fib_om = Formula::forall(av, Formula::imp(a_in, Formula::and(k_sub_s, k_om)));
    let h = Formula::and(a_sub_s.clone(), fib_om.clone());
    let weaken = hyp_and(
        &and_left(a_sub_s.clone(), fib_om.clone()),
        &syl(&and_right(a_sub_s, fib_om), &under_all)?,
    )?;
    if *weaken.concl() != Formula::imp(h.clone(), fin_bnd) {
        return None
    }
    let out = syl(&weaken, &general_at)?;
    if *out.concl() != Formula::imp(h, concl) || !out.hyps().is_empty() {
        return None
    }
    Some(gen_all(&[big_a, big_b], &out))
}
