//! Kuratowski ordered pairs: the injectivity lemma.
//!
//! `⟨a,b⟩ = upair(upair(a,a), upair(a,b))` is built in the parent module as a
//! pure term composition. What is *not* free is its characteristic property,
//! that the pair determines its components. That lemma is derived here.
//!
//! The first half — that the pair determines its *first* component — lives in
//! the parent module as [`crate::opair_fst`]. The second half is harder,
//! because the second component is not pinned down by a single membership
//! step: `{a,b} ∈ ⟨c,d⟩` leaves two possibilities, and the degenerate one
//! (`{a,b}` a singleton) has to be closed off by looking at `⟨c,d⟩`'s *other*
//! member as well. So the derivation below is a case analysis nested two deep,
//! and everything runs under a conjunction of hypotheses, in the `⊢ H → φ`
//! style that [`crate::hyp_mp`] supports.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{
    a1i, and_left, and_right, eq_symm_imp, gen_all, hyp_and, hyp_mp, hyp_or_elim, iff_mp, imp_refl,
    inst_all, mpd_const, opair, singleton, syl, uncurry, upair_members,
};

// ─────────────────────────────────────────────────────────────────────────────
// Small implication-form equality steps.
//
// Every equation in the derivation below is *hypothetical* — it holds only
// under `H` — so the equality toolkit in the parent module, which consumes
// proved equations, does not apply. What is needed instead is each rewrite in
// implication form, which is Leibniz used directly.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ u = v → (t ∈ u → t ∈ v)` — carry a membership across an equation.
fn carry_mem(env: &mut Env, t: Term, u: Term, v: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(u, v, w, Formula::mem(t, Term::var(w)))
}

/// `⊢ u = v → (t = u → t = v)` — rewrite the right-hand side of an equation.
fn carry_eq_rhs(env: &mut Env, t: Term, u: Term, v: Term) -> Thm {
    let w = env.fresh_var();
    Thm::eq_leibniz(u, v, w, Formula::eq(t, Term::var(w)))
}

/// `⊢ u = v → {u} = {v}` — congruence for the singleton, in implication form.
///
/// `{u}` is `upair(u,u)`, so the two occurrences of `u` are abstracted at once
/// and the reflexivity `{u} = {u}` discharges the antecedent.
fn sing_congr_imp(env: &mut Env, up: FnSym, u: Term, v: Term) -> Thm {
    let w = env.fresh_var();
    let su = singleton(up, u.clone());
    let hole = Formula::eq(su.clone(), Term::apply(up, vec![Term::var(w), Term::var(w)]));
    let leib = Thm::eq_leibniz(u, v, w, hole);
    mpd_const(&leib, &Thm::eq_refl(su)).expect("sing_congr_imp: reflexivity discharges the antecedent")
}

/// From `⊢ t ∈ p` infer `⊢ p = {s} → t = s`.
///
/// The workhorse of the degenerate cases: whenever a two-element set turns out
/// to be a singleton, each of its members is forced to be that singleton's
/// element.
fn eq_singleton_elim(env: &mut Env, up: FnSym, mem_sing: &Thm, t_in_p: &Thm, s: Term) -> Option<Thm> {
    let (t, p) = t_in_p.concl().as_mem()?;
    let carry = carry_mem(env, t.clone(), p, singleton(up, s.clone()));
    // ⊢ p = {s} → t ∈ {s}
    let to_mem = mpd_const(&carry, t_in_p)?;
    // ⊢ t ∈ {s} ↔ t = s
    let ms = inst_all(mem_sing, &[s, t])?;
    syl(&to_mem, &iff_mp(&ms)?)
}

/// From `⊢ H → x = z` and `⊢ H → y = z` infer `⊢ H → x = y`.
fn eq_bridge(env: &mut Env, h_xz: &Thm, h_yz: &Thm) -> Option<Thm> {
    let (h, xz) = h_xz.concl().as_imp()?;
    let (x, z) = xz.as_eq()?;
    let (h2, yz) = h_yz.concl().as_imp()?;
    let (y, z2) = yz.as_eq()?;
    if h != h2 || z != z2 {
        return None
    }
    // ⊢ H → z = y, then Leibniz turns `x = z` into `x = y`.
    let h_zy = syl(h_yz, &eq_symm_imp(env, y.clone(), z.clone()))?;
    let leib = carry_eq_rhs(env, x, z, y);
    hyp_mp(&hyp_mp(&a1i(&leib, h), &h_zy)?, h_xz)
}

/// From `⊢ K → φ` infer `⊢ (K ∧ E) → φ` — move a fact into a larger context.
fn weaken(t: &Thm, e: Formula) -> Option<Thm> {
    let (k, _) = t.concl().as_imp()?;
    syl(&and_left(k, e), t)
}

// ─────────────────────────────────────────────────────────────────────────────
// The lemmas.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → b = d)` — the second component of the
/// Kuratowski pair is determined.
///
/// Companion to [`crate::opair_fst`], and the harder half. Writing `H` for the
/// equation, the argument is:
///
/// `{a,b} ∈ ⟨a,b⟩`, so `H` carries it into `⟨c,d⟩ = {{c},{c,d}}` and either
/// `{a,b} = {c}` or `{a,b} = {c,d}`.
///
/// * `{a,b} = {c}`: then `b = c`, and also `a = c`, so `{a} = {c} = {a,b}`.
///   Now `{c,d} ∈ ⟨c,d⟩`, which `H` carries back into `⟨a,b⟩`, so `{c,d}` is
///   `{a}` or `{a,b}` — both equal to `{c}`. Hence `{c,d} = {c}`, so `d = c`,
///   and `b = c = d`.
/// * `{a,b} = {c,d}`: then `b ∈ {c,d}`, so `b = c` or `b = d`. The second is
///   the goal. In the first, [`crate::opair_fst`] supplies `a = c`, so
///   `{c,d} = {a,b} = {c,c} = {c}`, giving `d = c = b`.
///
/// `sing_inj` is not needed: where `opair_fst` uses singleton injectivity to
/// extract `a = c`, here that fact is imported wholesale from `opair_fst`
/// itself.
pub fn opair_snd(env: &mut Env, up: FnSym, up_ax: &Thm, mem_sing: &Thm, opair_fst_thm: &Thm) -> Option<Thm> {
    let (a, b, c, d) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(a), Term::var(b), Term::var(c), Term::var(d));

    let (sa, sc) = (singleton(up, ta.clone()), singleton(up, tc.clone()));
    let ab = Term::apply(up, vec![ta.clone(), tb.clone()]);
    let cd = Term::apply(up, vec![tc.clone(), td.clone()]);
    let (pab, pcd) = (opair(up, ta.clone(), tb.clone()), opair(up, tc.clone(), td.clone()));

    let h = Formula::eq(pab.clone(), pcd.clone());
    let goal = Formula::eq(tb.clone(), td.clone());

    // ⊢ H → a = c, imported.
    let h_ac = inst_all(opair_fst_thm, &[ta.clone(), tb.clone(), tc.clone(), td.clone()])?;
    debug_assert_eq!(
        *h_ac.concl(),
        Formula::imp(h.clone(), Formula::eq(ta.clone(), tc.clone())),
        "opair_snd: opair_fst has an unexpected shape"
    );

    // The four membership facts the argument leans on.
    let (_, ab_in_pab) = upair_members(up_ax, &sa, &ab)?; // ⊢ {a,b} ∈ ⟨a,b⟩
    let (_, cd_in_pcd) = upair_members(up_ax, &sc, &cd)?; // ⊢ {c,d} ∈ ⟨c,d⟩
    let (_, b_in_ab) = upair_members(up_ax, &ta, &tb)?; // ⊢ b ∈ {a,b}
    let (_, d_in_cd) = upair_members(up_ax, &tc, &td)?; // ⊢ d ∈ {c,d}

    // ⊢ {c,d} = {c} → d = c. Used in both cases; the whole derivation is really
    // a hunt for a proof of `{c,d} = {c}`.
    let cd_to_dc = eq_singleton_elim(env, up, mem_sing, &d_in_cd, tc.clone())?;

    // ⊢ H → ({a,b} = {c} ∨ {a,b} = {c,d})
    let carry_ab = carry_mem(env, ab.clone(), pab.clone(), pcd.clone());
    let h_ab_in_pcd = hyp_mp(&carry_ab, &a1i(&ab_in_pab, h.clone()))?;
    let pcd_members = inst_all(up_ax, &[sc.clone(), cd.clone(), ab.clone()])?;
    let h_disj = syl(&h_ab_in_pcd, &iff_mp(&pcd_members)?)?;

    // ⊢ H → ({c,d} = {a} ∨ {c,d} = {a,b}), the same step run backwards along the
    // equation.
    let h_symm = eq_symm_imp(env, pab.clone(), pcd.clone());
    let carry_cd = carry_mem(env, cd.clone(), pcd.clone(), pab.clone());
    let h_cd_in_pab = syl(&h_symm, &mpd_const(&carry_cd, &cd_in_pcd)?)?;
    let pab_members = inst_all(up_ax, &[sa.clone(), ab.clone(), cd.clone()])?;
    let h_disj2 = syl(&h_cd_in_pab, &iff_mp(&pab_members)?)?;

    // ── Case 1: {a,b} = {c} ──────────────────────────────────────────────────
    // Work under K₁ := H ∧ ({a,b} = {c}) and `uncurry` at the end, since this
    // case needs the equation as well as the case assumption.
    let e1 = Formula::eq(ab.clone(), sc.clone());
    let k1 = Formula::and(h.clone(), e1.clone());
    let k1_e1 = and_right(h.clone(), e1.clone());

    let ab_to_bc = eq_singleton_elim(env, up, mem_sing, &b_in_ab, tc.clone())?;
    let k1_bc = syl(&k1_e1, &ab_to_bc)?; // K₁ → b = c
    let k1_ac = weaken(&h_ac, e1.clone())?; // K₁ → a = c
    let k1_sa_sc = syl(&k1_ac, &sing_congr_imp(env, up, ta.clone(), tc.clone()))?; // K₁ → {a} = {c}

    // Both members of ⟨a,b⟩ are `{c}` here, so either disjunct pins {c,d} down.
    let l_sa = carry_eq_rhs(env, cd.clone(), sa.clone(), sc.clone());
    let sub_left = hyp_mp(&a1i(&l_sa, k1.clone()), &k1_sa_sc)?;
    let l_ab = carry_eq_rhs(env, cd.clone(), ab.clone(), sc.clone());
    let sub_right = hyp_mp(&a1i(&l_ab, k1.clone()), &k1_e1)?;
    let k1_cd_sc = hyp_or_elim(&weaken(&h_disj2, e1.clone())?, &sub_left, &sub_right)?;

    let k1_dc = syl(&k1_cd_sc, &cd_to_dc)?; // K₁ → d = c
    let case1 = uncurry(&eq_bridge(env, &k1_bc, &k1_dc)?)?;
    debug_assert_eq!(
        *case1.concl(),
        Formula::imp(h.clone(), Formula::imp(e1, goal.clone())),
        "opair_snd: case 1 has an unexpected shape"
    );

    // ── Case 2: {a,b} = {c,d} ────────────────────────────────────────────────
    let e2 = Formula::eq(ab.clone(), cd.clone());
    let k2 = Formula::and(h.clone(), e2.clone());
    let k2_e2 = and_right(h.clone(), e2.clone());

    // K₂ → (b = c ∨ b = d)
    let carry_b = carry_mem(env, tb.clone(), ab.clone(), cd.clone());
    let e2_b_in_cd = mpd_const(&carry_b, &b_in_ab)?;
    let cd_members = inst_all(up_ax, &[tc.clone(), td.clone(), tb.clone()])?;
    let k2_disj = syl(&k2_e2, &syl(&e2_b_in_cd, &iff_mp(&cd_members)?)?)?;

    // Right disjunct: b = d is the goal already.
    let case_bd = a1i(&imp_refl(goal.clone()), k2.clone());

    // Left disjunct: b = c collapses {c,d} to {c}. Descend into K₃ := K₂ ∧ (b = c).
    let bc = Formula::eq(tb.clone(), tc.clone());
    let k3 = Formula::and(k2.clone(), bc.clone());
    let k3_bc = and_right(k2.clone(), bc.clone());
    let k3_e2 = weaken(&k2_e2, bc.clone())?;
    let k3_ac = weaken(&weaken(&h_ac, e2.clone())?, bc.clone())?;

    // K₃ → {c,d} = {a,b}, then rewrite a ↦ c and b ↦ c to reach {c,d} = {c}.
    let k3_cd_ab = syl(&k3_e2, &eq_symm_imp(env, ab.clone(), cd.clone()))?;
    let w1 = env.fresh_var();
    let leib_a = Thm::eq_leibniz(
        ta.clone(),
        tc.clone(),
        w1,
        Formula::eq(cd.clone(), Term::apply(up, vec![Term::var(w1), tb.clone()])),
    );
    let k3_cd_cb = hyp_mp(&hyp_mp(&a1i(&leib_a, k3.clone()), &k3_ac)?, &k3_cd_ab)?;
    let w2 = env.fresh_var();
    let leib_b = Thm::eq_leibniz(
        tb.clone(),
        tc.clone(),
        w2,
        Formula::eq(cd.clone(), Term::apply(up, vec![tc.clone(), Term::var(w2)])),
    );
    let k3_cd_sc = hyp_mp(&hyp_mp(&a1i(&leib_b, k3), &k3_bc)?, &k3_cd_cb)?;

    let k3_dc = syl(&k3_cd_sc, &cd_to_dc)?; // K₃ → d = c
    let case_bc = uncurry(&eq_bridge(env, &k3_bc, &k3_dc)?)?;

    let case2 = uncurry(&hyp_or_elim(&k2_disj, &case_bc, &case_bd)?)?;
    debug_assert_eq!(
        *case2.concl(),
        Formula::imp(h.clone(), Formula::imp(e2, goal.clone())),
        "opair_snd: case 2 has an unexpected shape"
    );

    let out = hyp_or_elim(&h_disj, &case1, &case2)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, goal), "opair_snd: unexpected shape");
    Some(gen_all(&[a, b, c, d], &out))
}

/// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → (a = c ∧ b = d))` — the characteristic
/// property of the Kuratowski pair.
///
/// Both halves are already available; all that remains is to instantiate them
/// at a common quadruple and conjoin them under the shared hypothesis.
pub fn opair_inj(env: &mut Env, up: FnSym, opair_fst_thm: &Thm, opair_snd_thm: &Thm) -> Option<Thm> {
    let (a, b, c, d) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tc, td) = (Term::var(a), Term::var(b), Term::var(c), Term::var(d));
    let args = [ta.clone(), tb.clone(), tc.clone(), td.clone()];

    let h_ac = inst_all(opair_fst_thm, &args)?;
    let h_bd = inst_all(opair_snd_thm, &args)?;
    let out = hyp_and(&h_ac, &h_bd)?;

    // `up` appears nowhere else: the conclusion is assembled entirely out of
    // the two theorems handed in, so this comparison is the only thing that
    // makes the result a statement about the *caller's* pairing. Two halves
    // built over a second `upair` compose just as well and would be returned
    // under this one's name.
    if !opair_fst_thm.hyps().is_empty()
        || !opair_snd_thm.hyps().is_empty()
        || *out.concl()
            != Formula::imp(
                Formula::eq(
                    opair(up, ta.clone(), tb.clone()),
                    opair(up, tc.clone(), td.clone()),
                ),
                Formula::and(Formula::eq(ta, tc), Formula::eq(tb, td)),
            )
    {
        return None
    }
    Some(gen_all(&[a, b, c, d], &out))
}
