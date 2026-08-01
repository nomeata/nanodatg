//! Separation, derived from Replacement.
//!
//! # Interface
//!
//! For an element variable `x` which `psi` may mention, and a set term `a` which
//! must not:
//!
//! ```text
//! ⊢ ∃!y. ((ψ ∧ y = x) ∨ (¬ψ ∧ y = d))                       [cond_relation_unique]
//! ⊢ (∃x. (x ∈ A ∧ ψ)) → ∃s ∀x. (x ∈ s ↔ (x ∈ A ∧ ψ))        [separation_nonempty]
//! ⊢ ∃s ∀x. (x ∈ s ↔ (x ∈ A ∧ ψ))                            [separation_full]
//! ```
//!
//! **[`separation_full`] is unconditional and is what callers should reach
//! for.** [`separation_nonempty`] is kept as the half that needs no empty set.
//! Callers need none of the derivations below.
//!
//! # Why Replacement, and where the antecedent came from
//!
//! Separation is not an axiom here; it has to come from Replacement. The
//! standard derivation replaces the predicate `ψ` by the *total* relation
//!
//! ```text
//! φ(x, y)  :=  (ψ(x) ∧ y = x) ∨ (¬ψ(x) ∧ y = d)
//! ```
//!
//! which is functional for every `x` whatever ([`cond_relation_unique`], which
//! holds with no side condition at all), so Replacement applies and its image is
//! `{x ∈ A : ψ(x)} ∪ {d}`. Choosing `d` to be a witness — an element of `A` that
//! already satisfies `ψ` — makes the spurious element harmless and the image
//! exactly the wanted set.
//!
//! That is why [`separation_nonempty`] is *conditional on the separated set
//! being inhabited*: without a witness there is no harmless `d`. The other case
//! needs a set with no members to hand back, i.e. it needs `∅` — which was not
//! obtainable from the axioms this kernel had. Pairing, Union, Power and
//! Replacement all send inhabited sets to inhabited sets, and Regularity only
//! produces an ∈-minimal *element* of a set one already has. (A nonempty
//! transitive set would do it — Regularity on one yields `∅` immediately — but
//! building a transitive set is the same problem again.)
//!
//! `crate::empty::empty` supplies it. [`separation_full`] takes the inhabited case
//! from [`separation_nonempty`], answers the vacuous one with `∅` itself, and
//! glues the two with [`crate::funcs::cases`] — so Separation is unconditional.
//! The empty set is **consumed**: `e` is discharged as the witness of the
//! existential, so it does not appear in the conclusion, and a construction that
//! derives its own `∅` to call this does not thereby drag the symbol into
//! anything downstream.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, com12, contrapos, eq_symm_imp, ex_falso, exists_elim_imp,
    exists_intro_imp, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_or_elim, hyp_or_same,
    imp_refl, inst_all, syl, syl_imp, uncurry,
};
use super::logic::{cases, hyp_mp2, hyp_syl, or_intro_left, or_intro_right};

/// From `⊢ K → φ` infer `⊢ (K ∧ E) → φ`.
fn weaken_l(t: &Thm, e: Formula) -> Option<Thm> {
    let (k, _) = t.concl().as_imp()?;
    syl(&and_left(k, e), t)
}

/// From `⊢ K → ψ`, `⊢ K → (l ∨ r)` and `⊢ K → (r → ¬ψ)` infer `⊢ K → l`.
///
/// The right disjunct is refuted by `ψ`, so the disjunction collapses onto its
/// left half. Spelled out: `¬l` gives `r` gives `¬ψ`, which contradicts `ψ`, so
/// `¬l → ⊥ → l`, and Clavius closes it.
fn or_resolve_left(k_psi: &Thm, k_disj: &Thm, k_r_np: &Thm) -> Option<Thm> {
    let (k, disj) = k_disj.concl().as_imp()?;
    let (nl, r) = disj.as_imp()?;
    let (l, _) = nl.as_imp()?;
    let (_, psi) = k_psi.concl().as_imp()?;

    // K → (¬l → ¬ψ)
    let bridge = a1i(&syl_imp(nl.clone(), r, Formula::not(psi.clone())), k.clone());
    let k_nl_np = hyp_mp(&hyp_mp(&bridge, k_disj)?, k_r_np)?;
    // K → (¬l → ψ), then contradiction, then ex falso, then Clavius.
    let k_nl_psi = syl(k_psi, &Thm::ax_k(psi, nl.clone()))?;
    let k_nl_false = hyp_mp2(&k_nl_np, &k_nl_psi)?;
    let bridge2 = a1i(&syl_imp(nl, Formula::false_(), l.clone()), k.clone());
    let k_nl_l = hyp_mp(&hyp_mp(&bridge2, &k_nl_false)?, &a1i(&ex_falso(l), k))?;
    hyp_or_same(&k_nl_l)
}

/// From `⊢ H → ∀z. (φ(z) ↔ χ(z))` and `⊢ H → ∃s ∀z. (z ∈ s ↔ φ(z))` infer
/// `⊢ H → ∃s ∀z. (z ∈ s ↔ χ(z))`.
///
/// Swapping one membership condition for a provably equivalent one inside an
/// existential is a step every set construction below needs, and each time it
/// costs the same four moves: instantiate under the `∃`, compose the two
/// biconditionals, re-generalise, and re-introduce the `∃`.
///
/// `sv` must be fresh; it names the bound set variable, which is invisible in
/// the result because alpha-equivalent formulas are syntactically equal.
fn retarget(z: FreeVar, sv: FreeVar, h_iff: &Thm, h_ex: &Thm) -> Option<Thm> {
    let (h, all_iff) = h_iff.concl().as_imp()?;
    let iff_at_z = Thm::ax_inst(all_iff.clone(), Term::var(z))?;
    let (_, iff) = iff_at_z.concl().as_imp()?;
    let (fwd, _) = split_iff(&iff)?;
    let (phi, chi) = fwd.as_imp()?;

    let ts = Term::var(sv);
    let mem_zs = Formula::mem(Term::var(z), ts.clone());
    let p_phi = Formula::forall(z, Formula::iff(mem_zs.clone(), phi));
    let p_chi = Formula::forall(z, Formula::iff(mem_zs.clone(), chi.clone()));
    debug_assert_eq!(
        h_ex.concl().as_imp()?.1,
        Formula::exists(sv, p_phi.clone()),
        "retarget: the existential has an unexpected shape"
    );

    // Under J := H ∧ P_φ(s), chain `z ∈ s ↔ φ(z)` with `φ(z) ↔ χ(z)`.
    let j = Formula::and(h.clone(), p_phi.clone());
    let j_iff1 = syl(&and_right(h.clone(), p_phi.clone()), &Thm::ax_inst(p_phi.clone(), Term::var(z))?)?;
    let j_iff2 = syl(&and_left(h.clone(), p_phi.clone()), &syl(h_iff, &iff_at_z)?)?;
    let j_fwd = hyp_syl(&hyp_iff_mp(&j_iff1)?, &hyp_iff_mp(&j_iff2)?)?;
    let j_bwd = hyp_syl(&hyp_iff_mpr(&j_iff2)?, &hyp_iff_mpr(&j_iff1)?)?;
    let j_iff = hyp_and(&j_fwd, &j_bwd)?;
    let j_q = Thm::mp(&Thm::ax_dist(z, j, Formula::iff(mem_zs, chi))?, &Thm::gen(z, &j_iff))?;

    // ⊢ (∃s. P_φ(s)) → (H → ∃s. P_χ(s)), then feed it the existential we have.
    let ex_chi = Formula::exists(sv, p_chi.clone());
    let h_p_ex = hyp_syl(&uncurry(&j_q)?, &a1i(&exists_intro_imp(sv, p_chi, ts)?, h.clone()))?;
    let elim = exists_elim_imp(sv, &Thm::gen(sv, &com12(&h_p_ex)?), &Formula::imp(h.clone(), ex_chi))?;
    hyp_mp(&syl(h_ex, &elim)?, &imp_refl(h))
}

/// Decompose `φ ↔ ψ` into its two implication halves.
fn split_iff(iff: &Formula) -> Option<(Formula, Formula)> {
    let (inner, _) = iff.as_imp()?;
    let (fwd, nb) = inner.as_imp()?;
    let (bwd, _) = nb.as_imp()?;
    Some((fwd, bwd))
}

/// The conditional-value relation `(ψ ∧ y = x) ∨ (¬ψ ∧ y = d)`.
fn cond_relation(psi: &Formula, tx: &Term, ty: &Term, td: &Term) -> Formula {
    Formula::or(
        Formula::and(psi.clone(), Formula::eq(ty.clone(), tx.clone())),
        Formula::and(Formula::not(psi.clone()), Formula::eq(ty.clone(), td.clone())),
    )
}

/// `⊢ ∃!y. ((ψ ∧ y = x) ∨ (¬ψ ∧ y = d))`.
///
/// The premise Replacement demands. It holds for *every* `x`, with no side
/// condition at all: the relation is a two-branch case distinction on `ψ(x)`,
/// each branch pinning `y` to a named term, and classical logic says one branch
/// or the other applies.
///
/// `psi` must not mention `y`, and `d` must mention neither `x` nor `y`.
pub fn cond_relation_unique(env: &mut Env, x: FreeVar, psi: &Formula, y: FreeVar, d: &Term) -> Option<Thm> {
    if psi.occurs_free(y) || d.occurs_free(x) || d.occurs_free(y) {
        return None
    }
    let (tx, ty) = (Term::var(x), Term::var(y));
    let phi = cond_relation(psi, &tx, &ty, d);

    // The `∃!` shape the kernel expects, rebuilt with our own fresh variable —
    // alpha-equivalent formulas are syntactically equal, so this matches.
    let target = kernel::thm::exists_unique(env, y, &phi);
    let y2 = env.fresh_var();
    let ty2 = Term::var(y2);
    let phi2 = phi.subst(y, &ty2);
    let uniq = Formula::forall(y2, Formula::imp(phi2.clone(), Formula::eq(ty2.clone(), ty.clone())));
    let exbody = Formula::and(phi.clone(), uniq);
    debug_assert_eq!(Formula::exists(y, exbody.clone()), target, "cond_relation_unique: ∃! shape drift");

    let np = Formula::not(psi.clone());

    // ── ψ holds: the value is `x`. ───────────────────────────────────────────
    let lx = Formula::and(psi.clone(), Formula::eq(tx.clone(), tx.clone()));
    let rx = Formula::and(np.clone(), Formula::eq(tx.clone(), d.clone()));
    let pos_l = hyp_and(&imp_refl(psi.clone()), &a1i(&Thm::eq_refl(tx.clone()), psi.clone()))?;
    let pos_phi = syl(&pos_l, &or_intro_left(lx, rx))?;

    // Uniqueness: under `ψ ∧ φ(x,y₂)` the right disjunct is refuted, so `y₂ = x`.
    let kp = Formula::and(psi.clone(), phi2.clone());
    let kp_r_np = a1i(&and_left(np.clone(), Formula::eq(ty2.clone(), d.clone())), kp.clone());
    let kp_l = or_resolve_left(
        &and_left(psi.clone(), phi2.clone()),
        &and_right(psi.clone(), phi2.clone()),
        &kp_r_np,
    )?;
    let kp_eq = syl(&kp_l, &and_right(psi.clone(), Formula::eq(ty2.clone(), tx.clone())))?;
    let pos_uniq_body = uncurry(&kp_eq)?;
    let dist_p = Thm::ax_dist(y2, psi.clone(), Formula::imp(phi2.clone(), Formula::eq(ty2.clone(), tx.clone())))?;
    let pos_uniq = Thm::mp(&dist_p, &Thm::gen(y2, &pos_uniq_body))?;
    let pos = syl(&hyp_and(&pos_phi, &pos_uniq)?, &exists_intro_imp(y, exbody.clone(), tx.clone())?)?;

    // ── ψ fails: the value is `d`. ───────────────────────────────────────────
    let ld = Formula::and(psi.clone(), Formula::eq(d.clone(), tx.clone()));
    let rd = Formula::and(np.clone(), Formula::eq(d.clone(), d.clone()));
    let neg_r = hyp_and(&imp_refl(np.clone()), &a1i(&Thm::eq_refl(d.clone()), np.clone()))?;
    let neg_phi = syl(&neg_r, &or_intro_right(ld, rd))?;

    // Uniqueness: `¬ψ` refutes the left disjunct outright, so `y₂ = d`.
    let kn_np = and_left(np.clone(), phi2.clone());
    let kn_phi = and_right(np.clone(), phi2.clone());
    let kn_nl = syl(&kn_np, &contrapos(&and_left(psi.clone(), Formula::eq(ty2.clone(), tx.clone())))?)?;
    let kn_r = hyp_mp(&kn_phi, &kn_nl)?;
    let kn_eq = syl(&kn_r, &and_right(np.clone(), Formula::eq(ty2.clone(), d.clone())))?;
    let neg_uniq_body = uncurry(&kn_eq)?;
    let dist_n = Thm::ax_dist(y2, np.clone(), Formula::imp(phi2, Formula::eq(ty2, d.clone())))?;
    let neg_uniq = Thm::mp(&dist_n, &Thm::gen(y2, &neg_uniq_body))?;
    let neg = syl(&hyp_and(&neg_phi, &neg_uniq)?, &exists_intro_imp(y, exbody, d.clone())?)?;

    let out = cases(&pos, &neg)?;
    debug_assert_eq!(*out.concl(), target, "cond_relation_unique: unexpected shape");
    Some(out)
}

/// `⊢ (∃x. (x ∈ A ∧ ψ)) → ∃s ∀x. (x ∈ s ↔ (x ∈ A ∧ ψ))` — Separation, for an
/// inhabited result.
///
/// The element variable is `x`, which `psi` may mention; `a` is the set being
/// carved up and must not mention `x`. The theorem is stated with `x` bound by
/// the leading `∃` and again by the inner `∀`, which is legitimate because the
/// two occurrences are in different scopes and the representation is locally
/// nameless.
///
/// The inhabitation antecedent is not an artefact of the proof — see the note
/// above this section: without a witness the choice relation has no harmless
/// default. [`separation_full`] discharges it with `∅`, and is what callers
/// should reach for; this is kept as the half that needs no empty set.
pub fn separation_nonempty(env: &mut Env, x: FreeVar, psi: &Formula, a: &Term) -> Option<Thm> {
    if a.occurs_free(x) {
        return None
    }
    let tx = Term::var(x);
    let (x0, y) = (env.fresh_var(), env.fresh_var());
    let (tx0, ty) = (Term::var(x0), Term::var(y));

    let psi_x0 = psi.subst(x, &tx0);
    let psi_y = psi.subst(x, &ty);
    // H — the witness hypothesis: `x₀ ∈ A ∧ ψ(x₀)`.
    let h = Formula::and(Formula::mem(tx0.clone(), a.clone()), psi_x0.clone());

    let phi = cond_relation(psi, &tx, &ty, &tx0);
    let exuniq = cond_relation_unique(env, x, psi, y, &tx0)?;

    // ── Replacement at `a := A` ──────────────────────────────────────────────
    let repl = Thm::ax_replacement(env, x, y, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(a))?;
    let premise = Thm::gen(x, &a1i(&exuniq, Formula::mem(tx.clone(), a.clone())));
    let img = Thm::mp(&repl_a, &premise)?; // ⊢ ∃b ∀y. (y ∈ b ↔ E(y))

    // E(y) — the image condition Replacement hands back — and Ψ(y), the
    // condition we want in its place.
    let inner = Formula::and(Formula::mem(tx.clone(), a.clone()), phi.clone());
    let e = Formula::exists(x, inner.clone());
    let target = Formula::and(Formula::mem(ty.clone(), a.clone()), psi_y.clone());

    let np = Formula::not(psi.clone());

    // ── E(y) → Ψ(y), under H ─────────────────────────────────────────────────
    // Work under G := (x ∈ A ∧ φ) ∧ H, then discharge the witness variable.
    let g = Formula::and(inner.clone(), h.clone());
    let mem_xa = Formula::mem(tx.clone(), a.clone());
    let mem_x0a = Formula::mem(tx0.clone(), a.clone());
    let g_left = and_left(inner.clone(), h.clone());
    let g_right = and_right(inner.clone(), h.clone());
    let g_xa = syl(&g_left, &and_left(mem_xa.clone(), phi.clone()))?;
    let g_phi = syl(&g_left, &and_right(mem_xa.clone(), phi.clone()))?;
    let g_x0a = syl(&g_right, &and_left(mem_x0a.clone(), psi_x0.clone()))?;
    let g_psix0 = syl(&g_right, &and_right(mem_x0a, psi_x0))?;

    // Case ψ(x): the relation forces y = x, and x is the good element.
    let g2 = Formula::and(g.clone(), psi.clone());
    let g2_psi = and_right(g.clone(), psi.clone());
    let g2_phi = weaken_l(&g_phi, psi.clone())?;
    let g2_xa = weaken_l(&g_xa, psi.clone())?;
    let g2_r_np = a1i(&and_left(np.clone(), Formula::eq(ty.clone(), tx0.clone())), g2.clone());
    let g2_l = or_resolve_left(&g2_psi, &g2_phi, &g2_r_np)?;
    let g2_yx = syl(&g2_l, &and_right(psi.clone(), Formula::eq(ty.clone(), tx.clone())))?;
    let g2_xy = syl(&g2_yx, &eq_symm_imp(env, ty.clone(), tx.clone()))?;
    let w = env.fresh_var();
    let leib_mem = Thm::eq_leibniz(tx.clone(), ty.clone(), w, Formula::mem(Term::var(w), a.clone()));
    let g2_ya = hyp_mp(&hyp_mp(&a1i(&leib_mem, g2.clone()), &g2_xy)?, &g2_xa)?;
    let leib_psi = Thm::eq_leibniz(tx.clone(), ty.clone(), x, psi.clone());
    let g2_psiy = hyp_mp(&hyp_mp(&a1i(&leib_psi, g2), &g2_xy)?, &g2_psi)?;
    let case_pos = uncurry(&hyp_and(&g2_ya, &g2_psiy)?)?;

    // Case ¬ψ(x): the relation forces y = x₀, and x₀ is the witness.
    let g3 = Formula::and(g.clone(), np.clone());
    let g3_np = and_right(g.clone(), np.clone());
    let g3_phi = weaken_l(&g_phi, np.clone())?;
    let g3_x0a = weaken_l(&g_x0a, np.clone())?;
    let g3_psix0 = weaken_l(&g_psix0, np.clone())?;
    let g3_nl = syl(&g3_np, &contrapos(&and_left(psi.clone(), Formula::eq(ty.clone(), tx.clone())))?)?;
    let g3_r = hyp_mp(&g3_phi, &g3_nl)?;
    let g3_yx0 = syl(&g3_r, &and_right(np.clone(), Formula::eq(ty.clone(), tx0.clone())))?;
    let g3_x0y = syl(&g3_yx0, &eq_symm_imp(env, ty.clone(), tx0.clone()))?;
    let w2 = env.fresh_var();
    let leib_mem2 = Thm::eq_leibniz(tx0.clone(), ty.clone(), w2, Formula::mem(Term::var(w2), a.clone()));
    let g3_ya = hyp_mp(&hyp_mp(&a1i(&leib_mem2, g3.clone()), &g3_x0y)?, &g3_x0a)?;
    let leib_psi2 = Thm::eq_leibniz(tx0.clone(), ty.clone(), x, psi.clone());
    let g3_psiy = hyp_mp(&hyp_mp(&a1i(&leib_psi2, g3), &g3_x0y)?, &g3_psix0)?;
    let case_neg = uncurry(&hyp_and(&g3_ya, &g3_psiy)?)?;

    // `ψ ∨ ¬ψ` is `¬ψ → ¬ψ` in this encoding, so excluded middle is reflexivity.
    let g_disj = a1i(&imp_refl(np.clone()), g.clone());
    let g_goal = hyp_or_elim(&g_disj, &case_pos, &case_neg)?;
    let h_target = Formula::imp(h.clone(), target.clone());
    let fwd = com12(&exists_elim_imp(x, &Thm::gen(x, &uncurry(&g_goal)?), &h_target)?)?;

    // ── Ψ(y) → E(y) ──────────────────────────────────────────────────────────
    // Witness x := y; the left disjunct of the relation holds by reflexivity.
    let phi_y = phi.subst(x, &ty);
    let ly = Formula::and(psi_y.clone(), Formula::eq(ty.clone(), ty.clone()));
    let ry = Formula::and(Formula::not(psi_y.clone()), Formula::eq(ty.clone(), tx0.clone()));
    debug_assert_eq!(phi_y, Formula::or(ly.clone(), ry.clone()), "separation_nonempty: relation shape drift");
    let p_ya = and_left(Formula::mem(ty.clone(), a.clone()), psi_y.clone());
    let p_psiy = and_right(Formula::mem(ty.clone(), a.clone()), psi_y.clone());
    let p_ly = hyp_and(&p_psiy, &a1i(&Thm::eq_refl(ty.clone()), target.clone()))?;
    let p_phiy = syl(&p_ly, &or_intro_left(ly, ry))?;
    let bwd = a1i(&syl(&hyp_and(&p_ya, &p_phiy)?, &exists_intro_imp(x, inner, ty.clone())?)?, h.clone());

    let iff = Formula::iff(e.clone(), target.clone());
    let all_iff = Thm::mp(&Thm::ax_dist(y, h.clone(), iff.clone())?, &Thm::gen(y, &hyp_and(&fwd, &bwd)?))?;

    // ── Transfer the characterisation from E to Ψ inside the ∃ ───────────────
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let h_ex = retarget(y, bv, &all_iff, &a1i(&img, h.clone()))?;

    // ── Discharge the witness ────────────────────────────────────────────────
    let ex_q = h_ex.concl().as_imp()?.1;
    let out = exists_elim_imp(x0, &Thm::gen(x0, &h_ex), &ex_q)?;
    let carved = Formula::and(Formula::mem(tx.clone(), a.clone()), psi.clone());
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            Formula::exists(x, carved.clone()),
            Formula::exists(bv, Formula::forall(x, Formula::iff(Formula::mem(tx, tb), carved)))
        ),
        "separation_nonempty: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∃s ∀x. (x ∈ s ↔ (x ∈ A ∧ ψ))` — Separation, **unconditionally**.
///
/// [`separation_nonempty`] covers the case where something in `A` satisfies
/// `ψ`. The other case is the one that needed an empty set, and now has one:
/// `empty` is a proof `⊢ ∀z. ¬(z ∈ e)` — [`crate::empty::empty`] supplies it —
/// and when nothing satisfies the condition, `e` itself is the separated set,
/// since both sides of the biconditional are then refutable. The two cases are
/// glued with [`cases`], i.e. with Clavius' law rather than an appeal to
/// excluded middle.
///
/// The empty set is *consumed*: `e` is discharged as the witness of the
/// existential, so it does not appear in the conclusion. A construction that
/// derives its own `∅` to call this therefore does not thereby drag the symbol
/// into anything downstream.
///
/// Returns `None` unless `empty` says exactly `∀z. ¬(z ∈ e)` for some term `e`
/// mentioning neither the probe variable nor `x`.
pub fn separation_full(
    env: &mut Env,
    x: FreeVar,
    psi: &Formula,
    a: &Term,
    empty: &Thm,
) -> Option<Thm> {
    let nonvacuous = separation_nonempty(env, x, psi, a)?; // ⊢ NE → G
    let (ne, g) = nonvacuous.concl().as_imp()?;

    // Read the empty set's term off the theorem, insisting it says precisely
    // what it must, so a caller cannot slip in something else.
    let probe = env.fresh_var();
    let (mem_probe, fls) = inst_all(empty, &[Term::var(probe)])?.concl().as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (lhs, e) = mem_probe.as_mem()?;
    if lhs != Term::var(probe) || e.occurs_free(probe) || e.occurs_free(x) {
        return None
    }

    let tx = Term::var(x);
    let carved = Formula::and(Formula::mem(tx.clone(), a.clone()), psi.clone());
    debug_assert_eq!(
        ne,
        Formula::exists(x, carved.clone()),
        "separation_full: separation_nonempty's antecedent has drifted"
    );

    // ── Nothing satisfies the condition: `e` is the separated set ────────────
    let nne = Formula::not(ne.clone());
    let mem_xe = Formula::mem(tx.clone(), e.clone());

    // `x ∈ e` is absurd, so it implies the carved condition.
    let not_mem = inst_all(empty, std::slice::from_ref(&tx))?;
    debug_assert_eq!(*not_mem.concl(), Formula::not(mem_xe.clone()));
    let nne_fwd = crate::separation::hyp_ex_falso(&a1i(&not_mem, nne.clone()), carved.clone())?;

    // Conversely a carved element would witness `NE`, which `¬NE` refutes.
    let carved_ne = exists_intro_imp(x, carved.clone(), tx.clone())?;
    let nne_absurd = hyp_syl(&a1i(&carved_ne, nne.clone()), &imp_refl(nne.clone()))?;
    let nne_bwd = crate::separation::hyp_ex_falso(&nne_absurd, mem_xe.clone())?;

    // `x` is bound in `¬NE`, so it can be generalised out from under it.
    let nne_all = Thm::mp(
        &Thm::ax_dist(x, nne, Formula::iff(mem_xe, carved.clone()))?,
        &Thm::gen(x, &hyp_and(&nne_fwd, &nne_bwd)?),
    )?;

    // The goal's set binder is invisible — alpha-equivalent formulas are
    // syntactically equal — so a fresh one rebuilds exactly the same `G`.
    let sv = env.fresh_var();
    let body = Formula::forall(x, Formula::iff(Formula::mem(tx, Term::var(sv)), carved));
    debug_assert_eq!(g, Formula::exists(sv, body.clone()), "separation_full: goal shape drift");
    let neg = syl(&nne_all, &exists_intro_imp(sv, body, e)?)?;

    let out = cases(&nonvacuous, &neg)?;
    debug_assert_eq!(*out.concl(), g, "separation_full: unexpected shape");
    Some(out)
}
