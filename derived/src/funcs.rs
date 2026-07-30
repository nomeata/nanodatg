//! Set-theoretic function application, and beta reduction.
//!
//! `app(f, a)` is `⋃ { y : ⟨a,y⟩ ∈ f }`, so the construction climbs four rungs:
//!
//! 1. every such `y` lies in `⋃⋃f` ([`snd_in_union2`]), which gives Separation
//!    a superset to cut the collection out of;
//! 2. Separation itself, derived from the Replacement scheme
//!    ([`separation_nonempty`]);
//! 3. the collection as a total function symbol ([`collection`]), and `app` as
//!    the union of it ([`Apply`], [`app_members`]);
//! 4. beta reduction for the graph `{ ⟨x,t(x)⟩ : x ∈ A }` ([`lambda`],
//!    [`beta_conditional`]).
//!
//! # The empty set, and why it does not block any of this
//!
//! Separation is only derivable here for an *inhabited* result — the vacuous
//! case would produce a set with no members, and `∅` is not obtainable from
//! this kernel's axioms (see the section comment on Separation below). Every
//! symbol below is nevertheless **total**, because a definitional extension
//! has to be:
//! [`collection`] falls back on an arbitrary default when there is nothing to
//! collect, and its characteristic theorem carries an inhabitation antecedent
//! that hides the default away.
//!
//! That antecedent never has to be paid for in [`beta_conditional`], and the
//! reason is worth stating: what must be inhabited is the *collection*
//! `{ y : ⟨a,y⟩ ∈ lam(A) }`, not the value `t(a)`. On the domain the collection
//! contains `t(a)`, whatever `t(a)` happens to be — so beta comes out in its
//! full form, `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = t(a))`, with no side
//! condition on the body at all.
//!
//! What is *not* available is the off-domain behaviour: `app(f,a) = ∅` for `a`
//! outside the domain is exactly the statement that needs `∅`, and it will land
//! with the full Separation development.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_intro, and_left, and_right, clavius, com12, contrapos, eq_symm_imp, ex_falso, exists_elim_imp,
    exists_intro_imp, exists_mono, gen_all, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_or_elim, hyp_or_same,
    iff_mpr, imp_mono_r, imp_refl, inst_all, opair, singleton, syl, syl_imp, uncurry, upair_members,
};

// ─────────────────────────────────────────────────────────────────────────────
// Propositional odds and ends.
//
// Disjunction is `¬a → b`, so introducing a disjunct is not a projection but a
// small derivation, and a case analysis with no ambient hypothesis needs its
// own combinator. Both are used constantly below.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ l → (l ∨ r)`.
///
/// `l ∨ r` is `¬l → r`, so from `l` the antecedent is absurd and ex falso
/// supplies `r`.
pub fn or_intro_left(l: Formula, r: Formula) -> Thm {
    let mono = imp_mono_r(&ex_falso(r), l).expect("or_intro_left: monotonicity applies");
    com12(&mono).expect("or_intro_left: com12 applies")
}

/// `⊢ r → (l ∨ r)`. Weakening, since `l ∨ r` is `¬l → r`.
pub fn or_intro_right(l: Formula, r: Formula) -> Thm { Thm::ax_k(r, Formula::not(l)) }

/// Case analysis with no ambient hypothesis: from `⊢ φ → χ` and `⊢ ¬φ → χ`
/// infer `⊢ χ`.
pub fn cases(pos: &Thm, neg: &Thm) -> Option<Thm> {
    let (_, chi) = pos.concl().as_imp()?;
    let nc_chi = syl(&contrapos(pos)?, neg)?; // ¬χ → ¬φ → χ
    Thm::mp(&clavius(chi), &nc_chi)
}

/// Modus ponens two implications deep: from `⊢ H → (A → (B → C))` and
/// `⊢ H → (A → B)` infer `⊢ H → (A → C)`.
pub fn hyp_mp2(h_imp: &Thm, h_arg: &Thm) -> Option<Thm> {
    let (h, rest) = h_imp.concl().as_imp()?;
    let (a, bc) = rest.as_imp()?;
    let (b, c) = bc.as_imp()?;
    let s = a1i(&Thm::ax_s(a, b, c), h);
    hyp_mp(&hyp_mp(&s, h_imp)?, h_arg)
}

/// Chain two implications under a hypothesis: from `⊢ H → (a → b)` and
/// `⊢ H → (b → c)` infer `⊢ H → (a → c)`.
pub fn hyp_syl(h_ab: &Thm, h_bc: &Thm) -> Option<Thm> {
    let (h, ab) = h_ab.concl().as_imp()?;
    let (a, b) = ab.as_imp()?;
    let (_, bc) = h_bc.concl().as_imp()?;
    let (_, c) = bc.as_imp()?;
    let bridge = a1i(&syl_imp(a, b, c), h);
    hyp_mp(&hyp_mp(&bridge, h_ab)?, h_bc)
}

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

/// The pairing and union symbols with their characteristic theorems.
///
/// Bundled rather than passed one at a time: every lemma below needs all four,
/// and threading them individually makes the signatures unreadable.
pub struct Sets {
    /// `upair`, with `⊢ ∀x ∀y ∀z. (z ∈ upair(x,y) ↔ (z = x ∨ z = y))`.
    pub up: FnSym,
    /// The characteristic theorem of [`Sets::up`].
    pub up_ax: Thm,
    /// `union`, with `⊢ ∀x ∀z. (z ∈ union(x) ↔ ∃y. (y ∈ x ∧ z ∈ y))`.
    pub un: FnSym,
    /// The characteristic theorem of [`Sets::un`].
    pub un_ax: Thm,
}

impl Sets {
    /// Introduce both symbols and prove their characteristic theorems.
    pub fn new(env: &mut Env) -> Sets {
        let (up, up_ax) = crate::upair(env);
        let (un, un_ax) = crate::union(env);
        Sets { up, up_ax, un, un_ax }
    }

    /// The term `⋃s`.
    pub fn union_of(&self, s: Term) -> Term { Term::apply(self.un, vec![s]) }

    /// The term `⟨a, b⟩`.
    pub fn pair(&self, a: Term, b: Term) -> Term { opair(self.up, a, b) }
}

// ─────────────────────────────────────────────────────────────────────────────
// Separation, as far as the kernel's axioms reach.
//
// Separation is not an axiom here; it has to come from Replacement. The
// standard derivation replaces the predicate `ψ` by the *total* relation
//
//     φ(x, y)  :=  (ψ(x) ∧ y = x) ∨ (¬ψ(x) ∧ y = d)
//
// which is functional for every `x` whatever, so Replacement applies and its
// image is `{x ∈ A : ψ(x)} ∪ {d}`. Choosing `d` to be a witness — an element of
// `A` that already satisfies `ψ` — makes the spurious element harmless and the
// image exactly the wanted set.
//
// That is why the derivation below is *conditional on the separated set being
// inhabited*. The unconditional form needs a default `d` that contributes
// nothing, i.e. it needs `∅`; and `∅` is not obtainable from the axioms this
// kernel has. Pairing, Union, Power and Replacement all send inhabited sets to
// inhabited sets, and Regularity only produces an ∈-minimal *element* of a set
// one already has. (A nonempty transitive set would do it — Regularity on one
// yields `∅` immediately — but building a transitive set is the same problem
// again.) So `∅` must arrive with the full Separation development; see the
// module docs for why this does not stand in the way of beta reduction.
// ─────────────────────────────────────────────────────────────────────────────

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

/// `⊢ (v ∈ s ∧ u ∈ v) → u ∈ ⋃s` — the backward half of the Union axiom, with
/// the existential already witnessed.
///
/// The union axiom characterises `u ∈ ⋃s` as `∃y. (y ∈ s ∧ u ∈ y)`; supplying
/// `v` for `y` is all that separates it from the form every use actually wants.
pub fn union_intro(env: &mut Env, sets: &Sets, s: Term, v: Term, u: Term) -> Option<Thm> {
    let un_inst = inst_all(&sets.un_ax, &[s.clone(), u.clone()])?;
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let body = Formula::and(Formula::mem(ty.clone(), s.clone()), Formula::mem(u.clone(), ty));
    debug_assert_eq!(
        *un_inst.concl(),
        Formula::iff(Formula::mem(u.clone(), sets.union_of(s.clone())), Formula::exists(yv, body.clone())),
        "union_intro: the Union axiom has an unexpected shape"
    );
    let intro = exists_intro_imp(yv, body, v)?;
    syl(&intro, &iff_mpr(&un_inst)?)
}

/// `⊢ ∀f ∀a ∀y. (⟨a,y⟩ ∈ f → y ∈ ⋃⋃f)`.
///
/// The superset lemma that makes `{ y : ⟨a,y⟩ ∈ f }` a legitimate instance of
/// Separation. Two applications of [`union_intro`] along the chain
/// `y ∈ {a,y} ∈ ⟨a,y⟩ ∈ f`: the middle set is a member of the pair, which is a
/// member of `f`, so it is in `⋃f`, and `y` is in it, so `y` is in `⋃⋃f`.
pub fn snd_in_union2(env: &mut Env, sets: &Sets) -> Option<Thm> {
    let (f, a, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, ty) = (Term::var(f), Term::var(a), Term::var(y));

    let ay = Term::apply(sets.up, vec![ta.clone(), ty.clone()]); // {a,y}
    let pair = sets.pair(ta.clone(), ty.clone()); // ⟨a,y⟩ = {{a},{a,y}}
    let uf = sets.union_of(tf.clone()); // ⋃f
    let uuf = sets.union_of(uf.clone()); // ⋃⋃f

    let h = Formula::mem(pair.clone(), tf.clone());

    // ⊢ {a,y} ∈ ⟨a,y⟩ and ⊢ y ∈ {a,y}, both from the Pairing characterisation.
    let (_, ay_in_pair) = upair_members(&sets.up_ax, &singleton(sets.up, ta.clone()), &ay)?;
    let (_, y_in_ay) = upair_members(&sets.up_ax, &ta, &ty)?;

    // ⊢ H → {a,y} ∈ ⋃f
    let step1 = union_intro(env, sets, tf.clone(), pair, ay.clone())?;
    let h_ay_in_uf = syl(&hyp_and(&imp_refl(h.clone()), &a1i(&ay_in_pair, h.clone()))?, &step1)?;

    // ⊢ H → y ∈ ⋃⋃f
    let step2 = union_intro(env, sets, uf, ay, ty.clone())?;
    let out = syl(&hyp_and(&h_ay_in_uf, &a1i(&y_in_ay, h.clone()))?, &step2)?;

    debug_assert_eq!(*out.concl(), Formula::imp(h, Formula::mem(ty, uuf)), "snd_in_union2: unexpected shape");
    Some(gen_all(&[f, a, y], &out))
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
/// above this section. It is what stands in for the empty set, which the
/// kernel's axioms do not supply.
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

// ─────────────────────────────────────────────────────────────────────────────
// The collection of values, and application.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀f ∀a. ((∃y. ⟨a,y⟩ ∈ f) → ∃s ∀y. (y ∈ s ↔ ⟨a,y⟩ ∈ f))`.
///
/// The collection `{ y : ⟨a,y⟩ ∈ f }` is a set. Separation supplies it once a
/// superset is known, and [`snd_in_union2`] is that superset: the very same
/// inclusion also erases the `y ∈ ⋃⋃f` conjunct Separation leaves behind, so
/// the condition comes out clean.
///
/// The inhabitation antecedent is inherited from [`separation_nonempty`]; for
/// the beta rule it is discharged by the pair `⟨a, t(a)⟩` itself, which is why
/// it costs nothing there even when the *value* `t(a)` is empty.
pub fn value_collection(env: &mut Env, sets: &Sets, snd_in_uu: &Thm) -> Option<Thm> {
    let (f, a, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, ty) = (Term::var(f), Term::var(a), Term::var(y));
    let uuf = sets.union_of(sets.union_of(tf.clone()));

    let l = Formula::mem(sets.pair(ta.clone(), ty.clone()), tf.clone());
    let mem_uu = Formula::mem(ty.clone(), uuf.clone());

    let sep = separation_nonempty(env, y, &l, &uuf)?;
    // ⊢ ⟨a,y⟩ ∈ f → y ∈ ⋃⋃f, and hence `L ↔ (y ∈ ⋃⋃f ∧ L)`.
    let l_to_uu = inst_all(snd_in_uu, &[tf.clone(), ta.clone(), ty.clone()])?;
    let l_to_both = hyp_and(&l_to_uu, &imp_refl(l.clone()))?;
    let both_to_l = and_right(mem_uu, l.clone());

    // The antecedent weakens along the same implication.
    let ante = exists_mono(y, &Thm::gen(y, &l_to_both))?;
    let h_ex = syl(&ante, &sep)?;

    let sv = env.fresh_var();
    let h_iff = a1i(&Thm::gen(y, &and_intro(&both_to_l, &l_to_both)), Formula::exists(y, l.clone()));
    let out = retarget(y, sv, &h_iff, &h_ex)?;

    debug_assert_eq!(
        out.concl().as_imp()?.0,
        Formula::exists(y, l),
        "value_collection: unexpected antecedent"
    );
    Some(gen_all(&[f, a], &out))
}

/// The collection symbol `coll(f,a) = { y : ⟨a,y⟩ ∈ f }`, together with
/// `⊢ ∀f ∀a. ((∃y. ⟨a,y⟩ ∈ f) → ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f))`.
///
/// A definitional extension has to be *total*: `kernel::thm::define` wants
/// `∃!`, so a symbol that only exists when the collection is inhabited is not
/// on offer. The condition actually defined is therefore
///
/// ```text
/// y ∈ coll(f,a)  ↔  ⟨a,y⟩ ∈ f  ∨  (¬∃y. ⟨a,y⟩ ∈ f  ∧  y ∈ f)
/// ```
///
/// which agrees with the intended one whenever anything is there to collect,
/// and otherwise degenerates to `f` — an arbitrary but harmless default, chosen
/// because it is a set we already have. (`∅` would be the natural default, and
/// is exactly what the axioms do not provide.) The default is invisible in the
/// theorem returned, which is conditional on inhabitation.
pub fn collection(env: &mut Env, sets: &Sets, value_coll: &Thm) -> Option<(FnSym, Thm)> {
    let (f, a, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, ty) = (Term::var(f), Term::var(a), Term::var(y));

    let l = Formula::mem(sets.pair(ta.clone(), ty.clone()), tf.clone());
    let ne = Formula::exists(y, l.clone());
    let nne = Formula::not(ne.clone());
    let mem_yf = Formula::mem(ty.clone(), tf.clone());
    let rgt = Formula::and(nne.clone(), mem_yf.clone());
    let phi = Formula::or(l.clone(), rgt.clone());

    // ── Inhabited: the definition agrees with the intended condition. ────────
    let k = Formula::and(ne.clone(), phi.clone());
    let k_r_np = a1i(&and_left(nne.clone(), mem_yf.clone()), k);
    let k_l = or_resolve_left(&and_left(ne.clone(), phi.clone()), &and_right(ne.clone(), phi.clone()), &k_r_np)?;
    let ne_phi_l = uncurry(&k_l)?;
    let ne_l_phi = a1i(&or_intro_left(l.clone(), rgt.clone()), ne.clone());
    let ne_iff = hyp_and(&ne_l_phi, &ne_phi_l)?; // NE → (L ↔ φ)

    let ne_all = Thm::mp(
        &Thm::ax_dist(y, ne.clone(), Formula::iff(l.clone(), phi.clone()))?,
        &Thm::gen(y, &ne_iff),
    )?;
    let sv = env.fresh_var();
    let pos = retarget(y, sv, &ne_all, &inst_all(value_coll, &[tf.clone(), ta.clone()])?)?;

    // ── Empty: the condition degenerates to `y ∈ f`, so `f` itself serves. ───
    let nne_nl = contrapos(&exists_intro_imp(y, l.clone(), ty.clone())?)?; // ¬NE → ¬L
    let k2_nl = syl(&and_left(nne.clone(), phi.clone()), &nne_nl)?;
    let k2_r = hyp_mp(&and_right(nne.clone(), phi.clone()), &k2_nl)?;
    let nne_phi_mem = uncurry(&syl(&k2_r, &and_right(nne.clone(), mem_yf.clone()))?)?;
    let k3_r = hyp_and(&and_left(nne.clone(), mem_yf.clone()), &and_right(nne.clone(), mem_yf.clone()))?;
    let nne_mem_phi = uncurry(&syl(&k3_r, &or_intro_right(l.clone(), rgt))?)?;
    let nne_all = Thm::mp(
        &Thm::ax_dist(y, nne.clone(), Formula::iff(mem_yf.clone(), phi.clone()))?,
        &Thm::gen(y, &hyp_and(&nne_mem_phi, &nne_phi_mem)?),
    )?;
    let sv2 = env.fresh_var();
    let p_s = Formula::forall(y, Formula::iff(Formula::mem(ty.clone(), Term::var(sv2)), phi.clone()));
    let neg = syl(&nne_all, &exists_intro_imp(sv2, p_s, tf.clone())?)?;

    let existence = cases(&pos, &neg)?;
    let (coll, coll_ax) = crate::define_by_membership(env, &[f, a], &existence, y, &phi)?;

    // ── Strip the default back off, under the inhabitation hypothesis. ───────
    let coll_term = Term::apply(coll, vec![tf.clone(), ta.clone()]);
    let inst = inst_all(&coll_ax, &[tf, ta, ty.clone()])?;
    let mem_yc = Formula::mem(ty.clone(), coll_term);
    let ne_c_l = hyp_syl(&a1i(&crate::iff_mp(&inst)?, ne.clone()), &ne_phi_l)?;
    let ne_l_c = hyp_syl(&ne_l_phi, &a1i(&iff_mpr(&inst)?, ne.clone()))?;
    let all = Thm::mp(
        &Thm::ax_dist(y, ne, Formula::iff(mem_yc, l))?,
        &Thm::gen(y, &hyp_and(&ne_c_l, &ne_l_c)?),
    )?;
    Some((coll, gen_all(&[f, a], &all)))
}

/// The whole application apparatus: the symbols and the characteristic
/// theorems every rule below consumes.
///
/// Assembling it once and passing it around is not just convenience — each
/// piece is a *definitional extension*, so building it twice would introduce
/// two different symbols and the theorems would not compose.
pub struct Apply {
    /// Pairing and union.
    pub sets: Sets,
    /// `coll(f,a) = { y : ⟨a,y⟩ ∈ f }`; see [`collection`].
    pub coll: FnSym,
    /// `⊢ ∀f ∀a. ((∃y. ⟨a,y⟩ ∈ f) → ∀y. (y ∈ coll(f,a) ↔ ⟨a,y⟩ ∈ f))`.
    pub coll_ax: Thm,
    /// `app(f,a) = ⋃ coll(f,a)`.
    pub app: FnSym,
    /// `⊢ ∀f ∀a. app(f,a) = ⋃ coll(f,a)`.
    pub app_ax: Thm,
    /// `⊢ ∀a ∀z. (z ∈ {a} ↔ z = a)`.
    pub mem_sing: Thm,
    /// `⊢ ∀c. ⋃{c} = c`.
    pub union_sing: Thm,
    /// `⊢ ∀a ∀b ∀c ∀d. (⟨a,b⟩ = ⟨c,d⟩ → (a = c ∧ b = d))`.
    pub pair_inj: Thm,
}

impl Apply {
    /// Introduce every symbol and derive every theorem, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Apply> {
        let sets = Sets::new(env);
        let mem_sing = crate::mem_singleton(env, sets.up, &sets.up_ax)?;
        let sing_inj = crate::singleton_inj(env, sets.up, &mem_sing)?;
        let fst = crate::opair_fst(env, sets.up, &sets.up_ax, &mem_sing, &sing_inj)?;
        let snd = crate::pairs::opair_snd(env, sets.up, &sets.up_ax, &mem_sing, &fst)?;
        let pair_inj = crate::pairs::opair_inj(env, sets.up, &fst, &snd)?;
        let union_sing = crate::union_singleton(env, sets.up, &sets.up_ax, sets.un, &sets.un_ax)?;

        let sni = snd_in_union2(env, &sets)?;
        let vc = value_collection(env, &sets, &sni)?;
        let (coll, coll_ax) = collection(env, &sets, &vc)?;

        // `app` is an *explicit* definition, so it costs nothing: the work all
        // sits in `coll`, and stripping the outer union is a term composition.
        let (f, a) = (env.fresh_var(), env.fresh_var());
        let body = sets.union_of(Term::apply(coll, vec![Term::var(f), Term::var(a)]));
        let (app, app_ax) = crate::define_abbrev(env, &[f, a], &body)?;

        Some(Apply { sets, coll, coll_ax, app, app_ax, mem_sing, union_sing, pair_inj })
    }

    /// The term `app(f, a)`.
    pub fn apply(&self, f: Term, a: Term) -> Term { Term::apply(self.app, vec![f, a]) }

    /// The term `coll(f, a)`.
    pub fn coll_of(&self, f: Term, a: Term) -> Term { Term::apply(self.coll, vec![f, a]) }
}

/// `⊢ ∀f ∀a. ((∃y. ⟨a,y⟩ ∈ f) → ∀w. (w ∈ app(f,a) ↔ ∃y. (⟨a,y⟩ ∈ f ∧ w ∈ y)))`
/// — the characteristic property of application.
///
/// `app(f,a)` is `⋃ coll(f,a)`, so membership unfolds through the Union axiom
/// and then through [`Apply::coll_ax`]; the antecedent is the one inherited
/// from `coll`.
pub fn app_members(env: &mut Env, ap: &Apply) -> Option<Thm> {
    let (f, a, w, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tw, ty) = (Term::var(f), Term::var(a), Term::var(w), Term::var(y));

    let coll_term = ap.coll_of(tf.clone(), ta.clone());
    let app_term = ap.apply(tf.clone(), ta.clone());
    let ucoll = ap.sets.union_of(coll_term.clone());

    let l = Formula::mem(ap.sets.pair(ta.clone(), ty.clone()), tf.clone());
    let ne = Formula::exists(y, l.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let mem_wy = Formula::mem(tw.clone(), ty.clone());
    let src = Formula::and(mem_yc.clone(), mem_wy.clone());
    let tgt = Formula::and(l.clone(), mem_wy.clone());
    let ex_tgt = Formula::exists(y, tgt.clone());

    // `w ∈ app(f,a) ↔ w ∈ ⋃coll(f,a)`, by Leibniz on the defining equation.
    let app_def = inst_all(&ap.app_ax, &[tf.clone(), ta.clone()])?;
    let (v1, v2) = (env.fresh_var(), env.fresh_var());
    let a2u = Thm::mp(
        &Thm::eq_leibniz(app_term.clone(), ucoll.clone(), v1, Formula::mem(tw.clone(), Term::var(v1))),
        &app_def,
    )?;
    let u2a = Thm::mp(
        &Thm::eq_leibniz(ucoll.clone(), app_term.clone(), v2, Formula::mem(tw.clone(), Term::var(v2))),
        &crate::eq_symm(env, &app_def)?,
    )?;
    let un_inst = inst_all(&ap.sets.un_ax, &[coll_term, tw.clone()])?;
    let coll_here = inst_all(&ap.coll_ax, &[tf, ta])?;
    let all_iff = Formula::forall(y, Formula::iff(mem_yc.clone(), l.clone()));

    // Swap `y ∈ coll` for `⟨a,y⟩ ∈ f` under the existential, both ways.
    let swap = |from: &Formula, to: &Formula, forward: bool| -> Option<Thm> {
        let k_from = and_left(from.clone(), ne.clone());
        let k_ne = and_right(from.clone(), ne.clone());
        let k_iff = syl(&syl(&k_ne, &coll_here)?, &Thm::ax_inst(all_iff.clone(), ty.clone())?)?;
        let head = if forward { mem_yc.clone() } else { l.clone() };
        let side = if forward { hyp_iff_mp(&k_iff)? } else { hyp_iff_mpr(&k_iff)? };
        let k_head = hyp_mp(&side, &syl(&k_from, &and_left(head.clone(), mem_wy.clone()))?)?;
        let k_tail = syl(&k_from, &and_right(head, mem_wy.clone()))?;
        let k_ex = syl(&hyp_and(&k_head, &k_tail)?, &exists_intro_imp(y, to.clone(), ty.clone())?)?;
        let elim = exists_elim_imp(
            y,
            &Thm::gen(y, &uncurry(&k_ex)?),
            &Formula::imp(ne.clone(), Formula::exists(y, to.clone())),
        )?;
        com12(&elim)
    };
    let fwd_ex = swap(&src, &tgt, true)?;
    let bwd_ex = swap(&tgt, &src, false)?;

    let ne_fwd = hyp_syl(&a1i(&syl(&a2u, &crate::iff_mp(&un_inst)?)?, ne.clone()), &fwd_ex)?;
    let ne_bwd = hyp_syl(&bwd_ex, &a1i(&syl(&iff_mpr(&un_inst)?, &u2a)?, ne.clone()))?;
    let out = Thm::mp(
        &Thm::ax_dist(w, ne, Formula::iff(Formula::mem(tw, app_term), ex_tgt))?,
        &Thm::gen(w, &hyp_and(&ne_fwd, &ne_bwd)?),
    )?;
    Some(gen_all(&[f, a], &out))
}

/// The graph `lam(A) = { ⟨x, t(x)⟩ : x ∈ A }` of a unary function symbol,
/// with `⊢ ∀A ∀y. (y ∈ lam(A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(x)⟩))`.
///
/// Replacement, at its cheapest: the relation is `y = term`, so the `∃!`
/// premise is [`crate::exists_unique_eq`] and costs nothing. The domain stays a
/// parameter, so one symbol serves every domain.
pub fn lambda(env: &mut Env, ap: &Apply, t: FnSym) -> Option<(FnSym, Thm)> {
    if t.arity() != 1 {
        return None
    }
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (t_a, tx) = (Term::var(av), Term::var(x));
    let pair = ap.sets.pair(tx.clone(), Term::apply(t, vec![tx.clone()]));

    let (y, phi, exu) = crate::exists_unique_eq(env, &[], &pair);
    let repl = Thm::ax_replacement(env, x, y, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&t_a))?;
    let premise = Thm::gen(x, &a1i(&exu, Formula::mem(tx.clone(), t_a.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, t_a), phi));
    crate::define_by_membership(env, &[av], &img, y, &cond)
}

/// `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = t(a))` — beta reduction.
///
/// The membership antecedent is not removable: a set-theoretic function has a
/// set domain, and off it `app` returns whatever the default in [`collection`]
/// happens to give. On the domain the argument is:
///
/// * `⟨a, t(a)⟩ ∈ lam(A)`, witnessed by `x := a`, which in particular makes the
///   collection inhabited — so [`Apply::coll_ax`]'s antecedent is discharged
///   *without* assuming anything about `t(a)` itself;
/// * conversely `⟨a,y⟩ ∈ lam(A)` forces `y = t(a)`, by injectivity of the
///   Kuratowski pair;
/// * so `coll(lam(A), a)` and `{t(a)}` have the same members, hence are equal;
/// * and `app` strips the union off a singleton.
pub fn beta_conditional(env: &mut Env, ap: &Apply, t: FnSym, lam: FnSym, lam_ax: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (av, a, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (t_a, ta, tx, ty) = (Term::var(av), Term::var(a), Term::var(x), Term::var(y));

    let lam_t = Term::apply(lam, vec![t_a.clone()]);
    let val = Term::apply(t, vec![ta.clone()]); // t(a)
    let tx_val = Term::apply(t, vec![tx.clone()]); // t(x)
    let h = Formula::mem(ta.clone(), t_a.clone()); // a ∈ A

    let pair_ay = ap.sets.pair(ta.clone(), ty.clone()); // ⟨a,y⟩
    let pair_aval = ap.sets.pair(ta.clone(), val.clone()); // ⟨a,t(a)⟩
    let pair_x = ap.sets.pair(tx.clone(), tx_val.clone()); // ⟨x,t(x)⟩

    // ── ⟨a,t(a)⟩ ∈ lam(A), by taking x := a in the image condition ───────────
    let lam_at_val = inst_all(lam_ax, &[t_a.clone(), pair_aval.clone()])?;
    let body_val = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_aval.clone(), pair_x.clone()));
    let h_witness = hyp_and(&imp_refl(h.clone()), &a1i(&Thm::eq_refl(pair_aval.clone()), h.clone()))?;
    let h_ex = syl(&h_witness, &exists_intro_imp(x, body_val, ta.clone())?)?;
    let h_in_lam = syl(&h_ex, &iff_mpr(&lam_at_val)?)?; // H → ⟨a,t(a)⟩ ∈ lam(A)

    // ── The collection is inhabited, so `coll_ax` applies ────────────────────
    let mem_pair_y = Formula::mem(pair_ay.clone(), lam_t.clone());
    let h_ne = syl(&h_in_lam, &exists_intro_imp(y, mem_pair_y.clone(), val.clone())?)?;
    let coll_here = inst_all(&ap.coll_ax, &[lam_t.clone(), ta.clone()])?;
    let h_coll = syl(&h_ne, &coll_here)?; // H → ∀y. (y ∈ coll ↔ ⟨a,y⟩ ∈ lam(A))

    // ── ⟨a,y⟩ ∈ lam(A) ↔ y = t(a) ────────────────────────────────────────────
    let eq_y_val = Formula::eq(ty.clone(), val.clone());
    // ←: rewrite the membership just established along `y = t(a)`.
    let w = env.fresh_var();
    let carry = Thm::eq_leibniz(
        val.clone(),
        ty.clone(),
        w,
        Formula::mem(ap.sets.pair(ta.clone(), Term::var(w)), lam_t.clone()),
    );
    let bwd = syl(&h_in_lam, &com12(&syl(&eq_symm_imp(env, ty.clone(), val.clone()), &carry)?)?)?;

    // →: the image condition plus injectivity of ⟨·,·⟩.
    let lam_at_y = inst_all(lam_ax, &[t_a.clone(), pair_ay.clone()])?;
    let k = Formula::and(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let k_eq = and_right(Formula::mem(tx.clone(), t_a.clone()), Formula::eq(pair_ay.clone(), pair_x.clone()));
    let inj = inst_all(&ap.pair_inj, &[ta.clone(), ty.clone(), tx.clone(), tx_val.clone()])?;
    let k_conj = syl(&k_eq, &inj)?;
    let (e_ax, e_yt) = (Formula::eq(ta.clone(), tx.clone()), Formula::eq(ty.clone(), tx_val.clone()));
    let k_ax = syl(&k_conj, &and_left(e_ax.clone(), e_yt.clone()))?;
    let k_ytx = syl(&k_conj, &and_right(e_ax, e_yt))?;
    // a = x → t(a) = t(x)
    let w2 = env.fresh_var();
    let congr = crate::mpd_const(
        &Thm::eq_leibniz(
            ta.clone(),
            tx.clone(),
            w2,
            Formula::eq(val.clone(), Term::apply(t, vec![Term::var(w2)])),
        ),
        &Thm::eq_refl(val.clone()),
    )?;
    let k_txta = syl(&syl(&k_ax, &congr)?, &eq_symm_imp(env, val.clone(), tx_val.clone()))?;
    let w3 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(tx_val.clone(), val.clone(), w3, Formula::eq(ty.clone(), Term::var(w3)));
    let k_goal = hyp_mp(&hyp_mp(&a1i(&carry2, k), &k_txta)?, &k_ytx)?;
    let fwd = syl(&crate::iff_mp(&lam_at_y)?, &exists_elim_imp(x, &Thm::gen(x, &k_goal), &eq_y_val)?)?;

    // ── coll(lam(A), a) and {t(a)} have the same members ─────────────────────
    let sing = singleton(ap.sets.up, val.clone());
    let ms = inst_all(&ap.mem_sing, &[val.clone(), ty.clone()])?;
    let coll_term = ap.coll_of(lam_t.clone(), ta.clone());
    let mem_yc = Formula::mem(ty.clone(), coll_term.clone());
    let coll_at_y = Formula::forall(y, Formula::iff(mem_yc.clone(), mem_pair_y));
    let h_iff_y = syl(&h_coll, &Thm::ax_inst(coll_at_y, ty.clone())?)?;
    let (h_c_lam, h_lam_c) = (hyp_iff_mp(&h_iff_y)?, hyp_iff_mpr(&h_iff_y)?);
    let h_c_sing = hyp_syl(&hyp_syl(&h_c_lam, &a1i(&fwd, h.clone()))?, &a1i(&iff_mpr(&ms)?, h.clone()))?;
    let h_sing_c = hyp_syl(&hyp_syl(&a1i(&crate::iff_mp(&ms)?, h.clone()), &bwd)?, &h_lam_c)?;
    let mem_ys = Formula::mem(ty.clone(), sing.clone());
    let h_same = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_yc, mem_ys))?,
        &Thm::gen(y, &hyp_and(&h_c_sing, &h_sing_c)?),
    )?;
    let h_coll_eq = syl(&h_same, &inst_all(&ext, &[coll_term.clone(), sing.clone()])?)?;

    // ── app(lam(A),a) = ⋃coll = ⋃{t(a)} = t(a) ───────────────────────────────
    let ucoll = ap.sets.union_of(coll_term.clone());
    let using = ap.sets.union_of(sing.clone());
    let w4 = env.fresh_var();
    let congr_u = crate::mpd_const(
        &Thm::eq_leibniz(coll_term, sing, w4, Formula::eq(ucoll.clone(), ap.sets.union_of(Term::var(w4)))),
        &Thm::eq_refl(ucoll.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?; // H → ⋃coll = ⋃{t(a)}

    let app_term = ap.apply(lam_t.clone(), ta.clone());
    let app_def = inst_all(&ap.app_ax, &[lam_t, ta.clone()])?; // ⊢ app = ⋃coll
    let w5 = env.fresh_var();
    let carry3 = Thm::eq_leibniz(ucoll, using.clone(), w5, Formula::eq(app_term.clone(), Term::var(w5)));
    let h_app_using = hyp_mp(&hyp_mp(&a1i(&carry3, h.clone()), &h_u_eq)?, &a1i(&app_def, h.clone()))?;
    let w6 = env.fresh_var();
    let carry4 = Thm::mp(
        &Thm::eq_leibniz(using, val.clone(), w6, Formula::eq(app_term.clone(), Term::var(w6))),
        &inst_all(&ap.union_sing, std::slice::from_ref(&val))?,
    )?;
    let out = syl(&h_app_using, &carry4)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(app_term, val)),
        "beta_conditional: unexpected shape"
    );
    Some(gen_all(&[av, a], &out))
}
