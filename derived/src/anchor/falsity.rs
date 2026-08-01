//! `Prop` as the two-element set `{0, 1}`, and `False` as `0`.
//!
//! # Interface
//!
//! ```text
//! ⟦Prop⟧  := upair(0, 1) = {∅, {∅}}                  [truth_values]
//! ⟦False⟧ := 0 = ∅                                   [false_set]
//! ⟦True⟧  := 1 = {∅}                                 [true_set]
//!
//! ⊢ ∀x. ¬(x ∈ ⟦False⟧)                               [false_uninhabited]
//! ⊢ t ∈ ⟦False⟧ → ψ,  for any term t and formula ψ    [false_absurd]
//! ⊢ ⟦False⟧ ∈ ⟦Prop⟧                                 [false_in_prop]
//! ⊢ ⟦True⟧ ∈ ⟦Prop⟧                                  [true_in_prop]
//! ⊢ ¬(⟦False⟧ = ⟦True⟧)                              [prop_two_valued]
//! ⊢ [φ] ∈ ⟦Prop⟧                                     [cond_in_prop]
//! ⊢ [⊥] = ⟦False⟧                                    [bot_is_false]
//! ⊢ ∀p ∀x. ((p ∈ ⟦Prop⟧ ∧ x ∈ p) → x = •)            [prop_subsingleton]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Where these terms come from
//!
//! Carneiro's *The Type Theory of Lean* identifies `Prop` with the zeroth
//! universe — `P := U₀`, with `U₀ = {∅, {•}}` and `• = ∅` — so a proposition
//! *is* a subset of `{•}`, false when it is `∅` and true when it is `{•}`.
//! `⊥` is the empty `Prop`-valued inductive, and the thesis's own clause for it
//! is `⟦Γ ⊢ ⊥⟧γ = ∅`. Nothing here is a design choice of this project's; the
//! only work is to make the terms be those terms and prove what they are.
//!
//! In this crate's notation `0` is [`crate::sums::Sums::zero`], `1` is
//! [`crate::sums::Sums::unit`] and `{0,1}` is the unordered pair of the two, so
//! `⟦Prop⟧` is a term over the *existing* pairing symbol and needs no new
//! definitional extension at all.
//!
//! One consequence is worth naming so it is not mistaken for a bug: since `• = ∅`
//! and `⟦False⟧ = ∅`, the proof object and the false proposition are **the same
//! set**. That is the thesis's convention, and it is harmless — the two occur at
//! different places (`•` as an element, `⟦False⟧` as a set) and nothing here
//! confuses them. In particular `⊢ • ∈ ⟦True⟧` and `⊢ ¬(• ∈ ⟦False⟧)` are both
//! theorems, which is only to say `∅ ∈ {∅}` and `∅ ∉ ∅`.
//!
//! # This is not yet tied to the backend
//!
//! **`checker/src/tg.rs` does not produce these terms today.** `interp_sort`
//! maps `Level::Zero` to an opaque nullary symbol `sort0` about which nothing is
//! provable, and `False` — a `Prop`-valued inductive with no value — is rejected
//! by the enumeration recogniser (correctly: a `Prop` is a subsingleton, not a
//! W-type) and falls through to an opaque nullary symbol as well. So the
//! theorems below are about the term the interpretation *should* use, not about
//! one it does use. The one-line change that would close the gap is recorded in
//! this crate's `tests/anchor.rs`.
//!
//! Contrast [`super::wtype`], whose statements *are* stated at the term
//! `checker/src/tg.rs` uses for `⟦Empty⟧`.
//!
//! # Proof irrelevance falls out
//!
//! [`prop_subsingleton`] is derived for **every** member of `⟦Prop⟧`, not only
//! for the conditional singletons [`crate::prop`] constructs: if `p ∈ {0,1}`
//! then `p` is `∅` — which has no elements — or `{•}` — all of whose elements
//! are `•`. That is why [`crate::prop::cond_subsingleton`] needed no side
//! hypothesis; the general fact is a property of the universe, not of the
//! construction.
//!
//! # Non-vacuity
//!
//! Every statement here would hold, and say nothing, in a development where
//! `0 = 1`: `⟦Prop⟧` would be a one-element set and "true" and "false" would be
//! the same proposition. [`prop_two_valued`] rules that out —
//! [`crate::sums::tags_distinct`] is `⊢ ¬(∅ = 1)` — and [`cond_in_prop`] is what
//! makes the two values reachable, since `[φ]` lands on one or the other
//! according to `φ`.

use kernel::{Env, Formula, Term, Thm};

use crate::funcs::logic::hyp_syl;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, clavius, com12, eq_symm_imp, ex_falso, gen_all, imp_mono_r, imp_refl,
    inst_all, mp_const, mpd_const, syl, syl_imp,
};

/// `⟦Prop⟧ = {0, 1}` — the two-element set of truth values, `U₀`.
pub fn truth_values(s: &Sums) -> Term {
    Term::apply(s.ap.sets.up, vec![s.zero(), s.unit()])
}

/// `⟦False⟧ = 0 = ∅`.
pub fn false_set(s: &Sums) -> Term { s.zero() }

/// `⟦True⟧ = 1 = {∅}`.
pub fn true_set(s: &Sums) -> Term { s.unit() }

/// **The anchor for `False`.** `⊢ ∀x. ¬(x ∈ ⟦False⟧)`
///
/// `⟦False⟧` is `∅`, so this is [`crate::empty`]'s `⊢ ∀z. ¬(z ∈ ∅)` read at that
/// term — but read *at that term*, which is the whole content of the claim. The
/// check below is what makes it a statement about the interpretation rather than
/// a restatement of the empty set's defining property.
///
/// Because `Formula::not(φ)` is literally `φ → ⊥` in this kernel, this formula
/// already **is** "an inhabitant of `⟦False⟧` yields a contradiction". See
/// [`false_absurd`] for the packaged consequence.
pub fn false_uninhabited(env: &mut Env, s: &Sums) -> Option<Thm> {
    let out = s.ap.empty_ax.clone();
    let xv = env.fresh_var();
    let want = Formula::forall(xv, Formula::not(Formula::mem(Term::var(xv), false_set(s))));
    (*out.concl() == want).then_some(out)
}

/// **The consequence that matters.** `⊢ t ∈ ⟦False⟧ → ψ` — from an inhabitant of
/// `⟦False⟧`, every formula follows.
///
/// This is [`false_uninhabited`] at `t` followed by [`crate::ex_falso`]. It is
/// the form an end-to-end argument uses: a Lean `theorem foo : False` accepted
/// with a certified typing gives `⊢ ⟦foo⟧ ∈ ⟦False⟧`, and one modus ponens then
/// gives `⊢ ⊥` — so the target theory is inconsistent, contrapositively the
/// acceptance was impossible.
pub fn false_absurd(s: &Sums, t: &Term, psi: Formula) -> Option<Thm> {
    let at_t = inst_all(&s.ap.empty_ax, std::slice::from_ref(t))?;
    let out = syl(&at_t, &ex_falso(psi.clone()))?;
    (*out.concl() == Formula::imp(Formula::mem(t.clone(), false_set(s)), psi)).then_some(out)
}

/// `⊢ ⟦False⟧ ∈ ⟦Prop⟧` — falsity is one of the two truth values.
pub fn false_in_prop(s: &Sums) -> Option<Thm> {
    let (zero, one) = (s.zero(), s.unit());
    let at = inst_all(&s.ap.sets.up_ax, &[zero.clone(), one.clone(), zero.clone()])?;
    // `0 = 0 ∨ 0 = 1` is `¬(0 = 0) → (0 = 1)`, and `0 = 0` refutes its
    // antecedent outright.
    let refl = Thm::eq_refl(zero.clone());
    let absurd = mp_const(&refl, Formula::false_());
    let disj = syl(&absurd, &ex_falso(Formula::eq(zero.clone(), one.clone())))?;
    let out = Thm::mp(&crate::iff_mpr(&at)?, &disj)?;
    (*out.concl() == Formula::mem(zero, truth_values(s))).then_some(out)
}

/// `⊢ ⟦True⟧ ∈ ⟦Prop⟧` — and so is truth.
pub fn true_in_prop(s: &Sums) -> Option<Thm> {
    let (zero, one) = (s.zero(), s.unit());
    let at = inst_all(&s.ap.sets.up_ax, &[zero.clone(), one.clone(), one.clone()])?;
    // `1 = 0 ∨ 1 = 1` is `¬(1 = 0) → (1 = 1)`, and the consequent is reflexivity.
    let disj = a1i(&Thm::eq_refl(one.clone()), Formula::not(Formula::eq(one.clone(), zero)));
    let out = Thm::mp(&crate::iff_mpr(&at)?, &disj)?;
    (*out.concl() == Formula::mem(one, truth_values(s))).then_some(out)
}

/// **Non-vacuity.** `⊢ ¬(⟦False⟧ = ⟦True⟧)` — the two truth values are different
/// sets, so `⟦Prop⟧` really has two elements.
///
/// [`crate::sums::tags_distinct`], named for what it means here. Without it every
/// theorem in this file would be compatible with `⟦Prop⟧` being a singleton, in
/// which case "`φ` denotes `1`" would say nothing.
pub fn prop_two_valued(s: &Sums) -> Option<Thm> {
    let out = s.tags_distinct.clone();
    (*out.concl() == Formula::not(Formula::eq(false_set(s), true_set(s)))).then_some(out)
}

/// `⊢ [φ] ∈ ⟦Prop⟧` — **the denotation of a proposition is a truth value**.
///
/// A construction taking a formula, exactly as
/// [`crate::prop::conditional_singleton`] is: `φ` is arbitrary, so this cannot
/// be a single `∀`-quantified theorem. Given the characteristic theorem `chi`
/// of `c = [φ]`, the derivation is [`crate::prop::cond_true`] and
/// [`crate::prop::cond_false`] plus excluded middle — `[φ]` is `1` when `φ` and
/// `0` when `¬φ`, and both are members of `{0,1}`.
///
/// This is the general statement that nothing in the crate proved before: that
/// the interpretation of a `Prop` lands in `⟦Prop⟧` at all.
pub fn cond_in_prop(env: &mut Env, s: &Sums, phi: &Formula, c: &Term, chi: &Thm) -> Option<Thm> {
    let (zero, one) = (s.zero(), s.unit());
    let pv = truth_values(s);
    let goal = Formula::mem(c.clone(), pv.clone());

    // `⊢ v ∈ {0,1}` carried backwards along `c = v`, for each truth value.
    let land = |env: &mut Env, decided: &Thm, v: &Term, v_in: &Thm| -> Option<Thm> {
        let w = env.fresh_var();
        let leib =
            Thm::eq_leibniz(v.clone(), c.clone(), w, Formula::mem(Term::var(w), pv.clone()));
        let carried = mpd_const(&leib, v_in)?; // `v = c → c ∈ {0,1}`
        let flip = eq_symm_imp(env, c.clone(), v.clone()); // `c = v → v = c`
        syl(decided, &syl(&flip, &carried)?)
    };

    let is_true = crate::prop::cond_true(env, s, phi, c, chi)?;
    let is_false = crate::prop::cond_false(env, s, phi, c, chi)?;
    let t_case = land(env, &is_true, &one, &true_in_prop(s)?)?;
    let f_case = land(env, &is_false, &zero, &false_in_prop(s)?)?;

    let out = crate::funcs::cases(&t_case, &f_case)?;
    (*out.concl() == goal).then_some(out)
}

/// `⊢ [⊥] = ⟦False⟧` — the conditional singleton at `⊥` *is* the empty set.
///
/// The two candidate readings of `False` — "the empty `Prop`-inductive, hence
/// `0`" and "the conditional singleton `{x ∈ 1 : ⊥}`" — agree, so the anchor
/// holds whichever route an interpretation takes. `⊢ ¬⊥` is reflexivity of `⊥`,
/// since `¬φ` is `φ → ⊥`.
pub fn bot_is_false(env: &mut Env, s: &Sums, c: &Term, chi: &Thm) -> Option<Thm> {
    let bot = Formula::false_();
    let out = Thm::mp(&crate::prop::cond_false(env, s, &bot, c, chi)?, &imp_refl(bot))?;
    (*out.concl() == Formula::eq(c.clone(), false_set(s))).then_some(out)
}

/// `⊢ ∀p ∀x. ((p ∈ ⟦Prop⟧ ∧ x ∈ p) → x = •)` — **proof irrelevance, for every
/// proposition at once**.
///
/// A member of `{0,1}` is `∅`, which has no elements, or `1`, all of whose
/// elements are `•` ([`crate::sums::unit_eta`]). No axiom, and no appeal to how
/// the proposition was built.
pub fn prop_subsingleton(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (zero, one, pt) = (s.zero(), s.unit(), s.point());
    let pv = truth_values(s);
    let (pver, xv) = (env.fresh_var(), env.fresh_var());
    let (tp, tx) = (Term::var(pver), Term::var(xv));

    let in_pv = Formula::mem(tp.clone(), pv.clone());
    let in_p = Formula::mem(tx.clone(), tp.clone());
    let h = Formula::and(in_pv.clone(), in_p.clone());
    let goal = Formula::eq(tx.clone(), pt.clone());

    let hp = and_left(in_pv.clone(), in_p.clone()); // H → p ∈ {0,1}
    let hx = and_right(in_pv, in_p); // H → x ∈ p

    // H → (p = 0 ∨ p = 1), i.e. H → (¬(p = 0) → p = 1).
    let at = inst_all(&s.ap.sets.up_ax, &[zero.clone(), one.clone(), tp.clone()])?;
    let h_disj = syl(&hp, &crate::iff_mp(&at)?)?;

    // One branch per truth value: rewrite `p` and read off `x`.
    let branch = |env: &mut Env, v: &Term, finish: &Thm| -> Option<Thm> {
        let w = env.fresh_var();
        let carry = Thm::eq_leibniz(
            tp.clone(),
            v.clone(),
            w,
            Formula::mem(tx.clone(), Term::var(w)),
        ); // `p = v → (x ∈ p → x ∈ v)`
        let staged = syl(&hx, &com12(&carry)?)?; // H → (p = v → x ∈ v)
        syl(&staged, &imp_mono_r(finish, Formula::eq(tp.clone(), v.clone()))?)
    };

    // `x ∈ 0` is refutable, so the `p = 0` branch proves anything.
    let void = syl(
        &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tx))?,
        &ex_falso(goal.clone()),
    )?;
    let case0 = branch(env, &zero, &void)?;
    let case1 = branch(env, &one, &inst_all(&s.unit_eta, std::slice::from_ref(&tx))?)?;

    // H → (¬(p = 0) → x = •), by composing the disjunction with the `p = 1` case.
    let case_not0 = hyp_syl(&h_disj, &case1)?;
    let out = hyp_cases(&case0, &case_not0)?;
    if *out.concl() != Formula::imp(h, goal) {
        return None
    }
    Some(gen_all(&[pver, xv], &out))
}

/// [`crate::funcs::cases`] under a fixed hypothesis: from `⊢ H → (φ → χ)` and
/// `⊢ H → (¬φ → χ)` infer `⊢ H → χ`.
///
/// The same three moves as `cases` — contrapose the positive branch, chain it
/// into the negative one to get `¬χ → χ`, and collapse that with Clavius' law —
/// but every step taken under `H`, since a Hilbert system has no way to discharge
/// `H` and put it back.
fn hyp_cases(pos: &Thm, neg: &Thm) -> Option<Thm> {
    let (_, imp) = pos.concl().as_imp()?;
    let (phi, chi) = imp.as_imp()?;
    // `(φ → χ) → (¬χ → ¬φ)` is syllogism with `⊥` as the far end.
    let contra = syl_imp(phi, chi.clone(), Formula::false_());
    let h_nn = syl(pos, &contra)?; // H → (¬χ → ¬φ)
    let h_loop = hyp_syl(&h_nn, neg)?; // H → (¬χ → χ)
    syl(&h_loop, &clavius(chi))
}
