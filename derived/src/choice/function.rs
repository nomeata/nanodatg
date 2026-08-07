//! The choice function.
//!
//! # Interface
//!
//! Private to [`crate::choice`]. `choice_fn_existence` and
//! `choice_fn_on_universe` produce the function `ax_choice` asserts;
//! `choice_app` gives the property of its values in the `app` form the rest of
//! the development uses; `choice_nonvacuous` shows the statement is not about an
//! unsatisfiable antecedent.
//!
//! # What this rests on
//!
//! Extensionality, Pairing (through `upair`), and [`kernel::Thm::ax_choice`] —
//! plus the whole of [`super::bridge`], which is what turns the axiom's
//! *described* pairs into the terms `app` is defined over.
//!
//! Note what it does **not** rest on: neither propositional extensionality nor
//! quotients needed a set-theoretic axiom — the first is case analysis inside
//! `U₀ = {∅,{•}}` closed by Extensionality (§6.3), the second is Separation plus
//! Replacement on `ᾱ/∼` (§6.2). Choice was the only one of Lean's three
//! non-primitive axioms that needed anything new.

use kernel::{Env, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::funspace::is_single_valued;
use crate::{
    a1i, and_intro, and_left, and_right, exists_intro_imp, exists_mono, gen_all, hyp_and, hyp_mp,
    iff_mp, iff_mpr, imp_refl, inst_all, mpd_const, syl, uncurry,
};

use super::shared::{and_cong_imp, discharge, hyp_eq_symm, hyp_gen_all, hyp_leibniz, inst_all_imp};
use super::bridge::and_left_of;

/// `⊢ ∃f. IsChoiceFn(f, u)` — a choice function exists on any set at all, and
/// in particular on a universe.
///
/// One instantiation of [`kernel::Thm::ax_choice`]. It is stated at an arbitrary
/// term because that is what the axiom says; [`choice_fn_on_universe`] is the
/// specialisation the model actually uses.
pub fn choice_fn_existence(env: &mut Env, u: &Term) -> Option<Thm> {
    inst_all(&Thm::ax_choice(env), std::slice::from_ref(u))
}

/// `⊢ ∀x ∃f. IsChoiceFn(f, U(x))` — a choice function on the least universe
/// containing `x`.
///
/// This is Carneiro's `ε`, as closely as this development can name it: the
/// thesis fixes one choice function on `U_ω` (§6.2), and `U(x)` is what stands
/// in for a universe here. Note the quantifier order — the universe is chosen
/// first and the function second, which is what makes this *set*-sized choice
/// rather than global choice.
pub fn choice_fn_on_universe(env: &mut Env, lu: kernel::FnSym) -> Option<Thm> {
    let x = env.fresh_var();
    let u = Term::apply(lu, vec![Term::var(x)]);
    Some(Thm::gen(x, &choice_fn_existence(env, &u)?))
}

/// `⊢ ∀f ∀u ∀x. (IsChoiceFn(f,u) → ((x ∈ u ∧ ∃w. w ∈ x) → app(f,x) ∈ x))` —
/// **the lemma a caller needs**.
///
/// Everything else in this module exists to make this statement usable: the
/// hypothesis is exactly the body of the axiom's existential, so
/// [`choice_fn_existence`] discharges it, and the conclusion is about `app`, so
/// the rest of the development can consume it.
///
/// Three of the four clauses of `IsChoiceFn` are used. Totality supplies a `b`
/// with `⟨x,b⟩ ∈ f`; single-valuedness turns that into `app(f,x) = b`, via
/// [`crate::ext::app_of_pair`]; and the choice clause — the only one that
/// mentions the non-emptiness guard — gives `b ∈ x`. The first clause, which
/// bounds `f`'s domain by `u`, is not needed and is carried only because the
/// axiom states it.
pub fn choice_app(env: &mut Env, ap: &Apply, bridge: &Thm, app_pair: &Thm) -> Option<Thm> {
    let (f, u, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, tu, tx) = (Term::var(f), Term::var(u), Term::var(x));

    // The four clauses, read off the axiom's own body rather than rebuilt.
    let h = kernel::thm::is_choice_fn(env, tf.clone(), tu.clone());
    let (c1, r1) = crate::empty::split_and(&h).ok()?;
    let (c2, r2) = crate::empty::split_and(&r1).ok()?;
    let (c3, c4) = crate::empty::split_and(&r2).ok()?;
    let h_r1 = and_right(c1, r1); // ⊢ H → (C₂ ∧ (C₃ ∧ C₄))
    let h_c2 = syl(&h_r1, &and_left(c2.clone(), r2.clone()))?; // ⊢ H → C₂
    let h_r2 = syl(&h_r1, &and_right(c2.clone(), r2))?;
    let h_c3 = syl(&h_r2, &and_left(c3.clone(), c4.clone()))?; // ⊢ H → C₃
    let h_c4 = syl(&h_r2, &and_right(c3.clone(), c4.clone()))?; // ⊢ H → C₄

    // ── single-valuedness, in the constructed-pair form ──────────────────────
    let (sx, sy, sy2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tsx, tsy, tsy2) = (Term::var(sx), Term::var(sy), Term::var(sy2));
    let h_sv_body = {
        let inst = syl(&h_c2, &inst_all_imp(&c2, &[tsx.clone(), tsy.clone(), tsy2.clone()])?)?;
        let br1 = inst_all(bridge, &[tf.clone(), tsx.clone(), tsy.clone()])?;
        let br2 = inst_all(bridge, &[tf.clone(), tsx.clone(), tsy2.clone()])?;
        let conv = and_cong_imp(&iff_mpr(&br1)?, &iff_mpr(&br2)?)?;
        crate::funcs::hyp_syl(&a1i(&conv, h.clone()), &inst)?
    };
    let h_sv = hyp_gen_all(&[sy2, sy, sx], &h_sv_body)?;
    let sv = is_single_valued(env, &ap.sets, &tf);
    if h_sv.concl().as_imp()?.1 != sv {
        return None
    }

    // ── totality, in the constructed-pair form ───────────────────────────────
    let bv = env.fresh_var();
    let tbv = Term::var(bv);
    let mem_xb = Formula::mem(ap.sets.pair(tx.clone(), tbv.clone()), tf.clone());
    let h_total = {
        let inst = syl(&h_c3, &inst_all_imp(&c3, std::slice::from_ref(&tx))?)?;
        let br = inst_all(bridge, &[tf.clone(), tx.clone(), tbv.clone()])?;
        let mono = exists_mono(bv, &Thm::gen(bv, &iff_mp(&br)?))?;
        crate::funcs::hyp_syl(&inst, &a1i(&mono, h.clone()))?
    };

    // ── the caller's hypothesis, and the two of them together ────────────────
    let guard = Formula::and(
        Formula::mem(tx.clone(), tu.clone()),
        kernel::thm::nonempty(env, tx.clone()),
    );
    let h2 = Formula::and(h.clone(), guard.clone());
    let h2_h = and_left(h.clone(), guard.clone());
    let h2_guard = and_right(h.clone(), guard.clone());
    let h2_ex = hyp_mp(&syl(&h2_h, &h_total)?, &syl(&h2_guard, &and_left_of(&guard))?)?;

    // ── the choice clause, in the constructed-pair form ──────────────────────
    let h_choose = {
        let inst = syl(&h_c4, &inst_all_imp(&c4, &[tx.clone(), tbv.clone()])?)?;
        let br = inst_all(bridge, &[tf.clone(), tx.clone(), tbv.clone()])?;
        let conv = and_cong_imp(&imp_refl(guard.clone()), &iff_mpr(&br)?)?;
        crate::funcs::hyp_syl(&a1i(&conv, h.clone()), &inst)?
    };

    // ── under a witness `b` ──────────────────────────────────────────────────
    let k = Formula::and(h2.clone(), mem_xb.clone());
    let k_h2 = and_left(h2.clone(), mem_xb.clone());
    let k_mem = and_right(h2, mem_xb.clone());
    let k_h = syl(&k_h2, &h2_h)?;
    let k_guard = syl(&k_h2, &h2_guard)?;

    // `app(f,x) = b`, from single-valuedness.
    let k_sv = syl(&k_h, &h_sv)?;
    let k_pair = hyp_and(&k_sv, &k_mem)?;
    let k_eq = syl(&k_pair, &inst_all(app_pair, &[tf.clone(), tx.clone(), tbv.clone()])?)?;

    // `b ∈ x`, from the choice clause.
    let k_b_in_x = hyp_mp(&syl(&k_h, &h_choose)?, &hyp_and(&k_guard, &k_mem)?)?;

    let goal = Formula::mem(ap.apply(tf.clone(), tx.clone()), tx.clone());
    let w = env.fresh_var();
    let k_goal = {
        let symm = hyp_eq_symm(env, &k_eq)?; // ⊢ K → b = app(f,x)
        let carry = hyp_leibniz(&symm, w, &Formula::mem(Term::var(w), tx.clone()))?;
        hyp_mp(&carry, &k_b_in_x)?
    };
    if *k_goal.concl() != Formula::imp(k, goal.clone()) {
        return None
    }

    let out = uncurry(&discharge(bv, &h2_ex, &k_goal)?)?;
    Some(gen_all(&[f, u, x], &out))
}

/// `⊢ ∃f. (IsChoiceFn(f, {{∅}}) ∧ app(f,{∅}) = ∅)` — **the antecedent of
/// [`choice_app`] is satisfiable, and has bite.**
///
/// Without this every lemma above is vacuous: `IsChoiceFn(f,u) → …` says
/// nothing if nothing is a choice function. The witness set is concrete and
/// inhabited — `{{∅}}`, whose one member `{∅}` is itself non-empty — so the
/// guard on the choice clause is *discharged* rather than dodged.
///
/// The equation is the point. Nothing in the first three clauses of
/// `IsChoiceFn` determines `app(f,{∅})`: they say only that `f` is a function
/// with domain `{{∅}}`, and its value at `{∅}` could a priori be anything. It
/// is the fourth clause — the choice clause, the one this whole axiom exists
/// for — that forces the value to lie in `{∅}`, hence to be `∅`. So this
/// derivation is evidence not merely that the hypothesis is satisfiable, but
/// that it says something.
pub fn choice_nonvacuous(env: &mut Env, ap: &Apply, choice_app_thm: &Thm) -> Option<Thm> {
    let empty = Term::apply(ap.empty, vec![]);
    let s_empty = crate::singleton(ap.sets.up, empty.clone()); // {∅}
    let ss_empty = crate::singleton(ap.sets.up, s_empty.clone()); // {{∅}}

    let existence = choice_fn_existence(env, &ss_empty)?;
    let f = env.fresh_var();
    let tf = Term::var(f);
    let hyp = kernel::thm::is_choice_fn(env, tf.clone(), ss_empty.clone());
    if *existence.concl() != Formula::exists(f, hyp.clone()) {
        return None
    }

    // ⊢ {∅} ∈ {{∅}}, and ⊢ ∃w. w ∈ {∅} — the guard, discharged.
    let mem_here = inst_all(&ap.mem_sing, &[s_empty.clone(), s_empty.clone()])?;
    let s_in_ss = Thm::mp(&iff_mpr(&mem_here)?, &Thm::eq_refl(s_empty.clone()))?;
    let mem_inner = inst_all(&ap.mem_sing, &[empty.clone(), empty.clone()])?;
    let e_in_s = Thm::mp(&iff_mpr(&mem_inner)?, &Thm::eq_refl(empty.clone()))?;
    let w = env.fresh_var();
    let ne = Thm::mp(
        &exists_intro_imp(w, Formula::mem(Term::var(w), s_empty.clone()), empty.clone())?,
        &e_in_s,
    )?;
    let guard = and_intro(&s_in_ss, &ne);

    // The main lemma at (f, {{∅}}, {∅}), with its guard discharged.
    let at = inst_all(choice_app_thm, &[tf.clone(), ss_empty, s_empty.clone()])?;
    let (_, rest) = at.concl().as_imp()?;
    let (g, _) = rest.as_imp()?;
    if g != *guard.concl() {
        return None
    }
    let h_mem = mpd_const(&at, &guard)?; // ⊢ IsChoiceFn(f,{{∅}}) → app(f,{∅}) ∈ {∅}

    // Membership in a singleton is equality.
    let app_t = ap.apply(tf, s_empty.clone());
    let mem_app = inst_all(&ap.mem_sing, &[empty, app_t])?;
    let h_eq = syl(&h_mem, &iff_mp(&mem_app)?)?;

    let paired = hyp_and(&imp_refl(hyp.clone()), &h_eq)?;
    Thm::mp(&exists_mono(f, &Thm::gen(f, &paired))?, &existence)
}
