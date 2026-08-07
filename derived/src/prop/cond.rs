//! The conditional singleton.
//!
//! # Interface
//!
//! [`conditional_singleton`] introduces, for a formula `φ` with a designated
//! variable, the symbol `χ` with
//!
//! ```text
//! χ(…) = { x ∈ 1 : φ }        i.e.   χ = 1 when φ,   χ = 0 when ¬φ
//! ```
//!
//! and the lemmas that make it usable: [`cond_intro`] and [`cond_elim`] move
//! between `φ` and `• ∈ χ`, [`cond_subset_unit`] and [`cond_subsingleton`] say
//! `χ` is a subset of `1` with at most one element, and [`cond_false`] /
//! [`cond_true`] compute it at a decided `φ`. Callers need none of the
//! derivations below.
//!
//! # Why this is the whole of `Prop`
//!
//! Lean's `Prop` is interpreted as `U₀ = {0, 1}`, and a proposition is a
//! *set*: the empty one when false, the one-point one when true. A proof of `φ`
//! is then an element of `⟦φ⟧`, and proof irrelevance is
//! [`cond_subsingleton`] — two elements of a subsingleton are equal, so any two
//! proofs of the same proposition are the same set.
//!
//! One [`crate::funcs::separation_full`] builds it, and Separation is
//! unconditional, so `χ` is the intended set whether or not `φ` holds — which is
//! exactly what a *conditional* singleton has to be. No case analysis on `φ` is
//! needed to introduce the symbol; [`cond_false`] and [`cond_true`] are for
//! callers who have decided `φ` and want the value.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};
use crate::funcs::{hyp_syl, separation_full};
use crate::separation::hyp_ex_falso;
use crate::sums::Sums;
use crate::{
    a1i, and_intro_imp, and_left, and_right, com12, contrapos, eq_symm_imp, ex_falso, gen_all,
    hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all,
};

/// The membership condition `t ∈ 1 ∧ φ` that Separation cuts `[φ]` out with.
fn guard(s: &Sums, phi: &Formula, t: &Term) -> Formula {
    Formula::and(Formula::mem(t.clone(), s.unit()), phi.clone())
}

/// Instantiate a conditional singleton's characteristic theorem at `t`,
/// insisting it says precisely `t ∈ c ↔ (t ∈ 1 ∧ φ)`.
///
/// Every lemma below goes through this, so a caller cannot pass a theorem about
/// some *other* set and have the derivation silently conclude about `c`.
fn chi_at(s: &Sums, phi: &Formula, c: &Term, chi: &Thm, t: &Term) -> Option<Thm> {
    let at = inst_all(chi, std::slice::from_ref(t))?;
    if *at.concl() != Formula::iff(Formula::mem(t.clone(), c.clone()), guard(s, phi, t)) {
        return None
    }
    Some(at)
}

/// Introduce `[φ] = { x ∈ 1 : φ }` as a fresh symbol over `params`, with
/// `⊢ ∀params ∀z. (z ∈ [φ] ↔ (z ∈ 1 ∧ φ))`.
///
/// One Separation on the unit set, and nothing else: existence is
/// [`crate::funcs::separation_full`] at the superset `1`, uniqueness is
/// Extensionality via [`crate::define_by_membership`]. Conservative, like every
/// other definitional extension in this crate.
///
/// `params` must cover the free variables of `phi` — otherwise the extension
/// would be unsound, and `kernel::thm::define` refuses, so this returns `None`.
pub fn conditional_singleton(
    env: &mut Env,
    s: &Sums,
    params: &[FreeVar],
    phi: &Formula,
) -> Option<(FnSym, Thm)> {
    let z = env.fresh_var();
    if phi.occurs_free(z) {
        return None
    }
    let one = s.unit();
    let existence = separation_full(env, z, phi, &one, &s.ap.empty_ax)?;
    let cond = guard(s, phi, &Term::var(z));
    crate::define_by_membership(env, params, &existence, z, &cond)
}

/// `⊢ φ → • ∈ [φ]` — a proof of `φ` inhabits its denotation, at the point.
pub fn cond_intro(s: &Sums, phi: &Formula, c: &Term, chi: &Thm) -> Option<Thm> {
    let pt = s.point();
    let at = chi_at(s, phi, c, chi, &pt)?;
    // `• ∈ 1` is free, so the whole guard follows from `φ` alone.
    let both = hyp_and(&a1i(&s.unit_mem, phi.clone()), &imp_refl(phi.clone()))?;
    let out = crate::syl(&both, &iff_mpr(&at)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(phi.clone(), Formula::mem(pt, c.clone())),
        "cond_intro: unexpected shape"
    );
    Some(out)
}

/// `⊢ • ∈ [φ] → φ` — the denotation is not vacuously inhabited.
///
/// The useful direction: it is what stops `[φ]` from being `1` regardless of
/// `φ`, and hence what makes the interpretation *sound* rather than merely
/// well-typed.
pub fn cond_elim(s: &Sums, phi: &Formula, c: &Term, chi: &Thm) -> Option<Thm> {
    let pt = s.point();
    let at = chi_at(s, phi, c, chi, &pt)?;
    let out = crate::syl(&iff_mp(&at)?, &and_right(Formula::mem(pt.clone(), s.unit()), phi.clone()))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(pt, c.clone()), phi.clone()),
        "cond_elim: unexpected shape"
    );
    Some(out)
}

/// `⊢ [φ] ⊆ 1` — a conditional singleton is a `Prop`.
pub fn cond_subset_unit(env: &mut Env, s: &Sums, phi: &Formula, c: &Term, chi: &Thm) -> Option<Thm> {
    let z = env.fresh_var();
    let tz = Term::var(z);
    let at = chi_at(s, phi, c, chi, &tz)?;
    let body = crate::syl(&iff_mp(&at)?, &and_left(Formula::mem(tz.clone(), s.unit()), phi.clone()))?;
    let out = Thm::gen(z, &body);
    // `⊆` is spelled out rather than rebuilt through `kernel::thm::subset`,
    // which would need a fresh variable and so would run only in debug builds.
    debug_assert_eq!(
        *out.concl(),
        Formula::forall(
            z,
            Formula::imp(Formula::mem(tz.clone(), c.clone()), Formula::mem(tz, s.unit()))
        ),
        "cond_subset_unit: unexpected shape"
    );
    Some(out)
}

/// `⊢ ∀x ∀y. ((x ∈ [φ] ∧ y ∈ [φ]) → x = y)` — **proof irrelevance**.
///
/// Both members are in `1`, so [`crate::sums::unit_eta`] sends both to `•`, and
/// transitivity closes it. Note this holds whatever `φ` is: it is the reason the
/// interpretation needs no proof-irrelevance axiom.
pub fn cond_subsingleton(env: &mut Env, s: &Sums, phi: &Formula, c: &Term, chi: &Thm) -> Option<Thm> {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let pt = s.point();

    let mem_x = Formula::mem(tx.clone(), c.clone());
    let mem_y = Formula::mem(ty.clone(), c.clone());
    let h = Formula::and(mem_x.clone(), mem_y.clone());

    // `w ∈ [φ] → w ∈ 1 → w = •`, for each of the two members.
    let to_point = |v: &Term| -> Option<Thm> {
        let at = chi_at(s, phi, c, chi, v)?;
        let in_one = crate::syl(&iff_mp(&at)?, &and_left(Formula::mem(v.clone(), s.unit()), phi.clone()))?;
        crate::syl(&in_one, &inst_all(&s.unit_eta, std::slice::from_ref(v))?)
    };
    let h_x = crate::syl(&and_left(mem_x.clone(), mem_y.clone()), &to_point(&tx)?)?;
    let h_y = crate::syl(&and_right(mem_x, mem_y), &to_point(&ty)?)?;

    // `H → • = y`, then Leibniz rewrites `x = •` into `x = y`.
    let h_pt_y = crate::syl(&h_y, &eq_symm_imp(env, ty.clone(), pt.clone()))?;
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(pt, ty.clone(), w, Formula::eq(tx.clone(), Term::var(w)));
    let out = hyp_mp(&hyp_mp(&a1i(&leib, h.clone()), &h_pt_y)?, &h_x)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::eq(tx, ty)),
        "cond_subsingleton: unexpected shape"
    );
    Some(gen_all(&[x, y], &out))
}

/// `⊢ ¬φ → [φ] = 0` — a false proposition denotes the empty set.
pub fn cond_false(env: &mut Env, s: &Sums, phi: &Formula, c: &Term, chi: &Thm) -> Option<Thm> {
    let z = env.fresh_var();
    let tz = Term::var(z);
    let zero = s.zero();
    let at = chi_at(s, phi, c, chi, &tz)?;

    let nphi = Formula::not(phi.clone());
    let mem_zc = Formula::mem(tz.clone(), c.clone());
    let mem_z0 = Formula::mem(tz.clone(), zero.clone());

    // `z ∈ [φ] → φ`, contraposed against the hypothesis, refutes `z ∈ [φ]`.
    let zc_phi = crate::syl(&iff_mp(&at)?, &and_right(Formula::mem(tz.clone(), s.unit()), phi.clone()))?;
    let fwd = hyp_ex_falso(&contrapos(&zc_phi)?, mem_z0.clone()).ok()?;
    // The converse is ex falso the other way: nothing is in `∅`.
    let not_z0 = inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?;
    let bwd = a1i(&crate::syl(&not_z0, &ex_falso(mem_zc.clone()))?, nphi.clone());

    let iff_z = Formula::iff(mem_zc, mem_z0);
    let all_z = Thm::mp(&Thm::ax_dist(z, nphi.clone(), iff_z)?, &Thm::gen(z, &hyp_and(&fwd, &bwd)?))?;
    let ext = inst_all(&Thm::ax_extensionality(env), &[c.clone(), zero.clone()])?;
    let out = crate::syl(&all_z, &ext)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(nphi, Formula::eq(c.clone(), zero)),
        "cond_false: unexpected shape"
    );
    Some(out)
}

/// `⊢ φ → [φ] = 1` — a true proposition denotes the unit set.
pub fn cond_true(env: &mut Env, s: &Sums, phi: &Formula, c: &Term, chi: &Thm) -> Option<Thm> {
    let z = env.fresh_var();
    let tz = Term::var(z);
    let one = s.unit();
    let at = chi_at(s, phi, c, chi, &tz)?;

    let mem_zc = Formula::mem(tz.clone(), c.clone());
    let mem_z1 = Formula::mem(tz.clone(), one.clone());

    let fwd = a1i(&crate::syl(&iff_mp(&at)?, &and_left(mem_z1.clone(), phi.clone()))?, phi.clone());
    // Under `φ` the guard is just `z ∈ 1`, so membership goes back the other way.
    let intro = com12(&and_intro_imp(mem_z1.clone(), phi.clone()))?;
    let bwd = hyp_syl(&intro, &a1i(&iff_mpr(&at)?, phi.clone()))?;

    let iff_z = Formula::iff(mem_zc, mem_z1);
    let all_z = Thm::mp(&Thm::ax_dist(z, phi.clone(), iff_z)?, &Thm::gen(z, &hyp_and(&fwd, &bwd)?))?;
    let ext = inst_all(&Thm::ax_extensionality(env), &[c.clone(), one.clone()])?;
    let out = crate::syl(&all_z, &ext)?;

    debug_assert_eq!(
        *out.concl(),
        Formula::imp(phi.clone(), Formula::eq(c.clone(), one)),
        "cond_true: unexpected shape"
    );
    Some(out)
}
