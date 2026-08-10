//! **Propositional extensionality** — two subsets of `1` that inhabit each
//! other are the same set.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀x ∀y. ((x ⊆ 1 ∧ (y ⊆ 1 ∧ ((• ∈ x → • ∈ y) ∧ (• ∈ y → • ∈ x)))) → x = y)
//! ```
//!
//! — [`prop_ext`], and that is the whole module. The antecedent is the
//! **right-nested** conjunction [`crate::conj_of`] builds, so a caller holding
//! the four facts separately folds them with [`crate::and_intro`] and applies.
//!
//! # Why it is a theorem and not an axiom
//!
//! Lean's `propext : (a ↔ b) → a = b` is one of its three standard axioms, and
//! the set-theoretic model *validates* it: `⟦Prop⟧` is `U₀ = {∅, {•}}`, so a
//! proposition's denotation is a subset of `1`, and a subset of `1` is
//! determined by whether `•` is in it. Two of them that imply each other
//! therefore have the same members, and Extensionality closes it. Carneiro,
//! *The Type Theory of Lean* §6.3, states exactly this: propositional
//! extensionality needs no set-theoretic axiom beyond Extensionality — unlike
//! choice, which needs [`kernel::Thm::ax_choice`] (see
//! [`crate::choice`]'s header, which draws the same contrast).
//!
//! **`⊆ 1`, not `∈ U₀`.** The two are interchangeable here — every member of
//! `U₀` is a subset of `1` — but `⊆ 1` is the weaker hypothesis and the one a
//! consumer already holds: `mini`'s `rec_prop::subset_of_unit` produces
//! precisely [`kernel::thm::subset`]`(env, B, 1)` out of `⊢ B ∈ U₀`, and this
//! module then owes nothing to the tower. A statement over `U₀` would drag
//! [`crate::tower`] into a file that is one Extensionality.
//!
//! # The derivation
//!
//! Extensionality wants `∀z. (z ∈ x ↔ z ∈ y)`, and the hypotheses are about
//! `•` alone, so each direction has to move an arbitrary `z` onto `•` and back:
//!
//! ```text
//! z ∈ x   and  x ⊆ 1   ⟹  z ∈ 1  ⟹  z = •       [Sums::unit_eta]
//! z = •   and  z ∈ x                ⟹  • ∈ x       [Thm::eq_leibniz]
//! • ∈ x   and  • ∈ x → • ∈ y        ⟹  • ∈ y
//! • = z   and  • ∈ y                ⟹  z ∈ y       [Thm::eq_leibniz]
//! ```
//!
//! and the other direction is the same four steps with `x` and `y` swapped —
//! which is why [`half`] is a function of *which* pair it is over and is called
//! twice, rather than written out twice. The subsingleton step is what makes
//! this true only for subsets of `1`: without `x ⊆ 1` there is a `z ∈ x` that
//! is not `•` and the hypotheses say nothing about it.
//!
//! The whole derivation runs under the antecedent, in the `⊢ H → φ`
//! hypothesis form the rest of `derived` uses; the inner `z ∈ x` is carried by
//! working under `H ∧ z ∈ x` and [`crate::uncurry`]ing at the end, which is the
//! shape [`crate::rules::uncurry`]'s own comment describes.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::sums::Sums;
use crate::{a1i, and_left, and_right, conj_of, conj_proj, eq_symm_imp, gen_all, hyp_mp, inst_all, syl, uncurry};

/// `⊢ ∀x ∀y. ((x ⊆ 1 ∧ (y ⊆ 1 ∧ ((• ∈ x → • ∈ y) ∧ (• ∈ y → • ∈ x)))) → x = y)`.
///
/// `s` is threaded rather than rebuilt for [`crate::prop`]'s standing reason:
/// two `Sums` would mean two different `1`s, and `unit_eta` would then be about
/// a unit set the caller's `⊆ 1` is not.
pub fn prop_ext(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (pt, unit) = (s.point(), s.unit());
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));

    let px = kernel::thm::subset(env, tx.clone(), unit.clone());
    let py = kernel::thm::subset(env, ty.clone(), unit);
    let mem = |t: &Term| Formula::mem(pt.clone(), t.clone());
    let sxy = Formula::imp(mem(&tx), mem(&ty));
    let syx = Formula::imp(mem(&ty), mem(&tx));
    // The order is the interface: `x ⊆ 1`, `y ⊆ 1`, then the two implications
    // in the same order. [`half`] indexes into it and so does every caller.
    let atoms = [px, py, sxy, syx];
    let h = conj_of(&atoms)?;

    // One `z` for both halves and for Extensionality's own binder: `Formula::forall`
    // closes it, so the two `iff` sides and the axiom's body agree by construction.
    let z = env.fresh_var();
    let fwd = half(env, s, &atoms, &h, z, (&tx, &ty), (0, 2))?;
    let bwd = half(env, s, &atoms, &h, z, (&ty, &tx), (1, 3))?;
    // `φ ↔ ψ` is `(φ → ψ) ∧ (ψ → φ)`, so the two halves conjoin into it directly.
    let iff = crate::hyp_and(&fwd, &bwd)?;
    let body = Formula::iff(
        Formula::mem(Term::var(z), tx.clone()),
        Formula::mem(Term::var(z), ty.clone()),
    );
    if *iff.concl() != Formula::imp(h.clone(), body.clone()) {
        return None
    }
    // `⊢ H → ∀z. (z ∈ x ↔ z ∈ y)`. `ax_dist`'s side condition is real and is
    // checked by the kernel: `H` mentions `x`, `y` and `•` and not `z`.
    let dist = Thm::ax_dist(z, h.clone(), body)?;
    let same = Thm::mp(&dist, &Thm::gen(z, &iff))?;

    let ext = inst_all(&Thm::ax_extensionality(env), &[tx.clone(), ty.clone()])?;
    let out = syl(&same, &ext)?;
    if *out.concl() != Formula::imp(h, Formula::eq(tx, ty)) {
        return None
    }
    Some(gen_all(&[xv, yv], &out))
}

/// `⊢ H → (z ∈ from → z ∈ to)`, for one of the two directions.
///
/// `sides` is `(from, to)` and `idx` is `(the index of `from ⊆ 1` in `atoms`,
/// the index of `• ∈ from → • ∈ to`)`. Both are passed rather than derived from
/// a boolean so that the caller's two calls read as the two statements they are.
fn half(
    env: &mut Env,
    s: &Sums,
    atoms: &[Formula; 4],
    h: &Formula,
    z: FreeVar,
    sides: (&Term, &Term),
    idx: (usize, usize),
) -> Option<Thm> {
    let (from, to) = sides;
    let (p_i, s_i) = idx;
    let pt = s.point();
    let tz = Term::var(z);
    let z_in_from = Formula::mem(tz.clone(), from.clone());
    // Everything below is under `G = H ∧ z ∈ from`; `uncurry` splits it back
    // into the two antecedents at the end.
    let g = Formula::and(h.clone(), z_in_from.clone());
    let g_h = and_left(h.clone(), z_in_from.clone());
    let g_from = and_right(h.clone(), z_in_from);

    // `⊢ G → z ∈ 1`, through `from ⊆ 1` instantiated at this `z`.
    let g_sub = syl(&g_h, &conj_proj(atoms, p_i)?)?;
    let g_sub_z = syl(&g_sub, &Thm::ax_inst(atoms[p_i].clone(), tz.clone())?)?;
    let g_z1 = hyp_mp(&g_sub_z, &g_from)?;

    // `⊢ G → z = •` — the subsingleton step, and the only place `⊆ 1` is used.
    let g_zpt = hyp_mp(&a1i(&inst_all(&s.unit_eta, std::slice::from_ref(&tz))?, g.clone()), &g_z1)?;

    // `⊢ G → • ∈ from`, then the caller's implication, then back onto `z`.
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(tz.clone(), pt.clone(), w, Formula::mem(Term::var(w), from.clone()));
    let g_pt_from = hyp_mp(&hyp_mp(&a1i(&leib, g.clone()), &g_zpt)?, &g_from)?;
    let g_imp = syl(&g_h, &conj_proj(atoms, s_i)?)?;
    let g_pt_to = hyp_mp(&g_imp, &g_pt_from)?;

    let g_ptz = hyp_mp(&a1i(&eq_symm_imp(env, tz.clone(), pt.clone()), g.clone()), &g_zpt)?;
    let w2 = env.fresh_var();
    let back = Thm::eq_leibniz(pt, tz.clone(), w2, Formula::mem(Term::var(w2), to.clone()));
    let g_z_to = hyp_mp(&hyp_mp(&a1i(&back, g), &g_ptz)?, &g_pt_to)?;

    let out = uncurry(&g_z_to)?;
    (*out.concl()
        == Formula::imp(
            h.clone(),
            Formula::imp(Formula::mem(tz.clone(), from.clone()), Formula::mem(tz, to.clone())),
        ))
    .then_some(out)
}
