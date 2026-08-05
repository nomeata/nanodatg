//! The three internal helpers shared by the constructions in [`crate::wpath`].
//!
//! **Nothing here is exported and nothing here is a theorem about sets.** The
//! kernel is Hilbert style and has no deduction theorem, so every derivation in
//! this module runs as `H → …`; these are the three moves that shape makes
//! repetitive, and doing them by hand each time is where the formulas drift.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::sums::Sums;
use crate::{a1i, hyp_mp, inst_all, syl};

/// From `⊢ H → ∀x. φ` infer `⊢ H → φ[t/x]`.
pub(super) fn hyp_inst(h_all: &Thm, t: &Term) -> Option<Thm> {
    let (_, all) = h_all.concl().as_imp()?;
    syl(h_all, &Thm::ax_inst(all, t.clone())?)
}

/// From `⊢ H → ∀x. (P → Q)` and `⊢ H → P[t/x]` infer `⊢ H → Q[t/x]`.
pub(super) fn hyp_inst_mp(h_all: &Thm, t: &Term, h_arg: &Thm) -> Option<Thm> {
    hyp_mp(&hyp_inst(h_all, t)?, h_arg)
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, given that `v` is not free in `H`.
///
/// The `∀`-distribution axiom, with the generalisation already applied — the
/// move that closes every `∀`-quantified conclusion in this module.
pub(super) fn gen_under(v: FreeVar, h: &Formula, body: &Formula, thm: &Thm) -> Option<Thm> {
    Thm::mp(&Thm::ax_dist(v, h.clone(), body.clone())?, &Thm::gen(v, thm))
}

/// From `⊢ H → a = b` infer `⊢ H → (φ[a/w] → φ[b/w])`.
pub(super) fn hyp_leibniz(h_eq: &Thm, w: FreeVar, phi: &Formula) -> Option<Thm> {
    let (h, eq) = h_eq.concl().as_imp()?;
    let (a, b) = eq.as_eq()?;
    hyp_mp(&a1i(&Thm::eq_leibniz(a, b, w, phi.clone()), h), h_eq)
}

/// `⊢ ∀x ∀y. (⟨x,y⟩ = ∅ → ⊥)` — **a Kuratowski pair is not the empty set**.
///
/// The one fact that separates the two path rules: the root path is `∅` and a
/// step path is `⟨b,s⟩`, so every case analysis over
/// [`super::path_arises`] closes one of its two branches with this. `{x}` is a
/// member of `⟨x,y⟩ = {{x},{x,y}}` and `∅` has no members.
pub(super) fn pair_not_empty(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let up = s.ap.sets.up;
    let sing = crate::singleton(up, tx.clone());
    let pair = crate::opair(up, tx.clone(), ty.clone());
    let zero = s.zero();

    // `{x} ∈ ⟨x,y⟩`, from the pairing axiom's left disjunct.
    let mem_ax = inst_all(
        &s.ap.sets.up_ax,
        &[sing.clone(), Term::apply(up, vec![tx.clone(), ty.clone()]), sing.clone()],
    )?;
    let disj = Thm::mp(
        &crate::funcs::or_intro_left(
            Formula::eq(sing.clone(), sing.clone()),
            Formula::eq(sing.clone(), Term::apply(up, vec![tx.clone(), ty.clone()])),
        ),
        &Thm::eq_refl(sing.clone()),
    )?;
    let in_pair = Thm::mp(&crate::iff_mpr(&mem_ax)?, &disj)?;
    if *in_pair.concl() != Formula::mem(sing.clone(), pair.clone()) {
        return None
    }

    // `⟨x,y⟩ = ∅` moves it into `∅`, which has no members.
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        pair.clone(),
        zero.clone(),
        hole,
        Formula::mem(sing.clone(), Term::var(hole)),
    );
    let none = inst_all(&s.ap.empty_ax, std::slice::from_ref(&sing))?;
    let eq_f = Formula::eq(pair, zero);
    let out = syl(&hyp_mp(&carry, &a1i(&in_pair, eq_f))?, &none)?;
    Some(Thm::gen(xv, &Thm::gen(yv, &out)))
}
