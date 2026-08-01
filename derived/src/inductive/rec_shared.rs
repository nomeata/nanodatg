//! Small rewriting steps, in implication form, shared by the general
//! recursor's constructions ([`super::step`] through [`super::iota`]).
//!
//! **Nothing here is exported and nothing here is a theorem about sets.**
//! Every equation in the recursor argument is derived under the ambient
//! hypothesis, and there is no deduction theorem, so congruence, transport,
//! generalisation, instantiation and the two elimination folds all have to
//! exist in the `H → …` form. They are the [`crate::wlist_rec`] combinators
//! with the two-branch eliminations replaced by folds over `n` branches,
//! because that — a Rust loop where the hand-written file had two cases — is
//! the whole difference between the general recursor and `List.rec`.
//!
//! Reading a formula apart produces no `Thm`, so a helper here can fail to
//! build a theorem but never build a wrong one.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funcs::Apply;
use crate::{a1i, and_left, and_right, com12, hyp_mp, hyp_or_elim, inst_all, syl, uncurry};

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
pub(super) fn congr_ctx<F: Fn(Term) -> Term>(env: &mut Env, eq: &Thm, ctx: F) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq)?, &Thm::eq_refl(lhs))
}

/// From `⊢ x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
pub(super) fn carry_under<F: Fn(Term) -> Formula>(
    env: &mut Env,
    eq: &Thm,
    ctx: F,
    prev: &Thm,
) -> Option<Thm> {
    let (x, y) = eq.concl().as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    syl(prev, &Thm::mp(&leib, eq)?)
}

/// From `⊢ H → x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
pub(super) fn rewrite_under<F: Fn(Term) -> Formula>(
    env: &mut Env,
    h_eq: &Thm,
    ctx: F,
    h_prev: &Thm,
) -> Option<Thm> {
    let (_, eq) = h_eq.concl().as_imp()?;
    let (x, y) = eq.as_eq()?;
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    hyp_mp(&syl(h_eq, &leib)?, h_prev)
}

/// From `⊢ H → x = v` and `⊢ H → v ∈ T` infer `⊢ H → x ∈ T` — a computed
/// value carried back along its own computation.
pub(super) fn carry_back(env: &mut Env, h_eq: &Thm, h_mem: &Thm, t: &Term) -> Option<Thm> {
    let back = crate::recursion::hyp::hyp_eq_symm(env, h_eq)?;
    let tt = t.clone();
    rewrite_under(env, &back, move |w| Formula::mem(w, tt.clone()), h_mem)
}

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
pub(super) fn gen_under(v: FreeVar, h: &Formula, thm: &Thm) -> Option<Thm> {
    let (_, body) = thm.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h.clone(), body)?, &Thm::gen(v, thm))
}

/// From `⊢ H → ∀v₁…∀vₙ. φ` infer `⊢ H → φ[t₁…tₙ]`.
pub(super) fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// From `⊢ H → ⟨a,b⟩ = ⟨c,d⟩` infer `⊢ H → a = c` and `⊢ H → b = d`.
pub(super) fn split_pair(
    ap: &Apply,
    h_eq: &Thm,
    a: &Term,
    b: &Term,
    c: &Term,
    d: &Term,
) -> Option<(Thm, Thm)> {
    let inj = inst_all(&ap.pair_inj, &[a.clone(), b.clone(), c.clone(), d.clone()])?;
    let (l, r) = (Formula::eq(a.clone(), c.clone()), Formula::eq(b.clone(), d.clone()));
    let both = syl(h_eq, &inj)?;
    Some((
        syl(&both, &and_left(l.clone(), r.clone()))?,
        syl(&both, &and_right(l, r))?,
    ))
}

/// From `⊢ (H ∧ φ(q)) → χ`, with `q` free in neither `H` nor `χ`, infer
/// `⊢ H → ((∃q. φ) → χ)` — one branch of a case analysis whose case carries a
/// witness.
pub(super) fn hyp_ex_branch(qv: FreeVar, k_goal: &Thm, h: &Formula, chi: &Formula) -> Option<Thm> {
    let per = com12(&uncurry(k_goal)?)?;
    let elim = crate::exists_elim_imp(qv, &Thm::gen(qv, &per), &Formula::imp(h.clone(), chi.clone()))?;
    com12(&elim)
}

/// From `⊢ H → (d₀ ∨ (d₁ ∨ (… ∨ d_{n-1})))` and, per disjunct,
/// `⊢ H → (dᵢ → χ)`, infer `⊢ H → χ` — the `n`-branch elimination every case
/// analysis in this module runs on. `branches` must be non-empty and ordered.
pub(super) fn hyp_disj_elim(h_disj: &Thm, h: &Formula, branches: &[Thm]) -> Option<Thm> {
    let mut acc = branches.last()?.clone();
    for b in branches[..branches.len() - 1].iter().rev() {
        // `acc : H → (Rest → χ)`, `b : H → (d → χ)`; assemble `H → ((d ∨ Rest) → χ)`.
        let (_, d_imp) = b.concl().as_imp()?;
        let (d, _) = d_imp.as_imp()?;
        let (_, r_imp) = acc.concl().as_imp()?;
        let (rest, _) = r_imp.as_imp()?;
        let disj = Formula::or(d, rest);
        let k_h = and_left(h.clone(), disj.clone());
        let k_disj = and_right(h.clone(), disj.clone());
        let elim = hyp_or_elim(&k_disj, &syl(&k_h, b)?, &syl(&k_h, &acc)?)?;
        acc = uncurry(&elim)?;
    }
    hyp_mp(&acc, h_disj)
}

/// Fold `⊢ H → atomᵢ` theorems into `⊢ H → (atom₀ ∧ (atom₁ ∧ …))`, matching
/// [`crate::conj_of`]'s right nesting. `None` on an empty list.
pub(super) fn hyp_conj(thms: &[Thm]) -> Option<Thm> {
    let mut acc = thms.last()?.clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = crate::hyp_and(t, &acc)?;
    }
    Some(acc)
}

/// `⊢ H → φ` for `φ` from an unconditional theorem — [`a1i`] under the ambient
/// hypothesis, named for symmetry with the rest.
pub(super) fn under(t: &Thm, h: &Formula) -> Thm { a1i(t, h.clone()) }
