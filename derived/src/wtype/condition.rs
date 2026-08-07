//! The two membership conditions, and the symbol they define.
//!
//! # Interface
//!
//! ```text
//! closed(A,B,S) := ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), S) → ⟨a,f⟩ ∈ S))      [closed]
//! w_cond(A,B,u,z) := ∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S)              [w_cond]
//!
//! ⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) ↔ (z ∈ u ∧ w_cond(A,B,u,z)))           [w_symbol]
//! ⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) → z ∈ u)                               [w_subset]
//! ```
//!
//! Callers need none of the derivations below. Both formulas are built here in
//! one place so that every file that mentions one builds *the same* formula —
//! they are compared syntactically all over the development, and a second
//! spelling would silently stop matching.
//!
//! # Why the intersection is a condition, not a set
//!
//! The definition is "the intersection of all closed subsets of `u`", and the
//! obvious rendering is `⋂{S ∈ 𝒫u : closed(A,B,S)}`. That needs `𝒫(u)` to
//! exist as a set and then a Separation on it. Phrasing it as the *condition*
//! [`w_cond`] instead — a universally quantified implication ranging over `S`,
//! evaluated inside a single Separation on `u` — keeps the whole construction
//! to **one** Separation, and `𝒫(u)` is never needed. That is the only trick in
//! this file; everything else is bookkeeping.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::separation_full;
use crate::sums::Sums;
use crate::{and_left, gen_all, iff_mp, inst_all, opair, syl};


/// `∀a. (a ∈ A → ∀f. (f ∈ fs(B(a), S) → ⟨a,f⟩ ∈ S))` — "`S` is closed under
/// `sup`", as a formula.
///
/// `B(a)` is `app(B,a)`: the family is an ordinary set-theoretic function, so
/// the fibre is an application and nothing more.
pub fn closed(env: &mut Env, s: &Sums, a: &Term, b: &Term, set: &Term) -> Formula {
    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(fv));
    let fibre = s.ap.apply(b.clone(), ta.clone());
    Formula::forall(
        av,
        Formula::imp(
            Formula::mem(ta.clone(), a.clone()),
            Formula::forall(
                fv,
                Formula::imp(
                    Formula::mem(tf.clone(), s.fs.of(fibre, set.clone())),
                    Formula::mem(opair(s.ap.sets.up, ta, tf), set.clone()),
                ),
            ),
        ),
    )
}

/// `∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S)` — the condition Separation carves
/// `W(A,B,u)` out of `u` with.
///
/// This is "`z` is in every closed subset of `u`", i.e. membership in the
/// intersection — written as a condition so that the intersection needs no
/// `𝒫(u)` and no indexed family, only one Separation.
pub fn w_cond(env: &mut Env, s: &Sums, a: &Term, b: &Term, u: &Term, z: &Term) -> Formula {
    let sv = env.fresh_var();
    let ts = Term::var(sv);
    let guard = Formula::and(
        kernel::thm::subset(env, ts.clone(), u.clone()),
        closed(env, s, a, b, &ts),
    );
    Formula::forall(sv, Formula::imp(guard, Formula::mem(z.clone(), ts)))
}

/// Introduce `W(A,B,u) = { z ∈ u : ∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S) }`,
/// with `⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) ↔ (z ∈ u ∧ ∀S. …))`.
///
/// One Separation on `u`, exactly as [`crate::prop::conditional_singleton`] is
/// one Separation on `1`: existence is [`crate::funcs::separation_full`],
/// uniqueness is Extensionality via [`crate::define_by_membership`]. Unlike the
/// conditional singleton, the condition here is *closed* — `closed(A,B,S)` is
/// an ordinary first-order formula in `A`, `B` and `S` — so `W` is a genuine
/// ternary function symbol rather than a construction parameterised by a
/// formula.
pub fn w_symbol(env: &mut Env, s: &Sums) -> Option<(FnSym, Thm)> {
    let (av, bv, uv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu) = (Term::var(av), Term::var(bv), Term::var(uv));
    let z = env.fresh_var();
    let tz = Term::var(z);

    let cond = w_cond(env, s, &ta, &tb, &tu, &tz);
    let existence = separation_full(env, z, &cond, &tu, &s.ap.empty_ax).ok()?;
    let guard = Formula::and(Formula::mem(tz, tu), cond);
    crate::define_by_membership(env, &[av, bv, uv], &existence, z, &guard)
}

/// `⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) → z ∈ u)` — the W-type sits inside its bound.
///
/// The left conjunct of the defining biconditional, and nothing more. It is
/// what makes `W ⊆ u` available as the inclusion that [`crate::wtype::sup_mem`] moves an
/// `f ∈ fs(B(a), W)` across.
pub fn w_subset(env: &mut Env, s: &Sums, w: FnSym, w_ax: &Thm) -> Option<Thm> {
    let (av, bv, uv, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tz) = (Term::var(av), Term::var(bv), Term::var(uv), Term::var(z));

    let cond = w_cond(env, s, &ta, &tb, &tu, &tz);
    let mem_u = Formula::mem(tz.clone(), tu.clone());
    let at = inst_all(w_ax, &[ta.clone(), tb.clone(), tu.clone(), tz.clone()])?;
    let w_t = Term::apply(w, vec![ta, tb, tu]);
    if *at.concl()
        != Formula::iff(
            Formula::mem(tz.clone(), w_t.clone()),
            Formula::and(mem_u.clone(), cond.clone()),
        )
    {
        return None
    }
    let out = syl(&iff_mp(&at)?, &and_left(mem_u.clone(), cond))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(tz, w_t), mem_u),
        "w_subset: unexpected shape"
    );
    Some(gen_all(&[av, bv, uv, z], &out))
}
