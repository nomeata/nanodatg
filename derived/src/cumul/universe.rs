//! **Every stage is inside a universe that holds the seed.**
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀c ∀n. (n ∈ ω → (S ∈ U(c) → Vₙ ∈ U(c)))                  [stages_in_universe]
//! ```
//!
//! where `Vₙ = app(iter(S), n)` and `U(c)` is
//! [`crate::universe::least_universe`]. Callers need none of the derivation
//! below.
//!
//! # Why it is stated at `∀c` and not at a tower rung
//!
//! Two different universes need this, and they are not the same one:
//!
//! * `U(A)` — the *bound* the W-type is carved out of ([`crate::wlist`] uses
//!   `W(1+α,B,U(1+α))`). [`crate::wtype::w_induction`] needs `T ⊆ U(A)`, so the
//!   stages have to be inside the bound;
//! * `U₁ = U(ω)` — the universe `⟦N⟧ ∈ ⟦Type 0⟧` is a membership in. `T ∈ U₁`
//!   is what makes `W ⊆ T` worth having.
//!
//! Both are `U(c)` for a closed `c`, so one `∀c` statement serves both, and
//! nothing here mentions [`crate::tower`] at all. The two closure theorems it
//! consumes — power set and binary union, both at `∀c` — are
//! [`crate::tower::Tower`]'s `pow` and `bin_union` fields, or equivalently
//! [`crate::funspace::pow_closed`] and
//! [`crate::universe::least_universe_bin_union`] assembled directly.
//!
//! # It is not enough on its own
//!
//! `∀n ∈ ω. Vₙ ∈ U(c)` gives `T ⊆ U(c)` (by transitivity) but **not**
//! `T ∈ U(c)`: a union of `ω`-many members of a universe is a member only for a
//! size reason. See the closing note in [`crate::cumul`] for the route —
//! `T ⊆ ⋃⋃⋃iter(S)` and `iter(S) ∈ U(c)` through
//! [`crate::bound::least_universe_funspace_mem`] — and for why `ω ∈ U(c)` is
//! exactly the hypothesis that route spends.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funspace::bin_union;
use crate::recursion::{induction_scheme, Rec};
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm, gen_all, hyp_and, hyp_mp, inst_all, syl,
};

use super::stages::Stages;
use super::step::curry;

/// `⊢ ∀c ∀n. (n ∈ ω → (S ∈ U(c) → Vₙ ∈ U(c)))`.
///
/// One induction on `n`. The base is the recursion's own base equation
/// `V₀ = S`; the step is power-set closure and binary-union closure applied to
/// `G(Vₙ) = Vₙ ∪ 𝒫Vₙ`, then rewritten along the step equation.
///
/// `pow_all` must be `⊢ ∀c ∀y. (y ∈ U(c) → 𝒫y ∈ U(c))` and `bu_all`
/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a ∪ b) ∈ U(c))`, both over the same
/// power set symbol the [`super::Step`] was built with — otherwise the two
/// speak about different `𝒫` and nothing composes.
pub fn stages_in_universe(
    env: &mut Env,
    r: &Rec,
    st: &Stages,
    lu: FnSym,
    pow: FnSym,
    pow_all: &Thm,
    bu_all: &Thm,
) -> Option<Thm> {
    let (cv, nv) = (env.fresh_var(), env.fresh_var());
    let (tc, tn) = (Term::var(cv), Term::var(nv));
    let u = Term::apply(lu, vec![tc.clone()]);
    let s = Term::var(st.seed);

    let s_in = Formula::mem(s.clone(), u.clone());
    let vn = st.v(r, tn.clone());
    let phi = Formula::imp(s_in.clone(), Formula::mem(vn.clone(), u.clone()));

    // ── Base: `V₀ = S` ──────────────────────────────────────────────────────
    let v0 = st.v(r, r.zero());
    let wv = env.fresh_var();
    let base = {
        let sym = eq_symm(env, &st.rec.base)?;
        debug_assert_eq!(*sym.concl(), Formula::eq(s.clone(), v0.clone()));
        Thm::mp(
            &Thm::eq_leibniz(
                s.clone(),
                v0.clone(),
                wv,
                Formula::mem(Term::var(wv), u.clone()),
            ),
            &sym,
        )?
    };
    debug_assert_eq!(*base.concl(), phi.subst(nv, &r.zero()), "stages_in_universe: base drifted");

    // ── Step ────────────────────────────────────────────────────────────────
    let n_om = Formula::mem(tn.clone(), r.omega());
    let k = Formula::and(n_om.clone(), phi.clone());
    let j = Formula::and(k.clone(), s_in.clone());

    let j_k = and_left(k.clone(), s_in.clone());
    let j_s = and_right(k.clone(), s_in.clone());
    let j_phi = syl(&j_k, &and_right(n_om.clone(), phi.clone()))?;
    let j_vn = hyp_mp(&j_phi, &j_s)?;

    let powvn = Term::apply(pow, vec![vn.clone()]);
    let j_pow = hyp_mp(&a1i(&inst_all(pow_all, &[tc.clone(), vn.clone()])?, j.clone()), &j_vn)?;
    let bu_at = inst_all(bu_all, &[tc.clone(), vn.clone(), powvn.clone()])?;
    let j_bu = hyp_mp(&a1i(&bu_at, j.clone()), &hyp_and(&j_vn, &j_pow)?)?;
    debug_assert_eq!(
        *j_bu.concl(),
        Formula::imp(
            j.clone(),
            Formula::mem(bin_union(&r.ap.sets, vn.clone(), powvn), u.clone())
        ),
        "stages_in_universe: the binary union drifted"
    );

    // `G(Vₙ)` is that binary union, and `V₍succ n₎` is `G(Vₙ)`.
    let gvn = st.step.of(vn.clone());
    let g_eq = eq_symm(env, &inst_all(&st.step.g_ax, std::slice::from_ref(&vn))?)?;
    let carry_g = Thm::mp(
        &Thm::eq_leibniz(
            bin_union(&r.ap.sets, vn.clone(), Term::apply(pow, vec![vn.clone()])),
            gvn.clone(),
            wv,
            Formula::mem(Term::var(wv), u.clone()),
        ),
        &g_eq,
    )?;
    let j_gvn = hyp_mp(&a1i(&carry_g, j.clone()), &j_bu)?;

    let j_n = syl(&j_k, &and_left(n_om.clone(), phi.clone()))?;
    let step_eq = hyp_mp(&a1i(&inst_all(&st.rec.step, std::slice::from_ref(&tn))?, j.clone()), &j_n)?;
    let vsn = st.v(r, r.succ_of(tn.clone()));
    let carry_v = Thm::eq_leibniz(gvn, vsn.clone(), wv, Formula::mem(Term::var(wv), u.clone()));
    let j_sym = syl(&step_eq, &crate::eq_symm_imp(env, vsn.clone(), st.step.of(vn.clone())))?;
    let j_vsn = hyp_mp(&syl(&j_sym, &carry_v)?, &j_gvn)?;

    let step = curry(&j_vsn)?;
    debug_assert_eq!(
        *step.concl(),
        Formula::imp(k, phi.subst(nv, &r.succ_of(tn.clone()))),
        "stages_in_universe: step drifted"
    );

    let scheme = induction_scheme(env, r.core(), nv, &phi)?;
    let out = Thm::mp(&scheme, &and_intro(&base, &Thm::gen(nv, &step)))?;
    Some(gen_all(&[cv], &out))
}
