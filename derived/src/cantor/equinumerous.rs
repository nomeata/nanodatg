//! No member of a universe is equinumerous with it.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → ¬(y ≈ u))       [member_not_equinumerous]
//! ```
//!
//! with `≈` the `kernel::thm::equinumerous` of the axiom's fourth clause.
//! Callers need none of the derivation below.
//!
//! # Why this is the bridge, and what it costs
//!
//! `C₄` offers a disjunction — a set is a member of the universe *or* it is
//! equinumerous with it — and that is useless as a closure property until the
//! second disjunct can be refuted. This is what refutes it.
//!
//! It needs **`C₂` only**, not the transitivity clause `C₁`. That is worth
//! recording, because the plan this module was written to execute expected the
//! proof to go through `𝒫y ∈ u` and transitivity. It does not have to: `C₂`
//! says directly that a subset of a member is a member, which is all the
//! diagonal argument needs. So this theorem was available before 2026-07-31 and
//! had simply not been proved.
//!
//! The argument: a bijection `y ≈ u` is in particular a relation whose pairs
//! start in `y`, which is single-valued, and which hits every subset of `y` —
//! because every such subset is a member of `u` by `C₂`, hence in the range.
//! That is precisely the hypothesis of [`super::no_diagonal_surjection`], and
//! the point of leaving totality and injectivity out of those clauses is that
//! the bijection restricts to them without further work.

use kernel::{Env, Formula, Term, Thm};
use crate::separation::hyp_syl;
use crate::{
    a1i, and_left, and_right, com12, exists_elim_imp, gen_all, hyp_and, hyp_mp, inst_all, syl,
    uncurry,
};

use super::shared::{inst_all_imp, open_exists, split_and};
use super::clauses::{onto_subsets, pairs_start_in, single_valued};
use super::diagonal::no_surjection_onto_subsets;

/// `⊢ H → ∀z. (z ⊆ y → z ∈ u)` — the subsets of a member of `u` are members.
///
/// This is `C₂` instantiated at `y`, packaged for a caller who already holds
/// `⊢ H → is_universe(u)` and `⊢ H → y ∈ u`. It is what supplies Cantor's
/// `ONTO` clause in both theorems below: the diagonal set is a subset of the
/// index, so it has to be somewhere the bijection is onto.
pub(super) fn subsets_of_member(env: &mut Env, u: &Term, y: &Term, h_univ: &Thm, h_y: &Thm) -> Option<Thm> {
    let cl = crate::universe::universe_clauses(env, u)?;
    let c2_at_y = Thm::ax_inst(cl.c2, y.clone())?;
    hyp_mp(&syl(h_univ, &syl(&cl.to_c2, &c2_at_y)?)?, h_y)
}

/// `⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → ¬(y ≈ u))` — **no member of a universe
/// is equinumerous with it**.
///
/// This is the fact that turns `C₄` from a disjunction into a decision
/// procedure: for `y ⊆ u`, `y ∈ u` and `y ≈ u` are now mutually exclusive, so
/// `C₄` says a subset of `u` is a member exactly when it is not equinumerous
/// with `u`.
///
/// The argument: a bijection `f : y → u` is a single-valued relation whose
/// pairs start in `y` and which hits every *subset* of `y` — because a subset of
/// the member `y` is itself a member of `u` (`C₂`), and `f` is onto `u`. That is
/// exactly Cantor's three clauses at `I := y`, so
/// [`no_surjection_onto_subsets`] refutes it.
///
/// **This needs `C₂` and `C₄` only.** It was reached while looking for a use of
/// the new transitivity clause, and the honest report is that it does not need
/// one: routing "every subset of `y` is in `u`" through `𝒫y ∈ u` and
/// transitivity works, but `C₂` says it in one step. So this theorem was
/// available before 2026-07-31 and nobody had proved it. Transitivity is needed
/// further downstream — for `f ⊆ u`, where the members of `y` themselves have to
/// be members of `u` — and countermodel B in `crate::universe` is a model of
/// `C₂`, `C₃` and `C₄` in which that fails.
///
/// Note that only three of the bijection's five clauses are used — the pairs'
/// range, single-valuedness and ontoness. Totality and injectivity are not
/// touched, so the same proof refutes a mere *surjection* `y ↠ u`.
pub fn member_not_equinumerous(env: &mut Env, empty: &Thm) -> Option<Thm> {
    let cantor = no_surjection_onto_subsets(env, empty)?;

    let (uv, yv) = (env.fresh_var(), env.fresh_var());
    let (tu, ty) = (Term::var(uv), Term::var(yv));

    let univ_u = crate::universe::is_universe(env, &tu);
    let y_in_u = Formula::mem(ty.clone(), tu.clone());
    let h = Formula::and(univ_u.clone(), y_in_u.clone());
    let h_univ = and_left(univ_u.clone(), y_in_u.clone());
    let h_y = and_right(univ_u.clone(), y_in_u.clone());

    // ── `H → ∀z. (z ⊆ y → z ∈ u)` — this is `C₂` at `y`, and nothing else ────
    let h_subs_in_u = subsets_of_member(env, &tu, &ty, &h_univ, &h_y)?;

    // ── The bijection, and the three of its five clauses this uses ───────────
    let equi = kernel::thm::equinumerous(env, ty.clone(), tu.clone());
    let fv = env.fresh_var();
    let tf = Term::var(fv);
    let body = open_exists(&equi, &tf)?;
    debug_assert_eq!(equi, Formula::exists(fv, body.clone()), "the ∃f did not reopen");
    let (in_ym, r1) = split_and(&body)?;
    let (total, r2) = split_and(&r1)?;
    let (onto_u, r3) = split_and(&r2)?;
    let (sv_f, inj) = split_and(&r3)?;

    let n = Formula::and(h.clone(), body.clone());
    let n_h = and_left(h.clone(), body.clone());
    let n_body = and_right(h.clone(), body.clone());
    let n_in_ym = syl(&n_body, &and_left(in_ym.clone(), r1.clone()))?;
    let n_r2 = syl(&syl(&n_body, &and_right(in_ym.clone(), r1))?, &and_right(total, r2))?;
    let n_onto = syl(&n_r2, &and_left(onto_u.clone(), r3.clone()))?;
    let n_sv = syl(&syl(&n_r2, &and_right(onto_u.clone(), r3))?, &and_left(sv_f.clone(), inj))?;

    // `f` satisfies Cantor's three clauses at `I := y`.
    //
    // DOM is `in_ym`'s first conjunct; SV is `f`'s own; ONTO needs the inclusion
    // just proved — a subset of `y` is in `u`, and `f` is onto `u`.
    let (av, bvv) = (env.fresh_var(), env.fresh_var());
    let (ta, tbb) = (Term::var(av), Term::var(bvv));
    let p_ab = kernel::thm::pair_in(env, tf.clone(), ta.clone(), tbb.clone());
    let in_ym_at = inst_all_imp(&in_ym, &[ta.clone(), tbb.clone()])?;
    let n_dom_step = syl(
        &syl(&n_in_ym, &in_ym_at)?,
        &crate::imp_mono_r(
            &and_left(Formula::mem(ta.clone(), ty.clone()), Formula::mem(tbb.clone(), tu.clone())),
            p_ab.clone(),
        )?,
    )?;
    let n_dom = Thm::mp(
        &Thm::ax_dist(
            av,
            n.clone(),
            Formula::forall(bvv, Formula::imp(p_ab.clone(), Formula::mem(ta.clone(), ty.clone()))),
        )?,
        &Thm::gen(
            av,
            &Thm::mp(
                &Thm::ax_dist(
                    bvv,
                    n.clone(),
                    Formula::imp(p_ab, Formula::mem(ta.clone(), ty.clone())),
                )?,
                &Thm::gen(bvv, &n_dom_step),
            )?,
        ),
    )?;
    debug_assert_eq!(
        *n_dom.concl(),
        Formula::imp(n.clone(), pairs_start_in(env, &tf, &ty)),
        "the bijection's range clause is not Cantor's DOM"
    );

    let n_sv_c = {
        let want = single_valued(env, &tf);
        if sv_f != want {
            return None
        }
        n_sv
    };

    // ONTO: `b ⊆ y → b ∈ u → ∃a. ⟨a,b⟩ ∈ f`.
    let onto_at_b = Thm::ax_inst(onto_u.clone(), tbb.clone())?;
    let all_subs_in_u = h_subs_in_u.concl().as_imp()?.1;
    let n_subs_in_u = syl(&syl(&n_h, &h_subs_in_u)?, &Thm::ax_inst(all_subs_in_u, tbb.clone())?)?;
    let n_onto_step = hyp_syl(&n_subs_in_u, &syl(&n_onto, &onto_at_b)?)?;
    let b_sub_y = kernel::thm::subset(env, tbb.clone(), ty.clone());
    let (_, ex_a) = n_onto_step.concl().as_imp()?.1.as_imp()?;
    let n_onto_c = Thm::mp(
        &Thm::ax_dist(bvv, n.clone(), Formula::imp(b_sub_y, ex_a))?,
        &Thm::gen(bvv, &n_onto_step),
    )?;
    debug_assert_eq!(
        *n_onto_c.concl(),
        Formula::imp(n.clone(), onto_subsets(env, &tf, &ty)),
        "the bijection's onto clause did not restrict to the subsets of y"
    );

    // Cantor refutes the package, so the bijection cannot exist.
    let cantor_at = inst_all(&cantor, &[ty.clone(), tf.clone()])?;
    let n_false = hyp_mp(
        &a1i(&cantor_at, n.clone()),
        &hyp_and(&n_dom, &hyp_and(&n_sv_c, &n_onto_c)?)?,
    )?;
    let h_not_body = uncurry(&n_false)?;
    let out = com12(&exists_elim_imp(
        fv,
        &Thm::gen(fv, &com12(&h_not_body)?),
        &Formula::imp(h.clone(), Formula::false_()),
    )?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::not(equi)),
        "member_not_equinumerous: wrong shape"
    );
    Some(gen_all(&[uv, yv], &out))
}
