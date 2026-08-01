//! Closure under unordered pairing, and hence under the ordered pair.
//!
//! # Interface
//!
//! ```text
//! ⊢ ¬(∅ = 𝒫∅) ∧ (¬(∅ = 𝒫𝒫∅) ∧ ¬(𝒫∅ = 𝒫𝒫∅))                    [power_tower_distinct]
//! ⊢ ∀u ∀a. ((is_universe(u) ∧ a ∈ u) → (∅ ∈ u ∧ (𝒫∅ ∈ u ∧ 𝒫𝒫∅ ∈ u)))
//!                                                              [universe_three_members]
//! ⊢ ∀u ∀a ∀b ∀v₁ ∀v₂ ∀v₃. (((v₁ ∈ u ∧ (v₂ ∈ u ∧ v₃ ∈ u))
//!        ∧ (¬(v₁=v₂) ∧ (¬(v₁=v₃) ∧ ¬(v₂=v₃)))) → ¬({a,b} ≈ u)) [upair_not_equinumerous]
//! ⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → {a,b} ∈ u) [universe_pairing]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))           [least_universe_pairing]
//! ⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → ⟨a,b⟩ ∈ U(c))           [least_universe_opair]
//! ```
//!
//! The last two carry **no hypothesis at all**. Callers need none of the
//! derivations below.
//!
//! # The argument
//!
//! This is the one closure property `C₄` really does deliver, and it delivers it
//! for an *arbitrary* universe — so it transfers to `U(x)` through the
//! intersection without `is_universe(U(x))` being available. `a` and `b` are
//! members, so `{a,b} ⊆ u`, and `C₄` offers `{a,b} ≈ u` or `{a,b} ∈ u`;
//! [`upair_not_equinumerous`] kills the first disjunct, because a two-element
//! set cannot be equinumerous with a set that has **three** distinct members.
//! `∅`, `𝒫∅` and `𝒫𝒫∅` are three such members of every universe that has any
//! member at all ([`universe_three_members`], via `C₂` and then
//! [`crate::universe::universe_power_closed`] twice), and they are pairwise
//! distinct ([`power_tower_distinct`], which runs entirely off `∅ ∈ 𝒫∅` and
//! `¬(∅ ∈ ∅)`).
//!
//! [`upair_not_equinumerous`] is **the only place in the development where
//! `kernel::thm::equinumerous` is unpacked** rather than carried around whole.
//! It uses three of the five clauses of a bijection and none of the other two:
//! *onto* supplies a pre-image `pᵢ` for each `vᵢ`, the *domain* clause puts each
//! `pᵢ` in `{a,b}`, and *single-valuedness* makes distinct pre-images of
//! distinct values — so three pairwise-distinct `pᵢ` are each `a` or `b`, which
//! a pigeonhole refutes. Totality and injectivity are never touched.
//!
//! [`least_universe_opair`] is then three applications of
//! [`least_universe_pairing`]: `{a}` is `{a,a}`, `{a,b}` is a pair, and `⟨a,b⟩`
//! is the pair of those two. **No binary union is involved**, which mattered
//! when binary union was open; it is now
//! [`crate::universe::universe_bin_union`] /
//! [`crate::universe::least_universe_bin_union`], so the independence is a
//! layering convenience rather than a necessity.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::separation::hyp_syl;
use crate::{
    a1i, and_left, and_right, com12, eq_symm_imp, ex_falso, exists_elim_imp, gen_all, hyp_and,
    hyp_mp, hyp_or_elim, iff_mp, iff_mpr, imp_mono_r, imp_refl, inst_all, mpd_const, notnot_elim,
    syl, uncurry,
};
use super::shared::{hyp_contract, open_exists, split_and};
use super::predicate::is_universe;
use super::least::{in_all_universes, least_universe_mem};
use super::closure::{least_universe_transfer, universe_clauses, universe_power_closed};

/// From `⊢ (H ∧ E) → φ` and `⊢ H → ∃v. E` infer `⊢ H → φ`, discharging the
/// witness `v` (which must not occur free in `H` or `φ`).
///
/// A private copy of the combinator `crate::funspace` and `crate::ext` keep
/// privately too, on the reasoning they give: reading formulas apart produces
/// no `Thm`, so a duplicate is safe.
fn discharge(v: FreeVar, h_ex: &Thm, he_goal: &Thm) -> Option<Thm> {
    let (_, goal) = he_goal.concl().as_imp()?;
    let (h, _) = h_ex.concl().as_imp()?;
    let target = Formula::imp(h, goal);
    let elim = exists_elim_imp(v, &Thm::gen(v, &com12(&uncurry(he_goal)?)?), &target)?;
    hyp_contract(&syl(h_ex, &elim)?)
}

/// `⊢ (∀x⃗. φ) → φ[t⃗/x⃗]` — instantiation in implication form, for a quantified
/// formula that is only available under a hypothesis.
fn inst_all_imp(phi: &Formula, ts: &[Term]) -> Option<Thm> {
    let mut cur = Thm::ax_inst(phi.clone(), ts.first()?.clone())?;
    for t in &ts[1..] {
        let (_, body) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(body, t.clone())?)?;
    }
    Some(cur)
}

/// `⊢ x = t → (y = t → x = y)` — two things equal to a third are equal.
fn eq_both_imp(env: &mut Env, x: &Term, y: &Term, t: &Term) -> Option<Thm> {
    let w = env.fresh_var();
    // `t = y → (x = t → x = y)`, by Leibniz at `φ(w) := (x = w)`.
    let leib = Thm::eq_leibniz(t.clone(), y.clone(), w, Formula::eq(x.clone(), Term::var(w)));
    com12(&syl(&eq_symm_imp(env, y.clone(), t.clone()), &leib)?)
}

/// `⊢ ¬(t = s)`, from `⊢ t ∈ s` and `⊢ ¬(t ∈ t)`.
///
/// The equation would carry the membership into itself. This is the only way
/// two sets are told apart below, and it needs no Regularity: `¬(t ∈ t)` is
/// supplied by the empty set at the bottom of the tower rather than by an
/// `∈`-minimality argument.
fn distinct_by_mem(env: &mut Env, t: &Term, s: &Term, t_in_s: &Thm, not_self: &Thm) -> Option<Thm> {
    if *t_in_s.concl() != Formula::mem(t.clone(), s.clone())
        || *not_self.concl() != Formula::not(Formula::mem(t.clone(), t.clone()))
    {
        return None
    }
    let w = env.fresh_var();
    // `s = t → (t ∈ s → t ∈ t)`, composed with symmetry of the equation.
    let carry = Thm::eq_leibniz(s.clone(), t.clone(), w, Formula::mem(t.clone(), Term::var(w)));
    let step = syl(&eq_symm_imp(env, t.clone(), s.clone()), &carry)?;
    syl(&mpd_const(&step, t_in_s)?, not_self)
}

/// `⊢ ∅ ⊆ x` and `⊢ x ⊆ x`, the two inclusions the tower below rests on.
fn trivial_inclusions(env: &mut Env, empty_ax: &Thm, e: &Term, x: &Term) -> Option<(Thm, Thm)> {
    let z = env.fresh_var();
    let tz = Term::var(z);
    // `∅ ⊆ x`: nothing is in `∅`, so the implication holds by ex falso.
    let none = Thm::ax_inst(empty_ax.concl().clone(), tz.clone())?;
    let at_z = Thm::mp(&none, empty_ax)?;
    debug_assert_eq!(*at_z.concl(), Formula::not(Formula::mem(tz.clone(), e.clone())));
    let empty_sub = Thm::gen(z, &syl(&at_z, &ex_falso(Formula::mem(tz.clone(), x.clone())))?);
    debug_assert_eq!(*empty_sub.concl(), kernel::thm::subset(env, e.clone(), x.clone()));

    let v = env.fresh_var();
    let self_sub = Thm::gen(v, &imp_refl(Formula::mem(Term::var(v), x.clone())));
    debug_assert_eq!(*self_sub.concl(), kernel::thm::subset(env, x.clone(), x.clone()));
    Some((empty_sub, self_sub))
}

/// `⊢ (¬(∅ = 𝒫∅) ∧ (¬(∅ = 𝒫𝒫∅) ∧ ¬(𝒫∅ = 𝒫𝒫∅)))` — the bottom three sets of
/// the power-set tower are pairwise distinct.
///
/// Three, not two, because that is what a two-element set cannot be
/// equinumerous with. Everything runs off `∅ ∈ 𝒫∅` (the empty set is a subset
/// of anything) and `¬(∅ ∈ ∅)`; even `¬(𝒫∅ ∈ 𝒫∅)` reduces to the latter,
/// because `𝒫∅ ∈ 𝒫∅` says `𝒫∅ ⊆ ∅` and `∅ ∈ 𝒫∅`.
pub fn power_tower_distinct(
    env: &mut Env,
    empty: FnSym,
    empty_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> Option<Thm> {
    if empty.arity() != 0 || pow.arity() != 1 {
        return None
    }
    let e = Term::apply(empty, vec![]);
    let p1 = Term::apply(pow, vec![e.clone()]);
    let p2 = Term::apply(pow, vec![p1.clone()]);

    let (e_sub_e, _) = trivial_inclusions(env, empty_ax, &e, &e)?;
    let (e_sub_p1, p1_sub_p1) = trivial_inclusions(env, empty_ax, &e, &p1)?;

    // `∅ ∈ 𝒫∅`, `∅ ∈ 𝒫𝒫∅`, `𝒫∅ ∈ 𝒫𝒫∅`.
    let e_in_p1 = Thm::mp(&iff_mpr(&inst_all(pow_ax, &[e.clone(), e.clone()])?)?, &e_sub_e)?;
    let e_in_p2 = Thm::mp(&iff_mpr(&inst_all(pow_ax, &[p1.clone(), e.clone()])?)?, &e_sub_p1)?;
    let p1_in_p2 = Thm::mp(&iff_mpr(&inst_all(pow_ax, &[p1.clone(), p1.clone()])?)?, &p1_sub_p1)?;

    // `¬(∅ ∈ ∅)`, straight from the empty set.
    let not_e_in_e = Thm::mp(&Thm::ax_inst(empty_ax.concl().clone(), e.clone())?, empty_ax)?;

    // `¬(𝒫∅ ∈ 𝒫∅)`: it would say `𝒫∅ ⊆ ∅`, and `∅ ∈ 𝒫∅`.
    let p1_in_p1_iff = inst_all(pow_ax, &[e.clone(), p1.clone()])?;
    let sub_at_e = Thm::ax_inst(kernel::thm::subset(env, p1.clone(), e.clone()), e.clone())?;
    let not_p1_in_p1 = syl(
        &syl(&iff_mp(&p1_in_p1_iff)?, &mpd_const(&sub_at_e, &e_in_p1)?)?,
        &not_e_in_e,
    )?;

    let d1 = distinct_by_mem(env, &e, &p1, &e_in_p1, &not_e_in_e)?;
    let d2 = distinct_by_mem(env, &e, &p2, &e_in_p2, &not_e_in_e)?;
    let d3 = distinct_by_mem(env, &p1, &p2, &p1_in_p2, &not_p1_in_p1)?;

    let out = crate::and_intro(&d1, &crate::and_intro(&d2, &d3));
    debug_assert_eq!(
        *out.concl(),
        Formula::and(
            Formula::not(Formula::eq(e.clone(), p1.clone())),
            Formula::and(
                Formula::not(Formula::eq(e, p2.clone())),
                Formula::not(Formula::eq(p1, p2)),
            ),
        ),
        "power_tower_distinct: wrong shape"
    );
    Some(out)
}

/// `⊢ ∀u ∀a. ((is_universe(u) ∧ a ∈ u) → (∅ ∈ u ∧ (𝒫∅ ∈ u ∧ 𝒫𝒫∅ ∈ u)))` — a
/// universe with any member at all has these three.
///
/// `∅ ⊆ a`, so `C₂` puts `∅` in; [`universe_power_closed`] then climbs twice.
pub fn universe_three_members(
    env: &mut Env,
    empty: FnSym,
    empty_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> Option<Thm> {
    if empty.arity() != 0 {
        return None
    }
    let upc = universe_power_closed(env, pow, pow_ax)?;

    let (uv, av) = (env.fresh_var(), env.fresh_var());
    let (tu, ta) = (Term::var(uv), Term::var(av));
    let e = Term::apply(empty, vec![]);
    let p1 = Term::apply(pow, vec![e.clone()]);
    let p2 = Term::apply(pow, vec![p1.clone()]);

    let univ_u = is_universe(env, &tu);
    let a_in_u = Formula::mem(ta.clone(), tu.clone());
    let h = Formula::and(univ_u.clone(), a_in_u.clone());
    let h_univ = and_left(univ_u.clone(), a_in_u.clone());
    let h_a = and_right(univ_u, a_in_u);

    // `∅ ∈ u`, by `C₂` at the member `a` and the subset `∅`.
    let cl = universe_clauses(env, &tu)?;
    let (c2_u, to_c2) = (cl.c2, cl.to_c2);
    let c2_at_a = Thm::ax_inst(c2_u, ta.clone())?;
    let (_, c2_body) = c2_at_a.concl().as_imp()?;
    let (_, all_sub_u) = c2_body.as_imp()?;
    let c2_at_e = syl(&c2_at_a, &imp_mono_r(&Thm::ax_inst(all_sub_u, e.clone())?, Formula::mem(ta.clone(), tu.clone()))?)?;
    let (empty_sub, _) = trivial_inclusions(env, empty_ax, &e, &ta)?;
    let h_e = hyp_mp(
        &hyp_mp(&syl(&h_univ, &syl(&to_c2, &c2_at_e)?)?, &h_a)?,
        &a1i(&empty_sub, h.clone()),
    )?;

    // Two steps up the power-set tower.
    let climb = |env: &mut Env, from: &Term, to: &Term, h_from: &Thm| -> Option<Thm> {
        let _ = env;
        let at = inst_all(&upc, &[tu.clone(), from.clone()])?;
        if at.concl().as_imp()?.1 != Formula::mem(to.clone(), tu.clone()) {
            return None
        }
        hyp_mp(&a1i(&at, h.clone()), &hyp_and(&syl(&imp_refl(h.clone()), &h_univ)?, h_from)?)
    };
    let h_p1 = climb(env, &e, &p1, &h_e)?;
    let h_p2 = climb(env, &p1, &p2, &h_p1)?;

    let out = hyp_and(&h_e, &hyp_and(&h_p1, &h_p2)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            h,
            Formula::and(
                Formula::mem(e, tu.clone()),
                Formula::and(Formula::mem(p1, tu.clone()), Formula::mem(p2, tu)),
            ),
        ),
        "universe_three_members: wrong shape"
    );
    Some(gen_all(&[uv, av], &out))
}

/// One branch of [`pigeonhole_three`]: `⊢ H → (p₀ = first → ⊥)`.
///
/// With `p₀` pinned to `first`, neither `p₁` nor `p₂` can be `first` — that
/// would make it equal to `p₀` — so both are `second`, and they were assumed
/// distinct. `first_is_left` says which side of the disjunction `first` is on,
/// which is the only asymmetry: `x = a ∨ x = b` is `¬(x = a) → x = b`, so the
/// left disjunct is refuted by *applying* the implication and the right one by
/// contraposing it.
fn pigeonhole_branch(
    env: &mut Env,
    first: &Term,
    second: &Term,
    first_is_left: bool,
    p: &[Term; 3],
    disj: &[Thm; 3],
    ne: &[Thm; 3],
) -> Option<Thm> {
    let (h, _) = disj[0].concl().as_imp()?;
    let eq0 = Formula::eq(p[0].clone(), first.clone());
    let n = Formula::and(h.clone(), eq0.clone());
    let n_h = and_left(h.clone(), eq0.clone());
    let n_eq = and_right(h, eq0);

    let mut at_second = Vec::new();
    for i in 1..3 {
        // `N → ¬(pᵢ = first)`, since `pᵢ = first` and `p₀ = first` give `p₀ = pᵢ`.
        let both = eq_both_imp(env, &p[0], &p[i], first)?;
        let n_imp = hyp_mp(&a1i(&both, n.clone()), &n_eq)?;
        let n_not = hyp_syl(&n_imp, &syl(&n_h, &ne[i - 1])?)?;
        // `N → pᵢ = second`.
        let n_disj = syl(&n_h, &disj[i])?;
        at_second.push(if first_is_left {
            hyp_mp(&n_disj, &n_not)?
        } else {
            let goal = Formula::eq(p[i].clone(), second.clone());
            syl(&hyp_syl(&n_disj, &n_not)?, &notnot_elim(goal))?
        });
    }

    let both = eq_both_imp(env, &p[1], &p[2], second)?;
    let n_eq12 = hyp_mp(&hyp_mp(&a1i(&both, n), &at_second[0])?, &at_second[1])?;
    uncurry(&hyp_mp(&syl(&n_h, &ne[2])?, &n_eq12)?)
}

/// `⊢ H → ⊥`, from `⊢ H → (pᵢ = a ∨ pᵢ = b)` for each `i` and
/// `⊢ H → ¬(pᵢ = pⱼ)` for `(i,j)` in the order `(0,1), (0,2), (1,2)`.
///
/// Three pairwise-distinct objects do not fit in a two-element set. Purely
/// propositional plus the equality axioms — nothing set-theoretic enters.
fn pigeonhole_three(
    env: &mut Env,
    a: &Term,
    b: &Term,
    p: &[Term; 3],
    disj: &[Thm; 3],
    ne: &[Thm; 3],
) -> Option<Thm> {
    let left = pigeonhole_branch(env, a, b, true, p, disj, ne)?;
    let right = pigeonhole_branch(env, b, a, false, p, disj, ne)?;
    hyp_or_elim(&disj[0], &left, &right)
}

/// `⊢ ∀u ∀a ∀b ∀v₁ ∀v₂ ∀v₃.
///      ((((v₁ ∈ u ∧ (v₂ ∈ u ∧ v₃ ∈ u)) ∧ (¬(v₁=v₂) ∧ (¬(v₁=v₃) ∧ ¬(v₂=v₃))))
///        → ¬({a,b} ≈ u))`
///
/// **A set with three distinct members is not equinumerous with an unordered
/// pair.** This is the lemma that refutes the wrong disjunct of `C₄`, and it is
/// the only place in the development where `kernel::thm::equinumerous` is
/// unpacked rather than carried around whole.
///
/// The argument uses three of the five clauses of a bijection and none of the
/// other two: *onto* supplies a pre-image `pᵢ` for each `vᵢ`, the *domain*
/// clause puts each `pᵢ` in `{a,b}`, and *single-valuedness* makes distinct
/// pre-images of distinct values — so three pairwise-distinct `pᵢ` are each `a`
/// or `b`, which [`pigeonhole_three`] refutes. Totality and injectivity are
/// never touched.
pub fn upair_not_equinumerous(env: &mut Env, up: FnSym, up_ax: &Thm) -> Option<Thm> {
    if up.arity() != 2 {
        return None
    }
    let (uv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(uv), Term::var(av), Term::var(bv));
    let pair = Term::apply(up, vec![ta.clone(), tb.clone()]);

    let vs = [env.fresh_var(), env.fresh_var(), env.fresh_var()];
    let tv = [Term::var(vs[0]), Term::var(vs[1]), Term::var(vs[2])];

    // `D := (v₁ ∈ u ∧ (v₂ ∈ u ∧ v₃ ∈ u)) ∧ (¬(v₁=v₂) ∧ (¬(v₁=v₃) ∧ ¬(v₂=v₃)))`
    let mem_v: Vec<Formula> = (0..3).map(|i| Formula::mem(tv[i].clone(), tu.clone())).collect();
    let mems = Formula::and(mem_v[0].clone(), Formula::and(mem_v[1].clone(), mem_v[2].clone()));
    let ne_v = |i: usize, j: usize| Formula::not(Formula::eq(tv[i].clone(), tv[j].clone()));
    let dist = Formula::and(ne_v(0, 1), Formula::and(ne_v(0, 2), ne_v(1, 2)));
    let d = Formula::and(mems.clone(), dist.clone());

    let d_mems = and_left(mems.clone(), dist.clone());
    let d_dist = and_right(mems.clone(), dist.clone());
    let tail_m = Formula::and(mem_v[1].clone(), mem_v[2].clone());
    let d_v = [
        syl(&d_mems, &and_left(mem_v[0].clone(), tail_m.clone()))?,
        syl(&syl(&d_mems, &and_right(mem_v[0].clone(), tail_m.clone()))?,
            &and_left(mem_v[1].clone(), mem_v[2].clone()))?,
        syl(&syl(&d_mems, &and_right(mem_v[0].clone(), tail_m))?,
            &and_right(mem_v[1].clone(), mem_v[2].clone()))?,
    ];
    let tail_d = Formula::and(ne_v(0, 2), ne_v(1, 2));
    let d_ne = [
        syl(&d_dist, &and_left(ne_v(0, 1), tail_d.clone()))?,
        syl(&syl(&d_dist, &and_right(ne_v(0, 1), tail_d.clone()))?,
            &and_left(ne_v(0, 2), ne_v(1, 2)))?,
        syl(&syl(&d_dist, &and_right(ne_v(0, 1), tail_d))?,
            &and_right(ne_v(0, 2), ne_v(1, 2)))?,
    ];

    // The bijection, and the three clauses of it this argument uses.
    let equi = kernel::thm::equinumerous(env, pair.clone(), tu.clone());
    let fv = env.fresh_var();
    let tf = Term::var(fv);
    let body = open_exists(&equi, &tf)?;
    debug_assert_eq!(equi, Formula::exists(fv, body.clone()), "the ∃f did not reopen");
    let (in_xm, r1) = split_and(&body)?;
    let (total, r2) = split_and(&r1)?;
    let (onto, r3) = split_and(&r2)?;
    let (sv, inj) = split_and(&r3)?;

    let h = Formula::and(d.clone(), body.clone());
    let h_d = and_left(d.clone(), body.clone());
    let h_body = and_right(d.clone(), body.clone());
    let h_in_xm = syl(&h_body, &and_left(in_xm.clone(), r1.clone()))?;
    let h_r2 = syl(&syl(&h_body, &and_right(in_xm.clone(), r1))?, &and_right(total, r2))?;
    let h_onto = syl(&h_r2, &and_left(onto.clone(), r3.clone()))?;
    let h_sv = syl(&syl(&h_r2, &and_right(onto.clone(), r3))?, &and_left(sv.clone(), inj))?;

    // `H → ∃pᵢ. ⟨pᵢ, vᵢ⟩ ∈ f`, one per value, from *onto*.
    let ps = [env.fresh_var(), env.fresh_var(), env.fresh_var()];
    let tp = [Term::var(ps[0]), Term::var(ps[1]), Term::var(ps[2])];
    let mut h_ex = Vec::new();
    let mut pf = Vec::new();
    for i in 0..3 {
        let onto_at = Thm::ax_inst(onto.clone(), tv[i].clone())?;
        let (_, imp_body) = onto_at.concl().as_imp()?;
        let (_, ex_i) = imp_body.as_imp()?;
        let pi = open_exists(&ex_i, &tp[i])?;
        debug_assert_eq!(
            pi,
            kernel::thm::pair_in(env, tf.clone(), tp[i].clone(), tv[i].clone()),
            "the onto clause does not speak about ⟨p, v⟩ ∈ f"
        );
        debug_assert_eq!(ex_i, Formula::exists(ps[i], pi.clone()), "the ∃p did not reopen");
        h_ex.push(hyp_mp(&syl(&h_onto, &onto_at)?, &syl(&h_d, &d_v[i])?)?);
        pf.push(pi);
    }

    // `K₃ := ((H ∧ P₁) ∧ P₂) ∧ P₃`, with every pre-image in hand at once.
    let k1 = Formula::and(h.clone(), pf[0].clone());
    let k2 = Formula::and(k1.clone(), pf[1].clone());
    let k3 = Formula::and(k2.clone(), pf[2].clone());
    let k3_k2 = and_left(k2.clone(), pf[2].clone());
    let k3_k1 = syl(&k3_k2, &and_left(k1.clone(), pf[1].clone()))?;
    let k3_h = syl(&k3_k1, &and_left(h.clone(), pf[0].clone()))?;
    let k3_p = [
        syl(&k3_k1, &and_right(h.clone(), pf[0].clone()))?,
        syl(&k3_k2, &and_right(k1.clone(), pf[1].clone()))?,
        and_right(k2.clone(), pf[2].clone()),
    ];

    // Each pre-image lies in `{a,b}`, hence is `a` or `b`.
    let mut disj = Vec::new();
    for i in 0..3 {
        let ix = inst_all_imp(&in_xm, &[tp[i].clone(), tv[i].clone()])?;
        let both = hyp_mp(&syl(&syl(&k3_h, &h_in_xm)?, &ix)?, &k3_p[i])?;
        let in_pair = syl(&both, &and_left(Formula::mem(tp[i].clone(), pair.clone()), mem_v[i].clone()))?;
        let up_at = inst_all(up_ax, &[ta.clone(), tb.clone(), tp[i].clone()])?;
        disj.push(syl(&in_pair, &iff_mp(&up_at)?)?);
    }

    // Distinct values have distinct pre-images: single-valuedness.
    let mut ne_p = Vec::new();
    for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
        let eqp = Formula::eq(tp[i].clone(), tp[j].clone());
        let m = Formula::and(k3.clone(), eqp.clone());
        let m_k3 = and_left(k3.clone(), eqp.clone());
        let m_eq = and_right(k3.clone(), eqp);

        let w = env.fresh_var();
        let hole = kernel::thm::pair_in(env, tf.clone(), Term::var(w), tv[j].clone());
        let leib = Thm::eq_leibniz(tp[j].clone(), tp[i].clone(), w, hole);
        let carry = syl(&eq_symm_imp(env, tp[i].clone(), tp[j].clone()), &leib)?;

        let m_pj = syl(&m_k3, &k3_p[j])?;
        let m_pi_vj = hyp_mp(&hyp_mp(&a1i(&carry, m.clone()), &m_eq)?, &m_pj)?;
        let m_pi_vi = syl(&m_k3, &k3_p[i])?;
        let sv_at = inst_all_imp(&sv, &[tp[i].clone(), tv[i].clone(), tv[j].clone()])?;
        let m_eqv = hyp_mp(
            &syl(&syl(&m_k3, &syl(&k3_h, &h_sv)?)?, &sv_at)?,
            &hyp_and(&m_pi_vi, &m_pi_vj)?,
        )?;
        let m_false = hyp_mp(&syl(&m_k3, &syl(&k3_h, &syl(&h_d, &d_ne[ne_p.len()])?)?)?, &m_eqv)?;
        ne_p.push(uncurry(&m_false)?);
    }

    let disj: [Thm; 3] = [disj[0].clone(), disj[1].clone(), disj[2].clone()];
    let ne_p: [Thm; 3] = [ne_p[0].clone(), ne_p[1].clone(), ne_p[2].clone()];
    let k3_false = pigeonhole_three(env, &ta, &tb, &tp, &disj, &ne_p)?;

    // Discharge the three pre-images, then the bijection itself.
    let k1_h = and_left(h.clone(), pf[0].clone());
    let k2_h = syl(&and_left(k1.clone(), pf[1].clone()), &k1_h)?;
    let k2_false = discharge(ps[2], &syl(&k2_h, &h_ex[2])?, &k3_false)?;
    let k1_false = discharge(ps[1], &syl(&k1_h, &h_ex[1])?, &k2_false)?;
    let h_false = discharge(ps[0], &h_ex[0], &k1_false)?;

    let body_dg = com12(&uncurry(&h_false)?)?;
    let d_goal = Formula::imp(d.clone(), Formula::false_());
    let out = com12(&exists_elim_imp(fv, &Thm::gen(fv, &body_dg), &d_goal)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(d, Formula::not(equi)),
        "upair_not_equinumerous: wrong shape"
    );
    Some(gen_all(&[uv, av, bv, vs[0], vs[1], vs[2]], &out))
}

/// `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → {a,b} ∈ u)` — **every
/// universe is closed under unordered pairing**.
///
/// `a` and `b` are members, so `{a,b} ⊆ u`, and `C₄` offers `{a,b} ≈ u` or
/// `{a,b} ∈ u`. [`upair_not_equinumerous`] kills the first disjunct, using the
/// three distinct members [`universe_three_members`] supplies. This is the one
/// closure property `C₄` really does deliver, and it needs no hypothesis about
/// `u` beyond `is_universe(u)` — which is what lets it transfer to `U(x)`
/// through the intersection ([`least_universe_pairing`]) without
/// `is_universe(U(x))` ever being proved.
pub fn universe_pairing(
    env: &mut Env,
    up: FnSym,
    up_ax: &Thm,
    empty: FnSym,
    empty_ax: &Thm,
    pow: FnSym,
    pow_ax: &Thm,
) -> Option<Thm> {
    if up.arity() != 2 {
        return None
    }
    let not_equi = upair_not_equinumerous(env, up, up_ax)?;
    let three = universe_three_members(env, empty, empty_ax, pow, pow_ax)?;
    let distinct = power_tower_distinct(env, empty, empty_ax, pow, pow_ax)?;

    let (uv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, ta, tb) = (Term::var(uv), Term::var(av), Term::var(bv));
    let pair = Term::apply(up, vec![ta.clone(), tb.clone()]);

    let univ_u = is_universe(env, &tu);
    let a_in_u = Formula::mem(ta.clone(), tu.clone());
    let b_in_u = Formula::mem(tb.clone(), tu.clone());
    let both = Formula::and(a_in_u.clone(), b_in_u.clone());
    let h = Formula::and(univ_u.clone(), both.clone());
    let h_univ = and_left(univ_u.clone(), both.clone());
    let h_a = syl(&and_right(univ_u.clone(), both.clone()), &and_left(a_in_u.clone(), b_in_u.clone()))?;
    let h_b = syl(&and_right(univ_u.clone(), both), &and_right(a_in_u.clone(), b_in_u.clone()))?;

    // ── `H → {a,b} ⊆ u` ──────────────────────────────────────────────────────
    let z = env.fresh_var();
    let tz = Term::var(z);
    let z_in_pair = Formula::mem(tz.clone(), pair.clone());
    let z_in_u = Formula::mem(tz.clone(), tu.clone());
    let l = Formula::and(h.clone(), z_in_pair.clone());
    let l_h = and_left(h.clone(), z_in_pair.clone());
    let l_mem = and_right(h.clone(), z_in_pair.clone());
    let l_disj = syl(&l_mem, &iff_mp(&inst_all(up_ax, &[ta.clone(), tb.clone(), tz.clone()])?)?)?;
    let mut sides = Vec::new();
    for (t, have) in [(&ta, &h_a), (&tb, &h_b)] {
        let w = env.fresh_var();
        let carry = Thm::eq_leibniz(t.clone(), tz.clone(), w, Formula::mem(Term::var(w), tu.clone()));
        let step = com12(&syl(&eq_symm_imp(env, tz.clone(), t.clone()), &carry)?)?;
        sides.push(hyp_mp(&a1i(&step, l.clone()), &syl(&l_h, have)?)?);
    }
    let l_z_in_u = hyp_or_elim(&l_disj, &sides[0], &sides[1])?;
    let h_sub = Thm::mp(
        &Thm::ax_dist(z, h.clone(), Formula::imp(z_in_pair, z_in_u))?,
        &Thm::gen(z, &uncurry(&l_z_in_u)?),
    )?;
    let sub_f = kernel::thm::subset(env, pair.clone(), tu.clone());
    debug_assert_eq!(*h_sub.concl(), Formula::imp(h.clone(), sub_f), "the inclusion C₄ wants is not the one built");

    // ── `H → ¬({a,b} ≈ u)` ───────────────────────────────────────────────────
    let e = Term::apply(empty, vec![]);
    let p1 = Term::apply(pow, vec![e.clone()]);
    let p2 = Term::apply(pow, vec![p1.clone()]);
    let three_at = inst_all(&three, &[tu.clone(), ta.clone()])?;
    let h_mems = hyp_mp(&a1i(&three_at, h.clone()), &hyp_and(&h_univ, &h_a)?)?;
    let ne_at = inst_all(&not_equi, &[tu.clone(), ta.clone(), tb.clone(), e, p1, p2])?;
    let h_not_equi = hyp_mp(&a1i(&ne_at, h.clone()), &hyp_and(&h_mems, &a1i(&distinct, h.clone()))?)?;

    // ── `C₄`, with the equinumerosity disjunct refuted ───────────────────────
    let cl = universe_clauses(env, &tu)?;
    let (c4_u, to_c4) = (cl.c4, cl.to_c4);
    let c4_at = Thm::ax_inst(c4_u, pair.clone())?;
    let h_disj = hyp_mp(&syl(&h_univ, &syl(&to_c4, &c4_at)?)?, &h_sub)?;
    let goal = Formula::mem(pair.clone(), tu.clone());
    let equi = kernel::thm::equinumerous(env, pair, tu);
    debug_assert_eq!(
        *h_disj.concl(),
        Formula::imp(h.clone(), Formula::or(equi, goal.clone())),
        "C₄ did not instantiate to the expected disjunction"
    );
    let out = hyp_mp(&h_disj, &h_not_equi)?;
    debug_assert_eq!(*out.concl(), Formula::imp(h, goal), "universe_pairing: wrong shape");
    Some(gen_all(&[uv, av, bv], &out))
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))` — **`U(c)` is closed
/// under unordered pairing**, with no hypothesis at all.
///
/// The transfer that [`crate::universe::least_universe_closed_sub`] and
/// [`crate::universe::least_universe_closed_pow`] use, applied to [`universe_pairing`]: a
/// closure property that holds in *every* universe holds in their
/// intersection, so `is_universe(U(c))` — whose third clause is open — is not
/// needed. This is the only one of the four closure properties one would want
/// for `U(c)` that is true; see the section note below.
pub fn least_universe_pairing(
    env: &mut Env,
    lu: FnSym,
    lu_ax: &Thm,
    up: FnSym,
    pairing: &Thm,
) -> Option<Thm> {
    if lu.arity() != 1 || up.arity() != 2 {
        return None
    }
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(lu, vec![tc.clone()]);
    let pair = Term::apply(up, vec![ta.clone(), tb.clone()]);

    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let b_in_w = Formula::mem(tb.clone(), w.clone());
    let h = Formula::and(a_in_w.clone(), b_in_w.clone());
    let h_a = and_left(a_in_w.clone(), b_in_w.clone());
    let h_b = and_right(a_in_w, b_in_w);

    // A universe `u` containing `c`, held fixed until the very end.
    let uv = env.fresh_var();
    let tu = Term::var(uv);
    let univ_u = is_universe(env, &tu);
    let c_in_u = Formula::mem(tc.clone(), tu.clone());
    let a = Formula::and(univ_u.clone(), c_in_u.clone());

    let n = Formula::and(h.clone(), a.clone());
    let n_h = and_left(h.clone(), a.clone());
    let n_a = and_right(h.clone(), a.clone());
    let n_univ = syl(&n_a, &and_left(univ_u, c_in_u))?;

    let mut in_u = Vec::new();
    for (t, have) in [(&ta, &h_a), (&tb, &h_b)] {
        let transfer = least_universe_transfer(env, lu_ax, &tc, t, &tu)?;
        in_u.push(hyp_mp(&hyp_mp(&a1i(&transfer, n.clone()), &syl(&n_h, have)?)?, &n_a)?);
    }
    // `pairing` must be [`universe_pairing`] for this very `up`, rebuilt here
    // and compared — a mismatched theorem gets a rejection, not a conclusion.
    let pairing_at = inst_all(pairing, &[tu.clone(), ta.clone(), tb.clone()])?;
    let want = Formula::imp(
        Formula::and(
            is_universe(env, &tu),
            Formula::and(
                Formula::mem(ta.clone(), tu.clone()),
                Formula::mem(tb.clone(), tu.clone()),
            ),
        ),
        Formula::mem(pair.clone(), tu.clone()),
    );
    if *pairing_at.concl() != want {
        return None
    }
    let n_pair = hyp_mp(
        &a1i(&pairing_at, n.clone()),
        &hyp_and(&n_univ, &hyp_and(&in_u[0], &in_u[1])?)?,
    )?;

    // Generalise over `u`, then read the result back as membership in `U(c)`.
    let pair_in_u = Formula::mem(pair.clone(), tu);
    let h_phi = Thm::mp(
        &Thm::ax_dist(uv, h.clone(), Formula::imp(a, pair_in_u))?,
        &Thm::gen(uv, &uncurry(&n_pair)?),
    )?;
    debug_assert_eq!(
        *h_phi.concl(),
        Formula::imp(h.clone(), in_all_universes(env, &tc, &pair)),
        "the generalised membership condition is not `in_all_universes`"
    );
    let out = syl(&h_phi, &iff_mpr(&least_universe_mem(lu_ax, &tc, &pair)?)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(pair, w)),
        "least_universe_pairing: wrong shape"
    );
    Some(gen_all(&[cv, av, bv], &out))
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → ⟨a,b⟩ ∈ U(c))` — `U(c)` is closed
/// under the Kuratowski ordered pair.
///
/// Three applications of [`least_universe_pairing`]: `{a}` is `{a,a}`, `{a,b}`
/// is a pair, and `⟨a,b⟩` is the pair of those two. Nothing else is needed —
/// in particular no binary union, which is the closure property that fails
/// (see the section note below).
pub fn least_universe_opair(env: &mut Env, lu: FnSym, up: FnSym, pairing: &Thm) -> Option<Thm> {
    if lu.arity() != 1 || up.arity() != 2 {
        return None
    }
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(lu, vec![tc.clone()]);

    let a_in_w = Formula::mem(ta.clone(), w.clone());
    let b_in_w = Formula::mem(tb.clone(), w.clone());
    let h = Formula::and(a_in_w.clone(), b_in_w.clone());
    let h_a = and_left(a_in_w.clone(), b_in_w.clone());
    let h_b = and_right(a_in_w, b_in_w);

    // The pairing lemma must be the one for *this* `lu` and `up`.
    let at = |env: &mut Env, x: &Term, y: &Term| -> Option<Thm> {
        let _ = env;
        let inst = inst_all(pairing, &[tc.clone(), x.clone(), y.clone()])?;
        let want = Formula::imp(
            Formula::and(Formula::mem(x.clone(), w.clone()), Formula::mem(y.clone(), w.clone())),
            Formula::mem(Term::apply(up, vec![x.clone(), y.clone()]), w.clone()),
        );
        if *inst.concl() != want {
            return None
        }
        Some(inst)
    };

    let sing = crate::singleton(up, ta.clone());
    let upair_ab = Term::apply(up, vec![ta.clone(), tb.clone()]);
    let h_sing = hyp_mp(&a1i(&at(env, &ta, &ta)?, h.clone()), &hyp_and(&h_a, &h_a)?)?;
    let h_pair = hyp_mp(&a1i(&at(env, &ta, &tb)?, h.clone()), &hyp_and(&h_a, &h_b)?)?;
    let out = hyp_mp(
        &a1i(&at(env, &sing, &upair_ab)?, h.clone()),
        &hyp_and(&h_sing, &h_pair)?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(crate::opair(up, ta, tb), w)),
        "least_universe_opair: wrong shape"
    );
    Some(gen_all(&[cv, av, bv], &out))
}
