//! The two constructors' typing rules.
//!
//! # Interface
//!
//! Private to [`crate::wnat`]; surfaced as
//! [`Nat::zero`](crate::wnat::Nat::zero) and
//! [`Nat::succ`](crate::wnat::Nat::succ):
//!
//! ```text
//! ⊢ zero ∈ N
//! ⊢ ∀n. (n ∈ N → succ(n) ∈ N)
//! ```
//!
//! # Where the hypotheses come from, and which are real
//!
//! Both are [`crate::wtype::sup_mem`] at the corresponding tag, with the fibre
//! function supplied. For `zero` the fibre is `0`, so the function is `∅` and
//! there is nothing to discharge — the rule is unconditional. For `succ` the
//! fibre is `1`, so the function is the one-point graph `{⟨•,n⟩}`
//! ([`crate::point_fun`]), which needs `n ∈ N` and nothing else.
//!
//! Neither hypothesis is an artefact: they are precisely Lean's
//! `zero : N` and `succ : N → N`.

use kernel::{Env, Formula, Term, Thm};
use crate::bound::Bound;
use crate::wrec::{hyp_congr, hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{
    a1i, and_intro, and_left, and_right, exists_elim_imp, hyp_mp, hyp_or_elim, inst_all, syl,
};

/// `⊢ A ∈ U(A) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(A))` — the antecedent every
/// unconditional W-type rule carries, at `c := A`.
///
/// The second conjunct is the **case analysis** the whole file exists for: an
/// `a ∈ 1 + 1` is `inl x` or `inr y` with `x, y ∈ 1`, hence `inl •` or `inr •`
/// by [`crate::sums::Sums::unit_eta`], and the two fibre equations then say
/// `app(B,a)` is `0` or `1`, both of which are in `U(A)`.
#[allow(clippy::too_many_arguments)]
pub(super) fn typing_at(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    empty_u: &Thm,
    tags: &Term,
    fam: &Term,
    fibre_zero: &Thm,
    fibre_succ: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let (zero_s, one, point) = (s.zero(), s.unit(), s.point());
    let u = bnd.universe_of(tags.clone());

    let mem_lu = crate::universe::mem_least_universe(env, bnd.lu, &bnd.lu_ax)?;
    let a_in_u = inst_all(&mem_lu, std::slice::from_ref(tags))?;

    // `0 ∈ U(A)` and `1 ∈ U(A)`. The second is pairing at `a = b = ∅`: the term
    // `{∅,∅}` **is** the term `1`, so nothing has to be rewritten.
    let zero_in_u = inst_all(empty_u, std::slice::from_ref(tags))?;
    let one_in_u = Thm::mp(
        &inst_all(&bnd.least_pairing, &[tags.clone(), zero_s.clone(), zero_s.clone()])?,
        &and_intro(&zero_in_u, &zero_in_u),
    )?;
    debug_assert_eq!(
        *one_in_u.concl(),
        Formula::mem(one.clone(), u.clone()),
        "wnat: {{∅,∅}} is not the term 1"
    );

    // `app(B, inl •) ∈ U(A)` and `app(B, inr •) ∈ U(A)`, by rewriting backwards
    // along the two computation rules.
    let carry_back = |env: &mut Env, eq: &Thm, val_in_u: &Thm| -> Option<Thm> {
        let (lhs, rhs) = eq.concl().as_eq()?;
        let hole = env.fresh_var();
        let carry =
            Thm::eq_leibniz(rhs, lhs, hole, Formula::mem(Term::var(hole), u.clone()));
        Thm::mp(&Thm::mp(&carry, &crate::eq_symm(env, eq)?)?, val_in_u)
    };
    let at_left = carry_back(env, fibre_zero, &zero_in_u)?;
    let at_right = carry_back(env, fibre_succ, &one_in_u)?;

    // ── the case analysis ───────────────────────────────────────────────────
    let av = env.fresh_var();
    let ta = Term::var(av);
    let h = Formula::mem(ta.clone(), tags.clone());
    let goal = Formula::mem(wt.fibre(fam.clone(), ta.clone()), u.clone());

    let branch = |env: &mut Env, left: bool, at_pt: &Thm| -> Option<Thm> {
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let inj = |t: Term| if left { s.inl(t) } else { s.inr(t) };
        let k = Formula::and(
            Formula::mem(tx.clone(), one.clone()),
            Formula::eq(ta.clone(), inj(tx.clone())),
        );
        let (k_mem, k_eq) = (
            and_left(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(ta.clone(), inj(tx.clone())),
            ),
            and_right(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(ta.clone(), inj(tx.clone())),
            ),
        );
        // `K → x = •`, hence `K → inj(x) = inj(•)`, hence `K → a = inj(•)`.
        let k_x = syl(&k_mem, &inst_all(&s.unit_eta, std::slice::from_ref(&tx))?)?;
        let k_inj = hyp_congr(env, &k_x, inj)?;
        let k_a = hyp_eq_trans(env, &k_eq, &k_inj)?;
        let k_back = hyp_eq_symm(env, &k_a)?;
        // `inj(•) = a → (app(B, inj(•)) ∈ U → app(B,a) ∈ U)`.
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            inj(point.clone()),
            ta.clone(),
            hole,
            Formula::mem(wt.fibre(fam.clone(), Term::var(hole)), u.clone()),
        );
        let k_goal = hyp_mp(&syl(&k_back, &leib)?, &a1i(at_pt, k.clone()))?;
        exists_elim_imp(xv, &Thm::gen(xv, &k_goal), &goal)
    };

    let cases = inst_all(&s.sum_cases, &[one.clone(), one.clone(), ta.clone()])?;
    let left = a1i(&branch(env, true, &at_left)?, h.clone());
    let right = a1i(&branch(env, false, &at_right)?, h.clone());
    let fibres = Thm::gen(av, &hyp_or_elim(&cases, &left, &right)?);
    debug_assert_eq!(
        *fibres.concl(),
        crate::bound::fibres_in(env, s, tags, fam, &u),
        "wnat: the family condition is not the one the W-type rules state"
    );
    Some(and_intro(&a_in_u, &fibres))
}
