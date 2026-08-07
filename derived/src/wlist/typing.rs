//! The two constructors' typing rules.
//!
//! # Interface
//!
//! Private to [`crate::wlist`]; surfaced as [`crate::wlist::WList`]'s `nil_mem`
//! and `cons_mem` fields:
//!
//! ```text
//! ⊢ nil ∈ lt(α)
//! ⊢ ∀h ∀t. ((h ∈ α ∧ t ∈ lt(α)) → cons(h,t) ∈ lt(α))
//! ```
//!
//! # Where the hypotheses come from, and which are real
//!
//! Both are [`crate::wtype::sup_mem`] at the corresponding tag, with the fibre
//! function supplied. For `nil` the fibre is `0`, so the function is `∅` and
//! there is nothing to discharge — the rule is unconditional. For `cons` the
//! fibre is `1`, so the function is the one-point graph `{⟨•,t⟩}`, which needs
//! `t ∈ lt(α)`; and the tag is `inr h`, which needs `h ∈ α` because the index
//! set is `1 + α` and membership in the right summand is a statement about `h`.
//!
//! Neither hypothesis is an artefact: they are precisely Lean's
//! `nil : List α` and `cons : α → List α → List α`.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::bound::Bound;
use crate::wrec::{hyp_eq_symm, hyp_eq_trans};
use crate::wtype::Wtype;
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm, exists_elim_imp, hyp_mp, hyp_or_elim, inst_all,
    syl,
};


/// `⊢ A ∈ U(A) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(A))` at `A := 1 + α` — the antecedent
/// every unconditional W-type rule carries, with **`α` free and no hypothesis**.
///
/// The case analysis is [`crate::wnat`]'s with one branch generalised: an
/// `a ∈ 1 + α` is `inl x` with `x ∈ 1`, hence `inl •` by
/// [`crate::sums::Sums::unit_eta`], or `inr y` with `y ∈ α` — and *that* `y` is
/// exactly what [`WList::fibre_cons`] wants, so the right branch discharges its
/// own hypothesis. Nothing asks what `α` is.
#[allow(clippy::too_many_arguments)]
pub(super) fn typing_at(
    env: &mut Env,
    wt: &Wtype,
    bnd: &Bound,
    empty_u: &Thm,
    tags: &Term,
    fam: &Term,
    fibre_nil: &Thm,
    fibre_cons: &Thm,
    av: FreeVar,
) -> Option<Thm> {
    let s = &wt.sums;
    let (zero_s, one, point) = (s.zero(), s.unit(), s.point());
    let u = bnd.universe_of(tags.clone());
    let ta = Term::var(av);

    let mem_lu = crate::universe::mem_least_universe(env, bnd.lu, &bnd.lu_ax).ok()?;
    let a_in_u = inst_all(&mem_lu, std::slice::from_ref(tags))?;
    let zero_in_u = inst_all(empty_u, std::slice::from_ref(tags))?;
    let one_in_u = Thm::mp(
        &inst_all(&bnd.least_pairing, &[tags.clone(), zero_s.clone(), zero_s.clone()])?,
        &and_intro(&zero_in_u, &zero_in_u),
    )?;
    debug_assert_eq!(
        *one_in_u.concl(),
        Formula::mem(one.clone(), u.clone()),
        "wlist: {{∅,∅}} is not the term 1"
    );

    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let h = Formula::mem(tc.clone(), tags.clone());
    let goal = Formula::mem(wt.fibre(fam.clone(), tc.clone()), u.clone());

    // ── the left branch: `x ∈ 1`, so `a = inl •`, and the fibre is `0` ──────
    let left = {
        let xv = env.fresh_var();
        let tx = Term::var(xv);
        let k = Formula::and(
            Formula::mem(tx.clone(), one.clone()),
            Formula::eq(tc.clone(), s.inl(tx.clone())),
        );
        let (k_mem, k_eq) = (
            and_left(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(tc.clone(), s.inl(tx.clone())),
            ),
            and_right(
                Formula::mem(tx.clone(), one.clone()),
                Formula::eq(tc.clone(), s.inl(tx.clone())),
            ),
        );
        // `⊢ app(fam, inl •) ∈ U`, from `0 ∈ U` backwards along the fibre equation.
        let hole = env.fresh_var();
        let carry = Thm::eq_leibniz(
            zero_s.clone(),
            wt.fibre(fam.clone(), s.inl(point.clone())),
            hole,
            Formula::mem(Term::var(hole), u.clone()),
        );
        let at_pt = Thm::mp(&Thm::mp(&carry, &eq_symm(env, fibre_nil)?)?, &zero_in_u)?;

        let k_x = syl(&k_mem, &inst_all(&s.unit_eta, std::slice::from_ref(&tx))?)?;
        let k_inj = crate::wrec::hyp_congr(env, &k_x, |t| s.inl(t))?;
        let k_a = hyp_eq_trans(env, &k_eq, &k_inj)?;
        let k_back = hyp_eq_symm(env, &k_a)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            s.inl(point.clone()),
            tc.clone(),
            hole,
            Formula::mem(wt.fibre(fam.clone(), Term::var(hole)), u.clone()),
        );
        let k_goal = hyp_mp(&syl(&k_back, &leib)?, &a1i(&at_pt, k.clone()))?;
        exists_elim_imp(xv, &Thm::gen(xv, &k_goal), &goal)?
    };

    // ── the right branch: `y ∈ α`, so the fibre is `1` — at *that* `y` ──────
    let right = {
        let yv = env.fresh_var();
        let ty = Term::var(yv);
        let k = Formula::and(
            Formula::mem(ty.clone(), ta.clone()),
            Formula::eq(tc.clone(), s.inr(ty.clone())),
        );
        let (k_mem, k_eq) = (
            and_left(
                Formula::mem(ty.clone(), ta.clone()),
                Formula::eq(tc.clone(), s.inr(ty.clone())),
            ),
            and_right(
                Formula::mem(ty.clone(), ta.clone()),
                Formula::eq(tc.clone(), s.inr(ty.clone())),
            ),
        );
        // `⊢ K → app(fam, inr y) = 1`, hence `⊢ K → app(fam, inr y) ∈ U`.
        let fib_y = syl(&k_mem, &inst_all(fibre_cons, std::slice::from_ref(&ty))?)?;
        let back = hyp_eq_symm(env, &fib_y)?;
        let hole = env.fresh_var();
        let leib2 = Thm::eq_leibniz(
            one.clone(),
            wt.fibre(fam.clone(), s.inr(ty.clone())),
            hole,
            Formula::mem(Term::var(hole), u.clone()),
        );
        let at_y = hyp_mp(&syl(&back, &leib2)?, &a1i(&one_in_u, k.clone()))?;

        let k_back = hyp_eq_symm(env, &k_eq)?;
        let hole = env.fresh_var();
        let leib = Thm::eq_leibniz(
            s.inr(ty.clone()),
            tc.clone(),
            hole,
            Formula::mem(wt.fibre(fam.clone(), Term::var(hole)), u.clone()),
        );
        let k_goal = hyp_mp(&syl(&k_back, &leib)?, &at_y)?;
        exists_elim_imp(yv, &Thm::gen(yv, &k_goal), &goal)?
    };

    let cases = inst_all(&s.sum_cases, &[one.clone(), ta.clone(), tc.clone()])?;
    let fibres = Thm::gen(
        cv,
        &hyp_or_elim(&cases, &a1i(&left, h.clone()), &a1i(&right, h.clone()))?,
    );
    debug_assert_eq!(
        *fibres.concl(),
        crate::bound::fibres_in(env, s, tags, fam, &u),
        "wlist: the family condition is not the one the W-type rules state"
    );
    Some(and_intro(&a_in_u, &fibres))
}
