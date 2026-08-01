//! Where the recursor's own values live.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
//!       ∀x. (indom(wrec(…), x) → app(wrec(…), x) ∈ T))     [wrec_value_typed]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) → ∀f ∀d.
//!       ((∀b. (b ∈ d → indom(wrec(…), app(f,b)))) →
//!            comp(wrec(…), f, d) ∈ fs(d,T)))            [wrec_composite_typed]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # What these are for
//!
//! They are the two lemmas the induction of step 4 needs before it can extend an
//! attempt by a point. An attempt is *by definition* a subset of `W × T`, so the
//! new value has to be shown to lie in `T` — and the step's typing hypothesis
//! `step_typed` only delivers that once its third premise,
//! `r ∈ fs(B(a), T)`, is discharged. That premise is exactly
//! [`wrec_composite_typed`]'s conclusion.
//!
//! [`wrec_value_typed`] is the ingredient: every value of the recursor is a
//! value of some attempt, and attempts land in `T` by definition, so
//! [`super::composite_typed`]'s pointwise hypothesis is met along any subterm
//! map whose values are in the recursor's domain.
//!
//! [`wrec_composite_typed`]'s antecedent is **literally** the induction
//! hypothesis of [`crate::wrec_extend`], so it drops in there with no
//! adaptation.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::wrec::{comp_of, hyp_eq_symm, hyp_exists_elim};
use crate::{a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, inst_all, syl, uncurry};


/// **The recursor's values lie in the target.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
///       ∀x. (indom(wrec(…), x) → app(wrec(…), x) ∈ T))
/// ```
///
/// A point of the domain gives a pair `⟨x,y⟩ ∈ wrec`;
/// [`crate::wrec::wrec_subset_prod`] puts that pair in `prod(W,T)`, so
/// [`crate::sums::pair_in_product`] puts `y` in `T`; and
/// [`crate::wrec::wrec_single_valued`] — hence the bound hypothesis — makes `y`
/// the value.
///
/// `subset_prod` is [`crate::wrec::wrec_subset_prod`] and `sv` is
/// [`crate::wrec::wrec_single_valued`].
pub fn wrec_value_typed(
    env: &mut Env,
    wt: &crate::wtype::Wtype,
    rec: FnSym,
    subset_prod: &Thm,
    sv: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu, tt) = (
        args[0].clone(),
        args[1].clone(),
        args[2].clone(),
        args[3].clone(),
    );
    let w_t = wt.of(ta.clone(), tb.clone(), tu.clone());
    let f_t = Term::apply(rec, args.clone());
    let cl = crate::wtype::closed(env, s, &ta, &tb, &tu);

    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let pxy = ap.sets.pair(tx.clone(), ty.clone());
    let mem_xy = Formula::mem(pxy.clone(), f_t.clone());
    let ind = Formula::exists(yv, mem_xy.clone());
    debug_assert_eq!(
        ind,
        crate::wrec::indom(env, ap, &f_t, &tx),
        "wrec_value_typed: indom drifted"
    );
    let val = ap.apply(f_t.clone(), tx.clone());

    let h = Formula::and(cl.clone(), ind.clone());
    let k = Formula::and(h.clone(), mem_xy.clone());
    let k_h = and_left(h.clone(), mem_xy.clone());
    let k_mem = and_right(h.clone(), mem_xy.clone());
    let k_cl = syl(&k_h, &and_left(cl.clone(), ind.clone()))?;

    // `⟨x,y⟩ ∈ prod(W,T)`, hence `y ∈ T`.
    let sp = inst_all(subset_prod, &args)?;
    let k_prod = syl(&k_mem, &inst_all(&sp, std::slice::from_ref(&pxy))?)?;
    let pip = inst_all(
        &s.pair_in_prod,
        &[w_t.clone(), tt.clone(), tx.clone(), ty.clone()],
    )?;
    let k_yt = syl(
        &syl(&k_prod, &iff_mp(&pip)?)?,
        &and_right(
            Formula::mem(tx.clone(), w_t),
            Formula::mem(ty.clone(), tt.clone()),
        ),
    )?;

    // `app(wrec,x) = y`, from single-valuedness.
    let k_sv = syl(&k_cl, &inst_all(sv, &args)?)?;
    let k_eq = hyp_mp(
        &a1i(
            &inst_all(&wt.app_pair, &[f_t.clone(), tx.clone(), ty.clone()])?,
            k.clone(),
        ),
        &hyp_and(&k_sv, &k_mem)?,
    )?;

    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        ty,
        val.clone(),
        hole,
        Formula::mem(Term::var(hole), tt.clone()),
    );
    let k_symm = hyp_eq_symm(env, &k_eq)?;
    let k_out = hyp_mp(&hyp_mp(&a1i(&leib, k), &k_symm)?, &k_yt)?;

    let h_out = hyp_exists_elim(yv, &k_out, &and_right(cl.clone(), ind.clone()))?;
    let body = uncurry(&h_out)?;
    let out = Thm::mp(
        &Thm::ax_dist(
            xv,
            cl.clone(),
            Formula::imp(ind, Formula::mem(val, tt)),
        )?,
        &Thm::gen(xv, &body),
    )?;
    Some(gen_all(&vars, &out))
}

/// **The composite the recursion equation forms is a function into `T`.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. (closed(A,B,u) →
///       ∀a ∀f. ((∀b. (b ∈ B(a) → indom(wrec(…), app(f,b))))
///                  → comp(wrec(…), f, B(a)) ∈ fs(B(a), T)))
/// ```
///
/// [`super::composite_typed`] with its hypothesis discharged by
/// [`wrec_value_typed`]. The antecedent is exactly the subterm clause of
/// [`crate::wrec::rec_cond`], and also exactly the induction hypothesis of
/// step 4 — which is what makes this the bridge between the two: it is what
/// turns "every subterm is in the domain" into "the third argument of the step
/// is a legal one", so that `step_typed` can be applied at all.
pub fn wrec_composite_typed(
    env: &mut Env,
    wt: &crate::wtype::Wtype,
    comp: FnSym,
    rec: FnSym,
    value_typed: &Thm,
    comp_typed: &Thm,
) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tb, tu, tt) = (
        args[0].clone(),
        args[1].clone(),
        args[2].clone(),
        args[3].clone(),
    );
    let f_t = Term::apply(rec, args.clone());
    let cl = crate::wtype::closed(env, s, &ta, &tb, &tu);

    let (pa, pf, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, tbv) = (Term::var(pa), Term::var(pf), Term::var(bv));
    let fibre = wt.fibre(tb.clone(), tpa.clone());
    let fb = ap.apply(tpf.clone(), tbv.clone());

    let ih = Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tbv.clone(), fibre.clone()),
            crate::wrec::indom(env, ap, &f_t, &fb),
        ),
    );
    let k = Formula::and(cl.clone(), ih.clone());
    let k_cl = and_left(cl.clone(), ih.clone());
    let k_ih = and_right(cl.clone(), ih.clone());

    // `K → (b ∈ B(a) → app(wrec, app(f,b)) ∈ T)`, pointwise.
    let vt = syl(&k_cl, &inst_all(value_typed, &args)?)?;
    let at_fb = crate::funcs::hyp_syl(
        &syl(&k_ih, &Thm::ax_inst(ih.clone(), tbv.clone())?)?,
        &hyp_inst(&vt, std::slice::from_ref(&fb))?,
    )?;
    let inner = Formula::imp(
        Formula::mem(tbv.clone(), fibre.clone()),
        Formula::mem(ap.apply(f_t.clone(), fb), tt.clone()),
    );
    let k_all = Thm::mp(&Thm::ax_dist(bv, k.clone(), inner)?, &Thm::gen(bv, &at_fb))?;

    // …which is exactly [`super::composite_typed`]'s hypothesis at `g := wrec`.
    let ct = inst_all(
        comp_typed,
        &[f_t.clone(), tpf.clone(), fibre.clone(), tt.clone()],
    )?;
    let k_out = hyp_mp(&a1i(&ct, k.clone()), &k_all)?;
    debug_assert_eq!(
        *k_out.concl(),
        Formula::imp(
            k,
            Formula::mem(
                comp_of(comp, f_t, tpf.clone(), fibre),
                s.fs.of(wt.fibre(tb, tpa.clone()), tt)
            )
        ),
        "wrec_composite_typed: unexpected shape"
    );

    let body = uncurry(&k_out)?;
    let (_, bf) = body.concl().as_imp()?;
    let all_f = Thm::mp(&Thm::ax_dist(pf, cl.clone(), bf)?, &Thm::gen(pf, &body))?;
    let (_, ba) = all_f.concl().as_imp()?;
    let out = Thm::mp(&Thm::ax_dist(pa, cl, ba)?, &Thm::gen(pa, &all_f))?;
    Some(gen_all(&vars, &out))
}

/// From `⊢ H → ∀v₁…∀vₙ. φ` infer `⊢ H → φ[t₁…tₙ]`.
fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}
