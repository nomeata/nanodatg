//! **The thesis's `rec_acc(A,R,e)`** — the recursor packaged as a function on
//! `A` taking the accessibility proof.
//!
//! # Interface
//!
//! ```text
//! accprop(A,R) := prod(acc(A,R), {•})
//! pack(A,R,T,e) := ih(accrec(A,R,T,e), A, accprop(A,R), •)
//!                = { ⟨x, (h ∈ [x ∈ acc(A,R)] ↦ app(accrec,x))⟩ : x ∈ A }
//!
//! ⊢ ∀A ∀R ∀T ∀e ∀x. (x ∈ acc(A,R) →
//!       app(app(pack(A,R,T,e), x), •) = app(accrec(A,R,T,e), x))     [pack_app]
//! ⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) →
//!       app(app(pack(A,R,T,e), x), •)
//!         = app(app(app(e,x),•), ih(accrec,A,R,x))))                [pack_iota]
//! ```
//!
//! # What this is, and why it needs no new symbol
//!
//! Carneiro's *The Type Theory of Lean* §6.2.2 defines
//!
//! ```text
//! rec_acc(A,R,e) = (x ∈ A ↦ (h ∈ [x ∈ acc(A,R)] ↦ F(x)))
//! ```
//!
//! and `⟦rec_acc e⟧ = rec_acc(⟦α⟧,⟦r⟧,⟦e⟧)` (thesis.txt:2129). `F` is
//! [`super::union`]'s `accrec`; what remains is the *outer* abstraction, and it
//! has exactly the shape of the inner one that [`super::ih`] already builds — a
//! Replacement over `A` whose rows are conditional values. So it is not built
//! again: `pack` is [`super::ih::ih_of`] instantiated at the relation
//!
//! ```text
//! accprop(A,R) := acc(A,R) × {•}
//! ```
//!
//! under which "`x` is a predecessor of `•`" says precisely "`x ∈ acc(A,R)`".
//! One term, no Replacement, no Separation, and every lemma about `ih` applies
//! verbatim.
//!
//! **The one deviation, stated plainly.** The thesis writes the inner domain as
//! the conditional singleton `[x ∈ acc(A,R)]`; what `pack` actually carries is
//! `ep(accprop(A,R), x, •) = [⟨x,•⟩ ∈ acc(A,R) × {•}]`. The two conditions are
//! equivalent — [`pack_app`] is derived by showing exactly that — so the two
//! sets are equal by Extensionality, but they are not the same *term*. Nothing
//! downstream should compare them syntactically; what a consumer needs is the
//! beta rule [`pack_app`], and that is stated at the thesis's spelling of the
//! *proof*, namely `•`.
//!
//! # Why the outer packaging matters at all
//!
//! Lean's `Acc.rec` is applied to a point and to a proof of `Acc r a`. Under the
//! interpretation the proof is `•` (thesis.txt:2127), so the interpreted
//! recursor must be a function of *two* arguments, the second of which is
//! ignored. [`super::union`]'s `accrec` is the one-argument `F`; `pack` is what
//! `⟦rec_acc e⟧` denotes, and [`pack_iota`] is the ι rule at that spelling.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, gen_all, hyp_and, hyp_mp, iff_mpr, imp_refl, inst_all, singleton, syl,
};

use super::base::Base;
use super::extend::step_typed;
use super::ih::ih_of;
use super::shared::{gen_under, hyp_inst};

/// The term `accprop(A,R) := acc(A,R) × {•}` — the relation under which every
/// accessible point is a predecessor of `•`.
pub fn accprop_of(b: &Base, a: &Term, r: &Term) -> Term {
    b.s.prod.of(b.acc_of(a, r), singleton(b.s.ap.sets.up, b.s.point()))
}

/// The term `pack(A,R,T,e)` — the thesis's `rec_acc(A,R,e)`, at the target `T`.
pub fn pack_of(b: &Base, rec: FnSym, a: &Term, r: &Term, t: &Term, e: &Term) -> Term {
    let rec_t = Term::apply(rec, vec![a.clone(), r.clone(), t.clone(), e.clone()]);
    ih_of(b.ih, rec_t, a.clone(), accprop_of(b, a, r), b.s.point())
}

/// `⊢ ∀A ∀R ∀T ∀e ∀x. (x ∈ acc(A,R) →
///       app(app(pack(A,R,T,e), x), •) = app(accrec(A,R,T,e), x))`
/// — **the packaged recursor, applied to a point and to the accessibility
/// proof, is the recursive value**.
///
/// [`super::ih::ih_app`] at the relation `accprop(A,R)` and the point `•`, with
/// its two premises supplied by [`crate::acc::acc_subset`] and by the product's
/// membership condition. Unconditional — which is a claim about the sequent, so
/// the `Base` it reads `ih_app`, `acc_subset`, `mem_sing` and `pair_in_prod` off
/// must carry no hypothetical theorem. The equation is pinned in release,
/// against a rebuilt `app(app(pack,x),•) = app(accrec,x)`.
pub fn pack_app(env: &mut Env, b: &Base, rec: FnSym) -> Option<Thm> {
    if !b.all_unconditional() {
        return None
    }
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt, te) = (ps[0].clone(), ps[1].clone(), ps[2].clone(), ps[3].clone());
    let rec_t = Term::apply(rec, ps.clone());
    let acc_t = b.acc_of(&ta, &tr);
    let pt = b.s.point();
    let rel = accprop_of(b, &ta, &tr);

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let h = Formula::mem(tx.clone(), acc_t.clone());

    // `x ∈ A`, from `acc(A,R) ⊆ A`.
    let sub = inst_all(&b.ac.acc_subset, &[ta.clone(), tr.clone(), tx.clone()])?;
    let h_xa = syl(&imp_refl(h.clone()), &sub)?;

    // `⟨x,•⟩ ∈ acc(A,R) × {•}`, which is what `ep(accprop(A,R),x,•)` decides.
    let sing = singleton(b.s.ap.sets.up, pt.clone());
    let ms = inst_all(&b.s.ap.mem_sing, &[pt.clone(), pt.clone()])?;
    let pt_in_sing = Thm::mp(&iff_mpr(&ms)?, &Thm::eq_refl(pt.clone()))?;
    let pip = inst_all(
        &b.s.pair_in_prod,
        &[acc_t.clone(), sing, tx.clone(), pt.clone()],
    )?;
    let h_edge = syl(
        &hyp_and(&imp_refl(h.clone()), &a1i(&pt_in_sing, h.clone()))?,
        &iff_mpr(&pip)?,
    )?;

    // `ih_app` at `g := accrec`, `R := accprop(A,R)`, `x := •`, `y := x`.
    let ia = inst_all(
        &b.ih_app,
        &[rec_t.clone(), ta.clone(), rel, pt.clone(), tx.clone()],
    )?;
    let out = hyp_mp(&a1i(&ia, h.clone()), &hyp_and(&h_xa, &h_edge)?)?;
    let want = Formula::imp(
        h,
        Formula::eq(
            b.app(&b.app(&pack_of(b, rec, &ta, &tr, &tt, &te), &tx), &pt),
            b.app(&rec_t, &tx),
        ),
    );
    if *out.concl() != want {
        return None
    }
    Some(gen_all(&vars, &Thm::gen(xv, &out)))
}

/// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) →
///       app(app(pack(A,R,T,e), x), •) = app(app(app(e,x),•), ih(accrec,A,R,x))))`
/// — **the ι rule at the thesis's spelling**.
///
/// [`pack_app`] chained with [`super::total::iota`]. The only hypothesis is
/// `step_typed`, exactly as there — so both premises must be **unconditional**,
/// or there would be a second one that the header denies and the formula does
/// not show. The equation is pinned in release, against a rebuilt one.
pub fn pack_iota(env: &mut Env, b: &Base, rec: FnSym, app: &Thm, iota: &Thm) -> Option<Thm> {
    if !b.all_unconditional() || !crate::all_unconditional(&[app, iota]) {
        return None
    }
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt, te) = (ps[0].clone(), ps[1].clone(), ps[2].clone(), ps[3].clone());
    let rec_t = Term::apply(rec, ps.clone());
    let acc_t = b.acc_of(&ta, &tr);
    let st = step_typed(env, b, &ta, &tr, &tt, &te);
    let pt = b.s.point();

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let mem = Formula::mem(tx.clone(), acc_t.clone());

    let app_at = inst_all(app, &ps)?;
    let app_x = Thm::mp(&Thm::ax_inst(app_at.concl().clone(), tx.clone())?, &app_at)?;
    let iota_at = inst_all(iota, &ps)?;
    let iota_x = hyp_inst(&iota_at, std::slice::from_ref(&tx))?;

    // Under `K := ST ∧ x ∈ acc(A,R)`.
    let k = Formula::and(st.clone(), mem.clone());
    let k_st = crate::and_left(st.clone(), mem.clone());
    let k_mem = crate::and_right(st.clone(), mem.clone());
    let k_left = hyp_mp(&a1i(&app_x, k.clone()), &k_mem)?;
    let k_right = hyp_mp(&syl(&k_st, &iota_x)?, &k_mem)?;
    let k_goal = crate::wrec::hyp_eq_trans(env, &k_left, &k_right)?;
    if *k_goal.concl()
        != Formula::imp(
            k,
            Formula::eq(
                b.app(&b.app(&pack_of(b, rec, &ta, &tr, &tt, &te), &tx), &pt),
                b.step_at(&te, &tx, &b.ih_at(&rec_t, &ta, &tr, &tx)),
            ),
        )
    {
        return None
    }
    let out = gen_under(xv, &crate::uncurry(&k_goal)?)?;
    Some(gen_all(&vars, &out))
}
