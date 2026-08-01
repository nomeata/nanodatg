//! A composite over an empty domain is empty.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀g ∀f. comp(g,f,∅) = ∅                                [comp_empty_domain]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # Why this is what stops the recursion being circular
//!
//! At the instance [`crate::wrec_unit`] works at, the fibre is
//! `B(c) = app(∅,c) = ∅` ([`crate::wtype::app_of_empty`]), and the recursion
//! equation's right-hand side is `app(e, ⟨c,⟨∅, comp(wrec,∅,∅)⟩⟩)`. This lemma
//! collapses that composite to `∅` **whatever it composes** — in particular
//! without knowing anything about `wrec` — so the value
//! `V = app(e, ⟨c,⟨∅,∅⟩⟩)` is a *closed term*, not a fixed-point equation.
//!
//! That is what makes ι fire here without totality.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::Apply;
use crate::wrec::comp_of;
use crate::{and_intro, and_left, ex_falso, exists_elim_imp, gen_all, iff_mp, inst_all, syl};

/// `⊢ ∀g ∀f. comp(g,f,∅) = ∅` — **the composite over an empty domain is empty,
/// whatever it composes**.
///
/// This is what makes the unit instance non-circular: `comp(g,∅,B(c))` does not
/// mention `g` at all once `B(c)` is `∅`, so the value the recursion equation
/// demands at `⟨c,∅⟩` is a closed term rather than something defined in terms
/// of the graph being built.
///
/// One Extensionality over [`crate::wrec::compose`]'s membership condition:
/// the existential `∃b. (b ∈ ∅ ∧ …)` is refuted by `∅`'s emptiness one witness
/// at a time, and `∅`'s own membership condition refutes the converse.
pub fn comp_empty_domain(env: &mut Env, ap: &Apply, comp: FnSym, comp_ax: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (gv, fv, pv, bv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tf, tp, tb) = (Term::var(gv), Term::var(fv), Term::var(pv), Term::var(bv));
    let e_t = Term::apply(ap.empty, vec![]);
    let c_t = comp_of(comp, tg.clone(), tf.clone(), e_t.clone());

    let value = ap.apply(tg.clone(), ap.apply(tf.clone(), tb.clone()));
    let mem_b = Formula::mem(tb.clone(), e_t.clone());
    let eq_p = Formula::eq(tp.clone(), ap.sets.pair(tb.clone(), value));
    let body = Formula::and(mem_b.clone(), eq_p.clone());
    let ex = Formula::exists(bv, body.clone());

    let at = inst_all(comp_ax, &[tg.clone(), tf.clone(), e_t.clone(), tp.clone()])?;
    if *at.concl() != Formula::iff(Formula::mem(tp.clone(), c_t.clone()), ex.clone()) {
        return None
    }

    // No witness: `b ∈ ∅` is refutable, so the existential is.
    let no_b = syl(&and_left(mem_b, eq_p), &inst_all(&ap.empty_ax, std::slice::from_ref(&tb))?)?;
    let no_ex = exists_elim_imp(bv, &Thm::gen(bv, &no_b), &Formula::false_())?;

    let fwd = syl(
        &iff_mp(&at)?,
        &syl(&no_ex, &ex_falso(Formula::mem(tp.clone(), e_t.clone())))?,
    )?;
    let bwd = syl(
        &inst_all(&ap.empty_ax, std::slice::from_ref(&tp))?,
        &ex_falso(Formula::mem(tp.clone(), c_t.clone())),
    )?;

    let all = Thm::gen(pv, &and_intro(&fwd, &bwd));
    let out = Thm::mp(&inst_all(&ext, &[c_t.clone(), e_t.clone()])?, &all)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::eq(c_t, e_t),
        "comp_empty_domain: unexpected shape"
    );
    Some(gen_all(&[gv, fv], &out))
}
