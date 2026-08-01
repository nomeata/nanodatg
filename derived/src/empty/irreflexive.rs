//! No set is a member of itself.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀x. ¬(x ∈ x)    [no_self_mem]
//! ```
//!
//! Regularity at the singleton `{x}`: its only member is `x`, so `x` is the
//! `∈`-minimal one, and `x ∈ x` would put `x` in `x ∩ {x}`. `mem_sing` must be
//! `⊢ ∀a ∀z. (z ∈ {a} ↔ z = a)` for the pairing symbol `up` handed in; that is
//! checked rather than assumed. Callers need none of the derivation below.
//!
//! Independent of everything else in [`crate::empty`] — it needs no universe and
//! no empty set — and it is what [`crate::recursion::succ_inj`] closes its last
//! case with.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{
    a1i, and_left, and_right, eq_symm_imp, exists_elim, exists_intro, exists_intro_imp, hyp_and,
    hyp_mp, iff_mp, iff_mpr, inst_all, singleton, syl, uncurry,
};

/// `⊢ ∀x. ¬(x ∈ x)` — no set is a member of itself.
///
/// Regularity at the singleton `{x}`: its only member is `x`, so `x` is the
/// `∈`-minimal one, and `x ∈ x` would put `x` in `x ∩ {x}`.
pub fn no_self_mem(env: &mut Env, up: FnSym, mem_sing: &Thm) -> Option<Thm> {
    let reg = Thm::ax_regularity(env);

    let x = env.fresh_var();
    let tx = Term::var(x);
    let sx = singleton(up, tx.clone());

    // Regularity at `{x}`, with the two bound variables rebuilt as our own —
    // alpha-equivalent formulas are syntactically equal, so this is the very
    // formula the kernel produced.
    let (y, z) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(y), Term::var(z));
    let inst = inst_all(&reg, std::slice::from_ref(&sx))?;
    let y_in_sx = Formula::mem(ty.clone(), sx.clone());
    let clash = Formula::exists(
        z,
        Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz.clone(), sx.clone())),
    );
    let body = Formula::and(y_in_sx.clone(), Formula::not(clash.clone()));
    debug_assert_eq!(
        *inst.concl(),
        Formula::imp(Formula::exists(y, Formula::mem(ty.clone(), sx.clone())), Formula::exists(y, body.clone())),
        "Regularity did not instantiate to the expected shape"
    );

    // `⊢ x ∈ {x}`, so `{x}` is non-empty and Regularity applies.
    let ms_x = inst_all(mem_sing, &[tx.clone(), tx.clone()])?;
    let x_in_sx = Thm::mp(&iff_mpr(&ms_x)?, &Thm::eq_refl(tx.clone()))?;
    let nonempty = exists_intro(y, Formula::mem(ty.clone(), sx.clone()), tx.clone(), &x_in_sx)?;
    let ex_min = Thm::mp(&inst, &nonempty)?;

    // Under `W := body(y) ∧ x ∈ x`, derive `⊥`.
    let xx = Formula::mem(tx.clone(), tx.clone());
    let w = Formula::and(body.clone(), xx.clone());
    let w_body = and_left(body.clone(), xx.clone());
    let w_y_in_sx = syl(&w_body, &and_left(y_in_sx.clone(), Formula::not(clash.clone())))?;
    let w_y_eq_x = syl(&w_y_in_sx, &iff_mp(&inst_all(mem_sing, &[tx.clone(), ty.clone()])?)?)?;
    let w_x_eq_y = syl(&w_y_eq_x, &eq_symm_imp(env, ty.clone(), tx.clone()))?;
    let w_xx = and_right(body.clone(), xx.clone());

    // Leibniz carries `x ∈ x` along `x = y` to `x ∈ y`.
    let v = env.fresh_var();
    let leib = Thm::eq_leibniz(tx.clone(), ty.clone(), v, Formula::mem(tx.clone(), Term::var(v)));
    let w_x_in_y = hyp_mp(&hyp_mp(&a1i(&leib, w.clone()), &w_x_eq_y)?, &w_xx)?;
    let w_x_in_sx = a1i(&x_in_sx, w.clone());
    let w_pair = hyp_and(&w_x_in_y, &w_x_in_sx)?;
    let clash_body =
        Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz.clone(), sx.clone()));
    let w_clash = syl(&w_pair, &exists_intro_imp(z, clash_body, tx.clone())?)?;
    let w_not_clash = syl(&w_body, &and_right(y_in_sx, Formula::not(clash)))?;
    let w_false = hyp_mp(&w_not_clash, &w_clash)?;

    let not_xx = Formula::not(xx);
    let body_to_goal = uncurry(&w_false)?;
    debug_assert_eq!(*body_to_goal.concl(), Formula::imp(body, not_xx.clone()));

    let out = exists_elim(y, &ex_min, &Thm::gen(y, &body_to_goal), &not_xx)?;
    debug_assert_eq!(*out.concl(), not_xx);
    Some(Thm::gen(x, &out))
}
