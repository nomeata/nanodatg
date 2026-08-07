//! No two sets are members of each other.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀a ∀b. ¬(a ∈ b ∧ b ∈ a)    [no_two_cycle]
//! ```
//!
//! Regularity at the unordered pair `{a,b}` — the same argument as
//! [`super::no_self_mem`], one size up. `{a,b}` is non-empty, so it has an
//! `∈`-minimal member `y`, and `y` is `a` or `b`; either way the *other* one is
//! a member of `y` and a member of `{a,b}`, which is the clash `y`'s minimality
//! forbids. `up_ax` must be `⊢ ∀x ∀y ∀z. (z ∈ upair(x,y) ↔ (z = x ∨ z = y))`
//! for the symbol handed in; that is checked rather than assumed, in the sense
//! that a wrong theorem yields `None` rather than a conclusion.
//!
//! Independent of everything else in [`crate::empty`] — it needs no universe
//! and no empty set — and it is what
//! [`crate::universe::universe_union_closed`] closes its argument with:
//! `S ∈ u ⊆ ⋃S` produces a two-cycle, and this refutes it.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::err::DResult;
use crate::prim;
use crate::rules::{
    exists_elim, exists_intro, exists_intro_imp, hyp_and, hyp_mp, hyp_or_elim, iff_mp, inst_all,
    syl, uncurry, upair_members,
};
use crate::{a1i, and_left, and_right, decline, eq_symm_imp, gen_all};

/// `⊢ ∀a ∀b. ¬(a ∈ b ∧ b ∈ a)` — membership has no 2-cycles.
///
/// Regularity at `{a,b}`: its `∈`-minimal member is `a` or `b`, and in either
/// case the other one lies both in it and in `{a,b}`.
///
/// This is [`super::no_self_mem`] one size up, and the two are genuinely
/// different statements: `a ∈ a` is not an instance of `a ∈ b ∧ b ∈ a` unless
/// one already knows `a = b` is allowed, and conversely a 2-cycle is not a
/// self-membership. Both are needed.
pub fn no_two_cycle(env: &mut Env, up: FnSym, up_ax: &Thm) -> DResult<Thm> {
    if up.arity() != 2 {
        return Err(decline!("the unordered-pair symbol is not binary"))
    }
    let reg = Thm::ax_regularity(env);

    let (av, bv) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let p = Term::apply(up, vec![ta.clone(), tb.clone()]);

    // Regularity at `{a,b}`, with the two bound variables rebuilt as our own —
    // alpha-equivalent formulas are syntactically equal, so this is the very
    // formula the kernel produced.
    let (yv, zv) = (env.fresh_var(), env.fresh_var());
    let (ty, tz) = (Term::var(yv), Term::var(zv));
    let inst = inst_all(&reg, std::slice::from_ref(&p))?;
    let y_in_p = Formula::mem(ty.clone(), p.clone());
    let clash_body =
        Formula::and(Formula::mem(tz.clone(), ty.clone()), Formula::mem(tz.clone(), p.clone()));
    let clash = Formula::exists(zv, clash_body.clone());
    let body = Formula::and(y_in_p.clone(), Formula::not(clash.clone()));
    debug_assert_eq!(
        *inst.concl(),
        Formula::imp(
            Formula::exists(yv, y_in_p.clone()),
            Formula::exists(yv, body.clone())
        ),
        "Regularity did not instantiate to the expected shape"
    );

    // `⊢ a ∈ {a,b}` and `⊢ b ∈ {a,b}`; the first makes the pair non-empty.
    let (a_in_p, b_in_p) = upair_members(up_ax, &ta, &tb)?;
    let nonempty = exists_intro(yv, y_in_p.clone(), ta.clone(), &a_in_p)?;
    let ex_min = prim::mp(&inst, &nonempty)?;

    // ── Under `W := body(y) ∧ (a ∈ b ∧ b ∈ a)`, derive `⊥` ───────────────────
    let ab = Formula::mem(ta.clone(), tb.clone());
    let ba = Formula::mem(tb.clone(), ta.clone());
    let h = Formula::and(ab.clone(), ba.clone());
    let w = Formula::and(body.clone(), h.clone());

    let w_body = and_left(body.clone(), h.clone());
    let w_h = and_right(body.clone(), h.clone());
    let w_ab = syl(&w_h, &and_left(ab.clone(), ba.clone()))?;
    let w_ba = syl(&w_h, &and_right(ab.clone(), ba.clone()))?;
    let w_y_in_p = syl(&w_body, &and_left(y_in_p.clone(), Formula::not(clash.clone())))?;
    let w_not_clash = syl(&w_body, &and_right(y_in_p.clone(), Formula::not(clash.clone())))?;

    // `y ∈ {a,b}` is `y = a ∨ y = b` — the case split.
    let w_disj = syl(&w_y_in_p, &iff_mp(&inst_all(up_ax, &[ta.clone(), tb.clone(), ty.clone()])?)?)?;

    // Both branches are the same move with the roles of `a` and `b` swapped:
    // `y` is one of them, the *other* is a member of it by the hypothesis, and
    // the other is also a member of `{a,b}` — so `y` has a member in common
    // with `{a,b}`, which its minimality forbids.
    let branch = |env: &mut Env, side: &Term, other: &Term, w_mem: &Thm, other_in_p: &Thm| {
        // `w_mem : W → other ∈ side`, and `side` is what `y` is equal to.
        let eq = Formula::eq(ty.clone(), side.clone());
        let k = Formula::and(w.clone(), eq.clone());
        let k_w = and_left(w.clone(), eq.clone());
        let k_eq = and_right(w.clone(), eq.clone());

        // `y = side` gives `side = y`, which carries `other ∈ side` to
        // `other ∈ y`.
        let k_side_eq_y = syl(&k_eq, &eq_symm_imp(env, ty.clone(), side.clone()))?;
        let wv = env.fresh_var();
        let leib = Thm::eq_leibniz(
            side.clone(),
            ty.clone(),
            wv,
            Formula::mem(other.clone(), Term::var(wv)),
        );
        let k_other_in_y =
            hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), &k_side_eq_y)?, &syl(&k_w, w_mem)?)?;
        let k_pair = hyp_and(&k_other_in_y, &a1i(other_in_p, k.clone()))?;
        let k_clash = syl(&k_pair, &exists_intro_imp(zv, clash_body.clone(), other.clone())?)?;
        let k_false = hyp_mp(&syl(&k_w, &w_not_clash)?, &k_clash)?;
        uncurry(&k_false)
    };

    let case_a = branch(env, &ta, &tb, &w_ba, &b_in_p)?;
    let case_b = branch(env, &tb, &ta, &w_ab, &a_in_p)?;
    let w_false = hyp_or_elim(&w_disj, &case_a, &case_b)?;

    let not_h = Formula::not(h.clone());
    let body_to_goal = uncurry(&w_false)?;
    debug_assert_eq!(*body_to_goal.concl(), Formula::imp(body, not_h.clone()));

    let out = exists_elim(yv, &ex_min, &Thm::gen(yv, &body_to_goal), &not_h)?;
    debug_assert_eq!(*out.concl(), not_h, "no_two_cycle: wrong shape");
    Ok(gen_all(&[av, bv], &out))
}
