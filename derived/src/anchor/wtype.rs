//! `W(∅, B, u) = ∅` — a W-type over an empty tag set has no elements.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀B. closed(∅, B, ∅)                              [empty_closed]
//! ⊢ ∀B ∀u ∀x. ¬(x ∈ W(∅, B, u))                      [empty_wtype_uninhabited]
//! ⊢ ∀B ∀u. W(∅, B, u) = ∅                            [empty_wtype_eq]
//! ⊢ ∀x. ¬(x ∈ enum(0))                               [enum0_uninhabited]
//! ⊢ enum(0) = ∅                                      [enum0_eq]
//! ⊢ ∀T. ∅ ∈ fs(enum(0), T)                           [enum0_rec]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why it is short
//!
//! [`crate::wtype::w_induction`] — W2 — says `W(A,B,u)` is contained in **every**
//! closed subset of the bound:
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀C. ((C ⊆ u ∧ closed(A,B,C)) → ∀z. (z ∈ W(A,B,u) → z ∈ C))
//! ```
//!
//! Take `C := ∅`. Its two hypotheses are both vacuous:
//!
//! * `∅ ⊆ u` because nothing is a member of `∅`;
//! * `closed(A,B,∅)` is `∀a. (a ∈ A → …)`, and at `A := ∅` the antecedent `a ∈ ∅`
//!   is refutable, so the whole formula holds **for every `B` and every `S`** —
//!   in particular for `S := ∅`. That is the one observation the file rests on:
//!   the closure condition constrains a set only through the tags, so an empty
//!   tag set constrains nothing.
//!
//! So `W(∅,B,u) ⊆ ∅`, and Extensionality upgrades that to `W(∅,B,u) = ∅`.
//!
//! No `closed(∅,B,u)` is needed anywhere — W1 is never used — so the result
//! holds for a completely arbitrary bound `u`, including bounds that bound no
//! W-type at all.
//!
//! # The tie to `⟦Empty⟧`
//!
//! [`crate::enums::enum0`] builds `enum(0) := W(0, ∅, U(0))`, and
//! `checker/src/tg.rs` hands that very term back as the body of `⟦Empty⟧` for a
//! Lean inductive with zero constructors. [`enum0_uninhabited`] and
//! [`enum0_eq`] therefore *call* `enum0` for their subject term rather than
//! re-spelling it, and refuse to hand back a theorem about anything else, so the
//! statement cannot drift away from the term the backend uses.
//!
//! # `Empty.rec` is the empty function
//!
//! The thesis gives `⟦Γ ⊢ rec⊥⟧γ = ∅` alongside `⟦Γ ⊢ ⊥⟧γ = ∅`: eliminating from
//! an empty type needs no recursor machinery, because the empty function is
//! already a function out of the empty set into anything. [`enum0_rec`] is that,
//! carried across `enum(0) = ∅`.

use kernel::{Env, Formula, Term, Thm};

use crate::bound::Bound;
use crate::wtype::Wtype;
use crate::{and_intro, eq_symm, ex_falso, gen_all, inst_all, syl};

/// `⊢ ∀B. closed(∅, B, ∅)` — the empty set is closed under `sup` over an empty
/// tag set.
///
/// `closed(A,B,S)` is `∀a. (a ∈ A → ∀f. (f ∈ fs(B(a),S) → ⟨a,f⟩ ∈ S))`, so at
/// `A := ∅` every instance has a refutable antecedent. The `S := ∅` instance is
/// the one W2 wants; the derivation would go through for any `S` at all.
pub fn empty_closed(env: &mut Env, wt: &Wtype) -> Option<Thm> {
    let s = &wt.sums;
    let z = wt.empty();
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(fv));

    // The body of `closed` at the tag `a`, built exactly as
    // `crate::wtype::closed` builds it, so the two formulas are the same one.
    let inner = Formula::forall(
        fv,
        Formula::imp(
            Formula::mem(tf.clone(), s.fs.of(wt.fibre(tb.clone(), ta.clone()), z.clone())),
            Formula::mem(wt.sup(ta.clone(), tf), z.clone()),
        ),
    );
    let no_tag = inst_all(&s.ap.empty_ax, std::slice::from_ref(&ta))?;
    let out = Thm::gen(av, &syl(&no_tag, &ex_falso(inner))?);
    if *out.concl() != wt.closed_at(env, &z, &tb, &z) {
        return None
    }
    Some(Thm::gen(bv, &out))
}

/// **The anchor for `Empty`.** `⊢ ∀B ∀u ∀x. ¬(x ∈ W(∅, B, u))`
///
/// W2 at `C := ∅`, with both of its hypotheses discharged: `∅ ⊆ u` because `∅`
/// has no members, and `closed(∅,B,∅)` by [`empty_closed`]. What comes back is
/// `∀z. (z ∈ W(∅,B,u) → z ∈ ∅)`, and `∅` has no members, so nothing is in the
/// W-type either.
pub fn empty_wtype_uninhabited(env: &mut Env, wt: &Wtype, closed0: &Thm) -> Option<Thm> {
    let z = wt.empty();
    let empty_ax = wt.sums.ap.empty_ax.clone();
    let (bv, uv) = (env.fresh_var(), env.fresh_var());
    let (tb, tu) = (Term::var(bv), Term::var(uv));

    // `∅ ⊆ u`, in the exact shape `kernel::thm::subset` builds.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let sub = Thm::gen(
        zv,
        &syl(
            &inst_all(&empty_ax, std::slice::from_ref(&tz))?,
            &ex_falso(Formula::mem(tz.clone(), tu.clone())),
        )?,
    );
    if *sub.concl() != kernel::thm::subset(env, z.clone(), tu.clone()) {
        return None
    }

    let hyp = and_intro(&sub, &inst_all(closed0, std::slice::from_ref(&tb))?);
    let ind = inst_all(&wt.w_induction, &[z.clone(), tb.clone(), tu.clone(), z.clone()])?;
    let all_z = Thm::mp(&ind, &hyp)?;

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let at_x = inst_all(&all_z, std::slice::from_ref(&tx))?;
    let out = syl(&at_x, &inst_all(&empty_ax, std::slice::from_ref(&tx))?)?;
    if *out.concl() != Formula::not(Formula::mem(tx, wt.of(z, tb, tu))) {
        return None
    }
    Some(gen_all(&[bv, uv, xv], &out))
}

/// `⊢ ∀B ∀u. W(∅, B, u) = ∅` — the same fact as an equation.
///
/// Extensionality applied to [`empty_wtype_uninhabited`]: both directions of
/// `x ∈ W ↔ x ∈ ∅` are refutations of their own antecedents.
pub fn empty_wtype_eq(env: &mut Env, wt: &Wtype, uninhabited: &Thm) -> Option<Thm> {
    let z = wt.empty();
    let empty_ax = wt.sums.ap.empty_ax.clone();
    let (bv, uv) = (env.fresh_var(), env.fresh_var());
    let (tb, tu) = (Term::var(bv), Term::var(uv));
    let w_t = wt.of(z.clone(), tb.clone(), tu.clone());

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let not_in_w = inst_all(uninhabited, &[tb.clone(), tu.clone(), tx.clone()])?;
    let fwd = syl(&not_in_w, &ex_falso(Formula::mem(tx.clone(), z.clone())))?;
    let bwd = syl(
        &inst_all(&empty_ax, std::slice::from_ref(&tx))?,
        &ex_falso(Formula::mem(tx.clone(), w_t.clone())),
    )?;
    let all_iff = Thm::gen(xv, &and_intro(&fwd, &bwd));
    let ext = inst_all(&Thm::ax_extensionality(env), &[w_t.clone(), z.clone()])?;
    let out = Thm::mp(&ext, &all_iff)?;
    if *out.concl() != Formula::eq(w_t, z) {
        return None
    }
    Some(gen_all(&[bv, uv], &out))
}

/// **The anchor, at the term the backend uses.**
/// `⊢ ∀x. ¬(x ∈ enum(0))`, where `enum(0)` is [`crate::enums::enum0`].
///
/// The subject term is obtained by calling `enum0`, not by re-spelling
/// `W(0,∅,U(0))`, and the result is checked to be about that term — so if
/// `enum0` ever changes shape this returns `None` rather than a theorem about a
/// set nothing interprets.
pub fn enum0_uninhabited(env: &mut Env, wt: &Wtype, bnd: &Bound, uninhabited: &Thm) -> Option<Thm> {
    let z = wt.empty();
    let u = Term::apply(bnd.lu, vec![z.clone()]);
    let e0 = crate::enums::enum0(wt, bnd);
    let out = inst_all(uninhabited, &[z, u])?;
    let xv = env.fresh_var();
    if *out.concl() != Formula::forall(xv, Formula::not(Formula::mem(Term::var(xv), e0))) {
        return None
    }
    Some(out)
}

/// `⊢ enum(0) = ∅` — the same, as an equation, at the backend's term.
pub fn enum0_eq(wt: &Wtype, bnd: &Bound, eq: &Thm) -> Option<Thm> {
    let z = wt.empty();
    let u = Term::apply(bnd.lu, vec![z.clone()]);
    let e0 = crate::enums::enum0(wt, bnd);
    let out = inst_all(eq, &[z.clone(), u])?;
    if *out.concl() != Formula::eq(e0, z) {
        return None
    }
    Some(out)
}

/// Carry an emptiness theorem along a **defining equation**: from `⊢ c = X` and
/// `⊢ ∀x. ¬(x ∈ X)` infer `⊢ ∀x. ¬(x ∈ c)`.
///
/// This is the last step an interpretation needs. `checker/src/tg.rs` does not
/// use `enum(0)` directly — it introduces an abbreviation symbol with
/// `⊢ ⟦Empty⟧ = W(0,∅,U(0))` (`ind_abbrev`) and uses that — so the anchor has to
/// travel one Leibniz step to reach `⟦Empty⟧` itself. The same helper serves the
/// `Prop` side, where `⟦False⟧` would be introduced with `⊢ ⟦False⟧ = ∅`.
///
/// The companion equation `⊢ c = ∅` is [`crate::eq_trans`] of the same two
/// inputs and needs no helper.
pub fn uninhabited_along(env: &mut Env, def: &Thm, uninhabited: &Thm) -> Option<Thm> {
    let (c, body) = def.concl().as_eq()?;
    let back = eq_symm(env, def)?; // `⊢ X = c`

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let at_x = inst_all(uninhabited, std::slice::from_ref(&tx))?;
    if *at_x.concl() != Formula::not(Formula::mem(tx.clone(), body.clone())) {
        return None
    }
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(
        body,
        c.clone(),
        w,
        Formula::not(Formula::mem(tx.clone(), Term::var(w))),
    );
    let out = Thm::mp(&Thm::mp(&leib, &back)?, &at_x)?;
    if *out.concl() != Formula::not(Formula::mem(tx, c)) {
        return None
    }
    Some(Thm::gen(xv, &out))
}

/// `⊢ ∀T. ∅ ∈ fs(enum(0), T)` — **the eliminator for the empty type is the
/// empty function**.
///
/// `⊢ ∀S. ∅ ∈ fs(∅, S)` is [`crate::wtype::empty_is_a_function`], already in the
/// crate; all that happens here is that `∅` is rewritten to `enum(0)` in the
/// domain, backwards along [`enum0_eq`]. No W-recursor, no totality argument,
/// no ι rule: there is no element to compute at.
pub fn enum0_rec(env: &mut Env, wt: &Wtype, bnd: &Bound, e0_eq: &Thm) -> Option<Thm> {
    let z = wt.empty();
    let e0 = crate::enums::enum0(wt, bnd);
    if *e0_eq.concl() != Formula::eq(e0.clone(), z.clone()) {
        return None
    }
    let back = eq_symm(env, e0_eq)?;

    let tv = env.fresh_var();
    let tt = Term::var(tv);
    let at_t = inst_all(&wt.empty_fun, std::slice::from_ref(&tt))?;

    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(
        z.clone(),
        e0.clone(),
        w,
        Formula::mem(z.clone(), wt.sums.fs.of(Term::var(w), tt.clone())),
    );
    let out = Thm::mp(&Thm::mp(&leib, &back)?, &at_t)?;
    if *out.concl() != Formula::mem(z, wt.sums.fs.of(e0, tt)) {
        return None
    }
    Some(Thm::gen(tv, &out))
}
