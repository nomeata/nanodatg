//! **Non-vacuity**: the quotient of `A` by nothing is `A` again.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀x. (x ∈ A → app(id(A),x) = x)                       [identity_beta]
//! ⊢ ∀A ∀f. rcompat(A,∅,f)                                   [rcompat_at_empty]
//! ⊢ ∀A ∀f. compat(A,∅,f)                                    [compat_at_empty]
//! ⊢ ∀A ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,∅) → x = y)                    [eqv_of_empty]
//! ⊢ ∀A ∀a ∀b. ((b ∈ A ∧ class(A,∅,a) = class(A,∅,b)) → a = b)
//!                                                           [class_injective_at_empty]
//! ⊢ ∀A ∀f ∀x. (x ∈ A → app(lift(A,∅,f), class(A,∅,x)) = app(f,x))
//!                                                           [lift_beta_at_empty]
//! ```
//!
//! # What could have gone wrong, and why these say it did not
//!
//! Every theorem in [`super::eqv`], [`super::classes`] and [`super::lift`] is
//! satisfied by the **collapsed** interpretation
//!
//! ```text
//! eqv(A,R) = prod(A,A)        class(A,R,x) = A        quot(A,R) = {A}
//! ```
//!
//! — one class, one point in the quotient, `mk` constant, `sound` trivial and
//! `lift` a one-entry graph. That reading makes `q_sound` true for free and
//! makes the entire module say nothing about Lean's `Quot`. So the module needs
//! a witness that `∼` is *not* everything, and [`eqv_of_empty`] is it:
//! **`eqv(A,∅)` is contained in the diagonal**, so at `R := ∅` distinct points
//! of `A` have distinct classes ([`class_injective_at_empty`]) and `quot(A,∅)`
//! is in bijection with `A`.
//!
//! There is a second way the module could have said nothing: [`super::lift`]'s
//! theorems all carry `compat(A,R,f)` as an antecedent, and an antecedent no `f`
//! ever satisfies makes a theorem vacuous just as surely as a collapsed `∼`.
//! [`compat_at_empty`] discharges that — at `R := ∅` *every* `f` is compatible —
//! so [`lift_beta_at_empty`] is `lift`'s computation rule with **no hypothesis
//! at all**, for an arbitrary `f`.
//!
//! # How the diagonal bound is derived
//!
//! Not by building a diagonal set and re-proving four closure clauses. The
//! machinery is already in [`super::compat`]: `ker(A,f)` is an equivalence
//! relation on `A` containing `∅` for *every* `f`, so
//! [`super::compat::compat_closure`] gives `∼ ⊆ ker(A,f)` — that is,
//! **`app(f,·)` cannot tell related points apart, whatever `f` is**. Taking
//! `f := id(A)`, the identity graph of [`crate::funspace::identity_graph`],
//! turns that into `x = y`, because `app(id(A),·)` is the identity on `A`
//! ([`identity_beta`]).
//!
//! That is the whole argument, and it is why [`super::eqv::eqv_induction`] is
//! load-bearing twice over: once for `Quot.lift`'s hypothesis and once here.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funspace::{identity_graph, identity_is_function, is_function};
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, eq_symm_imp, ex_falso, exists_intro_imp, gen_all, hyp_and, hyp_mp,
    iff_mp, iff_mpr, imp_refl, inst_all, syl,
};

use super::compat::rcompat;
use super::shared::{eq_chain, split_and};

/// The empty set as a term.
fn empty_of(s: &Sums) -> Term { Term::apply(s.ap.empty, vec![]) }

/// The identity graph `id(A) = { ⟨x,x⟩ : x ∈ A }`, its defining axiom, and
/// `⊢ ∀A. isfun(id(A))`.
///
/// Built here rather than taken as a parameter because it is used for exactly
/// one thing — separating the points of `A` in [`eqv_of_empty`] — and a caller
/// with no interest in non-vacuity should not have to supply one.
pub struct Identity {
    /// The symbol `id`.
    pub id: FnSym,
    /// `⊢ ∀a ∀z. (z ∈ id(a) ↔ ∃x. (x ∈ a ∧ z = ⟨x,x⟩))`.
    pub id_ax: Thm,
    /// `⊢ ∀a. isfun(id(a))`.
    pub is_fun: Thm,
    /// `⊢ ∀A ∀x. (x ∈ A → app(id(A),x) = x)`.
    pub beta: Thm,
}

impl Identity {
    /// Build the graph and derive its beta rule.
    pub fn new(env: &mut Env, s: &Sums, app_pair: &Thm) -> Option<Identity> {
        let (id, id_ax) = identity_graph(env, &s.ap.sets)?;
        let is_fun =
            identity_is_function(env, &s.ap.sets, &s.prod, id, &id_ax, &s.ap.pair_inj)?;
        let beta = identity_beta(env, s, id, &id_ax, &is_fun, app_pair)?;
        Some(Identity { id, id_ax, is_fun, beta })
    }
}

/// `⊢ ∀A ∀x. (x ∈ A → app(id(A),x) = x)` — the identity graph computes.
///
/// `⟨x,x⟩ ∈ id(A)` witnesses the Replacement image at `x`, and single-valuedness
/// is the third conjunct of [`crate::funspace::identity_is_function`], so
/// [`crate::ext::app_of_pair`] returns `x`.
fn identity_beta(
    env: &mut Env,
    s: &Sums,
    id: FnSym,
    id_ax: &Thm,
    is_fun: &Thm,
    app_pair: &Thm,
) -> Option<Thm> {
    let (av, xv, wv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tx, tw) = (Term::var(av), Term::var(xv), Term::var(wv));
    let id_a = Term::apply(id, vec![ta.clone()]);
    let pair_xx = s.ap.sets.pair(tx.clone(), tx.clone());
    let mem_a = Formula::mem(tx.clone(), ta.clone());

    // `x ∈ A → ⟨x,x⟩ ∈ id(A)`.
    let at = inst_all(id_ax, &[ta.clone(), pair_xx.clone()])?;
    let body = Formula::and(
        Formula::mem(tw.clone(), ta.clone()),
        Formula::eq(pair_xx.clone(), s.ap.sets.pair(tw.clone(), tw)),
    );
    let intro = exists_intro_imp(wv, body, tx.clone())?;
    let witnessed =
        hyp_and(&imp_refl(mem_a.clone()), &a1i(&Thm::eq_refl(pair_xx.clone()), mem_a.clone()))?;
    let has = syl(&syl(&witnessed, &intro)?, &iff_mpr(&at)?)?;

    // Single-valuedness, the third conjunct of `isfun(id(A))`.
    let isfun = is_function(env, &s.ap.sets, &s.prod, &ta, &ta, &id_a);
    let fun_at = inst_all(is_fun, std::slice::from_ref(&ta))?;
    if *fun_at.concl() != isfun {
        return None
    }
    let (sub, rest) = split_and(&isfun)?;
    let (total, sv_f) = split_and(&rest)?;
    let sv = Thm::mp(&and_right(total, sv_f), &Thm::mp(&and_right(sub, rest.clone()), &fun_at)?)?;

    let ap = inst_all(app_pair, &[id_a, tx.clone(), tx.clone()])?;
    let out = syl(&hyp_and(&a1i(&sv, mem_a), &has)?, &ap)?;
    Some(gen_all(&[av, xv], &out))
}

/// `⊢ ∀A ∀f. rcompat(A,∅,f)` — **every** function is compatible with the empty
/// relation.
///
/// Vacuously: the hypothesis of each instance contains `⟨x,y⟩ ∈ ∅`, which
/// [`crate::empty::empty`] refutes.
pub fn rcompat_at_empty(env: &mut Env, s: &Sums) -> Option<Thm> {
    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(fv));
    let e = empty_of(s);
    let rc = rcompat(env, s, &ta, &e, &tf);

    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let pair = s.ap.sets.pair(tx.clone(), ty.clone());
    let in_e = Formula::mem(pair, e);
    let (ma_x, ma_y) = (
        Formula::mem(tx.clone(), ta.clone()),
        Formula::mem(ty.clone(), ta.clone()),
    );
    let tail = Formula::and(ma_y.clone(), in_e.clone());
    let h = Formula::and(ma_x.clone(), tail.clone());

    let to_in_e = syl(&and_right(ma_x, tail), &and_right(ma_y, in_e))?;
    let probe = s.ap.sets.pair(tx.clone(), ty.clone());
    let refuted = inst_all(&s.ap.empty_ax, std::slice::from_ref(&probe))?;
    let eq = Formula::eq(s.ap.apply(tf.clone(), tx), s.ap.apply(tf.clone(), ty));
    let absurd = syl(&to_in_e, &refuted)?;
    let out = syl(&absurd, &ex_falso(eq))?;
    if out.concl().as_imp()?.0 != h {
        return None
    }
    let mut all = out;
    for v in [yv, xv] {
        all = Thm::gen(v, &all);
    }
    if *all.concl() != rc {
        return None
    }
    Some(gen_all(&[av, fv], &all))
}

/// `⊢ ∀A ∀f. compat(A,∅,f)` — and therefore every function respects
/// `eqv(A,∅)`.
///
/// [`super::compat::compat_closure`] applied to [`rcompat_at_empty`]. This is
/// what makes [`super::lift`]'s antecedent satisfiable, and hence its theorems
/// non-vacuous.
pub fn compat_at_empty(env: &mut Env, s: &Sums, compat_closure: &Thm, rc: &Thm) -> Option<Thm> {
    let (av, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(fv));
    let e = empty_of(s);
    let cc = inst_all(compat_closure, &[ta.clone(), e, tf.clone()])?;
    let at = inst_all(rc, &[ta, tf])?;
    let out = Thm::mp(&cc, &at)?;
    Some(gen_all(&[av, fv], &out))
}

/// `⊢ ∀A ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,∅) → x = y)` — **the closure of nothing is the
/// diagonal**.
///
/// [`compat_at_empty`] at `f := id(A)` says `app(id(A),x) = app(id(A),y)`, and
/// [`identity_beta`] turns both sides into the points themselves. `x ∈ A` and
/// `y ∈ A` come from `eqv(A,∅) ⊆ prod(A,A)`, so no membership hypothesis is
/// needed.
pub fn eqv_of_empty(
    env: &mut Env,
    s: &Sums,
    eqv: FnSym,
    eqv_subset: &Thm,
    identity: &Identity,
    compat_at_empty: &Thm,
) -> Option<Thm> {
    let (av, xv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tx, ty) = (Term::var(av), Term::var(xv), Term::var(yv));
    let e = empty_of(s);
    let id_a = Term::apply(identity.id, vec![ta.clone()]);
    let app = |t: &Term| s.ap.apply(id_a.clone(), t.clone());
    let pair = s.ap.sets.pair(tx.clone(), ty.clone());
    let h = Formula::mem(pair.clone(), Term::apply(eqv, vec![ta.clone(), e.clone()]));

    // `x ∈ A` and `y ∈ A`, out of `eqv(A,∅) ⊆ A²`.
    let sub = inst_all(eqv_subset, &[ta.clone(), e.clone(), pair])?;
    let pip = inst_all(&s.pair_in_prod, &[ta.clone(), ta.clone(), tx.clone(), ty.clone()])?;
    let (ma_x, ma_y) = (
        Formula::mem(tx.clone(), ta.clone()),
        Formula::mem(ty.clone(), ta.clone()),
    );
    let both = syl(&sub, &iff_mp(&pip)?)?;
    let h_x = syl(&both, &and_left(ma_x.clone(), ma_y.clone()))?;
    let h_y = syl(&both, &and_right(ma_x, ma_y))?;

    // `app(id(A),x) = app(id(A),y)`.
    let c = inst_all(compat_at_empty, &[ta.clone(), id_a.clone()])?;
    let h_app = inst_all(&c, &[tx.clone(), ty.clone()])?;

    // `x = app(id,x) = app(id,y) = y`.
    let bx = inst_all(&identity.beta, &[ta.clone(), tx.clone()])?;
    let by = inst_all(&identity.beta, &[ta.clone(), ty.clone()])?;
    let h_bx = syl(&h_x, &syl(&bx, &eq_symm_imp(env, app(&tx), tx.clone()))?)?;
    let h_by = syl(&h_y, &by)?;
    let c1 = eq_chain(env, tx.clone(), app(&tx), app(&ty));
    let s1 = hyp_mp(&syl(&h_app, &c1)?, &h_bx)?;
    let c2 = eq_chain(env, tx.clone(), app(&ty), ty.clone());
    let out = hyp_mp(&syl(&h_by, &c2)?, &s1)?;
    if *out.concl() != Formula::imp(h, Formula::eq(tx, ty)) {
        return None
    }
    Some(gen_all(&[av, xv, yv], &out))
}

/// `⊢ ∀A ∀a ∀b. ((b ∈ A ∧ class(A,∅,a) = class(A,∅,b)) → a = b)` — **`mk` is
/// injective at `R := ∅`**, so `quot(A,∅)` has as many points as `A`.
///
/// The statement that keeps the whole module honest: it rules out the collapsed
/// reading in which `class` is constant and `quot(A,R)` is a singleton.
pub fn class_injective_at_empty(
    env: &mut Env,
    s: &Sums,
    class_exact: &Thm,
    eqv_of_empty: &Thm,
) -> Option<Thm> {
    let (av, a1, b1) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, taa, tbb) = (Term::var(av), Term::var(a1), Term::var(b1));
    let e = empty_of(s);
    let exact = inst_all(class_exact, &[ta.clone(), e.clone(), taa.clone(), tbb.clone()])?;
    let diag = inst_all(eqv_of_empty, &[ta, taa, tbb])?;
    let out = syl(&exact, &diag)?;
    Some(gen_all(&[av, a1, b1], &out))
}

/// `⊢ ∀A ∀f ∀x. (x ∈ A → app(lift(A,∅,f), class(A,∅,x)) = app(f,x))` —
/// **`lift`'s computation rule with no compatibility hypothesis**.
///
/// [`super::lift::lift_beta`] with its antecedent discharged by
/// [`compat_at_empty`]. Its point is that `lift_beta` is not vacuously true: at
/// `R := ∅` it is an unconditional ι-rule for an arbitrary `f`, over a quotient
/// that [`class_injective_at_empty`] shows is not a point.
pub fn lift_beta_at_empty(
    env: &mut Env,
    s: &Sums,
    lift_beta: &Thm,
    compat_at_empty: &Thm,
) -> Option<Thm> {
    let (av, fv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tx) = (Term::var(av), Term::var(fv), Term::var(xv));
    let e = empty_of(s);
    let beta = inst_all(lift_beta, &[ta.clone(), e.clone(), tf.clone(), tx.clone()])?;
    let c = inst_all(compat_at_empty, &[ta.clone(), tf.clone()])?;
    let mem_a = Formula::mem(tx.clone(), ta.clone());
    let paired = hyp_and(&a1i(&c, mem_a.clone()), &imp_refl(mem_a))?;
    let out = syl(&paired, &beta)?;
    Some(gen_all(&[av, fv, xv], &out))
}
