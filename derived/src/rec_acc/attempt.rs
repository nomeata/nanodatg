//! **Attempts** — partial approximations to the recursor — and the set of them.
//!
//! # Interface
//!
//! ```text
//! preds_indom(A,R,g,x) := ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → indom(g,y)))
//! rec_cond(A,R,e,g)    := ∀x. (indom(g,x) →
//!                           (preds_indom(A,R,g,x) ∧
//!                            app(g,x) = app(app(app(e,x),•), ih(g,A,R,x))))
//!
//! ⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att(A,R,T,e) ↔
//!       (g ∈ 𝒫(prod(acc(A,R),T)) ∧ (sv(g) ∧ rec_cond(A,R,e,g))))     [attempts]
//! ```
//!
//! with [`att_of`] building the term `Att(A,R,T,e)` and [`attempt_bound`] the
//! superset Separation carves it out of. Callers need none of the derivation
//! below.
//!
//! # What an attempt is, and what it is not
//!
//! An attempt is a single-valued set of pairs, inside `acc(A,R) × T`, whose
//! domain is closed *downwards along `R`* and which satisfies the recursion
//! equation wherever it is defined. It is the same object
//! [`crate::wrec::attempts`] defines for `W`, with one difference that shapes
//! the whole module: `W`'s downward closure is "every subterm `f(b)` is in the
//! domain", read off the tree structure of the point, whereas here it is "every
//! `R`-predecessor inside `A` is in the domain", read off the *relation*. So
//! there is no composite, no fibre and no domain operator; there is
//! [`super::ih`].
//!
//! **No attempt is required to be total, and none is required to be a
//! function on `acc(A,R)`.** `∅` is an attempt ([`empty_attempt`]), which is
//! what makes the set of attempts non-empty before anything has been proved
//! about it, and what makes the union a legitimate object to start from.
//!
//! # Why the bound needs no universe
//!
//! `acc(A,R) ⊆ A` by construction ([`crate::acc::acc_subset`]), so
//! `𝒫(prod(acc(A,R),T))` exists outright and Separation carves the attempts out
//! of it in one step. [`crate::wrec`] has to carry a bound `u` and the
//! antecedent `closed(A,B,u)` through every single theorem for exactly the
//! reason this module does not: `W(A,B,u)` is not a subset of anything already
//! named. Every theorem in [`crate::rec_acc`] up to and including the guarded ι
//! rule is therefore **unconditional**, where the corresponding `wrec` theorem
//! carries `closed(A,B,u)`.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::separation_full;
use crate::funspace::is_single_valued;
use crate::{exists_intro_imp, gen_all, inst_all, syl};

use super::base::Base;

/// `∀y. (y ∈ A → (⟨y,x⟩ ∈ R → indom(g,y)))` — "`g` is defined at every
/// `R`-predecessor of `x` inside `A`", as a formula.
///
/// The exact analogue of [`crate::acc::preds_in`] with "lies in `C`" replaced by
/// "lies in the domain of `g`". The domain itself stays unnamed: there is no
/// domain operator in this crate, and this condition is only ever passed along.
pub fn preds_indom(env: &mut Env, b: &Base, a: &Term, r: &Term, g: &Term, x: &Term) -> Formula {
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let inner = b.indom(env, g, &ty);
    Formula::forall(
        yv,
        Formula::imp(
            Formula::mem(ty.clone(), a.clone()),
            Formula::imp(Formula::mem(b.edge(&ty, x), r.clone()), inner),
        ),
    )
}

/// The recursion condition on `g`:
///
/// ```text
/// ∀x. (indom(g,x) → (preds_indom(A,R,g,x) ∧
///                    app(g,x) = app(app(app(e,x),•), ih(g,A,R,x))))
/// ```
///
/// Two clauses, exactly as in [`crate::wrec::rec_cond`]: the domain is closed
/// downwards, and the equation holds there. Note it mentions neither the target
/// `T` nor `acc(A,R)` — those are carried by the ambient condition
/// `g ⊆ prod(acc(A,R),T)`.
pub fn rec_cond(env: &mut Env, b: &Base, a: &Term, r: &Term, e: &Term, g: &Term) -> Formula {
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let head = b.indom(env, g, &tx);
    let preds = preds_indom(env, b, a, r, g, &tx);
    let equation = Formula::eq(
        b.app(g, &tx),
        b.step_at(e, &tx, &b.ih_at(g, a, r, &tx)),
    );
    Formula::forall(xv, Formula::imp(head, Formula::and(preds, equation)))
}

/// `sv(g) ∧ rec_cond(A,R,e,g)` — what Separation carves the attempts out with.
///
/// Single-valuedness is not needed by the agreement induction, but the union of
/// all attempts has to be a *function* for `app(·,x)` to mean anything, and that
/// needs every attempt to be one.
pub fn attempt_cond(env: &mut Env, b: &Base, a: &Term, r: &Term, e: &Term, g: &Term) -> Formula {
    Formula::and(
        is_single_valued(env, &b.s.ap.sets, g),
        rec_cond(env, b, a, r, e, g),
    )
}

/// The term `𝒫(prod(acc(A,R), T))` — the set Separation carves the attempts out
/// of.
pub fn attempt_bound(b: &Base, a: &Term, r: &Term, t: &Term) -> Term {
    Term::apply(b.s.pow, vec![b.s.prod.of(b.acc_of(a, r), t.clone())])
}

/// Introduce `Att(A,R,T,e)`, the set of attempts, with
///
/// ```text
/// ⊢ ∀A ∀R ∀T ∀e ∀g. (g ∈ Att(A,R,T,e) ↔
///       (g ∈ 𝒫(prod(acc(A,R),T)) ∧ (sv(g) ∧ rec_cond(A,R,e,g))))
/// ```
///
/// One [`crate::funcs::separation_full`] — the full form rather than the
/// inhabited one, because nothing yet says an attempt exists. `∅` is one, but
/// that is [`empty_attempt`] and is not needed to make the symbol legal.
pub fn attempts(env: &mut Env, b: &Base) -> Option<(FnSym, Thm)> {
    let (av, rv, tv, ev, gv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, tt, te, tg) = (
        Term::var(av),
        Term::var(rv),
        Term::var(tv),
        Term::var(ev),
        Term::var(gv),
    );

    let bound = attempt_bound(b, &ta, &tr, &tt);
    let psi = attempt_cond(env, b, &ta, &tr, &te, &tg);
    let existence = separation_full(env, gv, &psi, &bound, &b.s.ap.empty_ax).ok()?;
    let guard = Formula::and(Formula::mem(tg, bound), psi);
    crate::define_by_membership(env, &[av, rv, tv, ev], &existence, gv, &guard)
}

/// The term `Att(A,R,T,e)`.
pub fn att_of(att: FnSym, a: Term, r: Term, t: Term, e: Term) -> Term {
    Term::apply(att, vec![a, r, t, e])
}

/// `⊢ ⟨x,y⟩ ∈ g → indom(g,x)` — the only way the domain condition is ever
/// introduced, and it is introduction only.
pub fn indom_intro(env: &mut Env, b: &Base, g: &Term, x: &Term, y: &Term) -> Option<Thm> {
    let yv = env.fresh_var();
    let body = Formula::mem(b.s.ap.sets.pair(x.clone(), Term::var(yv)), g.clone());
    exists_intro_imp(yv, body, y.clone())
}

/// `⊢ ∀A ∀R ∀T ∀e. ∅ ∈ Att(A,R,T,e)` — **the set of attempts is never empty**.
///
/// Without this the union could be `⋃∅ = ∅` for a reason having nothing to do
/// with the recursion, and every theorem about it would be about nothing. The
/// three clauses are all vacuous at `∅`: it has no members, so it is inside any
/// power set, single-valued, and satisfies `rec_cond` because `indom(∅,x)` never
/// holds.
///
/// `att_ax` must be **unconditional**, and the final membership is pinned in
/// **release**. The three clauses derived here are all compared against
/// rebuilt formulas, so the *right-hand side* of `att_ax` is checked by the
/// [`Thm::mp`] that spends it — but its *left-hand side* is not, and the
/// left-hand side is the claim: `iff_mpr` hands back whatever membership the
/// caller's biconditional had on the left, so a foreign
/// `∀A ∀R ∀T ∀e ∀g. (g ∈ FOO(A,R,T,e) ↔ same-RHS)` returned a true theorem
/// relabelled "`∅` is an attempt". With the check only under `debug_assert`
/// the release measurement path had no pin on it at all.
pub fn empty_attempt(env: &mut Env, b: &Base, att: FnSym, att_ax: &Thm) -> Option<Thm> {
    if !att_ax.hyps().is_empty() {
        return None
    }
    let (av, rv, tv, ev) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, tt, te) = (
        Term::var(av),
        Term::var(rv),
        Term::var(tv),
        Term::var(ev),
    );
    let z = Term::apply(b.s.ap.empty, vec![]);

    // Everything about `∅` is `⊢ ∀w. ¬(w ∈ ∅)` used to kill a hypothesis.
    let no_member = |t: &Term| -> Option<Thm> {
        inst_all(&b.s.ap.empty_ax, std::slice::from_ref(t))
    };

    // `∅ ∈ 𝒫(prod(acc,T))`, i.e. `∅ ⊆ prod(acc,T)`.
    let bound = attempt_bound(b, &ta, &tr, &tt);
    let wv = env.fresh_var();
    let tw = Term::var(wv);
    let sub_body = crate::ex_falso(Formula::mem(tw.clone(), b.s.prod.of(b.acc_of(&ta, &tr), tt.clone())));
    let sub = Thm::gen(wv, &syl(&no_member(&tw)?, &sub_body)?);
    let pow_at = inst_all(&b.s.pow_ax, &[b.s.prod.of(b.acc_of(&ta, &tr), tt.clone()), z.clone()])?;
    let in_pow = Thm::mp(&crate::iff_mpr(&pow_at)?, &sub)?;
    if *in_pow.concl() != Formula::mem(z.clone(), bound) {
        return None
    }

    // `sv(∅)`.
    let (xv, yv, y2v) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(xv), Term::var(yv), Term::var(y2v));
    let m1 = Formula::mem(b.s.ap.sets.pair(tx.clone(), ty.clone()), z.clone());
    let m2 = Formula::mem(b.s.ap.sets.pair(tx.clone(), ty2.clone()), z.clone());
    let sv_body = syl(
        &crate::and_left(m1.clone(), m2.clone()),
        &syl(
            &no_member(&b.s.ap.sets.pair(tx.clone(), ty.clone()))?,
            &crate::ex_falso(Formula::eq(ty.clone(), ty2.clone())),
        )?,
    )?;
    let sv = gen_all(&[xv, yv, y2v], &sv_body);
    if *sv.concl() != is_single_valued(env, &b.s.ap.sets, &z) {
        return None
    }

    // `rec_cond(A,R,e,∅)`: the head `indom(∅,x)` is refutable.
    let x2 = env.fresh_var();
    let tx2 = Term::var(x2);
    let head = b.indom(env, &z, &tx2);
    let preds = preds_indom(env, b, &ta, &tr, &z, &tx2);
    let equation = Formula::eq(
        b.app(&z, &tx2),
        b.step_at(&te, &tx2, &b.ih_at(&z, &ta, &tr, &tx2)),
    );
    let wit = env.fresh_var();
    let no_pair = no_member(&b.s.ap.sets.pair(tx2.clone(), Term::var(wit)))?;
    let not_head = crate::exists_elim_imp(
        wit,
        &Thm::gen(wit, &no_pair),
        &Formula::false_(),
    )?;
    if *not_head.concl() != Formula::imp(head, Formula::false_()) {
        return None
    }
    let rc_body = syl(&not_head, &crate::ex_falso(Formula::and(preds, equation)))?;
    let rc = Thm::gen(x2, &rc_body);
    if *rc.concl() != rec_cond(env, b, &ta, &tr, &te, &z) {
        return None
    }

    let cond = crate::and_intro(&sv, &rc);
    let at = inst_all(att_ax, &[ta.clone(), tr.clone(), tt.clone(), te.clone(), z.clone()])?;
    let out = Thm::mp(&crate::iff_mpr(&at)?, &crate::and_intro(&in_pow, &cond))?;
    // Release, not `debug_assert`: this pins the *claim*, i.e. that the set the
    // theorem says `∅` belongs to really is `Att(A,R,T,e)`. See the header.
    if *out.concl() != Formula::mem(z, att_of(att, ta, tr, tt, te)) {
        return None
    }
    Some(gen_all(&[av, rv, tv, ev], &out))
}
