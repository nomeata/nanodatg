//! **Step 2** — attempts, and the set of them.
//!
//! An *attempt* is a partial approximation to the recursor: a single-valued set
//! of pairs inside `prod(W,T)` that satisfies the recursion equation wherever
//! it is defined, and whose domain is closed downwards under subterms.
//!
//! # Interface
//!
//! ```text
//! indom(g,x)      := ∃y. ⟨x,y⟩ ∈ g                                       [indom]
//! rec_cond(B,e,g) := ∀a ∀f. (indom(g,⟨a,f⟩) →
//!                      ((∀b. (b ∈ B(a) → indom(g, app(f,b))))
//!                       ∧ app(g,⟨a,f⟩) = app(e, ⟨a,⟨f, comp(g,f,B(a))⟩⟩)))  [rec_cond]
//!
//! ⊢ ∀A ∀B ∀u ∀T ∀e ∀g.
//!       (g ∈ Att ↔ (g ∈ 𝒫(prod(W,T)) ∧ (sv(g) ∧ rec_cond(B,e,g))))        [attempts]
//! ```
//!
//! [`att_of`] builds the term `Att(A,B,u,T,e)`, [`attempt_bound`] the superset
//! `𝒫(prod(W,T))` Separation carves it out of, [`attempt_cond`] the condition
//! itself, and [`step_at`] the term `app(e, ⟨a,⟨f, comp(g,f,B(a))⟩⟩)`. Callers
//! need none of the derivation below.
//!
//! # Why the recursion equation is stated with `app`
//!
//! The two natural phrasings of "the recursion equation holds at `w ∈ dom g`"
//! are
//!
//! ```text
//! ∀y. (⟨w,y⟩ ∈ g → y = app(e, …))        and        app(g,w) = app(e, …)
//! ```
//!
//! The second is used, and the reason is [`super::agreement`]: it runs by
//! structural induction with the hypothesis *"`g` and `h` agree at every
//! subterm"*, and with the first phrasing that hypothesis has to be
//! destructured — an existential witness for each of `g` and `h`, eliminated
//! under the induction's ambient hypothesis — before the two values can be
//! compared. With the second it is an equation between terms and composes
//! directly. Measured effect: the induction step needs *no* existential
//! elimination at all.
//!
//! `dom g` itself stays unnamed. [`indom`] is only ever introduced —
//! `indom_intro` is the sole way in, and it is introduction only — or passed
//! along, never taken apart inside the induction.
//!
//! Single-valuedness is still part of being an attempt, because the union has
//! to be a function for `app(wrec,·)` to mean anything; it is simply not needed
//! *inside* the induction.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::funcs::{separation_full, Apply};
use crate::funspace::is_single_valued;
use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::exists_intro_imp;

use super::composite::comp_of;

/// `∃y. ⟨x,y⟩ ∈ g` — "`x` is in the domain of `g`", as a formula.
///
/// There is no domain *operator* here, and none is needed: this condition is
/// only ever passed along, never taken apart.
pub fn indom(env: &mut Env, ap: &Apply, g: &Term, x: &Term) -> Formula {
    let yv = env.fresh_var();
    Formula::exists(yv, Formula::mem(ap.sets.pair(x.clone(), Term::var(yv)), g.clone()))
}

/// The term `app(e, ⟨a, ⟨f, comp(g,f,d)⟩⟩)` — the step applied to the flat
/// Kuratowski triple. See the module header for why it is flat.
pub fn step_at(
    ap: &Apply,
    comp: FnSym,
    e: &Term,
    g: &Term,
    a: &Term,
    f: &Term,
    d: &Term,
) -> Term {
    let c = comp_of(comp, g.clone(), f.clone(), d.clone());
    ap.apply(e.clone(), ap.sets.pair(a.clone(), ap.sets.pair(f.clone(), c)))
}

/// The recursion condition on `g`:
///
/// ```text
/// ∀a ∀f. (indom(g,⟨a,f⟩) →
///           ((∀b. (b ∈ B(a) → indom(g, app(f,b))))
///            ∧ app(g,⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(g,f,B(a))⟩⟩)))
/// ```
///
/// Two clauses: the domain is closed under subterms, and the equation holds
/// there. Note it mentions neither `A`, nor the bound `u`, nor the target `T` —
/// those are carried by the *ambient* condition `g ⊆ prod(W(A,B,u), T)`.
pub fn rec_cond(env: &mut Env, ap: &Apply, comp: FnSym, b: &Term, e: &Term, g: &Term) -> Formula {
    let (av, fv, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tf, tb) = (Term::var(av), Term::var(fv), Term::var(bv));

    let fibre = ap.apply(b.clone(), ta.clone());
    let w = ap.sets.pair(ta.clone(), tf.clone());

    let sub = indom(env, ap, g, &ap.apply(tf.clone(), tb.clone()));
    let subterms = Formula::forall(bv, Formula::imp(Formula::mem(tb, fibre.clone()), sub));
    let equation = Formula::eq(
        ap.apply(g.clone(), w.clone()),
        step_at(ap, comp, e, g, &ta, &tf, &fibre),
    );

    let head = indom(env, ap, g, &w);
    Formula::forall(
        av,
        Formula::forall(fv, Formula::imp(head, Formula::and(subterms, equation))),
    )
}

/// `sv(g) ∧ rec_cond(g)` — what Separation carves the set of attempts with.
///
/// Single-valuedness is not used by the agreement argument, but the union of
/// all attempts has to be a *function* for `app` to mean anything, and that
/// needs every attempt to be one.
pub fn attempt_cond(
    env: &mut Env,
    s: &Sums,
    comp: FnSym,
    b: &Term,
    e: &Term,
    g: &Term,
) -> Formula {
    Formula::and(
        is_single_valued(env, &s.ap.sets, g),
        rec_cond(env, &s.ap, comp, b, e, g),
    )
}

/// The term `𝒫(prod(W(A,B,u), T))` — the set Separation carves the attempts out
/// of. Every attempt is a set of pairs with domain in `W` and values in `T`.
pub fn attempt_bound(s: &Sums, wt: &Wtype, a: &Term, b: &Term, u: &Term, t: &Term) -> Term {
    let w = wt.of(a.clone(), b.clone(), u.clone());
    Term::apply(s.pow, vec![s.prod.of(w, t.clone())])
}

/// Introduce `Att(A,B,u,T,e)`, the set of attempts, with
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e ∀g.
///     (g ∈ Att(A,B,u,T,e) ↔ (g ∈ 𝒫(prod(W(A,B,u),T)) ∧ (sv(g) ∧ rec_cond(g))))
/// ```
///
/// One Separation. It is `separation_full` rather than the inhabited form
/// because nothing yet says an attempt exists — `∅` is one, but that is proved
/// later and is not needed to make the symbol legal.
pub fn attempts(env: &mut Env, wt: &Wtype, comp: FnSym) -> Option<(FnSym, Thm)> {
    let s = &wt.sums;
    let (av, bv, uv, tv, ev, gv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tu, tt, te, tg) = (
        Term::var(av),
        Term::var(bv),
        Term::var(uv),
        Term::var(tv),
        Term::var(ev),
        Term::var(gv),
    );

    let bound = attempt_bound(s, wt, &ta, &tb, &tu, &tt);
    let psi = attempt_cond(env, s, comp, &tb, &te, &tg);
    let existence = separation_full(env, gv, &psi, &bound, &s.ap.empty_ax)?;
    let guard = Formula::and(Formula::mem(tg, bound), psi);
    crate::define_by_membership(env, &[av, bv, uv, tv, ev], &existence, gv, &guard)
}

/// The term `Att(A,B,u,T,e)`.
pub fn att_of(att: FnSym, a: Term, b: Term, u: Term, t: Term, e: Term) -> Term {
    Term::apply(att, vec![a, b, u, t, e])
}

/// `⊢ ⟨x,y⟩ ∈ g → indom(g,x)` — the only way the domain condition is ever
/// introduced, and it is introduction only: see the module header.
pub(super) fn indom_intro(env: &mut Env, ap: &Apply, g: &Term, x: &Term, y: &Term) -> Option<Thm> {
    let yv = env.fresh_var();
    let body = Formula::mem(ap.sets.pair(x.clone(), Term::var(yv)), g.clone());
    exists_intro_imp(yv, body, y.clone())
}
