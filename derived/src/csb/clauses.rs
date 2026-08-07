//! The four clauses of an injection, as formulas, and the two derived
//! conditions the fixed point is built from.
//!
//! # Interface
//!
//! For an arbitrary two-variable formula `F(x,b)` whose distinguished variables
//! are named by `xv` and `bv` — read "`F` sends `x` to `b`" — and set terms `a`
//! (the domain) and `b` (the codomain):
//!
//! ```text
//! DOM(F,a,b) :=  ∀x ∀b. (F(x,b) → (x ∈ a ∧ b ∈ b))               [inj_dom]
//! TOT(F,a)   :=  ∀x. (x ∈ a → ∃b. F(x,b))                      [inj_total]
//! SV (F)     :=  ∀x ∀b ∀c. ((F(x,b) ∧ F(x,c)) → b = c)            [inj_sv]
//! INJ(F)     :=  ∀x ∀y ∀b. ((F(x,b) ∧ F(y,b)) → x = y)          [inj_inj]
//!
//! injection_clauses(F,a,b) := [DOM, TOT, SV, INJ]       [injection_clauses]
//! ```
//!
//! and, at the *set* relation `F(x,b) := ⟨x,b⟩ ∈ f`,
//!
//! ```text
//! INJECTION(f,a,b) := DOM ∧ (TOT ∧ (SV ∧ INJ))                 [injection]
//! ```
//!
//! which is exactly `kernel::thm::equinumerous`'s body with the **onto** clause
//! deleted — same five-clause spelling, same nesting, same described pairs. A
//! caller who has a bijection therefore has an injection by projection, and a
//! caller who has an injection needs no translation layer to state it.
//!
//! The two derived conditions, for a set term `s` standing for a candidate
//! subset of `a`:
//!
//! ```text
//! IMG(F,s,b)     :=  ∃w. (w ∈ s ∧ F(w,b))            — `b ∈ F[s]`   [in_image]
//! STOP(F,G,s,d)  :=  ¬∃b. ((b ∈ b_ ∧ ¬IMG(F,s,b)) ∧ G(b,d))         [stopper]
//! STEP(F,G,s,d)  :=  d ∈ a ∧ STOP(F,G,s,d)          — `d ∈ Φ(s)`      [step]
//! PRE(F,G,s)     :=  ∀d. (STEP(F,G,s,d) → d ∈ s)                [pre_fixed]
//! ```
//!
//! `STEP` is the Knaster–Tarski operator `Φ(s) = a ∖ G[b ∖ F[s]]` written as a
//! condition on `d` rather than as a set: nothing here needs `Φ(s)` to *be* a
//! set, and not building it is what keeps the whole construction inside
//! Separation. `PRE(s)` says `Φ(s) ⊆ s`.
//!
//! # Why `G`'s clauses are these same four builders
//!
//! `G` runs the other way — `G(b,d)` reads "`G` sends `b ∈ b_` to `d ∈ a`" — so
//! its four clauses are [`inj_dom`], [`inj_total`], [`inj_sv`] and [`inj_inj`]
//! called with the two distinguished variables and the two sets **swapped**.
//! Notably that makes `G`'s *single-valuedness* the clause that pins the
//! pre-image `d` of a `b`, and `G`'s *injectivity* the clause that pins the `b`
//! belonging to a `d` — which is why the finished bijection's single-valuedness
//! comes from `INJ(G)` and its injectivity from `SV(G)`, crosswise. See
//! [`super::bijection`].
//!
//! Callers need these builders: the theorems are schemes, so the caller has to
//! build the very same formulas to instantiate them, and building them here in
//! one place is what makes the caller's copy match syntactically.
//!
//! # How this fails
//!
//! Nothing here builds a theorem, so nothing here can mis-assemble one. The
//! only refusals are the freshness and distinctness conditions on the variables
//! a caller hands in — `cv` for [`inj_sv`], `yv` for [`inj_inj`], `wv` for
//! [`in_image`] — and each is a [`crate::err::DerErr::Declined`]: the contract
//! working, with the reason naming the variable that was not usable. Those
//! three, and the four builders that do nothing but forward their conditions
//! ([`stopper`], [`step`], [`pre_fixed`], [`fixed`], [`injection_clauses`]),
//! carry `#[track_caller]`, so a decline is sited at the line of the
//! construction that chose the variables rather than inside this file.

use kernel::{Env, Formula, FreeVar, Term};

use crate::decline_at_caller;
use crate::err::DResult;
use crate::rules::conj_of;

/// `∀x ∀b. (F(x,b) → (x ∈ a ∧ b ∈ codom))` — `F` runs from `a` to `codom`.
pub fn inj_dom(f: &Formula, xv: FreeVar, bv: FreeVar, a: &Term, codom: &Term) -> Formula {
    let concl = Formula::and(
        Formula::mem(Term::var(xv), a.clone()),
        Formula::mem(Term::var(bv), codom.clone()),
    );
    Formula::forall(xv, Formula::forall(bv, Formula::imp(f.clone(), concl)))
}

/// `∀x. (x ∈ a → ∃b. F(x,b))` — `F` is total on `a`.
pub fn inj_total(f: &Formula, xv: FreeVar, bv: FreeVar, a: &Term) -> Formula {
    Formula::forall(
        xv,
        Formula::imp(Formula::mem(Term::var(xv), a.clone()), Formula::exists(bv, f.clone())),
    )
}

/// `∀x ∀b ∀c. ((F(x,b) ∧ F(x,c)) → b = c)` — `F` is single-valued.
///
/// `cv` must be fresh for `F` and the three variables must be pairwise
/// distinct; declines otherwise. The choice of `cv` is invisible in the result,
/// since it is bound.
#[track_caller]
pub fn inj_sv(f: &Formula, xv: FreeVar, bv: FreeVar, cv: FreeVar) -> DResult<Formula> {
    if f.occurs_free(cv) || cv == xv || cv == bv || xv == bv {
        return Err(decline_at_caller!(
            "the comparison variable occurs in the relation, or two of the three variables coincide"
        ))
    }
    let (tb, tc) = (Term::var(bv), Term::var(cv));
    let shifted = f.subst(bv, &tc);
    Ok(Formula::forall(
        xv,
        Formula::forall(
            bv,
            Formula::forall(cv, Formula::imp(Formula::and(f.clone(), shifted), Formula::eq(tb, tc))),
        ),
    ))
}

/// `∀x ∀y ∀b. ((F(x,b) ∧ F(y,b)) → x = y)` — `F` is injective.
///
/// `yv` must be fresh for `F` and the three variables must be pairwise
/// distinct; declines otherwise. The choice of `yv` is invisible in the result,
/// since it is bound.
#[track_caller]
pub fn inj_inj(f: &Formula, xv: FreeVar, bv: FreeVar, yv: FreeVar) -> DResult<Formula> {
    if f.occurs_free(yv) || yv == xv || yv == bv || xv == bv {
        return Err(decline_at_caller!(
            "the second argument variable occurs in the relation, or two of the three variables coincide"
        ))
    }
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let shifted = f.subst(xv, &ty);
    Ok(Formula::forall(
        xv,
        Formula::forall(
            yv,
            Formula::forall(bv, Formula::imp(Formula::and(f.clone(), shifted), Formula::eq(tx, ty))),
        ),
    ))
}

/// `[DOM, TOT, SV, INJ]` — the four clauses in the order the theorem's
/// hypothesis lists them.
///
/// `cv` and `yv` must be fresh for `F`, for [`inj_sv`] and [`inj_inj`]
/// respectively.
#[track_caller]
pub fn injection_clauses(
    f: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    cv: FreeVar,
    yv: FreeVar,
    a: &Term,
    codom: &Term,
) -> DResult<[Formula; 4]> {
    Ok([
        inj_dom(f, xv, bv, a, codom),
        inj_total(f, xv, bv, a),
        inj_sv(f, xv, bv, cv)?,
        inj_inj(f, xv, bv, yv)?,
    ])
}

/// `INJECTION(f,a,b)` — the four clauses at the set relation `⟨x,b⟩ ∈ f`,
/// conjoined right-nested.
///
/// This is `kernel::thm::equinumerous`'s body with the onto clause deleted, so
/// it composes with a bijection without translation.
pub fn injection(env: &mut Env, f: &Term, a: &Term, codom: &Term) -> DResult<Formula> {
    let (xv, bv, cv, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let rel = kernel::thm::pair_in(env, f.clone(), Term::var(xv), Term::var(bv));
    let cl = injection_clauses(&rel, xv, bv, cv, yv, a, codom)?;
    conj_of(&cl)
}

/// `∃w. (w ∈ s ∧ F(w,b))` — `b` is in the image `F[s]`.
///
/// `wv` must be fresh for `F`, must not occur in `s`, and must differ from
/// `xv`; declines otherwise.
#[track_caller]
pub fn in_image(f: &Formula, xv: FreeVar, wv: FreeVar, s: &Term) -> DResult<Formula> {
    if f.occurs_free(wv) || s.occurs_free(wv) || wv == xv {
        return Err(decline_at_caller!(
            "the image witness variable occurs in the relation or in the subset term, or is the argument variable"
        ))
    }
    let tw = Term::var(wv);
    Ok(Formula::exists(wv, Formula::and(Formula::mem(tw.clone(), s.clone()), f.subst(xv, &tw))))
}

/// `¬∃b. ((b ∈ codom ∧ ¬IMG(F,s,b)) ∧ G(b,d))` — nothing outside `F[s]` is sent
/// to `d` by `G`.
///
/// The negative half of the Knaster–Tarski operator. `bv` is `G`'s *argument*
/// variable and `dv` its *value* variable; `wv` is [`in_image`]'s witness.
#[allow(clippy::too_many_arguments)]
#[track_caller]
pub fn stopper(
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    dv: FreeVar,
    wv: FreeVar,
    s: &Term,
    codom: &Term,
) -> DResult<Formula> {
    let img = in_image(f, xv, wv, s)?;
    let left = Formula::and(Formula::mem(Term::var(bv), codom.clone()), Formula::not(img));
    let g_at_d = g.subst(xv, &Term::var(dv));
    Ok(Formula::not(Formula::exists(bv, Formula::and(left, g_at_d))))
}

/// `d ∈ a ∧ STOP(F,G,s,d)` — the Knaster–Tarski operator `Φ(s) = a ∖ G[b ∖ F[s]]`,
/// as a condition on `d`.
#[allow(clippy::too_many_arguments)]
#[track_caller]
pub fn step(
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    dv: FreeVar,
    wv: FreeVar,
    s: &Term,
    a: &Term,
    codom: &Term,
) -> DResult<Formula> {
    let stop = stopper(f, g, xv, bv, dv, wv, s, codom)?;
    Ok(Formula::and(Formula::mem(Term::var(dv), a.clone()), stop))
}

/// `∀d. (STEP(F,G,s,d) → d ∈ s)` — `s` is a pre-fixed point of `Φ`.
#[allow(clippy::too_many_arguments)]
#[track_caller]
pub fn pre_fixed(
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    dv: FreeVar,
    wv: FreeVar,
    s: &Term,
    a: &Term,
    codom: &Term,
) -> DResult<Formula> {
    let st = step(f, g, xv, bv, dv, wv, s, a, codom)?;
    Ok(Formula::forall(dv, Formula::imp(st, Formula::mem(Term::var(dv), s.clone()))))
}

/// `∀d. (d ∈ c ↔ STEP(F,G,c,d))` — `c` is a **fixed** point of `Φ`.
///
/// The conclusion of [`super::fixpoint::csb_fixpoint`] and the hypothesis
/// [`super::bijection`] consumes.
#[allow(clippy::too_many_arguments)]
#[track_caller]
pub fn fixed(
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    dv: FreeVar,
    wv: FreeVar,
    c: &Term,
    a: &Term,
    codom: &Term,
) -> DResult<Formula> {
    let st = step(f, g, xv, bv, dv, wv, c, a, codom)?;
    Ok(Formula::forall(dv, Formula::iff(Formula::mem(Term::var(dv), c.clone()), st)))
}
