//! The three clauses asked of the relation, as formulas.
//!
//! # Interface
//!
//! For an arbitrary two-variable formula `R(x,b)` with the variables named by
//! `xv` and `bv`:
//!
//! ```text
//! DOM (R,I)  :=  ∀x ∀b. (R(x,b) → x ∈ I)                                [r_dom]
//! SV  (R)    :=  ∀x ∀b ∀c. ((R(x,b) ∧ R(x,c)) → b = c)                   [r_sv]
//! ONTO(R,S)  :=  ∀b. (b ∈ S → ∃x. R(x,b))                              [r_onto]
//! ONTO⊆(R,I) :=  ∀b. (b ⊆ I → ∃x. R(x,b))                     [r_onto_subsets]
//! ```
//!
//! [`surjects_onto_subsets`] is the conjunction `DOM ∧ (SV ∧ ONTO⊆)` in the
//! shape the theorems consume. [`pairs_start_in`], [`single_valued`] and
//! [`onto_subsets`] are the same three clauses at the *set* relation
//! `R(x,b) := ⟨x,b⟩ ∈ k`, which is the instance
//! [`super::no_surjection_onto_subsets`] is stated at.
//!
//! Callers need none of the derivations elsewhere in this module, but they do
//! need these: the theorems are schemes, so a caller has to build the very same
//! formulas to instantiate them, and building them here in one place is what
//! guarantees the caller's copy matches syntactically.
//!
//! # What is deliberately absent
//!
//! **Totality and injectivity.** The diagonal argument does not need them, and
//! leaving them out is what lets a bijection be *restricted* to a subset of its
//! codomain and still qualify — exactly the move
//! [`super::member_not_equinumerous`] makes. Phrasing the target as `b ⊆ I`
//! rather than `b ∈ 𝒫I` also keeps the power-set symbol out of the statements
//! altogether.
//!
//! # How this fails
//!
//! Nothing here builds a theorem, so nothing here can mis-assemble one. The
//! only refusal is the freshness and distinctness condition on the comparison
//! variable `cv` a caller hands [`r_sv`], and it is a
//! [`crate::err::DerErr::Declined`]: the contract working, with the reason
//! naming what was not usable about the variable. [`r_sv`] and
//! [`surjects_onto_subsets`], which does nothing but forward that condition,
//! carry `#[track_caller]`, so the decline is sited at the line of the
//! construction that chose the variable rather than inside this file.

use kernel::{Env, Formula, FreeVar, Term};

use crate::decline_at_caller;
use crate::err::DResult;

/// `∀x ∀b. (R(x,b) → x ∈ i)` — the relation starts in `i`.
pub fn r_dom(r: &Formula, xv: FreeVar, bv: FreeVar, i: &Term) -> Formula {
    Formula::forall(
        xv,
        Formula::forall(bv, Formula::imp(r.clone(), Formula::mem(Term::var(xv), i.clone()))),
    )
}

/// `∀x ∀b ∀c. ((R(x,b) ∧ R(x,c)) → b = c)` — the relation is single-valued.
///
/// `cv` must be fresh for `R` and must differ from `xv` and `bv`; declines
/// otherwise. The choice is invisible in the result, since it is bound.
#[track_caller]
pub fn r_sv(r: &Formula, xv: FreeVar, bv: FreeVar, cv: FreeVar) -> DResult<Formula> {
    if r.occurs_free(cv) || cv == xv || cv == bv {
        return Err(decline_at_caller!(
            "the comparison variable occurs in the relation, or coincides with one of the other two"
        ))
    }
    let (tb, tc) = (Term::var(bv), Term::var(cv));
    let r2 = r.subst(bv, &tc);
    Ok(Formula::forall(
        xv,
        Formula::forall(
            bv,
            Formula::forall(cv, Formula::imp(Formula::and(r.clone(), r2), Formula::eq(tb, tc))),
        ),
    ))
}

/// `∀b. (b ⊆ i → ∃x. R(x,b))` — every subset of `i` is a value of the relation.
pub fn r_onto_subsets(env: &mut Env, r: &Formula, xv: FreeVar, bv: FreeVar, i: &Term) -> Formula {
    let sub = kernel::thm::subset(env, Term::var(bv), i.clone());
    Formula::forall(bv, Formula::imp(sub, Formula::exists(xv, r.clone())))
}

/// `∀b. (b ∈ s → ∃x. R(x,b))` — every member of `s` is a value of the relation.
///
/// The variant [`super::image_in_universe`] wants, where the target is a set rather
/// than "the subsets of `i`".
pub fn r_onto(r: &Formula, xv: FreeVar, bv: FreeVar, s: &Term) -> Formula {
    Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(Term::var(bv), s.clone()),
            Formula::exists(xv, r.clone()),
        ),
    )
}

/// `DOM ∧ (SV ∧ ONTO)` at the subsets of `i` — the package
/// [`super::no_diagonal_surjection`] refutes.
///
/// `cv` must be fresh for `R`, for [`r_sv`]; declines otherwise.
#[track_caller]
pub fn surjects_onto_subsets(
    env: &mut Env,
    r: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    cv: FreeVar,
    i: &Term,
) -> DResult<Formula> {
    let dom = r_dom(r, xv, bv, i);
    let sv = r_sv(r, xv, bv, cv)?;
    let onto = r_onto_subsets(env, r, xv, bv, i);
    Ok(Formula::and(dom, Formula::and(sv, onto)))
}

/// `∀x ∀b. (⟨x,b⟩ ∈ k → x ∈ i)`, at the relation-as-a-set `k`.
pub fn pairs_start_in(env: &mut Env, k: &Term, i: &Term) -> Formula {
    let (x, b) = (env.fresh_var(), env.fresh_var());
    let p = kernel::thm::pair_in(env, k.clone(), Term::var(x), Term::var(b));
    r_dom(&p, x, b, i)
}

/// `∀x ∀b ∀c. ((⟨x,b⟩ ∈ k ∧ ⟨x,c⟩ ∈ k) → b = c)`, at the relation-as-a-set `k`.
///
/// Rebuilt rather than imported from `crate::funspace::is_single_valued`,
/// because that one is stated with an `Apply` apparatus in scope; this is the
/// bare formula, and it is the clause `kernel::thm::equinumerous` carries.
pub fn single_valued(env: &mut Env, k: &Term) -> Formula {
    let (x, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let p = kernel::thm::pair_in(env, k.clone(), Term::var(x), Term::var(b));
    r_sv(&p, x, b, c).expect("c is fresh for a freshly built pair_in")
}

/// `∀b. (b ⊆ i → ∃x. ⟨x,b⟩ ∈ k)`, at the relation-as-a-set `k`.
pub fn onto_subsets(env: &mut Env, k: &Term, i: &Term) -> Formula {
    let (x, b) = (env.fresh_var(), env.fresh_var());
    let p = kernel::thm::pair_in(env, k.clone(), Term::var(x), Term::var(b));
    r_onto_subsets(env, &p, x, b, i)
}
