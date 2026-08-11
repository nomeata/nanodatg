//! **Carneiro's `ε`, per rung** — the apparatus `Classical.choice.{u}` needs at
//! `u ≥ 1`, built on its own first use.
//!
//! # Interface
//!
//! ```text
//! Interp::epsilon(u) -> Option<Rc<Epsilon>>          // ε on Uᵤ, minted once
//! ChoiceClause::chooses_at(ip, u, α, α_in_uᵤ, ne) -> Option<(Term, Thm)>
//! ```
//!
//! `chooses_at` hands back `app(εᵤ, ⟦α⟧)` and `⊢ app(εᵤ, ⟦α⟧) ∈ ⟦α⟧`, both
//! **unconditional**, given `⊢ ⟦α⟧ ∈ Uᵤ` and `⊢ ∃w. w ∈ ⟦α⟧`.
//!
//! # Why this is a clause and not a line in `crate::mini::axiom`
//!
//! Two reasons, and the second is the one that decided it.
//!
//! `derived::choice::choice_app` is the pair bridge plus `app_of_pair` plus a
//! dozen combinator steps. An export that never mentions `Classical.choice` —
//! which is nearly all of them — must not pay for it, so it sits behind
//! [`Interp::choice`] exactly as [`crate::mini::acc::AccClause`] and
//! [`crate::mini::nat_clause::NatClause`] sit behind theirs.
//!
//! And `ε` **must be minted once per rung and then threaded**.
//! [`derived::choice::Epsilon::on`] mints a *fresh* constant every call and
//! nothing relates two of them, so a version that built `ε` where it was needed
//! would silently produce a different choice function per use site — every
//! theorem still true, and no two of them about the same function. That is not
//! a soundness bug and it is not detectable downstream, which is precisely why
//! the identity has to live in a store rather than in a convention. `epsilons`
//! is keyed on the rung, and [`Interp::epsilon`] is the only way to reach one.
//!
//! # Why per rung, and not one `ε` for the run
//!
//! `⟦α⟧ ∈ ⟦Sort u⟧ = Uᵤ`, so the choice function has to be defined on `Uᵤ`, and
//! [`derived::choice::Epsilon::on`] requires a **closed** domain — which every
//! `Tower::u(n)` is and `U(x)` at a variable is not. There is no `U_ω` term to
//! mint one global `ε` at; `derived/src/choice/epsilon.rs`'s header says why
//! that is forced rather than provisional, and what building one would take.
//!
//! Two rungs' `ε`s are unrelated symbols. Nothing here needs them related: the
//! bottom at `σ = [u]` uses `εᵤ` and only `εᵤ`, and a declaration at two levels
//! is two pairs with two interpretations anyway.

use std::rc::Rc;

use derived::choice::Epsilon;
use kernel::{Formula, Term, Thm};

use crate::mini::interp::Interp;

/// `derived::choice::choice_app` over this `Interp`'s own pairing, and the
/// `ε`s minted against it.
pub struct ChoiceClause {
    /// `⊢ ∀f ∀u ∀x. (IsChoiceFn(f,u) → ((x ∈ u ∧ ∃w. w ∈ x) → app(f,x) ∈ x))`.
    pub choice_app: Thm,
}

impl ChoiceClause {
    /// Build the lemma, over the prelude's `Apply`.
    ///
    /// **The `Apply` must be the prelude's**, not a fresh one: `app` in the
    /// conclusion has to be the same symbol the interpretation applies with, or
    /// the membership handed to a nest bottom is about a different function
    /// application and nothing composes with it. `Csb::with_apply` and
    /// `ext::app_of_pair` both take the caller's, for the same reason.
    pub fn build(ip: &mut Interp) -> Option<ChoiceClause> {
        let ap = ip.prelude.tower.sums.ap.clone();
        let env = &mut *ip.env_mut();
        let csb = derived::csb::prereq::Csb::with_apply(env, &ap).ok()?;
        let app_pair = derived::ext::app_of_pair(env, &ap)?;
        let choice_app = derived::choice::choice_app(env, &ap, &csb.pair_in_bridge, &app_pair)?;
        // Unconditional, or a nest bottom would carry `Γ` into a `Sealed` that
        // cannot see it. Everything below is `mp` against this, so checking
        // once here is checking every use.
        (choice_app.hyps().is_empty()).then_some(ChoiceClause { choice_app })
    }
}

impl Interp {
    /// The choice apparatus, built on first use and then shared.
    pub fn choice(&mut self) -> Option<Rc<ChoiceClause>> {
        if self.choice.is_none() && !self.choice_failed {
            self.choice = ChoiceClause::build(self).map(Rc::new);
            self.choice_failed = self.choice.is_none();
        }
        self.choice.clone()
    }

    /// `ε` on rung `u` — **minted once per rung**, then handed back.
    ///
    /// Identity and not memoisation, and the distinction is the whole reason
    /// this is a store: a second `Epsilon::on` at the same rung is a second
    /// constant, true of itself and related to the first by nothing.
    pub fn epsilon(&mut self, u: u32) -> Option<Rc<Epsilon>> {
        if let Some(e) = self.epsilons.get(&u) {
            return Some(e.clone())
        }
        if self.epsilons_failed.contains(&u) {
            return None
        }
        let uu = self.sort(u);
        let built = Epsilon::on(&mut self.env_mut(), &uu).map(Rc::new);
        match built {
            Some(e) => {
                self.epsilons.insert(u, e.clone());
                Some(e)
            }
            None => {
                self.epsilons_failed.insert(u);
                None
            }
        }
    }

    /// `(app(εᵤ, α), ⊢ app(εᵤ, α) ∈ α)` from `⊢ α ∈ Uᵤ` and `⊢ ∃w. w ∈ α`.
    ///
    /// The two antecedents are exactly `derived::choice::Epsilon::chooses`'s,
    /// and they are **checked against rebuilt formulas** before being applied:
    /// `a_in_u` must be a membership in this rung's `Uᵤ` and `ne` must be
    /// `kernel::thm::nonempty` at the same `α`, or an antecedent for some other
    /// set would be discharged against this one's implication.
    ///
    /// # The premises may carry `Γ`, and refusing one was a bug
    ///
    /// This opened with `if !a_in_u.hyps().is_empty() || !ne.hyps().is_empty()`
    /// and it declined every real call. Inside a `lam_nest` a binder's typing
    /// **is** a scope assumption — `crate::mini::scope` is mini's one `Thm::assume`
    /// module — so `⟦α⟧ ∈ Uᵤ` arrives as `{⟦α⟧ ∈ Uᵤ} ⊢ ⟦α⟧ ∈ Uᵤ` and everything
    /// derived from it inherits that `Γ`. `crate::mini::kernel`'s `lam_evidence`
    /// discharges it as each binder closes, which is the entire point of the
    /// scope stack; a hypothesis here is the normal case and not a defect.
    ///
    /// So the guard was not a weaker version of the right check, it was the
    /// wrong check — and the right one is somewhere else entirely and already
    /// exists: `crate::mini::ev::Sealed::new` refuses a theorem with hypotheses at the
    /// point it would reach a store, after the nest has closed. What this
    /// function owes is that the two premises are about **this** `α` and
    /// **this** rung, which is checked below and is a statement about their
    /// conclusions.
    ///
    /// The apparatus's own theorems are a different matter and *are* required
    /// closed: `ChoiceClause::build` checks `choice_app`, and `Epsilon`'s two
    /// are sentences by construction. Those are not scope-relative and a `Γ` on
    /// one would never be discharged by anything.
    pub fn chooses_at(&mut self, u: u32, a: &Term, a_in_u: &Thm, ne: &Thm) -> Option<(Term, Thm)> {
        if *a_in_u.concl() != Formula::mem(a.clone(), self.sort(u)) {
            return None
        }
        let want_ne = kernel::thm::nonempty(&mut self.env_mut(), a.clone());
        if *ne.concl() != want_ne {
            return None
        }
        let cl = self.choice()?;
        let eps = self.epsilon(u)?;
        let at = derived::inst_all(&cl.choice_app, &[eps.term().clone(), self.sort(u), a.clone()])?;
        let discharged = Thm::mp(&at, eps.is_choice_fn())?;
        let out = Thm::mp(&discharged, &derived::and_intro(a_in_u, ne))?;
        let tm = self.prelude.tower.sums.ap.apply(eps.term().clone(), a.clone());
        (*out.concl() == Formula::mem(tm.clone(), a.clone())).then_some((tm, out))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The apparatus builds over the prelude, and its lemma is unconditional.
    #[test]
    fn the_apparatus_builds_and_is_unconditional() {
        let mut ip = Interp::new();
        let c = ip.choice().expect("the choice apparatus builds over the prelude");
        assert!(c.choice_app.hyps().is_empty(), "choice_app must be unconditional");
    }

    /// **One `ε` per rung, and it is the same one every time.** A second
    /// `Epsilon::on` would be a second constant with no theorem relating it to
    /// the first; the store is what makes "Carneiro fixes *one*" true here.
    #[test]
    fn epsilon_is_identity_per_rung_and_distinct_across_rungs() {
        let mut ip = Interp::new();
        let a = ip.epsilon(1).expect("ε on U₁");
        let b = ip.epsilon(1).expect("ε on U₁ again");
        assert_eq!(a.sym(), b.sym(), "two lookups at one rung must be one constant");
        let c = ip.epsilon(2).expect("ε on U₂");
        assert_ne!(a.sym(), c.sym(), "different rungs are different choice functions");
        assert_eq!(*a.domain(), ip.sort(1));
        assert_eq!(*c.domain(), ip.sort(2));
    }

    /// `ε` picks a member, at a set the test supplies a non-emptiness proof for
    /// — `U₀`, whose membership in `U₁` and whose inhabitant are both derivable
    /// here. This is the end-to-end shape [`crate::mini::axiom`]'s `u ≥ 1` bottom
    /// uses, without the nest.
    #[test]
    fn chooses_at_produces_a_closed_membership() {
        let mut ip = Interp::new();
        let u0 = ip.prelude.tower.u0();
        let u0_in_u1 = ip.prelude.u0_in_u1.clone();
        assert_eq!(*u0_in_u1.concl(), Formula::mem(u0.clone(), ip.sort(1)), "the premise's shape");

        // `∃w. w ∈ U₀`, from `⊢ 0 ∈ U₀`.
        let false_in_u0 = ip.prelude.tower.false_in_u0.clone();
        let zero = ip.prelude.tower.sums.zero();
        let w = ip.env_mut().fresh_var();
        let intro = derived::exists_intro_imp(w, Formula::mem(Term::var(w), u0.clone()), zero)
            .expect("∃ introduction");
        let ne = Thm::mp(&intro, &false_in_u0).expect("U₀ is inhabited");

        let (tm, thm) = ip.chooses_at(1, &u0, &u0_in_u1, &ne).expect("ε chooses on U₀");
        assert_eq!(*thm.concl(), Formula::mem(tm, u0), "the membership is about the term");
        assert!(thm.hyps().is_empty(), "and it is closed");
    }

    /// **The antecedents are checked, not assumed.** A membership in the wrong
    /// rung, and a non-emptiness proof about the wrong set, are both refused —
    /// otherwise `chooses_at` would discharge one implication with another
    /// set's premise and hand back a theorem about neither.
    #[test]
    fn a_premise_about_another_set_is_refused() {
        let mut ip = Interp::new();
        let u0 = ip.prelude.tower.u0();
        let u0_in_u1 = ip.prelude.u0_in_u1.clone();
        let false_in_u0 = ip.prelude.tower.false_in_u0.clone();
        let zero = ip.prelude.tower.sums.zero();
        let w = ip.env_mut().fresh_var();
        let ne = Thm::mp(
            &derived::exists_intro_imp(w, Formula::mem(Term::var(w), u0.clone()), zero)
                .expect("∃ introduction"),
            &false_in_u0,
        )
        .expect("U₀ is inhabited");

        // The rung is wrong: `⊢ U₀ ∈ U₁` says nothing about `U₂`.
        assert!(ip.chooses_at(2, &u0, &u0_in_u1, &ne).is_none(), "the rung must match");
        // The subject is wrong: the non-emptiness is about `U₀`, not `U₁`.
        let u1 = ip.sort(1);
        assert!(ip.chooses_at(1, &u1, &u0_in_u1, &ne).is_none(), "the set must match");
        // And the positive control, so neither refusal above is the clause
        // failing to work at all.
        assert!(ip.chooses_at(1, &u0, &u0_in_u1, &ne).is_some(), "the right premises derive");
    }
}
