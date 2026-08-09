//! **`derived::rec_acc`'s apparatus, over the `Acc` clause's own `acc`** — the
//! accessor `Acc.rec` at `u₁ ≥ 1` stands on.
//!
//! # Interface
//!
//! ```text
//! Interp::rec_acc() -> Option<Rc<RecAccApparatus>>
//! ```
//!
//! Built on **its own** first use and then shared, exactly as
//! [`Interp::acc`](crate::interp::Interp::acc) and
//! [`Interp::quotient`](crate::interp::Interp::quotient) are: it derives the
//! whole of [`derived::rec_acc`] — the attempts, the union, totality, the ι rule
//! and the packaging — and no export that never reaches `Acc.rec` at a value
//! motive should pay for any of it.
//!
//! Everything it carries is stated over `A`, `R`, `T` and `e` as *bound
//! variables*, so one build serves every `σ`; what makes it this checker's is
//! the `acc` and the pairing it is built over, which is the whole of the next
//! section.
//!
//! # The trap: `RecAcc::new` mints a second `acc`, and `Base::over` cannot see it
//!
//! [`derived::rec_acc::RecAcc::new`] is
//!
//! ```text
//! let s = Sums::new(env)?;
//! let ac = Acc::with_apply(env, &s.ap)?;      // ← a *fresh* carrier
//! let base = Base::over(env, s, ac)?;
//! RecAcc::over(env, base)
//! ```
//!
//! and `Acc::with_apply` mints its symbols through `define_abbrev`, so calling
//! it a second time yields **two unrelated `acc` carriers with no equation
//! between them**. `Acc.rec`'s major premise `t : Acc α r a` delivers
//! `⟦a⟧ ∈ acc(A,R̄)` at [`AccClause::sets`](crate::acc::AccClause::sets)'s one,
//! and the `u₁ = 0` clause reasons about that same set; an apparatus built
//! through `RecAcc::new` would compile, derive, and be about **somebody else's
//! set**.
//!
//! [`derived::rec_acc::Base::over`] checks `ac.sets.up == s.ap.sets.up` — it
//! refuses a mismatched *pairing*, so a wrong [`Sums`] is caught — but it cannot
//! see that a same-shaped `Acc` is a different `acc`. **That near miss is why
//! the trap is worth a paragraph**: the guard is exactly close enough to be
//! mistaken for one against this. So the build below threads the clause's own
//! `Acc` and the prelude's own `Sums`, and
//! [`tests::the_apparatus_is_over_the_clause_s_own_acc`] pins it, because prose
//! does not recompile.
//!
//! # What it carries beyond `RecAcc`, and why each is here
//!
//! Three theorems whose inputs are exactly this apparatus's symbols, so that no
//! consumer has to re-derive one and risk minting a second certificate:
//!
//! | field | statement | spent by |
//! |---|---|---|
//! | [`RecAccApparatus::bounded`] | `ST → app(accrec,y) ∈ T`, and `ih(accrec,…) ∈ ih_bound` | the ι rule's own instantiation |
//! | [`RecAccApparatus::pred_closed`] | **A4** — a predecessor of an accessible point is accessible | the `h` binder of Lean's minor |
//! | [`RecAccApparatus::edge_value`] | `ep(rel_graph(A,r),y,x) = app(app(r,y),x)` | the induction hypothesis's rows |
//! | [`RecAccApparatus::app_off_domain`] | `(¬∃y. ⟨a,y⟩ ∈ f) → app(f,a) = ∅` | the junk branch of `step_typed` |
//!
//! [`derived::acc::acc_pred_closed`] and [`derived::rec_acc::Bounded::build`]
//! each mint one fresh symbol — the subset `acc_rect` runs their induction at —
//! and `Bounded` calls A4 again internally. That is two symbols and one
//! duplicated derivation of a theorem whose *conclusion* mentions neither, so
//! nothing downstream can tell them apart and no equation is owed between them;
//! it is noted rather than avoided, because avoiding it means changing
//! `derived/`.

use std::rc::Rc;

use kernel::Thm;

use derived::acc::acc_pred_closed;
use derived::quot::RelGraph;
use derived::rec_acc::{edge_is_relation_value, Base, Bounded, RecAcc};

use crate::interp::Interp;

/// [`derived::rec_acc`], over this `Interp`'s `acc`, pairing and unit.
pub struct RecAccApparatus {
    /// Every symbol and theorem of the accessibility recursor: `Att`, `accrec`,
    /// `pack`, totality, `rec_funspace` and both spellings of ι.
    pub ra: RecAcc,
    /// `ST → app(accrec,y) ∈ T` and `ST → ih(accrec,A,R,x) ∈ ih_bound(A,T)`.
    pub bounded: Bounded,
    /// **A4** — `⊢ ∀A ∀R ∀y ∀z. (z ∈ acc(A,R) → ((y ∈ A ∧ ⟨y,z⟩ ∈ R) → y ∈ acc(A,R)))`.
    pub pred_closed: Thm,
    /// `⊢ ∀A ∀r ∀y ∀x. ((y ∈ A ∧ (x ∈ A ∧ app(app(r,y),x) ∈ ⟦Prop⟧))
    /// → ep(rel_graph(A,r), y, x) = app(app(r,y),x))`.
    ///
    /// The antecedent is
    /// [`AccClause::pair_in_graph`](crate::acc::AccClause::pair_in_graph)'s own,
    /// one atom longer and in its order, so a consumer assembles the conjunction
    /// once and spends it on both.
    pub edge_value: Thm,
    /// `⊢ ∀f ∀a. ((¬∃y. ⟨a,y⟩ ∈ f) → app(f,a) = ∅)` — application off the
    /// domain, [`derived::funcs::app_off_domain`].
    ///
    /// Not a `rec_acc` theorem, and carried here anyway: it is what makes
    /// `step_typed`'s junk branch dischargeable at all (`MINI-HANDOFF.md` §23
    /// item 2), it is derived rather than looked up, and this is the one place
    /// that wants it.
    pub app_off_domain: Thm,
}

impl RecAccApparatus {
    /// The hypothesis half of the house rule, for everything this struct
    /// carries. [`RecAcc::all_unconditional`] covers its own fields and its
    /// [`Base`]; the three theorems beside it are checked here.
    pub fn all_unconditional(&self) -> bool {
        self.ra.all_unconditional()
            && self.bounded.all_unconditional()
            && derived::all_unconditional(&[
                &self.pred_closed,
                &self.edge_value,
                &self.app_off_domain,
            ])
    }
}

impl Interp {
    /// The accessibility recursor's apparatus, over **this** `Interp`'s `Acc`
    /// clause, built on first use and then shared.
    ///
    /// Identity, not memoisation, for the same reason
    /// [`Interp::acc`](crate::interp::Interp::acc) is: `⟦Acc.rec.{1,u}⟧` at two
    /// `σ` must name one `accrec` and one `pack`, or their definitional equality
    /// would need a theorem where reflexivity should do — and, one layer up,
    /// they must name the `acc` the major premise's own typing is about. See the
    /// module header.
    pub fn rec_acc(&mut self) -> Option<Rc<RecAccApparatus>> {
        if self.rec_acc.is_none() && !self.rec_acc_failed {
            self.rec_acc = self.build_rec_acc().map(Rc::new);
            self.rec_acc_failed = self.rec_acc.is_none();
        }
        self.rec_acc.clone()
    }

    /// One build. Split out so that the memo above is three lines and the
    /// threading is readable in one screen.
    fn build_rec_acc(&mut self) -> Option<RecAccApparatus> {
        let ac = self.acc()?;
        let sums = self.prelude.tower.sums.clone();
        // **The clause's `Acc`, not a fresh one.** See the module header; this
        // one line is the whole of the trap.
        let base = Base::over(&mut self.env_mut(), sums.clone(), ac.sets.clone())?;
        let ra = RecAcc::over(&mut self.env_mut(), base)?;
        let bounded = Bounded::build(&mut self.env_mut(), &ra)?;
        let pred_closed = acc_pred_closed(&mut self.env_mut(), &ac.sets)?;
        let g = RelGraph { s: &sums, graph: ac.graph, graph_ax: &ac.graph_ax };
        let edge_value = edge_is_relation_value(
            &mut self.env_mut(),
            &g,
            ra.base.ep,
            &ra.base.ep_ax,
            &ac.graph_pair,
            &ac.pair_in_graph,
        )?;
        let app_off_domain = derived::funcs::app_off_domain(&mut self.env_mut(), &sums.ap)?;
        let out = RecAccApparatus { ra, bounded, pred_closed, edge_value, app_off_domain };
        out.all_unconditional().then_some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **The apparatus is over the clause's own `acc`** — the trap in the module
    /// header, asserted.
    ///
    /// `RecAcc::new` would produce a struct that passes every other check in
    /// this file: same shapes, same arities, unconditional throughout, and
    /// `Base::over`'s pairing guard satisfied. What it would not be is about the
    /// set `Acc.rec`'s major premise delivers a membership in. Two symbols and
    /// one pairing are what say so.
    #[test]
    fn the_apparatus_is_over_the_clause_s_own_acc() {
        let mut ip = Interp::new();
        let clause = ip.acc().expect("the Acc clause's apparatus builds");
        let ra = ip.rec_acc().expect("the recursor's apparatus builds over it");
        assert_eq!(
            ra.ra.base.ac.acc, clause.sets.acc,
            "the recursor must recurse along the acc the major premise is about"
        );
        assert_eq!(
            ra.ra.base.s.ap.sets.up, ip.prelude.tower.sums.ap.sets.up,
            "…over the interpretation's own pairing"
        );
        assert_eq!(
            ra.ra.base.ac.empty, ip.prelude.tower.sums.ap.empty,
            "…and its own ∅"
        );
    }

    /// One `accrec`, not one per call — the identity property every other lazy
    /// apparatus on `Interp` has, and for the same reason.
    #[test]
    fn the_apparatus_is_identity_not_a_cache() {
        let mut ip = Interp::new();
        let first = ip.rec_acc().expect("builds");
        let second = ip.rec_acc().expect("builds");
        assert_eq!(first.ra.rec, second.ra.rec, "two uses of Acc.rec must name one accrec");
        assert_eq!(first.ra.att, second.ra.att, "…and one Att");
        assert_eq!(first.ra.base.ih, second.ra.base.ih, "…and one ih");
    }

    /// Everything it carries is **unconditional**, its `Base` and its `Acc`
    /// included: a `Γ`-carrying theorem would ride into a nest bottom the
    /// consumers document as closed.
    #[test]
    fn everything_it_carries_is_unconditional() {
        let mut ip = Interp::new();
        let ra = ip.rec_acc().expect("builds");
        assert!(ra.all_unconditional(), "the whole apparatus is ⊢, not Γ ⊢");
        assert!(ra.ra.pack_iota.hyps().is_empty(), "ι at the thesis's spelling");
        assert!(ra.edge_value.hyps().is_empty(), "the edge equation");
        assert!(ra.pred_closed.hyps().is_empty(), "A4");
        assert!(ra.app_off_domain.hyps().is_empty(), "application off the domain");
    }
}
