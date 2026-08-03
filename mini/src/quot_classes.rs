//! **`Quot`'s interpretation clause at `u ≥ 1`** — the equivalence-class
//! reading (`QUOT-MODEL.md` §5's second clause).
//!
//! # Interface
//!
//! ```text
//! quot_classes::QuotClause::build(env, prelude) -> Option<QuotClause>
//! qc.carrier(ip, a, r)                          -> Term      ⟦Quot α r⟧
//! qc.formation(ip, u, a, r, a_mem)              -> Option<Thm>
//! quot_classes::mk_at(qc, ip, former, …)        -> Option<(Term, Thm)>
//! Interp::quotient()                            -> Option<Rc<QuotClause>>
//! ```
//!
//! The clauses are dispatched from [`crate::quot::build`], which owns the
//! `u = 0` / `u ≥ 1` split. What lives here is the **apparatus** — the symbols
//! and theorems the bottoms consume — and the two clauses built so far.
//!
//! # The clauses
//!
//! ```text
//! ⟦Quot α r⟧      = quot(⟦α⟧, rel_graph(⟦α⟧, ⟦r⟧))
//! ⟦Quot.mk α r a⟧ = class(⟦α⟧, rel_graph(⟦α⟧, ⟦r⟧), ⟦a⟧)
//! ```
//!
//! — Carneiro §6.2, `⟦α/R⟧ = ⟦α⟧/∼`, with the same correction the thesis's
//! notation hides that [`crate::acc`] records one construction along:
//! **`quot` takes a set of pairs and `⟦r⟧` is curried.** Every theorem in
//! [`derived::quot`] reads `⟨x,y⟩ ∈ R`, while Lean's `r : α → α → Prop`
//! interprets as `⟦r⟧ ∈ fs(A, fs(A, U₀))`.
//! [`derived::quot::rel_graph_symbol`] is the bridge, and this is its **second**
//! consumer.
//!
//! **No symbol of mini's own.** `Acc`'s clause needed one because its
//! denotation is a `Prop` and had to be a conditional singleton over a formula;
//! here the denotation is a genuine set and `quot`/`rel_graph` are already
//! arity-2 symbols of `derived`'s. The composite is built through
//! [`Interp::mk`] at both nodes, which is what makes it decomposable again — an
//! unrecorded node is the defect [`Interp::rebuild`]'s doc is about.
//!
//! # Why the apparatus is lazy, and why there are two `rel_graph`s
//!
//! [`derived::quot::Quotient::over`] derives the equivalence closure, the
//! classes, `lift`'s graph, `ker` and the four non-vacuity witnesses from the
//! axioms up. An export that mentions no quotient must not pay for it, so it is
//! built on **its own** first use and cached on the `Interp` — the same
//! lazy-with-a-failure-flag shape [`Interp::direct`], [`Interp::acc`] and
//! `ind_apparatus` all have, and for the same identity reason: `⟦Quot.{1}⟧` and
//! `⟦Quot.{2}⟧` must name one `quot`, or their definitional equality would need
//! a theorem where reflexivity should do.
//!
//! `Quotient::over` mints its **own** `rel_graph`, and [`crate::acc`] has
//! already minted one. That is a re-minted symbol, which this project's standing
//! rule (`MINI-HANDOFF.md` §2) calls a defect *whenever two routes have to agree
//! about it* — and these two do not. `⟦Acc α r x⟧` is a conditional singleton
//! over `acc(A, rel_graph_acc(A,r))` and `⟦Quot α r⟧` is
//! `quot(A, rel_graph_quot(A,r))`; they are different sets, no theorem crosses
//! between them, and nothing anywhere compares an accessibility carrier with a
//! quotient. What the two **must** share is the pairing — `⟨x,y⟩` has to be one
//! term or the two graphs' members would be unrelated statements — and they do,
//! because both are built over `prelude.tower.sums`. That is asserted rather
//! than argued: `the_two_graphs_share_one_pairing`.
//!
//! The alternative — one `rel_graph` lifted onto the `Interp` and handed to
//! both — is the right move if a third consumer ever appears. It is not worth
//! it for two that never compare notes, and it would cost an `Acc`-only export
//! the whole `Quotient`, which is exactly what the laziness is for.
//!
//! # What is here and what is not
//!
//! **Formation** and **`mk`**. `Quot.lift` and `Quot.ind` at `u ≥ 1` decline,
//! each by its own name, and `Quot.sound`'s inhabitation is
//! `MINI-HANDOFF.md` §14's point 3 and lives in [`crate::axiom`] — where at
//! `u ≥ 1` it is **not** reflexivity, because `⟦mk a⟧` and `⟦mk b⟧` are two
//! different classes rather than two `•`s, and the rule it wants is
//! [`derived::quot::q_sound`]. The apparatus carries what the three owe —
//! `q_sound`, `lift_beta`, `lift_in_funspace`, `compat_closure`,
//! `pair_in_graph` — because they must all speak of **one** `quot`, and minting
//! at each site would give three.
//!
//! **`pair_in_graph` is the bridge with no consumer yet**, and this module is
//! where it acquires one: `q_sound` wants `⟨ā,b̄⟩ ∈ R̄` while Lean's `h` arrives
//! as `• ∈ app(app(r̄,ā),b̄)`, which is *owing* the pair rather than holding it.
//! That is the prediction `mini/src/acc.rs`'s field doc makes, and `Quot.sound`
//! at `u ≥ 1` is where it gets tested.

use std::rc::Rc;

use kernel::{Env, Formula, Term, Thm};

use derived::prelude::Prelude;
use derived::quot::{quot_in_universe, Quotient};

use crate::interp::Interp;

/// The `Quot` clause's symbols and the theorems its bottoms consume.
///
/// Built over **the prelude's own** [`derived::sums::Sums`], so that the
/// `⟨x,y⟩` this module's `rel_graph` speaks of is the ordered pair every other
/// construction uses and its `𝒫` is the one the tower's rungs are closed under.
pub struct QuotClause {
    /// Every symbol and theorem of [`derived::quot`], over one definitional
    /// extension.
    pub q: Quotient,
    /// `⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))` — **formation**, at every
    /// rung `c ≥ 1`.
    ///
    /// Built here rather than carried by [`Quotient`] because it needs the
    /// tower's two `∀c` closure statements, which are not quotient apparatus.
    pub in_universe: Thm,
}

impl QuotClause {
    /// Introduce the quotient apparatus and derive the formation theorem.
    ///
    /// Returns `None` rather than half a clause if either declines —
    /// `Quotient::over` refuses a conditional [`derived::sums::Sums`], and
    /// `quot_in_universe` refuses a `pow`/`sub` pair that is not this tower's.
    pub fn build(env: &mut Env, prelude: &Prelude) -> Option<QuotClause> {
        let q = Quotient::over(env, prelude.tower.sums.clone())?;
        let in_universe = quot_in_universe(
            env,
            &q.sums,
            q.class,
            q.quot,
            &q.quot_ax,
            prelude.u_sym,
            &prelude.tower.pow,
            &prelude.tower.sub,
        )?;
        Some(QuotClause { q, in_universe })
    }

    /// `rel_graph(A, r)` — Lean's curried `r` as the set of pairs `quot` wants.
    pub fn graph(&self, ip: &mut Interp, a: &Term, r: &Term) -> Term {
        ip.mk(self.q.rel_graph, vec![a.clone(), r.clone()])
    }

    /// `⟦Quot α r⟧ = quot(A, rel_graph(A,r))`, recorded at both nodes.
    pub fn carrier(&self, ip: &mut Interp, a: &Term, r: &Term) -> Term {
        let g = self.graph(ip, a, r);
        ip.mk(self.q.quot, vec![a.clone(), g])
    }

    /// **`Γ ⊢ ⟦Quot α r⟧ ∈ ⟦Sort u⟧`** at `u ≥ 1`, from `Γ ⊢ ⟦α⟧ ∈ ⟦Sort u⟧`.
    ///
    /// One instantiation of [`QuotClause::in_universe`] and one modus ponens.
    /// The rung is what makes `u ≥ 1` load-bearing rather than decorative:
    /// `⟦Sort u⟧` is `U(seed)` for a *seed term the tower names*, and
    /// `in_universe` is stated at `U(c)` for a variable `c` — so the two meet
    /// exactly when there is a rung, which is `u ≥ 1`. At `u = 0` there is no
    /// rung (`Tower::at(0) = None`) and the statement is not merely unavailable
    /// but false: `quot(1,R) = {1} ∉ U₀`, `QUOT-MODEL.md` §1.2's countermodel.
    ///
    /// The conclusion is compared against the term [`QuotClause::carrier`]
    /// builds, so a caller cannot get a membership about a different set.
    pub fn formation(
        &self,
        ip: &mut Interp,
        u: u32,
        a: &Term,
        r: &Term,
        a_mem: &Thm,
    ) -> Option<Thm> {
        let rung = ip.prelude.tower.at(u as usize)?;
        let carrier = self.carrier(ip, a, r);
        let g = self.graph(ip, a, r);
        if *a_mem.concl() != Formula::mem(a.clone(), rung.set.clone()) {
            return None
        }
        let at = derived::inst_all(&self.in_universe, &[a.clone(), g, rung.seed.clone()])?;
        let out = Thm::mp(&at, a_mem)?;
        (*out.concl() == Formula::mem(carrier, rung.set)).then_some(out)
    }
}

/// **`Γ ⊢ class(A,R̄,ā) ∈ ⟦Quot α r⟧`** — `Quot.mk`'s typing at `u ≥ 1`.
///
/// # The clause
///
/// ```text
/// ⟦Quot.mk α r a⟧ = class(⟦α⟧, rel_graph(⟦α⟧,⟦r⟧), ⟦a⟧)
/// ```
///
/// — Carneiro §6.2's `⟦mk_R x⟧ = [⟦x⟧]∼`. The rule is
/// [`derived::quot::Quotient::mk_mem`], `⊢ ∀A ∀R ∀x. (x ∈ A → class(A,R,x) ∈
/// quot(A,R))`, and its one premise is the `a` binder's own scope typing.
///
/// # The one step that is not the rule
///
/// The declared codomain is `Quot α r`, and §6.2's application clause makes
/// that `app(app(⟦Quot.{u}⟧,A),r̄)` — a **redex over the formation clause's own
/// stored nest**, related to `quot(A,R̄)` by β and not by syntax. So `mk_mem`
/// lands in `quot(A,R̄)` and the codomain is one [`Interp::beta_spine`] away, in
/// the *opposite* direction from the usual: the membership is carried **onto**
/// the spine rather than off it, so the equation is reversed before it is used.
///
/// That is `SCOPING.md` §1's sixth category, and it is the same β step
/// [`crate::quot`]'s `Prim::Mk` needs at `u = 0` for the same reason — where
/// `⟦Quot α r⟧` is a redex onto `⟦α⟧` instead of onto `quot(A,R̄)`. The two
/// clauses disagree about everything except this.
///
/// `None` is a decline: the conclusion is compared against the codomain's own
/// interpretation, so a constant called `Quot.mk` that does not land in its own
/// quotient produces no theorem rather than a wrong one.
pub fn mk_at(
    qc: &QuotClause,
    ip: &mut Interp,
    former: &Term,
    a: &Term,
    a_mem: &Thm,
    r: &Term,
    r_mem: &Thm,
    x: &Term,
    x_mem: &Thm,
    cod_tm: &Term,
) -> Option<(Term, Thm)> {
    let graph = qc.graph(ip, a, r);
    let term = ip.mk(qc.q.class, vec![a.clone(), graph.clone(), x.clone()]);
    let rule = derived::inst_all(&qc.q.mk_mem, &[a.clone(), graph, x.clone()])?;
    let mem = Thm::mp(&rule, x_mem)?;

    // `⊢ ⟦Quot α r⟧ = quot(A,R̄)`, reversed: the membership is in `quot(A,R̄)`
    // and the codomain is the spine.
    let (bot, beta) = ip.beta_spine(former, &[a.clone(), r.clone()], &[a_mem.clone(), r_mem.clone()])?;
    if beta.concl().as_eq()?.0 != *cod_tm {
        return None
    }
    let back = derived::eq_symm(&mut ip.env, &beta)?;
    if *mem.concl() != Formula::mem(term.clone(), bot) {
        return None
    }
    let out = ip.retarget_set(&mem, &back)?;
    (*out.concl() == Formula::mem(term.clone(), cod_tm.clone())).then_some((term, out))
}

impl Interp {
    /// The `Quot` clause's apparatus at `u ≥ 1`, over **this** `Interp`'s own
    /// pairing and power set, built on first use and then shared.
    ///
    /// Identity, not memoisation: two uses of `Quot` at two `σ` must name one
    /// `quot`, and `Quot.mk`'s and `Quot.lift`'s clauses are further builds over
    /// the carrier the formation clause was stored at.
    pub fn quotient(&mut self) -> Option<Rc<QuotClause>> {
        if self.quotient.is_none() && !self.quotient_failed {
            let p = self.prelude.clone();
            self.quotient = QuotClause::build(&mut self.env, &p).map(Rc::new);
            self.quotient_failed = self.quotient.is_none();
        }
        self.quotient.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The apparatus builds, and the two theorems the formation clause rests on
    /// are **unconditional** — a `Γ`-carrying one would ride into a nest bottom
    /// this module's caller documents as closed.
    #[test]
    fn the_apparatus_builds_and_formation_is_unconditional() {
        let mut ip = Interp::new();
        let q = ip.quotient().expect("the Quot apparatus builds over the prelude");
        assert!(q.in_universe.hyps().is_empty(), "formation is unconditional");
        assert!(q.q.quot_ax.hyps().is_empty(), "quot's defining axiom is unconditional");
        assert!(q.q.rel_graph_ax.hyps().is_empty(), "rel_graph's axiom is unconditional");
    }

    /// **One `quot`, not one per call.** Two clause builds at two `σ` must name
    /// the same symbol or their definitional equality would need a theorem; the
    /// cache is what makes that true, so it is what is pinned.
    #[test]
    fn the_apparatus_is_identity_not_a_cache() {
        let mut ip = Interp::new();
        let first = ip.quotient().expect("builds");
        let second = ip.quotient().expect("builds");
        assert_eq!(first.q.quot, second.q.quot, "two uses of Quot must name one quot");
        assert_eq!(first.q.rel_graph, second.q.rel_graph, "…and one rel_graph");
        assert_eq!(first.q.class, second.q.class, "…and one class");
    }

    /// **The two `rel_graph`s share the pairing.** The header argues that
    /// minting a second `rel_graph` beside [`crate::acc`]'s is safe *because*
    /// `⟨x,y⟩` is one term in both; that is a property of two lazily-built
    /// objects and prose does not recompile, so it is asserted.
    #[test]
    fn the_two_graphs_share_one_pairing() {
        let mut ip = Interp::new();
        let (x, y) = (ip.env.fresh_var(), ip.env.fresh_var());
        let mine = ip.quotient().expect("builds").q.sums.ap.sets.clone();
        let theirs = ip.acc().expect("builds").sets.sets.clone();
        assert_eq!(
            mine.pair(Term::var(x), Term::var(y)),
            theirs.pair(Term::var(x), Term::var(y)),
            "the Quot clause's rel_graph and the Acc clause's must speak of one ordered pair"
        );
    }

    /// **Formation, at the rung the interpretation actually uses.** `⟦Sort 1⟧`
    /// is `U(ω)` and not `U(⟦Sort 0⟧)`, so this is the one step where the
    /// tower's seeding could have made a `∀c` theorem fail to instantiate.
    #[test]
    fn formation_lands_in_the_rung_the_interpretation_names() {
        let mut ip = Interp::new();
        let q = ip.quotient().expect("builds");
        for u in [1u32, 2] {
            let rung = ip.prelude.tower.at(u as usize).expect("a rung");
            let (av, rv) = (ip.env.fresh_var(), ip.env.fresh_var());
            let (a, r) = (Term::var(av), Term::var(rv));
            // The premise the checker would hold: `⟦α⟧ ∈ ⟦Sort u⟧`.
            let a_mem = crate::scope::test_support::assume(Formula::mem(a.clone(), rung.set.clone()));
            let out = q.formation(&mut ip, u, &a, &r, &a_mem).expect("formation applies");
            let carrier = q.carrier(&mut ip, &a, &r);
            assert_eq!(*out.concl(), Formula::mem(carrier, ip.sort(u)));
        }
    }

    /// **`u = 0` has no rung and the clause must not answer there.** The
    /// identity reading is `crate::quot`'s and the two are refutably different
    /// sets (`QUOT-MODEL.md` §1.2), so a formation theorem at `Sort 0` would be
    /// a wrong one rather than a missing one.
    #[test]
    fn formation_declines_at_sort_zero() {
        let mut ip = Interp::new();
        let q = ip.quotient().expect("builds");
        let (av, rv) = (ip.env.fresh_var(), ip.env.fresh_var());
        let (a, r) = (Term::var(av), Term::var(rv));
        let a_mem = crate::scope::test_support::assume(Formula::mem(a.clone(), ip.sort(0)));
        assert!(q.formation(&mut ip, 0, &a, &r, &a_mem).is_none(), "there is no rung 0");
    }
}
