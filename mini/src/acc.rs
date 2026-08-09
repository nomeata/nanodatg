//! **`Acc`'s interpretation clause** — the accessibility predicate, Carneiro
//! §6.2.2's second named denotation.
//!
//! # Interface
//!
//! ```text
//! acc::AccClause::build(env, sums) -> Option<AccClause>   (the apparatus)
//! acc::AccClause::phi(A, r, x)     -> Formula             (the condition)
//! Interp::acc()                    -> Option<Rc<AccClause>>
//! ```
//!
//! The clause itself is a row of [`crate::direct::Clause`] and is dispatched
//! from [`crate::zoneb::build`] exactly as `Eq`'s is — before the index check
//! and before the eliminator trichotomy, because `Acc` is an *indexed*
//! declaration whose constructor's recursive field is function-typed at
//! telescope depth 2, so both of those routes decline it — as `Gap::IndSpec`,
//! with the step that refused it. *(This read `Gap::FunTypedRecArg`, "the
//! reason the three corpus pairs wait on today"; that variant no longer has a
//! mint site, and no `Acc` pair has waited on it since this clause was
//! wired.)* What lives here is only the **apparatus**:
//! the symbols and theorems the clause's bottoms consume.
//!
//! # The clause
//!
//! ```text
//! ⟦Acc α r x⟧ = [ x̄ ∈ acc(⟦α⟧, rel_graph(⟦α⟧, ⟦r⟧)) ]
//! ```
//!
//! — thesis.txt:2126, `⟦acc_{α,r} x⟧ = [x ∈ acc(⟦α⟧,⟦r⟧)]`, with one
//! correction the thesis's notation hides and the code cannot: **`acc` takes a
//! set of pairs and `⟦r⟧` is curried.** Every theorem in [`derived::acc`] reads
//! `⟨y,x⟩ ∈ R`, while Lean's `r : α → α → Prop` interprets as
//! `⟦r⟧ ∈ fs(A, fs(A, U₀))` and "`r y x` holds" is `• ∈ app(app(⟦r⟧,y),x)`.
//! [`derived::quot::rel_graph_symbol`] is the bridge and it is consumed here
//! for the first time; it was built for the `ℓ > 0` quotient clause and is the
//! same seam at a different declaration.
//!
//! So the denoting symbol is arity **3** — `acc_set(A, r, x)` — where `Eq`'s is
//! arity 2, and the relation argument is Lean's curried `r`, never the graph:
//! baking the graph into the symbol would make `⟦Acc α r x⟧` mention a term the
//! `Π` clause's domain slot cannot recover.
//!
//! # Why the apparatus is lazy and separate from [`crate::direct::Direct`]
//!
//! `Direct::build` runs on the first constant that takes a direct clause, and
//! `Eq` occurs in most exports. [`derived::acc::Acc`] derives A0–A2 and two
//! non-vacuity witnesses from the axioms up, and `rel_graph_symbol` carves a
//! Separation over `prod(A,A)`; none of that is wanted by an export that
//! mentions only `Eq`. So this apparatus is built on **its own** first use and
//! cached on the `Interp` — the same lazy-with-a-failure-flag shape
//! [`crate::interp::Interp::direct`] and `ind_apparatus` both have, and for the
//! same identity reason: two uses of `Acc` at different `σ` must name one
//! `acc_set`, or their definitional equality would need a theorem where
//! reflexivity should do.
//!
//! # There are now two `acc` symbols, and this is why that is safe
//!
//! [`crate::interp::IndApparatus`] already builds a
//! [`derived::acc::Acc`](derived::acc::Acc) — the one `LeCarrier` needs for
//! §5.3's *general* class-(S) carrier. This module mints a **second**, and by
//! this project's own standing rule (`MINI-HANDOFF.md` §2, and
//! `INDEXED-DESIGN.md` §8.1 note 1, where re-minting `⟦List⟧` cost 54 ι sites)
//! a re-minted symbol is a defect whenever two routes have to agree about it.
//!
//! They cannot meet here. `zoneb::build` dispatches on
//! [`crate::direct::clause_for`] **before** the eliminator trichotomy, so the
//! Lean declaration `Acc` never acquires a `ClassS`, and no class-(S)
//! declaration's carrier is ever compared with `⟦Acc α r x⟧`: one is the
//! interpretation of a Lean type, the other is a set the translation of a
//! *different* declaration is carved out of. What the two must share is the
//! **pairing** — `⟨y,x⟩` has to be one term or `rel_graph`'s members are not
//! `acc`'s edges — and they do: `IndApparatus::acc` builds over
//! `mach.wt.sums.ap` and `Wtype::over` is handed `prelude.tower.sums`, which is
//! the `Sums` this module takes its `ap` from.
//!
//! The alternative — reaching for `IndApparatus::acc` — was rejected on cost,
//! not on taste: it would make an export that mentions `Acc` and no other
//! inductive (`117_accRecType` is exactly one) build a `Wtype`, a `Bound`, an
//! `IndChain` and a `Machine`, which is the expense that apparatus is lazy to
//! avoid. If a third consumer of `acc` ever appears, the right move is to lift
//! **one** lazy `derived::acc::Acc` onto [`crate::interp::Interp`] and have
//! both read it; that is a refactor across a borrow boundary
//! (`IndApparatus::acc` takes `&mut Env` from inside `&mut IndApparatus`), and
//! it is not worth it for two consumers that never compare notes.
//!
//! # What is here and what is not
//!
//! The formation clause needs `acc_set` and its defining biconditional and
//! nothing else — `[φ] ∈ U₀` is a closed theorem of the tower at any `φ`
//! whatever, so the type former costs no `acc` theorem at all. A0–A2 and the
//! graph bridges are carried because the **constructor** and the **eliminator**
//! consume them, and they are minted here rather than at those sites so that
//! all three speak of one `acc`.
//!
//! [`intro_mem`] is the constructor's half. Measured, it consumes **A1,
//! `graph_pair` and `acc_set_ax`** and nothing else: not `pair_in_graph`, which
//! points the wrong way for it, and not A0 or A2, which `acc_intro` has already
//! spent. The eliminator's half is open.

use std::rc::Rc;

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::acc::Acc as AccSets;
use derived::prop::{cond_elim, cond_intro, conditional_singleton};
use derived::quot::{graph_pair, pair_in_graph, rel_graph_symbol, RelGraph};
use derived::sums::Sums;

use crate::interp::{Interp, PiShape};
use crate::scope::Scopes;

/// The `Acc` clause's symbols and the theorems its bottoms consume.
///
/// Built over **the prelude's own** [`Sums`], so that the `⟨y,x⟩` this module's
/// `acc` speaks of is the ordered pair every other construction uses, and its
/// `1` and `•` are the ones the interpretation already committed to.
pub struct AccClause {
    /// `acc(A,R)`, A0, A1 and A2 — over the prelude's pairing.
    pub sets: AccSets,
    /// `rel_graph(A,r)` — Lean's curried `r` as the set of pairs `acc` wants.
    pub graph: FnSym,
    /// `⊢ ∀A ∀r ∀p. (p ∈ rel_graph(A,r) ↔ (p ∈ A² ∧ ∀u ∀v. (p = ⟨u,v⟩ → …)))`.
    pub graph_ax: Thm,
    /// `⊢ ∀A ∀r ∀u ∀v. (⟨u,v⟩ ∈ rel_graph(A,r) → • ∈ app(app(r,u),v))` — hold a
    /// pair, owe Lean's `r`. **This is the direction [`intro_mem`] uses**, and
    /// it is the one the eliminator does **not**: see
    /// [`AccClause::pair_in_graph`].
    ///
    /// *(This line read "the direction the **eliminator** needs" against
    /// [`AccClause::pair_in_graph`]'s "the direction the **constructor**
    /// needs", and the two were the wrong way round. The pair membership is an
    /// *antecedent* of `acc_intro`'s second premise, so the constructor
    /// **holds** it and owes Lean's `r`. A bridge is chosen by which side of
    /// the implication the consumer is on, not by which of the two it is —
    /// and the second revision of that sentence said "so the eliminator wants
    /// `graph_pair` too", which is false: `step_closed` is `acc_intro`'s
    /// premise when it is **proved** and `ind_step`'s antecedent when it is
    /// **used**, and `Acc.rec` is the second. The rule has to be applied to
    /// the occurrence.)*
    pub graph_pair: Thm,
    /// `⊢ ∀A ∀r ∀u ∀v. ((u ∈ A ∧ (v ∈ A ∧ • ∈ app(app(r,u),v)))
    /// → ⟨u,v⟩ ∈ rel_graph(A,r))` — hold Lean's `r`, owe a pair.
    ///
    /// **[`crate::rec_acc`] is its consumer, and it uses it twice.**
    ///
    /// *(This line read "carried with no consumer in `mini/`", and named
    /// `derived::quot`'s `q_sound`/`rcompat` and the `ℓ > 0` quotient clause as
    /// the direction that would eventually want it. Measured at `Acc.rec`:
    /// the **eliminator** wants it, at both of Lean's predecessor hypotheses.
    /// The two consumers stand on opposite sides of one formula —
    /// `acc_intro`'s second premise is *proved*, so the pair membership is an
    /// antecedent it holds; `acc_rect`'s `ind_step` receives the same formula
    /// as an antecedent and *uses* it, so the pair is owed. `MINI-HANDOFF.md`
    /// §17 item 3's rule is right and was applied to the theorem rather than to
    /// the occurrence.)*
    pub pair_in_graph: Thm,
    /// `acc_set(A,r,x) = [ x ∈ acc(A, rel_graph(A,r)) ]`.
    pub acc_set: FnSym,
    /// `⊢ ∀A ∀r ∀x ∀z. (z ∈ acc_set(A,r,x) ↔ (z ∈ 1 ∧ x ∈ acc(A,rel_graph(A,r))))`.
    pub acc_set_ax: Thm,
}

impl AccClause {
    /// Introduce the graph, the accessibility carrier and the conditional
    /// singleton over them.
    ///
    /// Returns `None` rather than half a clause if any of the three declines —
    /// `Acc::with_apply` refuses a conditional `empty_ax`, `rel_graph_symbol`
    /// refuses a conditional `Sums`, and `conditional_singleton` refuses a `φ`
    /// its parameter list does not cover.
    pub fn build(env: &mut Env, sums: &Sums) -> Option<AccClause> {
        let (graph, graph_ax) = rel_graph_symbol(env, sums)?;
        let g = RelGraph { s: sums, graph, graph_ax: &graph_ax };
        let graph_pair = graph_pair(env, &g)?;
        let pair_in_graph = pair_in_graph(env, &g)?;
        // The pairing `acc` reasons about must be the one `rel_graph`'s members
        // are built from, or `⟨y,x⟩ ∈ R̄` would be two unrelated statements.
        let sets = AccSets::with_apply(env, &sums.ap)?;
        let (av, rv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let phi = condition(&sets, graph, &Term::var(av), &Term::var(rv), &Term::var(xv));
        let (acc_set, acc_set_ax) = conditional_singleton(env, sums, &[av, rv, xv], &phi)?;
        Some(AccClause { sets, graph, graph_ax, graph_pair, pair_in_graph, acc_set, acc_set_ax })
    }

    /// The condition `x ∈ acc(A, rel_graph(A,r))` — the formula `acc_set` is
    /// the conditional singleton of, at arbitrary terms.
    ///
    /// Every consumer builds it through this one function, so a bottom cannot
    /// state a membership about a formula the symbol is not about.
    pub fn phi(&self, a: &Term, r: &Term, x: &Term) -> Formula {
        condition(&self.sets, self.graph, a, r, x)
    }

    /// `acc(A, rel_graph(A,r))` — the carrier the clause is about.
    pub fn carrier(&self, a: &Term, r: &Term) -> Term {
        Term::apply(self.sets.acc, vec![a.clone(), Term::apply(self.graph, vec![a.clone(), r.clone()])])
    }
}

/// **`Γ ⊢ • ∈ acc_set(A,r̄,x̄)`** — `Acc.intro`'s typing, from the step
/// hypothesis's own scope typing.
///
/// # What this is
///
/// `Acc.intro α r x (h : ∀ y, r y x → Acc α r y) : Acc α r x`. The rule is
/// [`derived::acc::acc_intro`] (A1), which is unconditional and wants
///
/// ```text
/// x̄ ∈ A   and   ∀y. (y ∈ A → (⟨y,x̄⟩ ∈ R̄ → y ∈ acc(A,R̄)))
/// ```
///
/// The first is the `x` binder's own scope typing, read off. The second is the
/// whole of the work, and it is **not** what `h`'s scope typing says: `h`'s
/// typing is `• ∈ ⟦∀y:α, r y x → Acc α r y⟧`, a conditional singleton over the
/// same statement spelled in Lean's terms. Three transports separate them, and
/// each is one of the seams this module exists to hold:
///
/// * **the quantifier.** [`Interp::cond_app`] delivers its conclusion *at a
///   term*, and A1's premise is a `∀`. So the derivation runs at a **fresh**
///   `y` with `y ∈ A` assumed and discharges — `Closed::discharge`'s
///   `∀y. (y ∈ A → …)` is A1's premise shape on the nose, which is why no
///   formula surgery appears below;
/// * **the curried relation.** Lean's `r y x` arrives as
///   `• ∈ app(app(r̄,y),x̄)` and A1 wants `⟨y,x̄⟩ ∈ R̄`.
///   [`AccClause::graph_pair`] is that step, and it is an *implication*, so it
///   composes with `derived::syl` rather than by modus ponens: the pair
///   membership is A1's own antecedent and is never in hand;
/// * **the β step.** `⟦Acc α r y⟧` in `h`'s type is a redex over the stored
///   `⟦Acc.{σ}⟧` nest, not the conditional singleton the clause denotes with.
///   One [`Interp::beta_spine`] reduces it to `acc_set(A,r̄,ȳ)`, and only then
///   can [`derived::prop::cond_elim`] read `ȳ ∈ acc(A,R̄)` off it.
///
/// # The inner binder is opened and instantiated at `•`
///
/// `r y x → Acc α r y` is a `Prop`-valued `Π` like any other, so its
/// interpretation is a second conditional singleton and `cond_app` needs an
/// *element* of `⟦r y x⟧` to fire at. There is none in hand — what A1 gives is
/// the pair membership — so the walk opens a scope at `⟦r y x⟧`, derives under
/// it, discharges to `∀w. (w ∈ ⟦r y x⟧ → …)` and instantiates at `•`. That is
/// the same move `graph_pair`'s conclusion then discharges, and doing it in
/// this order is what keeps every step an implication between formulas the
/// library already states.
///
/// # What the caller owes
///
/// `former` must be the stored `⟦Acc.{σ}⟧`, and the three `mem` arguments the
/// binders' own scope typings at the *same* σ. Nothing here is checked by name:
/// a wrong `h_mem` fails [`Interp::as_pi`] or the final shape comparison, and
/// `None` is a decline with the caller's reason, never a wrong theorem.
#[allow(clippy::too_many_arguments)]
pub fn intro_mem(
    ip: &mut Interp,
    ac: &AccClause,
    former: &Term,
    a: &Term,
    a_mem: &Thm,
    r: &Term,
    r_mem: &Thm,
    x: &Term,
    x_mem: &Thm,
    h_mem: &Thm,
) -> Option<Thm> {
    let sums = ip.prelude.tower.sums.clone();
    let point = ip.point();
    // `R̄ = rel_graph(A,r̄)`, the set of pairs `acc` reasons about.
    let graph = Term::apply(ac.graph, vec![a.clone(), r.clone()]);

    // ── `∀y. (y ∈ A → (⟨y,x̄⟩ ∈ R̄ → y ∈ acc(A,R̄)))` ─────────────────────────
    let mut scopes = Scopes::new();
    let tok_y = scopes.open(&mut ip.env_mut(), a.clone());
    let (y, y_mem) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };

    // `h` at `y`: `• ∈ ⟦r y x → Acc α r y⟧`.
    let h_set = h_mem.concl().as_mem()?.1;
    let PiShape::Prop { site: outer, dom: outer_dom } = ip.as_pi(&h_set)? else { return None };
    if outer_dom != *a {
        return None
    }
    let at_y = ip.cond_app(&outer, a, h_mem, &y, &y_mem)?;

    // …and at a proof of `r y x`, which is a scope rather than a certificate.
    let rel_set = at_y.concl().as_mem()?.1;
    let PiShape::Prop { site: inner, dom: rel } = ip.as_pi(&rel_set)? else { return None };
    let tok_w = scopes.open(&mut ip.env_mut(), rel.clone());
    let (w, w_mem) = {
        let sc = scopes.get(0)?;
        (sc.term(), sc.assumption().clone())
    };
    let at_w = ip.cond_app(&inner, &rel, &at_y, &w, &w_mem)?;

    // `⟦Acc α r y⟧` is a redex over the stored nest; `acc_set(A,r̄,ȳ)` is what
    // the conditional singleton's elimination is about.
    let args = [a.clone(), r.clone(), y.clone()];
    let mems = [a_mem.clone(), r_mem.clone(), y_mem];
    let (set_y, beta) = ip.beta_spine(former, &args, &mems)?;
    let at_set = ip.retarget_set(&at_w, &beta)?;
    let phi_y = ac.phi(a, r, &y);
    let chi_y = derived::inst_all(&ac.acc_set_ax, &args)?;
    let elim = cond_elim(&sums, &phi_y, &set_y, &chi_y)?;
    let y_in_acc = Thm::mp(&elim, &at_set)?;

    // Discharge the proof of `r y x`, then re-supply it at `•` — which is where
    // `graph_pair` hands the relation back, in Lean's curried spelling.
    let over_w = scopes.close(tok_w).discharge(&y_in_acc).ok()?;
    let from_rel = derived::inst_all(&over_w, std::slice::from_ref(&point))?;
    let gp = derived::inst_all(&ac.graph_pair, &[a.clone(), r.clone(), y, x.clone()])?;
    let step = derived::syl(&gp, &from_rel)?;
    let preds = scopes.close(tok_y).discharge(&step).ok()?;

    // ── A1 at this instance, and back into the clause's own singleton ───────
    let a1 = derived::inst_all(&ac.sets.acc_intro, &[a.clone(), graph, x.clone()])?;
    let x_in_acc = Thm::mp(&a1, &derived::and_intro(x_mem, &preds))?;

    let phi_x = ac.phi(a, r, x);
    let set_x = ip.mk(ac.acc_set, vec![a.clone(), r.clone(), x.clone()]);
    let chi_x = derived::inst_all(&ac.acc_set_ax, &[a.clone(), r.clone(), x.clone()])?;
    let intro = cond_intro(&sums, &phi_x, &set_x, &chi_x)?;
    let out = Thm::mp(&intro, &x_in_acc)?;
    (*out.concl() == Formula::mem(point, set_x)).then_some(out)
}

/// [`AccClause::phi`], as a free function so that [`AccClause::build`] can call
/// it before the struct exists.
fn condition(sets: &AccSets, graph: FnSym, a: &Term, r: &Term, x: &Term) -> Formula {
    let g = Term::apply(graph, vec![a.clone(), r.clone()]);
    Formula::mem(x.clone(), Term::apply(sets.acc, vec![a.clone(), g]))
}

impl Interp {
    /// The `Acc` clause's apparatus, over **this** `Interp`'s own pairing and
    /// unit set, built on first use and then shared.
    ///
    /// Identity, not memoisation: `⟦Acc.{0}⟧` and `⟦Acc.{1}⟧` must name one
    /// `acc_set`, and the eliminator is a second build over the carrier the
    /// type former was stored at.
    pub fn acc(&mut self) -> Option<Rc<AccClause>> {
        if self.acc.is_none() && !self.acc_failed {
            let sums = self.prelude.tower.sums.clone();
            let built = AccClause::build(&mut self.env_mut(), &sums).map(Rc::new);
            self.acc = built;
            self.acc_failed = self.acc.is_none();
        }
        self.acc.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The apparatus builds, and every theorem it carries is **unconditional**
    /// — a `Γ`-carrying one would ride into a bottom this module's callers
    /// document as closed.
    #[test]
    fn the_apparatus_builds_and_is_unconditional() {
        let mut ip = Interp::new();
        let a = ip.acc().expect("the Acc apparatus builds over the prelude");
        assert!(a.graph_ax.hyps().is_empty(), "rel_graph's axiom is unconditional");
        assert!(a.graph_pair.hyps().is_empty(), "graph_pair is unconditional");
        assert!(a.pair_in_graph.hyps().is_empty(), "pair_in_graph is unconditional");
        assert!(a.acc_set_ax.hyps().is_empty(), "acc_set's axiom is unconditional");
        assert!(a.sets.acc_intro.hyps().is_empty(), "A1 is unconditional");
        assert!(a.sets.acc_induction.hyps().is_empty(), "A2 is unconditional");
        assert!(a.sets.acc_subset.hyps().is_empty(), "A0 is unconditional");
    }

    /// **One `acc_set`, not one per call.** Two clause builds at two `σ` must
    /// name the same symbol or their definitional equality would need a
    /// theorem; the cache is what makes that true, so it is what is pinned.
    #[test]
    fn the_apparatus_is_identity_not_a_cache() {
        let mut ip = Interp::new();
        let first = ip.acc().expect("builds");
        let second = ip.acc().expect("builds");
        assert_eq!(first.acc_set, second.acc_set, "two uses of Acc must name one acc_set");
        assert_eq!(first.graph, second.graph, "…and one rel_graph");
        assert_eq!(first.sets.acc, second.sets.acc, "…and one acc");
    }

    /// **The two `acc`s share the pairing.** The header argues that minting a
    /// second `derived::acc::Acc` beside `IndApparatus`'s is safe *because*
    /// `⟨y,x⟩` is one term in both; that is a property of two lazily-built
    /// objects and prose does not recompile, so it is asserted.
    #[test]
    fn the_two_acc_apparatus_share_one_pairing() {
        let mut ip = Interp::new();
        let mine = ip.acc().expect("builds").sets.sets.clone();
        let (x, y) = (ip.fresh_var(), ip.fresh_var());
        let pair_here = mine.pair(Term::var(x), Term::var(y));
        let theirs = {
            let (mut env, app, _) = ip.ind_parts().expect("the inductive apparatus builds");
            let env = &mut *env;
            app.acc(env).expect("the class-(S) acc builds").sets.clone()
        };
        assert_eq!(
            pair_here,
            theirs.pair(Term::var(x), Term::var(y)),
            "the class-(S) acc and the Acc clause's acc must speak of one ordered pair"
        );
    }

    /// The condition really is the one `acc_set` was carved out of: the
    /// defining biconditional, instantiated at three arbitrary terms, has
    /// [`AccClause::phi`] on its right-hand side.
    ///
    /// This is the check that keeps a bottom from proving `• ∈ acc_set(…)`
    /// from a formula the symbol is not about.
    #[test]
    fn the_axiom_is_about_the_condition_this_module_states() {
        let mut ip = Interp::new();
        let a = ip.acc().expect("builds");
        let (av, rv, xv) = (ip.fresh_var(), ip.fresh_var(), ip.fresh_var());
        let (ta, tr, tx) = (Term::var(av), Term::var(rv), Term::var(xv));
        let z = ip.fresh_var();
        let at = derived::inst_all(&a.acc_set_ax, &[ta.clone(), tr.clone(), tx.clone()])
            .and_then(|t| derived::inst_all(&t, &[Term::var(z)]))
            .expect("instantiates");
        let one = ip.prelude.tower.sums.unit();
        let set = Term::apply(a.acc_set, vec![ta.clone(), tr.clone(), tx.clone()]);
        assert_eq!(
            *at.concl(),
            Formula::iff(
                Formula::mem(Term::var(z), set),
                Formula::and(Formula::mem(Term::var(z), one), a.phi(&ta, &tr, &tx)),
            ),
            "acc_set is the conditional singleton of exactly AccClause::phi"
        );
    }
}
