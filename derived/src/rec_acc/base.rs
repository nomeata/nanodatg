//! The **base apparatus** every later file in [`crate::rec_acc`] is stated over.
//!
//! # Interface
//!
//! [`Base::over`] takes a caller-supplied [`crate::sums::Sums`] and an
//! [`crate::acc::Acc`] built over *its* `Apply`, checks that the two really do
//! share their pairing, and derives everything about the conditional value
//! ([`super::cval`]) and the induction hypothesis ([`super::ih`]) once.
//! [`Base::new`] is the same from the axioms up, for tests.
//!
//! The struct's methods build the terms and formulas the recursion equation is
//! written with, so that every file below builds *the same* ones:
//!
//! ```text
//! Base::acc_of(A,R)         acc(A,R)
//! Base::edge(y,x)           ⟨y,x⟩
//! Base::ih_at(g,A,R,x)      ih(g,A,R,x)
//! Base::step_at(e,x,i)      app(app(app(e,x),•),i)
//! ```
//!
//! # Why it must be built *over* the caller's symbols
//!
//! The relation `R` is a set of Kuratowski pairs, the recursor applies things,
//! and `acc(A,R)` has to be the same set the caller's `acc_intro` speaks about.
//! An apparatus that minted its own `Sets` — or its own `Acc` — would produce
//! theorems about a *different* `⟨·,·⟩` and a *different* `acc`, and nothing
//! would compose with either the checker's terms or the rest of `derived/`.
//! That failure has been paid for more than once in this development, which is
//! why [`crate::acc::Acc::with_apply`] exists and why [`Base::over`] refuses an
//! `Acc` whose pairing is not the `Sums`'.
//!
//! # Why the step is applied curried
//!
//! Carneiro writes the recursion equation as `F(x) = e(x)(•)(ih)` — three
//! curried set-applications — and [`Base::step_at`] spells it exactly that way.
//! [`crate::wrec`] instead flattens its step to `app(e, ⟨a,⟨f,r⟩⟩)`, on the
//! grounds that each `app` in a chain costs a separate beta obligation at the
//! point of use. The trade is different here: `W`'s step is a *packed* object
//! assembled from `n` minor premises, so its argument order is the
//! construction's own choice, whereas `acc` has exactly one introduction rule
//! and `e` **is** Lean's minor premise. Keeping the thesis's spelling makes
//! `⟦rec_acc e⟧ = rec_acc(⟦α⟧,⟦r⟧,⟦e⟧)` (thesis.txt:2129) literally true and
//! matches the curried lambda-nest a checker backend produces anyway; the cost
//! is two extra beta obligations at each ι site, paid by the consumer.
//!
//! The `•` in the middle is the interpretation of the accessibility proof that
//! Lean's `Acc.rec` hands its minor premise: `⟦intro_acc x f⟧ = •`
//! (thesis.txt:2127). It carries no information, and it is *not* dropped —
//! dropping it would change the arity of `e` and so would derive a true equation
//! about a term no backend produces.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::acc::Acc;
use crate::funcs::Apply;
use crate::sums::Sums;

use super::cval::{
    cval_app, cval_bound, cval_ext, cval_single_valued, prod_inhabited, prod_snd_singleton,
};
use super::ih::{edge_prop, ih_app, ih_ext, ih_of, ih_single_valued, ih_symbol, ih_typed, ih_value};

/// Everything the recursion equation is written with, derived once.
#[derive(Clone)]
pub struct Base {
    /// Pairing, `∅`, application, the product, the power set, the unit and `•`.
    pub s: Sums,
    /// The accessibility carrier, over `s.ap`'s pairing.
    pub ac: Acc,
    /// `⊢ ∀f ∀a ∀b. ((sv(f) ∧ ⟨a,b⟩ ∈ f) → app(f,a) = b)`.
    pub app_of_graph: Thm,
    /// `⊢ ∀c ∀w ∀z. (z ∈ prod(c,w) → ∃x. x ∈ c)`.
    pub prod_inhabited: Thm,
    /// `⊢ ∀c ∀v ∀p ∀q. (⟨p,q⟩ ∈ cval(c,v) → q = v)`.
    pub prod_snd_singleton: Thm,
    /// `⊢ ∀c ∀v. sv(cval(c,v))`.
    pub cval_single_valued: Thm,
    /// `⊢ ∀c ∀v. (• ∈ c → app(cval(c,v), •) = v)` — the inner beta rule.
    pub cval_app: Thm,
    /// `⊢ ∀c ∀u ∀v. ((∀h. (h ∈ c → u = v)) → cval(c,u) = cval(c,v))`.
    pub cval_ext: Thm,
    /// `⊢ ∀c ∀u ∀d ∀t. ((∀h. (h ∈ c → (h ∈ d ∧ u ∈ t))) → cval(c,u) ⊆ prod(d,t))`.
    pub cval_bound: Thm,
    /// The symbol `ep(R,y,x) = [⟨y,x⟩ ∈ R]`.
    pub ep: FnSym,
    /// `⊢ ∀R ∀y ∀x ∀z. (z ∈ ep(R,y,x) ↔ (z ∈ 1 ∧ ⟨y,x⟩ ∈ R))`.
    pub ep_ax: Thm,
    /// The symbol `ih(g,A,R,x)`.
    pub ih: FnSym,
    /// `⊢ ∀g ∀A ∀R ∀x ∀p. (p ∈ ih(g,A,R,x) ↔ ∃y. (y ∈ A ∧ p = row(g,R,x,y)))`.
    pub ih_ax: Thm,
    /// `⊢ ∀g ∀h ∀A ∀R ∀x. (preds_agree(g,h,A,R,x) → ih(g,A,R,x) = ih(h,A,R,x))`.
    pub ih_ext: Thm,
    /// `⊢ ∀g ∀A ∀R ∀T ∀x. (preds_typed(g,A,R,T,x) → ih(g,A,R,x) ∈ ih_bound(A,T))`.
    pub ih_typed: Thm,
    /// `⊢ ∀g ∀A ∀R ∀x ∀p ∀u. (⟨p,u⟩ ∈ ih(g,A,R,x) → u = cval(ep(R,p,x), app(g,p)))`.
    pub ih_value: Thm,
    /// `⊢ ∀g ∀A ∀R ∀x. sv(ih(g,A,R,x))`.
    pub ih_single_valued: Thm,
    /// `⊢ ∀g ∀A ∀R ∀x ∀y. ((y ∈ A ∧ ⟨y,x⟩ ∈ R) →
    /// app(app(ih(g,A,R,x),y),•) = app(g,y))` — the induction hypothesis
    /// computes to the recursive value.
    pub ih_app: Thm,
}

impl Base {
    /// Build everything from the axioms up, minting a fresh [`Sums`] and a
    /// fresh [`Acc`] over its `Apply`.
    pub fn new(env: &mut Env) -> Option<Base> {
        let s = Sums::new(env)?;
        let ac = Acc::with_apply(env, &s.ap)?;
        Base::over(env, s, ac)
    }

    /// The same over caller-supplied symbols.
    ///
    /// Refuses unless `ac` was built over `s`'s pairing and `s`'s `∅` — two
    /// pairing operations mean two unrelated `⟨y,x⟩`, and then no theorem here
    /// speaks about the caller's relation. It also refuses an `Acc` whose
    /// theorems carry hypotheses, since everything below is stated
    /// unconditionally and a hypothetical input would ride its `Γ` straight
    /// through.
    pub fn over(env: &mut Env, s: Sums, ac: Acc) -> Option<Base> {
        if ac.sets.up != s.ap.sets.up || ac.sets.un != s.ap.sets.un || ac.empty != s.ap.empty {
            return None
        }
        for t in [&ac.acc_ax, &ac.acc_subset, &ac.acc_induction, &ac.acc_intro] {
            if !t.hyps().is_empty() {
                return None
            }
        }

        let app_of_graph = crate::recursion::app_of_graph(env, &s.ap)?;
        let prod_inhabited = prod_inhabited(env, &s)?;
        let prod_snd_singleton = prod_snd_singleton(env, &s)?;
        let cval_single_valued = cval_single_valued(env, &s, &prod_snd_singleton)?;
        let cval_app = cval_app(env, &s, &cval_single_valued, &app_of_graph)?;
        let cval_ext = cval_ext(env, &s, &prod_inhabited)?;
        let cval_bound = cval_bound(env, &s)?;

        let (ep, ep_ax) = edge_prop(env, &s)?;
        let (ih, ih_ax) = ih_symbol(env, &s, ep)?;
        let ih_ext = ih_ext(env, &s, ep, &ep_ax, ih, &ih_ax, &cval_ext)?;
        let ih_typed = ih_typed(env, &s, ep, &ep_ax, ih, &ih_ax, &cval_bound)?;
        let ih_value = ih_value(env, &s, ep, ih, &ih_ax)?;
        let ih_single_valued = ih_single_valued(env, &s, ih, &ih_value)?;
        let ih_app = ih_app(env, &s, ep, &ep_ax, ih, &ih_ax, &ih_single_valued, &cval_app)?;

        Some(Base {
            s,
            ac,
            app_of_graph,
            prod_inhabited,
            prod_snd_singleton,
            cval_single_valued,
            cval_app,
            cval_ext,
            cval_bound,
            ep,
            ep_ax,
            ih,
            ih_ax,
            ih_ext,
            ih_typed,
            ih_value,
            ih_single_valued,
            ih_app,
        })
    }

    /// The shared [`Apply`].
    pub fn ap(&self) -> &Apply { &self.s.ap }

    /// The term `acc(A,R)`.
    pub fn acc_of(&self, a: &Term, r: &Term) -> Term { self.ac.of(a.clone(), r.clone()) }

    /// The term `⟨y,x⟩` — the edge of the relation, pointing from `y` to `x`.
    pub fn edge(&self, y: &Term, x: &Term) -> Term {
        self.s.ap.sets.pair(y.clone(), x.clone())
    }

    /// The term `ih(g,A,R,x)`.
    pub fn ih_at(&self, g: &Term, a: &Term, r: &Term, x: &Term) -> Term {
        ih_of(self.ih, g.clone(), a.clone(), r.clone(), x.clone())
    }

    /// The term `app(app(app(e,x),•),i)` — the step applied as Carneiro writes
    /// it. See the module header for why it is curried and why `•` stays.
    pub fn step_at(&self, e: &Term, x: &Term, i: &Term) -> Term {
        let ap = &self.s.ap;
        ap.apply(
            ap.apply(ap.apply(e.clone(), x.clone()), self.s.point()),
            i.clone(),
        )
    }

    /// `app(f,a)`.
    pub fn app(&self, f: &Term, a: &Term) -> Term {
        self.s.ap.apply(f.clone(), a.clone())
    }

    /// `∃y. ⟨x,y⟩ ∈ g` — "`x` is in the domain of `g`", as a formula. Shared
    /// with [`crate::wrec`], which is where the idiom comes from.
    pub fn indom(&self, env: &mut Env, g: &Term, x: &Term) -> Formula {
        crate::wrec::indom(env, &self.s.ap, g, x)
    }
}
