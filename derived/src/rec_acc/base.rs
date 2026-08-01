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
    /// speaks about the caller's relation.
    ///
    /// # The hypothesis checks, and why they are where they are
    ///
    /// Everything in [`crate::rec_acc`] up to `totality` is stated
    /// unconditionally, and the module's non-vacuity claim
    /// ("**every one of these has no antecedent at all**") is about theorems
    /// derived here. A hypothetical input would ride its `Γ` straight through
    /// the first [`Thm::mp`] into a result still labelled `⊢`. Three checks,
    /// covering the three ways one could get in:
    ///
    /// * **all seven of `ac`'s theorems**, via [`Acc::all_unconditional`]. This
    ///   used to be four — `acc_ax`, `acc_subset`, `acc_induction`, `acc_intro`
    ///   — while the doc claimed all. The gap was real and reachable:
    ///   `ac.empty_relation` is `pub`, nothing else reads its `hyps()`, and
    ///   [`super::witness::unit_accessible`] consumes it with a conclusion-only
    ///   pin, so a `Γ`-carrying one produced `{…} ⊢ • ∈ acc(1,∅)` and
    ///   [`super::witness::unit_facts`] threaded that `Γ` into all four of the
    ///   closed non-vacuity witnesses.
    /// * **the theorems of `s` that this module reads directly.** `Sums`,
    ///   `Apply` and `Sets` also carry `pub` `⊢ …` fields, and the recursor
    ///   spends nine of them (listed below) — inside [`super::attempt`],
    ///   [`super::union`], [`super::total`] and here. They belong to
    ///   [`crate::sums`], but this is the boundary at which `rec_acc` accepts
    ///   them, so this is where they are checked.
    /// * **the fields of the `Base` being returned**, once built. Each is
    ///   documented `⊢ φ`, and three of them come from outside this module
    ///   ([`crate::recursion::app_of_graph`] and, through
    ///   [`super::ih::edge_prop`], [`crate::prop::conditional_singleton`]), so
    ///   the check is not implied by the two above.
    pub fn over(env: &mut Env, s: Sums, ac: Acc) -> Option<Base> {
        if ac.sets.up != s.ap.sets.up || ac.sets.un != s.ap.sets.un || ac.empty != s.ap.empty {
            return None
        }
        if !ac.all_unconditional() {
            return None
        }
        // The `Sums` theorems `rec_acc` reads directly. `fs.fs_ax` and
        // `ap.sets.un_ax` are spent in `total`/`union` rather than here, but a
        // `Base` is the object those files are stated over, so refusing early is
        // what makes their headers true.
        if !crate::all_unconditional(&[
            &s.pow_ax,
            &s.pair_in_prod,
            &s.unit_mem,
            &s.prod.prod_ax,
            &s.fs.fs_ax,
            &s.ap.empty_ax,
            &s.ap.mem_sing,
            &s.ap.pair_inj,
            &s.ap.sets.un_ax,
        ]) {
            return None
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

        let out = Base {
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
        };
        if !out.all_unconditional() {
            return None
        }
        Some(out)
    }

    /// The hypothesis half of the house rule for **every theorem this struct
    /// carries**, its [`Acc`] included.
    ///
    /// `Base`'s fields are all `pub` and all documented `⊢ φ`, so a caller can
    /// replace any of them after [`Base::over`] has returned with a
    /// [`Thm::assume`] of the same conclusion — and every file in
    /// [`crate::rec_acc`] is stated over a `Base`. So anything that takes one it
    /// did not itself build owes this check; [`super::RecAcc::over`] is the one
    /// such boundary today.
    ///
    /// Conclusions are deliberately *not* rechecked: they are this struct's own
    /// business, pinned by the derivations [`Base::over`] runs, whereas the
    /// hypothesis leg is checked nowhere else. See [`crate::all_unconditional`].
    pub fn all_unconditional(&self) -> bool {
        self.ac.all_unconditional()
            && crate::all_unconditional(&[
                &self.app_of_graph,
                &self.prod_inhabited,
                &self.prod_snd_singleton,
                &self.cval_single_valued,
                &self.cval_app,
                &self.cval_ext,
                &self.cval_bound,
                &self.ep_ax,
                &self.ih_ax,
                &self.ih_ext,
                &self.ih_typed,
                &self.ih_value,
                &self.ih_single_valued,
                &self.ih_app,
            ])
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
