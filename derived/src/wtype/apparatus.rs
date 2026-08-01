//! The W-type apparatus, assembled once.
//!
//! # Interface
//!
//! [`Wtype::new`] builds every symbol and derives every theorem from the axioms
//! up; [`Wtype::over`] does the same over a caller-supplied [`crate::sums::Sums`],
//! so that a client already holding one gets a W-type whose terms compose with
//! everything else built over it. The fields are the theorems of W1–W4 and the
//! auxiliary facts, so a caller reads them off the struct and never calls the
//! functions in the sibling files directly.
//!
//! # Why it is a struct and not a set of free functions
//!
//! Every theorem in [`crate::wtype`] is about *the* pairing, *the* function
//! space and *the* `W` symbol of one definitional extension. Building any of
//! them twice would mint a second `upair`, and then `⟨a,f⟩` would name two
//! different terms and none of the theorems would compose — the same hazard
//! [`crate::sums::Sums::over`] and [`crate::bound::Bound::over`] exist to avoid.

use kernel::{Env, FnSym, Formula, Term, Thm};
use crate::ext::{app_of_pair, funspace_app_mem, funspace_retarget};
use crate::sums::Sums;
use crate::opair;

use super::condition::{closed, w_subset, w_symbol};
use super::monotone::fs_mono;
use super::empty::{app_of_empty, empty_funspace, empty_is_a_function, empty_product};
use super::induction::w_induction;
use super::sup::sup_mem;
use super::inversion::w_inversion;
use super::witness::{unit_bound_closed, unit_wtype_inhabited};

/// The `W` symbol together with everything derived about it.
///
/// Built over a **single** [`Sums`], so that `⟨·,·⟩`, `fs`, `app` and `∅` all
/// come from one definitional extension and the theorems compose. Building two
/// would mint two unrelated pairing operations and nothing here would fit.
#[derive(Clone)]
pub struct Wtype {
    /// The unit type, sums, product, function space and application.
    pub sums: Sums,
    /// `⊢ ∀f ∀x ∀y. ((f single-valued ∧ ⟨x,y⟩ ∈ f) → app(f,x) = y)`.
    pub app_pair: Thm,
    /// `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)`.
    pub app_mem: Thm,
    /// `⊢ ∀a ∀b ∀c ∀f. ((f ∈ fs(a,b) ∧ ∀x. (x ∈ a → app(f,x) ∈ c)) → f ∈ fs(a,c))`.
    pub retarget: Thm,
    /// `⊢ ∀X ∀Y ∀Z ∀f. ((f ∈ fs(X,Y) ∧ Y ⊆ Z) → f ∈ fs(X,Z))`.
    pub fs_mono: Thm,
    /// `⊢ ∀S. ∅ ∈ fs(∅, S)`.
    pub empty_fun: Thm,
    /// `⊢ ∀a. app(∅, a) = ∅`.
    pub app_empty: Thm,
    /// The symbol `W`.
    pub w: FnSym,
    /// `⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) ↔ (z ∈ u ∧ ∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S)))`.
    pub w_ax: Thm,
    /// `⊢ ∀A ∀B ∀u ∀z. (z ∈ W(A,B,u) → z ∈ u)`.
    pub w_subset: Thm,
    /// **W2**:
    /// `⊢ ∀A ∀B ∀u ∀C. ((C ⊆ u ∧ closed(A,B,C)) → ∀z. (z ∈ W(A,B,u) → z ∈ C))`.
    pub w_induction: Thm,
    /// **W1**: `⊢ ∀A ∀B ∀u. (closed(A,B,u) → ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a),
    /// W(A,B,u)) → ⟨a,f⟩ ∈ W(A,B,u))))`.
    pub sup_mem: Thm,
    /// `⊢ ∀a ∀f ∀a′ ∀f′. (⟨a,f⟩ = ⟨a′,f′⟩ → (a = a′ ∧ f = f′))` — **W4**,
    /// injectivity of `sup`. This *is* [`crate::pairs::opair_inj`]: `sup` is the
    /// Kuratowski pair, so there is nothing to prove beyond naming it.
    pub sup_inj: Thm,
    /// `⊢ ⟨•,∅⟩ ∈ W(1, ∅, {⟨•,∅⟩})` — **non-vacuity**. See
    /// [`crate::wtype::unit_wtype_inhabited`]; it is built unconditionally so that a
    /// development whose `W` came out empty would fail to construct at all.
    pub inhabited: Thm,
    /// `⊢ closed(1, ∅, {⟨•,∅⟩})` — **non-vacuity of the bound hypothesis**.
    /// W1, W3 and [`crate::wtype::w_rect`] all carry `closed(A,B,u)` as an antecedent, and
    /// this exhibits a `u` that satisfies it. See [`crate::wtype::unit_bound_closed`].
    pub bound_closed: Thm,
}

impl Wtype {
    /// Introduce the symbol and derive everything, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Wtype> {
        let sums = Sums::new(env)?;
        Wtype::over(env, sums)
    }

    /// The same, over a **caller-supplied** [`Sums`], so that a client already
    /// holding one gets a W-type whose terms compose with everything else built
    /// over it.
    pub fn over(env: &mut Env, sums: Sums) -> Option<Wtype> {
        let app_pair = app_of_pair(env, &sums.ap)?;
        let app_mem = funspace_app_mem(env, &sums.ap, &sums.prod, &sums.fs, &app_pair)?;
        let retarget = funspace_retarget(env, &sums.ap, &sums.prod, &sums.fs, &app_pair)?;
        let fs_mono = fs_mono(env, &sums, &app_mem, &retarget)?;
        let empty_fun = empty_is_a_function(env, &sums)?;
        let app_empty = app_of_empty(env, &sums)?;

        let (w, w_ax) = w_symbol(env, &sums)?;
        let w_sub = w_subset(env, &sums, w, &w_ax)?;
        let w_ind = w_induction(env, &sums, w, &w_ax)?;
        let sup = sup_mem(env, &sums, w, &w_ax, &w_sub, &w_ind, &fs_mono)?;
        let sup_inj = sums.ap.pair_inj.clone();
        let inhabited =
            unit_wtype_inhabited(env, &sums, w, &w_ax, &empty_fun, &app_empty)?;
        let prod_empty = empty_product(env, &sums)?;
        let empty_fs = empty_funspace(env, &sums, &prod_empty)?;
        let bound_closed = unit_bound_closed(env, &sums, &empty_fs, &app_empty)?;

        Some(Wtype {
            sums,
            app_pair,
            app_mem,
            retarget,
            fs_mono,
            empty_fun,
            app_empty,
            w,
            w_ax,
            w_subset: w_sub,
            w_induction: w_ind,
            sup_mem: sup,
            sup_inj,
            inhabited,
            bound_closed,
        })
    }

    /// The term `W(A,B,u)`.
    pub fn of(&self, a: Term, b: Term, u: Term) -> Term {
        Term::apply(self.w, vec![a, b, u])
    }

    /// The term `⟨a,f⟩` — the `sup` constructor.
    pub fn sup(&self, a: Term, f: Term) -> Term { opair(self.sums.ap.sets.up, a, f) }

    /// The term `B(a)`, i.e. `app(B,a)`.
    pub fn fibre(&self, b: Term, a: Term) -> Term { self.sums.ap.apply(b, a) }

    /// The term `∅`.
    pub fn empty(&self) -> Term { Term::apply(self.sums.ap.empty, vec![]) }

    /// **W3**, derived on demand — see [`crate::wtype::w_inversion`].
    ///
    /// Not a field: it is [`crate::wtype::w_rect`] at a particular `φ`, and `w_rect` mints a
    /// fresh symbol per call, so making every `Wtype` carry one would put a
    /// definitional extension into the struct that most callers never use.
    pub fn inversion(&self, env: &mut Env) -> Option<Thm> { w_inversion(env, self) }

    /// `closed(A,B,S)`, as a formula.
    pub fn closed_at(&self, env: &mut Env, a: &Term, b: &Term, set: &Term) -> Formula {
        closed(env, &self.sums, a, b, set)
    }
}
