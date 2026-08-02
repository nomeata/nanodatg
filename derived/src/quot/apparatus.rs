//! The quotient apparatus, assembled once.
//!
//! # Interface
//!
//! [`Quotient::new`] builds every symbol and derives every theorem from the
//! axioms up; [`Quotient::over`] does the same over a caller-supplied
//! [`crate::sums::Sums`], so that a client already holding one gets a quotient
//! whose terms compose with everything else built over it. The fields are the
//! theorems, so a caller reads them off the struct and never calls the functions
//! in the sibling files directly.
//!
//! # Why it is a struct and not a set of free functions
//!
//! Every theorem in [`crate::quot`] is about *the* pairing, *the* product,
//! *the* `eqv`, *the* `class` and *the* `lift` of one definitional extension.
//! Building any of them twice would mint a second `⟨·,·⟩`, and then `⟨x,y⟩`
//! would name two different terms and none of the theorems would compose — the
//! same hazard [`crate::wtype::Wtype::over`] and [`crate::sums::Sums::over`]
//! exist to avoid.
//!
//! # Why every entry in [`crate::quot`] reads `hyps()`
//!
//! A [`Thm`] is a sequent `Γ ⊢ φ`, and it *establishes* `φ` only when `Γ` is
//! empty. Every field of [`Quotient`] below is documented `⊢ …`, and nothing in
//! the kernel makes that documentation true: [`Thm::mp`] silently unions the two
//! sides' hypothesis sets, so one premise obtained by [`Thm::assume`] anywhere
//! upstream rides through every derivation in this module and comes back out on
//! a field whose doc comment denies it.
//!
//! [`Quotient::over`] is where that bites hardest, because it consumes a
//! **caller-supplied** [`Sums`] whose theorem fields are `pub` and are equally
//! documented `⊢ …`. Give that `Sums` a `pow_ax` of `{φ} ⊢ φ` and the whole
//! quotient used to build without complaint: [`super::classes::mk_mem`] joins
//! the power set axiom with [`Thm::mp`] and imports `Γ`, so `mk_mem` came back
//! carrying it, and so did [`super::lift::lift_in_funspace`], which consumes
//! `mk_mem`. No caller reads `hyps()` afterwards — in this crate none does — so
//! the label was simply wrong from there on.
//!
//! Measured rather than assumed: with the checks off, those **two** fields carry
//! the hypothesis and the other thirty-two do not. `quot_cases`, `sound` and the
//! five non-vacuity theorems are clean, because none of them routes through the
//! power set — `sound` is `eqv_incl` then `class_eq`, and the non-vacuity chain
//! goes by way of `ker` and the identity graph. Which fields are reachable from
//! which `Sums` field is not something a reader should have to work out, and it
//! changes whenever a derivation grows a step, which is the argument for
//! checking the bundle rather than the reachable subset.
//!
//! So `over` checks the whole `Sums` bundle up front with `shared`'s
//! `sums_unconditional`, and every function in the sibling files independently
//! checks the theorems *it* is handed, whether they come from a caller
//! assembling the development by hand or from the `over` above. The refusal is
//! then local to whoever supplied the bad premise, rather than deferred to a
//! caller who was never going to look.
//!
//! The *conclusion* half of the house rule is already carried by this module:
//! every defining biconditional is rebuilt and compared before use
//! (`Classes::parts`, `Ker::parts`, `Lift::parts`, `eqv_parts`), and the composite
//! lemmas pin the formula they hand back. The few that did not — `q_sound`,
//! `lift_beta`'s consequent, and the three non-vacuity compositions — now do,
//! and take the symbols they need to rebuild it as arguments.

use kernel::{Env, FnSym, Thm};

use crate::ext::{app_of_pair, funspace_app_mem};
use crate::sums::Sums;

use super::classes::{self, Classes};
use super::compat::{self, Ker};
use super::eqv;
use super::graph;
use super::lift::{self, Lift};
use super::shared::sums_unconditional;
use super::witness::{self, Identity};

/// Every quotient symbol together with everything derived about it.
///
/// Built over a **single** [`Sums`], so that `⟨·,·⟩`, `prod`, `𝒫`, `fs` and
/// `app` all come from one definitional extension and the theorems compose.
pub struct Quotient {
    /// The unit type, sums, product, power set, function space and application.
    pub sums: Sums,

    /// The symbol `eqv`.
    pub eqv: FnSym,
    /// `⊢ ∀A ∀R ∀p. (p ∈ eqv(A,R) ↔ (p ∈ A² ∧ eqv_cond(A,R,p)))`.
    pub eqv_ax: Thm,
    /// `⊢ ∀A ∀R ∀p. (p ∈ eqv(A,R) → p ∈ prod(A,A))`.
    pub eqv_subset: Thm,
    /// `⊢ ∀A ∀R ∀E. ((E ⊆ A² ∧ eqv_closed(A,R,E)) → ∀p. (p ∈ eqv(A,R) → p ∈ E))`
    /// — minimality of the closure.
    pub eqv_induction: Thm,
    /// `⊢ ∀A ∀R ∀x. (x ∈ A → ⟨x,x⟩ ∈ eqv(A,R))`.
    pub eqv_refl: Thm,
    /// `⊢ ∀A ∀R ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,R) → ⟨y,x⟩ ∈ eqv(A,R))`.
    pub eqv_sym: Thm,
    /// `⊢ ∀A ∀R ∀x ∀y ∀z. ((⟨x,y⟩ ∈ eqv ∧ ⟨y,z⟩ ∈ eqv) → ⟨x,z⟩ ∈ eqv)`.
    pub eqv_trans: Thm,
    /// `⊢ ∀A ∀R ∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R)) → ⟨x,y⟩ ∈ eqv(A,R))`.
    pub eqv_incl: Thm,
    /// `⊢ ∀A ∀R. eqv_closed(A,R,eqv(A,R))` — the closure is an equivalence
    /// relation on `A` containing `R`.
    pub eqv_closed: Thm,

    /// The symbol `class`.
    pub class: FnSym,
    /// `⊢ ∀A ∀R ∀x ∀y. (y ∈ class(A,R,x) ↔ (y ∈ A ∧ ⟨x,y⟩ ∈ eqv(A,R)))`.
    pub class_ax: Thm,
    /// `⊢ ∀A ∀R ∀x. class(A,R,x) ⊆ A`.
    pub class_subset: Thm,
    /// `⊢ ∀A ∀R ∀x. (x ∈ A → x ∈ class(A,R,x))`.
    pub class_self: Thm,
    /// `⊢ ∀A ∀R ∀a ∀b. (⟨a,b⟩ ∈ eqv(A,R) → class(A,R,a) = class(A,R,b))`.
    pub class_eq: Thm,
    /// `⊢ ∀A ∀R ∀a ∀b. ((b ∈ A ∧ class(A,R,a) = class(A,R,b)) → ⟨a,b⟩ ∈ eqv(A,R))`
    /// — exactness.
    pub class_exact: Thm,

    /// The symbol `quot` — this is `A/∼`.
    pub quot: FnSym,
    /// `⊢ ∀A ∀R ∀c. (c ∈ quot(A,R) ↔ (c ∈ 𝒫A ∧ ∃x. (x ∈ A ∧ c = class(A,R,x))))`.
    pub quot_ax: Thm,
    /// **`mk`**: `⊢ ∀A ∀R ∀x. (x ∈ A → class(A,R,x) ∈ quot(A,R))`.
    pub mk_mem: Thm,
    /// **No junk**: `⊢ ∀A ∀R ∀c. (c ∈ quot(A,R) → ∃x. (x ∈ A ∧ c = class(A,R,x)))`.
    pub quot_cases: Thm,
    /// **`sound`**: `⊢ ∀A ∀R ∀a ∀b. ((a ∈ A ∧ (b ∈ A ∧ ⟨a,b⟩ ∈ R))
    /// → class(A,R,a) = class(A,R,b))`.
    pub sound: Thm,

    /// The symbol `rel_graph` — Lean's **curried** `r` as a set of pairs.
    ///
    /// Minted **once, here**, and taking `A` and `r` as arguments, so every use
    /// site is an application of this one arity-2 symbol. A formulation that
    /// baked `r` into the symbol would mint one Separation per relation and
    /// would need a caller-side keyed table to stay canonical; see
    /// [`super::graph`]'s header.
    pub rel_graph: FnSym,
    /// `⊢ ∀A ∀r ∀p. (p ∈ rel_graph(A,r) ↔ (p ∈ A² ∧ ∀u ∀v. (p = ⟨u,v⟩ → …)))`.
    pub rel_graph_ax: Thm,
    /// `⊢ ∀A ∀r ∀u ∀v. (⟨u,v⟩ ∈ rel_graph(A,r) → • ∈ app(app(r,u),v))` — the
    /// direction `Quot.lift`'s hypothesis needs.
    pub graph_pair: Thm,
    /// `⊢ ∀A ∀r ∀u ∀v. ((u ∈ A ∧ (v ∈ A ∧ • ∈ app(app(r,u),v)))
    /// → ⟨u,v⟩ ∈ rel_graph(A,r))` — the direction `Quot.sound` needs.
    pub pair_in_graph: Thm,
    /// `⊢ ∀A ∀r. rel_graph(A,r) ⊆ prod(A,A)`.
    pub graph_subset: Thm,

    /// The symbol `ker`, the kernel of a function.
    pub ker: FnSym,
    /// `⊢ ∀A ∀f ∀p. (p ∈ ker(A,f) ↔ (p ∈ A² ∧ ∀u ∀v. (p = ⟨u,v⟩ → …)))`.
    pub ker_ax: Thm,
    /// `⊢ ∀A ∀f ∀u ∀v. (⟨u,v⟩ ∈ ker(A,f) → app(f,u) = app(f,v))`.
    pub ker_pair: Thm,
    /// `⊢ ∀A ∀R ∀f. (rcompat(A,R,f) → compat(A,R,f))` — Lean's `Quot.lift`
    /// hypothesis implies the one [`Quotient::lift_beta`] consumes.
    pub compat_closure: Thm,

    /// The symbol `lift`.
    pub lift: FnSym,
    /// `⊢ ∀A ∀R ∀f ∀p. (p ∈ lift(A,R,f) ↔ ∃x. (x ∈ A ∧ p = ⟨class(A,R,x), app(f,x)⟩))`.
    pub lift_ax: Thm,
    /// `⊢ ∀A ∀R ∀f ∀x. (x ∈ A → ⟨class(A,R,x), app(f,x)⟩ ∈ lift(A,R,f))`.
    pub lift_pair: Thm,
    /// `⊢ ∀A ∀R ∀f. (compat(A,R,f) → sv(lift(A,R,f)))` — `lift` is well defined.
    pub lift_single_valued: Thm,
    /// **The computation rule**: `⊢ ∀A ∀R ∀f ∀x. ((compat(A,R,f) ∧ x ∈ A)
    /// → app(lift(A,R,f), class(A,R,x)) = app(f,x))`.
    pub lift_beta: Thm,
    /// **`lift`'s typing rule**: `⊢ ∀A ∀R ∀B ∀f. ((f ∈ fs(A,B) ∧ compat(A,R,f))
    /// → lift(A,R,f) ∈ fs(quot(A,R), B))`.
    pub lift_in_funspace: Thm,

    /// The identity graph and its beta rule, used only for non-vacuity.
    pub identity: Identity,
    /// `⊢ ∀A ∀f. compat(A,∅,f)` — **non-vacuity of the compatibility
    /// antecedent**: every `f` respects `eqv(A,∅)`.
    pub compat_at_empty: Thm,
    /// `⊢ ∀A ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,∅) → x = y)` — **non-vacuity of the
    /// closure**: `eqv(A,∅)` is inside the diagonal, so `∼` is not everything.
    pub eqv_of_empty: Thm,
    /// `⊢ ∀A ∀a ∀b. ((b ∈ A ∧ class(A,∅,a) = class(A,∅,b)) → a = b)` —
    /// **non-vacuity of the quotient**: at `R := ∅`, `mk` is injective, so
    /// `quot(A,∅)` is not a point.
    pub class_injective_at_empty: Thm,
    /// `⊢ ∀A ∀f ∀x. (x ∈ A → app(lift(A,∅,f), class(A,∅,x)) = app(f,x))` —
    /// [`Quotient::lift_beta`] with its antecedent discharged.
    pub lift_beta_at_empty: Thm,
}

impl Quotient {
    /// Introduce every symbol and derive every theorem, from the axioms up.
    pub fn new(env: &mut Env) -> Option<Quotient> {
        let sums = Sums::new(env)?;
        Quotient::over(env, sums)
    }

    /// The same, over a **caller-supplied** [`Sums`].
    ///
    /// Building one afresh instead would mint a *second* `⟨·,·⟩` and a second
    /// `prod`, and then no theorem here would speak of the same operators as
    /// the caller's.
    ///
    /// Every theorem field of `sums` must be **unconditional**, and this is
    /// where that is checked, once, for the whole bundle. Every field of the
    /// [`Quotient`] returned is documented `⊢ …`, and a `Sums` carrying a
    /// hypothesis would put its `Γ` on most of them by way of the `Thm::mp`s
    /// below without any of the sibling constructions noticing — see the module
    /// header for the worked case. The conclusions are `sums`'s own business:
    /// [`Sums::over`] pins them, and the constructions below rebuild and compare
    /// the ones they actually consume.
    pub fn over(env: &mut Env, sums: Sums) -> Option<Quotient> {
        if !sums_unconditional(&sums) {
            return None
        }

        let app_pair = app_of_pair(env, &sums.ap)?;
        let app_mem = funspace_app_mem(env, &sums.ap, &sums.prod, &sums.fs, &app_pair)?;

        // ── The equivalence closure ──────────────────────────────────────────
        let (eqv_s, eqv_ax) = eqv::eqv_symbol(env, &sums)?;
        let eqv_subset = eqv::eqv_subset(env, &sums, eqv_s, &eqv_ax)?;
        let eqv_induction = eqv::eqv_induction(env, &sums, eqv_s, &eqv_ax)?;
        let pip = sums.pair_in_prod.clone();
        let eqv_refl = eqv::eqv_refl(env, &sums, eqv_s, &eqv_ax, &pip)?;
        let eqv_sym = eqv::eqv_sym(env, &sums, eqv_s, &eqv_ax, &pip)?;
        let eqv_trans = eqv::eqv_trans(env, &sums, eqv_s, &eqv_ax, &pip)?;
        let eqv_incl = eqv::eqv_incl(env, &sums, eqv_s, &eqv_ax, &pip)?;
        let eqv_closed = eqv::eqv_closed_self(
            env, &sums, eqv_s, &eqv_refl, &eqv_sym, &eqv_trans, &eqv_incl,
        )?;

        // ── Classes and the quotient set ─────────────────────────────────────
        let (class, class_ax) = classes::class_symbol(env, &sums, eqv_s)?;
        let cls = Classes { s: &sums, eqv: eqv_s, class, class_ax: &class_ax };
        let class_subset = classes::class_subset(env, &cls)?;
        let class_self = classes::class_self(env, &cls, &eqv_refl)?;
        let class_eq = classes::class_eq(env, &cls, &eqv_sym, &eqv_trans)?;
        let class_exact = classes::class_exact(env, &cls, &class_self)?;

        let (quot, quot_ax) = classes::quot_symbol(env, &sums, class)?;
        let mk_mem = classes::mk_mem(env, &sums, class, &class_subset, quot, &quot_ax)?;
        let quot_cases = classes::quot_cases(env, &sums, class, quot, &quot_ax)?;
        let sound = classes::q_sound(env, &sums, class, &eqv_incl, &class_eq)?;

        // ── The kernel, and Lean's compatibility hypothesis ──────────────────
        let (ker, ker_ax) = compat::ker_symbol(env, &sums)?;
        let kv = Ker { s: &sums, ker, ker_ax: &ker_ax };
        let ker_subset = compat::ker_subset(env, &kv)?;
        // ── Lean's curried relation, as a set of pairs ───────────────────────
        let (rel_graph, rel_graph_ax) = graph::rel_graph_symbol(env, &sums)?;
        let gv = graph::RelGraph { s: &sums, graph: rel_graph, graph_ax: &rel_graph_ax };
        let graph_pair = graph::graph_pair(env, &gv)?;
        let pair_in_graph = graph::pair_in_graph(env, &gv)?;
        let graph_subset = graph::graph_subset(env, &gv)?;

        let ker_pair = compat::ker_pair(env, &kv)?;
        let pair_in_ker = compat::pair_in_ker(env, &kv)?;
        let ker_closed = compat::ker_closed(env, &kv, &ker_pair, &pair_in_ker)?;
        let compat_closure = compat::compat_closure(
            env,
            &kv,
            eqv_s,
            &eqv_induction,
            &(ker_subset, ker_pair.clone(), ker_closed),
        )?;

        // ── The eliminator ───────────────────────────────────────────────────
        let (lift_s, lift_ax) = lift::lift_symbol(env, &sums, class)?;
        let lv = Lift {
            s: &sums,
            eqv: eqv_s,
            class,
            quot,
            lift: lift_s,
            lift_ax: &lift_ax,
        };
        let lift_pair = lift::lift_pair(env, &lv)?;
        let lift_single_valued = lift::lift_single_valued(env, &lv, &class_exact)?;
        let lift_beta =
            lift::lift_beta(env, &lv, &lift_single_valued, &lift_pair, &app_pair)?;
        let lift_in_funspace = lift::lift_in_funspace(
            env,
            &lv,
            &mk_mem,
            &quot_cases,
            &lift_pair,
            &lift_single_valued,
            &app_mem,
        )?;

        // ── Non-vacuity ──────────────────────────────────────────────────────
        let identity = Identity::new(env, &sums, &app_pair)?;
        let rc_empty = witness::rcompat_at_empty(env, &sums)?;
        let compat_at_empty =
            witness::compat_at_empty(env, &sums, eqv_s, &compat_closure, &rc_empty)?;
        let eqv_of_empty = witness::eqv_of_empty(
            env, &sums, eqv_s, &eqv_subset, &identity, &compat_at_empty,
        )?;
        let class_injective_at_empty =
            witness::class_injective_at_empty(env, &sums, class, &class_exact, &eqv_of_empty)?;
        let lift_beta_at_empty =
            witness::lift_beta_at_empty(env, &sums, class, lift_s, &lift_beta, &compat_at_empty)?;

        Some(Quotient {
            sums,
            eqv: eqv_s,
            eqv_ax,
            eqv_subset,
            eqv_induction,
            eqv_refl,
            eqv_sym,
            eqv_trans,
            eqv_incl,
            eqv_closed,
            class,
            class_ax,
            class_subset,
            class_self,
            class_eq,
            class_exact,
            quot,
            quot_ax,
            mk_mem,
            quot_cases,
            sound,
            rel_graph,
            rel_graph_ax,
            graph_pair,
            pair_in_graph,
            graph_subset,
            ker,
            ker_ax,
            ker_pair,
            compat_closure,
            lift: lift_s,
            lift_ax,
            lift_pair,
            lift_single_valued,
            lift_beta,
            lift_in_funspace,
            identity,
            compat_at_empty,
            eqv_of_empty,
            class_injective_at_empty,
            lift_beta_at_empty,
        })
    }

    /// The empty set as a term — the `R` at which the non-vacuity theorems
    /// speak.
    pub fn empty(&self) -> kernel::Term { kernel::Term::apply(self.sums.ap.empty, vec![]) }
}
