//! `ω`, its induction principle, and recursion along it.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::recursion::…` all still resolve and no caller has to know which file
//! a theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`succ`] | the symbol `succ(n) = n ∪ {n}`, `succ(q) ⊆ 𝒫q` and `Trans(succ q)` at transitive `q`, `Trans(∅)` |
//! | [`naturals`] | `Ind`, `Least`, `⊢ ∃m. Least(∅,m)`, the symbol `ω`, and [`OmegaCore`] |
//! | [`induction`] | induction over `ω`, as a scheme in `φ` and as a statement about a set |
//! | [`peano`] | `Trans(n)`, `succ(n) ≠ 0`, injectivity of `succ`, and [`Peano`] |
//! | [`graph`] | `app(f,a) = b` from `⟨a,b⟩ ∈ f` for single-valued `f` |
//! | [`rec`] | [`Rec`] — `Apply` and `Peano` over one chain of definitional extensions |
//! | [`approximation`] | [`Approx`]'s five clauses, `succ(k) ∈ m → k ∈ m`, and `approx_dom` |
//! | [`hyp`] | equational glue under a fixed hypothesis |
//! | [`mod@adjoin`] | the term `s ∪ {e}`, and `z ∈ s ∪ {e} ↔ (z ∈ s ∨ z = e)` |
//! | [`agree`] | two approximations agree where their domains overlap, hence contain each other, hence are equal |
//! | [`existence`] | the base `Approx(succ 0, {⟨0,c⟩})`, the one-pair extension, and `∀n ∈ ω. ∃h. Approx(succ n, h)` |
//! | [`mod@family`] | Replacement over `ω` at `n ↦ ⟨n, app(hₙ,n)⟩`, giving the graph as a set |
//! | [`mod@iterate`] | [`RecFn`] — that graph is a function on `ω` with both equations |
//! | [`unique`] | there is at most one such function |
//! | [`theorem`] | `⊢ ∃!f. RecFn(f)`, and the symbol `iter` |
//! | [`mod@omega_tower`] | `⊢ ∀z. (z ∈ tower(c) ↔ ∃n ∈ ω. z ∈ app(iter(c), n))` |
//!
//! # Why this exists — and why it is no longer on the inductives path
//!
//! **Read this before planning work here.** The original motivation has been
//! discharged by something else, and the plan this header used to state is void.
//!
//! To interpret Lean's inductive types as W-types we need a *bound*: a set
//! containing the whole tree structure before the W-type is carved out of it.
//! `crate::universe`'s countermodels refuted the assumption that a Tarski
//! universe `U(x)` would serve — under the four-clause `ax_tarski` that stood
//! until 2026-07-31 it was not transitive, and not closed under `⋃`, binary
//! union, products or function spaces. The replacement plan was to bound
//! finitely-branching W-types by an `ω`-indexed tower, which needs recursion
//! along `ω`; a transitive-closure construction was thought to need the same
//! thing (`crate::empty`'s "open middle"), so recursion looked like the critical
//! path either way.
//!
//! **All three premises have since failed:**
//!
//! * the axiom's `C₁` clause makes `U(x)` transitive
//!   ([`crate::universe::least_universe_transitive`]), so the countermodels are
//!   not models any more — and the closure properties are not merely reopened,
//!   they are **proved**: [`crate::universe::universe_union_closed`],
//!   [`crate::universe::universe_bin_union`],
//!   [`crate::funspace::product_in_universe`],
//!   [`crate::funspace::funspace_in_universe_pair`] and
//!   [`crate::ext::dprod_in_universe_pair`]. See `crate::universe`'s "Settled"
//!   list;
//! * the `ω`-tower is **not** how W-types are bounded. `crate::inductive`'s
//!   carrier bounds every declaration at `U({A,T})` directly, by the
//!   transitivity clause. `INDUCTIVES.md` puts it as "the transitivity clause
//!   removed the need for the ω-tower … **do not restart it** on the strength of
//!   a remaining-cost estimate without checking the above first";
//! * `crate::empty`'s "open middle" is gone — `empty.rs` records that `C₁`
//!   removed the obstruction outright, so the transitive closure is not needed
//!   and the iterates `⋃ⁿx` are not built.
//!
//! What remains here has **independent** value — `ω`, `succ`, induction, Peano,
//! the recursion theorem and the symbol it licenses — and callers use it. It is
//! simply not a prerequisite for anything in `crate::inductive`.
//!
//! # The successor, and why `ω` is not simply Tarski's universe
//!
//! `succ(n) := n ∪ {n}` and `0 := ∅`. An *inductive* set is one containing `0`
//! and closed under `succ`, and `ω` is the least of them.
//!
//! The obvious route — copy [`crate::empty::least_inductive_set_exists`] with
//! `succ` in place of `𝒫` — does not work as stated, and the reason is worth
//! recording. That construction carves the least inductive set out of Tarski's
//! universe `u` around `x`, which requires `u` to be closed under the successor
//! operation. `u` **is** closed under `𝒫` ([`crate::empty::universe_power_closed`]),
//! but it is *not* closed under `n ↦ n ∪ {n}`:
//!
//! * `⋃` points downwards, and under the pre-2026-07-31 four-clause axiom `u`
//!   was not transitive — countermodel A in `crate::universe` had `{ω} ∈ u` and
//!   `⋃{ω} = ω ∉ u`. `u` *is* transitive now (`C₁`), so `n ∈ u` gives `n ⊆ u`
//!   and hence `⋃n ⊆ u`. `⋃n ∈ u` was open when this note was written; it is a
//!   theorem now ([`crate::universe::universe_union_closed`]). The derivation
//!   below never needed it;
//! * pairing closure is not derivable from the first three Tarski clauses
//!   either. Take `x := {{3}}` and let `u` be the closure of `{x}` under `𝒫`
//!   and "subset of a member". All three clauses hold, yet `{x, 𝒫x} ∉ u`,
//!   because the only member of `u` containing `x` is `𝒫x`, and `𝒫x ∉ 𝒫x`.
//!   Getting pairing therefore needs the *inaccessibility* clause, i.e. ruling
//!   out `{a,b} ≈ u`. That was expected to cost cardinal arithmetic on top of
//!   the equinumerosity formula; it did not.
//!   [`crate::universe::universe_pairing`] gets it from three members of the
//!   power tower `∅, 𝒫∅, 𝒫𝒫∅` and a pigeonhole — see `universe/pairing.rs`.
//!
//! Both obstructions are therefore gone. The route below is still the one taken,
//! because it is cheaper than either closure property, not because it has to be.
//!
//! The way through is to notice that closure is only needed **at transitive
//! sets**: if `n` is transitive then every member of `n` is a subset of `n`, so
//! `succ(n) = n ∪ {n} ⊆ 𝒫n`, and `𝒫n ∈ u` plus Tarski's second clause (subsets
//! of members are members) puts `succ(n)` into `u`. Every von Neumann natural
//! *is* transitive, so nothing is lost — and the transitivity is carried in the
//! separation condition defining `ω` rather than assumed, which is what makes
//! the argument non-circular. See [`omega_exists`].
//!
//! # What is here, and what is not
//!
//! **Here, and complete.** `ω` with the Peano properties: [`Peano`] bundles
//! `0 ∈ ω`, closure under `succ`, the induction principle in both its schematic
//! ([`induction_scheme`]) and set ([`induction_principle`]) forms, transitivity
//! of every natural ([`omega_trans`]), `succ(n) ≠ 0` ([`succ_ne_zero`]) and
//! injectivity of `succ` ([`succ_inj`]). Nothing is conditional and no axiom
//! was added: `Thm::ax_tarski` supplies the ambient universe, Replacement
//! supplies Separation, and `crate::empty::empty` supplies `0`.
//!
//! **Here, and complete: the recursion theorem.** For a base value `c` and a
//! **unary function symbol** `G` of the ambient extension,
//!
//! ```text
//! ⊢ ∃!f. ( ∀p. (p ∈ f → ∃a. (a ∈ ω ∧ ∃b. p = ⟨a,b⟩))          R1
//!        ∧ SingleValued(f)                                     R2
//!        ∧ ∀a. (a ∈ ω → ∃b. ⟨a,b⟩ ∈ f)                         R3
//!        ∧ app(f, 0) = c                                       R4
//!        ∧ ∀n. (n ∈ ω → app(f, succ n) = G(app(f, n))) )       R5
//! ```
//!
//! ([`recursion`]), and with it the symbol `iter` — `⊢ ∀c. RecFn(iter(c))` when
//! `c` is handed in as a parameter — together with the tower
//! `⊢ ∀z. (z ∈ tower(c) ↔ ∃n. (n ∈ ω ∧ z ∈ app(iter(c), n)))`
//! ([`mod@omega_tower`]). R1–R3 spell out "`f` is a function with domain exactly
//! `ω`" without a `dom` symbol and **without a codomain**, which is what the
//! approximation argument needs and what [`crate::funspace::is_function`] cannot
//! supply.
//!
//! Nothing is conditional and no axiom was added. The route, and where each step
//! lives:
//!
//! 1. the codomain-free predicate [`Approx`], in [`approximation`];
//! 2. the one-pair extension `h ∪ {⟨succ n, G(app(h,n))⟩}`, in [`existence`];
//! 3. `∀n ∈ ω. ∃!h. Approx(succ n, h)` — existence by induction
//!    ([`approx_exists`]), uniqueness from [`approx_agree`] through
//!    [`approx_subset`] to [`approx_unique`];
//! 4. Replacement over `ω`, in [`mod@family`];
//! 5. that image *is* the graph, in [`mod@iterate`];
//! 6. uniqueness of the whole function ([`unique`]), then `kernel::thm::define`
//!    ([`theorem`]).
//!
//! # Why step 5 takes no union
//!
//! The textbook argument replaces `n` by *the approximation* with domain
//! `succ n` and takes `⋃` of the result. Replacing `n` by the *pair*
//! `⟨n, app(h,n)⟩` instead makes the image already be the graph, and
//! single-valuedness then follows from uniqueness of the approximation over one
//! domain rather than from agreement of two approximations over different ones.
//! [`approx_agree`] is still stated across two domains, because R5 needs it —
//! `app(f, succ n)` is read off the approximation with domain `succ(succ n)` and
//! `app(f, n)` off the one with domain `succ n` — but it is spent exactly once
//! instead of underlying the whole function property.
//!
//! # Non-vacuity
//!
//! `derived/tests/recursion.rs` instantiates the theorem at `c := ∅` and
//! `G := 𝒫` and derives `⊢ ¬(app(iter,0) = app(iter, succ 0))`: `app(iter,0)` is
//! `∅`, `app(iter, succ 0)` is `𝒫∅`, and `∅ ∈ 𝒫∅` would transport to `∅ ∈ ∅`.
//! Without that check the whole construction could have been satisfied by a
//! constant function with every equation still true.

pub mod adjoin;
pub mod agree;
pub mod approximation;
pub mod existence;
pub mod family;
pub mod graph;
pub mod hyp;
pub mod induction;
pub mod iterate;
pub mod naturals;
pub mod omega_tower;
pub mod peano;
pub mod rec;
pub mod succ;
pub mod theorem;
pub mod unique;

pub use adjoin::{adjoin, mem_adjoin};
pub use agree::{approx_agree, approx_subset, approx_unique, omega_is_transitive};
pub use approximation::{approx, approx_dom, pred_in_omega_member, Approx};
pub use existence::{approx_exists, approx_extend, approx_one, extension, one_point_graph};
pub use family::{family, Family};
pub use graph::app_of_graph;
pub use hyp::{hyp_eq_symm, hyp_eq_trans, inst_chain};
pub use induction::{induction_principle, induction_scheme};
pub use iterate::{iterate, rec_fn, Iter, RecFn};
pub use omega_tower::{omega_tower, OmegaTower};
pub use naturals::{inductive, least_inductive, omega, omega_exists, OmegaCore};
pub use peano::{mem_succ_self, omega_trans, succ_inj, succ_ne_zero, Peano};
pub use rec::Rec;
pub use theorem::{recursion, Recursion};
pub use unique::{rec_agree, rec_subset, rec_unique};
pub use succ::{mem_union_succ, succ_subset_pow, successor, trans_empty, trans_succ};
