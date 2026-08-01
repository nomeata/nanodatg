//! The unit type `1`, the binary sum `A + B`, and the case function `rec₊`.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::sums::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need.
//!
//! | file | what it exports |
//! |---|---|
//! | [`unit_type`] | `• ∈ 1`, `x ∈ 1 → x = •`, `¬∃x. x ∈ 0`, and `¬(∅ = 1)` — the tags differ |
//! | [`membership`] | members of a binary union, of a tagged copy `{t} × a`, and `⟨u,v⟩ ∈ A × T` |
//! | [`sum`] | [`Sums`] — the symbol `A + B`, its master lemma, and both injections |
//! | [`cases`] | [`Cases`] — the symbol `rec₊`, its typing rule and its two computation rules |
//! | [`in_universe`] | `(a + b) ∈ U(c)` — closure of a universe under the sum |
//!
//! `shared` holds the term constructors for `0`, `1`, `inl`, `inr` and the body
//! of `A + B`, together with the private implication-form combinators more than
//! one of the files needs; it exports no theorem and is not re-exported.
//!
//! # Nothing here is an axiom
//!
//! `0` and the point `•` are `∅`, `1` is `{∅}`, `A + B` is
//! `({∅} × A) ∪ ({1} × B)`, and everything below is derived from those
//! definitions with the pairing, union, power set, Separation and Replacement
//! apparatus that [`crate::funcs`] and [`crate::funspace`] already build. The
//! two new symbols, [`Sums::sum`] and [`Cases::case`], are ordinary definitional
//! extensions: one explicit ([`sum_symbol`]), one by a membership condition
//! ([`case_symbol`]).
//!
//! # Why these tags
//!
//! `inl(a) = ⟨∅, a⟩` and `inr(b) = ⟨1, b⟩`. The whole construction rests on the
//! two tags being *different sets*, which is [`Sums::tags_distinct`]:
//! `⊢ ¬(∅ = 1)`, because `∅ ∈ {∅}` and nothing is a member of `∅`. Without that
//! lemma disjointness would be a statement about one tag and would prove
//! nothing, so it is derived and tested separately rather than assumed.
//!
//! # The shape of the development
//!
//! | fact | lemma | file |
//! |---|---|---|
//! | `• ∈ 1` | [`unit_mem`] | [`unit_type`] |
//! | `x ∈ 1 → x = •` | [`unit_eta`] | [`unit_type`] |
//! | `¬∃x. x ∈ 0` | [`zero_empty`], from [`crate::empty::empty`] | [`unit_type`] |
//! | `¬(∅ = 1)` | [`tags_distinct`] | [`unit_type`] |
//! | `z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v)` | [`mem_bin_union_iff`] | [`membership`] |
//! | `z ∈ {t} × a ↔ ∃y. (y ∈ a ∧ z = ⟨t,y⟩)` | [`tagged_copy_members`] | [`membership`] |
//! | `⟨u,v⟩ ∈ A × T ↔ (u ∈ A ∧ v ∈ T)` | [`pair_in_product`] | [`membership`] |
//! | `z ∈ A + B ↔ (∃a. … ∨ ∃b. …)` | [`sum_members`] — **the master lemma** | [`sum`] |
//! | intro, disjointness, injectivity, no junk | [`injection_mem`], [`sum_disjoint`], [`injection_inj`], [`sum_case_analysis`] | [`sum`] |
//! | `⟨inl(a),y⟩ ∈ case ↔ ⟨a,y⟩ ∈ f` | [`case_pairs`] | [`cases`] |
//! | `case ∈ fs(A+B,T)` | [`case_in_funspace`] | [`cases`] |
//! | `app(case, inl(a)) = app(f,a)` | [`case_beta`] | [`cases`] |
//! | `(a ∈ U(c) ∧ b ∈ U(c)) → (a+b) ∈ U(c)` | [`sum_in_universe`] | [`in_universe`] |
//!
//! Once [`sum_members`] is proved the four requested facts about `A + B` are
//! corollaries of it and of the Kuratowski pair's injectivity: choosing a
//! disjunct, reading one off, and cancelling a tag.
//!
//! # The antecedents on the computation rules, and which are real
//!
//! [`case_beta`] concludes
//!
//! ```text
//! ⊢ ∀A ∀B ∀T ∀f ∀g ∀a. (f ∈ fs(A,T) → (a ∈ A → app(case(A,B,T,f,g), inl(a)) = app(f,a)))
//! ```
//!
//! * `f ∈ fs(A,T)` **is** consumed, in one place: [`case_pairs`] runs backwards
//!   through `f ⊆ A × T`, which is what supplies `a ∈ A` and `y ∈ T` and hence
//!   puts `⟨inl(a),y⟩` into `(A+B) × T`. Without some such hypothesis the pair
//!   cannot be shown to satisfy the Separation guard. Note the `inl` rule needs
//!   only `f`'s membership, not `g`'s.
//! * `a ∈ A` is **not** consumed. The derivation establishes the equation
//!   outright and the antecedent is added afterwards by weakening, because it is
//!   the shape a caller reducing `rec₊` will have to hand. The stronger
//!   statement is one `Thm::ax_k` step away inside [`case_beta`].
//!
//! `case` also carries `A`, `B` and `T` as parameters, since Separation needs a
//! superset and the sum needs its two summands; `case(A,B,T,f,g)` is the
//! `case(f,g)` of the informal statement.

pub mod cases;
pub mod in_universe;
pub mod membership;
mod shared;
pub mod sum;
pub mod unit_type;

pub use cases::{case_beta, case_in_funspace, case_pairs, case_symbol, Cases};
pub use in_universe::sum_in_universe;
pub use membership::{mem_bin_union_iff, pair_in_product, tagged_copy_members};
pub use sum::{
    injection_inj, injection_mem, sum_case_analysis, sum_disjoint, sum_members, sum_symbol, Sums,
};
pub use unit_type::{tags_distinct, unit_eta, unit_mem, zero_empty};
