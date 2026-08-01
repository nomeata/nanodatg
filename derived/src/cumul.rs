//! **`⟦N⟧ ∈ U₁`**, and the cumulative hierarchy `V₀ = S`, `V₍ₙ₊₁₎ = Vₙ ∪ 𝒫Vₙ`,
//! `T(S) = ⋃ₙ Vₙ` that gets there.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here.
//!
//! | file | what it exports |
//! |---|---|
//! | [`step`] | the unary symbol `G(x) = x ∪ 𝒫x`, its membership rules and its monotonicity, plus `subset_trans` and the binary union's elimination rule |
//! | [`stages`] | [`Stages`] — the recursion at `G`, the tower `T(S) = ⋃ₙ Vₙ`, and that the chain increases and is **directed** |
//! | [`mod@bounded`] | `⊢ ∀k ∈ ω. bnd(k)` — a function out of a natural number lands in a single stage |
//! | [`closure`] | stage arithmetic: `Vₚ ⊆ T`, subsets of a stage land one `succ` up, pairs two |
//! | [`universe`] | `⊢ ∀c ∀n ∈ ω. (S ∈ U(c) → Vₙ ∈ U(c))` — the stages stay inside any universe holding the seed |
//! | [`closed`] | `⊢ closed(A,B,T)` — **(b)**, the tower is closed under `sup` |
//! | [`inside`] | [`Inside`] — `T ⊆ U(c)` **(c)** and `T ∈ U(c)` **(e)** |
//! | [`wmem`] | [`WMem`] — `W ⊆ T` **(d)** and `W ∈ U(d)` **(f)** |
//! | [`witness`] | [`NatUniverse`] — **(g)**, `⊢ ⟦N⟧ ∈ U₁` at closed terms |
//! | [`chain`] | [`Chain`] — the one chain of definitional extensions all of the above live over |
//! | [`ambient`] | `Chain::over` — the same chain over a signature the caller already has |
//! | [`enums`] | `⊢ enum(A) ∈ U₁` — the same argument where the fibres are empty |
//!
//! # What it is for, and what it now proves
//!
//! `⟦N⟧ ∈ ⟦Type 0⟧` — for a long time the largest remaining wall in the
//! checker, and no longer a wall: `checker/src/tg.rs` consumes this module's
//! `NatMem::over` and `enums::enum_in_u1` through its `IndTy` clause, so `⟦N⟧`,
//! `⟦Bool⟧`, `⟦Unit⟧` and `⟦Empty⟧` are discharged rather than assumed (see
//! "WHAT THE CHECKER NOW CONSUMES" below). It is a
//! **size** statement: `W(A,B,u) ⊆ u` is free by construction, but membership
//! needs `W` to be caught inside a set that is itself a member of a universe,
//! and the cumulative hierarchy over a seed containing `A` and the fibres is
//! that set. The chain is complete and its end point is
//!
//! ```text
//! ⊢ W(1+1, B, U(1+1)) ∈ U(ω)        [NatUniverse::nat_in_u1]
//! ```
//!
//! at **closed terms with no hypothesis**, together with [`crate::wnat::Nat`]'s
//! `zero`, `succ` and `zero_ne_succ` at the same terms — so the set it is about
//! is provably infinite. Start at [`Chain`], then [`NatUniverse`]; the closing
//! note at the bottom of this file is the record of how the route was found and
//! which parts of it were wrong.

pub mod ambient;
pub mod bounded;
pub mod chain;
pub mod closed;
pub mod closure;
pub mod enums;
pub mod inside;
pub mod stages;
pub mod witness;
pub mod wmem;
pub mod universe;
pub mod step;

pub use bounded::{bnd, bounded, bounded_at};
pub use chain::Chain;
pub use closed::{tower_closed, tower_closed_bnd};
pub use closure::{mem_tower, pair_in_stage, sub_in_stage};
pub use enums::{enum_in_u1, unit_in_u1, zero_in_u1};
pub use inside::Inside;
pub use stages::{subset_refl, Stages};
pub use universe::stages_in_universe;
pub use step::{curry, mem_bin_union_elim, subset_trans, Step};
pub use witness::{NatMem, NatUniverse};
pub use wmem::WMem;

// ─────────────────────────────────────────────────────────────────────────────
// Closing note — 2026-07-31, in two sessions: the one that built the tower and
// refuted the target it was asked for, and the one that finished the chain to
// `⟦N⟧ ∈ U₁`. The first session's record is kept verbatim, because its
// corrections are what made the second short.
//
// WHAT IS DONE, all unconditional and each pinned by a test in
// `derived/tests/cumul.rs` at fresh constants or (for the last three) at
// closed terms:
//
//   ⊢ ∀a ∀b ∀c. ((a ⊆ b ∧ b ⊆ c) → a ⊆ c)                    [subset_trans]
//   ⊢ ∀a ∀b ∀z. (z ∈ a ∪ b → (z ∈ a ∨ z ∈ b))                [mem_bin_union_elim]
//   ⊢ ∀x. G(x) = x ∪ 𝒫x, plus mem/sub/elim/mono               [Step]
//   ⊢ V₀ = S,  ⊢ ∀n ∈ ω. V₍succ n₎ = G(Vₙ),  the tower `T(S)` [Stages]
//   ⊢ ∀n ∈ ω. Vₙ ⊆ V₍succ n₎                                  [Stages::incr]
//   ⊢ ∀m ∈ ω. V₀ ⊆ Vₘ                                         [Stages::zero_least]
//   ⊢ ∀n ∈ ω ∀m ∈ ω. ∃p ∈ ω. (Vₙ ⊆ Vₚ ∧ Vₘ ⊆ Vₚ)              [Stages::directed]
//   ⊢ ∀k ∈ ω. bnd(k)                                          [bounded]
//   ⊢ ∀p ∈ ω ∀z. (z ∈ Vₚ → z ∈ T)                             [mem_tower]
//   ⊢ ∀p ∈ ω ∀z. (z ⊆ Vₚ → z ∈ V₍succ p₎)                     [sub_in_stage]
//   ⊢ ∀p ∈ ω ∀x ∀y. ((x ∈ Vₚ ∧ y ∈ Vₚ) → ⟨x,y⟩ ∈ V₍succ² p₎)  [pair_in_stage]
//   ⊢ ∀c ∀n ∈ ω. (S ∈ U(c) → Vₙ ∈ U(c))                       [stages_in_universe]
//   ⊢ ∀A ∀B. (Fin(A,B) → closed(A,B,T))                       [tower_closed]
//   ⊢ ∀n ∈ ω. ⟨n,Vₙ⟩ ∈ iter(S)                                [Inside::graph_pair]
//   ⊢ ∀c. (S ∈ U(c) → T ⊆ U(c))                               [Inside::tower_subset]
//   ⊢ ∀c. (S ∈ U(c) → iter(S) ∈ fs(ω, U(c)))                  [Inside::iter_in_fs]
//   ⊢ ∀c. ((S ∈ U(c) ∧ ω ∈ U(c)) → T ∈ U(c))                  [Inside::tower_mem]
//   ⊢ ∀A ∀B ∀c. ((Fin(A,B) ∧ S ∈ U(c)) → W(A,B,U(c)) ⊆ T)     [WMem::w_sub_tower]
//   ⊢ ∀A ∀B ∀c ∀d. (… → W(A,B,U(c)) ∈ U(d))                   [WMem::w_in_universe]
//   ⊢ 1 = succ 0        ⊢ 1 ∈ ω        ⊢ (1+1) ∈ U₁           [NatUniverse]
//   ⊢ W(1+1, B, U(1+1)) ∈ U(ω)   — i.e. ⊢ ⟦N⟧ ∈ U₁            [NatUniverse::nat_in_u1]
//
// The last of those is the deliverable, it is at closed terms, and
// `crate::wnat::Nat`'s `zero`/`succ`/`zero_ne_succ` at the same terms are what
// stop it being a statement about a one-element set.
//
// ── THE STATEMENT IN THE BRIEF IS FALSE, AND THIS IS THE FIRST THING TO KNOW ──
//
// `W(A,B,u) ∈ u` is **refutable** at the `u` the development actually uses.
// `⟦N⟧` is `W(A, B, U(A))` with `A = 1+1` (`crate::wnat`), and:
//
//   * `V_ω`, the hereditarily finite sets, satisfies every clause of
//     `crate::universe::is_universe` — this is already recorded in
//     `crate::tower`, where it is the countermodel that forces `U₁ := U(ω)`
//     rather than `U(U₀)`;
//   * `A ∈ V_ω`, so `U(A) ⊆ V_ω`, so **every member of `U(A)` is finite**;
//   * `crate::bound::least_universe_closed` gives `closed(A,B,U(A))`, so
//     `W(A,B,U(A))` really is the least closed subset, and `crate::wnat`'s
//     `zero`, `succ`, `zero_ne_succ` and `succ_inj` make it infinite.
//
// So `W(A,B,U(A)) ∉ U(A)`. `W ∈ u` is a *size* statement and the size has to
// come from somewhere: the correct target is
//
//     W(A,B,U(A)) ∈ U₁      (or any `U(c)` with `ω ∈ U(c)`)
//
// and `⊢ ω ∈ Uₙ` (`crate::tower::Level::omega_mem`) is not an optional
// ingredient of the argument — it is the whole of its size content. Every note
// downstream that says "`W ∈ u` for the bound `u`" should be read as "`W ∈ u′`
// for a universe `u′` containing `ω`". Nothing else about the plan changes:
// `⟦N⟧ ∈ ⟦Type 0⟧` was always a membership in `U₁`, not in the bound.
//
// ── WHAT THE PREVIOUS HANDOVER GOT WRONG ────────────────────────────────────
//
// `recursion/theorem.rs`'s closing note names three remaining items. Two of the
// three are the wrong shape, and the reasons are worth having:
//
//   1. "Build `G` as a real unary `FnSym` from Product/Funspace — the step
//      `X ↦ {⟨a,f⟩ : a ∈ A, f ∈ fs(B(a),X)}`." **Not possible, and not needed.**
//      `crate::recursion::recursion` takes the step as a `FnSym`, and a `FnSym`
//      introduced by `define_abbrev` may mention no free variables outside its
//      own parameters — so a step depending on `A` and `B` cannot exist at
//      arity 1. Everything parametric has to enter through the recursion's
//      *base*, which may have free variables listed in `params`. Hence the step
//      here is the closed `G(x) = x ∪ 𝒫x` and the parameter is the **seed**:
//      `V₀ = S`, `V₍ₙ₊₁₎ = Vₙ ∪ 𝒫Vₙ`. That is a cumulative hierarchy over `S`,
//      it contains the W-stage tower, and it works for `wlist`'s `A = 1 + α`
//      with `α` free, which a W-stage `G` could not have.
//   2. "A second, universe-relative copy of `omega_tower`'s Replacement
//      instance." **Not needed.** `iter(S)` is a set of pairs `⟨n,Vₙ⟩`, so
//      `Vₙ ∈ ⋃⋃iter(S)` and hence `T = ⋃ₙVₙ ⊆ ⋃⋃⋃iter(S)`. Three `⋃`-closures
//      and `C₂` ("a subset of a member is a member") then give `T ∈ U(c)` from
//      `iter(S) ∈ U(c)` — no image symbol, no `Tower::family`, and no matching
//      of two Replacement symbols by Extensionality. `Tower::family` could not
//      have served anyway: it demands a **unary** fibre symbol, and `n ↦ Vₙ` is
//      `app(iter(S),n)` with `S` free.
//   3. "`W ⊆ ⋃ₙWₙ` is the only genuinely new mathematics left, an induction
//      over `crate::wtype::rect`." Half right. The induction is not over `rect`
//      — plain `w_induction` (W2) suffices, since `T` is a closed subset of the
//      bound and `W` is the least one. The genuinely new mathematics is the
//      thing W2's antecedent needs, namely `closed(A,B,T)`, and *that* is where
//      finite branching enters: `f : B(a) → T` picks a stage per argument and
//      `⟨a,f⟩ ∈ T` needs one stage for all of them. See `bounded`.
//
// ── THE TWO IDEAS THAT MADE IT WORK ─────────────────────────────────────────
//
//   * **Directedness without an order on `ω`.** Merging two stage indices looks
//     like it needs `max`, hence trichotomy, hence two nested inductions this
//     development does not have. It does not: the step operator is monotone, so
//     an induction on `n` can build the merge point by applying `succ` to the
//     one the induction hypothesis produced (`Stages::directed`). This is why
//     the step is `x ∪ 𝒫x` and not `𝒫x` — with `𝒫x` the chain increases only
//     at a transitive seed, and a transitive seed is a transitive closure, i.e.
//     another `ω` recursion.
//   * **Finite branching as `k ∈ ω`.** `bounded` proves that a function out of
//     a von Neumann natural lands in a single stage, by induction on `k` with
//     `directed` doing the merge. The fibres of every inductive in scope *are*
//     naturals — `crate::wnat` sends its two tags to `0` and `1`, `crate::wlist`
//     likewise, a two-recursive-argument constructor would send its tag to `2`
//     — so `∀a ∈ A. B(a) ∈ ω` is the finite-branching hypothesis to carry. A
//     fibre merely *equinumerous* to a natural needs `bnd` transported along a
//     surjection, which is one extra lemma and is not written.
//
// ── WHAT WAS LEFT, AND WHAT EACH STEP TURNED OUT TO COST ────────────────────
//
// All of (a)–(g) below are now derived. Each is pinned by a test in
// `derived/tests/cumul.rs` at the exact statement, and `Chain::new` returning
// `Some` is itself the check that every symbol involved is the same symbol.
//
//  (a) THE SEED. Proposed: `S := A ∪ ⋃⋃⋃B`, proved once and for all.
//      **Not taken, and it is a worse deal than it looks.** `B(a) ⊆ ⋃⋃⋃B` needs
//      `⟨a,B(a)⟩ ∈ B`, i.e. `B` known to be a function with `A` in its domain —
//      two more hypotheses of exactly the kind the generic seed was meant to
//      remove. So the seed stays a **free variable** and the two facts the
//      construction actually spends stay antecedents (`closed::tower_closed`):
//
//          Fin(A,B) := A ⊆ S ∧ ∀a ∈ A. (B(a) ⊆ S ∧ B(a) ∈ ω)
//
//      At `crate::wnat` the seed is then `S := (1+1) ∪ 1` — the fibres are `0`
//      and `1` — which is a great deal smaller and needs no facts about `B` as
//      a set at all. See `witness`.
//
//  (b) `⊢ ∀A ∀B. (Fin(A,B) → closed(A,B,T))`  [closed::tower_closed]
//      The route in the old note is exactly right and every step of it already
//      existed. The one part it called "the only real work" — reading "the
//      members of `f` are exactly the pairs `⟨b,f(b)⟩`" off `is_function` —
//      **was already proved**: `crate::bound::funspace_pairs` is the first half
//      and `Rec::app_of_graph` the second. Nothing new about functions was
//      needed; the file is long only because it moves six nested hypotheses.
//
//  (c) `⊢ ∀c. (S ∈ U(c) → T ⊆ U(c))`          [Inside::tower_subset]
//      As predicted: the tower's membership condition plus `C₁`.
//
//  (d) `⊢ ∀A ∀B ∀c. ((Fin(A,B) ∧ S ∈ U(c)) → W(A,B,U(c)) ⊆ T)` [WMem]
//      One application of `w_induction` (W2). Three lines, as predicted, and
//      **not** an induction over `wtype::rect`.
//
//  (e) `⊢ ∀c. ((S ∈ U(c) ∧ ω ∈ U(c)) → T ∈ U(c))`  [Inside::tower_mem]
//      As predicted, including the absence of a second Replacement instance:
//      `iter(S)` is already the set of pairs `⟨n,Vₙ⟩`, `crate::funcs::snd_in_union2`
//      puts `Vₙ` in `⋃⋃iter(S)` and one more `⋃` reaches the members of the
//      stages. **`ω ∈ U(c)` is spent exactly here and nowhere else**, in
//      `crate::bound::least_universe_funspace_mem` at `x := ω`.
//      One lemma had to be added that `crate::recursion` does not export:
//      `Inside::graph_pair`, `⊢ ∀n ∈ ω. ⟨n,Vₙ⟩ ∈ iter(S)` — R3 gives *some* `b`
//      and R2 plus `app_of_graph` identifies it as `app(iter(S),n)`.
//
//  (f) `⊢ ∀A ∀B ∀c ∀d. (((Fin(A,B) ∧ S ∈ U(c)) ∧ (S ∈ U(d) ∧ ω ∈ U(d)))
//                          → W(A,B,U(c)) ∈ U(d))`   [WMem::w_in_universe]
//      `Level::sub` at (d) and (e). Note the **two** universes: `c` is the
//      bound the W-type is carved out of, `d` is where it lives, and they
//      cannot be identified — at `c = d = A` the antecedent `ω ∈ U(A)` is
//      refutable, which is the whole content of the correction above.
//
//  (g) `⊢ W(1+1, B, U(1+1)) ∈ U(ω)`, i.e. `⊢ ⟦N⟧ ∈ U₁`  [NatUniverse::nat_in_u1]
//      At closed terms, no hypothesis. The obligations and what they cost:
//        * `1 ∈ ω` — one Extensionality, `1 = {∅} = ∅ ∪ {∅} = succ 0`, exactly
//          as the old note predicted. It is the **only** equality-of-sets step
//          in the whole chain.
//        * `Fin(A,B)` — the case analysis on `a ∈ 1+1`, `sum_cases` plus
//          `unit_eta` plus the two `rec₊` computation rules.
//        * `S ∈ U(1+1)` — `A ∈ U(A)`, `∅ ∈ U(A)`, pairing, binary union.
//        * `S ∈ U₁` — this needs `1 + 1 ∈ U₁`, which the old note did not list.
//          It is **not** hard and needs no Replacement: `A + B` *abbreviates*
//          `({∅} × A) ∪ ({1} × B)`, so `sum_def` plus `Level`'s pairing,
//          product and binary-union closures do it in five instantiations and
//          one rewrite. Going through the sum's membership condition instead
//          would have needed an Extensionality and a case analysis; the
//          defining equation is the short way and it is easy to miss.
//        * `ω ∈ U₁` — `Level::omega_mem`, free.
//      Non-vacuity is `Nat::zero`, `Nat::succ` and `Nat::zero_ne_succ` at the
//      same closed terms, so `N` is provably infinite and `N ∈ U₁` is not a
//      statement about a set with fewer than two elements. That it is *not*
//      also a member of its own bound `U(1+1)` is the refutation recorded
//      above, and is why the deliverable was worth restating before proving.
//
// ── WHAT IS NOT HERE ────────────────────────────────────────────────────────
//
//   * **Only finitely branching W-types.** `bounded` proves `bnd(k)` for
//     `k ∈ ω`, so `Fin(A,B)` demands `B(a) ∈ ω` on the nose. A fibre merely
//     *equinumerous* to a natural — a sum of units, say — needs `bnd`
//     transported along a surjection, one lemma that is not written. Every
//     inductive in scope has von Neumann naturals as fibres (`wnat`, `wlist`),
//     so nothing currently needs it.
//   * **`crate::wlist` is not instantiated.** `List α` is this construction
//     with `A = 1 + α` and a free `α`; the seed would be `A ∪ 1` again and the
//     obligations are the same three, but `α ∈ U(c)` becomes a hypothesis.
//     Nothing in the chain assumes `A` closed — `witness` is the only file that
//     fixes concrete terms — so this is an afternoon, not a redesign. What that
//     afternoon buys is measured and small; see `MEASUREMENTS.md`, "`⟦T⟧ ∈
//     ⟦Type 0⟧` wired into the checker".
//
// ── WHAT THE CHECKER NOW CONSUMES — 2026-08-01 ──────────────────────────────
//
// `checker/src/tg.rs` uses `NatMem::over` and `enums::enum_in_u1`, so
// `⟦N⟧ ∈ ⟦Type 0⟧`, `⟦Bool⟧ ∈ ⟦Type 0⟧`, `⟦Unit⟧` and `⟦Empty⟧` are discharged
// rather than assumed. Two things had to change here for that, and both are
// plumbing rather than mathematics:
//
//   * `Chain::over` (`ambient`) builds the chain over a **caller-supplied**
//     tower, `Wtype` and `Bound`. `Chain::new` mints its own, and a theorem
//     about those symbols says nothing about the checker's — the failure mode
//     is silent, which is why the constructor guards on the pairing, the power
//     set and `U(·)` being shared. `Sums`, `Wtype`, `Bound`, `Space`, `Peano`
//     and `OmegaCore` became `Clone` for it: cloning one copies the *same*
//     symbols, which is the whole point.
//   * `NatMem::over` is `NatUniverse::new` minus the `Nat` it used to build.
//     `Cases::new` mints a fresh `rec₊`, so a second `Nat` has a different
//     fibre family and hence a different `W`; the client's own `N` has to be
//     handed in.
//
// `enums` is the same argument where the fibres are empty, and it is shorter
// rather than merely different — no case analysis, and the seed is the tag set
// itself. It reuses `NatMem::tags_in_u1` for `Bool`'s `(1+1) ∈ U₁`.

// ── PRACTICALITIES THAT COST TIME ───────────────────────────────────────────
//
//   * **One chain.** `Tower::new` and `Rec::new` each mint their own `∅`, `ω`
//     and `𝒫`, and theorems about one say nothing about the other. `Peano` was
//     not `Clone` when this was written — it is now, along with `Sums`, `Wtype`,
//     `Bound`, `Space` and `OmegaCore` (see the 2026-08-01 section above), so
//     the dance below is no longer forced. The assembly as it was written: build
//     the `Tower`, clone off `space.lu`,
//     `space.pow`, `space.pow_ax`, `t.pow`, `t.bin_union` and `sums.ap`, then
//     `let Tower { peano, .. } = t;` and rebuild `Rec { ap, peano,
//     app_of_graph }`. **This is now `cumul::Chain::new`** — call that rather
//     than rediscovering it. Note the `Step` must be built with
//     `space.pow`, *not* with a fresh `power(env)` and not with
//     `peano.core.pow` — `OmegaCore` mints a third one.
//   * `inst_all` only strips **leading** `∀`s. `Stages::directed` is
//     `∀n. (n ∈ ω → ∀m. …)`, so the second variable needs
//     `Thm::ax_inst` on the consequent after the first `hyp_mp`, not a second
//     term in `inst_all`.
//   * `crate::funspace::discharge` is the right tool for every `∃`; `bounded`
//     runs it three deep (the stage from the induction hypothesis, the stage of
//     the extra point, and the merge) and each is one line.
//   * Nothing in this module needed a new axiom, and `kernel/` is untouched.
