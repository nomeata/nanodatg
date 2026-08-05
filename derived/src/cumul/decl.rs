//! **`⊢ ⟦T⟧ ∈ Uₙ` from a `DeclSpec`** — the general inductive carrier
//! ([`crate::inductive`]) multiplied by the cumulative hierarchy
//! ([`crate::cumul`]), **at any rung of the tower**.
//!
//! # Interface
//!
//! Writing `A` for [`Inductive::tags`], `B` for the fibre family, `T` for the
//! fibre codomain `{finord(m₀)} ∪ (… ∪ ∅)`, `Uₙ` for the tower rung
//! ([`crate::tower::Rung`]) the declaration is to land in, and
//!
//! ```text
//! S := A ∪ ⋃T                       the tower seed
//! ```
//!
//! [`DeclUniverse::over_at`] takes an [`IndChain`], the
//! [`Machine`](crate::inductive::Machine) the declaration was translated over,
//! an [`Inductive`], an optional antecedent `H`, a [`Rung`] and
//! `⊢ [H →] A ∈ Uₙ`, and returns
//!
//! ```text
//! ⊢ A ⊆ S ∧ ∀a. (a ∈ A → B(a) ⊆ S)                   [fin]              at S
//! ⊢ S ∈ U({A,T})                                     [seed_in_bound]
//! ⊢ T ∈ Uₙ     ⊢ ⋃T ∈ Uₙ                             [target_in_u1, union_target_in_u1]
//! ⊢ [H →] S ∈ Uₙ                                     [seed_in_u1]
//! ⊢ [H →] W(A, B, U({A,T})) ∈ Uₙ                     [wty_in_u1]
//! ⊢ ∀p⃗. ([H →] ind(p⃗) ∈ Uₙ)                          [ty_in_u1]
//! ```
//!
//! [`DeclUniverse::over`] is `over_at` at `ic.chain.u1`, i.e. `n = 1`, which is
//! `⟦Type 0⟧`. The field names still say `u1` because that is what two
//! consumers already read them by; [`DeclUniverse::universe`] is the term the
//! memberships are actually in, and comparing against it is the check a caller
//! owes itself.
//!
//! The first three are **unconditional at every declaration**, `H` or no `H`:
//! the fibre condition and the bound-side seed membership cost the caller
//! nothing. The last three carry whatever `H` the tag membership carried, and
//! nothing else.
//!
//! # Step (f) is the **path route**, and what its five clauses cost
//!
//! [`crate::wpath::w_in_universe_paths`] is what puts `W` in `Uₙ`, at
//! `Q := T` — *not* [`super::WMem::w_in_universe_bnd`], which asked for
//! [`super::bnd`] at every fibre value and is therefore unreachable at an
//! infinitely branching declaration. `bnd` is not weakened here; it is **never
//! stated**. Four of the five clauses are discharged outright:
//!
//! | obligation | how, and what it costs |
//! |---|---|
//! | `closed(A,B,U({A,T}))` | [`Inductive::closed`], unconditional, and already built by [`crate::inductive::carrier`]. **No fibre condition** — [`crate::bound::least_universe_closed`] has none. |
//! | `amb(A,B,T)` | [`super::tower_amb`] at the fibre half of `fin`, `∀a ∈ A. B(a) ⊆ S`. That half is [`Fibre::values_in_target`](crate::fibre::Fibre::values_in_target) followed by one elimination over `T`, whose `n` cases are `⊢ vᵢ ∈ T` (a subset of `⋃T`, hence of `S`). **No case analysis on the tag sum, and no mention of the rung at all.** |
//! | `T ∈ Uₙ` | [`super::Inside::tower_mem`], at `S ∈ Uₙ` and `ω ∈ Uₙ`. The latter is [`crate::tower::Rung::omega_mem`], which [`crate::tower::Tower::at`] supplies at **every** `n ≥ 1`, and this is the only place it is spent. |
//! | `W ⊆ Uₙ` | `W ⊆ U({A,T})` is W1, free; `U({A,T}) ⊆ Uₙ` is [`crate::bound::least_universe_subset`] at `{A,T} ∈ Uₙ` and [`crate::universe::least_universe_is_universe`]. **The one new set-theoretic step in the route**, and the pairing it wants is `A ∈ Uₙ` and `T ∈ Uₙ`, both already in hand. |
//! | `A ∈ Uₙ` | **the one antecedent**, and it is [`super::tags`]' business. |
//!
//! `S ∈ U({A,T})` and `S ∈ Uₙ` are still derived — the first because `A` and
//! `T` are *members of the bound's seed*, so `U({A,T})`'s transitivity puts
//! both in it; the second because `⋃T ∈ Uₙ` is free
//! ([`crate::isum::isum_in_universe`] is stated at whatever seed it is given)
//! and `A ∈ Uₙ` is carried. Both are exported, and `S ∈ Uₙ` feeds `T ∈ Uₙ`.
//!
//! So the antecedent list at `Type n` is **`A ∈ Uₙ` and nothing else** — the
//! same single item, moved up a rung. Nothing in the table above grows a term
//! with `n`, because every ingredient is either rung-free (`closed`, `amb`, the
//! bound) or already stated `∀c`/`∀d` (the closure clauses, and
//! `w_in_universe_paths`, whose universe seed is its last argument). The
//! `n = 1` path is therefore literally the same derivation and costs nothing
//! extra: [`DeclUniverse::over`] is one line, and the
//! specialisation-stays-cheap pattern is the one [`crate::cumul`] already uses
//! for the `∈ ω` form.
//!
//! **What *does* depend on the declaration is the fibre side**, and it is the
//! one obligation this file cannot discharge itself. Both rows above read every
//! constructor's fibre value, and §5.2 makes that value `Sum_{mᵢ}(A⃗ᵢ)` at the
//! summands its recursive arguments' domains produce. When every domain is
//! empty every `Aᵢⱼ` is `1` and both facts are free; otherwise they are inputs
//! — see [`DeclUniverse::over_at_general`] and [`FibreFacts`].
//!
//! `A ∈ Uₙ` is not an artefact of this route: `fin` forces `A ⊆ S`, `S ∈ Uₙ`
//! is what the size argument spends, and `C₂` turns `A ⊆ S ∈ Uₙ` back into
//! `A ∈ Uₙ`. No seed removes it. For a closed declaration
//! [`super::tags::nullary_summands_at`] discharges it at whatever rung it is
//! asked for and the whole chain comes out unconditional; for `List α` it is
//! `α ∈ U₁`, carried as `H`.
//!
//! # Getting the two inputs at a rung above `U₁`
//!
//! Neither is this file's to build, and neither needs a new derivation:
//!
//! * **The [`Rung`]** is [`crate::tower::Tower::at`] `(n)`, on the *same*
//!   `Tower` that was handed to [`super::Chain::over`] /
//!   [`IndChain::over`](super::IndChain::over). A rung from any other tower is
//!   refused: `over_at` checks that `Uₙ` is this chain's own `U(·)` applied to
//!   the rung's seed, and that the rung's `∅` and `ω` memberships are about
//!   this chain's `∅` and this chain's `ω`.
//! * **`⊢ [H →] A ∈ Uₙ`** is [`super::tags::tags_at`]'s `⊢ [H →] A ∈ U_{n₀}`
//!   raised by [`crate::tower::Cumul`]. Unconditional, that is
//!   `cumul.raise(n₀, n, &tags)`; under an `H` the antecedent lives in the
//!   conclusion rather than in a `Γ`, so it is one syllogism,
//!   `syl(&tags, &inst_all(cumul.lift(n₀, n)?, &[A])?)`. There is deliberately
//!   no wrapper for the second: it is a line, and a wrapper would have to guess
//!   `A`.
//!
//! # Which rung to run the summand/tag pipeline at
//!
//! The whole summand/tag pipeline ([`super::sigma_n`], [`super::sigma`],
//! [`super::tags`]) is generalised to an arbitrary [`Rung`], with the `U₁`
//! entry points kept as one-line `n = 1` instances. That does **not** overturn
//! the reasoning this header used to record ("raising the finished `A ∈ U₁` is
//! strictly cheaper than re-running `k` Replacement instances one rung
//! higher"); it turns that reasoning from a hard-coded choice into a
//! caller-side parameter, and the reasoning is what decides the parameter:
//!
//! * running the pipeline at rung `n` costs **the same** as running it at rung
//!   1 — every lemma it spends is a `∀c` statement instantiated at the rung's
//!   own seed;
//! * what is not free is running it **twice**. Each outer telescope level calls
//!   [`crate::ext::image_symbol_n`], which mints a **fresh function symbol and
//!   a fresh Replacement axiom instance** in the `Env`; two runs for one
//!   declaration leave `k−1` redundant symbols in the signature, not merely
//!   duplicated work;
//! * [`crate::tower::Cumul::raise`] is one `inst_all` plus one `mp` and mints
//!   nothing.
//!
//! So the rule is: **run the pipeline exactly once, at
//! `n₀ := max(1, max over the fields of the rung that field's type lives in)`,
//! and [`crate::tower::Cumul::raise`] the finished `A ∈ U_{n₀}` to whatever
//! rung the declaration is placed at.** A field membership available *below*
//! `n₀` is raised individually first, which is again one `mp`. For a
//! declaration all of whose fields are small, `n₀ = 1` — the old behaviour
//! exactly, and that is the sense in which existing callers pay nothing.
//!
//! Hence **one** generalised pipeline and not two entry points. Two would offer
//! only the binary choice "`U₁`" versus "the rung the declaration is placed
//! at", and the actual decision is over `n₀`, which is in general neither:
//! `Prod.{1,0}` (fields `α ∈ U₂`, `β ∈ U₁`) has `n₀ = 2` and may be placed at
//! any rung ≥ 2. Generalising is also not merely an optimisation: a field whose
//! type is `Type 0` has the *value* `U₁`, whose membership `U₁ ∈ U₂` is
//! [`Rung::mem_below`] — there is no `U₁` obligation for it at all, and raising
//! only goes upward.
//!
//! # The seed question, decided
//!
//! There are **two** seeds and they answer to different constraints.
//!
//! * The **bound** seed `c`, in `W(A,B,U(c))`. [`crate::inductive::carrier`]
//!   takes `c := {A,T}`; [`crate::isum::finord_in_universe`] has since made the
//!   *tight* seed `c := A` reachable, since the fibre obligation
//!   `finord(mᵢ) ∈ U(A)` is now available. **Keep `{A,T}`.** The tight seed
//!   buys nothing here and costs something: this file needs `S ∈ U(c)`, hence
//!   `T ∈ U(c)` and `A ∈ U(c)`, and at `c = {A,T}` both are one use of
//!   transitivity at a member of the seed, with no dependence on `mᵢ` at all.
//!   At `c = A` the same two obligations become `A ∈ U(A)` (free) and
//!   `T ∈ U(A)` (`finord_in_universe` plus `U(A)`'s pairing and binary-union
//!   closures, `n + 1` steps). So the workaround is not merely retained for
//!   compatibility — it is the cheaper of the two on this path, and the
//!   argument in `carrier.rs`'s header ("four uses of one lemma and no case
//!   analysis") survives the obstacle being removed.
//! * The **tower** seed `S`, which is this file's own choice, and it is
//!   `A ∪ ⋃T`. `⋃T` rather than `T` because `fin` wants `B(a) ⊆ S`, and
//!   `B(a)` is a *member* of `T`; `⋃T` is exactly the set its members are
//!   subsets of, and the union axiom supplies that with no case analysis. This
//!   is [`super::NatUniverse`]'s `A ∪ 1` generalised — there the one non-empty
//!   fibre is `1` and `⋃T` is `⋃{0,1} = 1` — and it is *not* the generic
//!   `A ∪ ⋃⋃⋃B` the closing note of [`crate::cumul`] proposed and rejected: it
//!   needs nothing about `B` as a set of pairs.
//!
//! # Non-vacuity
//!
//! The set placed in `U₁` is provably inhabited by *distinct* elements
//! whenever the declaration has two constructors:
//! [`Inductive::distinct`] is `⊢ ¬(ctor_i(…) = ctor_j(…))` and
//! [`Ctor::mem`](crate::inductive::Ctor::mem) puts both in the carrier. For a
//! recursive declaration [`Ctor::inj`](crate::inductive::Ctor::inj) makes it
//! infinite. `derived/tests/cumul.rs` cashes both at `Bool` and at `N`. A
//! membership theorem about `∅` would satisfy nothing here.
//!
//! # Nothing here is an axiom
//!
//! No symbol is introduced. Every caller-supplied theorem is checked for the
//! conclusion it must have **and** for an empty hypothesis set — a `Γ ⊢` has
//! the conclusion the real theorem has, composes through `mp` with `Γ` intact,
//! and would arrive at a statement this module advertises without one.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::finset::FinSet;
use crate::funcs::{union_intro, Sets};
use crate::funspace::bin_union;
use crate::inductive::{Inductive, Machine};
use crate::isum::isum_in_universe;
use crate::sums::Sums;
use crate::tower::Rung;
use crate::{
    a1i, all_unconditional, and_intro, eq_symm, eq_symm_imp, establishes, ex_falso, gen_all,
    hyp_or_elim, iff_mp, inst_all, mpd_const, singleton, syl, upair_members,
};

use super::apparatus::IndChain;
use super::opt::Ctx;
use super::curry;

/// **What a caller owes about each constructor's fibre summands.**
///
/// One entry per constructor, and within it one per that constructor's
/// recursive slots, in the order
/// [`fibre_summands`](crate::inductive::carrier::fibre_summands) produces
/// them — which is the order [`RecArg::summands`](crate::recarg::RecArg) holds
/// and the order the fibre value sums.
///
/// **One** fact per summand, and it used to be two. The other was
/// `⊢ bnd(Aᵢⱼ)`, and it is gone rather than weakened — see
/// [`DeclUniverse::over_at_general`] and [`mod@super::wpaths`].
///
/// Unconditional, and that is [`crate::isum::isum_in_universe`]'s
/// requirement rather than a convenience: it refuses a theorem with a
/// non-empty hypothesis set *and* one whose conclusion is an implication.
#[derive(Clone)]
pub struct FibreFacts {
    /// `mem[i][j] : ⊢ Aᵢⱼ ∈ Uₙ`, at the rung the declaration is placed in.
    pub mem: Vec<Vec<Thm>>,
}

/// A translated declaration's carrier, placed in `Uₙ`.
pub struct DeclUniverse {
    /// The tower seed `S = A ∪ ⋃T`.
    pub seed: Term,
    /// The term `Uₙ` every membership below is in — [`Rung::set`] of the rung
    /// [`DeclUniverse::over_at`] was called at, and `U₁` for
    /// [`DeclUniverse::over`]. Carried so that a caller checks the rung it got
    /// rather than the one it meant to ask for.
    pub universe: Term,
    /// `⊢ T ∈ Uₙ` — the fibre codomain is small.
    pub target_in_u1: Thm,
    /// `⊢ ⋃T ∈ Uₙ`.
    pub union_target_in_u1: Thm,
    /// `⊢ A ⊆ S ∧ ∀a. (a ∈ A → B(a) ⊆ S)` at `S` — **unconditional at every
    /// declaration**, and independent of the rung.
    ///
    /// This used to be `Fin⁺`, with `bnd(B(a))` in the second conjunct, and it
    /// was the antecedent step (f) spent. The path route wants only the `⊆`
    /// half ([`super::tower_amb`]), and that half is provable at *any* fibre;
    /// what is left is [`super::wpaths::fin_sub`].
    pub fin: Thm,
    /// `⊢ S ∈ U({A,T})` — the seed is inside the *bound*. Unconditional, and
    /// independent of the rung.
    pub seed_in_bound: Thm,
    /// `⊢ [H →] S ∈ Uₙ`.
    pub seed_in_u1: Thm,
    /// **`⊢ [H →] W(A,B,U({A,T})) ∈ Uₙ`**, before the abbreviation.
    pub wty_in_u1: Thm,
    /// **`⊢ ∀p⃗. ([H →] ind(p⃗) ∈ Uₙ)`** — the statement a checker consumes.
    pub ty_in_u1: Thm,
}

impl DeclUniverse {
    /// Put a translated declaration's carrier in `U₁` — [`DeclUniverse::over_at`]
    /// at `ic.chain.u1`, and nothing else.
    ///
    /// `tags_in_u1` must be `⊢ A ∈ U₁` when `hyp` is `None` and `⊢ H → A ∈ U₁`
    /// when it is `Some(H)`. Every guard is `over_at`'s.
    pub fn over(
        env: &mut Env,
        ic: &IndChain,
        mach: &Machine,
        ind: &Inductive,
        hyp: Option<&Formula>,
        tags_in_u1: &Thm,
    ) -> Option<DeclUniverse> {
        DeclUniverse::over_at(env, ic, mach, ind, hyp, &ic.chain.u1, tags_in_u1)
    }

    /// Put a translated declaration's carrier in `Uₙ`, at any rung of the
    /// tower.
    ///
    /// `mach` must be the apparatus `ind` was built over
    /// ([`Inductive::is_over`]) and must be over `ic`'s signature
    /// ([`IndChain::is_over`]) — over any other, every step below resolves
    /// against a different `Inj`, `upair` and `W`, and the theorem returned
    /// would be true of a set that is not this carrier.
    ///
    /// `tags_in_un` must be `⊢ A ∈ Uₙ` when `hyp` is `None` and `⊢ H → A ∈ Uₙ`
    /// when it is `Some(H)`, at [`Inductive::tags`] and at `rung`'s set. Both
    /// the conclusion and the **empty hypothesis set** are checked, on the way
    /// in and on the way out.
    ///
    /// `rung` must be a rung of the **same** tower the chain was built over.
    /// Three comparisons enforce it, and they are checks on *statements*, not
    /// on symbols: `Uₙ` must be this chain's `U(·)` applied to the rung's own
    /// seed, and the rung's `⊢ ∅ ∈ Uₙ` and `⊢ ω ∈ Uₙ` must be about this
    /// chain's `∅` and this chain's `ω`. A rung from a second tower in the
    /// same `Env` fails the first of them, and a `Rung` whose theorems have
    /// drifted from its `set` field fails wherever it is used, because every
    /// use below is compared against a formula rebuilt at `Uₙ`.
    ///
    /// See the module header for how a caller obtains `rung` and
    /// `tags_in_un`; neither costs a new derivation.
    pub fn over_at(
        env: &mut Env,
        ic: &IndChain,
        mach: &Machine,
        ind: &Inductive,
        hyp: Option<&Formula>,
        rung: &Rung,
        tags_in_u1: &Thm,
    ) -> Option<DeclUniverse> {
        DeclUniverse::over_at_general(env, ic, mach, ind, hyp, rung, tags_in_u1, None)
    }

    /// [`DeclUniverse::over_at`] with the **per-summand** fibre facts supplied.
    ///
    /// §5.2's recursive-argument rule gives the `j`-th recursive slot of the
    /// `i`-th constructor the fibre summand `Aᵢⱼ = Σ(z::γᵢⱼ)`, so the fibre
    /// *value* is `Sum_{mᵢ}(A⃗ᵢ)`
    /// ([`fibre_values`](crate::inductive::carrier::fibre_values)). One reader
    /// below needs a fact about each summand and cannot compute it:
    ///
    /// ```text
    /// fibres.mem[i][j]  ⊢ Aᵢⱼ ∈ Uₙ                     for  `T ∈ Uₙ`
    /// ```
    ///
    /// **There used to be a second**, `⊢ bnd(Aᵢⱼ)`, for `Fin⁺` and hence for
    /// step (f). It is gone: step (f) is now
    /// [`crate::wpath::w_in_universe_paths`], which says nothing about the
    /// fibres, and the surviving `⊆` half of [`DeclUniverse::fin`] is provable
    /// at any fibre without an input. That is the whole of why an infinitely
    /// branching declaration reaches this function at all.
    ///
    /// `None` means **every summand is `1`** — every `γᵢⱼ` empty, so every
    /// fibre value is literally `finord(mᵢ)` — and this file supplies the fact
    /// itself, from [`SumClosure::unit`](crate::isum::SumClosure). That is what
    /// [`DeclUniverse::over_at`] passes, so no existing caller changes and none
    /// pays anything. A declaration with a non-empty `γ` and `None` here is
    /// **refused**, not silently mis-placed: `isum_in_universe` checks each
    /// input at the summand it is used at.
    ///
    /// The list is checked to have one entry per constructor and one entry per
    /// that constructor's recursive slots, and every theorem is checked at its
    /// own summand for the conclusion it must have **and** for an empty
    /// hypothesis set.
    ///
    /// # Why the fibre facts carry no `H`, when the tag membership does
    ///
    /// **The reason has changed, and it is now weaker than it was.** It used to
    /// be that `H` is the conjunction of the *parameters'* typings, that a
    /// summand needing it is one mentioning a parameter, and that `bnd` at a
    /// parameter is not merely unproved but **refutable** (`α := ⟦Nat⟧`) — so
    /// the two obligations stood or fell together and requiring both
    /// unconditional lost nothing true.
    ///
    /// With `bnd` gone that argument is gone with it. What remains is
    /// structural rather than mathematical: [`crate::isum::isum_in_universe`]
    /// refuses an input with a non-empty hypothesis set *or* with an
    /// implication for a conclusion, so `Aᵢⱼ ∈ Uₙ` must arrive outright at the
    /// place it is spent. `Aᵢⱼ ∈ Uₙ` **is** discharge-able under an `H` — that
    /// is the difference — so this requirement is now *re-openable*, and
    /// re-opening it is what a parameter-domain declaration
    /// (`inductive Tree (α) | node : (α → Tree α) → Tree α`) needs. See
    /// SCOPING.md §14.5. It is also what keeps [`DeclUniverse::fin`]
    /// unconditional at every declaration, as this file's header promises.
    #[allow(clippy::too_many_arguments)]
    pub fn over_at_general(
        env: &mut Env,
        ic: &IndChain,
        mach: &Machine,
        ind: &Inductive,
        hyp: Option<&Formula>,
        rung: &Rung,
        tags_in_u1: &Thm,
        fibres: Option<&FibreFacts>,
    ) -> Option<DeclUniverse> {
        if !ic.is_over(mach) || !ind.is_over(mach) || !tags_in_u1.hyps().is_empty() {
            return None
        }
        let ctx = Ctx(hyp.cloned());
        let s = &mach.wt.sums;
        let sets: Sets = s.ap.sets.clone();
        let (r, st, u1) = (&ic.chain.r, &ic.chain.st, rung);
        let lu = ic.chain.lu();

        // The rung is this chain's own: its `∅` is this `Sums`' `∅` and its
        // `ω` is this chain's `ω`. `establishes` carries the hypothesis leg for
        // those two; the three closure schemas are checked for it beside them.
        // `rests_on_nothing` would catch a hypothetical field at the very end,
        // but only as a nameless failure of the whole composition — this is the
        // same check made where the input arrives, on the four fields of `rung`
        // this file reads and on nothing else.
        if !establishes(&u1.empty_mem, &Formula::mem(s.zero(), u1.set.clone()))
            || !establishes(&u1.omega_mem, &Formula::mem(r.omega(), u1.set.clone()))
            || !all_unconditional(&[&u1.pairing, &u1.union, &u1.bin_union])
        {
            return None
        }

        let tags = ind.tags.clone();
        let fam = ind.fibre.fam.clone();
        let target = ind.fibre.target.clone();
        let values = ind.fibre.values.clone();

        // ── the fibre summands, and the facts about them ────────────────────
        //
        // Read off the *recursive-argument functions* rather than recomputed
        // from the spec: `RecArg::summands` is the list `fibre_values` summed,
        // so checking `Sum_{mᵢ}(A⃗ᵢ)` against `Fibre::values[i]` is what makes
        // this the declaration's own decomposition and not a second one that
        // happens to agree. A declaration whose fibre value is not the sum of
        // its own recursive arguments' summands is refused here.
        let mut fib: Vec<Vec<Term>> = Vec::with_capacity(values.len());
        for (i, v) in values.iter().enumerate() {
            let a = ind.recargs.get(i)?.summands.clone();
            if mach.syms.sum(&a).as_ref() != Some(v) {
                return None
            }
            fib.push(a);
        }
        let fib_mem: Vec<Vec<Thm>> = match fibres {
            Some(f) => {
                if f.mem.len() != fib.len() {
                    return None
                }
                f.mem.clone()
            }
            None => {
                let um = inst_all(&ic.clo.unit, std::slice::from_ref(&u1.seed))?;
                fib.iter().map(|a| vec![um.clone(); a.len()]).collect()
            }
        };

        if *tags_in_u1.concl() != ctx.wrap(Formula::mem(tags.clone(), u1.set.clone()))
            || u1.set != Term::apply(lu, vec![u1.seed.clone()])
        {
            return None
        }

        let ut = sets.union_of(target.clone());
        let seed = bin_union(&sets, tags.clone(), ut.clone());

        // ── the two halves of `S`, as inclusions ────────────────────────────
        let (bu_left, bu_right) = crate::funspace::pow_pow::mem_bin_union(env, &sets)?;
        let zv = env.fresh_var();
        let tz = Term::var(zv);
        let tags_sub = Thm::gen(zv, &inst_all(&bu_left, &[tags.clone(), ut.clone(), tz.clone()])?);
        let ut_sub = Thm::gen(zv, &inst_all(&bu_right, &[tags.clone(), ut.clone(), tz.clone()])?);
        if *tags_sub.concl() != kernel::thm::subset(env, tags.clone(), seed.clone())
            || *ut_sub.concl() != kernel::thm::subset(env, ut.clone(), seed.clone())
        {
            return None
        }

        // ── `A ⊆ S ∧ ∀a ∈ A. B(a) ⊆ S`: one elimination over `T` ───────────
        //
        // No case analysis on `A`, and — since `bnd` went — no input at all.
        // The whole of what step (f) asks about the fibres is that they lie in
        // the seed, which is a fact about `T` rather than about their size.
        let hole = env.fresh_var();
        let th = Term::var(hole);
        let goal_sub = kernel::thm::subset(env, th.clone(), seed.clone());

        let mut cases_sub = Vec::with_capacity(values.len());
        for (i, v) in values.iter().enumerate() {
            // `vᵢ ⊆ ⋃T ⊆ S`, from `⊢ vᵢ ∈ T` and the union axiom.
            let into_union = Thm::mp(
                &curry(&union_intro(env, &sets, target.clone(), v.clone(), tz.clone())?)?,
                &ind.fibre.value_mem[i],
            )?;
            let v_sub_ut = Thm::gen(zv, &into_union);
            if *v_sub_ut.concl() != kernel::thm::subset(env, v.clone(), ut.clone()) {
                return None
            }
            let v_sub = Thm::mp(
                &inst_all(&st.step.subset_trans, &[v.clone(), ut.clone(), seed.clone()])?,
                &and_intro(&v_sub_ut, &ut_sub),
            )?;
            if *v_sub.concl() != goal_sub.clone().subst(hole, v) {
                return None
            }
            cases_sub.push(v_sub);
        }
        let bu_elim = super::step::mem_bin_union_elim(env, &sets)?;
        let over_target_sub =
            fin_elim(env, s, &bu_elim, &values, hole, &goal_sub, &cases_sub)?;

        let av = env.fresh_var();
        let ta = Term::var(av);
        let fibres_sub = Thm::gen(
            av,
            &syl(
                &inst_all(&ind.fibre.values_in_target, std::slice::from_ref(&ta))?,
                &inst_all(
                    &over_target_sub,
                    std::slice::from_ref(&r.apply(fam.clone(), ta.clone())),
                )?,
            )?,
        );
        let fin = and_intro(&tags_sub, &fibres_sub);
        if *fin.concl() != super::wpaths::fin_sub(env, r, st, &seed, &tags, &fam) {
            return None
        }

        // ── `S ∈ U({A,T})`, free from the bound's own seed ──────────────────
        let bound_seed = ind.seed.clone();
        let seed_in_lu = inst_all(&mach.mem_lu, std::slice::from_ref(&bound_seed))?;
        let trans = inst_all(&mach.trans_lu, std::slice::from_ref(&bound_seed))?;
        let widen = inst_all(&trans, std::slice::from_ref(&bound_seed))?;
        let widen = Thm::mp(&widen, &seed_in_lu)?;
        let (a_in_seed, t_in_seed) = upair_members(&sets.up_ax, &tags, &target)?;
        let a_in_bound =
            Thm::mp(&inst_all(&widen, std::slice::from_ref(&tags))?, &a_in_seed)?;
        let t_in_bound =
            Thm::mp(&inst_all(&widen, std::slice::from_ref(&target))?, &t_in_seed)?;
        let ut_in_bound = Thm::mp(
            &inst_all(&ic.chain.union_all, &[bound_seed.clone(), target.clone()])?,
            &t_in_bound,
        )?;
        let seed_in_bound = Thm::mp(
            &inst_all(&ic.chain.bin_union_all, &[bound_seed.clone(), tags.clone(), ut.clone()])?,
            &and_intro(&a_in_bound, &ut_in_bound),
        )?;
        if *seed_in_bound.concl() != Formula::mem(seed.clone(), ind.bound.clone()) {
            return None
        }

        // ── `T ∈ U₁`, `⋃T ∈ U₁`, `S ∈ U₁` ──────────────────────────────────
        let mut target_in_u1 = u1.empty_mem.clone();
        for i in (0..values.len()).rev() {
            let v_in = isum_in_universe(
                env,
                &ic.clo,
                s,
                &mach.syms,
                &u1.seed,
                &fib[i],
                &fib_mem[i],
            )?;
            if *v_in.concl() != Formula::mem(values[i].clone(), u1.set.clone()) {
                return None
            }
            let sing = Thm::mp(
                &inst_all(&u1.pairing, &[values[i].clone(), values[i].clone()])?,
                &and_intro(&v_in, &v_in),
            )?;
            target_in_u1 = Thm::mp(
                &inst_all(
                    &u1.bin_union,
                    &[singleton(sets.up, values[i].clone()), FinSet::of(s, &values[i + 1..])],
                )?,
                &and_intro(&sing, &target_in_u1),
            )?;
        }
        if *target_in_u1.concl() != Formula::mem(target.clone(), u1.set.clone()) {
            return None
        }
        let union_target_in_u1 =
            Thm::mp(&inst_all(&u1.union, std::slice::from_ref(&target))?, &target_in_u1)?;
        let seed_in_u1 = ctx.mp(
            &ctx.lift(&inst_all(&u1.bin_union, &[tags.clone(), ut.clone()])?),
            &ctx.and(tags_in_u1, &ctx.lift(&union_target_in_u1))?,
        )?;

        // ── step (f): the path route, at this declaration's terms ───────────
        //
        // `wpath::w_in_universe_paths` in place of `WMem::w_in_universe_bnd`.
        // The two differ in exactly one thing: this one says nothing about the
        // fibres, so an infinitely branching declaration reaches it.
        let tower = Term::apply(st.tower.tower, vec![seed.clone()]);
        if st.tower_set() != Term::apply(st.tower.tower, vec![Term::var(st.seed)]) {
            return None
        }

        // `amb(A,B,T)` — the tower is a legal ambient for the paths, from the
        // fibre half of `fin` with `bnd` dropped.
        let amb = Thm::mp(
            &inst_all(
                &Thm::gen(st.seed, &ic.chain.paths.tower_amb),
                &[seed.clone(), tags.clone(), fam.clone()],
            )?,
            &fibres_sub,
        )?;

        // `T ∈ Uₙ` — `Inside::tower_mem`, and the only place `ω ∈ Uₙ` is spent.
        let tower_in_u1 = ctx.mp(
            &ctx.lift(&inst_all(
                &Thm::gen(st.seed, &ic.chain.inside.tower_mem),
                &[seed.clone(), u1.seed.clone()],
            )?),
            &ctx.and(&seed_in_u1, &ctx.lift(&u1.omega_mem))?,
        )?;
        if *tower_in_u1.concl() != ctx.wrap(Formula::mem(tower.clone(), u1.set.clone())) {
            return None
        }

        // `W ⊆ Uₙ` — `W ⊆ U({A,T})` is free (W1), and `U({A,T}) ⊆ Uₙ` is
        // leastness at `{A,T} ∈ Uₙ`. **This is the one new line of set theory
        // in the whole wiring**, and `bound::least_universe_subset` is it.
        let bound_in_u1 = ctx.mp(
            &ctx.lift(&inst_all(&u1.pairing, &[tags.clone(), target.clone()])?),
            &ctx.and(tags_in_u1, &ctx.lift(&target_in_u1))?,
        )?;
        if *bound_in_u1.concl() != ctx.wrap(Formula::mem(bound_seed.clone(), u1.set.clone())) {
            return None
        }
        let lu_sub = crate::bound::least_universe_subset(
            env,
            &ic.chain.space.lu_ax,
            &bound_seed,
            &ind.bound,
            &u1.set,
        )?;
        let bound_sub = ctx.mp(
            &ctx.lift(&lu_sub),
            &ctx.and(
                &ctx.lift(&inst_all(
                    &ic.chain.paths.is_universe,
                    std::slice::from_ref(&u1.seed),
                )?),
                &bound_in_u1,
            )?,
        )?;
        let zv2 = env.fresh_var();
        let tz2 = Term::var(zv2);
        let w_body = Formula::imp(
            Formula::mem(tz2.clone(), ind.wty.clone()),
            Formula::mem(tz2.clone(), u1.set.clone()),
        );
        let w_sub_u1 = ctx.gen(
            zv2,
            &w_body,
            &ctx.syl(
                &ctx.lift(&inst_all(
                    &mach.wt.w_subset,
                    &[tags.clone(), fam.clone(), ind.bound.clone(), tz2.clone()],
                )?),
                &ctx.inst(&bound_sub, tz2.clone())?,
            )?,
        )?;
        if *w_sub_u1.concl()
            != ctx.wrap(kernel::thm::subset(env, ind.wty.clone(), u1.set.clone()))
        {
            return None
        }

        let at = inst_all(
            &ic.chain.paths.w_in_universe,
            &[tags.clone(), fam.clone(), ind.bound.clone(), tower, u1.seed.clone()],
        )?;
        let wty_in_u1 = ctx.mp(
            &ctx.lift(&at),
            &ctx.and(
                &ctx.lift(&and_intro(&ind.closed, &amb)),
                &ctx.and(&ctx.and(&w_sub_u1, &tower_in_u1)?, tags_in_u1)?,
            )?,
        )?;
        if *wty_in_u1.concl() != ctx.wrap(Formula::mem(ind.wty.clone(), u1.set.clone())) {
            return None
        }

        // ── and onto the abbreviation `ind(p⃗)` ──────────────────────────────
        let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
        let to_ty = eq_symm(env, &inst_all(&ind.ty_ax, &ps)?)?;
        if *to_ty.concl() != Formula::eq(ind.wty.clone(), ind.carrier.clone()) {
            return None
        }
        let hole2 = env.fresh_var();
        let onto = Thm::mp(
            &Thm::eq_leibniz(
                ind.wty.clone(),
                ind.carrier.clone(),
                hole2,
                Formula::mem(Term::var(hole2), u1.set.clone()),
            ),
            &to_ty,
        )?;
        let ty_in_u1 = gen_all(&ind.params, &ctx.mp(&ctx.lift(&onto), &wty_in_u1)?);

        let out = DeclUniverse {
            seed,
            universe: u1.set.clone(),
            target_in_u1,
            union_target_in_u1,
            fin,
            seed_in_bound,
            seed_in_u1,
            wty_in_u1,
            ty_in_u1,
        };
        out.rests_on_nothing().then_some(out)
    }

    /// Whether every field is a `⊢` with nothing on the left.
    ///
    /// Checked before [`DeclUniverse::over`] returns. An antecedent `H` lives
    /// in the *conclusion*; a sequent hypothesis would be invisible to a
    /// conclusion comparison and would make the final `Thm::gen` over the
    /// declaration's parameters unsound.
    pub fn rests_on_nothing(&self) -> bool {
        [
            &self.target_in_u1,
            &self.union_target_in_u1,
            &self.fin,
            &self.seed_in_bound,
            &self.seed_in_u1,
            &self.wty_in_u1,
            &self.ty_in_u1,
        ]
        .iter()
        .all(|t| t.hyps().is_empty())
    }
}

/// `⊢ ∀x. (x ∈ {v₀} ∪ ({v₁} ∪ (… ∪ ∅)) → φ(x))`, from `⊢ φ(vᵢ)` for each `i`.
///
/// The elimination rule [`crate::finset::FinSet`] does not have — it exports
/// the `n` memberships and the inclusion, which are the two *introductions*.
/// The chain is peeled with the binary union's elimination rule, each singleton
/// names its point, and the base case is `z ∈ ∅`. `φ` is a formula with `hole`
/// free; `cases[i]` must conclude `φ[vᵢ/hole]`, which is checked.
///
/// Everything indexed by `n` happens in Rust: a declaration's constructor count
/// is a `usize` known at translation time, so there is no induction in the
/// object language and none is done.
///
/// `pub(super)` for [`mod@super::carrier_bnd`], which spends it at
/// `φ(x) := x = ∅` to show a non-recursive declaration's fibres are empty.
pub(super) fn fin_elim(
    env: &mut Env,
    s: &Sums,
    mem_bu_elim: &Thm,
    values: &[Term],
    hole: FreeVar,
    phi: &Formula,
    cases: &[Thm],
) -> Option<Thm> {
    if cases.len() != values.len() {
        return None
    }
    let sets = &s.ap.sets;
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let goal = phi.clone().subst(hole, &tx);
    let tails: Vec<Term> = (0..=values.len()).map(|i| FinSet::of(s, &values[i..])).collect();

    // `x ∈ ∅ → φ(x)` — the base of the chain, and the whole of `n = 0`.
    let mut acc = syl(
        &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tx))?,
        &ex_falso(goal.clone()),
    )?;
    for i in (0..values.len()).rev() {
        if *cases[i].concl() != phi.clone().subst(hole, &values[i]) {
            return None
        }
        let sing = singleton(sets.up, values[i].clone());
        let disj = inst_all(mem_bu_elim, &[sing, tails[i + 1].clone(), tx.clone()])?;
        let here = Formula::mem(tx.clone(), tails[i].clone());
        if disj.concl().as_imp()?.0 != here {
            return None
        }
        // `x ∈ {vᵢ} → (φ(vᵢ) → φ(x))`, discharged by the case.
        let left = mpd_const(
            &syl(
                &syl(
                    &iff_mp(&inst_all(&s.ap.mem_sing, &[values[i].clone(), tx.clone()])?)?,
                    &eq_symm_imp(env, tx.clone(), values[i].clone()),
                )?,
                &Thm::eq_leibniz(values[i].clone(), tx.clone(), hole, phi.clone()),
            )?,
            &cases[i],
        )?;
        acc = hyp_or_elim(&disj, &a1i(&left, here.clone()), &a1i(&acc, here))?;
    }
    let out = Thm::gen(xv, &acc);
    (out.hyps().is_empty()
        && *out.concl() == Formula::forall(xv, Formula::imp(Formula::mem(tx, tails[0].clone()), goal)))
    .then_some(out)
}
