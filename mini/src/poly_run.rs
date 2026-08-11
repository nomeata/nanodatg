//! **The de-scheduled pass** — one interpretation per *declaration*, at that
//! declaration's own universe parameters, driven over a whole file.
//!
//! # Interface
//!
//! ```text
//! poly_run::run(&Environment, &[Declaration], &mut Interp) -> PolyLedger
//! ```
//!
//! [`crate::run::Options::poly`] is the switch, `mini --poly` the command line,
//! and [`PolyLedger::rows`] the report. `LEVELPOLY.md` §5.3 step 1's second
//! half: *"a caller that drives `Checker::poly` over a whole file"*. Until this
//! module existed the de-scheduled route had no caller in anger, and every
//! claim about it was a claim about unit tests.
//!
//! # What it does, in one paragraph
//!
//! For each `axiom` / `def` / `theorem`, in file order, it builds a
//! [`crate::kernel::Checker::poly`] over the declaration's `lparams` and infers
//! the declaration's type and value **unsubstituted** — no σ, no
//! `ground::subst_ground`, no schedule. `Nat.add.{}` and `List.map.{u,v}` are
//! each one pass, not one pass per ground instantiation. The certificates come
//! back under `{u⃗ ∈ ω}` and are closed together at declaration exit by
//! [`crate::kernel::Checker::discharge_levels`].
//!
//! # The counterpart, not the replacement
//!
//! This is [`crate::ledger::Ledger::run`]'s de-scheduled twin and the two are
//! **mutually exclusive within a run**, which is a decision rather than a
//! limitation. They mint into one [`Interp`]: the scheduled pass fills the
//! store at ground keys and this one would fill it at parametric ones, and
//! `derived::levels::apparatus::level_poly` declares symbols off the shared
//! `Env`, so a run that did both would renumber every symbol the second pass's
//! declarations mint. The branch's whole measurement discipline is that the
//! scheduled route's rows are **byte-identical**; a route that perturbs them by
//! existing would end that. So `--poly` runs *instead*, and the scheduled rows
//! stay reproducible because nothing about the default path changed.
//!
//! # Where the apparatus is built, and why it is here
//!
//! At route entry, before the first declaration — the hazard
//! [`crate::kernel::Checker::poly`]'s header describes, one level up.
//! `Checker::poly` forces it too and [`Interp::levels`] is idempotent, so the
//! extra call buys exactly one thing: the numbering stops depending on
//! **whether the file has a declaration this route accepts at all**. A file of
//! nothing but inductives would otherwise build no apparatus and number its
//! symbols differently from a file with one `def` in front, and the poly rows
//! of the two would not be comparable.
//!
//! # The store, and what it made of the census
//!
//! Every zone-A declaration whose value interprets gets a **generic point**
//! written to [`Interp`]'s poly store: an abbreviation `f̂` of arity
//! `|lparams|` with `⟦c.{ℓ⃗}⟧ = f̂(ℓ̂⃗)`, and `⊢ ∀u⃗. ⋀(uᵢ∈ω) → f̂(u⃗) ∈ T̂(u⃗)`
//! where the value's certificate reached the declared type. §5.3 step 5, in
//! three steps that must happen in this order and do: `poly_const_open` while
//! the level hypotheses are live, [`Checker::discharge_levels`] over all three
//! conclusions at once, then `gen_all_checked` on the closed theorem.
//!
//! This header used to say *"nothing is stored"* and size the remainder at 84
//! (later 109) `const_evidence` sites. That site is **0 and absent** from the
//! census now. What replaced it is a *fall-through*: 68 constant references
//! whose name has no generic point — and instrumented to name them, every one
//! is an inductive type, a constructor or a recursor (`Quot`, `Prod`, `Eq`,
//! `RBTree`, `List`, `Acc`, `Bool.rec`). Not one is a zone-A `def` or `axiom`.
//!
//! # Zone B, and where its frontier actually is
//!
//! `inductive`, `mutual` and `Quot` are **attempted** — [`zone_b`], one call to
//! `zoneb::ensure` per constant the declaration owns, at that constant's own
//! universe parameters instead of at every ground σ the schedule predicted.
//! This section used to be a bullet under "what is not here yet" reading
//! "counted and skipped", and the skip is what capped the per-file verdict at
//! 25 of the 89 tutorial files: 64 contain a zone-B declaration and no zone-A
//! clause could touch them. **The denominator is 89 again.**
//!
//! What the attempt measures, over the corpus: **121 of 362** zone-B constants
//! interpret at their own parameters. The other 241 are 235 `symbolic-level`
//! and 6 `ind-spec(…: parameter reduction)`, and the blocked population splits
//! — measured, not predicted — into **55 type formers, 74 constructors and 106
//! eliminators**.
//!
//! # The frontier is in two halves and only one of them is still a type
//!
//! `zoneb::ensure` takes `inst: &[Level]`. It splits: the constant's **own**
//! instantiation stays a level vector, the **declaration's** must still be
//! numerals. So the two halves are
//!
//! * **the declaration's levels** — `Prod.{u,v}`, `Eq.{u}`, `Quot.{u}` — which
//!   `ground::as_numeral` refuses at one place, standing in for the seven
//!   `as_numeral`/`subst_ground` calls in `zoneb.rs`'s interior; and
//! * **the eliminator's motive level**, which is polymorphic *even where the
//!   declaration is not*. `Bool` has no universe parameter and translates;
//!   `Bool.rec.{u}` carries the motive's level whatever `Bool` does.
//!
//! The second half is where this route now is. `crate::recursor::empty_rec` is
//! through — it never reads `u₁`, so `Empty.rec.{u}` costs
//! [`crate::interp::Interp::sort_of`] and the already-landed `Π` clause and
//! nothing else — and `033_empty` is clean on the strength of it.
//!
//! Of the eliminators that reach a route at all: **27 `rec_dep`, 9 `rec_prop`,
//! 2 `rec_nat`, 1 `rec_s_ix`**. Seven tutorial files are clean but for one
//! eliminator each — four of them `rec_dep`, two `rec_prop`, one `rec_nat`.
//!
//! # Where `rec_dep` stops now, and it is not the boundary
//!
//! `crate::rec_dep::ensure` takes `&[Level]`. **All 27** of its eliminators are
//! past the `&[u32]` boundary and past `crate::rec_dep::cx_of` — the motive
//! binder's type, the carrier equations, the codomain check, all at a variable
//! rung — and every one of them now reports §6.2's `u₁ = 0` split by name
//! instead of `symbolic-level`, which fell 235 → **208**, exactly 27. The
//! `zoneBOk` column did not move, and that is the honest shape of the tranche:
//! a reason axis, not a coverage one.
//!
//! What made `cx_of` reach is one collapse with **no case analysis in it**:
//! `⟦T p⃗ → Sort u₁⟧` is `ite0(succ(û₁), cndd, dprod)` at a variable rung, and
//! its guard is a *successor*, so
//! [`crate::interp::Interp::level_nonzero`] settles it outright and
//! [`crate::interp::Interp::pi_dprod_at`] takes the term back to the product.
//!
//! **The split then landed, and this paragraph's sizing of what was left was
//! wrong — recorded because getting it wrong twice would be worse.** It said
//! the remaining cost was `Interp::as_pi`'s 42 blind call sites, at *every*
//! binder of *every* minor premise. `crate::rec_dep::split_bottom` runs both
//! clauses under their own hypotheses and merges them with `Ite0`; `COD` needs
//! no guard on either arm (it is discharged at `srt(û₁)` for every `û₁ ∈ ω` by
//! the two `Srt` facts) and the zero arm needs one collapse away from any
//! binder, `⟦Sort u₁⟧ = U₀`. The `zoneBOk` column moved 121 → 136 and the 27
//! split rows became 15 certifications and 12 declines. Those 12 were the
//! `as_pi` frontier, and every one of them is a declaration with a
//! **field-carrying** constructor — the only shape whose minor premise has a
//! binder to be blind at.
//!
//! **The binder collapse then landed too, and closed all 12**:
//! `Interp::as_pi_mem` settles the guard by hypothesis and takes the
//! conditional apart, `zoneBOk` 136 → **148**, and the whole `recursor(…)`
//! family left the histogram. Two blind sites moved, not forty: `minor_at`'s
//! binder walk and `ih_transport`'s induction-hypothesis domain. And the sizing
//! was wrong once more, in the same direction as before — **both** arms need
//! the collapse. "The nonzero arm needs no guard" was measured over
//! field-*free* constructors, which open no binder at all.
//!
//! # Zone A's own type — the frontier is not only zone B's
//!
//! Everything above is about the constants a zone-B declaration owes. The
//! obstacle that held the per-file verdict at **27 of 89** for three tranches
//! was in neither zone B nor any eliminator route: it was
//! `crate::kernel`'s `Expr::App` rule, one node of the ordinary zone-A walk,
//! certifying the declaration's **own type**.
//!
//! `⟦boolRec.{u}⟧`'s type is
//! `∀ {motive : Bool → Sort u}, motive false → motive true → ∀ t, motive t`.
//! Its codomain is an *application*, so the type's certificate needs the
//! application rule at `motive`, whose own type is `Bool → Sort u` — and at a
//! variable rung that is `ite0(succ(û), cndd, dprod)`, which
//! [`crate::interp::Interp::as_pi`] is blind to. **This node holds no
//! `Guard`**: it is zone A, not inside anybody's case split, so
//! [`crate::interp::Interp::as_pi_at`]'s guard-keyed route had nothing to
//! offer it.
//!
//! What settles it is the same observation `cx_of` spends on the motive binder
//! and cannot lend: the guard is a **successor**, because `Sort u` inhabits
//! `Sort (u+1)`. `Interp::level_nonzero` reads a `Level` and this node has an
//! `Expr`, so the fact is spent unguarded —
//! [`crate::interp::Interp::succ_nonzero_at`], over
//! `derived::recursion::succ_ne_zero_pair`'s first component.
//!
//! Measured over the corpus, of the zone-A application nodes where `as_pi` is
//! blind *and the function's membership is present* — a real frontier, not a
//! downstream casualty:
//!
//! ```text
//! ite0 guard is a successor   1489    settled
//! ite0 guard is an imax        315    wants level_guard_at's recursion
//! ite0 guard is a bare û       290    undecidable; wants a split
//! other                          3
//! ```
//!
//! `typeEv` **74 → 80**, every other column unchanged, and the exits
//! **27 → 31 of 89**. Six files gain a type certificate — `059_emptyRec`,
//! `060_boolRec`, `061_twoBoolRec`, `062_andRec`, `067_nRec`,
//! `090_projDataIndexRec` — and the four with nothing else outstanding exit 0;
//! `062` and `090` still owe zone-B constants.
//!
//! Two files owed *only* `typeEv` and did not get it, each for a reason that is
//! not this clause's: `115_rTreeRec` moved off `no-endpoint` and onto
//! `conv-compose(pi-poly)` — the collapse happens, the composition after it
//! does not — and `015_levelParams` never had this obstacle at all, reporting
//! `not-decomposable` off a *stored* generic point's blocked typing.
//!
//! # The `imax` guards, and the census re-read at its own shape
//!
//! [`crate::interp::Interp::level_guard_at`] now returns a
//! [`crate::interp::Guard`] instead of a `Thm` and takes the caller's half as
//! an `Option`, so the same recursion serves both entries. Re-censused *after*
//! the successor clause landed — the population moves when nodes stop
//! declining, so the totals are not comparable, but the two categories that
//! matter are unchanged to the unit:
//!
//! ```text
//! guard is a successor           860    settled (successor clause)
//! guard is imax over a successor 286  ┐
//! guard is imax over imax over "   17  ├ 315 — settled here, exactly the
//! guard is imax over ∅            11  ┘        count the census predicted
//! guard is ∅                       3    settled here — the census's "other"
//! guard is a bare û              290    the boundary; still refused
//! guard is imax over a bare û      1    inherits it; still refused
//! ```
//!
//! **Two things the previous tranche's sizing got wrong, both found by probing
//! before writing.** Its note said "the unconditional route only ever produces
//! `NonZero`" — **11 of the 315 produce `Zero`**, because Lean's
//! `imax ℓ 0 = 0` and the `Π` above such a guard is a `Prop` wanting
//! `Interp::pi_cndd_at`. That is not a detail: it is why the function must
//! hand back a *tagged* `Guard` and not a bare theorem, and a caller that
//! guessed `dprod` would have named a different set eleven times. And the
//! census's unattributed **"other 3"** are guards that are literally `∅` —
//! a `Prop`-valued codomain at a variable rung, where the clause still emits
//! `ite0(∅, cndd, dprod)` rather than a numeral. Both are settled here, so
//! **317 of the 318 non-bare-parameter nodes** now come apart.
//!
//! **What moved is one column: `typeEv` 80 → 81**, `071_sortElimPropRec`, off
//! `no-endpoint`. Every other counter, every denominator and **the exits are
//! unchanged at 31 × 0 / 58 × 4 / 2 × 2**. That is the honest shape of this
//! tranche and it is worth stating plainly: 317 nodes that used to refuse now
//! answer, and the certificates they feed stop somewhere else. The frontier
//! moved; the verdict did not.
//!
//! The 290 bare-parameter guards are the genuine boundary and **must** stay
//! refused — `Sort u` is `Prop` at `u = 0` and a universe above it, the two
//! clauses are different sets, and no unconditional theorem separates them.
//! They need §6.2's split reaching zone A, which is `rec_dep::split_bottom`'s
//! machinery at a node that is inside nobody's case analysis.
//!
//! **No new `derived` mathematics.** `Ite0::when_zero`/`when_nonzero`,
//! `Order::max_ne_zero` (already unconditional, derived two tranches ago for
//! exactly this caller) and `kernel`'s `Thm::eq_refl` are the whole of it —
//! the branch's three-step run of new derivations does not continue here.
//!
//! # The level bridge — `typeEv` 81 → 92, exits 31 → 32 of 89
//!
//! `conv-compose(pi-poly)` was 50 declarations and is **0**. It was never
//! downstream of the `Π` collapse: it is two functions rendering one `Level`
//! and disagreeing. [`crate::interp::level_term_over`] is **structural**;
//! [`crate::ground::as_numeral`] **evaluates** — it folds `max(1,1)` to `1`
//! and short-circuits `imax ℓ 0` to `0` without looking at `ℓ`. So a closed
//! level reaches `pi_imax_dep`'s `mp` spelled `srt(succ(∅) ∪ succ(∅))` from
//! one side and `srt(succ(∅))` from the other.
//!
//! **Probed before writing, and the probe moved the target.** Of the 18 714
//! `Interp::mem_at_srt` calls the corpus makes, 13 629 are at an *open* level
//! and every one certifies — both sides are structural, so nothing has to
//! agree with a canonical form, and that holds for the 3 591 whose raw
//! spelling is not `Level::simplify`'s as much as for the 10 038 whose is.
//! **The `≤`-kit's own "1005 of 2103" census is that open population**, and on
//! this route it costs nothing. What blocks is the 224 *closed* sites where
//! the raw spelling is not the numeral rung — matching, to the unit, the 224
//! `mp` failures — in four shapes:
//!
//! ```text
//! max(1,1)                     142   union idempotence
//! imax(0,0)                     45   Ite0::when_zero at an ∅ guard
//! imax(imax(P,imax(0,0)),0)     24   the same, and the left operand is never
//!                                    looked at — which is why this fires
//!                                    where it mentions a parameter
//! imax(1,1)                     13   when_nonzero, then idempotence
//! ```
//!
//! So `Leq::imax_absorb` — the fact the coordinator and this module both
//! expected to spend — is spent by **none** of them. Union idempotence is
//! `Order::max_absorb` at equal operands, where its disjunction has one
//! distinct disjunct and an `or`-elimination with two identical arms is the
//! whole derivation. Still **no new `derived` mathematics**, and the `≤`-kit
//! still has no consumer.
//!
//! **And the fix upstream made a "never fires" check fire.**
//! `Interp::pi_typing_of`'s conclusion check was documented as *"measured, it
//! never fires"*. It never fired because the `mp` above it refused first;
//! with the premise side bridged it fired **157** times, all the same
//! mismatch arriving on the conclusion side. `Interp::mem_from_srt` is
//! `mem_at_srt` run backwards and puts it right.
//!
//! **What moved.** `typeEv` **81 → 92** — eleven declarations gain a type
//! certificate — `conv-compose(pi-poly)` 50 → **0**, and the exits **31 → 32
//! of 89** (`115_rTreeRec`). No column fell, no denominator moved, `open = 0`
//! on all 89. The other 39 declarations moved to the obstacle behind this one:
//! `conv-compose(proof-irrel)` 38 and one `ind-spec(Acc: …)`. `015_levelParams`
//! is now the only file owing `typeEv` alone, and 15 owe only `zoneB`.
//!
//! # What is *not* here yet, stated so a zero row is readable
//!
//! * **A ground use of a poly constant pays the §1.2 bridge — and does not
//!   yet cost anything here.** The instantiation is unconditional and derives
//!   a true typing, but at the ω spelling `srt(n̄)` where the use site's own
//!   `⟦Sort n⟧` is `Uₙ`; the two are `Interp::rung_bridge` apart, so the
//!   declared-type retarget declines and the cost lands on
//!   [`PolyLedger::const_ev_ok`].
//!   `a_ground_use_of_a_polymorphic_constant_interprets_and_certifies`
//!   exhibits it — `constEv=1` of 2, reason `classifier`. **Over the tutorial
//!   corpus that bucket is empty**: the poly constants that reach the store
//!   are used at parametric levels, so the bridge is real, demonstrated, and
//!   not on the critical path. Retired by the switchover (§5.5) all the same.
//! * **Every zone-B constant the frontier refuses** is in
//!   [`PolyLedger::zone_b_blocked`] with the reason `zoneb::ensure` gave, never
//!   a stand-in — and `zone_b_ok` plus that histogram is `zone_b_consts`,
//!   which `tests::owed_is_met_or_explained` pins.
//!
//! Both are counted rather than silently passed over, because a pass that
//! reports `declars=N` while having attempted a third of them is the shape of
//! report this project has been burned by.

use std::collections::BTreeMap;

use crate::env::{Declaration, Environment};
use crate::ev::{Gap, Sealed};
use crate::interp::Interp;
use crate::kernel::{Checker, Typing};
use crate::ledger::Ledger;

/// What the de-scheduled pass reached, per declaration.
///
/// Deliberately **not** [`crate::ledger::Ledger`]. That one counts
/// `(declaration, σ)` pairs and half its columns — `pairs`, `fullyInterpreted`,
/// the σ-keyed store columns — have no meaning without a schedule; reusing it
/// would have produced a report whose column headings lie about what was
/// counted. The two share `Ledger::key` and nothing else, and sharing *that* is
/// deliberate: one vocabulary for a gap, so the two routes' rows can be read
/// against each other.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct PolyLedger {
    /// `axiom` / `def` / `theorem` declarations this route attempted.
    pub declarations: usize,
    /// `inductive` / `mutual` / `Quot` declarations this route **attempted**.
    ///
    /// It used to say "counted and skipped". Since the zone-B clause it is an
    /// attempt count like [`PolyLedger::declarations`], and the two axes a
    /// zone-B declaration is judged on are [`PolyLedger::zone_b_consts`] and
    /// [`PolyLedger::zone_b_ok`]. The number itself is unchanged — the same
    /// declarations are reached — which is what keeps the Gate B row readable
    /// across the change.
    pub zone_b: usize,
    /// The **constants** those declarations owe: a type former, each of its
    /// constructors, and each eliminator it owns; `Quot`'s four; a `mutual`
    /// block's members and theirs.
    ///
    /// Counted apart from [`PolyLedger::zone_b`] because a zone-B declaration
    /// is not one obligation but several, and a route that reported
    /// `zoneB=108` while owing 300 constants would be the shape of report the
    /// module header warns about. This is the denominator
    /// [`PolyLedger::is_clean`]'s zone-B conjunct is taken against.
    pub zone_b_consts: usize,
    /// Those whose `⟦c.{ℓ⃗}⟧` is in the store when the declaration is done,
    /// at the constant's **own** universe parameters.
    ///
    /// The interpretation axis only, deliberately: zone B stores a typing
    /// beside the term and `Sealed` already refuses an open one, so a stored
    /// interpretation on this route is a certified one — but that is zone B's
    /// invariant rather than this ledger's, and a separate certificate column
    /// would be this module asserting it rather than reading it.
    pub zone_b_ok: usize,
    /// Declarations whose `⟦ty⟧` was produced.
    pub types_ok: usize,
    /// Declarations whose `⊢ ⟦ty⟧ ∈ ⟦Sort ℓ⟧` was derived **and closed**.
    pub type_ev_ok: usize,
    /// Declarations with a value at all.
    pub values_attempted: usize,
    /// Declarations whose `⟦val⟧` was produced.
    pub values_ok: usize,
    /// Declarations whose `⊢ ⟦val⟧ ∈ ⟦valTy⟧` was derived **and closed**.
    ///
    /// At the type *inference* assigned the value, which is not the declared
    /// type. That is the meaning this column's Gate B baseline was taken at
    /// and it is deliberately unchanged by the generic-point tranche — the
    /// retarget to the declared type happens for [`PolyLedger::const_ev_ok`]
    /// and only there, so a ratchet column cannot move by having been
    /// redefined.
    pub value_ev_ok: usize,
    /// **Generic points minted** — `⟦c⟧ = f̂(u⃗)` written to the poly store,
    /// with or without a typing. `LEVELPOLY.md` §5.3 step 5.
    ///
    /// Counted apart from [`PolyLedger::const_ev_ok`] for MINI-DESIGN.md §0's
    /// reason: an interpretation and a certificate are two axes, and a
    /// constant whose term is in the store still unblocks a use site's
    /// `valuesOk` where it cannot unblock its `valueEv`.
    ///
    /// Counts generic points **minted**, which is the same number as generic
    /// points *inserted* on any one file — a name appears once — and differs
    /// only when one [`Interp`] is driven over the same declarations twice,
    /// where [`Interp::put_poly_const`] is first-writer-wins.
    pub stored: usize,
    /// Generic points whose `⊢ ∀u⃗. ⋀(uᵢ∈ω) → f̂(u⃗) ∈ T̂(u⃗)` was derived,
    /// generalised **and sealed**.
    pub const_ev_ok: usize,
    /// **Certificates that reached declaration exit still carrying a
    /// hypothesis**, after [`Checker::discharge_levels`].
    ///
    /// The de-scheduled route's counterpart of
    /// [`crate::ledger::Ledger::unsealed`], and it must be **zero**. A nonzero
    /// count is an escaped assumption: `discharge_levels` closes exactly the
    /// `uᵢ ∈ ω` it opened, so anything left is a hypothesis some clause raised
    /// and did not discharge, and it would be `Sealed`-refused the moment step
    /// 5 gave this route a store to write to. Counting it here means the
    /// defect is found by the pass rather than by the funnel.
    pub open: usize,
    /// The apparatus built at route entry. `false` means nothing ran.
    pub apparatus: bool,
    /// Why `⟦ty⟧` or `⟦val⟧` was absent, by first blocking cause, in
    /// [`Ledger::key`]'s vocabulary.
    ///
    /// **This histogram is the point of the module.** `LEVELPOLY.md` §5.3
    /// step 1 lists the remaining §6.2 clauses by *`Gap::SymbolicLevel` site
    /// count* — `zoneb.rs` at 23, `kernel.rs` at 21 — and a site count is not a
    /// work estimate; the branch has already had three sizings corrected for
    /// exactly that reason, and a fourth here: this histogram is what said the
    /// const clause's 109 sites were one clause, and it is what said the 68
    /// that replaced them are zone B rather than more of the same. This is
    /// what the clauses cost when a real file is run through them.
    pub blocked: BTreeMap<String, usize>,
    /// Why a certificate was absent where the interpretation was present — the
    /// evidence axis, kept in its own histogram for MINI-DESIGN.md §0's reason.
    pub ev_blocked: BTreeMap<String, usize>,
    /// Why a **generic point's** typing was absent where the abbreviation was
    /// minted. Its own histogram, and not folded into
    /// [`PolyLedger::ev_blocked`], because the two answer different questions:
    /// that one is "why does this declaration have no certificate", this one is
    /// "why will every *later* use of this constant have none".
    pub const_blocked: BTreeMap<String, usize>,
    /// Why a **zone-B constant** has no interpretation at its own universe
    /// parameters. Its own histogram, for the same reason the three above are
    /// three: zone B's obligations are per *constant*, and folding them into
    /// [`PolyLedger::blocked`] would put a type former's decline in the same
    /// bucket as a `def`'s and lose which route reported it.
    ///
    /// **The reason is the one `zoneb::ensure` returned, never a stand-in.**
    /// The finding the const clause left behind — *a reason in a store is not a
    /// leaf* — is sharper here than anywhere: zone B keeps three reason tables
    /// of its own (`untranslated`, `ctor_untranslated`, `rec_untranslated`) and
    /// every later use of the constant reads them, so a `Gap` guessed at this
    /// site would be handed back at every occurrence. Nothing here synthesises
    /// one.
    pub zone_b_blocked: BTreeMap<String, usize>,
    /// **Where the reported gap was minted**, `file:line`, when
    /// `MINI_POLY_SITES` asked — empty otherwise.
    ///
    /// # The row [`PolyLedger::blocked`] cannot produce
    ///
    /// [`Gap::SymbolicLevel`] carries no payload, so every one of them keys to
    /// the single string `symbolic-level`, and on the first run of this route
    /// that one bucket was **90% of every blocked interpretation**. That number
    /// sizes the remaining work and says nothing about *which* work: under a
    /// [`Checker::poly`] thread the two sites that could mint it were
    /// `pi_evidence`, which wanted `as_numeral(l1)`/`as_numeral(l2)` and was
    /// **derivation** (`derived::levels::{pi_rules, ite0, leq}`), and
    /// `const_evidence`, which wanted the whole level vector as numerals and
    /// was **the store's key** (§5.3 step 5). Those are different jobs with
    /// different owners, and a bucket that merges them is `MINI-DESIGN.md`
    /// §0.4's "keyed on a name instead of a cause" in the one place the branch
    /// most needs the cause.
    ///
    /// **Both are gone from the census, and this row is what showed it.** Each
    /// went to zero and *disappeared* rather than shrinking — the shape a
    /// clause takes when the obstruction was the schedule rather than the
    /// mathematics. What the row reports now is the fall-through to the ground
    /// store, and it is a zone-B population; the module header names it.
    ///
    /// The trail [`crate::blocker`] already keeps is exactly the missing
    /// information, and its oldest entry is the origin rather than a
    /// forwarding — the eviction bug its `TRAIL_CAP` header records is the
    /// reason that is true. So this arms the blocker, clears per declaration,
    /// and files the **first** mint whose variant matches the reason that was
    /// actually reported.
    ///
    /// **Both axes land in this one map, and that is deliberate.**
    /// [`PolyLedger::blocked`] and [`PolyLedger::ev_blocked`] are kept apart
    /// because "no interpretation" and "no certificate" are different
    /// questions (MINI-DESIGN.md §0); a *mint site* is neither, it is a line of
    /// code, and the same line answers for both. Merging them is what let the
    /// unguarded-successor tranche put five of six declarations at
    /// `kernel.rs`'s `app_evidence` in one run — the evidence axis had no
    /// census at all until then, and the four eliminator wrappers had sat on
    /// `no-endpoint` for three tranches with nothing saying where it came from.
    /// Which axis a row belongs to is still answerable: it is whichever
    /// histogram carries the reason.
    ///
    /// Off by default and off in every gate: arming puts a thread-local write
    /// on `Ev::missing`, which is the failure branch of `whnf`.
    pub sites: BTreeMap<String, usize>,
}

impl PolyLedger {
    /// Nothing owed: every declaration this route attempted interpreted and
    /// certified, both halves, with nothing left open.
    ///
    /// **Zone B is *not* excused.** A file whose inductives this route cannot
    /// reach owes them; counting the route clean on the strength of having
    /// skipped them is the "SKIP is not PASS" defect with a ledger column as
    /// the vehicle.
    ///
    /// # The conjunct was `zone_b == 0`, and widening it is not a weakening
    ///
    /// It had to be, while zone B was skipped: "the file has no inductive" was
    /// the only zone-B fact this route could establish, and any weaker test
    /// would have excused the skip. Now that the declarations are attempted the
    /// honest test is that every constant they owe is interpreted, and the two
    /// **agree on every file the old one accepted** — no zone-B declaration
    /// means no zone-B constant, so `0 == 0`. A file with an inductive still
    /// has to earn it, one constant at a time, and can no longer be clean by
    /// virtue of the route not having looked.
    ///
    /// The old conjunct is also what capped this route's per-file verdict at
    /// **25 of the 89** files that reach it — 64 contain a zone-B declaration
    /// and no zone-A clause could touch them. That cap is gone with the skip:
    /// the denominator is 89 again, and the number against it is a measurement
    /// of zone B's clauses rather than of the route's coverage.
    ///
    /// **[`PolyLedger::const_ev_ok`] is deliberately not a conjunct.** It
    /// counts what a *later* declaration will be able to do, not what this
    /// file owes; a file whose last declaration is an uncertifiable `def`
    /// nobody references is clean, and folding the store's coverage in here
    /// would call it dirty for an obligation that has no consumer.
    pub fn is_clean(&self) -> bool {
        self.apparatus
            && self.zone_b_ok == self.zone_b_consts
            && self.open == 0
            && self.types_ok == self.declarations
            && self.type_ev_ok == self.declarations
            && self.values_ok == self.values_attempted
            && self.value_ev_ok == self.values_attempted
    }

    /// The report, one `key=value` per tab — `mini --poly --verbose`'s rows and
    /// the poly gate's baseline.
    ///
    /// Three lines, so the interpretation axis and the evidence axis do not
    /// share a histogram (MINI-DESIGN.md §0), plus a fourth only when
    /// `MINI_POLY_SITES` asked for one.
    pub fn rows(&self) -> Vec<String> {
        let mut head = format!(
            "polyledger\tdeclars={}\tzoneB={}\tzoneBOk={}/{}\ttypesOk={}\ttypeEv={}\tvaluesOk={}/{}\tvalueEv={}\tstored={}\tconstEv={}\topen={}",
            self.declarations,
            self.zone_b,
            self.zone_b_ok,
            self.zone_b_consts,
            self.types_ok,
            self.type_ev_ok,
            self.values_ok,
            self.values_attempted,
            self.value_ev_ok,
            self.stored,
            self.const_ev_ok,
            self.open,
        );
        // Named on the row and not merely implied by a zero, because "the
        // apparatus did not build" and "the file had no declarations" produce
        // the same counters and are entirely different results.
        head.push_str(if self.apparatus { "\tapparatus=built" } else { "\tapparatus=none" });
        let hist = |tag: &str, m: &BTreeMap<String, usize>| {
            let mut s = tag.to_string();
            for (k, v) in m {
                s.push_str(&format!("\t{k}={v}"));
            }
            s
        };
        let mut rows = vec![
            head,
            hist("polyblocked", &self.blocked),
            hist("polyev", &self.ev_blocked),
            hist("polyconstev", &self.const_blocked),
            hist("polyzoneb", &self.zone_b_blocked),
        ];
        // Only when it was asked for: a bare `polysites` row on every run would
        // read as "no site was recorded" rather than "nobody asked".
        if !self.sites.is_empty() {
            rows.push(hist("polysites", &self.sites));
        }
        rows
    }

    fn note(m: &mut BTreeMap<String, usize>, g: Option<&Gap>) {
        *m.entry(Ledger::key(g)).or_insert(0) += 1;
    }

    /// File the origin of `g` from the current [`crate::blocker`] trail — the
    /// **oldest** mint of the same variant, which is the site that gave up
    /// rather than one that forwarded its reason.
    fn note_site(&mut self, g: Option<&Gap>) {
        let Some(g) = g else { return };
        let want = crate::blocker::variant_name(g);
        let Some(m) = crate::blocker::trail().into_iter().find(|m| {
            crate::blocker::variant_name(&m.gap) == want
        }) else {
            return
        };
        *self.sites.entry(format!("{}:{}", m.file, m.line)).or_insert(0) += 1;
    }
}

/// Run the de-scheduled interpretation over a whole file.
///
/// Declarations in file order — mini-lean's order, and the same order
/// [`Ledger::run`] uses, so the two reports name the same declarations in the
/// same sequence. There is no inner loop: **that is the whole point.**
pub fn run(env: &Environment, decls: &[Declaration], ip: &mut Interp) -> PolyLedger {
    // The build point, pinned at route entry — before the first declaration,
    // and in the initialiser so nothing can slip in front of it. See the module
    // header for why *when* this runs decides every later symbol's number.
    let mut led = PolyLedger { apparatus: ip.levels().is_some(), ..Default::default() };
    if !led.apparatus {
        return led
    }
    // The site census — [`PolyLedger::sites`]. Armed here rather than by the
    // caller, and disarmed on the way out, so an env variable cannot leave the
    // blocker on for whatever runs next in the process.
    let sites = std::env::var_os("MINI_POLY_SITES").is_some();
    let was_armed = crate::blocker::is_armed();
    if sites {
        crate::blocker::arm(true);
    }
    for d in decls {
        if sites {
            crate::blocker::enter_pair();
        }
        let (name, lparams, ty, val) = match d {
            Declaration::Axiom { name, lparams, ty, .. } => (name, lparams, ty, None),
            Declaration::Def { name, lparams, ty, value, .. } => {
                (name, lparams, ty, Some(value))
            }
            Declaration::Quot | Declaration::Inductive { .. } | Declaration::Mutual { .. } => {
                zone_b(env, ip, d, &mut led);
                continue
            }
        };
        led.declarations += 1;
        let Some(mut c) = Checker::poly(env, ip, lparams) else {
            // `Interp::levels` answered above, so it answers here: a `None`
            // would mean the apparatus stopped building mid-file, which is
            // not a thing that can happen and is not silently tolerated.
            unreachable!("the apparatus built at route entry")
        };
        // One traversal per half, both results, and the reason for a missing
        // one is the `Typing`'s own `ev` — `Ledger::run`'s discipline, kept.
        let ty_t = c.infer_type(ty);
        let val_t = val.map(|v| c.infer_type(v));

        // ── The generic point (§5.3 step 5), minted while `u⃗ ∈ ω` are open ──
        //
        // `⟦c⟧` is an **abbreviation** for `⟦val⟧` abstracted over the
        // declaration's level variables, and its typing is the value's typing
        // carried back along that defining equation — the ground pipeline's
        // last step (`Ledger::run`, §8) at a variable rung, with `f̂(u⃗)` where
        // that one has a 0-ary constant.
        //
        // **Retargeted to the *declared* type first.** The value's own
        // certificate is at the type inference assigned it, and a use site
        // asks about the declared one; a store filled at the inferred type
        // would answer a question nobody asks. This is `Ledger::run`'s
        // `retarget_to` on the de-scheduled route, and it is used **only** for
        // the store: `valueEv` below still counts `val_t.ev`, so Gate B's
        // ratchet column keeps the meaning its baseline was taken at.
        let ty_tm = ty_t.as_ref().ok().and_then(|t| t.tm.clone());
        // The whole [`crate::ev::Ev`] and not just its theorem: when the
        // retarget declines, **its** reason is the one the store owes (§0.4 —
        // a missing typing carries the reason of the sub-result that stopped
        // it, never a stand-in). This read `.thm().cloned()` and the store
        // then reported `Gap::Classifier` by fallback, which is a guess.
        //
        // **The guess did not stay inside the store's own column**, and that
        // is the part worth naming: `Checker::poly_const_evidence` hands the
        // stored gap straight back to every later *use* of the constant, so a
        // wrong reason here is a wrong reason at every reference to it. Fixing
        // it moved 26 entries out of `polyev classifier` as well as 29 out of
        // `polyconstev classifier`, and those 26 were never this function's
        // to report. A reason in a store is not a leaf.
        let store_ev = match (val_t.as_ref().and_then(|t| t.as_ref().ok()), &ty_tm) {
            (Some(tv), Some(want)) => Some(c.retarget_to(tv, ty, want.clone())),
            _ => None,
        };
        let store_mem = store_ev.as_ref().and_then(|e| e.thm().cloned());
        let opened = val_t
            .as_ref()
            .and_then(|t| t.as_ref().ok())
            .and_then(|t| t.tm.clone())
            .and_then(|v| c.poly_const_open(lparams, &v, store_mem.as_ref()));

        // **Closed together, in one call, before anything is read back.**
        // The conclusions stand over the same `uᵢ`, so they are discharged
        // against the same assumptions in one pass; `Checker::discharge_levels`
        // says why the singular form could not do this. The constant's own
        // typing is the **third** conclusion that function's slice form was
        // widened for, and it arrives exactly where §5.3 predicted it would.
        let raw: Vec<_> = [
            ty_t.as_ref().ok().and_then(|t: &Typing| t.ev.thm().cloned()),
            val_t.as_ref().and_then(|t| t.as_ref().ok()).and_then(|t: &Typing| t.ev.thm().cloned()),
            opened.as_ref().and_then(|o| o.typing.clone()),
        ]
        .to_vec();
        let present: Vec<_> = raw.iter().flatten().cloned().collect();
        let mut closed = c.discharge_levels(&present).into_iter();
        drop(c);
        // Back into the two slots the theorems came from, so a missing type
        // certificate does not shift the value's into its place.
        //
        // **`if r.is_some()` and not `r.as_ref().and(closed.next())`**, which
        // is what this was and is wrong: `Option::and` evaluates its argument
        // eagerly, so an absent type certificate still consumed the iterator's
        // next element — the value's — and both slots came back `None`. It
        // reported itself as `polyev inference-error`, a reason no clause can
        // mint here, which is the only thing that gave it away. See
        // [`tests::a_missing_type_certificate_does_not_eat_the_values`].
        let closed: Vec<Option<kernel::Thm>> = raw
            .iter()
            .map(|r| if r.is_some() { closed.next() } else { None })
            .collect();

        let ty_ok = ty_t.as_ref().is_ok_and(|t| t.tm.is_some());
        if ty_ok {
            led.types_ok += 1;
        } else {
            let g = ty_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
            PolyLedger::note(&mut led.blocked, g.as_ref());
            if sites {
                led.note_site(g.as_ref());
            }
        }
        match &closed[0] {
            Some(t) if t.hyps().is_empty() => led.type_ev_ok += 1,
            Some(_) => led.open += 1,
            None => {
                let g = ty_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
                PolyLedger::note(&mut led.ev_blocked, g.as_ref());
                if sites {
                    led.note_site(g.as_ref());
                }
            }
        }

        let Some(val_t) = val_t else { continue };
        led.values_attempted += 1;
        if val_t.as_ref().is_ok_and(|t| t.tm.is_some()) {
            led.values_ok += 1;
        } else {
            let g = val_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
            PolyLedger::note(&mut led.blocked, g.as_ref());
            if sites {
                led.note_site(g.as_ref());
            }
        }
        match &closed[1] {
            Some(t) if t.hyps().is_empty() => led.value_ev_ok += 1,
            Some(_) => led.open += 1,
            None => {
                let g = val_t.as_ref().ok().and_then(|t| t.ev.gap().cloned());
                PolyLedger::note(&mut led.ev_blocked, g.as_ref());
            }
        }

        // ── …and generalised, third and last (§5.3 step 5, obstacle 1) ──
        //
        // Only now. `crate::rec_dep::gen_all_checked` refuses to bind a
        // variable that is free in a live hypothesis, and `uᵢ ∈ ω` is exactly
        // such a hypothesis until the discharge above turned it into an
        // antecedent. That refusal is the reason the order is retarget →
        // batch-discharge → generalise and not any other, and it is a refusal
        // rather than a caveat: `Thm::gen` is banned in `mini/src` (R6′ I3)
        // precisely so the side condition cannot be waived by accident.
        let Some(o) = opened else { continue };
        led.stored += 1;
        let typing = match &closed[2] {
            Some(t) => match crate::rec_dep::gen_all_checked(&o.vars, t) {
                // `Sealed` is the funnel, and it is what makes `open` an
                // *assertion* here rather than an observation: a theorem that
                // reached this point still carrying a hypothesis is refused
                // the store instead of being written to it.
                Some(g) => match Sealed::new(g) {
                    Ok(s) => {
                        led.const_ev_ok += 1;
                        Ok(s)
                    }
                    Err(_) => {
                        led.open += 1;
                        Err(Gap::Skeleton)
                    }
                },
                None => Err(Gap::Skeleton),
            },
            // The retarget's own reason first, the value's behind it, and
            // `Classifier` only where neither exists — which is the store
            // having nothing to say about a value that had a certificate, and
            // cannot arise from the branch above.
            None => Err(store_ev
                .as_ref()
                .and_then(|e| e.gap().cloned())
                .or_else(|| val_t.as_ref().ok().and_then(|t| t.ev.gap().cloned()))
                .unwrap_or(Gap::Classifier)),
        };
        if let Err(g) = &typing {
            PolyLedger::note(&mut led.const_blocked, Some(g));
        }
        ip.put_poly_const(
            *name,
            crate::interp::PolyConst {
                sym: o.sym,
                arity: lparams.len(),
                typing,
                // Unconditional by construction — a definitional extension
                // assumes nothing — so it is sealed here rather than
                // discharged. See `Checker::poly_const_open`.
                defeq: Sealed::new(o.defeq).ok(),
                // A definition's interpretation stays folded — the `upi`
                // measurement is what unfolding one costs.
                unfold_at_use: false,
            },
        );
    }
    if sites {
        crate::blocker::arm(was_armed);
    }
    led
}

/// **A zone-B declaration on the de-scheduled route** — its type former, its
/// constructors and its eliminators, each at *its own* universe parameters.
///
/// `LEVELPOLY.md` §5.3, the zone-B clause group. The counterpart of
/// [`crate::ledger::fill_declaration`] with the σ loop removed: that one asks
/// the schedule for every ground instantiation of every constant the
/// declaration owns and calls [`crate::zoneb::ensure`] once per pair, this one
/// asks for the declaration's own parameters and calls it once.
///
/// # The obligation is per *constant*, and the list is `fill_declaration`'s
///
/// Deliberately the same list, read the same way — including the nested case,
/// where the splice's `NestedRecord::constants` names every recursor a nested
/// declaration owns and `T.rec` names only the first. Deriving a second list
/// here would be a second answer to "what does this declaration owe", and the
/// two would drift.
///
/// # Where the frontier is, and it is exactly one predicate
///
/// [`crate::zoneb::ensure`] takes `inst: &[u32]`, so it can be asked about a
/// constant only at an instantiation of numerals. At a constant's *own*
/// parameters that is the empty vector or nothing — `Level::param` is never a
/// numeral — so today this test is `lparams.is_empty()` and nothing else. It is
/// written as the numeral test all the same, because that is the predicate the
/// `&[u32]` boundary actually enforces (`ground::as_numeral`, and
/// `mini/src/ground.rs`'s header on where the groundness assumption lives), and
/// it is the one that loosens when the boundary retypes to `&[Level]`. Every
/// refusal is [`Gap::SymbolicLevel`] in [`PolyLedger::zone_b_blocked`], which
/// is the census the next clause is sized from.
///
/// **A parameterless declaration is not a level-polymorphic result and is not
/// claimed as one.** `Bool`, `Nat` and `And` have no universe parameter, so
/// this route interprets them at the same empty instantiation the scheduled
/// route uses and the mathematics is identical; what is new is that the
/// *route* reaches them at all, which is what turns 64 skipped files into 64
/// measured ones. Their **eliminators** are a different matter and are the
/// finding: `Bool.rec.{u}` carries the motive's level whatever `Bool` does, so
/// a declaration with no parameters still owes a polymorphic recursor.
///
/// # A `mutual` block is recorded, never attempted
///
/// [`crate::ledger::fill_declaration`]'s reason, unchanged and load-bearing:
/// `zoneb::ensure` resolves a name through the environment, where a block's
/// members look like single inductives, so calling it here would not decline.
/// The block's members are counted and their reason is
/// [`crate::mutual_aux::encode`]'s own.
///
/// The mutation was run;
/// `tests::a_mutual_block_is_recorded_and_never_interpreted_member_by_member`
/// records what it does, which is not what `fill_declaration` predicts.
fn zone_b(env: &Environment, ip: &mut Interp, d: &Declaration, led: &mut PolyLedger) {
    use crate::expr::{Level, Name};

    led.zone_b += 1;
    // The one arm that must not reach `ensure`. Counted and given the
    // encoder's own reason — the same one the scheduled route files into the
    // three untranslated tables — so `polyzoneb` names the shape rather than
    // the feature.
    if let Declaration::Mutual { types, .. } = d {
        let why = crate::mutual_aux::encode(env, d)
            .err()
            .unwrap_or(crate::mutual_aux::Reason::NotABlock)
            .label();
        for t in types {
            // The member, its constructors and its recursor — the same three
            // groups `fill_declaration` keys into the three untranslated
            // tables, counted rather than keyed because this route has no
            // schedule to key them at.
            for _ in 0..t.ctors.len() + 2 {
                led.zone_b_consts += 1;
                PolyLedger::note(&mut led.zone_b_blocked, Some(&Gap::IndSpec(t.name, why)));
            }
        }
        return
    }
    let names: Vec<Name> = match d {
        Declaration::Inductive { name, ctors, .. } => {
            match ip.ind_opt().and_then(|a| a.nested.get(name)) {
                Some(r) => r.constants.clone(),
                None => {
                    let mut v = Vec::with_capacity(ctors.len() + 2);
                    v.push(*name);
                    v.extend(ctors.iter().map(|(n, _)| *n));
                    v.push(Name::str(name, "rec"));
                    v
                }
            }
        }
        // `add_quot` mints all four and `convert::load` pushes one
        // [`Declaration::Quot`] for them, so this arm names them itself — in
        // `add_quot`'s order, which `fill_declaration` records as load-bearing.
        Declaration::Quot => {
            let q = Name::simple("Quot");
            vec![q, Name::str(&q, "mk"), Name::str(&q, "lift"), Name::str(&q, "ind")]
        }
        _ => return,
    };
    for n in &names {
        led.zone_b_consts += 1;
        // The constant's **own** parameters, off the environment rather than
        // off the declaration: a recursor's list is one longer than its
        // declaration's — the motive's level, prepended — and `ensure` splits
        // the declaration's off the tail itself.
        let Some(lps) = env.get(n).map(|ci| ci.lparams().to_vec()) else {
            // Not a fallback: the name came from the declaration or from the
            // splice's own list, so an environment that does not own it is a
            // constant nothing can interpret, which is what this `Gap` says.
            PolyLedger::note(
                &mut led.zone_b_blocked,
                Some(&Gap::NoInterpretation(*n)),
            );
            continue
        };
        let own: Vec<Level> = lps.iter().map(|u| Level::param(*u)).collect();
        // `Checker::poly` and not `Checker::threaded`, even where `lps` is
        // empty and the two would derive the same theorems: this route's
        // symbol numbering has to be a function of the route and not of which
        // constructor a given arm happened to pick.
        //
        // With `lps` empty it opens no `uᵢ ∈ ω`, so there is nothing for
        // `discharge_levels` to close. Where it is **not** empty — every
        // eliminator, whose motive level is its own — the assumptions are live
        // for the whole build and `Sealed` inside `crate::zoneb::store_at` is
        // what refuses a certificate that escaped with one, which is why zone
        // B has no `open` column of its own here.
        let Some(mut c) = Checker::poly(env, ip, &lps) else {
            unreachable!("the apparatus built at route entry")
        };
        // **The levels go through, not their numerals.** This used to test the
        // whole vector with `ground::as_numeral` and report `symbolic-level`
        // for anything else — the frontier when `zoneb::ensure` took `&[u32]`.
        // It takes `&[Level]` now and makes the split itself, per its header:
        // the declaration's own levels must still be numerals, the constant's
        // own prefix need not be. Reporting it here as well would be a second
        // frontier disagreeing with the first.
        let r = crate::zoneb::ensure(&mut c, n, &own);
        // **The store is the verdict, not the `Result`.** `ensure` answers
        // `Ok` having filled the declaration's key, and the constant asked for
        // is one of several it fills; reading the return value alone would
        // count a constructor as done because its type former was.
        let stored = c.stored_term_at(n, &own).is_some();
        // ── the generic point for a zone-B constant (§5.3 step 5, inductives) ─
        //
        // Before `drop(c)`, because the `uᵢ ∈ ω` tokens die with it.
        generic_points(&mut c);
        drop(c);
        if stored {
            led.zone_b_ok += 1;
        } else {
            // `ensure`'s own reason, and `Skeleton` only where it returned
            // `Ok` and the constant is still absent — which is the store
            // having nothing to say, and is not a reason zone B can mint.
            PolyLedger::note(&mut led.zone_b_blocked, Some(&r.err().unwrap_or(Gap::Skeleton)));
        }
    }
}

/// **The generic point for the zone-B constants this `ensure` just built** —
/// `LEVELPOLY.md` §5.3 step 5 for inductive declarations, which never had one.
///
/// # Why an inductive needed this and a `def` did not
///
/// A `def`'s generic point is minted from its *value*. A type former, a
/// constructor and an eliminator have no value; what they have is a term and a
/// typing that `crate::zoneb::store_at` built under `u⃗ ∈ ω`. `Sealed` refuses
/// that typing at the ground key — correctly — and the four eliminators that
/// reported `ind-spec(…: hypothesis escaped the nest)` were **not** missing a
/// derivation. They were missing declaration exit: the theorem was proved and
/// then discarded for want of the discharge a `def` gets.
///
/// So the shape is the `def` path's, with the store standing in for the value:
///
/// ```text
///   {u⃗ ∈ ω} ⊢ ⟦c.{u⃗}⟧ ∈ T̂        the parked typing
///   {u⃗ ∈ ω} ⊢ f̂(u⃗)   ∈ T̂        poly_const_open — retarget along f̂'s equation
///          ⊢ u⃗ ∈ ω → f̂(u⃗) ∈ T̂   discharge_levels, once, batched
///          ⊢ ∀u⃗. u⃗ ∈ ω → …       gen_all_checked
/// ```
///
/// # The order is forced and the batch is not an optimisation
///
/// [`Checker::discharge_levels`] **drains** its tokens, so it runs exactly once
/// per `Checker`; every conclusion has to be in that one call or the ones left
/// out keep a hypothesis whose token is gone. `crate::rec_dep::gen_all_checked`
/// then refuses to bind a variable that is free in a live hypothesis, which is
/// what makes *generalise last* a refusal rather than a convention —
/// `Thm::gen` is banned in `mini/src` (R6′ I3) so it cannot be waived.
///
/// # What is skipped, and why that is a decline rather than a guess
///
/// An entry whose key is not a vector of **distinct bare parameters** gets no
/// generic point: the symbol's arity is the key's length and
/// `Checker::poly_const_evidence` instantiates positionally, so a key like
/// `[max u v]` would mint a symbol whose argument order means nothing. Those
/// keep the reason they already have.
fn generic_points(c: &mut Checker<'_, '_>) {
    use crate::expr::{LevelView, Name};

    let pending = c.take_pending_poly();
    if pending.is_empty() {
        return
    }
    // ── 1. retarget each onto its own `f̂`, while the assumptions are live ──
    let mut opened: Vec<(Name, crate::kernel::PolyOpen)> = Vec::new();
    for (name, levels, thm) in &pending {
        let ups: Option<Vec<Name>> = levels
            .iter()
            .map(|l| match l.view() {
                LevelView::Param(u) => Some(u),
                _ => None,
            })
            .collect();
        let Some(ups) = ups else { continue };
        // Distinct: two arguments standing for one parameter would make the
        // arity a lie in the other direction.
        let mut seen = ups.clone();
        seen.sort_by_key(|n| format!("{n}"));
        seen.dedup();
        if seen.len() != ups.len() {
            continue
        }
        let Some(term) = c.stored_term_at(name, levels) else { continue };
        if let Some(o) = c.poly_const_open(&ups, &term, Some(thm)) {
            opened.push((*name, o));
        }
    }
    // ── 2. one discharge for all of them ─────────────────────────────────────
    let raw: Vec<Option<kernel::Thm>> = opened.iter().map(|(_, o)| o.typing.clone()).collect();
    let present: Vec<kernel::Thm> = raw.iter().flatten().cloned().collect();
    let mut closed = c.discharge_levels(&present).into_iter();
    let closed: Vec<Option<kernel::Thm>> =
        raw.iter().map(|r| if r.is_some() { closed.next() } else { None }).collect();

    // ── 3. …and only now, generalise and store ───────────────────────────────
    let Some(ip) = c.interp() else { return };
    for ((name, o), t) in opened.into_iter().zip(closed) {
        let typing = match t {
            Some(t) => match crate::rec_dep::gen_all_checked(&o.vars, &t) {
                // `Sealed` again, and it is an assertion here exactly as it is
                // on the `def` path: a theorem that still carries a hypothesis
                // after the discharge is refused the store, not written to it.
                Some(g) => Sealed::new(g).map_err(|_| Gap::Skeleton),
                None => Err(Gap::Skeleton),
            },
            None => Err(Gap::Skeleton),
        };
        // **A generic point without a certificate does not get to shadow one
        // that has one**, and this is where an inductive differs from a `def`.
        //
        // `Checker::const_evidence` consults the poly store *first*. For a
        // `def` that is free: nothing else on this route can answer, so storing
        // a bare symbol with `typing: Err` still moves `valuesOk`. An inductive
        // constant has a **competitor** — the keyed store, which
        // `Checker::miss_reason`'s lazy fill will build at a ground key on
        // demand, ι-rules and all. Shadowing that with an uncertified `f̂` is a
        // strict loss, and it was measured as one: `075_nRecReduction` and
        // `116_rtreeRecReduction` lost `typesOk`, `typeEv`, `valueEv` and
        // `constEv` when this arm stored unconditionally.
        //
        // So the entry goes in only with its typing. The reason for the ones
        // left out is unchanged and still reported from the keyed store.
        let Ok(typing) = typing else { continue };
        ip.put_poly_const(
            name,
            crate::interp::PolyConst {
                sym: o.sym,
                arity: o.vars.len(),
                typing: Ok(typing),
                defeq: Sealed::new(o.defeq).ok(),
                // An inductive constant's is *walked* — see the field's header.
                unfold_at_use: true,
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantInfo, DefKind};
    use crate::expr::{E, Level, Name, app, bvar, forall, konst, sort};

    fn n(s: &str) -> Name { Name::simple(s) }

    /// The `Environment` the declarations describe — what a *reference* to one
    /// of them needs, and what `run` alone does not build.
    fn env_of(ds: &[Declaration]) -> Environment {
        let mut env = Environment::empty();
        for d in ds {
            if let Declaration::Def { name, lparams, ty, value, .. } = d {
                env.insert_new(
                    *name,
                    ConstantInfo::Def { lparams: lparams.clone(), ty: *ty, value: *value },
                )
                .expect("a fresh name per declaration");
            }
        }
        env
    }

    /// A `def` whose type is `Sort u` and whose value is `Sort v`, at whatever
    /// parameters are asked for.
    fn def(name: &str, us: &[&str], ty: E, value: E) -> Declaration {
        Declaration::Def {
            name: n(name),
            lparams: us.iter().map(|s| n(s)).collect(),
            ty,
            value,
            kind: DefKind::Def,
        }
    }

    /// **The route runs, and it runs at a variable rung.**
    ///
    /// `def d.{u} : Sort (u+1) := Sort u` is the smallest declaration that has
    /// a level parameter in *both* halves and needs no constant, so it is the
    /// one thing this route can certify end to end today. Both certificates
    /// come back closed, which is the property the singular `discharge_levels`
    /// could not have produced.
    #[test]
    fn a_polymorphic_declaration_is_certified_at_its_own_parameter() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let d = def("d", &["u"], sort(u.succ()), sort(u));
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert!(led.apparatus, "the apparatus builds at route entry");
        assert_eq!(led.declarations, 1);
        assert_eq!(led.types_ok, 1, "⟦Sort (u+1)⟧ at a variable rung: {:?}", led.blocked);
        assert_eq!(led.values_ok, 1, "⟦Sort u⟧ at a variable rung: {:?}", led.blocked);
        // **Both halves, and this is the assertion that needed the batch
        // discharge.** Under the singular form the second theorem came back
        // with `u ∈ ω` still on it and `open` would be 1.
        assert_eq!(led.type_ev_ok, 1, "the type's certificate: {:?}", led.ev_blocked);
        assert_eq!(led.value_ev_ok, 1, "the value's certificate: {:?}", led.ev_blocked);
        assert_eq!(led.open, 0, "nothing escaped its discharge");
        assert!(led.is_clean(), "{:?}", led.rows());
    }

    /// **Three parameters, and the one the declaration mentions is the one
    /// assumed.** Two would pass under a constructor that bound them all to one
    /// variable; the strand's own rule.
    ///
    /// Run twice over one `Interp` as well, because the apparatus is built at
    /// route entry and [`Interp::levels`] is idempotent: a second file through
    /// the same `Interp` must produce the same counters and must not rebuild.
    #[test]
    fn the_route_is_idempotent_in_the_apparatus_and_picks_the_right_parameter() {
        let env = Environment::empty();
        let v = Level::param(n("v"));
        let d = def("d", &["u", "v", "w"], sort(v.succ()), sort(v));
        let mut ip = Interp::new();
        assert!(ip.levels_built().is_none(), "nothing built before the route runs");
        let first = run(&env, std::slice::from_ref(&d), &mut ip);
        let built = ip.levels_built().cloned().expect("built by the route");
        let again = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(first, again, "a second pass over one Interp must report the same");
        assert!(
            std::rc::Rc::ptr_eq(&built, ip.levels_built().expect("still built")),
            "the apparatus was rebuilt, which renumbers every later symbol"
        );
        assert!(first.is_clean(), "{:?}", first.rows());
    }

    /// **Zone B is owed, not excused** — and a declaration the environment does
    /// not own owes it with nothing to show.
    ///
    /// The declaration here is not in the `Environment`, so `zone_b` cannot
    /// resolve its type former or its recursor to anything: both are counted in
    /// `zone_b_consts`, neither is met, and `is_clean` is false. That is the
    /// conjunct's job, and it is the same job it did when the conjunct was
    /// `zone_b == 0` — the widening to `zone_b_ok == zone_b_consts` (see
    /// [`PolyLedger::is_clean`]) does not let this file through.
    ///
    /// **This is not a fixture asserting something stays broken.** An input
    /// naming a constant nothing declares is ill-formed rather than backlogged;
    /// no clause is scheduled to cure it, and the reason it reports —
    /// `no-interp(·)` — is a *scope* gap, not the threading gap this strand's
    /// clauses retire.
    ///
    /// # …and it is the only witness the pinned build point has
    ///
    /// The apparatus is forced at route entry rather than left to
    /// `Checker::poly`'s own idempotent force, because `level_poly` declares
    /// symbols off the shared `Env` and *when* it runs decides the numbering of
    /// every symbol minted after it. **Measured, that pin is invisible in the
    /// corpus rows**: removing it and rerunning all 91 tutorial exports
    /// produces byte-identical `polyledger` / `polyblocked` / `polyev` lines,
    /// because every one of those exports has at least one `def` or `axiom`,
    /// so `Checker::poly` builds the apparatus at the first declaration either
    /// way, and the ledger counts declarations and reasons rather than terms.
    ///
    /// A file of **nothing but** zone B is the cell where the two differ, and
    /// the tutorial corpus does not contain one. So the assertion below is not
    /// belt-and-braces on a covered property — it is the *whole* coverage the
    /// pin has, and without it the mutation that deletes the pin is green.
    /// Recorded here rather than dropped, per the branch's own rule.
    ///
    /// The empty environment is what keeps that witness: it stops `zone_b`
    /// before it can build a `Checker::poly`, so an apparatus present on the
    /// way out was built by the route entry and by nothing else. Adding `T` to
    /// the environment would interpret it and destroy the witness.
    #[test]
    fn an_inductive_the_environment_does_not_own_keeps_the_run_unclean() {
        let env = Environment::empty();
        let d = Declaration::Inductive {
            name: n("T"),
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::zero()),
            ctors: Vec::new(),
        };
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!((led.declarations, led.zone_b), (0, 1));
        // The type former and `T.rec`: owed, and neither met.
        assert_eq!((led.zone_b_ok, led.zone_b_consts), (0, 2), "{:?}", led.rows());
        assert!(!led.is_clean(), "an unmet zone-B constant is owed, not excused");
        assert!(led.rows()[0].contains("zoneB=1\tzoneBOk=0/2"), "{:?}", led.rows());
        // The pin. Nothing on this file ever constructs a `Checker::poly`, so
        // an apparatus built here was built by the route and by nothing else.
        assert!(led.apparatus, "the apparatus is built at route entry, not at the first def");
        assert!(ip.levels_built().is_some(), "…and it really is on the Interp");
    }

    /// Every zone-B constant is **either interpreted or carries a reason** —
    /// the accounting identity, and the one assertion that survives every cure.
    ///
    /// `zone_b_ok + Σ zone_b_blocked == zone_b_consts`. A clause that lands
    /// moves a constant from the right-hand histogram into `zone_b_ok` and the
    /// identity holds unchanged; what it *cannot* hold through is a constant
    /// dropped on the floor, which is "SKIP is not PASS" at the one place this
    /// route could still commit it. Pinning a per-bucket count instead would be
    /// a fixture asserting the recursor stays broken, which the next clause is
    /// scheduled to cure.
    fn owed_is_met_or_explained(led: &PolyLedger) {
        let blocked: usize = led.zone_b_blocked.values().sum();
        assert_eq!(
            led.zone_b_ok + blocked,
            led.zone_b_consts,
            "a zone-B constant was neither interpreted nor given a reason: {:?}",
            led.rows()
        );
    }

    /// `inductive R : Type` with `R.z : R`, `R.s : R → R` and
    /// `R.t : R → R → R` — the shape whose minor premises **open binders**.
    ///
    /// Three constructors of three different arities, and that is the point:
    /// a collapse applied at the outermost binder only certifies `R.s` and
    /// declines `R.t`, and one applied nowhere still certifies `R.z`, whose
    /// minor premise has no binder at all. Nothing under two field-carrying
    /// arities can tell those three apart.
    fn field_ind() -> (Environment, Declaration) {
        let r = n("R");
        let rr = || konst(r, [].into());
        let d = Declaration::Inductive {
            name: r,
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::zero().succ()),
            ctors: vec![
                (Name::str(&r, "z"), rr()),
                (Name::str(&r, "s"), forall(rr(), rr())),
                (Name::str(&r, "t"), forall(rr(), forall(rr(), rr()))),
            ],
        };
        let mut env = Environment::empty();
        crate::kernel::add(&mut env, &d).expect("a recursive inductive is accepted");
        (env, d)
    }

    /// `inductive T : Type` with `n` nullary constructors, in the environment.
    fn nullary_ind(names: &[&str]) -> (Environment, Declaration) {
        let d = Declaration::Inductive {
            name: n("T"),
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::zero().succ()),
            ctors: names.iter().map(|s| (Name::str(&n("T"), s), konst(n("T"), [].into()))).collect(),
        };
        let mut env = Environment::empty();
        crate::kernel::add(&mut env, &d).expect("a nullary enumeration is accepted");
        (env, d)
    }

    /// **A parameterless inductive is translated on the de-scheduled route** —
    /// the first zone-B clause, at the declaration's own instantiation.
    ///
    /// `T : Type` with three constructors. Its own instantiation is the empty
    /// vector, which is the *same* vector the scheduled route passes, so the
    /// mathematics here is the scheduled route's exactly: what is new is that
    /// the de-scheduled route reaches the declaration at all. That is the
    /// honest content of this clause and it is worth saying rather than
    /// dressing up — no construction in `derived/src/levels/` is spent, because
    /// a declaration with no universe parameter has no rung to vary.
    ///
    /// **Three constructors, not two.** The claim is that *each* constructor is
    /// keyed and stored under its own name, and two cannot tell that from a
    /// list stored twice under the first name or from a pair swapped end for
    /// end (`MEMORY`: two atoms cannot distinguish).
    ///
    /// The recursor is deliberately not asserted either way. `T.rec.{u}`
    /// carries the motive's level whatever `T` does, and it is the next clause;
    /// a count here would be this fixture asserting it stays broken. So
    /// `zone_b_ok` is checked as a **floor** where this project's habit is to
    /// compare a whole table for equality — the four names below are the
    /// equality, and the floor is the one column a cure is meant to raise.
    #[test]
    fn a_parameterless_inductive_is_translated_at_its_own_empty_instantiation() {
        let (env, d) = nullary_ind(&["a", "b", "c"]);
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(led.zone_b, 1, "{:?}", led.rows());
        // The type former, three constructors, and `T.rec`.
        assert_eq!(led.zone_b_consts, 5, "{:?}", led.rows());
        owed_is_met_or_explained(&led);
        // Each under its own name, at the empty instantiation.
        let t = n("T");
        for name in [t, Name::str(&t, "a"), Name::str(&t, "b"), Name::str(&t, "c")] {
            assert!(
                ip.get_const(&(name, Vec::new())).is_some(),
                "⟦{name}⟧ is owed at the declaration's own levels: {:?}",
                led.rows()
            );
        }
        assert!(led.zone_b_ok >= 4, "the type former and its three constructors: {:?}", led.rows());
    }

    /// **A zone-B declaration with a universe parameter of its own owes three
    /// constants, and every one of them is accounted for.**
    ///
    /// `Box.{u}` is the frontier — `zoneb::ensure` takes `inst: &[u32]`, so a
    /// declaration whose own instantiation is `[Level::param(u)]` cannot be
    /// asked about at all — and this fixture is deliberately **not** written as
    /// a claim about that.
    ///
    /// # What it does not assert, and why
    ///
    /// Not `symbolic-level == 3`, not `zone_b_ok == 0`, not `!is_clean()`.
    /// Every one of those is a claim that `Box.{u}` stays uninterpreted, and
    /// the next clause group is scheduled to cure exactly that —
    /// `DECISIONS.md` (2026-08-10): distance in the backlog is not safety.
    /// This branch has already gone red twice on a fixture that pinned the
    /// frontier it was standing on.
    ///
    /// What is left is what a cure cannot change: the declaration owes a type
    /// former, a constructor and a recursor whatever the route can do with
    /// them, and `owed_is_met_or_explained` says none of the three was passed
    /// over. `is_clean`'s refusal is covered by
    /// `an_inductive_the_environment_does_not_own_keeps_the_run_unclean`, whose
    /// negative is a **scope** gap on the other axis and so is unreachable from
    /// any clause this strand will land.
    #[test]
    fn a_universe_parameter_of_its_own_owes_three_constants_and_accounts_for_them() {
        let u = Level::param(n("u"));
        let d = Declaration::Inductive {
            name: n("Box"),
            lparams: vec![n("u")],
            num_params: 0,
            ty: sort(u.succ()),
            ctors: vec![(Name::str(&n("Box"), "mk"), konst(n("Box"), [u].into()))],
        };
        let mut env = Environment::empty();
        crate::kernel::add(&mut env, &d).expect("Box.{u} is accepted");
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!((led.zone_b, led.zone_b_consts), (1, 3), "Box, Box.mk, Box.rec: {:?}", led.rows());
        owed_is_met_or_explained(&led);
        // The row exists whatever the buckets in it say, so the census cannot
        // vanish silently the way a deleted test does.
        assert!(led.rows().iter().any(|r| r.starts_with("polyzoneb")), "{:?}", led.rows());
    }

    /// **The eliminator of a parameter-free declaration is built at a
    /// *symbolic* motive level** — the first eliminator off the ground
    /// schedule, and the answer to whether the motive level needs mathematics
    /// `derived/src/levels/` does not have.
    ///
    /// `Empty : Type` has no universe parameter, so its type former goes
    /// through at the empty instantiation like any other; `Empty.rec.{u}`
    /// carries the motive's level and used to stop at the `&[u32]` boundary.
    /// It goes through now, and what it spends is
    /// [`crate::interp::Interp::sort_of`] for `⟦Sort u⟧` and the already-landed
    /// `Π` clause for the motive's own type `⟦Empty → Sort u⟧` — **no new
    /// mathematics**, which is why `crate::recursor::empty_rec` is the route
    /// that could go first: it never reads `u₁`.
    ///
    /// # Both keys, and they are different keys
    ///
    /// `⟦Empty⟧` is stored at `[]` and `⟦Empty.rec⟧` at `[u]`. Asserting both
    /// is the point rather than belt-and-braces: the two instantiations differ
    /// by exactly the motive level, and a clause that keyed the eliminator on
    /// its declaration's list would put `⟦Empty.rec⟧` at `[]` and every later
    /// lookup would miss. That confusion is what `zoneb::ensure`'s own/ind
    /// split exists to prevent, and this is the first fixture where the two
    /// lists are not equal.
    #[test]
    fn a_parameter_free_declarations_eliminator_builds_at_a_symbolic_motive_level() {
        let e = n("Empty");
        let d = Declaration::Inductive {
            name: e,
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::zero().succ()),
            ctors: Vec::new(),
        };
        let mut env = Environment::empty();
        crate::kernel::add(&mut env, &d).expect("Empty is accepted");
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        // The type former and `Empty.rec` — both owed, both met.
        assert_eq!((led.zone_b_ok, led.zone_b_consts), (2, 2), "{:?}", led.rows());
        assert!(led.is_clean(), "{:?}", led.rows());
        owed_is_met_or_explained(&led);
        // `⟦Empty⟧` at the declaration's own (empty) instantiation…
        assert!(ip.get_const(&(e, Vec::new())).is_some(), "⟦Empty⟧");
        // …and `⟦Empty.rec⟧` at the *recursor's* own, which is one longer.
        let rec = Name::str(&e, "rec");
        let lps = env.get(&rec).expect("Empty.rec is generated").lparams().to_vec();
        assert_eq!(lps.len(), 1, "the motive's level is the recursor's own parameter");
        let own: Vec<Level> = lps.iter().map(|u| Level::param(*u)).collect();
        assert!(
            ip.get_const(&(rec, crate::ground::key_levels(&own))).is_some(),
            "⟦Empty.rec.{{u}}⟧ at a symbolic motive level: {:?}",
            led.rows()
        );
        // Not at the declaration's list — the keys are not interchangeable.
        assert!(
            ip.get_const(&(rec, Vec::new())).is_none(),
            "the eliminator must not be keyed on its declaration's instantiation"
        );
    }

    /// **An inductive constant gets a generic point too** — [`generic_points`],
    /// and the thing four eliminators were missing.
    ///
    /// `⟦Empty.rec.{u}⟧`'s typing is proved under `u ∈ ω`, which `Sealed`
    /// refuses at the keyed store — that refusal is the
    /// `ind-spec(…: hypothesis escaped the nest)` that `060_boolRec`,
    /// `061_twoBoolRec`, `067_nRec` and `115_rTreeRec` reported. They were not
    /// missing a derivation; they were missing **declaration exit**, which a
    /// `def` gets and an inductive never did.
    ///
    /// What is asserted here is that the exit now happens: a `PolyConst` exists
    /// for the eliminator, its arity is the recursor's own parameter count, and
    /// its typing is `Ok` — the `∀u. u ∈ ω → …` that `Sealed` will accept
    /// because the hypothesis has become an antecedent.
    ///
    /// **The keyed entry is still there and still says what it said.** The
    /// generic point does not replace it and must not: `const_evidence` prefers
    /// a keyed entry *with a certificate*, because the reduction route's ι
    /// rules are registered for that term and not for the generic point's
    /// instantiation of it. Pinning both here is what keeps the next tranche
    /// from "simplifying" one of them away.
    ///
    /// Non-vacuity and no more: the conclusion shape is the content of a
    /// kernel-certified `Thm`, and `generic_points`' own steps are pinned by
    /// the `debug_assert`s under them.
    #[test]
    fn an_eliminator_gets_a_generic_point_at_declaration_exit() {
        // A two-constructor enumeration, which is `Bool`'s shape. **Not
        // `Empty`**: `crate::recursor::empty_rec` never reads `u₁`, so its
        // typing is hypothesis-free already and nothing parks — measured, and
        // the reason this fixture is the one with constructors.
        let (env, d) = nullary_ind(&["ff", "tt"]);
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        let rec = Name::str(&n("T"), "rec");

        let p = ip
            .get_poly_const(&rec)
            .unwrap_or_else(|| panic!("⟦Empty.rec⟧ has no generic point: {:?}", led.rows()));
        assert_eq!(p.arity, 1, "the motive's level is the one argument");
        assert!(
            p.typing.is_ok(),
            "the typing must survive declaration exit, not `hypothesis escaped the nest`: {:?}",
            p.typing
        );
        assert!(
            p.typing.as_ref().is_ok_and(|s| s.thm().hyps().is_empty()),
            "discharged: `u ∈ ω` is an antecedent now, not a live hypothesis"
        );
        assert!(p.unfold_at_use, "an inductive constant's interpretation is walked");
        // And the keyed entry is untouched — both, or the reduction route loses
        // the term its rules were built for.
        let own = vec![Level::param(env.get(&rec).expect("generated").lparams()[0])];
        assert!(
            ip.get_const(&(rec, crate::ground::key_levels(&own))).is_some(),
            "the keyed entry must survive beside the generic point"
        );
    }

    /// **A class-(T) eliminator's motive binder comes apart at a symbolic
    /// motive level** — `crate::rec_dep::collapse_motive_ty`, and the reason
    /// axis it moves.
    ///
    /// `T.rec.{u}` used to stop at `crate::recursor::ensure`'s `numerals`
    /// predicate, which is the `&[u32]` **boundary** and says nothing about the
    /// eliminator. It now runs `crate::rec_dep::cx_of` at the variable rung —
    /// the motive's type `⟦T → Sort u⟧` is `ite0(succ(û), cndd, dprod)` there,
    /// collapsed by [`crate::interp::Interp::level_nonzero`] and
    /// [`crate::interp::Interp::pi_dprod_at`] with no case analysis — and stops
    /// at §6.2's own `u₁ = 0` split, which is a construction and not a
    /// boundary.
    ///
    /// # The axis, and why this cannot go red on the cure
    ///
    /// `DECISIONS.md` (2026-08-10): a fixture may not assert that something
    /// stays broken, and *distance in the backlog is not safety*. So this does
    /// **not** pin the split's own reason string — the next clause is scheduled
    /// to remove it, and an eliminator that certifies is not in
    /// [`PolyLedger::zone_b_blocked`] at all, so every assertion below still
    /// holds when it does.
    ///
    /// What is pinned is the two reasons this tranche **retired**, and each
    /// corresponds to one mutation:
    ///
    /// * `symbolic-level` — the boundary put back, i.e. `rec_dep::ensure` taking
    ///   numerals again;
    /// * `…the motive's type is not T p⃗ → Sort u₁` — the collapse deleted from
    ///   `cx_of`, which leaves the `ite0` where the product is expected and
    ///   declines under a label that is *false* about the declaration.
    ///
    /// Neither can be reintroduced by progress. Three constructors, so the
    /// declaration is a real class-(T) one with a real `decl_rect` behind it
    /// rather than a shape two atoms could imitate.
    #[test]
    fn an_eliminators_motive_binder_comes_apart_at_a_symbolic_motive_level() {
        let (env, d) = nullary_ind(&["a", "b", "c"]);
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        // The type former, three constructors and `T.rec` — every one accounted
        // for, which is what makes the reason table below the whole story.
        assert_eq!(led.zone_b_consts, 5, "{:?}", led.rows());
        owed_is_met_or_explained(&led);
        assert_eq!(led.open, 0, "the eliminator's route left no assumption open");
        for key in led.zone_b_blocked.keys() {
            assert_ne!(
                key, "symbolic-level",
                "the eliminator is past the &[u32] boundary; this is it put back: {:?}",
                led.rows()
            );
            assert!(
                !key.contains("the motive's type is not"),
                "the motive binder's type must collapse at a variable rung: {:?}",
                led.rows()
            );
        }
    }

    /// **A class-(T) eliminator is *one* term at a symbolic motive level** —
    /// `crate::rec_dep::split_bottom`, and the strand's objective stated as a
    /// test: every Lean term has one interpretation, with the level parameter
    /// an element of `ω`.
    ///
    /// `T.rec.{u}` is `•` where `u` is `0` and `drec t` where it is not, and at
    /// a parameter it is **neither and both** — the conditional
    /// `ite0(û, •, drec t)`, whose value at each instantiation is §6.2's own.
    /// Both clauses are built, each under its own kernel hypothesis, and joined
    /// by `Interp::ite0_merge`.
    ///
    /// # What is asserted, and why none of it can go red on progress
    ///
    /// This is a **positive** fixture throughout: the declaration certifies,
    /// so there is no reason string in it to rot. `zone_b_ok == zone_b_consts`
    /// at 5 of 5 — the type former, three constructors and the eliminator —
    /// with `is_clean()` and `open == 0`, and `⟦T.rec.{u}⟧` addressable at the
    /// recursor's own instantiation rather than the declaration's.
    ///
    /// The last assertion is the soundness one and it is the only negative:
    /// `IndApparatus::dep_elims` must hold **nothing** for this eliminator.
    /// `dep_bottom` files an equation `sym(…) = app(drec,t)` there for
    /// `crate::iota_dep` to reduce through; on this path `⟦T.rec⟧` is the
    /// conditional and not `drec`, so that equation would be true about its own
    /// symbol and *wrong* about the interpretation. A stored fact that is wrong
    /// about the thing it is filed under is discovered nowhere, which is
    /// exactly the class `crate::ev::Sealed` exists to keep out.
    ///
    /// Three constructors, so `decl_rect` is a real structural induction with
    /// three steps rather than a shape two atoms could imitate.
    #[test]
    fn an_eliminator_is_one_conditional_term_at_a_symbolic_motive_level() {
        let (env, d) = nullary_ind(&["a", "b", "c"]);
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(
            (led.zone_b_ok, led.zone_b_consts),
            (5, 5),
            "the type former, three constructors and T.rec, all interpreted: {:?}",
            led.rows()
        );
        assert!(led.is_clean(), "{:?}", led.rows());
        assert_eq!(led.open, 0, "the split's two assumptions were both discharged");
        owed_is_met_or_explained(&led);

        let t = n("T");
        let rec = Name::str(&t, "rec");
        let lps = env.get(&rec).expect("T.rec is generated").lparams().to_vec();
        let own: Vec<Level> = lps.iter().map(|u| Level::param(*u)).collect();
        let key = (rec, crate::ground::key_levels(&own));
        assert!(
            ip.get_const(&key).is_some(),
            "⟦T.rec.{{u}}⟧ at a symbolic motive level: {:?}",
            led.rows()
        );
        // **The bottom of the nest is the conditional itself**, which is the
        // assertion the objective actually names and the only one a
        // "took one clause and called it the interpretation" mutation fails.
        // Descend the λ-nest by body shape — five levels, one per binder of
        // `∀ C S⃗ t` — and read the head symbol off what is left.
        //
        // Head symbol, not "mentions an `ite0`": `⟦Sort u⟧` is *itself* an
        // `ite0` and occurs all over this nest, so an occurrence test is green
        // under every mutation. The bottom is `sym(û,p⃗,C,S⃗,t)` if one clause
        // was taken and `ite0(û, •, sym(…))` if both were.
        {
            let stored = ip.get_const(&key).expect("⟦T.rec.{u}⟧").term.clone();
            let ite0 = ip.levels().expect("the ω-vocabulary").i.sym;
            let mut cur = stored;
            let mut depth = 0;
            while let Some((site, _)) = ip.as_lam(&cur) {
                cur = site.skel.clone();
                depth += 1;
            }
            assert_eq!(depth, 5, "the nest binds the motive, three minors and the major premise");
            let (head, args) = ip.parts_of(&cur).expect("the bottom is an application");
            assert_eq!(
                head, ite0,
                "the eliminator's bottom must be §1.4's conditional, not one of its arms"
            );
            assert_eq!(args.len(), 3, "ite0(guard, proof clause, value clause)");
            assert_ne!(args[1], args[2], "the two clauses must not be the same term");
        }
        // …and the ι-reduction table must not have been told the eliminator is
        // `drec`, because here it is not.
        assert!(
            ip.ind_apparatus().is_some_and(|a| !a.dep_elims.contains_key(&key)),
            "the split path must file no dep_elim: ⟦T.rec⟧ is the conditional, not drec"
        );
    }

    /// **An eliminator whose minor premises open binders** — the per-binder
    /// frontier the `u₁ = 0` split left behind, closed by
    /// `crate::interp::Interp::as_pi_mem`.
    ///
    /// `an_eliminator_is_one_conditional_term_at_a_symbolic_motive_level`'s `T`
    /// is an enumeration: every constructor is field-free, so no minor premise
    /// has a binder and `Interp::as_pi` is never reached. That is exactly why
    /// it certified while `N`, `TwoBool`, `RTree` and `TypeWithTypeField` did
    /// not, and this fixture is the other side of that line — `R.s` and `R.t`
    /// carry fields, so `minor_at` walks a `Π` whose interpretation is §1.4's
    /// conditional and has to settle the guard to walk it.
    ///
    /// **Both arms need it, which corrected the sizing this was handed with.**
    /// The split's own header records the nonzero arm as needing no hypothesis;
    /// measured here, it needs one per binder just as the zero arm does. What
    /// differs is only which clause the guard selects.
    ///
    /// Positive throughout, so nothing in it rots on progress: 5 of 5 zone-B
    /// constants, `is_clean`, `open == 0`, and the bottom of `⟦R.rec.{u}⟧`
    /// still the conditional — the last because a collapse that leaked into the
    /// *eliminator's own* level, rather than staying at the minor premises',
    /// would take one clause and be greener for it.
    #[test]
    fn a_minor_premise_with_fields_collapses_its_binders_at_a_symbolic_motive_level() {
        let (env, d) = field_ind();
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(
            (led.zone_b_ok, led.zone_b_consts),
            (5, 5),
            "the type former, three constructors and R.rec, all interpreted: {:?}",
            led.rows()
        );
        assert!(led.is_clean(), "{:?}", led.rows());
        assert_eq!(led.open, 0, "the split's two assumptions were both discharged");
        owed_is_met_or_explained(&led);

        let rec = Name::str(&n("R"), "rec");
        let lps = env.get(&rec).expect("R.rec is generated").lparams().to_vec();
        let own: Vec<Level> = lps.iter().map(|u| Level::param(*u)).collect();
        let key = (rec, crate::ground::key_levels(&own));
        let stored = ip.get_const(&key).expect("⟦R.rec.{u}⟧").term.clone();
        let ite0 = ip.levels().expect("the ω-vocabulary").i.sym;
        let mut cur = stored;
        let mut depth = 0;
        while let Some((site, _)) = ip.as_lam(&cur) {
            cur = site.skel.clone();
            depth += 1;
        }
        assert_eq!(depth, 5, "the nest binds the motive, three minors and the major premise");
        let (head, args) = ip.parts_of(&cur).expect("the bottom is an application");
        assert_eq!(head, ite0, "the eliminator's bottom is still §1.4's conditional");
        assert_ne!(args[1], args[2], "the two clauses must not be the same term");
    }

    /// **An infinitary constructor's induction hypothesis, at a variable
    /// rung** — the *second* blind `as_pi` on this route, and the one the
    /// fixture above cannot reach.
    ///
    /// `Q.f : (E → Q) → Q` has a **function-typed** recursive slot, so
    /// `rec_dep::minor_at` opens an induction-hypothesis binder as well as a
    /// field binder and hands its domain — `⟦∀z:E, C (f z)⟧`, itself §1.4's
    /// conditional — to `rec_dep::ih_transport`, one level below where the
    /// minor premise's own collapse happens. A plain recursive slot (`R.s`,
    /// `R.t` above) has no crossing and never goes there, which is why this is
    /// a second fixture and not another constructor in the first: measured on
    /// the corpus, `RTree` was the one declaration of the four that still
    /// declined after `minor_at` alone was fixed.
    ///
    /// `E` has two constructors and `Q` two, so the block owes 4 + 4 = 8
    /// zone-B constants; the assertion is the whole pair, met.
    #[test]
    fn an_infinitary_minor_premise_transports_its_hypothesis_at_a_symbolic_motive_level() {
        let (e, q) = (n("E"), n("Q"));
        let (ee, qq) = (|| konst(e, [].into()), || konst(q, [].into()));
        let de = Declaration::Inductive {
            name: e,
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::zero().succ()),
            ctors: vec![(Name::str(&e, "a"), ee()), (Name::str(&e, "b"), ee())],
        };
        let dq = Declaration::Inductive {
            name: q,
            lparams: Vec::new(),
            num_params: 0,
            ty: sort(Level::zero().succ()),
            ctors: vec![
                (Name::str(&q, "z"), qq()),
                (Name::str(&q, "f"), forall(forall(ee(), qq()), qq())),
            ],
        };
        let mut env = Environment::empty();
        crate::kernel::add(&mut env, &de).expect("E is accepted");
        crate::kernel::add(&mut env, &dq).expect("an infinitary constructor is accepted");
        let ds = [de, dq];
        let mut ip = Interp::new();
        let led = run(&env, &ds, &mut ip);
        assert_eq!(
            (led.zone_b_ok, led.zone_b_consts),
            (8, 8),
            "two type formers, four constructors and two eliminators: {:?}",
            led.rows()
        );
        assert!(led.is_clean(), "{:?}", led.rows());
        assert_eq!(led.open, 0, "every assumption the two splits opened was discharged");
        owed_is_met_or_explained(&led);
    }

    /// **A `mutual` block is recorded and never handed to `zoneb::ensure`** —
    /// and this is a *soundness* guard, not a coverage one.
    ///
    /// `zoneb::ensure` resolves a name through the environment, where a block's
    /// members are indistinguishable from single inductives, so deleting the
    /// `Mutual` arm in [`zone_b`] does not produce a decline.
    /// `crate::ledger::fill_declaration` carries the same guard for the
    /// scheduled route and predicts the failure: an interpretation of `A` built
    /// as though `B` did not exist.
    ///
    /// **Mutation run, and what it actually does is worse.** With the arm
    /// deleted and the block's members routed through the loop below, this test
    /// **overflows the stack** rather than returning a wrong `⟦A⟧`: `A.mk`'s
    /// field is `B`, whose constructor's field is `A`, and `ensure` re-enters
    /// at a declaration whose carrier is being built. The silent
    /// mis-translation `fill_declaration` names is what a *degenerate* block —
    /// two independent types written in one `mutual` — would get; a genuinely
    /// recursive one does not get that far. Either way the arm is load-bearing,
    /// and this fixture is the only thing on this route that would notice.
    /// Recorded rather than left as a prediction, because the prediction was
    /// not what happened.
    ///
    /// Not a fixture asserting something stays broken either: when the mutual
    /// encoding lands, `mutual_aux::expand` rewrites the block *before* this
    /// route sees it and this arm is not reached at all. What is pinned is what
    /// happens to a block the encoder declined, which stays declined by
    /// construction.
    #[test]
    fn a_mutual_block_is_recorded_and_never_interpreted_member_by_member() {
        let (a, b) = (n("A"), n("B"));
        // `A : Type` with `A.mk : B → A`, `B : Type` with `B.mk : A → B` — a
        // genuine block: neither member's constructor types without the other.
        let types = vec![
            crate::env::IndType {
                name: a,
                ty: sort(Level::zero().succ()),
                ctors: vec![(
                    Name::str(&a, "mk"),
                    forall(konst(b, [].into()), konst(a, [].into())),
                )],
            },
            crate::env::IndType {
                name: b,
                ty: sort(Level::zero().succ()),
                ctors: vec![(
                    Name::str(&b, "mk"),
                    forall(konst(a, [].into()), konst(b, [].into())),
                )],
            },
        ];
        let d = Declaration::Mutual { lparams: Vec::new(), num_params: 0, types };
        let mut env = Environment::empty();
        crate::kernel::add(&mut env, &d).expect("the block is accepted");
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        // Two members, each a type former, a constructor and a recursor.
        assert_eq!((led.zone_b, led.zone_b_consts), (1, 6), "{:?}", led.rows());
        assert_eq!(led.zone_b_ok, 0, "no member of a block may be interpreted alone");
        // The second, independent witness for `is_clean`'s zone-B conjunct —
        // on a negative that is design-stable rather than backlogged, because
        // a block this arm records is a block the encoder declined. One
        // witness for a guard this load-bearing is one too few.
        assert!(!led.is_clean(), "a block nothing can interpret is owed, not excused");
        owed_is_met_or_explained(&led);
        for name in [a, b, Name::str(&a, "mk"), Name::str(&b, "mk")] {
            assert!(
                ip.get_const(&(name, Vec::new())).is_none(),
                "⟦{name}⟧ built without the rest of its block would be a wrong theorem"
            );
        }
        // The encoder's own reason, not this route's fallback.
        assert!(
            led.rows().iter().any(|r| r.starts_with("polyzoneb") && r.contains("ind-spec(")),
            "{:?}",
            led.rows()
        );
    }

    /// **The `is_clean` widening agrees with the conjunct it replaced on every
    /// file that conjunct accepted.**
    ///
    /// `zone_b == 0` implies `zone_b_consts == 0` implies
    /// `zone_b_ok == zone_b_consts`, so a file with no inductive is clean under
    /// both. The direction that matters is the other one, and it is the
    /// previous three tests: a file *with* an inductive now has to earn it.
    /// Without this control the widening could have been a weakening nobody
    /// measured — the guard `Outcome::fully_certified` reads.
    #[test]
    fn a_file_with_no_zone_b_is_clean_exactly_as_before() {
        let env = Environment::empty();
        let d = def("d", &[], sort(Level::zero().succ()), sort(Level::zero()));
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!((led.zone_b, led.zone_b_consts, led.zone_b_ok), (0, 0, 0));
        assert!(led.is_clean(), "{:?}", led.rows());
        owed_is_met_or_explained(&led);
    }

    /// **A monomorphic declaration on this route is the scheduled one.** With
    /// no `lparams` there is no ω-variable, `Checker::poly`'s thread is
    /// `Checker::threaded`'s, and `⟦Sort 0⟧` is the ground rung — so the two
    /// routes agree on the population where they overlap, which is what makes
    /// the poly row readable against the scheduled one at all.
    #[test]
    fn a_monomorphic_declaration_takes_the_ground_rung_on_this_route() {
        let env = Environment::empty();
        let d = def("d", &[], sort(Level::zero().succ()), sort(Level::zero()));
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert!(led.is_clean(), "{:?}", led.rows());
        // The value is `⟦Sort 0⟧` and it is `U₀`, not `srt(0̄)`.
        let mut c = Checker::poly(&env, &mut ip, &[]).expect("poly");
        let t = c.infer_type(&sort(Level::zero())).expect("infer");
        drop(c);
        assert_eq!(t.tm, Some(ip.sort(0)), "a monomorphic Sort 0 must stay the ground rung");
    }

    /// **The `Π` clause at a variable rung, end to end through the route.**
    ///
    /// `def d.{u} : Sort (u+1) := Sort u → Sort u` — the value is a `Π` whose
    /// *both* levels are the declaration's own parameter, so neither the
    /// scheduled `l2 == 0` split nor `as_numeral` can reach it. Before the
    /// clause landed this was `polyblocked symbolic-level`; now it interprets
    /// to `ite0(û, cndd(⟦Sort u⟧), dprod(⟦Sort u⟧))` and certifies.
    ///
    /// The type is `Sort (u+1)` rather than the `Π`'s real type because this
    /// route infers the two halves independently and does not check them
    /// against each other — see `run`.
    #[test]
    fn a_pi_at_a_variable_rung_interprets_and_certifies() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let arrow = forall(sort(u), sort(u));
        let d = def("d", &["u"], sort(u.succ()), arrow);
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(led.values_ok, 1, "⟦Π x:Sort u. Sort u⟧: {:?}", led.rows());
        assert_eq!(led.value_ev_ok, 1, "…and its typing: {:?}", led.rows());
        assert_eq!(led.open, 0, "the Π clause discharged everything it opened");
        assert!(
            !led.blocked.contains_key("symbolic-level"),
            "the Π clause still wants a numeral: {:?}",
            led.blocked
        );
    }

    /// **The mixed case, which is the one the bridge exists for.**
    ///
    /// `Sort 0 → Sort u` has one numeral level and one parameter, so the
    /// domain's membership arrives spelled `⟦A⟧ ∈ U₀` while `pi_imax_dep`
    /// states its premise over `srt(0̄)`. `Interp::mem_at_srt` is what
    /// reconciles them, and this is the shape that exercises it — a test with
    /// two parameters and no numeral would pass with the bridge deleted.
    ///
    /// Both orders, because the domain's premise and the fibre's are
    /// reconciled by two *different* calls and a bridge applied to only one of
    /// them would pass whichever test used it.
    #[test]
    fn a_pi_mixing_a_numeral_level_with_a_parameter_bridges_both_ways() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let z = Level::zero();
        for (i, body) in [forall(sort(z), sort(u)), forall(sort(u), sort(z))].into_iter().enumerate()
        {
            let d = def("d", &["u"], sort(u.succ()), body);
            let mut ip = Interp::new();
            let led = run(&env, std::slice::from_ref(&d), &mut ip);
            assert_eq!(led.values_ok, 1, "case {i} did not interpret: {:?}", led.rows());
            assert_eq!(led.open, 0, "case {i} left an assumption open");
            // The certificate is the point; `mem_at_srt` returning `None` shows
            // up here and nowhere else.
            assert_eq!(led.value_ev_ok, 1, "case {i} lost its certificate: {:?}", led.rows());
        }
    }

    /// **A nonzero numeral codomain needs no `ite0` collapse, measured.**
    ///
    /// `Checker::pi_evidence_poly`'s header predicted this case would be
    /// declined: `imax ℓ k` for nonzero `k` was expected to arrive already
    /// normalised by Lean to `max ℓ k`, mismatching the rule's
    /// `srt(ite0(k̄, ∅, ℓ̂ ∪ k̄))` and waiting on `Ite0::when_nonzero`. It is
    /// **not** normalised — `Level::imax(u, 1)` is `imax(u,(0+1))`, mini's
    /// smart constructor keeps the node — so `sort_of` spells the target
    /// exactly as the rule concludes it and the clause certifies.
    ///
    /// Kept as a test rather than deleted with the prediction, because it is
    /// the only thing standing between that paragraph and rotting back: if a
    /// future `Level::imax` *does* start collapsing, this goes red at the
    /// clause rather than silently at the next tranche's measurement.
    ///
    /// `k = 0` is included and is a different case — `imax ℓ 0` is `0`, the
    /// `Prop` clause — so the loop covers both sides of `ite0`'s split.
    #[test]
    fn a_pi_over_a_nonzero_numeral_codomain_needs_no_ite0_collapse() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        for k in 0..3u32 {
            let l2 = crate::ground::numeral(k);
            let d = def("d", &["u"], sort(u.succ()), forall(sort(u), sort(l2)));
            let mut ip = Interp::new();
            let led = run(&env, std::slice::from_ref(&d), &mut ip);
            assert_eq!(led.values_ok, 1, "Sort u → Sort {k} did not interpret: {:?}", led.rows());
            assert_eq!(led.value_ev_ok, 1, "Sort u → Sort {k} uncertified: {:?}", led.rows());
            assert_eq!(led.open, 0, "Sort u → Sort {k} left an assumption open");
        }
    }

    /// **A `Π` at a variable rung comes apart again once its guard is
    /// settled** — [`crate::interp::Interp::level_nonzero`] and
    /// [`crate::interp::Interp::pi_dprod_at`].
    ///
    /// The `Π` clause certifies `ite0(ℓ̂₂, cndd, dprod)` in one theorem and
    /// needs no clause to do it. **Everything downstream of a `Π` does**:
    /// [`crate::interp::Interp::as_pi`] dispatches on the head symbol, and at a
    /// variable rung the head is `ite0`. This is the way back on the value
    /// side, and the case it is built for is the one Lean writes by itself: a
    /// codomain that is a *sort*, `ℓ₂ = ℓ + 1`, which is never zero.
    ///
    /// Three successors and not one — `u+1`, `u+2` and `max(u,v)+1` — because
    /// two would pass under a `level_nonzero` that read only the outermost
    /// `succ` and ignored what is under it, and the third is the one whose
    /// premise needs `Order::max_in_omega` rather than the parameter's own
    /// hypothesis.
    ///
    /// Non-vacuity, three ways: the collapsed right-hand side must **decompose
    /// as a `Π`** where the `ite0` does not; the equation's left side must be
    /// the term the clause actually built, not one rebuilt here; and the
    /// theorem must carry exactly the level hypotheses of the parameters its
    /// level mentions.
    ///
    /// The last case is the boundary and is asserted from the other side: a
    /// bare parameter `ℓ₂ = u` is **not** settled, and must not be. `Sort u`
    /// is `Prop` at `u = 0` and a universe above it, so a construction that
    /// answered there would be claiming a clause it cannot see.
    #[test]
    fn a_pi_over_a_sort_comes_apart_at_a_variable_rung() {
        let env = Environment::empty();
        let (u, v) = (Level::param(n("u")), Level::param(n("v")));
        let mut ip = Interp::new();
        let mut c = Checker::poly(&env, &mut ip, &[n("u"), n("v")]).expect("poly");
        // `∀ x : Sort u. Sort b` — the codomain is `Sort b`, so the level the
        // `ite0` guards on is `ℓ₂ = b + 1`. That is the whole reason a motive
        // binder is decidable: Lean writes the codomain as a sort and a sort's
        // own level is a successor.
        let cases = [("u+1", u), ("u+2", u.succ()), ("max(u,v)+1", Level::max(u, v))];
        let mut got = Vec::new();
        for (label, b) in cases {
            let t = c.infer_type(&forall(sort(u), sort(b))).expect("infer");
            got.push((label, b.succ(), t.tm.clone().unwrap_or_else(|| panic!("{label}: no ⟦Π⟧"))));
        }
        let vars = c.level_vars();
        drop(c);

        for (label, l2, pi) in got {
            let ne = ip
                .level_nonzero(&l2, &vars)
                .unwrap_or_else(|| panic!("{label}: ¬(ℓ̂₂ = ∅) is owed at a successor"));
            // Exactly the parameters the level mentions, and no others.
            let want_hyps = if label == "max(u,v)+1" { 2 } else { 1 };
            assert_eq!(ne.hyps().len(), want_hyps, "{label}: the level hypotheses carried");
            let eq = ip
                .pi_dprod_at(&pi, &ne)
                .unwrap_or_else(|| panic!("{label}: the ite0 did not collapse"));
            let (lhs, rhs) = eq.concl().as_eq().expect("an equation");
            assert_eq!(lhs, pi, "{label}: the equation must be about the term the clause built");
            assert!(
                matches!(ip.as_pi(&rhs), Some(crate::interp::PiShape::Dep { .. })),
                "{label}: the collapsed Π must decompose, which is the whole point"
            );
        }
        // `Sort u` is `Prop` at `u = 0`; neither half may be claimed.
        assert!(
            ip.level_nonzero(&u, &vars).is_none(),
            "a bare parameter is zero at some instantiation and must not be settled"
        );
        assert!(
            ip.level_nonzero(&Level::zero(), &vars).is_none(),
            "…nor may `0`, whose ite0 takes the other branch"
        );
    }

    /// **The type's slot and the value's slot are the slots they came from.**
    ///
    /// A declaration whose type has no certificate and whose value does is not
    /// a corner case: it is what `015_levelParams` did when this was written.
    /// The two theorems are closed in one batch, so putting them back takes an
    /// index, and getting that wrong reported the **value's** certificate as
    /// absent under the reason `inference-error` — a key no clause on this
    /// route can mint, which is the only reason it was visible at all.
    ///
    /// # The fixture may not assert that something stays broken
    ///
    /// This first used `Sort u → Sort u` as the uninterpretable type, because
    /// the `Π` clause wanted a numeral. **The `Π` clause then landed one
    /// tranche later and this test went red on the cure** — it was asserting
    /// `typesOk == 0` about the very clause whose purpose was to make it 1.
    /// That is the branch's own rule, and this is the second time it has
    /// caught something.
    ///
    /// A string literal is the replacement, and the choice is the point:
    /// `Gap::StrLit` is not *waiting* on anything. Mini declines string
    /// literals as a matter of interpretation **scope**, not of unfinished
    /// threading (MINI-DESIGN.md §0's two axes), so no clause conversion can
    /// cure it and this fixture cannot go red on progress a second time.
    ///
    /// **The axis is what makes it safe, not the distance.** Re-founding this
    /// on the next dark thing — a constant at a parametric level, 109 sites
    /// today — would have failed again at the very next slice. `DECISIONS.md`
    /// 2026-08-10 is the rule: when a stays-broken fixture is cured, cross to
    /// the *other* axis rather than moving further along the same one.
    ///
    /// The pair is not well-typed and does not need to be — this route infers
    /// the two halves independently and checks neither against the other.
    #[test]
    fn a_missing_type_certificate_does_not_eat_the_values() {
        let env = Environment::empty();
        let u = Level::param(n("u"));
        let d = def("d", &["u"], crate::expr::str_lit("not a type"), sort(u));
        let mut ip = Interp::new();
        let led = run(&env, std::slice::from_ref(&d), &mut ip);
        assert_eq!(led.types_ok, 0, "a string literal interprets to nothing: {:?}", led.rows());
        assert_eq!(led.type_ev_ok, 0);
        assert_eq!(
            led.blocked.get("strLit"),
            Some(&1),
            "…and the reason is scope, not threading: {:?}",
            led.blocked
        );
        assert_eq!(led.values_ok, 1, "⟦Sort u⟧ interprets: {:?}", led.rows());
        // The assertion the misalignment failed, and the reason it minted.
        assert_eq!(led.value_ev_ok, 1, "the value's certificate went to the type's slot");
        assert_eq!(led.open, 0);
        assert!(
            !led.ev_blocked.contains_key("inference-error"),
            "`inference-error` is unmintable on this route: {:?}",
            led.ev_blocked
        );
    }

    /// **A use under a *different parameter name* hits** — the miss the
    /// generic point exists to sidestep, `LEVELPOLY.md` §5.3 step 5.
    ///
    /// This is the axis and nothing else. The obvious design keys the store by
    /// the widened [`crate::interp::ConstKey`] and looks a use up at
    /// `ground::key_levels(ls)`; `key_levels` canonicalises by `simplify()` but
    /// does **not** rename parameters positionally, so `(d,[param u])` and
    /// `(d,[param v])` are two keys and this file — where `d` is declared over
    /// `u` and used over `v` — misses. The *checker's* own step-5 fixture pins
    /// exactly that miss on its side. Keyed by [`Name`] alone the parameter's
    /// name never enters the key at all, so there is nothing to disagree.
    ///
    /// Renaming `v` to `u` in `e` must keep this green: a fixture that only
    /// passes at one spelling is testing the spelling.
    #[test]
    fn a_use_under_a_different_parameter_name_hits_the_generic_point() {
        let (u, v) = (Level::param(n("u")), Level::param(n("v")));
        let d = def("d", &["u"], sort(u.succ()), sort(u));
        let e = def("e", &["v"], sort(v.succ()), konst(n("d"), [v].into()));
        let ds = [d, e];
        let env = env_of(&ds);
        let mut ip = Interp::new();
        let led = run(&env, &ds, &mut ip);
        assert_eq!(led.stored, 2, "both declarations mint a generic point: {:?}", led.rows());
        assert_eq!(
            led.const_ev_ok, 2,
            "the use at `v` of a constant declared over `u`: {:?}",
            led.rows()
        );
        assert!(led.is_clean(), "{:?}", led.rows());
    }

    /// **The generic point is instantiated positionally, and a permutation is
    /// what shows it.**
    ///
    /// Three parameters, used in a rotated order — `d.{c,a,b}` — because two
    /// cannot distinguish a transposition from an identity and one cannot
    /// distinguish anything. The assertion is on the **conclusion**, not on a
    /// counter: `f̂`'s arguments and the set the membership is about must both
    /// be at the *use site's* levels in the *use site's* order. A store that
    /// handed back the theorem at the wrong permutation would still be a
    /// theorem, still `Proved`, and still counted — which is precisely the
    /// silent failure `pi_typing_of`'s conclusion check exists for, one clause
    /// over.
    #[test]
    fn the_generic_point_is_instantiated_positionally_at_three_parameters() {
        let (u, v, w) = (Level::param(n("u")), Level::param(n("v")), Level::param(n("w")));
        let big = Level::max(u, Level::max(v, w));
        let d = def("d", &["u", "v", "w"], sort(big.succ()), sort(big));
        let ds = [d];
        let env = env_of(&ds);
        let mut ip = Interp::new();
        let led = run(&env, &ds, &mut ip);
        assert_eq!(led.const_ev_ok, 1, "{:?}", led.rows());
        let sym = ip.get_poly_const(&n("d")).expect("stored").sym;

        // The use site: a fresh declaration over `a,b,c`, referring to
        // `d.{c,a,b}`. Its type is therefore `Sort ((max c (max a b))+1)`.
        let (a, b, c) = (Level::param(n("a")), Level::param(n("b")), Level::param(n("c")));
        let mut ck = Checker::poly(&env, &mut ip, &[n("a"), n("b"), n("c")]).expect("poly");
        let t = ck.infer_type(&konst(n("d"), [c, a, b].into())).expect("infer");
        let vars = ck.level_vars();
        drop(ck);

        let args: Vec<_> =
            [c, a, b].iter().map(|l| ip.level_term(l, &vars).expect("ℓ̂")).collect();
        let want_tm = ip.mk(sym, args);
        let want_set =
            ip.sort_of(&Level::max(c, Level::max(a, b)).succ(), &vars).expect("⟦Sort ·⟧");
        assert_eq!(t.tm, Some(want_tm.clone()), "⟦d.{{c,a,b}}⟧ is f̂ at the rotated levels");
        assert_eq!(
            t.ev.thm().map(|t| t.concl().clone()),
            Some(kernel::Formula::mem(want_tm, want_set)),
            "the instantiated typing is about the rotated levels, in that order"
        );
    }

    /// **A generic point with no certificate still interprets.** The two axes
    /// are separate (MINI-DESIGN.md §0) and the store keeps them separate: a
    /// `def` whose value has no typing still gets its abbreviation, so a later
    /// reference to it has a *term* and moves `valuesOk` where it cannot move
    /// `valueEv`.
    ///
    /// `d`'s value is an application of a bound variable, which interprets and
    /// has no certificate on this route. Were the store to refuse the whole
    /// entry on a missing typing, `e` below would report `no-interp(d)` — the
    /// reason the ground path reserves for a constant that *denotes nothing*.
    #[test]
    fn a_generic_point_is_stored_without_a_typing_and_still_names_a_term() {
        let u = Level::param(n("u"));
        // `def d.{u} : Sort u → Sort u := fun (x : Sort u) => x`
        let d = def(
            "d",
            &["u"],
            forall(sort(u), sort(u)),
            crate::expr::lam(sort(u), crate::expr::bvar(0)),
        );
        let e = def("e", &["u"], forall(sort(u), sort(u)), konst(n("d"), [u].into()));
        let ds = [d, e];
        let env = env_of(&ds);
        let mut ip = Interp::new();
        let led = run(&env, &ds, &mut ip);
        assert_eq!(led.stored, 2, "an entry per declaration: {:?}", led.rows());
        assert!(
            ip.get_poly_const(&n("d")).is_some(),
            "the abbreviation is stored whatever the typing did"
        );
        // The term axis reached `e` — which is the whole claim.
        assert_eq!(led.values_ok, 2, "⟦d.{{u}}⟧ names a term at the use site: {:?}", led.rows());
        assert!(
            !led.blocked.contains_key("no-interp(d)"),
            "a stored constant is never `no-interp`: {:?}",
            led.blocked
        );
    }

    /// **A ground use of a polymorphic constant, and what the §1.2 bridge
    /// costs** — the one thing `LEVELPOLY.md` §5.3 step 5 said to *measure*
    /// rather than assume.
    ///
    /// `d.{0}` instantiates the generic point at `∅`, so its typing is about
    /// `srt(succ ∅)`. A fresh `⟦Sort 1⟧` at the use site is `U₁`
    /// ([`Interp::sort`]), because [`Interp::sort_of`]'s numeral branch is
    /// deliberately term-for-term the ground one. The two are **provably
    /// equal and not the same term** — [`Interp::rung_bridge`] is the
    /// equation — so the instantiation delivers a true typing at the ω
    /// spelling and the declared-type retarget, which compares terms, does
    /// not close.
    ///
    /// What is asserted here is what the clause **does**: the constant
    /// interprets at a ground use and its typing is derived. The spelling
    /// residue is a measurement and lives in `LEVELPOLY.md` §5.3, not in an
    /// assertion — a fixture that pinned `const_ev_ok == 0` would be pinning
    /// the bridge's absence, and the bridge is scheduled to be built.
    #[test]
    fn a_ground_use_of_a_polymorphic_constant_interprets_and_certifies() {
        let u = Level::param(n("u"));
        let d = def("d", &["u"], sort(u.succ()), sort(u));
        let e = def("e", &[], sort(Level::zero().succ().succ()), konst(n("d"), [Level::zero()].into()));
        let ds = [d, e];
        let env = env_of(&ds);
        let mut ip = Interp::new();
        let led = run(&env, &ds, &mut ip);
        assert_eq!(led.values_ok, 2, "⟦d.{{0}}⟧ is a term: {:?}", led.rows());
        assert_eq!(
            led.value_ev_ok, 2,
            "…and the instantiation at `∅` really derives a typing: {:?}",
            led.rows()
        );
        assert_eq!(led.open, 0, "a closed level vector discharges unconditionally");
    }

    /// **Nothing is stored on the σ-scheduled route**, which is what makes
    /// `const_evidence`'s new first lookup inert there by construction rather
    /// than by measurement — and so what makes Gate A's byte-identity a
    /// property of the code instead of a property of the corpus.
    #[test]
    fn the_scheduled_route_writes_no_generic_point() {
        let u = Level::param(n("u"));
        let d = def("d", &["u"], sort(u.succ()), sort(u));
        let ds = [d];
        let env = env_of(&ds);
        let mut ip = Interp::new();
        let mut sched = std::collections::HashMap::new();
        sched.insert(n("d"), vec![vec![0u32]]);
        let _ = Ledger::run(&env, &ds, &sched, &mut ip);
        assert_eq!(ip.poly_const_count(), 0, "the scheduled route filled the poly store");
        assert!(ip.const_count() > 0, "…while filling the one it owns");
    }

    /// **Zone A's own type comes apart at a sort-valued binder** — the
    /// obstacle the four eliminator wrappers stopped at, in the smallest
    /// declaration that has it and no inductive at all.
    ///
    /// `axiom a.{u} : ∀ (m : Sort 1 → Sort u) (x : Sort 1), m x`
    ///
    /// The codomain `m x` is an **application**, so certifying the type needs
    /// `crate::kernel`'s `Expr::App` rule at `m`, whose own type is
    /// `Sort 1 → Sort u`. At a variable rung §1.4's `Π` clause emits that as
    /// `ite0(succ(û), cndd, dprod)` and [`crate::interp::Interp::as_pi`] is
    /// blind to it — and this node is zone A, so unlike
    /// `crate::rec_dep::minor_at` it holds **no `Guard`** to settle the
    /// conditional with. What settles it is that the guard is a *successor*,
    /// unconditionally, which is
    /// [`crate::interp::Interp::succ_nonzero_at`].
    ///
    /// # Why an `axiom` and why this exact type
    ///
    /// An `axiom` has no value, so `valuesOk`/`valueEv` are vacuous and the
    /// only conjunct left for [`PolyLedger::is_clean`] is the one under test.
    /// A declaration whose type were merely `Sort u` would pass without any of
    /// this — the `Π` *formation* rule certifies the `ite0` in one theorem and
    /// never takes it apart. **It is the elimination that was blind**, so the
    /// type has to apply something, and the thing it applies has to be a
    /// binder whose own type is a `Π` into a sort.
    ///
    /// **Two binders and not one.** With `m` alone the application's argument
    /// would have to be a closed term and the node would be exercised at a
    /// constant; `x` makes the argument a scope variable, which is what every
    /// one of the four corpus declarations passes (`motive false`, `motive t`).
    ///
    /// The **control is `k`**, the same shape with `Sort u` replaced by
    /// `Sort 1`: a ground codomain emits the product directly, `as_pi` answers
    /// on its own, and it certified before this clause existed. Both are run
    /// through one route, so a change that broke the ground path would show up
    /// here and not only in Gate A.
    #[test]
    fn a_sort_valued_binder_is_applied_in_zone_as_own_type() {
        let one = Level::zero().succ();
        let u = Level::param(n("u"));
        // `∀ (m : Sort 1 → Sort ℓ) (x : Sort 1), m x`
        let ty_at = |l: Level| {
            forall(
                forall(sort(one), sort(l)),
                forall(sort(one), app(bvar(1), bvar(0))),
            )
        };
        let cases = [("Sort u", u, vec![n("u")]), ("Sort 1", one, Vec::new())];
        for (label, l, lparams) in cases {
            let d = Declaration::Axiom { name: n("a"), lparams, ty: ty_at(l) };
            let env = Environment::empty();
            let mut ip = Interp::new();
            let led = run(&env, std::slice::from_ref(&d), &mut ip);
            assert_eq!(led.declarations, 1, "{label}");
            assert_eq!(led.types_ok, 1, "{label}: ⟦ty⟧ is owed: {:?}", led.blocked);
            assert_eq!(
                led.type_ev_ok, 1,
                "{label}: the type's certificate is owed: {:?}",
                led.ev_blocked
            );
            assert_eq!(led.values_attempted, 0, "{label}: an axiom has no value");
            assert_eq!(led.open, 0, "{label}: nothing escaped its discharge");
            assert!(led.is_clean(), "{label}: {:?}", led.rows());
        }
    }

    /// The row is wire-safe in the same sense `Ledger`'s is: one `key=value`
    /// per tab, and the harness splits on the first `=`.
    #[test]
    fn every_poly_row_is_wire_safe() {
        let mut led = PolyLedger { apparatus: true, ..Default::default() };
        led.blocked.insert("no-interp(Nat)".to_string(), 3);
        led.ev_blocked.insert("symbolic-level".to_string(), 1);
        for row in led.rows() {
            let mut it = row.split('\t');
            assert!(it.next().is_some_and(|t| !t.contains('=')), "the tag is bare: {row}");
            for cell in it {
                assert!(cell.contains('='), "every cell is key=value: {cell:?} in {row}");
                assert!(!cell.contains(' '), "no spaces around the separator: {cell:?}");
            }
        }
    }
}

