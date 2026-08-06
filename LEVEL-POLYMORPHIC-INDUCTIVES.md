# Level-polymorphic inductives: is the carrier one set or one per instantiation?

Theory analysis, 2026-08-01. Read-only investigation; sources are the thesis
(line numbers refer to the extracted `thesis.txt`, sections quoted alongside),
the corpus exports (read, not inferred from names), and the current code.
Question asked: *when a level-polymorphic inductive is used at several level
instantiations, is its carrier the same set at each, or must it be constructed
separately per instantiation?* Together with the owner's conjecture that
"inductives are by construction (or by Lean type system restrictions) either
Type or Prop, but never both."

## 1. The owner's claim, answered plainly

**As stated, the claim is false.** A single Lean inductive declaration can be
`Prop`-valued at one level instantiation and `Type`-valued at another, and the
corpus contains two such declarations.

Measured over every `inductive` block in `init-prelude.ndjson` (resultant sort
read off the export, walking each inductive's type to its trailing `Sort`):

* **`PUnit : Sort u`** — `Prop` at `u := 0`, `Type 0` at `u := 1`. From
  `vendor/arena-tests/good/tutorial/039_pUnitType.ndjson`: the inductive's type
  is `{"ie":0,"sort":1}` with `{"il":1,"param":2}`, i.e. literally `Sort u`;
  one constructor `unit : PUnit.{u}` with `numFields: 0`; recursor
  `PUnit.rec.{u_1, u} : {motive : PUnit.{u} → Sort u_1} → motive unit → ∀t, motive t`
  — **large-eliminating** (motive in a fresh `Sort u_1`), and `"k": false`.
* **`PEmpty : Sort u`** — same shape, zero constructors, also
  large-eliminating.

Every other inductive in `init-prelude` (129 checked) has a resultant sort that
is either **fixed `Prop`** at all instantiations (`Eq`, `HEq`, `And`, `Or`,
`True`, `False`, `Nonempty`, `Nat.le`, `Nat.le.below`, `ByteArray.IsValidUTF8`)
or **provably `≥ 1`** at all instantiations (a `succ` or a `max` with a `succ`
or `succ 0` inside). The near-counterexamples named in the brief are *not*
counterexamples:

* `PProd : Sort u → Sort v → Sort (max (max 1 u) v)` (038_pprodType.ndjson) —
  the `max 1` clamp means it is never `Prop`;
* `PULift : Sort (max s (max r 1))` — same clamp;
* `PSigma`, `PSum`, `Subtype`, `Inhabited`, `Hashable`, `Trans` — all carry the
  `max 1` (or an outer `succ`) in the export.

So the sort-ambiguous class exists, is legal, and in the shipped prelude is
**exactly the level-polymorphic subsingletons `PUnit` and `PEmpty`**. (Users
can declare more — nothing in the kernel forbids `inductive Foo : Sort u`
with several constructors — but Lean core deliberately clamps everything else
with `max 1`.)

**And `PUnit.{0}` is reachable in this project's schedule.** `PUnit` occurs in
`init-prelude` at level arguments `u`, `u_1`, `max 1 u`, `1`, `u+1`,
`max (u+1) u_1` (measured). The occurrences at bare `u`/`u_1` become `0`
whenever the enclosing declaration is instantiated at `0` — which
`instantiations.rs` guarantees happens, both through demand and through the
default instantiation for undemanded declarations, which is
`DEFAULT_LEVELS = &[0, 1]`. The `Prop` instantiation of `PUnit` is not a corner
case the schedule avoids.

*(This paragraph originally said "`DEFAULT_LEVEL = 0`". That was wrong on the
day it was written — the recorded choice at the time was the scalar
`DEFAULT_LEVEL = 1`, and MEASUREMENTS gives the reason: "since 27/27 on the
fragment is the acceptance criterion for this design, the default is 1". So the
conclusion above was **not** supported by the mechanism cited; it is supported
now, by the later change to a list containing 0. Worth knowing that the
conclusion outran its evidence once.)* (I did not run the pre-pass
to confirm the pair `(PUnit, [0])` lands in the fixpoint on `init-prelude`;
the inference is from the occurrence levels plus the seeding rules. Flagged
below as unmeasured.)

## 2. What Lean's rules *do* fix per declaration — the refined invariant

Although the *sort* of a sort-ambiguous inductive varies with the
instantiation, its **elimination discipline does not**. Lean decides large
elimination once, at the polymorphic declaration, and the decision is
conservative over all instantiations. Thesis §2.6.2 (thesis.txt:700–705):

> "There are two reasons an inductive type can be large eliminating:
> 1. The type family `t : ∀x :: α. U_ℓ` lives in a universe `1 ≤ ℓ`. (This
>    means that ℓ is not zero for **any** values of the parameters.) …
> 2. The type family has at most one constructor, and all the non-recursive
>    arguments to the constructor are either propositions or directly appear
>    in the output type."

and §2.6.3 (thesis.txt:762–763): the recursor's motive is
`κ = ∀a :: α. P a → U_u` with `u` a fresh universe variable **iff** the LE
judgment holds, otherwise `κ = ∀a :: α. P a → P`. The recursor is one
declaration with one type; there is no per-instantiation recursor.

Consequently every Lean inductive falls in exactly one of three
**per-declaration** classes:

| class | resultant sort | eliminator | prelude examples |
|---|---|---|---|
| (T) always-Type | provably `≥ 1` at all instantiations | large | `Nat`, `List`, `Bool`, `PProd`, `PULift`, … |
| (S) sort-ambiguous or Prop, subsingleton | may be `0` | large (reason 2) | `PUnit`, `PEmpty`; fixed-Prop: `Eq`, `HEq`, `True`, `False`, `Acc` |
| (P) may-be-Prop, not subsingleton | may be `0` | **small only — at every instantiation, including Type ones** | `And`, `Or`, `Nonempty`, `Nat.le` (all fixed-Prop in the prelude) |

The load-bearing consequence for class (P): a two-constructor `Sort u`
inductive instantiated at `u := 1` is a `Type` whose two elements **cannot be
distinguished by anything in the theory** — distinguishing them would need a
motive in `Sort 1`, which its recursor does not offer. That is exactly the
thesis's justification for truncating them (§5.2, thesis.txt:1816–1818: "since
we have a small eliminator, it's impossible to tell that members of the
inductive type are distinct, so we lose nothing in the propositional
truncation").

*Caveat, and what makes the case reachable rather than hypothetical.* The
class-(P)-at-Type-level case is settled here from the thesis's rules and from
Lean's own test as ported in `checker/src/inductive.rs::large_elim_test`, which
gates on `is_nonzero(ℓ) = leq(1, ℓ)` (`checker/src/level.rs:270`). That test is
**conservative**: a bare `Sort u` is neither provably zero nor provably nonzero,
so it does not return early, and the declaration falls through to the
subsingleton analysis — where two constructors, or one constructor with a data
field absent from the result spine, make it class (P). Its resultant sort at
`u := 1` is then the nonzero numeral `1`. §3.5 names the two shapes this
produces, says what the corpus actually contains, and records what the
implementation does about it. It has **not** been tested against a live Lean
kernel.

## 3. So must the carrier be per-instantiation? Five findings

### 3.1 Nothing ever *compares* carriers across instantiations

In this design every level is ground per check (`instantiations.rs`;
`tc.rs::check_declar_all`), and Lean's definitional equality never equates a
constant at levels `[0]` with the same constant at `[1]` — level equality is
equality of (normalised) level expressions, and distinct numerals are
distinct. `⟦c.{0}⟧` and `⟦c.{1}⟧` being different symbols with unrelated
denotations is therefore *sound by itself*; no obligation of the form
"`⟦PUnit.{0}⟧ = ⟦PUnit.{1}⟧`" can ever arise. The question is purely one of
**economy**: can one derived construction (one `∀α`-lemma package in
`derived/`) serve every instantiation, or does each instantiation need its own
construction?

### 3.2 For class (T) the carrier is genuinely uniform — and the code already realises this

The thesis's W-translation (§5.2, thesis.txt:1808–1810) produces, for an
always-Type inductive, a carrier that is a **set-level function of the
parameter sets only**. The level appears in none of it. The implementation
matches:

* `derived/src/wlist.rs`: `lt(α) := W(1+α, fam(α), U(1+α))`, where `U(·)` is
  the *least-universe term function* of `derived/src/universe.rs`
  (`U(x) := ∩{u | is_universe(u) ∧ x ∈ u}`). The bound is computed **from the
  parameter set itself**, not from Lean's `u` — that is why "the level appears
  nowhere" in `wlist.rs`, and it is correct, not an accident (see §5 below).
* `derived/src/wlist_fun.rs`: `L(S) := {⟨α, lt(α)⟩ : α ∈ S}` with
  `⊢ ∀S ∀α. (α ∈ S → app(L(S),α) = lt(α))`. The **only** thing the level
  touches is `S`.
* `checker/src/tg.rs::list_const`: `⟦List.{u}⟧ := L(⟦Sort (u+1)⟧)` as a
  per-`(name, levels)` abbreviation. So — one correction to the brief — the
  per-instantiation symbols do **not** have identical bodies: `⟦List.{0}⟧` is
  the graph over `U₁` and `⟦List.{1}⟧` the graph over `U₂`. They are different
  sets (different domains) that agree wherever both are defined:
  `app(⟦List.{0}⟧, ⟦Nat⟧) = lt(⟦Nat⟧) = app(⟦List.{1}⟧, ⟦Nat⟧)`.

So for class (T) the answer is: **uniform carrier, per-instantiation
wrapper**. The carrier-at-a-parameter `lt(α)` is one set function; per
instantiation there remain exactly (a) the domain `S` of the set-function
graph, and (b) the universe-membership theorem `lt(α) ∈ ⟦Sort ℓ⟧σ` — which is
where all the level content lives. The working hypothesis in the brief is
correct for this class.

### 3.3 For classes (S) and (P) a W-carrier and a Prop-carrier are different sets — but the thesis never uses both

Under §6.2 the two readings really are different sets: a `Prop` denotes a
subset of `{•}` (thesis.txt:2075, and Theorem 6.7, thesis.txt:2184: "If
`Γ ⊢ α : P`, then `⟦Γ ⊢ α⟧γ ⊆ {•}`"), while a W-type denotes a set of
`(a, f)` pairs (thesis.txt:2116, 2146–2152). If `⟦PUnit.{1}⟧` were built as a
W-type and `⟦PUnit.{0}⟧` as a subset of `{•}`, the carriers would genuinely
differ. **But the thesis's translation never takes the W branch for these
declarations at any instantiation.** Its case split (§5.2–5.3) is made at the
*declaration*, on the same trichotomy as Lean's eliminator decision:

* class (T), `1 ≤ ℓ` provable: W-translation (thesis.txt:1788–1810; note the
  spec rule's explicit side condition `1 ≤ ℓ` at 1788);
* class (P), not LE: truncation —
  `⟦µt : ∀x::α. U_ℓ. K⟧ = λx::α. ulift_ℓ ‖⟦µt : ∀x::α. U_{ℓ'}. K⟧ x‖`
  (thesis.txt:1813–1815; this rule is in **§5.2**, not §5.1 as the brief had
  it). Since `⟦ulift⟧ = id` (thesis.txt:2106) and `⟦‖β‖⟧ = [⟦β⟧ ≠ ∅]`
  (thesis.txt:2109), the carrier is a subset of `{•}` **at every
  instantiation, including Type ones** — sound precisely because of the
  small-eliminator observation in §2 above;
* class (S), LE but possibly-Prop: the acc-translation of §5.3
  (thesis.txt:1826–1828 "we must abandon W-types entirely … propositional
  truncation will destroy the large elimination property, so we have to use
  acc instead"; final rule 1885–1889:
  `⟦µt : ∀x::α. U_ℓ. (c : β)⟧ = λx::α. ulift_ℓ (acc^ϕ_r (x))`, and the zero
  case 1829–1830: `⟦µt : ∀x::α. U_ℓ. 0⟧ = λx::α. 0_ℓ`). Interpreted
  (thesis.txt:2126), `acc^ϕ_r x` is again a subset of `{•}`.

A subset of `{•}` is a perfectly good **Type** denotation: it is a set with at
most one element, `• = ∅` its only possible member, and it is a member of
every universe level (`[φ] ∈ U₀` is `Tower::cond_in_u0`; `[φ] ∈ Uₙ` follows
from `Rung::u0_mem` + `Rung::transitive` — all already in
`derived/src/tower/rungs.rs`). Concretely, running §5.3 on the two corpus
counterexamples:

* `⟦PUnit.{u}⟧ = {•}` at **every** `u` — read as the truth value "true" at
  `u = 0` and as the one-point type at `u ≥ 1`, with `⟦unit⟧ = •` and
  `⟦PUnit.rec⟧ C e := e`;
* `⟦PEmpty.{u}⟧ = ∅` at every `u` — "false" at `u = 0`, the empty type at
  `u ≥ 1`.

**Conclusion.** The uniform-carrier hypothesis survives, but in a sharpened
form:

> The carrier can be one construction per **declaration**, valid at all
> instantiations, *provided the construction is chosen by the declaration-level
> trichotomy (Lean's own eliminator trichotomy), never by the instantiated
> sort.* For class (T) that construction is the W-carrier; for classes (S) and
> (P) it is a subsingleton carrier `⊆ {•}` (acc-based resp. truncation-based),
> **including at instantiations where the inductive is a Type**. What is
> per-instantiation is only: the sort-encoding wrapper (the set-function
> domain `S`), the universe-membership theorem, and the Prop/Type *reading* of
> terms (§6.2's `sort`-indexed clauses — which the backend already implements
> as `Clause::Prop/Type/Undet`).

The safety argument is exactly the pair of facts from §2: an (S)-class
inductive can never have two distinguishable elements (subsingleton test), and
a (P)-class inductive can never have its elements distinguished (no large
eliminator at any instantiation). Lean's per-declaration eliminator decision
is what makes the per-declaration carrier legitimate. The owner's conjecture,
restated as "*the translation branch* is fixed per declaration", is true —
it is just fixed by the eliminator trichotomy, not by the sort.

### 3.4 The alternative — branch per instantiation — is also sound, and is not obviously worse

Because of 3.1, nothing forbids interpreting `PUnit.{1}` as a one-point
W-type/enum and `PUnit.{0}` as `[⊤]`. Every obligation is per-instantiation
and each reading discharges its own. The trade-off is engineering, not
soundness:

* **per-declaration uniform (thesis route):** one derived package per
  declaration; `Unit`-heavy code (`Unit := PUnit.{1}`, ubiquitous) is served
  by the subsingleton machinery (`derived/src/prop.rs`), which is *much*
  cheaper than the W machinery — `cond_in_u0` + `u0_mem` + `transitive` give
  the universe membership at every level for free, where the W route needs
  the whole `cumul` chain. Structure-eta for `PUnit` (`t ≡ unit`, which
  `tc.rs::reduce_rec` already performs) becomes `cond_subsingleton`, a
  one-liner. This route requires accepting that `⟦Unit⟧` is `{•}` rather than
  a W-type — harmless, since class-(S) types have no distinguishable
  structure to lose.
* **per-instantiation branch:** reuse `enum`/W machinery at Type
  instantiations, `[φ]` at Prop ones. Costs two constructions per ambiguous
  declaration, a branch keyed on the *instantiated* resultant sort, and
  duplicated recursor wiring. Buys nothing visible: no theorem anywhere needs
  `⟦PUnit.{1}⟧` to be W-shaped.

**Recommendation: the per-declaration route.** Decide the branch by evaluating
whether the declaration's resultant level is nonzero for all parameter values
(the export's level expression makes this a syntactic check: is it a `succ`,
or a `max` with a nonzero branch), plus the subsingleton test — i.e. recompute
Lean's own trichotomy. Note this is *weaker* than the check the code performs
today: `tg.rs::enum_arity`/`nat_shape`/`list_shape` test `Level::Zero` on the
declaration's own (symbolic) level, which correctly excludes fixed-`Prop`
declarations but would **not** exclude a hypothetical `Sort ℓ → Sort ℓ`
list-shaped inductive (`ℓ` a bare parameter is not `Level::Zero`), whose
`ℓ := 0` instantiation would then be given a W-carrier. No such declaration
exists in the corpus, and because every ctor rule is *derived* rather than
asserted the failure mode would be unprovable obligations (gaps), not
unsoundness — but the shape checks should say `is provably ≥ 1`, not
`is not syntactically 0`, once level-polymorphic inductives are in scope.

### 3.5 Class (P) at a `Type` instantiation: reachable, sound, witnessed — and still declined, now for want of the theorem

§3.3 concludes that the truncation carrier is a subset of `{•}` "at every
instantiation, including Type ones". That conclusion is right, and this
subsection records the three things needed to act on it: that the case is
reachable, that the implementation currently declines it, and what the
replacement is when a witness appears.

**Reachable, and here are the two shapes.** Tracing
`large_elim_test_aux` (`checker/src/inductive.rs:865`) by hand:

* `MyBool.{u} : Sort u` with `tt`, `ff` — two constructors, so the
  `_ => false` arm fires and the declaration is class (P). This shape is *in
  the repository*, as `bad/large-elim-param.ndjson`, and the fixture's name
  says what it is for. At `u := 1` its resultant sort is `Sort 1`.
* `Squash.{u} (α : Sort u) : Sort u | mk : α → Squash α` — one constructor,
  but its field `a : α` infers as `Sort u`, which `is_zero` rejects, so `a`
  joins `non_prop_ctor_telescope_elems`; the result spine is `Squash α`, whose
  arguments are the *parameter* `α` and not the field, so the subset test
  fails and the declaration is class (P). Natural, unlike the first.

**What the corpus contains — decoded, over every `inductive` record in every
export.** Every class-(P) declaration in `good/` has resultant sort literally
`Sort 0`; there is **no** sort-ambiguous class-(P) declaration among them. The
only witnesses anywhere are in `bad/`, which is rejected at acceptance before
any interpretation clause runs. So the branch is unreachable on any file the
checker accepts.

The same sweep turned up a related conflation worth naming, since it decides
class membership: a declaration with **no recursor in the export at all** must
not be read as "not large eliminating". `bad/large-elim-param.ndjson` omits its
recursors deliberately, and a `|rec.lparams|` comparison classifies all three of
its declarations as class (P) on that basis. This is why
`zoneb::large_eliminating` computes the judgement from the declaration and keeps
the exported recursor only as an oracle (`zoneb::elim_audit`): whether a
recursor was exported is not a property of the type.

**The implementation declines, and the reason is not a model question.**
`build_trunc` refuses when the declaration's resultant sort is a nonzero numeral
at that σ. The model question is settled — §3.3 and thesis.txt:1813–1815, whose
`ulift_ℓ` is in the rule precisely because `ℓ` ranges over nonzero levels, and
whose soundness is §2's small-eliminator observation, which is stated for
`U_ℓ` and not for `Prop`. Concretely at `MyBool.{1}`: the model gives
`⟦tt⟧ = ⟦ff⟧ = •`, so it validates `tt = ff`, which Lean does not prove. That is
soundness-preserving and not completeness-breaking in any sense claimed —
refuting `tt = ff` needs a `Sort 1`-valued motive, which a class-(P) recursor
does not offer, so no Lean-accepted judgement can observe the collapse. The
decline is therefore **not** hedging against unsoundness; it is declining to
ship a branch that no accepted file can exercise and no fixture can test.

Note this is not the error §3.3's conclusion forbids. That rule is about letting
the *instantiated* sort choose a **construction**; here the construction is still
chosen per declaration by the eliminator trichotomy, and the instantiated sort
only gates a refusal. A refusal cannot produce a wrong carrier.

**The replacement, when a witness appears.** One theorem and one deleted line.
`TruncCarrier::in_u0` gives `⊢ ∀p⃗∀x⃗. ‖a‖ ∈ U₀` unconditionally; `Rung::u0_mem`
gives `⊢ U₀ ∈ Uₙ` at the rung; `Rung::transitive` (C₁) composes them:

```text
⊢ ∀p⃗ ∀x⃗. ‖a‖ ∈ Uₙ            for any rung n ≥ 1      [TruncCarrier::in_un]
```

This is the exact analogue of `IndexedUniverse::over_at`, and like it the C₁
step is rung-independent, so the generalisation is a signature change rather
than a second derivation.

**The witness this section asked for now exists; the theorem still does not.**
It asked for "a `good/` fixture with a `Squash.{u}`-shaped declaration used at
`u := 1`, which would give the branch the test it currently cannot have". That
is `mini/tests/fixtures/squash_at_nonzero_sigma.{lean,ndjson}` —
`inductive Squash (α : Sort u) : Sort u | mk : α → Squash α`, with `squashProp`
demanding `u := 0` and `squashType` demanding `u := 1` — and its header names
this section as what it was built for. The branch is **still declined**
(`mini/src/zoneb.rs`, `Gap::IndSpec(…, "class (P) above Prop")`), and the
decline is now *pinned as expected behaviour* by
`mini/tests/designed.rs::squash_is_class_p_at_a_nonzero_sigma_and_is_declined_there_today`.
So the accurate statement is: reachable, sound, **witnessed**, and declined for
want of `TruncCarrier::in_un` — which does not exist in
`derived/src/inductive/family/trunc.rs` — plus the one deleted line. Item 3 of
§7 is closed by the same fixture.

## 4. Ranked consequences for the design

1. **No work (correctness of the current List/Nat/Bool path).** Class (T)
   carriers are uniform; per-instantiation symbols with per-level domains and
   per-level membership theorems are the right shape. Nothing to undo.
2. **Small work (when `PUnit`/`PEmpty` are interpreted):** implement class (S)
   non-recursive subsingletons as `[φ]`-carriers uniformly at all levels —
   `PUnit ↦ 1`, `PEmpty ↦ 0`, constructors ↦ `•`, `rec ↦ K-combinator graph`.
   All the set-level machinery exists in `derived/src/prop.rs` and
   `derived/src/tower.rs`. The only new policy is the trichotomy check of
   §3.4. `PULift`/`PProd` (the 166 init-prelude misses) are class (T) — they
   need the ordinary W/enum route or opaque treatment, not this one.
3. **Medium work, already on the books (task #18 / recursors):** see §6 — the
   extra recursor level `u_1` multiplies *instantiations of theorems about one
   carrier*, not carriers; `u_1 := 0` needs the `ulift`-wrapper reading of the
   thesis (thesis.txt:1705–1709), not a new construction.
4. **Deferred but real (class (S) recursive, class (P) general):** `Acc` and
   any large-eliminating recursive Prop need §5.3's `acc^ϕ_r` translation —
   already recorded as out of scope in `INDUCTIVES.md` ("subsingleton
   elimination — §5.3, which abandons W-types for acc; a separate
   construction"). This analysis adds one datum: that machinery is *also* what
   serves the sort-ambiguous class at its Type instantiations, so it is on the
   critical path for full `PUnit`-style generality, though not for the
   prelude's fixed-`Prop` uses.
5. **Bug-shaped finding, independent of the theory question — FIXED
   2026-08-01.** `tg.rs`'s `ctor_rules` is now
   `HashMap<(NamePtr, Vec<Term>), CtorRule>`, populated and read at
   `(name, levels)`, so the mismatch described below no longer exists. The
   analysis is kept because it is what motivated the fix. As written:
   `tg.rs::ctor_rules` was keyed by **name only** and populated on
   first use (`!contains_key(&nil_name)` at 6078), but the stored rule's
   statement mentions that first instantiation's `S = ⟦Sort ℓ⟧` and that
   instantiation's `⟦List⟧`/`⟦nil⟧`/`⟦cons⟧` symbols. Every other
   inductive-related table (`ind_syms`, `rec_nests`) is keyed
   `(name, levels)`. If `List` is ever demanded at two levels in one run, the
   second level's constructor-typing lookups will retrieve the first level's
   rule; the premise/conclusion matching in `has_type_ctor_app` (7273–7298)
   will then fail against the second level's symbols, so the expected outcome
   is spurious gaps, not unsoundness — but the key should be
   `(name, levels)`. (Not traced to an end-to-end repro; today's corpus
   appears to demand `List` only at `[0]` via the literal-expansion seeds.)

## 5. Is `U(1+α)` the right bound at every level?

**Yes, and the reason is that it is not a level bound at all.** `U(·)` is the
least-Grothendieck-universe *term function* (`derived/src/universe.rs`), and
Tarski's Axiom A supplies a universe over any set whatsoever, so `U(1+α)` is
defined and correct for `α` of arbitrary rank — a "large α" enlarges the bound
automatically. The two facts that make the carrier honest are both proven
unconditionally in `∀α` form:

* `closed(1+α, fam(α), U(1+α))` — `WList::closed`. Given closure, the least
  closed subset of `U(1+α)` *is* the inductively generated set of lists (the
  generated set stays inside any closed superset by induction, and is itself
  closed and least), so no truncation can occur however big `α` is.
* the constructor memberships `nil ∈ lt(α)`, `cons h t ∈ lt(α)` with only the
  hypotheses Lean's constructor types state.

Lean's `u` enters nowhere in this; it enters only in `lt(α) ∈ ⟦Type u⟧`, which
is a *different* statement per ground `u` and is exactly what the `cumul`
chain is for.

**Does the `cumul` chain instantiate at `d := ⟦Sort u⟧`?** Yes, cleanly —
`WMem::w_in_universe` is a first-order `∀A ∀B ∀c ∀d` over set variables
(`derived/src/cumul/wmem.rs`), so it instantiates at any closed term; the
closed-term witness `NatUniverse::nat_in_u1` (`d := ω`) is one instance, not a
specialisation baked into the lemma. Two qualifications:

* the conclusion has the shape `W ∈ U(d)`, so the target universe must be
  presented as `U(t)` — which every `⟦Sort n⟧` with `n ≥ 1` literally is
  (`interp_sort`: `⟦Sort 1⟧ = U(ω)`, `⟦Sort (n+1)⟧ = U(⟦Sort n⟧)`). "A
  *variable* universe `d := U_{u+1}`" never actually arises in this design:
  levels are ground per instantiation, so each use is a closed instance.
  The per-level residue is the side conditions `S_seed ∈ U(t)` and
  `ω ∈ U(t)`, and the tower already exports the ladder for these at every
  ground level (`Level::omega_mem` is `⊢ ω ∈ Uₙ` for each `n ≥ 1`, plus
  `transitive`, `bin_union`, `pairing` for the seed memberships). What is
  missing is only the wiring per ground level, not new mathematics.
* the chain's real restriction is orthogonal to levels: `Fin(A,B)` demands
  **finite fibres** (`B(a) ∈ ω`). `Nat` and `List` qualify; an inductive with
  infinitary recursive arguments (`Acc`'s `∀y, r y x → t y`, or any
  function-typed recursive field) does not, and will need a
  cardinality-general replacement for the `V₀, V₁, …`-over-ω tower (the thesis
  uses `cf(λ) > sup|B(x)|`, thesis.txt:2146–2149). That is a future wall, but
  a large *level* does not hit it — a large *fibre* does.

## 6. The recursor's extra level (task #18)

A recursor has one more level parameter than its inductive (`List.rec.{u_1, u}`),
so the schedule multiplies pairs — but every `(u_1, u)` pair is a family of
**theorems about the same carrier** `lt(α)`; `u_1` never touches the carrier.
The thesis is explicit about how the `u_1 = 0` instance relates to the others
(thesis.txt:1705–1709):

> "we have simplified all the large eliminating recursors to require `1 ≤ ℓ`.
> The general recursor can be constructed from this by using
> `C′ := λx. ulift^{max(1,ℓ)}_ℓ (C x)`."

and `⟦ulift⟧ = id` (thesis.txt:2106), so at `u_1 = 0` the recursor is the
*same* set-level transfinite-recursion operator (§6.2.1's `rec_W`, which
mentions no universe at all) read through the Prop clauses: the motive's
values are subsets of `{•}`, the recursor's Lean-level output is a proof, and
the obligation degenerates to "`• ∈ ⟦C t⟧` for all `t` in the carrier" — an
induction over the carrier that `wtype::w_induction` already supports. So:

* one correction to the brief's framing: `u_1 := 0` selects **small
  elimination** (Prop motive), which every inductive has; it does not by
  itself select §5.3. **Subsingleton elimination** (§5.3) is the property of
  *Prop-valued inductives that eliminate large* (`Eq`, `Acc`, class (S)) — the
  opposite corner (`u_1 ≥ 1` from a Prop major premise). The two must not be
  conflated in the recursor wiring: `List.rec.{0,u}` needs only the
  `ulift`-wrapper reading; `Eq.rec.{u_1,u}` and `PUnit.rec.{1,0}` need the
  §5.3/K-like story.
* and the answer to "does this change §3?": no. The `u_1` axis adds
  per-instantiation *theorems* (typing of the motive, `•`-valuedness at
  `u_1 = 0`), never a second carrier. For class (S) at `u_1 ≥ 1, u = 0` —
  large elimination out of a Prop — the uniform `⊆ {•}` carrier is exactly
  what makes the recursor definable (`rec C e h := e` is total because every
  `h` *is* `•` by `cond_subsingleton`, which is also what discharges Lean's
  K-like/structure-eta reductions there).

## 7. What I could not settle

1. **Whether `(PUnit, [0])` actually appears in the computed schedule on
   `init-prelude`** — inferred from the six occurrence-level shapes plus the
   seeding rules, not measured by running the pre-pass.
2. **The exact per-instantiation behaviour of `has_type_ctor_app` at a second
   `List` level** — the name-only `ctor_rules` key was a real mismatch, and the
   premise check `subj != ts[i]` makes a spurious *proof* look impossible, but
   I did not build a two-level corpus file to observe the failure and rule out
   a subtler interaction. Moot for the key itself, which is now
   `(name, levels)` (§4.5); the unobserved-interaction caveat stands.
3. **A live-kernel check that a sort-ambiguous non-subsingleton inductive gets
   a Prop-only recursor at every instantiation** — asserted here from thesis
   §2.6.2–2.6.3, from the fixed recursor type in the export format, and from
   tracing Lean's own test as ported (`large_elim_test`, §3.5). What §3.5 adds
   is that the shape is *constructible* and one instance sits in `bad/`; what it
   does not add is an exported recursor for such a declaration — that fixture
   omits them — so the assertion is still unchecked against a real Lean run.
   This is the item a `good/` `Squash.{u}` fixture would close. *(**It is
   closed**: `mini/tests/fixtures/squash_at_nonzero_sigma` carries `Squash.rec`,
   and `mini/tests/designed.rs` asserts Lean's own verdict on the declaration
   agrees with `zoneb::large_eliminating`'s. What it did **not** open is the
   class-(P)-at-`Type` branch — that now waits on `TruncCarrier::in_un`, not on
   a test. See §3.5.)*
4. **Whether any downstream corpus (mathlib-scale) states cross-level facts
   whose proofs are more than per-instantiation typing** — e.g. lemmas about
   `ULift`/`PULift` round-trips. I see no mechanism by which a cross-level
   *equation between carriers* could be demanded (levels never unify across
   distinct numerals), but I checked the prelude only.
5. **§5.4 is future work in the thesis itself** (thesis.txt:1895–1901): the
   intro/recursor translations for the general reduction are "left as future
   work". The §3.3 claim that the subsingleton carrier supports the
   constructors and recursor uniformly is therefore an argument in the
   thesis's *style*, verified here concretely for `PUnit`/`PEmpty` only —
   not a theorem one can cite for the general class-(S) case.
