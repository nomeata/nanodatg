# Interpreting inductive types in TG

Design note for milestone 5–7. Written before implementation; revise it when
measurement contradicts it, and say so in the log at the bottom.

> **Status, 2026-08-06 — historical, and heavily cited.** The route described
> here (the hand-written `Bool`/`N`/`List` stacks, `derived/src/{enums,wnat,
> wlist,wlist_fun,wnat_rec,wlist_rec,wbool_rec,twopoint}.rs`) was superseded
> twice: first by the general translation (`derived/src/inductive/`), then by
> `mini/`, which uses **none** of the hand-written stack and cites this file
> **zero** times. The recognisers were never deleted — `checker/src/tg.rs` still
> has `enum_arity`, `nat_shape`, `list_shape` and `RecBottom::{Enum,Nat,List}`,
> dispatched ahead of `RecBottom::General`, so they are compiled and tested, not
> dead. `WIRING-DESIGN.md` §8's "step two — cut over `Bool`/`N`/`List`/enums,
> delete the recognisers" never happened, because the consumer moved instead.
>
> The file is kept because **50 code sites in `checker/` and `derived/` cite
> it**, several by line number: §"Glue types" (the `Σ` definition, quoted
> verbatim in `derived/src/sigma/dsum.rs`), §"The recursor" with its
> `step_typed` correction (cited from all of `wrec*` and `rec_acc*`),
> §"Why `List α` is the W-type outright" (**line-number-cited three times**;
> keep it at its line), §"Wiring: how ι reaches the kernel" and its route-2
> correction, §"Scope", §"Non-negotiables", and §"Does `N` need the ω-tower?".
> The **Scope**, **State** and corpus tables below are the parts that have gone
> stale, and each now says so where it stands.

## Two standing rules

Given by the project owner on 2026-07-31, and they override any "cheapest
route" reasoning elsewhere in this note:

1. **Simpler-first is fine when it generalises incrementally.** What is not
   acceptable is a shortcut that reaches a milestone — a tutorial test — using
   an approach or construction that is mostly unsuitable for further extension.
2. **When it is unclear how to prove or construct something, consult the
   thesis** rather than inventing.

The test to apply before building `X` for milestone `M` is: **when the next case
arrives, do I extend `X` or replace it?**

Worked examples from this file's own history. `enums.rs` → `wnat.rs` →
`wlist.rs` each strictly generalised the last — that is the good pattern, and
it is why `List`'s memberships fell out of `N`'s with only a parameter added.
The two-point-graph step behind `Bool.rec` is the bad one: it took `073` to zero
gaps but cannot survive `N`, whose fibres are non-empty, so it must be replaced
rather than extended. Note the distinction that matters — the *plumbing* around
it (`RecNest`, `Certifier::iota`, `derive_iota`) does generalise, and it is what
flushed out the `def_eq` certificate bug. The lesson is about the construction,
not the milestone.

The second has earned its place: the thesis has settled in minutes questions
that cost sessions when reasoned about from scratch — that Tarski universes need
not be transitive, that choice is ambient rather than derived, that `Σ` comes
with real `π₁`/`π₂` projections. Every entry in the log below marked "corrected"
is a case where reasoning ran ahead of reading.

Extract the text with `pdftotext` and grep it; the PDF converts poorly through
fetch. Landmarks: §5.1 "The menagerie", §5.2 "Translating type families",
§6.2 "Modeling Lean in ZFC", §6.2.1 "W-types in ZFC", §6.3 "Soundness".

## Source

Mario Carneiro, *The Type Theory of Lean* (MSc thesis, CMU 2019),
§5 "Reduction of inductive types to W-types" and §6.2.1 "Definition of
W-types in ZFC". We follow it rather than inventing, for the same reason we
followed his type-directed interpretation in the first place: the soundness
argument is his, and departing from it means redoing it.

Two things come from the thesis and are worth stating up front.

**The reduction target is the W-type.** §5.1 fixes a finite "menagerie" —
`⊥`, `Σ`, `+`, `ulift`, `‖·‖`, `W`, `=`, `acc` — and shows every Lean inductive
reduces to it. We do not need to interpret Lean's general inductive
specification directly; we need the menagerie, plus a translation.

**The set-theoretic definition is small.** §6.2.1, in full:

> If `A` is a set and `B(x)` is a family of sets indexed by `x ∈ A`, then
> `W_{x∈A} B(x)` is a set, defined as the intersection of all sets `W` such that
> `(a, f) ∈ W` whenever `a ∈ A` and `f : B(a) → W`.

That is a least-closed-set definition. It is conservative, it needs no new
axiom, and — this is the part that makes it attractive here — the induction
principle falls out of the definition rather than having to be proved.

## The construction

Throughout, `⟨a,b⟩` is the Kuratowski pair, `fs(X,Y)` the function space,
`U(x)` the least universe containing `x`, all already in `derived/`.

### Glue types

```
0        := ∅
1        := {∅}
A + B    := ({0} × A) ∪ ({1} × B)          inl a = ⟨0,a⟩, inr b = ⟨1,b⟩
Σ_{x∈A} B(x) := { p ∈ A × ⋃img(B) : snd p ∈ B(fst p) }        (Separation)
```

### The W-type

Say `S` is *closed* when `∀a ∈ A. ∀f ∈ fs(B(a), S). ⟨a,f⟩ ∈ S`. Let `u` be a
universe with `A ∈ u` and `B(a) ∈ u` for every `a ∈ A`. Then `u` is closed,
because universes are closed under pairing and function spaces. Define

```
W := ⋂ { S ∈ P(u) : closed(S) }
```

which is a legitimate Separation on `P(u)`, and non-vacuous because `u` is in
the family.

Four properties, in the order they should be derived:

- **W1 (closure).** `closed(W)`. If `f ∈ fs(B(a), W)` then `f ∈ fs(B(a), S)` for
  every closed `S ⊆ u`, so `⟨a,f⟩ ∈ S` for every such `S`, so `⟨a,f⟩ ∈ W`.
  This is `sup`'s typing rule.
- **W2 (induction).** If `C ⊆ W` and `closed(C)` then `W ⊆ C`. Immediate: `C` is
  a member of the family being intersected. Note that instantiating `C` at
  `{w ∈ W : P(w)}` yields the *strong* induction principle with the induction
  hypothesis available, because `f ∈ fs(B(a), C)` unfolds to
  `∀b ∈ B(a). f b ∈ W ∧ P(f b)`. We get structural induction for free.
- **W3 (inversion / no junk).** `∀w ∈ W. ∃a ∈ A. ∃f ∈ fs(B(a),W). w = ⟨a,f⟩`.
  By W2 at `C := {w ∈ W : …}`.
- **W4 (injectivity).** `⟨a,f⟩ = ⟨a',f'⟩ → a = a' ∧ f = f'`. Already available
  as `pairs::opair_inj`.

### The recursor

The thesis defines `F(a,f) = e(a)(f)(F ∘ f)` by transfinite recursion on rank.
**We should not follow that route** — it would require developing ordinals and
rank, which is a large detour. The standard ordinal-free construction is
available and lands in the same place:

Fix a target set `T`. An *attempt* is a function `g` with `dom g ⊆ W` such that
for every `w = ⟨a,f⟩ ∈ dom g`: `ran f ⊆ dom g`, and `g(w) = e(a)(f)(g ∘ f)`.
Attempts form a set, being carved by Separation out of `P(W × T)`. Put

```
F := ⋃ { g : g is an attempt }
```

- `F` is a function: any two attempts agree on the intersection of their
  domains, by W2 applied to "for all attempts `g,h`, `w ∈ dom g ∩ dom h →
  g w = h w`".
- `F` is itself an attempt: attempt domains are closed under subterms, and the
  union of such domains is too; the recursion equation transfers pointwise by
  agreement.
- `F` is total on `W`: by W2. Given `a ∈ A` and `f ∈ fs(B(a), W)` with every
  `f b ∈ dom F`, the set `F ∪ {⟨⟨a,f⟩, e(a)(f)(F∘f)⟩}` is an attempt, so
  `⟨a,f⟩ ∈ dom F`.

  **Correction (2026-07-31): this step is not provable as stated above.** An
  attempt is by definition a subset of `W × T`, so that extension is an attempt
  only if `e`'s value lands in `T` — and `e` is an arbitrary set, so nothing
  supplies that. Totality needs a carried typing hypothesis on the step:

  ```
  step_typed := ∀a ∈ A. ∀f ∈ fs(B(a),W). ∀r ∈ fs(B(a),T). app(e,⟨a,⟨f,r⟩⟩) ∈ T
  ```

  so the conclusion is `(closed ∧ step_typed) → wrec ∈ fs(W,T)`, not
  `closed → …`. This is not a defect in the construction: Lean's recursor is
  typed the same way, and the hypothesis is one a caller with a motive already
  has. It does mean `wrec ∈ fs(W,T)` is not free.

The **ι rule** is then the defining equation, `F(⟨a,f⟩) = e(a)(f)(F ∘ f)`, and
needs no separate argument. This is the definitional equality the checker must
discharge when a recursor meets a constructor.

`T` comes from the motive: for a recursor with motive `C`, take `T := ⋃img(C)`.
That is Replacement plus union, so it is a **universe-closure obligation**, see
below.

## What `List` needs

```
inductive List (α : Type u) | nil : List α | cons : α → List α → List α
```

is non-indexed, large-eliminating, non-mutual, non-nested. So it needs `W`, `0`,
`1`, `+` — and **not** `Σ`, `=`, `acc`, `ulift` or `‖·‖`:

```
A    := 1 + α
B    := λx. rec₊ (λ_. 0) (λ_. 1) x          nil has 0 recursive args, cons has 1
List α := W_{x∈A} B(x)
nil    := ⟨inl •, ∅⟩                        the empty function out of 0
cons h t := ⟨inr h, {⟨•, t⟩}⟩               the one-point function out of 1
```

Lean's `List.rec` takes one minor premise per constructor, whereas the W-recursor
takes a single packed `e`. The translation packs them with `rec₊`. For
non-indexed types with no `Prop` elimination this is mechanical — that is the
part of §5.2 we need and no more.

### Why `List α` is the W-type outright

The thesis's general translation (§5.2) is not `Jµt. KK = W` but

```
Jµt : ∀x :: α. U_ℓ. KK = λx :: α. { s : Wp : A. B p | recW (λ(p:A). G p) s x }
```

— a *subset* of the W-type carved out by a `good` predicate `G`, which exists to
undo the erasure of **indices**. The three components `A; B; G` are produced by a
`spec` judgment recursing on the constructor list.

The distinction that matters for us: `α` in that telescope is the list of
**indices**, not parameters. Parameters are fixed throughout the declaration and
so remain free variables of the whole construction. `List α` is parameterised but
**not indexed**, so the telescope is empty, `G`'s base case `(x) = (e)` degenerates
to `() = ()`, and the `good` predicate is vacuously true. The subset carving
collapses and `List α` *is* the W-type.

That is what makes this push tractable: it lets us build `W` and the translation
without first building the equality type. It is also exactly why indexed families
are out of scope below — for them `good` is not vacuous, and `=` becomes a
prerequisite.

## Where the bound comes from — corrected

`W` is well-defined only given a bound: a set containing `⟨a,f⟩` for every
`a ∈ A` and `f : B(a) → W`. The first draft of this note assumed that bound
would be a universe `U(x)`, once the Tarski inaccessibility clause was derived.
**That was wrong, and the error was in the diagnosis, not the difficulty.**

Two countermodels (recorded in full in `derived/src/universe.rs`) show the
required closure properties are not merely unproved but **refutable**:

- `M` := hereditarily finite sets over the atom `ω`. `M` satisfies all four
  clauses of `ax_tarski` — inaccessibility holds because `M` is countable, so a
  subset is finite and hence a member, or infinite and hence `≈ M`. But
  `{ω} ∈ M` while `ω ∉ M`. Since `U({ω}) ⊆ M`, the operator `U(c)` is **neither
  transitive nor `⋃`-closed**.
- A two-atom variant refutes `(a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ∈ U(c)` — the
  exact shape Lean's Π rule would want — and the same for `∪` and `×`.

I checked these against the axiom as actually stated in `kernel/src/thm.rs`
rather than against the intended reading, and they hold. The mechanism is worth
remembering: from `y ∈ u` and `z ∈ y` the subset clause gives `{z} ∈ u`, because
`z ∈ y` means `{z} ⊆ y` — but it never gives `z ∈ u`. Transitivity is simply not
among Tarski's four clauses, and cannot be derived from them.

So **Cantor–Schröder–Bernstein was the wrong target**. Deriving inaccessibility
would not have unlocked these properties, because they are false. The comments in
`funspace.rs`, `ext.rs` and `universe.rs` that named CSB as the obstruction have
been corrected. What *is* true, and is now derived unconditionally:

```
⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → {a,b} ∈ U(c))       least_universe_pairing
⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → ⟨a,b⟩ ∈ U(c))       least_universe_opair
```

— closure properties holding in *every* universe transfer through the
intersection, so `is_universe(U(x))` is never needed for them.

### The bound comes from ω-recursion instead

Nothing above blocks this push, because a universe was never the only possible
bound. Iterating

```
W₀ := ∅          W₍ₙ₊₁₎ := { ⟨a,f⟩ : a ∈ A, f ∈ fs(B(a), Wₙ) }          W := ⋃ₙ Wₙ
```

bounds `W` whenever every element of `W` has finite height — which holds exactly
when the branching `B(a)` is finite, since a finitely-branching well-founded tree
is finite. That covers `Bool`, `N` and `List`: everything in scope here. Each
`Wₙ₊₁` is a set by Separation from `A × 𝒫(B(a) × Wₙ)`, and the union over `ω` is
Replacement.

The prerequisite is therefore **the recursion theorem over ω**, not universe
closure. We already have `empty::least_inductive_set_exists`; the recursion
theorem is a standard conservative construction on top of it, and it is *also*
what the transitive-closure route needs, so it is the critical path either way.

For infinitely-branching `W` the ω-tower is genuinely insufficient and a real
bound is needed. That is out of scope, and should surface as a counted gap.
*(**Built, 2026-08-05**, and not by a taller tower: `derived/src/wpath/` bounds
`W(A,B,u)` by its set of labelled finite paths at an arbitrary fibre family —
no ordinals, no condition on the fibres. The `ω`-tower survives as the set the
paths live in and stops being the catcher. SCOPING.md §14.)*

### It reduces to one step, in one place

With `wtype.rs` complete, every rule the W-type exports — W1, W3, and the
structural induction principle — carries exactly one antecedent, `closed(A,B,u)`.
Nothing else is missing. And discharging it for a universe `u` is a single
inference:

```
f ∈ fs(B(a), u)  ∈ u   ⟹   f ∈ u
```

which is **transitivity**, and nothing else: `A ∈ u` gives `fs(B(a),u) ∈ u` by
product and power closure, and `⟨a,f⟩ ∈ u` then follows from
`least_universe_opair`, which is already derived unconditionally. The ω-tower and
the recursion theorem exist *solely* to route around that one step.

### Against the thesis

Carneiro's model takes `U₀ = {∅,{•}}` and `U_{n+1} = V_{κₙ}` — levels of the
cumulative hierarchy, **transitive by construction**, i.e. Grothendieck and not
Tarski universes. Its closure proofs are rank arguments that do not survive in a
non-transitive set: Π by "`B` is bounded in rank by some `µ < λ`" (Remark 1), and
W by "`cf(λ) > sup_{x∈A}|B(x)|`, since `rank ∘ f` is a sequence of ordinals of
length `B(a) < cf(λ)`" (§6.2.1).

Consistency strength is identical — Tarski's Axiom A is equivalent to arbitrarily
many inaccessibles, which is what the thesis assumes. The mismatch is *shape*,
not power, and we chose the shape that does not support the arguments the
interpretation is built on.

Note also that the kernel's own doc comment on `ax_tarski` reads "every set
belongs to a Grothendieck universe", which is **false** of the clauses beneath
it — a Tarski universe need not be transitive. That comment is what led to the
CSB detour.

### Resolved: the axiom was changed

2026-07-31. `ax_tarski` gained a fifth conjunct, transitivity, inserted second so
the body is `x ∈ u ∧ (C₁ ∧ (C₂ ∧ (C₃ ∧ C₄)))`. Additive rather than a rewrite:
the other four clauses all stay, `C₄`'s cofinality being load-bearing in the
thesis's own closure proofs. Costs no consistency strength — `V_κ` for `κ`
inaccessible satisfies all five.

Consequences, all verified: fragment 27/27, arena 152/0/2, `ci/check.sh` green.
The kernel audit then found the change makes **`ax_empty` derivable** (`ax_tarski`
gives a non-empty `u`; Regularity gives an `∈`-minimal `y ∈ u`; `C₁` makes `y`
empty), and `ax_power`, `ax_union`, `ax_pairing` besides — 8 set axioms could
become 4. It also found `C₂` is redundant given `C₁ ∧ C₃`.

Two corrections the audit made to claims *inside* the trusted base, both now
fixed: `ax_empty`'s justification cited the very non-transitivity that `C₁`
removed, and `define`'s doc claimed Skolemising a proved `∀x∃y` would be
non-conservative, which is false — the real reasons to demand `∃!` are
eliminability and not using AC in the metatheory. That second one matters
because a choice function is never unique, so `Classical.choice` cannot go
through `define` at all.

### A decision for the human

The alternative is to **replace `ax_tarski` with the standard Grothendieck
universe axiom** (transitive; closed under pairing, power set, and unions of
set-indexed families), from which every closure property here falls straight out.
It is arguably *easier to audit* than the present four-clause axiom, since it
contains no equinumerosity formula — and that formula is where the one
inconsistency in this project's history came from.

I am not taking that decision autonomously: it changes the trusted base, and the
standing guideline is to prefer conservative construction over new features in
the target logic. The ω-recursion route above needs no kernel change and reaches
everything in scope, so it is what this push follows.

## What the corpus actually demands

Measured against the tutorial corpus rather than assumed. Two findings move the
plan.

**`Eq` and `And` are not avoidable.** `076_listRecReduction` is the only file in
all 91 tutorial files that mentions `List`, and it also declares `Eq` (indexed,
`is_k = true`) and `And` (`Prop`). This is not an accident of that one file: every
test where ι actually fires states its result as an equation, so `Eq` is reached
by `073`, `074`, `075` and `076` alike. A scope that excludes `Eq` cannot reach a
zero-gap recursor result at all.

The saving grace is that these do **not** need the W-type machinery. In the
thesis's interpretation a `Prop` is a subset of `{•}` and `Eq a b` is the
conditional singleton `[ā = b̄]` (§6.3), with `refl` interpreting to `•`. That is
one Separation on `1`:

```
[φ] := { x ∈ 1 : φ }
```

So `Eq` and `And` come from a small construction that is independent of `W`, of
the universe closure, and of everything else here. What `076` needs from them is
*typing* — `Eq.refl a : Eq a a`, `And.intro` — not their recursors firing. The
full subsingleton-elimination story of §5.3 stays out of scope; this is only the
interpretation of the types themselves. **To verify against §5.3 before relying
on it.**

**ι is 5 gaps out of 87; the interpretation is worth more than the rule.** On
`076`, only 5 of 87 gaps are the ι rule. The other 82 are cascade: `has_type`
discharges *zero* of 100 typing obligations there, because almost every argument
is an application of an opaque constant (`List.cons`, `myListApped`). Same shape
on `075` — 6 ι gaps of 74, 0 of 54 obligations discharged. So giving
`List`/`nil`/`cons` a real interpretation with membership theorems attacks the
bulk of the gaps *independently of ι*, and should come first. Merely declaring an
inductive already costs nothing: `033`–`071` are all at zero gaps, because
checking a declaration rarely needs ι. Gaps appear exactly where a recursor meets
a constructor.

## Ladder

Each rung is a measurable corpus result, in dependency order:

1. **`[φ]`, `Eq`, `And`** — conditional singleton; no W, no universe closure.
2. **`W` + non-indexed large elimination** — `Bool` (`034`/`060`), then `N`
   (`041`/`067`), then `List`.
3. **ι wiring** — `073_boolRecEqns` (2 ι gaps), `075_nRecReduction` (6),
   `076_listRecReduction` (5).

`HAS_GAPS` in `checker/tests/tg_tutorial.rs` asserts `gaps > 0` for the files it
names, so a closed gap surfaces as an unexpected pass rather than passing
silently. Use it. (It was empty when this was written; it is
`["075_nRecReduction", "076_listRecReduction"]` today.)

## Wiring: how ι reaches the kernel

> **Superseded 2026-07-31 — route 1 was taken.** `Certifier` *does* have an
> `iota` method (`checker/src/certify.rs`), with a default implementation
> delegating to `admit` so that a backend with nothing to say about ι needs no
> change and keeps reporting a gap. The trait also carries the
> `has_type`/`declar_checked` typing family, which did not exist when the list
> below was written. The section is kept for the route-1-vs-2 argument, which is
> still the interesting content — but read it as history, and read
> `Certifier::iota`'s doc comment ("Why this is a trait method and not
> `admit(_, _, \"iota\")`") for the reasoning that actually won.

As written: the `Certifier` trait has no `iota` method — it carries `refl, symm,
trans, app_cong, lam_cong, pi_cong, beta, zeta, delta, eta, sort, const_eq,
admit`. The reduction itself is fully implemented (`tc.rs`'s `reduce_rec`, which
already handles K and structure-eta), but its certificate is
`admit(_, _, "iota")`, i.e. a counted gap.

Two ways to close it. **Prefer the second:** *(the recommendation did not
survive; route 1 is what shipped)*

1. add an `iota` method to the trait — touches the certifier interface and every
   backend;
2. interpret the recursor constant as a **definitional extension** whose defining
   equation *is* `F(⟨a,f⟩) = e(a)(f)(F ∘ f)`. Then ι is delta-shaped, discharged
   by machinery that already exists, and neither the trait nor the kernel
   changes.

Route 2 also matches how the recursor is constructed above: union-of-attempts
produces exactly a `define`-style unique-existence obligation, so the defining
equation is what we get out anyway. Route 1 would be adding a rule to paper over
a construction we already have.

### Correction (2026-07-31): route 2 does not reach `tc.rs` as written

Checked against the code rather than against the intention. **"Neither the trait
nor the checker changes" is false**, for two independent reasons, and the second
is not a plumbing detail.

*The delta path is unreachable for a recursor.* `Certifier::delta` is called
from exactly one place, `TypeChecker::delta`, which is gated on
`get_applied_def` — and that, like `unfold_def` beneath it, resolves a constant
through `Env::get_declar_val`, which returns `Some` only for `Declar::Definition`
and `Declar::Theorem`. A `Declar::Recursor` never gets there. ι is dispatched
instead in `whnf_no_unfolding_aux_with_cert`'s `Const` arm, and its certificate
is `self.admit(e, reduced, Admit::Iota)` — the *`admit`* method. So route 2 needs
either a change at `tc.rs:1031` or a backend that special-cases
`admit(reason = "iota")`, which is an abuse of a method whose contract is "I
cannot justify this".

*The reduct is not delta-shaped.* `TgBackend::delta` works by taking a defining
equation `⊢ ⟦c⟧ = ⟦value⟧` for the *head* constant and folding `app_cong` over
the argument spine. ι does not have that shape: `reduce_rec` substitutes the
matching `RecRule::val` and re-applies it to
`params ++ motives ++ minors ++ ctor_fields ++ trailing`, so the recursor
constant **disappears from the reduct entirely**. For `Bool`,

```
Bool.rec.{u} C f t Bool.true   ≡   (λ C f t. t) C f t
```

— the left side's head is `Bool.rec`, the right side's is an anonymous lambda,
and no congruence over a spine gets from one to the other. A defining equation
for `⟦Bool.rec⟧` would have to be an equation between *four-fold curried
set-applications*, `app(app(app(app(rec,C),f),t),true) = …`, whereas
`crate::wrec` supplies `app(wrec, ⟨a,f⟩) = app(e, ⟨a,⟨f, comp⟩⟩)` — one `app` at
a Kuratowski pair. Bridging the two is *currying*: `⟦T.rec⟧` has to be built as
a nest of `derived::funcs::lambda` graphs, one per recursor argument, and each
one costs a beta obligation with its own domain premise at the point of use.

So the honest statement of the remaining work is: route 2 is still the right
shape — the recursor should be a definitional extension and ι should be its
defining equation — but it needs (a) a change to the ι site in `tc.rs`, and
(b) a currying layer between Lean's argument order and `wrec`'s packed step.
Neither is a kernel change and neither needs a new axiom; both are real work
that the note previously counted as free.

## Scope

In, for this push:

- the menagerie fragment `0`, `1`, `+`, `Σ`, `W` with `sup`, induction,
  inversion, injectivity, the recursor and ι
- `[φ]` and the interpretation of `Eq` and `And` as subsingletons, enough for
  typing
- the translation for **non-indexed, non-mutual, non-nested, large-eliminating**
  inductives
- `List` end to end, with zero gaps and zero escapes

Out, and deliberately so — *at the time. Four of the five are now **in**, on
`mini`; only nested is not. Kept because four code sites cite this section for
the **rule** it states below (out-of-scope must be a counted gap), not for the
list.*

- **indexed families in general** — need the skeleton-plus-`good`-predicate
  translation of §5.2. `Eq` is handled above as a subsingleton, which is not the
  same thing and does not generalise. *(In: `derived/src/inductive/family/`,
  `mini/src/{ctor_ix,class_s_ix,class_p_ix,rec_ix_dep,rec_ix_prop,rec_s_ix,minor_ix,iota_ix_dep,rec_trunc_ix}.rs`.)*
- **subsingleton elimination** — §5.3, which abandons W-types for `acc`; a
  separate construction. `is_k` recursors (`Eq.rec`) included. *(In:
  `derived/src/inductive/family/le*.rs`, `mini/src/{class_s,rec_acc*}.rs`; `is_k`
  at `mini/src/convert.rs` and `mini/src/recursor.rs`.)*
- **mutual and nested** inductives *(mutual is in: `mini/src/mutual_aux.rs`,
  `mini/tests/mutual.rs`, ten fixtures, and `ci/check-mutual-blackbox.sh`.
  **Nested is the only survivor of this list**, and its reason is now a
  kernel-checked test rather than a scope line: `mini/tests/nested.rs`.)*
- **quotients**, propositional extensionality, choice *(quotients are in at both
  level clauses: `mini/src/{quot,quot_classes,quot_iota}.rs`, QUOT-MODEL.md.)*
- primitive `Nat`/`String` literals, already shelved *(still shelved.)*

Anything out of scope must surface as a *counted gap*, never as an
unjustified `Proved`. The cardinal rule is unchanged: never return `Proved`
for a theorem not matched against the claim.

## Non-negotiables

- No new kernel axioms. The whole construction above is conservative:
  Separation, Replacement, power set, union, pairing.
- The inductive-free fragment stays at 27/27 with zero gaps. It is the
  project's headline result and must not regress by a single gap.
- Arena stays 152 matched / 0 mismatched.
- Every derived lemma pinned to its exact conclusion by a test, and checked for
  non-vacuity — a lemma whose two sides are the same term proves nothing, which
  has already been a near-miss here more than once.

## State

*Historical: a snapshot of one day's tree. Five rows are wrong now — the
recursion theorem is done, `checker/src/tg.rs`'s general wiring is not "not
started" (`RecBottom::General` and `gen_rec_bottom` exist; WIRING-DESIGN §§13–14
are the record), RECURSOR-DESIGN's rung 5 landed, and the test counts are an
order of magnitude low (`derived/tests` has 873 `#[test]`s across 92 files). No
code cites this table. Read `MEASUREMENTS.md` and `MINI-HANDOFF.md` for state.*

Baseline at the start of this push: fragment 27/27 zero gaps, tutorial 527 gaps
over 91 files with 67 at zero, arena 152 matched / 0 mismatched / 2 declined,
`derived` at 239 tests.

| piece | file | status |
| --- | --- | --- |
| `0`, `1`, `+`, `rec₊` | `derived/src/sums.rs` | **done**, 19 tests |
| `[φ]`, `Eq`, `And` | `derived/src/prop.rs` | **done**, 21 tests |
| ω, `succ`, induction | `derived/src/recursion.rs` | **done**, 14 tests |
| recursion theorem | `derived/src/recursion.rs` | in progress — 6 steps named in that file's closing notes |
| `W`, W1–W4, structural induction | `derived/src/wtype.rs` | **done**, 16 tests — all carry `closed(A,B,u)` |
| Cantor, regularity of a universe | `derived/src/cantor.rs` | **done** — `member_not_equinumerous`, `image_in_universe` |
| discharging `closed(A,B,u)` | `derived/src/bound.rs` | **done**, 12 tests — `sup_mem_at`, `w_inversion_at`, `w_rect_at` are unconditional |
| W-recursor, attempts, agreement | `derived/src/wrec.rs` | **done** |
| ι fires (non-vacuity witness) | `derived/src/wrec_unit.rs` | **done** — unconditional at the unit W-type, with `⟨⟨c,∅⟩,V⟩ ∈ wrec` |
| step typing prerequisites | `derived/src/wrec_typing.rs` | **done** |
| one-point extension is an attempt | `derived/src/wrec_extend.rs` | **done** — the induction step |
| recursor totality, `wrec ∈ fs(W,T)`, ι unguarded | `derived/src/wrec_total.rs` | **done**, 10 tests — all three carry `closed ∧ step_typed`, and `wrec_unit` discharges both |
| recursor uniqueness (`define` rather than `define_abbrev`) | — | not started — optional, see the closing notes in `wrec.rs` |
| one construction per file | all of `derived/` | in progress |
| the bound, from ω-recursion | — | not needed for enumerations; see `enums.rs` |
| enumerations (`Bool`, `Empty`) as W-types | `derived/src/enums.rs` | **done**, 5 tests |
| the one-point function `{⟨a,b⟩}` | `derived/src/point_fun.rs` | **done**, 4 tests |
| `N` as a W-type, with `zero`/`succ` | `derived/src/wnat.rs` | **done**, 5 tests |
| `List` as a W-type, with `nil`/`cons` | `derived/src/wlist.rs` | **done**, 8 tests — every statement unconditional in `α` |
| `List`/`nil`/`cons` as **set functions** | `derived/src/wlist_fun.rs` | **done**, 3 tests — `cons` curried, three nested graphs |
| parameterised lambda graphs | `derived/src/funcs/beta.rs` | **done** — `lambda_n`/`beta_conditional_n` moved out of `tg.rs` |
| backend wiring, types and constructors | `checker/src/tg.rs` | **done for enumerations, `N` and `List`** |
| backend wiring, recursors and ι | `checker/src/tg.rs` | **done for `Bool.rec`, `N.rec` and `List.rec`** |
| `π₁`, `π₂` as term-formers | `derived/src/proj.rs` | **done**, 5 tests — §5.1's projections, `⋂p` by Separation |
| `N.rec`: the packed step and both ι rules | `derived/src/wnat_rec.rs` | **done**, 7 tests — ι with the recursive call live |
| `List.rec`: the packed step and both ι rules | `derived/src/wlist_rec.rs` | **done**, 7 tests — ι with a **field** and the recursive call live |
| `Sum_n` and `Inj_i` as **real symbols** | `derived/src/isum/symbols.rs` | **done**, 3 tests — cached per arity / per depth, with membership, injectivity, distinctness and **no junk** |
| the finite set `{a₀ … a_{m-1}}` | `derived/src/finset.rs` | **done**, 4 tests — memberships and the inclusion rule; `fibre.rs` now shares it |
| a constructor's recursive-argument function | `derived/src/recarg.rs` | **done**, 4 tests — a `Dispatch` out of `finord(m)`, at **any** `m` |
| **the translation, from declaration data** | `derived/src/inductive/` | **done**, 10 tests — carrier, constructors, typing, injectivity, distinctness at 8 shapes |
| wiring the general translation into the checker | `checker/src/tg.rs` | not started — separate task |
| the general recursor and ι | `derived/src/inductive/{recursor,step,iota,premise,typed,computes,…}.rs` | **in flight** — `RECURSOR-DESIGN.md` rungs 1–4 landed (`derived/tests/genrec.rs`); the checker wiring (rung 5) is not started |

Also landed alongside: `MAX_HYPS` removed (it *was* being hit — 528→527 tutorial
gaps, true max 22); `MAX_TYPE_DEPTH = 16` kept as a termination bound with
`deepest derivation: N of …` now reported every run; `Sets` hazard fixed.
(`MAX_TYPE_DEPTH` has since been removed too — `tg.rs` says "There used to be a
constant here" — replaced by per-edge visited sets. This row records the state as
of the day; the constant is gone.)

## Does `N` need the ω-tower? **No — measured, 2026-07-31**

The `Bool` wiring report puts `N` (`041`/`067`/`075`) as needing "a bound that is
no longer the tag set — i.e. the ω-tower". **That was wrong.** The prediction
below was checked by construction rather than by argument: `derived/src/wnat.rs`
derives `⊢ closed(1+1, B, U(1+1))` with **no hypothesis at all**, and
`tests/wnat.rs` pins it. The rest of this section stands as written.

`enum(A) := W(A, ∅, U(A))` works because the bound is seeded at the tag set
itself. For `N` the fibres stop being empty — `A = 1 + 1`, `B(inl •) = 0`,
`B(inr •) = 1` — but `bound::universe_closed` asks only for

```
A ∈ U(c)   and   ∀a ∈ A. B(a) ∈ U(c)
```

and at `c := A` all three hold already:

- `A ∈ U(A)` — `mem_least_universe`;
- `0 = ∅ ∈ U(A)` — the subset clause `C₂`, since `∅ ⊆ A ∈ U(A)`;
- `1 = {∅} ∈ U(A)` — `least_universe_pairing` at `a = b = ∅`.

So `closed(A, B, U(A))` should follow from machinery that is already built, and
the W-type is carved out of `U(A)` exactly as for `Bool`. The real work in `N` is
then the *case analysis* — computing `app(B,a)` for `a ∈ 1 + 1` through `rec₊`'s
computation rules — which is `sums.rs` work, not a bound construction.

More generally: **the transitivity clause removed the need for the ω-tower.** It
was only ever wanted because no universe could be shown to bound `W`; now
`bound::universe_closed` does that directly. The half-built recursion theorem in
`recursion/` retains independent value (ω, `succ`, induction, Peano) but is no
longer on the path to inductives. Do not restart it on the strength of a
remaining-cost estimate without checking the above first.

## Log

- 2026-07-31 — first draft, from thesis §5.1, §5.2, §6.2.1, §6.3.
  Departure from the thesis recorded: recursor by union-of-attempts rather than
  transfinite recursion on rank, to avoid developing ordinals.
- 2026-07-31 — **corrected the bound.** The first draft assumed a Tarski
  universe would bound `W` once inaccessibility was derived. Refuted: the
  closure properties are false, not merely unproved, and CSB was the wrong
  target. Replaced by the ω-tower; the prerequisite is now the recursion
  theorem. See "Where the bound comes from — corrected".
- 2026-07-31 — ω needed the same correction a third time. Tarski's universe is
  not closed under `n ↦ n ∪ {n}` either, so `least_inductive_set_exists` could
  not simply be re-run with `succ` for `𝒫`. ω is separated at
  `Trans(q) ∧ …` instead, since `succ(n) ⊆ 𝒫n` at transitive `n` and `C₂` then
  puts `succ(n)` back. Three independent constructions have now been blocked by
  the same missing transitivity; that is the strongest argument yet for the
  Grothendieck-axiom question above being worth answering deliberately rather
  than routing around a fourth time. (Note for future agents: `universe.rs` does
  have `least_universe_pairing` unconditionally — pairing closure *is* available
  and was re-litigated needlessly here.)
- 2026-07-31 — **corrected the scope.** `Eq` and `And` were listed as out of
  scope; measurement showed every ι-exercising test states its result as an
  equation, so they are unavoidable. They are cheap as subsingletons and are now
  in scope and done. Also measured: ι is only 5 of `076`'s 87 gaps, so the
  interpretation matters more than the rule.
- 2026-07-31 — **the W-recursor is finished except for uniqueness.** Totality
  (step 4), `wrec ∈ fs(W,T)` (step 5) and the unguarded ι rule (step 6) are
  derived, in `wrec_extend.rs` (the one-point extension is an attempt) and
  `wrec_total.rs` (the induction and its two consequences). The `step_typed`
  correction above stands and is now load-bearing in exactly one place — the
  inclusion `G ⊆ prod(W,T)` — and it is *discharged*, at the unit instance, so
  the three theorems are not about an unsatisfiable antecedent:
  `wrec_unit::unit_funspace` has no hypothesis left. The `sv(G)` design note
  needed one further correction: the previous pass said a two-way split on
  `x = ⟨a,f⟩` was unavoidable; it is not, because the lemma "every `G`-value at
  `⟨a,f⟩` is `V`" collapses the four cases to three with no split at all. What
  the previous pass got exactly right, and what the whole argument turns on, is
  that an *already present* value at `⟨a,f⟩` is forced by `rec_cond(wrec)` to
  equal the new one rather than merely to be compatible with it. Step 7,
  uniqueness, is left: `define_abbrev` is already conservative, so it buys the
  stronger `define` form and nothing downstream is blocked on it.
- 2026-07-31 — **`Bool` is interpreted, and the "interpretation beats ι"
  hypothesis held on it.** `derived/src/enums.rs` interprets an inductive whose
  constructors are all nullary as the W-type with empty fibres, seeded at its own
  tag set: `enum(A) := W(A, ∅, U(A))`, with `A ∈ U(A)` free from
  `mem_least_universe` and `∅ ∈ U(A)` from the subset clause, so the bound
  hypothesis is discharged **without** the ω-tower. `Bool` is `enum(1+1)`, its
  constructors `⟨inl •,∅⟩` and `⟨inr •,∅⟩`, both with real membership theorems
  and provably distinct. `tg.rs` recognises the shape from `InductiveData` and
  `ConstructorData` — no name matching — and `has_type` gained one clause,
  `HtClause::Ctor`, which reads the membership theorem off a table.

  Measured, per file, before → after: `034_boolType` 0 → 0 gaps and
  `060_boolRec` 0 → 0 (neither ever reduces, so neither ever asked); **`073_boolRecEqns`
  24 → 12 gaps, 12 → 0 escapes, and 0 → 12 of 18 typing obligations discharged**.
  All 12 closed gaps were `⟦Bool.true⟧ ∈ ⟦Bool⟧` and `⟦Bool.false⟧ ∈ ⟦Bool⟧`
  escaping to the boundary. `116_rtreeRecReduction` improved as a side effect,
  27 → 23, for the same reason. Tutorial total 527 → 511 over 91 files; fragment
  27/27 zero gaps, arena 152/0/2, `derived` 324 → 329 tests. **The ι rule is
  untouched**, and on `073` it is now 2 of 12 gaps rather than 2 of 24 — so on
  `Bool` the interpretation was worth six times the rule, matching what `076`
  predicted.

  Two things the implementation found that the note did not say. **Route 2 for ι
  does not reach `tc.rs`** — see the correction under "Wiring" above; that is the
  main negative result of this push. And **the interpretation has to stay
  injective on constants**: `035_twoBool` and `061_twoBoolRec` declare `Bool` and
  `TwoBool` side by side, and an inductive interpreted as its bare W-type would
  give two distinct Lean constants one denotation. (As it happens `TwoBool` has a
  two-field constructor and so does not qualify, but the hazard is real and the
  next enumeration pair would hit it.) Each interpreted name therefore gets its
  own `define_abbrev` symbol, exactly as a Lean definition does, and the
  membership theorems are transported across the two defining equations.

  What this does **not** do, and what the next rung costs. `⟦Bool⟧ ∈ ⟦Sort 1⟧` is
  not derived and cannot be with this `Sort` encoding: `⟦Sort 1⟧` is `U(⟦Sort 0⟧)`
  over an opaque `⟦Sort 0⟧`, and nothing relates `W(1+1,∅,U(1+1))` to it. No
  obligation in the corpus asks for it, but a `Π` over a universe will.

  **The encoding changed and this obstruction is gone.** `⟦Sort 0⟧` is not
  opaque in either crate — it is `U₀ = {0,1}` (`checker/src/tg.rs`,
  `mini/src/interp.rs`) — and the membership is derived generally by
  `derived::cumul`'s `DeclUniverse::over_at` at any rung, with
  `IndexedUniverse::over_at` for indexed families. **This is the origin of the
  "underivable with this `Sort` encoding" phrase that recurs throughout the log
  below; every one of those occurrences is refuted by this paragraph, and none
  of them is corrected where it stands, because they are dated entries.** What
  is still out of reach is `⟦Sort u⟧` at a universe *parameter*, which is a
  different statement — README's remaining-work item 3.
  For `N` (`041`/`067`/`075`) the fibre family stops being `∅` — `B(zero) = 0`,
  `B(succ) = 1` — so it needs `rec₊` from `sums.rs` (built, unused so far) and a
  bound that is no longer the tag set, i.e. the ω-tower or `U` closed under the
  relevant union. For `List` (`076`) the parameter α makes the type a *family*,
  so `⟦List⟧` becomes a symbol of arity 1 and every theorem above needs α as a
  parameter — mechanical, but every membership theorem gains a hypothesis
  `α ∈ ⟦Sort u⟧` that nothing currently discharges.

- 2026-07-31 — **`N` is interpreted, the `U(A)` bound held, and the
  "interpretation beats ι" hypothesis did *not* hold this time.**

  *The bound.* The prediction that `N` would need the ω-tower is refuted.
  `bound::least_universe_closed` at `c := A := 1+1` needs `A ∈ U(A)`
  (`mem_least_universe`), `0 = ∅ ∈ U(A)` (`enums::empty_in_least_universe`) and
  `1 = {∅} ∈ U(A)` — the last is `least_universe_pairing` at `a = b = ∅`, since
  `{∅,∅}` *is* the term `1`, so nothing has to be rewritten. `Bound` gained one
  field, `least_pairing`, purely so that derivation is not run twice. So the
  bound is `U(A)`, exactly as for the enumerations, and the ω-tower and the
  recursion theorem stay off the critical path for everything in scope.

  *What the real work was.* Not the bound but the **case analysis**, as
  predicted: `app(B, inl •) = 0` and `app(B, inr •) = 1` through `sums`' `rec₊`
  computation rules (`Cases::beta_left`/`beta_right`, until now unused), and
  then `sum_cases` + `unit_eta` to lift them to `∀a ∈ 1+1`. The two "constant
  functions" `λ_. 0` and `λ_. 1` on `1` are **one-point graphs**, because `1` is
  a singleton — so `point_fun.rs` had to be built first, and it pays three
  times: the two fibre functions and `succ`'s recursive argument `{⟨•,n⟩}`.

  *`succ` has to be a function, not a term-former.* Lean applies `N.succ`, so
  `⟦N.succ⟧` is the graph `{⟨n, ⟨inr •,{⟨•,n⟩}⟩⟩ : n ∈ N}` and its typing
  statement is `∈ fs(N,N)`, not `∈ N`. `ext::lam_in_funspace` supplies it from
  the membership theorem. This also needed one change in `tg.rs` beyond the
  `Bool` pattern: `typeable_shape` refused *every* opaque constant, so
  `N.succ n` never reached the application rule at all; it now admits a constant
  this backend interprets.

  *Measured, per file, before → after.* `041_natDef` 0 → 0 and `067_nRec` 0 → 0
  (neither ever reduces). **`075_nRecReduction` 74 → 72 gaps, 15 → 13 escapes,
  0 → 3 of 54 typing obligations discharged outright**, with `Ctor` firing 15
  times and `App: fs` 7 times inside conditional derivations. Tutorial total
  511 → 509 over 91 files; fragment 27/27 zero gaps, arena 152/0/2, `derived`
  329 → 338 tests. Nothing else in the corpus moved.

  **The negative result: on `N` the interpretation was worth *less* than the ι
  rule, not six times more.** Two gaps closed against six ι gaps still open.
  The reason is visible in the ledger and is not about `N`: of `075`'s 54
  undischarged obligations, 23 are locals (by design), 18 are lambdas whose
  typing rule did not apply, and 10 are applications of an opaque constant —
  and the opaque constant is `N.rec`, together with the motive lambdas around
  it. `073_boolRecEqns` was dominated by constructor memberships escaping;
  `075` is dominated by the recursor. So the `Bool` result generalises to
  "interpret whatever the file's arguments are made of", and here that is the
  recursor, which is the next rung and is untouched. The lambda misses want
  `⟦N⟧ ∈ ⟦Sort 1⟧`, which the `Bool` report already recorded as underivable
  with this `Sort` encoding.

  *What `List` will additionally need.* The parameter `α` makes `List` a
  *family*: `A := 1 + α`, so `⟦List⟧` is a symbol of arity 1 and every theorem
  in `wnat.rs` gains `α` as a parameter. Two things stop that being purely
  mechanical. The fibre family's right branch is `λ_ : α. 1`, a constant
  function on an **arbitrary** `α` rather than on `1`, so `point_fun` no longer
  covers it and a constant-function-in-a-function-space lemma is needed
  (`ext::lam_in_funspace` over a constant body symbol will do it). And the
  bound has to become `U(1 + α)` with `α` free, which needs `1 + α ∈ U(1+α)`
  (free) but also `α ∈ U(1+α)` if anything wants the elements — plus every
  membership theorem acquires a hypothesis `α ∈ ⟦Sort u⟧` that nothing
  currently discharges, exactly as the `Bool` report predicted. `cons` is
  two-field, so its tag component is `inr h` with `h ∈ α` rather than `inr •`,
  which is a strict generalisation of what `wnat.rs` does and costs no new
  machinery.

- 2026-07-31 — **`List` is interpreted, the memberships came out unconditional in
  `α`, and the corpus did not move by a single gap.**

  *The `α ∈ ⟦Sort u⟧` question, answered.* The `N` report predicted that
  parameterising the type would put a hypothesis `α ∈ ⟦Sort u⟧` on **every**
  membership theorem. That is **refuted**, and the brief's counter-conjecture is
  right. `derived/src/wlist.rs` derives, with `α` a free variable and no
  hypothesis anywhere:

  ```text
  ⊢ ∀α. app(fam(α), inl •) = 0
  ⊢ ∀α ∀h. (h ∈ α → app(fam(α), inr h) = 1)
  ⊢ ∀α. closed(1+α, fam(α), U(1+α))
  ⊢ ∀α. ⟨inl •,∅⟩ ∈ lt(α)
  ⊢ ∀α ∀h ∀t. ((h ∈ α ∧ t ∈ lt(α)) → ⟨inr h,{⟨•,t⟩}⟩ ∈ lt(α))
  ```

  `bound::least_universe_closed` asks only for `A ∈ U(c)` and
  `∀a ∈ A. app(B,a) ∈ U(c)`; at `c := A := 1 + α` those are `mem_least_universe`,
  `empty_in_least_universe` and `least_pairing`, none of which mentions `α`'s own
  type. The only hypothesis anywhere is `h ∈ α`, which is what Lean's
  `cons : α → List α → List α` states. `⟦List α⟧ ∈ ⟦Sort u⟧` is still not
  derivable, but that is the `Sort` obstruction already recorded for
  `⟦Bool⟧ ∈ ⟦Sort 1⟧` and is not about inductives.

  *Where `α ∈ ⟦Sort u⟧` does enter, and it is not where the report said.* One
  level up, in `wlist_fun.rs`. Lean **applies** `List`, `List.nil` and
  `List.cons`, and the backend reads `List α` as `app(⟦List⟧,⟦α⟧)`, so all three
  have to be sets. A set function has a **set domain**, and `app(f,x)` off it is
  `∅` — so `app(⟦List⟧,α) = lt(α)` cannot hold for an `α` outside `⟦Type u⟧`,
  whatever `lt` is. Every lambda in the interpretation pays this; nothing about
  inductives does.

  *`cons` is curried.* Three nested graphs, one per Lean argument, because the
  checker reads `f a b` as `app(app(⟦f⟧,⟦a⟧),⟦b⟧)` — one `app` per argument,
  chosen before the head is known — so a graph taking the pair `⟨h,t⟩` could
  never be applied. The inner two carry the outer arguments as parameters, which
  is why `lambda_n`/`beta_conditional_n` were moved out of `tg.rs` into
  `derived::funcs`.

  *Non-vacuity has real content here, and it holds.* `nil ≠ cons h t` for every
  `h`, `t` (the tags differ) and `cons h t = cons h′ t′ → (h = h′ ∧ t = t′)` —
  **both** components, unlike `N`'s `succ_inj`, so distinct heads give distinct
  one-element lists and `lt(α)` sees `α` rather than only its being non-empty.
  Cashed at three concrete lists: `nil`, `cons h nil`, `cons h (cons h nil)` are
  pairwise distinct outright and all three lie in `lt(α)` as soon as `α` has an
  element.

  *The wiring.* `tg.rs` recognises the shape from `InductiveData`/`ConstructorData`
  — one parameter, no indices, `Sort ℓ → Sort ℓ` for the same `ℓ`, two
  constructors of arity 0 and 2 with the de Bruijn indices of both field types
  checked — never by name. `List` is the first shape admitting a **universe
  parameter**, so `ind_abbrev` is now keyed on (name, levels) rather than on the
  name: `⟦List.{u}⟧` is a graph over `⟦Type u⟧` and genuinely varies with `u`.
  `has_type` gained one clause, `CtorApp`, which instantiates a constructor's
  conditional rule and discharges each premise by recursion — which is how
  `⟦α⟧ ∈ ⟦Type u⟧` is found among the binder's own assumptions rather than
  invented.

  *Measured, before → after.* `076_listRecReduction` **87 → 87 gaps**, 400 → 400
  derived, 21 → 21 escapes, 0 of 100 obligations discharged either way. Tutorial
  total 509 → 509 over 91 files, 67 at zero; fragment 27/27 zero gaps zero
  escapes; arena 152/0/2; `derived` 338 → 349 tests.

  **The negative, and why it is not about `List`.** The interpretation *is*
  working: `CtorApp` fires 21 times, and the 21 obligations about `List.nil α`
  and `List.cons α h t` that were pure assumptions before are now real
  derivations. They are **conditional**, and on `076` that is fatal to the gap
  count, because the file states its theorem under `∀ α (xs : List α)` — so every
  single term in it mentions a context local, and *no* typing obligation in the
  file can be discharged unconditionally. Instrumenting `beta_step` confirms it:
  of the file's 100 obligations, **zero** are settled with an empty hypothesis
  set, before or after. `073_boolRecEqns` improved 24 → 12 because `Bool.true` is
  a *closed* term; `List.nil α` never is.

  So the rule that generalises is not "interpret the file's arguments" but
  **"only a closed argument can close a gap"**, and it predicts the `Bool`, `N`
  and `List` results in that order. A conditional certificate whose hypotheses
  are exactly the typings of the free locals in scope is, morally, a complete
  proof of the def-eq *in that context*; the escape ledger counts it as a gap
  because the boundary demands unconditional theorems. Making the boundary
  context-aware — discharging `⟦w⟧ ∈ ⟦A⟧` for a local `w : A` the checker itself
  introduced — is the single change that would move `076`, `075` and
  `077_RBTree.id_spec` together, and it is a change to the *ledger's* contract,
  not to any interpretation.

  *The remaining ledger on `076`.* 87 = **21** escaped assumptions + **66** the ι
  rule and its cascade (5 ι, 24 trans-over-admitted, 16 pi-cong-over-admitted, 9
  congruence-over-admitted, 5+1 pi-cong shape mismatches, 4 symm-over-admitted, 2
  eq_cache). The undischarged obligations are 52 locals (by design), 24 lambdas —
  12 motives `λ_:List α. List α`, which want `⟦List α⟧ ∈ ⟦Sort u⟧`, and 12 minor
  premises — and 24 applications of an opaque constant, which by name are
  **10 `List.nil`, 11 `List.cons`, 3 `List.rec`**. The first 21 now settle
  conditionally; only `List.rec` is genuinely unreachable. So on `076` the
  recursor is what is left, exactly as on `075`.

  *What the recursor will cost.* Unchanged from the correction under "Wiring":
  route 2 needs a change at the ι site in `tc.rs` and a **currying layer**, and
  `List` makes the second one concrete. `Lean's List.rec` takes
  `α, C, minor_nil, minor_cons, t` — five curried arguments — whereas
  `crate::wrec` supplies `app(wrec, ⟨a,f⟩) = app(e, ⟨a,⟨f,comp⟩⟩)`, one `app` at
  a Kuratowski pair. `wlist_fun.rs` is a worked example of exactly that layer at
  depth three, and it says what depth five costs: one `lambda_n`/`beta_conditional_n`
  pair per level, one `define_abbrev` per level, and a beta obligation with its
  own domain premise at each level *at the point of use*. The three-level version
  is about 120 lines of derivation; five levels is not five times harder, but the
  premises multiply, and on `076` every one of them will be conditional on a
  context local.

  That last point is a **prediction, not a measurement**, and it is worth stating
  precisely because it changes the expected payoff. An ι certificate for `076`
  would be conditional, so it would turn the 5 ι *admits* and their 61 cascade
  steps into *escapes* rather than into `Proved`: admits poison every step above
  them one at a time, whereas a conditional certificate is one gap however far it
  travels. So the recursor should still cut `076` substantially — plausibly to
  something near the escape count — but it will not reach zero while the boundary
  demands unconditional theorems. If that is right, the ledger change above is
  both cheaper than the recursor and the thing that decides what the recursor is
  worth, and the two should be sequenced in that order.

- 2026-07-31 — **`has_type` now derives a local's typing itself, and the corpus
  did not move by a single gap or a single escape.** The prediction that this
  "would move `076`, `075` and `077_RBTree.id_spec` together" is **refuted**, and
  the reason is that the mechanism was already there under another name.

  *What was built.* `has_type` was split. `has_type_a` returns the derivation
  *together with* the assumption list it is stated under, and may **acquire** one
  kind of assumption on the way: `TgBackend::has_type_local` answers an obligation
  about a context local `w : A` with `⊢ (… ∧ ⟦w⟧ ∈ ⟦A⟧) → ⟦w⟧ ∈ ⟦A⟧`, the
  antecedent being the ambient assumption Carneiro's reading of `Γ ⊢ e : B`
  supplies and this kernel has no context to hold. Every clause threads the list;
  `has_type_a`'s guard checks the returned list still *begins with* the one it was
  asked for, so a clause cannot silently weaken its statement; `has_type_h` is the
  entry for callers that cannot carry a new antecedent and declines instead. The
  lambda rule's discharge is unchanged — it still peels off exactly its own
  binder's guard (`drop_guard` pins which one) and hands the rest back.

  *Measured, before → after.* `073_boolRecEqns` 12 → 12, `075_nRecReduction`
  72 → 72, `076_listRecReduction` 87 → 87, `077_RBTree.id_spec` 187 → 187.
  Tutorial total **509 → 509** over 91 files, 67 at zero, **115 → 115 escapes**;
  every per-file gap and escape count is byte-identical. Fragment 27/27, zero
  gaps, **zero escapes**. Arena 152/0/2, `ci/check.sh` green, `derived` 349.
  The only thing that moved is the ledger's own vocabulary: the derivations
  formerly attributed to "the binder's own assumption" are now attributed to the
  new `Local` clause (`076`: 57, `077`: 142, `075`: 27, `073`: 1).

  *Why it is a no-op, checked rather than argued.* `beta_step` already called
  `local_premises`, which collects `⟦w⟧ ∈ ⟦A⟧` for **every** local free in the
  argument and retries the whole obligation under them. Every local the recursion
  can ever reach is a subterm of that argument — the three non-structural edges
  (`has_type_const` into a constant's closed value, the target-unfolding tail,
  `has_type_pi` into the `Π`) introduce no new locals — so the pre-computed set is
  already a superset of what on-demand acquisition would ask for. Instrumenting
  the miss site before the change: of the 552 obligations in the tutorial corpus,
  `has_type` is asked about a local it has no assumption for 144 times, and in
  **142** of them the assumption set is empty because it is the unconditional
  probe that `local_premises` then retries. Exactly **2** are genuinely new, and
  neither closes a gap.

  *So what is left, with numbers.* 143 of the corpus's obligations end in the
  fallback that is genuinely undischargeable — the raw `⟦a⟧ ∈ ⟦dom⟧`, which
  mentions the binder variable inside a compound term and so blocks the
  generalisation at that binder. They split as **61 lambdas** whose typing rule
  did not apply, **56 applications of an opaque constant** (the recursors),
  **20 locals** and 6 opaque constants. Cross-cut by the *target*: **72 of the
  143 are stated at a set-application `app(f,x)`** — a Lean type like a motive
  `C xs`, which the interpretation renders as an application and `has_type` has no
  rule to reduce. That is nearly all of the local ones (19 of 20) and most of the
  opaque-application ones (46 of 56). `has_type` unfolds a target along a
  *defining equation* (`TypeDelta`) but never **beta-reduces** one, and that
  missing clause is what stops a local's declared type `⟦List α⟧` from meeting an
  obligation stated at `⟦C xs⟧`. It is a smaller, better-defined piece of work
  than the currying layer and it is on the same critical path, since a recursor
  application's argument types are exactly motives applied to arguments.

- 2026-07-31 — **ι is certified for `Bool.rec`, `073_boolRecEqns` is at zero
  gaps and zero escapes, and the rule "only a closed argument can close a gap"
  needed a correction.**

  *Route 1, taken.* The "Wiring" section above prefers route 2 and its own
  correction shows route 2 cannot reach `tc.rs`. Route 1 is what landed: an
  `iota` method on `Certifier`, called from `whnf_no_unfolding_aux_with_cert`'s
  `Const` arm in place of `self.admit(e, reduced, Admit::Iota)`. It is the only
  change to `kernel/` in this push — **no new axiom and no new way to construct
  a `Thm`** — and it has a default implementation delegating to `admit`, so the
  null backend and every other backend are untouched and still report a gap.
  Kernel 628 → 631 non-comment lines of a 1000 budget.

  *The derived side.* `derived/src/wbool_rec.rs` joins `enums` to `wrec`:

  ```text
  A := 1+1   B := ∅   u := U(1+1)   T := {fls, tru}
  kf := ⟨inl •,⟨∅,∅⟩⟩          kt := ⟨inr •,⟨∅,∅⟩⟩
  e  := {⟨kf,fls⟩, ⟨kt,tru⟩}                     brec(fls,tru) := wrec(A,B,u,T,e)

  ⊢ ∀fls ∀tru. app(brec(fls,tru), ⟨inl •,∅⟩) = fls
  ⊢ ∀fls ∀tru. app(brec(fls,tru), ⟨inr •,∅⟩) = tru
  ```

  Both **unconditional in the two minor premises**, both about the same `brec`.
  Two things made that free. `T := {fls,tru}` rather than anything read off the
  motive is what discharges `wrec_total`'s `step_typed` with no assumption at
  all: the step has exactly two values and an unordered pair contains both. And
  the step is a **two-point graph** (`derived/src/twopoint.rs`), not `rec₊` as
  this note suggested — `rec₊` is a function of the *tag*, whereas the
  W-recursor applies its step to the whole triple `⟨a,⟨f,r⟩⟩`; with empty fibres
  `f` and `r` are forced to `∅`, so the triple takes two values and a graph on
  two points is exactly the right object. `comp_empty_domain` and
  `app_of_empty` collapse the composite as predicted.

  *The currying layer, built.* `⟦Bool.rec.{u}⟧` is a nest of four `lambda_n`
  graphs — `RecNest` in `tg.rs` — with `app(brec(F,T), b)` at the bottom. Its
  domains are read off the recursor's **own type**, each binder opened at a
  local exactly as `interp_lambda` opens one. That is load-bearing rather than
  stylistic: `reduce_rec` re-applies the matching `RecRule::val` to the same
  arguments, so the reduct's beta steps carry the very same domain premises, and
  the two sides of the iota equation can only *share* their assumptions if the
  two nests share their domains. They do, because both go through `interp` on
  the same Lean types. The note's estimate of what this costs was right: one
  `define_abbrev` + `lambda_n` + `beta_conditional_n` per level, and a domain
  premise per level at the point of use.

  *Measured, before → after.* `073_boolRecEqns` **12 → 10** gaps on the iota
  wiring alone (both ι gaps closed, two of the ten cascade gaps followed, two
  escapes appeared), and `116_rtreeRecReduction` 23 → 18. Tutorial 509 → 502.
  Then a second change (below) took `073` to **0 gaps and 0 escapes** — the
  first file in the corpus where a recursor meets a constructor and every step
  is a real kernel theorem.

  *The second change, and the correction it forces.* Chasing `073`'s two
  remaining `app_cong` guard failures found a **certificate-accounting bug in
  `tc.rs`**, older than any of this work. `def_eq` weak-head-normalises both
  sides and must compose the two reduction legs back on; the quick check on the
  *reduced* pair returned early and skipped that. When one side reduces to the
  other — which is exactly what an iota step does — it therefore returned
  **reflexivity as the certificate for `x ≡ y`**. The backend's congruence guard
  caught it where the caller was a congruence (those were `073`'s two guard
  failures and the corpus's nine); where the caller was the top-level judgement
  nothing caught it at all. Fixed by routing that exit through the same leg
  composition as every other, in one shared `compose_whnf_legs`. The early
  return is kept — falling through would also reach `eq_cache.union`, and
  populating the cache more eagerly trades derivations for `Admit::Cache` gaps
  (measured: 50 rather than 6 over the tutorials).

  **So the rule "only a closed argument can close a gap" is too strong.**
  `Bool.rec`'s arguments in `073` are *not* closed — `motive`, `falseVal` and
  `trueVal` are context locals, and the iota certificate is conditional on all
  three. It closes the gap anyway, because with nothing admitted beneath it the
  binder discharge (`pi_cong`/`lam_cong`) reaches it: `073` makes 16 conditional
  derivations and accounts for all 16. The corrected rule is: **a conditional
  certificate closes a gap exactly when no admitted step sits below it** — an
  admit poisons every rule above it one at a time, and it is the poison, not the
  conditionality, that strands the assumptions. That also explains the earlier
  measured negatives: they added derivations *under* an unrepaired admit.

  *Corpus, before → after (both changes).*

  | | before | after |
  | --- | ---: | ---: |
  | tutorial gaps (91 files) | 509 | **358** |
  | tutorial escapes | 115 | **47** |
  | tutorial `derived (real kernel Thm)` | 7514 | **7764** |
  | tutorial files at 0 gaps | 67 | **68** |
  | `073` / `075` / `076` / `077` gaps | 12 / 72 / 87 / 187 | **0 / 54 / 63 / 101** |
  | `073` / `075` / `076` / `077` escapes | 0 / 13 / 21 / 61 | **0 / 0 / 15 / 19** |
  | `116_rtreeRecReduction` gaps | 23 | **10** |
  | `init-prelude` gaps | 15646 | **11570** |
  | `init-prelude` escapes | 2486 | **812** |
  | `init-prelude` runtime | 17.6 s | **10.3 s** |
  | inductive-free fragment | 0 gaps, 0 escapes | 0 gaps, 0 escapes |
  | arena | 152/0/2 | 152/0/2 |
  | `derived` tests | 349 | 355 |

  Three files got **worse** and that is the accounting becoming honest, not a
  regression: `094_ruleK` 8 → 10, `124_quotLiftReduction` 8 → 9,
  `125_quotIndReduction` 7 → 8. Each reduces through a step this backend cannot
  justify (`Eq.rec`'s `is_k` iota, `Quot.lift`), and each was previously getting
  a dropped leg and a reflexivity certificate instead of a reported gap.

  *What `N.rec` and `List.rec` additionally need.* Measured, not estimated: the
  remaining iota gaps are **17 "the recursor is not applied to exactly four
  arguments"** (6 on `075`, 5 on `076`, the rest `Eq.rec`, `Acc.rec`,
  `prod.rec`) and **1 "no curried interpretation"**. So the blocker is not the
  currying layer's depth — that is mechanical, one more level per Lean argument
  — but the *W-recursor instance* underneath it. For `N` the fibres are not
  empty: `B(inr •) = 1`, so the step's `f` and `r` are one-point graphs rather
  than `∅`, `comp(wrec,f,1)` does **not** collapse by `comp_empty_domain`, and
  the ι equation's right-hand side genuinely mentions the recursive call. The
  step therefore has to compute `app(r, •)` and can no longer be a two-point
  graph; it is `rec₊` over one constant function and one graph in the recursive
  value, which is what this note originally proposed and what `Bool` did not
  need. `step_typed` also stops being free: `T := {zero-case, succ-case}` does
  not contain the value at a *recursive* call, so the target has to come from
  the motive after all, and that is where `⟦N⟧ ∈ ⟦Sort 1⟧` — already recorded as
  underivable with this `Sort` encoding — becomes load-bearing. `List` adds the
  parameter on top of all of that. The honest summary is that `Bool` was the
  degenerate case in exactly the way `enums.rs` is the degenerate case of
  `wlist.rs`, and the next rung is `N`, not a deeper nest.

- 2026-07-31 — **feasibility read for `N.rec`. `075`'s motive is constant, so
  route (a) is real; the `Sort` obstruction is real but is *not* in
  `step_typed`; and the cost is neither `Sort` closure nor the recursion
  theorem but the packed step `e`.** Nothing wired yet; one derived lemma
  landed, below.

  *What `075` actually contains* (dumped from the export, not assumed). The
  file declares `N.add := fun t => N.rec.{1} C z s t` with

  ```text
  C := fun x : N => (∀ _ : N, N)      -- a **constant** motive
  z := fun m : N => m
  s := fun n : N => fun ih : (∀_:N, N) => fun m : N => N.succ (ih m)
  ```

  and states `nRecReduction` as the conjunction of the two `rfl` equations.
  `067_nRec` is just `def nRec := N.rec.{u}` — it never reduces and is already
  at 0 gaps; it needs nothing. So the entry in the previous log — "the target
  has to come from the motive, and that is where `⟦N⟧ ∈ ⟦Sort 1⟧` becomes
  load-bearing" — is **half right**. `T` does have to come from the motive,
  but the motive is constant, so `T := ⟦motive N.zero⟧ = app(⟦C⟧, ⟦N.zero⟧)`,
  which the motive graph's own `beta_conditional` computes to `fs(⟦N⟧,⟦N⟧)`
  given `⟦N.zero⟧ ∈ ⟦N⟧`. Nothing about `Sort` is needed for `T`.

  Better: `T := ⟦motive N.zero⟧` is **literally `doms[1]`**, the domain the
  currying nest already walks off the recursor's own type, and `step_typed`'s
  two halves are then

  ```text
  ⟦z⟧ ∈ T                                                -- = the level-2 domain obligation
  ∀n ∀y. ((n ∈ ⟦N⟧ ∧ y ∈ T) → app(app(⟦s⟧,n),y) ∈ T)     -- = ⟦s⟧ ∈ fs(⟦N⟧, fs(T,T)), twice `funspace_app_mem`
  ```

  — i.e. exactly the argument typings the iota derivation is already paying
  for. So `step_typed` is **not** free (the brief is right) but it is also not
  new work: it is the recursor's own domain obligations, and `has_type` can be
  asked for the second at the beta-reduced kernel term `fs(⟦N⟧, fs(T,T))`
  rather than at `doms[2]`, which is a dependent product it cannot match.

  *Where `Sort` really bites, measured.* Instrumenting `domain_obligation` on
  `075` (temporary probe, removed) gives the full list of undischarged typing
  obligations. Two closed lambdas fail, 6 times each:

  | argument | why |
  | --- | --- |
  | `fun x:N => ∀_:N, N` (the motive) | wants `⟦N → N⟧ ∈ ⟦Sort 1⟧`, i.e. `fs(N,N) ∈ U(⟦Sort 0⟧)` over an opaque `⟦Sort 0⟧` — **underivable**, as recorded |
  | `fun n => fun ih => fun m => N.succ (ih m)` (the `succ` minor) | `has_type_lam`'s dependent branch needs `targs[0] == dom`, and the fibre is `fs(app(C,a), app(C,succ a))` while the binder's domain is `fs(N,N)`; it needs the motive **beta-reduced inside the fibre** |

  The rest are locals (discharged at their binders) and `N.rec` itself. So the
  motive's typing is the one genuinely undischargeable premise, and since the
  motive in `075` is a **closed** term it cannot be discharged at a binder
  either: an iota certificate for `075` will carry it and it will **escape**.
  Predicted shape of the result, therefore: the 6 ι gaps and most of the 48
  cascade gaps close, and a small number of escapes appear — the same pattern
  `073` showed at its first stage (12 → 10 with two escapes), not zero. `073`
  reached zero only because *its* motive is a context local.

  *Route (b) is not needed, and neither is the ω-tower.* Checked: the brief's
  proposed route to `W(A,B,u) ∈ u` via a member `v ∈ u` with `W ⊆ v` runs into
  closure of a universe under `⋃` — `app(f,x)` is `⋃coll(f,x)`, and `coll` is
  reachable by `cantor::image_in_universe` but the union over it is not. Binary
  union closure is the same obstruction one step down and is exactly what
  `funspace/in_universe.rs` already records as open. That would be the real
  cost of (b), and none of it is on the path, because `T` comes from the motive
  and the motive is constant.

  A tempting third route — `T := U(⟨z,s⟩)`, making `step_typed` free and
  *generic* (it would serve `List.rec` too) by transitivity alone — dies on the
  same rock: it needs `app(g,x) ∈ u` for an **arbitrary** `g ∈ u`, and that is
  `⋃`-closure again. It survives with `sv(g)` added as a hypothesis, since a
  single-valued graph's value is an element-of-element-of-element and `C₁`
  reaches it; worth remembering if the dependent case is ever attacked.

  *What the remaining cost actually is.* The packed step. For `Bool` it is a
  graph on two points (`twopoint.rs`, 215 lines) because the fibres are empty
  and the triple `⟨a,⟨f,r⟩⟩` takes exactly two values. For `N` the `succ` fibre
  is `1`, so `f` and `r` range over `fs(1,W)` and `fs(1,T)` and the step has to
  compute `app(app(s, app(f,•)), app(r,•))`. `derived` has no `fst`/`snd`
  operator, so a lambda graph over the triples is not available; the cheapest
  construction is one Replacement over `{∅} ∪ prod(fs(1,W), fs(1,T))` along

  ```text
  φ(q,p) := (q = ∅ ∧ p = ⟨⟨inl •,⟨∅,∅⟩⟩, z⟩)
          ∨ ∃f ∃r. (q = ⟨f,r⟩ ∧ p = ⟨⟨inr •,⟨f,r⟩⟩, app(app(s,app(f,•)),app(r,•))⟩)
  ```

  — the existential does the projecting, so no new operator is needed — plus
  its two computation rules, the `inl • ≠ inr •` disjointness that separates
  them, `step_typed` from the two hypotheses above, and the glue to
  `wrec_total`'s ι. Estimate, at this codebase's density: 700–1000 lines for
  `wnat_rec.rs` and its tests. The backend then needs `derive_iota` generalised
  from "exactly four arguments" to **n ≥ 4** (`075` applies `N.rec` to five —
  the motive is a function type, so there is a trailing argument, and that is
  what all 6 of its current ι gaps report) and from a major premise that is a
  bare `Const` to one **applied to its fields** (`N.succ n`), plus the `T` and
  premise plumbing above: 300–500 lines. **Two to three sessions**, none of it
  a kernel change, no new axiom, and the ω-tower and the recursion theorem stay
  off the path exactly as they have been since the transitivity clause landed.

  *Landed now.* `wrec_typing.rs` gains the one lemma every route needs and
  `Bool` never did — the composite at a non-empty fibre:

  ```text
  ⊢ ∀g ∀f ∀d. sv(comp(g,f,d))                      [composite_single_valued]
  ⊢ ∀g ∀f ∀d ∀b. (b ∈ d → app(comp(g,f,d),b) = app(g,app(f,b)))  [composite_app]
  ```

  Both unconditional apart from `b ∈ d`, which is genuine (off `d` the
  composite relates nothing and `app` is `∅`). `tests/wrec.rs` pins both at
  fresh constants and cashes the second at the instance `N` needs, with the
  antecedent **discharged**: at `d := 1` and `f := {⟨•,n⟩}` it reads
  `app(comp(g,{⟨•,n⟩},1), •) = app(g,n)` — the recursive call, which is
  precisely what `comp_empty_domain` collapses away for `Bool` and what `N`'s ι
  right-hand side has to produce. `derived` 355 → 358 tests. Corpus unmoved and
  deliberately so: `073` 0 gaps / 0 escapes, `075` 54 / 0, `076` 63 / 15,
  `067` 0, fragment 27/27 zero gaps zero escapes, arena 152/0/2,
  `ci/check.sh` green.

- 2026-07-31 — **`N.rec` is derived, ι fires with the recursive call live, and
  the projections `π₁`/`π₂` are built because the shorter construction would
  have had to be replaced.** Backend not started; `075` is unmoved and
  deliberately so.

  *What landed.* `derived/src/proj.rs` (~300 lines, 5 tests) introduces `⋂p` by
  Separation on `⋃p` and defines

  ```text
  π₁ p := ⋃⋂p          π₂ p := app({p}, π₁ p)
  ⊢ ∀a ∀b. π₁⟨a,b⟩ = a      ⊢ ∀a ∀b. π₂⟨a,b⟩ = b
  ⊢ ∀a ∀b. ⟨π₁⟨a,b⟩, π₂⟨a,b⟩⟩ = ⟨a,b⟩
  ```

  all unconditional. `π₂` is **not** the textbook
  `⋃{y ∈ ⋃p : ⋃p ≠ ⋂p → y ∉ ⋂p}`: that needs a case split on `a = b`, and the
  split disappears entirely once one notices that `{⟨a,b⟩}` *is* a one-point
  function whose value at `a` is `b`. So `π₂` is `point_fun::point_app` and a
  congruence, and `point_fun` absorbs the degenerate case.

  `derived/src/wnat_rec.rs` (~1050 lines, 7 tests) packs Lean's two minor
  premises into the W-recursor's single step and derives, with
  `HYP := z ∈ T ∧ s ∈ fs(N, fs(T,T))`:

  ```text
  ⊢ ∀z ∀s ∀T. app(e(z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z
  ⊢ ∀z ∀s ∀T ∀f ∀r. ((f ∈ FW ∧ r ∈ FT(T)) →
        app(e(z,s,T), ⟨inr •,⟨f,r⟩⟩) = app(app(s,app(f,•)),app(r,•)))
  ⊢ ∀z ∀s ∀T. (HYP → step_typed(1+1, B, U(1+1), T, e(z,s,T)))
  ⊢ ∀z ∀s ∀T. (HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z)
  ⊢ ∀z ∀s ∀T ∀n. ((HYP ∧ n ∈ N) → app(nrec(z,s,T), ⟨inr •,{⟨•,n⟩}⟩)
        = app(app(s,n), app(nrec(z,s,T), n)))
  ```

  The last is **ι with the recursive call live** — its right-hand side mentions
  `nrec` again — which is what `Bool` could not exercise and what
  `wrec_typing::composite_app` was landed in advance for. `HYP` is satisfiable
  and is *discharged* at `T := 1`, `z := •`, `s :=` the constant function
  (`premise_witness`), so `⊢ app(nrec, ⟨inl •,∅⟩) = •` holds with nothing
  assumed.

  *The construction, and the one that was thrown away.* The feasibility read
  proposed one Replacement over `{∅} ∪ prod(fs(1,W), fs(1,T))` whose relation
  uses an existential to do the projecting, "no new operator needed". That was
  built first and it works. It was then **replaced**, on the extend-or-replace
  test: `List.cons` has a field as well as a recursive argument, so its step
  value has three components rather than two, and with the existential encoding
  that is a third Replacement layer — widening `step_cases`, `value_at_*` and
  `step_single_valued`, i.e. rewriting every proof in the file. With projections
  it is one more `π` in the value term and nothing else, because every lemma
  between the step's Replacement and `unpack` is stated at the **packed**
  payload and never names a component. The thesis agrees independently: §5.1's
  menagerie takes `Σx : α. β` with `π₁` and `π₂` as *primitives*, with ι rules
  `π₁(a,b) ≡ a` and the η rule `(π₁ x, π₂ x) ≡ x`, so it expects to project out
  of packed tuples everywhere.

  *What is deliberately not built.* The `Σ` **type former**. The step's true
  domain is dependent — at `inl •` the payload is in `fs(0,N) × fs(0,T)`, at
  `inr •` in `fs(1,N) × fs(1,T)` — but both embed in the single non-dependent
  `𝒫(prod(1,N)) × 𝒫(prod(1,T))`, since `fs(0,X) = {∅}` and `∅` is in every power
  set. That collapse holds whenever the fibres are bounded by a common power
  set, which covers every non-indexed inductive with finitely many recursive
  arguments per constructor, `List` included. `Σ` becomes load-bearing only for
  an unbounded fibre family, which is out of scope for the same reason the
  ω-tower is. *(Both are built:
  `derived/src/sigma/{dsum,pair_parts,push,reindex,telescope}.rs` for the `Σ`
  former, and `derived/src/wpath/` for the unbounded fibre family. The
  collapse-argument above is still the reason `Σ` was **not** needed for the
  shapes this note covers, and that is why it is kept.)*

  *Measured.* `derived` 358 → 370 tests. **The corpus is unmoved**, and
  deliberately: nothing in `checker/src/tg.rs` is wired, so `075` is still
  54 gaps / 0 escapes, `073` 0 / 0, `076` 63 / 15, fragment 27/27 zero gaps zero
  escapes, arena 152/0/2, `ci/check.sh` green. `GAP_BUDGET` and
  `RECURSOR_DERIVED` are untouched.

  *What the backend needs, precisely.* Four things, all listed in the closing
  notes of `wnat_rec.rs`: a `nat_recursor()` sharing `bool_recursor()`'s
  expensive `Recursor`/`totality`/`iota` prefix; `rec_nest`'s bottom made
  pluggable (the *depth* is the same four for `N.rec`, only `t₄` differs);
  `derive_iota` generalised from "exactly four arguments" to `n ≥ 4` and from a
  bare-`Const` major premise to one applied to its fields; and `HYP` supplied at
  the point of use, where `T := doms[1]` makes `z ∈ T` literally the level-2
  domain obligation and `s ∈ fs(N,fs(T,T))` an obligation that must be asked at
  the beta-reduced kernel term rather than at the dependent `doms[2]`.

  *The prediction stands and is untested.* `075`'s motive is a **closed** term
  whose typing wants `fs(N,N) ∈ U(⟦Sort 0⟧)`, underivable with this `Sort`
  encoding and undischargeable at any binder, so an ι certificate for `075` will
  carry it to the boundary and escape. Expect the `073`-first-stage pattern —
  the 6 ι gaps and most of the 48 cascade gaps closing, a few escapes appearing
  — not zero.

- 2026-07-31 — **`N.rec` is wired, `075_nRecReduction` is at 4 gaps and 1
  escape, and the prediction that most of the cascade would merely turn into
  escapes is refuted.** All six ι gaps closed; nothing in `kernel/` changed.

  *The four items, all done.* (1) The expensive prefix — `Recursor::new`, the
  one-point extension, `totality`, `iota`, `wrec_funspace` — is now a `RecCore`
  of its own, shared by `bool_recursor()` and the new `nat_recursor()`. It
  mentions no tag set, so there was never a reason to build it twice, and
  sharing is not merely a saving: a second `Recursor::new` mints fresh symbols
  and nothing composes across the two. `Inductives` gained the `PointFun` field
  because `NatRec::over` insists on the very one `Nat` was built over. (2)
  `rec_nest`'s bottom is pluggable (`RecBottom`), its depth is `major_idx + 1`
  rather than a hand-unrolled four, and **every level now carries the whole
  prefix above it** (`prefixes[k] = 0..k`) rather than only what its body
  mentions. That last change is the one that generalises: `Bool`'s bottom
  ignores the motive, `N`'s cannot, because its target `T` *is* the motive at
  `N.zero`. (3) `derive_iota` splits the trailing arguments off both sides,
  derives the equation at the **core** — the recursor applied to exactly its own
  arguments — and lifts it back by congruence, with the guard still comparing
  against the full redex and reduct; the major premise is `unfold_apps`ed, so a
  constructor applied to its fields is now the normal case. (4) `HYP` is
  supplied at the point of use: `⟦z⟧ ∈ T` is literally the level-2 domain
  obligation, handed back by `nest_chain` rather than asked a second time, and
  `⟦s⟧ ∈ fs(⟦N⟧,fs(T,T))` is asked at that kernel term and transported to the
  W-type along `⊢ ⟦N⟧ = W(1+1,B,U(1+1))` — the *assumption* staying stated at
  the abbreviation, which is what keeps it dischargeable at a binder.

  *Two older bugs that only an ι certificate could reach.* `derive_beta`
  counted its contractions on the **substituted** head rather than on the
  syntactic lambda nesting. `075`'s zero rule is
  `(λ motive zero succ. zero) C z s m`; the checker peels three lambdas and
  re-applies `m`, but after three substitutions the head is `fun m => m`, so the
  backend took a fourth contraction and proved a *different* equation. Its own
  guard caught it — three times on `075` — and reported a gap, which is the
  system working, but the derivation was there for the taking. And
  `recall_reduction` had nothing to recall whenever a reduct had been memoised
  by an uncertified `whnf` call; it now re-runs the reduction and uses the
  certificate **only if it lands on the memoised reduct**, so what the checker
  returns is unchanged and a disagreement (the cheap-projection variant shares
  the cache key) still admits. Neither fix is about inductives, and both were
  invisible while an admit sat underneath them.

  *Measured, staged so the credit is honest.* `075` **54 → 33** on the ι wiring
  alone, **33 → 12** on `derive_beta`, **12 → 4** on the `whnf` recall. The
  `whnf` fix also moved `101_proofIrrelevanceWhnf` 10 → 6,
  `113_reduceCtorParamRefl.mk` 5 → 1 and `114_reduceCtorParamRefl2.mk` 6 → 2.

  | | before | after |
  | --- | ---: | ---: |
  | tutorial gaps (91 files) | 358 | **296** |
  | tutorial escapes | 47 | **48** |
  | tutorial files at 0 gaps | 68 | 68 |
  | `073` / `075` / `076` gaps | 0 / 54 / 63 | **0 / 4 / 63** |
  | `073` / `075` / `076` escapes | 0 / 0 / 15 | **0 / 1 / 15** |
  | `init-prelude` gaps | 11570 | **10919** |
  | `init-prelude` escapes | 812 | **834** |
  | inductive-free fragment | 0 gaps, 0 escapes | 0 gaps, 0 escapes |
  | arena | 152/0/2 | 152/0/2 |
  | `derived` tests | 370 | 370 |

  Nothing else in the tutorial corpus moved by a single gap or escape;
  `ci/check.sh` is green.

  **The prediction was right about the escape and wrong about its size.** The
  feasibility read expected the `073`-first-stage pattern — the ι gaps and most
  of the cascade closing, "a few escapes appearing". Exactly **one** escape
  appeared. It carries three assumptions: `⟦motive⟧ ∈ ⟦N → Sort 1⟧`, which is
  the closed-motive obstruction predicted (`fs(N,N) ∈ U(⟦Sort 0⟧)` over an
  opaque `⟦Sort 0⟧`, dischargeable at no binder), plus the `succ` minor's typing
  at both `doms[2]` and its beta-reduced form. Three undischargeable
  assumptions, **one** gap — because a conditional certificate with nothing
  admitted beneath it is one gap however far it travels, whereas an admit
  poisons every rule above it one at a time. The `Bool` entry recorded that as a
  correction to "only a closed argument can close a gap"; on `N` it is the
  dominant effect rather than a caveat, and it is why the answer is 4 rather
  than the ~20 the prediction implied.

  *What is left on `075`, and none of it is the recursor.* Two `pi congruence:
  the body certificate is not the fibres' pointwise equation` (the `dprod_ext`
  route, 283 occurrences on `init-prelude` — a pre-existing weakness now
  unmasked), one congruence above them, and the one escape. The ι rule, its
  cascade, `derive_beta` and the `whnf` recall are all gone.

  *What `List.rec` still needs.* Recorded in full on `RecBottom` in `tg.rs`.
  From the nest: **nothing** — depth five is already `major_idx + 1` and the
  prefixes already carry everything. What is needed is a `derived::wlist_rec`
  (one more `π` in the step's value term, which is the whole argument for
  `proj.rs`); **parameter handling**, because `List.rec` has `num_params = 1` so
  the minor premises are no longer at `vars[1]`/`vars[2]` and `List.nil`/`cons`
  carry `α` — `derive_iota_core` rejects a constructor with parameters today;
  and `T := doms[2]`, the motive at `List.nil α`, with a `HYP` mentioning `α`.
  `076` should aim at the `073` outcome rather than the `075` one: its theorem
  is stated under `∀ α (xs : List α)`, so every argument is a context local and
  every assumption is dischargeable at a binder.

- 2026-07-31 — **`List.rec` is derived and wired, `076_listRecReduction` is at
  4 gaps… no: at 32, with all five ι gaps closed. The "one more `π`" claim held
  in full. The prediction that `076` would reach the `073` outcome is refuted,
  and the reason is that its escapes were never the recursor's.**

  This was the milestone the whole inductives push was aimed at: the corpus's
  only `List` file, with a recursor meeting a constructor that carries a *field*
  as well as a recursive argument.

  *The derived side.* `derived/src/wlist_rec.rs` (~1000 lines, 7 tests) joins
  `wlist` to `wrec`, with `HYP := z ∈ T ∧ s ∈ fs(α, fs(lt(α), fs(T,T)))`:

  ```text
  ⊢ ∀α∀z∀s∀T. app(e(α,z,s,T), ⟨inl •,⟨∅,∅⟩⟩) = z
  ⊢ ∀α∀z∀s∀T∀h∀f∀r. ((h ∈ α ∧ (f ∈ FW(α) ∧ r ∈ FT(T))) →
        app(e(α,z,s,T), ⟨inr h,⟨f,r⟩⟩) = app(app(app(s,h),app(f,•)),app(r,•)))
  ⊢ ∀α∀z∀s∀T. (HYP → step_typed(1+α, fam(α), U(1+α), T, e))
  ⊢ ∀α∀z∀s∀T. (HYP → app(lrec(α,z,s,T), ⟨inl •,∅⟩) = z)
  ⊢ ∀α∀z∀s∀T∀h∀t. ((HYP ∧ (h ∈ α ∧ t ∈ lt(α))) →
        app(lrec(α,z,s,T), ⟨inr h,{⟨•,t⟩}⟩)
             = app(app(app(s,h),t), app(lrec(α,z,s,T), t)))
  ```

  Every statement is **unconditional in `α`** beyond what Lean's own signature
  says, exactly as `wlist.rs`'s memberships are. `HYP` is discharged outright by
  `premise_witness` at `α := 1`, `T := 1`, `z := •` — `α := 1` rather than the
  cheaper `α := 0` deliberately, because with an empty parameter the cons rule's
  own hypothesis `h ∈ α` would be unsatisfiable and that rule would still say
  nothing. At `α := 1` the cons ι rule fires at `h := •`, `t := nil`, with
  nothing assumed, and `tests/wlist_rec.rs` pins that.

  *The "one more `π`" claim, cashed.* `wnat_rec.rs`'s closing notes justify
  `proj.rs` by predicting that a constructor with a field costs "one more `π` in
  the value term and nothing else, because every lemma between the step's
  Replacement and `unpack` is stated at the packed payload". **It held.**
  `value_packed` gained one application, `unpack` one congruence, and
  `step_cases`, `value_at_packed`, `value_at_nil` and `step_single_valued` are
  `wnat_rec`'s proofs with `h` threaded through as an *inert extra argument* —
  not one of them changed shape. The construction that was thrown away for this
  reason would have needed a third Replacement layer and a rewrite of all four.

  What the prediction did **not** cover, and what the next reader should expect:
  `List`'s *tag* varies. `N`'s cons-side key is the constant `inr •`; `List`'s
  is `inr h`. So the Replacement can no longer range over the fibre payload
  alone — it ranges over `q ∈ prod(α, P(α,T))` — and one projection appears at
  the Replacement, in `row_at`. It stays confined there, and the reason is the
  one real design choice in the file: stating `value_at_packed` at `(h,p)`
  rather than at `q` means the case analysis compares `⟨inr h, p⟩` with
  `⟨inr(π₁ q), π₂ q⟩` and reads off `h = π₁ q` (by `inr_inj`) and `p = π₂ q`
  *separately*, never reassembling `q` and so never needing the η rule
  `⟨π₁ q, π₂ q⟩ = q`. Had it been stated at `q`, `step_cases` would have had to
  carry the dropped membership `q ∈ prod(α,P(α,T))` through every case analysis
  — precisely the widening the existential encoding was rejected for.

  *The wiring.* `RecBottom` gained a third arm and `tg.rs` a `list_rec_shape`,
  a `list_recursor()` on the same `RecCore`, and `fire_list`. From the nest:
  **nothing**, as the previous entry predicted. What the parameter cost:

  1. the minors and the target move along by `num_params` — `vars[np+1]`,
     `vars[np+2]`, `doms[np+1]`, the last being the motive at `List.nil α`;
  2. `derive_iota_core` stopped rejecting a constructor with parameters and now
     takes `ctor_args[num_params..]`, mirroring `reduce_rec`'s
     `num_extra_params_to_major`, held to it by requiring the argument count to
     be `num_params + num_fields` exactly and by the existing guard against the
     reduct `reduce_rec` really produced;
  3. `⟦List α⟧` is `app(⟦List.{u}⟧, ⟦α⟧)` and so is a **redex**, so the bridge
     to `lt(α)` is `wlist_fun`'s `l_beta` under `⟦α⟧ ∈ ⟦Type u⟧` — a
     *conditional* equation, hence `mem_along_c` beside `mem_along`;
  4. `wlist_fun` gained `nil_beta` and `cons_beta`, the *equations* behind the
     two membership rules it already exported. ι needs
     `app(Nil(S),α) = ⟨inl •,∅⟩`, not `∈`.

  *Measured, before → after.*

  | | before | after |
  | --- | ---: | ---: |
  | tutorial gaps (91 files) | 296 | **265** |
  | tutorial escapes | 48 | **49** |
  | tutorial files at 0 gaps | 68 | 68 |
  | `073` / `075` / `076` gaps | 0 / 4 / 63 | **0 / 4 / 32** |
  | `073` / `075` / `076` escapes | 0 / 1 / 15 | **0 / 1 / 16** |
  | `076` ι gaps | 5 | **0** |
  | `init-prelude` gaps | 10919 | **10771** |
  | `init-prelude` escapes | 834 | **843** |
  | inductive-free fragment | 0 gaps, 0 escapes | 0 gaps, 0 escapes |
  | arena | 152/0/2 | 152/0/2 |
  | `derived` tests | 376 | **384** |

  Nothing else in the tutorial corpus moved by a single gap or escape; the whole
  31-gap improvement is `076`. (The handover's baseline of 370 `derived` tests
  was right; a *concurrent* session added `derived/{src,tests}/choice.rs` — six
  tests — while this work was in progress, so the tree measured 376 immediately
  before these eight landed. 384 is the total; +8 is this entry's.)

  **The prediction of the `073` outcome is refuted, and the reasoning behind it
  was wrong in a specific way.** The brief argued that `076` states its theorem
  under `∀ α (xs : List α)`, so every argument is a context local and every
  assumption is dischargeable at a binder. The first half is true and the second
  does not follow. The decisive measurement is that `076` had **15** escaping
  certificates *before* any ι certificate existed and has **16** after: closing
  five ι gaps and 26 cascade gaps beneath them moved the escapes by one. So the
  escapes were never the recursor's, and "conditional on a local" was never what
  was stranding them.

  *What the residue is made of*, since that is the interesting number. 32 =
  **16 escapes** + **3 primary gaps** + **13 cascade** over those three. The
  three are two `eq_cache` and one
  `pi congruence: the body certificate is not the fibres' pointwise equation` —
  the `dprod_ext` route, 283 occurrences on `init-prelude`, which is *also*
  what two of `075`'s remaining four are. Probing the escaping certificates'
  assumptions gives, by occurrence: 15 × `⟦α⟧ ∈ ⟦Type 0⟧`, 4 × `⟦xs⟧ ∈ ⟦List α⟧`,
  2 × `⟦h⟧ ∈ ⟦α⟧` — all locals, all dischargeable at a binder *in principle* —
  plus 1 × the motive lambda `fun _ : List α => List α` at `List α → Sort 1` and
  2 × the cons minor premise. The last two are the obstructions already on
  record: the motive's typing wants `⟦List α⟧ ∈ ⟦Sort u⟧`, which `wlist.rs`'s
  header records as underivable with this `Sort` encoding (nothing relates
  `W(1+α,fam,U(1+α))` to `U(⟦Sort 0⟧)`), and the minor's wants the motive
  beta-reduced inside a dependent fibre. So `076`'s residue is `075`'s residue
  at `076`'s binder depth: a *local's* typing escapes only because a `pi_cong`
  above it admitted and could no longer peel its guard.

  The corrected rule, third revision: an admit poisons every rule above it one
  at a time; a conditional certificate is one gap however far it travels; **and
  a conditional certificate whose binder-discharge is blocked by an admit above
  it escapes even though its assumption is a local's**. `073` reaches zero
  because nothing above its certificates admits. The single cheapest thing that
  would move `075`, `076` and `077` together is therefore still not an
  interpretation but `pi_cong`'s extensionality route.

  *What indexed families need next.* Nothing from `wlist_rec.rs`, and that is
  the point: `α` is a **parameter**, fixed throughout the declaration, so it
  stays a free variable and §5.2's `good` predicate is vacuous — which is what
  lets `lt(α)` be the W-type outright. An *index* varies per constructor, so the
  translation carves a subset by `good`, whose base case is an **equality**
  between index tuples. `prop.rs` interprets `Eq` as a conditional singleton,
  which types `Eq.refl` and no more; `good` needs `Eq`'s *elimination*, and for
  `Eq` that is `is_k` subsingleton elimination (§5.3), which abandons W-types
  for `acc`. The order is therefore `acc`, then §5.3, then §5.2's `spec`
  judgment — and only then a second file beside `wlist_rec.rs`. Extending it
  would not reach them. The nearer and much cheaper generalisation is a
  constructor with **two or more plain recursive arguments**: that changes only
  the fibre — `f` and `r` are still single sets, over a two-point domain instead
  of `1` — so neither the encoding nor any proof in `wlist_rec.rs` cares.

  **Correction, 2026-08-01: `116_rtreeRecReduction` is not that test.** It was
  named here and in three other places, and the export says otherwise:
  `RTree.node` has `numFields: 1` and `RTree` carries `isReflexive: true`, i.e.
  its single recursive argument is *function-typed*, `children : (Bool → RTree)`.
  That is the `Σ(z::γ)` fibre shape, not the `m ≥ 2` shape — harder, not
  cheaper, and the reduct contains a lambda under the minor premise.
  Exhaustively: the tutorial corpus contains **no** plain `m ≥ 2` constructor on
  a non-indexed type. `RBTree.red`/`black` (`042`/`068`/`077`) are the only
  `m ≥ 2` constructors and `RBTree` is an indexed family (`numIndices: 2`,
  `numParams: 1`), so it is the *previous* bullet's work, not this one's. The
  witnesses live in `init-prelude`: `Lean.ParserDescr.binary`
  (`Plain, Rec, Rec`), and `sepBy`/`sepBy1` (`Rec, Plain, Rec, Plain` —
  interleaved, which is where the interleaving requirement actually comes from).

- 2026-08-01 — **the translation is a procedure now: the carrier half of §5.2
  is driven by declaration data, and it runs at seven shapes.** `derived/src/inductive/`,
  with `derived/src/finset.rs` and `derived/src/recarg.rs` beneath it. `derived`
  525 → 543 tests; `ci/check.sh` green throughout; nothing in `checker/` touched.

  *The spec.* `DeclSpec { params: np, ctors: [CtorSpec { args: Vec<FnSym>, recs: usize }] }`
  — and nothing else, because nothing else is what §5.2's `spec` judgment looks
  at. Argument types are **function symbols**, `βᵢ` of arity `np + i`, because
  the thesis's
  `A[y'/y]`/`B[π₁p'/y]` is only expressible as *applying a symbol to different
  terms*. *(The reason recorded here was "the kernel has `Formula::subst` but no
  `Term::subst`". **That reason is void** — `Formula::subst` is public and
  `derived::subst_term` derives term substitution over the kernel's existing API;
  DECISIONS.md 2026-08-06. The symbol design is right for a different reason,
  which is that the caller wants the *equation*, not the body.)* That was flagged as the thing to establish early, and it is
  **workable**: dependency is unrestricted (`βᵢ` may mention every earlier
  argument, which is the dependent telescope), and the cost falls on the
  caller, who must `define_abbrev` the Lean type expression over the parameter
  and argument variables. For `List`'s `cons` that symbol is the identity,
  `β₀(p) = p`. A recursive argument is *counted*, not described, which is
  exactly the non-nesting assumption: `thesis.txt:1800`'s `Σ(z::γ)` collapses to
  `1` only for a non-nested recursive argument.

  *Two new primitives, and why the ones from yesterday were not enough.*
  `finset.rs` is `{a₀} ∪ ({a₁} ∪ (… ∪ ∅))` with its `m` memberships and
  `⋀ aᵢ ∈ T → fin(a⃗) ⊆ T`; `fibre.rs` was already building that term by hand
  and now shares it. `recarg.rs` is the constructor's recursive-argument
  function. The brief's warning that `finord(1)` is `1 + 0` and not the term `1`
  is **load-bearing**: the single element of `finord(1)` is `inj_0(•) = ⟨∅,•⟩`,
  so `point_in_funspace`'s `fs({a},T)` never matches and `wnat`'s one-point graph
  cannot be reused at any arity. The general function is a
  `Dispatch` over `m` copies of `1` with one-point graphs as branches — and the
  one non-obvious move is **its codomain**. `Dispatch::new` demands
  *unconditional* branch typings, but `{⟨•,r_j⟩} ∈ fs(1,S)` needs `r_j ∈ S`,
  which is precisely the hypothesis the constructor rule is trying to work
  under. Taking the codomain to be `fin(r⃗)` makes every branch typing
  unconditional (`r_j ∈ fin(r⃗)` holds by construction) and moves the `m`
  hypotheses into `fs_mono`'s premise `fin(r⃗) ⊆ S`, where they are paid once.
  No change to `Dispatch` was needed.

  *The bound is now one lemma, four times, with no case analysis.* `wnat.rs` and
  `wlist.rs` both seed the universe at `A` and then split on the tag sum to show
  each constructor's fibre lands in `U(A)`. That does not generalise — the
  fibres are `finord(mᵢ)` and `finord(m) ∈ U(A)` would want `U` closed under
  binary sums. Seeding at **`c := {A, T}`** instead, with `T` the fibre family's
  codomain, removes the problem: `c ∈ U(c)` is `mem_least_universe`, `A ∈ c` and
  `T ∈ c` are `upair_members`, and `least_universe_transitive` turns each into
  membership in `U(c)`; the family condition is `Fibre::values_in_target`
  followed by transitivity once more. So the whole obligation is four uses of
  the transitivity clause and it never asks what `mᵢ` is. **This is the first
  construction that could not have been written before the 2026-07-31
  transitivity clause** — the hand-written files could have, since their fibres
  are `0` and `1`.

  *`ext::funspace_app_mem` confirmed.* The brief's note that it gives
  `∀a ∈ A. app(B,a) ∈ T` directly, with no case analysis on the tag sum, is
  right, and it is what `Fibre::values_in_target` already packages. `wnat.rs`'s
  comment to the contrary should be read as being about `wnat.rs`.

  *The "no junk" lemma was not needed.* It was named as the obvious next
  primitive; the carrier half never asks for it. Constructor typing is `sup`
  forwards, injectivity and distinctness are the Kuratowski pair backwards.
  Inversion is a *recursor*-side obligation, and `bound::w_inversion_at` already
  has the W-type form of it. It should be built when the recursor needs it, not
  before.

  *Shapes demonstrated, with the same code:* `Empty` (0 constructors — tag set
  `0`, fibre family `∅`, bound still discharged), `Unit`, `Bool`, **`RGB` (3
  nullary constructors)**, `N`, `List α`, **a binary tree (`node : T → T → T`)**,
  and **a two-argument dependent telescope** where the second argument's stated
  type mentions the first. The last three are shapes nothing in `derived/` could
  express. Non-vacuity is cashed at each: `RGB` has three pairwise-distinct
  closed elements, `N` has `zero`, `succ zero`, `succ (succ zero)` pairwise
  distinct and all in the carrier, `node` is injective in **both** subtrees, and
  the dependent constructor is inhabited at `⟨•,•⟩`.

  *One shape difference from the hand-written files, deliberately.* A nullary
  constructor's membership is stated **without** an antecedent rather than under
  a vacuous one, because `073`'s result turns on `⟦Bool.true⟧ ∈ ⟦Bool⟧` being a
  closed unconditional theorem. That is what `inductive/shared.rs`'s
  `Ctx(Option<Formula>)` exists for; every step of the constructor derivation
  goes through it.

  *What is still open, and is not in this file.* Wiring into `checker/src/tg.rs`
  (a concurrent task), and the recursor/ι. `Inductive::ty` is a `define_abbrev`
  symbol of arity `np`, which is the shape `tg.rs`'s `ind_abbrev` already keys
  on, and `Ctor::mem`'s hypothesis list is in constructor-argument order, which
  is what `CtorApp` instantiates against.

- 2026-08-01 — **the `n`-ary sum and its injections are real symbols now, and
  the injection's cache key is `i` alone.** `derived/src/isum/symbols.rs`.
  `derived` 543 → 548 tests; `ci/check.sh` green; `checker/` untouched.

  *The design.* `Sum_n(A₀ … A_{n-1})` and `Inj_i(a)` are `define_abbrev`
  symbols, minted on demand and cached — `Sum_n` by `n`, `Inj_i` by **`i`** —
  with the nest of `derived/src/isum/tags.rs` demoted to "the construction".
  `derived/src/sigma/dsum.rs` is the pattern followed. Downstream, nothing in
  `fibre.rs`, `recarg.rs` or `inductive/` states anything over the nest any
  more; `Dispatch` still walks it internally and restates every export over the
  symbols at its boundary.

  *Why `i` and not `(n,i)`, and what it says about the trailing `+ 0`.*
  `inj_i(a) = inr^i(inl(a))` mentions neither `n` nor any summand, so one symbol
  per depth serves every arity and the cache is linear rather than quadratic.
  That is a **second, independent argument for keeping the trailing `+ 0`**,
  beyond the uniformity one `tags.rs` already made: collapse it and the last
  injection becomes `inr^{n-1}` with no `inl`, which *does* depend on `n`.
  `tests/isum.rs` pins it — the same `Inj_1` lands in `Sum_2`, `Sum_3` and
  `Sum_4`.

  *What the properties cost.* Membership, injectivity and distinctness are each
  one Leibniz transport off the corresponding nest lemma, and all three are
  cached under the key that indexes them (`(n,i)`, `i`, `(i,j)`), so a hit
  returns the theorem rather than re-deriving it. **No junk** — `⊢ ∀A⃗ ∀p.
  (p ∈ Sum_n(A⃗) → ⋁ᵢ ∃a. (a ∈ Aᵢ ∧ p = Inj_i(a)))`, degenerating at `n = 0` to
  `⊢ ∀p. ¬(p ∈ Sum_0())` — is the one that is real work: an induction down the
  nest, `sum_cases` at each link, the tail's statement shifted up one injection
  by `p = inr y`, and `¬(p ∈ 0)` at the bottom. It needed two new propositional
  combinators in `lib.rs`, `curry` (the dual of `uncurry`, and the only way out
  of `⊢ H → (X → φ)` when every hypothesis-form rule concludes `⊢ H → φ`) and
  `disj_of`/`disj_inject`, the disjunction mirror of `conj_of`/`conj_proj`.
  It is cached by `n`, and it is **not used by the carrier half** — it is an
  exhaustiveness rule, which is a recursor-side obligation.

  *The telescope's cache key is `(np, β⃗)`, not `n`.* A telescope is
  parameterised by its argument-type *symbols*, so two constructors of the same
  arity over different types must not share one. `Machine::telescope` keys on
  the pair and hands back an `Rc<Telescope>`; `tests/inductive.rs` pins that a
  declaration whose two constructors have identical argument types builds **one**
  `Σ` nest and that the two constructors are still provably distinct, because
  the tags differ even when the summands do not.

  *One term is still a meta-level nest, deliberately.* `rec₊`'s dispatcher —
  the fibre family `B` — is a nest of the `case` symbol, `O(n)` deep. It is not
  a sum or a product, its exported statements are already symbol-level, and the
  carrier it appears in is itself behind a `define_abbrev`, so the exposure is
  `Inductive::closed` and `Fibre`'s own statements and nothing else. Naming it
  `Disp_n(A⃗, T, f⃗)` is the same recipe and is the obvious next application of
  it; it was left out of this pass rather than forgotten.
