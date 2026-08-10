# Deriving `W` as a least fixpoint — an assessment of Kha's gist

*2026-08-09. On the owner's instruction: read
<https://gist.github.com/Kha/cd1fffe73a3ee666fb0adcd401dd7a39> (`LFP.lean`, 398
lines, single file, **no comments**, updated 2026-08-08) and decide whether it
is good enough to be a **third `modelgen` layer** — one that models a simple
inductive out of something more primitive — and separately whether it suggests a
cheaper `W` in `derived/`. Nothing is implemented; nothing is landed except this
document. Everything cited was read in a scratch worktree at `27965df`. Every
number below with a "measured" tag was produced in this session by the command
shown; §8 names what is not measured.*

## Verdict — SUPERSEDED 2026-08-10. Build it.

> **This document's verdict was "No third layer. Do not build it." It was
> right when written and both of its legs have since been cut.** It is
> corrected here rather than below, because a reader who acts on the first
> screen is the reader this matters to.
>
> **Leg one — the circle — broke this week.** The argument was that the
> derivation's irreducible closure contains `List` and `Acc`, so a layer
> modelling every simple inductive as a `W` would model `List` out of `List`.
> Both members are now derived rather than primitive: `Acc` by the graph route
> (`MODELGEN.md` §8.7 — the Church carrier plus `Classical.choice` at the
> recursion's graph), and `List` by the tuple tower (§8.4), which models it
> with every ι rule `Eq.refl` and no axiom. The W arm therefore emits its path
> type as a **bespoke tower per declaration** and its accessibility as arm G's
> construction **inlined**, splicing neither as a primitive — which is what
> breaks the circularity, independently of axioms.
>
> **Leg two — the axiom bill — was answered by a ruling that postdates this
> document.** §2 measures the derivation at `choice`, `em` and `funext` and
> calls that "a genuine widening of `modelgen`'s prelude". The owner has since
> ruled that axiom-freedom is not a goal and the standard axioms may be used
> liberally. And `em` is not an axiom in Lean 4 — `Classical.em` is a theorem,
> Diaconescu from `choice` + `propext` + `funext` — so the true delta against
> what layer 3 already asserts is `propext`, which is a standard axiom on every
> list this repo keeps (`mini/src/convert.rs`'s `is_standard_axiom`).
>
> **Leg three, which this document did not have and is the operative reason.**
> The framing here is a layer that models *every* simple inductive as a W, and
> that framing is dead: layer 3 exists, models 122 of `init-prelude`'s 125 over
> four primitives, and W is **one more arm** for branching recursion. So §3's
> ledger — "layer 3 deletes nothing, `mini` keeps 16,800 lines" — is an
> argument against a layer that no longer exists. The arm's own justification
> is coverage: at the 30M Mathlib prefix, branching and under-a-binder
> recursion is ~39 of 110 remaining declines, and `Lean.ParserDescr` is one of
> the two declarations standing between `init-prelude` and full coverage.
>
> **What survives unchanged and should still be believed:** §1's account of the
> derivation, §2's closure measurement, §4 on ι, §5 on what it does not cover,
> §6 on the `derived/` question (which was always the weaker half of the
> brief), and §7's finding that cost was never the deciding number. Read on
> with the verdict inverted, not the evidence.

**The original verdict, as written on 2026-08-09, follows.**

**No third layer. Do not build it.** The derivation is correct and elegant, but
it does not break the circle, and the reason is measurable rather than
aesthetic: the inductive dependency closure of the generic construction contains
**`List` and `Acc`** — a recursive simple inductive and a recursive,
large-eliminating `Prop` inductive. A layer that modelled *every* simple
inductive as a `W` would have to model `List` out of `List`. Exempting a basis
instead means `mini` keeps every line of the plain-inductive machinery the layer
was supposed to replace (§3), so the layer only adds. That is the opposite shape
from layers 1 and 2, each of which was justified by a whole file `mini` could
delete (`MODELGEN.md` §7: 2117 lines of `nested_ev.rs` gone, 1059 of
`mutual_aux.rs` available).

**On `derived/`: a real but much smaller suggestion than the brief supposes.**
The transferable idea is one line of the gist — take the intersection of closed
subsets *inside a concrete carrier* (`List (Sigma B) → Option A`) rather than
inside an arbitrary bound `u`. That is precisely the cheapening
`derived/src/acc.rs`'s header already names (`acc(A,R) ⊆ A` **by definition**,
so no bound, no `closed`, no ω-tower). It would make W1/W3/`w_rect`
unconditional. But the prize is **not 1,891 lines**: measured, only ~570 of
`bound`'s 1,922 are W-specific, and the ~1,350 remainder is general
universe-closure with live non-W consumers — which the replacement carrier needs
*harder*, not less (§6). Net line saving, honestly estimated: near zero. Net
interface improvement: real.

**Which first: neither.** If the owner wants one thing from this, it is a
four-line note in `wtype.rs`'s header recording that a concrete carrier is a
known alternative to the bound parameter, so the next person to touch that
module does not rediscover it. Rewriting a finished 1,724-line module with 20
dependents to save ~570 lines elsewhere is not a trade this repo should make
now.

**Three things in the brief this refutes**, stated early as asked:

1. **The blow-up is not the deciding number, and it is not large.** The brief
   frames simple inductives as "the overwhelming majority of declarations".
   Measured: the `init-prelude` export is 1,803 declaration records of which
   **127 are inductives** (7.0 %), and across all of `Init` only **19 of 581
   inductives are plain *and recursive*** — the only population a `W` model is
   even meaningful for (§5). Cost was never going to decide this.
2. **`bound` is not 1,891 lines of W cost.** `acc.rs`'s header calls it "the
   module that exists solely to discharge `closed(A,B,u)` at a universe". That
   is true of its *origin* and false of its *content today*: three of its nine
   files are general universe-closure lemmas with live callers in `cumul` and
   `enums` (§6.1).
3. **My own first worry was wrong and I withdraw it.** I expected the
   container/W gap to bite — a constructor field whose type depends on an
   earlier *recursive* field. Measured: Lean rejects such a declaration
   (`(kernel) invalid nested inductive datatype 'Eq', nested inductive datatypes
   parameters cannot contain local variables`), and structurally it cannot
   arise, because forming a type from a `T`-value needs a family over `T` that
   does not exist yet. **Simple non-indexed Lean inductives really are
   containers.** The obstacle is the circle, not expressiveness.

---

## 1. What the derivation is

Three sentences. `W` is built as a set of **partial labelled trees**: a tree is
a function `PTree B := List (Sigma B) → Option A` sending a path to the label at
that node, and `W B := Subtype (Good B)` where `Good` is the **Knaster–Tarski
least fixpoint** of a one-step-unfolding operator, defined impredicatively as
`lfp F x := ∀ S, (∀ y, F S y → S y) → S x`. Induction is immediate from the
fixpoint (`lfp_induct`); **recursion into `Sort v` is not**, and is recovered by
proving the immediate-subtree relation well-founded (`accSubtree`) and running
`Acc.fix` over it. The ι rule `W.recOn (W.mk a f) = ih a f (…)` is then a
**theorem**, proved from `Acc.fix_eq` with the transports discharged by
definitional proof irrelevance.

The two load-bearing definitions, quoted so a reader need not fetch the gist:

```lean
def lfp {α : Type u} (F : (α → Prop) → (α → Prop)) : α → Prop :=
  fun x => ∀ S, (∀ y, F S y → S y) → S x

abbrev PTree (B : A → Type u) := List (Sigma B) → Option A

/-- One unfolding: a root label, children at every position of that label, and no junk under
any other label.  The `∃`/`∧` are impredicatively encoded, so no logical inductive is needed. -/
def Fop (S : PTree B → Prop) (t : PTree B) : Prop :=
  ∀ r : Prop, (∀ a, t List.nil = Option.some a →
    (∀ b : B a, S (t.child ⟨a, b⟩)) →
    (∀ (s : Sigma B) (p), s.fst ≠ a → t (List.cons s p) = Option.none) → r) → r

def Good (t : PTree B) : Prop := lfp Fop t
def W (B : A → Type u) := Subtype (Good (B := B))
```

The gist is careful about its own footprint: `Nonempty`, `Or` and `∃`/`∧` are
Church-encoded so that no logical inductive is pulled in, and `choice`, `em`,
`funext` are axiomatized locally rather than imported so the residual `Init`
dependency is visible.

### Against the thesis

Same family of ideas, **not** the same use. `thesis.txt`'s whole §5 is
"Reduction of inductive types to W-types" (`thesis.txt:153, 1590`), and §5.1
lists `W` among the primitives it *assumes*: after giving `Wx : α. β := µt :
U…. (sup : …)` it says plainly

> All of these could have been defined as inductive types in the sense of
> section 2.6 … **However, we are interested in taking them as primitive in this
> section and deriving general inductive types.**

So the gist is doing the step the thesis declines to do, and the thesis does
**not** rule it out. Three specific relations:

* **`lfp` is already our `W`.** `derived/src/wtype.rs`'s header defines
  `W(A,B,u) := { z ∈ u : ∀S. ((S ⊆ u ∧ closed(A,B,S)) → z ∈ S) }` — the
  intersection of all closed subsets. That *is* Knaster–Tarski. The gist's
  novelty is not the fixpoint; it is the **carrier** (§6).
* **The `Acc` detour is the gist's own, and is a Lean artefact.** The thesis
  reaches for `acc` only in §5.3, for subsingleton eliminators, where it says
  the opposite thing: *"In this case we must abandon W-types entirely, since we
  have to produce a subsingleton family from the start"* (`thesis.txt:1826`).
  The gist needs `Acc` for a different reason — `lfp` lives in `Prop`, and
  `Prop` has no large elimination, so `Acc` is how a `Prop`-level fixpoint buys
  a `Sort v` recursor. **In set theory that reason evaporates**, which is why
  the transferable part of the gist for `derived/` is small (§6).
* **Indexed families are outside it**, in the gist and in the thesis both.
  §5.2's translation is `P x ≃ {s : Wp : A. B p | recW (λ(p : A) _. G p) s x}`
  — a *skeleton* `W` plus a `good` predicate — and even that needs two η rules
  the thesis helps itself to, noting that *"without such η rules we would only
  be able to go as far as indexed W-types, which are more complex"*
  (`thesis.txt:1744`).

---

## 2. What it bottoms out in — measured

Compiled at the pinned toolchain (`leanprover/lean4:v4.29.1`, the version
`modelgen` and `lean4export` are built at) in **0.29 s**, then the dependency
closure of `{W.mk, W.recOn, W.ind, W.recOn_mk}` walked over types *and* values:

```
closure size: 139 constants
INDUCTIVES (14): Bool, Eq, False, HEq, LFP.Acc, LFP.Decidable, LFP.List,
                 LFP.Option, LFP.Sigma, LFP.Subtype, Nat, PProd, PUnit, True
AXIOMS (3):      LFP.choice, LFP.em, LFP.funext
```

Shortest path to each, which separates the construction's real needs from
elaborator boilerplate:

| inductive | shortest path from a root | verdict |
|---|---|---|
| `Eq` | `Eq ← W.recOn_mk` | **irreducible** |
| `LFP.Option` | `← W.recOn_mk` | **irreducible** |
| `LFP.Sigma` | `← W.recOn_mk` | **irreducible** |
| `LFP.Subtype` | `← W.ind` | **irreducible** |
| `LFP.List` | `← W.ind` | **irreducible — and recursive** |
| `LFP.Acc` | `← Acc.fix_eq ← W.recOn_mk` | **irreducible — recursive, `Prop`, large-eliminating** |
| `False` | `← absurd ← W.recOn_mk` | irreducible |
| `LFP.Decidable` | `← byCases_neg ← eta ← W.ind` | avoidable in principle (`em`+`choice` are already there) |
| `HEq` | `← Subtype.ext ← W.ind` | boilerplate (`cases`) |
| `PUnit` | `← Unit ← eta ← W.ind` | boilerplate |
| `Bool`, `True` | `← noConfusion_of_Nat ← Option.someNeNone.match_1 ← …` | boilerplate (matcher) |
| `Nat` | `← Option.ctorIdx ← Option.someNeNone.match_1 ← …` | boilerplate (`ctorIdx`) |
| `PProd` | `← Nat.below ← … ← Option.someNeNone.match_1 ← …` | boilerplate (`brecOn`) |

The six boilerplate entries are matchers, `ctorIdx`, `noConfusion` and `brecOn`,
which a generated model would sidestep by emitting raw recursor applications —
the gist's own header says exactly this. **The seven irreducible entries do not
go away**, and the two that matter are `List` and `Acc`.

The axioms are `choice`, `em`, `funext` and **not** `propext`, **not**
`Quot.sound` — the file's `#print axioms` output, reproduced verbatim from the
compile:

```
'LFP.W.recOn_mk' depends on axioms: [LFP.choice, LFP.em, LFP.funext]
```

That is a genuine widening of `modelgen`'s prelude, which today needs `Eq`,
`Quot`, `Quot.sound` and `funext` *derived, not asserted* (`modelgen/README.md`
§The prelude). `choice` and `em` are new, and every model produced this way
would be `noncomputable`.

---

## 3. Why that does not break the circle

**The literal circularity.** A layer 3 fires on simple inductives. `List` is a
simple inductive. Its model would be `W` over a tag family, built out of
`List (Sigma B) → Option A`. There is no ordering of the output export in which
that typechecks. So a basis must be exempted: at minimum
`{Eq, False, Option, Sigma, Subtype, List, Acc}`.

**And exempting the basis costs everything the layer was for.** `mini` does not
merely *check* declarations; it interprets them into `derived/`'s set theory
along `thesis.txt` §5.2 (class P, indexed) and §5.3 (class S, subsingleton).
Those two translations are implemented across 22 modules —
`class_s.rs 615`, `class_s_ix.rs 536`, `class_p_ix.rs 1025`, `ctor_ix.rs 1432`,
`recursor.rs 727`, `rec_prop.rs 875`, `rec_dep.rs 2746`, `rec_ix_dep.rs 622`,
`rec_ix_prop.rs 489`, `rec_s_ix.rs 489`, `rec_trunc.rs 613`,
`rec_trunc_ix.rs 368`, `iota_dep.rs 836`, `iota_ix_dep.rs 670`,
`iota_model.rs 346`, `minor_ix.rs 895`, `acc.rs 430`, and the five `rec_acc*`
files (3086) — **16,800 lines**, and the seven basis inductives use all of them:
`List`/`Option`/`Sigma`/`Subtype` are class P, `Eq`/`False`/`Acc` are class S.
None of that code gets *simpler* for running on seven declarations instead of
tens of thousands; it is generic, and its genericity is the whole of it.

Set that against the precedent `MODELGEN.md` §7 establishes for what makes a
layer worth having:

> **What would go.** `mini/src/mutual_aux.rs`, **1059 lines**, whole. … The
> nested arc is the precedent — 2117 lines of `nested_ev.rs` deleted whole once
> `mini` learned to recognise what `modelgen` had written.

**Layer 3 deletes nothing.** Its ledger is: `mini` keeps 16,800 lines, gains a
recogniser for the `W` naming convention (the existing analogue,
`nested_splice.rs`, is 792 lines), and interprets a `W` apparatus in
`derived/`'s terms for every inductive in the file instead of the family's own.

**The steel-man, and why it still fails.** Suppose the basis were hard-wired:
`mini` interprets `List` via `derived::wlist`, `Acc` via `derived::acc`, `Eq`
via §5.3, and the generic §5.2 path is deleted. Two things break it. First,
`derived::wlist` is List-as-a-W-type and so keeps `derived::wtype` alive — the
recursion is pushed into `derived/`, not removed. Second, the recogniser must
still, for an arbitrary inductive, build the tag Σ-type `A`, the fibre family
`B`, and thread evidence through an arbitrary motive to the ι theorems — which
is what `ctor_ix.rs`, `class_p_ix.rs`, `rec_dep.rs` and `iota_dep.rs` *are*. The
work moves; it does not shrink. And the ι side, which `MODELGEN.md` identifies
as where the existing layers spend their effort, is untouched by the move.

---

## 4. Does it give ι rules, or only a carrier?

**It gives them, propositionally, and that is the right shape for this repo.**
`W.recOn_mk`, `Ord.rec'_zero`, `Ord.rec'_succ` and `Ord.rec'_lim` are all
proved, and the gist closes with a worked `Ord.depth` showing the three rules
suffice to compute.

They are **not** definitional. Measured:

```lean
example … : W.recOn ih (W.mk a f) = ih a f (fun b => W.recOn ih (f b)) := rfl
-- error: Type mismatch: rfl has type ?m = ?m but is expected to have type
--   W.recOn ih (W.mk a f) = ih a f fun b => W.recOn ih (f b)
```

This is not an objection. `modelgen`'s contract already emits ι rules as
theorems under `T._model.iota_k_j` (`modelgen/README.md`, `MODELGEN.md` §1), and
`mini/src/nested_splice.rs` already recognises them by that name. The gist's
output is the same species.

**Do the proofs survive as terms?** Yes — the gist is heavily tactic-written
(`cases`, `rw`, `refine`, `unfold`, `subst`, `congr 1`, `injection`, `nomatch`),
but it elaborates to ordinary terms and exports cleanly. What that costs is
implementation, not soundness: `modelgen` builds its models as `Expr`s, so a
layer 3 would have to *construct* the term `W.recOn_mk` elaborates to — casts,
matchers, `Acc.fix_eq` and all — in Lean-the-metaprogram rather than write the
tactic script. That is the single largest hidden cost in the proposal and it is
unestimated here.

---

## 5. What it does not cover

`modelgen`'s "simple inductive" — non-mutual, non-nested — includes two shapes
the gist says nothing about.

* **Indexed families.** `W` has no indices. The route is `thesis.txt` §5.2's
  skeleton-plus-`good` (a second construction, on top of this one, with the two
  η rules of `thesis.txt:1744`), and the gist does not attempt it.
* **Subsingleton eliminators.** `thesis.txt:1826`: *"we must abandon W-types
  entirely … we have to use `acc` instead."* Every `Prop` inductive with large
  elimination — including `Eq` and `Acc` themselves — is outside.

Measured over all of `Init` at v4.29.1 (non-internal inductives only):

| | count |
|---|---|
| inductives | 581 |
| indexed | 48 |
| plain (non-indexed, non-mutual) | 533 |
| **plain *and recursive*** | **19** (80 constructors) |
| indexed *and* recursive | 34 |

So the gist's actual target — plain recursive inductives — is **19 of 581**, and
the 34 indexed-recursive ones, which are the hard ones, are out of reach. For
the other 514 plain inductives a `W` model is degenerate: they are structures
and enumerations, `B` is empty at every tag, and the recursor is a projection.

---

## 6. The `derived/` question

**The transferable idea, in one sentence.** `derived`'s `W` carves the
intersection of closed subsets out of a **parameter** `u`, and therefore carries
`closed(A,B,u)` as an antecedent that a whole companion module exists to
discharge; the gist carves it out of a **concrete** carrier `PTree`, for which
closure is provable outright (`good_node`, four lines). That is exactly the
contrast `derived/src/acc.rs`'s header already draws:

> `acc(A,R) ⊆ A` **by definition**, so the set being carved out of is already
> given. Consequently: there is no bound parameter `u` and no `closed(A,B,u)`
> antecedent, hence no `crate::bound`-style companion module, no universe
> hypothesis and no `ω`-tower; every theorem exported here is
> **unconditional** — including the introduction rule, which is the one that
> costs `W` the whole bound apparatus.

The gist says: `W` can have that shape too. `W ⊆ PTree(A,B)` by definition.
W1 (`sup_mem`), W3 (`w_inversion`) and `w_rect` become unconditional, and the
`_at` variants in `bound::rules` stop being needed.

**And the `Acc` half of the gist does not transfer, which is good news.** The
gist needs `Acc` only because `lfp` lands in `Prop` and `Prop` has no large
elimination. Set theory has no `Prop`/`Sort` distinction, so `derived`'s
existing `w_rect` (induction over a formula) is already the recursor. Everything
from `Subtree` to `cast_recOn` — the longest and fiddliest half of the 398 lines
— drops out. What would have to be built is only: **`Seq(X)`**, finite
sequences, which `derived/` does not have (`Seq(X) = ⋃_{n∈ω} fs(finord n, X)`,
from `infinity`, `enums`, `funspace` and Replacement, all present), plus `node`
as a set-function defined by cases on a path (an `isum::Dispatch`, the apparatus
`finset.rs` exists for) and its six small lemmas.

### 6.1 What it would actually save — and the brief's number is wrong

Measured line counts today (`wc -l`, hub file plus its directory):

| module | lines | `acc.rs` header says (2026-08-01) |
|---|---|---|
| `derived/src/wtype*` | 1,724 | — |
| `derived/src/bound*` | 1,922 | 1,891 |
| both | 3,646 | 3,612 |
| `derived/src/acc*` | 1,626 | 1,291 |

The W-specific part of `bound` is **`closure.rs` (184) + `least.rs` (232) +
`rules.rs` (154) ≈ 570 lines** — the files defining `universe_closed`,
`least_universe_closed`, `discharge_closed`, `sup_mem_at`, `w_inversion_at`,
`w_rect_at`. The other six files are general universe-closure facts, and they
have **live non-W callers**:

```
derived/src/enums.rs:145         crate::bound::fibres_in(env, s, ta, &z, &u)
derived/src/cumul/closed.rs:184  crate::bound::funspace_pairs(env, s)?
derived/src/cumul/decl.rs:658    crate::bound::least_universe_subset(
```

— and eight of `cumul`'s files reference `bound` in code, none of them about
W. (`grep -rn 'crate::bound' derived/src` minus doc lines and `bound/` itself:
**24 files**. `cumul/inside.rs` and `funspace.rs` name `bound` only in headers
and are not counted as callers.)

`fibres_in` and `least_universe_subset` live *inside* the two W-specific files
and would have to be lifted out, shrinking the deletable set to roughly **520
lines of 1,922 (27 %)**.

Worse for the trade: the replacement carrier needs `fs(Seq(Σ(A,B)), A ⊎ 1) ∈
Uₙ`, which is `funspace::pi_rule` plus Seq-in-universe — i.e. it consumes
`funspace_mem_universe` (`member.rs`, 363), `funspace_subset_universe`
(`subset.rs`, 280) and `universe_opair` (`opair.rs`, 89) **harder** than the
present W does. The general half of `bound` is not merely unsavable; it becomes
more load-bearing.

Net: ~520 lines retired, an unmeasured `Seq` construction and a `node`
dispatcher built, and a finished module with **24 code dependents** rewritten.
**I do not believe that clears.**

### 6.2 "Do we need `W` less than we thought?"

No — and the gist mildly argues the other way. It shows `W` is *derivable* from
`acc` plus a function-space carrier plus impredicative `Prop`, which is a
statement about Lean's primitives, not about `derived/`'s. In `derived/`, `W`
already exists, its bound is already discharged at `U(c)`
(`bound::least_universe_closed`), and `wlist`/`wnat`/`wrec`/`inductive::carrier`
are all built on it. The gist gives no reason to want fewer W-types; it gives
one reason to want a differently-carved one.

---

## 7. Cost, measured — and why it was never the deciding number

Elaborated and exported at v4.29.1 through `lean4export` (githash `f72c35b3`),
taking `Init.Core` as the baseline so the deltas are marginal bytes in an
already-interned file:

| export | bytes | `def` | `thm` | `inductive` | `axiom` |
|---|---|---|---|---|---|
| `Init.Core` (baseline) | 6,358,020 | 2,535 | 649 | 194 | 7 |
| + generic `W` development (incl. `Nat`) | 6,857,419 | 2,641 | 703 | 203 | 10 |
| + `Ord` instantiation (3 ctors) | 6,913,490 | 2,655 | 713 | 203 | 10 |

* **Generic `W`, spliced once**: +499,399 bytes (488 KiB), **+172
  declarations**. (Nine of those "inductives" are the gist's re-declared
  primitives, which a real layer would take from the export instead.)
* **Per inductive, `Ord` at 3 constructors**: +56,071 bytes (55 KiB), **+24
  declarations** — 14 `def`, 10 `thm`. `Init` averages 1.47 constructors per
  inductive, so ~15 declarations is the realistic unit.

For calibration, `modelgen` today emits **3,170 declarations for 92 models** on
Mathlib (`MODELGEN.md` §6.2) — about 34 per model. Layer 3's unit cost is
*smaller* than the existing layers'.

Extrapolating to the `init-prelude` export (`/tmp/ip-new.ndjson`, 3,805,695
bytes, 1,803 declaration records, **127 inductives**):

* firing on **every** simple inductive: ≈ +3,000 declarations (2.7×) and ≈ +7 MB
  (2.8×);
* firing only where a `W` model means anything — the **recursive** ones, of which
  all of `Init` has 19 — ≈ +450 declarations and ≈ +1 MB, i.e. **negligible**.

Mathlib's inductive count is **not measured here** (§8), so no Mathlib figure is
given. It does not matter: the honest reading is the second row, and it says the
cost is affordable. Layer 3 fails on the circle, not on the bill.

---

## 8. What is not measured

* **Mathlib's inductive count**, and therefore any Mathlib-scale blow-up. The
  5.6 GB export was not run; only `Init` and the `init-prelude` ndjson were
  counted.
* **The cost of building the gist's proof terms in `modelgen`.** The gist is
  tactic-written; `modelgen` constructs `Expr`s. §4 names this as the largest
  hidden cost and does not estimate it.
* **`Seq(X)` in `derived/`**, and the `node` dispatcher — §6 asserts both are
  buildable from present apparatus (`infinity`, `enums`, `funspace`, `isum`,
  `finset`, Replacement) and estimates neither.
* **Whether `mini` could accept `choice` and `em`** in a model's axiom closure.
  §2 records that it would have to; nothing was checked downstream.
* The `acc.rs` header's line counts have drifted since 2026-08-01 (§6.1 table);
  the drift is recorded, not corrected here.
* The gist has **no comments** (GitHub API, `comments: 0`), so no author
  clarification was available beyond the file itself.

## 9. Reproducing the measurements

```bash
T=~/.elan/toolchains/leanprover--lean4---v4.29.1
E=/home/joachim/nanodatg/target/lean4export
curl -sSL https://gist.githubusercontent.com/Kha/cd1fffe73a3ee666fb0adcd401dd7a39/raw/LFP.lean -o LFP.lean
# md5 ebea23ac3ac492daf8c1b1467d28b393, 398 lines
env -u LEAN_PATH LEAN_SYSROOT=$T LEAN_PATH=$T/lib/lean/library:$PWD $T/bin/lean LFP.lean -o LFP.olean
env -u LEAN_PATH LEAN_SYSROOT=$T LEAN_PATH=$E/.lake/build/lib/lean:$PWD PATH=$T/bin:$PATH \
    $E/.lake/build/bin/lean4export LFP > lfp.ndjson
```

The closure walk of §2, the `rfl` probe of §4 and the `Init` census of §5 were
`lean --run` scripts over `importModules`; they are short enough to rewrite from
their stated outputs and are not committed.
