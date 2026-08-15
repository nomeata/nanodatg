# The definitive tranche ordering: all admit-origins, all three populations

Companion to `NAT-CHAR-CENSUS.md`, which censused one fixture. This ranks
**every** admit-origin across every gap-bearing population by measured closure.

*Re-taken in full on **2026-08-15** at master `d73c94f`, in the `recensus`
worktree, `ci/corpus-dir.sh --link` run first. The previous ranking was taken at
`17384f6` over a tree that no longer exists — six of its thirteen rows have
closed, moved, or split, and its headline recommendation is superseded. No row
below is carried forward unmeasured.*

Binary:

```sh
cargo build -p nanoda_lib --features tg,stepcount --release --bin checker
./target/release/checker --no-modelgen --verbose <file>
./target/release/checker --nested --no-modelgen --verbose <init-prelude>
```

`stepcount` remains mandatory: without it `NANODA_ASSUME` is compiled out and
every deletion silently reports the baseline. **Release and debug were
cross-checked and agree to the digit** (`076_listRecReduction` 45 baseline,
10 under rank 1, 4 under `*`, on both). Release is ~20× faster and makes the
full three-population sweep a 15-minute job rather than a five-hour one.

> **New measurement hazard, and it bit this tranche.** Running the verification
> gates *after* building the census binary silently destroys it: `cargo test
> --features tg` rebuilds `target/debug/checker` **without** `stepcount` and
> overwrites the hardlink. The result is a binary that runs, accepts, prints
> gap counts — and ignores `NANODA_ASSUME` completely. This is the third member
> of the family recorded in "Two defects in the measurement machinery" below,
> and the only one that produces a *stale* rather than an absent reading.
> Check that some deletion moves some number before trusting a sweep.

## The three populations

| population | files with gaps | gaps | own | relayed | multi | escaped |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `checker/tests/fixtures/` | 14 | 215 | 16 | 65 | 0 | 134 |
| `vendor/arena-tests/good/tutorial/` | 16 of 91 | 168 | 30 | 113 | 5 | 20 |
| **the two small populations** | **30** | **383** | **46** | **178** | **5** | **154** |
| `vendor/arena-tests/good/init-prelude.ndjson` | 1 | **10 262** | **1 456** | **7 247** | **485** | **1 074** |
| **all three** | **31** | **10 645** | **1 502** | **7 425** | **490** | **1 228** |

Every row sums to its total. The three-category partition from
`NAT-CHAR-CENSUS.md` holds on all three populations: escapes carry no origin bit
and are neither origins nor relays.

**`budget_decline` is excluded**, as it was from the previous census: 2 102 gaps,
one per `succ`, a pathology fixture rather than a certification target
(`MEASUREMENTS.md:10134`).

### Two corrections to the population figures everyone has been quoting

* **The fixture population is 215, not 166.** Fourteen fixtures carry gaps, not
  the eight usually listed. The seven routinely omitted are
  `delta_inside_a_proof` 11, `nested_roundtrip` 11,
  `transport_through_eq_rec` 11, `whnf_of_a_proof` 6,
  `ground_unit_subsingleton` 4, `mono_prefix` 4, `reducible_ctor_binders` 2 —
  **49 gaps, 23 % of the population**, and two of them (`nested_roundtrip`,
  `transport_through_eq_rec`) carry origins nothing else in the tree carries.
  `stuck_recursor_major` has gone 4 → 0 and leaves the population.
* **The small-population total is 383, not 334.** By coincidence that is exactly
  the previous ranking's *fixture-only* figure, which is a good way to get
  confused; the split is now 215 + 168 where it was 383 + 217.

## Ranking A — the two small populations (383 gaps)

Sorted by `SUBTREE`. `Δ` is the **measured** fall in total gaps across both
populations when that origin alone is deleted with `NANODA_ASSUME`.

| # | origin cause | own | relay | SUBTREE | Δ measured | over | acquired | fixtures Δ | exports Δ |
| --: | --- | --: | --: | --: | --: | --: | :-: | --: | --: |
| 1 | `iota: the major premise's domain is not this inductive at this parameter` | 5 | 32 | 37 | **−35** | 5 % | 5/5 | 0 | −35 |
| 2 | `nat_eq` | 9 | 25 | 34 | −11 ⚠ | 68 % | **5/9** | −10 | −1 |
| 3 | `quot` | 6 | 18 | 24 | −18 ⚠ | 25 % | **2/6** | −10 | −8 |
| 4 | `iota: no interpretation — a K-like eliminator` | 3 | 20 | 23 | **−20** | 13 % | 3/3 | −13 | −7 |
| 5 | `iota: IDEP undischargeable — a minor premise has no typing to rest on` | 3 | 19 | 22 | **−19** | 14 % | 3/3 | 0 | −19 |
| 6 | `unit_like` | 5 | 15 | 20 | −15 | 25 % | 5/5 | −6 | −9 |
| 7 | `iota: the major premise's domain is not this inductive` | 1 | 9 | 10 | −9 | 10 % | 1/1 | 0 | −9 |
| 8 | `eta (needs a function-extensionality lemma)` | 2 | 8 | 10 | **0 ✗** | — | **no hook** | 0 | 0 |
| 9 | `nat_reduce` | 2 | 8 | 10 | −8 | 20 % | 2/2 | −8 | 0 |
| 10 | `iota: no interpretation — an indexed family` | 1 | 8 | 9 | −8 | 11 % | 1/1 | 0 | −8 |
| 11 | `iota: no interpretation — several constructors` | 1 | 7 | 8 | −7 | 12 % | 1/1 | 0 | −7 |
| 12 | `pi congruence: one Π of undetermined sort and one decided` | 3 | 4 | 7 | −4 | 43 % | 3/3 | −4 | 0 |
| 13 | `eq_cache` | 3 | 3 | 6 | −4 | 33 % | 3/3 | 0 | −4 |
| 14 | `eta_struct` | 2 | 2 | 4 | −2 | 50 % | 2/2 | 0 | −2 |
| | **total** | **46** | **178** | **224** | | | | | |

⚠ = the deletion is **partial**, so `Δ` is a lower bound.
✗ = the origin has **no deletion hook at all**, so `Δ` is not a measurement.

**Rows 1 and 7 are prefix-nested**: `NANODA_ASSUME` matches by substring, so the
shorter pattern deletes both. They were separated by running the shorter pattern
and reading the per-file split — they live on disjoint files, `076` and `074`,
and the joint −44 is exactly −35 + −9. Anyone re-running this must do the same
or will double-count row 7.

**What changed from the previous ranking.** `iota: no interpretation — an
indexed family` has gone from rank 1 at −117 to rank 10 at −8: the composite
landed (`INDEXED-DESIGN.md` §8.6, −70) and the label's other two causes are now
separate rows (rank 4 `K-like eliminator`, the `Acc.rec` share absorbed).
**`proj_reduce` is gone from both small populations entirely** — it was rank 2
at −74 and is now zero on 383 gaps. Two rows are new: rank 5 (`IDEP
undischargeable`, all of it `077_RBTree.id_spec`) and rank 4, which is the
`iota: K-like eliminator` cause the previous ranking predicted was hiding inside
rank 1 and priced at −20. **That prediction was exactly right**, and it is the
only forecast in the old document that survives re-measurement unchanged.

### Where the small-population origins live

| origin | files |
| --- | --- |
| 1 `…at this parameter` | `076_listRecReduction` (own 5, sub 37) |
| 2 `nat_eq` | `nat_char_equations` (5/29), `098_natLitEq` (4/5) |
| 3 `quot` | `quot_lift_reduction` (2/12), `124_quotLiftReduction` (2/10), `125_quotIndReduction` (2/2) |
| 4 `K-like eliminator` | `delta_inside_a_proof` (1/9), `094_ruleK` (1/8), `transport_through_eq_rec` (1/6) |
| 5 `IDEP undischargeable` | `077_RBTree.id_spec` (3/22) |
| 6 `unit_like` | `103_unitEta2` (2/8), `102_unitEta1` (1/4), `ground_unit_subsingleton` (1/4), `mono_prefix` (1/4) |
| 7 `…is not this inductive` | `074_prodRecEqns` (1/10) |
| 8 `eta funext` | `106_funEta` (1/5), `107_funEtaDep` (1/5) |
| 9 `nat_reduce` | `nat_char_equations` (2/10) |
| 10 `indexed family` | `118_accRecReduction` (1/9) |
| 11 `several constructors` | `116_rtreeRecReduction` (1/8) |
| 12 `pi congruence` | `nested_roundtrip` (3/7) |
| 13 `eq_cache` | `105_structEta` (2/4), `076_listRecReduction` (1/2) |
| 14 `eta_struct` | `105_structEta` (2/4) |

Eleven of fourteen rows are single-file or two-file. **The small populations are
now a long tail**: the largest row is 37 of 383, and the top three together are
95 of 383. There is no dominant tranche left in them.

## Ranking B — `init-prelude`, the real goal population (10 262 gaps)

**Nobody had ever ranked this and it is not a scaled-up version of Ranking A.**
Its top row does not appear in either small population at all, and the two rows
the small populations are built around (`…at this parameter`, `IDEP
undischargeable`) are 6th and absent here.

Measured with `--nested --no-modelgen`; **`modelgen` is not built in this
worktree**, so this run accepts 1 774 declarations against the 1 822 recorded in
`MEASUREMENTS.md:11043` for the modelgen run, with 10 262 gaps against 11 909
and certified prefix 127 against 152. The origin *shape* is what this table is
for and it is not sensitive to that difference; the absolute totals are, and are
quoted here on the flags stated, not on the recorded ones.

| # | origin cause | own | relay | SUBTREE | Δ measured | over | acquired |
| --: | --- | --: | --: | --: | --: | --: | :-: |
| 1 | `iota: the major premise is not a constructor` | 577 | 3 333 | 3 910 | **−3 780** | 3 % | 577/577 |
| 2 | `iota: the major premise's domain is not this inductive` | 249 | 1 495 | 1 744 | **−1 609** | 8 % | 249/249 |
| 3 | `proj_reduce` | 213 | 717 | 930 | **−890** | 4 % | 213/213 |
| 4 | `eq_cache` | 163 | 502 | 665 | **−511** | 23 % | 163/163 |
| 5 | `iota: no interpretation — a nested inductive` | 100 | 493 | 593 | **−525** | 11 % | 100/100 |
| 6 | `iota: the major premise's domain is not this inductive at this parameter` | 46 | 264 | 310 | −283 | 9 % | 46/46 |
| 7 | `nat_eq` | 44 | 200 | 244 | −62 ⚠ | 75 % | **18/44** |
| 8 | `nat_reduce` | 32 | 113 | 145 | −119 | 18 % | 32/32 |
| 9 | `iota: no interpretation — a K-like eliminator` | 6 | 54 | 60 | −54 | 10 % | 6/6 |
| 10 | `iota: the constructor's bridge is not about this spine` | 4 | 22 | 26 | −24 | 8 % | 4/4 |
| 11 | `eta_struct` | 6 | 18 | 24 | −6 | 75 % | 6/6 |
| 12 | `beta: the lambda has no function-graph interpretation` | 8 | 16 | 24 | −23 | 4 % | 8/8 |
| 13 | `proof_irrel` | 3 | 14 | 17 | −14 | 18 % | 3/3 |
| 14 | `pi congruence: two Πs of undetermined sort over differently shaped bodies` | 4 | 3 | 7 | **−3 ‼** | 57 % | 4/4 |
| 15 | `def_eq_proj` | 1 | 3 | 4 | **0 ✗** | — | **no hook** | 
| | **total** | **1 456** | **7 247** | **8 703** | | | |

‼ = **`Δ` is below `own`.** All four origins acquire and the ledger falls by
three, so one acquisition mints an escape that did not exist before. This is the
first row anywhere in the census where closing an origin is *worth less than the
origin's own count*, and it is the clearest single illustration that the escape
ledger takes back part of every win.

Rows 2 and 6 are the same prefix-nesting as Ranking A's 7 and 1, separated the
same way (joint −1 892 = −1 609 + −283).

**`def_eq_proj` is a second unhooked origin**, `crate::certify::Admit::Proj.name()`
raised through `note_admit` at `tg.rs:23073`. Its `Δ = 0` is not a result. The
previous ranking said exactly one unhooked reason string carried gaps; that was
true of the small populations and is false of the goal population.

## Composition, all three populations

`sum ≤ joint ≤ sum + MULTI` holds everywhere, and the `iota:` family composes
**exactly** additively on both populations that have one.

| population | sum of singles | joint (`*`) | MULTI | bound holds |
| --- | --: | --: | --: | :-: |
| small (14 rows) | 160 | **164** | 5 | 160 ≤ 164 ≤ 165 ✓ |
| small, `iota:` only (6 rows) | 98 | **98** | — | exact ✓ |
| `init-prelude` (15 rows) | 7 903 | **8 211** | 485 | 7 903 ≤ 8 211 ≤ 8 388 ✓ |
| `init-prelude`, `iota:` only (6 rows) | 6 275 | **6 315** | 485 | ✓ |

There is still no bundling premium worth capturing: the excess over the sum is
4 % on the goal population and 2.5 % on the small ones, and bundling would lose
per-tranche attribution.

## `SUBTREE` is a ceiling — confirmed a third time, and the band is now tight

Twenty-eight measurable rows across three populations, **`Δ ≤ SUBTREE` without
exception**. The previous ranking's bands were taken on sub-trees of size 4–129
and were correspondingly noisy. On `init-prelude`'s large rows the ceiling is
much tighter than anyone has been budgeting for:

* **large terminal rows (sub-tree ≥ 300): 3–11 % over** — rank 1 3 %,
  `proj_reduce` 4 %, rank 2 8 %, `…at this parameter` 9 %, `nested inductive`
  11 %. The 25–50 % mid-chain band does **not** appear at scale.
* **mid-size rows (sub-tree 17–70): 8–23 %** — `constructor's bridge` 8 %,
  `K-like` 10 %, `proof_irrel` 18 %, `nat_reduce` 18 %, `eq_cache` 23 %.
* **small rows (sub-tree ≤ 10): 20–75 %, and one negative.** Treat anything
  under a sub-tree of ~10 as granularity, not signal.

**The rule to plan on, revised: budget ~5 % under `SUBTREE` for a terminal row
with a sub-tree over 300, ~20 % for one in the tens, and do not plan off
`SUBTREE` at all below ten.** The old blanket "~10 % terminal / ~30 % mid-chain"
was calibrated on the small populations and is pessimistic by 2× on the rows
that now matter.

## Acquire shortfall, per row

`admit_or_acquire` acquires only when `premask == 0 && ta != tb` and
`CondEq::new` succeeds. Measured by re-counting each origin's own row *under its
own deletion*:

| origin | population | own | survives its own deletion | verdict |
| --- | --- | --: | --: | --- |
| `nat_eq` | small | 9 | **4** | −11 is a **lower** bound; ceiling 34 |
| `nat_eq` | `init-prelude` | 44 | **26** | −62 is a **lower** bound; ceiling 244 |
| `quot` | small | 6 | **4** | −18 is a **lower** bound; ceiling 24 |
| `eta (funext)` | small | 2 | **2** | no hook; unmeasured, ceiling 10 |
| `def_eq_proj` | `init-prelude` | 1 | **1** | no hook; unmeasured, ceiling 4 |
| every other row | both | — | 0 | full acquisition, `Δ` is the number |

**`nat_eq` is the only origin that is partial on both populations**, and it is
partial in the same proportion (56 % / 59 % surviving). That is a property of the
rule, not of a fixture.

## Two — now three — defects in the measurement machinery

Neither of the first two is in `checker/` production behaviour; the third is in
the build, not the code. No production code was changed by this tranche.

**1. `NANODA_ASSUME` cannot delete every origin.** `TgBackend::admit_or_acquire`'s
doc comment still claims "any origin can be deleted by name". False: reason
strings raised by calling `note_admit` directly never consult `origin_assume`.
There are now **19** such call sites in `tg.rs` (the previous count of 17 was
taken before two were added), and **two** of them carry gaps —
`eta (needs a function-extensionality lemma)` at `tg.rs:23031` on the small
populations, and `def_eq_proj` at `tg.rs:23073` on `init-prelude`. A zero from an
unhooked origin is indistinguishable from a real absorption unless you look.

**2. The ACQUIRED line disappears when a deletion empties a file's origin set.**
`origin_report()` returns early when `ORIGINS` is empty and the
`equations ACQUIRED` line lives inside the report, so a single-origin file that
fully acquires prints no acquired count. This is why the shortfall table is
computed from surviving own-rows rather than from the printed counter.
`TEST-INVENTORY.md` §6.4 records this as a known, deliberately unfixed
measurement hazard; it is still live and it still costs every census a step.

**3. The gates destroy the census binary.** See the box at the top. New, found
here, and the only one of the three that yields a plausible wrong number rather
than an obviously absent one.

## The floor, and the escape endgame

With every hooked origin deleted:

| | small populations | `init-prelude` | all three |
| --- | --: | --: | --: |
| baseline | 383 | 10 262 | **10 645** |
| floor (`NANODA_ASSUME='*'`) | **219** | **2 051** | **2 270** |
| reduction | 43 % | 80 % | **79 %** |
| of the floor: escapes | 187 (**85 %**) | 1 874 (**91 %**) | **2 061 (91 %)** |
| of the floor: residual relays | 22 | 151 | 173 |
| of the floor: undeletable origins | 10 | 26 | 36 |

**The escape row is still the terminal wall and it is more dominant than the
previous ranking found, not less.** It was 254 of 286 (89 %) on a 600-gap tree;
it is 2 061 of 2 270 (91 %) on a 10 645-gap one. Escapes rise as origins close —
154 → 187 on the small populations, 1 074 → 1 874 on `init-prelude` — because
each acquisition becomes an antecedent the escape ledger then charges for. On
the goal population the escape population **grows by 800 as the origins close**,
which is 75 % growth: the ledger takes back nearly a tenth of the −8 211.

Closing every admit-origin in the tree is worth 10 645 → 2 270. Then the whole
remaining programme is the escape ledger, and its sub-tree is empty by
construction — it is worth exactly its own count and unlocks nothing.

### The shape of the escape population, re-measured

The brief that scoped this tranche said a beta-typing seat had found **ten**
shape-groups needing different constructions, and that the raw-beta category was
priced at **44 gaps tree-wide**. **Neither is in the tree.** `MEASUREMENTS.md`
has no such section; the nearest is a three-group classification dated
2026-07-31, and `CLAUDE-HANDOFF.md:238` says 77 raw-beta obligations, unpriced.
The decomposition was therefore taken fresh, off `crate::escapes::report()`,
which groups by `Prov::group()` — the obligation's shape, ignoring the subject.

| | small populations | `init-prelude` |
| --- | --: | --: |
| escaping certificates | 154 | 1 074 |
| **distinct shape groups** | **23** | **48** |
| carrying **only** raw-beta atoms | 61 (40 %) | 625 (58 %) |
| …of those, carrying only atoms **already concluded elsewhere in the run** | **2** | **1** |
| certificates closable by **any single** shape group (Σ of the `sole` column) | 24 (16 %) | 309 (29 %) |
| largest single group's closable count | 9 | 86 |

**Three findings, and the first one governs the whole programme.**

1. **The escape population does not decompose into tranches.** A certificate
   closes only when *every* atom it carries is discharged. The largest shape
   group on `init-prelude` — `raw beta [a lambda whose typing rule did not apply
   @ something else] (never checked at an application)` — carries **3 182 atoms
   across 245 certificates, and exactly 6 of those certificates carry nothing
   else**. Building that one construction perfectly closes 6 of 1 074 escapes.
   Summed over all 48 groups, single-shape constructions can reach **309 of
   1 074 (29 %)**; the other 71 % need two or more different constructions each
   before a single gap moves. This is the opposite of the ten-groups picture the
   brief inherited, and it is why the escape endgame cannot be scheduled as a
   sequence of tranches with individual numbers.
2. **The "thread it, don't derive it" prize is essentially zero.** Of 625
   `init-prelude` certificates carrying only raw-beta atoms, **one** carries only
   atoms the run already concluded somewhere. A cross-declaration typing store
   is worth 1 gap. This refutes the standing hope that most of the escape
   population is plumbing.
3. **The ambient-local category is not exhausted.** The brief said scope
   provenance had closed it corpus-wide; no such measurement exists, and
   `context local's own typing` is still the **second** largest group on
   `init-prelude` (738 atoms, 344 certificates, 15 closable) and the **largest**
   on the small populations (180 atoms, 43 certificates, 9 closable).

## `nat_char_equations`, re-adjudicated

Asked: is the standing "do not build the `Nat` bridge" verdict still −11 and
still zero theorems? **The price has moved and the verdict has not.**

| | at `b91433b` (152 gaps) | now (61 gaps) |
| --- | --: | --: |
| `nat_eq` alone | −6 | **−10** |
| `nat_reduce` alone | −5 | **−8** |
| both (= `*` on this fixture) | **−11** (7.2 %) | **−18** (30 %) |
| ceiling (`SUBTREE`) | 26 | **39** |
| theorems that certify as a result | 0 | **0** |

The fixture's composition is exactly as the brief states — 22 escapes, 18
`trans`, 7 `congruence`, 6 `pi congruence`, 5 `nat_eq`, 2 `nat_reduce`, 1 `symm`
— and `nat_eq`/`nat_reduce` are now the *only* hooked origins on it, so `*` and
"both" coincide at 43.

**The price is −18, not −11, and as a fraction of the fixture it has gone from
7 % to 30 %** — because `proj_reduce`'s −87 landed at `3eab691` and removed the
denominator, not because the Nat wall moved.

**The "zero additional theorems" half is confirmed directly, by a measurement
the earlier census could not take.** Under `*`, the escape census names every
declaration that still carries an escaping certificate, and **16 of the fixture's
17 theorems are on that list**: `recAddZero`, `recAddSucc`, `natAddZero`,
`natAddSucc`, `natSubZero`, `natSubSucc`, `natMulSucc`, `natPowZero`,
`natPowSucc`, `natBeqZZ`, `natBeqZS`, `natBeqSZ`, `natBeqSS`, `natBleZ`,
`natBleSZ`, `natBleSS`. The seventeenth, `natMulZero`, carries no escaping
certificate **in either state** — so **no theorem changes status between the
baseline and `*`**, which is the claim that matters. Two theorems move the wrong
way: `natPowZero` and `natBeqZZ` appear **only** under `*`, i.e. assuming the Nat
equations true creates escapes on declarations that had none. The `ble`/`beq`
theorems carry 16–25 raw-beta atoms each, the same shape and the same count as
the `sub`/`mul`/`pow` ones, confirming they fail for the identical reason.
`natLits=2`, `maxNatLit=1` — there are still no numerals.

**So the verdict stands on this fixture, and stands for a sharper reason than
before: the fixture's residual wall is now the escape ledger (26 of the
remaining 43), which no Nat construction reaches.** — **but see the next
section, because the fixture is no longer the reason to care about the Nat
bridge, and the conclusion drawn from it corpus-wide is now wrong.**

## The next build: the `Nat` bridge, −3 780, and why the standing decision inverted

**`iota: the major premise is not a constructor` is the largest single origin in
the project: own 577, sub-tree 3 910, measured −3 780 — 37 % of `init-prelude`'s
entire gap population from one origin, with full acquisition and a 3 % ceiling
overshoot.** It is 2.3× the next row in its own ranking and 22× the largest
number in the whole of the previous census (`iota`, all four causes, −168).

The tree already instruments it. Its own census (`NOT_CTOR`, `NOT_CTOR_NAMES`)
says **563 of 577 firings are "a CONSTANT that is not a constructor — it did not
reduce"**, over **7 distinct head constants**. Temporary instrumentation added
here, measured, and reverted spelled the whole major premise rather than only its
head:

| major premise | firings |
| --- | --: |
| `Nat.ble <lit> <lit>` | **466** |
| `Nat.decEq (_.ctorIdx _) <lit>` (four inductives) | 46 |
| `OfNat.ofNat Nat <lit> (instOfNatNat _)` | 18 |
| `Nat.decLt (OfNat.ofNat _ _ _) UInt{8,16,32,64}.size` etc. | 16 |
| `Nat.beq (_.ctorIdx _) (_.ctorIdx _)`, `Nat.beq Nat.zero Nat.zero`, … | 14 |
| `instDecidableEqNat …`, `HAdd.hAdd Nat Nat Nat …` | 3 |
| | **563** |

**All 563 are `Nat` arithmetic or `Nat` decidability, and 466 of them — 83 % of
the origin, 81 % of its own count — are `Nat.ble` applied to two literals.**
Ground. Not symbolic. Exactly the clause
`derived::nat::BleClauses` / `ble_transfer` concludes
(`⊢ app(app(g,a),b) = bleb(t,f,a,b)`, `derived/src/nat/ble_unique.rs:306,330`),
and whose "only callers in the tree are `derived/tests/nat.rs`".

**This inverts `NAT-CHAR-CENSUS.md` §6's standing decision, and the reason it was
wrong is instructive rather than embarrassing.** §6 declined to build the Nat
bridge on a measurement that was correct — 11 gaps and zero theorems on
`nat_char_equations` — taken on a hand-written 44-declaration fixture with
`natLits=2, maxNatLit=1`, i.e. **a fixture with no numerals in it**. Lean's own
prelude is full of them. §6's own reasoning ("build it when something is actually
gated on it; nothing here is") was right; what was missing was that the thing
gated on it had never been measured. This is the second time in a week that a
conclusion true of the fixtures has been false of the reference population, after
`proj_reduce` — which, note, is **rank 3 on `init-prelude` at −890** having been
declared "worth exactly zero on the reference population" when the reference
population was the 91 tutorial exports.

**What the next seat must refute first, because this brief is a hypothesis
too.** −3 780 prices the equations being *true*, not a construction reaching
them. Two specific checks, in this order:

1. **Does `Nat.ble n m` at two literals need `BleClauses` at all, or does it need
   the native `NatClause` routed one level further?** `nat_reduce` ("native
   arithmetic on literals") already exists, fires 32 times, and is worth −119 —
   yet 466 ground `Nat.ble` applications reach ι unreduced. If the native clause
   already decides them and merely fails to hand TG a certificate at the ι site,
   this is a wiring tranche of the `3eab691` shape (one added disjunct in a
   readiness gate, −87 on its fixture) rather than a derivation tranche. **That
   is the cheapest possible outcome and it should be checked before a line is
   written.** `NAT-CHAR-CENSUS.md` §5 is the precedent: the wall was located at
   the rule whose *name* was on the gap, and it was one gate away.
2. **`ble_transfer`'s preconditions.** `NAT-CHAR-CENSUS.md` §3 priced them: a
   `&mut mini::kernel::Checker` over a populated interpretation store, which
   `TgBackend` holds at no site. If check 1 fails and the construction really is
   needed on the TG side, that seam cost is the tranche, and §6's refusal to pay
   it for an 11-gap prize should be re-taken against −3 780. It is exactly the
   "revisit it if a large origin ever turns out to need cashing" clause, and this
   is that origin.

**Second-ranked build, if the Nat row turns out to be blocked:**
`iota: the major premise's domain is not this inductive` at **−1 609** on
`init-prelude` — the same cause as Ranking A's rank 7 (−9 on `074_prodRecEqns`),
which makes `074` a 10-gap development fixture for a 1 609-gap goal-population
tranche. That is the best fixture-to-goal leverage ratio in the tree and nobody
has noticed it. **Third:** `proj_reduce` at −890, whose construction already
landed once (`3eab691`) on `nat_char_equations` and would be an extension rather
than a new derivation.

## Question (b), answered: the `np == 0` layer in `fire_dep` is **twelve** constructions

`SEAM-DESIGN.md` §10.4 left `076_listRecReduction`'s −35 "bounded below by three
walls and above by nothing anyone has measured", and asked for a census before
anyone builds. Taken here, by walking `fire_dep` and its transitive callees and
enumerating every site that assumes the inductive has no parameters:

**12 sites: 10 hard (would decline or be wrong at `np > 0`), 2 latent. Three are
the walls §10.4 named — all three verified still present and unfixed. Seven are
new.**

| # | site | `file:line` | assumption | fix |
| --: | --- | --- | --- | --- |
| 1 † | `gen_ty_nest` | `tg.rs:9545` | `gi.param_vars.is_empty()` gates carrier adoption; `np > 0` mints a third `⟦T⟧` | substantial (~75 lines, prototyped) |
| 2 | `adopt_ty_nest` | `tg.rs:9658` | `self.mk(tn.head_sym?, vec![])` rebuilds the head **nullary** | small |
| 3 | `gen_ind_build` | `tg.rs:9386` | `betas: …map(\|_\| Vec::new())` drops the βⱼ on the adoption branch | small — 8 lines already exist at `:9412` |
| 4 † | `dep_minor_typed` | `tg.rs:18151` | `inst_all(ax, &[])` against mini's `∀p⃗. ⟦cᵢ⟧(p⃗) = …` | **one line** |
| 5 † | `dep_minor_typed` | `tg.rs:18161` | `from != mdom` compares parameter-applied against nullary | small, possibly **zero** once #4 lands |
| 6 | `fire_dep` | `tg.rs:19067` | `np == 0 && fields.is_empty()` gate on the major's own spine equation | one line |
| 7 | `mini_ctor_spine_bridge` | `tg.rs:19372` | explicit `!param_vars.is_empty()` decline — **this is where the 37-gap sub-tree lands once #1 falls** | substantial |
| 8 | `mini_ctor_spine_bridge` | `tg.rs:19379` | arity check compares the whole spine against `fields` alone | part of #7 |
| 9 | `mini_ctor_spine_bridge` | `tg.rs:19404` | transports **every** spine argument along the carrier bridge, parameters included | part of #7 |
| 10 | `mini_ctor_spine_bridge` | `tg.rs:19445,19453` | `ctor_term(…, &[], &ts)` and `ys_c = Vec::new()` hand parameters on as recursive fields | part of #7 |
| 11 ‡ | `fire_dep` | `tg.rs:19178` | `ctor_term` resolves parameters at the *declaration's* variables; `ctor_term_at` exists uncalled at `carrier.rs:510` | one line |
| 12 ‡ | `fire_dep` | `tg.rs:19189` | `minor_ihs` → `minor_subs` → `rec_slot_domains`, same | one line, or nothing |

† = named in `SEAM-DESIGN.md` §10.4. ‡ = latent (inert behind other declines today).

**The verdict this census was asked for: `076`'s −35 sits behind at least ten
walls, not three, and seven of them were unknown when §10.4 recommended the
census.** Six are one-liners or small; the cost is concentrated in two
substantial pieces (#1, and #7–#10 as a single rewrite of
`mini_ctor_spine_bridge` into the parameterised form that its already-general
sibling `ctor_spine_bridge` has). Half of `fire_dep`'s parameterised path needs
nothing at all — `gen_ty_bridge`, `ctor_spine_bridge`, `dep_subst`/`dep_rec_at`,
`carrier_at`, `mini_cod_at_rung`, `dep_minor_typed`'s fieldful walk and
`nest_chain` are already written for arbitrary `np`.

**And the scheduling answer is no.** §10.4 measured every one of the three walls
it cleared at `076` = 45, sub-tree 37 — the tranche migrates rather than
shrinking, so **there is no partial credit anywhere in this layer**: the payoff
is 0 until all ten hard sites are done, and then it is −35, on one file, in the
population that is now 168 of 10 645 gaps. Against `init-prelude`'s −3 780 for a
Nat bridge, or −1 609 for rank 2, **this layer should not be started.** The
correct disposition of §10.4's open question is: censused, ten walls, declined.
Cheapest useful act if anyone touches it anyway: land #4 (one line) and see
whether #5 disappears — that is the only sub-question in the layer with an
answer shorter than the whole tranche.

## Construction reachability, per row

`Δ` prices *the equations being true*; a construction has to *derive* them.

| origin | expect a construction to reach `Δ`? |
| --- | --- |
| `major premise is not a constructor` (−3 780) | **Unknown and it is the whole question.** 83 % is ground `Nat.ble`. If the native clause already decides it, a gate reaches most of `Δ`; if `ble_transfer` is needed on the TG side, the `mini::Checker` seam is the tranche. Check 1 above settles it. |
| `…domain is not this inductive` (−1 609) | Probably. Terminal, 8 % over, full acquisition, and it has a 10-gap fixture (`074_prodRecEqns`) to develop against. |
| `proj_reduce` (−890) | Likely — the construction landed once at `3eab691` and beat its own price (−87 against −74). |
| `eq_cache` (−511) / `nested inductive` (−525) | Partly. 23 % / 11 % over; both mid-chain at scale. |
| `…at this parameter` (−35 small / −283 goal) | **No on the small population — measured at −1**, `SEAM-DESIGN.md` §10, and behind the ten-wall layer above. The goal population's −283 is the same cause and inherits the same obstruction. |
| `IDEP undischargeable` (−19) | Priced at `INDEXED-DESIGN.md` §8.7; the wall is a constructor typing for an indexed family and `mem_lean`'s protocol **cannot** be met from a use site (task #38). Not reachable as scoped. |
| `nat_eq` (−11 / −62, both LB) | Small on the small populations. On the goal population it is the same family as rank 1 and should be taken with it, not separately. |
| everything under 25 | Not worth a tranche either way. |

Every row that acquires fully raises the escape count as it closes, and on the
goal population that take-back is 800 gaps across the whole census. No number in
this document is net of it.

## What I would not do

* **Start the `fire_dep` `np > 0` layer.** Ten walls, no partial credit, −35 on
  one file. Censused and declined; see question (b).
* **Treat `nat_char_equations` as the reason to decide anything about `Nat`.**
  It has no numerals. It said the bridge was worth 11 gaps; it was right about
  itself (now 18) and the same family of origins on the goal population measures
  **−3 961** (rank 1 −3 780, `nat_reduce` −119, `nat_eq` −62).
* **Bundle tranches.** Excess over the sum is 2.5–4 %.
* **Plan anything off the `SUBTREE` column alone**, or off the old 10 %/30 %
  bands — they are 2× pessimistic on the rows that now matter.
* **Trust a `Δ` without its acquire column.** Five of twenty-nine rows are
  partial or unhooked, and one row (`pi congruence: two Πs…`) is *negative*
  against its own count.
* **Spend a seat on `eta (function-extensionality)` or `def_eq_proj`.** Worth
  ≤ 10 and ≤ 4, and pricing either requires touching `checker/`.
* **Read the escape endgame as ten constructions with ten numbers.** It is 48
  shape groups on the goal population and 71 % of its certificates need two or
  more of them before one gap moves.
* **Measure with a binary built before the gates ran.** See defect 3.

## Provenance

Every number above is from mechanisms already in the tree — `origin_report`, the
escape ledger, `crate::escapes::report()`, `NOT_CTOR`/`NOT_CTOR_NAMES`, and
`NANODA_ASSUME` under the existing `stepcount` feature. One temporary
instrumentation line was added inside `derive_iota_core`'s `NOT_CTOR_NAMES` arm
(`tg.rs:~17270`, `lean_sketch` on the major premise rather than `spell` on its
head), measured, and **reverted**; `git diff` is empty and no file under
`checker/`, `kernel/`, `derived/` or `modelgen/` is modified by this tranche.
Gates at the time of writing: `unified_cli` 6/6, `mini_designed` 34/34,
`tg_tutorial` 36/36, `--no-default-features --lib` 251/251,
`cargo check --no-default-features --all-targets` existing warnings only,
`ci/check-boundary.sh` OK. No ratchet moved.
