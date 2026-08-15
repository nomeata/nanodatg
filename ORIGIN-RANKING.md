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

### And a second ceiling nobody had named: `Δ` overprices a one-leg construction

`Δ` deletes *the origin's own equation*. Where the checker reaches that origin
through a **composite** — a reduction of the major premise, then the rule at the
result — a construction that closes only one leg cannot assume the origin's
equation; it can assume only its own leg's, and the other leg still has to
derive. The two are not the same number and the gap is large: rank 1 is
**−3 780** on the ι equation and **−2 630** on the numeral equation, a 30 %
haircut, measured (2026-08-15). *Before pricing any tranche, ask which equation
the construction actually concludes and delete that one.* The composite legs are
visible in the code — `reduce_rec`'s `MajorStep` and `reduct::fully_ruled` — so
this is checkable in advance rather than after building.

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

## The largest origin, and why it is **not** the next build

> **Measured and declined, 2026-08-15.** This section recommended the `Nat`
> bridge on −3 780 and named two checks that had to refute it first. Both were
> taken (`MEASUREMENTS.md`, *"The `Nat.ble` tranche, refuted at its own gate"*).
> **Check 1 fails: there is no gate to open** — the numeral step is
> `Rule::Admitted(Admit::NatRed)`, which is by definition a step the backend has
> no rule for, and firing the tree's own `NANODA_NAT_RULED` simulation moves the
> origin 577 → 106 straight onto `nat_reduce` 32 → 503 and costs **+942 gaps**.
> **Check 2 fails**, and on a step recorded as unmeasured: on the one input that
> contains `Nat.ble`'s three clauses, `checker --features tg` gives all three
> **escaping** certificates (16 / 23 / 24 raw-beta atoms), so `ble_transfer`
> would return a conditional equation rather than a theorem. **And the headline
> is 30 % high**: what a numeral construction can price is −2 630, not −3 780,
> with escapes 1 074 → 1 777. **Reachable prize: 0.** The census below is
> correct and is kept; the recommendation it carried is withdrawn, and the
> second-ranked build named at the end of this section is now the first.

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

**The two checks, taken.** −3 780 prices the equations being *true*, not a
construction reaching them, and the gap between the two turned out to be the
whole tranche. Full numbers in `MEASUREMENTS.md`, *"The `Nat.ble` tranche,
refuted at its own gate"*; the answers:

1. **Does `Nat.ble n m` at two literals need `BleClauses` at all, or does it need
   the native `NatClause` routed one level further?** **Neither — there is no
   rule to route.** `try_reduce_nat` (`tc.rs:685`) computes the value by bignum
   and records `Rule::Admitted(Admit::NatRed)`, and `Rule::Admitted` *is* the
   enum's "the backend has no rule for this" case (`reduct.rs:96`); the
   `Certifier` trait has no numeral method at all. `reduce_rec`'s `fully_ruled`
   gate is already correct and `tc.rs:2796–2800` already says it fires on 466
   the moment a numeral rule exists. Fired via the tree's own
   `NANODA_NAT_RULED`: the origin goes 577 → **106** and reappears entire on
   `nat_reduce` 32 → **503**, for **+942 gaps** in relays. The `3eab691` shape
   needs a construction behind the gate; there is none.
2. **`ble_transfer`'s preconditions.** Blocked twice over, and the second one is
   new. The three clauses are not in `init-prelude` (one `Nat.ble` const node in
   3.7 MB, 156 `thm`s, none about `ble`) — and on
   `nat_char_equations.ndjson`, which *does* contain them, `checker --features tg`
   certifies none: `natBleZ` / `natBleSZ` / `natBleSS` escape carrying **16 / 23
   / 24 raw-beta atoms**, the β-domain obligations of `Nat.ble`'s `brecOn` nest.
   `ble_transfer` `mp`s its premises, so its conclusion inherits them and the
   numeral equation comes out conditional. The `eq_cash` seam was never the
   binding cost; **the escape ledger is**, which is where this document already
   puts the terminal wall.

**And the price is −2 630, not −3 780.** The ι deletion assumes the *ι* equation;
a numeral construction can only assume the *numeral* equation, after which the
ι-at-the-`Bool`-constructor leg still has to derive and 106 still do not.
Measured, `NANODA_NAT_RULED=1 NANODA_ASSUME='nat_reduce'`: 10 262 → **7 632**,
escapes 1 074 → **1 777**. Every future quotation of this row should be −2 630.

**The next build, therefore:**

> **Withdrawn, 2026-08-15 — rank 2 is the `np > 0` layer, at every one of its
> 249 sites.** This paragraph recommended
> `iota: the major premise's domain is not this inductive` at **−1 609** on the
> strength of `074_prodRecEqns` being a 10-gap development fixture for it. The
> leverage claim is true and the scoping was wrong: the row is not a tranche of
> its own, it is **wall #1 of the layer question (b) censused and declined**,
> and it is raised at `gen_ty_bridge`'s `np > 0` arm at 249 of 249 firings —
> `np = 1` 185, `np = 2` 52, `np = 3` 12, **`np = 0` zero**, all
> `lhs_eq = false, rhs_eq = true`, i.e. mini's `ind(p⃗)` matches and the
> `⟦T p⃗⟧` is the third spelling. `074`'s single firing is the same thing at
> `Prod.mk`, `np = 2`. Full measurement in "Rank 2, censused" below.
> **Reachable prize of the one-leg construction: 0 of 249 sites.**
> **Second — also withdrawn, 2026-08-15, measured at 12 of 213.**
> This recommended `proj_reduce` at −890 as "an extension rather than a new
> derivation" with "no known structural obstruction". Both halves are false.
> `3eab691` extended no consumer: it added a disjunct to the *readiness
> predicate* `wants_proj_red_iota`, and `proj.subject` is the master switch for
> the whole rule. The obstruction is known and is written in the run's own
> output — **146 of 231 declines name a declaration in the `untranslated:`
> census**, 46 need `Eq.rec`, 27 are the readiness gate over-promising, and the
> 12 that are the `3eab691` shape sit behind `derive_iota`'s `usable`
> (`tg.rs:17025`), which rejects `RecBottom::List`. The projection composition
> itself declines **zero** times. See "`proj_reduce`, censused" below.

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

**And the scheduling answer is no — but the price below is wrong, and the
correction inverts the comparison.** §10.4 measured every one of the three walls
it cleared at `076` = 45, sub-tree 37 — the tranche migrates rather than
shrinking, so **there is no partial credit anywhere in this layer**: the payoff
is 0 until all ten hard sites are done. That part stands and was re-confirmed
independently (see "Rank 2, censused"). What does not stand is the sentence this
paragraph originally ended with, *"and then it is −35, on one file, in the
population that is now 168 of 10 645 gaps … against `init-prelude`'s −3 780 for
a Nat bridge, or −1 609 for rank 2, this layer should not be started"*: **rank 2
IS this layer**, all 249 of its firings being wall #1 at `np > 0`, so the layer's
payoff on the goal population is **−1 609**, or **−1 892** with row 6's
`fire_list` sibling — and the −3 780 it was compared against is worth 0
reachable. The comparison that justified the decline no longer exists.

**The disposition, restated.** Censused, ten hard sites, **no partial credit,
and now the largest reachable prize in the tree**. Decline it if you cannot
commit to all ten; do not decline it on the −35. Cheapest useful act if anyone
touches it anyway: land #4 (one line) and see whether #5 disappears — that is
the only sub-question in the layer with an answer shorter than the whole
tranche. And note that #7's gate is **three** predicates, not one: with the `np`
test set aside, 243 of the 249 goal-population sites still decline on a plain
slot.

## Rank 2, censused: it is the `np > 0` layer, and one leg of it is worth zero

*Measured 2026-08-15 on `joachim/domain-rank2` at master `a10369e`, release
binary `cargo build -p nanoda_lib --features tg,stepcount --release --bin
checker` kept at a path the gates cannot overwrite, `ci/corpus-dir.sh --link`
run first. One temporary census was added inside `fire_dep`, `gen_ty_bridge` and
`derive_iota_core`'s `succ` arm, measured, and **reverted**; `git diff` is empty
and no file under `checker/`, `kernel/`, `derived/` or `modelgen/` is modified.*

### The deletion reproduces, on both populations

| probe | `074_prodRecEqns` | `init-prelude` | escapes |
| --- | ---: | ---: | ---: |
| baseline | 10 | 10 262 | 1 074 |
| `NANODA_ASSUME` on the **short** prefix (deletes rows 2 **and** 6) | **1** | **8 370** | 1 236 |
| `NANODA_ASSUME` on `…at this parameter` alone (row 6) | — | 9 979 | 1 101 |
| row 2 alone, by subtraction | **−9** | **−1 609** | ≈ +135 |

### The row is one site, and that site is `np > 0`

The string is raised at three places — `derive_iota_core`'s `succ` arm
(`tg.rs:17598`) and `gen_ty_bridge`'s two arms (`:19785` at `np == 0`, `:19793`
at `np > 0`). Instrumenting all three:

| site | `074` | `init-prelude` |
| --- | ---: | ---: |
| `derive_iota_core` succ arm | 0 | **0** |
| `gen_ty_bridge`, `np == 0` | 0 | **0** |
| `gen_ty_bridge`, `np > 0` | **1** | **249** |

with `np = 1` 185, `np = 2` 52, `np = 3` 12 over **57 distinct constructors**
(`Decidable.isTrue` 10, `Decidable.isFalse` 7, `Option.some`/`none` 6 each,
`Except.ok`/`error` 6 each, `EStateM.Result.ok`/`error` 6 each, then a long tail
of single-field classes — `Add.mk`, `Monad.mk`, `Inhabited.mk`, … — at 4 apiece).
**Every one of the 249 reports `lhs_eq = false, rhs_eq = true`**: mini's
`ind(p⃗)` is the term the bridge concludes about and `⟦T p⃗⟧` is not, which is
`SEAM-DESIGN.md` §10.2's third spelling and §10.4's **wall #1**, verbatim. `074`
is the same firing at `Prod.mk`, `np = 2`.

**So rank 2 does not sit next to the layer, it is the layer's first wall**, and
the "best fixture-to-goal leverage in the tree" is leverage on an entry ticket.
Ranking A's rank 7 and Ranking B's rank 2 are the same wall as Ranking A's
rank 1 and Ranking B's rank 6; the two label families differ only in which
recogniser raises them (`fire_dep` versus `fire_list`).

### The census inside the rule: the one-leg prize is 0 of 249

`Δ = −1 609` prices the ι equation at those 249 sites being *true*. What wall #1
alone can reach was measured by evaluating, at the moment of the decline, the
gate the site would meet next:

| next gate after wall #1 falls | sites |
| --- | ---: |
| `mini_ctor_spine_bridge` declines — `!dp.gi.param_vars.is_empty()` | **249 of 249** |
| anything else | 0 |

`fire_dep` routes a fielded constructor of an adopted declaration to
`mini_ctor_spine_bridge` (`dp.elim.is_some()` at all 249), whose first act is
`if !dp.gi.param_vars.is_empty() { … }`. **It is the same predicate `gen_ty_nest`
gates carrier adoption on.** A construction that clears wall #1 therefore closes
nothing at all — not "few", zero — and this is checkable in advance because both
gates read the same field.

Removing that predicate from consideration and re-asking gives the size of the
wall behind it:

| `mini_ctor_spine_bridge`, ignoring its `np` gate | sites |
| --- | ---: |
| declines — a **plain** slot (`order` is not all `Slot::Rec`) | **243** |
| admits | **6** |

So the layer's site #7 is not one predicate but three, and 243 of 249 need the
plain-slot and arity generality as well. *Hypothesis, unbuilt and unmeasured:*
the already-general sibling `ctor_spine_bridge` (`tg.rs:19524`) handles arbitrary
`np`, plain slots and any arity, so #7–#10 might be a **reroute** of the
`dp.elim.is_some()` branch rather than the rewrite question (b) priced — but it
needs `Inductive::ctor_bridge`, which the adopted path may not hold, and that
was not checked here.

### Conditionality, and where it does and does not bite

`gen_ty_bridge` at `np > 0` returns the union of the parameters' own assumption
lists as the bridge's `hyps`, which merge into the final `CondEq`. **At all 249
sites every parameter's typing carries a non-empty assumption list**
(`cond-params = np/np`, 249 of 249), so a completed layer delivers the ι
equation *conditionally* at every site.

**That is a haircut, not a second zero, and the distinction matters.** On `074`
conditional derivations close at the judgement boundary — "29 made, 21 accounted
for by a rule, **0 escaped**", 8 closed as the ambient context's own typings. On
`init-prelude` they do not all close: rank 2's own deletion mints ≈ 135 escapes
against 249 acquisitions. The −1 609 is already net of that.

### Not composite-reached

Unlike rank 1, this origin carries no second leg. `reduce_rec` splits the major
premise off only when its reduction is **fully ruled** (`tc.rs:2810`), which is
an empty population today, and reaching `fire_dep` at all requires the major to
already be a constructor application. So `Δ` is not overpriced by the
composite ceiling `ORIGIN-RANKING`'s second-ceiling section names; it is
overpriced by the layer, which is the stronger of the two effects here — the
haircut is 100 %, not 30 %.

### The scheduling consequence, and the one thing question (b) got wrong

Question (b)'s verdict — **ten hard sites, no partial credit, do not start** —
is confirmed and strengthened: rank 2 is inside it, and its first wall is
provably worth zero because the next gate reads the same field.

What question (b) got wrong is the **price**. It declined the layer at **−35 on
one file in a 168-gap population**, against a `Nat` bridge at −3 780. Both of
those numbers have since moved: the `Nat` bridge is worth **0** reachable, and
the layer is worth **−1 609 on the goal population** (rank 2), plus **−283** if
`fire_list`'s sibling wall (row 6) is taken with it — **−1 892, 18 % of
`init-prelude`'s entire gap population**. That is not a −35 tranche on one
export. **The decline stands for any seat that cannot commit to all ten sites;
the layer is now the largest reachable prize in the tree and should be scheduled
as one piece or not at all.**

## `proj_reduce`, censused: the composition is never at fault, and the prize is 12

*Measured 2026-08-15 on `joachim/proj-reduce-rank3` at master `ef29bde`. Full
numbers in `MEASUREMENTS.md`, "`proj_reduce`, refuted inside its own rule".
Two temporary censuses added, measured, and **reverted**; `git diff` is empty.*

The deletion reproduces exactly — 10 262 → **9 372**, escapes 1 074 → 1 127.

**Its three named development fixtures no longer carry it.**
`proj_reduced_carrier` is 13/13 escape ledger, `proj_stuck_subject` 6/6,
`proj_reduced_subject` 2 — zero `proj_reduce` on all three. The goal
population is the only signal this origin has.

**Every decline is at the rule's first four lines.** Of 231 declines of
`derive_projection_computation`, 140 are "the structure head is not a
constructor", 79 "the redex is not a projection", 12 "mini published no
class-(T) package", and **0 anywhere at or past `adopted_const_spine`**.
Tagging each decline with whether a subject leg was offered *and consumed*
gives "offered, consumed, then declined" = **0**: the composition succeeds
every time it is reached with its premises. The origin lives in the **subject
reduction**; `proj_reduce` is the label of the rule that noticed.

### The census inside the rule

| what the site would need built | gaps |
| --- | ---: |
| mini to translate `Lean.ParserDescr`, `Lean.Syntax`, `Lean.Name` | 92 |
| mini to translate the untranslated **structures** (`HAdd`…, `Fin`, `Char`, `String`, `UInt32`, `BitVec`, `ByteArray`) | 54 |
| an ι interpretation for **`Eq.rec`** — K-like **and** indexed (rank 9's origin) | 46 |
| `consume` refused an **admitted** subject certificate — the readiness gate over-promised | 27 |
| a **`List.rec`** readiness arm — the only `3eab691`-shaped site | **12** |
| | **231** |

**146 of 231 (63 %) name a declaration that the same run's own `untranslated:`
line already declines, with mini's reason attached.** Those are the mini
translation frontier, not a `proj_reduce` tranche.

> **Corrected 2026-08-15 by the census below, "The untranslated frontier".
> Naming a declaration on the `untranslated:` list is *co-location*, and this
> row's 63 % is the same figure the whole goal population produces (63.2 %) for
> the same reason.** The matched controls are decisive: `List.brecOn.eq` is
> **translated** and carries 24 `proj_reduce`; `Lean.Name.brecOn.eq` is
> untranslated and carries 37. The tree's own `PROJ_STRUCTS` census agrees —
> of the 152 declines that record the structure projected, **131 are `PProd`**
> (translated, the `brecOn` tower), 6 `PULift` and 2 `Array`, and only
> **13** (`Fin` 7, `Char` 6) project an untranslated structure. `proj_reduce`'s
> reachable share of the translation frontier is **0**, not 146. The sentence
> at the end of "What I would not do" — *"the honest way to price those 146
> gaps is against `untranslated:`"* — is right about the method and wrong about
> the answer: priced against `untranslated:`, they are worth zero too.

### The downstream gate, checked in advance

The rank-2 trap does not repeat in its exact form — `wants_proj_red_subject`
and the consumer's `mini_projection_at` read the same store but are *nested*,
the consumer's test being the stronger. The gate that does bite is one further
down: readying `List.rec` makes `wants_proj_red_iota` promise a certificate
`derive_iota`'s `usable` cannot produce, because it accepts `RecBottom::Nat`,
`Dep`, `IxDep` and closes `_ => false`. **That is measurable in advance and it
is the second time this week the deciding gate was one line of `match`.**

### Conditionality, and a number that is new

`consume` returns `None` only on `TgCert::Admitted`. At **27 of 231** the leg
was offered — readiness predicted the subject's ι would certify — and the
derivation returned an admission. **12 % of this origin's gaps exist because
the readiness gate promised what `iota` could not deliver**, which is
`SEAM-DESIGN.md` §10.5's warning measured on the goal population for the first
time, and is evidence *against* widening that gate.

### Not blocked behind rank 1

Checked, because `authoritative_reduction_ready` refuses on
`Node::One(Rule::Admitted(_))`: **zero** `Admitted(…)` refusals. All 192
firing-level refusals are `Iota: not ready`. This origin does not inherit rank
1's obstruction — it has its own.

### And the 678 in `tg_tutorial`'s ledger is a different programme

`GAP_LEDGER`'s `gap: proj_reduce` 678 is read from `nanoda_bin` — kernel plus
TG backend, **no mini dispatch** — while Ranking B's 213 is the unified
`checker`. The 3× is mini's published class-(T) packages, not modelgen. The
ratchet is one-sided (`<= 678`), so the divergence never surfaced.

## The untranslated frontier, censused: 63 % is co-location, 1 333 is reachable, and it is one chain

*Measured 2026-08-15 on `joachim/untranslated-frontier` at master `d979adb`.
Full numbers in `MEASUREMENTS.md`, "The untranslated frontier, censused". Three
temporary censuses added, measured, and **reverted**; `git diff` is empty. Both
populations quoted: `--nested --no-modelgen` (1 774 declarations, 89
untranslated, **10 262** gaps) and, using the `modelgen` built at the repo root,
`--verbose --mutual --nested --modelgen=…` (1 822, 91, **11 556** gaps).*

**This is the sixth tranche in a row to be declined, and it is the first one
declined for a reason that is not "the construction cannot reach the number".**

### The attribution, and the control that undoes most of it

A per-declaration gap ledger keyed on `TgBackend::seq` reproduces
`origin_report` to the digit (own **1 456**, relay **7 732** = 7 247 + 485; the
residue 10 262 − 9 188 = **1 074** is the escape ledger, which raises no
`note_admit`). **All 384 gap-bearing seqs are named** — every gap in the goal
population is raised inside a `Definition`/`Theorem`/`Opaque`.

| | `--no-modelgen` | modelgen |
| --- | ---: | ---: |
| admit-gaps | 9 188 | 10 339 |
| in a declaration that **is** `X` or `X.*` for an untranslated `X` | **5 380 (58.6 %)** | **6 531 (63.2 %)** |
| untranslated declarations with **zero** gaps in their own family | **41 of 57** | **43 of 59** |

A permutation null makes the enrichment real (200 random 56-subsets of the 188
translated inductives with generated machinery: median **14.6 %**, p95 26.8 %).
**Three matched controls make it a size effect.** `X.ctorElim` normalised by
constructor count and σ gives 1.00–2.00 own/ctor/σ on **both** sides of the
classifier, and the pairs are exact: `Bool` and `Nat` (translated) and
`Lean.Syntax.Preresolved` and `Lean.Macro.Exception` (untranslated) all carry
**28 gaps / 4 own**. On the `brecOn` tower `List.brecOn.go` (translated) and
`Lean.Name.brecOn.go` (untranslated) both carry **36 `eq_cache`**. And **52 of
the 56 untranslated-base `noConfusion` declarations carry zero gaps** — `Fin`,
`Char`, `String`, every machine word, every `H*` and every `Monad*`.

**Rank 1 is the whole of the excess.** 3 303 of its 3 910 sub-tree gaps sit in
untranslated families, and its own head census names `Nat.ble` 466, `Nat.decEq`
46, `OfNat.ofNat` 18, `Nat.decLt` 16, `Nat.beq` 14: **563 of 577 firings are Nat
arithmetic and not one is a `Lean.*` constructor.** The Nat wall, located inside
`Lean.*.ctorElim` bodies.

### Ranking B-U — the untranslated declarations, by gaps downstream

`reachable` counts only origins that fire **exclusively** in untranslated
families and whose reason string *is* "mini published no interpretation".

| untranslated declaration | co-located | **reachable** | obstruction, named at the decline site |
| --- | ---: | ---: | --- |
| `Lean.ParserDescr` | 2 805 | **0** | field `Lean.Name` |
| **`Lean.Syntax`** | 2 561 | **1 307** | `nested model not interpreted`; `_model.0._auxCarrier` declines on field `Lean.SourceInfo` |
| `Lean.Name` | 372 | 0 | field `String` |
| `Lean.SourceInfo` | 305 | 0 | field `Substring.Raw` |
| `Char` | 152 | 0 | field `UInt32` |
| `USize` | 94 | 0 | field `BitVec System.Platform.numBits` |
| `Lean.Macro.Exception` / `Lean.Syntax.Preresolved` | 52 each | 0 | field `Lean.Syntax` / `Lean.Name` |
| `String` | 41 | **26** | field `ByteArray` |
| `UInt8/16/32/64` | 17 each | 0 | field `BitVec 8/16/32/64` |
| `Trans` | 14 | 0 | `type former spine`, 4 σ |
| `BitVec` | 8 | 0 | field `Fin (2^w)` |
| **`Fin`** | **7** | **0** | field `i < n` = `LT.lt.{0} Nat instLTNat #0 #1` — **no interpretation for `Nat.lt`/`Nat.le`**; the run's own `elim Nat.le computed=false oracle=false` |
| the other 43 | 0 | 0 | — |
| **total** | **6 531** | **1 333** | |

**One declaration is 1 307 of the 1 333.**

### `Fin`, answered: it gates everything and it pays nothing

The decline sites name the field, so the chain is fact, not inference:

    Nat.lt / Nat.le → Fin → BitVec → UInt8 → ByteArray (Array UInt8)
      → String → Substring.Raw → Lean.SourceInfo → Lean.Syntax's nested model

with `UInt16/32/64`, `USize`, `Char` off `BitVec`/`UInt32`; `Lean.Name` off
`String`; `Lean.ParserDescr`, `Lean.Syntax.Preresolved` off `Lean.Name`;
`Lean.Macro.*` off `Lean.Syntax`.

**The brief's hypothesis is structurally right and numerically inverted.** `Fin`
does not pay five times — it gates the whole `field type uninterpretable`
family, 24 of the 59 untranslated declarations and all four that carry gaps.
But **the first eight links carry a reachable prize of 0 between them and the
ninth carries 1 307.** No partial credit anywhere in it: the same shape as
question (b)'s layer, one link longer.

### The deletion is −1 162 and **nothing migrates** — the one thing this road has that the last five did not

`NANODA_ASSUME` on the five reachable origins together, modelgen run: 11 556 →
**10 394**, escapes 1 217 → 1 388, ACQUIRED 354. **−1 162 against a `SUBTREE`
of 1 333, 13 % over.** On `--no-modelgen`, `nested inductive` alone reproduces
rank 5 exactly (10 262 → 9 737, **−525**).

**Every other origin row is unchanged**: `major premise is not a constructor`
598 → 598, `domain is not this inductive` 249 → 249, `proj_reduce` 213 → 213,
`eq_cache` 171 → 171, `nat_eq` 44 → 44, `nat_reduce` 32 → 32. The five deleted
rows go to zero and only the relays fall with them. **This is the exact opposite
of rank 1**, whose simulation moved 577 → 106 straight onto `nat_reduce`
32 → 503 for +942. Rule 4's "read the next gate" check comes back empty.

### And rule 3 does not bite in the form that killed rank 1

`NANODA_ASSUME`'s acquisition is `CondEq::new(derived::imp_refl(f), vec![f])`
(`tg.rs:5415–5423`) — it makes the equation an **antecedent**, which is exactly
what the escape ledger charges for. A landed translation publishes mini's ι as
an unconditional `Thm` and mints no antecedent, so **the +171 is the
instrument's artifact and the deletion overstates the take-back**, where for
ranks 1–3 it understated the obstruction. *This is the first road in the census
whose price is not eaten by the escape ledger.*

**The positive control is real, and the risk it was read as carrying was
measured away on 2026-08-15 (`joachim/layer-probe`).** `Nat`, fully translated
with native support, carries **zero** gaps on `Nat.brecOn.go` and
`Nat.brecOn.eq`. `List`, also fully translated, carries 76 + 27 on the same two.
**Translation alone does not certify the generated machinery** — that part
stands. What does not stand is the sentence this paragraph originally ended
with, *"a translated `Lean.Syntax` would still meet `List`'s residue, which is
the `np > 0` layer measured at 0 reachable"*, together with the split quoted for
it (`.go` was given as 36 `eq_cache` + 40 `…at this parameter` and `.eq` as 24
`proj_reduce`; **by the origin mask it is `.go` own 16 = 8 + 8 over four seqs,
and `.eq` own 7 = 6 `proj_reduce` + 1 `beta`**). Only **8 of the 103** are the
layer, and `Nat` and `List` differ in `np`, not in translation: `List` is
`np = 1`, `Nat` is `np = 0`, and **`Lean.Syntax` is `np = 0` at every recursor,
every constructor and every member of its nested model**. The layer's walls are
`np > 0` walls, so a translated `Lean.Syntax` does not meet them. See the probe
section under "Synthesis". The −1 162 is not exposed to this.

### Disposition

**Declined, and for a new reason.** The prize is genuinely reachable — the
construction concludes exactly the equation the deletion assumes, nothing
migrates, and the escape ledger does not take it back. What declines it is the
**shape**: 1 307 of 1 333 sit behind a nine-link chain rooted at an
interpretation for `Nat.lt`/`Nat.le`, whose first eight links are measured at
zero. A seat that cannot commit to the whole chain should not start it.

> **The one caveat this disposition carried is withdrawn, 2026-08-15
> (`joachim/layer-probe`).** It read *"and a seat that can should price the
> `List` residue first, because a translated `Lean.Syntax` inherits it."* It
> does not: `Lean.Syntax` is `np = 0` everywhere and the layer is `np > 0`
> everywhere, `gen_ty_bridge` being **356 admits / 0 declines at `np == 0`**
> against **0 / 249 at `np > 0`**. The residue a translated `Lean.Syntax` should
> actually be priced against is the **indexed** row — its nested model's
> `._model.0._model.aux` is `numIndices = 1` — and `eq_cache`, which
> `List.brecOn.go` and `Lean.Name.brecOn.go` carry at the same rate. Neither is
> this layer.

**The cheapest useful act if anyone touches this anyway** is the root and only
the root: **an interpretation for `Nat.le`** (`elim Nat.le computed=false
oracle=false` in every run of the goal population). It is worth **0 gaps** by
itself and it is the single precondition of all nine links — so it is the one
sub-question here with an answer shorter than the whole tranche, and it should
be taken as a feasibility probe, not as a tranche.

## Construction reachability, per row

`Δ` prices *the equations being true*; a construction has to *derive* them.

| origin | expect a construction to reach `Δ`? |
| --- | --- |
| `major premise is not a constructor` (−3 780) | **No — measured at 0, 2026-08-15.** The route's own ceiling is **−2 630** (the numeral equation, not the ι equation), and nothing reaches it: the numeral step has no backend rule to certify, and `Nat.ble`'s three clauses escape with 16/23/24 raw-beta atoms in the program that owns the ledger, so `ble_transfer` returns a conditional equation. Declined. |
| `…domain is not this inductive` (−1 609) | **No — measured at 0, 2026-08-15.** All 249 firings are `gen_ty_bridge`'s `np > 0` arm, so the row *is* the layer of question (b), and the construction that concludes its equation is the whole layer. The one-leg construction (wall #1, the `gen_ty_nest` carrier adoption) reaches **0 of 249**: the next gate, `mini_ctor_spine_bridge`, tests the same `param_vars.is_empty()` predicate. See "Rank 2, censused". |
| `proj_reduce` (−890) | **No — measured at 12 of 213, 2026-08-15.** Every one of the 231 declines is at the rule's first four lines; the projection composition produces **zero** declines and succeeds whenever it is reached with its premises. 146 of 231 need mini to translate a declaration named in the run's own `untranslated:` census, 46 need `Eq.rec` (rank 9's own origin), 27 are the readiness gate over-promising, and **12** are the `3eab691` shape — behind `derive_iota`'s `usable`, which rejects `RecBottom::List`. See "`proj_reduce`, refuted inside its own rule". |
| `eq_cache` (−511) | Partly. 23 % over; mid-chain at scale. **Not the translation frontier** — `List.brecOn.go` is translated and carries 36 of it, exactly as `Lean.Name.brecOn.go` does. |
| `nested inductive` (−525) | **Yes — the only row in the census where a construction concludes the deleted equation, nothing migrates, and the escape ledger does not take the price back.** It is `Lean.Syntax` at every firing. Declined only on shape: with its four siblings it is −1 162, and 1 307 of that 1 333 sits behind a **nine-link** translation chain rooted at `Nat.lt`/`Nat.le` whose first eight links are measured at **0**. See "The untranslated frontier, censused". |
| the untranslated frontier as a whole (−1 162) | **Co-location, mostly.** 63 % of the goal population's gaps are raised inside an untranslated declaration and **1 333 of them are reachable**; the rest is rank 1's Nat wall and the `brecOn` tower, both of which a matched translated control carries at the same rate. |
| `…at this parameter` (−35 small / −283 goal) | **No on the small population — measured at −1**, `SEAM-DESIGN.md` §10, and behind the ten-wall layer above. The goal population's −283 is the same cause and inherits the same obstruction. |
| `IDEP undischargeable` (−19) | Priced at `INDEXED-DESIGN.md` §8.7; the wall is a constructor typing for an indexed family and `mem_lean`'s protocol **cannot** be met from a use site (task #38). Not reachable as scoped. |
| `nat_eq` (−11 / −62, both LB) | Small on the small populations. On the goal population it is the same family as rank 1 and should be taken with it, not separately. |
| everything under 25 | Not worth a tranche either way. |

Every row that acquires fully raises the escape count as it closes, and on the
goal population that take-back is 800 gaps across the whole census. No number in
this document is net of it.

## What I would not do

* **Start the `fire_dep` `np > 0` layer *in part*.** Ten hard sites, no partial
  credit anywhere. Its first wall is measured at **0 of 249 sites** because the
  next gate reads the same `param_vars.is_empty()` field. What has changed since
  question (b) is the price: the layer is **−1 609** on the goal population
  (Ranking B rank 2 is the layer), not −35 on one export, so the decline is now
  about the commitment and not about the size of the prize. **And the commitment
  is larger than the census says** (2026-08-15, `joachim/layer-probe`): all
  twelve sites are `np`-shaped, and with `np` set aside **243 of the 249** still
  decline on a plain slot or arity, which is a thirteenth piece outside the
  census; the reroute to `ctor_spine_bridge` that would have supplied it is
  unavailable, **249 of 249** having no `gen_ctor_bridges` entry.
* **Buy the layer in order to get `Lean.Syntax`.** Measured and refuted,
  2026-08-15. `Lean.Syntax` is `np = 0` at every recursor, every constructor and
  every member of its nested model; `gen_ty_bridge` is **356 admits / 0 declines
  at `np == 0`** and **0 / 249 at `np > 0`**. The two roads are independent.
* **Take Ranking B rank 2 as a tranche of its own.** It has no separable
  construction; see "Rank 2, censused".
* **Build the `Nat` bridge.** Measured and declined, 2026-08-15 — see the box at
  the head of "The largest origin". Reachable prize 0 against a route ceiling of
  −2 630. The one thing left worth doing with it is *not* a construction:
  `derived::nat::BleClauses` / `ble_transfer` should stay in
  `derived/tests/nat.rs` until something can hand them **unconditional**
  clause theorems, and nothing in the checker can.
* **Treat `nat_char_equations` as the reason to decide anything about `Nat`.**
  It has no numerals. It said the bridge was worth 11 gaps; it was right about
  itself (now 18), and it was right about the corpus for a reason it could not
  see — the goal population's Nat family looks like **−3 961** (rank 1 −3 780,
  `nat_reduce` −119, `nat_eq` −62) and *reaches* none of it. The fixture's
  verdict was right twice and well-founded once.
* **Take `proj_reduce` as a tranche.** Measured and declined, 2026-08-15 —
  reachable prize **12 of 213**, and the projection composition it is named for
  declines zero times. See "`proj_reduce`, censused". Two thirds of the row is
  the mini translation frontier wearing this origin's label; the honest way to
  price those 146 gaps is against `untranslated:`, not against −890.
* **Widen `wants_proj_red_iota` to reach a projection subject.** It is a
  *prediction*, and it already over-promises at 27 of this origin's 231 sites.
  Any new arm needs the matching arm in `derive_iota`'s `usable` first, or it
  trades a projection gap for an ι one — `proj_reduced_carrier` 13 → 169.
* **Price a tranche by which declarations its gaps are raised in.** Measured
  and declined, 2026-08-15. 63 % of `init-prelude`'s gaps are raised inside a
  declaration the same run's `untranslated:` line names, and **1 333 of 10 339
  are reachable**; the rest is rank 1's Nat wall and the `brecOn` tower sitting
  in `Lean.*` bodies. The matched control is the whole argument: a
  2-constructor *translated* `ctorElim` (`Bool`, `Nat`) and a 2-constructor
  *untranslated* one (`Lean.Syntax.Preresolved`, `Lean.Macro.Exception`) both
  carry 28 gaps / 4 own. This retroactively corrects rank 3's 146 of 231.
* **Start the `Fin` chain for the machine words.** `Fin` gates `BitVec`, five
  machine words, `Char`, `ByteArray`, `String`, `Substring.Raw`, `Lean.Name`,
  `Lean.ParserDescr`, `Lean.SourceInfo` and `Lean.Syntax`'s nested model — nine
  links — and **the first eight are worth 0 gaps between them**. `Fin` itself
  is worth 7, all `proof_irrel`; the five machine words 162, all `<multi>` /
  `nat_reduce` / `proj_reduce`. One construction paying seven times, and seven
  of the seven pay nothing.
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

---

## Synthesis after six refutations — the two roads are INDEPENDENT

*Written 2026-08-15 by the coordinator as a reading of the six tranches below,
asserting no new measurement, and headed "the `np == 0` layer is the shared
root". **The probe it asked for was run the same day on `joachim/layer-probe`
and refuted it**; the section is corrected in place, as its own last paragraph
instructed. What it got right, what it got wrong, and the measurement, are
below — see "The probe, run: `Lean.Syntax` is np = 0 at every site".*

| tranche | headline | reachable | why it died |
| --- | ---: | ---: | --- |
| B1 `major premise is not a constructor` | −3 780 | **0** | no backend rule for the numeral step; simulating it costs **+942** |
| B2 `major premise's domain is not this inductive` | −1 609 | **0** | all 249 firings are wall #1 of the `np == 0` layer; next gate reads the same field |
| B3 `proj_reduce` | −890 | **12** | 231 declines, **zero** at or past the composition |
| A1 `076`'s `…at this parameter` | −35 | **−1** | three independent mints of `⟦List⟧` in one binary |
| `077`'s `has_type_lam` | −19 | **0** | needs task #38's bridge, which does not exist |
| the untranslated frontier | 6 531 | **1 333** | 63 % is co-location, proved by a matched control; 1 307 of the rest is `Lean.Syntax` |

**Two roads survive contact with measurement. They do not intersect.**

* The **`np == 0` layer in `fire_dep`** is worth **−1 609** on its own (−1 892 with
  its `fire_list` sibling, 18 % of `init-prelude`). Twelve constructions, ten
  hard, seven previously unknown, **no partial credit** — the sub-tree migrates
  intact across each wall rather than shrinking. **And twelve is a floor**: all
  twelve are `np`-shaped, and 243 of the 249 sites need plain-slot and arity
  generality that no one of them supplies (below).
* **`Lean.Syntax`'s translation** is worth **−1 162**, and it is the only tranche
  measured this week where **nothing migrates**: every other origin row is
  unchanged under the deletion (598→598, 249→249, 213→213), the exact opposite
  of B1's +942. The escape ledger does not take a cut, because a landed
  translation publishes an *unconditional* ι where `NANODA_ASSUME` mints the
  antecedent the ledger charges for.

**The second road was said to run through the first. It does not.** The claim
rested on the frontier seat's residual risk — *`List` is fully translated and
still carries 103 gaps on its `brecOn` tower, so a translated `Lean.Syntax`
inherits the `np > 0` layer* — which was an inference from `List`, never a
measurement of `Lean.Syntax`. **`List` differs from `Lean.Syntax` in exactly the
variable at issue: `List` is `np = 1` and `Lean.Syntax` is `np = 0`, at every
recursor, every constructor and every member of its nested model.** The layer's
walls are `np > 0` walls and cannot gate a declaration that has no parameters.
See the probe section below for the numbers.

**So the layer is one option among two, not the root of both.** It is worth
−1 609 (−1 892 with row 6) and it is a precondition for **none** of the −1 162.
`Lean.Syntax` remains a nine-link chain rooted at `Nat.le` whose **first eight
links are measured at 0** — that is its own shape problem, and it is the reason
that road was declined; but the ninth link does not additionally owe the layer.

**Which inverts the recommendation this section was written to support.** The
two roads are now comparable on their merits rather than nested, and on the
merits the translation is the better bet: it is the only tranche measured this
week where nothing migrates and the escape ledger takes no cut, whereas the
layer is a ten-site commitment whose own census is now known to be **short** of
what −1 609 needs (below). Neither is a small piece of work; the point is that
committing to the layer no longer buys anything on the other road.

### The probe, run: `Lean.Syntax` is np = 0 at every site

*Measured 2026-08-15 on `joachim/layer-probe` at master `7ecef03`, release binary
`cargo build -p nanoda_lib --features tg,stepcount --release --bin checker` kept
at `_tmp/checker-probe` where the gates cannot overwrite it, `ci/corpus-dir.sh
--link` run first. Both populations: `--no-modelgen` (1 774 declarations, **10
262** gaps) and `--modelgen=…` at the repo root (1 822, **11 556**). Four
temporary censuses were added inside `note_admit_m`, `note_declar`,
`gen_ty_bridge`, `fire_dep` and `mini_ctor_spine_bridge`, measured, and
**reverted**; the gap totals were byte-identical with the instrumentation in, and
`git diff` is empty.*

**1. `gen_ty_bridge`, by `np`, admits and declines.** The wall the whole layer
is entered through, censused at its own entry rather than at its declines:

| `np` at the ι site | entries | admits | declines |
| --- | ---: | ---: | ---: |
| **0** | **356** (284 `--no-modelgen`) | **356** | **0** |
| 1 | 185 | 0 | 185 |
| 2 | 52 | 0 | 52 |
| ≥ 3 | 12 | 0 | 12 |

`np` predicts the outcome perfectly and **neither cell is empty** — the `np == 0`
arm is not vacuously green, it is the busiest ι path in the run. That is the
control the "0 at `np == 0`" figure needed: without it, "the layer never fires at
`np == 0`" would have been consistent with `np == 0` never being reached.

**2. Every `Lean.Syntax` gap is raised at an `np = 0` recursor.** The report's own
`NO_NEST` census, which records `r.num_params` at the `derive_iota` decline that
a landed translation would move past — 188 of the 201 firings:

| recursor | `np` | firings (modelgen) |
| --- | ---: | ---: |
| `Lean.Syntax.rec` | **0** | 66 |
| `Lean.Syntax._model.2.rec` | **0** | 36 |
| `Lean.Syntax._model.1.rec` | **0** | 34 |
| `Lean.Syntax.rec_1` | **0** | 22 |
| `Lean.Syntax._model.0._model.aux.rec` | **0** | 14 |
| `Lean.Syntax.rec_2` | **0** | 12 |
| `Lean.Syntax._model.0.rec` | **0** | 4 |
| `Eq.rec` | 2 | 13 |

**3. And the nested model does not smuggle a parameter back in.** `rec_1` and
`rec_2` state their ι rules at `Array.mk` and `List.nil`/`List.cons`, which are
`np = 1` constructors, so the reading that survives step 2 is that mini's model
would meet the layer on the constructor side. It would not: reading `modelgen`'s
own output for this export, **every** member of the model — `Lean.Syntax._model.0`,
`._model.1`, `._model.2`, `._model.0._model.tag`, `._model.0._model.aux` — and
every one of their constructors is `numParams = 0`. The nested model
*specialises the parameter away*; `_model.2` is `List Syntax` as a nullary
declaration with nullary `nil`/`cons`. (`._model.0._model.aux` is `numIndices = 1`,
so a translated `Lean.Syntax` meets the **indexed** row, `INDEXED-DESIGN.md`'s
programme — a different obstruction, not this one.)

**4. Nor do the parameterised declarations in the family carry any of the prize.**
`Lean.Syntax.SepArray` (`np = 1`), `Lean.Syntax.TSepArray` (`np = 2`) and
`Lean.TSyntax` (`np = 1`) are untranslated too, and a per-declaration gap ledger
keyed on `TgBackend::seq` gives them **0 gaps between them**. The 2 561 co-located
and 429 own are `Lean.Syntax` proper.

**5. `Lean.Syntax` owns nothing on either of the layer's rows.** Its 437 own gaps
(429 base + 8 `Preresolved`) split as: `no interpretation` 195 (nested 100,
mutual 74, indexed 14, K-like 7), `major premise is not a constructor` 85,
`eq_cache` 54, `proj_reduce` 36, `pi congruence` 36, `beta` 18, `delta` 11,
`nat_reduce` 2 — and **0** on `…domain is not this inductive` and **0** on
`…at this parameter`. The 62 declarations that own the first row are
`Option.noConfusion` 8, `EStateM.Result.noConfusion` 8, `Decidable.noConfusion` 8,
`Except.noConfusion` 8, `Pow.noConfusion` 4, … — all `np > 0`, none `Lean.*`. The
10 that own the second are `List.noConfusion` 12, `List.brecOn.go` 8,
`List.hasDecEq` 4, `instDecidableEqList` 4, `List.instDecidableNilEq` 4, … — all
`List`, `np = 1`.

### `List`'s 103, re-attributed — and the matched control that reassigns it

The same ledger reproduces the 103 exactly and shows it is mostly not the layer:

| declaration | gaps | seqs | own | own, by origin |
| --- | ---: | ---: | ---: | --- |
| `List.brecOn.go` | 76 | 4 | 16 | `eq_cache` **8**, `…at this parameter` **8** |
| `List.brecOn.eq` | 27 | 2 | 7 | `proj_reduce` **6**, `beta` **1** |

Identical on both populations. **8 of the 103 are the layer**, not the whole of
it; the rest is `eq_cache`, `proj_reduce` and their relays, which are separately
ranked and separately declined.

**The matched control, in the technique that retired the 63 % headline.** Pair
two *translated* declarations of the same shape — recursive, two constructors, a
`brecOn` tower — differing only in `np`:

| declaration | translated | `np` | gaps on `brecOn.go` + `.eq` | of which the layer |
| --- | :-: | ---: | ---: | ---: |
| `Nat` | yes | **0** | **0** | 0 |
| `List` | yes | **1** | **103** | **8** |

`Nat.brecOn.go` is checked and appears in the escape ledger, so its zero is a
measured zero and not an absent declaration. **`List`'s residue is evidence about
`np > 0`, not about translation** — which is precisely the substitution the
synthesis made, and `Lean.Syntax` sits on `Nat`'s side of the split.

### The layer's own census is short of what −1 609 needs

Evaluating, at each of wall #1's 249 declines, the gate the site would meet next
— this time reading `dp` directly rather than by simulation:

| at wall #1's decline | sites |
| --- | ---: |
| declines | **249** |
| `dp.elim.is_some()` — really does route to `mini_ctor_spine_bridge` | **249** |
| would pass that gate's three predicates | **0** |
| blocked by `np` **only** | **6** |
| blocked by `np` **and a plain slot** | **203** |
| blocked by `np`, a plain slot **and** arity > 1 | **40** |

**So the twelve-site census, all of whose sites are `np`-shaped, would leave 243
of 249 still declining.** The plain-slot and arity generality is a thirteenth
piece and is not in the twelve; "ten hard sites" is a floor, not the commitment.

**And the escape hatch rank 2 left open is closed.** That census hypothesised
#7–#10 might be a *reroute* to the already-general `ctor_spine_bridge` rather
than a rewrite, noting it "needs `Inductive::ctor_bridge`, which the adopted path
may not hold, and that was not checked here". Checked here: `ctor_spine_bridge`'s
first requirement is a `gen_ctor_bridges` entry for the constructor, and **249 of
249 have none** — only the general path mints one, and all 249 are on the adopted
path. The reroute is not available; #7–#10 is a rewrite.

**No prefix pays, for a third reason on top of the two already recorded.**
`mini_ctor_spine_bridge` is called **zero** times on either population — every ι
site that would reach it dies at wall #1 first — so sites #7–#10 are unreachable
code until #1 lands, and #1 is worth 0. Sites #4, #5, #6, #11 and #12 are all
inside paths only `np > 0` enters. There is no ordering of the twelve in which an
early one closes a gap.

### The two pre-build checks this week produced, both cheap and both decisive

1. **Read the gate immediately downstream of the one you would open, and check
   it does not test the same predicate.** B2's prize was 0 because it did; B3's
   one buildable arm sat behind a `match` closing `_ => false`. Twice the
   deciding gate was one line, checkable before any work.
2. **Distinguish co-location from causation with a matched control.** The
   frontier seat paired a 2-constructor *translated* `ctorElim` with a
   2-constructor *untranslated* one and got 28 gaps / 4 own from both. That one
   comparison retired a 63 % headline and retroactively corrected B3's
   146-of-231.
