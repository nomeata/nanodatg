# The definitive tranche ordering: all admit-origins, both populations

Companion to `NAT-CHAR-CENSUS.md`, which censused one fixture. This ranks
**every** admit-origin across both gap-bearing populations by measured closure.

Taken at `17384f6` in the `natchar` worktree, `ci/corpus-dir.sh --link` run
first. Binary:

```sh
cargo build -p nanoda_lib --features tg,stepcount --bin checker
./target/debug/checker --no-modelgen --verbose <file>
```

`stepcount` remains mandatory: without it `NANODA_ASSUME` is compiled out and
every deletion silently reports the baseline.

## The two populations

| population | files with gaps | gaps | own | relayed | multi | escaped |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `checker/tests/fixtures/` | 15 | 383 | 37 | 199 | 13 | 134 |
| `vendor/arena-tests/good/tutorial/` | 17 of 91 | 217 | 30 | 113 | 5 | 69 |
| **both** | **32** | **600** | **67** | **312** | **18** | **203** |

Every row sums to its total. Both populations independently confirm the
three-category partition from `NAT-CHAR-CENSUS.md`: escapes carry no origin bit
and are neither origins nor relays.

## The ranking

Sorted by `SUBTREE`, both populations combined. `Δ` is the **measured** fall in
total gaps when that origin alone is deleted with `NANODA_ASSUME`.

| # | origin cause | own | relay | SUBTREE | Δ measured | over | acquired | fixtures Δ | exports Δ |
| --: | --- | --: | --: | --: | --: | --: | :-: | --: | --: |
| 1 | `iota: no interpretation — an indexed family` | 12 | 117 | 129 | **−117** | 9 % | 12/12 | −83 | −34 |
| 2 | `proj_reduce` | 14 | 71 | 85 | **−74** | 13 % | 14/14 | −74 | **0** |
| 3 | `iota: the major premise's domain is not this inductive at this parameter` | 5 | 32 | 37 | **−35** | 5 % | 5/5 | 0 | −35 |
| 4 | `nat_eq` | 9 | 16 | 25 | −7 ⚠ | — | **5/9** | −6 | −1 |
| 5 | `quot` | 6 | 18 | 24 | −18 ⚠ | — | **2/6** | −10 | −8 |
| 6 | `unit_like` | 5 | 15 | 20 | −15 | 25 % | 5/5 | −6 | −9 |
| 7 | `eq_cache` | 5 | 9 | 14 | −10 | 29 % | 5/5 | −6 | −4 |
| 8 | `iota: the constructor's bridge is not about this spine` | 1 | 9 | 10 | −9 | 10 % | 1/1 | 0 | −9 |
| 9 | `eta (needs a function-extensionality lemma)` | 2 | 8 | 10 | **0 ✗** | — | **no hook** | 0 | 0 |
| 10 | `iota: no interpretation — several constructors` | 1 | 7 | 8 | −7 | 13 % | 1/1 | 0 | −7 |
| 11 | `pi congruence: one Π of undetermined sort and one decided` | 3 | 4 | 7 | −4 | 43 % | 3/3 | −4 | 0 |
| 12 | `nat_reduce` | 2 | 4 | 6 | −5 | 17 % | 2/2 | −5 | 0 |
| 13 | `eta_struct` | 2 | 2 | 4 | −2 | 50 % | 2/2 | 0 | −2 |
| | **total** | **67** | **312** | **379** | | | | | |

⚠ = the deletion is **partial**, so `Δ` is a lower bound (see below).
✗ = the origin has **no deletion hook at all**, so `Δ` is not a measurement.

### `SUBTREE` is a ceiling in every measurable row — confirmed, and the band is wider

Thirteen rows, twelve of them measurable: **`Δ ≤ SUBTREE` without exception.**
The recorded bands (terminal 7–14 %, mid-chain 32–34 %) hold in shape but need
widening at both ends:

* terminal / no-interpretation rows: **5–13 %** over (`major premise's domain`
  5 %, `indexed family` 9 %, `constructor's bridge` 10 %, `several constructors`
  13 %, `proj_reduce` 13 %). The 5 % row sits below the recorded 7 % floor.
* mid-chain rows: **25–50 %** over (`unit_like` 25 %, `eq_cache` 29 %,
  `pi congruence` 43 %, `eta_struct` 50 %).

The high overshoots are all on small populations, where a single relay is a
large fraction of the sub-tree; treat percentages under a sub-tree of ~10 as
granularity, not signal. **The rule to plan on: `SUBTREE` is an upper bound,
never an estimate. Budget ~10 % under it for a terminal origin and ~30 % under
it for a mid-chain one.**

### Acquire shortfall, per row

`admit_or_acquire` acquires only when `premask == 0 && ta != tb` and
`CondEq::new` succeeds. Where it cannot, the origin is admitted as usual and the
deletion under-reports. Measured by re-counting each origin's own row *under its
own deletion*:

| origin | own | survives its own deletion | verdict |
| --- | --: | --: | --- |
| `quot` | 6 | **4** | −18 is a **lower** bound; ceiling 24 |
| `nat_eq` | 9 | **4** | −7 is a **lower** bound; ceiling 25 |
| `eta (function-extensionality)` | 2 | **2** | no hook; unmeasured, ceiling 10 |
| all ten others | — | 0 | full acquisition, `Δ` is the number |

**Do not read a zero or a small `Δ` as "this origin is worth nothing" without
checking this column.** Two of thirteen rows are partial and one is unhooked.

## Two defects in the measurement machinery

Both found by this census; neither is in `checker/` production behaviour, and I
have changed no code.

**1. `NANODA_ASSUME` cannot delete every origin.** `TgBackend::admit_or_acquire`'s
doc comment (`tg.rs:4931-4936`) claims "**any origin can be deleted by name** —
which is what makes the census completable rather than only the origins that
happened to get a hook". That is **false**. Seventeen reason strings are raised
by calling `note_admit` directly rather than going through `admit`, so
`origin_assume` is never consulted for them:

```
tg.rs:4471, 4473, 19771, 19936, 19953, 19963, 19971, 19994,
     20008, 20017, 20044, 20047, 20051, 20072, 20075, 20110, 20113
```

Exactly one of them carries gaps on either population:
`eta (needs a function-extensionality lemma)` at `tg.rs:19994`, own 2, sub-tree
10. Its `Δ = 0` is **not** a result. Anyone extending this table must check
`note_admit` first — a zero from an unhooked origin is indistinguishable from a
zero from a real absorption unless you look.

**2. The ACQUIRED line disappears when a deletion empties a file's origin set.**
`origin_report()` returns `String::new()` early when `ORIGINS` is empty, and the
`equations ACQUIRED rather than reported` line lives inside the report. So a
single-origin file that fully acquires prints **no** acquired count, and a naive
sum reads 0. Measured: `delta_inside_a_proof` goes 11 → 3 gaps with derived
theorems 45 → 54 under `indexed family` deletion, and prints no ACQUIRED line at
all. This is why the shortfall table above is computed from surviving own-rows
rather than from the printed counter.

## Composition of the top groups

The standing arithmetic `sum ≤ joint ≤ sum + MULTI` holds, with `MULTI = 18`
combined.

| deleted together | fixtures | exports | both | Δ | sum of singles |
| --- | --: | --: | --: | --: | --: |
| baseline | 383 | 217 | 600 | — | — |
| all four `iota:` causes | 300 | 132 | 432 | **−168** | 168 (exact) |
| `iota` + `proj_reduce` | 226 | 132 | 358 | **−242** | 242 (exact) |
| `iota` + `proj_reduce` + `quot` | 216 | 124 | 340 | **−260** | 260 (exact) |
| `*` (every hooked origin) | 182 | 104 | 286 | **−314** | 303, +11 |

The top three compose **exactly additively** — no shared relays between them at
all. Superadditivity appears only when everything goes at once (+11, inside the
18-gap `MULTI` bound), so the leverage is in single tranches and there is no
argument for bundling them.

**Scheduling consequence, since the `PProd` tranche is in flight:** `iota` is
worth −168 standalone (600 → 432) and −168 again on top of `proj_reduce`
(526 → 358). Its value is **completely unaffected** by whether `PProd` lands
first, so the two can be scheduled in either order, or in parallel, without
either seat's number moving.

## The floor, and what it says about the whole programme

With every hooked origin deleted, **286 gaps remain** and their composition is
the finding:

| | count |
| --- | --: |
| `undischarged assumption ⟦arg⟧ ∈ ⟦binder domain⟧ survived to the boundary` | **254** |
| residual relays (`trans` 10, `pi congruence` 7, `congruence` 5) | 22 |
| undeletable origins (`quot` 4, `nat_eq` 4, `eta funext` 2) | 10 |

**89 % of the floor is the escape row.** It rises from 203 to 254 as origins are
deleted, because each acquisition becomes an antecedent the escape ledger then
charges for. So:

* closing every admit-origin in the tree takes 600 → 286, a **52 %** reduction;
* the escape row is the terminal wall for the entire corpus, and its sub-tree is
  empty by construction — it is worth exactly its own count and unlocks nothing;
* it cannot be deferred forever, but it also cannot be *reached* by any origin
  tranche. It is a separate programme of work: discharging conditional
  certificates at declaration boundaries.

## Answering the `iota:` question directly

**The four `iota:` causes are not terminal in the ledger sense — they carry
relays heavily, and as a group they are the largest thing in the tree.**

| | own | relay | SUBTREE | Δ measured |
| --- | --: | --: | --: | --: |
| all four `iota:` causes | 19 | 165 | 184 | **−168** |
| `proj_reduce`, for comparison | 14 | 71 | 85 | −74 |

`iota` is **2.3×** `proj_reduce` combined, and the gap is far wider on the
population that matters:

| | fixtures (383) | exports (217) | both (600) |
| --- | --: | --: | --: |
| `iota` (all four) | −83 (22 %) | **−85 (39 %)** | −168 (28 %) |
| `proj_reduce` | −74 (19 %) | **0 (0 %)** | −74 (12 %) |

### The correction this forces

**`proj_reduce` is worth exactly zero on the reference population.** It occurs on
one file in the entire tree — `nat_char_equations`, which is our own
hand-written development fixture — and on none of the 91 Lean exports. The
`PProd` tranche now in flight is real work and my recommendation for it stands
*for that fixture*, but it should be understood as unblocking a development
signal, not as moving the reference measurement. I did not know this when I
recommended it; the fixture-only census could not have shown it, and this is the
correction I owe on my earlier note.

**The next tranche after `PProd` should be `iota: no interpretation — an indexed
family`** (rank 1, −117 combined, −34 on exports), and the one after it
`iota: the major premise's domain is not this inductive at this parameter`
(rank 3, −35, **all of it on exports**, all of it on one file,
`076_listRecReduction`). Together with the two small iota rows that is −168.

Where the iota origins live:

| cause | file | own | sub-tree |
| --- | --- | --: | --: |
| indexed family | `mutual_aux_encoding` | 3 | 50 |
| indexed family | `ctor_abbrev_major` | 2 | 25 |
| indexed family | `077_RBTree.id_spec` | 3 | 22 |
| indexed family | `118_accRecReduction` | 1 | 9 |
| indexed family | `delta_inside_a_proof` | 1 | 9 |
| indexed family | `094_ruleK` | 1 | 8 |
| indexed family | `transport_through_eq_rec` | 1 | 6 |
| major premise's domain | `076_listRecReduction` | 5 | 37 |
| constructor's bridge | `074_prodRecEqns` | 1 | 10 |
| several constructors | `116_rtreeRecReduction` | 1 | 8 |

The leverage ratio is the highest in the tree: `mutual_aux_encoding` carries
**50 gaps on 3 origins**, ~17 gaps per origin.

The whole iota population sits on **six distinct recursors**, 13 firings —
`Aux.rec` 3, `RBTree.rec` 3, `Eq.rec` 3, `Ix.rec` 2, `RTree.rec` 1, `Acc.rec` 1.
That is a bounded, enumerable target, not an open family.

## Pure absorption: none found

Asked: is any origin large and moving the ledger by zero because another row
takes its declines the instant it stops? **No — not among the twelve hooked
origins.** Every one moves the ledger by at least its own count, and eleven of
twelve move it by strictly more:

* the only zero-mover is `eta (function-extensionality)`, and that is the
  **missing hook**, not absorption. It is untested, not refuted;
* the closest thing to absorption is `eta_struct`, whose `Δ` equals its own count
  exactly (2), so both of its predicted relays failed to vanish;
* `nat_eq` has `Δ = 7` against `own = 9`, but only 5 of the 9 acquire, so it is a
  shortfall row, not an absorption row.

To test the one open case, `note_admit` at `tg.rs:19994` would have to be routed
through `admit` as the other origins are. That is a one-line change to
production code in `checker/`, which this tranche is not permitted to make, and
it is worth at most 10 gaps — I would not spend a seat on it.

## Construction reachability, per row

The distinction the project keeps paying for skipping: `Δ` prices *the equations
being true*; a construction has to *derive* them, and may not reach the same
number.

| origin | expect a construction to reach `Δ`? |
| --- | --- |
| `indexed family` (−117) | **See the sized note below** — the derivation may largely exist. |
| `proj_reduce` (−74) | Likely yes on its own fixture; already in flight. |
| `major premise's domain` (−35) | Probably. Terminal, 5 % overshoot, one file, one recursor shape. |
| `constructor's bridge` / `several ctors` (−9 / −7) | Probably; both terminal, single-file, single-recursor. |
| `unit_like` / `eq_cache` (−15 / −10) | **Partly.** Both mid-chain (25–29 % over), so the derivation runs on into the next wall rather than ending the conversion. Expect noticeably under `Δ`. |
| `quot` (−18, LB) | Unknown — two thirds of it does not acquire, so it is not yet priced. |
| `nat_eq` / `nat_reduce` (−7 LB / −5) | Small, and `NAT-CHAR-CENSUS.md` §6 already argues against building them now. |
| `pi congruence` / `eta_struct` (−4 / −2) | Not worth a tranche either way. |

Every row that acquires fully raises the escape count as it closes, so each of
these numbers is additionally subject to the escape ledger taking back part of
the win. That is the one respect in which all thirteen rows are alike, and it is
why the escape programme is not optional.

## What I would not do

* **Bundle tranches.** The top three compose exactly additively; there is no
  bundling premium to capture and bundling would lose the per-tranche
  attribution.
* **Plan anything off the `SUBTREE` column alone.** It is a ceiling in all twelve
  measurable rows, over by 5–50 %.
* **Trust a `Δ` without its acquire column.** Three of thirteen rows are partial
  or unhooked.
* **Spend a seat on `eta (function-extensionality)`.** Worth ≤ 10, and pricing it
  at all requires touching `checker/`.
* **Treat `proj_reduce` as a reference-population win.** It is zero there.
