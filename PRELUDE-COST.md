# What `init-prelude` costs, and what is behind `Nat`

*2026-08-09. A measurement study; it changes no behaviour and lands no fix. The
question it was set: **when `Nat` stops dominating, what does?** — asked while a
seat landed the `Nat` clause, so that the next lever would be known rather than
discovered. That seat's own re-measurement, `NAT-REPRESENTATION.md` §1.3.4,
arrived mid-study and reports **the wall unmoved**: 21.71 T against 20.85 T,
`SIGABRT` inside the same declaration. This document says why, in numbers, and
says which lever moves it and which does not.*

*Provenance. **Which binary**: `origin/master` at `1e817c5` — the `Nat` clause
in — `release` profile, instrumented by `scripts/prelude-cost-probe.diff` (a
counting global allocator, a per-declaration memory trace, `MINI_STOP_AFTER`, a
teardown attribution pass, `MINI_PARTS_RESET`, a per-declaration acceptance
trace). The probe is **behaviour-neutral and costs a measured +7.6 % to +8.1 %
in instructions** (§7). Where a figure predates `1e817c5` it says so and gives
the `f9bc1db` pair beside it. **Which workload**: the `Nat`-filtered residue,
`scripts/nat-reach.py --write` over `vendor/arena-tests/good/init-prelude.ndjson`
— 1 248 declaration lines, 1 245 mini declarations — and two backward closures
cut out of it with `scripts/decl-closure.py`. All runs `perf stat -e
instructions`, each under its own `ulimit -v`. Wall clocks are commentary: the
machine carried up to five other seats, `anon` between 9.3 and 24.9 GB.*

## Verdict

**On the prefix that has ever been measured, `Nat` is 98.8 % of the
conversions — so "what dominates once `Nat` is dealt with" cannot be answered
from that prefix at all. It has to be answered by cutting declarations out of
the file and running them alone, and when you do, three declarations no run has
ever reached are each in `Nat.modCoreGo_lt`'s class or above** (§4):

| declaration | residue idx | measured, in its own closure |
| --- | ---: | --- |
| **`List.get.match_1`** | 555 | **11.00 T instructions and 8 GB — and it did not finish** |
| **`BitVec.decEq._proof_1`** | 464 | **5 545 459 conversions, +1.39 GB** |
| **`BitVec.noConfusion`** | 466 | **4 638 228 conversions, +0.76 GB** |
| *(for scale)* `Nat.modCoreGo_lt` | 229 | 12.43 M conversions — the one that kills the file |
| *(for scale)* the whole recorded run | — | 21.71 T, 10 GB, dies at declaration 232 |

`List.get.match_1` alone is **at least half the entire recorded `init-prelude`
run**, and that is a lower bound. All three were ranked 1–3 among the unreached
by an acceptance-cost proxy *before* any of them was run (§4.1).

**And the accelerated operations — `NAT-REPRESENTATION.md` §7's step 4, the
outstanding half of the `Nat` work — cannot move this wall, because there is
nothing for them to fire on.** Over the *entire backward dependency closure* of
each hot declaration, every numeral in existence is `0` or `1`:

| closure of | declarations in it | `natVal` nodes | distinct values |
| --- | ---: | ---: | --- |
| `Nat.modCoreGo_lt` | 174 | 50 | **`0`, `1`** |
| `Nat.modCore_lt` | 180 | 56 | **`0`, `1`** |
| `Nat.mod_lt` | 196 | 65 | **`0`, `1`** |
| `Nat.ble_eq_true_of_le` | 69 | 8 | **`0`, `1`** |
| `List.get.match_1` | 76 | 6 | **`0`, `1`** |

`init-prelude`'s arithmetic *proofs* are universally quantified: what runs
inside them is `Nat.rec` / `Nat.casesOn` / `noConfusion_of_Nat` against
`Nat.succ` chains that are **symbolic**, never numeric, and 77.6 % of the
conversions are `whnf` reduction legs rather than def-eq decisions (§2.3). §1.3.4
already attributes the null result to the residue having had its literals
deleted; **this is the stronger statement, and it survives on the unfiltered
file too** — a literal-pair rule has no literal pair to match in any of these
closures. The lever that moves this wall makes *symbolic* `Nat.rec` reduction
cheaper, or makes the proofs need fewer of them. Step 4 is neither.

**Three further results, each measured here.**

* **The acceptance pass is not the cost, and now there is a number.** Parsing
  the residue and running `kernel::add` over all 1 245 declarations is
  **285 017 328 220 instructions and a 31.4 MB peak heap** — **1.3 %** of
  §1.3.4's 21.71 T and 0.3 % of its 10 GB (§1). The interpretation pass is
  98.7 % of the run.
* **The 10 GB is not the certificates, not the frame memo and not the parsed
  export. It is one hint table.** `Interp::parts` — `derived::skeleton`'s
  `HashMap<Term, (FnSym, Vec<Term>)>`, which remembers the applicative structure
  of every term ever built through `Interp::mk` and is never pruned — is
  **54.4 % of the live heap** and holds **80 % of the live kernel `Term` nodes**.
  Certificate structure retained by `Interp::consts` is **0.5 %**. At most
  **24 %** of the table's entries are ever read (§3). **It is gone**: the value
  it stored was the key's own contents, and a six-line reader on `kernel::Term`
  replaces it outright — peak RSS **−81.1 %** on the corpus and **−95.6 %** on a
  closure, output byte-identical, `gapped 0` (§3.4).
* **The memory is accumulation, and it tracks the conversions at ~241 bytes
  each.** The per-pair `Checker` — `frames` and `wt_memo`, what a "transient
  peak" reading would blame — never holds more than 35 frame entries and frees
  at most 11.6 MB when dropped, against 1.88 GB live (§3.1). So the brief's
  alternative, "the 10 GB has nothing to do with the conversions", is refuted:
  it is the same story, through `parts`.

**What that means for the goal — "the checker handles `init-prelude` at
reasonable time and memory costs".** Time and memory are two different problems
with two different owners. Time is `Nat.rec` on symbolic successors, and step 4
does not address it. Memory was `parts`, and it was *independent of `Nat`*: at
241 B/conversion, any 30 M-conversion run needed ~7 GB and any 100 M run ~24 GB,
whatever the conversions were about. It was the one lever here that paid off no
matter how the `Nat` question is settled, and **it has been pulled** (§3.4).
What is left of the memory half is bounded by the parsed export and the arena,
which are flat at 32 MB; **the binding constraint on `init-prelude` is now time
alone.**

**Best estimate of what `init-prelude` costs with `Nat` genuinely solved —
flagged as an estimate, and as a floor.** Projecting the measured
interpretation-to-acceptance ratio onto the 1 015 unreached declarations gives
**≈23 T instructions and ≈6.8 GB** for them — today's whole run again. But the
one top-ranked declaration since measured, `List.get.match_1`, came in at
**≥11.00 T against a 3.95 T prediction**, so the projection under-prices its own
tail by at least 2.8× and the ranking is the trustworthy half (§5). The honest
summary is that **no one has yet demonstrated a memory budget at which the
residue completes**, and this study did not find one.

## 1. The two passes, separated

`--acceptance-only` does not skip the interpretation pass — it only changes the
exit code — so the two had never been priced apart. `MINI_STOP_AFTER=0` (probe)
runs load, `kernel::add` over every declaration and the schedule, then stops
before `Ledger::run`'s first row:

| the acceptance axis, all 1 245 declarations | |
| --- | ---: |
| instructions | **285 017 328 220** |
| task-clock | 22.8 s |
| peak live heap (counting allocator) | **31 376 256 B** |
| RSS | 35 749 888 B |
| frame-cache hits / calls | 18 229 899 / 89 792 055 = **20.3 %** |

Against §1.3.4's 21.71 T and 10 GB that is **1.3 % of the instructions and
0.3 % of the memory**. Everything below is the interpretation pass.

## 2. The conversions, by declaration

`MINI_STOP_AFTER=231` under `ulimit -v` 4 GB. It ended the way a capped run
should — an allocator failure **inside declaration 229** — having completed 229
of them. **Run on both trees**, and they agree: the per-declaration table in
§2.1 is *identical to the digit* on `f9bc1db` and `1e817c5`, and the 229-row
total differs by 375 conversions in 7.8 million, −0.005 %.

| | `f9bc1db` | `1e817c5` |
| --- | ---: | ---: |
| declarations completed | 229 (indices 0–228) | 229 |
| conversions there, `proved` | 7 809 091 | **7 808 716** |
| `gapped`, throughout | 0 | **0** |
| instructions | 6 772 129 718 234 | **6 709 282 749 599** |
| task-clock | 907 s | 896 s |
| live heap at that point | 1 883 509 983 B | **1 840 729 490 B** |
| how it ended | allocator failure at the 4 GB cap, inside `Nat.modCoreGo_lt` | same |

**7 808 716 is `NAT-REPRESENTATION.md` §1.3.4's own figure for row 229 with the
`Nat` clause in, to the digit** — an independent reproduction of that table on a
different cap (4 GB against 10 GB) and a different binary (probed against
clean). Where a figure below carries only the `f9bc1db` value it is because the
two trees produce the same one.

**Note the sign.** Over declarations 0–228 the `Nat` clause is 0.9 % *cheaper*
(6.709 T against 6.772 T) and 2.3 % smaller in heap. §1.3.4's +4.2 % over the
whole 231 is therefore concentrated in declarations 229–231, the `Nat.mod*`
cluster, and is not a flat per-declaration tax.

**This run reproduces `1ba1220`'s off-by-one independently and by a different
route.** That commit corrects `MINI-HANDOFF.md` §43's "`Nat.modCore_lt` alone
takes conversions from 7.8 M to 20.2 M" to `Nat.modCoreGo_lt`'s 12.43 M, with
`Nat.modCore_lt`'s own 10.10 M next. Here the declaration *index* is read off a
separate per-declaration acceptance trace over all 1 245 declarations — 229
`Nat.modCoreGo_lt`, 230 `Nat.modCore_lt`, 231 `Nat.mod_lt`, 232
`Fin.Internal.ofNat` — and the ladder's own last completed row is 7 809 091 at
index 229. 7 809 091 + 12.43 M + 10.10 M = 30.34 M, which is the recorded figure
at index 231. The two derivations agree to the digit.

### 2.1 The ten that pay for it

Percentages are of the 7 809 091 the ladder measured, and of the 30 347 733 at
declaration 231.

| idx | declaration | conversions | of 7.81 M | of 30.3 M |
| ---: | --- | ---: | ---: | ---: |
| 133 | `_private.…0.Nat.le_of_ble_eq_true.match_1_1` | 1 259 748 | 16.1 % | 4.15 % |
| 153 | `_private.…0.Nat.ble_succ_eq_true.match_1_1` | 1 259 748 | 16.1 % | 4.15 % |
| 155 | `Nat.ble_eq_true_of_le` | 1 113 995 | 14.3 % | 3.67 % |
| 154 | `Nat.ble_succ_eq_true` | 633 435 | 8.1 % | 2.09 % |
| 148 | `Nat.le_of_ble_eq_true` | 498 134 | 6.4 % | 1.64 % |
| 177 | `_private.…0.Nat.le_trans.match_1_6` | 495 973 | 6.4 % | 1.63 % |
| 199 | `Nat.sub_lt` | 431 110 | 5.5 % | 1.42 % |
| 140 | `_private.…0.Nat.succ_le_succ.match_1_4` | 253 984 | 3.3 % | 0.84 % |
| 150 | `_private.…0.Nat.ble_eq_true_of_le.match_1_4` | 253 984 | 3.3 % | 0.84 % |
| 129 | `_private.…0.noConfusion_of_Nat.aux` | 191 906 | 2.5 % | 0.63 % |

**Two pairs have identical counts to the digit** — 1 259 748 twice
(`Nat.le_of_ble_eq_true.match_1_1`, `Nat.ble_succ_eq_true.match_1_1`) and
253 984 twice (`Nat.succ_le_succ.match_1_4`, `Nat.ble_eq_true_of_le.match_1_4`).
Equal to the unit over a million conversions is not coincidence: these are
Lean's generated `match_` auxiliaries, and the two of a pair are the *same
matcher shape* over the same scrutinee. The work is a function of the shape and
not of the theorem it serves.

### 2.2 The `Nat` split

A declaration counts as `Nat`-attributable if its **logical** name — the
`_private.Init.Prelude.0.` prefix stripped — is `Nat`, is under `Nat.`, or
contains `of_Nat`. Without the stripping the `_private` namespace looks like a
separate 48.9 % cost centre, which it is not.

| over the 229 completed declarations | declarations | conversions | allocations | live-heap growth |
| --- | ---: | ---: | ---: | ---: |
| `Nat`-attributable | 90 | **7 432 009 (95.2 %)** | 96.9 % | 94.5 % |
| everything else | 139 | **377 082 (4.8 %)** | 3.1 % | 5.5 % |

Declarations 229 and 230 take the count from 7 809 091 to 30 347 733 and both
are `Nat`, so over the whole 231-declaration prefix:

> **`Nat` is 29 970 651 of 30 347 733 conversions — 98.76 %. Non-`Nat` is
> 377 082 — 1.24 %.**

The largest non-`Nat` declaration in the entire prefix is
`EStateM.Backtrackable.noConfusion` at 50 179 conversions — **0.17 %** — with
`Pow.noConfusion` (43 912), `Fin.noConfusion` (34 209), `BitVec.toNat` (34 069)
and `eq_of_heq` (29 890) behind it. **On this prefix there is no second cost
centre at all**, which is why §4 has to leave the prefix to find one.

### 2.3 Which kinds of work

Both splits from `1e817c5`, over the first 60 declarations, where `gapped` is 0
and the totals reconcile exactly against `proved`.

**By the site that asks.** `Interp::note_conv` has exactly two callers, and they
are the two axes MINI-DESIGN.md §0.3 distinguishes:

| | conversions | share |
| --- | ---: | ---: |
| `Checker::whnf`'s `done!` — reduction legs | 159 127 | **77.6 %** |
| `Checker::assert_def_eq_as` — decisions | 45 947 | 22.4 % |
| total (= `proved` 205 074, `gapped` 0) | 205 074 | |

**Reduction, not decision, is more than three quarters of the census.** That is
the population any `Nat` acceleration has to act on.

**By the shape of the declaration**, over all 229 (`f9bc1db`):

| shape | declarations | conversions | share |
| --- | ---: | ---: | ---: |
| `match_` auxiliaries | 37 | 3 677 946 | **47.1 %** |
| plain definitions and theorems | 152 | 3 573 703 | 45.8 % |
| `noConfusion` | 13 | 390 135 | 5.0 % |
| `casesOn` | 14 | 61 271 | 0.8 % |
| `rec` | 4 | 51 650 | 0.7 % |
| `brecOn` | 5 | 39 738 | 0.5 % |
| `below` | 3 | 13 151 | 0.2 % |
| `decEq` | 1 | 1 497 | 0.0 % |

**Lean's generated `match_` auxiliaries are 16 % of the declarations and 47 % of
the conversions** — the most over-represented shape on the axis, and, unlike a
`Nat` lemma, one that is generated for every pattern match in the file. It
recurs past the wall: `List.get.match_1`, `BitVec.decEq.match_1` (§4).

### 2.4 The hot declarations contain no numerals

Counted statically over each declaration's whole expression DAG, and then over
its whole backward dependency closure:

| declaration | DAG nodes | `natVal` in it | closure | `natVal` in the closure |
| --- | ---: | --- | ---: | --- |
| `_private.…Nat.le_of_ble_eq_true.match_1_1` | 241 | 2 × `0` | — | — |
| `Nat.ble_eq_true_of_le` | 131 | **none** | 69 | 8, all `0`/`1` |
| `_private.…Nat.le_trans.match_1_6` | 755 | **none** | — | — |
| `_private.…noConfusion_of_Nat.aux` | 66 | **none** | — | — |
| `Nat.modCoreGo_lt` | 197 | 2 × `0` | 174 | 50, all `0`/`1` |
| `Nat.modCore_lt` | 121 | 2 × `0` | 180 | 56, all `0`/`1` |
| `Nat.mod_lt` | 148 | 2 × `0` | 196 | 65, all `0`/`1` |
| `List.get.match_1` | 380 | 2 × `0` | 76 | 6, all `0`/`1` |

**Nine declarations carrying 5.9 M of the 7.8 M measured conversions, and
between them eight numeral nodes, all `0`.** These are *small* declarations —
66 to 755 DAG nodes — whose cost is entirely dynamic. Widening the search to
everything they can reach does not change the picture: across 174–196
declarations of closure, the only numerals that exist anywhere are `0` and `1`.

`List.get.match_1`'s 28 constants make the point across a family boundary:
`Nat`, `Nat.casesOn`, `Nat.ctorIdx`, `Nat.succ`, `Nat.zero`, `Nat.le`,
`Nat.le.casesOn`, `Nat.le.refl`, `Nat.le.step`, `noConfusion_of_Nat`,
`instOfNatNat`, `instLTNat` — eleven of them. **The second wall is not a
different problem wearing a `List` name; it is the same `Nat`-destructuring
matcher shape.**

### 2.5 The `Nat` clause changed none of this

Every figure in §2.3, §3.2 and §3.3 was re-taken on `1e817c5` after the clause
landed. The 60-declaration prefix, side by side:

| | `f9bc1db` | `1e817c5` |
| --- | ---: | ---: |
| instructions | 370 483 647 037 | 369 268 757 865 |
| conversions `proved` / `gapped` | 205 331 / **0** | 205 074 / **0** |
| `whnf` / `assert_def_eq` split | 159 300 / 46 031 | 159 127 / 45 947 |
| live heap at declaration 60 | 92 426 479 | 91 819 730 |
| `parts` share of it | **54.4 %** | **54.4 %** |
| `parts` entries / lookups | 124 468 / 30 193 | 123 037 / 30 193 |

And the 229-declaration ladder, over the same span:

| | `f9bc1db` | `1e817c5` |
| --- | ---: | ---: |
| conversions over the 229 | 7 809 091 | 7 808 716 (**−0.005 %**) |
| `Nat`-attributable, of them | 7 432 009 = **95.2 %** | 7 431 892 = **95.2 %** |
| top ten by conversions (§2.1) | | **identical to the digit** |
| largest per-declaration divergence | | `UInt8.lt`, 218 → 121 |

The largest movement anywhere in 229 declarations is 97 conversions on
`UInt8.lt`. **The clause is invisible on this workload**, which is §1.3.4's
conclusion arrived at from the per-declaration side.

## 3. The memory, on its own

### 3.1 It is accumulation, not a transient

The probe prints the live heap at every declaration boundary — a point at which
the previous pair's `Checker` has been dropped — with the all-time peak beside
it. Over the 229-declaration ladder:

| | |
| --- | --- |
| live at declaration 229 | 1 883 509 983 B |
| all-time peak there | 1 883 779 036 B — **269 KB above live** |
| high-water of `peak − live` at any boundary | 114 479 229 B (**6.1 %** of the final live) |
| largest heap freed by dropping one pair's `Checker` | 11 601 188 B |
| largest `Frame::map` over 295 traced pairs | **35** entries |
| largest `wt_memo` | 5 018 entries |

**The per-pair `Checker` is not where the memory is.** `frames` — the memo
`PROFILE.md` §5 was about — peaks at 35 entries. What costs is what survives the
declaration boundary, and it grows with the conversions at a rate that slowly
*improves*:

| conversions | live heap | bytes / conversion |
| ---: | ---: | ---: |
| 26 904 | 42.3 MB | 1 573 |
| 636 094 | 193.5 MB | 304 |
| 7 809 091 | **1 883.5 MB** | **241** |

At 241 B/conversion the 30 347 733 conversions of the recorded run come to
**7.3 GB**, which is the run that dies at 10 GB.

### 3.2 Where it goes: `Interp::parts`, 54 %

At declaration 60 the probe drops each retained table in turn and reports the
live-heap fall. Shared structure is attributed to whichever table goes first, so
the order is a parameter (`MINI_TEARDOWN_ORDER=reverse`). **It is not a caveat
here**: run both ways, `parts` frees 35 305 728 B forward and 35 808 104 B
reverse — 1.4 % apart, so essentially nothing it holds is shared. *(Those two
use `HashMap::clear`, which keeps the table's own allocation; the column below
uses `= Default::default()`, which returns it. Both are `parts`.)*

| dropped, in order | freed | share of the 91 819 730 B live |
| --- | ---: | ---: |
| **`Interp::parts`** | **49 942 008** | **54.4 %** |
| `Interp::consts` — the certificates: `term`, `typing`, `defeq` | 442 652 | 0.5 % |
| `lams`/`fibres`/`conds` and their three by-symbol indices | 5 428 728 | 5.9 % |
| the clauses — `direct`, `eta`, `quotient`, `acc`, `rec_acc`, `ind`, `dprod_fs` | 3 937 522 | 4.3 % |
| `prop_sub`, `labels` | 1 240 | 0.0 % |
| **residue: parsed export, the `TcCtx` arena, `Environment`, the schedule** | 32 067 580 | 34.9 % |

`parts` takes the live kernel `Term` count from **491 503 to 99 604** on its own
— **80 % of every live `Term` in the process is held by the hint table.** The
residue, 32.1 MB, is within 3 % of the 31.4 MB the acceptance pass peaks at
before any interpretation runs (§1): the parsed export and the arena are
**flat**.

`derived/src/skeleton.rs` said what the table was, and its own header was why
it was 54 % of the heap:

> `pub type Parts = HashMap<Term, (FnSym, Vec<Term>)>;`
> … `record` builds `f(args)` and remembers its applicative structure in
> `parts`; **every term the caller intends to decompose later must be built
> through it.**

It was a *hint* — "a wrong hint yields a skeleton whose reassembly fails to
match, never a bad proof" — so no soundness rested on it. It had no eviction, no
scope and no bound, and `Interp::mk` was the only way to build an interpretation
term, so every term the interpretation ever constructed was retained for the
life of the run together with a cloned `Vec` of its arguments.

**And the value it stored was the key's own contents.** `Term` is
`Rc<TermData>` and `TermData::App(FnSym, Vec<Term>)` is one of its three
constructors, so `parts[t]` was exactly what the node `t` points at, in a second
`Vec`. The table existed because the kernel exposed no *reader* — `data()` is
`pub(crate)` — and not because the information was anywhere else. §3.3 is
written against that reading and is superseded by it.

**Confirmed at scale, on two workloads, four orders of magnitude up.** The
teardown above is at declaration 60, where the live heap is 92 MB. The probe
also prints `parts.len()` on every row, so its growth can be followed to
3.84 GB — and it is a straight line with the same slope on both files:

| | conversions | live | `parts` entries | entries / conversion |
| --- | ---: | ---: | ---: | ---: |
| residue ladder, decl 60 | 204 496 | 91.5 MB | 122 701 | 0.60 |
| residue ladder, decl 154 | 5 079 824 | 1 149.1 MB | 3 276 675 | 0.65 |
| `BitVec` closure, decl 70 | 5 238 012 | 1 149.3 MB | 3 635 201 | 0.69 |
| `BitVec` closure, decl 81 | 17 242 524 | 3 841.6 MB | 11 693 778 | 0.68 |

**`parts` grows at 0.56–0.71 entries per conversion everywhere**, and the
*marginal* cost of an entry is **245 B** on the residue ladder's last
declaration and **247 B** on the closure's — two independent workloads,
declarations of wildly different size, the same number. Against the total
241 B per conversion (§3.1) that puts `parts` at about 0.6 × 246 ≈ 150 B of it,
which is 62 % — the same answer the teardown gives from the other direction.

The single clearest instance: **`BitVec.decEq._proof_1` adds 3 737 947 `parts`
entries and 1 393.8 MB of live heap in one declaration**, while adding one entry
to `Interp::consts`.

### 3.3 How much of it is dead, and what pruning costs

Counted over the same 60 declarations:

| | |
| --- | ---: |
| `skeleton::record` calls | 431 598 |
| distinct entries inserted | **123 037** |
| `skeleton` lookups into the table | **30 193** |
| lookup misses | **0** |

**At most 30 193 of 123 037 entries are ever read — at least 76 % of the table
is never touched**, and the true figure is higher because lookups repeat.

**The naive prune is unsound, and that is measured rather than argued.**
`MINI_PARTS_RESET=1` empties `parts` at each declaration boundary:

| first 60 declarations, `1e817c5` | baseline | `parts` cleared per declaration |
| --- | ---: | ---: |
| instructions | 369 268 757 865 | 357 817 603 209 (**−3.1 %**) |
| live heap at declaration 60 | 91 819 730 | **36 532 425 (−60.2 %)** |
| conversions `proved` | 205 074 | 171 643 |
| **`gapped`** | **0** | **213** |

The 213 are `not-decomposable` 108, `no-endpoint` 69,
`NoDefiningEquation(LT.lt)` 36. So `parts` genuinely *is* read across
declaration boundaries and cannot simply be dropped at one. What the row
establishes is the size of the prize: **the table costs nothing in time — it
saves slightly more than it costs — and holds 60 % of the heap.**

### 3.4 The prune, and why there was none to find

**The question this section asks — *which* entries may be discarded — has no
answer, because the premise is wrong. There is nothing in the table to keep.**

`skeleton::record` stored `(f, args)` under the key `Term::apply(f, args)`, and
that key is an `Rc<TermData::App(f, args)>`: the value is a second copy of what
the key already holds. What the table bought was not information, it was
*access* — `kernel::Term` exposed constructors and no reader, so a client that
had to take a term apart had to have remembered building it.

So the fix is a reader. `kernel::Term::as_app(&self) -> Option<(FnSym, &[Term])>`
is six lines, is the exact analogue of the `Formula::as_eq` that has always been
there, and widens nothing: it can only expose `TermData::App`, and an `App`'s
arguments are locally closed whenever the whole term is, so it hands back
nothing a client could not already hold. With it, `derived::skeleton::skeleton`
reads structure off the term and is **total**, `Interp::parts_of` is
`t.as_app()`, `Interp::mk` is `Term::apply`, and the field is deleted.

**The 213 gaps were the proxy failing, not entries being lost.** Recordedness
was standing in for decomposability, and it was wrong in both directions.
Wrong on the read side: a term the *kernel* built — a substitution instance, or
either endpoint of a `derived::congr` — never passed through `Interp::mk` and
read back as structureless, which is `mini/src/conv.rs`'s six lost conversions
on `mutual_aux_encoding` and, generalised, the 108 `not-decomposable` and 69
`no-endpoint` above. Wrong on the write side: keeping the proxy true meant
remembering every term ever built, forever. Clearing the table breaks the proxy;
deleting it removes the thing being approximated.

Measured on the change, `test` profile, `perf stat -e instructions`, against
`origin/master` at `0260925`:

| workload | | baseline | reader | |
| --- | --- | ---: | ---: | ---: |
| 91 good tutorial exports | instructions | 405 375 599 994 | 402 689 993 069 | −0.66 % |
| | peak RSS | 178 540 kB | **33 808 kB** | **−81.1 %** |
| `Nat.ble_eq_true_of_le` closure, 47 decls | instructions | 2 251 144 138 254 | 2 232 215 740 074 | −0.8 % |
| | peak RSS | 1 049 824 kB | **46 524 kB** | **−95.6 %** |

**And the two declarations that stop `init-prelude` today, cut out with
`scripts/decl-closure.py` and run alone.**

| closure | | baseline | reader |
| --- | --- | ---: | ---: |
| **`Nat.mod_lt`, 159 decls** — the `Nat.mod*` cluster the file dies inside | outcome | **`SIGABRT` at a 12 GB `ulimit -v`**: `memory allocation of 3 825 205 264 bytes failed`, at 1 992 s | **completes**, 159 of 159, **66 569 578 conversions, `gapped 0`** |
| | peak RSS | **11 142 200 kB** | **501 984 kB** |
| | instructions | 26 461 224 027 620, to the abort | 38 790 399 776 432, 2 825 s |
| **`BitVec.decEq` + `BitVec.noConfusion`, 83 decls** | outcome | §4.2: killed by a 25-minute timeout **inside declaration 81 of 83**, 17 242 524 conversions | **completes**, 83 of 83, **25 335 661 conversions, `gapped 0`** |
| | peak RSS | ≥ 3 841 600 kB | **106 172 kB** |
| | instructions | — | 15 071 153 293 830, 1 096 s |

**That is the memory half of the goal, answered, and the `Nat.mod_lt` row is
the sharpest form of it.** That closure runs **66 569 578 conversions** — more
than twice the 30 347 733 at which the whole file died — and peaks at 490 MB.
At §3.1's measured 241 B per conversion it would have needed **16 GB**; it
needs **7.5 B**, and the figure is *flat* rather than a slope, because what was
growing was the table and not the work. Both walls this document found are
memory-free now: the `Nat.mod*` cluster completes, and §4.2's `BitVec` pair,
which no run had ever finished, completes.

What stops `init-prelude` is **time** — `List.get.match_1` alone is 11.00 T
instructions (§4.2) and this change moves none of it.

All 91 exports' `--verbose` output is **byte-identical** across the change —
every `facts`, `clauses`, `ledger`, `evidence`, `convs` and `untranslated` row,
`accept 89 / decline 2 / reject 0`, `constEv 218/218`, `unsealed 0`,
**`gapped 0`** — after two baseline runs were diffed against each other to
establish that the output is deterministic at all. The closure's report is
byte-identical too, at `proved=3 750 820  gapped=0`.

**Time is unchanged and that is the expected sign.** §3.3's row has the table
*saving* 3.1 % when cleared, because clearing is 33 431 conversions that stop
happening; removing it changes no conversion at all, and the ≈0.7 % it returns
is the 431 598 hash inserts and their `Vec` clones. The lever was always memory,
and it is the whole of it: what remains at declaration 60 is §3.2's 32.1 MB
residue, which is the parsed export and the arena and is flat.

## 4. Is there a second `Nat.modCore_lt`? Yes — `BitVec.decEq._proof_1`

No run has ever reached declaration 232, so the prefix cannot answer this. Two
methods were used instead and they agree.

### 4.1 The acceptance pass as a proxy, over all 1 245 declarations

The acceptance pass runs the whole file in 23 s (§1), so a per-declaration
allocation trace over *all* of it is cheap. Against the 229 declarations
measured on both axes it predicts interpretation cost with a **Spearman rank
correlation of 0.776**, an aggregate ratio of **1 643×**, and a per-declaration
spread of 130×–7 400× (p10–p90). Good enough to rank; not to price.

**Validated out of sample on five declarations no ladder has ever reached.**
The `BitVec` closure of §4.2 interprets residue declarations 427–431 on its way,
so their interpretation-pass allocations are directly measured:

| idx | declaration | measured allocs | predicted (1 645×) | error |
| ---: | --- | ---: | ---: | ---: |
| 427 | `_private.…Nat.eq_of_beq_eq_true.match_1_1` | 1 968 387 268 | 2 083 463 235 | **+6 %** |
| 428 | `Nat.eq_of_beq_eq_true` | 1 545 279 683 | 1 012 642 260 | −34 % |
| 429 | `_private.…Nat.ne_of_beq_eq_false.match_1_1` | 2 350 738 289 | 2 475 035 745 | **+5 %** |
| 430 | `Nat.ne_of_beq_eq_false` | 1 425 597 266 | 1 029 796 320 | −28 % |
| 431 | `Nat.decEq` | 146 079 057 | 106 053 150 | −27 % |

Five for five inside 1.5×, two inside 6 %. The closure interprets them with a
different store behind it, so this is not a controlled comparison — but it is
far better than the p10–p90 spread would suggest, and it is why §5's aggregate
is written down at all.

Of the file's 68 109 737 acceptance-pass allocations, the first 229 declarations
are 10.8 % and the unreached 1 015 are **89.2 %**. The largest of the unreached,
`Nat` set aside:

| idx | declaration | acceptance allocs |
| ---: | --- | ---: |
| 555 | **`List.get.match_1`** | 4 760 852 |
| 466 | **`BitVec.noConfusion`** | 3 830 784 |
| 464 | **`BitVec.decEq._proof_1`** | 3 639 824 |
| 468 | `BitVec.decEq` | 2 713 880 |
| 467 | `BitVec.decEq._proof_2` | 2 282 470 |
| 1164 | `BitVec.ofFin.noConfusion` | 1 814 332 |
| 557 | `List.get` | 1 509 134 |
| 456 | `BitVec.decEq.match_1` | 1 365 932 |
| 845 | `Trans.noConfusion` | 560 258 |
| 455 | `BitVec.casesOn` | 453 772 |

The **eight-declaration `BitVec` cluster (455, 456, 464–468, 1164) is 16.46 M —
59 % of all non-`Nat` acceptance cost in the unreached remainder**; `List.get`
and its matcher a further 6.27 M. Both are §2.3's over-represented shapes,
`match_` and `noConfusion`, recurring where the prefix cannot see.

### 4.2 Cut them out and run them

`scripts/decl-closure.py` emits the **backward dependency closure** of named
declarations as a standalone export — the closure only, so no `Nat.mod*` is in
either of these. Both run under `ulimit -v` 8 GB.

**`BitVec.decEq` + `BitVec.noConfusion`: 83 declarations, and two of them are
second `Nat.modCoreGo_lt`s.** The run was killed by a 25-minute timeout inside
declaration 81 of 83, at **17 242 524 conversions and 3.84 GB**, with `gapped` 0
throughout:

| idx | declaration | conversions | share | live added |
| ---: | --- | ---: | ---: | ---: |
| 78 | **`BitVec.decEq._proof_1`** | **5 545 459** | **32.2 %** | **+1 393.8 MB** |
| 80 | **`BitVec.noConfusion`** | **4 638 228** | **26.9 %** | **+761.2 MB** |
| 70 | `BitVec.decEq.match_1` | 1 375 045 | 8.0 % | +464.8 MB |
| 65 | `_private.…Nat.ne_of_beq_eq_false.match_1_1` | 1 373 902 | 8.0 % | +352.8 MB |
| 63 | `_private.…Nat.eq_of_beq_eq_true.match_1_1` | 1 146 434 | 6.6 % | +251.0 MB |
| 64 | `Nat.eq_of_beq_eq_true` | 890 104 | 5.2 % | +216.3 MB |
| 69 | `BitVec.casesOn` | 852 465 | 4.9 % | +139.6 MB |
| 66 | `Nat.ne_of_beq_eq_false` | 834 842 | 4.8 % | +144.6 MB |
| 79 | `BitVec.noConfusionType` | 401 719 | 2.3 % | +65.6 MB |
| | `BitVec`-named, total | 12 813 140 | **74.3 %** | |
| | `Nat`-named, total | 4 354 255 | 25.3 % | |

**`BitVec.decEq._proof_1` is 5 545 459 conversions and 1.39 GB; `BitVec.noConfusion`
is 4 638 228 and 0.76 GB.** For scale, `Nat.modCoreGo_lt` — the declaration that
kills the whole file — is 12.43 M. These are the same class of object, they are
measured rather than projected, and §4.1's proxy had them second and third on
its list before either was run.

Two further things the table settles. **Reaching the first `BitVec` declaration
at all costs 4 385 547 conversions and 1.01 GB, and every one of them is
`Nat`** — five declarations, the same generated-`match_1_1`-plus-theorem shape
as §2.1's, over `Nat.beq` at symbolic arguments with no numeral in reach (§2.4).
And **`BitVec` genuinely is a cost centre of its own**: 74.3 % of the closure,
not an artefact of the `Nat` it drags in.

**`List.get`: 71 declarations, and `List.get.match_1` on its own is bigger than
`Nat.modCoreGo_lt`.** The closure reaches declaration 68, `List.get.match_1`, in
1 100 680 conversions and 263 MB — one twenty-eighth of what it takes to reach
`Nat.modCoreGo_lt` in the residue — and then **that single declaration ran for
1 467 s of user time, spent 11 001 763 784 707 instructions, exhausted an 8 GB
`ulimit -v` (`memory allocation of 1 912 602 640 bytes failed`) and did not
complete.**

| | |
| --- | --- |
| instructions, whole run | **11 001 763 784 707** (11.00 T) |
| …of which before `List.get.match_1` | 1.1 M conversions' worth, 263 MB — a rounding error |
| how it ended | `SIGABRT` at the 8 GB cap, **inside declaration 68 of 71** |
| for comparison, the whole residue to declaration 231 | 21.71 T, 10 GB, 1 245 declarations |

**One declaration at residue index 555 is at least half of the entire recorded
`init-prelude` run, and that is a lower bound because it did not finish.** It is
a `match_` auxiliary over `Fin`/`Nat` (§2.4), 380 DAG nodes, containing two
numerals, both `0`. It was ranked first among the unreached by §4.1's proxy.

## 5. What `init-prelude` costs with `Nat` solved — an estimate

**Flagged as an estimate throughout, and now doubly so, because §1.3.4 has shown
that landing the `Nat` clause moved the wall by 0.02 % and this projection
assumes a `Nat` that is actually cheap.**

The measured anchors:

* the 229 completed declarations cost **6.27 T** instructions (probe-corrected)
  for 12 062 157 335 interpretation-pass allocations — **519.8 instructions and
  0.154 live bytes per allocation**, 1 544.6 allocations per conversion;
* the interpretation-to-acceptance allocation ratio is **1 643×** over all 229,
  **1 595×** over the 138 non-`Nat` declarations and **1 645×** over the 91
  `Nat` ones. That the two agree to 3 % is what makes the projection worth
  writing down;
* the 1 015 unreached declarations carry **60 768 475** acceptance allocations,
  **27 688 115 (46 %)** of them non-`Nat`.

Applying the non-`Nat` ratio to the non-`Nat` remainder, 27 688 115 × 1 595:

> **≈44.2 G allocations ≈ 28.6 M conversions ⇒ ≈23 T instructions and ≈6.8 GB
> of live heap.**

So even granting a free `Nat`, `init-prelude` would cost about today's whole
run again on `BitVec` and `List`, with memory binding both times — 6.8 GB is
under a 10 GB cap and over a 4 GB one, with no margin either way.

**And that is a floor, because the one top-ranked declaration since measured
came in far above its own prediction.** `List.get.match_1`'s 4 760 852
acceptance allocations predict 7.59 G interpretation allocations ⇒ **≈3.95 T**;
it measured **≥11.00 T** and did not finish (§4.2). The proxy under-priced the
largest item on its own list by **at least 2.8×**. §4.1's out-of-sample check
was on five mid-sized `Nat` declarations and evidently does not extend to the
tail. Read the ≈23 T as a lower bound and the ranking as the reliable part.

**Four things make this weak.** The per-declaration ratio spans two orders of
magnitude, so only the aggregate is meant; the out-of-sample check came in five
for five inside 1.5× (§4.1), which is the reason to state it. The 54 % of
unreached acceptance cost that is `Nat`-named is set to zero here, and §2.4
argues it will not be zero. The projection assumes the unreached declarations
behave like the reached ones, which `List.get.match_1` already strains. **And
"non-`Nat`" means only that the declaration's name does not begin with `Nat.`**:
the `BitVec` closure is 25.3 % `Nat` by measurement (§4.2) and
`List.get.match_1` spends its conversions on `Nat.casesOn` and
`noConfusion_of_Nat` (§2.4).

**The memory half is the firmer half**, because it rests on a measured constant
rather than a proxy — and it is the half `Nat` does not touch.

## 6. What was not measured, and why

* **The full `init-prelude` run was not re-taken.** The critical path had
  priority and a second ~10 GB / 26-minute run would have risked the ~50 GB
  ceiling. §1.3.4's 21.71 T / 30 341 025 / 10 GB is used as given.
* **Declarations 229–231 were never completed here.** `Nat.modCoreGo_lt` killed
  the 4 GB ladder. So declarations 0–228 are 30 % of the recorded instructions
  and 26 % of the recorded conversions, and the three `Nat.mod*` declarations
  plus the aborted 232nd are the other 70 % — the split *within* those three is
  `1ba1220`'s, not this study's.
* **`List.get.match_1`'s cost has a lower bound and no upper one.** It did not
  finish in either run — the second ended at an 8 GB cap after 11.00 T. What it
  would cost to completion, and therefore whether the residue can be finished at
  all at any memory budget, is unknown.
* **The closures were run, not profiled.** They say *whether* a declaration is a
  wall, not what inside it is expensive. A `perf record` on
  `List.get.match_1` is the obvious next measurement and was not taken.
* **The `BitVec` closure did not finish either** — a 25-minute timeout inside
  declaration 81 of 83, so `BitVec.decEq._proof_2` and `BitVec.decEq` are
  unmeasured and the 17.24 M is a lower bound too.
* **Nothing past declaration 232 has been interpreted in file order.** §4.1's
  ranking is a proxy; §4.2 measures two points on it out of context.
* **The teardown *split* (§3.2) is from declaration 60**, where the live heap is
  92 MB. `parts`' share of the *growth* is separately confirmed to 3.84 GB on two
  workloads (§3.2), but the other five rows of that table were not re-taken at
  scale.
* **The 229-declaration ladder and the shape table are `f9bc1db`.** §2.5 shows
  the 60-declaration prefix unmoved by the `Nat` clause and §1.3.4 shows the
  cumulative counts unmoved by 0.02 %, but the per-declaration table itself was
  not re-taken.

## 7. How to reproduce

```bash
git apply scripts/prelude-cost-probe.diff     # not landed; a scratch worktree
cargo build --release --bin mini
python3 scripts/nat-reach.py vendor/arena-tests/good/init-prelude.ndjson --write residue.ndjson

# §1 the acceptance axis alone, and §4.1's per-declaration trace over all 1245
( ulimit -v 4000000; MINI_STOP_AFTER=0 MINI_CONV_TRACE=1 MINI_ACCEPT_TRACE=1 \
    perf stat -e instructions ./target/release/mini --no-modelgen --verbose residue.ndjson )

# §2 the ladder — dies inside declaration 229 under a 4 GB cap, which is the point
( ulimit -v 4000000; MINI_STOP_AFTER=231 MINI_CONV_TRACE=1 \
    perf stat -e instructions ./target/release/mini --no-modelgen --verbose residue.ndjson )

# §2.3, §2.5, §3.2, §3.3 — ~90 s each
( ulimit -v 4000000; MINI_STOP_AFTER=60 MINI_CONV_TRACE=1 \
    perf stat -e instructions ./target/release/mini --no-modelgen --verbose residue.ndjson )
( ulimit -v 4000000; MINI_TEARDOWN_ORDER=reverse MINI_STOP_AFTER=60 MINI_CONV_TRACE=1 \
    ./target/release/mini --no-modelgen --verbose residue.ndjson )
( ulimit -v 4000000; MINI_PARTS_RESET=1 MINI_STOP_AFTER=60 MINI_CONV_TRACE=1 \
    perf stat -e instructions ./target/release/mini --no-modelgen --verbose residue.ndjson )

# §4.2 the closures
python3 scripts/decl-closure.py residue.ndjson bitvec.ndjson BitVec.decEq BitVec.noConfusion
python3 scripts/decl-closure.py residue.ndjson listget.ndjson List.get
( ulimit -v 8000000; MINI_CONV_TRACE=1 perf stat -e instructions \
    ./target/release/mini --no-modelgen --verbose bitvec.ndjson )
```

**The probe's cost and its neutrality, measured rather than assumed.** Against a
clean release build of the same tree, on three tutorial exports both binaries
complete:

| export | clean | probe | overhead |
| --- | ---: | ---: | ---: |
| `090_projDataIndexRec` | 2 594 189 899 | 2 804 603 444 | +8.1 % |
| `124_quotLiftReduction` | 5 159 534 343 | 5 551 402 030 | +7.6 % |
| `037_prodType` | 2 810 708 482 | 3 035 498 229 | +8.0 % |

and the two binaries' `--verbose` output is **byte-identical** on all three, so
no ledger row, conversion count or verdict here is a probe artefact.

Sources: §1, §2, §2.5, §3, §4 — the probe's `convtrace` / `convtrace-stop` /
`pairdrop` / `convkind` / `teardown` / `accepttrace` rows and `perf stat`;
§2.4 and the verdict's closure table — `scripts/nat-reach.py`'s pool walker over
the export JSON, no run involved; §4.2 — `scripts/decl-closure.py` outputs;
§1.3.4 and `1ba1220` are cited as the record and were not re-derived.
