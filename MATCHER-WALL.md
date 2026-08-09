# The matcher wall is `mini`'s, not the design's

*2026-08-09. A measurement, on the owner's question — "if `mini` cannot handle
declarations like matchers then maybe that's just unavoidable, and we won't be
able to process the prelude until we switch to the `nanoda` type checker with
the proper caching and lazy defeq". It is avoidable, and the evidence is that
**the upstream `mini` already does it**. This document changes no behaviour and
lands no fix; it runs the same declarations through three checkers and reports
what each costs.*

*Provenance. Every figure is `perf stat -e instructions`; peak RSS from
`time -v`; each run under its own `ulimit -v` (8 GB unless stated — a cap
bounds address space, not RSS). Wall clocks are commentary: the machine carried
three other seats throughout.*

* *`mini` and `nanoda_bin`: `origin/master` at **`d8c027f`**, `release`, in a
  scratch worktree. `f29c7ef`'s term reader is in, so `Interp::parts` no longer
  exists. Figures from the previous master **`0260925`** say so. `233bbc1`
  (bounded `whnf` self-recursion) landed while this was being written and is
  **neutral on these closures**: `p1` re-taken on it is 2 999 349 222 779
  against `d8c027f`'s 2 998 879 824 804, +0.016 %, conversions identical to the
  digit.*
* *`nanoda_bin --features tg`: the same tree, separate `CARGO_TARGET_DIR`.*
* *`lean-mini-kernel` — what `mini` is a port of — at **`ef7ade0`** (`master`,
  cloned today), `lake build` on `leanprover/lean4:v4.28.0`.*
* *Two `mini` rows are **cited, not re-taken**: `15c63ad`'s `Nat.mod_lt` and
  `BitVec`-pair closures, which are `test` profile. They are marked †.*

## Verdict

**(b), and not narrowly. `lean-mini-kernel` — the upstream reference `mini` is
a fidelity port of, with the same no-state, no-cache, no-hash-consing,
full-eager-delta design, written in Lean — checks `List.get.match_1`'s closure
in 34.2 G instructions and 71.6 MB, and checks the *entire* `init-prelude`
residue, all 1 245 declarations, in 805 G and 73.9 MB. `mini` dies at
declaration 232 of those same 1 245.**

So "no checker of this design can handle a matcher" is false by construction:
the checker of that design does handle it. On the matcher's own closure the
reference is **302× cheaper** than `mini` (34.2 G against 10.33 T); on the whole
residue it uses **1/27 of the instructions `mini` spends getting 18 % of the
way, and 1/135 of the memory** (§2.5). **The owner's read does not survive, and
`init-prelude` is not gated on the pivot.**

The mechanism the brief offered for (a) is refuted specifically, not just
outweighed. Eager delta is not what costs: `lean-mini-kernel`'s `whnf` unfolds
any `const` carrying a value unconditionally, has no lazy-delta heuristic and
no reduction hints (`MiniKernel/Kernel.lean:148–180`, read), its monad is
`ReaderT LEnv (Except String)` with no cache of any kind anywhere in its 777
lines, and its `assertIsDefEq` opens with `inferType e1` at *every* entry for
the proof-irrelevance gate — the same shape as `mini`'s `def_eq_ev`
(`:415–420`). Same strategy, same shape, **77–302× less work**.

### What is actually wrong, measured

`CERTIFYING-OVERHEAD.md` (2026-08-07) already named the cause: `mini`'s
*certified* path re-enters full `infer_type` from inside itself —
`beta_premise` infers the argument at every β step
(`mini/src/kernel.rs:2125–2126`), `def_eq_ev` infers its left endpoint at every
`Lhs::Unknown` entry (`:3717`), nothing caches `infer_type` — and **97.8 % of
conversions happen inside a repeat of an already-seen α-canonical judgement**.
Both sites are still live at `d8c027f`. This study adds three things:

* **The tax is a per-step constant, not a blowup.**
  Across five closures spanning 5.5 M to 66.6 M conversions, `mini` spends
  **326 000 to 594 900 instructions per conversion it records** — a 1.8× spread
  over closures that differ 12× in size — while the reference's whole run is
  **1 078 to 7 533** instructions per one of those same conversions (§2.3).
  `mini` is both taking steps the reference does not take and paying far more
  for each; both are the one recurrence.
* **A flat profile of where those instructions go, which `PRELUDE-COST.md` §6
  named as the missing measurement.** On `p1`: **47.4 % of samples are in
  `kernel/` — `Term`/`Formula` construction, `open`/`close`, `PartialEq`, `Rc`
  teardown — 44.0 % are in glibc `malloc`/`free`, 6.0 % in `derived/`, and
  1.58 % in `mini/`.** The type checker is 1.58 % of its own run; the first
  line of it, `Checker::infer_type`, is 0.16 % (§2.4).
* **Two lines of that are free, and they are measured.** `checker/src/main.rs`
  links mimalloc as the binary's `#[global_allocator]` and carries the
  measurement that put it there (−28 % on `init-prelude`); `mini/src/main.rs`
  has no `#[global_allocator]` and runs on the glibc allocator that is 44 % of
  its profile. Copying those two lines into `mini` takes `p1` from
  **2 998 879 824 804 to 2 173 504 088 058 instructions — −27.5 %**, and does
  the same on the other two closures (−27.6 %, −29.3 %) with every conversion
  and gap count identical to the digit (§2.6). Between a quarter and a third of
  the run, sitting unclaimed in the sibling binary.

**Three further things the numbers settle.**

* **The arena's `mini` ❌ is not evidence of anything.** `arena.lean-lang.org`
  reports `mini` on `mathlib` — and on `init-prelude` — as **"Declined via the
  `declines` field in the checker configuration; the checker was not run"**:
  exit 2, 0 ms, 0 B. Three other checkers carry the identical non-result. On
  the one large test upstream `mini` *is* run on, `perf/shift-cascade`, it
  accepts in 573 ms / 74.6 MB (§4).
* **Memory has stopped being the question; time is the question.** `f29c7ef`
  landed hours before this study: on `p1`, `mini`'s peak RSS falls from
  **1 400 064 kB to 87 436 kB** while instructions move **−0.8 %** and the
  conversion count is **identical to the digit** (§2.2).
* **`checker/` already accepts `init-prelude` end to end and already certifies
  most of it.** `nanoda_bin` checks all 2 059 declarations in **1.53 G
  instructions and 18.9 MB** — 0.007 % of what `mini` spends failing to. With
  `--features tg` it derives **149 682 real kernel `Thm`s with 15 423 gaps** in
  **198.0 G and 328.0 MB** (§3).

### Which axis, and what the goal therefore needs

The routing instrument of `ENV-UNIFY.md` buys the **acceptance** axis, and
nothing on the acceptance axis is in doubt: `checker/` accepts the file for
1.53 G today. The **evidence** axis is where the goal lives, and there the two
engines answer different questions — four of the five `mini` runs here report
`gapped 0` and the fifth reports **22 gaps in 31 698 088 conversions**, against
`nanoda_bin --features tg`'s **241 on that same closure** and 15 423 on the
file.

**So the goal is not *gated* on either half of the pivot.** Routing would buy
an axis that is already free, and the pivot's evidence half would buy
`init-prelude` at 198 G with 15 423 gaps — which is a different product from
what `mini` delivers. The local axis is open, is cheaper, and preserves
`gapped 0`: `CERTIFYING-OVERHEAD.md`'s verdict is that carrying typing evidence
through the reduction stack plus a `Sealed` α-canonically-closed memo is *two
changes to the checker and none to `kernel/`*, and this study puts a floor
under what that is worth — **805 G and 74 MB is what the whole residue costs an
implementation of `mini`'s own design that does none of the re-derivation.**

What is *not* settled is how much of the 77–302× a genuinely gapless
certificate is entitled to. The reference produces no evidence at all, so it
bounds the type-checking half and nothing else. Nothing here says the gap
closes to 1×; it says the gap is not the design's, and that two of its
components are named and local — the allocator, priced here at −27.5 %, and
`CERTIFYING-OVERHEAD.md`'s `infer_type` recurrence, which is not priced by
anything yet.

### Two corrections to the brief

Stated early, as the standing rule asks.

* **`ENV-UNIFY.md`'s "certificates cannot cross engines" was withdrawn** at
  `d8c027f`, hours before the brief was written; its §0.4 records the overturn
  and §3 the re-derivation. The premise that a mixed run "degrades to counted
  escape-ledger gaps" no longer holds as stated.
* **`List.get.match_1`'s backward closure is 51 declarations**, not 76, by
  `scripts/decl-closure.py`. 76 is `PRELUDE-COST.md` §2.4's pool-walker count
  over a different relation; `List.get`'s closure — the one §4.2 ran — is 71.

## 1. What was run, and on what

Five closures, all cut from `vendor/arena-tests/good/init-prelude.ndjson` with
`scripts/decl-closure.py`, plus the whole residue. Three closures are the
brief's; two more are the ones this tree already has independent `mini` numbers
for, so the comparison does not rest only on runs taken here.

| tag | target declaration | export decl lines | nanoda declarations |
| --- | --- | ---: | ---: |
| `m1` | `List.get.match_1` | 51 | 84 |
| `p1` | `BitVec.decEq._proof_1` | 38 | 64 |
| `nc` | `BitVec.noConfusion` | 44 | 72 |
| `bvpair` | `BitVec.decEq` + `BitVec.noConfusion` | 83 | 118 |
| `modlt` | `Nat.mod_lt` | 159 | 208 |
| `residue` | `scripts/nat-reach.py --write` over the file | 1 248 | — |

A closure cut from the residue and the same closure cut from the unfiltered
file are **byte-identical** for all three of the brief's targets, so the
`Nat`-filtering makes no difference at this scale and the unfiltered file is
used throughout.

### 1.1 The pool had to be pruned, and the prune is neutral

`decl-closure.py` keeps the whole expression pool by design — it drops
declaration lines and does not renumber. That is invisible to `mini` and
`nanoda`, which index the pool lazily, and fatal to `lean-mini-kernel`, which
validates every pool line as it parses and declines a closure on a `natVal` of
`18446744073709551616` **that no surviving declaration mentions**. Dropping the
dead lines is not enough on its own either: nanoda's parser requires continuous
back-references — `Declined: Expr back-reference mismatch, expected Ie(272),
found Ie(282)`.

`scripts/prune-pool.py` (landed with this document) drops
the unreachable `"ie"` lines and renumbers the survivors densely, rewriting
every reference. Names and levels are untouched. **It is verdict-neutral and
work-neutral, checked on both engines:**

| | unpruned | pruned |
| --- | --- | --- |
| `nanoda_bin` verdict, `m1` / `p1` / `nc` | 84 / 64 / 72 declarations, no errors | **identical** |
| `nanoda_bin` instructions, `m1` | 318 542 737 | 68 384 971 |
| `mini` conversions `proved`, `p1` | **5 555 200** (`0260925`, unpruned) | **5 555 200** (`d8c027f`, pruned) |
| `mini` conversions `proved`, `nc` | **11 631 170** | **11 631 170** |

The instruction fall on nanoda is the dead pool it no longer parses — 250 M of
its 319 M was parsing 53 054 expression lines nothing reads. The conversion
counts agreeing **to the digit** across the prune *and* a master bump is the
control that matters: the pruned file is the same problem.

## 2. The three checkers, on the same declarations

### 2.1 The table

Instructions and peak RSS. `mini` and `nanoda` at `d8c027f`, `release`;
`lean-mini-kernel` at `ef7ade0`. † is cited from `15c63ad` (`test` profile).
**Every cell here completes.** Every `mini` cell reports `gapped 0` except `m1`,
which reports **22 gaps in 31 698 088 conversions** (12 `no-endpoint`, 10
`proj(HAdd)`) — 0.00007 %, against `--features tg`'s 241 on the same closure.

| closure | `mini` | `lean-mini-kernel` | `nanoda_bin` | `nanoda_bin --features tg` |
| --- | ---: | ---: | ---: | ---: |
| `m1` | **10 333 463 323 859** / 169.7 MB | **34 174 142 598** / 71.6 MB | 68 384 971 / 18.1 MB | 4 577 216 644 / 24.7 MB |
| `p1` | **2 998 879 824 804** / 87.4 MB | **18 288 889 710** / 71.6 MB | 50 106 280 / 18.9 MB | 2 797 414 955 / 18.2 MB |
| `nc` | **6 221 443 322 806** / 81.3 MB | **51 501 654 531** / 70.8 MB | 56 764 971 / 18.9 MB | 3 603 277 522 / 20.8 MB |
| `bvpair` † | 15 071 153 293 830 / 106.2 MB | **145 879 835 109** / 72.5 MB | 77 890 127 / 18.9 MB | 5 884 726 536 / 30.0 MB |
| `modlt` † | 38 790 399 776 432 / 502.0 MB | **501 459 855 675** / 72.3 MB | 143 976 713 / 19.0 MB | 12 309 904 075 / 46.2 MB |

### 2.2 The same closures on the previous master

`0260925`, `release`, unpruned closures, `ulimit -v` 8 GB:

| closure | instructions | peak RSS | conversions | outcome |
| --- | ---: | ---: | ---: | --- |
| `p1` | 3 022 180 175 514 | 1 400 064 kB | 5 555 200 | accepted |
| `nc` | 6 274 644 252 728 | 3 704 368 kB | 11 631 170 | accepted |
| `m1` | 10 423 303 656 232 | 6 178 032 kB | — | **`SIGABRT`: `memory allocation of 1 912 602 640 bytes failed`** |

`m1` independently reproduces `PRELUDE-COST.md` §4.2's "≥11.00 T and did not
finish", on a tighter closure (51 declarations against `List.get`'s 71).

Against §2.1 the term reader is **a memory fix and only a memory fix**, which is
`15c63ad`'s own conclusion, here confirmed on three further workloads:

| | instructions | peak RSS |
| --- | ---: | ---: |
| `p1` | −0.8 % | 1 400 064 → 87 436 kB (**16×**) |
| `nc` | −0.8 % | 3 704 368 → 81 332 kB (**46×**) |
| `m1` | −0.9 % | 6 178 032 → 169 744 kB (**36×**) |

`p1` and `nc` keep their conversion counts to the digit. **`m1` is the sharper
row: on `0260925` it spends 10 423 303 656 232 instructions and aborts; at
`d8c027f` it spends 10 333 463 323 859 and finishes.** Essentially the same
work, and the difference between a result and a corpse was the hint table.

### 2.3 The tax, per conversion

`mini` records a conversion count; the reference records nothing. Dividing each
checker's whole run by `mini`'s count is the only common denominator the two
expose. It prices `mini`'s work per unit of its own; it does **not** claim the
reference performs that many steps — the point of the right-hand column is
precisely that it evidently does not.

| closure | `mini` conversions | `mini` instr / conv | reference instr / same conv | ratio |
| --- | ---: | ---: | ---: | ---: |
| `m1` | 31 698 088 | **325 996** | 1 078 | **302.4×** |
| `p1` | 5 555 200 | **539 833** | 3 292 | **164.0×** |
| `nc` | 11 631 170 | **534 894** | 4 428 | **120.8×** |
| `bvpair` † | 25 335 661 | 594 859 | 5 758 | **103.3×** |
| `modlt` † | 66 569 578 | 582 705 | 7 533 | **77.4×** |

**`mini`'s own figure moves by 1.8× while the closures move by 12×**: its cost
is (its conversion count) × (a large per-step constant). A linear engine with an
expensive step, not a blowup.

The right-hand column moves by 7× and in the *opposite* direction, and that is
the informative half. On `m1` the reference's **entire run** is 1 078
instructions per `mini` conversion — at or below what one substituting
reduction step costs a kernel with owned de Bruijn terms and an explicit
`substs`, so it is not plausible that it performs 31.7 M of them. **`mini` is
therefore not only paying more per step; on the matcher it is taking steps the
reference does not take.** That is `CERTIFYING-OVERHEAD.md`'s measured
recurrence seen from outside: 40 271 → 4 369 255 conversions on
`proj_reduced_carrier` when the certified path is armed, and 97.8 % of
conversions inside a repeat of an already-seen α-canonical judgement. More
steps and a dearer step are the same defect from two sides.

*(The inference in that paragraph is a plausibility argument about the
reference's step count, not a measurement of it — see §6.)*

### 2.4 Where the instructions go

`perf record -F 99`, flat symbols, no call graph — the tree builds
`debug = "line-tables-only"` with `lto = true`, so a DWARF unwind is not
affordable and was abandoned after producing 353 MB on one closure. `mini` at
`d8c027f` on `p1`, everything above 0.7 %:

| % | symbol |
| ---: | --- |
| 14.66 | `_int_free_chunk` (libc) |
| 11.28 | `_int_malloc` (libc) |
| 9.62 | `kernel::term::Formula::new` |
| 8.02 | `malloc` (libc) |
| 6.84 | `cfree` (libc) |
| 5.16 | `Rc<kernel::term::FormulaData>::drop_slow` |
| 4.63 | `kernel::term::Formula as PartialEq>::eq` |
| 3.91 | `kernel::thm::Thm::mp` |
| 3.56 | `kernel::term::Term::new` |
| 3.28 | `kernel::term::Term::open` |
| 2.40 | `__libc_malloc2` (libc) |
| 2.40 | `Rc<kernel::term::TermData>::drop_slow` |
| 2.07 | `kernel::term::Formula::open` |
| 2.04 | `kernel::thm::Thm::ax_s` |
| 1.99 | `kernel::term::Term::close` |
| 1.95 | `kernel::term::Term as PartialEq>::eq` |
| 1.52 | `drop_glue::<kernel::thm::Thm>` |
| 1.31 | `Vec<kernel::term::Formula>::extend_trusted` |
| 1.03 | `kernel::term::Formula::close` |
| 0.88 | `derived::rules::syl` |
| 0.85 | `derived::prim::mp` |
| 0.83 | `Vec<kernel::term::Formula>::dedup_by` |
| 0.73 | `derived::a1i` |

The first `mini::` symbol at all is `mini::expr::E::view` at **0.20 %** and the
first line of the type checker is `mini::kernel::Checker::infer_type` at
**0.16 %**. Aggregated over the whole profile by owning crate:

| | share of samples |
| --- | ---: |
| `kernel/` — `Term`/`Formula` construction, `open`/`close`, `PartialEq`, `Thm` rules, `Rc` teardown | **47.40 %** |
| glibc `malloc`/`free` | **44.02 %** |
| `derived/` — the rule combinators | 5.96 % |
| **`mini/` — the type checker itself** | **1.58 %** |
| `nanoda_lib` (the hash-consed arena) | 0.39 % |

**`mini` spends about 2 % of its run doing Lean type theory and about 93 %
building and tearing down TG kernel objects.** These are self times, so they
attribute a call into `kernel::Term::new` to `kernel/` and not to the `mini/`
line that made it — which is exactly the split wanted here, since the question
is whether the reduction strategy or the derivation machinery is the cost.

**And it cross-checks against the reference.** `mini/` plus the arena is 1.97 %
of `p1`'s 2.999 T, i.e. **≈ 59 G instructions of Lean-side work** — against
`lean-mini-kernel`'s **18.3 G** for the whole file, in Lean, with owned de
Bruijn terms and no hash-consing. Same order of magnitude, from a completely
independent direction. The 164× is not in the type checking.

### 2.5 What the reference does with the whole residue

`work/p_residue.ndjson` — `scripts/nat-reach.py --write` over `init-prelude`,
pool-pruned per §1.1 — is exactly the workload `PRELUDE-COST.md` and
`NAT-REPRESENTATION.md` §1.3.4 measure `mini` on: 1 248 declaration lines,
1 245 declarations, which is the number both checkers report.

| | `lean-mini-kernel` | `mini` (`NAT-REPRESENTATION.md` §1.3.4, cited) |
| --- | ---: | ---: |
| outcome | **accepted 1 245, rejected 0, 0 skipped** | **`SIGABRT` inside declaration 232** |
| instructions | **805 127 432 383** | 21.71 T, to the abort |
| peak RSS | **73 920 kB** | 10 GB |

**27× the instructions to get 18.6 % of the way, and 135× the memory.**
Unattended, under a 16 GB cap, in **49.7 s** of wall clock.

### 2.6 Two lines of the gap, priced

`checker/src/main.rs` links mimalloc as the binary's `#[global_allocator]` and
carries the measurement that put it there — glibc 41.92 s, jemalloc 33.96 s,
mimalloc 30.25 s on `init-prelude`, −28 %. `mini/src/main.rs` has no
`#[global_allocator]` and runs on glibc, which §2.4 says is 44.0 % of its
samples. Adding the same two lines to `mini` (scratch, reverted; separate
`CARGO_TARGET_DIR`):

| `d8c027f`, `release`, pruned | glibc | mimalloc | |
| --- | ---: | ---: | ---: |
| `p1` instructions | 2 998 879 824 804 | **2 173 504 088 058** | **−27.5 %** |
| `p1` peak RSS | 87 436 kB | 83 940 kB | −4.0 % |
| `p1` conversions `proved` / `gapped` | 5 555 200 / 0 | **5 555 200 / 0** | — |
| `nc` instructions | 6 221 443 322 806 | **4 502 895 768 956** | **−27.6 %** |
| `nc` peak RSS | 81 332 kB | 78 240 kB | −3.8 % |
| `nc` conversions `proved` / `gapped` | 11 631 170 / 0 | **11 631 170 / 0** | — |
| `m1` instructions | 10 333 463 323 859 | **7 303 459 276 217** | **−29.3 %** |
| `m1` peak RSS | 169 744 kB | 157 784 kB | −7.0 % |
| `m1` conversions `proved` / `gapped` | 31 698 088 / 22 | **31 698 088 / 22** | — |

Three closures, **−27.5 %, −27.6 % and −29.3 %**, against
`checker/src/main.rs`'s own −28 % on `init-prelude`. Every conversion and gap
count is identical to the digit, so nothing about what the run *does* has
changed.

**This is also a confound in the `nanoda` columns of §2.1** — `nanoda_bin`
links mimalloc and `mini` does not — and it is the only one this study found.
It is worth about 1.4× of a 77–302×.

## 3. `checker/`, on both axes

`nanoda_bin` on the unpruned `init-prelude`, with the flags
`checker/tests/corpus.rs` and `scripts/mini-vs-nanoda.sh` use — `nat_extension`
and `string_extension` on, all axioms permitted:

| | plain | `--features tg` |
| --- | ---: | ---: |
| declarations | 2 059, no errors | 2 059, no errors |
| instructions | **1 530 921 071** | **197 986 266 638** |
| peak RSS | 18 864 kB | **328 036 kB** |
| kernel `Thm`s derived | — (`NullCertifier`) | **149 682** |
| gaps | — | **15 423** |

Per closure, `--features tg`, derived / gaps: `m1` 3 470 / 241; `p1` 1 311 /
34; `nc` 2 289 / 93; `bvpair` 4 718 / 224; `modlt` 12 589 / 1 949.

The plain column corroborates against a third party: the arena's own
`init-prelude` row for `nanoda` is **145 ms / 8.3 MB**, and this run's wall
clock is 0.15 s. (Its 18.9 MB against the arena's 8.3 MB is mimalloc's arena,
not work.)

**That is the whole axis distinction in two numbers.** `checker/` accepts
`init-prelude` for 1.53 G and certifies 90.7 % of its own obligations for
198 G. `mini` certifies 100 % of its own and does not finish. The acceptance
axis is not where the goal is stuck.

## 4. What the arena's `mini` ❌ actually is

Read off `arena.lean-lang.org/checker/mini/`, `/test/mathlib/` and
`/test/init-prelude/` rather than inferred from the cross:

* `mathlib`: **🚫 Declined, exit 2, 0 ms, 0 B — "Declined via the `declines`
  field in the checker configuration; the checker was not run."** The same
  non-result covers `cedar`, `cslib`, `init`, `std` and **`init-prelude`**;
  `evmlean`, `rpylean` and `nyaya` carry an identical 0 ms / 0 B row on
  `mathlib`.
* Where upstream `mini` *is* run at size: `perf/shift-cascade` **👍 accepted,
  573 ms, 74.6 MB**; `perf/app-lam` 💥 at the 30 s timeout; `perf/grind-ring-5`
  declined on the literal cap.
* Its scored record is 97/100 completeness, 56/56 soundness, 135/136 tutorial.

**The arena says nothing about whether this design can do `init-prelude`.
§2.5 does, and the answer is yes.** The 22.1 m / 7.9 GB `nanoda` mathlib row is
real and is not in question; the `mini` cross beside it is a configuration
entry.

## 5. Can `lean-mini-kernel` get through `init-prelude`? Two answers

**The raw file: no — for a documented feature gap, not a performance one.** It
declines at the parser after 293 933 532 instructions:

> `Declinig to handle due to parse error: The mini kernel does not support nat
> literals larger than 10`

Its README lists that under "what's (intentionally) missing", beside mutual
inductives, nested inductives, string literals and lazy unfolding.
`init-prelude` carries literals up to `18446744073709551616`.

**The residue — that file with those declarations removed, which is the
workload `mini` is actually measured on: yes.** §2.5: all 1 245, 805 G, 74 MB.

Which is the honest form of the answer. The reference cannot read
`init-prelude` because of a feature `mini` has and it does not; on everything
`mini` is actually asked to do, it is 27–302× cheaper.

## 6. What was not measured, and why

* **`mini`'s acceptance and interpretation passes were not priced apart here.**
  A scratch probe handing `Ledger::run` an empty schedule was built and
  discarded: the schedule is the σ-instantiation map, not the interpretation
  gate, so the run still interpreted and the number measured nothing.
  `PRELUDE-COST.md` §1's 1.3 % / 98.7 % split is used as given.
* **`lean-mini-kernel` produces no evidence at all.** It bounds the
  *type-checking* half of `mini`'s job and nothing else, which is why the claim
  here is stated narrowly: the excess is on the certified path. **How much of a
  77–302× a genuinely gapless certificate is entitled to is not measured by
  anything in this document**, and it is the obvious next question.
* **No full `init-prelude` run of `mini` was taken.** Three seats had priority;
  `NAT-REPRESENTATION.md` §1.3.4's 21.71 T / 10 GB / declaration 232 is cited.
* **The `bvpair` and `modlt` `mini` rows are `15c63ad`'s**, `test` profile
  against this study's `release`; the §2.3 ratios for those two rows carry that
  difference.
* **`lean-mini-kernel`'s step count was not measured.** It has no counter and
  none was added, so §2.3's right-hand column is a per-unit price and its
  closing inference — that 1 078 instructions per `mini` conversion is too few
  for the reference to be taking 31.7 M reduction steps — is a plausibility
  argument about a substituting kernel, not a measurement. Adding a counter to
  the reference is one afternoon and would settle how much of the 302× is extra
  steps and how much is a dearer step.
* **`nat_extension` cannot be switched off for a control** — nanoda hard-errors
  on a literal it is not permitted to read — so its columns include the literal
  extension. `PRELUDE-COST.md` §2.4 argues it has nothing to fire on in these
  closures (every numeral in reach is `0`, `1` or `2`), and `lean-mini-kernel`
  has **no** native `Nat` at all by its own README, so the comparison that
  carries the verdict is unaffected either way.
* **§2.4's profile is one closure at 99 Hz with no call graph.** It attributes
  self time to symbols and cannot say which caller drove them; the `beta_premise`
  and `def_eq_ev` attribution in the verdict is `CERTIFYING-OVERHEAD.md`'s
  counter-based finding, not this profile's.
* **`scripts/prune-pool.py` has no test of its own.** §1.1 is its whole
  validation: the pruned file must draw the same verdict, declaration count and
  conversion count as the unpruned one, on both engines.

## 7. How to reproduce

```bash
# the reference
git clone https://github.com/nomeata/lean-mini-kernel        # ef7ade0
cd lean-mini-kernel && elan run leanprover/lean4:v4.28.0 lake build

# the closures
python3 scripts/decl-closure.py vendor/arena-tests/good/init-prelude.ndjson \
        work/f_m1.ndjson List.get.match_1
python3 scripts/prune-pool.py work/f_m1.ndjson work/p_m1.ndjson
python3 scripts/nat-reach.py vendor/arena-tests/good/init-prelude.ndjson \
        --write work/residue.ndjson
python3 scripts/prune-pool.py work/residue.ndjson work/p_residue.ndjson

# the three checkers, same file
( ulimit -v 8000000; perf stat -e instructions \
    ./target/release/mini --no-modelgen --verbose work/p_m1.ndjson )
( ulimit -v 8000000; perf stat -e instructions \
    .lake/build/bin/mini-kernel work/p_m1.ndjson )
( ulimit -v 8000000; perf stat -e instructions \
    ./target/release/nanoda_bin work/cfgp_m1.json )    # cfg per scripts/mini-vs-nanoda.sh
( ulimit -v 8000000; perf stat -e instructions \
    ./target-tg/release/nanoda_bin work/cfgp_m1.json ) # cargo build --release --features tg

# §2.4 and §2.6
perf record -F 99 -o work/p1.perf ./target/release/mini --no-modelgen work/p_p1.ndjson
perf report -i work/p1.perf --no-children --percent-limit 0.7 --stdio
#   then add `mimalloc = "0.1"` to mini/Cargo.toml and the two
#   `#[global_allocator]` lines of checker/src/main.rs to mini/src/main.rs
```

Sources: §1.1, §2.1, §2.3, §2.4, §2.5, §2.6, §3, §5 — runs taken in this study,
commands above; §2.2 — the same runs on `0260925`; the † rows and §2.5's `mini`
column — `15c63ad` and `NAT-REPRESENTATION.md` §1.3.4, cited and not
re-derived; §4 — `arena.lean-lang.org`, read 2026-08-09; the `beta_premise` /
`def_eq_ev` mechanism and the 97.8 % — `CERTIFYING-OVERHEAD.md`, with both code
sites re-checked at `d8c027f`.
