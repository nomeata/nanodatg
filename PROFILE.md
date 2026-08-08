# Where the minutes go — the acceptance axis, profiled against two references

*2026-08-08. A measurement study, not a redesign. The question, in the owner's
words: "I expect such small declarations to pass in seconds, not minutes!" —
and the four candidate causes to discriminate: (1) the type checker design,
(2) the certification algorithm, (3) the `kernel/` term representation,
(4) missing caching. Every number below was taken in this repository during
this study, on `origin/master` at `9a8702f`, under the `test` profile
(`opt-level = 1`, `debug-assertions = on`, `debuginfo = line-tables-only`),
each run capped at `ulimit -v 4 GB`. The instrumentation is
`scripts/profile-probe.diff`, applied to a scratch worktree and not landed.
§9 names what was not measured. Nothing here changes behaviour.*

## Verdict

**Cause (4), missing caching, with (1) as its enabling condition. Not (2), and
not (3).**

The 91.1 s the brief attributes to "generating the tower and `kernel::add`" is
**100.0% `kernel::add`** — tower *generation* measures `0.000 s` in all nine
tower rows (§2). It is therefore mini's own Lean-level type checker, on a path
where `Checker::new` sets `th: None` and **no `Interp`, no `kernel::Term` and
no `kernel::Thm` is constructed at all**. Certification cannot be the cause of
a cost that is paid before certification starts, and the TG term
representation cannot be either.

What that path does instead is ask `infer_type` **285 922 406 times** for one
23-declaration tower whose whole vocabulary is **9 561 distinct expressions**
— a directly measured **43 000× duplication** of expression construction
(§4), against `APP-SPINES.md`'s HyperLogLog estimate of 5–49× on the
certified side. On the acceptance axis mini has **no live cache whatsoever**:
`wt_memo` is keyed on a `Term` that does not exist there, and
`Checker::frames` — the memo that took `nested_model` from 8m08 to 1m48 on the
certified path — is switched off by one line, `frame_put`'s
`if t.ev.thm().is_none() { return }`, because acceptance-only evidence is
always a `Gap`. Measured: **0 hits in 285 922 406 lookups**. It still computes
the key: `hash_expr` walks the whole expression and `format!`s every universe
level, and that key-for-a-memo-that-stores-nothing is **34% of the entire run**
(§3, §5).

Removing the gate — nothing else, and no change to any verdict or ledger
line — takes the `DTree` tower from **91.9 s to 8.8 s (10.5×)**; adding a
non-allocating key makes it **7.25 s (12.7×)**; at `opt-level = 3`, **6.33 s
(14.5×)** (§5). `mini/tests/nested.rs`, the CI binary this is about, goes
**309.50 s → 124.21 s with all fifteen tests still passing**. The empirical cost is **n^2.20 ± 0.12** in tower expression
nodes (R² = 0.985, seven towers over a 4.5× size range); with the memo live it
is **n^1.98 ± 0.10** — the memo removes a factor of ten and about a fifth of an
exponent, and what remains is quadratic (§6).

**The reference comparison settles the framing.** On the *identical* export
`nested_model.ndjson` — the `Tree` tower, hand-written, 40 declarations —
Lean 4.32.2 elaborates *and* kernel-checks the source in **~0.05 s** over its
own 0.10 s startup; `nanoda_lib` (the fork mini's `checker/` is, running the
same algorithm with `NullCertifier`) reports **`Checked 40 declarations` in
under 0.01 s**; mini's acceptance axis takes **3.90 s**; mini certified takes
**97.0 s**. So mini's acceptance is ~400× nanoda and ~80× Lean's marginal cost
on the same declarations — and the reason is visible in §7's table: nanoda
hash-conses every expression, carries free variables *in* the term, and keeps
five `ExprPtr`-keyed caches (infer ×2, whnf ×2, a union-find for def-eq, plus a
failure cache) — **and the fork keeps all five while carrying certificates in
them**. Certification did not cost mini those caches. **Mini never had them**:
it is a fidelity port of `MiniKernel/Kernel.lean`, which MINI-DESIGN.md:21–27
records, marked *[read, all of `Kernel.lean`]*, as having "no state, no caches,
no hash-consing; plain owned de Bruijn expressions … a local context that is
literally a telescope … whnf as a stack machine with full eager delta". The
owner's hypothesis — *the certifying design cost us the kernel's caches* — is
**refuted in its strong form and confirmed in one narrow, one-line, entirely
fixable form**: the certifying design did not prevent the caches, but it is
what disabled the single cache that was rebuilt, on the axis that has no
certificates to store.

**And mini's checker is not slow in general.** Zone A over the whole 91-export
tutorial corpus is **1.38 s** total. The minutes are one *shape*: the ι
theorems of the generated isomorphism tower, whose proofs are `Eq.rec`
transport folds over recursor applications. Two or three declarations per
tower are ~95% of each tower's cost.

---

## 1. The reference comparison, first, because it decides the framing

`mini/tests/fixtures/nested_model.lean` is the `Tree` isomorphism tower written
by hand — the same development `mini::nested_ev::iso` generates. It exists as
Lean source *and* as an export, so all four implementations can be pointed at
the same declarations.

| implementation | what it does | `nested_model` |
| --- | --- | ---: |
| Lean 4.32.2 (`lean nested_model.lean`) | parse + elaborate + kernel-check | **0.15 s** wall; **~0.05 s** over the 0.10 s empty-`prelude` baseline |
| `nanoda_bin` (`checker/`, the fork, built without `--features tg`) | acceptance; the `Certifier` interface is in place and is `NullCertifier` (`checker/src/certify.rs:32`) | **< 0.01 s**, `Checked 40 declarations with no errors`, 3.2 MB peak RSS |
| mini zone A (`kernel::add`, `th: None`) | acceptance | **3.90 s** |
| mini zone A + the two §5 changes | acceptance | **0.70 s** |
| mini, full run (`--mutual --nested`) | acceptance + TG certification | **97.0 s**, 686 MB RSS |

*Lean: `/usr/bin/time lean mini/tests/fixtures/nested_model.lean`, best of
three, against three runs of a one-line `prelude` file (0.31 / 0.16 / 0.10 s —
the spread is page cache, so 0.10 s is the startup floor and ~0.05 s is an
upper bound on the marginal cost). nanoda: `target/debug/nanoda_bin` on a
config naming the same `.ndjson`, the flags `scripts/mini-vs-nanoda.sh` uses.
mini zone A: `examples/tower`, which loads the export and calls
`mini::kernel::add` on each declaration, timing each. mini full:
`./target/debug/mini --acceptance-only --mutual --nested` — note that
`--acceptance-only` is a **reporting** flag, it suppresses exit code 4 and does
not skip certification.*

Two consequences, both load-bearing:

* **The work is not intrinsically hard.** Two independent implementations of
  the same task finish it in under a tenth of a second. mini's acceptance axis
  is ~400× nanoda and ~80× Lean's marginal cost. This is an implementation
  gap, not a recalibration of the owner's expectation.
* **The gap is not certification's.** nanoda's number is for the same
  algorithm with no proofs produced, which is the right control for mini's
  *acceptance* axis — and that is the axis costing 3.90 s. The stronger claim,
  that a certifying checker can keep the caches, is not this row's: it is §7's,
  and it is read off the fork's source, where all five caches carry
  certificates in their values.

**Counter-check, so the comparison is not read too widely:** over the 91
`good/tutorial` exports, mini's zone A costs **1.38 s in total** and nanoda's
is under 0.01 s per file. mini's acceptance checker is fine on ordinary
declarations. What is slow is one generated shape.

## 2. The split the brief asked for — generation, acceptance, certification

The brief's "generating the tower and `kernel::add`" is a composite. Split it
with a probe that times every **outermost** `kernel::add` (an RAII guard with a
depth counter, so nested `add`s are not double counted) and subtracts:

| fixture / declaration | tower nodes | `iso` total | of which `kernel::add` | of which generation |
| --- | ---: | ---: | ---: | ---: |
| `nested_shapes` / `PTree` | 1 713 | 2.867 s | 2.867 s | **0.000 s** |
| `nested_iota` / `Tree` | 2 712 | 10.40 s | 10.40 s | **0.000 s** |
| `nested_shapes` / `BTree` | 3 339 | 16.93 s | 16.93 s | **0.000 s** |
| `nested_iota` / `PT α` | 3 940 | 26.86 s | 26.86 s | **0.000 s** |
| `nested_iota` / `BTree` | 5 531 | 38.93 s | 38.93 s | **0.000 s** |
| `nested_shapes` / `DTree` | 7 583 | 91.06 s | 91.06 s | **0.000 s** |
| `nested_deep` / `DTree` | 7 765 | 91.86 s | 91.86 s | **0.000 s** |

**Generation is free. 100.0% of the tower cost is type checking.** The brief's
caution was right to raise the question and wrong about the answer: the
composite was almost exactly the checking cost. (These reproduce
MEASUREMENTS.md's uninstrumented table — 10.3 / 38.0 / 26.5 / 91.1 / 2.8 /
89.3 / 16.6 — row for row, so the probe costs a few percent at most.) Every
tower figure in this document is a single run; repeated runs of the same tower
on this machine vary by 2–3% (`Tree` was 10.40, 10.54, 10.58, 10.67 s across
four runs), so no ratio below should be read to better than that.

Inside a tower, **two or three declarations are ~95% of it**. `Tree`, all
fifteen:

| declaration | nodes | `kernel::add` | `infer_type` entries |
| --- | ---: | ---: | ---: |
| `Tree._model.iota_1_1` | 800 | **6.147 s** | 19 870 633 |
| `Tree._model.iota_0_1` | 626 | **4.048 s** | 13 143 821 |
| `Tree._model.rec_1` | 264 | 0.069 s | 224 588 |
| `Tree._model.packUnpack_0` | 158 | 0.041 s | 132 780 |
| `Tree._model.unpackPack_0` | 146 | 0.038 s | 121 912 |
| `Tree._model.rec_0` | 218 | 0.033 s | 107 722 |
| `Tree._model.iota_1_0` | 152 | 0.012 s | 38 344 |
| `Tree._model.iota_0_0` | 146 | 0.011 s | 35 571 |
| `Tree._model.congrPack_0` | 92 | 0.004 s | 12 416 |
| `Tree._model.unpack_0` | 50 | 0.0002 s | 762 |
| `Tree._model.pack_0` | 30 | 0.0002 s | 650 |
| `Tree._model.0` (the block) | 12 | 0.0001 s | 156 |
| `Tree._model.ctor_1` | 14 | — | 44 |
| `Tree._model.self`, `ctor_0` | 2, 2 | — | 4, 4 |

800 expression nodes cost **24 838 `infer_type` calls per node**; the recursor
type, 264 nodes of ordinary Lean, costs 851. The expensive ones are the ι
theorems whose proofs fold `Eq.rec` over `unpackPackᵢ`.

**Acceptance versus certification, end to end**, on the three nested fixtures.
Zone A is the towers plus the export's own declarations; the remainder of the
full run is TG certification:

| fixture | zone A | full run | certification share |
| --- | ---: | ---: | ---: |
| `nested_model` (no nested declaration, so no tower) | 3.90 s | 97.0 s | **96%** |
| `nested_iota` `--nested` (three towers) | 76.2 + 0.43 s | 183.2 s | **58%** |
| `nested_deep` `--nested` (one tower) | 91.9 + 0.001 s | 98.7 s | **7%** |

So the brief's framing question — *"if acceptance alone is minutes, (2) is not
the primary cause"* — has a workload-dependent answer, and both halves are
real. On a fixture with a nested declaration the acceptance tower is the
dominant term; on one without, certification is. **The two halves have the same
diagnosis** (§4, §7), which is why one fix moves both.

## 3. The profile

`perf record -F 499` over `examples/tower nested_deep` (91.9 s, 45 K samples,
0 lost), flat, self time. Symbols merged by hand where a name repeats:

| what | share |
| --- | ---: |
| **SipHash `Hasher::write`** (two inlining copies) | **28.47%** |
| `hash_expr::go` + `hash_expr` | 7.02% |
| `Rc<Name>::hash` + `hash_one::<&Name>` + `DefaultHasher::write` | 5.47% |
| `core::fmt::write` + `String::write_str` (the `format!("{u}")` in `hash_expr`) | 1.68% |
| — **subtotal: computing memo keys and hashing names** | **≈ 42.6%** |
| `Checker::infer_type` | 7.34% |
| `Checker::whnf_conv_uncached` | 4.96% |
| `Checker::assert_def_eq_as` | 3.30% |
| `Checker::whnf_typing` | 2.24% |
| `malloc` / `free` / `_int_malloc` / `_int_free_chunk` / `RawVecInner::deallocate` | ≈ 6.2% |
| `subst_level`, `substs`, `app_n`, `has_bvar_in_proj`, `Level::subst` | ≈ 4.6% |
| `Checker::is_prop`, `const_evidence`, `lookup`, `def_eq_struct` | ≈ 3.7% |

A `--call-graph dwarf` run over `nested_iota` (15 K samples) attributes 28.11%
children to `infer_type`, 14.44% to `hash_expr` and 9.06% to hashing `Name`s
— consistent, and it is the same story: **the largest single line item in an
acceptance run is computing the key of a memo that never stores anything.**

That is confirmed directly rather than left to the profiler. `MINI_NO_HASH=1`
replaces the key with the constant `0`, which is sound whenever the frame map
is empty — which on the acceptance axis it always is:

| tower | baseline | key not computed | removed |
| --- | ---: | ---: | ---: |
| `Tree` | 10.67 s | 6.97 s | 34.7% |
| `PT α` | 26.86 s | 19.18 s | 28.6% |
| `BTree` | 38.93 s | 24.24 s | 37.7% |
| `DTree` | 91.86 s | 60.68 s | **33.9%** |

## 4. Allocation and duplication, measured directly rather than estimated

Two populations, and they are different populations. `APP-SPINES.md`'s
232.8 M figure is **`kernel::Term`**, which the acceptance axis does not build
at all.

**Acceptance axis — `mini::expr::Expr`.** Every `Rc<Expr>` construction in the
crate was routed through one function and counted; `MINI_INTERN=1` then makes
that function a hash-cons table (`O(1)` key from the children's cached hashes,
confirmed by `==`, the table holding a strong `Rc` so a pointer can never be
reused). On the `DTree` tower:

* **411 015 702 `Expr` constructions**
* **9 561 distinct expressions** — an intern-table count, not an estimate: a
  hash collision is resolved by structural `==`, so the number is exact. It is
  process-cumulative, which for this fixture means the tower plus the parse and
  `kernel::add` of a five-declaration export
* → **43 000× duplication**

The entire 91.9-second run builds fewer than ten thousand distinct
expressions. And `infer_type` is entered 285 922 406 times, so it is asked
about at most 9 561 distinct expressions — **≥ 29 900× duplication in the
question being asked**, before the telescope is considered.

**Hash-consing by itself buys nothing, and that is worth knowing.**
`MINI_INTERN=1` alone: 91.86 s → **105.15 s** (a 14% *regression* — the intern
lookup costs more than `Rc::new`, and nothing downstream exploits the pointer
identity it establishes). With the §5 changes: 7.25 s → 7.45 s. Interning is an
**enabler** for an O(1) cache key, not a saving; `Expr` equality was already
not a cost (22 837 `PartialEq` node visits on the whole `Tree` tower, because
`Rc<T: Eq>` short-circuits on pointer identity in std).

**Certification axis — `kernel::Term`.** `Term::new` already computes an O(1)
cached hash from its children's, so distinct structures can be counted exactly
rather than HLL-estimated. On a full certified `nested_model` run:

* **675 664 357 `Term::new` calls**
* **41 052 776 distinct cached hashes**
* → **16.5×** duplication

against `APP-SPINES.md` §3.5's HLL estimate of **5.3×** for the same fixture.
The direct count says duplication on this workload is **three times worse**
than the estimate; the allocation total has also fallen (1 087.5 M → 675.7 M)
as the proof-irrelevance gate and the frame memo landed. Distinct is counted by
64-bit hash, so collisions can only make the true distinct count higher and the
true ratio *lower*; and it is distinct-ever, not distinct-live. The probe's
mutex costs ~22% (118.1 s against 97.0 s uninstrumented).

RSS is not a problem anywhere on the acceptance axis: the 91.9 s `DTree` tower
peaks at **6.8 MB**. This is pure CPU.

## 5. What caching is worth, measured

Four one-flag experiments, none of which changes a verdict, a declaration
count, or a ledger line (checked: every run prints the same `accept … 25
declarations uncertified: 2 const typings, 41 conversions` etc.).

* **A — `MINI_FRAME_ALL=1`.** Delete `frame_put`'s
  `if t.ev.thm().is_none() { return }`. That gate is a *diagnostic* policy —
  its comment says caching a `Gap` "would keep it out of `blocker`'s trail on
  every call but the first" — not a soundness condition; `Frame`'s soundness
  argument is about the telescope being fixed and says nothing about evidence.
* **G — `MINI_FASTHASH=1`.** Replace `hash_expr`'s SipHash-plus-`format!` with
  a non-allocating structural mixer. Same information, no `String`.
* **B — `MINI_WHNF_MEMO=1`.** A frame-local `whnf` memo for acceptance-only
  calls, keyed and scoped exactly like the `infer_type` one.
* **H — `MINI_INTERN=1`.** Hash-cons `Expr` (§4).

| configuration | `Tree` | `PT α` | `BTree` | `DTree` | vs. baseline |
| --- | ---: | ---: | ---: | ---: | ---: |
| baseline | 10.67 | 26.86 | 38.93 | **91.86** | 1× |
| G (cheap key) | 9.13 | 22.33 | 32.35 | 73.72 | 1.25× |
| **A (frame memo live)** | 1.34 | 2.81 | 4.15 | **8.76** | **10.5×** |
| **A + G** | 1.12 | 2.38 | 3.46 | **7.25** | **12.7×** |
| A + G at `opt-level = 3` | 0.98 | 2.06 | 3.03 | **6.33** | **14.5×** |
| H (hash-consing alone) | — | — | — | 105.15 | 0.87× |
| H + A + G | — | — | — | 7.45 | 12.3× |
| **B (whnf memo alone)** | 16.93 | 43.86 | 62.16 | **145.44** | **0.63×** |
| A + B | 1.90 | — | — | 12.46 | 7.4× |

Three findings in that table.

**A is the lever.** `infer_type` entries on `DTree` fall 285 922 406 →
20 266 178 (14.1×) for a frame *hit rate* of only 30.6% — because each avoided
re-inference avoids a whole subtree. The speedup **grows** with tower size
(7.3× at `PTree`, 10.5× at `DTree`), which is what removing a superlinear term
looks like.

**B is a regression, and the reason is the key.** The whnf memo hits 54% of the
time and still costs 58% more, because `hash_expr` on the subject plus the
`==` confirmation costs more than the reduction it saves: `HASH_NODES` goes
1.28 G → 1.98 G and the `format!` count 85 M → 390 M. *A cache whose key costs
`O(size)` can be net-negative even at a 54% hit rate.* This is the sharpest
available argument for pointer-identity keys, i.e. for hash-consing — not as a
saving in itself (H shows it is not) but as what makes further caches viable.

**Even after A + G, key computation is still ~11.5% of the run** (`fast_name`
6.65%, `fast_hash_expr::go` 4.90%, `perf -F 999` over all three fixtures at
A+G), plus ~10% in `HashMap` hashing. That is the headroom an `ExprPtr`
representation would recover.

**End to end, on the full certified runs** (same binary, same flags, identical
output):

| fixture | baseline | A + G | |
| --- | ---: | ---: | ---: |
| `nested_deep --mutual --nested` | 98.67 s | **10.22 s** | 9.7× |
| `nested_iota --mutual --nested` | 183.15 s | **109.99 s** | 1.67× |
| `nested_model --mutual --nested` | 97.00 s | 93.46 s | 1.04× |

`nested_model` barely moves because it has no tower: it is 96% certification,
where the frame memo was already live. `nested_deep` is 9.7× because it is 93%
tower.

**And the CI test binary itself**, which is what `#110` is about:

| | wall | tests |
| --- | ---: | --- |
| `mini/tests/nested.rs`, baseline | **309.50 s** | 15 passed |
| `mini/tests/nested.rs`, `MINI_FRAME_ALL=1 MINI_FASTHASH=1` | **124.21 s** | 15 passed |

2.49×, with every assertion in the file — including the export oracle and the
generated-recursor comparison — still passing. It runs three times per CI run,
so that is ~9 minutes.

**The build profile is not part of the story, and `opt-level = 3` now builds.**
`CARGO_PROFILE_TEST_OPT_LEVEL=3 CARGO_BUILD_JOBS=1 cargo build -p mini` **succeeds**
in 3 m 27 s with a peak `rustc` RSS of **1.25 GB** — nowhere near the ceiling
the `Cargo.toml` comment records. The likeliest explanation is in that comment
itself: the SIGKILL it records was at `debuginfo = 2`, which `70409b7` has
since dropped to line tables. The speed it buys is small — `DTree` 91.86 →
87.53 s (−4.7%) at baseline, 7.25 → 6.33 s (−12.7%) at A+G.

## 6. Asymptotics, and the empirical exponent

Time is **linear in `infer_type` entries** at 3.1–3.2 M/s, stable to ±10% over
a 30× range of workload size (`PTree` 3.17, `Tree` 3.18, `nsBTree` 3.17,
`PT` 3.70, `BTree` 3.03, `nsDTree` 3.08, `ndDTree` 3.11 M entries/s). So the
scaling question is entirely "how many times is `infer_type` entered", and
wall clock and entry count give the same exponent.

Least squares in log-log over the seven towers (§2), size axis = tower
expression nodes, 1 713 → 7 765 (4.5×):

| | exponent | R² |
| --- | ---: | ---: |
| baseline, seconds | **2.20 ± 0.12** | 0.985 |
| baseline, `infer_type` entries | 2.18 | 0.973 |
| A (frame memo live), seconds | **1.98 ± 0.10** | 0.987 |
| A, `infer_type` entries | 1.99 | 0.981 |

Robust to leaving out the two largest towers (2.28 ± 0.23 on the remaining
five) and the largest single one (2.23 ± 0.15). Per-node entry counts, which is
the same fact stated without a fit: 5 303 / node at `PTree`, 12 422 at `Tree`,
16 066, 25 230, 21 308, 37 032, 36 822 at `ndDTree` — a factor of 6.9 across a
factor of 4.5 in size.

**So: the cost is ~n^2.2 in tower nodes, the frame memo takes it to ~n^2.0 and
divides the constant by ten, and n² is what is left.** The recurrence that
makes it so is not new — it is `#101`'s, on the other axis. `infer_type`'s
`App` arm infers `f`, `whnf_typing`s its type, infers the argument, and then
`assert_def_eq_as` compares the argument's type against the domain; the
comparison reduces both sides with `whnf`, whose `Const` arm performs **full
eager delta** with no lazy-delta step and no reducibility hints
(`kernel.rs`, whnf's `Const` arm: *"Mini-lean's whnf is eagerly unfolding, so
nanoda's `lazy_delta_step`/`recall_eq` machinery has no counterpart"*), and
reduction re-enters `infer_ty` at the K-rule. Nothing between those steps
remembers anything. On an ι theorem whose proof is an `Eq.rec` fold over a
recursor application, every level of the fold re-walks everything under it.

## 7. The caches, mini against its two references

The single highest-value table, and the one that answers the owner's
hypothesis. Everything in the nanoda columns is cited to a line in this
repository; the Lean column is marked *unverified* because the Lean 4
toolchain in this environment ships `src/lean/kernel` **empty** — only the
Lean-side library sources — so the C++ kernel's caching could not be read, and
this study will not assert it from memory. Lean's 0.05 s in §1 is the only
Lean-side evidence offered.

| | Lean 4 kernel | `nanoda_lib` upstream (`vendor/`) | `checker/` (the fork, certifying) | **mini** |
| --- | --- | --- | --- | --- |
| expressions hash-consed | *unverified* | **yes** — `alloc_expr` dedups into the DAG's `IndexSet`, `util.rs:394` | same | **no** — `Rc::new` per node, `expr.rs`, and 43 000× duplication measured (§4) |
| free variables live *in* the term | *unverified* | **yes** — `Expr::Local { id: FVarId }`, `expr.rs:96` | same | **no** — pure de Bruijn, ambient `lenv` telescope (a deliberate departure, `expr.rs` header) |
| `infer` cache | *unverified* | **yes ×2** — `infer_cache_check`, `infer_cache_no_check`, `ExprPtr`-keyed, `util.rs:819–820` | **yes, carrying the evidence** — value is `(ExprPtr, Y)`, and `util.rs:899–911` argues why a conditional typing is safe there | frame-local, telescope-scoped, **and disabled whenever the evidence is a `Gap`** — measured **0 hits / 285 922 406 lookups** on the acceptance axis |
| `whnf` cache | *unverified* | **yes ×2** — `whnf_cache`, `whnf_no_unfolding_cache`, `util.rs:821–822` | **yes, carrying the reduct's steps** — `Reduct<'t, C>`, `util.rs:914–922` | **none** (`wt_memo` is keyed on a `Term`, which does not exist on this axis) |
| def-eq cache | *unverified* | **yes** — `eq_cache: UnionFind<ExprPtr>`, `util.rs:823` | **yes, a proof-producing union-find** — every union edge carries its certificate, `util.rs:923–927` | **none** |
| congruence-failure cache | *unverified* | **yes** — `failure_cache`, `util.rs:825` | same | **none** |
| lazy delta / reducibility hints | *unverified* | **yes** — `lazy_delta_step` | same | **none** — full eager delta, by fidelity to mini-lean |

**Read the fork's column again.** `checker/` is a *certifying* checker and it
keeps every one of nanoda's caches, with certificates in the values. So the
hypothesis "a cache that must also carry a certificate is much harder to key,
and that is why mini lost its caches" is **false as stated**: this repository
contains a working counterexample. What makes it work there is the
representation — an `ExprPtr` into a hash-consed DAG, with free variables
named inside the term, so *the key alone denotes the judgement*. Mini's de
Bruijn expression plus ambient telescope does not: two openings of one binder
give the same `Expr` and different judgements, which is exactly why
`MINI-HANDOFF.md` §40's three memo attempts failed and why `Checker::frames`
had to be made telescope-scoped instead.

**Where the hypothesis is right, narrowly and expensively.** The one cache
mini *did* rebuild stores a whole `Typing` — type, interpretation *and*
evidence — and `frame_put` refuses an entry whose evidence is a `Gap`. On the
certified path that costs little. On the acceptance path *every* entry is a
`Gap`, so the cache is 100% dead and its key is still paid. That is the
certifying design switching off a cache on an axis that has no certificates,
and it is §5's experiment A: 10.5×, one line.

So the correct sentence is neither of the two on offer. It is: **mini inherited
a cache-free, hash-cons-free teaching kernel by deliberate fidelity, rebuilt
one of the missing caches for the certified path, and gated that one on
evidence — leaving the acceptance path with no caches at all and the full cost
of a key.**

## 8. The four candidates, judged

**(1) Type checker design — the enabling condition, and partly deliberate.**
The acceptance axis is a faithful port of `MiniKernel/Kernel.lean`: no caches,
no hash-consing, owned de Bruijn with explicit `shift`/`substs`, an ambient
telescope, and **full eager delta with no lazy-delta step**. Every one of those
is a documented fidelity choice (MINI-DESIGN.md §0, §2), and every one of them
is a thing both references do differently. The measured consequence is ~n^2.2
and a 400× gap to nanoda. But note what is *not* implicated: `Expr` structural
equality is 22 837 node visits on a whole tower (std's `Rc<T: Eq>` already
short-circuits on pointers); term *size* is not the issue (§4 — 9 561 distinct
expressions); memory is not the issue (6.8 MB peak). The design's cost is
concentrated in "asks the same question tens of thousands of times and has
nowhere to put the answer".

**(2) Certification algorithm — not the cause of the 91 s, and it shares the
diagnosis for the 97 s.** No `Interp`, no `Term`, no `Thm` exists on the path
that takes 91.9 s: `Checker::new` sets `th: None`. On `nested_model`, where
there is no tower, certification *is* 96% of the run — but §4 measures 16.5×
`Term` duplication there and CERTIFYING-OVERHEAD.md §4 already measured 151×
duplication of α-canonical judgements and 97.8% of conversions inside a repeat.
It is the same recurrence, and `#101`'s designed fix addresses it. Nothing here
suggests certifying is intrinsically expensive: the certifying fork checks
`nested_model` in under 10 ms.

**(3) `kernel/` term representation — ruled out, twice.** It is absent from the
expensive path entirely. Where it is present, `Term` already carries a cached
hash and short-circuits equality on pointers, and its duplication (16.5×) is
three orders of magnitude below the acceptance axis's 43 000×. And the direct
experiment on the analogous Lean-side representation says interning alone is a
14% *regression* (§4). Term representation is an enabler for cheap keys, not a
cost.

**(4) Missing caching — the cause, quantified.** 0 cache hits in 285 922 406
lookups; 43 000× duplication of construction; 34% of the run spent computing a
key for a memo that never stores; and a one-line change worth 10.5×, 12.7× with
a cheap key, 14.5× at `opt-level = 3`. The remaining n^2.0 after the memo is
the *cross-opening* share — the frame dies whenever `lenv` changes, which
CERTIFYING-OVERHEAD.md §4(3) measured on the certified side as
0.66% → 56.15% distinct when the key is re-based on live scope variables. A
cache that survives an opening needs either free variables in the term (what
both references have) or the α-canonical `Sealed` key CERTIFYING-OVERHEAD.md §2
already specifies. **That, and not arity, interning, or the TG kernel, is where
the next factor lives.**

**What this is worth to CI (`#110`).** `mini/tests/nested.rs` — the binary that
runs these towers, three times per CI run — is **309.50 s baseline and
124.21 s with experiment A + G**, 15 tests passing either way. 2.49×, 185 s
saved per invocation, ~9 minutes per CI run.

## 9. Not measured

* **Lean's kernel caches.** The toolchain ships `src/lean/kernel` empty; the
  C++ was not available and is not asserted. Only Lean's wall clock is
  evidence here.
* **The rest of CI.** Only `mini/tests/nested.rs` was timed end to end
  (§5); `ci/check.sh` is ~45 minutes and was not run, because this study lands
  no behaviour change.
* **Whether the frame memo may keep `Gap` entries in production.** Experiment A
  is sound by `Frame`'s own argument and changed no output in any run here, but
  it degrades `blocker`'s first-blocker trail by construction (that is what the
  gate is for), and no one has decided what to do about that. This study lands
  no such change.
* **Hash-consing `kernel::Term`.** The distinct count was measured (§4); the
  wall-clock effect was not. The Lean-side analogue (H) says expect ~0 by
  itself.
* **The cross-opening duplication share on the acceptance axis, as a number.**
  It is bounded above by 9 561 distinct expressions against 20 266 178 post-memo
  entries (≥ 2 100×) but was not partitioned by telescope: the census the probe
  carries (`MINI_PROBE_CENSUS=1`) recomputes an `O(lenv)` hash per entry and was
  judged too slow to run at 286 M entries. It was not run.
* **`nested_iota_arm`, `transport_through_eq_rec`, the tutorial corpus at the
  certified level, `proj_reduced_carrier`.** The tutorial corpus was measured
  on the acceptance axis only (1.38 s, §1).
* **`--release` proper** (`opt-level = 3` *plus* `lto = true`, overflow checks
  on). Only `CARGO_PROFILE_TEST_OPT_LEVEL=3` was tried, which keeps
  `debug-assertions = on`.
* **`Term::new` distinct** is counted by 64-bit FNV-style hash, not by
  structure; collisions can only lower the reported duplication.

## Appendix: reproduction

```sh
git worktree add --detach WT origin/master        # 9a8702f at measurement time
cd WT && ln -s ../../vendor vendor
git apply scripts/profile-probe.diff
CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 cargo build -p mini --example tower --profile test

# §2 the split, §6 the size axis
( ulimit -v 4194304; ./target/debug/examples/tower nested_iota nested_deep nested_shapes )

# §5 the experiments (each is idempotent and changes no verdict)
for c in "" "MINI_NO_HASH=1" "MINI_FASTHASH=1" "MINI_FRAME_ALL=1" \
         "MINI_FRAME_ALL=1 MINI_FASTHASH=1" "MINI_WHNF_MEMO=1" "MINI_INTERN=1"; do
  ( ulimit -v 4194304; env $c ./target/debug/examples/tower nested_deep )
done

# §3 the profile
( ulimit -v 4194304; perf record -F 499 -o p.data -- ./target/debug/examples/tower nested_deep )
perf report -i p.data --stdio --no-children --percent-limit 0.5

# §4 the TG side
cargo build -p mini --bin mini --profile test
( ulimit -v 8388608; KERNEL_TERM_PROBE=1 ./target/debug/mini --acceptance-only --mutual --nested \
    mini/tests/fixtures/nested_model.ndjson )

# §1 the references
lean mini/tests/fixtures/nested_model.lean
cargo build -p nanoda_lib --bin nanoda_bin --profile test
./target/debug/nanoda_bin cfg.json     # see scripts/mini-vs-nanoda.sh for the flags
```

Sources for every non-derived number: §1 — `/usr/bin/time` over `lean`,
`nanoda_bin` and `examples/tower`; §2–§6 — `examples/tower`'s `ISO` /
`ADD-IN-ISO` / `PROBE` lines and `perf report`; §4's TG row — the
`TERM-PROBE` line; §7 — file and line citations inline, read in this tree.
