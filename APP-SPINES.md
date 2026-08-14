# `app` spines — the n-ary question, measured and closed

*2026-08-07. A measurement-and-design study, not a feature. The question, in
the owner's words: "In the quoted code I saw that the terms you generate
contain `app` symbols. These of course inflate the term size. Can we avoid
this, given the existing kernel interface? Or can we at least define n-ary
`app` symbols for smaller terms? Would that even help?" Everything below that
is a number was measured in this repository during this study; §7 names what
was not. Nothing was wired into the checker; the probe that produced the
numbers is `scripts/appsize-probe.diff`, applied to a scratch worktree and
discarded.*

## Verdict

**Do nothing to `app`.** The premise — that `app` spines are where term size
goes — does not survive measurement. On the corpus mini certifies (the 89
accepted `good/tutorial` exports), the `app` symbol accounts for **10.4% of
all term allocations**, **0.66% of the final stored context**, and **13.7% of
the retained term registry**; the arguments, which no arity change shrinks,
account for the rest. The heavy `nested_model` fixture — a single run with
six times the corpus's inference volume — reproduces every ratio and pushes
the arity-sensitive shares *lower* (§3.5). An n-ary `appn` — option (b) — is dead on arithmetic
alone: collapsing every maximal spine in the corpus saves **3.9% of term
allocations** (the allocations at spine depth ≥ 2) and about **0.5% of
inference** (the congruence rows), against a cost of one symbol family per
arity up to 23 plus an n-ary twin or a bridge unfold for every binary `app`
lemma in `derived/` — the same economics `dprod_universe_n.rs`'s header
already refused once. Avoiding `app` for saturated known heads — option (a) —
is already the design where the thesis mandates it (`Eq`, via `Direct`), and
extending it further is capped by the same small numbers while violating
`direct.rs`'s own documented "no fourth row" rule. What the measurements *do*
point at is (c): the checker allocates **each distinct term 5–49× over**
(workload-dependent, §3.4; no hash-consing exists — `Term::new` allocates a
fresh `Rc` unconditionally, `kernel/src/term.rs:172`), and it calls the application
typing rule **~130× per source application site** — the same re-derivation
recurrence CERTIFYING-OVERHEAD.md diagnosed, of which `app` handling is just
one visible symptom. If effort is to be spent near this question, it is
interning and the already-designed evidence-carrying fixes, not arity.

---

## 1. The premise, verified before measuring

Three checks the brief demanded, all confirmed against the code:

* **The kernel is already n-ary.** `Term::apply(f, args)` takes any argument
  vector matching the symbol's arity (`kernel/src/term.rs:188`); arity is
  per-symbol and arbitrary. "Define n-ary `app` symbols" is entirely a
  `derived/` question — one `define_abbrev` per arity would do it — and no
  kernel change is involved in any branch of this study.

* **`app` is binary because it is the set-theoretic application operation,
  not a syntactic node.** `app(f,a) = ⋃ coll(f,a)` with the unconditional
  characteristic theorem `⊢ ∀f ∀a ∀w. (w ∈ app(f,a) ↔ ∃y. (⟨a,y⟩ ∈ f ∧ w ∈ y))`
  (`derived/src/funcs/apply.rs:161,175`). `⟦f⟧` for a Lean function is a
  *curried set value* — a graph — and `f x y` interprets as
  `app(app(⟦f⟧,x),y)`: two applications of a value that exists independently
  of how many arguments follow. This is what makes "collapse the spine" a
  semantic question, not a pretty-printing one.

* **A constant's denotation is one node, not an inlined value.** `⟦c.{σ}⟧` is
  stored as a minted abbreviation symbol (`ip.abbrev`,
  `checker/src/mini/ledger.rs:836`), so a use-site spine is
  `app(app(c_sym,⟦x⟧),⟦y⟧)` — the head costs one node, the spine `n` nodes,
  and the arguments whatever they cost. The `n−1` nodes an n-ary symbol could
  remove are a minority share of the site before any argument is counted.

The sentence the owner most likely saw is INDUCTIVES.md:818 — "the checker
reads `f a b` as `app(app(⟦f⟧,⟦a⟧),⟦b⟧)` — one `app` per argument" — written
about `checker/src/tg.rs`, the superseded backend. What mini actually
*retains* looks like this (`098_natLitEq`, `--dump-theorems`):

```text
typing   ⊢ ⟦natLitEq.{}⟧ ∈ app(app(app(⟦Eq.{1}⟧, ⟦Nat.{}⟧), …), app(⟦Nat.succ.{}⟧, …))
typing   ⊢ ⟦Nat.rec.{1}⟧ ∈ f141(⟦Nat.{}⟧, ⟦Nat.succ.{}⟧, ⟦Nat.{}⟧, ⟦Nat.zero.{}⟧, dprod₀(⟦Sort 1⟧, ⟦Nat.{}⟧))
```

Both lines are real and the second is the typical one: stored types are
mostly minted fibre/nest symbols (`f141`, `dprod₀`) with no spine at all. The
first shape — a declared type that is itself an applied term — exists and is
what the count in §3 prices: 104 `app` nodes in 15,722 stored-context nodes.

## 2. What was measured, and how

Two instruments, both in `scripts/appsize-probe.diff`, neither landed:

* **A kernel probe** (worktree-only patch to `kernel/src/term.rs` /
  `thm.rs`): allocation counters per `TermData` variant, a per-allocation
  spine-depth histogram for the watched `app` symbol, HyperLogLog registers
  for distinct-structure estimates, read-only structural accessors, and one
  counter ticked at each of the five `Thm` construction sites — so
  "inferences" below means *theorems constructed*, a uniform proxy.
* **mini-side attribution** (`mini/src/termstats.rs` plus thin wrappers):
  theorem-count deltas across `Interp::dprod_app` / `cond_app` / `fs_app`
  (the application typing rules), `conv::app_cong` (application congruence),
  and `Checker::beta_evidence` (β legs); plus a walker over the final
  constant store and over the `parts` registry — every term mini built
  through `Interp::mk` and remembered. (That registry has since been deleted;
  see §3.2.)

Corpus: the 91 `good/tutorial` exports, run individually (89 accept, 2
decline), plus the `nested_model` fixture as a scale check (§3.5), debug
build, `ulimit -v 4G`. **`init-prelude` cannot be measured at
the TG level** — mini declines it (nat literals over 10,
`checker/src/mini/convert.rs:668`) — so it appears only in the export-level numbers,
which is a real limitation (§7). Per-file fixed cost of building the prelude
(measured on the near-empty `001_basicDef`): 91,377 theorems, 61,185 term
allocations; ×89 files ≈ 6.8% of the corpus totals below, not enough to move
any conclusion. One file dominates: `077_RBTree.id_spec` alone is 58.0M of
the 120.0M theorems (48%).

## 3. The numbers

### 3.1 Lean side: spines are short and saturated

Export-level, over the expression DAG (each node once; a "site" is a non-`fn`
reference to an `app` node):

| | `init-prelude` | tutorials (91) |
|---|---:|---:|
| expression DAG nodes | 54,535 | 6,098 |
| `app` nodes | 30,113 (**55.2%**) | 2,465 (40.4%) |
| spine sites | 20,516 | 1,421 |
| mean spine length | 2.61 | 2.32 |
| length ≤ 4 | 89.9% | 93.7% |
| longest | 23 | 13 |
| const-headed | 87.2% | 59.3% |
| …of those, syntactically saturated | **96.3%** | 99.4% |
| partial (1–2 args short) | 1.0% | 0% |
| `Eq`-headed sites | 9.7% | 12.0% |

So Lean-side: applications are the majority node kind, spines are short
(33.6% are length 1 on `init-prelude`), heads are known constants and almost
always saturated. This is the population an n-ary or saturated-head scheme
would feed on — it is real. What follows is what it is worth on the TG side.

### 3.2 TG side, nodes: `app` is a small minority everywhere

Aggregated over the 89 accepted runs:

| population | total nodes | `app`-symbol nodes | share |
|---|---:|---:|---:|
| allocation traffic (every `Term::new`) | 232,840,323 | 24,140,674 | **10.4%** |
| retained registry (`Interp::mk` parts table, DAG) — **the table is gone; see below** | 1,452,685 | 199,579 | **13.7%** |
| final stored context (denotations + typing/defeq conclusions, DAG) | 15,722 | 104 | **0.66%** |

**The middle row no longer names anything that exists.** `Interp::parts` was
deleted on 2026-08-09 (MEASUREMENTS.md; `PRELUDE-COST.md` §3.4) — its value was
a second copy of what the key's own `TermData::App` node already held, and
`kernel::Term::as_app` reads it instead. Nothing about the *nodes* moved: the
same terms are built and the same ones stay reachable from the store, so the
`app` share in that row stands as a statement about retained structure. What is
gone is the second `Vec` per node and the table's own pin on every term ever
built, which was 54.4 % of an `init-prelude` run's live heap and 80 % of its
live `Term` nodes. Read the row as "retained structure", not as "a registry".

The rest of the traffic is free variables (3.7%), bound (8.3%), and — the
bulk, 77.6% — applications of *other* symbols (minted fibre/nest symbols and
the library's own operators; the walker labels only `app`/`fs`/`dprod₀`, so
the per-symbol split beyond `app` was not identified by name). The term
budget lives in the library's operations and in the arguments, not in the
application spine.

Spine lengths where spines are retained (registry, maximal, DAG-level):
80,961 spines — 23.5% length 1, 8.9% length 2, **64.4% length 3** (46,926 of
the 52,119 come from the one `Eq`-heavy file, `077_RBTree.id_spec`; spine
heads were not recorded, so "these are `Eq α a b`" is an inference from that
file's content, not a measurement), 3.2% length 4–8. Mean 2.53. The
allocation-side histogram gives the collapse ceiling directly: allocations at
spine depth ≥ 2 — exactly the nodes an n-ary node would not allocate — are
9,021,039, i.e. **3.9% of all term allocations**. That is option (b)'s entire
node-side upside, before costs.

### 3.3 TG side, inferences: bounded at 13.3%, and mostly not about arity

119,969,444 theorems constructed over the corpus. Attributed (delta of the
theorem counter across each call; rows overlap slightly and must not be
summed with the β row, which can re-enter the app rule):

| operation | calls | theorems | share of total | per call |
|---|---:|---:|---:|---:|
| `dprod_app` (application typing, `Type` fibres) | 185,200 | 13,693,416 | 11.4% | 74 |
| `cond_app` (application typing, `Prop`) | 2,369 | 1,732,320 | 1.4% | 731 |
| `app_cong` (conversion congruence over `app`) | 37,468 | 561,945 | **0.47%** | 15 |
| `beta_evidence` (β legs) | 8,402 | 3,183,906 | 2.7% | 379 |

App-shaped work in total: ~13.3% of all inferences. How much of that an
n-ary symbol could remove:

* **Congruence is the only row where arity is the cost.** A spine of `n`
  needs `n` binary `app_cong`s; one n-ary `congr` costs roughly half, not
  `1/n` (per-argument Leibniz + transitivity either way,
  `derived/src/rules.rs:167`). Ceiling: ~0.25% of inferences.
* **Typing is per Lean argument regardless of spine shape.** `dprod_app`
  consumes the Π telescope one binder at a time — instantiate the `dprod`
  defining axiom, peel the section, instantiate at the argument, unfold the
  fibre (`checker/src/mini/interp.rs:2436`). A saturated n-ary rule would still owe
  one argument membership and one fibre unfold per argument; what it could
  batch is the intermediate spine memberships, a fraction of the 74/call not
  measured here (§7) but structurally well under half.
* **β is untouched** — one binder per step whatever the surface arity.

And the number that reframes the whole column: 185,200 `dprod_app` calls
against 1,421 Lean-level application sites is **~130 rule firings per site**.
Some of that multiplier is legitimate — per-σ schedules, and applications
synthesized during reduction that never appear in the export — but most is
not: CERTIFYING-OVERHEAD.md measured 97.8% of conversions happening inside a
repeat of an already-seen α-canonical judgement, and has a designed fix (the
α-canonical `Sealed` memo and evidence threading). The cost of application
handling is not the per-site price; it is the re-derivation recurrence, and
any per-site optimisation, n-ary included, polishes a constant sitting inside
that unfixed factor.

### 3.4 Sharing: the lever the question was reaching for

* There is **no hash-consing**: `Term::new` allocates unconditionally;
  equality short-circuits on pointer then cached hash (`term.rs:129-134`), so
  spine *prefixes* are already structurally shared within a spine family.
* Distinct structures over the whole allocation traffic (HLL estimate, ±~2%,
  summed per run): **4.78M distinct against 232.8M allocated — 48.7×**; for
  `app`-symbol nodes alone, 55.3×.
* Even the retained registry holds 1,452,685 `Rc` nodes over 703,329 distinct
  structures — 2.1× duplication in what is deliberately kept.

The factor is workload-dependent: on the heavy `nested_model` run (§3.5) it
is 5.3× overall and 35× for `app`-symbol nodes — many small runs each
re-deriving prelude-adjacent terms inflate the corpus figure, one big run
dilutes it. A kernel-internal interning table would shrink *every* population
in §3.2 by about the duplication factor, make equality O(1) instead of
hash-plus-walk-on-collision, and cost nothing at the interpretation layer —
no lemma twins, no bridges, no change to what any theorem says. It does touch
`kernel/`, which nothing in this study's remit was allowed to land a change
to (the probe patched a scratch worktree only, and was not landed); it is
named here as the measured alternative, sized, for the owner to take or
shelve.

### 3.5 The heavy fixture, as a check

`nested_model` (`checker/tests/fixtures/`, run with `--mutual --nested`; exit 4 —
accepted, with untranslated debt) is a single run at **709,127,055 theorems**,
six times the whole tutorial corpus, and it reproduces every ratio that
matters:

| | tutorial corpus | `nested_model` |
|---|---:|---:|
| `app`-symbol share of allocations | 10.4% | 11.1% (120.4M of 1,087.5M) |
| `app`-symbol share of retained registry | 13.7% | 14.0% |
| `app` share of final stored context | 0.66% | 8.2% (157 of 1,913) |
| n-ary collapse ceiling (allocs at depth ≥ 2) | 3.9% | **2.3%** |
| app-shaped inference (`dprod_app`+`cond_app`+`app_cong`) | 13.3% | **8.9%** |
| `dprod_app` per call | 74 | 74 |
| β legs (`beta_evidence`) | 2.7% | **29.2%** |
| traffic / distinct structures (HLL) | 48.7× | 5.3× |

The one number that grows with scale is β — 29.2% of a heavy run, at 1,284
theorems per leg — which an n-ary `app` does not touch at all (one binder per
step regardless of surface arity). The app-shaped share *shrinks* as the
workload gets heavier. Whatever is worth optimising at scale, it is not the
spine.

## 4. The three candidate answers, judged

**(b) n-ary `appn` — ruled out.** Upside measured at 3.9% of allocations and
~0.25% of inferences. Cost: `appn` symbols per arity (spines reach 23 on
`init-prelude`); a characteristic theorem and a bridge
`appn(f,x⃗) = app(…app(f,x₁)…,xₙ)` each; and every binary `app` lemma —
`app_members`, `app_off_domain`, `beta_conditional(_n)`, `funspace_app_mem`,
`app_of_pair`/`funspace_ext`, the `rec_acc` application chain — either gets
an n-ary twin or is reached by unfolding the bridge, and a bridge unfolded at
the point of use has bought nothing: the unfold *rebuilds the binary spine*,
because the bridge equation's right-hand side is exactly the spine. Partial
applications (33.6% of `init-prelude` sites at length 1, plus every prefix a
conversion or β step exposes) keep the binary form alive underneath
regardless, so `appn` is an *additional* representation, not a replacement.
This is `derived/src/ext/dprod_universe_n.rs`'s economics again, at worse
exchange rates.

**(a) avoid `app` at saturated known heads — already done where it pays;
extending it is capped and against the design's own rule.** The `Direct`
clause is the thesis's own interpretation for its §6.2 menagerie (`Eq` today,
`Acc` when wired), not a size optimisation — and its former extra rows (`And`,
`PUnit`) were deliberately deleted in favour of the general clause, with a
standing rule that the table takes no fourth row (`checker/src/mini/direct.rs`,
"the table had three rows and now has one"). Measured headroom confirms the
deletion's wisdom: retained-store spines are 0.66% of nodes on the corpus and
8.2% on the heavy fixture — where 141 of the 144 maximal spines are length 1,
which no collapse of any kind shortens — and the inference share a
saturated-head fast path could touch is bounded by the 13.3% of §3.3 with the
same per-argument floor. `Eq`-headed sites — the
single biggest known-head population at 10–12% of sites, and by content the
likely bulk of the retained length-3 spines — are precisely the ones whose
*stored* types already collapse to fibre symbols; what remains is transient traffic inside an unfixed 130×
recurrence. Extending `Direct` is the wrong instrument for a cost that
deduplication removes wholesale.

**(c) the premise is wrong about where the cost is — supported.** Term size:
`app` is 10.4% of traffic and 0.66% of what is kept; arguments and library
operators dominate; a spine's prefix is already shared. Inference: app-shaped
work is 13.3%, of which the arity-sensitive part is under 1%; the measured
pathologies are the absence of interning (48.7×) and the re-derivation
recurrence (~130× per site here, 97.8% duplicate conversions in
CERTIFYING-OVERHEAD.md). Both have designs that do not touch the term
language: the `Sealed` memo / evidence threading (already specified), and
kernel-internal hash-consing (sized in §3.4, owner's call).

## 5. Does #28's deferral already answer this?

Partly, and instructively. The deferred task — "wire the n-ary Π clause in
`tg.rs`, and re-measure the 2903 first" — is about `checker/src/tg.rs`, where
the `Pi` clause is still a counted decline (`tg.rs:7809`). **mini already
consumes the n-ary Π rule**: `dprod_in_universe_pair_n` is called at
`checker/src/mini/interp.rs:2080`, inside the live Π typing clause. So the 2903
Π-into-`Type` sites measured on the old backend (`MEASUREMENTS.md:1224`) are
a population whose consumer moved out from under them — re-measuring before
wiring was exactly right, and the re-measurement is mini's own ledger, where
Π typing derives. The deferral does not answer the `app` question by itself —
it is about a typing rule, not the application operation — but its reasoning
is the operative lesson and this document is its application: measure the
population on the live backend before building the port. Measured, the
population for n-ary `app` is not there.

## 6. Recommendation

1. **Close the n-ary `app` question as "no".** No `appn` family, no new
   `Direct` rows, no change to `funcs/apply.rs`.
2. If term size or inference volume needs to move, the measured levers are,
   in order: the CERTIFYING-OVERHEAD.md fixes (recurrence + `Sealed` memo;
   removes most of the 130× and with it most app-shaped traffic), then
   kernel-internal interning (5–49× depending on workload, touches the
   trusted base, owner's decision). Both are separate pieces of work with
   their own briefs; neither was built here.

## 7. Not measured

* **`init-prelude` at the TG level.** mini declines it (nat literals > 10),
  so every TG-side number is from the tutorial corpus; `init-prelude`
  contributes export-level numbers only. The tutorial corpus is small and
  skewed (one file is 48% of inference traffic). NAT-REPRESENTATION.md's
  literal work is the path to closing this.
* **`proj_reduced_carrier`.** Needs ~10 min in release; it was not run under
  the debug probe build. `nested_model` *was* measured (§3.5) and is the
  scale check; the ten-minute fixture remains unprofiled.
* **The `checker/` (tg.rs) backend's term sizes** — likely the source of the
  owner's quoted code — were not instrumented; it is superseded by mini for
  this question.
* **The removable fraction of `dprod_app`'s 74 theorems/call** under a
  hypothetical telescope-batched saturated rule: bounded (well under half,
  per-argument floor), not measured.
* **HLL error**: distinct-structure counts are ±~2% estimates over a weak
  (FNV-style) hash; collisions can only make the true duplication *larger*
  than reported.
* Attribution rows overlap where a β leg re-enters the app rule; each row is
  correct in isolation, their sum is an upper bound.

## Appendix: reproduction

```sh
git worktree add --detach WT origin/master   # ac77101 at measurement time
cd WT && git apply scripts/appsize-probe.diff
CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 cargo build -p mini
for f in vendor/arena-tests/good/tutorial/*.ndjson; do
  ( ulimit -v 4194304; MINI_TERMSTATS=1 timeout 300 \
      ./target/debug/mini "$f" 2> "stats-$(basename $f .ndjson).txt" )
done
( ulimit -v 4194304; MINI_TERMSTATS=1 timeout 590 ./target/debug/mini \
    checker/tests/fixtures/nested_model.ndjson --mutual --nested 2> stats-nested.txt )
```

Export-level statistics are `scripts/appstats.py` over any `.ndjson` export.
Sources for every non-derived number: §3.1 — `appstats.py` on
`vendor/arena-tests/good/init-prelude.ndjson` and the 91 tutorial exports;
§3.2–3.4 — the `MINI_TERMSTATS=1` stderr reports, aggregated; the two quoted
store lines — `mini … 098_natLitEq.ndjson --dump-theorems`; file/line
citations inline throughout.
