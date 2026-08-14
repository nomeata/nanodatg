# The pivot — mini's inductive arc on `checker/`'s evidence engine, at monomorphic input

*2026-08-08. A design and an assessment, on the owner's instruction; not an
implementation. The question, in the owner's words: use the more developed
inductive code from `mini/`, do the evidence-producing typechecking of
declarations with `checker/`, assume fully monomorphic input so nothing is
split on σ, and let nanoda's de-Bruijn-level caching kill the re-derivation
overhead — with a global memo from de Bruijn level to target variable so the
evidence is always valid. Everything below marked measured was run in this
repository during this study (a scratch worktree at `d1b1698`, `test` profile,
`perf stat -e instructions` per the standing rule at `47b262b`); §4 is the
measurements, §8 names what is not measured. Nothing is landed except this
document.*

## Verdict

**Feasible, and it is the right pivot — but it is a port of wiring onto a
staged plan that already exists, not a marriage of two engines, and two of the
brief's premises need correction before sequencing.** The load-bearing facts:

* **The heavy construction layer does not need to move.** Mini's 34,051-line
  inductive arc (35 files of `mini/src/`, 71% of the crate) sits on
  `derived/src/inductive/` (9,782 lines plus `family/`), which is
  crate-neutral by the `derived/` vocabulary rule and is **already called by
  `checker/`'s backend** — this study's certifying run shows `tg.rs`'s general
  path translating a declaration through `derived::inductive` (§4). What moves
  is the Lean-facing wiring: declaration-shape reading, scope opening,
  store registration, the ι seeding. That is a re-target against
  `TcCtx`/`TgBackend` APIs, not a rewrite of the mathematics.
* **`checker/` is an evidence engine with all five caches carrying
  certificates** (`util.rs:898–932`: infer ×2 with `Typing` values, whnf ×2
  with `Reduct` steps, a proof-producing union-find) — the brief's reading
  survives, with one narrowing: the caches are **per-declaration**, not
  global (`with_tc_and_declar` mints a fresh `LeanDag` + `TcCtx` per
  `(declaration, σ)`, `util.rs:252–261`; `tg.rs:14720`: "a `TgBackend` is
  created per `TypeChecker`, i.e. per declaration"). That is the right
  lifetime: the measured duplication lives *within* declarations
  (285,922,406 `infer_type` entries against ≤ 9,561 distinct expressions on
  one tower, PROFILE §4; 151× α-canonical repeats on the certified axis,
  CERTIFYING-OVERHEAD §4). Cross-declaration evidence already flows through
  the `Sealed` stores (`declar_typings`, `tg.rs:2115–2123`).
* **The owner's memo exists in embryo at `tg.rs:7655–7676`**: `⟦Local⟧` is
  already a memo from `FVarId` — de Bruijn level or unique id — to a kernel
  `FreeVar`. §3 designs the finished form: the key must be the **`Local`
  node**, not the bare level, and the wiring home is exactly
  THREADING-CENSUS.md §2 stage 1, whose plumbing (`checker/src/scope.rs`, a
  tested port of `checker/src/mini/scope.rs` with **no production caller yet**) is
  sitting in the tree waiting.
* **"Fully monomorphic" is mode B, and no checker of nanoda lineage can read
  mode B today.** The Mathlib-scale validation the brief cites — 776,723
  declarations, nanoda accepts all — is **mode A** (MONOMORPH.md §9, §5.3),
  which leaves one level parameter per recursor plus ~22 carried built-ins
  (§4.1, §8). nanoda refuses mode B because it regenerates recursors by name
  (`Expected (Declar::Recursor, Declar::Recursor)`, §4.2). So "there is no σ
  any more" is exactly true only after a `checker/` recursor-path change;
  mode A delivers the deletion of `instantiations.rs` and everything σ now,
  with a one-numeral residue on recursor uses. §2 itemises; §5 sequences.
* **First timed certifying run of `checker/` — the row PROFILE §9 left open.**
  `nanoda_bin --features tg` on `nested_model.ndjson`: **3,963,804,418
  instructions**, all 40 declarations checked, 2,298 kernel `Thm`s derived.
  Mini, same export, full run: **1,277,210,565,843 instructions** — 322×.
  That ratio is **not** engine-vs-engine at equal work (checker's evidence
  coverage on this fixture is far thinner — 222 gaps, 334 typing obligations
  carried as assumptions, 41 escapes; mini certifies the fixture's whole
  specification), and §4 says exactly how much of the 322× the coverage
  confound could account for. What the run does establish: the certifying
  fork builds, runs, keeps its caches with the backend live, and its cost is
  three orders of magnitude under mini's on identical input. The hope that
  it *stays* fast at mini's coverage is supported by the duplication
  measurements and is **unmeasured**; §8 names it.

The one-sentence sequencing verdict: **three of the four work packages are
safe to start today** — the stage-1 scope wiring with the strengthened memo
key, the inductive-coverage port into `tg.rs`'s general path, and mono-input
consumption in mode A — and the fourth, end-to-end nested declarations
through the pipeline, waited on #116 in `monomorph` rather than on anything in
`checker/` or `mini/`. **#116 is closed** (`MONOMORPH.md` §1.2 property 4 and
§1.3), so all four are open; the paragraphs below that state the wait are kept
for the shape of the problem and are marked where they are now history.

## 0. Where the brief is wrong or needs narrowing, stated first

Per the standing instruction, before anything is built on them:

1. **"285,922,406 times for 9,561 distinct expressions — 43,000×
   duplication."** The 43,000× is *`Expr` constructions* (411,015,702 against
   9,561 distinct, PROFILE §4). The `infer_type` figure is 285,922,406
   entries, which against ≤ 9,561 distinct subjects is "≥ 29,900×". Same
   order, different numerator; both are PROFILE §4's, and the 0-hits-in-286 M
   figure is right as stated.
2. **"Mini has none by design."** Mini *began* with none; today it has three
   caches — `Checker::frames`, `wt_memo`, and the `Interp` symbol tables —
   added by measurement (MINI-DESIGN §0.3's bracketed note). The clause that
   used to stand here — "on the **acceptance** axis the frame memo is disabled
   by the `Gap` gate, so that axis effectively has none" — was true when it
   was written and is **no longer**: CACHING-DESIGN's step 1 landed, the gate
   in `frame_put` is now `self.th.is_some() && t.ev.thm().is_none()`, and the
   acceptance axis has a live memo (corpus hit rate 3.38% → 18.15%,
   `checker/tests/mini_nested.rs` 17.906 T → 8.409 T instructions).
3. **"Assume fully monomorphic input."** Only mode B is fully monomorphic,
   and mode B's output is refused by every kernel that mints recursors by
   name — nanoda, and Lean itself (MONOMORPH §4.2: "Mode B needs a checker
   that does not regenerate recursors by name"). The corrected premise: mode
   A input now, one checker-side change to reach mode B, §2.3.
4. **"This pivot is not 'add caching to an evidence engine'; it is 'move the
   inductive work onto an evidence engine that is already cached.'"**
   Survives contact with the code, with one addition: checker's *evidence
   discipline* is a stage behind mini's. Its assumptions are formula-level
   antecedents (`CondEq`) with an escape ledger, not kernel hypotheses with
   scoped discharge (`checker/src/scope.rs` header: "no production caller
   yet"; this study's tg run: 334 typing obligations asked, **0 discharged,
   334 carried as assumptions**). So the pivot is: move the inductive work
   onto an engine that is already cached **and finish that engine's
   threading to mini's design** — which is not new work invented here; it is
   THREADING-CENSUS.md §2's staged plan, stages 1–3.

## 1. Feasibility: what exactly moves, what stays, what dies

### 1.1 The `Expr` question, settled

Two different Rust types; a real correspondence on closed terms; already
exercised in one direction on every parse.

| | `mini::Expr` (`checker/src/mini/expr.rs:204`) | `checker::Expr` (`checker/src/expr.rs`) |
| --- | --- | --- |
| bound variable | `BVar(u32)` | `Var { dbj_idx: u16 }` |
| free variable | **none** — ambient telescope `Checker::lenv` | `Local { binder_name, binder_style, binder_type, id: FVarId }` with `FVarId::{DbjLevel(u16), Unique(u32)}` |
| allocation | `Rc` per node | arena, hash-consed (`LeanDag`), cached hash per node |
| binder names | dropped (deliberate, header) | kept, and **in the `Local` hash** |
| nat literals | `u64`, parser declines > 10 | `BigUint` |
| everything else | `Const/App/Lam/Forall/Let/Sort/Proj/StrLit` | same constructors, ptr-shaped |

On closed expressions (no `Local`) the two are in bijection up to binder
names and literal width — `checker/src/mini/convert.rs` *is* that bijection's
checker→mini half, run on every declaration mini has ever checked. The
reverse bridge does not exist, and **this design does not build it**: bridging
at runtime would keep mini's uncached engine in the loop for exactly the
inference the pivot exists to move off it. The modules are re-targeted to
`ExprPtr` accessors; the closed-term correspondence is what makes that a
transliteration of shape-reading code rather than a redesign.

### 1.2 The "more developed code for inductives", and its dependency surface

The arc is 34,051 lines across 35 files — `zoneb`, the `rec_*` family (dep,
prop, ix_dep, ix_prop, s_ix, trunc, trunc_ix, acc ×5), `iota_{dep,ix_dep,
model}`, `ctor_ix`, `class_{s,s_ix,p_ix}`, `minor_ix`, `proj_{data,prop}`,
`nested`, `nested_splice`, `mutual_aux`, `quot{,_iota,_classes}`, `direct`,
`unit_like`, `eq_cash`, `fun_eta`, `interp`, `recursor` — against `tg.rs`'s
17,376 lines total, whose inductive coverage is the general non-indexed path
plus hand recognisers, with `gen_scope` still returning `Decline::Indices`
(`tg.rs:6356–6390`). The imports of the owner's eight named modules split
cleanly:

| dependency | which modules | essential or incidental | checker counterpart |
| --- | --- | --- | --- |
| `kernel::{Term, Formula, Thm, FreeVar, …}` | all | **essential, and portable unchanged** — the TCB is crate-neutral | same crate, same types |
| `derived::inductive::{DeclSpec, CtorSpec, Inductive, Slot, rect, step, decl_proj, family::*}`, `derived::sigma` | zoneb, rec_dep, iota_dep, ctor_ix, proj_data | **essential, already shared** | `tg.rs` already consumes `derived::inductive` (this study's run, §4); `family/` has no checker consumer yet — that consumer is the port |
| evidence-producing `infer_type` / `whnf` / `whnf_conv` / `whnf_typing` | zoneb (25/3/3/2 call sites), rec_dep, iota_dep, eq_cash | **essential** — the engine being swapped | `TypeChecker::infer` returns `Typed { ty, cert }` (`tc.rs`); `whnf` returns `Reduct` with steps |
| scope open/close with kernel hypotheses (`Scopes`, `open`, `close_one`, `scope_vars`, `in_scope`) | zoneb, rec_dep, iota_dep | **essential** | `checker/src/scope.rs` — ported, tested, **unwired** (stage 1) |
| the `Interp` store (`c.interp()` — 44 call sites in zoneb alone), `ConstInterp`, `PiShape`, `stored_term`, `lam_nest` | all | **essential as a role**, mini-shaped as a type | `Shared`'s maps (`const_syms`, `gen_inds`, `gen_recs`, `rec_nests`, `gen_ty_nests`, `gen_ctor_nests`, `declar_typings`) — same role, `Sealed`-funnelled |
| `crate::expr::{Expr, E, Name, Level}` pattern-matching | all | **incidental** — representation | `ctx.read_expr` / `read_name` / `read_level` accessors |
| `Checker::lenv` telescope, `push`/`close_slot` | all | **incidental** — context representation | locals in the term (`mk_dbj_level`), `abstr_levels` on close |
| `Ev`/`Gap`/`Typing`/`Cause` | all | **incidental as types**, essential as policy (§0.4's cause-propagation rule) | `TgCert`/`TyGap`/`Typing<'t,'p>`; the gap taxonomies differ and must be mapped, not copied |
| `ground::eval`, `Gap::SymbolicLevel` | proj_data, rec_ix_*, eq_cash, many | **dies** under monomorphic input (§2) | dies on both sides |
| `ConstKey = (Name, Vec<u32>)` | interp, nested_splice, dump | **dies to a name** under mode B; a ground singleton under mode A | `(u32, Vec<Term>)` keys, same collapse |

So the honest description of the port: the *constructions* stay where they
are; the *wiring* is rewritten module-by-module against checker's APIs, with
the evidence plumbing going through stage-1 scopes instead of `lenv`, and
mini's files remaining in place as the executable reference (§6). The two
modules that are **not** primarily wiring: `nested_splice` (recognises and
splices `modelgen` output — its keying by *constructed* name makes the mono
root marker transparent to it, MONOMORPH §1.3's last paragraph; the same §1.3
used to record that `rec_k`/`iota_k_j` land under a *different* marker and that
only one copy of `T` had a model at all, and **#116 closed both**, so the keying
works end-to-end now) and `mutual_aux`
(encodes a mutual block into Lean-world syntax — representation-level, needs
the fullest rewrite).

### 1.3 What this is not

Not a merge of the two checkers' kernels; not a runtime bridge between the
two `Expr`s; not a port of mini's `Checker` (its `lenv`/frame design is the
thing being left); and not a rescue of `tg.rs`'s search-based clauses —
`has_type_a` and family are what MINI-DESIGN §0's rule bans, and the port
must land the threaded discipline (stage 1–3), not feed the search more
cases.

## 2. The σ removal — the checker-side story is the same shape as mini's, and bigger

The structural fact that makes it clean, from `tc.rs:251–253` (verified):
**"`infer`, `whnf` and `def_eq` never read σ; only the interpretation does."**
σ is applied in exactly one place, `TcCtx::under_sigma` (`util.rs:354`). So
removing σ cannot change a verdict by construction, and the negative corpus
needs no σ machinery to go on being checked raw — acceptance always ran at
the declaration's own parameters. The deletion is total, not modal.

### 2.1 What deletes, concretely

The mini-side inventory is MONOMORPH.md §8's and is confirmed against the
code (`ground.rs` 141 lines; `Gap::SymbolicLevel` at 30+ raise sites across
the arc; `ConstKey` at `interp.rs:60`). The checker side, same shape, plus
two items mini never had:

* `checker/src/instantiations.rs` **entirely** — 511 lines, the worklist
  fixpoint, `Inst`, `DEFAULT_LEVELS`, the published schedule, the
  `was_predicted` audit. Shared with mini via `convert.rs`; dies for both.
* `TcCtx::sigma` (`util.rs:290–304`), `set_sigma`, `under_sigma` → the
  callers in `tg.rs` (3720, 3749, 3901, 9585, …) read the level directly.
* **`PropAt` (`tc.rs:152–171`) — the item mini has no counterpart for.** The
  Params/Sigma split exists because the checker's question and the model's
  question differ at a parameter σ sends to 0. At ground input the two
  questions coincide and the enum, its doc's whole argument, and the
  "asked at the parameters vs asked under σ" rule collapse to one classifier
  — MINI-DESIGN §0.1's six-line exactness, which `tc.rs:149` explicitly says
  "is *not* free here", becomes free here.
* **The per-σ re-check multiplier — the second checker-only item.**
  `check_declar_all`'s loop (`tc.rs:305–319`) re-runs the whole check per
  scheduled instantiation: 2,652 pairs for `init-prelude`'s 2,059
  declarations, 1.14× wall / 1.16× derivations (README §Coverage). Gone;
  one check per declaration.
* `TyGap::PiUndet` (`certify.rs:1013`) and `interp_sort`'s hedging
  (`undet_syms`) — unreachable at ground levels. This is the single largest
  buy (MONOMORPH §8): 2,206 Π nodes on `init-prelude`, 38% of the
  population, each becomes a numeral with exactly one §6.2 clause.
* `InstAudit` (`tg.rs:15574–15602`) — nothing to audit against.
* Every level-keyed store loses its level dimension **in the limit**:
  `declar_typings: HashMap<(u32, Vec<Term>), Sealed>` → keyed by name;
  `gen_inds`/`gen_recs`/`gen_ty_nests`/`gen_ctor_nests` likewise; mini's
  `ConstKey` → `NamePtr` — the widest blast radius on both sides, and the
  same edit.

### 2.2 What does not delete

Levels do not leave the language: `Sort n` numerals still climb the tower
(MONOMORPH §8). The ~22 carried built-ins keep `levelParams` used at
numerals. And under **mode A** every recursor keeps its motive universe as
one parameter, its uses supplying a numeral — so the level component of the
stores shrinks to ground singletons on recursor uses rather than vanishing.

### 2.3 The mode B gate

Mode B empties `levelParams` on everything not a carried built-in — the
owner's premise exactly — and is a pure post-pass over mode A
(`Modelgen.Mono.foldElim`). What blocks consuming it is one inherited
behaviour: `checker/` (as nanoda) **mints** each inductive's recursor and
pattern-matches the export's declaration of the same name
(`inductive.rs`; the refusal is `Expected (Declar::Recursor,
Declar::Recursor)`). The change: on meeting `T.rec._elim.w`, mint `T.rec.{u}`
as today, instantiate at `u := w`, and compare — an instantiate-and-compare
where today there is a name-match. Size unmeasured (§8); it is confined to
the inductive-checking path and mode A is the oracle for everything else.

## 3. The de Bruijn level memo, designed

### 3.1 What exists

Two pieces are already in the tree. `tg.rs:7655–7676`: interpreting a
`Local` consults `locals: HashMap<u64, FreeVar>` (`tg.rs:2266`), key = the
dbj level (unique ids in the other half of the key space), value = a kernel
free variable from the thread-shared `Env` — minted once, reused on every
later occurrence. And `checker/src/scope.rs`: mini's open/assume/discharge
discipline, ported and tested, no production caller — THREADING-CENSUS §2
stage 1 names its wiring point as "a context stack beside
`dbj_level_counter` in `TcCtx`".

### 3.2 The design

* **Key: the `Local` node itself** — the `ExprPtr` of
  `Local { id: DbjLevel(k), binder_type: T, … }`, which the `LeanDag`
  hash-conses, so the key is O(1) and *re-opening the same binder rebuilds
  the identical node*. Not the bare level `k`, which is today's key and
  aliases: the level counter is non-monotonic (`util.rs:283`,
  `replace_dbj_level` decrements), so two different binders occupy level `k`
  at different times with different types, and level-only keying maps two
  Lean locals to one kernel variable. Under today's formula-level
  antecedents that aliasing is sound (the assumption travels inside the
  formula, and discharge matches formulas, not variables) but muddies
  sharing; under stage-1 kernel hypotheses it must be excluded, and the node
  key excludes it — different type, different node, different variable.
* **Value: the target variable** `w : kernel::FreeVar`, drawn from the
  thread-shared `Env` (so it cannot collide across declarations), plus —
  once stage 1 lands — the interpretation `⟦T⟧` and the scope assumption
  `w ∈ ⟦T⟧` handle beside it.
* **Validity: an entry is valid forever.** The map is a pure function of its
  key; entries are never invalidated, never popped, never rebased. That is
  the whole point, and it is the answer to the question mini's frame answers
  with "throw it away".

### 3.3 The soundness argument — why an entry minted under one context is sound under another

Three legs, each already load-bearing somewhere in the tree:

1. **The key carries the relevant context, manifestly.** A `Local` at level
   `k` embeds its binder type `T`; `T`'s own free locals are `Local`s
   embedding *their* types; transitively, the key embeds every part of the
   telescope the judgement depends on. Any two contexts that can build this
   key pointer-equal agree on that whole prefix. This is the owner's
   "conveniently includes the relevant part of the context" made precise,
   and it is the argument `checker/` already runs for its infer cache:
   a memoised typing's hypotheses "are always about locals occurring in the
   very expression the entry is keyed on" (`util.rs:905–911`), enforced by
   the `typing_is_confined` debug assertion at every insert
   (`tc.rs:775–778`).
2. **The variable is a function of the key.** So evidence minted at one
   opening names exactly the variable every other opening of the same key
   uses, and the assumption formula `w ∈ ⟦T⟧` is *literally the same
   formula* each time — `⟦·⟧` is deterministic, which the design requires
   independently of any cache (`checker/src/mini/kernel.rs`, the `Clause` doc: two
   equal terms interpreting unequally would break every congruence). Mini's
   variables are fresh per opening and addressed relative to stack depth
   (`scope_term` reads `scopes.len() - 1 - depth`), which is why its frame's
   third failure mode — a scope opened behind `lenv`'s back *renumbers*
   the evidence — exists at all. Absolute naming has no renumbering to do.
3. **Hypotheses fail closed.** A kernel `Thm` carries `hyps()`; the `Sealed`
   funnel (`checker/src/sealed.rs`) refuses any theorem with hypotheses at
   every cross-declaration store; the escape ledger counts every antecedent
   that reaches a boundary. So even a defect in the key discipline degrades
   to a *counted incompleteness* — an assumption that fails to discharge —
   never to an unsound conclusion. The TCB is the backstop, exactly as for
   the three claim-matching bugs README records.

What this buys over mini's frame, stated as the mechanism: mini's memo key
is sound only while the telescope is fixed, so it dies at every `lenv`
change and the measured residue is cross-opening (n^1.98 after the memo,
≥ 2,100× duplication unpartitioned, PROFILE §6, §9). Under dbj levels a
re-entered binder *is* the same key, so the caches — which already survive
for the whole declaration — hit across openings with no frame, no
α-canonicalisation and no re-instantiation. The certified-axis fix that
CERTIFYING-OVERHEAD §2 designs for mini (close, seal, re-instantiate at
O(depth) per hit) is what this representation makes unnecessary *within a
declaration*; across declarations the `Sealed` stores keep that job, and
already do it.

### 3.4 Limits, stated

* **Globality is per thread-and-DAG, not per corpus.** `ExprPtr` keys die
  with the declaration's temporary DAG (`tg.rs:1463–1465`: `locals` stays
  per declaration because its keys do). The memo is "global" in the sense
  that matters — it survives every scope open/close within the check, where
  the measured duplication lives — and cross-declaration reuse remains the
  `Sealed` stores' job. Persisting further needs canonical keys; nothing
  measured demands it (§8).
* **`binder_name` is in the `Local` hash**, so α-equal binders with
  different display names miss. Cosmetic-miss rate unmeasured.
* `dbj_level_counter` is `u16`; the shared kernel `Env` counters are
  `checked_add` (`tg.rs:1477`), so exhaustion is a panic, not an alias.

## 4. Measured for this study

Both runs in the pivot worktree at `d1b1698`, `test` profile, single thread,
`ulimit -v 8 GB`, identical input `checker/tests/fixtures/nested_model.ndjson`
(the hand-written `Tree` tower, 40 declarations, both engines' common
denominator — PROFILE §1's reference fixture). Counters, not clocks.

| run | instructions | outcome |
| --- | ---: | --- |
| `nanoda_bin --features tg` (certifying backend live) | **3,963,804,418** | rc 0, all 40 checked; **2,298 derived kernel `Thm`s**, 222 gaps, 41 escapes, 334 typing obligations carried as assumptions; general inductive path: 1 declaration, 38 constructors, 1 recursor nest; schedule: 45 (declaration, σ) pairs, 0 unpredicted |
| `mini --no-modelgen --acceptance-only --mutual --nested` | **1,277,210,565,843** | accept, full certification pass |

Three readings, in decreasing order of confidence:

* **The certifying fork works and is cheap on this fixture.** This closes
  PROFILE §9's open row ("checker/ keeps its caches *and* is fast while
  certifying remains a source-level claim"): now exercised, backend on,
  caches carrying certificates, at 4 G instructions where mini spends
  1,277 G.
* **The 322× is not a like-for-like engine ratio.** Checker-tg derives 2,298
  theorems on this fixture and carries 334 typing obligations as
  assumptions; mini derives the whole specification (constEv 218/218,
  gapped 0 corpus-wide is mini's standing ledger). Part of the gap is
  coverage, not caching.
* **The honest bound on what caching can explain**: mini's own measurements
  put 97.8% of its certified conversions inside a repeat of an already-seen
  α-canonical judgement and the repeat factor at 151× (C-O §4). A perfectly
  cached engine doing *mini's* coverage would still do the distinct ~2%
  plus per-hit costs — order 25 G instructions on this fixture, several×
  above checker-tg's current 4 G. So the plausible end state is "tens of G,
  not 1.3 T" — a 30–60× improvement at full coverage, not 322×. **That is an
  extrapolation from measured duplication, not a measurement**, and §8 lists
  it first.

Reproduction:

```sh
W=.claude/worktrees/pivot   # detached at origin/master, vendor symlinked
cd $W
CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 cargo build -p nanoda_lib --features tg --bin nanoda_bin --profile test
CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 cargo build -p mini --bin mini --profile test
# config: export_file_path = checker/tests/fixtures/nested_model.ndjson,
# unsafe_permit_all_axioms, nat+string extensions, num_threads 1
( ulimit -v 8388608; perf stat -e instructions ./target/debug/nanoda_bin cfg.json )
( ulimit -v 8388608; perf stat -e instructions ./target/debug/mini --no-modelgen \
    --acceptance-only --mutual --nested checker/tests/fixtures/nested_model.ndjson )
```

(`--no-modelgen` because no `modelgen` binary is built in this tree; the
fixture contains no nested declaration to splice, so the flag changes
nothing — PROFILE §2 runs the same fixture as "no tower".)

## 5. Sequencing — what proceeds today, what waits, and on what

> **Superseded as a plan (2026-08-11, DECISIONS.md).** "Today" here is
> 2026-08-08. Item 2 below proposes lifting mini's indexed-family coverage
> *into* `tg.rs`; the standing rule is now the opposite — mini-owned inductive
> carriers, constructor graphs, recursors, projection packages and certificates
> are authoritative, and TG must consume those exact objects rather than
> reconstruct a parallel carrier or recursor. Item 4's "Mini CI relief
> (`mini/`)" presumes a separate crate, and there is none. §6's boundary
> argument is about a crate edge that no longer exists. The threading item (1)
> is the part that outlived the section.

**Today, in parallel, none blocked on the others:**

1. **Stage 1 + the memo key** (`checker/`). Wire `scope.rs` into `TcCtx`
   beside `dbj_level_counter` per THREADING-CENSUS §2 stage 1, and
   strengthen `TgBackend::locals`' key from the bare level to the `Local`
   node (§3.2). Correct at polymorphic *and* monomorphic input, so it does
   not wait for the pipeline. Measurables are the census's: escapes (1,484
   on init-prelude) fall, `HtMiss::Local` (5,186) falls to the ambient
   residue.
2. **The coverage port** (`checker/`). Lift `gen_scope`'s
   `Decline::Indices` (`tg.rs:6390`) by porting mini's indexed-family wiring
   onto `derived::inductive::family` — the derived/ layer needs nothing —
   then the `Prop`-class clauses, then quotients. Order within the port:
   whatever the tg gap report on the tutorial corpus ranks largest, which
   is the same discipline mini's ledger used. Each module lands with its
   counter ratchet (§7).
3. **Mode A mono input** (`checker/`). The pass exists, is validated at
   Mathlib scale standalone, and its output is ordinary polymorphic-looking
   export with almost every `levelParams` empty — checker consumes it
   **today with no change**. The σ deletion (§2.1) can then land as soon as
   the tg evidence path is only fed mono input; acceptance of the raw
   negative corpus is unaffected by construction (§2).
4. **Mini CI relief** (`mini/`, orthogonal). CACHING-DESIGN step 1 (narrow
   the gate) + step 2 — the oracle must stay runnable for the fidelity
   gates that §6 keeps; #110's 9 CI minutes do not care about the pivot.

**Waits, with the blocking fact named:**

* ~~**Nested declarations end-to-end** wait on **#116, in `monomorph`**~~ —
  **closed**, and this is what it was: a model did not survive the pass — one
  model for three copies (demand: nothing references a model, so its groups
  took `--default`), and the one model split across two markers
  (`rec_k`/`iota_k_j` carry the motive universe, so `|σ|` differed and the
  marker differed — MONOMORPH §1.3). The fix was the one §1.3 stated: key a
  model's declarations off **the declaration they model**, for instantiation
  and marker both. Nothing in `checker/` or `mini/` could have compensated;
  `nested_splice` constructs names, and seven-of-nine reachable families is a
  broken model. `MONOMORPH.md` §1.2 property 4 is now the contract, and
  §1.3's two items both read *closed*.
* **Mode B consumption** waits on the recursor instantiate-and-compare
  change (§2.3) — until then the σ deletion leaves the mode A residue.
* **The full `instantiations.rs` deletion** waits on the decision that the
  tg path's input is always the pipeline's output (the raw polymorphic
  corpus then runs acceptance-only, which never scheduled anything).
* **Evidence ratchets on checker** wait on coverage: they are re-established
  per ported module, not copied (§6, §7).

## 6. The boundary, redrawn

The rule the pivot breaks is README's: mini "reuses `checker/`'s parser and
level pre-pass **and changes nothing in it**". Note precisely what that rule
protects: it protects `checker/` *from mini*, so mini's fidelity experiment
could not perturb the fork. The pivot moves the frontier into `checker/`
deliberately, so the protection inverts:

* **The upstream-diff discipline stays and becomes the primary review
  instrument.** `git diff nanoda-upstream/master -- checker/` remains the
  exact instrumentation diff (README §Layout). The rule for the port, from
  the `scope.rs` precedent: **new capability lands in new files; upstream
  files take minimal, cited edits.** A reviewer can then read the diff as
  "nanoda + these named modules", which is the property the discipline
  existed for.
* **The moved code lives in `checker/`, not `derived/`.** The vocabulary
  test decides (README layout table): the wiring mentions `ExprPtr`,
  `NamePtr`, declaration shapes — checker vocabulary. The constructions
  stay in `derived/`, which both engines already share. The `scope.rs`
  header's own note — "collapse the two when both are in one pair of hands"
  — describes the whole port.
* **`ci/check-boundary.sh` gains the port's invariants**: I1 (only
  `scope.rs` names `Thm::assume`) already holds checker-side; the `Sealed`
  funnel already guards every cross-declaration store; the per-module
  counter ratchets are new steps.
* **What `mini/` is for afterwards** — MINI-DESIGN §0 rewritten in one
  paragraph: *mini was where the evidence-threading design was built without
  confounders; the design is settled (the "thread evidence, never search"
  memory records it as final) and its production home is `checker/`. Mini
  remains (i) the acceptance oracle — the mini-vs-nanoda gate
  (130 agree / 2 out-of-scope / 1 reason-only of 133, MINI-DESIGN §11.3)
  and the mini-lean fidelity fixtures are differential tests two cached
  engines cannot give each other; (ii) the executable specification of the
  evidence design, against which checker's ledger is compared
  explanation-for-explanation (§11 item 4's table); (iii) the measurement
  bench it always was.* Mini stops being the frontier; it does not stop
  being run. Its corpus ratchets (accept 89 / decline 2 / reject 0,
  constEv 218/218, unsealed 0, gapped 0) stay green on mini; **checker gets
  its own ladder, climbing per ported module, and the two ledgers are
  compared by explanation, not by number** — the gap taxonomies differ by
  architecture and MINI-DESIGN §11 item 4 already says what must match.

## 7. What could go wrong

* **Acceptance fidelity under caches — the named risk — mostly does not
  transfer, and where it does the detectors exist.** On the pivot,
  acceptance verdicts come from the engine that *always had* the caches:
  upstream nanoda's, validated by the arena corpus (102 good + 55 bad) and
  by mini-vs-nanoda. The clause-order sensitivity MINI-DESIGN §13 risk 2
  describes is mini's port-fidelity concern about *mini's own* clauses; the
  pivot does not touch mini's clauses. The genuinely new risk class is
  **evidence-vs-claim divergence at cache hits** — a hit returning a
  certificate for a different (defeq) reduct than the cold path would
  derive, the class of the three claim-matching bugs README records
  (`def_eq` skipping whnf-leg composition, `derive_beta` miscounting, the
  certificateless memoised reduct). Detectors, all standing: the
  single-exit guards that compare every derivation against its claim
  (`note_unmatched`, `tg.rs:14730–14755`), the `Sealed` constructor, the
  escape ledger, and `Admit::Whnf` pinned at zero. The test to add: **A/B
  cache-off vs cache-on over the corpus, comparing verdicts and the
  deterministic counters** (proved / gapped / escape rows) — and per the
  two-atoms memory, any pin on ordering or nesting uses three-element
  fixtures, not two.
* **The memo key bug class.** Level-only aliasing (§3.2) or a stale-key
  defect degrades to counted incompleteness, not unsoundness (§3.3 leg 3)
  — but a *silent hit-rate collapse* is possible and invisible in verdicts.
  Detector: hit-rate and escape counters per fixture, ratcheted like
  `Interp::lazy_fills` is pinned at 0 on mini.
* **A coverage plateau mistaken for done.** Mini's ledger is at zero gaps
  corpus-wide; checker's will be nonzero for months of ports. The failure
  mode is quoting mini's numbers for the pipeline. The guard is §6's rule:
  checker's ladder is its own, and the cross-ledger comparison matches
  explanations.
* **σ removed under a polymorphic straggler.** If mono detection is wrong or
  a poly file reaches the tg path, `PiUndet`'s 38% problem reappears
  silently as gaps. Detector: the `TyGap` rows and the "at levels still
  mentioning a parameter" audit line — keep that counter alive precisely
  because it must read zero on pipeline input.
* ~~**#116's shape is worse than its ticket.**~~ It was, and the reading held:
  the marker split was *intrinsic* to putting `|σ|` in the name (MONOMORPH
  §1.3: "neither is a property of §1.1's marker"), so the fix was a real
  design change in `monomorph` — model declarations keyed off the modelled
  declaration — and not a rename. Both halves have landed and the risk is
  spent.
* **The performance hope is an extrapolation.** §4's 322× is confounded and
  the ~30–60× full-coverage estimate is derived from mini-side duplication
  numbers. If checker-tg at full coverage lands at 10× instead, the pivot
  is still right (the σ deletion, the threading, the single engine), but
  the "kills the overhead" sentence would be overclaimed. Measure at each
  ported module; counters decide.

## 8. Not measured

* **Checker-tg at mini's evidence coverage** — the headline extrapolation
  (§4). Nothing can measure it until the port exists; the per-module
  ratchets are the running proxy.
* **Checker-tg on monomorphized input** — the `monomorph` binary is not
  built in this tree; the σ-removal yield on the tg path (PiUndet → 0,
  schedule gone) is asserted from MONOMORPH §5/§8's standalone numbers,
  not re-run here.
* **Cache hit rates on the ι-theorem shape under checker** — the shape that
  costs mini its minutes was not isolated under checker-tg.
* **The mode B recursor change's size** — read as confined to
  `inductive.rs`'s declaration-comparison path; not prototyped.
* **Stage 1's cost** — THREADING-CENSUS predicts escape/`HtMiss::Local`
  falls; no instruction-count estimate exists.
* **The cosmetic-miss rate of `binder_name` in the `Local` hash** (§3.4).
* **Checker-tg at Mathlib scale** — nanoda at Mathlib is measured
  acceptance-only (MONOMORPH §9.7); with the backend, unknown.
* **`derived/family` under checker's arena lifetimes** — the constructions
  are crate-neutral, but their driver's borrow patterns against
  `TcCtx`/`Shared` were not prototyped.

Sources: PROFILE.md §§1–9; CACHING-DESIGN.md §§1–7; CERTIFYING-OVERHEAD.md
§§2–4; MINI-DESIGN.md §0, §11, §13; THREADING-CENSUS.md §2; MONOMORPH.md §1,
§4, §5, §8, §9; README.md; `checker/src/{tc.rs, util.rs, expr.rs, tg.rs,
scope.rs, sealed.rs, instantiations.rs, certify.rs, inductive.rs}`,
`mini/src/{expr.rs, kernel.rs, convert.rs, zoneb.rs, interp.rs, ev.rs}` —
all read in this tree at `d1b1698`; and §4's own runs.
