# Threading census — evidence in and out of every type-checker operation

*2026-08-01. Survey of `checker/src/` against the target design: every operation
takes evidence of its precondition and returns evidence of its postcondition,
so that no fact is ever re-discovered by heuristics or search.*

**Method and caveats.** Everything in §1–§2 marked "verified" was read in the
code at the cited site; measured numbers are quoted from `MEASUREMENTS.md`
(entries dated 2026-07-30 to 2026-08-01) and from module docs in `tg.rs`, not
re-measured. `tg.rs` is under active edit as this census is being written, so
line numbers there drift — functions in `tg.rs` are cited by name; `tc.rs`,
`certify.rs`, `reduct.rs`, `quot.rs`, `inductive.rs`, `util.rs` line numbers
were stable during the survey. Note there is no `infer.rs`: inference lives in
`tc.rs` (`TypeChecker::infer` and its `infer_*` rules). Where I *infer* rather
than verify, the sentence says so.

The two scoping observations from the target design both check out in the code,
with one important qualification each:

* **Evidence only on the licensing branch** — confirmed everywhere the code is
  already threaded: `DefEq = Option<Cert>` with `None` = reject
  (`certify.rs:622`), the whnf-trace convention `None` = "no step taken, refl"
  (`tc.rs:1100–1103`), `Typed.cert` never optional but `ty_gap` a value
  (`tc.rs:59–92`). Qualification: several *negative-looking* branches feed an
  affirmative conclusion one level up (e.g. `def_eq_unit` returning `None`
  merely falls through to other rules that may still say yes), so "negative
  needs nothing" is per-*conclusion*, not per-function — the census below marks
  the branch that actually licenses.
* **The enabling mechanism exists but is unused in shipped code** — verified:
  `kernel/src/thm.rs:528,545` (`assume`, `implies_intr`); `Thm` is a sequent
  with `hyps()` (`thm.rs:305,354`). `ci/check-boundary.sh` bans `Thm::assume`
  outside `kernel/`, and grep confirms the only `tg.rs` uses are in its tests.
  Today all binder-context evidence is carried as *formula-level* antecedents
  (`⊢ conj(hs) → φ`, the `CondEq`/`u_*` discipline), at O(|hs|) cost per
  inference step, with `guard_and_generalise_at` re-implementing at the formula
  level exactly what `implies_intr` + `gen` do at the kernel level. So "hold
  assumptions at constant cost" is available and not yet taken. The ban on
  `Thm::assume` outside `kernel/` will need to be revisited (or the open/close
  API put *in* `kernel/`) when binder threading lands — flagged as a design
  decision in §2.

---

## 1. Per-function census

Column key. **Should take / should return**: the evidence per the target
design. **Status**: `done` = threaded; `partial`; `none`. **Instead**: how the
fact is currently recovered — `has_type` search (`TgBackend::has_type_a` and
family), `syn_type` delta-only re-walk, a `Dropped` ledger entry
(`certify.rs:920`, four variants: `Quot`, `Inductive`, `DefEqSide`,
`BinderSort`), an `Admit`, or an escaped assumption. **Difficulty**: M =
mechanical, D = needs a design decision.

### 1.1 Entry points (`tc.rs:157–324`)

| fn | today | should take / return | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `check_declar_at` (`tc.rs:176`) | per-σ dispatch; for value-bearing declars composes `infer`'s cert with `assert_def_eq`'s and hands `⊢ ⟦val⟧ ∈ ⟦ty⟧` to `declar_checked` | exactly what it does | **done** (`tc.rs:192–199`) — the model case | — | — |
| `check_declar_info` (`tc.rs:306`) | checks `infer(d.ty)` is a sort | should return `⊢ ⟦d.ty⟧ ∈ ⟦Sort l⟧` (and for theorems the `l = 0` witness that licenses "this constant is a proof" downstream) | none — result discarded via `infer_ty(…, Dropped::BinderSort)` at `tc.rs:310` | Dropped ledger; note the site label `BinderSort` is a misnomer here (it is a declaration type, not a binder domain) | M |
| `check_declar_all` / `check_all_declars*` | scheduling only | nothing | n/a | — | — |

### 1.2 Inference (`tc.rs:328–1002`) — the mostly-done tier

`infer` (`tc.rs:638`) returns `Inferred { ty, cert }`; the memos store the cert
(`util.rs:912–913`), guarded by `typing_is_confined` (`tc.rs:696`). Verified.

| fn | today | should return, on which branch | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `infer` (`tc.rs:638`) | `(T, ⊢ ⟦e⟧ ∈ ⟦T⟧)` | as-is | **done** (gaps are named values, `TyGap`) | remaining gaps are per-rule, below | — |
| `infer_ty` (`tc.rs:713`) | `infer` + counted discard | should eventually have no callers | the *discard adapter*; 12 call sites in `tc.rs` | Dropped ledger (33 587 `BinderSort` + 4 804 `DefEqSide` + … on init-prelude) | site-by-site |
| `infer_sort` (`tc.rs:717`) | cert via `ty_sort` | as-is | done (backend derives via `x ∈ U(x)`; 4 019 carried on ip) | — | — |
| `infer_const` (`tc.rs:328`) | returns substituted declared type; cert added by caller via `ty_const` | as-is | done as threading; the *backend* misses when no stored typing (20 494 `ty_const` no-evidence rows on ip). **Mostly but not wholly interpretation scope, §3**: of 2891 (declaration, σ) pairs with a value, 2674 have no certificate at all — cascade — but 198 had one that was *derived and discarded* because it stood under antecedents, which is threading debt. 1 161 of the 31 256 use-site misses are against those 198 | store miss ⇒ gap (search already removed) | — |
| `infer_app` (`tc.rs:743`) | rebuilds spine cert via `ty_app`/`ty_conv`; `assert_def_eq`'s cert consumed by `ty_conv` (`tc.rs:775–782`) | as-is, **plus**: when the head's type is not syntactically a `Π` and `ensure_pi` whnf-reduces it (`tc.rs:806–816`), the reduction certificate should be composed into the head's typing | **partial** — the `ensure_pi` leg is silently dropped (no `Dropped` entry, no compose); `TgBackend::ty_app` compensates with `ty_bridge`, which is **delta-only** (`unfolds_to`), and gaps otherwise | delta-only re-walk in `ty_bridge`; contributes to `ty_app` 45 + part of `ty_premise_missing` 4 503 on ip | M once whnf returns evidence (§2 stage 3) |
| `infer_lambda` (`tc.rs:873`) | rebuilds λ/Π per binder, cert via `ty_lam`; binder-domain sort check dropped (`Dropped::BinderSort`, `tc.rs:880`) | as-is; the domain-sort evidence `⊢ ⟦A⟧ ∈ ⟦Sort u⟧` *does* have a consumer in waiting — it is one of the two premises `point_of_proof` searches for | **partial** — typing threaded; domain-sort evidence dropped | Dropped `BinderSort` (the 33 587); `has_type` search re-derives `⟦α⟧ ∈ U₀` in `derive_point_of_proof` | M |
| `infer_pi` (`tc.rs:929`) | cert is `ty_pi` with three-way clause label (`Pi`/`PiProp`/`PiUndet`, `tc.rs:949–970`) | as-is; the missing evidence (`dprod_in_universe` n-ary) is a *library* gap, not threading (5 801 `ty_pi` rows on ip; `PiProp` 446/449 discharged) | done as threading | — | library work |
| `infer_let` (`tc.rs:979`) | expansion's typing via `ty_let`; the annotation check's certs dropped (`tc.rs:990–992`) | as-is (the dropped equality has nothing to compose with post-substitution — verified argument at `tc.rs:974–978`) | done; drops counted | Dropped `DefEqSide`/`BinderSort` | — |
| `infer_proj` (`tc.rs:582`) | computes field type by whnf-walking the ctor telescope; cert added by caller via `ty_proj` | should return the field-type derivation so the backend need not recompute | **partial** — `TgBackend::ty_proj` *re-derives* the field type by `syn_type_proj` (delta-only) and declines when whnf was needed (260 `ty_proj` rows on ip); also calls `is_proposition` twice discarding evidence, and its `infer_ty(structure, …)` discard is mislabelled `Dropped::DefEqSide` | syn_type delta-only re-walk (`TgBackend::syn_type_proj`, doc: "delta-only transcription of `infer_proj`") | D — either thread the checker's telescope walk to the backend, or accept the recompute-and-check as the honesty mechanism |
| `ensure_sort` / `ensure_pi` / `infer_sort_of` / `ensure_infers_as_sort` / `infer_then_whnf` (`tc.rs:380–413,576`) | whnf + shape check, evidence discarded | should return `(Sort l / Π, ⊢ ⟦T⟧ = ⟦whnf T⟧)` | none (the trace exists in the memo; the *composition* is missing) | nothing — silent; the backend re-bridges delta-only or gaps | M once whnf returns evidence |

### 1.3 Weak-head normalisation (`tc.rs:1074–1462`, `reduct.rs`)

Internally this is the best-instrumented tier: every reduction records a
`Trace` (rule + endpoints, `reduct.rs:100`), memos store trace beside reduct
(`util.rs:921–922`), and `certify_reduct`/`trace_cert`/`step_cert` turn a trace
into a certificate exactly once, guarded against endpoint drift
(`tc.rs:1268–1307`). What is missing is at the *boundary*, in both directions.

| fn | today | should take / return | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `whnf` (`tc.rs:1309`), `whnf_no_unfolding` (`tc.rs:1346`) | `ExprPtr` only; 28 callers (18 `tc.rs` + 10 `inductive.rs`, verified — the "28 callers" comment at `tc.rs:1077` is accurate) | **take** `⊢ ⟦e⟧ ∈ ⟦T⟧`; **return** `(e', ⊢ ⟦e⟧ = ⟦e'⟧)` — then `⟦e'⟧ ∈ ⟦T⟧` by Leibniz. The typing *input* is what feeds beta's domain obligations (next row) | **partial** — evidence out exists on demand (`whnf_no_unfolding_aux_with_cert`, `tc.rs:1364`) and is consumed on `def_eq` paths only; evidence *in* does not exist at all | callers that need the equality either use the aux-with-cert path (def_eq) or drop it (all of inference, §1.2 last row); the typing precondition is re-discovered per beta step, next row | signature change M; feeding beta D (below) |
| beta steps inside whnf (`Rule::Beta` → `Certifier::beta` → `TgBackend::beta_step`) | the redex's argument typing `⟦a⟧ ∈ ⟦A⟧` is **searched**: `domain_obligation` runs `has_type_a(arg, dom, [], 0)`, then retries under `local_premises` — which *reconstructs the ambient context by scanning the argument for `Local` nodes* — and finally hoists the raw membership as an escaped assumption | the typing should arrive with the whnf call: `infer` typed this very argument when the application was checked | none — this is the single largest re-discovery site left (init-prelude: 17 537 obligations asked, 1 451 discharged, 5 186 misses "a local at the top level", ~3 850 opaque-constant misses; escapes 1 484) | `has_type` search + `local_premises` context guess + escape ledger | **D** — the heart of §2 stage 3 |
| `whnf_reduce` / `whnf_no_unfolding_reduce` (`tc.rs:1316,1374`) | record traces; `Admit::ProjRed`, `Admit::Quot`, `Admit::NatRed` steps have no backend rule | as-is; missing pieces are backend rules (`proj` needs interpreted structures, `quot` interpreted `Quot`, `NatRed` is milestone 4) | done as threading | Admits, counted | out of threading scope |
| `certify_reduct` / `trace_cert` / `step_cert` / `seq` / `symm_leg` / `compose_legs` / `compose_whnf_legs` (`tc.rs:1106–1307`) | evidence plumbing, endpoint-checked | as-is | **done** (`Admit::Whnf` = bug report, at zero corpus-wide) | — | — |
| `unfold_def` (`tc.rs:2037`), `delta` (`tc.rs:2026`) | `delta` returns cert; `unfold_def` returns term, callers wrap in `Rule::Delta` trace | as-is | done | — | — |

### 1.4 Definitional equality (`tc.rs:1464–2386`)

`def_eq` returns evidence (`DefEq`), composes whnf legs on every exit, and
caches only unconditional certs on union-find edges (`tc.rs:1862–1876`).
What it does **not** do is *take* evidence: the target signature is
`def_eq(a, b, ⊢⟦a⟧∈⟦Ta⟧, ⊢⟦b⟧∈⟦Tb⟧) → ⊢ ⟦a⟧ = ⟦b⟧`, and the rules that need
typings re-derive them.

| fn | today | should take / return | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `def_eq` (`tc.rs:1762`) | `(x, y) → DefEq`; affirmative branch carries cert, negative rejects (sound) | add the two typing inputs; thread them to the rules below and into whnf's beta obligations | **partial** — out: done; in: none | see per-rule rows | signature M; plumbing D |
| `def_eq_quick_check` / `def_eq_sort` / `def_eq_const` / `def_eq_binder_aux` / `def_eq_app` / `try_eq_const_app` / `lazy_delta_step` / `recall_eq` | real rules: refl, `sort`, `const_eq`, `pi_cong`/`lam_cong` folds, `app_cong` folds, delta legs, explain-path composition | as-is | **done** — the certified core (58 694 certified vs 7 287 admitted at the 2026-07-30 measurement; `Binder`/`App` admits now zero) | residual `Admit::Cache` 272 on ip = conditional edges the cache rightly declines (needs binder threading, not cache work) | — |
| `proof_irrel_eq` (`tc.rs:2348`) | `is_proof(x)`, `is_proof(y)` (both discard their `infer` certs), `def_eq(l_type, r_type)` (cert discarded), then `Admit::ProofIrrel` | should pass: `⊢ ⟦x⟧ ∈ ⟦Tx⟧`, `⊢ ⟦Tx⟧ ∈ U₀` (from `is_proof`/`is_proposition`, §1.6) and the type equality, to a real `Certifier::proof_irrel(x, y, …)` rule | none — and this is the census's clearest double-work loop: the `admit` lands in `TgBackend::admit`, which calls `proof_eq` → `point_of_proof` → **`has_type_a` searches for exactly the two facts `is_proof` just established and threw away** (`derive_point_of_proof`: `has_type_a(e, tty)`, `has_type_a(ty, u0)`) | `has_type` search ×2 per side, plus `syn_type` for the subject's type — all recoverable from `infer` | **M/D** — mechanically thread once `is_proposition` returns evidence; D only in choosing the trait shape |
| `def_eq_local` (`tc.rs:1629`) | same id + `def_eq` on binder types (cert discarded) → `Admit::Local` | `w ≡ w` is refl of `⟦w⟧`; the binder-type equality cert should feed a real rule (or nothing — two locals with the same id interpret to the same variable, so refl suffices; the side condition is a checker-level sanity check) | none | Admit (0 uses on ip at last count) + Dropped `DefEqSide` | M |
| `def_eq_proj` (`tc.rs:1617`) | same idx + `def_eq(structures)` (cert discarded) → `Admit::Proj` | congruence `proj(i, ⟦s⟧) = proj(i, ⟦s'⟧)` from the structures' cert — derivable today, `proj` congruence needs no axioms about `proj` | none | Admit (16 on ip) + Dropped `DefEqSide` | M — this one looks like pure low-hanging fruit |
| `try_eta_expansion_aux` (`tc.rs:2368`) | `def_eq(x, λz. y z)` cert **discarded**, then `certifier.eta(x, y)` — which in `TgBackend` admits ("needs a function-extensionality lemma") | compose: `⟦x⟧ = ⟦λz. y z⟧` (in hand, discarded!) then `⟦λz. y z⟧ = ⟦y⟧` (the actual eta step, needs `lam_ext`-style lemma); also the `infer_then_whnf(y)` typing is dropped | none | recursive cert dropped with no ledger entry; backend admits | M for the composition; library work for the eta lemma |
| `try_eta_struct` / `try_eta_struct_aux` (`tc.rs:415–438`) | infers both types (`Dropped::DefEqSide`), `def_eq` on types and per-field projections, all certs discarded → `Admit::EtaStruct` | the per-field certs + a structure-eta lemma | none | Admit (3 on ip) + Dropped | blocked on interpreted structures (§3) |
| `def_eq_unit` (`tc.rs:469`) | type inference + `def_eq(types)` discarded → `Admit::UnitLike` | the type equality + a subsingleton lemma per unit-like structure | none | Admit + Dropped | blocked on interpreted structures |
| `try_string_lit_expansion*` / `def_eq_nat` / `delta_try_nat` | recursion certs partially composed; literal steps `Admit::StringLit`/`NatEq`/`NatRed` | as-is until milestone 4 primitives | partial (composition of recursive certs is correct; the literal steps themselves admit) | Admits, counted | milestone 4 |
| `assert_def_eq` (`tc.rs:1721`) | returns the cert | as-is | **done** | — | — |
| `assert_def_eq_only` (`tc.rs:1730`) | cert + counted drop | should lose its callers as consumers appear | the drop adapter; 23 sites total (`tc.rs` 1 + `quot.rs` 6 + `inductive.rs` 10 + `assert_def_eq` proper) | Dropped ledger | per-site |

### 1.5 Reduction helpers (`tc.rs:1880–2048`)

| fn | today | notes | status |
| --- | --- | --- | --- |
| `reduce_rec` (`tc.rs:1945`) | iota reduct; certificate handled by `Rule::Iota` → `Certifier::iota` (real trait rule, backend defaults to admit) | the *internal* uses of `whnf(major)`, `to_ctor_when_k`, `iota_try_eta_struct` all discard evidence that the iota rule's eventual derivation will need (the major-premise normalisation legs) | partial — trace covers the outer step; inner legs unthreaded, currently moot because `TgBackend` has no iota derivation to feed |
| `to_ctor_when_k` (`tc.rs:1889`) | `infer_then_whnf` + `def_eq(major_ty, new_type)` both discarded (`Dropped::DefEqSide`) | licenses replacing the major premise for K-recursors; the discarded equality is exactly the evidence a future iota-K rule needs | none — Dropped |
| `iota_try_eta_struct` (`tc.rs:1923`), `expand_eta_struct_aux` (`tc.rs:354`), `mk_nullary_ctor`, `is_ctor_app`, `get_rec_rule`, `get_applied_def` | shape probes / constructions | evidence-free by nature or blocked on inductive interpretation | — |
| `reduce_quot` (`tc.rs:1979`) | quot iota; `Admit::Quot` step in trace | needs interpreted `Quot` — not threading | — |
| `try_reduce_nat` / `do_nat_bin` (`tc.rs:483–561`) | native arithmetic; `Admit::NatRed` | milestone 4 | — |
| `reduce_proj` (`tc.rs:563`) | projection reduct; `Rule::ProjRed` step, asked of `Certifier::proj_red` | the reduction *as a reduction* needs interpreted structures; the case where both endpoints are proofs does not, and `proj_red_step` infers both and hands over Theorem 6.7's premises | done for the proof case (650 → 630 on ip; the residue is interpretation scope) |
| `strong_reduce` (`tc.rs:1006`) | debug-only, dead code allowance | out of scope | — |

### 1.6 The predicates (`tc.rs:2331–2346`) — small functions, outsized leverage

| fn | today | should return | status | instead |
| --- | --- | --- | --- | --- |
| `is_proposition` (`tc.rs:2338`) | `(bool, T)` via `infer_ty(…, Dropped::DefEqSide)` + `is_sort_zero` | `(bool, T, Option<⊢ ⟦T⟧ ∈ U₀>)` — witness on the `true` branch only (`false` licenses nothing; verified: every caller uses `true` to enable something and `false` to fall through) | none | the witness is re-derived by `has_type_a(ty, u0)` inside `derive_point_of_proof`; note `⟦Sort 0⟧ = U₀` *by the interpretation*, so `infer`'s `⟦T⟧ ∈ ⟦Sort 0⟧` cert **is** the witness — no new derivation needed, only non-discarding |
| `is_proof` (`tc.rs:2343`) | `(bool, T)`, both `infer` certs dropped | `(bool, T, Option<(⊢ ⟦e⟧ ∈ ⟦T⟧, ⊢ ⟦T⟧ ∈ U₀)>)` on the `true` branch | none | same double-derivation loop as `proof_irrel_eq` above |
| `is_sort_zero` (`tc.rs:2331`) | bool; whnf leg dropped | the whnf equality should ride along so the witness above is stated at the right term | none | silent |

### 1.7 `inductive.rs` and `quot.rs`

`inductive.rs` is within 25 diff lines of upstream — the evidence work has not
touched it, deliberately. Its 10 `assert_def_eq_only(…, Dropped::Inductive)`
sites (`inductive.rs:387,820,1207,1223,1246,1263,1617,1625,1669,1688`), its 10
`whnf` calls and its `ensure_sort`/`ensure_infers_as_sort` calls all discard
(950 inductive-telescope drops + share of `BinderSort` on init-prelude).
`quot.rs` likewise: 6 shape checks, `Dropped::Quot` (6 on ip).

Verdict: **correctly unthreaded for now**. These checks establish that
declarations have expected shapes; the judgements a backend could consume
(constructor/recursor typings, quot computation rules) require the inductive
and quotient *interpretations*, which do not exist yet. When they do, this file
becomes the place that *produces* `ind_mems`/`CtorRule`-grade facts instead of
`tg.rs` reconstructing them per-inductive — that is a large D-item, but it is
milestone-scoped (interpretation of inductives), not threading debt. Until
then, threading evidence through 1 700 lines of telescope manipulation would
produce certificates with no consumer.

### 1.8 Binder open/close (`util.rs:680–730`)

| fn | today | should do | status |
| --- | --- | --- | --- |
| `mk_dbj_level` (`util.rs:680`) | mints a `Local` carrying its `binder_type`; no kernel-side event | **open**: also acquire `⟦w⟧ ∈ ⟦A⟧` (kernel `assume`, or at least register the hypothesis in a checker-side context stack that whnf/def_eq/has_type can *read* instead of guessing) | none |
| `replace_dbj_level` (`util.rs:725`) | pops the counter | **close**: discharge — `implies_intr` + `gen` (kernel), or pop the context stack | none |
| `mk_unique` (`util.rs:710`) | free locals for inductive/quot telescopes — opened, never closed | see §3: these are the only genuinely ambient locals | — |

Key verified fact: **the binder that introduces `w` always knows `A`** — every
`Local` node carries `binder_type`, and both open paths (`mk_dbj_level`,
`mk_unique`) take it as an argument. The backend's `ty_local` and
`has_type_local` already state the hypothesis off the local's *own declared
type*, never off the obligation's target. What is missing is purely that the
hypothesis is acquired per-consumer (and, in the search, *guessed* per-argument
by `local_premises` scanning the term) instead of once at the open.

### 1.9 Backend counterparts (`tg.rs`) — what consumes vs what re-derives

* **Consume threaded evidence (target-shaped):** `ty_sort`, `ty_const`
  (lookup), `ty_local`, `ty_conv`, `ty_app`, `ty_lam`, `ty_let`, `ty_proj`,
  `ty_pi`, `typing` (single-exit guard), `declar_checked` →
  `store_declar_typing` (reads the handed-in cert; the 36 %-of-runtime search
  it replaced is gone — verified in code and `MEASUREMENTS.md` "Inference
  carries its evidence": 1 645 searches, 1 633 failures, removed; runtime
  16.0 s → 11.87 s).
* **Still search (the scaffolding to delete):** `has_type_h` / `has_type_a` /
  `has_type_uncached` and clauses (`has_type_const`, `has_type_app`,
  `has_type_pi`, `has_type_lam`, `has_type_lam_prop`, `has_type_ctor_app`,
  `has_type_local`, `has_type_proj`, `has_type_target_beta`,
  `target_head_step`, `target_mem`, `assumed`), plus `syn_type` /
  `syn_type_proj` / `expose_pi` / `typeable_shape` (the delta-only shadow
  type-inference that exists *only because* the search may not re-enter the
  checker), plus `local_premises` / `collect_locals` (the context guess) and
  `domain_obligation` (the beta-obligation driver). Per the owner's framing
  these are workarounds for incomplete threading; each §2 stage below names
  which of them it starves.
* **In between:** `point_of_proof` / `derive_point_of_proof` / `proof_eq` — a
  real derivation, currently fed by the search; after §1.6 threading it is fed
  by inference and only its `u0_subsingleton` composition remains.
* `discharge_families` at the `cert` funnel — the consumer for hoisted escaped
  assumptions, **measured to fire zero times** (module doc, table "offered
  1 378 / derived under the guard 0"): evidence that retry-search at the
  boundary cannot replace threading, which is the strongest single empirical
  argument for the target design in the tree.

---

## 2. Staging order

The owner's sketch (binder open/close → whnf → def_eq) is broadly right, but
two cheap stages come before the binder work, and the binder work hides the one
real design decision. Proposed order, each stage with the measurable that must
move — and the standing rule that **a stage after which `has_type` searches /
escapes do not fall has left a specific edge unthreaded**, which the per-clause
`HtClause`/`HtMiss`/`Dt` counters will localise.

**Stage 0 (mechanical, immediate): stop discarding what already has a
consumer. — LANDED 2026-08-01.**
(a) `is_proposition`/`is_proof` return their witnesses (§1.6); (b)
`proof_irrel_eq` passes them plus its type-equality cert to a new
`Certifier::proof_irrel` rule whose `TgBackend` implementation is
`proof_eq` minus the two `has_type_a` calls; (c) `def_eq_proj` composes a
`proj`-congruence from its structures' cert instead of `Admit::Proj`; (d)
`try_eta_expansion_aux` composes its discarded recursive cert so that only the
genuine `λz. y z ≡ y` step remains admitted.
*Measurables as proposed:* `has_type` calls from `point_of_proof` → 0 (the
`points` memo population); `Admit::Proj` 16 → 0; `Admit::ProofIrrel` becomes a
real-rule count; `Dropped::DefEqSide` falls from 4 804 by the share these sites
hold.

*What actually happened, on `init-prelude`.* All four items are in.
`Admit::Proj` 17 → 0, of which 16 are now derived and one is a premise hole.
`Admit::ProofIrrel` 7 → 0. `Dropped::DefEqSide` 7 632 → 272, and the ledger
grew two variants — `Probe` and `Predicate` — because the label was naming two
things it did not describe. Gaps 15 492 → 15 423, escapes 2 153 → 2 138,
runtime unchanged; on the tutorials exactly one file moved,
`101_proofIrrelevanceWhnf` 5 → 0, at each of `DEFAULT_LEVELS` `[0]`, `[1]` and
`[0,1]`.

**Three things the proposal got wrong, and they matter for the later stages.**

1. **`point_of_proof` has three askers, not one.** A new `Pop` ledger splits
   them. Proof irrelevance is at **0** and pinned there by a test. The other
   two are not stage 0's: 41 come from `point_the_subject` inside
   `has_type_lam_prop` — the search asking itself — and 34 from the `beta`/
   `zeta`/`delta`/`iota` proof shortcuts, which are rules deriving their own
   claims. So "→ 0" is met for the clause the stage owns and is a stage-1/2
   measurable for the rest.
2. **Threading does not dominate the search, and the ledger says exactly
   where.** Of the three proof-irrelevance sites that still gap, `⟦e⟧ ∈ ⟦α⟧`
   arrives every time and `⟦α⟧ ∈ U₀` is a hole every time — because
   `infer(α)`'s own certificate is a hole, which is mostly §3's `ty_const`
   store-miss residue — 2 674 of 2 891 declaration typings have no certificate
   at all — but not wholly: 198 were derived and thrown away, and that part *is*
   threading debt. The `Dt` ledger splits the two (`Dt::Gap` against
   `Dt::Conditional`); see `MEASUREMENTS.md`, "The declaration-typing ledger,
   read as a completeness measure". The searched route failed on the same three,
   so nothing was lost; the *reason* is now named instead of being a failed
   search.
3. **`TgBackend::admit` was guessing, and that is now deleted.** It tried
   `proof_eq` before reporting a gap and rescued any step whose two sides
   happened to interpret to `•`. Measured: **20 steps a run, every one
   `Admit::ProjRed`** — a projection reduction with no certificate, recorded as
   derived. Removing it takes gaps 15 423 → 15 455 (+20 primary, +48 cascade)
   and escapes 2 138 → 2 102 (the rescue manufactured conditional certificates
   that then escaped), and on the tutorials `125_quotIndReduction` stops
   reporting zero and reports its two `Admit::Quot` gaps. **A fallback is, by
   construction, the label of the site that noticed** — the rise is the
   correction, not a regression.

Nothing here risked breakage: all additions are new rule methods with
default-gap fallbacks, the existing pattern.

**Stage 1: binder open/close.**
Move context from per-consumer acquisition to per-binder open/close. Two
sub-decisions, and this is where D lives:
* *Representation.* Kernel hypotheses (`assume`/`implies_intr`) give constant
  cost per step but are **exactly what the memos must refuse**
  (`hypothesis_free` guard, `certify.rs:605`; `certify_reduct`'s store guard,
  `tc.rs:1292`): a `Γ ⊢ a = b` under an `ExprPtr` key silently imports `Γ`.
  Formula-level antecedents (the current `CondEq` discipline) are cacheable and
  escape-accounted but cost O(|assumptions|) per rule application and force the
  whole `u_*`/`reassume`/`merge_hyps` apparatus. The likely resolution — use
  kernel hyps *while under binders* and `implies_intr`+`gen` back to closed
  form at every memo write and at close — needs an explicit decision, because
  it changes what the caches can hold and the escape ledger's meaning. It also
  requires relaxing or relocating the `check-boundary.sh` ban on
  `Thm::assume` outside `kernel/`.
* *Plumbing.* A context stack beside `dbj_level_counter` in `TcCtx`
  (open pushes `(local, ⟦w⟧ ∈ ⟦A⟧ evidence)`, close pops and discharges),
  readable by the backend, replacing `local_premises`' term-scan guess.
*Measurables:* escapes (1 484 on ip) must fall — every escape today is an
assumption no binder discharged, and after this stage an assumption about a
checker-opened local *has* a discharging binder by construction; `HtMiss::Local`
(5 186) must fall to the genuinely-ambient residue (§3); `Admit::Cache` 272
(conditional union-find edges) should shrink as fewer certs are conditional at
cache-write time. If escapes do not fall, the leak is a consumer path that
still calls `has_type_a(…, &[], …)` — grep-auditable.

**Stage 2: `whnf` takes and returns evidence.**
Signature per target: `whnf(e, ⊢⟦e⟧∈⟦T⟧) → (e', ⊢⟦e⟧=⟦e'⟧)` (the equality
already exists via traces; the *new* content is the typing input). Internally,
the typing must flow *down the reduction*: when `whnf` beta-contracts
`(λx:A.b) a`, the typing of the application yields the typing of `a` at `A` —
which is precisely what `domain_obligation` currently searches for and, with
stage 1, what the open-binder context supplies for local-headed arguments.
Mechanically: `whnf_reduce`'s loop threads a typing alongside the cursor
(subject reduction, one Leibniz per step); `Certifier::beta` grows a typing
parameter; the 28 call sites split into evidence-carrying (inference,
`ensure_*`) and don't-care (`inductive.rs`, until inductives are interpreted).
Also closes §1.2's `ensure_pi` hole: `infer_app` composes the reduction leg
into the head typing via `ty_conv`, retiring `ty_bridge`'s delta-only rescue.
*Measurables:* `note_ht_raw` (raw-fallback hoists) and `domain_obligation`'s
search count must fall hard — this is the stage that attacks the 17 537
obligations directly; `ty_premise_missing` (4 503) and `ty_app` (45) fall as
the `ensure_pi` leg is composed; escapes continue down. Residual misses should
be dominated by opaque-constant heads (§3) — if local-headed misses remain,
stage 1's context is not reaching the reduction path.

**Stage 3: `def_eq` takes typings.**
`def_eq(a, b, ta, tb)` and thread to: `proof_irrel_eq` (already fed by stage
0 at the leaves, now without re-inferring), `def_eq_unit`, `try_eta_struct`,
`to_ctor_when_k`, and the whnf calls inside (stage 2's input). Under binders,
`def_eq_binder_aux` extends the typings as it opens — stage 1's machinery.
This is mostly mechanical after stages 1–2; the reason it goes last is that
its payoff (retiring `infer_ty(…, Dropped::DefEqSide)` — the sites at
`tc.rs:424,470,478,583,990,1008,1897,1903,1927,1931,2339,2344,2370`) is
re-*inference*, which is memoised and cheap, so it moves correctness-shape
(`Dropped::DefEqSide` 4 804 → ~0) more than it moves search counts.
*Measurables:* `Dropped::DefEqSide` → ~0; the remaining `Admit` rows are then
exactly the interpretation-scope list of §3, i.e. the admit report becomes a
pure milestone ledger with no threading debt in it.

**Explicitly not in the order:** improving `has_type` (owner's decision: it is
provisional scaffolding; stages 1–2 starve its two entry pressures —
`domain_obligation` and `point_of_proof` — after which what remains of it
serves only obligations about uninterpreted inductives, and it can be deleted
with them); `Dropped::BinderSort` (33 587) — most of these certify "domain is a
type", whose only foreseeable consumer is `point_of_proof`-style reasoning
already served by stage 0's witness threading at far fewer sites.

---

## 3. The residue — what genuinely cannot be threaded

1. **Ambient context locals: mostly *not* residue.** Checked as the task asked:
   every `Local` carries its `binder_type`; every local the checker itself
   opens (`mk_dbj_level` in `infer_lambda`, `infer_pi`, `def_eq_binder_aux`)
   has a closing binder where `implies_intr`+`gen` (or the formula-level
   equivalent) can discharge. The 5 186 "local at the top level" `has_type`
   misses arise because the search is entered with `assms = []`
   (`domain_obligation`, `derive_point_of_proof`) even when the checker is
   under open binders — unthreaded, not residue. The **genuine** residue is the
   `mk_unique` locals of `inductive.rs`/`quot.rs` telescopes: opened with a
   known type but never closed into a λ, so their typings stay ambient — and
   Carneiro's context-relative reading says that is the correct final state
   for them: the facts are hypotheses of the surrounding (meta-level) check,
   not theorems. Today they have no consumers anyway.
2. **`TyGap::PiUndet` — real, and bounded.** `imax u v` at a level parameter is
   neither §6.2 clause; no per-declaration interpretation can choose
   (`certify.rs:844` gives the argument). The level-instantiation pre-pass
   already collapses this at ground σ; what remains is the recursor's
   eliminator universe and declarations checked at their own parameters. This
   is residue of the *per-instantiation* strategy, not of threading, and it is
   closed by scheduling, not evidence.
3. **Uninterpreted inductives/constructors/recursors and structures.** ~3 850
   opaque-head obligations, `ty_const` store misses,
   `Admit::ProjRed`/`Quot`/`EtaStruct`/`UnitLike`, iota's default-admit. No
   axioms exist about these symbols, so no threading can manufacture the facts —
   this is interpretation scope (INDUCTIVES.md), and the correct current
   behaviour (decline + count) is what the code does.

   **Two corrections to this item, both measured.** (a) The `ty_const` misses
   are not all residue: 198 of 2 891 declaration typings were *derived and
   discarded*, and 1 161 use-site misses are against those. `Dt::Gap` against
   `Dt::Conditional` is where the line is drawn. (b) `Admit::ProjRed` is
   *partly* out of this list. The reduction as a reduction still needs
   interpreted structures — 630 of them do — but the case where both endpoints
   are proofs needs nothing about projections at all, and `Certifier::proj_red`
   closes it from premises the checker infers. 650 → 630.
4. **True axioms.** `propext`, `Classical.choice`, `Quot.sound` must remain
   assumptions of the model forever — but measured to head **zero** typing
   obligations on init-prelude, so they cost nothing today.
5. **Literals (`TyGap::Lit`, `Admit::NatRed`/`NatEq`/`StringLit`) and level
   algebra** (`sort/const equality modulo level algebra` admits): milestone-4
   primitives and translator-side level normalisation respectively. Not
   threading.
6. **Eta** needs a function-extensionality lemma (`TgBackend::eta` admits) —
   library work; the threading half (composing the discarded recursive cert)
   is stage 0.

No part of the target design looked *unworkable* in this survey. The one place
the design is under real tension is stage 1's cache-vs-hypotheses decision
(§2): kernel-hypothesis evidence and `ExprPtr`-keyed global caching are
mutually hostile, the guards that keep them apart exist and fail closed, and
the resolution (discharge at every memo boundary) is coherent but has a cost
that should be measured before being committed to — the project's own history
(four refuted readings recorded in `tg.rs`'s module doc) argues for measuring
first.

---

## 4. Scale

* **Functions.** `tc.rs`: 85 `fn`s, of which ~55 participate in checking with
  an evidence-relevant role (the census above names every one with a non-empty
  "should" column; the rest are constructors/plumbing). `inductive.rs`: ~45
  fns, all currently and correctly drop-only. `quot.rs`: 2. `tg.rs` backend:
  ~12 consumer rules in place, ~20 search/shadow functions slated to shrink or
  die as stages land.
* **Call sites touched by the remaining stages.** Stage 0: ~8 sites in
  `tc.rs` + 2 new trait methods. Stage 1: 2 functions in `util.rs`, the ~6
  open/close loops in `tc.rs`, every `has_type_a(…, &[], …)` entry in `tg.rs`
  (4), plus the cache-guard audit (3 stores, already enumerated in
  `certify.rs:589`). Stage 2: `whnf`'s 28 callers (18 `tc.rs` — mostly
  mechanical re-wraps; 10 `inductive.rs` — can take a don't-care adapter),
  `Certifier::beta`'s signature, `whnf_reduce`'s loop. Stage 3: `def_eq`'s
  26 references in `tc.rs`, 13 `Dropped::DefEqSide` sites.
* **Diff against upstream (`vendor/nanoda_lib-upstream`, verified by direct
  diff).** Today: `tc.rs` 1 537 changed lines (1 324 → 2 387), `util.rs` 124,
  `inductive.rs` 25, `quot.rs` 13, `expr.rs`/`env.rs` 0; new files
  `certify.rs` 1 043, `reduct.rs` 159, `union_find.rs` 305,
  `instantiations.rs` 511, `stepcount.rs` 130, `tg.rs` 14 983 (+ `kernel/`,
  `derived/` crates). The remaining threading concentrates where the diff
  already is: expect `tc.rs` to grow by a few hundred lines (signatures +
  composition at 28 + 26 call sites), `util.rs` by the context stack,
  `inductive.rs` to stay near-pristine until inductives are interpreted, and
  `tg.rs` to *shrink* as the search family and its shadow inference lose their
  callers — which is the point.

---

## 5. Stale documentation passed en route

1. `tg.rs`, `has_type_local` doc: "This kernel has no context — a `Thm` is a
   closed formula". False since `Thm` became a sequent
   (`kernel/src/thm.rs:59` states the opposite in bold). (As flagged in the
   task; confirmed.)
2. `tg.rs`, `ty_local` doc: same claim, second occurrence — "The kernel has no
   context — a `Thm` is a closed formula".
3. `certify.rs:926–931`, `Dropped::DefEqSide`: "…where the conclusion drawn is
   itself an admit". Stale twice over: (a) `TgBackend::admit` now routes
   through `proof_eq` and *derives* proof irrelevance where it can
   (`tg.rs`, `Certifier::admit` impl), so the conclusion is not always an
   admit; (b) the variant's site list omits `infer_proj` and `infer_let`/
   `strong_reduce`/`is_proposition`/`is_proof`, which also drop under this
   label despite not being "inside a definitional-equality rule".
   **Fixed by stage 0, and it was worse than "stale": the claim that these
   sites' evidence "has nothing to compose with" was *false* for two of them.
   `def_eq_proj`'s premise is the projection congruence and `eta`'s recursive
   comparison is half of eta's own conclusion. Both are rule premises now.**
   (b) is fixed by splitting `Dropped::Probe` and `Dropped::Predicate` out. And
   (a) has itself gone stale in the other direction: `Certifier::admit` no
   longer routes through `proof_eq` at all — see §2, stage 0, item 3.
4. `certify.rs:310` (`ty_const` doc) says the stored typing is "not a walk
   down the delta graph" — true of `ty_const`, but `has_type_const` still
   walks the delta graph as its fallback (by design, per the `028_peano2`
   measurement); a reader of `certify.rs` alone would conclude the walk is
   gone entirely.
5. `certify.rs:423`: "a 1300-line type checker" — `tc.rs` is 2 387 lines.
   Trivial, but it dates the paragraph.
6. `tc.rs:310` and `tc.rs:583`: `Dropped` site labels (`BinderSort` for a
   declaration type; `DefEqSide` for a projection-inference subject) misname
   what is being dropped, which will misattribute ledger counts as those rows
   shrink.
7. Accurate-but-worth-rechecking: the "28 callers" claim at `tc.rs:1077`
   currently matches (18 + 10, verified); it will silently rot when stage 2
   lands.
