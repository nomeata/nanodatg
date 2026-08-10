# Threading census — evidence in and out of every type-checker operation

*2026-08-01, re-taken in full 2026-08-09 against `8d2b9c9`. Survey of
`checker/src/` against the target design: every operation takes evidence of its
precondition and returns evidence of its postcondition, so that no fact is ever
re-discovered by heuristics or search.*

> **Status, 2026-08-09 — live as a work plan.**
> This census was marked "superseded as a work plan" on 2026-08-06, on the
> premise that the project's answer to the threading debt was `mini/` — an
> engine built so the debt cannot arise. That premise is dead:
> `MATCHER-WALL.md` (2026-08-09) measured that `lean-mini-kernel`, the upstream
> `mini` is a fidelity port of, checks the whole 1,245-declaration
> `init-prelude` residue in 805 G instructions where `mini` dies at declaration
> 232 — with 47.4 % of `mini`'s samples in `kernel/`, 44.0 % in glibc
> malloc/free and 1.58 % in `mini/` itself. The owner's decision (2026-08-09):
> mini keeps the inductive handler, **the checker does declarations**. So the
> debt catalogued here is back on the critical path, and §2 is again the plan.
> Stage 0 landed (2026-08-01); stages 1–3 have not: `TcCtx` has no context
> stack, `crate::scope` has no shipped caller (its own header says so,
> re-verified), `whnf` is still `fn whnf(&mut self, e: ExprPtr) -> ExprPtr`
> (`tc.rs:1389`) and `def_eq` still takes two arguments (`tc.rs:1884`).

**Method and caveats.** Every `file:line` citation below was re-read in the
code at `8d2b9c9` on 2026-08-09; none is inherited from the 2026-08-01 survey.
Every `init-prelude` ledger number below marked **(ip)** is from a fresh run
taken for this re-survey: `nanoda_bin`, `release`, `--features tg,stepcount`,
the `scripts/arena.sh` config (nat/string extensions on, axioms permitted),
197.9 G instructions (`perf stat -e instructions`; 198.2 G without
`stepcount`, and the `tg` ledgers of the two runs agree row for row). Numbers
quoted from `MEASUREMENTS.md` are identified by their entry date and were
**not** re-measured; the tutorial-corpus and arena per-file verdicts were not
re-run. `tg.rs` is cited by function name with the line as of `8d2b9c9`; it is
the file most under edit, so its lines will drift first. Note there is no
`infer.rs`: inference lives in `tc.rs` (`TypeChecker::infer` and its `infer_*`
rules). Where a sentence is inference rather than verification, it says so.

The two scoping observations from the target design both check out in the code,
with one important qualification each:

* **Evidence only on the licensing branch** — confirmed everywhere the code is
  already threaded: `DefEq = Option<Cert>` with `None` = "not shown equal,
  i.e. reject" (`certify.rs:836–839`), and `Typed.cert` never optional but
  `ty_gap` a value (`tc.rs:59–92`). The reduction plumbing uses an `Option`
  of the **opposite polarity**, and conflating the two was an error in the
  first edition of this bullet: for the `DefEq` returned by the whnf-leg
  helpers, `None` means *no step was taken, reflexivity applies* — it never
  means "not equal" (`tc.rs:1179–1182`, stated as the convention for
  `seq`/`compose_legs`/`compose_whnf_legs`). Qualification: several
  *negative-looking* branches feed an affirmative conclusion one level up
  (e.g. `def_eq_unit` returning `None` merely falls through to other rules
  that may still say yes), so "negative needs nothing" is per-*conclusion*,
  not per-function — the census below marks the branch that actually licenses.
* **The enabling mechanism exists but is unused in shipped code** — verified:
  `kernel/src/thm.rs:624,641` (`assume`, `implies_intr`); `Thm` is a sequent
  with `hyps()` (`thm.rs:310–320,382`). Today all binder-context evidence is
  carried as *formula-level* antecedents (`⊢ conj(hs) → φ`, the
  `CondEq`/`u_*` discipline), at O(|hs|) cost per inference step, with
  `guard_and_generalise_at` re-implementing at the formula level exactly what
  `implies_intr` + `gen` do at the kernel level. So "hold assumptions at
  constant cost" is available and not yet taken.

  The boundary question this bullet flagged was answered at `a52e553`
  (2026-08-01): `ci/check-boundary.sh` R6′ allowlists one named introduction
  module per crate and *fails if that module stops calling `Thm::assume`*.
  For `checker/` that module is `src/scope.rs` — the open/close API stage 1
  below needs, written and tested, still with no shipped caller (its module
  header carries the grep and the invariant argument, re-verified at
  `8d2b9c9`).

---

## 1. Per-function census

Column key. **Should take / should return**: the evidence per the target
design. **Status**: `done` = threaded; `partial`; `none`. **Instead**: how the
fact is currently recovered — `has_type` search (`TgBackend::has_type_a` and
family), `syn_type` delta-only re-walk, a `Dropped` ledger entry
(`certify.rs:1155`, six variants: `Quot`, `Inductive`, `DefEqSide`,
`BinderSort`, `Probe`, `Predicate`), an `Admit` (`certify.rs:861`, sixteen
variants, of which `Binder`, `App`, `Proj`, `ProofIrrel`, `ProjRed`, `Iota`
and `Whnf` are no longer raised by the checker — the first two retired by
congruence rules, the next four turned into backend rules whose *defaults*
admit under the same reason string, `Whnf` a bug report pinned at zero), or an
escaped assumption. **Difficulty**: M = mechanical, D = needs a design
decision.

**(ip)** totals for orientation: 15 423 gaps, 2 138 escapes, 149 682 real
kernel theorems; 161 815 certificates from real rules against **318** admitted
(`eq_cache` 260, `nat_eq` 44, `nat_reduce` 8, `eta_struct` 6, every other
variant 0). Dropped: `BinderSort` 66 594, `Inductive` 950, `Probe` 802,
`Predicate` 774, `DefEqSide` 272, `Quot` 6.

### 1.1 Entry points (`tc.rs:236–403`)

| fn | today | should take / return | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `check_declar_at` (`tc.rs:255`) | per-σ dispatch; for value-bearing declars composes `infer`'s cert with `assert_def_eq`'s via `ty_conv` and hands `⊢ ⟦val⟧ ∈ ⟦ty⟧` to `declar_checked` | exactly what it does | **done** (`tc.rs:261–279`) — the model case | — | — |
| `check_declar_info` (`tc.rs:385`) | checks `infer(d.ty)` is a sort | should return `⊢ ⟦d.ty⟧ ∈ ⟦Sort l⟧` (and for theorems the `l = 0` witness that licenses "this constant is a proof" downstream) | none — result discarded via `infer_ty(…, Dropped::BinderSort)` at `tc.rs:389` | Dropped ledger; the site label `BinderSort` is a misnomer here (a declaration type, not a binder domain), now documented at the variant (`certify.rs`, `Dropped::BinderSort` doc) but not corrected | M |
| `check_declar_all` / `check_all_declars*` (`tc.rs:305–372`) | scheduling only | nothing | n/a | — | — |

### 1.2 Inference (`tc.rs:407–1081`) — the mostly-done tier

`infer` (`tc.rs:717`) returns `Inferred { ty, cert }`; the memos store the cert
(`util.rs:920–921`), with confinement checked in debug builds by
`typing_is_confined` (`tc.rs:775–778`). Verified. **(ip)**: 14 371 typings
carried out of inference unconditionally, 32 829 conditional on the ambient
locals, 43 110 with no evidence.

| fn | today | should return, on which branch | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `infer` (`tc.rs:717`) | `(T, ⊢ ⟦e⟧ ∈ ⟦T⟧)` | as-is | **done** (gaps are named values, `TyGap`) | remaining gaps are per-rule, below | — |
| `infer_ty` (`tc.rs:792`) | `infer` + counted discard | should eventually have no callers | the *discard adapter*; counting its wrappers `infer_sort_of`/`infer_then_whnf`/`ensure_infers_as_sort`, 20 `Dropped`-passing call sites in `tc.rs` (one line carrying two) and 2 in `inductive.rs` | Dropped ledger (66 594 `BinderSort` + 802 `Probe` + 774 `Predicate` + 272 `DefEqSide` on ip) | site-by-site |
| `infer_sort` (`tc.rs:796`) | cert via `ty_sort` | as-is | done (backend derives via `x ∈ U(x)`; 8 338 carried on ip) | — | — |
| `infer_const` (`tc.rs:407`) | returns substituted declared type; cert added by caller via `ty_const` | as-is | done as threading; the *backend* misses when no stored typing (20 929 `ty_const` no-evidence rows on ip). **Mostly but not wholly interpretation scope, §3**: of 2 891 (declaration, σ) pairs with a value, 2 674 have no certificate at all — cascade — but 198 had one that was *derived and discarded* because it stood under antecedents, which is threading debt. 1 161 of the 31 256 use-site misses are against those 198. All five numbers re-confirmed on the fresh run | store miss ⇒ gap (search already removed) | — |
| `infer_app` (`tc.rs:822`) | rebuilds spine cert via `ty_app`/`ty_conv`; `assert_def_eq`'s cert consumed by `ty_conv`; the argument's composed typing `⟦arg⟧ ∈ ⟦binder domain⟧` is additionally handed to the backend (`Certifier::app_arg_checked`, 2026-08-10) — built now even when the head's derivation is dead, because the beta rule is its second consumer (§1.3); when the head's type is not syntactically a `Π`, `ensure_pi_with_cert` returns the reduction leg and it is composed into the head's typing via `ty_conv` (built only when a derivation is live, so the null backend pays nothing) | exactly what it does | **done** (stage 2's first slice, landed 2026-08-09): `ty_conv` carried 31 → 142, `ty_app` no-evidence 481 → 418, and 7 declaration typings complete antecedent-free and store (19 → 26, cascade root 2 674 → 2 667). `ty_bridge` survives for the typings the leg does not reach. Cost: a conditional leg's antecedents are counted at the boundary (escapes 2 138 → 2 257 — the `ty_conv` borrow policy's over-report, stage 1's to discharge), +0.17 % instructions | residual `ty_app` 418 is backend scope | — |
| `infer_lambda` (`tc.rs:952`) | rebuilds λ/Π per binder, cert via `ty_lam`; binder-domain sort check dropped (`Dropped::BinderSort`, `tc.rs:959`) | as-is; the domain-sort evidence `⊢ ⟦A⟧ ∈ ⟦Sort u⟧` has its consumer served since stage 0 by `proposition_witness` (§1.6), so the residual value of threading it here is small | **partial** — typing threaded; domain-sort evidence dropped | Dropped `BinderSort` (the largest single share of 66 594) | M |
| `infer_pi` (`tc.rs:1008`) | cert is `ty_pi` with three-way clause label (`Pi`/`PiProp`/`PiUndet`, `tc.rs:1043–1049`, computed under σ) | as-is; the missing evidence (`dprod_in_universe` n-ary) is a *library* gap, not threading (8 798 `ty_pi` no-evidence rows on ip; `PiProp` 2 566 carried against 6 no-evidence — the `Prop` clause is essentially closed) | done as threading | — | library work |
| `infer_let` (`tc.rs:1058`) | expansion's typing via `ty_let`; the annotation check's certs dropped (`tc.rs:1068–1071`) | as-is (the dropped equality has nothing to compose with post-substitution — the argument stands at `tc.rs:1053–1057`) | done; drops counted | Dropped `BinderSort`/`Probe`/`DefEqSide` | — |
| `infer_proj` (`tc.rs:661`) | computes field type by whnf-walking the ctor telescope; cert added by caller via `ty_proj` | should return the field-type derivation so the backend need not recompute | **partial** — `TgBackend::ty_proj` *re-derives* the field type by `syn_type_proj` (delta-only) and declines when whnf was needed (126 `ty_proj` no-evidence rows against 646 carried on ip); also calls `is_proposition` bool-only up to three times (`tc.rs:664,686,701`); its structure-typing discard is now correctly labelled `Dropped::Probe` (`tc.rs:662`) | syn_type delta-only re-walk (`TgBackend::syn_type_proj`, doc: "delta-only transcription of `infer_proj`") | D — either thread the checker's telescope walk to the backend, or accept the recompute-and-check as the honesty mechanism |
| `ensure_sort` / `ensure_pi` / `infer_sort_of` / `ensure_infers_as_sort` / `infer_then_whnf` (`tc.rs:459–492,655`) | whnf + shape check; `ensure_pi` has a with-cert counterpart (`ensure_pi_with_cert`, fed by `whnf_with_cert` — the trace was always recorded, the composition now exists) consumed by `infer_app`; the rest still discard | should return `(Sort l / Π, ⊢ ⟦T⟧ = ⟦whnf T⟧)` | **partial** — `ensure_pi`'s leg composed at its one evidence-bearing caller; `ensure_sort`/`infer_sort_of`/`infer_then_whnf` still silent (their consumers are the `Dropped::BinderSort` sites, which have none) | the remaining four: nothing — silent | M, per remaining consumer as one appears |

### 1.3 Weak-head normalisation (`tc.rs:1153–1547`, `reduct.rs`)

Internally this is the best-instrumented tier: every reduction records a
`Trace` (rule + endpoints, `reduct.rs`), memos store trace beside reduct
(`util.rs:922–930`), and `certify_reduct`/`trace_cert`/`step_cert` turn a
trace into a certificate exactly once, guarded against endpoint drift and
against parking hypothetical certificates (`tc.rs:1282–1387`;
`hypothesis_free` at the one store write, `tc.rs:1372`). What is missing is at
the *boundary*, in both directions.

| fn | today | should take / return | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `whnf` (`tc.rs:1389`), `whnf_no_unfolding` (`tc.rs:1426`) | `ExprPtr` only; 28 callers (18 `tc.rs` + 10 `inductive.rs`, re-counted 2026-08-09 — the "28 callers" comment at `tc.rs:1156–1157` is accurate) | **take** `⊢ ⟦e⟧ ∈ ⟦T⟧`; **return** `(e', ⊢ ⟦e⟧ = ⟦e'⟧)` — then `⟦e'⟧ ∈ ⟦T⟧` by Leibniz. The typing *input* is what feeds beta's domain obligations (next row) | **partial** — evidence out exists on demand (`whnf_no_unfolding_aux_with_cert`, `tc.rs:1444`) and is consumed on `def_eq` paths only; evidence *in* does not exist at all | callers that need the equality either use the aux-with-cert path (def_eq) or drop it (all of inference, §1.2 last row); the typing precondition is re-discovered per beta step, next row | signature change M; feeding beta D (below) |
| beta steps inside whnf (`Rule::Beta` → `Certifier::beta` → `TgBackend::beta_step`) | the redex's argument typing `⟦a⟧ ∈ ⟦A⟧` arrives **threaded where the checker ever held it**: `domain_obligation` first reads `TgBackend::arg_mems` — the store `Certifier::app_arg_checked` fills at `infer_app`'s argument check with the very `ty_conv` composition (`⟦arg⟧ ∈ ⟦binder domain⟧`) the application rule consumes, now built whether or not the head's own derivation is alive — and only then falls back to `has_type_a`, `local_premises`, and the raw hoist | exactly what it now does for checked arguments; the residue is below | **partial** (handoff landed 2026-08-10; fixture `beta_domain_obligation_reads_the_application_checks_handoff`, three atoms, both mutations verified). Measured at `a7b0c6a`: 39 951 asked, 26 724 entries stored, **10 300 answered from the handoff** (102 outright + 10 198 under antecedents, 0 recalls failing their claim), escapes 2 257 → 2 247, gaps 15 542 → 15 532, +0.09 % instructions. The former claim "`infer` typed this very argument when the application was checked" is now **measured, and it is not universal**: the 20 328 remaining raw hoists split by cause into **32** handed off at another domain term, **1 640** whose argument was checked but whose typing was already a hole there (the `ty_const` cascade seen from the beta rule — §3 bucket (ii), and these convert to store entries by themselves when the shared constant store lands), and **18 656 about terms no application check ever visited** — probe-sampled: `Eq.refl`/`HEq.refl` constructor apps built by `to_ctor_when_k`'s K-shortcut, and minor premises inside *other declarations' values* entering by delta, instantiated at the current locals. No intra-declaration handoff reaches those two. **The second named unblock is now measured, and refuted (2026-08-10).** `Shared::typed_at` records every `(subject, target)` pair a typing rule concluded, with the declaration that concluded it; of the 18 656, **34** are memberships some declaration's inference did conclude (all 34 in an *earlier* declaration, 26 free of antecedents), **0** were concluded in the current declaration, and **18 622** were never a typing rule's conclusion anywhere on the thread. So cross-declaration evidence reaches 0.18 % of this population: what is missing is not the transport of a fact but the fact. **Re-asked at three weaker keys on 2026-08-10 and the answer holds** (§2): the *subject* at some other target reaches 460, the **generalised** membership with free variables abstracted away reaches **134**, and the beta rule's target-side twin reading the same handoff answers 145 and closes 0. Of 10 450 open subjects — substitution instances whose ground pair is absent by construction — 10 316 were never concluded at any generality at all. The probe is claim-checked and calibrated, not just run: every handoff recall is a pair `typed_at` must know (0 unknown over 10 300 recalls), and **11 031** typings were re-concluded at a pair an *earlier* declaration already held — so the interpreted key does cross declarations abundantly, and a small `earlier` row means the facts are absent, not that the keys fail to line up. `stepcount`-gated | residue: `has_type` search + raw hoist, now cause-attributed and reach-attributed in the ledger (`raw hoists by cause`, `of the never-checked …`) | **D** — stage 2 only |
| `whnf_reduce` / `whnf_no_unfolding_reduce` (`tc.rs:1396,1454`) | record traces; `Admit::Quot` and `Admit::NatRed` steps have no backend rule; `Rule::ProjRed` and `Rule::Iota` are backend rules since 2026-08-01 (`proj_red_step`, `iota_step`, §1.5) | as-is; missing pieces are backend rules (`quot` needs interpreted `Quot` — 0 quot steps fire on ip — `NatRed` is milestone 4) | done as threading | Admits, counted | out of threading scope |
| `certify_reduct` / `trace_cert` / `step_cert` / `seq` / `symm_leg` / `compose_legs` / `compose_whnf_legs` (`tc.rs:1195–1387`) | evidence plumbing, endpoint-checked | as-is | **done** (`Admit::Whnf` = bug report, at zero on ip). The reduct memos audited as caches of evidence 2026-08-10 — §1.10 | — | — |
| `unfold_def` (`tc.rs:2159`), `delta` (`tc.rs:2148`) | `delta` returns cert; `unfold_def` returns term, callers wrap in `Rule::Delta` trace | as-is | done | — | — |

### 1.4 Definitional equality (`tc.rs:1551–2572`)

`def_eq` returns evidence (`DefEq`), composes whnf legs on every exit, and
caches only unconditional certs on union-find edges (`tc.rs:1986–1998`,
gated on `certify::is_unconditional`). What it does **not** do is *take*
evidence: the target signature is
`def_eq(a, b, ⊢⟦a⟧∈⟦Ta⟧, ⊢⟦b⟧∈⟦Tb⟧) → ⊢ ⟦a⟧ = ⟦b⟧`, and the rules that need
typings re-derive them. **(ip)**: 111 235 `def_eq` calls, 99 034 answered from
the proof-producing cache.

| fn | today | should take / return | status | instead | diff. |
| --- | --- | --- | --- | --- | --- |
| `def_eq` (`tc.rs:1884`) | `(x, y) → DefEq`; affirmative branch carries cert, negative rejects (sound) | add the two typing inputs; thread them to the rules below and into whnf's beta obligations | **partial** — out: done; in: none | see per-rule rows | signature M; plumbing D |
| `def_eq_quick_check` / `def_eq_sort` / `def_eq_const` / `def_eq_binder_aux` / `def_eq_app` / `try_eq_const_app` / `lazy_delta_step` / `recall_eq` (`tc.rs:2192,2172,1736,1594,1758,2265,2388,2229`) | real rules: refl, `sort`, `const_eq`, `pi_cong`/`lam_cong` folds, `app_cong` folds, delta legs, explain-path composition | as-is | **done** — the certified core (161 815 certified vs 318 admitted on ip; `Binder`/`App` admits zero) | residual `Admit::Cache` 260 on ip = paths through union edges whose *conditional* cert the cache rightly declined (needs binder threading, not cache work) | — |
| `Bool.true` shortcut (`tc.rs:1907`) | composes `x ≡ x_n ≡ x_nn = y_n ≡ y`: the entry legs, the certified `whnf` trace (`whnf_with_cert`), and hash-consing making `x_nn` *be* `y_n`; reflexivity when no step was taken | exactly what it does | **done** (2026-08-09; was latent — 0 uses on ip — and is pinned by a fixture with a delta-only and a beta-carrying subject, `bool_true_shortcut_composes_its_legs`). `Admit::BoolTrue` no longer raised; the variant doc says so | — | — |
| `proof_irrel_eq` (`tc.rs:2534`) | `proof_witness` on both sides (`PropAt::Params`), `def_eq` on the two propositions, all three handed to `Certifier::proof_irrel` | exactly what it does | **done — stage 0.** Residue: `gap: proof_irrel` 3 on ip, each because `infer(α)`'s own `⟦α⟧ ∈ U₀` certificate is a hole (`Pop::NoProp`), which is §3's `ty_const` cascade, not this rule | — | — |
| `def_eq_local` (`tc.rs:1724`) | same id + `def_eq` on binder types, the types' cert handed to `Certifier::local_eq`, which splits on `LocalKey`'s own grain: same interpreted type — one variable, reflexivity derived; types merely def-eq — two variables, a counted gap under the old `def_eq_local` label (no rule relates two distinct free variables, and keying variables by def-eq class is exactly what `LocalKey` rejects) | exactly what it does | **done** (2026-08-09; was latent — 0 uses on ip). Both directions pinned by `def_eq_local_splits_along_the_local_key`, mutation-verified: a bare admit fails the refl half, a forged refl fails the residue half. `Admit::Local` no longer raised by the checker | residue: backend gap `def_eq_local` (0 on ip) | — |
| `def_eq_proj` (`tc.rs:1710`) | same idx + `def_eq(structures)`, the structures' cert handed to `Certifier::proj_cong` | exactly what it does — congruence over the `proj` symbol, no axiom about `proj` needed | **done — stage 0.** Residue: 1 `gap: def_eq_proj` on ip, a premise hole | — | — |
| `try_eta_expansion_aux` (`tc.rs:2548`) | the recursive `def_eq(x, λz. y z)` cert is handed to `Certifier::eta`, which composes it with the genuine eta step *inside* the rule (one gap, not gap-plus-trans) | as-is for the composition; the `infer_then_whnf(y)` typing is still dropped (`Dropped::DefEqSide`, `tc.rs:2550`) and is what the eventual eta lemma will want | **composition done — stage 0**; the eta step itself admits in `TgBackend` ("needs a function-extensionality lemma") — 0 eta steps fire on ip | backend admits; library work for the lemma | library |
| `try_eta_struct` / `try_eta_struct_aux` (`tc.rs:494–517`) | infers both types (`Dropped::DefEqSide` ×2, `tc.rs:503`), `def_eq` on types and per-field projections, all certs discarded → `Admit::EtaStruct` | the per-field certs + a structure-eta lemma | none | Admit (6 on ip) + Dropped | blocked on interpreted structures (§3) |
| `def_eq_unit` (`tc.rs:548`) | type inference (`Dropped::DefEqSide`, `tc.rs:549,557`) + `def_eq(types)` discarded → `Admit::UnitLike` | the type equality + a subsingleton lemma per unit-like structure | none | Admit (0 on ip) + Dropped | blocked on interpreted structures |
| `try_string_lit_expansion*` (`tc.rs:523–545`) / `def_eq_nat` (`tc.rs:1551`) / `delta_try_nat` (`tc.rs:2352`) | recursion certs composed; literal steps `Admit::StringLit`/`NatEq`/`NatRed` | as-is until milestone 4 primitives | partial (composition of recursive certs is correct; the literal steps themselves admit) | Admits (44 `NatEq` + 8 `NatRed` + 0 `StringLit` on ip) | milestone 4 |
| `assert_def_eq` (`tc.rs:1816`) | returns the cert | as-is | **done** | — | — |
| `assert_def_eq_only` (`tc.rs:1825`) | cert + counted drop | should lose its callers as consumers appear | the drop adapter; **17 call sites** (1 `tc.rs:1071` + 6 `quot.rs` + 10 `inductive.rs`, re-counted) | Dropped ledger | per-site |

### 1.5 Reduction helpers (`tc.rs:562–658, 2002–2170`)

| fn | today | notes | status |
| --- | --- | --- | --- |
| `reduce_rec` (`tc.rs:2067`) | iota reduct; certificate handled by `Rule::Iota` → `iota_step` (`tc.rs:1845`) → `Certifier::iota`, which since the general ι rule landed (`dd351ec`) is a **real derivation** in `TgBackend` (`derive_iota`): both sides contracted to the same term through the recursor's curried nest, 92 ι sites computed on ip | the *internal* uses of `whnf(major)`, `to_ctor_when_k`, `iota_try_eta_struct` still discard evidence (the major-premise normalisation legs); this was once moot for want of a consumer and is not any more — `derive_iota` exists, though its current derivations do not consume those legs | partial — trace covers the outer step; inner legs unthreaded. **(ip)** residue: `iota: no curried interpretation` 792, `major premise is not a constructor` 486 — interpretation scope, not threading |
| `to_ctor_when_k` (`tc.rs:2011`) | `infer_then_whnf` + `def_eq(major_ty, new_type)` both discarded (`Dropped::DefEqSide`, `tc.rs:2019,2025`) | licenses replacing the major premise for K-recursors; the discarded equality is exactly the evidence a future ι-K rule needs | none — Dropped |
| `iota_try_eta_struct` (`tc.rs:2045`), `expand_eta_struct_aux` (`tc.rs:433`), `mk_nullary_ctor`, `is_ctor_app`, `get_rec_rule`, `get_applied_def` | shape probes / constructions; `iota_try_eta_struct` drops two `infer_then_whnf` results (`Dropped::DefEqSide`, `tc.rs:2049,2053`) | evidence-free by nature or blocked on inductive interpretation | — |
| `reduce_quot` (`tc.rs:2101`) | quot iota; `Admit::Quot` step in trace | needs interpreted `Quot` — not threading; **0 quot steps fire on ip** | — |
| `try_reduce_nat` / `do_nat_bin` (`tc.rs:562–640`) | native arithmetic; `Admit::NatRed` | milestone 4 | — |
| `reduce_proj` (`tc.rs:642`) | projection reduct; `Rule::ProjRed` step, asked of `Certifier::proj_red` via `proj_red_step` (`tc.rs:1870`), which gathers `proof_witness` for both endpoints at `PropAt::Sigma` — premises threaded from inference, not searched | the reduction *as a reduction* needs interpreted structures; the case where both endpoints are proofs needs nothing about projections, and Theorem 6.7 closes it | done for the proof case (`gap: proj_reduce` 630 on ip; the residue is interpretation scope) |
| `strong_reduce` (`tc.rs:1085`) | debug-only, dead code allowance (`Dropped::Probe` at `tc.rs:1087`) | out of scope | — |

### 1.6 The predicates (`tc.rs:2453–2524`) — the stage-0 witnesses, landed

Stage 0 resolved this section's rows by *pairing* each bool-only predicate
with a witness-bearing counterpart rather than by changing the predicates —
the bool versions survive for the callers that gate checker verdicts, and
their discards are counted apart (`Dropped::Predicate`, 774 on ip).

| fn | returns | status |
| --- | --- | --- |
| `is_sort_zero` (`tc.rs:2453`) / `sort_zero_leg` (`tc.rs:2471`) | bool / the `Sort 0` reduct **with the reduction leg**, on the yes branch only | leg threaded |
| `is_proposition` (`tc.rs:2484`) / `proposition_witness` (`tc.rs:2497`) | `(bool, T)` with counted discard / `Option<⊢ ⟦e⟧ ∈ U₀>` — `infer`'s own certificate carried across `sort_zero_leg` by `ty_conv`, no new derivation | witness threaded |
| `is_proof` (`tc.rs:2509`) / `proof_witness` (`tc.rs:2520`) | `(bool, T)` with counted discard / `Option<Proof>` = both premises of Carneiro's Theorem 6.7, `⟦e⟧ ∈ ⟦α⟧` and `⟦α⟧ ∈ U₀` | witness threaded |

One design fact was found here that the original census did not know, and it
gates every future consumer of these witnesses: **"is this a proposition?" is
two different questions** (`PropAt`, `tc.rs:119–171`). The question that
decides what the checker *accepts* must be asked at the declaration's own
universe parameters (`Params` — `Sort u` at a parameter is not `Prop`, or a
declaration ill-typed at `u := 1` would pass); the question that produces
*evidence for the backend* must be asked under the ambient instantiation σ
(`Sigma` — `⟦Sort u⟧` is built through σ, so at σ = `{u ↦ 0}` it *is* `U₀`).
`proof_irrel_eq` uses `Params`; `proj_red_step` uses `Sigma`, and 20 closures
on ip exist only because of that split (`MEASUREMENTS.md`, "Projection
reduction is a rule", 2026-08-01). Mini has no σ layer, so `MINI-DESIGN.md`
§0.1's "there is only one classifier" is free there and is not free here.

### 1.7 `inductive.rs` and `quot.rs`

`inductive.rs` is within 25 diff lines of upstream (re-diffed 2026-08-09) —
the evidence work has not touched it, deliberately. Its 10
`assert_def_eq_only(…, Dropped::Inductive)` sites
(`inductive.rs:387,820,1207,1223,1246,1263,1617,1625,1669,1688` — re-verified
exact), its 10 `whnf` calls, its 2 `infer_then_whnf(…, Dropped::Inductive)`
sites (`inductive.rs:1069,1139`) and its `ensure_sort`/`ensure_infers_as_sort`
calls (`inductive.rs:401,431,828,878`) all discard (950 `Inductive` drops on
ip). `quot.rs` likewise: 6 shape checks, `Dropped::Quot` (6 on ip).

Verdict: **correctly unthreaded for now**. These checks establish that
declarations have expected shapes; the judgements a backend could consume
(constructor/recursor typings, quot computation rules) require the inductive
and quotient *interpretations*. Those have begun to exist since this was first
written — the general inductive path translates 283 declarations, mints 10 200
constructor rules and 5 general recursor nests on ip — but they live in
`tg.rs`/`derived/`, fed by the environment, not by anything `inductive.rs`
could hand over. When the interpretations need telescope-level facts, this
file becomes the place that *produces* them instead of `tg.rs` reconstructing
them per-inductive — a large D-item, milestone-scoped, not threading debt.
Until then, threading evidence through 1 700 lines of telescope manipulation
would produce certificates with no consumer.

### 1.8 Binder open/close (`util.rs:686–741`)

| fn | today | should do | status |
| --- | --- | --- | --- |
| `mk_dbj_level` (`util.rs:688`) | mints a `Local` carrying its `binder_type`; no kernel-side event | **open**: also acquire `⟦w⟧ ∈ ⟦A⟧` (kernel `assume`, or at least register the hypothesis in a checker-side context stack that whnf/def_eq/has_type can *read* instead of guessing) | none — `crate::scope::Scopes` is that stack, written and tested, unwired |
| `replace_dbj_level` (`util.rs:733`) | pops the counter | **close**: discharge — `implies_intr` + `gen` (kernel), or pop the context stack | none |
| `mk_unique` (`util.rs:718`) | free locals for inductive/quot telescopes — opened, never closed | see §3: these are the only genuinely ambient locals | — |

**The interpretation's own binder opens (2026-08-09).** `tg.rs` used to open
every binder it interprets under (`interp_lambda`, `interp_pi`, the
`term_clause` λ-arm) at a `mk_unique` local — a fresh kernel variable per
occurrence, so no memoised statement about an opened body was ever reachable
from a second occurrence, defeating for the interpretation's own population
exactly what `LocalKey` provides. They now open at an **expression-derived**
de Bruijn level (`TgBackend::open_level` — one more than the largest level the
expression embeds; memoised, a function of the node), keyed
`(level, ⟦type⟧)`, with the variable obtained *through the interpretation
itself* so it is the one the body's occurrences resolve to. Not the ambient
counter, deliberately: a counter-relative open made `⟦·⟧` depend on when it
was first asked and cost `073_boolRecEqns` a `pi congruence` gap; the
expression-derived level is depth-independent, needs no open/close
discipline, and coincides with the checker's own numbering on a closed
telescope. Measured on `init-prelude`: 100 853 opens mint / **213 705 reuse**
(68 %), the gap/derivation ledger unchanged row for row, obligations
discharged +8, and **instructions 198.97 G → 193.81 G (−2.6 %)**.
`mk_unique` remains at the reserve-first sites (`rec_nest`, `walk_spec`) and
the ambient `inductive.rs`/`quot.rs` telescopes — `rec_nest`'s positional
`cached.vars` hint is the cross-declaration identity `LocalKey` cannot
transport, and it is claim-checked by `nest_agrees` before any stored
statement is reused (task #135, determined benign).

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
  it replaced is gone — `MEASUREMENTS.md` "Inference carries its evidence":
  1 645 searches, 1 633 failures, removed); `iota` (a real derivation,
  `derive_iota`, fed by the general inductive apparatus rather than by the
  checker — `dd351ec`); and, since stage 0 and its follow-on: `proof_irrel`
  (both witnesses + the type equality), `proj_cong` (the structures' cert),
  `proj_red` (per-side proof witnesses).
* **Still search (the scaffolding to delete):** `has_type_h` / `has_type_a` /
  `has_type_uncached` and clauses (`has_type_const`, `has_type_app`,
  `has_type_pi`, `has_type_lam`, `has_type_lam_prop`, `has_type_ctor_app`,
  `has_type_local`, `has_type_proj`, `has_type_target_beta`,
  `target_head_step`, `target_mem`, `assumed`), plus `syn_type` /
  `syn_type_proj` / `expose_pi` / `typeable_shape` (the delta-only shadow
  type-inference that exists *only because* the search may not re-enter the
  checker), plus `local_premises` / `collect_locals` (the context guess) and
  `domain_obligation` (the beta-obligation driver). All re-verified present at
  `8d2b9c9`. Per the owner's framing these are workarounds for incomplete
  threading; each §2 stage below names which of them it starves.
  `MINI-DESIGN.md` §0 adopted this list verbatim as mini's negative
  specification; with the checker back on the critical path it is the
  checker's own deletion list again.
* **In between:** `point_of_proof` / `derive_point_of_proof` / `proof_eq` — a
  real derivation with a per-asker ledger (`Pop`). **(ip)**: 75 answers still
  come from searched premises (41 the search asking itself via
  `point_the_subject`, 34 the reduction rules' proof shortcuts, 0 from proof
  irrelevance — pinned by a test), 14 from threaded premises, 53 from the
  §6.2 split, 22 from the memo.
* `discharge_families` at the `cert` funnel — the consumer for hoisted escaped
  assumptions, **measured to fire zero times** (fresh run: 1 186 offered,
  1 144 with a free binder, 677 plain memberships, 0 derived under the guard,
  0 discharged): evidence that retry-search at the boundary cannot replace
  threading, which is the strongest single empirical argument for the target
  design in the tree.

### 1.10 The caches, audited as caches of evidence

*Added 2026-08-10.* The goal clause is "evidence passing, **including all its
cache**", and until now that half had never been audited as such. The standard
is `TgBackend::arg_mems`': **(a)** what is stored is a real theorem or a real
term, not a bare answer whose justification was thrown away, and **(b)** a
recall is *claim-checked* — re-checked against the statement the caller is
asking about now — with the disagreement counted, not argued away.

| cache | stores | recall | verdict |
| --- | --- | --- | --- |
| `infer_cache_check` / `infer_cache_no_check` (`tc.rs:735–803`) | `(ty, cert)` | the stored cert is returned, not recomputed (`tc.rs:735–742`) | **satisfied.** Conditional entries are stored deliberately and licensed by `typing_is_confined`, debug-asserted at the one write |
| `whnf_cache` / `whnf_no_unfolding_cache` (`tc.rs:1476,1531`) | `Reduct { reduct, trace }`, the trace carrying a lazily-filled certificate slot | `trace_cert` reads the slot; `certify_reduct` fills it, checking the endpoints against the trace first | **satisfied, and the residual reuse measured at nil** — see below |
| `eq_cache` (`tc.rs:1997–2230`) | union-find edges carrying certificates | `recall_eq` composes an explain path | **documented exception** — see below |
| `TgBackend::arg_mems` | `(Thm, hyps)` | `derived::establishes` at both ends, `ArgMem::Mismatch` 0 | **satisfied** — the standard |
| `TgBackend::has_types` | `(Thm, HtClause, hyps)` | **was checked at the write only**; since 2026-08-10 at both ends, 8 630 recalls re-checked, 0 mismatches | **satisfied** |
| `Shared::prop_exts` | was a bare `Thm` | — | **was the one field in `Shared` against the struct header's own "every `Thm` here is a `Sealed`" rule; now `Option<Sealed>`.** Moves no number today; the point is that it cannot start to |
| `Shared::false_anchor` | `Option<Sealed>` | had **no read site at all**, while its doc claimed `global_report` used it | **corrected**: the report now reads the field. `note_anchor()` runs one line *before* `Sealed::new`, so the 237 tally could not distinguish "derived and kept" from "derived and refused" |
| the other ~40 backend and `Shared` memos | terms, symbols, `u16` levels, declines | — | **structurally safe**: the key determines the value, or the value is not a theorem. Full sweep taken 2026-08-10; no trusted theorem recall found |

**The reduct memos, measured.** `reduct.rs`'s module doc promises "memoise a
result, memoise why": each reduct is reduced once and *derived at most once*.
The second half is true and worth almost nothing. New ledger row (`reduct memos,
as caches of evidence`, `certify.rs`): on ip the slot answers **19** asks
against **21 392** derivations; `certify_reduct` parks **912** and refuses
**9 295** as not being a live memo entry's root, of which only **72** are the
full-`whnf` memo's own root. Two repairs were tried and both are refuted:

* parking every derived node under `hypothesis_free` — the guard
  `certify_reduct` itself uses, which admits *conditional* certificates — took
  recalls 19 → 36 and blew the ledger up: copies 184 → 15 618, escapes
  2 247 → **17 670**, gaps 15 532 → **30 955**. A parked conditional certificate
  is a copy the escape ledger charges for and no rule consumes; this is the
  recorded 843 → 5037 lesson at ten times the size.
* parking only *unconditional* certificates, which cost no escape, left the
  ledger unchanged row for row and took recalls 19 → 27: **8 derivations saved**
  for +0.03 % instructions.

So the ceiling on the whole idea is 17 derivations in a 21 411-derivation run,
and the reason is not a missing mechanism: a reduction is certified once
because `eq_cache` answers the repeat before `whnf` is re-entered. Both
refutations are recorded at `trace_cert` so the repair is not re-attempted.

**`eq_cache`: a documented exception, and the clause is satisfiable for it.**
`Admit::Cache` is 260 and stays there. The cache itself is *not* the defect:
`union_find::hop` (`union_find.rs:287`) returns no hop for a cert-less edge, so
`explain` cannot cross a conditional-declined union edge and cannot produce a
path it has no evidence for — it fails closed, which is (b) in the strongest
form available. What is admitted is the *conclusion the caller wanted* on a
path the cache legitimately refused to record, and the refusal is right:
caching conditional certificates was measured and took the tutorial corpus from
49 escapes to 96 and its gaps 265 → 291 (`certify::is_unconditional`). So the
clause is satisfiable here, and it is satisfied by **stage 1**, not by cache
work: fewer certificates conditional at write time is fewer declined edges. A
row that does not fall after stage 1 is the measurable that stage failed.

---

## 2. Staging order

The owner's sketch (binder open/close → whnf → def_eq) is broadly right, but
stage 0 came before the binder work, and the binder work hides the one real
design decision. Each stage carries the measurable that must move — and the
standing rule that **a stage after which `has_type` searches / escapes do not
fall has left a specific edge unthreaded**, which the per-clause
`HtClause`/`HtMiss`/`Dt`/`Pop` counters will localise. Stages 1–3 are
exactly the work of closing §3's bucket (i); §3's bucket (ii) is what they
must *not* be measured against.

**Stage 0 (mechanical): stop discarding what already has a consumer. —
LANDED 2026-08-01 (`ac04498`, follow-on `53f3c0f`).**
(a) `is_proposition`/`is_proof` gained witness-bearing counterparts (§1.6);
(b) `proof_irrel_eq` passes them plus its type-equality cert to
`Certifier::proof_irrel`; (c) `def_eq_proj` composes `Certifier::proj_cong`
from its structures' cert; (d) `try_eta_expansion_aux` hands its recursive
cert to `Certifier::eta` so only the genuine `λz. y z ≡ y` step remains
admitted.

*What happened, on `init-prelude` (as measured then; the run at `8d2b9c9`
confirms the end state).* `Admit::Proj` 17 → 0 (16 derived, 1 premise hole —
still exactly 1 today). `Admit::ProofIrrel` 7 → 0 (3 premise holes today).
`Dropped::DefEqSide` 7 632 → 272 (still 272 today), and the ledger grew two
variants — `Probe` and `Predicate` — because the label was naming two things
it did not describe.

**Three things the proposal got wrong, and they matter for the later stages.**

1. **`point_of_proof` has three askers, not one.** The `Pop` ledger splits
   them. Proof irrelevance is at **0** searched and pinned there by a test.
   The other two were never stage 0's: `point_the_subject` inside
   `has_type_lam_prop` is the search asking itself (41 on ip), and the
   `beta`/`zeta`/`delta`/`iota` proof shortcuts are rules deriving their own
   claims (34 on ip). Those are stage-1/2 measurables.
2. **Threading does not dominate the search, and the ledger says exactly
   where.** Where proof-irrelevance still gaps, `⟦e⟧ ∈ ⟦α⟧` arrives every
   time and `⟦α⟧ ∈ U₀` is a hole every time — because `infer(α)`'s own
   certificate is a hole, which is mostly §3's `ty_const` store-miss residue
   (2 674 of 2 891 declaration typings have no certificate at all) but not
   wholly: 198 were derived and thrown away, and that part *is* threading
   debt. The `Dt` ledger splits the two (`Dt::Gap` against
   `Dt::Conditional`); see `MEASUREMENTS.md`, "The declaration-typing
   ledger, read as a completeness measure", and §3 item 3 for why the 198 are
   nevertheless blocked.
3. **`TgBackend::admit` was guessing, and that is deleted.** It tried
   `proof_eq` before reporting a gap and rescued any step whose two sides
   happened to interpret to `•` — 20 steps a run, every one `Admit::ProjRed`,
   recorded as derived. Removing it made them visible; the follow-on
   (`53f3c0f`) answered them properly, with `Certifier::proj_red` fed by
   `proof_witness` at `PropAt::Sigma`. **A fallback is, by construction, the
   label of the site that noticed** — a count that rises when a rescue is
   deleted is the correction, not a regression.

**Stage 1: binder open/close.**
Move context from per-consumer acquisition to per-binder open/close. Two
sub-decisions, and this is where D lives:
* *Representation.* Kernel hypotheses (`assume`/`implies_intr`) give constant
  cost per step but are **exactly what the memos must refuse**
  (`certify::is_unconditional` at the union-find write, `tc.rs:1996`;
  `hypothesis_free` at `certify_reduct`'s store, `tc.rs:1372`; the three
  cert-level stores are enumerated in `is_unconditional`'s doc,
  `certify.rs:802–808`, and every cross-declaration `Thm` is `Sealed` by
  type): a `Γ ⊢ a = b` under an `ExprPtr` key silently imports `Γ`.
  Formula-level antecedents (the current `CondEq` discipline) are cacheable
  and escape-accounted but cost O(|assumptions|) per rule application and
  force the whole `u_*`/`reassume`/`merge_hyps` apparatus. The likely
  resolution — kernel hyps *while under binders*, `implies_intr`+`gen` back
  to closed form at every memo write and at close — needs an explicit
  decision, because it changes what the caches can hold and the escape
  ledger's meaning. The boundary side is done: R6′ (`a52e553`) allowlists
  `checker/src/scope.rs` as the introduction module, so no rule has to be
  relaxed to land this. (`tg.rs`'s `has_type_local` doc and
  `kernel/src/thm.rs`'s sorted-merge `mp` both cite this stage as their
  consumer; the antecedent-vs-hypothesis trade is named there too.)
* *Plumbing.* A context stack beside `dbj_level_counter` in `TcCtx`
  (open pushes `(local, ⟦w⟧ ∈ ⟦A⟧ evidence)`, close pops and discharges),
  readable by the backend, replacing `local_premises`' term-scan guess.
  `crate::scope::Scopes` is that stack, with `open`/`close`/
  `Closed::discharge` written and tested; wiring it into `TcCtx` is what
  stage 1 does. One decision was answered since the first edition
  (`b478d45`, 2026-08-04): the I2 set-half assertion sits on
  `test_support::close_single_stack`, not on `Scopes::close`, "because the
  precondition is a property of the derivation and not of the program" —
  and `scope.rs`'s header names the condition under which stage 1 may
  promote it onto `close` (exactly one `Scopes` per `TcCtx`, with `derived/`
  still barred from `Thm::assume`).
*Measurables (fresh baselines):* escapes (2 247 after the 2026-08-10 handoff)
must fall — every escape today is an assumption no binder discharged, and
after this stage an assumption about a checker-opened local *has* a
discharging binder by construction; the `has_type` miss row "a local" — which
this survey assigned to stage 1 at 11 211 — **fell to 1 132 without stage 1**,
through §1.3's application-check handoff (the antecedents arrive with the
argument's typing instead of being acquired by the search), leaving stage 1
the 1 132 residue and the *cost* argument (per-consumer acquisition versus
per-binder open/close), not the count; `Admit::Cache` 260 (paths through
conditional union-find edges) should shrink as fewer certs are conditional at
cache-write time. If escapes do not fall, the leak is a consumer path that
still enters the search with no assumptions — three `has_type_a(…, &[], …)`
sites exist (`domain_obligation`, and two in `derive_point_of_proof`),
grep-auditable.

**Stage 2: ~~`whnf` takes and returns evidence~~ — WITHDRAWN. The residue is
not threading-shaped, at any level of generality.**

*Rewritten in place 2026-08-10 after the population was measured four ways.
The previous text specified `whnf(e, ⊢⟦e⟧∈⟦T⟧) → (e', ⊢⟦e⟧=⟦e'⟧)` and called
this stage "the 18 656's only route". Both claims are false, and the second is
false for a reason no amount of plumbing changes.*

**The signature cannot pay the debt it was specified to pay, and the reason is
structural.** The stage existed to feed the beta rule's domain obligation
`⟦a⟧ ∈ ⟦A⟧` for the redex `(λx:A.b) a`. A typing carried alongside the cursor
gives `⟦(λx:A.b) a⟧ ∈ ⟦T⟧`, and **membership of a set-application is not a
statement about the argument**: nothing about `app(f, a) ∈ T` constrains `a`.
The transported typing is correct, costs a Leibniz per step, and is consumed by
nothing that owes a domain obligation. Do not implement it as specified. (The
`ensure_pi` slice of 2026-08-09 and the `arg_mems` handoff of 2026-08-10 are
unaffected — they are inference handing over what inference derived, which is a
different mechanism and did pay.)

**The residue is not a transport problem. Measured at four keys, on
`init-prelude`, of the 18 656 raw hoists no application check ever visited:**

| the question asked | the key | reached |
| --- | --- | ---: |
| was this very membership concluded anywhere? | `(subject, target)` | **34** |
| was the subject typed at *some other* target? | `subject` | **460** |
| was the **generalised** membership concluded — free variables abstracted away? | `∀w⃗. subject ∈ target` | **134** |
| does the beta rule's *target*-side twin find it? | `arg_mems` at `target_mem` | **145, closing 0** |

The third row is the one that settles it. An open subject — one carrying the
current declaration's locals — is a substitution instance of a subterm of
another declaration's value entering by delta, so its *ground* pair is absent
**by construction**: it is about variables that did not exist when that
declaration was checked. That is why the first row's 34 proves nothing on its
own, and why a delta-borne transport of generalised typings (instantiated by
the reduction's own substitution, each binder's `⟦u⟧ ∈ D` supplied by the
enclosing beta step) looked like the answer. It is not: **of 10 450 open
subjects, 133 have a generalised membership an earlier declaration concluded, 1
was concluded here, and 10 316 were never concluded at any generality at all.**
The facts are not somewhere else in a form that needs carrying. They were never
derived, anywhere, by anyone. (`Shared::typed_skel`; canonical via
`Formula::forall`, which needs no minted variables, so the key compares across
declarations. Calibrated on the closed subjects, where the skeleton *is* the
pair and the two keys must agree — they do.)

**Where the derivations would have to come from instead.** With every decline
point in `has_type_lam` attributed, **32 831 of 35 321 declines are "the rule
applied; the body has no typing"**, and the nine structural ways the lambda
rule can fail fire **zero** times on the whole prelude. The declines are a
nested-λ cascade — 21 263 untypeable bodies are themselves lambdas — whose real
leaves are **applications** (10 209: 4 218 headed by a defined constant, 3 782
by a lambda, 2 209 by an opaque constant) and **Πs** (690, wanting
`dprod_in_universe`). A second front, same shape: **8 496** of those body
obligations are stated at a target that beta-reduces, while
`HtClause::TargetBeta` discharges **125** in the whole run — `target_head_step`
reaches 12 874 redexes and loses 6 004 to its own domain premise and 8 624 to
the reduct still not being typeable.

So what this stage was for is **derivational power in the application rule and
in `ty_const`**, not plumbing. That is bucket (ii) work by §3's own
classification, which means §3's split needs re-reading: the 18 656 were
assigned to bucket (i) on the assumption that the facts existed and were being
dropped, and they do not exist.

**The one population that is not a ceiling, and what it would cost.** Of the
18 622, **7 717 are about closed terms** — no free variables, so nothing needs
transporting and nothing needs generalising; such a term's typing can simply be
*concluded*. They are **407 distinct terms** (223 lambdas, 88 applications of a
defined constant, 44 Πs, 17 let/projection/literal, 14 applications of an
opaque constant, 12 constants, 9 applications of a lambda), so typing them on
demand is 407 inferences, not 7 717. Two things stand between that and a
tranche, and they are engineering, not arithmetic:

* **Not at the obligation site.** `domain_obligation` runs inside `TgBackend`,
  which is a *field* of the `TypeChecker` (`tc.certifier.beta(tc.ctx, …)`), so
  there is no path from the backend back to `infer`. On-demand inference there
  needs the ownership restructured, which is a bigger change than the payoff.
* **At the construction site — BUILT, 2026-08-10, and it pays.**
  `TypeChecker::beta_arg_typing`. These terms are built by the reduction
  itself, inside `whnf`, where `self` *is* a `TypeChecker` and `infer` is in
  hand, so the right reading of "the typing arrives with the whnf call" is not
  a cursor-carried typing but **inference invoked at the beta contraction on
  the argument, handed over through the existing `Certifier::app_arg_checked`
  store** the beta rule already reads. Re-entrancy — `infer` calls `ensure_pi`
  calls `whnf`, on 81 % of all reduction steps — is bounded at depth one by
  `TypeChecker::whnf_typing_depth`, so termination is immediate rather than an
  argument about shrinking terms that no measure orders.

  Three restrictions, each measured (`MEASUREMENTS.md`, "Typing the
  reduction's own arguments"): **closed arguments only** — unrestricted,
  inference drives more `whnf` and the run inflates, +16.8 % instructions with
  escapes 2 247 → 3 033, against +0.47 % and escapes unmoved when restricted;
  **`Check` not `InferOnly`** — +977 discharged against +32; **the outermost
  argument only**, whose domain is the lambda's own and needs no instantiation.
  Safety: the backend is asked first (`Certifier::wants_arg_typing`, default
  `false`, so the null backend pays nothing), and the conversion uses `def_eq`
  rather than `assert_def_eq`, because a redex the reduction built need not be
  well-typed and a hard failure would turn an accepted file into a rejected
  one.

  **Result:** 3 313 closed arguments asked, 3 313 typed, no declines.
  Obligations discharged 5 373 → 6 350; handoff outright answers 102 → 3 266;
  raw hoists 20 328 → 19 460; and this row's own subject, "never checked at an
  application", **18 656 → 16 502**. Of that 2 154, 868 are now answered and
  1 286 are re-attributed into "a hole at their own check" — out of "nobody
  looked" and into the `ty_const` cascade, a gain in knowledge rather than in
  proving. Escapes unmoved at 2 247; three gap ratchets moved with the trade
  written at each assertion (+229 gaps, all six rows downstream of `nat_reduce`
  and `proj_reduce`, both already admitting and both bucket (ii)).

  **What is left of the 7 717 after it**, and where a successor goes: the
  inner binders of a nested redex (their domains are the instantiated ones,
  needing the intermediate lambdas the composite `inst` avoids building), and
  the open arguments, whose cost is the measured 16.8 % unless something
  cheaper than full inference can type them.

*Measurables, restated:* the `raw hoists by cause` row and its two new
cross-cuts (`lambda typing declines, by cause`; the subject/skeleton reach
rows) are what any successor tranche must move. The fifth route moved the first
of them by 2 154. Escapes stand unmoved at 2 247 throughout — and that is now a
*result* rather than an absence, since the tranche that closed 868 obligations
closed them without adding an assumption anything failed to discharge.

**Stage 3: `def_eq` takes typings.**
`def_eq(a, b, ta, tb)` and thread to: `proof_irrel_eq` (already fed by stage
0 at the leaves, now without re-inferring), `def_eq_unit`, `try_eta_struct`,
`to_ctor_when_k`, and the whnf calls inside (stage 2's input). Under binders,
`def_eq_binder_aux` extends the typings as it opens — stage 1's machinery.
This is mostly mechanical after stages 1–2; the reason it goes last is that
its payoff — retiring the nine `infer_ty`/`infer_then_whnf` discards under
`Dropped::DefEqSide`, at `tc.rs:503` (two on one line), `549`, `557`, `2019`,
`2025`, `2049`, `2053`, `2550`, plus the one `assert_def_eq_only` at
`tc.rs:1071` — is re-*inference*, which is memoised and cheap, so it moves
correctness-shape (`Dropped::DefEqSide` 272 → ~0) more than it moves search
counts. `def_eq` has ~20 call sites in `tc.rs` to grow the two parameters
through.
*Measurables:* `Dropped::DefEqSide` → ~0; the remaining `Admit` rows are then
exactly the interpretation-scope list of §3, i.e. the admit report becomes a
pure milestone ledger with no threading debt in it.

**Relation to task #103 (acceptance-only `whnf`/`is_def_eq`).** That task
enumerates 27 acceptance-only reduction sites and leaves "the allowlist
judgement" outstanding. Its site list was not readable from this tree and is
not reproduced here (unchecked); what this census supplies is the judgement's
criterion and its checker-side population. The recurring defect the project
keeps finding — a value computed at the bottom of a call whose site outlives
nothing, a reduction performed for acceptance whose certificate was thrown
away — is exactly the boundary this census walks: a site belongs on the
allowlist iff **no definitional-equality or typing conclusion rests on the
value after the enclosing decision returns** (shape probes, fail-fast
rejections); it is threading debt iff the value licenses something downstream
(every row above whose "instead" column is non-empty). The checker-side
population to run that judgement over is: `whnf`'s 28 callers (§1.3), the 17
`assert_def_eq_only` sites, the 20 `infer_ty`-family discard sites in
`tc.rs`, and the `def_eq`-under-`.is_some()` sites inside §1.4's admit rows.
The trace design already makes the allowlist cheap to be wrong about:
recording is unconditional and three words per step, so an acceptance-only
site that later turns out to have a consumer costs a composition, not a
re-reduction.

**Explicitly not in the order:** improving `has_type` (owner's decision: it is
provisional scaffolding; stages 1–2 starve its two entry pressures —
`domain_obligation` and `point_of_proof` — after which what remains of it
serves only obligations about uninterpreted inductives, and it can be deleted
with them); `Dropped::BinderSort` (66 594 on ip — the count doubled with the
level-instantiation schedule, not with new sites) — most of these certify
"domain is a type", whose only foreseeable consumer is `point_of_proof`-style
reasoning already served by stage 0's witnesses at far fewer sites.

---

## 3. The gap classification — threading-shaped against blocked

The owner's step 2 is *"finish threading evidence through the checker code
base, including all the caches, until no gaps are left"*. For that sentence to
be checkable, the ledger has to be split: **bucket (i)** is what threading
evidence closes — stages 1–3 — and **bucket (ii)** is what no amount of
threading reaches, each item named with what does unblock it. "No gaps left"
means: bucket (i) at zero, and every surviving row traceable to a bucket-(ii)
item. All counts **(ip)**, fresh run at `8d2b9c9`.

**Bucket (i) — threading-shaped.**

| debt | count (ip) | closed by |
| --- | ---: | --- |
| beta obligations searched / hoisted instead of arriving with the call | 39 951 asked; **10 300 now answered from the application check's handoff** (2026-08-10, §1.3). The 20 328 raw hoists are cause-split: 32 threading-shaped (another domain term), 1 640 bucket-(ii) (`ty_const` cascade at the argument's own check), 18 656 about reduction-built / delta-imported terms | handoff **landed**. The 18 656 were assigned to bucket (i) on the assumption that the facts existed and were being dropped. **They do not exist** — reached at four keys: 34 / 460 / 134 / 145-closing-0 (§2). They are bucket (ii): derivational power in the application rule and `ty_const`. The 1 640 remain the shared constant store's |
| escaped assumptions (undischarged at a boundary) | 2 247 (2 257 → 2 247 with the handoff: ten obligations about applications of locals now carry per-local antecedents their binders discharge, where the raw membership had none) | stage 1 |
| `has_type` misses that are "a local" — context guessed, not read | **1 132** (was 11 211) — closed not by stage 1's context stack but by the handoff: an argument whose typing rests on ambient locals now arrives from `infer_app` with those antecedents already attached, so the search never runs to acquire them. The residue is the genuinely-ambient population §3 item 1 describes | handoff (landed); residue stage 1 |
| `point_of_proof` premises still searched (`Pop`: 41 lam + 34 rule) | 75 | stages 1–2 |
| `Admit::Cache` — conditional union-find edges declined at write | 260 | stage 1 |
| `ensure_pi`/`ensure_sort`/`infer_then_whnf` legs silently dropped; `ty_bridge`'s delta-only rescue | **`ensure_pi` leg closed 2026-08-09** (`ty_app` 481 → 418, `ty_conv` carried 31 → 142, 7 more declaration typings stored; escapes 2 138 → 2 257, the borrow-policy over-report — see §1.2); `ensure_sort`/`infer_then_whnf` remain, consumers pending | stage 2 (remainder) |
| `Dropped::DefEqSide` — re-inference inside def-eq rules | 272 | stage 3 |
| `Admit::Local` (refl suffices), `Admit::BoolTrue` (legs all in hand) | **closed 2026-08-09** — both are composed/ruled, fixture-pinned (§1.4); neither is raised by the checker any more | done |
| 198 declaration typings derived under antecedents and not stored | 198 (1 161 use misses) | **counted here, blocked in (ii)** — see below |

**Bucket (ii) — blocked on something other than threading.** These are items
1–6 below. Headline rows: `ty_const` no-evidence 20 929 (of which the 2 674
never-derived declaration typings — (declaration, σ) pairs — are the cascade
root), opaque-head
obligations ~5 500, `iota` residue 792 + 486, `proj_reduce` 630, `ty_pi`
8 798, literals (`ty_lit` 890, `NatEq` 44, `NatRed` 8), `eta_struct` 6.

**The one bucket-(i)-looking class that is (ii), verified.** The 198
conditional declaration typings are threading debt by definition — computed
and thrown away — but storing them is not what is blocked on threading.
`checker/src/tg.rs` (doc of `store_declar_typing`, re-read at `8d2b9c9`, its
ledger rows re-confirmed by the fresh run) records: all 198 have an **empty
kernel sequent**, so `Sealed::new` would accept every one — the persistence
discipline is not the obstacle. Their 200 antecedents are hoisted guarded
families (196 carry one, 2 carry two); the `discharge_families` ledger reads
**1 186 offered / 0 discharged** corpus-wide; 170 of the antecedents are
families-of-families, and the recorded probe that unwrapped them to their
innermost membership and asked `has_type` under every guard collected on the
way derived **0 of 170** at every depth from 2 to 7 — because they, like all
30 plain-membership antecedents, are about **structure projections `⟦s.i⟧`**,
whose interpretation does not exist. Its own words: *"no amount of threading
reaches them."* This survey looked for an overstatement and did not find one:
the neighbouring `discharge_families` census (677 memberships split 221 /
186 / 32 / 238) does contain one sub-population that is *not* interpretation
scope — 144 premises about a bare context local stated at a domain no
unfolding or head-step reaches — but the same doc verifies that **none of the
144 is an antecedent of the 198**, so closing that bridge moves the family
ledger and leaves `Dt::Conditional` and the store hit-rate exactly where they
are. (The 0-of-170 unwrapping probe itself is a recorded measurement, not a
live report row — carried over, not re-run.) What unblocks the 198 is
interpretation of structure projections — task #125's shared environment,
giving the checker access to mini's interpretations — after which storing
them is the mechanical part.

1. **Ambient context locals: mostly *not* residue.** Checked again: every
   `Local` carries its `binder_type`; every local the checker itself opens
   (`mk_dbj_level` in `infer_lambda`, `infer_pi`, `def_eq_binder_aux`)
   has a closing binder where `implies_intr`+`gen` (or the formula-level
   equivalent) can discharge. The 11 211 "a local" `has_type` misses arise
   because the search is entered with `assms = []` (`domain_obligation`,
   `derive_point_of_proof`) even when the checker is under open binders —
   unthreaded, bucket (i), not residue. The **genuine** residue is the
   `mk_unique` locals of `inductive.rs`/`quot.rs` telescopes: opened with a
   known type but never closed into a λ, so their typings stay ambient — and
   Carneiro's context-relative reading says that is the correct final state
   for them: the facts are hypotheses of the surrounding (meta-level) check,
   not theorems. Today they have no consumers anyway.
2. **`TyGap::PiUndet` — real, and bounded.** `imax u v` at a level parameter
   is neither §6.2 clause; no per-declaration interpretation can choose (the
   argument is at the variant, `certify.rs`, `TyGap::PiUndet` doc). The
   level-instantiation pre-pass already collapses this at ground σ — the
   no-evidence row is down to **12** on ip — and what remains is the
   recursor's eliminator universe and declarations checked at their own
   parameters. Residue of the *per-instantiation* strategy, not of
   threading; closed by scheduling, not evidence.
3. **Uninterpreted inductives/constructors/recursors and structures.** The
   opaque-head obligations (~5 500 on ip), the `ty_const` store misses'
   cascade root (2 674 of the 2 891 **(declaration, σ) pairs with a value**
   whose own check gapped — pairs, not declarations: `init-prelude` has 2 059
   declarations, and the pre-pass schedules its 1 645 value-carrying ones at
   2 891 ground instantiations; see `MEASUREMENTS.md`, "How far along the goal
   is: the four denominators"), the `iota`
   residue (792 recursors with no curried interpretation + 486 stuck
   majors), `proj_reduce` 630, `Admit::EtaStruct`/`UnitLike`, `Quot`. No
   axioms exist about these symbols *in this backend's signature*, so no
   threading can manufacture the facts. Since 2026-08-01 this item is no
   longer static: the general inductive path interprets 283 declarations and
   derives real ι steps (92 sites) where the interpretation exists — the
   point stands that the *residue* is interpretation scope, and the correct
   current behaviour (decline + count) is what the code does. The 198
   conditional declaration typings above are this item's threading-facing
   face, and task #125 (shared environment; the checker reading mini's
   interpretations) is the named unblock.
4. **True axioms.** `propext`, `Classical.choice`, `Quot.sound` must remain
   assumptions of the model forever — measured (2026-07-30 instrument, not
   re-run in this survey) to head **zero** typing obligations on
   init-prelude, so they cost nothing today.
5. **Literals and level algebra.** `TyGap::Lit` 890, `Admit::NatRed` 8,
   `NatEq` 44, `StringLit` 0: milestone-4 primitives. The level-algebra
   admits (`sort`/`const` equality modulo level algebra) are at zero on ip —
   the translator-side level normalisation and the pre-pass carry them.
6. **Eta** needs a function-extensionality lemma (`TgBackend::eta` admits;
   0 uses on ip) — library work; the threading half (composing the recursive
   cert) landed in stage 0.

No part of the target design looked *unworkable* in this survey either. The
place the design is under real tension is still stage 1's cache-vs-hypotheses
decision (§2): kernel-hypothesis evidence and `ExprPtr`-keyed global caching
are mutually hostile, the guards that keep them apart exist and fail closed
(`is_unconditional`, `hypothesis_free`, `Sealed`), and the resolution
(discharge at every memo boundary) is coherent but has a cost that should be
measured before being committed to — the project's own history (four refuted
readings recorded in `tg.rs`'s module doc, re-verified) argues for measuring
first.

---

## 4. Scale

* **Functions.** `tc.rs`: ~91 `fn`s, of which ~55 participate in checking with
  an evidence-relevant role (the census above names every one with a non-empty
  "should" column; the rest are constructors/plumbing). `inductive.rs`: ~45
  fns, all currently and correctly drop-only. `quot.rs`: 2. `tg.rs` backend:
  ~16 consumer rules in place (the §1.9 first list), ~25 search/shadow
  functions slated to shrink or die as stages land.
* **Call sites touched by the remaining stages.** Stage 1: 2 functions in
  `util.rs`, the ~6 open/close loops in `tc.rs`, the 3
  `has_type_a(…, &[], …)` entries in `tg.rs`, plus the cache-guard audit
  (3 cert-level stores, enumerated at `certify.rs:802–808`). Stage 2:
  `whnf`'s 28 callers (18 `tc.rs` — mostly mechanical re-wraps; 10
  `inductive.rs` — can take a don't-care adapter), `Certifier::beta`'s
  signature, `whnf_reduce`'s loop. Stage 3: `def_eq`'s ~20 call sites in
  `tc.rs`, the 10 `DefEqSide` discard sites.
* **Diff against upstream (`vendor/nanoda_lib-upstream`, re-diffed
  2026-08-09).** Today: `tc.rs` 1 698 changed lines (1 324 → 2 573),
  `util.rs` 145 (1 000 → 1 128), `inductive.rs` 25, `quot.rs` 13,
  `expr.rs` 0, `env.rs` 17 (three read accessors made public for the
  inductive work — `num_params`, `all_ind_names`, `is_nested`); new files
  `certify.rs` 1 330, `reduct.rs` 166, `union_find.rs` 305,
  `instantiations.rs` 511, `stepcount.rs` 130, `scope.rs` 420,
  `sealed.rs` 135, `tg.rs` 17 431 (+ `kernel/`, `derived/` crates). The
  remaining threading concentrates where the diff already is: expect `tc.rs`
  to grow by a few hundred lines (signatures + composition at 28 + ~20 call
  sites), `util.rs` by the context stack, `inductive.rs` to stay
  near-pristine until inductives need telescope facts, and `tg.rs` to
  *shrink* as the search family and its shadow inference lose their callers —
  which is the point.

---

## 5. Stale documentation passed en route

Statuses re-checked 2026-08-09.

1. **Fixed, and fully**: `tg.rs`'s `has_type_local`/`ty_local` docs no longer
   claim "this kernel has no context — a `Thm` is a closed formula"; the
   phrase is gone from the file (grep), and `has_type_local`'s doc now states
   the opposite with the antecedent-vs-hypothesis trade and a pointer to §2
   stage 1.
2. **Fixed** (same rewrite): the second occurrence at `ty_local`, likewise
   gone.
3. **Fixed**: `Dropped::DefEqSide`'s variant doc (`certify.rs`, at the enum)
   was rewritten by stage 0 and now records the lesson: the old justification
   — "the conclusion drawn is itself an admit and the side condition's
   evidence has nothing to compose with" — was **false** for two of its
   sites (`def_eq_proj`, eta), and "nothing to compose with" is a claim
   about the rules that exist today, which goes stale the moment a rule is
   added. What remains under the label is the residue where the claim holds
   (`def_eq_local`, `unit_like`, `eta_struct`, `to_ctor_when_k`).
4. **NOT fixed** (`certify.rs:435–437`, text verbatim, re-read).
   `ty_const`'s doc says the stored typing is "not a walk down the delta
   graph" — true of `ty_const`, but `has_type_const` still walks the delta
   graph as its fallback (by design, per the `028_peano2` measurement); a
   reader of `certify.rs` alone would conclude the walk is gone entirely.
5. **NOT fixed** (`certify.rs:551`, re-read): "a 1300-line type checker" —
   `tc.rs` is 2 573 lines, out by a factor of two. Trivial, but it dates the
   paragraph.
6. **Half fixed**: `infer_proj` (`tc.rs:662`) now passes `Dropped::Probe` —
   corrected. `check_declar_info` (`tc.rs:389`) still passes `BinderSort`
   for a declaration type; that misnomer is *documented* at the variant
   rather than corrected, and will misattribute ledger counts as the
   `BinderSort` row shrinks.
7. The "28 callers" claim at `tc.rs:1156–1157`: re-verified 2026-08-09,
   still 18 + 10. Stage 2 has not landed, so it has not rotted.
8. **New**: `checker/src/main.rs`'s allocator comment quotes "init-prelude's
   16341 gaps / 2261 escapes" as the byte-identical corpus verdict — those
   are pre-stage-0 numbers; the run today is 15 423 / 2 138.
9. **New**: `Admit::Cache`'s variant doc says the unconditional-only rule
   left "687 → 272" on init-prelude; the row is 260 today. Drift, not error.
