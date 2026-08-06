# DERIVED-AUDIT — does each construction in `derived/` prove what its `# Interface` header says?

Audit date: 2026-07-31/08-01, against the working tree mid-session (five coding agents active).
Method: read-only. The kernel (`kernel/src/thm.rs`, in full) was read first to fix what a `Thm`
establishes; every `derived/` module was then audited by comparing its `# Interface` (or doc-comment)
claims against the exact expression that assembles the returned conclusion, with adversarial input
construction at every caller-supplied-theorem guard. Nothing was built and no tests were run.
The audit was executed as eight parallel passes over disjoint slices, each reading its slice in full
(the two large legacy slices — universe/recursion/funcs and the W-family — at interface level with
line-by-line reads of the guard and assembly sites; internals that only feed exact-formula-checked
joins were skimmed, as listed in "Where this audit stopped").

## Bottom line

No construction in the audited portion of `derived/` returns a theorem whose conclusion differs
from its header **when called with the inputs the crate itself produces**. The four claim-matching
bugs' shapes (wrong certificate for a true fact, wrong index, missing certificate, out-of-scope
obligation) were hunted specifically; nothing of the first, third or fourth shape was found, and the
index arithmetic that was singled out (`comp_i = π₁(π₂ⁱ q)`, `Inj_i` depth, `Sum_n` arity,
per-level towers) is correct everywhere it was traced. What was found instead: **one cache that
reports success for a derivation it never performed (F1), one checker-facing guard that reads
`concl()` without reading `hyps()` (F2), one API that lets a theorem be attributed to the wrong
machine's constructors (F3)**, a bounded class of release-only pins (F4), and a set of Interface
blocks that mis-state the theorem their own code correctly builds (F5, F6). Everything else audited
is listed as sound at the end, so it need not be re-verified.

Two crate-wide facts, verified directly, frame all of this:

1. **No shipped `derived/` theorem can carry kernel hypotheses.** `ci/check-boundary.sh` (rule 6)
   rejects `Thm::assume`/`Thm::implies_intr` outside `kernel/`; I grepped the tree and the only
   hits are in `checker/src/tg.rs` under `#[cfg(all(test, feature = "tg"))]` (gate at tg.rs:13247).

   *(**Rule 6 was deleted the day after this was written** — `kernel/src/thm.rs`
   carries the retraction, `ci/check-boundary.sh` carries R6′ — and `Thm::assume`
   is called in shipped code today at `checker/src/scope.rs` and
   `mini/src/scope.rs`. **The conclusion survives for `derived/`**, which is what
   this audit is about: R6′'s I1 keeps the scan over shipped `derived/` code a
   ban, because `derived/` derives and does not assume. What does **not** survive
   is the generalisation, and it is load-bearing for the severity notes below —
   every "test-code-gated" qualifier in this file, F2's included, assumed that
   only test code could mint a hypothetical theorem. `mini/` is exempt by design,
   depends on `derived`, and calls into it, so a caller-supplied `&Thm` reaching
   a `derived/` entry point **can** carry hypotheses. `DERIVED-AUDIT-2.md`'s
   §"Bottom line" item 2 is where that was found and acted on; read it before
   relying on a severity assessment here.)*
   So "hidden hypotheses" in `derived/` can only be antecedents *inside* the conclusion
   (`H → φ`), which is exactly what headers were compared against. Every "unconditional ⊢"
   claim in the sound list below was checked to have no such antecedent.
2. **The Hilbert-style composition fails closed.** `Thm::mp`/`syl`/`hyp_mp` compare formulas
   syntactically (locally nameless ⇒ α-equality is `==`), so a wrong input almost always yields
   `None`. The residual exposure is concentrated in exactly two places: the *final* conclusion
   shape, and the *labels* (struct-field docs, headers, success return values) attached to it.
   Every finding below is of that shape.

---

## Findings, ranked

### F1 (high) — `ISumSyms::ensure` reports success for an arity it never derived; the cache is
### poisoned by a failed mint and pins nothing about which `Sums` family it was built over
`derived/src/isum/symbols.rs:152-227` (placeholder pushes at :159 and :179; `arity()` at :145).

`ensure` pushes cache entries *before* deriving their theorems — an `Injection` placeholder with
`inj: Thm::eq_refl(av)` at :159 and a `Level { inj_mem: Vec::new(), .. }` at :179 — and every later
failure propagates `None` via `?`, leaving the pushed entry behind. Progress is keyed solely on
`injs.len()`/`levels.len()`, so the entry is never repaired.

Concrete failure: build two independent `Sums` in one `Env` (two `Sums::new` calls mint distinct
`upair`/`empty` symbols). `ensure(env, &s1, 2)` succeeds. `ensure(env, &s2, 3)` mints `Inj_2` and
`Sum_3` **over `s2`** (their own axioms suffice), then fails at level 3's `inj_mem` for `i = 0`
(the `Thm::mp` at :201-212 needs `inj_of(s2,0,a) = Inj_0(a)` but `inj_ax(0)` is over `s1`) —
leaving `levels[3]` pushed and empty. A third call, `ensure(env, &s1, 3)`, now returns
`Some(())` — both `while` loops see their targets met — although `inj_mem(3, ·)` is `None`
forever and `Sum_3`'s defining equation is over `s2`'s nest, not the caller's `s1`. `arity()`
overstates accordingly, and `sum_ax(3)` hands a caller a true theorem **about the other family's
symbols** with no error. This is precisely "reports derived what it did not derive". No false
theorem escapes (all per-item accessors fail closed), but a caller trusting `ensure`'s `Some` or
`arity()` will attribute `Sum_3`/`sum_ax(3)` to the wrong family.

Fix shape (for the dispatched fixer, not applied here): derive-then-push, or record the `Sums`
identity (e.g. `s.ap.sets.up`) in the cache and compare on every `ensure`/accessor.

Related, robustness not correctness: `no_junk(env, s, m)` for `m` beyond the ensured arity panics
at the `.expect("cached by ensure")` at symbols.rs:372 instead of returning `None` like every
other accessor. And the `eq_refl` placeholder at :159 is a latent trap: no input reaching
`inj_inj(i)` with the placeholder still in place could be constructed (the injection segment uses
only its own just-minted axiom), so that half stays a **suspicion**, but the pattern invites it.

### F2 (medium) — `NatMem::over` pins every conclusion but never reads `hyps()`; a hypothetical
### input theorem passes and Γ silently rides into the checker-facing statement
`derived/src/cumul/witness.rs:307` (final guard), :412 (`finite_branching` propagation);
contrast `derived/src/cumul/enums.rs:86` and `:157`.

The final guard is `if *nat_in_u1.concl() != Formula::mem(nat.ty, u1.set)` — conclusion only. None
of the other returned fields (`fin`, `tags_in_u1`, `seed_in_u1`, …) is checked for hypothesis-
freeness either, and `Nat`'s theorem fields are `pub`. Concrete failure (test code or any future
boundary exemption): replace `nat.fibre_zero` with
`Thm::assume(fibre(fam, inl •) = ∅)` — same conclusion, one hypothesis. `finite_branching`
consumes it through `a1i`/`hyp_mp` (mp-based; kernel unions Γ), so the returned
`NatMem.nat_in_u1` is `{fibre(fam, inl •) = ∅} ⊢ N ∈ U₁` while the struct doc (witness.rs:119-120)
claims `⊢ N ∈ U₁` outright. This is verbatim the "comparing case" the kernel header warns about
(`kernel/src/thm.rs:143-162`). Severity moderated: today only test code can mint the exploit
(crate-wide fact 1), and the one consumer builds its `Nat` honestly — but `NatMem::over` is the
checker-facing constructor, and `enum_in_u1`/`zero_in_u1` in the same module, written the same
session, check both input and output `hyps().is_empty()`. The asymmetry is the defect.

**Systemic corollary** (flagged independently by three audit passes): *no* guard anywhere in
`derived/` reads `hyps()` of an input theorem — `sums/in_universe.rs`, all of `ext/`, `isum/`,
`bound/`, `wrec_total` included. All of them are safe today for the same single reason (the CI
boundary rule). One `hyps().is_empty()` per public entry taking `&Thm` would make the crate
self-defending; recorded as a hardening item, with F2 the one instance promoted to a finding
because its module already contains the correct pattern and its output feeds the checker.

### F3 (medium) — `Inductive::distinct` and `Inductive::ctor_term` accept an arbitrary `&Machine`;
### nothing ties `self` to the machine it was built over
`derived/src/inductive/carrier.rs:334` (`distinct`), `:312` (`ctor_term`).

The `Inductive` struct does not record its machine, and neither method checks that `mach`'s
symbols are the ones `self.ctors[*].term` was built from — while `machine.rs`'s own header warns
that a second apparatus "mints a second `upair`, and then `⟨a,f⟩` names two different terms".
Concrete failure: build `mach1`, `ind1 = Inductive::build(env, &mut mach1, spec)`; build `mach2`
and warm its `isum` caches with any declaration of the same arities; call
`ind1.distinct(env, &mach2, 0, 1)`. Every internal step resolves against `mach2`, so the call
**succeeds** and returns a true theorem `⊢ ∀… ¬(ctor_i′ = ctor_j′)` — stated over `mach2`'s
`Inj`/`upair`/`rec₊` symbols, i.e. about terms that are not `ind1`'s constructors, with no error.
`ctor_term` likewise returns a term no theorem of `ind1` is about. (On a *cold* `mach2` parts may
fail closed via `isum`'s fallible accessors; the warm-cache scenario stands regardless.) Same
failure shape as the historical `Chain::new` symbol-mismatch. Fix shape: store the machine
identity (e.g. its `upair` symbol) in `Inductive` and compare, or take the machine by the same
borrow that built it.

### F4 (medium-low, release-only, misuse-gated) — constructions whose *claim-carrying leg* is
### pinned only by `debug_assert`, so a release-build caller with a plausible wrong input gets a
### correctly-proved theorem attributed to the wrong subject
All are unreachable through the crate's own call chains today (in-crate callers thread consistent
inputs); each has a concrete misuse that succeeds in release and returns a mislabeled theorem:

* `derived/src/ext/dprod.rs:237-270` `dprod_subset_funspace`: the `dp` parameter is compared only
  in `debug_assert_eq!` (:258-268); the conclusion's LHS comes solely from `dp_def`. `dprod_symbol`
  is `pub` and mints a fresh symbol per call: call it twice with the same `img`,`b`, then pass
  `dp2` with `dp1_def` — release returns `⊢ ∀A. dprod₁(A) ⊆ fs(A,⋃img(A))` attributed to `dp2`.
  The n-ary twin (`ext/dprod_n.rs:261,265`) makes both checks release-mode `if`s; promote to match.
* `derived/src/ext/dprod_universe.rs:167-196` `dprod_in_universe`: antecedent fully pinned in
  release, but the consequent — the actual claim `dprod(A) ∈ U(…)` — only at :190-194 in debug.
  Same two-symbol scenario shape. Its own sibling (`dprod_universe_n.rs:180,285`) checks the final
  shape release-mode with a comment saying why ("this is the statement the caller relies on").
* `derived/src/funspace/in_universe.rs:248-286` `funspace_in_universe`: the `fs: &Funspace`
  parameter is used **only** in a `debug_assert_eq!`. Passing `general = product_in_universe_of(…)`
  (same antecedent shape, different consequent) succeeds in release and returns
  `⊢ ∀a. prod(a,a) ∈ U(a)` from a function whose header says `fs(a,a)`.
* `derived/src/fibre.rs:248` (`Fibre::fibre[i]`'s LHS `app(B, Inj_i(a))`): pinned locally only by
  `debug_assert_eq!`; currently sound because `isum::Dispatch::new` release-checks the branch
  typings and the beta chain (verified — see sound list), but the local guard is debug-only, so
  fibre.rs's header holds by grace of another module's discipline.
* `derived/src/enums.rs:293-299` (`enum2`, also `enum1`) and `derived/src/pairs.rs:256`
  (`opair_inj`): agreement between the returned struct's *term fields* and its theorems is
  debug-only; a `mem` theorem about an `X ≠ enum(A)` with the right antecedent passes in release
  and the struct's `ty`/`fst_t` labels lie.
* `derived/src/universe/predicate.rs:143-152` `tarski_at`: the `is_universe`-matches-`ax_tarski`
  check is debug-only, but any drift is caught downstream by `Thm::mp` shape comparison before
  anything exports — hardening only.

The general pattern: today's files pin final shapes and inputs with release `if … return None`;
pre-today files used `debug_assert`. F4 is the enumeration of where the older idiom guards a
*label* rather than a join. Everywhere else the debug asserts are redundant with a kernel-checked
composition and were verified as such.

### F5 (low, fail-closed) — Interface blocks that mis-state the theorem the code correctly builds
Each is a real "header vs conclusion" mismatch in the documentation sense: a caller who rebuilds
the advertised formula and compares `concl()` gets a rejection (costing a session, not a false
claim). The code and, where noted, the per-function docs are right; the headers are wrong.

* `derived/src/isum/dispatch.rs:28-32`: module Interface still states the pre-rework meta-level
  **nest** forms (`disp ∈ fs(A₀ + (… + 0), T)`, `app(disp, inj_i(a)) = …`); the exported theorems
  are over the *symbols* (`fs(Sum_n(A⃗), T)`, `Inj_i(a)`) — provably equal, syntactically
  different terms. Struct-field docs at :106-109 are correct. (Nit at :110-114: "`nest₀` is
  `∅ ∈ fs(0,T)`" — actual `fs(Sum_0(), T)`.)
* `derived/src/wtype/empty.rs:8`: header advertises `⊢ ∀x. prod(∅,x) = ∅`; the theorem
  (`empty_product`, :162-198) is `⊢ ∀T ∀z. ¬(z ∈ prod(∅,T))` — non-membership, not equality,
  different quantifier count. Deriving the advertised equality would additionally need
  Extensionality. Per-function doc correct; the one in-repo consumer uses the real form.
* `derived/src/wrec_typing/values.rs:8-10`: header claims `∀f ∀d` — an arbitrary domain `d`; the
  theorem (`wrec_composite_typed`) fixes the domain to the fibre: `comp(wrec,f,B(a)) ∈ fs(B(a),T)`,
  quantified `∀a ∀f`. Generality claimed but not delivered — the header's `∀d` cannot be
  instantiated at `W(A,B,u)` or anything non-fibre. Function doc (:142-145) and
  `Recursor::comp_typed`'s field doc state it correctly.
* `derived/src/wrec_extend/assemble.rs:6`: header advertises
  `⊢ hypothesis(…) → (G ∈ Att ∧ app(G,⟨a,f⟩) = v)`; no export has that conjunction —
  `extension` returns five separate theorems and the value equation is internal only. The hub
  header (`wrec_extend.rs:34-38`) lists the five actual statements correctly.
* `derived/src/inductive/carrier.rs:73`, `inductive/ctor.rs:79`, `inductive/distinct.rs:13`:
  injectivity conclusion written as two grouped conjunctions `(⋀ⱼ yⱼ=yⱼ′) ∧ (⋀ⱼ rⱼ=rⱼ′)`; the
  built formula (distinct.rs:178-181) is one flat right-nested chain over all `k+m` equations
  (for `k=2, m=1`: `y₀=y₀′ ∧ (y₁=y₁′ ∧ r₀=r₀′)`, not `(y₀=y₀′ ∧ y₁=y₁′) ∧ r₀=r₀′`).
* `derived/src/bound/subset.rs:8`: module header spells `funspace_pairs` with the `∀p` outside the
  implication and the `∃∃` fully nested; the actual theorem has `∀p` inside
  (`f ∈ fs(x,u) → ∀p.(…)`) and `∃q.(q ∈ x ∧ ∃r.(…))`. Logically equivalent, syntactically
  different; `funspace_pairs_at` (:108) rebuilds the true shape, so in-crate consumers are pinned.
* `derived/src/cumul/ambient.rs:35-43`: "Two symbol comparisons catch it" — the code makes three
  (`pow` is also compared, :63-65). Understates the guard; see also F6.
* `derived/src/universe/closure.rs:534-535`: stale conjunct bookkeeping ("minus its third
  conjunct" — pre-2026-07-31 wording; the predicate now has four conjuncts and the theorem keeps
  C₂ ∧ C₃). Interface line and theorem correct.
* `derived/src/wnat/typing.rs:5-6`: says results surface as `Nat`'s `zero_mem`/`succ_mem`;
  the fields are named `zero`/`succ`.

### F6 (low, fail-closed downstream) — `Chain::over`'s doc claims its comparisons "decide" signature
### coherence; they do not compare `bound`'s `W` against `wt`'s
`derived/src/cumul/ambient.rs:60-68`.

The function doc says "`None` if the three did not come from one signature; see the module header
for the two comparisons that decide it". The comparisons check `up`, `pow`, `lu` — never `bound`'s
`W` against `wt.w`. A `Bound` built over a *second* `Wtype` sharing the same `Sums` and `lu`
passes, and the returned `Chain` carries `bound.sup_mem`/`bound.w_inversion` stated at a `W` that
is not `chain.wt`'s — mislabeled fields, exactly the hazard this constructor exists to prevent.
Verified consequence bound: the incoherent pair cannot reach the checker-facing statement —
`Nat::over`'s `zero` step joins `sup` (from `bnd.sup_mem`, about `W′`) against `in_fs` (from
`wt.empty_fun` instantiated at `ty = W(…)`) at a kernel `mp` (`wnat/apparatus.rs:196-211`), which
fails on `W′ ≠ W` in release. So: a doc defect plus one missing symbol comparison, not a live
route to a mislabeled `NatMem`. The module header's own "necessary, not sufficient" sentence is
the accurate one; the function doc and the missing `W` comparison should be brought up to it.

---

## Suspicions (could not exhibit a failing input; do not chase without a countermodel)

* `derived/src/wrec/is_attempt.rs::iota_on_domain`: validates `rec_thm` by shape destructuring
  only (five leading `∀`s, antecedent forced to `closed(A,B,u)`, body `∀a∀f.(X → (Y ∧ Z))`) —
  `X`,`Y`,`Z` are never compared against the wrec builders. Any theorem of that shape would be
  relabeled ι-on-domain. Only in-repo producer of the shape is `wrec_rec_cond`; the only caller
  passes exactly it and the downstream `debug_assert` pins the equation. Suspicion only.
* `derived/src/sums/sum.rs:140-187` `Sums::over`: stores caller-supplied `pow`/`pow_ax`/`fs`
  unchecked and unused by its own derivations; a mismatched `pow_ax` rides along for downstream
  readers. All known consumers fail closed.
* `derived/src/inductive/carrier.rs:312` `ctor_term`: checks `i < ctors.len()` but not
  `args.len() == k` / `recs.len() == m`; wrong arity yields a well-formed non-constructor term.
  Nothing misattributes a theorem to it; a client could still state an obligation about it.
* `derived/src/sigma/dsum.rs:126-167`: `dsum` mints its `img`/`Σ` definitional extensions before
  the `pparts` shape check at :281 — a refused call leaks two symbols into the `Env`. No wrong
  theorem escapes.
* `DeclSpec::well_formed` — the arity guard `Inductive::build` leans on — lives in
  `inductive/spec.rs`, which was mid-edit and is unaudited. If it under-checks, `build`'s
  header-conclusion agreement was verified independently of it, but the refusal behaviour is
  unverified.

## Answers to the specific questions posed

* **`isum/` caches**: mint→store→retrieve traced concretely (n=2 then 3; i=0,1,2). `Sum_n` keyed
  on `args.len()`, `Inj_i` on depth `i` alone — correct, because `inj_of` never mentions `n` or
  the summands (verified in `tags.rs:113-115`); `inj_mem` on `(n,i)` in push order; `distinct` on
  the **ordered** pair `(i,j)` matching the order-sensitive statement. No off-by-one anywhere.
  The one unkeyed dimension is the `Sums` family — that is F1.
* **`sigma/` telescope**: `tailᵢ = π₂ⁱq`, `compᵢ = π₁(π₂ⁱq)` exactly as advertised; traced k=3:
  `comp₂(q) = π₁(π₂(π₂ q))` and `proj_mem[2]` speaks about precisely that term with the right
  dependency list; last component does go through `π₁`; η pins the residual `π₂ᵏq = •`. The
  telescope cache (in `inductive/machine.rs:113-126`) is keyed on `(np, betas)`; `FnSym` hashes
  brand+id+arity, so cross-`Env` collision is impossible. Cache sound.
* **`cumul/` guards**: symbol provenance of `⊢ N ∈ U₁` fully traced — `nat.ty` verbatim from the
  caller (pinned at witness.rs:307), `u1.set` is the caller's tower's `U(ω)` at the tower's own
  `ω` (forced by the `mp` at :300), tags pinned to `sum(1,1)` at :259-262; the internally minted
  `iter`/`T`/`G`/`V` do not appear in the conclusion. The historical `Chain::new` failure mode
  **is** caught for this statement. The two gaps are F2 (hyps) and F6 (wt↔bound coherence).
* **`ext/dprod_pi.rs` discipline**: holds. All four inputs instantiated at locally-minted fresh
  variables and compared exactly (release `if`s at :87, :91, :103, :116) against formulas rebuilt
  from the caller's `lu`, `b`, `dp.img`, `dp.dprod`, `ap`. No plausibly-wrong input passes.
* **`pi_cong.rs` scope hygiene**: the past out-of-scope-obligation bug is fixed correctly; the
  obligation is generalised only after `uncurry` moves `x ∈ A′` into the consequent, and both
  `ax_dist` uses are at a `k` that closes over `x`. Both `DProd` inputs release-checked (:217, :221).
* **`prop/trunc.rs` and `sums/in_universe.rs`** (landed last hour): both sound. `trunc_ax` really
  `∀a ∀z`; `zero`/`unit`/`distinct` inputs pinned by release checks (:146, :177) or structural
  `mp`. `sum_in_universe`'s guards are adequate: every input instantiated and compared full-formula
  against shapes rebuilt from `s`'s own symbols and the caller's `lu`; wrong-`upair`, wrong-`prod`,
  wrong-universe-operator, concrete-`c`-only, and extra-antecedent inputs all fail closed;
  conclusion exactly `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a+b) ∈ U(c))`.

## Audited and found sound (do not re-verify)

Per slice; "sound" = header/field-doc matches the built conclusion, claimed quantifier prefixes are
delivered by `gen_all`/`define` at genuine variables, antecedents are exactly the listed hypotheses,
and input guards were probed adversarially.

* **`lib.rs` toolkit** (both halves) — all combinators; `define_abbrev`/`define_by_membership`
  discharge the kernel's `∃!` shape exactly; `upair`/`union`/`power`/`union_singleton` etc.
* **`hyp.rs` + `hyp/{order,prop,quant,eq}.rs`** — the invariant `concl == conj(Γ) → φ` is checked
  at every construction site; `into_thm` refuses unless empty, so a `Hyp` can never be presented
  as unconditional; `gen` and `obtain` check their side conditions; the memo key
  `(conj(hs), hs.len(), i)` uniquely determines the split (right-spine peel), so a hit cannot
  return a projection for a different hypothesis list; `rank` collisions cost completeness only.
* **`isum/tags.rs`** in full; **`isum/symbols.rs`** statements (modulo F1's cache lifecycle);
  **`isum/dispatch.rs`** construction incl. tails indexing and beta-chain composition (modulo F5
  header). `Dispatch::new`'s guards adequate (exact checks at :142-146, :151; foreign `Sums`
  fails the `mp`s at :199/:258) — this also discharges fibre.rs's dependency on `beta[i]`.
* **`sums/`** — `sum.rs` (all six exports incl. the α-equality argument in `injection_mem`),
  `unit_type.rs`, `membership.rs`, `cases.rs` (7-quantifier `case_pairs`, weakening in
  `case_beta` as documented), `in_universe.rs` (above).
* **`sigma/`** — `dsum.rs` all six exports (runtime `pparts` pin at :281-288, arity guard);
  `telescope.rs` (index arithmetic above; `k=0` degeneration as documented; `levels/sums`
  alignment after the double reverse); `pair_parts.rs` (`∀A ∀B ∀q` at genuine variables, doubly
  pinned); `shared.rs`. **`proj.rs`** — all five exports end in release-mode
  `if *concl != expected` pins; the strongest discipline in the crate.
* **`fibre.rs`** — `value_mem`, `in_funspace`, `values_in_target` runtime-pinned; `fibre[i]` sound
  via Dispatch (F4 note on the local debug-only pin).
* **`cumul/`** — `step.rs`, `stages.rs`, `bounded.rs`, `closure.rs`, `universe.rs`, `closed.rs`,
  `inside.rs`, `wmem.rs` (both exports incl. `∀A ∀B ∀c ∀d` order; `w_in_universe`'s two-universe
  split is faithfully in the statement), `enums.rs` (exemplary: input hyps, input concl, output
  hyps, output concl all checked), `witness.rs` statements (modulo F2), `chain.rs`. Some thirty
  explicit `if *concl != expected { return None }` sites enumerated and confirmed.
* **`prop/`** — `apparatus.rs` (14 fields), `cond.rs` (`chi_at` guard at :51 routes every lemma),
  `trunc.rs` (above).
* **`ext/`** — `app.rs`, `retarget.rs`, `lam_typing.rs` (no hidden inhabitation antecedent),
  `lam_cong.rs` (capture guard at :103), `funspace_cong.rs`, `shared.rs`, `dprod_n.rs` (all
  checks release-mode incl. output shape; **no caches exist** in `dprod_n`/`dprod_universe_n` —
  every call mints fresh, so there is no per-`n` key to get wrong), `dprod_universe_n.rs`,
  `dprod_universe.rs::dprod_in_universe_of`, `dprod.rs` (modulo F4), `dprod_pi.rs`, `pi_cong.rs`.
* **`inductive/` stable subset** — `shared.rs` (`Ctx`, all four `(k,m)` cases), `carrier.rs`
  `Inductive::build` (seed chain, `fibres`, unconditional `closed`, real `∀p⃗` on `ty_ax`,
  consistent declaration-order indexing), `ctor.rs` (`ctor_typing`: hypotheses exactly the `k+m`
  typings, right-nested, advertised order, capture-safe Leibniz), `distinct.rs`
  (`ctors_distinct` genuinely hypothesis-free; injectivity π₂-spine walk correct),
  `machine.rs` (telescope cache sound; `Machine::over` fails closed on mismatched pairs).
* **`universe/`** — `replacement_n.rs` (both exports release-check final conclusion and inputs at
  fresh variables), `closure.rs`/`least.rs` (`least_universe_transfer` pinning traced at use
  sites), `predicate.rs` (modulo F4 note); `pairing/union/apply/binary/replacement/inaccessibility`
  at guard-and-assembly level. **`tower/levels.rs`** (`omega_at` loop invariant; `Tower::at(n)`
  instantiates every `∀c` field at `seed(n)`; `U₁ = U(ω)` indexing). **`recursion/`** —
  `iterate.rs`/`theorem.rs` in detail (R1-R5 assembly, `∃!` through kernel `define`), remainder at
  guard level. **`funcs/`**, **`funspace/`** (modulo F4), **`separation.rs`** (empty-set probe).
* **W-family** — `wtype` (single-spelling discipline for `closed`/`w_cond`; W1-W3; `w_rect`'s
  params-coverage guard; `empty.rs` functions modulo F5 header), `wrec` (incl. `agreement`'s
  prefix and `empty_attempt`'s unconditionality), `wrec_total` (`Recursor` fields one-for-one),
  `wrec_extend` (modulo F5 header), `wrec_unit`, `wbool_rec`, `wnat` (17 `Nat` fields; the
  deliberate `h ∈ α` asymmetry propagated correctly in `wlist`), `wnat_rec`, `wlist`,
  `wlist_rec`, `wlist_fun` (rules stated at `app(L(S),α)` never `lt(α)`, as promised),
  `recarg` (`m = 0` degeneration over `Sum_0` as documented; pins every `isum` value it consumes,
  so a wrong-index return from `isum` would be rejected here, not mislabeled).
* **Small modules** — `anchor/` (every export ends in a hard `==` check against the advertised
  formula; the non-vacuity story is real), `choice/` (side conditions inherited and checked),
  `bound/` (the rebuild-and-compare discipline its hub header advertises is actually implemented;
  `⊆` vs `∈` honored), `cantor/` (freshness/collision checks on caller-supplied `R`; honest
  "stated at terms" disclaimer), `empty/`, `infinity.rs` (the power-set look-alike is genuinely
  excluded), `pairs.rs`, `point_fun.rs`, `twopoint.rs` (antecedent `¬(a=c)` honestly declared),
  `finset.rs`, `enums.rs` (modulo F4 note).

## Where this audit stopped (mid-edit; unaudited)

Actively edited during the audit (mtimes seconds-to-minutes old) and therefore **not audited**:

* `derived/src/acc.rs` + `acc/` (all files)
* `derived/src/quot.rs` + `quot/` (all files)
* `derived/src/inductive/`: `values.rs`, `recursor.rs`, `iota.rs`, `typed.rs`, `premise.rs`,
  `spec.rs`, `computes.rs`, `members.rs`, `step.rs`, `rec_shared.rs`, and `inductive.rs` itself
  (read for context only). **The whole recursor half of the inductive module (S1-S4, ι) is
  unaudited**, as is `DeclSpec::well_formed` (see suspicions).
* `derived/src/tower/cumulative.rs`

These need their own pass once their editors land.

## Not settled without building

* Nothing in the findings depends on building — every claim above was established by reading the
  conclusion-assembly code against the kernel's semantics. Two things reading cannot establish:
  (1) whether the crate currently compiles mid-edit (irrelevant to the audit question);
  (2) whether the test suite exercises the `debug_assert` pins — they only fire in debug profiles,
  which is the premise of F4; if CI runs tests in release, the F4 class is completely untested.
* Interface-level slices (universe/recursion/funcs, W-family): `pub(super)` internals that only
  feed exact-formula-checked joins in audited consumers were skimmed, not re-derived —
  specifically `wrec_extend/{value,single_valued,product,recursion}.rs`,
  `wrec_unit/composite.rs`, `wnat_rec/{step,members,values}.rs`,
  `wlist_rec/{step,members,values,typed}.rs`, `wlist/typing.rs`, the small `shared.rs` helpers,
  and the bodies of `recursion/{succ,naturals,…}` and `funcs/{apply,coll,…}` beyond their guard
  sites. A drift in any of them produces `None`/panic at an audited join, not a mislabeled
  theorem, which is why the skim is safe for *this* audit's question — but they have not been
  line-checked.
