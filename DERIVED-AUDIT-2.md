# DERIVED-AUDIT-2 — second pass: everything the first audit stopped at, plus everything landed since

Audit date: 2026-08-01, against a quiet committed tree at `db6ff54` (only `checker/src/tg.rs` and
`checker/tests/tg_tutorial.rs` dirty, both out of scope). Method: read-only, no build, no test run.
The kernel (`kernel/src/thm.rs` in full) was re-read first; the target surface (~15,600 lines:
`acc/`, `rec_acc/`, `quot/`, the recursor half of `inductive/`, `inductive/family/`, the new
`cumul/` files, `ext/{fun_ext,eta,*_n}`, `prop/{trunc,cond_ext_n}`, `isum/in_universe`,
`sums/in_universe` delta, `tower/cumulative`, `prelude`, `skeleton`) was then audited in eight
parallel passes over disjoint slices, each reading its slice line-by-line with adversarial input
construction at every caller-supplied-theorem guard, and the top findings were re-verified against
source by the coordinating pass before this report was written. The fix commit `cabf0be` was
verified by replaying the first audit's F1/F2/F3 failure sequences against the new code.

## Bottom line

As in the first audit: **no construction in the audited surface returns a theorem whose conclusion
differs from its header when called with the inputs the crate itself produces.** The specific
hazards the brief named were hunted and came back clean: no F1-shape cache exists anywhere in the
new code (every cache found is derive-then-push, and `ISumSyms` now also rolls back on failure);
`sigma_n`'s de Bruijn identity argument is real and kernel-checked, not asserted; `family/`'s (M)
rule states the `tup(e⃗ᵢ) ∈ Idx(p⃗)` obligation honestly (derived from exported index-typing atoms,
never assumed); the non-vacuity witnesses in `acc/`, `rec_acc/`, `quot/`, `family/vacuous`, and
`prop/trunc` all witness what they claim; and the `MachineId`/`is_over` guards genuinely refuse a
foreign stack wherever they are called (D2 below is where they are *not* called).

What was found instead is the same three shapes as last time, redistributed:

1. **The `hyps()` house rule was adopted unevenly.** The newest files follow it in full
   (`cumul/{decl,tags,sigma,sigma_n,finord,finite,closed}`, `ext/{fun_ext,eta}`,
   `family/{universe,vacuous,good(partial)}`, `isum/in_universe`, `sums/in_universe`,
   `rec_acc/base(partial)`) — some thirty release-mode `hyps().is_empty()` gates, several on
   outputs as well as inputs. But whole new modules written *after* the rule was adopted have
   **zero** `hyps()` reads: all of `quot/`, all of `acc/`, all of `rec_acc/` except `base.rs`,
   `GenRecursor::build`, `Good::build`, and every `ext/*_n` + `prop/cond_ext_n` entry (findings
   1–6 below).
2. **One instance of that gap now has a live shipped caller** — the first time the "only test code
   can mint a hypothetical theorem" mitigation fails (finding 1). Crate-wide fact 1 from the first
   audit must be restated: CI rule 6 scans only `derived/` and `checker/`; **`mini/` is exempt by
   design** (R6′, `ci/check-mini-scope.sh`), is licensed to call `Thm::assume` in shipped code
   (`mini/src/scope.rs`), depends on `derived`, and calls into it.
3. **A new enumeration of F4-class release-unpinned claim legs** (finding 7) and F5-class doc
   mismatches (finding 8), all fail-closed or misuse-gated, none reachable through crate wiring.

The first audit's F1, F2, F3, and F6 are **verified closed** by `cabf0be` (details at the end);
its F4 list is four-sixths fixed, with `ext/dprod.rs` and `ext/dprod_universe.rs` still open.

One framing correction to the brief: every test sweep `ci/check.sh` runs is in the **debug**
profile, so `debug_assert` pins do fire in CI. (At the time of the audit that was three sweeps of
the whole workspace — `cargo test --workspace`, `--features stepcount`, `--features tg`; the two
feature sweeps are now `-p nanoda_lib`, since `derived` neither declares those features nor links
the crate that does, so nothing here changes.) The path where they vanish is the release measurement binary
(`cargo build --release --features stepcount`, MEASUREMENTS.md) and any hand-run
`cargo test --release`. F4-class items are therefore untested exactly on the headline-number path,
as the brief said, but not untested everywhere.

---

## Findings, ranked

### 1 (medium-high) — `Cumul::raise`/`raise_fibres` pin the input conclusion but never read
### `hyps()`, their docs promise `⊢`-to-`⊢`, and — uniquely — a live shipped caller exists
`derived/src/tower/cumulative.rs:162-168` (`raise`: checks only
`*mem.concl() != Formula::mem(x, self.level(m)?)`), `:200-215` (`raise_fibres`: conclusion-only
pin at :211). Both docs read "From `⊢ t ∈ Uₘ` infer `⊢ t ∈ Uₙ`". A `Γ ⊢ t ∈ Uₘ` input passes the
pin, `Thm::mp` unions Γ, and the result is `Γ ⊢ t ∈ Uₙ` under an unconditional label — the kernel
header's "comparing case" verbatim.

Why this outranks every other instance of the same shape: `mini/src/interp.rs::fs_typing` calls
`self.cumul.raise(l1, n, dom_mem)` / `raise(l2, n, cod_mem)` on caller-supplied theorems, in a
crate whose entry points explicitly traffic in `Γ ⊢` sequents (`to_body_symbol`'s doc:
"Rewrite `Γ ⊢ ⟦b⟧ ∈ C`…") and which is exempt from boundary rule 6. `fs_typing`'s own success
check is conclusion-only (`(*out.concl() == want).then_some(out)`), so a hypothetical premise
would come out as `Some`, i.e. reported established. Whether mini *today* feeds `fs_typing` only
hypothesis-free theorems is a question about mini's sealing discipline (not audited — out of
scope); the guard asymmetry plus verified reachability is the defect. Fix shape: one
`mem.hyps().is_empty()` / `fib.hyps().is_empty()` line each.

Verified negative results that bound the blast radius: `Cumul` memoises **nothing** derived from a
caller `Thm` — `raise`/`raise_fibres` store nothing, and the `steps`/`lifts`/`strict` tables are
built in `Cumul::new` exclusively from the tower's own (hypothesis-free) fields with every entry
release-pinned (:229, :246, :268). So there is no cache-poisoning route, and kernel-level
soundness is intact throughout (Γ rides honestly inside the `Thm`). The defect is the label and
any `Some`-means-proved reader. `prelude.rs`/`skeleton.rs` expose no entry taking a caller `&Thm`,
so nothing else in the mini-reachable surface has this shape.

### 2 (medium) — `GenRecursor::build` takes two caller-supplied `&Thm`s and never reads their
### `hyps()`; a hypothetical input's Γ rides into every exported (S4) ι rule
`derived/src/inductive/recursor.rs:111-118` (params `iota`, `funspace`), consumed at
`derived/src/inductive/iota.rs:223-224`; final pin at iota.rs:417 checks `concl()` only.

Concrete failure (test code, or any future boundary exemption): pass
`Thm::assume(f)` where `f` is `wrec_total::iota`'s exact conclusion (clone the real theorem's
`concl()`). `build` succeeds — the formula is closed, so every `gen` passes — and
`GenRecursor.iota[i]` is `{f} ⊢ ∀p⃗∀s⃗∀T∀y⃗∀t⃗.(…)` while the struct doc (recursor.rs:29-31,
:101-102) claims `⊢` outright. Wrong-*conclusion* inputs do fail closed (traced: a
foreign-`Recursor` `iota` dies at the `hyp_eq_trans`/final-pin joins; a wrong `funspace` at the
`wt.app_mem` join) — only the hypothesis leg is open. This is the flagship checker-facing entry of
the general recursor, written after the house rule was adopted, and it is the exact F2 shape.

Same defect, same module family: **`Good::build`** (`derived/src/inductive/family/good.rs:122-155`)
takes `iota`/`funspace` with no `hyps()` read; `fs_thm`'s conclusion is pinned (:155) but not its
hypothesis set, and the stored `wrec_iota` (:153) is pinned not at all, while the `Good::funspace`
field doc (:103) says "unconditional". Fail-closed today only because both in-crate consumers
re-check (`vacuous.rs:333` checks output hyps; `good.rs:210` checks per-ctor `eq.hyps()`); any new
consumer reading `good.funspace.concl()` inherits the comparing case. Contrast
`family/universe.rs:75,:118-120` in the same directory, which checks everything both ways.

### 3 (medium) — all of `quot/` postdates the house rule and applies it nowhere; `Quotient::over`
### accepts a `Sums` with hypothetical theorem fields and every field doc claims `⊢` outright
Zero `hyps()` reads in the module. Every public entry takes unpinned `&Thm`s, and
`Quotient::over` (`derived/src/quot/apparatus.rs:141`) consumes a caller-supplied `Sums` whose pub
theorem fields are unchecked. Concrete (test-code-gated): give `Sums.pow_ax` a `Thm::assume` of
its own statement and pass it to `Quotient::over` — `mk_mem`'s `Thm::mp`
(`quot/classes.rs:352`) imports Γ, and the returned `Quotient` carries Γ on `mk_mem`,
`quot_cases`, `sound`, `lift_in_funspace`, and all five non-vacuity fields, while the field docs
(apparatus.rs:79-126) claim unconditional theorems. Conclusion shapes throughout the module are
pinned well (see sound list) and the `gen_all`s cannot panic (generalised variables are minted
after entry, so no caller Γ can mention them); the hypothesis leg is the only gap. One
`hyps().is_empty()` sweep over the module's `&Thm` parameters closes it.

### 4 (medium-low) — the F3 fix does not cover the new public term-builders: `carrier_at`,
### `GenRecursor::rec_of`, `GenRecursor::step_of` resolve against an arbitrary machine with no
### `is_over`, yielding well-formed terms nothing about this declaration is true of
`derived/src/inductive/recursor.rs:241-258` (`carrier_at`: `tags` from `mach.syms.sum`, `fam` from
`mach.cases`, `u` from `mach.bnd`), `:222-234` (`rec_of`, inherits), `:213-220` (`step_of`, takes a
bare `&Sums`). Concrete: `mach2 = Machine::over(env, wt, bnd)` sharing `mach1`'s `Wtype`, `syms`
warmed by a second declaration; `carrier_at(&mach2, &ind1, ps)` returns
`(Sum′_n(A⃗), fam′, U(…), W(A′,fam′,…))` built from `mach2`'s symbols — not `ind1.wty` at `ps` —
with no error. The doc says these are what a client uses "to *state* something about the recursor
at an instantiation": the stated obligation is then about the wrong terms, which is precisely the
mislabelling `is_over`'s own comment (carrier.rs:355-361) says costs a session. Fix shape:
`ind.is_over(mach)` at the top of `carrier_at`/`rec_of`; make `step_of` take the machine.

### 5 (medium-low) — `Base::over`'s hypothesis guard covers four of the seven `Acc` theorem
### fields while its doc claims all; the gap feeds `rec_acc`'s advertised-unconditional
### non-vacuity witnesses
`derived/src/rec_acc/base.rs:123-131`: the doc (:119-122) says it "refuses an `Acc` whose theorems
carry hypotheses", but the loop checks exactly `acc_ax`, `acc_subset`, `acc_induction`,
`acc_intro` — not `empty_ax`, `minimal`, or `empty_relation`. `rec_acc/witness.rs:146`
(`unit_accessible`) consumes `ac.empty_relation` with a conclusion-only pin. Concrete
(test-code-gated; `Acc` fields are pub): set
`ac.empty_relation = Thm::assume(∀A. acc(A,∅)=A)`, pass through `Base::over` (accepts) and
`RecAcc::over` (never touches it); `unit_accessible` returns `{…} ⊢ • ∈ acc(1,∅)` and
`unit_facts` (witness.rs:189) threads Γ into all four returns — so the hub's "Every one of these
has no antecedent at all" (rec_acc.rs:151-169) is falsified by a passing input. (`empty_ax` is
safe by accident — a hypothetical one dies at kernel `define` inside `separation_full`; `minimal`
is unconsumed in `rec_acc`.) The related systemic items: **all of `acc/`** has zero `hyps()` reads
(`acc_rect` accepts a hypothetical `Acc.acc_induction` and returns a Γ-carrying scheme), and all
of `rec_acc/` outside `base.rs` — every one of the ~20 pub constructors taking `&Thm`
(`cval_app`, `ih_*`, `rec_*`, `ext_*`, …) — skips the check. All test-code-gated today.

### 6 (medium-low) — the `ext/*_n` + `prop/cond_ext_n` entries read no `hyps()`, and one of them
### is called directly by `mini`
Eight of the ten public constructions in the new/moved `ext`/`prop` slice skip the check
(the two newest — `fun_ext.rs:121`, `eta.rs:130,163-166` — apply it in full):
`lam_typing_n.rs::{lam_pair_val_n, lam_single_valued_n, lam_in_funspace_n, lam_in_dprod_n}`,
`lam_cong_n.rs::{image_ext_n, lam_ext_n}`, `pi_cong_n.rs::dprod_ext_n`,
`const_fibre_n.rs::dprod_const_fibre_n`, `prop/cond_ext_n.rs::cond_ext_n` (its `guard` closure at
:108-117 compares `concl()` only; kernel hyps ride through `Hyp::lift`). None checks the theorem
fields of `Apply`/`Funspace`/`Product` either. Concrete failure: `Thm::assume` the exact closed
formula `lambda_n` would produce and pass it as `lam_ax` — every pin passes (they read `concl()`
only), every `gen` succeeds, and release returns `{φ} ⊢ ∀p⃗ ∀A ∀C. (…)` from functions documented
`⊢` outright. Adjacency note: `mini/src/interp.rs:349-357` calls `lam_in_funspace_n` in shipped
code; today its `lam_ax` input is `lambda_n`-built and hypothesis-free, and mini's scope
hypotheses have `x ∈ ⟦A⟧` shape rather than axiom shape, so this is a discipline gap with a live
adjacent producer, not a current exploit. (`checker/src/tg.rs` imports the same entries.)

### 7 (low-medium, F4 class) — release-unpinned claim-carrying legs, new enumeration
Each succeeds in release with a plausibly-wrong input and returns a correctly-proved theorem under
the wrong label; all are unreachable through the crate's own wiring (verified per item); the
consequent-shaped ones are the ones worth fixing first because the consequent *is* the claim.

* `derived/src/cumul/closed.rs:496-530` `tower_closed`: pins `bounded`'s exact statement (:487)
  and forces `general`'s **antecedent** to Fin⁺ (the :523 comparison against a locally-built
  `weaken`), but the consequent is read off `general_at.concl().as_imp()` at :497 and never
  compared to `closed(A,B,T)`; the output pin (:527) uses that floating `concl`. Weakening
  `tower_closed_bnd`'s output by any syllogism and regeneralising yields
  `⊢ ∀A∀B.(Fin(A,B) → ψ)` for arbitrary ψ, attributed by name and header (closed.rs:14-15) to
  `closed(A,B,T)`. Its sibling `tower_closed_bnd` pins its consequent (:450-453); promote to match.
* `derived/src/rec_acc/cval.rs:257-320` `cval_app` (pub, hub-re-exported): the advertised beta
  equation — the entire consequent — comes solely from the caller's `app_of_graph` and is pinned
  only by `debug_assert_eq!` (:314-318). Any theorem
  `∀g∀x∀y.((sv(g) ∧ ⟨x,y⟩ ∈ g) → C(g,x,y))` relabels `C` as the beta rule. No in-repo confusable
  with that antecedent exists (`recursion::app_of_graph` is the only producer), and a wrong
  `cval_app` fed onward dies at `ih_app`'s release pin (ih.rs:922-931).
* `derived/src/acc/witness.rs:57` `acc_minimal`: consequent from the caller's `acc_intro`, final
  shape pinned only by `debug_assert_eq!` (:91-95). `derived/src/rec_acc/attempt.rs:168`
  `empty_attempt`: final membership pinned only at :245-249 (debug); the caller's `att_ax` LHS is
  never release-compared, so a foreign `∀…(g ∈ FOO ↔ same-RHS)` relabels the theorem as about
  `Att`. `derived/src/rec_acc/witness.rs:189` `unit_facts`: returns 1-2 (`in_dom`, `fsp`) have no
  release pin — a `UnitInputs.funspace` of shape `ST → anything` returns "anything" labeled
  `F ∈ fs(acc(1,∅),1)`; returns 3-4 are pinned (:220, :230).
* `derived/src/quot/lift.rs:400` `lift_beta`: release-pins only its antecedent; the consequent —
  the ι-rule equation `app(lift,[x]) = f·x`, the statement the checker's `124_quotLiftReduction`
  story rests on — comes verbatim from the caller's `app_pair`. And four `quot` exports with no
  output check at all: `q_sound` (classes.rs:407), `compat_at_empty` (witness.rs:189),
  `class_injective_at_empty` (witness.rs:257), `lift_beta_at_empty` (witness.rs:279). All are pure
  input-compositions whose middle formulas the kernel forces; no in-crate wrong input pair
  composes.

Still open from the first audit's F4 list: `ext/dprod.rs:237-270` and
`ext/dprod_universe.rs:167-196` (untouched since); `universe/predicate.rs` hardening note
(docs-only commit since). Fixed by `cabf0be`: `funspace/in_universe.rs` (:287-292, now
release+hyps), `fibre.rs` (:256-266), `enums.rs` (:298-305, :332), `pairs.rs` (:261-272).

### 8 (low, fail-closed) — headers and docs that mis-state what the code correctly builds
* `derived/src/inductive/family/carrier.rs:28` and `family/le.rs:69`: antecedent written as
  grouped `(Hᵢ ∧ Eᵢ)`; the built formula is one flat right-nested chain over all `k+m+ni` atoms.
  `IndexedCtor::mem_atoms` exports the true list, but **`LeCarrier` exports no atom list**, so a
  caller rebuilding the grouped form gets a rejection. (Same F5 shape the first audit found in
  `inductive/{carrier,ctor,distinct}` — fixed there by `cabf0be`, reintroduced here.)
* `derived/src/inductive/step.rs:364-366` (`StepSym::e`): doc states arity `np+2` and prefix
  `∀p⃗∀s∀T∀x` unconditionally; under `Vals::Good` it is `np` and `∀p⃗∀x` (`GoodStep`'s own field
  doc :84-86 is correct).
* `derived/src/cumul/apparatus.rs:53` says "`Chain::over`'s five symbol comparisons";
  `derived/src/cumul/ambient.rs:35` says "Four" (its fourth bullet contains two `==`). The code
  makes five. A guard-count disagreement in the exact place guard counts were finding F6.
* `derived/src/prelude.rs` (`fast_forward` doc): claims necessity ("the single thing that must not
  happen") for a collision the brand system already makes impossible (`FnSym`/`FreeVar` carry the
  `Env` brand). Belt-and-braces presented as load-bearing; harmless.
* `derived/src/ext/fun_ext.rs:136`: the `pw != pointwise(...)` self-check is a tautology under
  locally-nameless α-equality — cosmetic.

---

## Suspicions (no failing input constructed; do not chase without a countermodel)

* `derived/src/inductive/machine.rs:113` `Machine::over(env, wt, bnd)` never checks `bnd` was
  built over `wt` — the F6 shape one level up. `Inductive::build` fails closed on a mismatch (the
  `closed`/`sup` `mp`s at carrier.rs:273/:293 need `bnd`'s symbols to be `wt`'s); other `Machine`
  consumers were not exhaustively enumerated.
* `derived/src/inductive/family.rs:126`: the "skeleton must be this declaration's erasure" gate
  compares only `params` count and constructor **count**, not per-constructor `args`/`recs`/
  `order`. Every divergence constructed dies at a kernel join deep inside; the refusal just does
  not come from the gate that claims to enforce it.
* `GenRecursor::build` with a foreign machine fails closed (traced to `typed.rs:105` /
  the `k_fib` join) but only after minting one Replacement symbol per constructor into the `Env` —
  symbol leakage on refusal, same class as the first audit's `dsum` note. `cumul/sigma_n.rs` mints
  one fresh companion image symbol per outer level per call — same class. An explicit
  `ind.is_over(mach)` at `build`'s top would also close finding 4.
* `derived/src/rec_acc/union.rs:83-119` `rec_members`: the output iff's RHS is read off
  `b.s.ap.sets.un_ax` (`as_iff`, :106) rather than rebuilt; the theorem is *labeled* with whatever
  that body is. Sound today (the field is the Sets union axiom, first-audit sound), and a drifted
  RHS fails closed at every downstream join traced.
* `derived/src/tower/cumulative.rs:224-247` `Cumul::new` reads `t.at(n)` theorem conclusions but
  not their `hyps()`; a doctored `Tower` would put Γ into the `lifts` table — a stored certificate
  replayed for every later caller (the definitional-equality-cache shape). Gated: the live path
  gets its `Tower` via `Rc<Prelude>`, honestly built.
* `derived/src/inductive/iota.rs:154`: the sole cross-check that ι's constructor spelling equals
  `ctor_term`'s is debug-only; today both are literally the same expression, so drift requires
  editing both spellings.
* Reproducibility nit (no soundness effect): several `quot/` `debug_assert`s evaluate
  `env`-mutating expressions (eqv.rs:316, classes.rs:159, lift.rs:488, :539, compat.rs:264, :438),
  so the fresh-variable stream diverges between debug and release builds after those points.

---

## The brief's specific questions, answered

* **Does `family/`'s (M) rule state the `Idx` obligation?** Yes, exactly. The antecedent is the
  atom list built at `family/carrier.rs:336-349`: `k` plain typings, `m` recursive-argument
  typings at the *indexed* types, then the `ni` result-index typings
  `eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, e⃗<k)`. `tup(e⃗ᵢ) ∈ Idx(p⃗)` is **derived** from those atoms via
  `conj_sub` + `Telescope::intro` (:386-392), never assumed. The exported conclusion is
  release-pinned (:466) as `conj(atoms) → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗))`, ∀-closed over
  `p⃗ y⃗ r⃗`, and `mem_atoms` exports the atom list so the checker can state exactly what it owes.
  (I) is pinned at :575. The design deviation is recorded honestly in three places.
* **Is `sigma_n`'s de Bruijn move sound?** Yes, and it is checked, not assumed. The inclusion
  `imgᵢ ⊆ img'(p⃗,y⃗,βᵢ)` is one `syl` between `iff_mp` of `dsum`'s `img_ax` and `iff_mpr` of the
  companion's `imgn_ax` (sigma_n.rs:470-482): `Thm::mp` compares the two existential bodies
  syntactically, so a de Bruijn mismatch returns `None`; the result is additionally release-pinned
  (:482) against `subset(...)` rebuilt from the telescope's own symbols, and the Replacement rule
  full-formula-pinned (:460-467). The `want`/`expected` pins in the slice are **not circular** —
  each compares against formulas rebuilt from caller-supplied subjects and the exported public
  builders (`obligations()`, `bounded::bnd`, `ind.summands[i]`), never from the derivation's own
  intermediates.
* **Did the Machine-as-argument rework (`ec9e017`) keep the identity checks?** Yes. Every public
  entry in `cumul/{decl,tags,sigma,sigma_n}` guards `ic.is_over(mach) && ind.is_over(mach)`.
  `IndChain::is_over` compares `up`/`w`/`lu`/`sum` plus `SumClosure::is_over` (a real family
  identity, `(s.sum, s.ap.sets.up)`); `Inductive::is_over` compares the full `MachineId`
  (`up`,`w`,`case`,`inter` — `case`/`inter` minted fresh per `Machine::over`, so even two machines
  over the same `Wtype`+`Bound` differ) plus `inj_syms`. Two-stack traces refuse at the right
  comparison. Residual: `Apply.app` is not compared (documented "necessary, not sufficient"; a
  mixed-`app` stack fails closed at the first kernel join). First audit's F6 (missing `bound.w`
  vs `wt.w`) is **fixed** in `Chain::over`. The remaining `is_over` gap is finding 4.
* **Vacuity.** All non-vacuity witnesses audited are real: `rec_acc/witness.rs` (a member of
  `accrec` exhibited, ι fired closed with both sides computed — modulo findings 5/7),
  `acc/witness.rs` (`acc_no_loops`/`acc_no_two_cycle` genuinely negative-polarity),
  `quot/witness.rs` (the `eqv = A²`/`quot = {A}` collapse genuinely excluded; `eqv_of_empty`
  really the diagonal), `family/vacuous.rs` (final pin checks hyps and pins
  `∀z. ¬(z ∈ ind(p⃗,x⃗))` at the caller's own indices through `ixc.ty_of` — the strong form,
  ruling out an always-`Idx` `good`), `prop/trunc.rs` (`‖1‖=1`, `‖0‖=0`, distinctness via
  `tags_distinct`), `cumul/finite.rs:42-51` (the `bnd(ω)` refutation honestly marked "written
  down here, not derived" — nothing in the slice assumes `bnd` of anything). `good` does not
  accept everything.
* **Caches.** No F1-shape defect anywhere in the audited surface: the `Machine` telescope cache is
  derive-then-push keyed `(np, β⃗)`; `Cumul`'s tables are tower-internal and pinned; `mini`'s
  `lam_site` cache is out of scope but keyed on the skeleton after successful minting; `ISumSyms`
  post-fix binds the cache to a family identity **and** truncates on failure (see below).

## Fix-commit verification (`cabf0be`, plus follow-ups)

* **F1 — closed.** `ISumSyms` binds its cache to `Family = (s.sum, s.ap.sets.up)` checked by
  `is_over` at every entry (isum/symbols.rs:189-208), and `ensure` snapshots and truncates
  `injs`/`levels` on failure (:210-224). Replaying the F1 sequence: `ensure(s2,3)` now fails at
  `is_over` before touching anything; `ensure(s1,3)` then derives arity 3 for real. The `eq_refl`
  placeholder is gone (`inj: Option<Thm>`), the `no_junk` panic is now `None` (:458-474), and two
  output-`hyps()` gates sit before caching (:255, :308).
* **F2 — closed.** `NatMem::over` checks both consumed `Nat` theorem fields' hyps (:196), pins the
  final conclusion (:348) and the intermediates (:256-261, :300, :470, :481), and gates the return
  on `is_unconditional()` over all seven outputs (:135-147, :366).
* **F3 — closed, with residue.** `Inductive` stores `MachineId` + `inj_syms`; `ctor_term`
  (carrier.rs:386) and `distinct` (:408) refuse on `is_over` failure, and `ctor_term` now also
  pins `args.len()`/`recs.len()` (the first audit's arity suspicion). Replay refuses regardless of
  cache warmth. The residue is finding 4: the *new* term-builders in `recursor.rs` were written
  without the guard the fix added next door.
* **F6 — closed.** `Chain::over` now compares `bound`'s `W` against `wt`'s.

## Audited and found sound (do not re-verify)

"Sound" as in the first audit: header/field-doc matches the built conclusion, claimed quantifier
prefixes delivered by `gen_all` at genuine variables, antecedents exactly as listed, guards probed
adversarially — modulo the findings above where noted.

* **`acc/`** — `acc.rs` hub; `condition.rs` (single-spelling discipline; `acc_subset` input pinned
  :160-166); `induction.rs` (both instances pinned); `intro.rs` (five release pins, `ax_dist`/`gen`
  at fresh variables); `rect.rs` (`acc_rect`'s conclusion kernel-forced in release; `zv ∉ params`
  checked; ∀-elision honest); `witness.rs` (modulo finding 7); `apparatus.rs` (`Acc::over` pins
  `empty_ax` over the supplied symbol). A hand-mixed `Acc` (symbol from acc₁, theorems from acc₂)
  fails closed at the first kernel `syl` in every path traced.
* **`rec_acc/`** — `base.rs` pairing-identity check (catches a foreign `Sets`; modulo finding 5);
  `attempt.rs` (Separation and clauses pinned; modulo `empty_attempt` in finding 7); `agree.rs`
  (nine release pins; the "`y ∈ acc` not used" claim true); `is_attempt.rs` (all three exports
  pinned; `iota_on_domain` fully pins its `rc` input — the first audit's wrec-shape suspicion does
  **not** recur here); `total.rs` (`ST` genuinely the only antecedent; pins :133, :181-190, :240,
  :251, :257); `package.rs` (deviation honestly documented; pins :131, :168); `witness.rs` pins
  :220/:230; **`cval.rs`** (six exports, quantifier order verified; `cval_single_valued` pinned
  against rebuilt `is_single_valued` — modulo `cval_app` in finding 7); **`ih.rs`** (all six; the
  three final debug_asserts each redundant with a kernel-forced or release-pinned last join —
  not F4-class; `ih_app` pinned :922-931; the first audit's `pow_ax` suspicion neutralized here);
  **`union.rs`** (seven exports, strongest discipline in the slice; modulo the `rec_members`
  suspicion); **`extend.rs`** (all twelve statements at the caller's concrete terms exactly as the
  header frames them — no false generality; ~25 release pins against formulas rebuilt from `Ext`'s
  own terms; hypothesis `K` left-nested as spelled; the no-case-split `sv(G)` argument is what the
  header claims). Hub `rec_acc.rs` + `apparatus.rs`: no F5 mismatch; `RecAcc::over` threads one
  development throughout.
* **`quot/`** (conclusions and shapes; modulo findings 3 and 7) — `eqv.rs` (eight theorems, Horn
  argument real, four clause pins :558-562); `classes.rs` (`Classes::parts` pin :139 makes a
  mixed-stack fail closed; `class_eq`'s extensionality argument incl. α-equality; `class_exact`'s
  `b ∈ A` asymmetry correctly built); `lift.rs` (`lift_single_valued`'s double `hyp_obtain`
  side-condition-clean; `lift_in_funspace` pins :551/:557); `compat.rs` (`ker_closed`'s four
  clauses individually pinned against `eqv_atoms`; only "contains R|A" spends `rcompat`, as
  documented); `witness.rs`; `shared.rs` (`hyp_obtain`'s S-contraction verified);
  `apparatus.rs` wiring checked argument-by-argument.
* **`inductive/` recursor half** — `spec.rs` (`well_formed` checks exactly what is leaned on:
  `βᵢ` arity `np+i`, `order_consistent` mask counts; an under-check lands on `Term::apply`'s loud
  arity panic, mislabeling nothing); `machine.rs` (telescope cache derive-then-push; `MachineId`
  per-apparatus); `step.rs` (`unpack`/`unpack_row` pinned; Replacement `∃!` discharged honestly;
  modulo the doc nit); `members.rs` (`row_in_step` union-climb indexing correct; `step_cases`
  per-link `e_ax` pinned; both finals pinned); `values.rs` (`value_at`: branch `i` by `inj_inj` +
  pair injectivity, `j ≠ i` refuted by `inj_distinct` alone — the §7.8 shared-telescope hazard
  genuinely avoided; `step_single_valued` pinned against rebuilt `is_single_valued`);
  `computes.rs` ((S1) exactly as advertised, pinned); `typed.rs` ((S3) pinned against
  `wrec_total::step_typed` rebuilt; junk instantiations covered because `minor_typed` quantifies
  over `W`); `premise.rs`/`rec_shared.rs`; `iota.rs` ((S4) exactly as advertised: final pinned
  :417 at the constructor's own variables with ih slots `app(grec,tⱼ)`, hypotheses exactly
  `HYP ∧ Hᵢ^ctor`, prefix `∀p⃗∀s⃗∀T∀y⃗∀t⃗` — modulo finding 2's hypothesis leg);
  `carrier.rs`/`ctor.rs`/`distinct.rs` deltas (F3 fix + F5 header fixes verified; `7fd061d`
  doc-only). Release-pin discipline in this slice is good; no new F4 instance.
* **`inductive/family/`** — `spec.rs` (`plains_before` mask walk; `tup` = `Telescope::tuple_of`'s
  spelling, so index tuples and telescope elements are the same term); `index.rs`; `gval.rs`
  (`in_target` doubly pinned, genuinely unconditional); `goodstep.rs` ((S3) pinned :376 and
  genuinely antecedent-free); `good.rs` per-ctor ι (pinned with hyps :210; modulo finding 2's
  `Good::build` leg); `carrier.rs` ((M)/(I) as above; comps↔fields rewrites Leibniz-based,
  fail-closed); `universe.rs` (exemplary: `is_over` + hyps + concl, in and out); `vacuous.rs`
  (refutation inputs checked both ways; the strong-form claim real); `le.rs` (`intro` :281,
  `degenerate` :333 pinned; the `up`-symbol guard :139 compares exactly the symbol that decides
  pair identity; `R = ∅` through real Extensionality; no capture in the ∃-closing loop).
* **`cumul/` new files** — `decl.rs` (eight fields incl. `[H →]` placement; `rests_on_nothing`
  on all seven outputs; `fin_elim` pinned; `seed_in_bound` literal-`{A,T}` check); `opt.rs`
  (`Ctx` honest); `tags.rs`; `sigma.rs` (structural checks tie the `DSum` to the telescope);
  `sigma_n.rs` (see above; `hyp_gen` sound via `ax_dist`'s side condition; `k = 0` lands on the
  pinned base); `finord.rs` (`m = 0` on the `⊥`-base and `Sum_0()` as documented); `finite.rs`
  (directedness merge traced three `discharge`s deep; four interior pins); `bounded.rs` (exported
  `bnd(k)` verbatim the header's; the seven debug_asserts guard interior shapes only, and the one
  consumer release-pins the exact statement); `closed.rs` (`fin_bnd`'s placeholder-then-substitute
  order protects a caller whose `A`/`B` mention `st.seed`; `tower_closed_bnd` in full — five
  release pins including the final consequent; `tower_closed` modulo finding 7); `apparatus.rs`
  ordering claims; hub `cumul.rs` table. House-rule compliance in this slice is complete —
  inputs *and* outputs.
* **`ext/` + `prop/` new/moved** (conclusions and shapes; modulo finding 6) — `fun_ext.rs` (export
  exactly the header's 4-∀ right-nested form, pinned :221; all inputs pinned against formulas
  rebuilt from `ap`/`p`/`fsp` via `isfun_parts` — not circular; discharge chain
  side-condition-clean; empty-domain story matches); `eta.rs` (all four fields; instances pinned
  :185/:201/:210/:226, final :241; wrong `graph` fails :201/:210); `lam_typing_n.rs` (all four
  exports, ~16 release pins, **zero** debug_asserts — an earlier grep counted comments); 
  `lam_cong_n.rs` (capture guard :111-115 sufficient; final pins :205/:357); `pi_cong_n.rs` (the
  historical out-of-scope-obligation shape handled correctly at :175/:192; pins :216/:220/:232);
  `const_fibre_n.rs` (pins :113/:124/:160/:191/:203; the unpinned instances forced by downstream
  kernel joins — fail-closed); `prop/cond_ext_n.rs` (χ axioms pinned against the
  `conditional_singleton` shape rebuilt from `sums`; Hyp discharges closed out; final :177);
  `prop/trunc.rs` (no delta — `1ef1728` created the file the first audit already audited).
* **Misc** — `isum/in_universe.rs` (strongest guard discipline in its slice: four-input hyps gate,
  `is_over` on both structs, every fold step and the final pinned incl. output hyps :333; `m = 0`
  claim delivered); `sums/in_universe.rs` delta (strictly strengthens: hyps gate :101, final
  debug_assert → release pin with output-hyps :185); `tower/cumulative.rs` statements (index
  bookkeeping verified: `lifts[m][n-m] = ⊢ Uₘ ⊆ Uₙ`, `n < m` fails closed; `strict` real; modulo
  finding 1); `prelude.rs` (packaging only; fields filled from audited producers over one stack;
  `n_syms`/`n_vars` include the probe id, so `fast_forward` burns strictly past everything);
  `skeleton.rs` (no `Thm` built or consumed; header honest; hole/`x_canon` ordering correct).

## Where this audit stopped

* **`mini/`** — out of scope, but it is now part of `derived/`'s threat model (findings 1, 6).
  Two one-line observations recorded for whoever audits it: `fs_typing` and `lam_typing_fs` join
  caller theorems by kernel `mp` (which silently unions Γ) and then check `out.concl()` only, so
  an undischarged scope hypothesis would ride into a theorem mini treats as established; whether
  the `Sealed` funnel is the only path such theorems can take was not established here.
* **`checker/src/tg.rs`** — mid-edit and does not compile; not read beyond import sites.
* Pass-level skims (a drift in any produces `None` at an audited pinned join, not a mislabel):
  `ctor.rs` below :110 (delta since first audit verified doc-only by diff); `wrec_total`/`Fibre`/
  `RecArg`/`Telescope` internals; `funcs/beta.rs` at assembly level; `hyp.rs` internals beyond
  `lift`/`into_thm`; `cumul/{chain,ambient}.rs` re-read at guard sites only (F6 fix confirmed),
  and `stages/step/witness/enums/inside/wmem/closure/universe.rs` unchanged since the first
  audit's sound list; `iota_core`/`step_single_valued`/`row_in_step` consumed by `family/` through
  pinned joins; `finite_branching` internals at guard level.

## Not settled without building

* Nothing above depends on a build; every claim was established by reading conclusion-assembly
  against the kernel's semantics (kernel/src/thm.rs re-read in full this pass).
* Whether any test exercises the finding-7 debug-only pins: CI's three `cargo test` sweeps run in
  the debug profile, so the asserts are live there *if* a test reaches them with a wrong input —
  which none should; the release measurement path exercises none of them. Confirming an individual
  pin fires requires a deliberate wrong-input test, i.e. a build.
* Whether `mini` today feeds `Cumul::raise`/`lam_in_funspace_n` only hypothesis-free theorems:
  requires auditing `mini`'s scope/sealing discipline end-to-end, which is a build-independent but
  out-of-scope read; finding 1 stands on the guard asymmetry plus verified reachability either way.
