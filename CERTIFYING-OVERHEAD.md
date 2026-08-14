# Certifying overhead — where the accepting and certifying walks diverge, judged

*2026-08-07. An architecture judgement, not a work plan. The question: the
uninstrumented checker looks at `e.1` and, by implicit rule inversion, assumes
`e` well-typed; producing evidence seems to require re-typechecking `e`, and a
cache breaks under substitution and on open terms. Is that a weakness of the
certifying design — can this checker have tolerable overhead? A sharper
hypothesis was raised mid-question: does the checker run an accepting `infer`
**and** a certifying `infer_ev`, causing an exponential blowup? Both are
answered below against the code and the measured record; the appendix lists a
source for every number used.*

## Verdict

**Yes — this design reaches a corpus 700× the current one, with two changes to
the checker and none to `kernel/`.** The measured blowup (40,271 → 4,369,255
conversions, 4.5 s → 10 min on `proj_reduced_carrier`) is not the intrinsic
price of certifying; it is a *recurrence*, and the owner's exponential
hypothesis is confirmed in mechanism though not at the guessed site. There are
no twin `infer`/`infer_ev` walks — mini's inference is one fused traversal —
but the certified reduction path re-enters full `infer_type` from inside
itself: `beta_premise` runs `infer_type(arg)` at **every β step**
(`kernel.rs:1736`), `def_eq_ev` runs `infer_type(e1)` at **every entry**
(`kernel.rs:3080`), nothing caches `infer_type`, and inference recursively
reduces, whose β steps re-infer their arguments — geometric compounding in the
nesting depth, armed only on the certified path (an acceptance walk hands
`tm = None` and bails before the premise is asked, which is exactly why
acceptance stays at 4.5 s while certification takes 10 minutes). The code
already names it: *"an argument inferred twice is an argument's whole subtree
walked twice, and at a nest of arguments that are themselves nests the factor
compounds"* (`kernel.rs`, `beta_premise_of`). This is a **design flaw a
certifying checker can fix, not a cost intrinsic to certifying** — and §4's
counters, run, say the fix is not the one this section first proposed. The
sentence *"the premise being re-derived is a value the checker held moments
earlier — `stack_tms` carries `⟦a⟧` but drops the membership theorem beside
it"* was wrong: `whnf_conv`'s `App` arm **peels** `⟦a⟧` out of `⟦f a⟧` and
never infers it, so there is no membership beside it to drop, and a `Typing`
minted at the push would be paid 252 962 times to save 119 216 (§4). What the
counters do confirm is that the re-derivation is nearly all *duplicate* —
**97.8%** of conversions happen inside a repeat of an already-seen
α-canonical judgement — so the value the checker held moments earlier is real
but is held across an *opening*, not across a stack slot. The metatheorems
whose absence forces the premise to *exist* (inversion, preservation,
substitution) each still have an O(1)-per-step certified replacement once
evidence is carried instead of re-derived. What blocks the cheap cache rescue
is real and also fixable: certificates stored in scope-relative form die with the binder
opening, so the memo must key on α-canonically *closed* judgements and store
`Sealed` (hypothesis-free, ∀-closed) theorems, re-instantiated at hits — the
closed form is the substitution-stable form. Fix the recurrence (carry typing
evidence through the reduction stack) and the sharing (the Sealed memo), and
the intrinsic residue is a **constant 30–100× over the uninstrumented
checker, linear in the corpus** — a one-time certification run in hours at
700×, not months. The two-counter measurement in §4 settles the diagnosis in
one run of the existing ten-minute fixture before any of this is built.

---

## 1. The four candidates, read against the code

### (a) Duplicated traversal — an accepting pass and a certifying pass over the same term

**Absent in the form hypothesized; present in a bounded, partly deliberate
form at decision seams.** There is no `infer`/`infer_ev` pair: inference is
one traversal producing type, interpretation and evidence together — "`⟦e⟧`
*is* `infer_type(e).tm` — there is no separate `interp` traversal"
(`kernel.rs:187,493`), and `whnf` (acceptance) is `whnf_conv` with `tm: None`
— the *same* loop, with certificate legs simply not built (`kernel.rs:734`).
So the naive symmetry argument survives at the traversal level: one walk,
evidence fused in.

What does exist is the **acceptance-decides / evidence-pays seam**: shape
decisions run acceptance-only, and where the step then fires, the certified
form is paid for separately — the projection arm reduces its subject with
`self.whnf(s)` acceptance-only (`kernel.rs:1273`) and `proj_data::iota` later
composes the certified reduction; the `StuckRecursor` arm reduced its major
acceptance-only with no certificate to compose (`MEASUREMENTS.md`,
2026-08-07). Each seam costs at most a re-walk — a bounded factor, not a
recurrence — and one is deliberately kept: paying for certificates on *stuck*
projections took `077_RBTree.id_spec` from 0.6 s to over two minutes
(`kernel.rs:1265–1272`), so deciding cheaply first and certifying only fired
steps is correct. Verdict: not the engine.

### (b) Premises re-derived inside reduction — the engine, confirmed

The structural difference between the two walks is not the certificate for a
step — each step's certificate is a bounded splice (delta: one stored
equation, `delta_evidence`; β: `beta_leg` + `body_unfold`; ι through an
interpreted recursor: a β chain down the stored nest). It is the **premise**:
TG's β is typed where Lean's conversion is untyped. `⟦(λx:A.b) a⟧ = ⟦b[a]⟧`
needs `Γ ⊢ ⟦a⟧ ∈ ⟦A⟧`, and the acceptance walk needs nothing there at all.

How mini obtains that premise is the whole story. `beta_evidence` →
`beta_premise` → **`self.infer_type(arg)`** (`kernel.rs:1736`): a full
inference of the argument, per β step taken under certification. `def_eq_ev`
opens with **`self.infer_type(e1)`** for the proof-irrelevance probe
(`kernel.rs:3080`). `infer_type` is uncached by design (`MINI-DESIGN.md`'s
opening premise, chosen for measurement cleanliness), and it reduces types
(`whnf_typing` → `whnf_conv`), whose β steps call `beta_premise`, which calls
`infer_type`, which… The recurrence is

```
cost(certify reduction of e)  ≥  Σ over β steps  cost(infer_type(argᵢ))
cost(infer_type(t))           ≥  Σ over its reductions  cost(certify them)
```

which compounds geometrically in the depth of "arguments that are themselves
nests" — Lean's `brecOn`/`below` output is precisely such a nest. The
measured signature fits everywhere it can be checked: certifying one ι
through a recursor ≈ 7,500 conversions (`kernel.rs:1675`) when the
per-declaration apparatus already reduced the *rule* to instantiation — the
7,500 is almost entirely the premise re-derivations; one `addN` re-enters
`proj_data::typing` 251 times at the same projection of the same subject
(`MINI-HANDOFF.md` §40); 108× on one small fixture, over half an hour on
`nat_char_equations`, 46 M conversions on the smallest nested-inductive model
there is. And the asymmetry of arming is exact: `beta_evidence` returns
before `beta_premise` when `tm` is `None` (`kernel.rs:1461`), so the
acceptance walk never enters the recurrence — 4.5 s against 10 minutes is not
"certification is 133× per step", it is "one path recurses and the other
does not".

So the owner's hypothesis is **right about the recurrence and wrong only
about the site**: not two parallel top-level walks, but `infer_type`
re-entered from inside the certified reduction, at every β premise and every
`def_eq` entry, uncached.

### (c) Lost sharing across scopes — the blocked rescue

Re-computation would be survivable if a cache caught it. Three attempts, and
the two failures are the finding (`MINI-HANDOFF.md` §40): `Rc::as_ptr` keys —
zero hits, `subst` allocates, 251 structurally identical types carry 251
pointers; `(decl, field, ⟦s⟧)` keys — no measurable change, because **every
binder entry mints fresh kernel variables**, so the same Lean subject under
two openings of one binder has two interpretations and no term-stated key can
ever collide; `⟦ty⟧` keyed with the Lean type checked structurally on the hit
— 1,936,075 → 1,311,117 conversions, kept (`wt_memo`), and blind by
construction to cross-opening duplicates. The invariant under all three: **a
memo key must denote the judgement, and a judgement stated at per-opening
variables denotes nothing beyond its opening.** What that implies for a
keyable cache is in §2. Verdict: (c) does not create the repeated asks — (b)
does — but it is what turns them from "cheap after the first" into the full
subtree walk every time.

### (d) No inversion principle in the target logic — permanent, and priced

The original framing. It is true and it will stay true: the embedding is
shallow, there is no induction over Lean syntax inside TG, so inversion,
preservation and substitution are not theorems and no per-instance shortcut
from "`e.1` certified" back to "`e` certified" exists. But (d)'s role in the
measured cost is indirect: it *forbids the reconstruction shortcut* the
ordinary kernel lives on, and mini answered that prohibition with
re-inference — which is (b). The direct price of (d), once evidence is
carried instead of re-derived, is a constant per use:

| implicit rule in the accepting walk | certified counterpart | cost per use, premises in hand |
| --- | --- | --- |
| inversion (subterms well-typed) | never discard: the typing rode in with the term | O(1) — a value move |
| preservation (reducts keep their type) | one Leibniz transport per step (`whnf_typing`, `retarget_set`) | O(1) kernel inferences |
| substitution (`b[a]` typed from `b`, `a`) | ∀-closed certificate; `ax_inst` + `mp` at the use | O(1) + term size |

The substitution row carries the answer to "a cache breaks under substitution
and on open terms": a certificate stored as `Γ, w∈A ⊢ φ(w)` is scope-relative
and unusable after substitution; discharged to `Γ ⊢ ∀w. (w∈A → φ(w))` —
`scope.rs`'s `Closed::discharge`, already written — substitution *becomes*
instantiation, sound because the interpretation is compositional in the scope
variable (bvar ↦ `w` by construction). **The closed form is the
substitution-stable form of evidence.** Nothing about (d) forces re-derivation;
it forces this discipline.

## 2. Flaw or intrinsic — the split, and the two fixes

| candidate | verdict | what fixes it, inside the certifying design |
| --- | --- | --- |
| (a) duplicated traversal | bounded; partly deliberate and measured to be right where kept | nothing to do now; seams are enumerated in the code |
| (b) re-derived premises | **design flaw** — the premise is a value the checker held | carry evidence through the reduction stack (fix 1) |
| (c) lost sharing | **design flaw with a named keyability requirement** | Sealed memo on α-canonical closed judgements (fix 2) |
| (d) no inversion | **intrinsic and permanent** | nothing; its price is the per-step constant in §3 |

**Fix 1 — *not* the reduction stack carrying typings; the dead gate at
`def_eq_ev`'s entry.** *(Corrected against §4's run. The proposal here was:
`whnf_conv`'s `stack_tms: Vec<Option<Term>>` holds `⟦a⟧` per pending argument
and "drops the membership theorem that was derived beside it", so widen the
slot to the `Typing` and `beta_premise` collapses into `beta_premise_of`.
Both halves of that are false. `infer_type`'s `App` arm does infer its
argument, but that is a **different traversal over a different expression**:
`whnf_conv` is handed a type or a def-eq endpoint, and its `App` arm recovers
`⟦a⟧` from `⟦f a⟧` by `split_app` — one lookup in the recorded applicative
structure, no typing produced and none available. Minting one at the push
would pay for arguments no β step ever consumes: **252 962 `App`-arm pushes
against 119 216 `Lam`-arm β steps**, one `beta_premise` per pop, so the
widening costs 2.1× what it saves. It was not built.)*

What the same paragraph got right is `def_eq_ev`'s entry, and there the
saving is real and was landed. `def_eq_ev` opens with `infer_type(e1)` whose
**only** consumer is the proof-irrelevance gate; nothing below the gate reads
it. That inference dynamically contains **53.0%** of all conversions on
`proj_reduced_carrier`, and proof irrelevance fires **25 times in the whole
run**. Where `e1` is a *type* — a `Π`'s domain against an argument's inferred
type, a binder domain against a binder domain, a declared type against an
inferred one — the gate is `None` by inspection of `is_prop_or_unit_ev` (the
type of a `Sort` is never `Sort 0`, and a `Sort` has no `Const` head for the
unit-like branch), so the whole inference is dead. `Checker::Lhs` is that
fact, handed in at the four sites that have it. Measured, `proj_reduced_carrier`
**4 369 255 → 3 344 124** conversions and 3 m 04 s → 2 m 44 s;
`077_RBTree.id_spec` **5 689 627 → 4 617 476** and 1 m 06 s → 0 m 56 s.
That is a bounded constant, not the exponent. The exponent is fix 2.

**Fix 2 — for re-encounters that survive threading: a memo that is actually
keyable.** Arguments materialised *by substitution* and subjects re-met at a
different scope are not covered by fix 1 — their evidence exists only in
scope-relative form and the opening that stated it is gone. The requirement
(c) imposes: key on the judgement **closed over its free variables** in
first-occurrence order — `Formula::forall` already performs de Bruijn closure
in kernel terms, so α-canonicalisation is an O(size) walk, and two openings
of the same binder yield byte-identical keys; store the **discharged**
theorem `⊢ ∀w⃗. (w⃗∈A⃗ → φ(w⃗))` — hypothesis-free, which is exactly the
`Sealed` funnel mini already enforces at its one store (invariant I4,
`scope.rs`) and the `is_unconditional` gate nanoda's caches already apply; a
hit re-instantiates with `ax_inst` + `mp` against the current scope's own
`assumed`, O(open-binder depth). This upgrades the settled cache policy
(`QUESTIONS.md`: cache only unconditional certificates; the end-of-definition
certificate must be closed) from *refuse conditional entries* to *close them
and share them*. It touches `MINI-DESIGN.md`'s "no caches" premise, which
§40 already concedes wants its own round — `wt_memo` is the concession half
made.

**One near-miss to rule out by name: deterministic binder variables.** Making
kernel variables deterministic-by-depth would make judgements syntactically
shareable — and is unsound here: `FreeVar` is branded and mintable only
through `Env::fresh_var` because aliasing a variable an inference rule
assumed fresh is "a demonstrated route to `⊢ ⊥`" (`kernel/src/term.rs:37–62`),
and ~15 scope stacks run concurrently (`scope.rs`, I2). Freshness stays;
canonicalisation lives in the *key*, which is a formula the memo owns, not a
theorem the kernel checks.

## 3. The constant, honestly

**Proof size is a non-issue; construction is the cost.** The kernel is LCF:
theorems are opaque values, no proof term is retained, and nanoda measured
+0.3% peak RSS for keeping a certificate beside every memoised result
(`MEASUREMENTS.md`, "Memoise a result, memoise why"). Memory is memo tables.

**The invariant after the fixes:** every operation of the accepting walk maps
to a bounded number of kernel inferences given carried premises. Itemised
against the existing splices:

* δ step: one stored `Sealed` equation, weakening free (`delta_evidence`) —
  a handful of inferences.
* β step: `beta_leg` (instantiate the graph equation, `mp` the carried
  membership) + `body_unfold` — order 5–20.
* ι through an interpreted recursor: the β chain down the stored nest, one
  leg per argument, premises carried — order arity × the β cost, i.e. tens
  to low hundreds, versus ~7,500 today; the gap between those numbers *is*
  the re-derivation being removed.
* binder open/close: `assume` at open, `implies_intr` + `gen_checked` at
  close — O(1) per binder.
* Sealed-memo store/hit: closure and re-instantiation — O(open depth).

**The honest expectation: 30–100× the uninstrumented checker,** in kernel
operations, and in wall clock to within a small factor since kernel
operations are cheap structural term builds. Why not 3×: the interpretation
is genuinely larger than the term — graph symbols, membership premises, β
typed where acceptance's is untyped, binder discipline — and those are (d)'s
intrinsic per-step taxes, not removable by any threading. Why not 300×: every
superlinearity so far measured in this repository has been attributed to a
named re-derivation or re-walk site — the 251×, the 7,500, the acceptance
seams, the memo misses — and none, so far, to an irreducible cost.
Calibration from the repo's own record: nanoda's partially-threaded backend
runs `init-prelude` at roughly two orders of magnitude over acceptance
(0.08–0.13 s `NullCertifier` against ~10–40 s certified, build-dependent)
*with its search machinery still in place*, and removing a single
re-derivation family (`store_declar_typing`) took 16.0 s → 11.87 s by itself
— i.e. the current ~100× already contains large known-removable components.

**Scaling, which is what 700× actually asks:** certificates seal at
declaration boundaries (`Sealed`, hypothesis-free — the end-of-definition
closure is settled policy), so cross-declaration cost is additive and the
corpus scales linearly once per-declaration cost is a bounded multiple of
acceptance. A constant 30–100× on a linear schedule, parallel per declaration,
is hours for a 700× corpus. What the corpus cannot survive is the recurrence:
46 M conversions for the *smallest* nested model, multiplied across a corpus
where nested inductives are routine, is unreachable at any constant. The
exponent is the whole question, and the exponent is (b).

**What would falsify the bound:** if the judgements asked repeatedly were
mostly *distinct* — genuinely new at every scope, nothing for fix 1 to carry
or fix 2 to share — the blowup would be inherent. Everything known argues
otherwise (251 known-identical entries at one site; `wt_memo` recovering a
third while blind to cross-opening duplicates), and §4 measures it directly.

## 4. The cheapest experiment

Two counters, no behaviour change, one debug run each of
`proj_reduced_carrier` (the ten-minute fixture) and — under the standing 4 GB
`ulimit -v` — `nested_model.ndjson`:

1. **Origin partition.** Tag every `infer_type` entry with its originating
   site — `beta_premise`, `def_eq_ev` entry, `whnf_typing`, `App`-arm
   recursion, top-level — and attribute conversions to the tag in force.
   *This tests the owner's hypothesis directly.* Prediction: ≥ 90% of the
   4,369,255 conversions sit under `beta_premise` + `def_eq_ev` origins. If
   instead the mass is at top level, the recurrence diagnosis is wrong and
   §2's fixes attack the wrong thing.
2. **Duplication census.** At the same entries, log the hash of the
   α-canonicalised judgement (close the would-be conclusion over its free
   variables in first-occurrence order — the closure exists, §2). Report
   distinct/total. Decision rule, fixed before the run: distinct/total ≲ 5%
   — duplication; fixes 1+2 recover the blowup; proceed. Distinct/total high
   (> 30%) — the work is genuinely new per scope, no sharing exists to
   recover, and bounded overhead for eager per-node certification is not
   achievable on this corpus shape; that answer changes the design
   conversation, and it is better bought now for two counters than after
   another month.

Prediction, stated so it can be wrong: (1) ≥ 90% under the two re-inference
origins, (2) well under 5% distinct at `proj_data::typing` and under 10%
overall. The confirming second step — one construction, not a rewrite — is to
re-run failed memo #2 with the α-canonical key and Sealed value on the same
fixture and expect conversions within a small multiple of the 40,271
acceptance baseline.

### Run, 2026-08-07, on `proj_reduced_carrier`

Both counters, plus three the run made necessary. Every figure below is from
one instrumented release binary over the ten-minute fixture; the totals agree
with the uninstrumented run row for row (4 369 270 conversions against the
verdict line's 4 369 255 + 15 gapped).

**(1) Origin partition — prediction ≥ 90%, measured 84.0%. A near miss that
does not change the diagnosis.** Of 4 369 270 conversions, **3 669 859 =
84.0%** occur inside an `infer_type` entered from `beta_premise`,
`def_eq_ev`'s entry, or `proof_irrel_ev` — with the two named origins
containing 51.7% and 53.0% respectively (they nest, hence the union). Of
7 165 213 `infer_type` entries, **89.2%** are under one. The mass is *not* at
top level: top level is **1.3%** of conversions. The recurrence is confirmed.

**(2) Duplication census — prediction < 5% distinct at `proj_data::typing`
and < 10% overall; measured 6.79% and 0.66%.** The site-level prediction
misses (840 calls, 57 distinct); the overall one is beaten by a factor of
fifteen. **7 165 213 `infer_type` entries are 47 345 distinct α-canonical
judgements — 151× duplication.** Decision rule: ≲ 5% is "duplication, proceed";
> 30% is "no sharing exists". At 0.66% overall this is decisively the first,
and eager per-node certification is *not* in the band where it fails to scale.

**(3) Where the sharing lives — the counter that redirected fix 1.** Re-key
the same census on the **live kernel scope variables** instead of the Lean
telescope, i.e. ask how much duplication is visible *without* discharging and
re-instantiating: distinct/total goes **0.66% → 56.15%**. At `beta_premise`
the same split is **1.59% → 52.08%** on 124 534 calls. So essentially all of
the 151× is **cross-opening**, and everything a single `whnf_conv` invocation
or a single `Γ` can see is bounded by ~1.9×. §2's "the value the checker held
moments earlier" is held across an opening, not across a stack slot.

**(4) Stack traffic — why the widening is a regression.** 252 962 `App`-arm
pushes, 119 216 `Lam`-arm β steps, 124 534 `beta_premise` calls (the surplus
is `nest_arg_mems`/`nest_iota`, which already have the single-inference
`nest_arg_typings` form). One `beta_premise` per pop, and 2.1 pushes per pop:
a `Typing` minted at the push is paid twice for every one it saves.

**(5) The recoverable share, and it is fix 2's.** Conversions occurring
inside a *repeat* of an already-seen α-canonical `infer_type` judgement —
counted once, at the outermost repeat, which is what a memo hit would elide:
**4 272 438 / 4 369 270 = 97.8%**. That is the dominant term, it is the
number fix 2 is aimed at, and no amount of threading inside one opening
reaches it.

---

## Appendix: sources for every number and code claim

* 4.5 s → 10 min; 40,271 → 4,369,255; 251 entries at one site; the three
  memo attempts and their keys; "every binder entry mints fresh kernel
  variables"; `nat_char_equations` over half an hour and `#[ignore]`d —
  `MINI-HANDOFF.md` §40.
* `beta_premise` runs `infer_type(arg)` — `checker/src/mini/kernel.rs`, `beta_premise`;
  the compounding stated in code — `kernel.rs`, `beta_premise_of`; acceptance bails
  before the premise — `kernel.rs:1461`; `def_eq_ev` opens with
  `infer_type(e1)` — `kernel.rs:3080`; one fused traversal, no separate
  interp walk — `kernel.rs:187,493`; `whnf` = `whnf_conv` with `None` —
  `kernel.rs:734`; ~7,500 conversions per certified ι and `wt_memo`'s
  1,936,075 → 1,311,117 — `kernel.rs:1671–1709`.
* Stuck projections deliberately uncertified, 0.6 s → 2 min the other way —
  `kernel.rs:1265–1272`; acceptance-only major reduction at the
  `StuckRecursor` arm, and 46 M conversions for the smallest nested model —
  `MEASUREMENTS.md`, nested-inductives entries, 2026-08-07.
* +0.3% RSS for certificates beside memos; `NullCertifier` 0.08 s;
  `store_declar_typing` 16.0 s → 11.87 s — `MEASUREMENTS.md`.
* Sealed funnel and invariants I1–I4; `Closed::discharge`; ~15 concurrent
  scope stacks — `checker/src/mini/scope.rs` module header.
* `FreeVar` branding; aliasing as a route to `⊢ ⊥` —
  `kernel/src/term.rs:37–62`.
* Cache policy: unconditional-only entries; the end-of-definition certificate
  must be closed — `QUESTIONS.md`.
* Corpus state: 89 accepted, `constEv 218/218` — `MINI-HANDOFF.md`.
