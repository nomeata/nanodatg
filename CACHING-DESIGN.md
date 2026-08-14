# Caching in mini — what to build, in what order, and what each step risks

*2026-08-08. A design recommendation over `PROFILE.md`'s measurements, written
to be second-guessed the same way: verdict first, every claim sourced, and §7
names what stays unfixed and unmeasured. The measurements taken for this study
are in §6 — the narrowed-gate variant on the `DTree` tower, the full tutorial
suite under it at the certified level (which PROFILE.md §9 names as not
measured), `checker/tests/mini_nested.rs`, and the attribution runs its one failure
required — using `scripts/profile-probe.diff` plus a ten-line extension
(`MINI_FRAME_ACC`) in a scratch worktree.*

**Status: step 1 is landed; step 2 is landed. Steps 3 and 4 are not.** The
landing re-took every figure that describes the code rather than the study, on
`origin/master` after the arena port (`#120`), with `perf stat -e
instructions` per `47b262b`; where a number below is superseded it is
corrected in place and marked. The two the reader wants first: `mini/tests/
nested.rs` **17 905 884 629 054 → 8 408 759 079 586 instructions (2.13×)**, and
the 91 good tutorial exports **453.88 G → 431.28 G (1.05×)** — the corpus
being the axis this was never expected to move much. The corpus ratchet held
to the counter: `accept 89 / decline 2 / reject 0`, `pairs 218`,
`constEv 218`, `typeEv 218`, `unsealed 0`, `gapped 0`, `proved 829 661`,
`sealed 827 084`, `moved 3 454`, `movedSealed 908`. Step 1's cache-off/on A/B
is stronger than a counter comparison and is recorded in §6.1, which is where
every figure in this paragraph comes from.

## Verdict

**Narrow the `Gap` gate to the certified path — do not delete it, and do not
build a second cache beside it.** The gate is one condition in
`Checker::frame_put` (`checker/src/mini/kernel.rs`): `if t.ev.thm().is_none() {
return }`. The recommendation is `if self.th.is_some() &&
t.ev.thm().is_none() { return }`: on the acceptance path (`th: None`), where
every entry's evidence is a `Gap` by construction and the gate disables the
memo completely, `Gap`-carrying entries are cached; on the certified path,
where the gate has a real job (§1) and removing it was measured to buy at
most 4% (PROFILE §5: `nested_model` 97.0 → 93.46 s under the *wholesale*
deletion, fast key included), it stays. Landed together with the non-allocating key
(PROFILE's experiment G), this is the measured 12.7× on the towers — re-taken
on current master for this study, 7.10 s (§6) — and the certified path is
**byte-identical by construction** rather than by test: the narrowed
condition cannot change any run in which `th` is `Some`. (PROFILE's second
headline, `nested.rs` 309.5 → 124.2 s, is **stale**: the tree moved under the
study — §3.)

*(As landed, the non-allocating key is not experiment G's mixer. `#120` made
an `E` a `u32` into `checker`'s hash-consed arena, where pointer identity is
structural identity, so the exact key is cheaper than any hash of the tree:
`Frame::map` became `HashMap<E, Typing>` and `hash_expr` was deleted rather
than rewritten. §6.1 has the landing's figures, and they are on `nested.rs`
and the corpus rather than on the `tower` probe, which is not on master.)*

The plan, ranked. Each step's yield is measured unless marked as an estimate.

| # | change | buys | risks, and the detector for each |
| --- | --- | --- | --- |
| 1 | **LANDED.** narrow the gate to `th.is_some()`; and the key — the "~60-line structural mixer" this row asked for was overtaken by `#120` and became a *deletion*: an `E` is `checker`'s `ExprPtr`, pointer identity is structural identity, so `Frame::map` is `HashMap<E, Typing>` and `hash_expr` is gone | as landed, `perf stat -e instructions`: `nested.rs` **17.906 T → 8.409 T (2.13×)**, the 91 good tutorial exports **453.88 G → 431.28 G (1.05×)**, frame-cache hit rate over that corpus **3.38% → 18.15%** and over `nested_model --nested` **10.2% → 33.2%**. Attributed: the gate is 2.04× / 1.046× of it, the pointer key the remaining 1.043× / 1.007×. The tower figures in this row (12.7×, 7.10 s) were taken on the `tower` probe, which is not on master, and are left as the study's own | certified path: none, by construction. Acceptance path: determinism argument in §2; detectors are the fidelity gate (91 accept / 42 reject, MINI-DESIGN §11.2) and the armed ratchet `tutorial_first_blocker` — all green, and §6.1's A/B is byte-exact |
| 2 | **LANDED.** take `opt-level = 3` for the profiles CI uses, **when there is memory for it** | as landed, at step 1's configuration: `nested.rs` **8.409 T → 7.783 T (−7.4%)**, the corpus **431.28 G → 404.27 G (−6.3%)**; step 1 and step 2 together are `nested.rs` **2.30×** and the corpus **1.12×**. Build re-measured on the landing tree: `cargo build --workspace --exclude nanoda_lib --all-targets` at `CARGO_BUILD_JOBS=2`, **exit 0, 3 m 19, 1 253 564 kB peak `rustc` RSS** — PROFILE's 1.25 GB to three digits | the condition this row made the step wait on is **satisfied and was checked, not assumed**: `9902ef1`'s SIGKILL was headroom (under 1 GiB free against a 1.25 GB peak) because 48.25 GiB of tmpfs was pinned in `user-1001.slice`. At the landing that tmpfs held **376 MB**, and the slice was at 25.8 GB of a 53.87 GB limit — 28 GB of headroom against a 1.25 GB peak. It is a *condition*, not a settled fact: a seat that finds the tmpfs full again will hit the same kill, and the `Cargo.toml` comment now says so. PROFILE §9's `--release` row is still open |
| 3 | the certified axis: build `CERTIFYING-OVERHEAD.md` §2's **fix 2** — the α-canonical `Sealed` memo — as designed | *estimate, not a measurement*: bounded above by the measured 97.8% of certified conversions that occur inside a repeat of an already-seen α-canonical judgement (C-O §4(5)); this is the only designed lever on the 97 s / 96%-certification fixture that step 1 does not touch (1.04×) | key cost is O(size) per entry and must be amortized (a whnf-memo at O(size) keys was a measured 0.63× *regression*, PROFILE §5 B); the memo must store **certificates only** — on this axis the gate's policy is *correct* (§5) |
| 4 | a cross-opening acceptance memo (telescope-chain key), **only if** generated towers must scale past the current sizes | *estimate*: the post-memo residue is n^1.98 and ≥ 2 100× duplicated (PROFILE §6, §9); a key that survives binder re-entry removes the remaining exponent's constant, plausibly to near-linear — unmeasured | the sound key must cover the reachable telescope (§7); the cheap version needs cached per-node hashes, which is the first real step toward `checker/`'s representation — take the enabler, not the representation (§4) |

Two non-recommendations, argued in §4 and §5: do **not** port `checker/`'s
five-cache design into mini as a package, and do **not** treat the certified
axis as "the same fix again" — its cache is structurally different (closure
and re-instantiation, not a frame), and it is already designed.

## 1. Why the gate is there — and where its argument actually applies

The brief asked that this be found out rather than assumed. Found:

* **The comment at the gate** (`frame_put`): *"Only a certificate is kept. A
  `Gap` is cheap to re-reach and caching one would keep it out of `blocker`'s
  trail on every call but the first — `wt_memo`'s policy, and the instrument
  it had to repair."* The gate is stated as an *instrument-protection* policy,
  not a soundness condition — `Frame`'s own soundness comment (three failure
  modes, all about the telescope and the scope stack) never mentions evidence.
* **The instrument is worth protecting.** `blocker`'s trail has been wrong
  twice — `TRAIL_CAP` at 64 evicting the origin, and `Err(Gap)` routes never
  filing — and each defect sent multiple seats to the wrong file
  (MINI-HANDOFF §40, blocker.rs's own cap note). A third way to thin the
  trail deserves suspicion, not a shrug.
* **But the trail only exists when armed.** `blocker::record` is a no-op
  unless `blocker::arm(true)` ran (`blocker.rs`, `filing()`); arming happens
  on `--block` runs only (`run.rs:208`) and in one ledger test. An ordinary
  run has no trail for the gate to protect — the gate pays its full cost
  (PROFILE §3: computing the key for the never-storing memo is 34% of the
  acceptance run) on runs where its stated purpose cannot occur.
* **And on the acceptance path the trail was never the issue.** Arming used to
  happen after the whole-file acceptance verdict; since the pipeline became one
  per-declaration loop (`checker/src/mini/decl_pass.rs`) it happens before the loop, so
  the file's own zone A now runs *inside* the armed window along with the zone A
  work that always did — the mutual expansion's `kernel::add`
  (`mutual_aux.rs`). That does not change the argument, and the reason is the
  next clause rather than the position: zone A mints gaps that are cleared at
  the next `enter_pair` before any pair report reads them, and blocking
  aborts at *pair* obligations (`ledger.rs:620`), which zone A mints are not. The empirical
  check is `tutorial_first_blocker`, the armed ratchet that pins *which*
  `(declaration, σ)` and *which* `Gap` stops the corpus first — green under
  the change (§6).

Where the gate's argument is real is the **certified** path, and there it is
stronger than its own comment says. On that path the `Interp` grows mid-run:
`zoneb::ensure` builds carriers on demand and the splice performs lazy fills
(MEASUREMENTS.md, "Two lazy fills per model"), so an inference that gaps at
`no-interp(T)` early can succeed later in the same frame's lifetime once `T`'s
interpretation lands. A cached `Gap` would freeze that — the memo would keep
reporting a reason that has stopped being true, which is exactly the
"value keyed on a name instead of a cause" defect class §0.4 exists to
prevent, now with a cache as the vehicle. A cached `Proved` cannot go stale in
either direction (a `Thm`, once derived, stays derived; the store only grows).
The gate's asymmetry — keep proofs, refuse gaps — is therefore *correct* on
the certified path, for a reason deeper than trail hygiene. On the acceptance
path the staleness route does not exist: there is no `Interp` at all
(`Checker::new` sets `th: None`), nothing grows, and the `Gap` a cached entry
carries (`SymbolicLevel` and kin) is the one recomputation would mint again.

So the verdict on the gate is **narrow** — and the narrowing is not a
compromise between "delete" and "keep" but the statement of where each was
right: delete it where its purpose cannot occur and its cost is total; keep it
where its purpose is real and its cost is ≤ 4%. A second cache ("cache `Gap`s
in a parallel structure") buys nothing over this: on the acceptance path the
whole `Typing` is deterministic, so the existing frame can hold it, and on the
certified path a `Gap` should not be cached at all.

## 2. The soundness argument for step 1

At the level asked for — why a cached entry cannot be reused in a context
where it is wrong.

**The context cannot differ.** `Frame`'s existing argument
(`checker/src/mini/kernel.rs`, `Frame` doc) is unchanged and carries the whole load:
the memo is per telescope slot, pushed and popped at every one of the five
sites that touch `lenv`, so a hit is only reachable while the telescope is the
very one the entry was computed under; a re-entered binder gets an empty frame
(`Frame::default()` on push); a kernel scope opened behind `lenv`'s back
empties the frame via `scopes_len` — and on the acceptance path `scopes_len`
is constantly 0, so that guard is vacuous rather than load-bearing. `mini::
Expr` has only `BVar(u32)` — no free-variable case — so at a fixed telescope
the expression alone denotes the judgement (MINI-DESIGN §0.3: the key is
sound "exactly when it determines the judgement *including its context*", and
the frame gets that by construction). The key is a hash *hint*; every hit is
confirmed by structural `==` before the `Typing` is returned.

**The value cannot differ.** What step 1 adds is entries whose `ev` is a
`Gap`, on the path where `th` is `None`. There, `infer_type_inner` is a pure
function of `(e, lenv, env)`: `env` is frozen for the duration of one
`kernel::add`, `lenv` is fixed within a frame by the argument above, there is
no `Interp` to consult or to grow, `tm` is `None`, and no kernel object of any
kind is constructed (PROFILE's verdict: no `Interp`, no `Term`, no `Thm` on
this path). Its only side effects are census counters and — armed only —
blocker mints, neither of which feeds back into any result. Errors are not
cached (`frame_put` is reached only on `Ok`), so rejection behaviour cannot
change. A hit therefore returns exactly the `Typing` recomputation would
return, including the same `Gap` for the same cause — the brief's
misattribution worry (a stale reason reused across contexts) needs either a
context change or a state change, and this path has neither.

**Nothing branded is stored.** The entries carry `tm: None` and no `Thm`, so
no kernel-scope-relative object can outlive its opening via the cache — the
hazard `Frame`'s third bullet and the `Sealed` funnel exist for does not
arise. The trusted base is untouched: `kernel/` is not in the changed set, and
no unproved conclusion can be reported proved, because acceptance-path entries
never contain a `Thm` at all and the certified path is unchanged.

**Fidelity.** The port's exactness depends on which clause fires where, and
MINI-DESIGN §13 risk 2's strictness deltas are cases where *whether a
conversion is asked at all* depends on the path taken — the class of thing a
cache that changed evaluation order could disturb. A memo hit does not make a
different clause fire and does not ask a new conversion — it skips clause
dispatch and returns the result the clauses already produced, in the same
context, under a determinism argument rather than an evaluation-order one. What *does* change is multiplicity:
conversions and inferences that used to be re-performed are performed once,
so counter-based instruments read distinct work rather than
work-with-repeats — the same shift `wt_memo` already caused and §40 recorded
("re-pins three counters"). The detectors are the ones the design already
maintains: the verdict fixture (91/91 accepted, 42/42 rejected), the declines
byte-identical, `constEv 218/218`, `gapped 0`, `unsealed 0`, and the armed
first-blocker pin. All of them ran green under the exact recommended
configuration (§6).

## 3. What was refuted in the brief, stated plainly

Per the standing instruction, the two places this study's own framing was
wrong or needed narrowing:

* **"Delete the `Gap` gate, get 10×" is right about the 10× and wrong about
  the delete.** All of the measured speedup comes from the `th: None` path —
  the wholesale deletion's *additional* effect, `Gap`-caching on the certified
  path, is worth at most the 3.7% seen on `nested_model` (PROFILE §5, and that
  figure includes the fast key) while opening the one real staleness route
  this design has (§1). The narrowing keeps the whole win and provably none of
  the risk.
* **PROFILE's `nested.rs` rows are stale on current master — the tree moved
  under this study while it ran.** The brief's ι-seeding figure ("13×,
  3.9 M → 51.8 M conversions, peak over 7.5 GB") is real and post-dates
  PROFILE's measurement commit: `87eb672` (2026-08-08, after `9a8702f`)
  removed the `refl_proved` guard and seeds **every** ι rule — the whole
  specification certifies, `constEv 134/134`, `gapped 0` — at
  `nested_iota --nested` going 3 878 982 → 51 830 194 conversions, 2 m 27 →
  25 m 52, peak **over 7.5 GB** (the seeding-site table,
  `checker/src/mini/nested_splice.rs:374–383`; the `#[ignore]` note,
  `checker/tests/mini_nested.rs:640`). Two consequences. PROFILE §5's
  "`nested.rs` 309.50 → 124.21 s, 15 passed both ways" no longer describes
  the file: the heavy leg now sits inside a *non-ignored* test
  (`a_nested_declaration_declines_…` runs `nested_iota --nested`), so the
  suite cannot complete under the 4 GB seat cap **at baseline, with no
  caching flags at all** — measured in §6. And the certified axis now owns a
  concrete, current number that step 1 does not touch and step 3 is aimed at
  (§5).

## 4. `checker/`'s five caches — adopt the policy, not the package

`checker/` proves the design's central claim: all five of nanoda's caches,
certificates in the values (`checker/src/util.rs:898–932`, read in this tree;
`checker/src/tc.rs:2388`; the upstream five are PROFILE §7's
`util.rs:819–825`), on a certifying checker. The question was whether mini should adopt it. **No — not
as a package.** Row by row:

| `checker/` cache | mini counterpart | verdict |
| --- | --- | --- |
| `infer_cache_check` / `_no_check`, `ExprPtr`-keyed, conditional typings admitted with an argument (`util.rs:899–911`: a typing's hypotheses are about locals occurring in the keyed expression itself) | `Checker::frames` | **already adopted, by the other half of the same insight** (MINI-DESIGN §0.3): checker/ makes the key denote the judgement by putting the locals *in* the term; mini makes it denote by discarding the frame when the context changes. Step 1 completes this row; nothing further to port |
| `whnf_cache` / `whnf_no_unfolding_cache`, values carry the reduct's steps (`Reduct`, `util.rs:914–922`) | none (`wt_memo` is `Term`-keyed, certified path only) | **refuted at mini's current representation**: PROFILE §5 B — 54% hit rate, 0.63× (a *regression*), because the O(size) key costs more than the reduction it saves. Viable only after step 4's O(1) keys, and only if the towers still need it then |
| `eq_cache`, a proof-producing union-find (`util.rs:923–927`) | none | acceptance towers do not need one: their def-eq mass rides inside `infer_type`'s recursion (§6's probe: 5.5 M `def_eq_struct` visits against 83 decision-only `is_def_eq` calls on the whole post-memo `DTree` tower), and a frame hit elides the whole subtree, comparison included. On the certified axis its counterpart is step 3's `Sealed` memo, per MINI-DESIGN §0.3's settled disjunction — key on `Γ` or store `Sealed`-only, and the second is measured cheaper (95.4% of differing-endpoint conversions are hypothesis-free) |
| `failure_cache` (congruence failures during lazy delta) | none | tied to `lazy_delta_step`, which mini deliberately lacks — whnf's `Const` arm does full eager delta by fidelity to mini-lean (PROFILE §7). Adopting lazy delta is an algorithmic divergence from the port with its own fidelity argument to make; nothing measured fingers delta as a remaining cost (§6's probe: 1.17 M delta unfolds against 27.2 M whnf calls, post-memo). Leave it |
| the enabling representation: hash-consed DAG, free variables in the term, O(1) `ExprPtr` keys | none — `Rc` per node, pure de Bruijn, ambient telescope, all deliberate (MINI-DESIGN §0; `expr.rs` header) | **do not adopt wholesale.** Measured alone it is a 14% regression (PROFILE §4 H); its value is as an enabler of O(1) keys. Wholesale adoption rewrites `expr.rs`, every `shift`/`substs` site, the `Frame` argument and the scope discipline's boundary — i.e. it turns mini into the thing that already exists in this tree under the name `checker/`, and re-imports exactly the confounders MINI-DESIGN §0 built mini to exclude. If step 4 is ever taken, the piece to take is the cached per-node hash (an O(1) key without free variables in the term), not the representation |

What mini *should* keep from checker/ is its cache **policy**, and it mostly
already has it: every cache value carries its evidence (`frames` stores the
whole `Typing`; `wt_memo` stores the `Thm`; the memory note "memoize
certificates, never re-derive" is this rule); equality-class entries are
unconditional-only (QUESTIONS.md's settled decision, `certify::
is_unconditional`, the same funnel as `Sealed`); and conditional entries are
admitted only where an argument says the key carries the condition — checker/
argues it via in-term locals, mini via frame scoping. The one policy row where
mini went *beyond* checker/ — refusing `Gap`s — is right on the axis that has
certificates and wrong on the axis that cannot have them, which is §1.

## 5. The certified axis — what step 1 does not fix, and what does

The bigger number is certified: `nested_model` is 97.0 s at 96% certification
share, and step 1 moves it 1.04× (PROFILE §5). Saying so plainly: **steps 1–2
are an acceptance-axis fix; they leave the certified axis where it is.**

The diagnosis there is already measured and the fix already designed, and
this study's contribution is only to place it in the sequence and mark where
the gate reasoning does and does not transfer:

* The duplication is real and larger than the acceptance axis's per-frame
  share: 7 165 213 `infer_type` entries are 47 345 distinct α-canonical
  judgements — 151×; 97.8% of all conversions happen inside a repeat
  (CERTIFYING-OVERHEAD §4). `dprod_app` fires ~130× per Lean-level
  application site, and APP-SPINES.md's own verdict stands: per-site
  optimisation "polishes a constant sitting inside that unfixed factor".
* **A frame cannot reach it.** The repeats are cross-opening — re-keying the
  census on live kernel scope variables collapses the visible duplication
  from 99.34% to 43.85% (C-O §4(3)) — and the frame dies at every `lenv`
  change *by its own soundness argument*. Three term-keyed memos were tried
  and failed for exactly this reason (§40: fresh kernel variables per
  opening; no term-stated key can collide across openings).
* The designed fix is **fix 2**: key on the judgement α-canonically *closed*
  over its free variables, store the **discharged** `Sealed` theorem
  (`⊢ ∀w⃗. w⃗∈A⃗ → φ(w⃗)`), re-instantiate at a hit with `ax_inst` + `mp`
  against the current scope's own assumptions — O(open depth) per hit. The
  closed form is the substitution-stable form; this upgrades the settled
  cache policy from *refuse conditional entries* to *close and share them*
  (C-O §2), and `Closed::discharge` and the `Sealed` funnel already exist
  (`scope.rs`, I1–I4).
* **The gate's policy transfers as a *positive* rule here.** Store certified
  entries only. On this axis a `Gap` genuinely can become provable later
  (lazy fills, §1), the ledger's reasons are load-bearing, and the trail is
  live on armed runs — every reason the gate exists applies. The memo that
  fixes the certified axis is certificate-only *by design*, not as a
  performance compromise.
* Two costs must be respected, both measured: the key is O(size) per entry
  (PROFILE B's lesson — an O(size) key can make a 54%-hit cache net
  negative), so the closure hash should be computed once per stored judgement
  and amortized, not per lookup on the hot path; and the win is bounded by
  the 97.8% repeat share, on top of an intrinsic certified constant honestly
  estimated at 30–100× acceptance (C-O §3) — fix 2 makes the certified axis
  *linear*, not free.
* **The ι seeding is the certified axis's sharpest current number, and it is
  step 3's target.** Since `87eb672` (post-PROFILE, §3) every ι rule is
  seeded and every one certifies — the `refl_proved` guard is gone, its
  residual having turned out to be `Checker::proof_point_leg` (`whnf` on a
  proof-valued spine, closed at `e72be32`), not `#90(b)`. The price is
  measured at the seeding site: `nested_iota` 3 878 982 → **51 830 194**
  conversions, 25 m 52, peak over 7.5 GB — 13×, "and it is the whole of
  nested inductives". That 13× is precisely the re-derivation recurrence fix
  2 exists for: 97.8% of certified conversions sit inside a repeat of an
  already-seen α-canonical judgement (C-O §4(5), measured on
  `proj_reduced_carrier`; the share on `nested_iota` is an extrapolation and
  is named as one). What hangs on it is concrete: the nested arc's
  finish-line test is `#[ignore]`d for exactly this cost
  (`nested.rs:640`), and §6 shows the non-ignored suite can no longer run
  under the 4 GB seat cap at all — fix 2 is what would bring both back.

## 6. Measurements taken for this study

All in a scratch worktree at `b512348` (`origin/master` — which, unlike
PROFILE's `9a8702f`, includes `87eb672` and `e72be32`, the two `mini/` commits
of §3), `test` profile (`opt-level = 1`, debug assertions on),
`scripts/profile-probe.diff` applied (`--3way`; it no longer applies clean)
plus a ten-line `MINI_FRAME_ACC` variant: `frame_put` keeps `Gap` entries
**only when `self.th.is_none()`** — the exact narrowing step 1 recommends, as
opposed to `MINI_FRAME_ALL`'s wholesale deletion. The machine was shared with
another seat's runs throughout; wall clocks are order-of-magnitude.

* **The narrowed gate reproduces experiment A exactly on the acceptance
  tower.** `examples/tower nested_deep`, `MINI_FRAME_ACC=1 MINI_FASTHASH=1`:
  **7.10 s** (PROFILE's A + G: 7.25 s; baseline 91.86 s), with
  `INFER_ENTRIES = 20 266 178` — **the same count to the digit** as PROFILE §5's
  experiment A, as it must be: the tower runs entirely at `th: None`, where
  the two variants coincide.
* **The tutorial suite at the certified level is green under the narrowed
  gate.** `cargo test -p mini --test tutorial`, `MINI_FRAME_ACC=1
  MINI_FASTHASH=1`: **12 passed, 0 failed, 33.76 s** — the acceptance-fidelity
  pins on the good and bad fixtures (`tutorial_good_all_accepted`, the
  accept 89 / decline 2 / reject 0 population; `tutorial_bad_*`), the
  certification ratchets `tutorial_evidence_ledger`,
  `tutorial_the_whole_corpus_certifies` and `tutorial_conversion_split`
  (pinned conversion counters, unchanged exactly as the construction predicts
  — the certified path is untouched), and the armed ordering pin
  `tutorial_first_blocker`. This is the measurement PROFILE §9 left open
  ("the tutorial corpus at the certified level"), taken at the exact
  configuration recommended.
* **`checker/tests/mini_nested.rs` under the narrowed gate: 13 passed, 1 failed,
  1 ignored, 457.9 s** under a 4 GB-capped harness — **and the failure is §3's
  tree movement meeting this study's own cap, not the gate.** The failing
  test, `a_nested_declaration_declines_and_only_its_own_gate_opens_it`, has
  `nested_iota --nested` as its third leg — since `87eb672` a > 7.5 GB,
  ~26-minute certified run. Under the cap the spawned `mini` is killed, its
  exit code is `None` and its stdout has no verdict line, so the accept
  assertion fails — the mode `nested.rs:640`'s own note predicts for a capped
  seat ("a run capped there is killed at about nine minutes"). Attribution
  was then measured rather than argued: the leg run alone under a 2 GB cap
  aborts on allocation failure **identically at baseline and under
  `MINI_FRAME_ACC=1 MINI_FASTHASH=1`** — same SIGABRT, same failing
  allocation to the byte (478 150 672), at ~4½ minutes each. The kill is the
  certified pass's RSS, which the narrowed gate cannot touch by construction.
  Every other test in the file, ι-arm and rule-firing tests included, passes
  under the flags. Consequence for `#110`, stated because someone will hit
  it: on current master this file needs > 7.5 GB *at baseline* — a capped
  seat cannot run it in any configuration, and that is step 3's number, not
  step 1's.

Reproduction:

```sh
git worktree add --detach WT origin/master
cd WT && ln -s ../../vendor vendor
git apply --3way scripts/profile-probe.diff   # -3way: master moved since 9a8702f
# add MINI_FRAME_ACC (see this document's §6 preamble; ~10 lines in
# mini/src/probe.rs and the frame_put condition in checker/src/mini/kernel.rs)
CARGO_BUILD_JOBS=2 CARGO_INCREMENTAL=0 cargo build -p mini --tests --examples --profile test
( ulimit -v 4194304; MINI_FRAME_ACC=1 MINI_FASTHASH=1 ./target/debug/examples/tower nested_deep )
( ulimit -v 4194304; MINI_FRAME_ACC=1 MINI_FASTHASH=1 cargo test -p mini --test tutorial )
# nested.rs: since 87eb672 the a_nested_declaration test's `nested_iota
# --nested` leg needs > 7.5 GB and ~26 min at baseline; under a 4 GB cap it
# fails as described in §6, with or without the flags.
( ulimit -v 4194304; MINI_FRAME_ACC=1 MINI_FASTHASH=1 cargo test -p mini --test nested )
```

## 6.1 The landing's own measurements

*Taken at the landing, not in a scratch worktree: `origin/master` at `8e2e45b`
plus the change, `test` profile, `perf stat -e instructions` per `47b262b`
("counters decide, clocks comment"). Three binaries were built and measured
against each other so the two halves of step 1 could be attributed
separately.*

| configuration | `checker/tests/mini_nested.rs` | 91 good tutorial exports |
| --- | ---: | ---: |
| baseline (`8e2e45b`) | 17 905 884 629 054 | 453 882 252 046 |
| gate narrowed only | 8 768 536 899 614 (2.042×) | 434 129 398 137 (1.045×) |
| **+ the pointer key (step 1)** | **8 408 759 079 586 (2.129×)** | **431 279 848 180 (1.052×)** |
| **+ `opt-level = 3` (step 2)** | **7 782 754 492 560 (2.301×)** | **404 270 824 242 (1.123×)** |

`nested.rs` is `20 passed; 0 failed; 2 ignored` in all four. The corpus column
is 91 spawns of `mini --no-modelgen --verbose`, one per export.

* **The frame cache stops being dead.** Over the corpus, `framecache` goes
  from `hits=225 327 misses=6 443 795` (**3.38%** of 6 669 122 lookups) to
  `hits=421 716 misses=1 901 703` (**18.15%** of 2 323 419) — the *lookup*
  count falls by 65% because a hit elides a whole subtree's worth of them. On
  `nested_model --nested`, the fixture that is 96% certification, **10.2% →
  33.2%** over 20 047 626 → 8 026 077 lookups, and the verdict line is the
  same `accept 25 declarations`.
* **The cache-off/on A/B is byte-exact, not counter-exact.** The guardrail
  asked for deterministic counters; the stronger check was available and is
  what was run. All 820 lines of `--verbose` output over the 91 exports —
  every `facts`, `clauses`, `ledger`, `evidence`, `convs` and `untranslated`
  row, `constEv 218/218`, `typeEv 218`, `unsealed 0`, `gapped 0`,
  `proved 829 661`, `sealed 827 084`, `moved 3 454`, `movedSealed 908`, and
  the `accept 89 / decline 2 / reject 0` population — are **identical between
  the cache-off and cache-on runs, and the only line that differs anywhere is
  the `framecache` row itself**. The same diff is identical again across
  `opt-level = 3`. Two baseline runs were diffed against each other first, to
  establish that the output is deterministic at all.
* **`ci/check.sh` is green** at `NANODATG_REQUIRE_CORPUS=1`, all steps, on the
  landing tree.
* **§6's `nested.rs` bullet is superseded by the arena port, not by this
  change.** That bullet reports the file failing under a 4 GB cap and needing
  "> 7.5 GB *at baseline*", so that "a capped seat cannot run it in any
  configuration". Since `#120` that is no longer true: the whole file runs
  uncapped in one process tree with the heaviest spawned `mini` peaking at
  about **1.8 GB RSS**, 20 passed / 2 ignored, in every one of the four
  configurations above. The `#[ignore]` on `nested.rs:640` and step 3's
  argument are untouched — this is a memory correction, not a cost one.

## 7. What this does not fix, and what stays unmeasured

* **The n^2.0 residue on the acceptance towers.** After step 1 the exponent is
  1.98 ± 0.10 (PROFILE §6); the duplication that remains is cross-opening,
  bounded below at ≥ 2 100× and unpartitioned (PROFILE §9). Step 4 names the
  only sound cheap key this study found for it: the pair
  `(e, chained hash of the current telescope)`, maintained incrementally at
  push/pop so a lookup is O(1) — sound because with the *whole* telescope in
  the key a hit's context is judgement-identical, and surviving exactly the
  case the frame dies on, a binder re-entered with the same types (the
  reduce–recheck loops §6 of PROFILE describes). What fraction of the
  residue that catches is not known; a key that survives *distinct* openings
  needs the α-canonical closure, i.e. step 3's machinery on the acceptance
  axis. Neither was prototyped — the towers are at seconds after step 1, and
  this is the "stop here unless the numbers say otherwise" line.
* **The certified constant.** Fix 2 removes repeats, not the intrinsic
  30–100× per-step price of carrying derivations (C-O §3). A certified
  corpus run stays a multiple of acceptance forever, by design.
* **The trail on armed runs, post-step-1.** Zone A mints inside the armed
  window are fewer under the change (a cached `Gap` is not re-minted). The
  argument and the green ratchet in §6 say no pair report can see the
  difference; a future armed *acceptance-axis* diagnostic (none exists
  today) would need to account for it.
* **Not measured**, carried forward from PROFILE §9 where still open: Lean's
  kernel caches (still unverified); a true `--release` build; the
  cross-opening share as a number; hash-consing `kernel::Term` wall-clock.
  New here: step 3's actual yield (the 97.8% is a bound measured on another
  fixture, not a prediction for `nested_iota`); and `checker/`'s certified
  (`--features tg`) speed — PROFILE
  §1's reference row exercised `NullCertifier` only, so "checker/ keeps its
  caches *and* is fast while certifying" remains a source-level claim, not a
  timing. Two entries left this list at the landing: `ci/check.sh` end to end
  ran green at both `opt-level`s, and `nested.rs` without a memory cap is
  §6.1's four rows — since `#120` it no longer needs the > 7.5 GB that made
  it unaffordable to take.

Sources: PROFILE.md §§1–9; CERTIFYING-OVERHEAD.md §§1–4 and its appendix;
MINI-DESIGN.md §0.3, §0.4, §11, §13; MINI-HANDOFF.md §40; MEASUREMENTS.md
(nested-inductive entries, 2026-08-07); QUESTIONS.md (the def-eq cache
decision); `checker/src/mini/kernel.rs` (`Frame`, `frame_get`/`frame_put`,
`hash_expr`), `checker/src/mini/blocker.rs`, `checker/src/mini/run.rs:208`,
`checker/src/util.rs:790–932`, `checker/src/tc.rs:2388`; and §6's own runs.
