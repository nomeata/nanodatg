# Claude handoff

Originally written 2026-08-14; **substantially rewritten 2026-08-15** after 94
commits. This is a delta/update for Claude's imported conversation context, not
a replacement for the design documents. Sections below marked as history are
kept because the reasoning is still useful; the *current* numbers are all in
"Current measured certification frontier" and the gate list.

**The four documents that now carry the live scoping**, in the order a new
reader should take them: `ORIGIN-RANKING.md` (every gap origin ranked by
bitmask and deletion over both populations), `SEAM-DESIGN.md` (where the
TG/mini seam belongs, plus §9's inventory of what crosses it and §10's
`fire_dep` findings), `TEST-INVENTORY.md` (every suite's true status, the
per-leg floors, and §4.5/§6 on structurally-untestable assertions), and
`MEASUREMENTS.md` (append-only; the 2026-08-14/15 sections are this arc).

## Executive state

Snapshot updated **2026-08-15**, 94 commits after the original handoff. The main
checkout is on `master` at `d73c94f`. The worktree is clean except for the
long-standing untracked `scripts/__pycache__/`; preserve it. **`git push` does
not work in this environment** — `origin` is GitHub with no credentials, so every
commit below is local. All seat branches are merged into `master`;
`explore/level-poly-target` is deliberately separate.

**`init-prelude` now ACCEPTS.** It reached declaration 1 and declined this
morning; it now reports `accept  1822 declarations`, certified prefix 152, pairs
32, in ~39 s. What stops it is no longer acceptance but *interpretation debt* —
see "The init-prelude frontier" below.

**Modelgen is out of scope: do not modify it.** It is being turned into a
standalone product elsewhere.

The level-polymorphism branch is paused cleanly with its restart head, pick-up
list and a *what-not-to-redo* list in `LEVELPOLY.md` §5.3.0.

## Owner decisions and non-negotiable architecture

The two historical pipelines are not alternatives. They are one checker:

- one parse;
- one `Instantiations::compute`;
- one loop over declaration groups;
- one dispatch on declaration kind;
- inductive, mutual-inductive, and quotient construction is handled by the
  former Mini implementation;
- axioms, definitions, theorems, and opaque definitions are checked by nanoda
  and produce TG evidence in that same call;
- each declaration group is accepted/type-checked exactly once;
- no fallback to the other checker, no repair sweep, and no post-loop second
  validation pass;
- `--naive` selects the historical whole-file Mini checker and is the only way
  to run that policy;
- a nanoda-accepted ordinary declaration is mirrored *unchecked* into the
  former Mini syntactic environment so a later Mini-owned inductive can refer
  to it;
- TG gaps are certification debt: the normal CLI exits 4 while any remain;
  `--acceptance-only` intentionally ignores certification debt.

The top-level `mini` crate/directory is gone. Its surviving implementation is
inside the checker crate, principally under `checker/src/mini/`. Do not restore
a separate crate or binary. The production policy and loop are in
`checker/src/mini/route.rs`; the nanoda group adapter is in
`checker/src/routed.rs`; the CLI is `checker/src/bin/checker.rs`.

The semantic ownership rule is equally important: Mini-owned inductive
carriers, constructor graphs, recursors, projection packages, and certificates
are authoritative. TG must consume those exact objects/evidence. It must not
reconstruct a parallel carrier or recursor, rerun reduction, invoke the other
checker, or hide failure behind a fallback.

## Unified-checker work already landed

The integration sequence from the pre-merge baseline `a10bf90` is:

| Commit | Result |
| --- | --- |
| `44e2de4` | Records the unified-pipeline decision. |
| `4e86d46` | Removes the top-level Mini crate and moves it into `checker`. |
| `8815abb` | Implements one declaration loop and one dispatch; removes force-route modes, fallback checking, and the post-loop checker sweep. |
| `18212fc` | Makes Mini's `Nat` carrier/constructors/recursor and shared `NatClause` authoritative to TG. |
| `02ab90f` | Makes TG consume Mini's class-(T) projection package for direct redexes and projection congruence. |
| `a3911d6`, `0e42cf3` | Threads memoized projection-subject reduction evidence into `proj_red`, with a readiness gate. |
| `b4127ac` | Consumes Mini's dependent iota evidence for parameterless fieldless inductives such as `Two`. |
| `fb1692c` | Consumes carrier, recursor, constructor-spine, and iota evidence for unary plain-recursive constructors such as `N.s n`. |
| `9b691cb` | Retains an inner projection proof and composes it under an application suffix; eliminates the remaining `proj_reduce` origins. |
| `cc5dfd5`, `4a1f567` | Replays exact lazy-delta traces, but retains recipes only when replay is sound and useful. |
| `4fc2f25` | Replays certificate-free, endpoint-checked structural equality recipes; eliminates the final `eq_cache` origin. |
| `b654c98` | Refuses to park conditional reduct certificates in memo traces; removes eight false escape/copy artifacts. |

The relevant production and regression code is concentrated in:

- `checker/src/mini/route.rs`
- `checker/src/routed.rs`
- `checker/src/tc.rs`
- `checker/src/reduct.rs`
- `checker/src/tg.rs`
- `checker/src/mini/interp.rs`
- `checker/src/mini/proj_data.rs`
- `checker/src/mini/nat_clause.rs`
- `checker/tests/unified_cli.rs`

`ENV-UNIFY.md` sections B6-B8 explain the first Nat/projection handoffs. Later
commits and `checker/tests/unified_cli.rs` are the current source of truth for
the subsequent projection work. Some earlier Track-D prose in `ENV-UNIFY.md`
still describes superseded force modes/fallbacks while narrating history; do
not mistake that historical stage for the current architecture.

## Current measured certification frontier

Measured on `master` `d73c94f`, verified independently rather than inherited.

### The two populations

| fixture | gaps | | Lean's own exports |
| --- | ---: | --- | --- |
| `nat_char_equations` | 61 | | 91 exports, **16** carry gaps, **168** total |
| `mutual_aux_encoding` | 49 | | `076_listRecReduction` 45 |
| `ctor_abbrev_major` | 23 | | `077_RBTree.id_spec` 28 |
| `proj_reduced_carrier` | 13 | | 74 exports are **fully certified** |
| `quot_lift_reduction` | 12 | | |
| `proj_stuck_subject` | 6 | | |
| `proj_reduced_subject` | 2 | | |
| `field_in_u0_by_carrier` | 0 | | |

**The exports are the completeness claim; the fixtures are the development
signal.** Completeness is measured against Lean, never against fixtures we wrote.
Where they disagree, believe the exports: `proj_reduce` was worth −74 on a
fixture and **zero** on the exports.

Movement over the 94 commits: exports **217 → 168**, `nat_char_equations`
152 → 61, `mutual_aux_encoding` 96 → 49, `ctor_abbrev_major` 46 → 23,
`proj_reduced_carrier` 16 → 13.

### The init-prelude frontier

`checker --verbose --mutual --nested vendor/arena-tests/good/init-prelude.ndjson`
— **all three flags are needed**; under `--no-modelgen` it declines at
declaration 1 on `Lean.Syntax`, and with modelgen but no gates it declines on the
*mutual* inductive the nested splice emits.

    accept  1822 declarations
    untranslated: 91 declarations, 10 eliminators
    uncertified:  32 const typings, 29 type typings
    tg gaps: 11909      prefix declarations=152 pairs=32      exit 4

Of the 11 909 gaps, **6 683 are `trans over an admitted premise`** — relays, not
origins. Exit 4 is correct: it is certification debt, not rejection.

What stops it now is **interpretation debt**, in two named families:

* **`type former spine`** — the heterogeneous-operator classes (`HAdd`, `HSub`,
  `HMul`, `HPow`, `HAnd`, `HOr`, `HXor`, `HShiftLeft/Right`, `HAppend`,
  `HAndThen`, `HOrElse`, `HDiv`, `HMod`, `HSMul`), the `Monad*` classes,
  `Membership`, `EStateM.Backtrackable` — 2 each, `Trans` 4.
* **`field type uninterpretable`** — the machine words `UInt8/16/32/64`,
  `USize`, plus `Char`, `String`, `Fin`, `BitVec`, `ByteArray`, `Substring.Raw`,
  `Hashable`, and the `Lean.*` syntax types.

Plus recursor declines: `False` and `PEmpty` (class (S) eliminator, no
constructors) and `HEq` (a result index is not a bare field).

### Performance, for calibration

`init-prelude` went **28.211 T → 0.507 T `instructions:u`** and **2126.7 s →
38.7 s** across four changes, each with a byte-identical verdict and every
`gap: <reason>` row unchanged across all fixtures and all 91 exports: a
closed-pair `def_eq` decision cache, a persistent `infer_type` gap memo, a
`whnf` reduction memo, and a five-line syntactic-equality shortcut. Separately,
mimalloc was linked into the production `checker` binary (it had only ever been
on `nanoda_bin`) for **−41 to −44 % task-clock**.

**Two measurement rules follow from that work.** `instructions:u` *understates*
allocation- or cache-shaped changes by 9–17 points — quote `task-clock`
alongside it for those. And **report rows, not totals**: two ratchets drifted for
134 commits because only a TOTAL was guarded.

## The gate list

**Corrected 2026-08-15 against a measured inventory of every test target and
every `ci/` step; see `TEST-INVENTORY.md` for the table and the method.**

The previous wording here said a full no-default unit-test run "is not a gate"
because it "exposed four pre-existing Mini-test failures and one unrelated test
running longer than 60 seconds, so it was stopped". Every clause of that
sentence was load-bearing and three of them were wrong:

* the four failures were not pre-existing noise. They had **one root cause** —
  the publication helpers read `joint_key(&key).is_some_and(…)` as "divergent
  shared evidence" when `joint_key` returns `None` for a `Name` in a
  per-declaration `TcCtx` arena, which cannot cross the seam at all. One fix
  took the suite to **244/244**;
* "one unrelated test" was never named, so nobody could weigh it. It is
  `checker/tests/mini_nested.rs` at ~175 s, of which two tests are individually
  over 60 s. A full `--features tg` run of every target is ~8 minutes;
* and a sentence that tells the next reader a red number is expected is how a
  real defect stays hidden. It did: the suite was carried as "four known
  failures" long enough that nobody re-counted, and the fifth was never noticed.

So the rule is now stated the other way round. **A suite is either a gate or it
has a written reason, with a measurement, for not being one.** "Not a gate" must
never again be readable as "unimportant" or as "expected to be red".

### Gates — all of these must be green before a commit

```bash
cargo test -p nanoda_lib --no-default-features --lib            # 244/244
cargo test -p nanoda_lib --features tg --lib                    # 292/292
cargo test -p kernel -p derived                                 # 1047/1047, 109 targets
cargo check -p nanoda_lib --no-default-features --all-targets   # 5 existing warnings only
ci/check-boundary.sh                                            # OK
ci/test-boundary.sh                                             # OK
```

`kernel` and `derived` are on the list because they were on no list at all,
and `kernel` is the entire trusted computing base — the only component that
must be correct for soundness. They are 1047 tests, all green, and they run in
seconds. There was never a reason to exclude them; nobody had looked.

`ci/test-boundary.sh` is on the list because it was **red on master** when this
inventory was taken, and it is the file that proves the boundary check can
fail.

Before any corpus test, in a worktree: **`ci/corpus-dir.sh --link`**. `vendor/`
is gitignored, so a worktree otherwise reports `ok … 0.00s` having checked
nothing.

### Ratchets — green, but exact, so run them when you touch the checker

```bash
cargo test -p nanoda_lib --features tg --test unified_cli       # 6/6
cargo test -p nanoda_lib --features tg --test mini_designed     # 34/34
```

### Currently red, with the reason — do not treat these as noise

`tg_tutorial` (3), `mini_envshare_tg` (2) and `mini_route_tg` (1) are red on
master and are **not** gates *yet*, for a reason that is written down rather
than assumed. Three of the six are stale assertions in the improvement
direction (carriers that used to differ now converge, with the offer
populations conserved); two are ratchets that moved *adversely* and need a
whole-ledger diff to adjudicate; one is a gap budget that improved 31 → 9.
`TEST-INVENTORY.md` §3 has the evidence for each, including why the adverse
pair cannot be re-based on the strength of the passing totals ratchet alone.

They are excluded because **nobody can currently say which commit moved them** —
the ratchets were last set at `43bac38`/`3c4323b` and a dozen checker commits
have landed since with nothing re-running these suites. That is a debt with an
owner and a next step, not a standing exemption. The moment the attribution
exists, they become gates: they are the strongest property in the tree, since
`tg_tutorial` asserts that *every* definitional-equality step on the listed
exports was discharged by a real kernel derivation.

### Everything else in `ci/`

`ci/check.sh` runs all 29 steps and is the full check; it is not a per-commit
gate because it builds three feature configurations and two release binaries
(4.40 T `instructions:u`, 603 s of task-clock for the compiles alone —
`TEST-INVENTORY.md` §4). It now fails if its own step count is not the declared
29, so a step can no longer vanish from the schedule in silence.

**It is a merge gate, and that is the correction this section exists for.**
`ci/check.sh` *does* cover `tg_tutorial`. When the two adverse ratchets were
adjudicated it turned out **both had fired correctly the first time they were
run** — nothing was missing from the assertions, and per-row floors were not
what was needed. What was missing is that nobody ran `ci/check.sh` across 134
commits, because it was on no list. So:

* **before a commit** — the gate block above;
* **before a merge to `master`** — `ci/check.sh`, in full.

A suite that is correct and unrun is indistinguishable from one that is absent.
The 134-commit gap is the measurement behind that sentence, and 13 of those
commits have empty message bodies, so `git log` would not have recovered the
attribution either.

## What is actually left, 2026-08-15

The section below this one is **history** — it described the carrier fixture at
16 gaps and the tranche that took it to 13. Read it for the reasoning, not the
numbers. What remains now, in the order the measurements put it:

1. **The escape population is the terminal wall.** A floor analysis found that
   with every *hooked* origin closed, 89 % of what survived were escapes —
   reachable by no origin tranche. Since then the **ambient-local** category was
   exhausted corpus-wide (scope provenance) and the **raw-beta** category was
   priced at **44 gaps tree-wide in the perfect limit**, across ten shape-groups
   needing different constructions, and deliberately abandoned. Closure there is
   brutally nonlinear: the largest single shape-group is 54 atoms present in 12
   of 16 certificates and closes **one**.
2. **`076_listRecReduction`'s −35 is behind a *layer*, not a wall.** `fire_dep`'s
   parameterised path is a run of constructions each written for `np == 0`, and
   the 37-gap sub-tree **migrates intact** across each rather than shrinking.
   Three are named in `SEAM-DESIGN.md` §10, the third unexamined. The `np > 0`
   type-former adoption was built, confirmed working end to end on `Prod` and
   `List`, measured at **0**, and reverted. **Census the layer before building
   anything there.**
3. **`077_RBTree.id_spec`'s −19 is blocked on task #38** and is *not* a
   consumption: `IndexedCtor::mem_lean`'s witness protocol demands closed,
   prenex witnesses at `derived`'s own working variables, while every consumer
   holds open-scope already-instantiated theorems whose scope assumptions are
   live hypotheses and therefore cannot be generalised back.
4. **The `Nat` bridge remains not worth building** — priced at −11 gaps and
   **zero additional certified theorems**, because all 17 theorems in
   `nat_char_equations` are `Eq.refl`, there are no numerals, and the `ble`/`beq`
   theorems fail for the identical reason as the arithmetic ones.
5. **`init-prelude`'s interpretation debt** — the `type former spine` and
   `field type uninterpretable` families listed above. This is a different kind
   of work from everything in this arc: *"what interprets a machine word and a
   type-former spine"*, not *"why does it stop"*.

**The pattern worth carrying forward**, found five times: *mini publishes the
fact and TG declines for want of a rule it could have stood on.* Variants seen —
published-and-unconsumed; published behind a guard whose own header says it is
about cost; **three independent mints of one carrier in a single binary**; and
published correctly but **consumed at the wrong arity**. `SEAM-DESIGN.md` §9 is
the inventory, and its **meetability column** is the point: a zero-consumer row
is a *question*, not a finding — one of the three that motivated it turned out
not to be an opportunity at all.

## History: the boundary blocker, as it stood at `b654c98`

All 16 remaining carrier-fixture gaps are honest conditional certificates that
reach a declaration boundary. Temporary classification instrumentation was
reverted; the branch is clean. Across the 16 certificates there are 135
antecedent atoms:

- **8** exact typings of context locals, `⟦w⟧ ∈ ⟦A⟧`;
- **50** guarded-family closures;
- **77** raw beta argument-typing obligations;
- **0** projection-field assumptions.

By declaration/certificate family:

```text
recAddNZ      raw 1
recAddNS      raw 1 + family 1
N.brecOn.go   four certificates: local 5 + raw 5 + family 1 total
addN          local 1 only
addNZ         raw 7 + family 6
addNS         raw 5 + family 11
dblN          local 1 only
dblNZ         raw 13
dblNS         raw 10 + family 6
leN           local 1 only
leNZ          raw 12 + family 3
leNSZ         raw 13 + family 9
leNSS         raw 10 + family 13
```

Exactly three escaping certificates (`addN`, `dblN`, `leN`) contain only an
ambient local's own typing. The other thirteen require real typing evidence
for raw beta obligations; the family wrappers largely carry the same debt.

### Why typed de Bruijn keys did not already solve this

The owner's intuition here is correct. TG's local identity is
`LocalKey::Level(level, interpreted_binder_type)`, so the term and its exact
typing premise remain available and same-level/different-type locals cannot
alias. The problem is not a lost context or a cache-key mismatch.

The missing information is *scope provenance*. TG can derive the real theorem

```text
⊢ ⟦w⟧ ∈ ⟦A⟧ → ⟦a⟧ = ⟦b⟧
```

but a bare equality cache/boundary asks for `⊢ ⟦a⟧ = ⟦b⟧`. A local may be:

1. ambient, already in the declaration context Γ, in which case its typing
   premise is part of the semantic interpretation of `Γ ⊢ a ≡ b` and should be
   abstracted at the judgement boundary; or
2. opened inside this definitional-equality query, in which case its premise
   must be discharged by the binder rule before the query returns.

The `(level, type)` key proves identity but not which operation owns the
binder. Production currently has no equality-query baseline/open-close marker
that distinguishes these cases. The escape ledger therefore conservatively
charges every conditional answer reaching the boundary. The explanatory
comments near "What the escapes actually are" and the escape ledger in
`checker/src/tg.rs` are accurate and should be read before changing this.

### Recommended next tranche

1. Add explicit equality-query scope provenance: capture a baseline at the
   outer `def_eq` entry and track locals opened beneath it.
2. At the judgement boundary, abstract only exact local-own-typing antecedents
   proven ambient relative to that baseline.
3. Query-opened locals must still be consumed/discharged or reported as
   escapes. Add an adversarial regression that would fail if a query local were
   misclassified as ambient.
4. First target only `addN`, `dblN`, and `leN`. A clean result should remove
   three escapes; do not broaden the rule merely because the key contains a
   local.
5. Reclassify the mixed `N.brecOn.go` certificates afterward. Ambient
   abstraction may remove some antecedent atoms there, but will not close a
   certificate that still carries raw/family debt.
6. Independently, derive actual typing evidence for the 77 raw beta premises.
   Do not relabel them as ambient and do not globally retain conditional
   certificates. The guarded-family atoms should be peeled only when the
   underlying typing obligation is genuinely discharged.

No implementation of scope provenance was in progress when Bacon was stopped.
The clean branch `joachim/equality-scope-provenance` points at `b654c98`, as
does its durable worktree
`/home/joachim/nanodatg/.claude/worktrees/equality-scope-provenance`.

## History: the Nat-equation plan, and why it was not taken

**Superseded — do not execute this.** The four-step plan below was written
before the census. Measured, the `Nat` bridge is worth **−11 gaps and zero
additional certified theorems**, and `nat_char_equations`' real wall was
`PProd` projection inside `brecOn` (closed, 152 → 65) and is now the escape
population (61, of which 22 escapes and 32 relays). Steps 1–2 were also
partly refuted on their own terms: `eq_cash`'s `cash`/`cash_stmt` do check
rather than assume, but they use `Direct::eq_ax` and **not** `Props::eq_sound`
as step 2 says; and a call from TG would not compile, because `TgBackend`
holds no `mini::Environment` — the seam question that `SEAM-DESIGN.md` was
written to settle. Kept because the reasoning about what the equations need is
still sound.

The earlier measured plan was:

1. get the exact Eq-refl theorem declarations in the fixture certified by the
   nanoda/TG path;
2. factor/consume the relevant equality cash/generalisation evidence from
   `checker/src/mini/eq_cash.rs` and `checker/src/mini/quot_classes.rs` without
   running the Mini checker again;
3. build the neutral `derived::nat::BleClauses` / `ble_transfer` path around
   `derived/src/nat/ble_unique.rs`;
4. ratchet the exact source clauses in
   `checker/tests/fixtures/nat_char_equations.lean`.

Do not synthesize new clauses merely to make them checker-routed failures, and
do not fall back to Mini for their checking. The projection and boundary work
has changed the gap census substantially, so inspect current provenance before
assuming the old ordering is still exact.

## Queued second thrust: level polymorphism

Main has priority. The level-poly work is complete but isolated on
`explore/level-poly-target` at `6fa6b19` (`mini: Eq.rec at two symbolic levels,
28 constants and two exits`) and was pushed to `origin/explore/level-poly-target`.
Its recorded result is:

- Gate A byte-identical;
- Gate B exits `32/57/2 → 34/55/2`;
- zone-B successes `208 → 236 / 362`;
- values OK `117 → 118 / 146`;
- value evidence `71 → 72`;
- stored `116 → 118`;
- ground instructions `+0.0033%`;
- `--poly` instructions `+8.21%`, because 28 Eq.rec nests now complete;
- its full test suite was green, including mutation regressions.

The branch predates the crate move and its worktree is
`/home/joachim/nanodatg/.claude/worktrees/lp2`. Do not blindly cherry-pick it
onto current master: port/rebase its former `mini/` paths into
`checker/src/mini/`, resolve against the unified environment deliberately, and
rerun both its gates and the unified CLI ratchets. Do this only after the main
thrust or explicit reprioritisation by the owner.

## Commands and operating constraints

Useful focused commands:

```bash
cargo test -p nanoda_lib --features tg --test unified_cli
cargo test -p nanoda_lib --features tg --test mini_designed
cargo check -p nanoda_lib --no-default-features --all-targets
cargo run -p nanoda_lib --features tg --bin checker -- \
  --no-modelgen --verbose checker/tests/fixtures/proj_reduced_carrier.ndjson
```

For commands that may use substantial memory, apply an explicit limit. Prior
work used 8 GiB per process, for example:

```bash
(ulimit -v 8388608; cargo test -p nanoda_lib --features tg --test unified_cli)
```

Keep aggregate resident memory below 50 GB and monitor it with:

```bash
systemd-cgtop -m user.slice/user-1001.slice
```

This is a shared machine. Use `perf stat -e instructions:u` rather than wall
time for performance comparisons. Put large temporary artifacts under the
project-local `_tmp/`, not `/tmp` or another tmpfs. Commit and push coherent
green checkpoints early. Keep the main checkout on `master`, fast-forward or
cherry-pick reviewed agent commits onto it, and push `master` as commits land.

Do not delete or modify unrelated Claude worktrees/branches. In particular,
modelgen-related worktrees belong to the separate product effort.

Two Codex-created worktrees were initially outside the repository's durable
area. They have been recreated, clean and branch-identical, at:

- `/home/joachim/nanodatg/.claude/worktrees/inductive-tg`
  (`joachim/inductive-tg`, `18212fc`); and
- `/home/joachim/nanodatg/.claude/worktrees/equality-scope-provenance`
  (`joachim/equality-scope-provenance`, `b654c98`).

There is no longer any project worktree at `/home/joachim/nanodatg-*`.
