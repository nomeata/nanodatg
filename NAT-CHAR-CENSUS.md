# `nat_char_equations`: provenance census, closure per group, and whether to build the `Nat` bridge

Taken at `b91433b` in the `natchar` worktree. Binary:

```sh
cargo build -p nanoda_lib --features tg,stepcount --bin checker
./target/debug/checker --no-modelgen --verbose \
  checker/tests/fixtures/nat_char_equations.ndjson
```

**The `stepcount` feature is not optional for this census.** `NANODA_ASSUME`'s
acquire path in `TgBackend::admit_or_acquire` is behind
`#[cfg(feature = "stepcount")]`, so a plain `--features tg` build silently
ignores the variable. Measured: with `--features tg` alone, every setting of
`NANODA_ASSUME` including `*` returns exactly the baseline 152 gaps. A tranche
that reads "the deletion moved nothing" off a `tg`-only build is reading a
compiled-out branch, not a result.

Confirmed baseline, independently of the number handed to me: **152 gaps**, 2035
derived kernel theorems, 44 declarations, `accept`.

## 1. The provenance census

The reason-string histogram and the origin bitmask disagree about what this
fixture is made of, and the bitmask is the one to plan on.

| reason-string row | count |
| --- | ---: |
| `trans over an admitted premise` | 64 |
| `pi congruence over an admitted body premise` | 24 |
| `congruence over an admitted premise` | 20 |
| `undischarged assumption ⟦arg⟧ ∈ ⟦binder domain⟧ survived to the boundary` | 20 |
| `proj_reduce` | 14 |
| `nat_eq` | 5 |
| `eq_cache` | 2 |
| `nat_reduce` | 2 |
| `symm over an admitted premise` | 1 |
| **total** | **152** |

By mask (`origin_report`), the same 152 partition into **three** categories, not
two:

| | count |
| --- | ---: |
| admit-origins (`Admitted`, `premask == 0`) | 23 |
| relays solely attributed to one origin | 96 |
| relays naming two or more origins | 13 |
| escapes (`CONDITIONAL − CONSUMED`, no mask at all) | 20 |
| **total** | **152** |

and the origins rank:

| origin | own | relayed | SUBTREE (predicted) |
| --- | ---: | ---: | ---: |
| `proj_reduce` | 14 | 71 | 85 |
| `nat_eq` | 5 | 15 | 20 |
| `eq_cache` | 2 | 6 | 8 |
| `nat_reduce` | 2 | 4 | 6 |
| **total** | **23** | **96** | **119** |

### The third category, and why it matters

The 20 `undischarged assumption …` gaps are **not admit-origins and not relays**.
They are a ledger *difference* computed once the run is over
(`tg::escaped()` = `CONDITIONAL − CONSUMED`), pushed into the histogram in
`global_report` rather than passing through `merge_one`. Three consequences,
each load-bearing for scoping:

1. **They carry no origin bit**, so `origin_report`'s columns do not see them at
   all: 23 + 96 + 13 = 132, and 152 − 132 = 20 exactly.
2. **Their sub-tree is empty by construction.** A relay exists only when a
   premise is `TgCert::Admitted`; an escaped certificate is a *successful*
   derivation that happens to still carry antecedents, so rules above it consume
   it normally and produce no gap. Nothing can ever name it. Closing the 20
   removes exactly 20.
3. **The row's wording is narrower than its count.** Its doc comment says so:
   the count is the whole ledger, covering `has_type_local`'s context-local
   typings and `has_type_proj`'s field typings as well as `beta_step`'s argument
   membership; only the *name* is beta-specific. So "20 beta argument-typing
   obligations" over-reads it — it is 20 *certificates* reaching a boundary
   conditional, of unknown atom composition on this fixture. (For calibration,
   `proj_reduced_carrier`'s 16 escapes carry 135 antecedent atoms, ≈ 8.4 each.)

### What the fixture is actually asking

All 17 theorems are `Eq.refl _` (`nat_char_equations.lean:71–95`). The single
question is whether δ + ι reduces through Lean's `brecOn` / `below` /
`match_1` nest, whose step case projects the induction hypothesis out of a
`PProd` with `Expr.proj`. The control `recAdd`, written straight onto `Nat.rec`,
certifies; nothing through the nest does.

The census agrees exactly. All 14 `proj_reduce` origins exit at the *same* point
— `the checker handed over no proof pair — the endpoints are not proofs` — and
the structure census names one structure only: **`ctors=1 PProd`**. There are no
numerals in the source, `natLits=2` with `maxNatLit=1`.

**So the wall on this fixture is projection reduction through `PProd` in the
`brecOn` nest. It is not `Nat` arithmetic.** `nat_eq` (literals in two
representations) and `nat_reduce` (native arithmetic on literals) fire here
incidentally, at 5 and 2.

## 2. Closure per group, measured

`NANODA_ASSUME` deletions, `--features tg,stepcount`, one run each.

| deleted | total | Δ | escapes | acquired |
| --- | ---: | ---: | ---: | ---: |
| — (baseline) | 152 | — | 20 | 0 |
| `proj_reduce` | 78 | **−74** | 31 | 14 |
| `nat_eq` | 146 | −6 | 21 | 2 |
| `eq_cache` | 146 | −6 | 22 | 2 |
| `nat_reduce` | 147 | −5 | 21 | 2 |
| `nat_eq,nat_reduce` | 141 | **−11** | 22 | 4 |
| `proj_reduce,nat_eq,nat_reduce` | 60 | −92 | 35 | 18 |
| all four | 54 | **−98** | 37 | 20 |
| `*` | 54 | −98 | 37 | 20 |

Readings:

* **`proj_reduce` is half the fixture: −74 of 152 (49 %).** Predicted `SUBTREE`
  was 85; measured 74, i.e. 13 % over — consistent with the recorded band
  (terminal ≈ 10 %, mid-chain 34 %).
* **The `Nat` bridge proper is −11 of 152 (7.2 %).** `nat_eq` and `nat_reduce`
  compose exactly additively (6 + 5 = 11).
* `*` and "all four" agree to the digit, which confirms the four are the only
  admit-origins present.
* Superadditivity is visible and bounded as documented: all four measure −98
  against a sum of 91, excess 7, under the `MULTI` bound of 13.

### Two limitations of the hook, both measured here

**(a) The recorded one — it prices the fact being true, not the route being able
to prove it.** Every deletion *raises* the escape count (20 → 31 → 37), because
acquiring turns an admitted equation into an antecedent that the escape ledger
then charges for. The floor is the proof: with `*`, 54 gaps remain, 37 of them
escapes. So −98 is what is available *if the equations are simply true*; a real
derivation might discharge those antecedents instead of escaping, or might not.

**(b) An unrecorded one — the deletion is partial for `nat_eq`.** `origin_report`
gives `nat_eq` own = 5, but only **2** are acquired; under `*`, 20 of the 23
origins acquire and 3 `nat_eq` gaps survive. `admit_or_acquire` acquires only
when `premask == 0 && ta != tb` and `CondEq::new` succeeds, so origins failing
those conditions are undeletable. **`nat_eq`'s measured −6 is therefore a lower
bound**, with the `SUBTREE` upper bound at 20. The bridge proper is
**11 ≤ prize ≤ 26**, best estimate 11.

## 3. The recorded four-step plan, tested against the measurement

Each claim marked with what was measured.

| # | claim | verdict |
| --- | --- | --- |
| A | `checker/src/mini/eq_cash.rs`'s `cash`/`cash_stmt` derive `Γ ⊢ ⟦lhs⟧ = ⟦rhs⟧` from a Lean proof of `Eq α lhs rhs`, built on `cond_elim` and `Props::eq_sound` | **partially confirmed** |
| B | the old blocker was a crate edge that no longer exists, so the bridge is reachable from the TG path | **refuted as stated** |
| C | `quot_classes.rs`'s `rcompat_at` is the exact `BleClauses` shape, running on corpus rows 122/124 | **refuted as stated** |
| D | `NAT-BRIDGE-FEASIBILITY.md` claims "the three premises are already available from the export" | **already corrected; brief is stale** |

**A — partially confirmed.** `cash` (`eq_cash.rs:313`) and `cash_stmt` (`:353`)
exist and return `Cashed { eq, lhs, rhs }` (`:290`) whose `eq` is
`Γ ⊢ ⟦lhs⟧ = ⟦rhs⟧` with `Γ` possibly non-empty. The conclusion is *checked*,
not assumed (`:464–472` rejects with `Gap::ConvCompose("eq-cash-conclusion")` if
the built formula is not the claim). `cond_elim` is genuinely used (`:467`,
`derived/src/prop/cond.rs:105`). **`Props::eq_sound` is not.** It exists
(`derived/src/prop/apparatus.rs:52`, `:90`) but has zero occurrences in
`eq_cash.rs`; the file feeds `Direct::eq_ax` into `cond_elim` at concrete terms
instead — the same content, re-derived rather than instantiated. This is the
"look it up by what it concludes, never by its name" rule paying off in reverse:
the *name* in the plan was wrong while the *conclusion* was right.

Preconditions worth pricing before anyone plans on it: a `&mut mini::kernel::Checker`
threaded over a **populated** interpretation store; a fully applied proof term;
head `Eq.{v}` at arity 3; **ground σ** (a symbolic level gives
`Gap::SymbolicLevel`); `⟦Eq.{v}⟧` in the store; and typings *and* interpretations
for all three arguments.

**B — refuted as stated; the blocker moved rather than closed.** The crate edge
really is gone (workspace members are `kernel`, `derived`, `checker`; there is no
`mini` crate) and the visibility chain is fully public in one crate —
`lib.rs:18 pub mod mini`, `mini.rs:79 pub mod eq_cash`, `eq_cash.rs:313 pub fn cash`
— so `crate::mini::eq_cash::cash` *resolves* from `tg.rs`, which already reaches
into `crate::mini::` in ~20 places. **But a call would not compile today**:
`cash` needs a live `mini::kernel::Checker`, built from a `mini::env::Environment`
and a `&mut mini::interp::Interp`, and `TgBackend` holds neither at any site
(`Environment` does not occur in `tg.rs`; every `Interp` mention is a comment).
Everything mini publishes to tg arrives as finished data through the shared const
store — `Rc<Translated>`, `Rc<DepRec>`, `Rc<NatClause>` — not as a resumable
checker. There is also an ordering constraint at `mini/route.rs:285–288`: a
routed run must start on a thread where no `TgBackend` has been built.

Corrected in place at `derived/src/nat/ble_unique.rs:35–36`, which still stated
the stale crate reason verbatim.

**C — refuted as stated, confirmed as a structural precedent.** `rcompat_at`
(`quot_classes.rs:505`, `pub(crate)`) concludes
`Γ ⊢ ∀x ∀y. ((x ∈ A ∧ (y ∈ A ∧ ⟨x,y⟩ ∈ R̄)) → app(f̄,x) = app(f̄,y))` — one
theorem, conjoined antecedent, a relation-graph premise discharged through
`derived::quot::graph_pair`, and `f̄` applied at the *same* two variables.
`BleClauses` (`derived/src/nat/ble_unique.rs:306`) wants three *separate*
theorems with *nested* implications over one carrier `ω`, no relation premise,
and `g` applied at *different* arguments on the two sides. Not the same shape.
What *is* shared, and is the honest form of the claim, is the machinery: two
fresh scopes, `dprod_app` at the fibre, one `beta_spine` down `⟦Eq.{v}⟧`'s nest,
`cond_elim` + `mp`, then the discharges.

`MEASUREMENTS.md:10003` renders `rcompat`'s antecedent without the two `∈ A`
conjuncts; that is not what the code builds.

"Runs on corpus rows 122/124" is **unverifiable at this commit**: `vendor/` does
not exist and is untracked, and `checker/tests/corpus.rs:103–106` returns early
via `skip_guard::absent`. The tie is narrative only — `LEAN3-INDUCTIVE-COMPILER.md:69–71`,
`MINI-HANDOFF.md:1284–1285` — with **no test exercising `rcompat_at`**; the only
tests in that area (`derived/tests/quot.rs:361,365`) exercise `compat_at_empty`,
a different `∅`-instantiated theorem.

`BleClauses` and `ble_transfer` do exist under exactly those names
(`ble_unique.rs:306`, `:330`, re-exported at `derived/src/nat.rs:97`), with
`ble_transfer` concluding `⊢ app(app(g,a),b) = bleb(t,f,a,b)`. **Their only
callers in the tree are `derived/tests/nat.rs`.** Nothing in `checker/` calls
either.

**D — the brief is stale here.** The sentence "the three premises are already
available from the export" **no longer appears**; a previous seat already
corrected it in place at `NAT-BRIDGE-FEASIBILITY.md:621–628`, and the correction
is right. I re-verified what I could: the export is **absent** from this worktree
(`vendor/` untracked, no `init-prelude` file), so the `grep -c … # 0` cannot be
re-run — I am reporting absence, not re-confirming the count. The certifying
fixture *is* hand-written (`nat_char_equations.lean:20–27` says so in terms; the
three `ble` clauses are hand-typed at `:93–95`).

One residual staleness in that passage, corrected in place: it says the clauses
are certified "by `mini`", a different program. At this commit
`checker/tests/mini_nat_equations.rs:160–168` spawns `CARGO_BIN_EXE_checker`
with `--naive --no-modelgen` — the *same* binary on the naive route. The
load-bearing half is untouched.

### Verdict on the ordering

**The recorded plan's step 3 is aimed at the wrong wall.** Building
`derived::nat::BleClauses` / `ble_transfer` into a neutral path addresses the
`ble`/`beq` clauses as *arithmetic*, but the census says the seven `ble`/`beq`
theorems in this fixture fail for the identical reason as the ten `add`/`sub`/
`mul`/`pow` ones: `PProd` projection inside `brecOn`. Closing the arithmetic
buys 11 gaps; it does not make one more theorem certify, because every one of
the 17 is blocked upstream of arithmetic.

Steps 1 and 2 are not wrong, but step 2 is blocked on something the plan did not
name: not a crate edge, but `TgBackend` having no live mini `Checker`.

## 4. The `proj_reduce` question

The handoff records the `proj_reduce` origin as *eliminated* (`9b691cb`,
`CLAUDE-HANDOFF.md:68`, `:100`). Re-measured here:

* `proj_reduced_carrier`: **16 gaps, all escapes, zero `proj_reduce`** — the
  record is accurate for the fixture it was taken on.
* `field_in_u0_by_carrier`: **0 gaps**.
* `nat_char_equations`: **14 `proj_reduce`**, and per the corpus census these are
  every `proj_reduce` gap in the tree.

So the answer is **the elimination is real but narrower than "eliminated"**: it
covers the carrier fixture's projection sites and does not reach the `PProd`
projection inside Lean's `brecOn` nest. All 14 exit at the same place — the
checker handed over no proof pair, the endpoints are not proofs — against one
structure, `ctors=1 PProd`, 2 firings. That is a single named site, not a
family.

**The "2 firings against 14 exits" discrepancy above is the whole story, and I
read past it.** `PROJ_STRUCTS` only counts when the redex is a bare
`Expr::Proj`; 12 of the 14 have an *application* as their redex, so they never
reached that census line at all. A census one level deeper —
`derive_projection_computation`'s own decline string, now permanent as
`PROJ_DECLINE` — shows all 14 exiting at the **first** line of the computation:
12 at "the redex is not a projection", 2 at "the structure head is not a
constructor". The projection composition is never consulted. See §5.

## 5. The exact next construction, sized

**Not the `Nat` bridge. Not the `PProd`-projection leg either — the ι readiness
gate underneath it.** (Heading kept; the diagnosis below is corrected in place.)

* **Prize, stated separately from the population.** Population touched: 85 gaps
  by `SUBTREE`. **Reachable prize, measured: 74 of 152 on this fixture (49 %),
  and 74 of 383 across the *fixture* corpus (19 %).** Caveat (a) applies: −74 is
  the price of the equations being *true*; escapes rose 20 → 31 under the
  deletion, so a real derivation must also discharge what it introduces or the
  net is smaller.
  * **Corrected scope.** This section originally called it "the single largest
    closure available anywhere in the tree from one construction". That was a
    statement about the fixture population only, and I did not have the census
    that could tell the two apart. `ORIGIN-RANKING.md` has since measured both:
    **`proj_reduce` is worth zero on Lean's 91 exports** — it exists on exactly
    one file in the tree, this fixture — which puts it at rank 2 behind
    `iota: no interpretation — an indexed family` at −117. The tranche is still
    worth taking, because driving this fixture to zero is a goal in its own
    right and nothing else on it comes close; it is not the corpus-wide win the
    sentence claimed. Confirmed after landing: both large exports are unmoved
    (076 at 59, 077 at 53).
* **What is wanted — corrected, and this is where the section was wrong.** The
  sites do *not* want a wider projection composition. `reduce_proj` carries a
  subject's whnf trace only when `authoritative_reduction_ready` accepts every
  rule in it, and on this fixture **every one of its 30 refusals is a `Nat.rec`
  ι step**, declined by `wants_proj_red_iota` for "mini published no translation
  at these levels". `Nat` is a **direct clause**: `mini::direct::clause_for`
  routes it to the native `NatClause` before `zoneb::build` runs, so
  `publish_projection_translation` is never called for it and
  `mini_plain_recursive_translation_at` is permanently `None`. The gate's only
  question predicts `iota`'s `RecBottom::Dep` arm; `iota`'s own `usable` accepts
  a second arm, `RecBottom::Nat`, that the question can never reach. So the
  subject trace was dropped at all 14 `PProd` sites and `proj_red` was handed an
  *unreduced* subject. The fix is one added disjunct in the ι readiness gate
  (`TgBackend::iota_nat_clause_ready`), not a line of projection work.
* **Size — confirmed as one tranche, for the wrong reason.** The estimate was
  right and the mechanism was not. Landed at `3eab691`: **152 → 65, a fall of
  87**, which *beats* the −74 the deletion priced. Limitation (a) of §2 runs the
  other way here: `NANODA_ASSUME` acquires the equation as an antecedent and
  charges the escape ledger for it, while a real derivation discharges most of
  what it introduces (escapes 20 → 26, not 20 → 31). `gap: proj_reduce` 14 → 0
  and `gap: eq_cache` 2 → 0. The ι-site counts rise, 10 → 17 at `Nat.zero` and
  13 → 22 at `Nat.succ`, which is what says the gate certifies rather than
  merely going quiet.
* **The advice to "first refute the claim that `9b691cb`'s composition applies
  unchanged" was the right advice.** It does apply unchanged, and it was never
  reached. The load-bearing error in this section was locating the wall at the
  projection rule because that is the rule whose *name* is on the gap.
* **Ordering.** It must be re-measured after, not before, whichever seat is on
  the 16 carrier gaps lands, because both terminate in the escape ledger and the
  ledger is the shared floor.

## 6. What I would not build, and why

* **The `Nat` bridge as scoped (steps 1–4).** Measured reachable prize **11 gaps
  of 152 on this fixture, 11 of 383 corpus-wide (2.9 %)**, upper bound 26. It
  makes **zero** additional theorems certify, because all 17 are blocked upstream
  at `PProd`. `nat_eq`'s deletion is additionally only 2/5 effective, so even the
  11 is partly untested. Build it when something is actually gated on it; nothing
  here is.

  > **REVERSED, 2026-08-15 — and the last sentence is why.** Something is gated
  > on it, and it had never been measured. On `init-prelude` — the real goal
  > population, 10 262 gaps — the origin
  > `iota: the major premise is not a constructor` measures **−3 780**, the
  > largest single closure in the project, and **466 of its 563 constant-head
  > firings are `Nat.ble` applied to two literals**, with the remaining 97
  > `Nat.decEq` / `Nat.beq` / `Nat.decLt` / `OfNat.ofNat` — all of them `Nat`
  > arithmetic or `Nat` decidability. `derived::nat::BleClauses` / `ble_transfer`
  > conclude exactly that clause and are still called only from
  > `derived/tests/nat.rs`.
  >
  > Everything measured *about this fixture* above remains correct — the price
  > here is now −18 of 61 (30 %, up from 11 of 152) and it still certifies zero
  > additional theorems. The error was one of population, not of arithmetic:
  > this fixture is hand-written with `natLits=2, maxNatLit=1`, i.e. **it
  > contains no numerals**, and Lean's prelude is full of them. Do not re-derive
  > the decision from this section; `ORIGIN-RANKING.md`, "The next build", has
  > the measurement and names the two checks that must refute it first.
* **`BleClauses` / `ble_transfer` wiring into a neutral path.** Same reason, plus
  the clauses are not in the export and would have to be synthesised first — and
  synthesising clauses to make them checker-routed failures is explicitly out of
  scope. The constructions exist and are tested in `derived/tests/nat.rs`; they
  should stay there until a real consumer appears.
* **Porting `rcompat_at` toward `BleClauses`.** The shapes differ in three ways
  (conjoined vs nested antecedent, relation premise vs none, same vs different
  arguments). The shared machinery is worth *reading* when the time comes; it is
  not worth a port.
* **Plumbing a `mini::Environment` / `Interp` handle into `TgBackend` to reach
  `eq_cash`.** This is the real cost of step 2 and it cuts across the one-checker
  architecture at the exact seam the design is most careful about. It should not
  be paid for an 11-gap prize; revisit it if a large origin ever turns out to
  need cashing.
* **Anything scoped off a `--features tg` build's `NANODA_ASSUME` output.** It is
  compiled out and reports the baseline unchanged.

## 7. Instrumentation

None added, and none committed. Every number above comes from mechanisms already
in the tree — `origin_report`, the escape ledger, and `NANODA_ASSUME` under the
existing `stepcount` feature. No file under `checker/` was modified.
