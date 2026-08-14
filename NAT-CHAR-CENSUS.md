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

## 5. The exact next construction, sized

**Not the `Nat` bridge. The `PProd`-projection leg of `proj_red`.**

* **Prize, stated separately from the population.** Population touched: 85 gaps
  by `SUBTREE`. **Reachable prize, measured: 74 of 152 on this fixture (49 %),
  and 74 of 383 corpus-wide (19 %)** — the single largest closure available
  anywhere in the tree from one construction. Caveat (a) applies: −74 is the
  price of the equations being *true*; escapes rose 20 → 31 under the deletion,
  so a real derivation must also discharge what it introduces or the net is
  smaller.
* **What is wanted.** All 14 sites want the same thing: `proj_red` on a
  one-constructor structure `PProd`, where the checker did not hand over a proof
  pair. The certificate needed is the ordinary projection-reduction equation
  `(mk a₁ … aₙ).i ⟶ aᵢ` at `PProd`, composed under the application suffix the
  `brecOn` nest wraps it in — which is exactly what `9b691cb` already built for
  the carrier fixture ("retains an inner projection proof and composes it under
  an application suffix").
* **Size.** This is an *extension of an existing derivation to one more site*,
  not a new construction. The mechanism is present and green; what is missing is
  reaching it when the endpoints are not proofs. I would scope it as **one
  tranche**, and I would have the seat first refute the claim that `9b691cb`'s
  composition applies unchanged — that is the load-bearing assumption and it is
  cheap to test by pointing the existing path at the `PProd` site and reading
  the exit code census.
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
