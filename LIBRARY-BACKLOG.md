# Library backlog: derived constructions to build in parallel

A laundry list of self-contained `derived/` constructions that the project will
certainly need, can be built now, and are independent enough to farm out to
background agents. Compiled 2026-08-01 against the tree at `derived` = 543
tests, after surveying `README.md`, `MEASUREMENTS.md`, `INDUCTIVES.md`,
`DECISIONS.md`, `QUESTIONS.md`, the thesis (§5.1–5.4, §6.2), and a full
inventory of `derived/src/`.

**Ground rules for every entry:**

- `derived/` only. Nothing here touches `checker/src/tg.rs`,
  `derived/src/inductive/`, or the recursor/ι design — all three are in flight
  concurrently. Where an entry's *payoff* needs a later `tg.rs` consumer, that
  wiring is called out as a separate, later step and is **not** part of the
  entry.
- One construction per file, each with a documented `# Interface` header, in
  the register of `derived/src/cumul/wmem.rs` / `derived/src/wlist.rs`.
- Every lemma pinned by a test and checked for non-vacuity (both polarities
  where the statement is a subsingleton or a closure).
- **The one shared touch-point is `derived/src/lib.rs`** (or a hub file), which
  gains one `pub mod …;` line per new top-level module. Entries 1, 5 and 6
  each add one. If dispatched simultaneously, expect a trivial one-line merge
  there; everything else is new files.
- No new kernel axioms. Everything below is conservative construction.

Ordered by payoff-per-risk. Status is **READY** (dispatch now) or **BLOCKED**
(named blocker).

> **Status of the READY list, 2026-08-01: it has been consumed.** This backlog
> was compiled the previous evening and every READY entry has since landed or is
> being built as this is read — in each case in the *exact* file the entry names.
> Entry 1 (`acc`) was independently verified done. Do **not** dispatch an agent
> against a READY heading below without first checking whether the file it names
> already exists; the per-entry notes say what was found. The specifications
> themselves are still worth reading — they are what the implementations were
> built against — but the status column is now historical.

---

## 1. `acc(A,R)` — the accessibility carrier — **DONE** (2026-08-01)

Built as `derived/src/acc.rs` (hub) + `derived/src/acc/{condition,induction,
intro,rect,witness,apparatus,shared}.rs`, with `derived/tests/acc.rs` (12
tests). The file split follows `wtype.rs`'s, not the `{set,intro,induction}`
sketched below. Everything exported is **unconditional** — the entry's
"cheaper than `W`" judgement held: `x ∈ A` is a hypothesis of the introduction
rule, which is exactly the conjunct `closed(A,B,u)` exists to supply for `W`,
so no bound, universe or `crate::bound` companion is needed. `pairs`' theorems
turned out not to be needed either: `⟨y,x⟩` is only ever built, never taken
apart. `rec_acc` (entry 7) is now unblocked. Original entry follows.


**Builds:** in new files `derived/src/acc.rs` (hub) + `derived/src/acc/`:

```text
acc(A,R) := ⋂ { C ∈ 𝒫A : ∀x ∈ A. ((∀y ∈ A. (⟨y,x⟩ ∈ R → y ∈ C)) → x ∈ C) }

⊢ ∀A ∀R. acc(A,R) ⊆ A                                          [acc_subset]
⊢ ∀A ∀R ∀x. ((x ∈ A ∧ ∀y. (y ∈ A → (⟨y,x⟩ ∈ R → y ∈ acc(A,R))))
      → x ∈ acc(A,R))                                          [acc_intro]
⊢ (C ⊆ A ∧ step_closed(C)) → acc(A,R) ⊆ C                      [acc_induction]
```

plus the strong-induction instance at `C := {x ∈ acc : φ}` (the exact analogue
of `wtype::rect`). Unlike `W`, **no bound and no universe is needed**:
`acc ⊆ A` by construction, so the Separation is on `𝒫A` and the whole
ω-tower/`closed(A,B,u)` apparatus is irrelevant. This is the same
least-closed-set pattern as `derived/src/wtype.rs` (W1/W2), which is the
template to copy.

**Why needed:** thesis.txt:2126 interprets `acc` as a real set
(`⟦acc_{α,r} x⟧ = [x ∈ acc(⟦α⟧,⟦r⟧)]`, "see below" → §6.2.2 at
thesis.txt:2155–2166); thesis.txt:1824–1889 (§5.3) translates *every*
subsingleton eliminator — `Eq.rec` included — through `acc`;
`README.md:212–214` (remaining-work item 2) puts `acc` before §5.3 before
§5.2's `spec` judgment for indexed families; `INDUCTIVES.md` (log,
"What indexed families need next"): "The order is therefore `acc`, then §5.3,
then §5.2's `spec` judgment." Verified missing: no accessibility or
well-founded construction anywhere in `derived/src/` (grep 2026-08-01;
`inductive/spec.rs:68` explicitly declares it out of that module's scope by
design).

**Dependencies / reuse:** `funcs::separation_full`, `pairs` (Kuratowski
`pair_in`), the `wtype.rs` proof pattern. Nothing else.

**Non-vacuity:** `acc(A,∅) = A`; a reflexive point (`⟨x,x⟩ ∈ R`) is not in
`acc`; over `empty::two_cycle`-style data, nothing is.

**Size / files:** ~1 session; `acc.rs` + `acc/{set,intro,induction}.rs` +
`derived/tests/acc.rs`; one `lib.rs` line. Parallel-safe.

**Payoff:** gates the whole indexed-family/§5.3 chain (README item 2). Direct
corpus witnesses today: `118_accRecReduction` (12 gaps / 3 escapes),
`094_ruleK` (10 gaps, `Eq.rec` is_k), the ι diagnostic's remaining rows
(`Eq.rec`, `Acc.rec` — MEASUREMENTS.md:366), and `Eq` at 113 opaque-constant
typing misses on `init-prelude` (MEASUREMENTS.md:1013). None of those close
until this exists, and everything downstream of it (entries 7–8) queues behind
it.

---

## 2. n-ary `dprod_in_universe_pair` — the Π typing rule at a prefix — ~~READY~~ LANDED

> **Landed (2026-08-01).** Both files this entry names exist:
> `derived/src/ext/dprod_universe_n.rs` and
> `derived/src/universe/replacement_n.rs`.

**Builds:** the prefix-threaded port of `ext::dprod_in_universe_pair`
(`derived/src/ext/dprod_pi.rs`, unary, already done), in a new file
`derived/src/ext/dprod_universe_n.rs`:

```text
⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ ∀x. (x ∈ A → b(q⃗,x) ∈ U(c))) → dprod(q⃗,A) ∈ U(c))
```

for a fibre symbol `b` of arity `k+1`. Follow the input discipline of
`checker`'s `lam_in_dprod_n`: take `(b, img, img_ax, dprod, dprod_def)` as
symbols-plus-defining-axioms, verify them against the shapes rebuilt locally,
and refuse a foreign stack rather than describe it. Internally this is the
n-ary port of the three closure steps `dprod_pi.rs` composes —
`least_universe_replacement` over a prefixed fibre, `least_universe_union`,
`least_universe_bin_union` — so a prefixed `fibres_in`/image lemma
(new `derived/src/universe/replacement_n.rs` or local helpers) comes with it.

**Why needed:** `ty_pi` is the largest single typing-rule hole in the ledger:
**2903** Π-into-`Type` sites on `init-prelude` and 187 on the tutorials
(MEASUREMENTS.md:1224), and "the other 92% want `dprod_in_universe`'s n-ary
port and cumulativity" (MEASUREMENTS.md:1175); `checker/src/tg.rs:6642`
records `Pi — needs dprod_in_universe, whose n-ary port does not exist` as a
counted decline. The unary form is the rare case: a dependent Π whose body
mentions only its own binder arises **11 times** on `init-prelude`
(tg.rs, "The n-ary dependent product" note) — the n-ary form *is* the path.

**Dependencies / reuse:** `ext/dprod_pi.rs` as the k=0 blueprint;
`universe::{least_universe_replacement, least_universe_union,
least_universe_bin_union}` (all exist since the transitivity clause);
`funcs::Apply`. Include the thin cumulativity lift (entry 4) as a named
consumer in the header, not as a dependency.

**Size / files:** 1–2 sessions; `ext/dprod_universe_n.rs`
(+ `universe/replacement_n.rs` if the image lemma doesn't thread cleanly),
one hub line in `ext.rs`; tests in `derived/tests/ext.rs` or a new
`tests/dprod_n.rs`. Parallel-safe: the later one-clause `ty_pi` consumer in
`tg.rs` is **not** part of this entry (tg.rs is in flight).

**Payoff:** the biggest measured, closable typing population on the board
(5269 `ty_pi` sites total on `init-prelude`, of which 2903 are definitely
into `Type`; only 83 derive today). Even discounted by the "conditional
certificates convert only where nothing below admits" rule, this is the
`has_type` rule with the most sites behind it.

---

## 3. Universe closure under `+` (binary sum) — ~~READY~~ LANDED

> **Landed (2026-08-01).** `derived/src/sums/in_universe.rs` exists.

**Builds:** in a new file `derived/src/sums/in_universe.rs`:

```text
⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a + b) ∈ U(c))       [sum_in_universe]
```

`a + b` is `({0}×a) ∪ ({1}×b)`: unfold `sum_def`, then product closure
(via `funspace::product_subset_pow_pow` + `pow`/`sub` closure, or
`Level`-style `product`), tag singletons by `least_universe_pairing` at `∅`,
finish with `least_universe_bin_union`.

**Why needed:** MEASUREMENTS.md:1524–1529 names it first of the three things
`⟦List α⟧ ∈ ⟦Type 0⟧` needs ("closure of `U₁` under `+` … from `sum_def` as
in `NatMem`"); every §5.2 carrier is a W-type over a **tag sum**, so the
general inductive-in-universe chain (the `cumul::Chain` analogue for the
`inductive/` compiler's carriers, once that lands) pays this toll per
declaration shape.

**Dependencies / reuse:** `sums::sum_def`, `universe::{least_universe_pairing,
least_universe_bin_union}`, `funspace` product closure. All exist.

**Size / files:** ~half a session; one file, one hub line in `sums.rs`, tests
appended to `derived/tests/sums.rs`. Parallel-safe.

**Payoff:** small on its own (MEASUREMENTS.md:1536–1540 prices the full
List-at-`Type 0` bundle at "between one and a few dozen gaps" and calls it
"the wrong next afternoon") — but it is the reusable third of that bundle and
a prerequisite for any parameterised carrier's universe membership. Cheap
enough that the payoff-per-cost is still good.

---

## 4. Tower cumulativity: the lift `Uₙ ⊆ Uₙ₊₁`, exported — ~~READY~~ LANDED

> **Landed (2026-08-01).** `derived/src/tower/cumulative.rs` exists.

**Builds:** in a new file `derived/src/tower/cumulative.rs`:

```text
⊢ ∀x. (x ∈ Uₙ → x ∈ Uₙ₊₁)          for each built level    [Level::lift]
```

This is nearly free — `Level::mem_below` (`Uₙ ∈ Uₙ₊₁`) into
`Level::transitive` — plus the `U₀ → U₁` base case (`0, 1 ∈ U(ω)` from the
subset clause and pairing). The content is the *export*: a named,
instantiable lemma per level pair, so a consumer can lift a membership
`i` levels without recomposing the chain each time.

**Why needed:** MEASUREMENTS.md:1175 pairs it with entry 2 ("want
`dprod_in_universe`'s n-ary port **and cumulativity**") — Π lands in
`Sort max(u,v)` while its base and fibres arrive at `Sort u` / `Sort v`, so
both memberships must be lifted to the max before entry 2 applies. The thesis
uses exactly `Uₙ ⊆ Uₙ′` for `ulift`'s soundness clause (thesis.txt:2284),
which is also the *only* thing `ulift`'s typing will ever need, since
`⟦ulift α⟧ = ⟦α⟧` (thesis.txt:2106) — no other ulift work exists.

**Dependencies / reuse:** `tower::Level` fields only.

**Size / files:** well under half a session; one file + one hub line in
`tower.rs`, tests in `derived/tests/tower.rs`. Parallel-safe. Could be folded
into entry 2's dispatch if agents are scarce.

---

## 5. `‖α‖` — propositional truncation as a conditional singleton — ~~READY~~ LANDED

> **Landed (2026-08-01).** `derived/src/prop/trunc.rs` exists. Note that this
> also retires the entry's own "Verified missing: … no third conditional
> singleton exists" — `trunc.rs` describes itself as the third one, so that
> justification is spent, not merely stale.

**Builds:** in a new file `derived/src/prop/trunc.rs` (one hub line in
`prop.rs`):

```text
trunc(A) := [∃x. x ∈ A]        one conditional_singleton instance

⊢ ∀A ∀x. (x ∈ A → • ∈ trunc(A))                             [trunc_intro]
⊢ ∀A. (• ∈ trunc(A) → ∃x. x ∈ A)                            [trunc_elim]
⊢ ∀A. trunc(A) ⊆ 1     and the subsingleton property        [trunc_prop]
```

**Why needed:** thesis.txt:2109 (`⟦‖α‖⟧ = [⟦α⟧ ≠ ∅]`; `⟦|e|⟧ = •` and the
eliminator interpret to `•`, so the *only* construction is the set);
thesis.txt:1696 lists `‖·‖` in the menagerie and thesis.txt:1813–1815 makes
it the reduction target of every Prop-valued recursive inductive, and thesis.txt:1900 lists it among the eight menagerie
types that are "indeed sufficient to cover all Lean-definable inductive
types". It is the last cheap menagerie member not built (`⊥`, `Σ`, `+`, `W`,
`=`-as-subsingleton, `π₁/π₂` all exist; `ulift` needs nothing — see entry 4).
Verified missing: `prop.rs`'s header says `Eq` and `And` "are then two
instances" and no third exists.

**Dependencies / reuse:** `prop::conditional_singleton` and its lemma family —
this is a third instance, exactly like `eq_set`/`and_set`.

**Non-vacuity:** `trunc(1) = 1` and `trunc(0) = 0` (both polarities), via
`cond_true`/`cond_false`.

**Size / files:** ~half a session, one file + tests in
`derived/tests/prop.rs`. Parallel-safe (prop/ is not in flight).

**Payoff:** no gap row cites it *today* — stated honestly — but the Prop-valued
inductive interpretation (`Or`, `Exists`, …) cannot be wired without it, and
`Or.inl`/`Or.inr` are 16-each among `init-prelude`'s escape-probe heads
(MEASUREMENTS.md:809). Buy it now because it is two hundred lines and on the
§5.2-for-Prop critical path.

---

## 6. Quotients: equivalence closure, `A/∼`, `mk`, `sound`, `lift` — ~~READY~~ LANDED / MID-BUILD

> **In the tree (2026-08-01).** `derived/src/quot/` exists with `eqv`,
> `classes`, `lift`, `compat`, `witness` and an `apparatus`/`shared` pair —
> i.e. the entry's whole shape. An agent held these files while this note was
> written, so treat completeness as unconfirmed and read the code, not this
> entry.

**Builds:** new files `derived/src/quot.rs` (hub) + `derived/src/quot/`:

```text
eqv(A,R) := ⋂ { E ∈ 𝒫(prod(A,A)) : refl_A(E) ∧ sym(E) ∧ trans(E) ∧ R|_A ⊆ E }
class(A,R,x) := { y ∈ A : ⟨x,y⟩ ∈ eqv(A,R) }
quot(A,R)    := { class(A,R,x) : x ∈ A }                    (Replacement)

⊢ x ∈ A → class(x) ∈ quot                                   [mk_mem]
⊢ (⟨a,b⟩ ∈ R ∧ a,b ∈ A) → class(a) = class(b)               [q_sound]
lift: the function on quot with app(lift(f), class(x)) = app(f,x),
      under the compatibility hypothesis ∀x∀y. (⟨x,y⟩ ∈ eqv → app(f,x) = app(f,y))
```

The least-equivalence-relation-by-intersection is the same idiom as `wtype`
and entry 1 — no transitive-closure recursion needed. `lift` is a Replacement
over `quot` whose single-valuedness is exactly the compatibility hypothesis.

**Why needed:** thesis.txt:2131–2139 gives the interpretation clauses
(`⟦α/R⟧ = ⟦α⟧/∼` for `∼` the equivalence closure of `R̄`, `⟦mk x⟧ = [x]∼`,
`⟦lift f h⟧([x]∼) = ⟦f⟧(x)`; `sound`/`propext` interpret to `•`). Corpus:
`124_quotLiftReduction` (9 gaps at the `[1]` default) and
`125_quotIndReduction` (8), both explicitly recorded as reducing "through a
step this backend cannot justify (`Quot.lift`)" (MEASUREMENTS.md:343–345).

**Dependencies / reuse:** `funcs::{separation_full, coll}`, `pairs`,
`funspace`, `prop` for the `Prop`-valued `sound`. Independent of entries 1–5.

**Size / files:** 1–2 sessions; `quot/{eqv,classes,lift}.rs` +
`derived/tests/quot.rs`; one `lib.rs` line. Parallel-safe (the checker's
`Quot` wiring is later, separate work).

**Payoff:** 17 tutorial gaps directly cited, plus it is the whole of Lean's
quotient primitive — one of the few remaining language features with **no**
derived-side story at all.

---

## 7. `rec_acc` — the accessibility recursor — **DONE** (2026-08-01)

Built as `derived/src/rec_acc.rs` (hub) + `derived/src/rec_acc/{cval,ih,base,
attempt,agree,union,is_attempt,extend,total,package,witness,apparatus}.rs`,
with `derived/tests/rec_acc.rs` (11 tests). `RecAcc::over` is the entry point.
The union-of-attempts route went through unchanged; the estimate held (~4 400
lines of module code against `wrec` + `wrec_extend` + `wrec_total`'s ~3 400).
Five findings worth not re-deriving:

* **Only `step_typed` survives as a hypothesis**, and only on `totality`,
  `rec_funspace`, `iota` and `pack_iota`. There is **no analogue of
  `closed(A,B,u)`** — the entry's "no bound and no universe" judgement, made
  for the carrier, holds for the recursor too, and for the same reason:
  `acc(A,R) ⊆ A`, so `𝒫(prod(acc(A,R),T))` exists outright. Agreement,
  `sv(accrec)`, `accrec ∈ Att` and the *guarded* ι rule are all unconditional,
  where every corresponding `wrec` theorem carries `closed`.
* **The proof-indexed abstractions need no new symbol.** `h ∈ [φ] ↦ v` is
  `prod([φ], {v})`, a term over the existing `Product`, so the thesis's two
  `↦`s cost one Replacement between them (`ih`) and the outer packaging costs
  *zero* — `pack` is `ih` at the relation `acc(A,R) × {•}`.
* **Guard the `cval` premises by `h ∈ c`, never by `φ`.** `cval_ext` and
  `cval_bound` ask for `u = v` / `v ∈ t` only where the proposition is
  inhabited. That is what makes the whole module free of any case analysis on
  a proposition: off the relation the conditional value is empty and the
  obligations vanish. Stating them unguarded would be false; stating them as
  `¬φ ∨ …` would need a split at every use.
* **`sv` of the one-point extension needs no case split**, because
  `iota_on_domain` forces the old value to *be* `V`. The `wrec_extend` lesson
  transferred exactly; four cases collapse to three.
* **`ih_app` is the lemma that gives ι content**:
  `⊢ ∀g ∀A ∀R ∀x ∀y. ((y ∈ A ∧ ⟨y,x⟩ ∈ R) → app(app(ih(g,A,R,x),y),•) = app(g,y))`,
  unconditional. Without it ι is a true statement about an opaque third
  argument. It is also exactly what a backend needs, since Lean's minor premise
  applies its induction hypothesis to `y` and to a proof of `r y x`.

`RECURSOR-DESIGN.md` does **not** subsume this: the general recursor is `wrec`
at the carrier machine's data with a packed step, and `acc` has no tags, no
fibres and no bound. What did transfer is §3.2's `pow_prod` superset trick —
`step_typed` quantifies its induction-hypothesis slot over
`𝒫(prod(A, 𝒫(prod(1,T))))`, not over a function space. Original entry follows.

**Builds:** the §6.2.2 recursor (thesis.txt:2160–2166): `F` on `acc(A,R)`
with `F(x) = e(x)(•)(y ∈ A ↦ (h ∈ [⟨y,x⟩ ∈ R] ↦ F(y)))`, by
union-of-attempts along `R` — the ordinal-free construction `wrec`
(`derived/src/wrec*.rs`) already demonstrates for `W`, with `acc_induction`
playing W2's role in agreement/totality, and a `step_typed`-style carried
hypothesis (expect the same correction `INDUCTIVES.md` records for `wrec`:
totality is not free, the step must be typed into `T`).

**Why needed:** same citations as entry 1 — §5.3 sends every subsingleton
eliminator (including `Eq.rec`, i.e. `094_ruleK` and every `is_k` reduction)
through `rec_acc`.

**Dependencies:** entry 1; the `wrec`/`wrec_extend`/`wrec_total` pattern.
**Before dispatching, read `RECURSOR-DESIGN.md`** (being written now) and
confirm the general-recursor design does not subsume or re-shape this; the
thesis keeps `rec_acc` a separate object from `rec_W`, so a collision is
unlikely but must be checked, not assumed.

**Size:** 2–3 sessions (the `wnat_rec` precedent: ~1050 lines, 7 tests).
New files `acc/rec*.rs` only.

---

## 8. §5.3 subsingleton elimination, §5.2 `good`/indexed carriers — ~~BLOCKED~~ LANDED

Entry 7 (`rec_acc`) is **no longer a blocker** — it landed 2026-08-01, with
`ih_app` and `pack_iota` as the two facts a §5.3 translation would consume.
*(This read "Still blocked on the in-flight §5.2 carrier compiler
(`derived/src/inductive/`) and on the recursor/ι wiring. Do not dispatch." **Both
are built.** §5.2's `good`: `derived/src/inductive/family/good.rs`, wired at
`mini/src/zoneb.rs::build_indexed`. §5.3's subsingleton carrier:
`derived/src/inductive/family/{le,le_rec,le_prop,le_prop_rec,le_prop_fields,le_index}.rs`,
wired at `mini/src/class_s.rs` and `mini/src/class_s_ix.rs`. `is_k`/`Eq.rec`:
`mini/src/convert.rs` and `mini/src/recursor.rs`, and `094_ruleK` certifies.)*

One fact worth recording so it is not re-derived: `good`'s base
case needs `Eq`'s *elimination* at the set level, and that already exists —
`prop::cond_elim` (`• ∈ [φ] → φ`) plus the kernel's Leibniz rule; and
`⟦rec₌ e b h⟧ = ⟦e⟧` (thesis.txt:2124) makes `Eq`'s eliminator the *identity*
on interpretations, so no "Eq recursor construction" should ever be built —
what `Eq.rec` needs is `rec_acc` for the K-like rule and a checker clause,
nothing more.

## 9. A universe closed under W-types at a universe parameter — ~~BLOCKED~~ LANDED, by a route this entry ruled out

**Refuted on both grounds it rested on, 2026-08-05.** `derived/src/wpath/`
proves `W(A,B,u) ∈ U(d)` at an arbitrary fibre family — no ordinals, no
condition on the fibres — by coding each tree as its set of labelled finite
paths and handing that to `cantor::image_in_universe`; and the `⋃`-closure
obstruction is gone (`universe::universe_union_closed`,
`funspace::product_in_universe` and the rest are proved, `derived/src/recursion.rs`).
The entry's own advice — "send an agent to write a note, not code" — was
therefore wrong, and the way past it was neither of the two routes it compared.
See DECISIONS.md 2026-08-05 "Infinitary branching is wired" and SCOPING.md §14.
What follows is the entry as written.

`README.md` remaining-work item 3. Not dispatchable as a construction: the
checked route dies on `⋃`-closure, the thesis's route is a rank/cofinality
argument (thesis.txt:2144–2153) this project has avoided, and `INDUCTIVES.md`
("A decision for the human") has a standing owner-level question — replace
`ax_tarski` with the Grothendieck universe axiom — that would change the
answer entirely. The honest sub-piece, if one is wanted as a *design spike*
rather than a construction: whether `cantor::image_in_universe` (regularity,
already derived) can bound `ran(f)` for `f ∈ fs(B,u)`, `B ∈ u` — the
`cf(λ) > |B(a)|` step. **The `is_universe(u)` half of that sub-piece is
closed**: `universe::least_universe_is_universe` proves `⊢ ∀x. is_universe(U(x))`
as of 2026-08-05, so `image_in_universe` applies at `U(x)` directly. What it
still wants is the *member of `u` surjecting onto the target*, which is the work
and which the universe supplies none of. Send an agent to *write a note*, not
code.

---

## 10. `cumul` at `finord(m)` fibres — ~~the blocker on task #26 step two~~ LANDED 2026-08-01

*(**Landed as `derived/src/cumul/finord.rs`**, which exports `finord_is_explicit`
and `bnd_finord` and names this entry's purpose in its own header; `Fin⁺`
carries `bnd(B(a))` directly and `cumul.rs:252–253` no longer resolves to the
`Fin` definition. Route (a), this entry's preferred one, is the one taken. The
**payoff** claimed below is dead for a different reason: the cutover it would
unblock never happened, because the consumer moved to `mini/`, which never had
the three recognisers. `checker/src/tg.rs` still has `enum_arity`, `nat_shape`,
`list_shape` and `RecBottom::{Enum,Nat,List}`, dispatched ahead of
`RecBottom::General`.)*

**Builds:** a `derived::cumul` chain that accepts a W-type whose fibres are
`finord(m) = Sum_m(1,…,1)` rather than members of `ω`. As written,
`cumul.rs:252–253` demanded `B(a) ∈ ω` **on the nose**, and the general
carrier's fibres are `finord(m)`, which is not a von Neumann numeral — the
recorded `finord(1) ≠ 1` trap (`isum/symbols.rs:246`).

**Why needed:** it is the *only* thing standing between the checker and task
#26 **step two**, the cutover of `Bool`/`N`/`Unit`/`Empty` from the
hand-written stacks to `derived::inductive`'s general carrier. Step one has
landed (`WIRING-DESIGN.md` §13); the general path is wired *after* the three
recognisers and cannot replace them, because doing so would silently lose the
four `⟦T⟧ ∈ ⟦Type 0⟧` theorems (`ind_ty_u1`, `tg.rs`) that `cumul` supplies —
a regression no amount of new coverage pays for. Nothing else blocks the
cutover.

**Two routes, in preference order:**

(a) generalise the `Fin`/`bounded` step to fibres *equinumerous* to a member
    of `ω` — or, directly, prove `bnd(finord(m))` by the same finite
    induction, since `bounded_at` is stated per `k` and its proof walks the
    elements, so a `finord` variant is plausibly the same induction over
    `Inj_j(•)` members. **Argued from the statement shape, not from
    `bounded.rs`'s internals** — the first job is to read them and say whether
    it transfers.

(b) failing that, entry 3 (`sums::sum_in_universe`) plus a `finord`-aware
    restatement, or an equinumerosity layer — which is a session-scale
    detour rather than an afternoon.

**Dependencies / reuse:** `cumul::{Chain, bounded}`, `isum::finord`,
`inductive::Fibre`. All exist.

**Size / files:** unknown until (a) is read; an afternoon if it transfers, a
session if it does not. `derived/`-only, parallel-safe with checker work.

**Payoff:** unblocks the deletion of `enums.rs`, `wnat.rs`, `wlist.rs`,
`wnat_rec.rs`, `wlist_rec.rs`, `wbool_rec.rs`, `twopoint.rs` and
`wlist_fun.rs` — one construction in place of eight — and with them the three
shape recognisers and three `RecBottom` arms in `tg.rs`.

---

## Checked and rejected — do not spend an agent on these

- **`ulift`** — no construction at all: `⟦ulift α⟧ = ⟦α⟧`, `⟦↑e⟧ = ⟦↓e⟧ = ⟦e⟧`
  (thesis.txt:2106–2108). Its typing needs only entry 4's lift.
- **Typing proofs for `propext` / `Classical.choice` / `Quot.sound`** — they
  head **zero** typing obligations on `init-prelude` (MEASUREMENTS.md:1009–1016).
- **The ω-recursion theorem / ω-tower completion** — off the critical path
  since the transitivity clause landed; `INDUCTIVES.md` ("Does `N` need the
  ω-tower? No — measured") explicitly warns against restarting it.
- **Recursor uniqueness (`define` over `define_abbrev`)** — recorded optional;
  nothing downstream is blocked on it (INDUCTIVES.md state table).
- **A two-recursive-argument recursor by hand** — in the in-flight general
  recursor/ι design's scope; building it now duplicates. Note that the corpus
  witnesses are `Lean.ParserDescr.{binary, sepBy, sepBy1}` in `init-prelude`,
  not any tutorial file.

  This entry named `116_rtreeRecReduction` until 2026-08-01, and both halves of
  that were wrong. `116` is **not** the two-recursive-argument shape —
  `RTree.node` has `numFields: 1` and `RTree` is exported `isReflexive: true`,
  so its recursive argument is function-typed (`children : Bool → RTree`). The
  shape distinction is right and still worth having.

  *(The correction then said function-typed recursive arguments "are
  **declined** by the general design (`RECURSOR-DESIGN.md` §7.9), not covered by
  it", so `116`'s "ι gaps stay open until the `Σ(z::γ)` fibre translation
  exists". **That is dead**: RECURSOR-DESIGN §7 item 9 retracts the decline by
  name, `CtorSpec::with_rec_doms` carries `γ` as a telescope, the fibre summand
  **is** `Σ(z::γ)`, and `116` derives with no export on `good/tutorial`
  stopping. Note the citation form too — RECURSOR-DESIGN's §7 is a flat
  numbered list, so "§7.9" there means its ninth item.)*
- **`ty_proj` / projection typing, `ctor_rules` keying** — in flight in
  `tg.rs`.
- **The rest of the List-at-`Type 0` bundle** (conditional `Fin(1+α, fam(α))`
  + the `tg.rs` clause) — measured at one-to-a-few-dozen gaps and called "the
  wrong next afternoon" (MEASUREMENTS.md:1536–1540); only its reusable part
  (entry 3) is worth doing now.
- **CSB / `is_universe(U(x))` inaccessibility** — **done**, 2026-08-05
  (`derived/src/csb`, `universe::least_universe_is_universe`), and the entry's
  original judgement stands: it unlocked nothing downstream, because the closure
  properties it was once meant to unlock were refutable pre-`C₁` and are now
  derived directly (INDUCTIVES.md, "Where the bound comes from — corrected").
  What it *did* cost is a third of what the estimate said — Knaster–Tarski, one
  Separation, no `ω`-recursion; see DECISIONS.md 2026-08-05.

## Not assessed

- Mutual and nested inductives (the thesis treats neither: `thesis.txt:902`
  says only that they "can all be encoded using regular inductives". This item
  used to cite "§5.2's `Σ`-packing of mutuals"; §5.2 has no mutual clause, and
  its Σ-packing at 1795–1797 packs a constructor's *non-recursive argument*):
  deliberately out of every current scope; no measurement exists to size them.
- Primitive `ℕ`/`String` literals: shelved by owner decision (QUESTIONS.md).
- Whether `sigma/dsum.rs` needs an η rule (`⟨π₁x, π₂x⟩ = x` at a Σ-member
  rather than at a literal pair) for §5.2's indexed translation — check when
  entry 8 unblocks.
