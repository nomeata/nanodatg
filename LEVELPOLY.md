# Level-polymorphism in the target — design and exploration record

**Branch exploration** (`explore/level-poly-target`), commissioned by the owner:
instead of handling only ground level instantiation, quantify over the level as
an element of **ω** in the target theory, so an assumption `a : Type u` becomes
`⟦a⟧ ∈ srt(u⁺)` with `u` a bound variable of the set theory, and the Prop/Type
split becomes an if-then-else **inside the target term**.

## Verdict, first

**No mathematical obstruction was found; the set theory supports the design in
full.** The verdict rests on constructions *built and kernel-checked* on this
branch (§3), not on argument alone: the level vocabulary lives in ω (`max` is
binary union, `imax` is one conditional), the universe tower is internalised
as a set function of a variable rung (the recursion theorem at `G := U(·)`),
and the centrepiece — Π-formation at `imax` with the Prop/Type split as an
if-then-else **inside the target term**, exactly the conditional the owner
predicted — is one theorem at fully variable levels whose two branches
provably compute to the correct ground facts. A prototype seam in the `tg`
backend (§4) interprets and certifies variable-level sorts end to end behind
a flag, at +0.24% instructions, with today's suites green in both flag
states.

What separates this branch from a shipping variant is engineering volume in
`checker/`/`mini/` — the ground-σ assumption is load-bearing in the
translation layer's keying and clause dispatch — and that volume is mapped in
§5, with what was prototyped named as prototyped and what is unmeasured named
as unmeasured. Nothing in it is blocked on mathematics.

Two claims in the commissioning brief are **refuted** by the tree as it stands,
and both make the design *easier* than briefed:

1. *"`is_universe(U(c))` is NOT available"* — *stale.* It is
   `derived::universe::least_universe_is_universe`, proved 2026-08-05 via
   Cantor–Schröder–Bernstein (see `DECISIONS.md` that date). Universe-closure
   lemmas therefore instantiate at `u := srt(n)` for a *variable* nonzero `n`
   directly; the `bound.rs` transfer-through-the-intersection detour is not
   needed for this design.
2. *"The tower is ω-high and branching must therefore be finite" as a possible
   conflict with quantified levels* — the 2026-08-05 "Infinitary branching is
   wired" entry supersedes the finiteness decision (the `wpath` route), and in
   any case that constraint is about *fibre* size of W-types, an axis
   orthogonal to the level index. A quantified level never touches it.

## 1. The design

### 1.1 Levels become ω-terms

A level expression `ℓ` over parameters `u₁…uₖ` is interpreted as a term `ℓ̂` of
the set theory with free variables `u₁…uₖ`, under the hypotheses `uᵢ ∈ ω`:

```text
0̂        = ∅
(succ ℓ)̂ = succ(ℓ̂)               — derived::recursion's succ, n ∪ {n}
(max ℓ ℓ')̂  = ℓ̂ ∪ ℓ̂'             — von Neumann max IS binary union
(imax ℓ ℓ')̂ = ite0(ℓ̂', ∅, ℓ̂ ∪ ℓ̂')  — the if-then-else, on "ℓ̂' = 0"
ûᵢ       = the free variable uᵢ
```

`ite0(g,a,b)` is the conditional term former (§3.1): `a` if `g = ∅`, else `b`.
Note `max` needs no conditional at all — for naturals `max(m,n) = m ∪ n` on the
nose — and `imax` needs exactly one, which is the conditional the owner
predicted. Closure (`m ∪ n ∈ ω`) is a corollary of trichotomy on ω (§3.2).

### 1.2 Sorts become one internal function of the level

Today `⟦Sort ·⟧` is a *meta-level* map: rung `n` is a Rust `usize` and the term
`U(U(…U(ω)))` is built by iterating in Rust (`derived/src/tower.rs` is explicit
that "no set-theoretic recursion happens and no recursion theorem is needed").
The quantified design internalises it. `derived::recursion::recursion` — the
recursion theorem along ω, already complete — instantiated at the step
`G := U(·)` (the least-universe symbol) and base `c := ω` yields a function
*set* `lvl` with

```text
app(lvl, ∅) = ω          app(lvl, succ n) = U(app(lvl, n))   (n ∈ ω)
```

so `app(lvl, n̄) = Uₙ` for every numeral `n̄ ≥ 1` — the existing tower's rungs,
now indexed by a *variable*. Then

```text
srt(n) := ite0(n, U₀, app(lvl, n))        ⟦Sort ℓ⟧ := srt(ℓ̂)
```

with `U₀ = {0,1}` (Prop) the one discontinuity, carried by the same `ite0`.
The seed `c := ω` (not `U₀`) preserves the 2026-07-xx countermodel decision
that `⟦Type 0⟧ = U(ω)`, not `U(U₀)`: `srt(1̄) = app(lvl, succ ∅) = U(ω)`.

Ground compatibility: at every numeral the new terms *provably equal* the old
rung terms, by computing `ite0` (`succ_ne_zero`) and unfolding R4/R5. So the
quantified interpretation is a conservative refinement of today's, and a
hybrid checker (ground σ where scheduled, quantified where not) is coherent.

### 1.3 The facts at a variable rung

All of today's per-rung closure facts (`Rung::…`) lift to one theorem each,
quantified over the rung (§3.3–3.4):

```text
⊢ ∀n∈ω. ¬(n = ∅) → is_universe(srt(n))          — R5 + least_universe_is_universe
⊢ ∀n∈ω. srt(n) ∈ srt(succ n)                     — sort-in-sort (Lean's Sort ℓ : Sort ℓ+1)
⊢ ∀n∈ω. ∀m. m ∈ n → srt(m) ⊆ srt(n)              — cumulativity along ∈
⊢ ∀m,n∈ω. m ⊆ n → srt(m) ⊆ srt(n)                — cumulativity along ≤ ( = ⊆)
⊢ ∀n∈ω. ω ∈ srt(succ n)                          — the size fact, at a variable rung
```

and the closure clauses (`fs`, `dprod`, pairing, `⋃`, replacement, `app`) come
from `is_universe(srt(n))` + the existing `∀u. is_universe(u) → …` lemmas —
no transfer machinery, because refuted-claim (1) above.

### 1.4 The Prop/Type split moves into the term

Carneiro's §6.2 interpretation is *clause-split*: `app`/`λ`/`∀` each interpret
one way when the relevant sort is 0 and another when it is ≥ 1, and the
proof-split language (§6.1) resolves the split **before** interpretation using
a ground valuation. At a variable level the split is unresolvable at
translation time — `Clause::Undet` in `checker/src/tg.rs` is precisely this —
and the quantified design interprets it as the conditional:

```text
⟦∀x:α. β⟧ = ite0(ℓ̂_β,  [∀a ∈ ⟦α⟧. • ∈ ⟦β⟧(a)],  Π_{a∈⟦α⟧}⟦β⟧(a))
⟦λx:α. e⟧ = ite0(ŝ,     •,                        (a ∈ ⟦α⟧ ↦ ⟦e⟧(a)))
⟦e₁ e₂⟧   = ite0(ŝ₁,    •,                        app(⟦e₁⟧, ⟦e₂⟧))
```

where `ŝ` is the (ω-valued) sort of the term, available because the checker
infers types. The **uniform typing invariant** is what makes this compose:

> `Γ̂, u⃗ ∈ ω ⊢ ⟦e⟧ ∈ ⟦α⟧` for `e : α`, in *both* clauses —

in the Prop case `⟦α⟧ ⊆ {•}` and `⟦e⟧ = •`, so `• ∈ ⟦α⟧` *is* the soundness
statement; in the Type case it is the membership the checker already tracks.
The thesis keeps these as two judgment shapes; the conditional merges them
into one, which is what lets a rule at an undetermined level be *one theorem*
with an `ite0` in it rather than a gap.

Rules about these terms are proved by **case analysis on the guard**
(`g = ∅ ∨ ¬(g = ∅)`, classical), one split per *distinct undetermined level
zero-test* in the obligation — in practice 1–2, bounded by the declaration's
level arity, never by the term size. §3.5 is the flagship instance: Π-formation
at `imax`, both branches, one theorem.

### 1.5 Level definitional equality

The checker decides level equality with its own algebra (`eq_antisymm`); the
target must *prove* every equality the checker uses (`canon_level` maps a
class to one representative — under quantification the representative's
interpretation must be provably equal to each member's). The kit:

* lattice laws of `∪` on ω — from trichotomy (§3.2): commutativity,
  associativity, idempotence, absorption are all set-algebra facts, free of
  case analysis; `m ∪ n ∈ ω` and `m ⊆ n → m ∪ n = n` need trichotomy;
* `imax` laws — one `ite0` case split each;
* the case principle `∀n∈ω. n = ∅ ∨ ∃m∈ω. n = succ m` — mirrors the
  checker's "cases on a parameter" step in `leq`.

A certified mirror of the checker's `leq` decision procedure (recursing
exactly where the Rust decision procedure recurses, emitting these lemmas) is
the clean architecture; it is **designed, not built** (§5).

### 1.6 Constants: the `(name, levels)` key becomes application

Today `⟦f.{σ}⟧` is a **0-ary symbol per ground instantiation**, and every
table in the translation layer is keyed `(name, interpreted levels)` to keep
the instantiations apart. Under quantification a declaration with `k` level
parameters becomes **one `k`-ary symbol** `f̂` with one defining axiom

```text
⊢ ∀u⃗. f̂(u⃗) = ⟦body⟧(u⃗)         — kernel `define`/`define_abbrev`, params = u⃗
```

and a use of `f` at levels `ℓ⃗` interprets as `f̂(ℓ̂⃗)` — the keying *becomes*
application, `⟦f.{σ}⟧` is the instance `f̂(σ̄)`, and the per-σ symbol tables
(`Shared::const_syms`, mini's `ConstKey`-keyed stores) collapse one dimension.
This is the target-side economy the ground schedule cannot have: two
instantiations of one declaration are two `ax_inst`s of one axiom, not two
translations.

### 1.7 Ten candidate obstructions, attacked

Each of the following was checked against the tree rather than assumed; none
survives as an obstruction. (1) `imax` under `simplify` — mirrored by
`ite0` + `succ_ne_zero`. (2) Per-σ inductive tables — the branch decider is
already per-declaration (`zoneb`'s eliminator trichotomy), and
`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.2 shows class-(T) carriers are
level-free; only the membership theorem quantifies. (3) The recursor's
eliminating universe — becomes one more quantified variable; it is precisely
today's `Undet` residue. (4) Proof irrelevance — lives in the `v = 0` branch
of the case split, where `u0_subsingleton` applies as today. (5) Non-numeral
ground levels — the target *evaluates*; no syntactic numeral matching.
(6) The fibre-size wall — orthogonal axis, and superseded anyway (`wpath`).
(7) Completeness of the level-defeq mirror — the checker's `leq` case-splits
on a parameter being `0`/`succ`; the target mirrors it with `Order::cases`,
and every structural step is a `⊆`-lattice fact. (8) `DeclUniverse` at a
variable rung — the underlying lemmas are `∀c`-shaped over `U(c)` and
instantiate at `c := app(lvl, n)`; no new mathematics, one more quantifier.
(9) Prop-clause skeleton symbols (`chi`) — level-free formulas; `ite0`
composes them unchanged. (10) Universe closure at a variable rung — the
tower's `∀c` closure theorems apply at `c := app(lvl, n)` directly; not even
`is_universe` is needed, though it is available (§ verdict).

## 2. Why quantification is sound where the schedule was — the two-line argument

The ground schedule is sound because Lean's own semantics quantifies levels at
the meta level (thesis §6.1: a valuation `v : UV → ℕ`). The quantified design
proves `⊢ ∀u⃗ ∈ ω. φ(u⃗)`; each ground σ is one `ax_inst` at numerals, and §1.2's
ground-compatibility theorems rewrite the instance to exactly the theorem the
ground path builds today. So everything the schedule can certify, the
quantified theorem certifies *after instantiation* — the quantified form is
strictly stronger, and the per-σ blowup (MONOMORPH.md measures 1.158× on
Mathlib, tail 118 copies in category theory) is what it removes.

## 3. What is built on this branch (all in `derived/src/levels/`, tested)

Every item is a real construction over the LCF kernel — no axioms added,
`kernel/` untouched — with its own file, interface header, and integration
test pinning shapes at independently rebuilt formulas. Status markers: [x]
landed and green, [ ] not landed.

* [x] **`ite0`** (`ite0.rs`, tests `levels_ite0.rs`) — the conditional term
  former `ite0(g,a,b)`, by `∃!`-definitional extension, classical cases on
  `g = ∅`. Exports `when_zero`/`when_nonzero`. Both computation directions
  pinned (`ite0(∅,a,b) = a`; `ite0(succ ∅,a,b) = b` through `succ_ne_zero`).
* [x] **`order`** (`order.rs`, tests `levels_order.rs`) — trichotomy on ω
  (previously recorded as "this development does not have" it,
  `cumul/stages.rs:34`), the zero/succ case principle, `⊆ ↔ (∈ ∨ =)`, and
  `max = ∪`: closure in ω, upper bound (unconditional), absorption.
  Non-vacuity: `1 ∪ 2 = 2` forced through Regularity.
* [x] **`utower`** (`utower.rs`, tests `levels_utower.rs`) — the recursion theorem at `G := U(·)`,
  seed ω: `app(lvl,0) = ω`, `∀n∈ω. app(lvl,succ n) = U(app(lvl,n))`,
  `is_universe` at every successor rung, the climb `lvl(n) ∈ lvl(succ n)`,
  `ω ∈ lvl(succ n)`, and the numeral bridges to the existing tower's rungs.
* [x] **`srt`** (`srt.rs`, tests `levels_srt.rs`) — `srt(n) = ite0(n, U₀,
  app(lvl,n))`: `⟦Sort ·⟧` as one term function of a *variable* level;
  `at_zero`/`at_succ` computation, sort-in-sort (`Sort ℓ : Sort (ℓ+1)` at a
  variable rung), cumulativity one rung up (`step_sub`) and along `∈`
  (`mono_mem`), `ω`- and `U₀`-membership at every successor rung.
  Non-vacuity: `srt(0) ≠ srt(1)` — Prop and Type 0 stay distinct.
* [x] **`apparatus`** (`apparatus.rs`, tests `levels_apparatus.rs`) — the
  `LevelPoly` bundle over one tower chain, plus `imax_in_omega`:
  `ite0(v, ∅, u ∪ v) ∈ ω` for `u, v ∈ ω`, closing ω-membership of every
  level expression's interpretation by structural recursion.
* [x] **`rules`** (`rules.rs`, tests `levels_rules.rs`) — the flagship:

  ```text
  ⊢ ∀u ∀v ∀A ∀b. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧ b ∈ srt(v)))
                    → ite0(v, cnd(A,b), fs(A,b)) ∈ srt(ite0(v, ∅, u ∪ v)))
  ```

  Π-formation at `imax(u,v)`, the Prop/Type split as `ite0` **inside the
  target term**, one theorem, both branches — Carneiro's two `Π` clauses
  (§6.2) merged by the level conditional at fully variable levels. The tests
  instantiate the *one* theorem at `(0,0,1,1)` and compute it down to
  `⊢ cnd(1,1) ∈ U₀` (the Prop clause), and at `(1,1,ω,ω)` down to
  `⊢ fs(ω,ω) ∈ U(ω)` (the Type clause, `U(ω)` pinned as the existing
  tower's rung 1) — both branches of the conditional compute to the right
  ground facts. Plus `mono_sub` (cumulativity along `⊆`), `fun_type_demo`
  (`α : Type u ⊢ (α → α) : Type u` at a *variable* `u` — the owner's
  "`a : Type u` becomes `⟦a⟧ ∈ U(u)`" sentence as a kernel theorem), and
  `punit_demo` (`⊢ ∀u∈ω. 1 ∈ srt(u)` — the `PUnit`-carrier membership as
  **one** theorem where the ground checker mints one symbol per σ, §1.6).

## 4. The checker prototype, and what it costs

### 4.1 The wedge

Behind `NANODATG_LEVELPOLY=1` (default off; flag unset ⇒ bit-identical
behaviour), the `tg` backend on this branch:

* builds the `LevelPoly` apparatus once per thread, over the prelude's own
  tower chain (`Shared::lp`);
* interprets a `Sort ℓ` whose **canonical level still mentions a parameter**
  as `srt(ℓ̂)` — the ω-vocabulary of §1.1/§1.2 — instead of the axiom-free
  `sort(⟦ℓ⟧)` symbol (`interp_sort_poly`); ground levels are untouched, and
  dispatch stays on the canonical representative, so `⟦·⟧` remains a function
  and the two vocabularies cannot collide (different head symbols);
* discharges the sort-typing obligation `⟦Sort ℓ⟧ ∈ ⟦Sort (ℓ+1)⟧` at a
  variable `ℓ` (`ty_sort_poly`): `Srt::sort_in_sort` instantiated at `ℓ̂`,
  composed with the structural ω-membership evidence
  `⊢ ⋀(uᵢ ∈ ω) → ℓ̂ ∈ ω` (`omega_level`, using `max_in_omega` /
  `imax_in_omega` / `succ`-closure at each constructor), as a **conditional
  certificate** whose assumptions are exactly the `uᵢ ∈ ω` facts — carried by
  the existing `hyps` channel of `TgTyping::Derived`, counted by the existing
  conditional-typing counters, and never silently dropped.

What the wedge deliberately does **not** do: the `ite0`-Π clause
(`interp_pi_undet` still mints the axiom-free symbol — the mathematics for
its replacement is `levels::rules`, the wiring is §5.3 step 3), constants,
inductives, and the store schema. It is a prototype of the *seam*, named as
such.

### 4.2 Measurements (init-prelude, `nanoda_bin` debug + `tg`, this branch)

* **Flag off is bit-for-bit today's behaviour**: the full `tg` suite (72 + 6
  + 28 tests) passes with the wedge code in the tree and the flag unset.
* **Cost**: 227,607,726,315 instructions flag-off vs 228,162,815,272 flag-on
  — **+0.24%**, which prices the whole apparatus construction (trichotomy,
  recursion theorem at `U`, `srt` laws) *plus* the per-level evidence
  building. Single runs of a deterministic counter (`perf stat -e
  instructions`); wall time not quoted, per project rule.
* **The honest surprise — the old encoding was already discharging the
  variable sort rule, vacuously.** Under the opaque arm,
  `⟦Sort (u+1)⟧ = U(⟦Sort u⟧)` by the `Succ` climb, so the obligation
  `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` is literally `x ∈ U(x)` at an axiom-free
  constant, and `domain_premise` discharged it **unconditionally** — true of
  *any set whatsoever*, carrying no fact connecting `⟦Sort u⟧@σ(u):=0` to
  `U₀` and no ω-structure. The report diff shows exactly this trade:
  `by x ∈ U(x)` drops 1399 → 1345 (−54) and those 54 sites move to
  conditional certificates under real `u ∈ ω` assumptions or (3 sites, where
  canonicalisation reshaped `succ ℓ`) to counted misses; escaped assumptions
  rise 2138 → 2156 (+18) because the prototype has no declaration-boundary
  quantifier yet (§5.3 step 5 is where `gen` would turn them into
  `∀u∈ω`-theorems); TOTAL gaps 15423 → 15443 (+20). **The counter regression
  is the semantic upgrade made visible**: a certificate that used to say
  "some set is in its least universe" now says "for every natural `u`, rung
  `u` is in rung `u+1`", and the counters price the fact that nothing above
  the seam consumes the stronger form yet.
* Acceptance is unchanged in both directions (exit 0, same declarations).

## 5. The checker-side map

A full census of where "levels are ground at translation time" is load-bearing
was taken on this branch (2026-08-09, against `f1925ae`). The short form, with
the integration consequence for each. "Checker" is `nanoda_lib`'s `tg`
backend; "mini" is the evidence-threaded port that is the live driver.

### 5.1 Where groundness is assumed

| site | what assumes it | quantified replacement |
|---|---|---|
| `checker/src/instantiations.rs` (511 lines; `Inst = Vec<u32>`, `DEFAULT_LEVELS`, the published `SCHEDULE`) | the whole pre-pass exists to answer "which ground σ must this declaration be checked at" | retired as the *checking* driver; survives (optionally) as the instantiation engine that specialises the final `∀u⃗∈ω` theorems to the σ a downstream consumer asks about |
| `TcCtx::sigma` / `under_sigma` (`checker/src/util.rs:304,354`; 5 call sites) | substitute numerals, then `simplify` | substitution becomes identity; `interp_level`'s `Param` arm becomes the *main* arm |
| `interp_sort`'s `_` arm (`tg.rs:3853`) | `Max`/`IMax`/`Param` fall to an opaque `sort(t)` with no facts | `srt(ℓ̂)` (§1.2) with the §1.3 fact kit |
| `Clause::{Prop,Type,Undet}` dispatch (`tg.rs:9583 clause_after`, `tc.rs:1043 infer_pi`) | reads the level shape after σ; `Undet` = axiom-free symbol + `TyGap::PiUndet` | `Undet` becomes the `ite0` clause (§1.4); the 12 residual `PiUndet` typing sites on `init-prelude` are the first live beneficiaries |
| const/ind/ctor tables keyed `(name, interpreted levels)` (`Shared::*`, `TgBackend::{ind_syms, ctor_rules, …}`, mini's `ConstKey = (Name, Vec<u32>)`) | one entry per ground instantiation | one entry per *declaration*, keyed by canonical level *expressions*; ground keys become the numeral instances |
| mini `ground::eval` → `Gap::SymbolicLevel` (~40 mint sites), `Interp::sort(n: u32)`, `CUMUL_HEIGHT = 8` | a symbolic level is a sanctioned dead end; the tower is consulted at a `usize` | the dead end becomes the entry point; `srt(ℓ̂)` has no height limit (`CUMUL_HEIGHT` retires — the internal ladder is ω-long) |
| `zoneb`'s `provably_nonzero` / eliminator trichotomy | already **per-declaration, not per-σ** — the module doc insists on it | unchanged: this is the one part of the pipeline that is already level-polymorphic in spirit |

### 5.2 The hypothesis mechanism already exists

The design needs `uᵢ ∈ ω` carried as an assumption through a translation.
**Neither crate needs a new mechanism:**

* mini: `Scopes::assume(φ)` (`mini/src/scope.rs:273`) takes an *arbitrary*
  formula into the kernel sequent's Γ and discharges it with
  `discharge_assumption` — the second of exactly two `Thm::assume` sites in
  the program, built for `derived::acc`'s induction hypothesis. `u ∈ ω` is one
  more such formula, opened at declaration entry and discharged (then
  `gen`-quantified) at declaration exit.
* checker: the formula-level antecedent lists (`CondEq`, the `assms`
  threading of `has_type_local`, `guard_and_generalise`) carry membership
  formulas; `Formula::mem(u, ω)` is one more.

The kernel is untouched either way; sequent hypotheses were priced for exactly
this shape (`kernel/src/thm.rs`, the `mk_union` note citing
THREADING-CENSUS §2).

### 5.3 Integration order (mini first)

1. **Level interpretation**: params to fresh free variables under `u ∈ ω`
   (via `Scopes::assume`); `0̂/succ/max/imax` per §1.1; `Interp::sort` takes
   the ω-term instead of a `u32`.
2. **`ConstKey` widens** from `(Name, Vec<u32>)` to `(Name, CanonLevels)`
   where `CanonLevels` is the canonicalised level-expression vector (the
   `canon_level` discipline, unchanged in spirit). Every `IndApparatus` table
   inherits the key change mechanically.
3. **Clause dispatch grows the third clause** (`ite0`), consuming
   `levels::rules`.
4. **Level defeq mirror** (§1.5): a certified `leq` that follows the checker's
   own decision procedure, splitting on `n = ∅ ∨ ∃m∈ω. n = succ m` where the
   procedure splits on a parameter.
5. **The schedule retires** from the checking loop (`Ledger::run`'s per-σ
   loop flattens to per-declaration); ground demands become `ax_inst`s of the
   stored `∀`-theorems at numeral terms plus the §1.2 bridge equations.

Steps 1–2 are mechanical but wide (every `ConstKey` consumer). Steps 3–4 are
where the new mathematics is consumed. Step 5 is the payoff. **None of this is
done on this branch beyond the prototype named in §3**; the volume estimate,
not any mathematical step, is what stands between this branch and a variant
passing today's suites.

## 6. What is deliberately not claimed

Named so nothing is hidden behind the verdict. As of this branch:

* **The checking pipeline is not rewritten.** The suites this project measures
  against (`ci/check.sh`'s eleven-plus steps, the arena corpus, mini-vs-nanoda)
  run exactly as on master — that is asserted, not improved. The quantified
  design is *demonstrated* at the `derived/` layer and prototyped at one
  checker seam (§3–§4), not shipped end to end. §5.3's steps 1–5 are the
  remaining volume, and every one of them is ordinary plumbing whose shape is
  known; none is blocked on mathematics.
* **The dependent product at a variable rung** is stated here for the
  non-dependent `fs` form; the dependent `dprod` form goes through
  `Tower::family`'s per-fibre scheme the same way and is not derived on this
  branch.
* **The certified level-`leq` mirror (§1.5)** is designed, not built.
* **The store schema for `∀u⃗∈ω` certificates** (what replaces
  `(name, Vec<u32>)`-keyed sealed theorems) is designed (§1.6, §5.3), not
  built.
* **Performance of quantified checking is unmeasured**, because the pipeline
  is not rewritten; what is measured is the construction cost of the new
  apparatus and the invariance of today's counters (§4). No claim is made
  either way about end-to-end speed; the owner has said a regression would
  not stop this line, and nothing here needed that allowance yet.
