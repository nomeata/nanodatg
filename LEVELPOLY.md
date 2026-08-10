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

### 1.8 The three commissioned attacks, answered

* **Is the `_` arm of `interp_sort` the only groundness assumption?** No —
  and this was established before designing, not assumed. The instantiation
  schedule, `under_sigma`, the `(name, levels)` keying (checker tables and
  mini's `ConstKey`), `IndApparatus`' per-σ stores, the `Clause` dispatch,
  mini's `ground::eval`/`Gap::SymbolicLevel`/`CUMUL_HEIGHT`, and the
  recursor's eliminating universe each assume groundness **independently**
  (§5.1 is the full census with locations). The `_` arm is merely where the
  assumption is *visible* as an opaque term; the wedge (§4) relieves exactly
  that seam and no other, which is why §5.3 lists five more steps.
* **Is ω the right index set, given the ω-high tower and the finite-branching
  record?** Yes, and the two are different axes. The 2026-08-05
  finite-branching entry is about W-type *fibre* cardinality, was superseded
  the same day ("Infinitary branching is wired", the `wpath` route), and is
  untouched by anything here. The level index is a different quantity: a
  Lean level under a valuation *is* a natural number (thesis §6.1,
  `v : UV → ℕ`), the tower's rungs are indexed by exactly ω, and quantifying
  `u ∈ ω` ranges over precisely the instantiations the ground schedule
  enumerates one by one. An index set larger than ω would quantify over
  rungs no Lean level can name.
* **Is `Prop` handled by the same conditional?** Yes — that is what
  `srt(n) = ite0(n, U₀, app(lvl,n))` *is*. `U₀` is not `U(anything)` and is
  not a rung of the internal ladder (the ladder's base is `ω`, preserving
  the `U(ω)`-not-`U(U₀)` countermodel decision); the `Zero ↦ pre.u0()`
  discontinuity lives inside the same `ite0` that carries `imax`, and every
  variable-level theorem splits on `n = ∅` exactly where the ground code's
  Rust `if` used to decide. Proof irrelevance stays a fact about `U₀`
  (`u0_subsingleton`), available in the zero branch of any such split; the
  tests pin `srt(0) = U₀`, `srt(0) ≠ srt(1)`, and the flagship's zero branch
  computing into `U₀`.

### 1.9 `is_universe(U(c))`, and what this construction actually spends

The commissioning brief's constraint — "`is_universe(U(c))` is NOT available"
(`derived/src/bound.rs:51`) — is **stale**: `least_universe_is_universe`
proves `⊢ ∀x. is_universe(U(x))` outright (CSB; `DECISIONS.md` 2026-08-05,
"the recursion theorem was never on the path"). `bound.rs`'s header has not
been corrected on master and still states the old constraint.

The construction here barely needs it either way. The closure facts the
flagship spends go through the tower's **`∀c`-shaped transfer theorems**
(`Tower::funspace`, `u0_in`, `transitive` — the transfer-through-the-
intersection route the brief pointed at) instantiated at the *variable-rung
term* `c := app(lvl, q)`, which is exactly the `bound.rs` precedent one
quantifier deeper. `is_universe` appears once, as `UTower::step_is_universe`
(exported for future consumers, e.g. closure lemmas stated over
`is_universe(u)` rather than over `U(c)`); nothing load-bearing on this
branch rests on it, so the design would have survived even under the stale
constraint.

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
* [x] **`pi_rules`** (`pi_rules.rs`, tests `levels_pi_rules.rs`) — the
  **dependent** twin of the flagship, per fibre family `b` of arity `k+1`
  (the `DProdN` stack):

  ```text
  ⊢ ∀q⃗ ∀u ∀v ∀A. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧ ∀x.(x∈A → b(q⃗,x) ∈ srt(v))))
                    → ite0(v, cndd(q⃗,A), dprod(q⃗,A)) ∈ srt(ite0(v, ∅, u ∪ v)))
  ```

  — §6's "dependent `dprod` form", now derived. Assembly, not new
  mathematics: `ext::dprod_in_universe_pair_n` is already quantified over its
  universe seed and instantiates at `c := app(lvl,q)` exactly where the
  flagship instantiates `Tower::funspace`; the one new move is the fibres
  conjunct raised pointwise under its binder (a fresh-witness `syl` chain
  closed by `prim::gen`). The tests pin the shape at prefix length 2 with
  distinct probes (prefix dropping *and* reordering both fail), compute both
  branches to ground facts (`cndd(ω,∅) ∈ U₀`; `dprod(ω,∅) ∈ U(ω)`, the rung
  pinned as the tower's `U₁`), and refuse a pair theorem for a foreign fibre
  stack; two mutations were run red and reverted (recorded in the test
  header).

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

Since the rebase the wedge also carries the step-5 kit (§5.3 status note):
parameters as free variables in the ω-vocabulary, `f̂(u⃗)`-shaped constant and
inductive abbreviations, the declaration-boundary quantifier and its
quantified store with two consumers. What the wedge still deliberately does
**not** do: the `ite0`-Π clause (`interp_pi_undet` still mints the axiom-free
symbol — the mathematics for its replacement is `levels::rules`, the wiring
is §5.3 step 3), the nests at a symbolic eliminating universe (§5.4 blocker
2), and the cross-vocabulary bridges (§5.4 blocker 3). It is a prototype of
the *seam*, named as such.

### 4.2 Measurements (init-prelude, `nanoda_bin` debug + `tg`, this branch, rebased onto master `a7b0c6a`)

The branch was rebased onto master `a7b0c6a` (2026-08-10; `dprod`-Π,
`EnvCore`, expression-derived binder levels, `LocalKey`), and every number in
this section was re-taken at that base. Master's own flag-off baseline moved
to **15542** total gaps / **2257** escapes; the flag-on deltas survived the
rebase exactly.

* **Flag off is bit-for-bit today's behaviour**: the full `tg` suite passes
  with the wedge code in the tree and the flag unset, and the whole
  init-prelude report is **diff-identical** to the pre-wedge tree's except
  for the three new declaration-ledger rows (quantified-store rows), each
  printed and each **0**.
* **Cost** (`perf stat -e instructions`, single runs, init-prelude, debug +
  `tg`, at this head): flag off **222.18 G**, flag on **221.67 G** — the
  wedge's former +0.24% became **−0.23%** at the rebased base: the −54
  vacuous discharges and −29 `ty_pi` derivations it declines to build now
  outweigh the apparatus construction. The staged deletion
  (`NANODATG_NO_SCHEDULE=1`, flag on) runs **142.79 G**, −36% — one
  interpretation pass per declaration instead of one per scheduled σ — which
  is the size of the prize the deletion is holding.
* **The honest surprise — the old encoding was already discharging the
  variable sort rule, vacuously.** Under the opaque arm,
  `⟦Sort (u+1)⟧ = U(⟦Sort u⟧)` by the `Succ` climb, so the obligation
  `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` is literally `x ∈ U(x)` at an axiom-free
  constant, and `domain_premise` discharged it **unconditionally** — true of
  *any set whatsoever*, carrying no fact connecting `⟦Sort u⟧@σ(u):=0` to
  `U₀` and no ω-structure. The report diff shows exactly this trade:
  `by x ∈ U(x)` drops 1399 → 1345 (−54) and those 54 sites move to
  conditional certificates under real `u ∈ ω` assumptions or (3 sites, where
  canonicalisation reshaped `succ ℓ`) to counted misses; `ty_pi` derivations
  fall 823 → 794, the same loss one rule downstream (a `srt`-shaped domain is
  not `U`-shaped); derived typings fall 14387 → 14003 with +352 more
  conditional. TOTAL gaps 15542 → 15562 (+20); escapes 2257 → 2275 (+18);
  `eq_cache` 260 → 262 (+2). **The counter regression is the semantic
  upgrade made visible**, and the +20 decomposes exactly: +18 conditional
  certificate copies the checker consumed as answers or parked in caches
  (the escape ledger's deliberate over-report direction), +2 union edges
  that used to carry a vacuous unconditional certificate and now carry none.
* **The step-5 hypothesis this section used to state is refuted by
  measurement.** This section previously said the declaration-boundary
  quantifier "is where `gen` would turn them into `∀u∈ω`-theorems" and §4.2
  attributed the +18 to its absence. The quantifier is now **built** (§5.3
  step 5 status below) and it fires **zero** times on the scheduled prelude
  — necessarily: under the σ-schedule a definition is only ever interpreted
  at ground levels, so no value typing ever reaches the boundary with a
  `u ∈ ω` antecedent. The +18 are definitional-equality certificate copies,
  not declaration typings, and no boundary rule sees them. What retires the
  +20 is the schedule deletion itself (at which point the sort rule's
  conditional form becomes the only form and the ratchet is re-derived), not
  a wedge-stage fix; until then the flag-on ι-gate failure stands, at +20,
  fully decomposed above.
* The wedge's k-ary constants (§1.6, built): a body mentioning ω-vocabulary
  parameter variables costs 20 inductive translations at their own
  parameters flag-on (283 → 263; `…declined: the parameter nest refused`
  +60, `…declined: field type depends on a recursive field` +20): the
  general nest's `define_abbrev(xs = params)` refuses a free level variable.
  That is census row 7's work item made precise, and the same change is what
  turns the *staged* state's canonicity declines 16/11/6 → 1/1/0 (§5.4).
* Acceptance is unchanged in both directions and in the staged state
  (exit 0, same declarations) — as it must be: σ selects which set a `Π` is
  interpreted as, never whether a declaration is accepted (`TcCtx::sigma`).
* **Gate results at head.** Flag **off**: the whole `tg` suite passes.
  Flag **on**: everything passes except
  `the_general_iota_rule_computes_on_the_prelude`, the total-gap/escape
  ratchet, tripping on precisely the +20/+18 this section decomposes.
* The arena corpus gate ran green on this branch
  (`152 matched, 0 mismatched, 2 declined, 0 waived (of 154)` — the same two
  declines as master). `mini` never builds the `tg` backend (the
  feature-inert guard in `ci/check.sh` enforces it) and `derived`'s changes
  are purely additive modules, so the flag cannot reach the mini gates.

## 4.5 The branch invariant, in the owner's words

> "the whole idea there is to model lean's theory directly, without any
> monomorphication. **every lean term has one interpretation, with level
> parameters turned into elements of omega and interpreted as elements of our
> universe tower**"

Stated as the checkable property it is: **`⟦·⟧` is a function of the term
alone — no σ in any key, anywhere**, in either engine. Deleting the ground
level scheduling code is *how* the branch satisfies it; the invariant is what
says the deletion actually happened. Two built pieces are the invariant
showing through, and are the model for the rest, not demos: the
`f̂(u⃗)`-shaped abbreviations (a constant's interpretation as a function of
its level parameters, where the ground path mints a symbol per σ) and
`punit_demo` (one theorem where the ground path mints one fact per σ).

Consequences this section owns:

* **Mini is in scope** (owner's ruling, 2026-08-10): mini's schedule must
  go — `ground.rs`, the per-σ pair walk, `zoneb`'s pre-ensure, `dump.rs`'s
  schedule enumeration. `instantiations.rs`-as-mini's-pre-pass is **not** a
  legitimate end state on this branch. Where master's line routes mini to
  inductives only, that is *master's* design; this branch follows the
  sentence above, and a future port must treat mini's de-scheduling here as
  branch-specific.
* **`pairs` and `constEv` are denominated in σ** and lose their referent at
  the switchover — a per-σ count has no meaning when there is one
  interpretation per term. Their replacements, to be reported side by side
  at the switchover: `decls` (declarations walked), `declEv` (declarations
  whose one typing carries evidence — unconditional or `∀u⃗∈ω`-quantified,
  counted apart), and the unchanged `gapped`/`unsealed`. The per-σ counters
  are a measurement casualty of the same honest kind as the ι gate's 54
  vacuous certificates, and are to be *renamed, never silently re-based* —
  the `permissive but consistent` rule for counters.

## 5. The checker-side map

A full census of where "levels are ground at translation time" is load-bearing
was taken on this branch against `f1925ae` and **re-taken 2026-08-10 against
`a7b0c6a`** after the rebase; §5.4 adds the *measured* deletion rehearsal. The
short form, with the integration consequence for each. "Checker" is
`nanoda_lib`'s `tg` backend; "mini" is the evidence-threaded port that is the
live driver.

**What "the ground level scheduling code" is, precisely** (the deletion
target, named so it can be checked off):

* `checker/src/instantiations.rs` — **511 lines**: `Inst`, `DEFAULT_LEVELS`,
  `Instantiations::compute` (the worklist fixpoint), `publish`/
  `was_predicted` (the audit channel), `eval`.
* `checker/src/tc.rs` — the schedule driver: `check_declar_all`, the
  `schedule` parameter threading through `check_all_declars{,_serial,_par}`
  and the `publish(compute(...))` call (~45 lines), plus the `PropAt::Sigma`
  evidence-side reading.
* `checker/src/util.rs` — the σ plumbing: `TcCtx::sigma`, `set_sigma`,
  `nat_level`, `under_sigma` (~80 lines with their doc comments).
* `checker/src/tg.rs` — the σ reads: four `under_sigma` call sites
  (`canon_level`, `interp_level`, `audit_instantiation`, one sort-shape
  probe), `audit_instantiation` (24 lines), `inst_report` + `InstAudit`
  (~60 lines).
* `mini/src/ground.rs` — **141 lines** (`eval`, `numeral`, `ground_env`,
  `ground_levels`, `subst_ground`), plus `mini/src/convert.rs`'s
  `Instantiations::compute(ef)` and schedule field, `ledger.rs`'s per-σ pair
  walk, `zoneb`'s per-σ pre-ensure loop, and `dump.rs`'s
  schedule-enumeration reporting. **This half is mini's evidence
  architecture itself** — the (declaration, σ) pair is its unit of account
  (`pairs`, `constEv`, the dump's row identity) — and is load-bearing for a
  reason §5.3 steps 1–2 describe and this branch has not built. The checker
  half above is deletable once §5.4's three blockers close; the mini half is
  the remaining §5.3 volume, and `instantiations.rs` survives as mini's
  pre-pass either way until it does.

### 5.1 Where groundness is assumed

Re-taken 2026-08-10 at `a7b0c6a`. **The seven sites are still seven.** In
particular `a7b0c6a`'s expression-derived binder levels (`open_level`,
`dbj_level_counter`) are about *de Bruijn* levels — the binder-depth axis —
and touch none of the universe-level groundness below; no census row was
dissolved by the 32 master commits. What did change: the sort seam and the
`(name, levels)` keying now have their quantified halves **built** on this
branch (rows 3 and 5; §5.3 step-5 status), and the staged rehearsal (§5.4)
turned every row's cost from an estimate into a measurement.

| site | what assumes it | quantified replacement |
|---|---|---|
| `checker/src/instantiations.rs` (511 lines; `Inst = Vec<u32>`, `DEFAULT_LEVELS`, the published `SCHEDULE`) | the whole pre-pass exists to answer "which ground σ must this declaration be checked at" | retired as the *checking* driver; survives (optionally) as the instantiation engine that specialises the final `∀u⃗∈ω` theorems to the σ a downstream consumer asks about |
| `TcCtx::sigma` / `under_sigma` (`checker/src/util.rs:304,354`; 5 call sites) | substitute numerals, then `simplify` | substitution becomes identity; `interp_level`'s `Param` arm becomes the *main* arm |
| `interp_sort`'s `_` arm (`tg.rs:4128`) | `Max`/`IMax`/`Param` fall to an opaque `sort(t)` with no facts | `srt(ℓ̂)` (§1.2) with the §1.3 fact kit — **built** (the wedge), now over per-name free variables |
| `Clause::{Prop,Type,Undet}` dispatch (`tg.rs:10449 clause_after`, `tc.rs:1059 infer_pi`) | reads the level shape after σ; `Undet` = axiom-free symbol + `TyGap::PiUndet` | `Undet` becomes the `ite0` clause (§1.4); 12 residual `PiUndet` sites under σ, **2407 without it** (§5.4 blocker 1) |
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
where the new mathematics is consumed. Step 5 is the payoff.

**Step-5 status (2026-08-10, checker side): the boundary quantifier is
built.** Level parameters now interpret, in the ω-vocabulary, to kernel
**free variables** (`Shared::param_vars`, per name, exactly so `Thm::gen`
can close over them); constant and inductive abbreviations abstract over the
variables free in their bodies (§1.6's `f̂(u⃗)`, via `define_abbrev`'s prefix)
and hand back the defining equation at the generic point;
`store_declar_typing` quantifies a value typing whose every antecedent is
`uᵢ ∈ ω` into `⊢ ∀u⃗. ⋀(uᵢ∈ω) → ⟦c⟧ ∈ ⟦T⟧` (`store_poly_typing`), and
`ty_const`/`has_type_const` answer later uses from that store by re-opening
the implication at the generic point, the `uᵢ ∈ ω` assumptions riding the
caller's own antecedent channel (§5.2, exactly as predicted). The fixture
`checker/test_resources/LevelPoly` pins all of it in the staged state — four
declarations quantified, two uses answered, a different-parameter-name use
*missing* — with two mutations verified red (a one-parameter fixture stayed
green under the gen-order mutation; the two-parameter `mypair` atom is what
made it observable). On the **scheduled** prelude the quantifier fires zero
times, structurally: a definition under σ is only ever interpreted at ground
levels (§4.2). Its live population arrives with the deletion.

### 5.4 The deletion, rehearsed and measured — and what still blocks it

`NANODATG_NO_SCHEDULE=1` (the staging switch in `check_declar_all`,
committed on this branch, deleted together with the schedule at the end)
checks every declaration exactly once at its own universe parameters — the
schedule-deleted control flow, runnable today. On `init-prelude`, wedge on,
at this branch's head:

* **Acceptance is unchanged** (exit 0, same declarations) — in both flag
  states. The deletion cannot move a verdict; every movement below is
  evidence-side.
* The census halves: 2891 (declaration, σ) value pairs → 1645 declarations;
  typing obligations asked 39951 → 21569; TOTAL gaps 15562 → 10710; escapes
  2275 → 1465; derived kernel theorems 149934 → 87108.
* **Blocker 1 — the Π clause (step 3).** `no evidence: ty_pi_undet`
  12 → 2407; Π-under-neither-clause for a parameter reason 1588 → 6005. The
  undetermined clause is *rare under σ and structural without it*. The
  mathematics for the `ite0` clause is now **complete**: `levels::rules` for
  the constant-fibre/`fs` form and `levels::pi_rules` (§3) for the dependent
  `dprod` form at a variable rung — the derivation the deletion was waiting
  on, and it went through as assembly, with **no fundamental blocker**.
  Master's `⟦Π⟧` is a `dprod` at every codomain, so the wiring consumes one
  rule shape. The unbuilt half is that wiring, now mapped function by
  function (2026-08-10 reading):
  * **The guard level.** `clause_after` reaches the undetermined level at
    its `_ =>` arm and discards it; `Clause` carries no payload. The wired
    interp needs it, so a sibling walk (`undet_body_level`, mirroring
    `body_clause`/`clause_after` but returning the level) recomputes it at
    the Undet site, canonicalised through `canon_level` — the same
    representative discipline the sort seam uses. Only the
    `Undet::Param` flavour is addressable; `undet_unknown()` (the walk gave
    up — 10516 expressions staged) has no level in hand and keeps the
    opaque symbol.
  * **The term.** `ite0(v̂, chi(h⃗,A), dprod(h⃗,A))` via `self.mk` on the
    apparatus's `ite0` symbol so `parts` records it and congruence is
    generic. The two halves come from the *pure skeleton cores* —
    `pi_info`/`build_fibre` and `prop_info`/`build_cond` — **without** the
    per-site `pi_sites`/`prop_sites` registration (a new
    `undet_poly_sites` map carries `{level, sk, holes, dom}`); the old
    "must not share tables" warning on `interp_pi_undet` is about the
    opaque symbol and does not apply, since the halves *are* the clause
    terms the instantiations compute to.
  * **The rule.** Per skeleton: a `DProdN`-adapter over the checker fibre
    stack (`build_fibre`'s `b`/`img`/`dprod` are already
    `image_symbol_n`/`dprod_symbol_n`-shaped), `dprod_subset_funspace_n` +
    `least_universe_replacement_n` derived from its axioms,
    `dprod_in_universe_pair_n` assembled, then `levels::pi_rules::pi_rules`
    — whose constructor needs the full chain (`Rec`, `Ite0`, `Order`,
    `UTower`, `Srt`, `Rules`, `Tower`), so `LevelPoly` (apparatus) grows
    those fields plus a per-skeleton `PiRules` cache. `ty_pi`'s Undet arm
    then instantiates `pi_imax_dep` at `(h⃗, û, v̂, A)` with the
    `u ∈ ω`/`v ∈ ω` evidence from `omega_level`, conditional via the assms
    channel, boundary-quantified at declarations like every other level
    hypothesis.
  * **The measures.** `no evidence: ty_pi_undet` 2407 → toward 0 (staged);
    the `Undet::Param` expression population 6005; the "clauses never
    meet" functionality test and the pi-congruence Undet rows are the
    invariants to re-pin, with the congruence rows expected to *fall* (two
    wired Undet Πs of equal shape are equal terms).
* **Blocker 2 — ι and the nests at a symbolic eliminating universe.**
  **First slice built** (the ω-prefix, commit `b6d93fa`): `gen_ty_nest` and
  `gen_ctor_nest` thread the level variables free in their domains as
  leading arguments of every body symbol and graph — `lambda_n` and
  `beta_conditional_n` are arity-generic and needed no change — closing the
  60 "parameter nest refused" rows and, staged, building +281 constructor
  rules (5803 → 6084); pinned by the `037_prodType` staged fixture with its
  mutation run red. ι stays at 37 staged because the remaining sites are
  deeper, and they are two:
  * **2b — the `βⱼ` field abbreviations** (76 rows staged, now their own
    `Decline::LevelVar` reason — they were misattributed to the
    recursive-field label, whose guard is the same free-variable refusal):
    `βᵢ` has arity `np + i` by the `DeclSpec` well-formedness check
    (`derived/src/inductive/spec.rs:271`). **Adjudicated 2026-08-10 by a
    full read of `derived/inductive` and the consumption sites: route
    (ii) — the ω-variables ride as ordinary parameters, `np' = nw + np` —
    is feasible and strictly smaller than route (i), because the machine
    is parameter-agnostic in the strong sense: it never states one fact
    *about* a parameter.** The evidence: parameters are only ever a
    leading argument prefix and a leading `∀`-prefix (`carrier.rs:239` and
    twelve sibling sites); `Ctor::mem`'s hypotheses are exactly the field
    typings with *no* `p ∈ ?` atom (`ctor.rs:37-41`); the recursor
    schemas' assumption list is complete and parameter-free
    (`recursor.rs:47-52`); `rec_doms` follows the same `np + i`
    convention and the checker never populates it; the spec is
    caller-relative so mini's `DeclSpec::new(3,…)`/`(np,…)` calls are
    untouched, and the one shared `np`-keyed cache
    (`Machine::telescopes`) cannot collide because `Telescope::new`
    checks arity. The change is checker-only: `GenInd` gains an ordered
    `omega: Vec<FreeVar>` (declaration level-parameter order, computed
    from the decl's `levels` before any interp, checked a superset of the
    bodies' ω-vars), `walk_spec`'s `xs` and `gen_ind_build`'s `np'` use
    it, and eleven derived-facing argument lists take `wts` as a leading
    prefix (`ty_of` at 7592/7857, `beta_ax`/`mem` at 7945/7966, and
    `fire_general`'s `ps` consumers). `nest_spine_eq` needs **no change**
    — its ω-leading instantiation split is already built and
    load-bearing. The one hazard: `omega_prefix` sorts by variable id
    while the declaration list is in level-parameter order; mixing the
    orders fails closed (both mismatch sites are literal-guarded), and
    the fix is the single-list discipline — `gi.omega` replaces both
    `omega_prefix` calls. Route (i) wins only self-documentation (a
    type-level split `derived/` could enforce) and would matter if a
    future theorem were genuinely conditional on `wᵢ ∈ ω`; today nothing
    is.
    **Built, same day.** `GenInd::omega`/`SpecWalk::omega`
    (declaration-ordered, `omega_of_levels` under the ambient σ — so a
    scheduled ground pass computes the empty list and is byte-identical,
    verified), `np' = nw + np` at `DeclSpec::new`, the eleven prefixes,
    `gen_minor_typed` taking the Lean parameter count `lnp` separately
    from the derived-facing list, and the nullary fast path instantiating
    a `∀w⃗`-closed `Ctor::mem`. All 76 `LevelVar` rows closed; staged,
    declarations translated 283 → 315, constructor rules 6084 → 6224.
    Pinned by `route_ii_translates_a_type_valued_field_in_the_staged_state`
    (`057_typeWithTypeFieldPoly`, a `Type u`-valued field), mutation
    (empty ω-list) run red and reverted.
  * **2c — the recursor path**: **the `define_abbrev` half is built** —
    `RecNest::omega` from the *recursor's* levels (they lead with the
    eliminating universe, which `gi.omega` alone would miss), the ω-prefix
    on every level's body symbol and graph, `nest_chain` and
    `nest_replay`/`nest_agrees` leading with the ω-terms. Staged ι
    37 → 43, "no curried interpretation" 429 → 399. **The eliminating
    universe itself remains**: the `T`-policy rows
    (`…declined (recursor): T-policy 2/3` 1104 → 600 staged) want the
    motive's target at a *variable* universe, which is blocker 1's `srt`
    machinery consumed on the recursor side — the two close together, not
    in sequence.
  The staged drift rows (15/9/6) are the *documented, expected* per-backend
  head drift (`Dt::IndDrift`'s own doc), population-scaled now that these
  nests build at all; a share-only-when-shared-named gating was tried and
  measured to change nothing, so it is not in the tree.
* **Blocker 3 — evidence consumption across the vocabulary switch.**
  Typing obligations discharged 5373 → 1624; declaration-typing store
  answers 1329 → 117. A ground use's interpretation (tower rungs) and a
  quantified theorem's instance (`srt(n̄)`) are provably equal, **not
  identical**, so every literal-formula guard misses across the boundary.
  **The §4.5 invariant resolves this by dissolution, not by bridges**: when
  `⟦Sort ℓ⟧ = srt(ℓ̂)` for *every* level — numerals included — there is one
  vocabulary and the boundary the guards miss across no longer exists. The
  tower-rung spelling retires from the interpretation entirely (it remains
  `derived/`'s internal business); `⟦Sort 1⟧` is `srt(succ ∅)`, whose facts
  (`at_zero`/`at_succ`/`sort_in_sort` at numerals, with the numerals'
  *unconditional* ω-membership) replace the vacuous `x ∈ U(x)` discharge
  with honest unconditional certificates. The §1.2 bridge equations are
  then needed only where a `derived` library theorem is stated over rung
  terms or `fs` (`fs_app_mem`, the machine's `Ctor::mem` carriers), a
  bounded, listable set of seams — not inside every formula. This is the
  switchover's actual content, and why it is **one commit that deletes and
  re-derives together**: unify `interp_sort` on `srt(·)`, retire the ground
  special case, re-point the sort-typing rules at the `Srt` kit, delete the
  schedule, and re-take every ratchet on the far side. This is also
  why the wedge could not be consumed incrementally: **§1.6's cross-level
  payoff needs the schedule gone, and the no-regression deletion needs
  blockers 1–2 closed first.**
* **Blocker 4 — mini** (§5.1's last row): its evidence pipeline is
  (declaration, σ)-shaped end to end, and none of §5.3 steps 1–2 is built.

The tg-suite rows that would go red under the deletion today are exactly the
blockers' rows: `fired ≥ 80` (reads 37), `stored ≥ 26` (reads 10),
`hit ≥ 1308` (reads 117), and the per-file zero-gap pins on polymorphic
tutorial declarations. Those are coverage losses, not honest-conditional
re-baselines, and they are why the schedule is still in the tree.

## 6. What is deliberately not claimed

Named so nothing is hidden behind the verdict. As of this branch:

* **The checking pipeline is not rewritten.** The suites this project measures
  against (`ci/check.sh`'s eleven-plus steps, the arena corpus, mini-vs-nanoda)
  run exactly as on master — that is asserted, not improved. The quantified
  design is *demonstrated* at the `derived/` layer and prototyped at one
  checker seam (§3–§4), not shipped end to end. §5.3's steps 1–5 are the
  remaining volume, and every one of them is ordinary plumbing whose shape is
  known; none is blocked on mathematics.
* **The dependent product at a variable rung is derived** (`levels::pi_rules`,
  §3) — via `dprod_in_universe_pair_n`'s `∀c` form at `c := app(lvl,q)`, not
  via `Tower::family` as this bullet used to predict. What is *not* built is
  its checker-side consumption: the interpretation of an Undet-`Π` as the
  `ite0` term and the typing rule that spends `pi_imax_dep` (§5.4 blocker 1's
  other half).
* **The certified level-`leq` mirror (§1.5)** is designed, not built.
* **The store schema for `∀u⃗∈ω` certificates** is built on the checker side
  (`Shared::declar_typings_poly`, §5.3 step-5 status) and pinned by fixture;
  its *cross-level* consumption (a ground use answered by `ax_inst` at a
  numeral plus the §1.2 bridges) is not built — §5.4 blocker 3 — and mini's
  side is untouched.
* **Performance of quantified checking is unmeasured**, because the pipeline
  is not rewritten; what is measured is the construction cost of the new
  apparatus and the invariance of today's counters (§4). No claim is made
  either way about end-to-end speed; the owner has said a regression would
  not stop this line, and nothing here needed that allowance yet.
