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
provably compute to the correct ground facts. A seam in the `tg` backend
(§4) interprets and certifies variable-level sorts behind a flag, and the
undetermined-`Π` clause it was built for now answers **1466 of 2407**
obligations in the schedule-deleted state with real conditional certificates
(§5.4 blocker 1). Flag off is bit-identical; both flag states have their
gate results recorded in §4.2.

What separates this branch from a shipping variant is engineering volume in
`checker/`/`mini/` — the ground-σ assumption is load-bearing in the
translation layer's keying and clause dispatch — and that volume is mapped in
§5, with what was prototyped named as prototyped and what is unmeasured named
as unmeasured. Nothing in it is blocked on mathematics.

**The switchover's first clause has now been run rather than argued.** With
`NANODATG_UNIFY_SORT=1`, `interp_sort` answers `srt(ℓ̂)` at *every* level,
numerals included — one vocabulary, the ground special case retired — and
both corpora are still accepted: `init-prelude` exit 0, arena
`152 matched, 0 mismatched, 2 declined, 0 waived`, at **+0.5 %** of
instructions. The design's central move is neither a soundness question nor a
performance one.

**What blocked the switchover turned out not to be about levels.** §5.5's
first clause required blockers 1–2 closed, measured by three tg-suite
ratchets. Partition-checked counters now attribute every one of them to a
level-independent cause: `iota: no curried interpretation` is 399 of 399 a
nullary-constructor gate and a shape gate, with all eighteen level-reachable
arms at zero and the same rows in all four flag/schedule states;
`stored` is 10 because 92.3 % of declarations have no value typing at all, at
the *same* rate the scheduled state has; `hit` is bounded by `stored`. Clause
1 is retired on that evidence, and what replaces it is clause 2 — the counter
correspondence — grown to cover `fired`/`stored`/`hit`, which are
σ-denominated too. The remaining work is named and sized in §5.5: ten
rung-shaped typing rules to re-point at the `Srt` kit (2511 firings), the
store's cross-level instantiation (483 sites, §1.6's other half, **not**
delivered by the vocabulary unification as §5.4 used to claim), and mini.

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
the clean architecture. Its **first slice is built** —
`derived::levels::leq` (§3) plus the checker-side recursion
`TgBackend::level_bridge`, carrying the one identity `imax(a,b) = b` when
`a ≤ b` and the `⊆` facts that discharge it. That slice was chosen by
measurement, not by design order: it is 72 % of what blocker 1 had left
(§5.4). The rest of the mirror — the strict order `succ(x) ⊆ b`, the
parameter case split, `max` reassociation — is still designed, not built, and
each missing arm is a counted row rather than a silent refusal.

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
* [x] **`leq`** (`leq.rs`, tests `levels_leq.rs`) — the certified `≤`-kit at
  the width the corpus demands: `∅ ⊆ x`, `x ⊆ x`, `succ(∅) ⊆ v` under
  `v ≠ ∅`, the two `⊆`-introductions for `∪` and `ite0`, and the flagship

  ```text
  ⊢ ∀u ∀v. (((u ∈ ω ∧ v ∈ ω) ∧ (¬(v = ∅) → u ⊆ v)) → ite0(v, ∅, u ∪ v) = v)
  ```

  — **`imax(u,v) = v` when `u ≤ v`**, the one identity the raw-versus-canon
  bridge spends (§5.4 blocker 1). `sub_refl` re-exports `cumul::subset_refl`
  and the absorption step reuses `order.rs`'s `union_absorb_one`, promoted to
  `pub(crate)`: one construction per fact. This is **not** §1.5's full
  certified `leq` mirror and the file's header says which arms are missing.
* [ ] **the full level-defeq mirror** (§1.5) — `leq.rs` is its first slice.
  Not built: `succ(x) ⊆ b` for `x ≠ ∅` (the strict order), the parameter case
  split against an unequal level, `max` reassociation. The checker counts
  every refusal by arm, so the next construction is named by the report.

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
  `tg`). Instructions, never wall time: this box is shared and wall time has
  been wrong by 2× from contention. Two heads, because the Undet-`Π` wiring
  (§5.4 blocker 1) moved every figure and the old ones must not be quoted:

  | state | at `0ab4ce7` (pre-wiring) | at this head |
  |---|---:|---:|
  | flag off, scheduled | 222.18 G | **222.75 G** |
  | flag on, scheduled | 221.67 G | **247.08 G** (+10.9 %) |
  | flag on, staged deletion | 142.79 G (−36 %) | **615.18 G** (+177 %) |
  | flag on, staged, **vocabulary unified** | — | **618.33 G** (+0.5 % on the row above) |

  The last row is the one that changes how the +177 % reads. Unifying
  `interp_sort` on `srt(·)` at *every* level — the switchover's central move,
  which changes every `⟦Sort ℓ⟧` in the program — costs **+0.5 %** (§5.5). The
  branch's cost is the Undet-`Π` clause and the level bridge; none of it is the
  quantified sort. A reader who assumed the design's central move was what made
  this branch slow would be wrong by two orders of magnitude.

  Flag off is unmoved (+0.26 %), as the bit-identity promise requires — the
  clause, the bridge and their counters are unreachable with the flag unset.
  Both flag-on states moved, and the honest reading is that **the deletion is
  no longer a saving at all**: it was −36 % before the `ite0` clause existed,
  −12.4 % once the clause was wired at 304 sites, and is +177 % now that the
  level bridge closes 1466. The work is real derivation the checker was
  previously not doing — 16073 `Π`s interpreted through `upi`, 494
  per-skeleton rule chains, 1466 conditional `pi_imax_dep` certificates and
  everything downstream that consuming them creates — and it is not overhead;
  but the "−36 % prize" is a stale number twice over and quoting it would be
  quoting a measurement of a checker that no longer exists. §5.4 blocker 1
  names the one identified reduction (deriving the level equation under the
  level-only antecedent so it can be shared across sites), untried.

  The scheduled state is untouched by the bridge: under σ all 12 `PiUndet`
  obligations land on `Π`s the interpretation never wired, so `pi_imax_dep`
  fires **zero** times and every bridge row reads 0. Its +10.9 % is the
  wiring's own (2119 `Π`s do take the `ite0` clause at interpretation), not
  this tranche's.
* **The honest surprise — the old encoding was already discharging the
  variable sort rule, vacuously.** Under the opaque arm,
  `⟦Sort (u+1)⟧ = U(⟦Sort u⟧)` by the `Succ` climb, so the obligation
  `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` is literally `x ∈ U(x)` at an axiom-free
  constant, and `domain_premise` discharged it **unconditionally** — true of
  *any set whatsoever*, carrying no fact connecting `⟦Sort u⟧@σ(u):=0` to
  `U₀` and no ω-structure. The report diff shows exactly this trade:
  `by x ∈ U(x)` drops 1399 → 1345 (−54) and those 54 sites move to
  conditional certificates under real `u ∈ ω` assumptions or (3 sites, where
  canonicalisation reshaped `succ ℓ`) to counted misses.

  **Re-measured at this head**, where the Undet-`Π` clause is wired and so
  changes the scheduled interpretation too: TOTAL gaps 15542 → **15568**
  (+26); escapes 2257 → **2263** (+6). The +26 decomposes exactly, and the
  rows are not the ones the pre-wiring wedge moved:

  | row | flag off | flag on | Δ |
  |---|---:|---:|---:|
  | escapes (`⟦arg⟧ ∈ ⟦binder domain⟧` at the boundary) | 2257 | 2263 | +6 |
  | pi congruence: two `Π`s of undetermined sort, differently shaped bodies | 59 | 69 | +10 |
  | lam congruence over an admitted premise | 179 | 184 | +5 |
  | lam congruence: the body certificate is not the graphs' pointwise equation | 19 | 24 | +5 |
  | `eq_cache` | 260 | 262 | +2 |
  | pi congruence over an admitted body premise | 1147 | 1146 | −1 |
  | pi congruence: the body certificate is not about the binder bodies | 33 | 32 | −1 |

  The +10 is new and is the wiring's own signature: a skeleton interpreted
  through `upi` on one side of a congruence and through the axiom-free symbol
  on the other is two differently-shaped bodies, and the row counts exactly
  that. **The counter regression is the semantic upgrade made visible**, but
  the earlier reading of it (+18 conditional certificate copies, +2 union
  edges) described the pre-wiring wedge and no longer holds; this table is
  what the flag-on state costs today.
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
* **Gate results at head.** Flag **off**: the whole `tg` suite passes — 113
  test binaries, 0 failures, re-run at this head with the decomposition, the
  bridge and `leq` in the tree. Flag **on**: the `tg_tutorial` gate binary is
  **34 passed, 1 failed** — the one failure is
  `the_general_iota_rule_computes_on_the_prelude`, on exactly the line the
  ratchet guards (`init-prelude: 15568 gaps, ratchet 15542`), i.e. the +26 the
  table above decomposes. That gate is
  **still red flag-on and is still deferred**, and the switchover must not
  inherit it: §5.4's condition is unchanged, and its cause has now moved (it
  is no longer the 18 certificate copies §4.2 used to attribute it to — the
  largest single row is the +10 congruence split between wired and opaque
  Undet `Π`s, which the switchover removes by making every Undet `Π` wired).
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
* `mini/src/ground.rs` (`numeral`, `ground_env`, `ground_levels`,
  `subst_ground`, and `eval`/`as_numeral`), plus `mini/src/convert.rs`'s
  `Instantiations::compute(ef)` and schedule field, `ledger.rs`'s per-σ pair
  walk, `zoneb`'s per-σ pre-ensure loop, and `dump.rs`'s
  schedule-enumeration reporting. **This half is mini's evidence
  architecture itself** — the (declaration, σ) pair is its unit of account
  (`pairs`, `constEv`, the dump's row identity) — and is load-bearing for a
  reason §5.3 steps 1–2 describe. **Its line count is the wrong unit and
  used to be quoted here as if it were the job**: `ground.rs` is 141 lines,
  and the de-scheduling is 40 of mini's 56 source files. See "Mini, sized" in
  §5.5 for the measurement and for which half is built (step 2) and which is
  not (step 1). The checker half above is deletable once §5.4's three
  blockers close; the mini half is the remaining §5.3 volume, and
  `instantiations.rs` survives as mini's pre-pass either way until it does.

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
| const/ind/ctor tables keyed `(name, interpreted levels)` (`Shared::*`, `TgBackend::{ind_syms, ctor_rules, …}`, mini's `ConstKey`) | one entry per ground instantiation | one entry per *declaration*, keyed by canonical level *expressions*; ground keys become the numeral instances. **Mini's half is built** — `ConstKey` is `(Name, Vec<Level>)`, canonicalised by `ground::key_levels` (§5.3 step-2 status) |
| mini `Checker::new` (`th: None`) → `Gap::SymbolicLevel` (132 production sites, 112 of them reading `c.interp().ok_or(…)`), `Interp::sort(n: u32)`, `CUMUL_HEIGHT = 8` | a symbolic level is a sanctioned dead end, so the declaration-shape zone has no `Interp` at all; the tower is consulted at a `usize` | **`Checker::poly`** — the dead end becomes the entry point, and the sites stop firing without being edited; `srt(ℓ̂)` has no height limit (`CUMUL_HEIGHT` retires — the internal ladder is ω-long) |
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

   **Step-1 status (2026-08-10): the vocabulary exists in mini, and nothing
   consumes it yet.** `mini/src/interp.rs` carries `LevelVar`
   (`(û, ⊢ u ∈ ω)` — the two travel together because neither is usable
   without the other), `Interp::levels` (a lazily built
   `derived::levels::apparatus::LevelPoly` over the *prelude's own* tower),
   `level_term` (§1.1, clause for clause), `level_in_omega`
   (`⊢ ℓ̂ ∈ ω`, one `mp` per former against `succ_closed` /
   `Order::max_in_omega` / `LevelPoly::imax_in_omega`), `sort_of`
   (**`⟦Sort ℓ⟧` at any level**) and `rung_bridge` (`⊢ srt(n̄) = Uₙ`,
   `Srt::rung_eq` checked against mini's own rung term rather than trusted).
   This is the predicted **second consumption of the checker's own
   construction**: mini imported `derived::levels` for the first time and
   wrote no mathematics.

   Two properties make it landable ahead of the switchover, and both are
   tested rather than argued. `sort_of` answers a numeral with `Interp::sort`
   **term for term** — `srt(n̄)` and `Uₙ` are provably equal and are not the
   same term, so spelling a ground rung the new way would move every ledger
   certificate for no gain. And the numeral branch **never builds the
   apparatus**, which matters beyond economy: `level_poly` declares symbols off
   the shared `Env`, so an apparatus built mid-run would renumber every symbol
   every later declaration mints. A ground run therefore mints exactly the
   symbols it did before, and the `ledger`/`evidence`/`untranslated` rows over
   all 91 tutorial exports are byte-identical.

   **What remains of step 1 is neither of the two columns §5.5 offered, and
   both counts were misleading — see the corrected decomposition there.** In
   one line: `.sort(` is 28 production sites, not 69, because that table
   counted fixtures; and the 132 production `Gap::SymbolicLevel` sites are not
   132 conversions but **112 consumers of one absent thing** — `Checker::new`
   sets `th: None`, so the declaration-shape zone has no `Interp` at all.

   **`Checker::poly` is that thing, and it is built.** `mini/src/kernel.rs`
   now has a third constructor beside `new` (acceptance only) and `threaded`
   ("the evidence-carrying pass, at one ground instantiation"): the
   evidence-carrying pass **at a declaration's own universe parameters**. It
   mints one kernel free variable per parameter, assumes `uᵢ ∈ ω` through
   `Scopes::assume`, and carries the resulting `LevelVars` on the thread;
   `Checker::discharge_levels` closes them innermost-first at declaration exit.
   §5.2's prediction that neither crate needs a new mechanism for this is
   confirmed — nothing was added to `scope.rs`, and `ci/check-mini-scope.sh`
   still finds `Thm::assume` spelled only there.

   The first §6.2 clause is converted with it. `infer_type`'s `Expr::Sort` arm
   gains a de-scheduled case: `⟦Sort ℓ⟧ = srt(ℓ̂)` with `Srt::sort_in_sort` at
   that rung as its certificate, carrying exactly the `uᵢ ∈ ω` hypotheses of
   the parameters `ℓ` mentions. **This is the first evidence mini has ever
   produced at a variable rung**, and it is the first place `CUMUL_HEIGHT`
   stops being the only answer: `sort_typing` is `None` above the tower's built
   height of 8, and `sort_in_sort` has no height at all. Pinned at `u + 12`.

   *The apparatus build point is pinned, deliberately.* `level_poly` declares
   symbols off the shared `Env`, so where it runs decides the numbering of
   every symbol minted afterwards; building it inside the first judgement that
   wanted it would make numbering depend on which declarations a run visited
   and turn the byte-identity gate into noise. It is forced in `Checker::poly`
   itself, at route entry, before any judgement, and `Interp::levels` is
   idempotent so a per-declaration route still builds it exactly once.

   **The caller exists, and it turned the remaining list into a
   measurement.** `mini/src/poly_run.rs` (`mini --poly`) drives
   `Checker::poly` over a whole file: one interpretation per *declaration* at
   its own universe parameters, no σ, no `subst_ground`, no schedule. It
   replaces the scheduled pass rather than joining it — the two mint into one
   `Interp` and `level_poly` declares symbols off the shared `Env`, so a run
   that did both would renumber the second pass's symbols — and it is off by
   default, which is why the scheduled rows are still byte-identical.

   The first real caller found a defect in the API it called, which is what a
   caller is for. `Checker::discharge_levels` took a single `&Thm` and
   **drained** its `AssumeToken`s: a declaration has two conclusions to close
   (`⊢ ⟦ty⟧ ∈ ⟦Sort ℓ⟧` and `⊢ ⟦val⟧ ∈ ⟦ty⟧`) and the second call would have
   handed its argument back unchanged, still carrying `u ∈ ω`, reporting
   success. It now takes a slice and closes every conclusion against the same
   assumptions in one pass, over a new `Scopes::discharge_assumption_many`.
   That is a **correction to §5.2's "no new mechanism was needed"**: the
   hypothesis mechanism was indeed already there, but its discharge was
   one-shot and the batch form had to be added.

   ### The measurement, over all 91 tutorial exports

   | | |
   |---|---|
   | declarations attempted (`def`/`axiom`) | **147** |
   | zone B skipped (`inductive`/`mutual`/`Quot`) | 108 |
   | `⟦ty⟧` produced | 56 |
   | `⊢ ⟦ty⟧ ∈ ⟦Sort ℓ⟧` derived **and closed** | **56 — every type that interpreted also certified** |
   | `⟦val⟧` produced | 83 / 146 |
   | `⊢ ⟦val⟧ ∈ ⟦valTy⟧` derived and closed | 59 |
   | **escaped assumptions (`open`)** | **0** |
   | **whole exports fully certified on this route** | **18** of 89 (`mini --poly` exits 0; 71 exit 4, 2 are frontend declines) |

   That last row is the one to read first, and it is the strongest thing this
   branch can currently say. Eighteen whole tutorial exports are interpreted
   and certified **at their declarations' own universe parameters**, with no σ
   anywhere and no assumption escaping its discharge. The route is not a
   prototype that types one hand-written `def`; it takes real files end to end.

   And the ordering, which is the thing a `Gap::SymbolicLevel` site count
   could not give. That variant carries no payload, so all 138 of them key to
   one string; `MINI_POLY_SITES=1` files the **origin** off `crate::blocker`'s
   trail instead:

   | site | count | the clause | the kind of work |
   |---|---|---|---|
   | `kernel.rs:3461` — `const_evidence`'s `ls → Vec<u32>` | **84** | `Expr::Const` at a parametric level | the **store's key** — step 5's generic point |
   | `kernel.rs:2959` — `pi_evidence`'s `as_numeral(l1)/(l2)` | **50** | the `Π` clause | **derivation** — `derived::levels::{pi_rules, ite0, leq}` |
   | `kernel.rs:3465` — `miss_reason` | 16 | a `no-interp(·)` store miss | downstream of the two above |
   | `kernel.rs:775` — `scope_typing`'s empty slot | 4 | a binder whose domain had no interpretation | downstream |

   Two things about that table are worth stating in words, because both cut
   against what the site counts predicted. **`zoneb.rs`'s 23 sites contribute
   nothing**: every one of them is `c.interp().ok_or(Gap::SymbolicLevel)?`, so
   with a thread in hand they stop firing, exactly as this section predicted —
   but zone B is not *reached* on this route at all yet, so its 108
   declarations are skipped rather than passing. And **the 84 is partly an
   artifact of this caller**: `poly_run` stores nothing, so every constant
   reference misses by construction. Even so it is real work either way, since
   `const_evidence` must be taught to look up at a level *expression* whatever
   fills the store — `ConstKey` already widened for it in step 2.

   **The `Π` clause is next**, at 50, and it is the one number in the table
   that no amount of store plumbing removes: it is pure derivation at
   `srt(ℓ̂)`, it is what §6.2 actually asks for, and it is on the critical path
   for the const clause too, since nearly every declaration's type is a `Π`.

   #### The `Π` clause, reconnoitred — assembly, and every argument is in hand

   Checked before it is briefed, because a brief on this strand has been wrong
   three times. `derived::levels::pi_rules::PiRules::pi_imax_dep` is *exactly*
   the theorem the de-scheduled arm wants, in one piece:

   ```text
   ⊢ ∀q⃗ ∀u ∀v ∀A. (((u ∈ ω ∧ v ∈ ω) ∧ (A ∈ srt(u) ∧ fib(q⃗,A,srt(v))))
         → ite0(v, cndd(q⃗,A), dprod(q⃗,A)) ∈ srt(imax(u,v)))
   ```

   Two things about it make the de-scheduled arm **simpler than the scheduled
   one**, which is not what the site count suggested. It is §1.4's `ite0`, so
   the arm does not have to *decide* `l2 == 0` — the two clauses `pi_evidence`
   splits on a numeral are merged inside the target term. And it takes its two
   premises at `srt(u)` and `srt(v)` directly and raises the fibres pointwise
   itself, so the de-scheduled arm has **no `raise_in_gamma`**: the scheduled
   one's cumulativity lift to `max(n1,n2)` disappears into the theorem.

   Every argument `pi_rules(env, r, i, ord, ut, s, ru, tower, dp, pair, cndd,
   cndd_ax)` takes is already in mini's hands: `r`/`i`/`ord`/`ut`/`s`/`ru` off
   `LevelPoly`, `tower` off the prelude, and `dp`/`pair` are **literally the
   `dp` and `rule` fields `Interp::fibre_site` already builds** for the ground
   path (`DProdN::new` and `dprod_in_universe_pair_n`, same stack). The derived
   side names this consumer in its own header — `cndd`/`cndd_ax` are handed in
   rather than minted precisely for *"the checker's lazy split"*.

   **One integration hazard, named now because the probe will otherwise find
   it the hard way.** `cndd` must be the conditional singleton over the
   **fibre site's** `b`. `Interp::cond_site` and `Interp::fibre_site` each call
   `define_abbrev` on the same skeleton through *separate* caches (`self.conds`
   and `self.fibres`), so they hold two different `FnSym`s for one body shape;
   `pi_rules` validates `cndd_ax` by probe against `dp.b` and would refuse the
   one `cond_site` built. The de-scheduled arm therefore mints its own via
   `prop::conditional_singleton` at `pi_body_dep(env, sums, fibre.b, holes,
   dom)` — which is the identical formula `cond_site` builds, over the other
   symbol.

   No new mathematics is required, which keeps the strand's running claim
   intact at the clause the brief said to attack first.

   ### What the gate becomes, now that the route is exercised

   Until this commit the byte-identity of the scheduled rows was free: nothing
   built a `poly` checker, so the new arm was unreachable. It is **still**
   byte-identical and it is **no longer free** — it is maintained by the
   exclusivity above, and that is the deliberate trade. The gate is therefore
   two-part from here:

   * **A — the scheduled route.** All 91 tutorial exports'
     `ledger`/`evidence`/`untranslated` rows byte-identical. Unchanged,
     verified this tranche, and still the primary gate.
   * **B — the de-scheduled route.** The `polyledger`/`polyblocked`/`polyev`
     rows over the same 91 exports, as a **ratchet and not an identity**:
     `typesOk`, `typeEv`, `valuesOk`, `valueEv` may only rise; `open` must stay
     **0**; `declars` and `zoneB` may not move without a stated reason. The
     numbers above are its first baseline.

   Gate B is what the strand's verdict is measured against:
   `PolyLedger::is_clean` — which refuses to excuse `zoneB` — is folded into
   `Outcome::fully_certified`, so `mini --poly` exits 4 today and exits 0 when
   the de-scheduled route works.
2. **`ConstKey` widens** from `(Name, Vec<u32>)` to `(Name, CanonLevels)`
   where `CanonLevels` is the canonicalised level-expression vector (the
   `canon_level` discipline, unchanged in spirit). Every `IndApparatus` table
   inherits the key change mechanically.

   **Step-2 status (2026-08-10): built.** `mini::interp::ConstKey` is
   `(Name, Vec<Level>)`; mini's `Level` is hash-consed and `Copy + Eq + Hash`,
   so the key costs no more than the numerals it replaced. Every one of the
   thirty-odd `IndApparatus` tables, `Interp::consts`, and
   `nested_splice::ModelKey` inherited it; the eighty-eight sites the compiler
   found were all key *construction*, and each now goes through
   `ground::ground_levels` (the schedule boundary, the one place a `Vec<u32>`
   becomes an instantiation) or `ground::key_levels` (`Level::simplify`, the
   canonicaliser). `ground.rs`'s `eval` split into `as_numeral` — a *closed*
   level as a `u32`, `None` at a parameter — so that **the groundness
   assumption now lives in one function instead of in the key's type**, and
   `subst_ground` is a thin wrapper over the general `subst_levels`. Nothing
   is minted at a symbolic key yet: the σ threading is still `&[u32]`, so this
   is exactly the type-level precondition and **no behaviour change,
   measured**: the `ledger` / `evidence` / `untranslated` rows over all 91
   tutorial exports are byte-identical to the pre-change sweep
   (`declars=255 pairs=218 typeEv=218 constEv=218`), `cargo test -p mini` is
   green at 188/24/12/6/1/12/2/20/16 (185 → 188 `#[test]` in `mini/src`,
   exactly the three added here — counted, because a deleted test does not
   fail), `envshare_tg` 5/5, and `tg_tutorial` holds at **39 passed**. What
   it buys is that the
   store can *name* `⟦c.{u}⟧`, which it could not, and that step 1's remaining
   work is the 138 `as_numeral`-shaped dead ends rather than eighty key sites
   as well.
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
levels (§4.2). **The prediction that its live population arrives with the
deletion is refuted by measurement**: staged — the deletion's own control flow
— it still fires zero times, because no declaration typing reaches the
boundary carrying a `uᵢ ∈ ω` antecedent. Of 1645 declarations, 1519 have no
value-typing certificate at all, and the 116 derived only under antecedents
carry *value* premises (87 a family of families, 30 a membership), never a
level one. The store's input population is empty for a reason upstream of
levels; §5.4 blocker 2c has the rates.

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
  rule shape. **The wiring is built** (commits `62b59f2`, `619b562`), as
  mapped, with two corrections the build forced:
  * **The guard level.** `undet_body_level`, the sibling walk of
    `body_clause` returning the level, **memoised** (the walk descends both
    children of a `Π` and expressions are DAGs; unmemoised, the staged
    prelude did not finish) and consumed **raw, not canonicalised**: the
    obligation's target `srt(ℓ̂)` is built from the raw arms of the
    *obligation's* canonical level, so raw-to-raw is what agrees, and
    canonicalising one side was measured to disagree exactly where canon
    reshapes (`imax u u` under a `succ`). A spelling drift is a counted
    miss. Only the `Undet::Param` flavour is addressable; `undet_unknown()`
    keeps the opaque symbol.
  * **The term.** `upi(h⃗, A, v̂)`, one `define_abbrev` per skeleton with
    `upi(h⃗,A,g) := ite0(g, cndd(h⃗,A), dprod(h⃗,A))` — **not** the spelled
    conditional: the two branches each repeat the holes, so a nest of Undet
    `Π`s doubles per level and every def-eq walk pays it exponentially
    (measured: the staged prelude went from minutes to *unfinished* at
    26:40 wall, 34% of samples under `def_eq_binder_aux`; behind the
    abbreviation it runs in ~14 s). The typing rule rides `upi_def` back in
    one Leibniz step; congruence is argwise over `upi` (guard position by
    reflexivity). Built via `self.mk`, so `parts` records the layer and
    congruence composes generically. The `dprod` half is the
    `Type` clause's **own symbol** for the skeleton (`pi_info_or_build`,
    the factored tail of `finish_pi_site`) — the nonzero branch *is* the
    decided clause's term. The Prop half is **not** `build_cond`'s `chi`,
    and cannot be: `define_abbrev` does not dedupe, so `build_cond`'s fibre
    symbol differs from `build_fibre`'s, and `pi_imax_dep` needs one fibre
    `b` for both the `cndd` characteristic formula and the fibres conjunct.
    The kit therefore mints `cndd` per skeleton over the `PiInfo` fibre;
    `cndd(h⃗,A)` is provably-equal-not-identical to `chi(h⃗,A)` — one more
    bounded blocker-3 seam, listed there.
  * **The rule.** Per skeleton (`Shared::pi_poly`, refusals memoised): the
    `DProdN` adapter over the `PiInfo` fibre stack (`dprod_members_n` +
    `dprod_subset_funspace_n` over the already-built symbols),
    `universe_replacement_n` → `least_universe_replacement_n`,
    `dprod_in_universe_of_n` → `dprod_in_universe_pair_n` (the
    `UniverseParts` all come off the prelude tower: `space.c2`,
    `funspace_of`, `union`, `bin_union`), then `levels::pi_rules`.
    `LevelPoly` grew the `Rules` field it needed (`ru`, pinned by
    `bundled_rules_are_over_this_chain`). `ty_pi`'s Undet arm instantiates
    `pi_imax_dep` at `(h⃗, û, v̂, A)` — the `û`/`v̂` arms read off the
    obligation's canonical `IMax`, the guard checked against the site's —
    with the `u ∈ ω` evidence rebuilt by `omega_level_rec` under the full
    antecedent, and the rule's two mathematical premises, `A ∈ srt(û)` and
    the fibres conjunct, **acquired as antecedents** exactly as a local's
    typing is: carried, counted, discharged where a binder's guard matches
    (the fixture's `pnest` pins the discharge — the enclosing λ's own
    guard closes the `A ∈ srt(û)` premise, the uniform typing invariant
    showing through).
  * **The fixture.** `checker/test_resources/UndetPi` — three Undet `Π`s:
    guard through a `Local`, through a `Const`, and under a binder;
    `by ty_pi_undet` 3 flag-on, `no evidence: ty_pi_undet` 3 flag-off
    (the red state and the bit-identity promise in one test). Mutations
    run red and reverted: the `û`/`v̂` instantiation swap (`piu`'s distinct
    arms make it observable) and the premise-projection swap.
  * **The measures** (staged, init-prelude, first `upi` run — wall 14 s,
    RSS 202 MB, exit 0): `no evidence: ty_pi_undet` 2407 → **2103**, with
    **304** sites answered by the wired rule (`by ty_pi_undet`, conditional
    certificates); TOTAL gaps 10521 → 10531 (the same honest direction as
    §4.2's +20 — no-evidence rows trade into carried-premise rows and the
    escape ledger's over-report). The recursor rows did **not** move at
    this coverage (ι computed 43, `T-policy 2/3` 600, `no curried` 399
    unchanged).
  * **The 2103, decomposed — measured, not guessed.** A counter per refusal
    reason now sits at both ends of the clause (`PiPoly`, reported as *the
    wired Undet-Π clause, by outcome*), and its typing rows are a **partition
    of the obligations**: they sum to `by ty_pi_undet` + `no evidence:
    ty_pi_undet`, a total kept by `certify.rs`'s gap ledger on an unrelated
    code path. Staged, init-prelude, flag on:

    | typing outcome | count | share of 2103 |
    |---|---:|---:|
    | `pi_imax_dep` fired (conditional) | 304 | — |
    | the canonical level is **not an `IMax`** | 1005 | 47.8 % |
    | the `Π` was **not wired** at interpretation | 588 | 28.0 % |
    | **canonicalisation drift** (guard ≠ the `IMax`'s right arm) | 510 | 24.2 % |
    | the obligation's type is not a `Sort` | 0 | — |
    | the rule chain refused / ω-recursion disagreed / a structural step | 0 | — |

    Three named candidates, three real populations, and **nothing else**: the
    per-skeleton rule chain never refused once (494 skeletons built, 0
    refused), the ω-membership recursion never disagreed, and no structural
    step ever missed its shape. The clause's *machinery* is not what is
    losing; its *level algebra* is.

    Interpretation side, same run: 15998 `Π`s took the `ite0` clause and 6097
    refused, **all** of them at the guard walk — the head's type not reaching
    a `Sort` after its arguments (4772), an application head that is neither
    `Local`, `Const` nor `λ` (741), and a `Var`/`Proj`/literal (584). The `λ`
    and unreadable-`Const` arms are **zero**, and so is the inert-fibre row.
    Only 588 of those 6097 are ever asked for a typing.

    Two of the three briefed candidates are therefore **one** problem. Taking
    the raw-versus-canon shapes off the same run:

    * the `IMax`-destructure miss is 999/1005 the *bare parameter* case —
      canon `u`, raw `imax(0,u)` (313), `imax(1,u)` (112), and nested
      `imax`-chains ending in `u`;
    * drift's largest rows are the same identity one level down — canon
      `imax(s(u), imax(u,u))` against a site guard built from raw
      `imax(u,u)`, and so on.

    Both are the single algebraic fact **`imax(a, b) = b` when `a ≤ b`**,
    which the target must *prove* because `⟦Sort ℓ⟧` is built from the
    canonical representative while the rule is instantiated at the site's raw
    arms. That is §1.5's kit, at the width the corpus demands — and the same
    bridge blocker 3 needs, so it is on the switchover's critical path rather
    than beside it. It was predicted to close **1515 of 2103 (72 %)** if it
    landed complete; it landed at the width below and closed **1162 (55 %)**,
    the shortfall being the two `≤` arms the slice does not build.
  * **The level bridge — built, and it closes 1162 of the 2103.** The two
    algebraic rows are gone, replaced by one honest row.

    *The mathematics*, `derived/src/levels/leq.rs` (new; `order.rs`'s
    `union_absorb_one` promoted to `pub(crate)` and reused rather than
    re-derived, `cumul::subset_refl` re-exported):

    ```text
    ⊢ ∀x. ∅ ⊆ x                                                    [Leq::empty_sub]
    ⊢ ∀x. x ⊆ x                                                    [Leq::sub_refl]
    ⊢ ∀v. ((v ∈ ω ∧ ¬(v = ∅)) → succ(∅) ⊆ v)                       [Leq::one_sub_nonzero]
    ⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → (p ∪ q) ⊆ v)                    [Leq::union_sub]
    ⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → ite0(q, ∅, p ∪ q) ⊆ v)          [Leq::imax_sub]
    ⊢ ∀u ∀v. (((u ∈ ω ∧ v ∈ ω) ∧ (¬(v = ∅) → u ⊆ v))
                → ite0(v, ∅, u ∪ v) = v)                           [Leq::imax_absorb]
    ```

    **The guard on `imax_absorb`'s premise is the content, not decoration.**
    `imax(1, u) = u` holds at every `u ∈ ω` *including* `u = ∅`, where
    `1 ⊆ ∅` is false; the premise is only ever needed in the branch where
    `v ≠ ∅`, and stating it as `¬(v = ∅) → u ⊆ v` is what makes the lemma
    usable at the 112 corpus sites of exactly that shape. An unguarded premise
    would be a strictly weaker lemma the dominant shape could not use. One
    honest note from the derivation: `imax_absorb`'s `(u ∈ ω ∧ v ∈ ω)`
    conjunct is **never consumed** — the identity holds for all sets — and is
    kept only because the consumer has the facts in hand anyway.

    *The consumer*, `TgBackend::level_bridge`/`level_absorb`/`level_le`: the
    rule is now instantiated at the **site's own raw arms** (the real domain
    and body sort levels, so its two mathematical premises stay dischargeable)
    and the conclusion's target is transported to the obligation's canonical
    spelling by one proved equation and one Leibniz step. Congruence is tried
    before absorption — `imax(u+1, u)` against `imax(u+1, imax(u,u))` differs
    only in an arm's spelling — and each shape is an independent attempt, so a
    sub-bridge that refuses falls through instead of sinking the call.

    *The measurement* (staged, init-prelude, flag on):

    | | before the bridge | after |
    |---|---:|---:|
    | `by ty_pi_undet` (conditional certificates) | 304 | **1466** |
    | `no evidence: ty_pi_undet` | 2103 | **941** |
    | `by ty_lam` | 872 | 1217 |
    | typings conditional on the ambient locals | 19993 | 21500 |
    | TOTAL gaps | 10531 | 10531 |
    | escapes | 1466 | 1466 |

    **1162 obligations moved from having no evidence at all to carrying a real
    conditional kernel certificate, and the total-gap counter cannot see it** —
    both states are "a gap", which is why the decomposition above had to exist
    before the work was worth doing. The +345 on `by ty_lam` is the same
    movement one rule downstream: a λ whose Π premise now exists becomes
    derivable.

    What is left of the 941: **588** `Π`s never wired at interpretation (the
    guard walk, untouched by this tranche), **6** with no domain sort level,
    **347** where the bridge refused. The bridge's own arm counters name the
    next two constructions rather than leaving them to be guessed at:
    `succ(x) ⊆ b` for `x ≠ ∅` (the strict order, 1081 refusals) and a bare
    parameter against an unequal level (63). Neither is in `leq.rs`, and the
    file's header says so.

    **The cost is real and is not hidden.** Staged instructions go
    195.02 G → **616.53 G** (3.16×). Memoising the level-to-ω map bought 1.5 %
    of it, so the bulk is the 1162 new certificates and the downstream work
    that consuming them creates — `ty_pi_undet_poly` and the bridge together
    are 17 % + 9.5 % of cycles under `perf record`, the rest is elsewhere in
    the pipeline. This is derivation the checker was previously not doing at
    all, not overhead; but it is a 3× and the switchover's economics section
    (§4.2) has to carry it.

    The identified reduction, **named and not built**: the bridge proves a
    *level* equation, which depends only on the `uᵢ ∈ ω` hypotheses and not on
    the site's two mathematical premises — yet it is currently derived under
    the full antecedent `H`, which makes every intermediate formula carry two
    conjuncts it never reads and makes the result uncacheable (H differs per
    site). Derived under the level-only antecedent and weakened to `H` in one
    step at the end, the same equation becomes shareable across every site
    with the same `(from, to)` pair and the same parameter set — and on this
    corpus that is a small number of distinct pairs against 1466 sites. This
    is a measurement-shaped guess and is written here as one; it has not been
    tried.
  * **"Blocker 1 closes 2c's residue too" is refuted, at 5× the coverage —
    and so is every other level-shaped explanation for 2c.** The commissioning
    brief carried the coupling; at 304/2407 wired it was neither confirmed nor
    refuted. It is now decided twice over. With the bridge landed the clause
    answers **1466 of 2407** — 4.8× the sites, 61 % of the population — and
    every recursor row on the staged prelude is **byte-identical** to what it
    read at 304:

    | row | at 304 wired | at 1466 wired |
    |---|---:|---:|
    | ι sites the general rule computed | 43 | 43 |
    | …declined (recursor): T-policy 2/3 | 600 | 600 |
    | iota: this recursor has no curried interpretation | 399 | 399 |
    | iota: the major premise is not a constructor | 184 | 184 |
    | declarations translated | 315 | 315 |
    | constant typings stored / uses answered | 10 / 117 | 10 / 117 |

    A coupling that survives a 4.8× change in the coupled quantity with zero
    response is not a coupling. **What replaced the dead attribution is a
    partition, not another guess** — the same method that turned the 2103 into
    "72 % is one identity", applied to the recursor path.

    `RecMiss` has one variant per `rec_nest` refusal site (`rec_nest`,
    `rec_bottom` and `gen_rec_bottom` return `Result<_, RecMiss>` and no bare
    `None` exit survives in any of them), and `note_rec_miss` is called from
    **exactly one place** — the ι site that asked. So the rows sum to the gap
    row, which `certify.rs`'s ledger counts on an unrelated code path. Staged
    `init-prelude`, flag on:

    | reason | count | share |
    |---|---:|---:|
    | the `T`-policy gate: no nullary constructor | **349** | 87.5 % |
    | indices / several motives / `K`-like / mutual | **50** | 12.5 % |
    | every other arm — eighteen of them | **0** | — |
    | **sum, = the gap row** | **399** | |

    The eighteen zeros are the finding. `OmegaEscape` (a domain mentioning an
    ω-variable the recursor's levels do not name), `BottomLevels` (the level
    list not `ind + motive`), `TPolicyTerm`, `Abbrev`, `RecOf` — every arm a
    level construction could ever reach — never fires once. And the fixture
    asserts the same rows in **all four states**: flag on and off, scheduled
    and staged. Level-independence stated as a test rather than as a sentence.

    **The `T`-policy row is all 600 the same gate**, established in code (one
    `note_decline(Decline::TPolicy)` site) and then *measured* rather than
    argued from the doc comment. Widening the gate: TOTAL gaps stay **10531**,
    ι fired stays **43**, `no curried` stays **399**; the 349 redistribute into

    * **172** refused by the nest walk's two-minor floor — `depth < np + 4`,
      inherited from the two-constructor hand-written bottoms, so a
      single-constructor structure sits at `np + 3` and is refused;
    * **149** with no `T`-policy target in the walk's own domains;
    * **28** with fewer than four recursor arguments;

    at the cost of **106** extra `GenRecursor` builds for zero closed gaps.
    Three named, level-independent constructions, and the largest of them is a
    hard-coded arity floor rather than anything about universes.

    **The other two ratchets are level-independent for their own reasons.**
    `stored ≥ 26` reads 10 because **1519 of 1645 declarations (92.3 %) have no
    value-typing certificate at all**, at the *same* 92.3 % rate the scheduled
    state has — so the drop is the census halving, not a level loss. And zero
    declarations reach the boundary with a `uᵢ ∈ ω` antecedent in either
    state, which **refutes §5.3's step-5 status line**: the quantified store's
    live population does *not* arrive with the deletion. `hit ≥ 1308` reads 117
    and is bounded by `stored`; see blocker 3 for the 483 that are not.

    The three tg-suite rows the deletion reddens are therefore nobody's
    blocker in the level sense — not blocker 1's, not 2c's, and not 3's. §5.5
    clause 1 is retired on this evidence.
  * **The instrument's own fixture.** `118_accRecReduction` staged populates
    three outcome rows at once (2 fired, 9 not wired, 1 bridge refused), so
    the partition is pinned there against the independent gap ledger and
    against each row separately, together with the three `≤` arms the bridge
    leans on — `the_undet_pi_outcome_rows_partition_the_obligations`. Three
    mutations run red and reverted: dropping the `note_pipoly` on the bridge
    exit (sum 11 against a ledger reading 12), giving two reasons one slot
    (sum right, rows moved 0/1), and — the one that tests the mathematics
    rather than the bookkeeping — instantiating `imax_absorb` at `(v̂, û)`
    instead of `(û, v̂)`, which takes the fired row to 0 because the absorbed
    side is the `imax`'s **right** arm and nothing else. `derived`'s own
    `levels_leq.rs` carries two more (the guard dropped from `imax_absorb`;
    `p`/`q` swapped in `imax_sub`) and computes both sides of the guard at
    ground numerals, three atoms for the two `⊆`-introduction rules.
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
* **Blocker 3 — evidence consumption across the vocabulary switch. Not
  separately closable, measured — and only half of it dissolves at the
  switchover.** Typing obligations discharged 5373 → 1624; declaration-typing
  store answers 1329 → 117. A ground use's interpretation (tower rungs) and a
  quantified theorem's instance (`srt(n̄)`) are provably equal, **not
  identical**, so every literal-formula guard misses across the boundary.

  **How big it is.** `Dt::MissOtherLevels` counts the only part of the
  store-miss population a level construction can reach: a use whose
  declaration *is* stored, at other levels. Staged `init-prelude`, flag on:
  **483 of 17124 misses (2.8 %)**; scheduled, 29. So blocker 3 closed
  completely takes `uses answered from the store` to at most **117 + 483 =
  600**, against a ratchet of **1308**. The other 97.2 % are declarations
  stored at no levels at all, which is not a level problem (see 2c).

  **Which half it is — the question §5.5 left open, now answered.** A
  cross-level miss at another declaration's *parameter variables* would need
  only the stored `∀u⃗` instantiated: no vocabulary switch, closable today. A
  miss at *numerals* needs `⟦Sort 0⟧` to be `srt(∅)` rather than a tower rung.
  Measured: **483 of 483 are ground.** There is no variable-to-variable
  population. Blocker 3 is therefore **part of** the switchover and not a
  precondition of it — the dissolution argument's conclusion is right, and it
  is now a measurement rather than an argument. `015_levelParams` is the whole
  thing at one site, with the schedule as its own control: two entries stored
  in both states, one use answered under σ and unanswered without it.

  **But the dissolution is only half of what was claimed.** §5.4 used to say
  the switchover dissolves this blocker in one commit. It does not. Running
  the vocabulary unification (`NANODATG_UNIFY_SORT=1`, §5.5) leaves **all 483
  cross-level misses in place**, because the store key is `(name, ⟦levels⟧)`
  and unifying the sort vocabulary does not make a use spelled `f.{0}` find an
  entry stored at `f`'s parameter variable. That needs §1.6's other half —
  instantiating the stored `∀u⃗` at the *use's own* levels. The consumer
  exists (`declar_typings_poly`, §5.3 step 5) but opens at the **generic
  point**, which answers only uses at the declaration's own parameter
  variables: a population measured at **zero**. Two independent mechanisms,
  one run and one not built.

  What the unification *does* buy is the seam §5.4 promised as "bounded and
  listable", now listed and sized: six rules go dark and three lose most of
  their population, 2511 firings in all, every one of them with a tower rung
  in its conclusion (§5.5's table). The `Srt` facts that replace them —
  `at_zero`/`at_succ`/`sort_in_sort` at numerals, with the numerals'
  *unconditional* ω-membership — are built, and they replace the vacuous
  `x ∈ U(x)` discharge with honest unconditional certificates.
* **Blocker 4 — mini** (§5.1's last row): its evidence pipeline is
  (declaration, σ)-shaped end to end. **Step 2 is built** (§5.3's step-2
  status: `ConstKey` is `(Name, Vec<Level>)`, so the store can address
  `⟦c.{u}⟧`); **step 1 is not**, and it is the larger half by a wide margin —
  138 `Gap::SymbolicLevel` sites across 36 files, `Interp::sort(n: u32)` at a
  tower rung with 69 consumers, and the eager `CUMUL_HEIGHT = 8` table. The
  first sizing of this blocker was wrong by an order of magnitude and is
  corrected under "Mini, sized" below.

The tg-suite rows that would go red under the deletion today are
`fired ≥ 80` (reads 43), `stored ≥ 26` (reads 10) and `hit ≥ 1308`
(reads 117), plus the per-file zero-gap pins on polymorphic tutorial
declarations. **They used to be called "the blockers' rows"; they are not.**
The partitions above attribute every one of them to a level-independent cause
— an arity floor and a nullary-constructor gate for `fired`, a 92.3 %
declaration-typing gap rate for `stored`, and `stored` itself for `hit`, with
483 of the residue in blocker 3. They are part coverage loss and part
**σ-denomination**: the ratchets count over 2891 (declaration, σ) pairs and
the deleted state walks 1645 declarations. §5.5's counter correspondence is
what makes the comparison honest, and neither reading lets them be quietly
re-based.

### 5.5 The switchover, run — what it costs and what still blocks it

The switchover is one commit: unify `interp_sort` on `srt(·)` at *every*
level, numerals included; retire the ground special case; delete
`instantiations.rs` (511 lines, verified), `tc.rs`'s schedule driver (~45),
`util.rs`'s σ-plumbing (~80) and `tg.rs`'s σ-reads (~90); de-schedule mini;
and re-take every ratchet on the far side. **It cannot be a ratchet** and it
cannot be partial: §1.6's cross-level payoff needs the schedule gone.

**Its first clause has been run.** `NANODATG_UNIFY_SORT=1` is the staging
switch — the twin of `NANODATG_NO_SCHEDULE=1`, deleted with it at the end —
and it makes `interp_sort` answer `srt(ℓ̂)` at every level, `⟦Sort 0⟧` being
`srt(∅)` rather than the tower's `U₀`. So the question "is the switchover
reachable" is now answered by running it rather than by argument, and **the
answer is yes**:

| | staged (ground path) | + unified | + the ground bridge |
|---|---:|---:|---:|
| `init-prelude` acceptance | exit 0 | exit 0 | **exit 0** |
| arena corpus | 152/0/2/0 | 152/0/2/0 | **152 matched, 0 mismatched, 2 declined, 0 waived** |
| TOTAL gaps | 10531 | 10752 (+221) | **10531 — parity** |
| escapes | 1466 | 1548 | **1466 — parity** |
| typing obligations discharged | 1624 | 519 (−1105) | **1624 — parity** |
| rule firings | 38587 | 36076 (−2511) | **38569 (−18, 0.05 %)** |
| instructions | 615.18 G | 618.33 G (+0.5 %) | 625.05 G (+1.6 %) |

**Every outcome measure is at parity.** Gaps, escapes and discharged
obligations are the ground path's numbers exactly; the residual 18 firings of
38587 are rules taking a different internal route (`ty_lam` 11, `App` 3,
`Local` 3, `ty_conv` 1), not coverage lost. The switchover's re-derivation
half is **done**.

Three readings, all of them load-bearing.

*The ground special case is not load-bearing for any verdict.* Both corpora
are accepted with one vocabulary, at master's own arena numbers. Nothing in
the switchover's core is a mathematical obstruction, and nothing in it is a
soundness question either — acceptance is unmoved in the state where every
`⟦Sort ℓ⟧` in the program changed.

*The vocabulary unification is free.* +0.5 % of instructions. The branch's
+177 % (§4.2) belongs entirely to the Undet-`Π` clause and the level bridge,
and none of it to the design's central move. A reader who assumed the
quantified sort was what cost the branch its performance would be wrong by
two orders of magnitude.

*The −1105 is blocker 3's seam, and it is now a list rather than a promise.*
§5.4 used to call it "a bounded, listable set of seams"; here it is, measured
on the staged prelude. Six typing rules go dark and three lose most of their
population:

| rule | staged | unified | Δ |
|---|---:|---:|---:|
| `IndTy`: an inductive type lies in its universe | 888 | 0 | −888 |
| `Lam`: a graph is a section of its fibres | 594 | 105 | −489 |
| `ty_pi_prop` | 446 | 0 | −446 |
| `ty_lam` | 1217 | 1079 | −138 |
| `ty_const` | 112 | 1 | −111 |
| `Const`: along the defining equation | 85 | 14 | −71 |
| `x ∈ U(x)` (Sort, and any `U`-shaped domain) | 51 | 0 | −51 |
| `ty_pi` | 50 | 0 | −50 |
| `U₀ ∈ U₁` (`⟦Prop⟧ ∈ ⟦Type 0⟧`) | 17 | 0 | −17 |
| `fs(a,a) ∈ U(a)` | 2 | 0 | −2 |

Every one of them has a tower rung in its conclusion, which is exactly the
predicted shape: a `derived` library theorem stated over `U(·)`, `U₀`, `U₁` or
`fs` no longer matches an interpretation spelled `srt(·)`.

**They were six symptoms of one missing equation, not six jobs.** The
construction is `⊢ srt(k̄) = Uₖ` at any rung — §1.2's numeral bridge,
generalised in `derived::levels` from the two hand-rolled instances
(`UTower::rung1_eq`/`rung2_eq`) that were already in the tree for exactly this
purpose. `UTower::rung_eq` iterates the ladder step at a numeral; `Srt::rung_eq`
composes it with `at_succ`, and answers rung 0 from `at_zero` instead — the one
place the two ladders differ in shape, since `lvl(0̄) = ω` while `srt(0̄) = U₀`.
It is **unconditional**: `numeral_in_omega` discharges every `n̄ ∈ ω` premise
with no hypothesis, which is why a ground use of a quantified theorem costs
nothing extra.

The checker spends it at **three guards** — `ind_ty_mem`, `domain_premise` (in
*both* positions, since `⟦Prop⟧ ∈ ⟦Type 0⟧` is a rung twice over), and
`prop_in_u0` — with `transport_to_srt`/`transport_subject_to_srt` carrying the
conclusion back in one Leibniz step each, checked against the membership
actually wanted. That closed **94 %** of the re-derivation half:

| | dark | bridged |
|---|---:|---:|
| `IndTy` | 0 | **888** |
| `ty_pi_prop` | 0 | **446** |
| `x ∈ U(x)` | 0 | **51** |
| `U₀ ∈ U₁` | 0 | **17** |
| `ty_const` | 1 | **112** |
| `Lam` | 105 | **593** |
| net rule firings vs the ground path | −2511 | **−153** |

**The fibre position was the last one, and it was not a blocker.** It is the
same equation at a third place: the sort is neither the subject nor the target
but a *component* of the subject `dprod(t,t)`, so the library fact is picked
at the rung and carried back by a Leibniz step whose pattern mentions the
variable **twice** — `fs(w,w) ∈ dom`, both occurrences substituted at once.
One step, no new construction. `Ctor` was the same idea once more at a lookup
*key*: `ind_mems` is keyed by the target and registered at the rung.

So all six dark rules and the three decimated ones were **one missing
equation, seen at five guards** — `ind_ty_mem`, `domain_premise` in three
positions (subject, target, fibre), `prop_in_u0`, and the `ind_mems` key.
`STILL_DARK` in
`the_ground_bridge_makes_the_unified_vocabulary_answer_as_the_ground_one_does`
is now **empty**, and is kept as an asserted-empty constant so a rule that
goes dark in future has to be written down to pass rather than merely
tolerated.

**One honest defect the bridge introduced and the fixture caught.** Bridging
`domain_premise` without also bridging the `HtClause` split left every count
correct and the report wrong: 51 `x ∈ U(x)` and 17 `U₀ ∈ U₁` were silently
reported as 68 `fs(a,a) ∈ U(a)`. This is why the fixture compares the *whole*
rule table rather than named rows — a per-row assertion cannot see a rule that
changed its label — and why the claim is *equality* with the ground path
rather than a floor: a unified run answering **more** than the ground run
would mean proving something the ground path does not, which is the direction
a bad transport fails in.

#### What the three clauses now say

1. **Blockers 1–2 closed.** **Retired as a precondition — it was never a level
   condition at all.** The three tg-suite rows the deletion reddens
   (`fired ≥ 80` reads 43, `stored ≥ 26` reads 10, `hit ≥ 1308` reads 117)
   are now decomposed by partition-checked counters, and *not one of them can
   be moved by any level construction*:
   * `iota: this recursor has no curried interpretation` = **399, of which
     349 are the `T`-policy-3 gate (no nullary constructor) and 50 are
     indices / several motives / `K`-like / mutual.** Every arm a level could
     reach — an ω-variable escaping a nest, a level list of the wrong shape, a
     refused abbreviation — reads **zero**. The fixture asserts the same rows
     in all four states (flag on/off × scheduled/staged), which is the
     level-independence claim stated as a test rather than as a sentence.
   * The `T`-policy row is **all 600** the no-nullary-constructor gate: one
     `note_decline(Decline::TPolicy)` site in the program. Widening it was
     *measured*, not reasoned about: TOTAL gaps stay 10531, ι fired stays 43,
     `no curried` stays 399, and the 349 merely redistribute into 172 refused
     by the nest walk's two-minor floor (`depth < np + 4` — a single-
     constructor structure sits at `np + 3`), 149 with no `T`-policy target in
     the walk's domains, and 28 with fewer than four arguments, at the cost of
     106 extra `GenRecursor` builds. The doc comment that claimed this was
     right; it is now a measurement.
   * `stored` is 10 because **1519 of 1645 declarations (92.3 %) have no
     value-typing certificate at all** — against the scheduled state's
     *identical* 92.3 % rate. And **zero** declarations reach the boundary
     carrying a `uᵢ ∈ ω` antecedent, in either state: the 116 that derive only
     under antecedents carry *value* premises (87 a family of families, 30 a
     membership). This **refutes §5.3's step-5 status line** — the quantified
     store's "live population arrives with the deletion" is false; it fires
     zero times staged too, and for a reason upstream of levels.
   * `hit` is bounded by `stored`. Of 17124 store misses, **483 (2.8 %)** are
     against a declaration stored at other levels — the only part a level
     construction reaches. Blocker 3 closed completely takes `hit` to at most
     **600**, against a ratchet of **1308**.
2. **The counter correspondence, stated.** *Written, below.* It is larger than
   §4.5 anticipated, because `fired`/`stored`/`hit` turn out to be
   σ-denominated too, not merely `pairs`/`constEv`.
3. **The ι gate at zero or re-decomposed with its new cause.** **The predicted
   cause is refuted and the disposition changes.** §5.5 used to say the
   switchover removes the +10 `pi congruence: two Πs of undetermined sort over
   differently shaped bodies` row "by making every Undet `Π` wired". Measured
   at all four states, that row reads **69 scheduled and 756 staged, with the
   vocabulary unified or not**. The switchover does not remove it; unifying
   `interp_sort` does not touch it. What the switchover removes is the
   *comparison*: the ratchet 15542 is a count over the scheduled prelude, and
   after the deletion there is no scheduled prelude. The gate must therefore be
   **re-taken on the only state that exists** — staged, **10535** at this head
   with the vocabulary unified and the ground bridge in (10531 on the ground
   path) — with the denomination named, the same rename-with-explanation as
   clause 2. Two dispositions are ruled out and one is required: it may **not**
   land as an accepted red, and it may **not** pass by accident because the new
   number happens to be smaller than a bar set over twice the population. It is
   re-baselined, at a stated denominator, in the switchover commit itself.

#### The counter correspondence

The unit of account changes from the **(declaration, σ) pair** to the
**declaration**, and on `init-prelude` that is 2891 → 1645. Every counter
denominated in the old unit loses its referent and must be renamed with its
denominator stated, never silently re-based (`permissive but consistent`).

| old counter | what it counted | replacement | what it counts | honest comparison |
|---|---|---|---|---|
| `pairs` | (declaration, σ) value pairs | `decls` | declarations walked | 2891 → 1645; a ratio, not a loss |
| `constEv` | pairs whose typing carries evidence | `declEv` | declarations whose one typing carries evidence, unconditional and `∀u⃗∈ω`-quantified counted apart | 26 → 10; **rates 0.90 % → 0.61 %**, so a real 32 % relative loss sits inside the denomination change and must be reported as such |
| `fired ≥ 80` | ι sites computed, over 2891 pairs | `fired` over `decls` | ι sites computed | 92 → 43; rates 3.18 % → 2.61 % |
| `stored ≥ 26` | typings stored, over 2891 pairs | `stored` over `decls` | typings stored | 26 → 10; see `declEv` |
| `hit ≥ 1308` | store answers | `hit` | store answers | 1329 → 117. **This one is mostly a real loss, not denomination**: 483 of it is blocker 3's cross-level boundary and is attributed there; the rest follows `stored` |
| `gapped`, `unsealed` | — | unchanged | — | unchanged |

The rule the table obeys is the one this branch already set with `TNotImax`
and `TGuardDrift` → `TBridge`: the new row records both old names, and where
a rate moved as well as a denominator, the rate is printed. A re-based counter
with no explanation is indistinguishable from a hidden regression, and three
of these moved for reasons that are *not* the re-basing.

**These counters change meaning at the switchover whether or not anyone
touches them.** That is the point of writing the correspondence down rather
than leaving it to be noticed. `fired`, `stored`, `hit`, `pairs` and `constEv`
are denominated in a unit — the (declaration, σ) pair — that the deletion
abolishes; a reader comparing 43 against a ratchet of 80 after the switchover
is comparing counts over different populations, and *nothing in the number
says so*. A counter left un-renamed through a denominator change is not a
neutral omission: it silently reports a smaller number against an unchanged
bar, which is exactly what a hidden regression looks like, and equally what a
hidden *improvement* looks like. Renaming is what makes the direction
recoverable.

#### Acceptance invariance, on the far side

Exit 0 and the same declarations in every state now measured — scheduled,
staged, and **staged with the vocabulary unified** — plus the arena corpus at
`152 matched, 0 mismatched, 2 declined, 0 waived` in the switched-over state.
That is the claim that makes a deletion this large reviewable, and it now
holds on the far side of the switchover's first clause rather than only on the
near one. Flag off is bit-identical with the new switch set or unset:
init-prelude at the untouched 15542 gaps / 2257 escapes.

#### What is actually left

Not blockers 1–2, and not blocker 3 *as a precondition*. What is left is:

* ~~The rung-shaped typing rules~~ — **done**, at parity on every outcome
  measure, by the one ground-bridge construction above.
* **The store answering cross-level uses** (§1.6). Unifying `interp_sort`
  leaves all 483 cross-level misses in place, because the store key is
  `(name, ⟦levels⟧)` and the vocabulary switch does not make a use spelled
  `f.{0}` find an entry stored at `f`'s parameter variable. §5.5 used to
  describe the switchover as one commit that dissolves blocker 3; the
  measurement says it is **two independent mechanisms**, the vocabulary
  unification and the instantiation of the stored `∀u⃗` at the use's own
  levels, and only the first has been run. `declar_typings_poly`'s consumer
  exists but opens at the *generic point*, which answers only uses at the
  declaration's own parameter variables — a population measured at **zero**.
* **Mini** — blocker 4, below, the largest of the three, and larger than it
  was sized: 40 of 56 source files, not `ground.rs`'s 141 lines. Step 2 of
  §5.3 landed 2026-08-10; step 1 is the volume.

None of these is blocked on mathematics, and none of them is a level problem
except the second.

#### A check that reported success having done nothing — a witness for task #137

Recorded here because it happened on this branch and #137's seat should
inherit a concrete case rather than a principle. It is not fixed here: it is
cross-cutting and belongs to CI, not to this branch.

**What happened.** A doc-comment rewrite of one fixture used a text slice
whose end marker sat *past* a neighbouring test, and the replacement deleted
`the_ground_bridge_makes_the_unified_vocabulary_answer_as_the_ground_one_does`
outright. `cargo test --test tg_tutorial` then reported

```text
test result: ok. 38 passed; 0 failed
```

having previously reported 39. **Nothing failed, because a deleted test does
not fail.** The loss was caught two commits later by hand, when a `grep` for
the constant it defined came back empty — not by any check.

The shape is exactly #137's: one aggregate counter (`N passed`) cannot
distinguish a suite that grew a pass from one that lost a test, and the run
that lost one is indistinguishable from a healthy run at a smaller number. A
per-suite expected-test-count, or a manifest of test names diffed across runs,
would have made it a red rather than a silent −1.

#### Mini, sized — and the first sizing was wrong by an order of magnitude

**The sizing this section used to carry — "141 lines, 80 `ConstKey`
occurrences across 4 files, 50 `ground::` sites" — is right about every number
it names and wrong about what the job is.** Each of those counts is the
*schedule's* footprint. The de-scheduling's footprint is the set of places that
assume a level is a **numeral**, and that is a different, much larger set.
Re-measured 2026-08-10 at `71f1c8f`:

| what | count | where |
|---|---:|---|
| `mini/src/ground.rs` | 141 lines | one file |
| `ConstKey` occurrences | 80 | 4 files |
| `ground::` call sites | 50 | **22** files, not 4 |
| **`Gap::SymbolicLevel` mint/match sites** | **138** | **36** files |
| σ-shaped signatures (`&[u32]`/`Vec<u32>`) | 151 | — |
| `Interp::sort(n: u32)` consumers (`.sort(`) | 69 | — |
| **mini source files touching any of the three** | **40 of 56** | — |

`Interp::sort(n: u32) -> Term` is `self.prelude.tower.u(n as usize)` — a `u32`
indexes a *rung* — and the eager cumulativity table `Cumul::new(…,
CUMUL_HEIGHT = 8)` exists because "a closed Lean level evaluates to [a small
numeral] before the interpretation runs". `interp.rs`'s module header states
the assumption as the module's founding invariant, in these words: "Every level
reaching this module is a numeral, because the checker runs once per ground
instantiation σ (§3). `⟦Sort u⟧` is therefore always exactly one clause, and
`PiUndet` … **cannot arise**."

**And it is not a low-coverage change either.** On mini's live corpus — the 91
tutorial exports, which is what mini is measured on, not `init-prelude` — 255
declarations are walked, 218 `(declaration, σ)` pairs are opened, and
`constEv = typeEv = pairs = 218`: mini certifies **every** pair. Of the 176
declarations the exports actually declare, **114 (65 %) carry universe
parameters** (82 `def`, 24 `quot`, 7 `thm`, 1 `axiom`). Every one of them is a
site where the ground path succeeds today and the symbolic path mints
`Gap::SymbolicLevel`. A de-scheduling that flattened the walk without the
ω-vocabulary would therefore trade a 218/218 certification rate for a large
measured loss — which is why §5.3's step order puts the vocabulary first and
why the flattening is not a separable first slice.

**No fundamental blocker, and the reason is specific rather than optimistic.**
Every construction mini needs at a variable rung is already built and tested in
`derived/src/levels/`, because the checker's `tg` backend needed the same ones:
`Srt::{at_zero, at_succ, step_sub, sort_in_sort, mono_mem}` for the ladder,
`levels::rules`/`levels::pi_rules` for the two `Π` clauses, `levels::leq` for
the level algebra (at the slice §6 names). In particular `Srt::mono_mem` —
`⊢ ∀n∈ω. ∀m∈n. srt(m) ⊆ srt(n)` — *is* what `CUMUL_HEIGHT`'s `O(h²)` table
tabulates, at a variable rung and with no height limit, so the table retires
rather than needing a replacement. Mini's de-scheduling is the **second
consumption of the checker's own construction, at a larger backend**: volume,
not mathematics.

**Step 1, decomposed by module** — a *static* count, so that the next seat
picks by size rather than by the order the compiler happens to complain in. It
is not a live-firing count and is not offered as one:

**Production sites only, and the two columns are the wrong unit for one of
them.** The first cut of this table counted whole files, and was wrong about
which half of step 1 is the big one. Re-measured at `7ab9688`, excluding doc and
comment lines and splitting each file at its `#[cfg(test)]`:

| module | `SymbolicLevel` | `.sort(` | what it is |
|---|---:|---:|---|
| `zoneb.rs` | 23 | 2 | zone B: the declaration-shape translation and the pre-ensure |
| `kernel.rs` | 21 | 2 | mini's `Checker` — `whnf`, `assert_def_eq`, the const/proj arms |
| `proj_data.rs` / `proj_prop.rs` | 11 / 6 | — / 1 | the two projection clauses |
| `minor_ix.rs` | 9 | 1 | indexed minor premises |
| the `rec_*` / `iota_*` family | 31 | 7 | eleven modules, recursors and their ι rules |
| `interp.rs` | — | 8 | the store itself; `Interp::sort` and the ω-vocabulary beside it |
| `quot*.rs`, `conv.rs`, `direct.rs`, `class_s*.rs`, … | 31 | 7 | the rest, none above 4 |
| **total (production)** | **132** | **28** | across 40 of 56 files |
| in tests | 1 | 46 | — |

`.sort(` is *where a rung is spelled*, and at 28 production sites it is the
**small** half — the "36 of 69" this table used to give `interp.rs` was 8
production sites against 33 fixtures. None of the eight has a `Level` in hand;
each takes a rung `u32` from its caller, so converting them is a signature
fan-out through the consumer modules rather than work inside `interp.rs`.

**And `SymbolicLevel` is not 132 conversions across 36 files. It is 132
consumers of one absent thing, and the count is misleading as a work
estimate.** Classified by what each site actually tests:

| | count | the site reads |
|---|---:|---|
| **no `Interp`/thread at all** | **112** | `c.interp().ok_or(Gap::SymbolicLevel)?`, `let Some(th) = self.th …` |
| a `None` arm in those same functions | 14 | `Ev::missing(Gap::SymbolicLevel)` |
| pure reporting | 3 | the blocker label, the dump string, `Cause::Scope` |
| **the level is not a numeral** | **3** | `ground::as_numeral(l).ok_or(…)` |

`mini/src/kernel.rs` has exactly two `Checker` constructors — `Checker::new`,
"the shape zone: acceptance only, no evidence" (`th: None`), and
`Checker::threaded`, "the evidence-carrying pass, **at one ground
instantiation**" (`th: Some`) — and `Gap::SymbolicLevel`'s own doc comment says
the same thing from the other end: "a judgement made in the declaration-shape
zone, where levels are the declaration's own parameters and no §6.2 clause
applies". So the whole population is downstream of **one binary choice**, and
the de-scheduling's shape at mini is not "edit 132 sites" but *"give zone A a
thread"*: a `Checker` constructor that opens the declaration's `LevelVars` under
`Scopes::assume` and hands the checker an `Interp` where today there is none.
The 132 sites then stop firing without being edited, and what they need instead
is that the §6.2 clauses behind them succeed at `srt(ℓ̂)` — derivation work, in
`zoneb` and `kernel` first, not editing work.

This does not make the switchover partial-able (§5.5's disposition stands), but
it does mean the per-module discipline applies to the *clauses*, not to the gap
sites: the new constructor can be exercised on its own route while the scheduled
path keeps calling `Checker::threaded`, so each module still lands green with
the ledger rows byte-identical.

`ledger.rs`'s per-σ pair walk, `zoneb`'s pre-ensure (keyed
`(name, ground levels)`, its module doc says so in the first thirty lines) and
`dump.rs`'s schedule enumeration ("this dump **enumerates the schedule, not the
store**") remain the three named consumers, and each states its σ-dependence in
its own header.

**Steps 1 and 2 are built** — see §5.3's step-1 and step-2 statuses. The
vocabulary exists in `interp.rs`, `Checker::poly` threads an `Interp` through
zone A at a declaration's own parameters, the `Sort` clause is converted, and
`mini/src/poly_run.rs` drives the route over a whole file: mini certifies
`⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` at a variable rung above the tower's built height,
and does it for 56 of the tutorial corpus's 147 `def`/`axiom` declarations with
**no escaped assumption anywhere**.

What remains is the other §6.2 clauses, and the order is now measured rather
than sized: the `Π` clause (`pi_evidence`, 50 of the 138 residual
`Gap::SymbolicLevel`) is derivation at `srt(ℓ̂)` and is next; `Expr::Const` at a
parametric level (84) is the store's key and belongs with step 5; `zoneb.rs`'s
23 sites contribute **nothing**, because they were all
`c.interp().ok_or(…)` and stopped firing when the thread arrived — zone B's
108 declarations are simply not on this route yet. §5.3 step 1 carries the
table and the two-part gate the route is now measured against.

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
* **The certified level-`leq` mirror (§1.5)** is built only in the slice the
  corpus demanded — `derived::levels::leq` and `TgBackend::level_bridge`,
  §3 and §5.4 blocker 1. The strict-order arm (`succ(x) ⊆ b` for `x ≠ ∅`,
  1081 refusals staged), the parameter case split (63) and `max`
  reassociation are **not** built. They are counted, not assumed away.
* **The store schema for `∀u⃗∈ω` certificates** is built on the checker side
  (`Shared::declar_typings_poly`, §5.3 step-5 status) and pinned by fixture;
  its *cross-level* consumption is not built — §5.4 blocker 3 — and mini's
  side is untouched. Two things measured since: the store's input population
  is **empty** in every state, including the staged one the §5.3 status line
  predicted would fill it; and its consumer opens the `∀u⃗` at the **generic
  point**, so even a full store would answer only uses at the declaration's
  own parameter variables — a population measured at zero, against 483 uses at
  numerals. The missing piece is `ax_inst` at the *use's* levels, and unifying
  `interp_sort` does not supply it.
* **Performance of quantified checking is unmeasured**, because the pipeline
  is not rewritten; what is measured is the construction cost of the new
  apparatus and the invariance of today's counters (§4). No claim is made
  either way about end-to-end speed. The one thing now measured is *negative
  and useful*: the quantified sort itself is not what costs anything
  (+0.5 %, §5.5), so the +177 % is attributable to the Undet-`Π` clause and
  the level bridge and to nothing structural in the design. The owner has said
  a regression would not stop this line, and the branch has not been slowed to
  chase one.
