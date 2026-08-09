# Level-polymorphism in the target — design and exploration record

**Branch exploration** (`explore/level-poly-target`), commissioned by the owner:
instead of handling only ground level instantiation, quantify over the level as
an element of **ω** in the target theory, so an assumption `a : Type u` becomes
`⟦a⟧ ∈ srt(u⁺)` with `u` a bound variable of the set theory, and the Prop/Type
split becomes an if-then-else **inside the target term**.

## Verdict, first

**No mathematical obstruction was found; the set theory supports the design in
full.** The verdict rests on constructions that are *built and tested* on this
branch (§3), not on argument alone. What separates this branch from a shipping
variant is engineering volume in `checker/`/`mini/` — the ground-σ assumption
is load-bearing in the translation layer's keying and clause dispatch — and
that volume is mapped in §5, with what was prototyped named as prototyped and
what is unmeasured named as unmeasured.

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

<!-- filled in as constructions land -->

## 4. What it costs

<!-- measurements -->

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

<!-- honest shortfalls -->
