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

<!-- census of groundness assumptions + integration plan -->

## 6. What is deliberately not claimed

<!-- honest shortfalls -->
