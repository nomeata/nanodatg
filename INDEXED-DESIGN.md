# Indexed inductive families — design

§5.2's `good` predicate and `spec` judgment, and §5.3's subsingleton
eliminators, translated into this development's terms. Companion to
`RECURSOR-DESIGN.md` (whose rungs 1–4 landed as `derived/src/inductive/`) and
`INDUCTIVES.md`. Thesis references are to the scratchpad `thesis.txt` copy:
§5.2 at `:1752–1820`, §5.3 at `:1822–1889`, the interpretation clauses at
`:2075–2131`.

Provenance markers, per the standing rule: **[read]** = verified in this
repository's code or docs during this design; **[decoded]** = read out of an
`.ndjson` export by actually decoding the declaration (the script parses the
name/level/expr tables and pretty-prints the types — no reasoning from names);
**[believed]** = inferred, with the inference stated. Every `RBTree` claim
below is **[decoded]** from `042_rbTreeDef.ndjson` line 294; this is the
declaration that was mis-stated twice this week, so nothing about it is taken
from any prior document.

---

## 1. Verdict up front

1. **`good` does not need a DTT equality type, and never did.** The chain
   recorded in `README.md` ("indexed families need `acc`, then §5.3, then
   §5.2 — because `good`'s base case wants `Eq`'s elimination") dissolves at
   the set level. `good`'s base case `(x) = (e)` is a **kernel-level equality
   of tuple terms** inside a Separation, and "eliminating" it is
   `kernel::thm::eq_leibniz` — a primitive rule **[read**,
   `kernel/src/thm.rs:759`**]**. The thesis's own interpretation says as much:
   `⟦rec₌ e b h⟧ = ⟦e⟧` (`thesis.txt:2124`) — the eliminator is the identity
   on the minor premise, so at the interpretation level there is nothing to
   build. **§5.2-indexed does not depend on §5.3 or on `acc` at all.** The
   two branches are independent, and `RBTree` needs only §5.2. §2.3 has the
   detail.
2. **The `good` function is the existing general W-recursor at one new
   target.** `goodrec := wrec(A, B, u, 𝒫(Idx), e_G)` — the same shared
   `RecCore`, the same step-by-Replacement shape as
   `inductive/step.rs`, with the step's values Separation subsets of the
   index-tuple space `Idx`. Because every value is a Separation subset,
   `step_typed` is **unconditional** — the `good` recursion is total with no
   `HYP` at all, unlike the value recursor. §3 gives the construction.
3. **The carrier is one more Separation**:
   `ind(p⃗, x⃗) := { s ∈ W(A,B,u) : tup(x⃗) ∈ app(goodrec, s) }`. Constructor
   membership, inversion ("no junk at an index") and non-vacuity in both
   polarities all fall out of the single per-constructor `good`-ι equation.
4. **The branch criterion is Lean's eliminator trichotomy, per declaration,
   read off the export** — never the instantiated sort
   (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3's rule, kept). `RBTree` is
   **class (T)**: its resultant sort is `Sort u+1` **[decoded]**, provably
   nonzero at every instantiation, so it takes §5.2 with a genuine `good` —
   **not** §5.3, which it never touches. §2 has the criterion and the full
   census of the 91 files: exactly five indexed families exist in the
   tutorial corpus, and each is classified there.
5. **`acc^φ_r` is not a new construction.** Because `derived/src/acc/`'s
   `preds_in` carries its own `y ∈ A` guard and `R ⊆ A × A` was deliberately
   never assumed **[read**, `acc/condition.rs` header**]**, the thesis's
   `acc^φ_r x := ∃h : φ x. acc_{r′}(x,h)` collapses to
   `acc(A_φ, R)` at the Separation `A_φ := {q ∈ Idx : φ(q)}` with **the same
   unrestricted `R`**. The two corrections that landed with `acc` are exactly
   what make this one-liner sound; §6.1 spells it out.
6. **`DeclSpec` is extended by wrapping, not by churning.** A new
   `IndexedDeclSpec` carries the index-type symbols and the per-constructor
   index expressions; its *erasure* is a plain `DeclSpec` and is what the
   existing `Machine`/`Inductive`/`GenRecursor` stack consumes, unchanged.
   The non-indexed path stays a special case, not an instance — deliberately,
   because the fragment's zero-gap results must not be re-derived through a
   vacuous-subset wrapper. §7.
7. **The riskiest step is not the mathematics.** Derived-side, the one proof
   with no ancestor at its shape is the `good`-ι/constructor-membership
   composition (§8, rung D3). Overall, the riskiest step is — as it was for
   the general recursor, five recorded late surprises running — the wiring:
   the `np > 0` lambda-graph nest (a blanket `Decline::Params` when this was
   written; **`np > 0` is wired now** and `Decline::Params` survives only as
   the exit for a declaration whose type-former nest refuses to build —
   `tg.rs:6392–6396`, and §8.1 says the same) and the new `T`-policy branch for
   family-valued motives, which `077`'s `RBTree.id` needs (§5.3, §8 rung C3).

---

## 2. The branch criterion, and the corpus census

### 2.1 The criterion

Per declaration, decided once, from the export's own data (never
per-instantiation — `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3's conclusion,
which this design adopts as-is):

| class | test on the export | translation |
| --- | --- | --- |
| (T) | **not a subsingleton**, and resultant level **provably nonzero** (`provably_nonzero`) | §5.2: skeleton W + `good` subset (this document §3–4); `good` vacuous iff `numIndices = 0` (existing path) |
| (S) | a **subsingleton** — one constructor, every non-recursive field a proposition or a result index (Carneiro §2.6.2 reason 2) | §5.3: `acc(A_φ, R)` carrier (§6) |
| (P) | not a subsingleton, resultant level possibly 0 | §5.2's truncation clause: `‖·‖` of the lifted translation — **built**, `family::trunc`, §6.3; **indifferent to `numIndices`**, since seven of the thirteen witnesses have none |

**(S) is asked first, and does not consult the level.** The class-(S) carrier is
a subset of `{•}`, hence a member of every rung, so it denotes a `Type`-valued
declaration as faithfully as a `Prop`-valued one (LPI §3.3) — `provably_nonzero`
therefore decides nothing about a subsingleton and only says what a
non-subsingleton gets. Asking it first is what `monomorph` broke, since it
grounds `Sort u` to `Sort 1` (`MONOMORPH.md` §4.3). Where both carriers are
admissible the choice is free and `mini::zoneb::collapsed_subsingleton` is the
narrowing: the preference for (S) stops at the non-indexed, one-constructor,
non-recursive shape whose §5.3 carrier `class_s` builds.

This design proposed reading the (S)/(P) split **off the recursor** rather than
recomputing Lean's subsingleton rules — `071`'s `SortElimProp.rec` has
`levelParams=['u']` (LE) and `072`'s `SortElimProp2.rec` has `levelParams=[]`
(not LE) **[decoded]**, the same constructor shape, differing only in that
`072`'s index `id Bool b1` is not invertible — on the argument that recomputing
Lean's invertibility analysis would be re-implementing the thing being checked.

**`mini` does not do that, and the reason it does not is worth keeping.**
Reading the recursor makes the answer depend on whether one was exported at all,
which is not a property of the type; `mini::zoneb::subsingleton` computes it
from the declaration and the exported recursor is kept as an **oracle**
(`zoneb::elim_audit`, cross-checked over the whole corpus by
`checker/tests/mini_tutorial.rs`). The two agree on all 91 files, `071` and `072`
included.

### 2.2 The census — every indexed family in the 91 tutorial files [decoded]

| declaration | shape | class | files | what it needs |
| --- | --- | --- | --- | --- |
| `RBTree : Sort u+1 → Color → N → Sort u+1` | 1 param, **2 indices**, recursive, 3 ctors; `rec` motive `Sort u_1`, `k=false` | **(T)** | `042`, `068`, `077` | §5.2 with genuine `good` — §3–5 of this document |
| `Eq : Sort u_1 → α → α → Sort 0` | 2 params, 1 index, non-recursive, `k=true` | (S) | 28 files | **direct clause**, not the general §5.3: carrier `[ā = b̄]` exists (`prop.rs`); `⟦Eq.rec⟧` is the minor-projection nest, ι is beta (`thesis.txt:2124`). `094_ruleK` uses `Eq.rec.{0+1,0+1}` — a **Type-level motive** — so this clause, not `proof_eq`, is what closes `094` |
| `Acc : Πα, (α→α→Prop) → α → Prop` | 2 params, 1 index, recursive, reflexive (function-typed rec arg), LE | (S) | `117`, `118` | **direct clause**: `⟦Acc α r x⟧ = [x̄ ∈ acc(⟦α⟧, R̄)]` (`thesis.txt:2126`), with `R̄ = rel_graph(⟦α⟧, ⟦r⟧)` (`quot::graph`, **built**); `Acc.rec` = `rec_acc::pack` — the module built for exactly this **[read]**. The reflexive field is **not on this path**: the direct clause replaces the carrier, so the walk that would refuse it never runs — see §6.2 |
| `SortElimProp : Bool → Bool → Bool → Prop`, `mk : ∀b b1 b2. P b b2 b1` | 1 param, 2 indices, non-recursive, LE | (S) | `071` | §5.3 **degenerate**: no recursive args ⇒ `R = ∅` ⇒ `acc(A_φ, ∅) = A_φ` (`acc_empty_relation`, exists **[read]**) ⇒ carrier `[φ(x⃗)]`, a conditional singleton. §6.2 |
| `SortElimProp2` (same, index `id Bool b1`) | 1 param, 2 indices, non-recursive, **not** LE | (P) | `072` | truncation clause: carrier `[∃…]` via `Trunc`. §6.3 |

Checked by enumerating every `inductive` record in all 91 files, not by
sampling: these five are the **only** declarations with `numIndices > 0`.
That census is scoped to the tutorials *and* to indexed declarations, and both
scopes matter: `init-prelude` and `grind-ring-5` add four more indexed families,
and class (P) is not an indexed-only class at all — §6.3 has the repository-wide
class-(P) table, thirteen declarations of which seven have no indices.
Also checked: every `Eq.rec`/`Acc.rec`/`RBTree.rec`/`SortElimProp*.rec`
*instantiation* in the corpus, because the branch a file needs depends on the
motive level actually used. `077`'s `Eq.rec` sites are all `u = 0`
(Prop motive → the existing `proof_eq` short-circuit); the only Type-motive
`Eq.rec` is `094`'s and the only Type-motive `Acc.rec` is `118`'s
**[decoded]**.

### 2.3 `RBTree`, resolved concretely

From `042_rbTreeDef.ndjson` **[decoded]**:

```text
RBTree : ∀(α : Sort u+1), Color → N → Sort u+1        numParams=1, numIndices=2
leaf  : ∀α. RBTree α Color.b N.zero
red   : ∀α (n : N). RBTree α Color.b n → α → RBTree α Color.b n → RBTree α Color.r n
black : ∀α (c1 c2 : Color) (n : N). RBTree α c1 n → α → RBTree α c2 n → RBTree α Color.b (N.succ n)
RBTree.rec : k=false, numMotives=1, numMinors=3, levelParams=[u_1, u]
             motive : ∀(c : Color)(n : N). RBTree α c n → Sort u_1
```

Its own sort is `Sort u+1` — nonzero at **every** instantiation, including
`u := 0` — so the trichotomy puts it in class (T) unconditionally and §5.3
never applies to it. The thing §5.3 is *for* — a family that must stay a
subsingleton because Prop instantiation is possible — has no purchase here.
What decides the branch is the declaration's resultant level, not
`numIndices` and not the `k` flag: `Eq` is indexed *and* subsingleton;
`RBTree` is indexed and never a subsingleton.

The `good` predicate `RBTree` needs, in the thesis's own notation:

```text
good leaf              (c,m) := (c,m) = (Color.b, N.zero)
good (red n l x r)     (c,m) := (c,m) = (Color.r, n)        ∧ good l (Color.b, n) ∧ good r (Color.b, n)
good (black c₁ c₂ n l x r) (c,m) := (c,m) = (Color.b, succ n) ∧ good l (c₁, n)      ∧ good r (c₂, n)
```

### 2.4 Where the "needs Eq elimination" belief came from, and why it is void

The `spec` judgment's base case (`thesis.txt:1793–1794`) emits `x = e` — in DTT, a
use of the equality *type*, and any later use of that fact (deriving the
recursor, inversion) transports along it with `rec₌`. Hence the recorded
chain: `Eq`'s elimination before `good`. But this development never builds
`good` as a DTT term. It builds `good` as a **set-level function into
`𝒫(Idx)`** (§3), where the base case is the kernel formula
`w = ⟨e₁,⟨e₂,•⟩⟩` inside a Separation, and every downstream use of it is
`eq_leibniz` plus Kuratowski-pair injectivity (`pairs.rs`, exists
**[read]**). The thesis's own interpretation of `rec₌` as the identity
(`thesis.txt:2124`) is the same observation made from the other side: after
interpretation, equality elimination is substitution of equals, which a
FOL kernel has as a primitive. **Checked, as the task asked: the cost is zero
new constructions.** What survives of the dependency is only that the
*checker* must interpret Lean's `Eq` type and `Eq.refl` — which
`derived/src/prop.rs` already does — and `Eq.rec` as the minor-projection
nest (§2.2's direct clause), which `094` needs regardless of indexed
families.

---

## 3. The `good` component — construction

### 3.1 The data

Fix a declaration with `np` parameters, index-type symbols `ι₀ … ι_{ni−1}`
(`ι_k` of arity `np + k`: parameters, then earlier indices), and per
constructor `i` the erased data (`args`, `order` — as today) plus:

- `e⃗ᵢ` — the **result indices**: `ni` symbols, each of arity `np + kᵢ`
  (parameters, then *all* of the constructor's non-recursive arguments, in
  plain order);
- `d⃗ᵢⱼ` — per recursive argument `j`, the **argument's indices**: `ni`
  symbols of arity `np + (#Plain slots before that Rec slot)`.

Arities follow the established `FnSym` convention (`inductive/spec.rs`
**[read]**): dependence is expressed by application. *(That header used to give
the reason as "the kernel has `Formula::subst` but no `Term::subst`". It is
void — term substitution is `derived::subst_term`, five public calls — and the
corrected reason is the seam: the symbol's defining equation is rewritten
along. DECISIONS.md 2026-08-06.)* The restriction this encodes — no
index expression may mention a recursive field — is the same one the thesis's
rules impose (the recursive-argument rule does not extend `Γ`,
`thesis.txt:1798–1801`), and a Lean declaration violating it is
**unrepresentable and must be declined** (§7, §9.2). `RBTree` satisfies it:
`red`'s rec-arg indices `(Color.b, n)` mention only the plain field `n`,
which precedes both `Rec` slots in the order mask `Plain,Rec,Plain,Rec`;
`black`'s `(c₁,n)`/`(c₂,n)` likewise **[decoded]**.

### 3.2 The index space

```text
Idx(p⃗) := Σ x₀:ι₀. … Σ x_{ni−1}:ι_{ni−1}. 1        tup(x⃗) := ⟨x₀,⟨x₁,…⟨x_{ni−1},•⟩…⟩⟩
```

— one `sigma::Telescope` at `(np, [ι₀…ι_{ni−1}])`, giving `intro`,
`proj_mem` and `eta` for free **[read**, `sigma/telescope.rs`**]**. This is
the thesis's `(z₁,…,(zₙ,()))` tuple convention exactly.

### 3.3 The per-constructor `good` value

One `define_by_membership` per constructor mints `Gᵢ(p⃗, σ, r)` — `σ` the tag
payload (the plain-argument tuple), `r` the induction-hypothesis row — with
defining axiom

```text
⊢ ∀p⃗ ∀σ ∀r ∀w.  ( w ∈ Gᵢ(p⃗,σ,r)  ↔
      ( w ∈ Idx(p⃗)
      ∧ ( w = tup(e⃗ᵢ(p⃗, comp₀σ … comp_{kᵢ−1}σ))
        ∧ ⋀ⱼ  tup(d⃗ᵢⱼ(p⃗, …)) ∈ app(app(r, Injⱼ(•)), •) ) ) )
```

i.e. `Gᵢ` is `{tup(e⃗ᵢ)}` when every recursive child is good at its required
index, and `∅` otherwise.

**Both halves of that conjunct are settled, and neither the way this line
guessed.** There is **one** application, not two: the row is consumed at
`wrec_total`'s composite, whose computation rule is a single application, so
`app(r, Injⱼ(•))` already *is* the child's good-set. And the `Injⱼ(•)` is the
plain fibre's: at a constructor taking `RecArg::general` the summand is
`Σ(z::γⱼ)` rather than `1`, and the conjunct is the bounded universal
`∀z. (z ∈ Aⱼ → tup(d⃗ᵢⱼ) ∈ app(r, Injⱼ(z)))` — one conjunct still. The choice is
per **constructor**: at a mixed one every branch is a function, the degenerate
slot included. `inductive/family/gval.rs`'s header carries the argument for
both.

This is the `spec` judgment's `G`, specialised to the set level. The three
`ctor` rules of `thesis.txt:1793–1801` correspond as: the base case is the
`w = tup(e⃗ᵢ)` conjunct; the `∀y : β` rule is absorbed into `σ` being the
telescope tuple (the thesis's `[π₁p′/y][π₂p′/p]` substitutions *are* the
`compⱼ` projections — the mechanism `sigma/telescope.rs` was built to
provide); the recursive-argument rule is the `⋀ⱼ … ∈ app(r,…)` conjunct
(`g (inl (z)) e` with `γ` empty for a plain recursive argument).

*(The parenthetical here read "since plain recursive arguments are the scope —
function-typed ones are declined today and stay declined". **They are not
declined.** `RecArg::general` (`derived/src/recarg.rs`) carries `γ` as a real
telescope, `CtorSpec::rec_doms` (`derived/src/inductive/spec.rs:179`) stores it,
and `gval.rs:37–43` turns the `j`-th summand into `Σ(z::γⱼ)` with the conjunct a
bounded universal. `checker/src/mini/ctor_ix.rs`'s general arm does it at an **indexed**
family, and `checker/tests/fixtures/indexed_infinitary_ctor` reads
`constEv = 4/4, gapped = 0`. The `γ`-empty reading of this rule is still what a
plain argument gets; it is no longer what every argument gets.)*

### 3.4 The `good` recursion, and why it is cheaper than the value recursion

```text
e_G(p⃗)      := the packed step with rows ⟨⟨Injᵢ(σ), q⟩, Gᵢ(p⃗, σ, π₂q)⟩   — one Replacement per ctor
goodrec(p⃗) := wrec(A, B, U({A,T_B}), 𝒫(Idx(p⃗)), e_G(p⃗))
```

— the same `RecCore`/`wrec` apparatus, the same step shape as
`inductive/step.rs` with `valᵢ` replaced by `Gᵢ`. The analogues of
(S1)/(S2) are the same derivations. The analogue of (S3) — `step_typed` — is
where the shape pays off:

> every value `Gᵢ(p⃗,σ,r)` is, by its defining axiom, a subset of `Idx(p⃗)`,
> hence a member of `𝒫(Idx(p⃗))`, **with no hypothesis about `σ` or `r` at
> all**.

So `goodrec`'s totality and ι are **unconditional** (given `closed`, which
`Inductive::closed` discharges at every arity **[read]**). The value
recursor's `HYP` — the pointwise minor-typing bundle that is the general
recursor's one standing hypothesis — simply has no counterpart here. The
per-constructor `good`-ι comes out as

```text
(G-ι)  ⊢ ∀p⃗ ∀y⃗ ∀r⃗. ( Hᵢ^W →
           app(goodrec, ctorᵢ(y⃗,r⃗)) = Gᵢ(p⃗, tup(y⃗), ih-row) )
       with  app(app(ih-row, Injⱼ(•)), •) = app(goodrec, rⱼ)
```

where `Hᵢ^W` is the constructor's argument typings with recursive arguments
at the **skeleton** `W` — exactly (S4)'s `Hᵢ^ctor`, minus `HYP`.

---

## 4. The carrier, membership, inversion

### 4.1 The carrier

```text
ind(p⃗, x⃗) := { s ∈ W(A,B,u) : tup(x⃗) ∈ app(goodrec(p⃗), s) }
```

— one `define_abbrev` of arity `np + ni`, and the thesis's
`λx :: α. {s : Wp:A. B p | rec_W (λp. G p) s x}` (`thesis.txt:1810`) with the
`rec_W … s x` application read as "the index tuple is in the good-set of
`s`". `ind(p⃗,x⃗) ⊆ W` holds for every `x⃗`, including junk ones — a Separation
is a subset no matter what is asked of it — which is what makes the universe
statement (§5.4) quantifier-friendly.

### 4.2 Constructor membership

```text
(M)  ⊢ ∀p⃗ ∀y⃗ ∀r⃗. ( Hᵢ^ind → ctorᵢ(y⃗,r⃗) ∈ ind(p⃗, e⃗ᵢ(p⃗,y⃗)) )
```

where `Hᵢ^ind` is the Lean-shaped hypothesis: plain arguments at their types,
recursive arguments at `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))`.

**(M) as stated here is incomplete, and that was found by building it.**
`derived/src/inductive/family/carrier.rs:64–86` cites this section by name:
`Hᵢ^ind` alone "is not enough" — the real antecedent also carries
`Eᵢ := ⋀ₖ eᵢₖ(p⃗,y⃗) ∈ ιₖ(…)`, the index expressions at their own index types.
The reason is structural rather than an oversight in the proof, and the
discharge is `IndexedCtor::mem_lean` at rule-build time (§8.1's open question,
answered generally rather than per-constructor). Read `carrier.rs` for the rule
this section approximates; the step list below is right about every step it
names and is missing that antecedent.

Derivation: (1) weaken each
`rⱼ ∈ ind(…)` to `rⱼ ∈ W` (Separation), obtaining `Hᵢ^W`; (2) `Ctor::mem`
puts `ctorᵢ ∈ W` (existing **[read]**); (3) (G-ι) computes
`app(goodrec, ctorᵢ)`; (4) `tup(e⃗ᵢ) ∈ Gᵢ(…)` by the defining axiom — the
equality conjunct by reflexivity, the child conjuncts because
`tup(d⃗ᵢⱼ) ∈ app(goodrec, rⱼ)` is exactly what `rⱼ ∈ ind(p⃗, d⃗ᵢⱼ)` unfolds to.
No step is new machinery.

### 4.3 Inversion, and where Leibniz earns its keep

From (G-ι) read right-to-left plus the `Gᵢ` axiom:

```text
(I)  ⊢ ∀p⃗ ∀y⃗ ∀r⃗ ∀x⃗. ( (Hᵢ^W ∧ ctorᵢ(y⃗,r⃗) ∈ ind(p⃗,x⃗)) →
         ( tup(x⃗) = tup(e⃗ᵢ(p⃗,y⃗))  ∧  ⋀ⱼ rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗)) ) )
```

and componentwise `xₖ = eᵢₖ` by Kuratowski injectivity. Every use of these
equalities downstream — moving a motive from index `e⃗ᵢ` to index `x⃗`, the
recursor's typing at the major premise's index — is one `eq_leibniz`. This is
the entire content of "the base case wants `Eq`'s elimination".

### 4.4 Non-vacuity — both polarities, per the standing discipline

A `good` that came out constant would make every theorem above true and
worthless. Pin both directions at the `RBTree` shape (as a derived-layer
test, no Lean syntax):

```text
⊢ leaf ∈ ind(p, ⟨Color.b, ⟨zero,•⟩⟩)                       (M) fired closed
⊢ ¬( leaf ∈ ind(p, ⟨Color.r, ⟨zero,•⟩⟩) )                  (I) + tag distinctness
```

the second from inversion: membership would force
`⟨Color.b,…⟩ = ⟨Color.r,…⟩`, refuted by injectivity plus the enum
distinctness already derived for the index type's own translation. This test
is the analogue of `acc`'s two-polarity witness set and is **not optional**:
it is the only thing that distinguishes `good` from `λs.Idx` (always-true)
and from `λs.∅` (always-false).

---

## 5. The indexed recursor and ι — the §5.4 invention

§5.4 is future work in the thesis; as with `RECURSOR-DESIGN.md`, this part is
ours. The finding is that **almost nothing is new**: the indexed family's
recursor engine *is* the erased declaration's `GenRecursor`.

### 5.1 Why the erased recursor is the right engine

**Scope of this subsection, stated about itself:** it covers the **value
motive** and nothing else. `⟦T.rec⟧ := app(grec(…), t)` below is the term for
that clause; the `Prop`-motive recursor is a separate construction (§5.3,
`checker/src/mini/rec_ix_prop.rs`), as are class (S) and class (P) at an index
(`mini/src/{class_s_ix,rec_s_ix,class_p_ix,rec_trunc_ix}.rs`). §5.3 says this
about §5.1; this paragraph is §5.1 saying it about itself.

Lean's indexed recursor
`T.rec p⃗ (C : Πx⃗. ind p⃗ x⃗ → Sort u₁) s⃗ x⃗ (t : ind p⃗ x⃗)` reduces, at
`t = ctorᵢ …`, to the minor applied to the constructor's fields in declared
order followed by one ih per recursive field — verified against
`RBTree.red`/`black`'s `RecRule::rhs` in the export (`RECURSOR-DESIGN.md`
§10 item 2 — that document's §10 is a flat numbered list, so "§10.2" there
and here means its second item — re-checked here **[decoded]**: `red`'s rhs is
`red n l x r (rec … Color.b n l) (rec … Color.b n r)`). The index arguments
`x⃗` appear in the reduct **only** inside the recursive calls' index spines —
and there they are determined by the child (`d⃗ᵢⱼ`), not free. At the set
level the recursion never needs the indices at all: it runs on the skeleton
tree. So:

```text
⟦T.rec⟧(p⃗, C, s⃗, x⃗, t) := app(grec(p⃗, s⃗, T_policy), t)      — x⃗ dead
```

with `grec` the **existing** `GenRecursor` of the erased spec. The ι
equation the checker must certify beta-reduces on both sides to (S4): on the
left the nest consumes `x⃗` as inert lambda binders; on the right each
recursive call `T.rec p⃗ C s⃗ d⃗ᵢⱼ rⱼ` beta-reduces to `app(grec, rⱼ)`, which is
(S4)'s rhs slot. **The indexed ι is the non-indexed ι with `ni` dead binders
per nest** — `(S4)` plus `2×ni`-ish extra beta obligations, all of the shape
the nest discipline already discharges. No new derived theorem is needed for
ι itself; the one new derived lemma is the `Hᵢ^ind → Hᵢ^W` weakening bridge
(§4.2 step 1) packaged for the wiring — `IndexedCarrier::bridge`, built.

**This section is about the *term* and the *ι rule*, and it is right about
both. It was silent about the recursor constant's *typing*, and that silence is
what `077` blocked on** (2026-08-02, Otto, on reaching it; **closed** the same
day by D8 and `checker/src/mini/rec_ix_dep.rs`). `GenRecursor`'s
conclusion is `app(grec,t) ∈ T` — one target **set**. The obligation at the
nest's bottom is `app(grec,t) ∈ app(⟦C⟧, x⃗, t)`, a **fibre** varying with `t`.
No choice of `T` makes those the same statement, so §5.2 below cannot supply
what is missing however the policy is chosen; and `T := S`, its answer for
`RBTree.id`, is strictly weaker than the goal, since `ind(p⃗,x⃗) ⊊ S`.

The non-indexed clause reaches the fibre through `DepRecursor`, whose `DEPᵢ`
applies the motive to the **tree alone** — `app(C, tⱼ)` at each induction
hypothesis and `app(C, ctorᵢ(y⃗,t⃗))` at the conclusion
(`inductive/motive.rs::dep_minor` **[read]**). Lean's *indexed* minor applies
it at the constructor's own indices, `app(C, d⃗ᵢⱼ, rⱼ)` and `app(C, e⃗ᵢ, ctorᵢ)`,
which a tree-only motive cannot name. So `DepRecursor` is not instantiable at
any `C'` that states Lean's premise: the mismatch is in the **premise**, not in
the wiring, and it is not something a consumer can bridge.

What is owed is the value sibling of D7 — `IndexedPropRecursor` with `•`
replaced by a value:

```text
⊢ ∀p⃗ ∀m ∀S⃗ ∀T. ( PRE → ∀x⃗ ∀t. ( t ∈ ind(p⃗,x⃗) → app(irec,t) ∈ app(m,x⃗,t) ) )

IDEPᵢ(m,Sᵢ) := ∀f⃗ ∀v⃗. ( Aᵢ → Sᵢ⟪f⃗⟫v⃗ ∈ app(m, e⃗ᵢ(p⃗,y⃗), ctorᵢ(y⃗,r⃗)) )
Aᵢ          := `IndexedPropRecursor::minor_atoms` with the mᵢ induction
               hypotheses' `•` replaced by the bound `vⱼ`
```

over `φ(z) := ∀x⃗. (tup(x⃗) ∈ app(goodrec(p⃗),z) → app(irec,z) ∈ app(m,x⃗,z))`,
with `irec := grec(p⃗, gmin⃗, T)` — so this section's term *is* the right term
and (S4) *is* the right ι rule, which is why the silence was easy to miss. It
is `derived/`'s by the boundary rule, and it is **not** a mechanical
generalisation of `prop_rec.rs`: the Prop induction step fires no ι, because
`•` is `•` at every tree, while this one must fire (S4) inside the step and so
needs `guard.rs`'s guarded minors as well. `dep.rs` at an indexed `φ`, in
short. Two atoms of `Aᵢ` are exactly `minor_atoms`', so a consumer that has
already transported the Prop minors transports these unchanged — which is the
one thing that makes the wiring cheap once the rule exists, and the reason to
keep `Aᵢ` **Lean-positional and in the same order**.

**Built as D8, `family/dep_rec.rs`, and consumed the same day.** It cashed: the
consumer's whole difference from the `Prop` clause is one three-field `Clause`
(`checker/src/mini/minor_ix.rs`), because `IDEPᵢ`'s antecedent *is* `minor_atoms_at` at
the bound `vⱼ`. `068` derives at both σ and leaves the blocked list after five
moves; `077` reaches `binder-congruence`. One consumer-side finding, on D8's own
flagged risk: **`ICOV`'s unbounded index binders cost nothing, provided `T` is
the rung the *motive* lives in and not the one its values live in.**
`Rung::app` is `⊢ ∀f ∀x. (f ∈ Uₙ → app(f,x) ∈ Uₙ)`, unconditional in the
argument, so at `T := ⟦Sort ℓ⟧` — `ℓ` the sort the motive's own *type* inhabits
— the whole spine walks at arbitrary arguments with no case split, no
`app_off_domain` and no excluded middle. At `⟦Sort u₁⟧`, which is what the
non-indexed `cod_at_rung` uses, it would have needed all three. The alternative
interface D8 proposes is therefore **not** needed for this consumer; whether a
later one is in the same position is not settled by that.

### 5.2 The `T`-policy for index-dependent motives — void, for the second time

*Rewritten 2026-08-02. What this section proposed is not needed and should not
be built; the reasoning is kept because the shape it recognises is real and
because the section is cited elsewhere.*

`RECURSOR-DESIGN.md` §5.2's three-way target choice died when `motive::cod` and
`guard.rs` made `HYP` dischargeable from `COD ∧ DEP` alone — `checker/src/mini/rec_dep.rs`'s
header records that the target is now simply the sort the motive was declared
into. This section re-introduced a policy for the indexed case on the premise
that the engine is the **simply typed** `grec`. §5.1 above shows that premise is
wrong: a simply-typed engine cannot type the recursor constant at all, and the
engine has to be a dependent rule. Once it is, the target is `⟦Sort u₁⟧`
unconditionally and there is nothing left to choose — so **the family-valued-motive
recogniser does not need to be written**, and the row it was sized as
(`recursor(RBTree: … a value-valued motive)`, filed *threading* on the strength
of "the policy is a mini-side recogniser") is a **library** row. `mini` files it
that way now, named by the construction that is missing.

*Argued, not derived*: the claim that `COD` at `⟦Sort u₁⟧` suffices for the
dependent indexed rule is by analogy with `dep.rs`, where `guard.rs` needs
nothing of `T` beyond `motive::cod`'s two halves. The rule does not exist yet to
check it against, and whoever builds it should check it rather than inherit it.

What follows is the original section.

#### 5.2.1 The shape it recognises (retained)

The value recursor is simply typed (`RECURSOR-DESIGN.md` §5: one target set
`T`). An indexed motive `C : Πx⃗. ind p⃗ x⃗ → Sort u₁` varies with `x⃗` even
when it ignores the tree — so policy 2 ("motive at the first nullary
constructor as the nest walked it") picks `⟦C⟧` at `leaf`'s indices, which
does **not** contain `red`/`black`'s minor values. `077`'s actual Type-motive
site is `RBTree.id`, whose motive is `λ c n t. RBTree α c n` **[decoded]** —
the family itself at its own index binders. For that shape the right target
exists and is canonical:

```text
family-valued motive:  C = λx⃗ t. T′ q⃗ ⃗f(x⃗)  for some translated family T′
                       ⇒  T := S′, the skeleton of T′
```

since every `ind′(q⃗, ⃗f(x⃗)) ⊆ S′` regardless of `x⃗` (§4.1). The `HYP` bridge
is then: Lean's minor typing gives values in `ind′(…)`; weaken to `S′`
(Separation) — the same safe direction as §4.2. For `RBTree.id`, `T′ = T`
and `T := S`, the declaration's own skeleton. Recognising the shape is a
syntactic check on the motive body (the family constant applied to the
motive's own binders / to translated index expressions); anything else
declines to policy 3 (counted gap). This is the one new policy branch; it
sits beside branches 1–3, replacing none of them.

### 5.3 The Prop-motive recursor — a separate construction, and the one that blocks

Two different things live at `u₁ = 0` and only the second was written down here.

**Prop-motive ι *at a use site* is unchanged**: `Certifier::iota` tries
`proof_eq` first **[read**, per `RECURSOR-DESIGN.md` §5.1**]**, and `077`'s
`id_spec` proof — motive `λ c n t. Eq (RBTree.id … t) t`, every `Eq.rec` at
`u = 0` **[decoded]** — never reaches `grec`.

**Prop-motive *typing of the recursor constant* is not covered by §5.1 at all,
and it is what used to block. It is wired** — `checker/src/mini/rec_ix_prop.rs`,
2026-08-02. `068`'s `rbTreeRef := RBTree.rec.{u,u}` is scheduled at `u := 0`
and at `u := 1` **[measured**, `mini --block`**]**; at `u := 0` the recursor's
own levels are `{0,0}`, the motive is `Sort 0`, so the whole recursor type is a
`Prop` (`⊢ ⟦ty[σ]⟧ ∈ ⟦Sort 0⟧`, in hand) and `⟦RBTree.rec.{0,0}⟧ = •`. There is
no `grec`, no `T`-policy and no target set — §5.1's
`app(grec(p⃗, s⃗, T_policy), t)` is the *value* recursor and does not apply. The
obligation is that the motive holds at every inhabitant of the carrier, which
is structural induction with the index carried:

```text
φ(z) := ∀x⃗. ( tup(x⃗) ∈ app(goodrec(p⃗), z) → • ∈ app(m, x⃗, z) )
```

`decl_rect` at that `φ`, with `IndexedCtor::inv` discharging each
`rect_stepᵢ`. §8's D7 states it; nothing in it is new machinery.

**The row it closed was two pairs and only one of them was this.** `068` at
`u := 0` derives. The other pair was `077`'s, which uses `RBTree.rec` at *both*
motive sorts — `Sort 0` for the `Eq` proof and `Sort 1` for `RBTree.id` — and
reported the first gap it met, so it could not say the value clause was also
missing until this one existed. `library-gap` 30 → 28, `threading` 12 → 13,
`constEv` 150 → 151 **[measured]**, and the first blocker is now `068`'s
*second* σ at the **value** clause — which, on reaching it, turned out not to
be §5.2's `T`-policy at all (§5.1, and §5.2 is now void).

**`077` is the other half and a different construction**: `RBTree.id` uses
`RBTree.rec.{1,0}` **[decoded]** — motive `Sort 1`, family-valued
(`λ c n t. RBTree α c n`). That was filed as §5.2's `T`-policy branch and is
not — see §5.1's 2026-08-02 addition: a target policy cannot type the constant,
and what is owed is a dependent rule over the indexed carrier. So the two
`RBTree` eliminator files do not share a construction, and closing one does
not close the other.

**`071` and `072` are not eliminator problems at all**, though they carry the
same `indexed-family(·)` label. Both reported `obligation: the type's
interpretation` **[measured]** — their declarations' *types* mention
`SortElimProp`/`SortElimProp2`, whose **carriers** did not exist, because
`zoneb::build` declined an indexed declaration that is not class (T) before
building anything. They needed the indexed class-(S) carrier (`LeCarrier` at
`ni ≥ 1`) and the indexed class-(P) carrier (`TruncCarrier::over_family`)
wired up — not `RBTree`'s eliminator. *(Both wirings landed:
`checker/src/mini/zoneb.rs` dispatches `class_s_ix::build` and `class_p_ix::build` on
the branch that used to decline, with `checker/src/mini/rec_s_ix.rs` and
`checker/src/mini/rec_trunc_ix.rs` above them. `072` closed at `c425ac5`, `071` with
class (S) at an index. The diagnosis in this paragraph is what the fix
followed.)*
That is the fourth time one gap label has covered more than one problem
(`Acc`, class (P), class (S), here); the label names where the walk stopped,
never what is missing.

---

## 6. §5.3 — subsingleton eliminators, against what `acc` actually exports

### 6.1 `acc^φ_r` is an instantiation, not a module

The thesis (`:1831–1845`) builds `acc^φ_r` from plain `acc` over the subtype
`{x : α | φ x}` with the projected relation `r′`. At the set level both
wrappers evaporate, **because of the two corrections that landed with
`derived/src/acc/` and must not be undone**:

- `step_closed` carries the `x ∈ A` guard the thesis omits, and `preds_in`
  carries `y ∈ A` — without the former, `acc(A,R) = A` for every `R`
  (recorded, with the collapse argument, in `acc/condition.rs`'s header
  **[read]**);
- `R ⊆ A × A` is **not** assumed anywhere — edges leaving `A` are ignored by
  the guards, and the countermodel at `acc_no_two_cycle` (`A := {a}`,
  `R := {⟨a,b⟩,⟨b,a⟩}`, `b ∉ A` — `a` is accessible *relative to `A`* while
  sitting on a 2-cycle through `b`) pins that the `w ∈ A` conjunct is
  load-bearing, not proof-convenience **[read**, `acc/witness.rs:226`**]**.

Consequently, with `A_φ := {q ∈ Idx(p⃗) : φ(q)}` (one Separation),

```text
acc^φ_r  =  acc(A_φ, R)        — R passed through UNRESTRICTED
```

is *definitionally* the φ-restricted accessibility: `preds_in(A_φ,R,C,q)`
quantifies only over predecessors satisfying `φ`, which is precisely the
thesis's intent, and no projected `r′`, no subtype pairing `⟨x,h⟩` (whose
second component would be `•` anyway) and no new module are needed. The
thesis's remark that "large elimination for `acc^φ_r` is derivable because
`∃h : p. q` has projections" becomes trivial: membership in `acc(A_φ,R)` is a
formula, and its "projections" are conjunction elimination.

`φ` and `R` come from §5.3's `LE ctor` recursion (`:1848–1877`), which at the
set level is a **formula** builder, not a set builder: existentially close
each argument (`∃y ∈ β̄ᵢ(…)`), the base case contributing
`q = tup(ē)` to `B` (=φ's matrix) and each recursive argument contributing
`(S ∧ ∃z⃗. q′ = tup(ē′)) ∨ R` to the relation's matrix, exactly per the
thesis's `[S; R]` accumulator. Both land as `define_by_membership`
Separations on `Idx` and `Idx × Idx`. The carrier is
`⟦P x⃗⟧ := [tup(x⃗) ∈ acc(A_φ, R)]` — a conditional singleton, as class (S)
requires at every instantiation.

### 6.2 The degenerate and direct cases are the whole tutorial demand

- **No recursive arguments** (`071_SortElimProp`): the `LE ctor` recursion
  emits `R` with an empty disjunction, i.e. `R = ∅`, and
  `acc(A_φ, ∅) = A_φ` — **already derived**, `acc_empty_relation` **[read]**.
  Carrier `[φ(x⃗)]` outright; intro is Separation-intro at the `mk` instance;
  the recursor's reduct is the minor at the **index projections rearranged
  per the variable–variable equalities** (`mk : ∀b b1 b2. P b b2 b1` ⇒ minor
  applied at `x₂, x₁`) — the thesis's "delayed elimination" of `:1866–1870`,
  which at the set level is: read the fields off `tup(x⃗)` with `compⱼ`,
  permute per the base-case equality, ι is beta. Invention, but small and
  checkable per-file.
- **`Acc` itself** (`117`/`118`): not the general §5.3 translation but the
  interpretation clause `⟦acc_{α,r} x⟧ = [x ∈ acc(⟦α⟧,⟦r̄⟧)]`
  (`thesis.txt:2126`) with `R̄ := {⟨y,x⟩ ∈ ⟦α⟧×⟦α⟧ : • ∈ app(app(⟦r⟧,y),x)}`,
  and `Acc.rec` = `rec_acc`'s `pack`, whose curried `e(x)(•)(ih)` spelling
  was chosen to match Lean's minor **[read**, `rec_acc.rs` header**]**. `R̄` is
  no longer a Separation to be written: it is `quot::rel_graph`, built with
  the four bridge lemmas both this clause and `Quot.sound` consume.

  **`Acc` is complete and this bullet's blocking narrative is history.**
  `mini/src/{acc,rec_acc,rec_acc_ap,rec_acc_ih,rec_acc_value,rec_acc_iota}.rs`
  over `derived/src/{acc,rec_acc}/`; `117` and `118` both certify. See
  MINI-HANDOFF.md §§16, 17, 23, 25, 26.1, 27, 28 — §28 is *"`iota(Acc.rec)`
  closed — `Acc` is done, and the threading axis is empty"*.

  What the bullet got right and is worth keeping is the **ordering**: it said
  (measured, `mini --block`) that both files reported
  `obligation: the type's interpretation, ⟦ty[σ]⟧` with `typesOk=0` and minted
  `fun-typed-rec-arg(Acc)` at `zoneb.rs`'s constructor walk, because the *type*
  of each declaration mentions `Acc.{ℓ}` and `⟦Acc⟧` did not exist — so
  `⊢ ⟦val[σ]⟧ ∈ ⟦ty[σ]⟧` was never attempted, and the three obligations are
  strictly ordered: carrier, then `⟦Acc.rec⟧`'s typing, then the ι. Reading
  `fun-typed-rec-arg(Acc)` as a statement about the recursor inverted that
  order. All three landed in that order.

  The reflexive field is a fact about `Acc` and **irrelevant to this route**:
  `zoneb::build` dispatches on `direct::clause_for` *before* the index check
  and the trichotomy, exactly as it does for `Eq`, so a declaration with a
  direct clause never reaches the walk that refuses a function-typed
  recursive argument. Widening `CtorSpec::recs` would serve the *general*
  translation of `Acc`, which this document has declined to use for `Acc`
  since it was written.

  The two files are also **different problems**, and the scheduled σ decide
  which **[decoded]**: `117` is one pair at `Acc.rec.{0,0}` — a `Sort 0`
  motive, so the eliminator is a proof and no `T`-policy arises — while `118`
  is one pair at `Acc.rec.{1,1}` with motive `fun _ _ => Bool`, a genuine
  large elimination at a *constant* motive, where the target is `⟦Bool⟧` and
  the `T`-policy is trivial. `118`'s reduct has a lambda under the minor (the
  `∀y h. …` ih), the shape that sank `116` on the W side; `rec_acc::ih`/`cval`
  were built as that lambda's graph, so the derived side is ready. *(This
  closed by naming "the wiring bridge from the reduct's lambda nest to
  `ih(accrec,…)`" as new work and a named risk, citing "§9.6" — a section that
  does not exist in this document; the referent is §9's *could not settle*
  item 5. The bridge is built: `checker/src/mini/rec_acc_ih.rs` and
  `checker/src/mini/rec_acc_iota.rs`, MINI-HANDOFF.md §27 piece 4 and §28.)*
- **`Eq`** (28 files): direct clause, §2.2/§2.4. No `acc` involvement.
- A **recursive user-defined subsingleton** (the case needing `acc^φ_r` with
  `R ≠ ∅` and the full §5.3 recursion) has **no witness in the 91 files —
  nor in `init-prelude`** **[decoded**, 2026-08-01, every `.ndjson` in
  `vendor/arena-tests` and `checker/tests/fixtures`**]**. The full list of
  class-(S) declarations anywhere in the repository is `Eq`, `HEq`,
  `SortElimProp`, `T` (`nested-unused-param`) — all **non-recursive**, hence
  degenerate — and `Acc`, which is recursive but *reflexive* (function-typed
  recursive argument), so it is not expressible as an `IndexedDeclSpec` at all
  and takes the direct clause above. `init-prelude`'s other two indexed
  declarations, `Nat.le` and `Nat.le.below`, have **two constructors** and are
  therefore not large-eliminating: class (P), the truncation clause. This
  corrects an expectation recorded during the C0 census that the prelude's
  indexed demand would exercise the general §5.3 route; it does not.

  The carrier is built generally (it is one formula recursion), and so now is
  the **recursor** — `derived/src/inductive/family/le_rec.rs`, §5 of this
  document's §5.4-invention discipline applied to class (S). It is `rec_acc` at
  `(A_φ, R)` plus the edge-introduction rule that makes ι fire, and it covers
  `mᵢ = 0` uniformly, which is the shape the degenerate witnesses need. What
  stays deferred is the **step**: `thesis.txt:1856–1858`'s delayed elimination
  (index tuple ↦ constructor fields) is per-declaration data
  `IndexedDeclSpec` does not carry, so `le_rec` states it as the hypothesis
  `minor_eq` — the same status `step_typed` and the general recursor's
  pointwise `HYP` have — and the wiring owes its discharge.

### 6.3 Class (P) — built, `derived/src/inductive/family/trunc.rs`

`‖·‖` of the lifted §5.2 translation, per `thesis.txt:1813–1815`. The general
route (translate at `ℓ′ ≥ 1`, wrap in `Trunc`) is what landed, at both an
indexed and a non-indexed entry point; `072`'s collapse to
`[∃y⃗. tup(x⃗) = tup(ē(y⃗)) ∧ …]` is not taken as a special case, because the
truncation is one symbol application on a carrier that already exists and the
collapse would save nothing.

Three things this section got wrong, all found by decoding rather than by
reasoning, and all corrected in `trunc.rs`'s header:

1. **The demand is not `072`.** Classifying every `inductive` record in every
   export in this repository by `rec.levelParams` against the declaration's own
   gives **thirteen** class-(P) declarations **[decoded]**: `SortElimProp2`,
   `Nat.le`, `Nat.le.below`, `List.Mem`, `Int.NonNeg` and `Prod.Lex` indexed;
   `Or`, `Exists`, `Nonempty`, `ByteArray.IsValidUTF8`, `BoolProp`,
   `PropStructure` and `PredWithTypeField` not. Three of them — `Nat.le`,
   `Nat.le.below`, `List.Mem` — are **recursive**, which §6.2 said had no
   witness anywhere; that finding was about class *(S)*, and does not carry to
   class (P).
2. **`numIndices > 0` is the wrong census for this class.** Seven of the
   thirteen have no indices at all, so `trunc.rs` serves both shapes. That is
   the opposite of §7.2's policy for class (T), and for a reason: nothing is
   re-derived here.
3. **`ulift` really does cost nothing, and the corollary is bigger than
   expected.** `thesis.txt:2106–2108` gives `⟦ulift_n^n α⟧ = ⟦α⟧` and
   `⟦↑e⟧ = ⟦↓e⟧ = ⟦e⟧` **[decoded]**, so the *same* carrier serves at `ℓ` and at
   `ℓ′` — there is no second W-type at the lifted universe. The level survives
   only in the universe statement, and there class (P) is **cheaper** than class
   (T): `‖a‖ ∈ U₀` is one `cond_in_u0`, with no `C₂`, no `W ∈ U₁` and no
   antecedent, because `‖a‖ ⊆ 1` holds whatever `a` is.

Small elimination only, so there is no recursor **target set**: ι is
`TruncCarrier::only_point` (*every* inhabitant is `•`, so both sides of an ι are
`•` and it holds by reflexivity) plus `TruncCarrier::irrel` to type it.

*(This sentence read "there is no recursor set" and, taken with §8's module
list, would tell a reader that class (P) has no recursor module. **Three exist
and are named nowhere in this document** — `derived/src/inductive/family/`'s
`trunc_rec.rs` (the class-(P) recursor, non-indexed), `trunc_rec_ix.rs` (the
indexed one, sharing `prop_rec`'s `motive_app` spine) and `trunc_fields.rs`
(`le_prop_fields`'s twin), with `derived/tests/family_trunc_rec.rs`,
`family_trunc_rec_ix.rs`, `family_trunc_fields.rs` above them, and
`checker/src/mini/rec_trunc.rs` / `rec_trunc_ix.rs` consuming them. Each carries its own
`MINORᵢ`/`minor_atoms` interface. This is **D5's failure one row over**: a
document that understates its own tree mis-scopes the next task, which is the
lesson §8 records twice and which this section then reproduced.)*

What
does need a derivation, and is the only one in the file, is the Lean-shaped
constructor rule for a *recursive* class-(P) declaration: a recursive argument
of a `Prop` is a proof, so its hypothesis is `• ∈ ‖ind(p⃗,d⃗ᵢⱼ)‖` rather than
`rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)`, and the element has to be eliminated existentially
(`Trunc::elim`, then one `hyp_ex_branch` per recursive argument).

### 6.4 Class-(P) constructors — built, and the reachable consequence is one pair

**Built on both sides.** `derived` always owed nothing here:
`TruncCtor::mem` is `⊢ ∀p⃗∀y⃗∀r⃗. (Hᵢ → • ∈ ‖ind(p⃗,e⃗ᵢ)‖)` and `trunc_mem` is its
Lean-shaped form, both in `derived/src/inductive/family/trunc.rs` and both
exported through `TruncCarrier::ctors`. The whole constant is a proof
(`imax _ 0 = 0` all the way out), so `⟦T.ctorᵢ⟧ = •` and the nest's bottom is
`mem` retargeted onto the former's abbreviation, exactly as the former's own
typing was.

`checker/src/mini/zoneb.rs::build_trunc` **used to** end at `former_at`, computing
`TruncCarrier`'s per-constructor rules and discarding them — the third instance
of "evidence produced and then made unreachable", and what blocked
`069_boolPropRec` on `no-interp(BoolProp.a)`. It no longer does: the non-indexed
route stores `⟦T.ctorᵢ.{σ}⟧` off `site.tc.ctors[site.i]` (`zoneb.rs:1302`, with
the derivation in that function's own header), and the indexed route is
`checker/src/mini/class_p_ix.rs` (landed `c425ac5`, closing `072`), which reports its
own shape failures as `Gap::TruncCtor` (`checker/src/mini/ev.rs`). The paragraphs below
size the *reachable* population and are unaffected by either landing.

**The reachable consequence is far narrower than "a class of constructors"
suggests, and the difference is measured.** A proof-valued
*application* interprets to `•` without ever consulting the head constant:
`070`'s type comes out `f60(⟦Exists.{0}⟧, •, ⟦Exists.{0}⟧, …)` **[measured**,
`mini --block`**]**, where that `•` *is* `⟦Exists.intro α p w h⟧`, and the file
reaches `typesOk=2` with `⟦Exists.intro⟧` never built. Only a **bare `Const`**
routes to the store. So a class-(P) constructor is unreachable exactly when it
occurs unapplied — which, for a declaration with parameters, it never does.

In the tutorials that leaves **one pair**: `069`'s `BoolProp.a`, nullary on a
parameterless `Prop`, appearing bare in `boolPropRec`'s *type*
(`∀ _ : motive BoolProp.a, …`). `Nat.le.refl` and `Nat.le.below.refl` are the
only other nullary class-(P) constructors anywhere and both sit under
parameters, so they always occur applied.

The same short-circuit is why **projections out of a `Prop` structure need no
`StructProj`**: `084`/`086` were predicted to move to that row when class (P)
closed and instead closed outright, `fullyInterpreted=1` **[measured]** —
`projProp1 := fun x => proj x` over a class-(P) `PropStructure` is a
proof-valued application, so `⟦proj x⟧ = •` and the typing is subsingleton
membership. `093`'s surviving `proj(Prod)` is a *data* structure and a
different row. There is no missing thesis clause here: `⟦|e|⟧ = •`
(`thesis.txt:2110`) and Theorem 6.7 part 2 (`thesis.txt:2186`) force the value,
and proof irrelevance covers the projection.

---

## 7. The `DeclSpec` extension

### 7.1 The shape

New type in `derived/src/family/` (or `inductive/family.rs` — placement per
the one-construction-per-file rule), **wrapping** the existing spec:

```rust
pub struct IndexedDeclSpec {
    pub base: DeclSpec,              // the ERASED declaration — unchanged consumers
    pub indices: Vec<FnSym>,         // ι_k, arity np + k;  empty ⇔ non-indexed
    pub ctors: Vec<CtorIndices>,     // parallel to base.ctors
}
pub struct CtorIndices {
    pub result: Vec<FnSym>,          // e⃗_i : ni symbols, arity np + k_i
    pub rec_args: Vec<Vec<FnSym>>,   // d⃗_ij : per Rec slot, ni symbols,
                                     //         arity np + plains_before(j)
}
```

`well_formed` extends `DeclSpec::well_formed` with the arity checks above and
`rec_args.len() == base.ctors[i].recs`.

**The defining axioms these symbols cross the seam with point in opposite
directions, and nothing recorded it until a consumer was written against
them.** `IndexAx` (`checker/src/mini/zoneb.rs`) publishes, per constructor:

```text
tr.ax.ctors[i].result[k]      ⊢ ∀p⃗ ∀y⃗. ( eᵢₖ(p⃗,y⃗) = ⟦eₖ⟧ )       derived LEFT
tr.ax.ctors[i].rec_args[j][k] ⊢ ∀p⃗ ∀y⃗<ⱼ. ( dᵢⱼₖ(p⃗,y⃗<ⱼ) = ⟦dₖ⟧ ) derived LEFT
tr.ctor_abbrev[i].1           ⊢ ∀f⃗. ( cᵢ(f⃗) = ctorᵢ(y⃗,r⃗) )      derived RIGHT
```

So on the two index axioms the symbol `derived` states a formula at is the
**left** endpoint and the interpretation is the right; on the constructor
abbreviation it is the other way round — mini's own `cᵢ` is on the left and
`derived`'s `ctorᵢ(y⃗,r⃗)` on the right. A consumer that assumed one orientation
for all three gets a decline reading "a published conclusion axiom is about
another symbol", which says nothing about the cause. `TgBackend::ix_concl_bridge`
accepts either end and bridges from the other; that is not defensive coding but
the actual shape of the seam.

### 7.2 Wrapper, not field — the judgment call, argued

The `Slot` mask went the other way (fields added to `CtorSpec` in place), so
this deviates from precedent and should say why. Three reasons:

1. **The erased spec is the identity the shared machinery is keyed on.**
   `Machine`/`Inductive`/`GenRecursor` consume `DeclSpec` and are cached
   against it; `goodrec` (§3.4) is *also* the erased declaration's `wrec` at
   another target. Growing index fields inside `DeclSpec` would make every
   existing consumer carry fields it must ignore, and the ignoring would be
   an invariant ("the carrier does not read `indices`") instead of a type.
2. **The non-indexed path stays a special case, and must.** Routing
   `ni = 0` through the subset carrier would wrap `Bool`/`N`/`List` in a
   provably-vacuous Separation (`INDUCTIVES.md:176`'s collapse), re-deriving
   the whole zero-gap fragment through `ind(p⃗) = {s ∈ W : • ∈ …}` — real
   cost, zero benefit, and a direct violation of the "fragment stays 27/27"
   non-negotiable. The vacuity collapse is a theorem worth *testing* (one
   witness: derive `ind(p⃗) = W` at an `ni = 0` toy spec), not a code path
   worth taking.
3. The `Slot` precedent's own caveat pointed here: "whether to put the mask
   on `CtorSpec` or on a thin `RecSpec` wrapper is the … task's call — the
   carrier files must not be churned" **[read**, `RECURSOR-DESIGN.md`
   §3.1**]**. The mask was consumed by the same module family; the index
   data is consumed by a *new* module family. Wrapping is the no-churn
   answer.

So: **the non-indexed path stays a special case; the indexed construction is
a new consumer of the same machine.** What must change inside
`inductive/spec.rs` itself: nothing. (`spec.rs`'s header sentence "adding
[an index field] would not be an extension of this construction but a
different one — it needs the equality type first" is half-superseded by this
document: a different construction, yes; the equality-type prerequisite is
void per §2.4. Correct that header in place when D1 lands.)

---

## 8. Ordered implementation plan

Boundary rule throughout: `derived/` speaks `Term`/`Formula`/`FnSym` only;
everything touching `ExprPtr`/`NamePtr`/export data is `checker/` (`tg.rs`)
— and, since the mini port shares `derived/` wholesale and reimplements only
clause dispatch **[read**, `checker/src/mini/interp.rs` header**]**, each checker
rung below lands twice (tg.rs and `mini/`), against the same derived
exports.

**Derived side** (one construction per file; every rung with its own
two-polarity witness test):

- **D1** — **Built**, `family/spec.rs` + `family/index.rs`:
  `IndexedDeclSpec`/`CtorIndices` + `well_formed`; the `Idx` telescope assembly
  (§3.2, reusing `sigma::Telescope`); `inductive/spec.rs`'s header sentence
  fixed in place (§7.2). Small, and it was.
- **D2** — **Built**, `family/gval.rs` + `family/goodstep.rs`: the `Gᵢ` symbols
  and the `good` step Replacements; (S1)/(S2) analogues; **unconditional**
  `step_typed` (§3.4). Mostly `inductive/step.rs` at a different value slot, as
  predicted.
- **D3** — **Built**, `family/good.rs` + `family/carrier.rs` +
  `family/vacuous.rs`: `goodrec`, (G-ι), the
  `ind(p⃗,x⃗)` Separation, membership (M), inversion (I), and the §4.4
  witness pair (`derived/tests/family.rs`, both polarities and the strong
  emptiness form). **← was the riskiest derived rung**: (M)/(I) compose a `wrec` ι with
  a `define_by_membership` unfolding under an ambient hypothesis across `n`
  branches — the same risk profile (S3) had, and like (S3) it has no
  hand-written ancestor at its shape.
- **D4** — **Built**, `family/universe.rs`: `⊢ [H →] ind(p⃗,x⃗) ∈ U₁` = `DeclUniverse`'s
  `wty_in_u1` + one `C₂` (`cumul/chain.rs:86–87` **[read]**), `∀`-closed over
  `x⃗` with no new antecedent — the list stays exactly `A ∈ U₁` (§7 of
  `cumul/decl.rs` unchanged). For class (S)/(P) carriers there is **no
  universe obligation at all**: `[φ] ∈ U₀` is `Tower::cond_in_u0`
  (`tower/rungs.rs:289` **[read]**), and membership at higher levels is
  `u0_mem` + transitivity. This settles the task's question 5: the
  subset-of-W carrier costs one lemma over the existing chain; the acc
  carrier costs zero.
- **D5** — **Built**, `family/le.rs` (class S), with `le_rec.rs`, `le_prop.rs`,
  `le_index.rs`, `le_prop_fields.rs` and `le_prop_rec.rs` beside it: the
  `LE ctor` formula recursion producing `φ`/`R`; carrier `acc(A_φ, R)`; the
  degenerate-`R` corollary via `acc_empty_relation`; the index-projection minor
  for the non-recursive recursor (§6.2). It was independent of D2–D4, as
  predicted.

  **`le_index.rs` is the carrier *term* at `ni ≥ 1`** and it was missing from
  this list for two rounds after it landed (`90d9bf3`), which cost a later seat
  a scoping pass on work that was done — D6's failure exactly, one entry
  further down. `LeCarrier` stops at the *set* `acc(A_φ,R)`;
  `LeIndexCarrier::build` mints the conditional singleton
  `χ(p⃗,x⃗) = [tup(x⃗) ∈ acc(A_φ,R)]` of arity `np + ni` over it, exports `chi`,
  `in_u0`, `intro`, `elim`, `only_point`, `irrel` and a per-constructor
  `ctor_intro`, and reaches other index terms through `at` / `chi_at` /
  `cond_at`. Consumed by `checker/src/mini/class_s_ix.rs` and `rec_s_ix.rs`; pinned by
  `derived/tests/family_le_index.rs`. `SCOPING.md` §6 is the scope it was built
  against and now records it as landed.
- **D6** — **Built**, and it was listed unmarked here long after it existed,
  which is how a doc that understates its own tree mis-scopes the next task.
  The `Hᵢ^ind → Hᵢ^W` weakening bridge is `IndexedCarrier::bridge`
  (`family/carrier.rs:370`), `⊢ ∀p⃗∀x⃗∀z. (z ∈ ind(p⃗,x⃗) → z ∈ skel(p⃗))`; the
  (S4)-reuse statement of §5.1 is pinned by
  `derived/tests/family.rs::the_erased_recursor_iota_fires_on_indexed_arguments`
  at exactly the RBTree-shaped spec this line asked for — 3 ctors, masks as
  decoded, 2 indices over an enum and a recursive type — firing `red`'s ι with
  both children supplied as *indexed* memberships and leaving only the erased
  recursor's own `HYP`.
- **D7** — `family/prop_rec.rs`: the **indexed Prop-motive elimination rule**
  (§5.3), one theorem per declaration, generated at declaration time. **Built**,
  `IndexedPropRecursor::over_family`, tests in
  `derived/tests/family_prop_rec.rs`:

  ```text
  ⊢ ∀p⃗ ∀m. ( ⋀ᵢ MINORᵢ(m) → ∀x⃗ ∀t. ( t ∈ ind(p⃗,x⃗) → • ∈ app(m, x⃗, t) ) )

  MINORᵢ(m) := ∀f⃗. ( Aᵢ → • ∈ app(m, e⃗ᵢ(p⃗,y⃗), ctorᵢ(y⃗,r⃗)) )
  ```

  with `Aᵢ` the conjunction, **in this order**, of

  ```text
  the kᵢ + mᵢ FIELD atoms in DECLARED order:
      yⱼ ∈ βⱼ(p⃗, y⃗<ⱼ)                    at a Slot::Plain
      rⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))             at a Slot::Rec, at its own indices
  then the mᵢ induction hypotheses:
      • ∈ app(m, d⃗ᵢⱼ(p⃗,y⃗), rⱼ)          one per recursive arg
  ```

  Export `Aᵢ` atom by atom (`minor_atoms: Vec<Vec<Formula>>`), as
  `IndexedCtor::mem_atoms` and `TruncCtor::trunc_atoms` do, plus the binders it
  is stated at (`minor_vars`). **The quantifier prefix `∀f⃗` is the
  constructor's *declared* field order, and the atoms match it.** This is a
  correction to what this section said until D7 was built: it specified
  plains-then-recs "matching `rect_step`", with the consumer permuting by the
  `Slot` mask. Nothing about the mathematics changed and `rect_step` is
  untouched — the permutation moved *inside* `over_family`, on three grounds.
  (1) A class-(T) minor premise is a `Prop`, so `• ∈ ⟦minorᵢ⟧` unfolds binder
  by binder into `∀ (declared field). (its typing → …)` with the IHs innermost
  — decoded at `RBTree.red` (mask `Plain,Rec,Plain,Rec`) as `n, l, x, r, ih_l,
  ih_r`, concluding `motive Color.r n (red α n l x r)` with the IHs at
  `motive Color.b n l` and `motive Color.b n r`. Prenexing that list is
  arithmetic; re-sorting it by a mask is a silent failure mode. (2) The
  declared order is dependency-correct, since `d⃗ᵢⱼ` mentions only the plains
  preceding that `Rec` slot, so plains-then-recs buys nothing. (3)
  `TruncRecursor::minor_atoms` and `IndexedCtor::mem_atoms_lean` are already
  Lean-positional; a second order here would be the third spelling of one list.
  The motive is applied **curried**, indices then major premise
  (`prop_rec::motive_app`), which is Lean's own `motive c n t` spine.

  Composition, not new machinery: `decl_rect` at `φ(z) := ∀x⃗. (tup(x⃗) ∈
  app(goodrec(p⃗), z) → • ∈ app(m, x⃗, z))`; each `rect_stepᵢ` from `MINORᵢ` by
  `IndexedCtor::inv` (which gives `tup(x⃗) = tup(e⃗ᵢ)` and `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)`),
  Kuratowski injectivity for `xₖ = eᵢₖ` componentwise, `IndexedCarrier::good_of`
  to fire `φ(rⱼ)` into the IH, and one `eq_leibniz` per index to move the
  conclusion from `e⃗ᵢ` to `x⃗`; the final step is `subset_w` + `good_of` at the
  major premise. All of that held on contact; nothing outside `family/` was
  needed and no new lemma fell out.

  **The symbols-versus-interpretations move is the consumer's, at a `mem`-shaped
  position, and D7's inside the motive's spine.** `mini`'s
  `ctor_ix::index_congr` moves a fact at `⟦x⃗⟧` to the same fact at the `e`
  symbols along their defining axioms, and degenerates to reflexivity at a
  closed index — but it congruences over a *single `FnSym` applied to
  `p⃗ ++ x⃗`*, which is `ind(p⃗,x⃗)`'s shape and not `app(m, x⃗, t)`'s. The motive's
  spine is a nest of **binary `app` nodes**, so the same move inside an IH atom
  or a minor's conclusion has to be folded down it one node at a time. That fold
  belongs to whoever defines the spine, so it is `prop_rec`'s:

  ```text
  ⊢ ∀m ∀a⃗ ∀t ∀b⃗ ∀u. ( (a₀ = b₀ ∧ (… ∧ (a_{ni−1} = b_{ni−1} ∧ t = u))) →
        app(m, a⃗, t) = app(m, b⃗, u) )                        [motive_congr]
  ```

  `ni + 1` equations, **the subject last and included** — the minor's conclusion
  needs `ctorᵢ(y⃗,r⃗)` moved as well, and a subject *retarget* cannot reach it
  because the constructor sits inside an *argument* of the membership, not at
  its subject. `motive_congr_of` applies it, reading the spine terms off the
  equations so a caller cannot mis-order the instantiation; pass `eq_refl` where
  a position does not move. An equation **may carry the caller's own `Γ`**, and
  the result carries exactly the union and nothing else: the subject equation is
  a β down the constructor's λ-nest and arrives as a *sequent*, which is not the
  same thing as an implication antecedent and is not covered by wrapping the
  scheme in `a1i`. Refusing it was a defect, found by the first real consumer
  (`068`'s Prop half, Otto), and it had already cost a second copy of the fold
  in `mini`; the shape guard is unchanged, so a `Γ` buys no leniency about what
  the fold produces. Everything else D7 owes is that the terms needing
  the move are enumerable, and they are: the `e⃗ᵢ` in `minors`' conclusions and
  the `d⃗ᵢⱼ` in `minor_atoms`' recursive and IH entries. The conclusion's `x⃗`
  need no move — they are `∀`-bound.

  **Consumed 2026-08-02** (`checker/src/mini/rec_ix_prop.rs`) and it fitted. One
  interface defect surfaced and is fixed: `motive_congr_of` refused a
  hypothesis-carrying equation and the minor's *conclusion* needs one, because
  moving `⟦C e⃗ᵢ (T.ctorᵢ p⃗ y⃗ r⃗)⟧` onto `app(m, e⃗ᵢ, ctorᵢ(y⃗,r⃗))` goes through a
  β down the constructor's λ-nest that carries that nest's scope assumptions as
  a sequent `Γ`. It cost a second copy of the fold in `mini` for one commit;
  the relax landed above and the copy is deleted, so both of the consumer's uses
  — the induction hypotheses and the conclusion — go through the one entry
  point. Everything else was used as written: the Lean-positional `minor_vars`,
  so level `l` answers atom `l` with **no permutation in the consumer at all**;
  the subject being one of the congruence's equations, which is what reaches the
  constructor term inside an argument; and `eq_refl` at a position that does not
  move.

  Two-polarity witness, both cashed: the rule is fired end to end at the RBTree
  spec against a *concrete* motive (a nest of three constant lambda graphs, so
  every minor is genuinely discharged and the conclusion is closed — and it
  reaches the rule's own spelling through `motive_congr_of`, so the exported
  congruence is the one production exercises), the same
  nest with its innermost value `∅` makes `MINOR_leaf` **refutable**, and at
  `(b, Inj₂(•))` — an index no constructor produces — `empty_at_index` proves
  the rule's own conclusion with no minor spent, so the theorem says nothing
  there. A synthetic family with two recursive arguments at **swapped** indices
  (`l` at `(a,zero)`, `r` at `(zero,a)`, result `(b,a)`) isolates the pairing
  pin, and the three claims around it are now measured in the tests rather than
  argued here, because two successive drafts of this line got them wrong. At
  `derived`'s own spelling **nothing** is blind: `d⃗ᵢ₀` and `d⃗ᵢ₁` are always
  different `FnSym`s, of different arities whenever a plain field separates the
  two `Rec` slots. After unfolding — the consumer's spelling — `black`
  distinguishes them at `c₁`/`c₂` and `red` does not, both children landing on
  `(b, n)`. What no corpus constructor supplies is a *reversal*, which is what
  the synthetic is for.

- **D8** — **Built**, `family/dep_motive.rs` + `family/dep_guard.rs` +
  `family/dep_rec.rs`: the indexed eliminator at a **value** motive. Not in the
  original plan, because §5.1 and §5.2 between them said `derived/` owed nothing
  here; §5.2 above is the correction and §5.3 has the statement, the consumer's
  `ICOV` verdict and the standing **ι** gap. Recorded here so that §8's list does
  not understate the tree, which is the failure D6 had.

  Two things from building it that live in the code rather than in §5:
  `guarded`'s Separation symbol was missing the declaration's own parameters —
  latent and harmless on the non-indexed path, whose `psi` mentions none, fatal
  on this one — and `guard.rs`'s plumbing is now a shared
  `guarded_core`/`unguarded_core` parameterised by the guard, with the
  non-indexed path a thin caller.

**Checker side** (tg.rs, then mini):

- **C0** — lift `Decline::Params`: the `np > 0` type-former lambda-graph
  nest and parameter spines. **Prerequisite, not indexed-specific** — it is
  already its own recorded item ("the spec is general in `np`; there would
  be nothing to attach it to" **[read**, `gen_scope`**]**), it currently
  declines 35 tutorial occurrences, and `RBTree` (`np = 1`) is unreachable
  without it. Do it first and bank its own corpus movement.
- **C1** — spec builder: walk `num_indices` binders, build
  `IndexedDeclSpec`; the branch trichotomy of §2.1 (reading the recursor's
  `levelParams` for S/P); new decline variants (`IndexRecFieldDep`,
  index-shape mismatch) replacing the blanket `Decline::Indices` — which
  today fires 106 times on the tutorials and is the single largest decline
  row **[read**, `MEASUREMENTS.md`**]**.
- **C2** — carrier + constructor wiring for class (T) indexed: type former
  as an `np + ni`-graph nest, constructor memberships from (M). Measurable:
  `042`'s declaration-checking gaps.
- **C3** — recursor nest: index binders dead in the bottom (§5.1), the
  family-valued-motive `T`-policy branch (§5.2 — **void**, see there),
  pointwise-`HYP` bridging through D6. **← riskiest step overall**, same grounds as every prior
  wiring rung — this is where derived statements meet nest-computed terms,
  and where all five recorded late surprises lived. Measurable: `068`, and
  `077`'s Type-motive site.

  **Done** — the `Prop` half as `checker/src/mini/rec_ix_prop.rs` (§5.3, so no `grec`
  and no `T`-policy) and the value half as `checker/src/mini/rec_ix_dep.rs` (§5.1's
  term, D8's typing), over one shared minor transport,
  `checker/src/mini/minor_ix.rs`. *(This said "What C3 still owes is **ι**, which D8
  does not build; §5.1's argument that it is the erased ι with `ni` dead binders
  is untested." **It is built and consumed.** `derived`:
  `IndexedDepRecursor::{iota, iota_atoms, iota_vars}` in
  `family/dep_rec.rs:38–55`. `mini`: `checker/src/mini/iota_ix_dep.rs`, wired into
  `checker/src/mini/kernel.rs`'s constructor-match branch. `dep_rec.rs:44` answers §5.1
  by name: "§5.1's 'the erased ι with `ni` dead binders' is not a remark about
  the term — it is the statement".)* Two things it met that this
  plan did not name, both recorded here because the value half meets the first
  of them again:

  1. **`⟦dₖ⟧ ∈ ⟦Iₖ⟧` has exactly one source, and it is inference.** The atom
     `rⱼ ∈ ind(p⃗,d⃗ᵢⱼ)` and the binder domain `⟦T p⃗ d⃗⟧` differ by one β down
     the type former's nest, and β consumes one membership per index. `d⃗ᵢⱼ`'s
     defining axioms give the *terms* and not the memberships, and the
     recursive argument's index expressions live inside the minor's Lean type
     where an interpretation walk cannot infer anything. So the minor walk
     opens the minor's binders on the **checker's own** telescope
     (`push_interpreted` at the domain the Π-interpretation recorded) and
     `ctor_ix`'s `infer_indices` runs there unchanged. `rec_dep::minor_at`'s
     interpretation-only walk cannot be reused at `ni > 0` for this reason
     alone.
  2. **The set-swap has to happen at each binder's close.** `rec_dep` converts
     the interleaved `∀w.(w ∈ D → …)` family into the prenex `∀f⃗.(⋀A → …)`
     using an *unconditional* equation between the two spellings of `D`. Here
     the equation is that β step and carries the scopes' own hypotheses, so it
     cannot survive to the final `gen_all_checked`. `rec_ix_prop::domain_swap`
     discharges and rewrites the domain in one step, innermost first, while the
     outer scopes are still open — the same move `zoneb`'s summand-leg close
     makes.

  Neither is about indices *per se*; both are about a β step under a binder,
  which is what §5.2's branch will also be doing.
- **C4** — the direct clauses, each small and independently landable:
  `Eq.rec` as the minor-projection nest (`094`); `Acc`/`Acc.rec` via
  `acc` + `rec_acc` (`117`/`118` — flag the reduct-lambda bridge, §9's
  *could not settle* item 5);
  class-(S) degenerate (`071`); class-(P) truncation (`072`).

Acceptance gates per the non-negotiables: fragment 27/27 at 0/0, arena
152/0/2, all existing zero-gap files byte-identical, `HAS_GAPS` rows removed
one at a time as they close.

### 8.1 Status, 2026-08-02 — C0/C1/C2 landed, C3's `Prop` half landed

**C0 is done and measured on its own**, per its own instruction. The whole of
the Lean-facing layer is now general in `np`: the type former is a nest of `np`
lambda graphs (`tg.rs::gen_ty_nest`, a `GenTyNest`), every constructor's nest
and `CtorRule` carries the parameter spine ahead of its fields, and the general
ι rule takes `p⃗` from `ta[..np]`. The `T`-policy and the recursor nest were
already written in `np` and needed no change. `MEASUREMENTS.md` has the
numbers; the short version is **`init-prelude` 15572 → 15492 gaps at +49% wall
clock**, and the tutorials do not move at any of the three instantiation sets.

Three things the design did not say, all of which C1–C3 will meet again:

1. **A declaration one of the hand-written recognisers owns must never fall
   through to the general path**, even when the recogniser refused a particular
   *use*, and saying so takes two guards. `ind_const_recognised` returns `None`
   for both "not my shape" and "my shape, but not for this use", and conflating
   them builds a *second* carrier for the same inductive over the other stack's
   incompatible sets — `ind_abbrev` then re-mints `⟦List⟧` and `interp` stops
   being a function on that constant, which is the recorded failure that cost 54
   ι sites. The shape-only `recognised_ind` gate in `ind_const` and
   `gen_rec_bottom` is the first guard; the second is that it must **not**
   consult `is_recursive`, because while an inductive is being checked the
   checker installs a temporary `InductiveData` with `is_recursive: false`
   (`inductive.rs:116`) and `list_shape`/`nat_shape` therefore refuse their own
   declarations for the duration. Found by reading `076_listRecReduction`'s
   ledger rows, not by a test: one
   `shared inductive symbols declined: body not canonical` where there had been
   none, and it did not move when only the first guard was in place. §8's C2/C3
   inherit both — the seam is the same, and an indexed family's own check will
   be inside exactly that window.
2. **`rec.levelParams` is `[motive, ind…]`** — the motive's level is *first*,
   so the declaration's own instantiation is the **tail** of the recursor's
   **[decoded**, `042`'s `RBTree.rec` is `[35, 5]` against `RBTree`'s `[5]`,
   and `076`'s `List.rec` is `[9, 2]` against `List`'s `[2]`**]**. This is what
   the wiring design left unchecked. *(This attributed the phrase "an
   export-format convention this has not been checked against" to
   `WIRING-DESIGN.md` §6.1. That sentence is not in `WIRING-DESIGN.md`
   anywhere — the wording belongs to `SCOPING.md:1510` / `MEASUREMENTS.md:2051`.
   The **fact** is independently decoded above and is not in doubt; only the
   attribution was.)* It is checked now, and it is what lets a
   level-polymorphic declaration be eliminated at all.
3. **`βⱼ`'s stored body is not usable at a use site once `np > 0`.** It is
   stated over the *walk's* parameter variables, so the body at actual
   parameters has to be read off `βⱼ`'s **instantiated defining equation**
   (`inst_all` substitutes into the formula). *(This said "the kernel has no
   `Term::subst`". Since 2026-08-06 it has `derived::subst_term`, so the body
   could be substituted — but the equation is what a consumer wants anyway,
   because it is the seam between `βⱼ` and the caller's own term.)* The same applies to the raw carrier `W`, which is why
   `fire_general` uses `recursor::carrier_at` at `p⃗` and checks it against
   `ind.ty_ax` rather than using `ind.wty`. Any C2 code that wants
   `eᵢₖ`'s or `ιₖ`'s body at a use site is in exactly this position.

**C1–C4 are not started *in `checker/src/tg.rs`*.** Nothing in
`derived::inductive::family` is reachable from `tg.rs`; `RBTree` still declines
there, now under a sharper reason (see below). That is still true — `tg.rs` has
no `IndexedDeclSpec`, no `family::`, and `gen_scope` still returns
`Decline::Indices` — and it is the reason this §8 plan is not yet purely
historical. *(Partly overtaken, 2026-08-14: mini now **publishes** its indexed
class-(T) translation and its `IndexedDepRecursor` package across the `EnvCore`
seam, so the evidence is reachable from `tg.rs` even though no consumer reads
it yet. The sentence's claim about `IndexedDeclSpec` and `family::` names in
`tg.rs` remains true and is the right test of C1–C4's status.)* **On the mini side all four landed**; see the paragraph below, which
covers C1–C3, and note that C4 landed too: `094`, `117`, `118`, `071` and `072`
all certify.

*Superseded on the mini side, 2026-08-02.* C1 and C2 landed (`checker/src/mini/zoneb.rs`'s
`build_indexed`, `checker/src/mini/ctor_ix.rs`), and C3's `Prop`-motive clause landed as
`checker/src/mini/rec_ix_prop.rs` and `checker/src/mini/rec_ix_dep.rs`; **C3's ι at a
value motive landed too** — `checker/src/mini/iota_ix_dep.rs`, 670 lines, routed live
from the `num_indices != 0` arm of `checker/src/mini/kernel.rs`'s recursor
dispatch. *(This paragraph said "what is left of C3 is **ι** at a value
motive". That was true when written and is not now. `MINI-HANDOFF.md` §26
supersedes it. Anyone sizing the indexed-ι tranche off this sentence sizes it
as a missing construction; the construction exists, is complete, and fires in
this binary today — which is why the tranche is a consumption problem. See the
2026-08-14 note at the end of this section for what the consumption problem
actually is, because it is not the one the sentence implies either.)*
`RBTree` is off the evidence ledger entirely — carrier,
constructors and both eliminators — and `068` is no longer the corpus's first
blocker, for the first time in the project. `tg.rs` is untouched — the rungs land
twice, and this is the first of the two. Point 3 below bit exactly as written:
the recursive argument's `d⃗ᵢⱼ` had to be read off an *instantiated* defining
equation rather than a stored body, and the memberships that equation's β step
consumes had to be inferred at the nest, which is what forced `rec_ix_prop`'s
minor walk onto the checker's own telescope. What C2 will hit first, and what this document does not answer: (M)'s
`ni` extra antecedents `Eᵢ` are **not positional against the constructor's Lean
spine**, and `has_type_ctor_app` instantiates a `CtorRule`'s premises
positionally against it (`tg.rs:8711`, the refusal at `tg.rs:8746`). So `Eᵢ`
cannot simply be appended to `CtorRule::prems`: either the rule grows a second,
subject-addressed premise list, or `Eᵢ` is discharged at rule-build time. For
`RBTree.red` the second is available — `n ∈ N` *is* the field premise `β₀`'s
own atom and `Color.r ∈ Color` is closed — but that is an argument about one
constructor, not a general answer, and it should be settled before C2 is
written rather than during. *(It was, and the second option is what was taken —
generally rather than per-constructor. `derived/src/inductive/family/carrier.rs:88–118`
cites this paragraph and answers it with `IndexedCtor::mem_lean`: `Eᵢ` is
discharged at rule-build time.)*

One decline row changed meaning as part of C0, and it is the census §2.2 asks
for at prelude scale: `gen_scope` now tests the **eliminator trichotomy before
`num_indices`**, so `…declined: indices` counts only class-(T) indexed
families — the ones §5.2 would serve — while every indexed `Prop` (`Eq`, `HEq`,
`Acc`, …) lands in `…declined: sort-ambiguous or Prop (class S/P)` where §5.3
and the truncation clause will find it.

### 8.2 What consuming the indexed ι in `tg.rs` actually costs — measured, 2026-08-14

`ORIGIN-RANKING.md` ranks this the largest tranche in the tree and sizes it as
"~800–1000 lines of wiring, no new `derived/` theorem", on the reading that
`IndexedDepRecursor::iota` already concludes the rule and only the publication
was missing. **The first half is right and the second is not.** Recorded here
because §8.1 is where a seat will look.

* **No new `derived/` theorem is needed.** Confirmed. `IndexedDepRecursor::iota`
  (`derived/src/inductive/family/dep_rec.rs`) concludes the indexed ι at Lean's
  own minor with the index vector eliminated, and mini fires it live.
* **The publication really was missing, in two places, and is now fixed.**
  `zoneb.rs`'s indexed branch filled `IndApparatus::indexed` without publishing,
  and `rec_ix_dep.rs`'s value clause inserted a `DepElim` without the
  `publish_dep_elim` its non-indexed sibling performs three lines from the
  identical insert. `EnvCore` now carries `ix_translated` and `ix_dep_elims`.
* **But receiving the rule is not enough, and this is the part the sizing
  missed.** The rule is `∀p⃗ ∀m ∀S⃗ ∀T. (PRE → …)` with
  `PRE = ICOD(m,T) ∧ IDEP(m,S⃗)`, and **`tg.rs` cannot discharge `PRE`**:
  - `tg.rs` contains **zero** occurrences of `IDEP`, `ICOD`, `idep` or `icod`;
  - `derived/` *states* the premise (`family/dep_motive.rs`'s `icod` and
    `idep_parts`) but only as `Formula` builders — stating is not discharging;
  - the only thing that discharges it is `checker/src/mini/minor_ix.rs` (895
    lines), whose `transport_at` at `ni > 0` reads a recursive field's index
    expressions **out of Lean syntax in mini's `E` representation** and which
    every caller reaches through a live `mini::kernel::Checker`. `TgBackend`
    holds the same Lean syntax as `ExprPtr<'t>` and holds no `Checker`.

  This is `NAT-CHAR-CENSUS.md` §3 B's obstruction — "everything mini publishes
  to tg arrives as finished data through the shared const store, not as a
  resumable checker" — resurfacing at a second site. It is a *premise-discharge*
  problem, not a wiring problem, and no amount of publication reaches it.

**Two routes reach it. Do not transliterate `minor_ix` into `tg.rs`** — that is
900 lines of the most intricate code in the tree and it would be a second copy
of a module mini owns. But note carefully what the semantic-ownership rule does
and does not forbid here, because the obvious reading of it is wrong:

> TG must consume mini's exact carriers, recursors and certificates. It is
> **not** forbidden from discharging a premise about them. `tg.rs` already
> discharges the *non-indexed* `DEP` itself, in `dep_minor_typed`, walking the
> minor's own Lean binder type — and `dep_minor_typed` is TG-native, not a port
> of mini's `minor` module.

So the two candidates are:

**(A) Write `ix_dep_minor_typed` in `tg.rs`, beside `dep_minor_typed`.** The
established precedent, and the closer one: TG already holds what it needs —
`dom_exprs[np+1+i]` is the minor's declared binder type and `derive_iota_core`
already walks binder telescopes over `ExprPtr`. What is new against
`dep_minor_typed` is that a recursive slot's induction hypothesis sits at the
child's own index vector `d⃗ᵢⱼ`, read off the constructor's binder type, so the
walk needs `ind_spine_at`'s equivalent over `ExprPtr` (~40 mechanical lines) and
the per-child index memberships. Bigger in `tg.rs`, ~400–600 lines, and it keeps
the premise discharge on the side that has the use site.

**(B) Publish the *discharged premise* from mini.** Less `tg.rs` code, and it
has this going for it:

* `rec_ix_dep::rec_bottom` already derives `PRE` at the checker's **telescope
  binders** — `c.binders(depth)` / `c.scope_vars(depth)`, i.e. kernel free
  variables, hence generalisable — and `premise_at`'s own doc states that the
  eliminator's nest and a use site "want the *same* premise about *different*
  terms".
* So mini can generalise that derivation and publish
  `⊢ ∀p⃗ ∀C ∀S⃗ ∀T. (typings → PRE)`, and `tg.rs` instantiates it at the use
  site's own terms and discharges `typings` from the `obligations` it already
  computes in `derive_iota_core`.
* **The shape to copy is `DepBottom::cod_gen`**, which does exactly this for the
  `COD` half of the non-indexed `PRE`: derived once per declaration with
  `cod_at_funspace`, closed with `derived::gen_all`, and consumed in `fire_dep`
  by two `inst_all`s and a `u_mp`. The indexed row wants the same move applied
  to the whole premise rather than to one conjunct.
* **Its weakness, and it is the reason (A) is listed first.** `cod_gen` is
  derived by `tg.rs` from a `derived` function that takes only `ind`; nothing in
  the tree currently publishes a *discharged, generalised* premise across the
  seam, so (B) needs mini-side generalisation machinery that does not exist —
  `PRE` is proved under the scope's memberships, and closing it means turning
  those into antecedents in the order `tg.rs` can supply them from
  `obligations`. Verify that `Closed::discharge` gives that shape on the nose
  before committing to (B); if it does not, (A) is the cheaper of the two.

**Whichever is taken, settle it before writing rather than during.** The
measurement that prices it is not `NANODA_ASSUME`'s: the deletion makes the
origin *acquire* `PRE` as an antecedent, so it prices a world in which the
premise holds and says nothing about whether either route can establish it.
That is the whole distinction this section exists to record.

### 8.3 Measured against the code, 2026-08-15 — route (A) taken as far as the rule

Route (A) is taken. `RecBottom::IxDep` and `mini_ix_dep_rec_bottom` adopt mini's
published `IxDepRec` and `IndexedTranslation` whole, `rec_nest` builds the nest,
and `fire_ix_dep` instantiates `IndexedDepRecursor::iota[i]` at the use site.
Four things were measured that this section had marked open or got wrong.

1. **The nest's difference from `RecBottom::Dep` is arity, and only arity** —
   `depth == np + n + ni + 2`, with the `ni` index binders *inert at the bottom*
   because the ι rule eliminates the index vector. All three declarations build
   a nest and reach the rule. §8.2's ~40 mechanical lines for an `ind_spine_at`
   equivalent over `ExprPtr` is right; it is 10.

2. **The premise's difference is not arity, and the brief that scoped this said
   it was.** `minor_atoms_general`'s plain atoms are the non-indexed ones
   exactly, but a recursive atom is `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))` — a different set
   *per slot*, at the child's own index vector — where `DEP`'s is `tⱼ ∈ W` at
   one carrier moved along one bridge, and the induction hypothesis is
   `vⱼ ∈ app(m, d⃗ᵢⱼ, tⱼ)`. The index **terms** come from
   `IndexedDeclSpec::rec_index_vec` and need no Lean syntax; only the
   **memberships** the β step consumes are inference's.

3. **`has_type_a` types index expressions at 35 of 35** (`RBTree.rec` 24,
   `Aux.rec` 9, `Ix.rec` 2), 17 unconditionally and 18 on assumptions that are
   the walk's own binder typings — 0 foreign. `SEAM-DESIGN.md` §6's residual
   risk is resolved in the favourable direction. `TgBackend::ix_index_census`
   is the measurement and stays in the tree.

4. **But that rate does not generalise to `ICOD`, and this is the new
   obstruction.** `ICOD(m,T)`'s discharge needs `⊢ ⟦T p⃗ → … → Sort u₁⟧ ∈ Uℓ` —
   the motive's own *type* in the rung, which is what
   `crate::mini::rec_ix_dep::icod_at_rung` starts from. Asking `has_type_a` for
   it **fails at every rung**, measured. The rung itself is found correctly, so
   this is not a target-availability failure of the kind §6 analysed.

   *This item then attributed the failure to `gen_scope`'s `Decline::Indices`
   and concluded that `has_type_a` was the wrong route. **Both halves are wrong,
   and §8.4 is the measurement that refutes them.** The top-level miss is
   `HtMiss::Pi`, "a `Π` — needs `dprod_in_universe`": `has_type_uncached`'s
   structural match has no `Expr::Pi` arm at all, indexed or not, so the ask
   dies before any indexed family is looked at. `Decline::Indices` is real but
   one level down and reached by a different path — `typeable_shape` →
   `interpreted_shape` → `gen_scope` — where it is a documented **cost** guard,
   not a soundness one. And the recommended remedy, deriving `doms[np] ∈ Uℓ`
   from `IndexedTranslation::ii.carrier` through the rung's closure lemmas, is
   not the route that works: `ii.carrier` carries `subset_w` but no universe
   membership, `IndexedUniverse::ty_in_u1` never crosses the seam, and the
   skeleton's own `W ∈ Uₙ` is not published either, so that route bottoms out
   in re-deriving mini's whole `decl_universe`. The route that works needs
   neither — see §8.4.*

The site declines naming the premise, and the row now prices exactly the
tranche: `ctor_abbrev_major` 2 firings −23, `mutual_aux_encoding` 3 firings −47,
`077_RBTree.id_spec` 3 firings −19 — 8 firings, **−89**, against
`ORIGIN-RANKING.md`'s hand split of the same number out of a −117 label.

What remains after that is TG-native and is the honest ~800–1000 lines the
ranking predicted: `RecBottom::IxDep`, a `mini_ix_dep_rec_bottom` that reads the
published package and checks identity, and a `fire_ix_dep` following
`iota_ix_dep.rs`'s four-step composite. Two of its steps have no non-indexed
analogue and should be budgeted separately — a recursive atom is
`tⱼ ∈ ind(p⃗, d⃗ᵢⱼ(p⃗,y⃗))` at the child's *own* indices rather than `tⱼ ∈ W`, and
step 4's reverse chain carries an index vector per child. `fire_ix_dep` is
*simpler* than `fire_dep` in one respect that partly pays for this:
`IndexedDepRecursor`'s theorems are already `∀`-closed, so none of
`DepBottom`'s `iota_gen`/`refl_gen`/`gvars` hoisting is needed.

### 8.4 `ICOD` discharged, 8 of 8 — measured, 2026-08-15

`TgBackend::ix_icod` re-derives `ICOD(⟦C⟧, T)` at the rung `DepElim::target`
names and checks it against `subst_f(&dr.guards.cod, &sub)`, `derived`'s own
formula at this site's substitution. It fires at **8 of 8** firings of the
tranche — `Ix.rec` 2, `Aux.rec` 3, `RBTree.rec` 3 — and **no publication was
added**. The seam rule holds: `ICOD` is an inference and it was re-derived
TG-side from published *objects* only.

**What §8.3 item 4 got wrong, and what the obstruction actually was.** Asking
`has_type_a` for the motive's type dies at `HtMiss::Pi` — there is no `Expr::Pi`
arm in `has_type_uncached`, so the *whole file* had no `Π`-formation rule, for
any declaration. Walking the telescope leaf by leaf separates two further
failures that item 4 read as one:

| leaf | at `U₂`, the motive's type's rung | at `U₁` |
| --- | --- | --- |
| each index domain (`Nat`, …) | **not** typed | typed |
| the major's domain `T p⃗ x⃗` | not typed | **not** typed |
| the body `Sort u₁` | typed | — |

So there were **three** missing facts, not one, and only the second is about
indices at all:

1. **`Π`-formation.** `crate::pi_store::Full::rule` —
   `⊢ ∀q⃗ ∀c ∀A. ((A ∈ U(c) ∧ ∀x. (x ∈ A → b(q⃗,x) ∈ U(c))) → dprod(q⃗,A) ∈ U(c))`
   — already exists on the **shared** `Π` store both engines mint into; the
   checker simply passed `want_full = false` and never asked. `pi_in_rung` asks,
   and nothing new is minted by asking: the `dprod` symbol is the one `interp_pi`
   built and only the proofs about it are added.
2. **`⟦T p⃗ x⃗⟧ ∈ U₁`.** Mini already publishes the type former's own typing
   `⊢ ⟦T⟧ ∈ ⟦Π p⃗ x⃗. Sort ℓ⟧` through the shared `ConstStore` — measured
   present at every firing before anything was changed. What blocked the
   application rule from standing on it was `typeable_shape`'s cheap screen,
   which routes an inductive through `interpreted_shape` → `gen_scope` →
   `Decline::Indices`. That guard is documented in its own header as **a cost
   guard, not a soundness one** ("answering `true` only lets a rule be
   attempted"), so it is widened for exactly the families mini has published an
   `IndexedTranslation` for. The walk then fires `ApStep::FiredDProd` and the
   family's domain types.
3. **Cumulativity.** `X ∈ Uₖ → X ∈ Uₙ`, one `Rung::transitive` at the rung below
   per step (`lift_rung`). This is what the index domains needed and nothing in
   `checker/` had ever consumed a rung closure lemma before.

**The prize is not only `ICOD`.** Item 2's widening is a general fact about
typing an indexed family's applications, and it moves the ratchet on its own:
`077_RBTree.id_spec` **41 → 28** gaps and its escapes **19 → 6**, with the
export corpus **185 → 172** over 91 exports and 16 still holding gaps. The other
two declarations of the tranche do not move yet — `ctor_abbrev_major` 46 and
`mutual_aux_encoding` 96 are unchanged — because their remaining gaps are the ι
sites themselves, which still decline on `IDEP`.

**Falsified three ways**, each dying where predicted: one `Rung::app` step
dropped from `ICOV`'s spine dies at the statement check against
`dr.guards.cod` (a *true* theorem, the wrong one); the `interpreted_shape`
widening removed puts 077 back at 41 gaps and 19 escapes with `ICOD`
discharged 0; the cumulativity clause disabled fails the `mini_designed` test at
its first assertion.

**What is left is `IDEP` alone**, and the ~800–1000 lines above are its size.
The decline now says so.

### 8.5 `IDEP` discharged on the `np = 0` declarations — measured, 2026-08-15

`PRE = ICOD ∧ IDEP` is derived at every firing of `Ix` (8 conjuncts of 8) and
`Aux` (18 of 18), checked against `subst_f(&dr.premise, sub)`. `RBTree` is 3 of
9 — `leaf` only; `red` and `black` stop *before* the indexed machinery, at a
minor premise `nest_chain` did not type, which is a different wall and is
counted as one.

**One of §8.3 item 2's three differences runs the favourable way.** The
antecedent is `minor_atoms_general`'s own list, which is in **declared** field
order with the `m` induction hypotheses after it — where `dep_minor`'s is
grouped plains-then-recs-then-ihs. So each rung's atom index *is* its position,
and the `rung: Vec<(Term, FreeVar, usize)>` indirection `dep_minor_typed` needs
to map declared order back onto grouped atoms disappears. The indexed walk is
**simpler** than the non-indexed one at this point, not harder; §8.3 costed
three differences and this is a credit against them.

The other two are as flagged. A recursive slot's bridge is one congruence per
index over `IndexedCarrier::ty` against the published `rec_args` axioms, and its
induction hypothesis is the *same* construction over the motive's spine — which
is why `ix_slot_bridge` is one function and not two. The conclusion moves in
`ni + 1` positions at once, and its constructor position needs mini's
`beta_spine` as `adopted_lam_step`s (`ix_ctor_spine`), whose domain premises are
the rung typings the walk has just produced.

**`RBTree`'s wall is not this tranche's, and it is not the `Π` hole either.**
`red` and `black` stop before any indexed machinery runs, at
`obligations[np+1+i]` — the minor premise's own typing, which `nest_chain`
could not produce. Measured on `077`: the miss is `HtMiss::Lam`, **"a lambda
whose typing rule did not apply"** (20 bodies, 14 unshown, 12 raw fallbacks),
i.e. `has_type_lam` declining on the minor's λ. It is *not* §8.4.1 item 1's
missing `Expr::Pi` arm; `ht_shape` on a minor's declared **type** says "a Π"
for any minor whatever, so that reading is tautological and was discarded.
Two separate holes, and `RBTree`'s −19 is behind the `has_type_lam` one.

**A fieldless constructor still takes the parameters' typings.** `⟦cᵢ p⃗⟧` is a
nest over the parameters even with no fields at all, so `RBTree.leaf` — fieldless
and parameterised at once — needs them to reach mini's own term. §8.3 did not
flag this and the non-indexed row never meets it, because its nullary shortcut
instantiates `ctor_abbrev` at `[]`.

### 8.6 The composite lands — −70 of the −89, measured 2026-08-15

`ctor_abbrev_major` 46 → **23** and `mutual_aux_encoding` 96 → **49**, both
exactly what `NANODA_ASSUME` priced for `IDEP` against the current base. Every
remaining gap on the two is an escaped assumption at the boundary; escapes went
21 → 23 and 46 → 49, the written trade. `077` is unmoved at 28 and the corpus at
172, for the reason in §8.5.

**Two things were wrong in the surrounding machinery, and both were invisible
until the tranche succeeded.**

1. **The indexed nest was never marked `adopted`.** `interp` hands back *mini's*
   term for a recursor mini has stored, so a nest built here started
   `nest_chain` at a head the redex's own interpretation is not. Nothing
   reported it: `derive_iota_core`'s only check is a final endpoint comparison
   whose message says the equation does not match the reduction. `RecBottom::Dep`
   had taken the adopted path since it landed; the indexed row simply was not
   added to the `usable` match.
2. **The readiness rows were emitted only on failure.** They lived inside
   `origin_report`, which returns early when there are no gap origins — exactly
   the state this tranche was trying to reach. The moment the ι rule started
   certifying, every row vanished and the two tests reading them went red on
   *success*. They are now `ix_readiness_report`.

**`Hᵢ` was priced before it was built and is not the cost the sizing feared.**
Every atom at a use site types conditionally on its own binder — the
dischargeable kind — and the distance to `derived`'s set is a bridge
`ix_slot_bridge` already had. The first pricing asked at `ind(p⃗, d⃗ᵢⱼ)` and every
recursive field came back "a local, carried as an assumption, by design": a
local has a typing at the type its *binder* declares and nowhere else, so asking
at the derived set measures the bridge and not the typing.

**One shape the minor premise's own walk never meets**: a use site writes a
domain through its own `def` (`IxA`, not `Ix Tag.ta`), which is a nullary
abbreviation symbol `target_head_step` has no head to step. The bridge takes a δ
step from `abbrev_defs` first. The recursor's *declared* minor type never has
that shape, which is why only the use-site walk needs it.

---

#### 8.4.1 Three findings that are not about indexed families

Recorded here because all three were found by walking one telescope, and none of
them is a fact about `ICOD`.

1. **`has_type_uncached` has no `Expr::Pi` arm, for any declaration.** Not an
   indexed-recursor fact — a hole in the typing rules with a general blast
   radius, and the rule it wants (`pi_store::Full::rule`) has been sitting on
   the shared `Π` store the whole time behind `want_full = false`. What else was
   downstream of it is **unmeasured** and is its own tranche; measure it before
   sizing it, because `HtMiss::Pi`'s raw count is obligations *asked*, not
   declarations that would move.

2. **A guard that declines for cost must say so at its call site.** The
   `Decline::Indices` that blocked this tranche is documented as a cost guard in
   `typeable_shape`'s own header ("a cost guard, not a soundness one … answering
   `true` only lets a rule be attempted") — and that header is not where anyone
   reads it. The reader is at the *call site*, where an obligation comes back
   `None` and the only visible fact is a decline naming indices. Three tranches
   this week were blocked by a guard whose documentation already said it was not
   load-bearing. **A `Decline` variant that exists for cost should be named so
   at the point it is returned**, or the next seat will price it as an
   obstruction again — as `§8.3` item 4 did.

3. **`checker/` had never consumed a rung closure lemma**, and after this change
   it consumes them **only along the `ICOD` path**. `ty_in_rung`, `pi_in_rung`
   and `lift_rung` are private and reached from `ix_icod` alone; `has_type_a`
   does not call them, so every other obligation in the checker still has
   neither Π-formation nor cumulativity. Generalising means having `has_type_a`
   dispatch into `ty_in_rung` when its target is a rung's `set`, which is one
   arm and a real blast radius — deliberately **not** taken here, so that the
   ICOD landing is attributable.

---

## 9. Failure modes and open questions

Failure modes (each must surface as a counted decline or a conditional
certificate — never a wrong `Proved`):

1. **Index expression mentions a recursive field** — unrepresentable in
   `CtorIndices` (§3.1); decline (`IndexRecFieldDep`). Same status as the
   existing `RecFieldDep`: no corpus witness, not tested against a live
   kernel whether Lean even accepts it (open, inherited from
   `RECURSOR-DESIGN.md` §9.4).
2. **`good` degenerating to a constant** — caught only by the §4.4
   two-polarity witness; a missing negative witness would let an
   always-true `good` ship every (M) and no (I) content. This is the
   design's own vacuity hazard; the test is part of D3's definition of done.
3. **Family-valued-motive recogniser misfiring** (§5.2) — a motive that
   *looks* family-valued but isn't lands in policy 3: conditional `HYP`,
   undischargeable, counted. Safe direction.
4. **Mutual / nested / function-typed-rec-arg indexed families** — out, as
   before, now with the index axis multiplied in; the existing declines
   cover them because `gen_scope`'s checks run before and independently of
   the index walk.

   *(This item said, of the function-typed case, that "the demand is **zero,
   not small**" — no representable witness in the tutorials or the prelude,
   `Acc` only apparently an exception — and concluded that widening
   `CtorSpec::recs` from a count to a telescope "should be ranked as
   speculative until a witness exists rather than as measured work". **The
   witness arrived and the widening landed.** `CtorSpec` carries `rec_doms:
   Vec<Vec<FnSym>>` beside `recs: usize` (`derived/src/inductive/spec.rs:156,179`),
   with `with_rec_doms` and a `well_formed` clause at `:275`; `115`–`118`
   certify; `derived/tests/family_infinitary.rs` and
   `checker/tests/fixtures/indexed_infinitary_ctor` are the witnesses at both ends.
   The blast-radius sizing — `step.rs`, `values.rs`, `typed.rs`, `iota.rs`,
   `rect.rs::recarg_eta` all keying on `finord(m)` — was right about the shape
   of the change and is now a record of it, not a forecast. What is still
   witness-free is the narrower `MIXED` case: a plain recursive field beside a
   function-typed one **at an indexed family** (`checker/src/mini/ctor_ix.rs:145–155`;
   the derived side is ready, `derived/tests/family_infinitary.rs`'s `mixed`).)*
5. **Per-instantiation drift** — the branch is per-declaration (§2.1); the
   recursor's extra level `u_1` is per-σ as today. Nothing new, but C1 must
   route the trichotomy through the declaration's *symbolic* level, exactly
   as `provably_nonzero` already does, or the LPI §3.3 design error returns.

Could not settle:

1. **Whether `077`'s remaining 53 gaps are all RBTree-opacity cascade.**
   Predicted (the file's gap history halved when an unrelated guard change
   landed, so its composition is volatile); needs one `stepcount` run with
   C0–C3 stubbed to attribute rows. Do it before C3, not after.
2. **The ih-row spelling in `Gᵢ`** (§3.3): whether `good`'s step reuses
   `wrec`'s `⟨f,r⟩` pair or only `r`, and the exact application depth. A D2
   decision; both spellings derive, one composes with (S4) more cheaply.
3. **`goodrec`/`grec` cache coexistence**: both are `wrec` instances over
   one `Machine`; whether the per-declaration memo (which must store both,
   with certificates, per the standing memo rule) needs a key extension I
   did not verify against the current cache keying in `tg.rs`.
4. **The general recursive §5.3 recursor** (user-defined WF predicate,
   `R ≠ ∅`): **settled** — carrier §6.1, recursor
   `derived/src/inductive/family/le_rec.rs`. Still no corpus witness anywhere,
   tutorials *or* `init-prelude` (§6.2, corrected). Two lemmas fell out that
   neither `acc` nor `rec_acc` had: **A4**, `acc::acc_pred_closed` (an
   `A`-predecessor of an accessible point is accessible), and
   `rec_acc::Bounded` (`accrec`'s values are in `T`, and its own induction
   hypothesis is in `ih_bound(A,T)`). A4 is what keeps `∅ ∈ T` off the
   hypothesis list, which matters because `T` is often a skeleton `W`. What
   remains open is the *step builder*, not the recursor.
5. **`118`'s reduct-lambda bridge** (§6.2): `rec_acc`'s `ih`/`cval` were
   shaped for it, but the wiring from Lean's `λ y h. Acc.rec … (h y h′)`
   nest to `ih(accrec, …)` is unwritten and is the same *kind* of shape that
   made `116` a permanent decline on the W side. If it fails, `118` stays a
   counted gap and nothing else regresses.
6. **Whether `068`'s symbolic-level `RBTree.rec.{u,u}` sites all ground
   through the instantiation pre-pass** — expected (the pre-pass exists for
   exactly this), not checked against `068`'s schedule.
