# The `Sort 0` clause for `Quot` — model analysis

Question: what is the interpretation of `Quot α r` when `α : Prop`, given that the
equivalence-class construction `quot(A,R) ⊆ 𝒫A` cannot land in `⟦Sort 0⟧`?

Sources read for this note: thesis.txt (§2.7.1 at 812–831, §3.1.1 at 1022–1029,
§6.1 at 1905–1935, §6.2 at 2040–2140, §6.3 at 2183–2415), `derived/src/quot/*`,
`derived/src/tower/rungs.rs`, `derived/src/prop/*`, `derived/src/anchor/falsity.rs`,
`kernel/src/thm.rs` (`define` and its choice note), `mini/src/kernel.rs` (`add_quot`),
`mini/src/zoneb.rs` and `checker/src/tg.rs` (`provably_nonzero`), MINI-DESIGN.md
§6.2–6.4, LEVEL-POLYMORPHIC-INDUCTIVES.md §2–3.4.

## Verdict in five lines

1. The observation is **confirmed**, with one refinement: the classes clause fails at
   `Sort 0` on every *inhabited* proposition (refutably, not just unprovably), and
   accidentally passes on the empty one.
2. The right `Sort 0` clause is the **identity interpretation**:
   `⟦Quot α r⟧ = ⟦α⟧`, `mk` and every proof to `•`, `lift` (into Type) to `⟦f⟧` itself.
   It costs approximately zero new theorems.
3. There is **no genuinely uniform clause**, and the obstruction is threefold; the
   only mathematically uniform candidate (choice representatives) is closed off by
   this kernel's own foundation, deliberately and correctly.
4. The split is **not a new decision point**: it is the proof-split the interpretation
   already performs at every application, lambda and Π. `provably_nonzero` is the
   **wrong instrument**; the right one is the ground level numeral plus the threaded
   `⊢ ⟦α⟧ ∈ U₀` certificate (the existing `is_prop` witness).
5. The `ℓ > 0` clause is sound as built, but has an unstated sub-case of its own
   (`lift` into `Prop` — the thesis hedges there too, `n′ ≥ 1` at thesis.txt:2359)
   and one genuinely missing seam (the `R̄`-graph conversion). Details in §6.

---

## 1. The observation is confirmed

### 1.1 `⟦Sort 0⟧` really is the subsets of `1`

Thesis.txt:2040: `U0 = {∅, {•}}` with `• = ∅`; a proposition is interpreted via
`[p] = {x ∈ {•} | p}` (thesis.txt:2059), so `A ∈ U₀ ↔ A ⊆ 1`. The code agrees
exactly: `Tower::u0_members` is `⊢ ∀p. (p ∈ U₀ ↔ (p = 0 ∨ p = 1))`
(`derived/src/tower/rungs.rs:57`), `derived/src/prop/cond.rs` builds every
proposition as `χ = {x ∈ 1 : φ}`, and MINI-DESIGN.md §6.3 fixes `⟦Sort 0⟧ = U₀`
with the `is_prop` witness `⊢ ⟦ty⟧ ∈ U₀`. The question does not dissolve.

### 1.2 The countermodel, in the code's own terms

Take `A = 1 = {•}` (any inhabited proposition), `R` arbitrary. Then, from the
interfaces in `derived/src/quot/`:

- `eqv_refl` (`eqv.rs`) is unconditional in `R`: `⟨•,•⟩ ∈ eqv(1,R)`.
- `class(1,R,•) = {y ∈ 1 : ⟨•,y⟩ ∈ eqv} = {•} = 1` (`class_self` + `class_subset`).
- `quot(1,R) = {c ∈ 𝒫1 : ∃x.(x ∈ 1 ∧ c = class(1,R,x))} = {1}` (`quot_symbol`).

And `{1} ∉ U₀` is **refutable**, not merely unprovable: by `u0_members`, membership
would force `{1} = 0` (false: `1 ∈ {1}`) or `{1} = 1 = {0}` (forces `1 = 0`,
refuted by `u0_two_valued`, `rungs.rs:63`). So a wiring that used the classes
clause at `Sort 0` would face a formation obligation `⊢ quot(A,R) ∈ U₀` whose
negation is a theorem. The failure mode is a permanent gap, not unsoundness — the
kernel cannot certify a false membership — but the clause is dead on arrival.

A second, independent way to see it cannot be rescued: the classes construction
lives inside `𝒫A`, and **rung 0 is not power-set closed** — `Tower::at`'s own
comment (`rungs.rs:303`): `𝒫{0} = {0,1} = U₀ ∉ U₀`. `pow` (`rungs.rs:84`) is a
closure of `U(x)`, i.e. of rungs ≥ 1 only. Nothing `⊆ 𝒫A`-shaped can be placed in
`U₀` by the tower's theorems, for any `A` at all.

### 1.3 One refinement to the expert's statement

At `A = 0`: `quot(0,R) = {c ∈ 𝒫∅ : ∃x.(x ∈ ∅ ∧ …)} = ∅ = 0 ∈ U₀`. So "lands
outside `⟦Sort 0⟧` exactly when Lean says it should land inside" is right as an
indictment of the clause but overstates pointwise: the clause fails on every
**inhabited** `Prop` and accidentally passes on the empty one. Since `Quot.mk` and
the ι-rule only ever fire on inhabited quotients, the failure covers every case
that matters.

### 1.4 What the thesis actually says (it hedges, knowingly)

The thesis's interpretation clause is stated uniformly (`⟦α/R⟧ = ⟦α⟧/∼`,
thesis.txt:2132) but its **soundness case is proved only for `n ≥ 1`**:
"Suppose `Γ ⊢ α : Un` with `n ≥ 1`" (thesis.txt:2353), and `lift`'s target is
likewise assumed `n′ ≥ 1` (thesis.txt:2359). Meanwhile §3.1.1 (thesis.txt:1022–1029)
explicitly admits prop-level quotients exist in Lean — it builds its second
non-transitivity example out of exactly `p : P`, `R : p → p → P`, `lift` into
`α : U₁`. So the thesis **has no `Sort 0` quotient clause**; the `n ≥ 1` hypothesis
is a silent gap, and anything we do here is an extension, not a reading. The
construction below is nonetheless taken from the thesis's own remark at
thesis.txt:828–830:

> "the other constants and the computational rule would all be satisfied with the
> definitions `α/R := α`, `mkR a := a`, `liftR f h := f`" — everything but `sound`.

At `Sort 0`, `sound` is the one obligation that comes free (proof irrelevance:
any two elements of a subset of `1` are equal), which is exactly why the identity
reading is the right clause there and only there.

## 2. The right `Sort 0` clause: the identity interpretation

### 2.1 The clause

Given the certificates the checker already threads — `Γ ⊢ A ∈ U₀` for `A := ⟦α⟧`
(the `is_prop` witness of `α`, MINI-DESIGN.md §6.3) — define, at ground level
`u = 0`:

```text
⟦Quot α r⟧γ        := ⟦α⟧γ                          (r is not consulted)
⟦Quot.mk r a⟧γ     := •     (it is a proof; forced by the proof-split, §4.1)
⟦Quot.lift β f h⟧γ := ⟦f⟧γ  when lvl(β) ≥ 1
                   := •     when lvl(β) = 0   (the whole lift is a proof)
⟦Quot.ind β h⟧γ    := •     (its result ∀q, β q is a Prop)
⟦Quot.sound …⟧γ    := •     (as at every level)
```

Note `⟦Quot α r⟧` and `⟦α⟧` are the *same term*. The model may conflate types that
Lean keeps definitionally distinct — it already interprets every true proposition
as `1` — and no certificate ever flows from model equality back to defeq, so this
is harmless and is what makes the clause nearly free.

### 2.2 The exact obligations, and what discharges each

Writing `B := ⟦β⟧`, `f̄ := ⟦f⟧`, `[φ]` for the conditional singleton, `fs` for the
function space, obligations per primitive at `u = 0`:

| # | obligation | discharged by |
|---|---|---|
| T1 | formation: `Γ ⊢ ⟦Quot α r⟧ ∈ U₀` | is literally the threaded witness `Γ ⊢ A ∈ U₀`; zero new theorems |
| T2 | `mk` typing: `Γ ⊢ • ∈ A` | from `Γ ⊢ ⟦a⟧ ∈ A` via `falsity::prop_subsingleton` — this is `mini::interp::point_of_proof` (interp.rs:591), unchanged |
| T3 | `lift` typing, `v ≥ 1`: `Γ ⊢ f̄ ∈ fs(A, B)` | is `f`'s own typing certificate, **verbatim** — `⟦Quot α r⟧ = A` makes the two funspace terms identical |
| T4 | ι, `v ≥ 1`: `Γ ⊢ app(f̄, ⟦Quot.mk r a⟧) = app(f̄, ⟦a⟧)` | two `Thm::eq_leibniz` steps along `⟦mk…⟧ = •` and `⟦a⟧ = •` (both from `point_of_proof`); app-congruence is one Leibniz instance at `φ(x) := app(f̄,⟦a⟧) = app(f̄,x)` |
| T5 | `lift` typing, `v = 0`: `Γ ⊢ • ∈ [∀x ∈ A → • ∈ B]` | is `f`'s own certificate: `α → β` and `Quot α r → β` interpret to the *same* conditional singleton, since the domains are the same term; ι at `v = 0` is proof irrelevance (both sides proofs of `β`) |
| T6 | `ind` typing: from `Γ ⊢ ḡ ∈ fs(A,U₀)` (motive) and the hypothesis's certificate `Γ ⊢ • ∈ app(ḡ, •)`-shaped, conclude `Γ ⊢ • ∈ [∀q ∈ A → • ∈ app(ḡ, q)]` | subsingleton transport: `q ∈ A → q = •` (`prop_subsingleton`), then Leibniz on `app(ḡ, ·)`, then `cond_intro`. **This is the one genuinely new composed lemma** |
| T7 | `ind` ι (`ind β h (mk r a) ≡ h a`, present in mini/src/kernel.rs:2564) | both sides are proofs of `β (mk r a)`-typed Props: `point_of_proof` on each side, `trans`/`symm` |
| T8 | `sound` typing: `Γ ⊢ • ∈ [t₁ = t₂]` where `t₁ = ⟦mk a⟧`, `t₂ = ⟦mk b⟧` | both provably `•`: `eq_refl`, Leibniz, `cond_intro`. `r a b` is never consulted — `sound` is *free* at `Sort 0`, because `A` is a subsingleton |

Total new `derived/` surface: T6 (one lemma, roughly
`⊢ ∀A ∀g. ((A ∈ U₀ ∧ (g ∈ fs(A,U₀) ∧ • ∈ app(g,•))) → ∀q. (q ∈ A → • ∈ app(g,q)))`
or its curried per-certificate form) plus, if not already a one-liner somewhere,
the app-congruence Leibniz instance for T4. Nothing from `derived/src/quot/` is
used at `u = 0` at all: no `eqv`, no `class`, no Replacement, no funspace lift,
and `r`'s graph need not even be constructed.

### 2.3 `Quot.lift` out of a `Prop` quotient into `Type` is real, and costs nothing

Checked against the primitive types as ported verbatim in `mini/src/kernel.rs`
(`add_quot`, lines 2496–2523): `Quot : ∀(α : Sort u), (α → α → Prop) → Sort u` and
`Quot.lift` carries an independent `sort_v` for `β`. Nothing ties `v` to `u`;
`u = 0, v = 1` typechecks, and thesis §3.1.1 exhibits precisely that instance —
it is Lean's second source of algorithmic non-transitivity ("lift acts like a
subsingleton eliminator in this case", thesis.txt:1024).

Under the identity clause this large elimination is free: `⟦Quot α r⟧ = A` and
`f̄ ∈ fs(A,B)` **is already** a function on the quotient, because the quotient *is*
the domain. This is worth stating as the design reason and not just a convenience:
any clause that moved `⟦Quot α r⟧` "away" from `A` (e.g. `{1}`) would need a
definable section back to representatives to build `lift`'s function — which is
where a choice operator would sneak in (§3.2). The identity clause is the unique
reading in which `lift` into `Type` requires no new function at all.

(On the non-transitivity itself: not our problem. The checker follows Lean's
algorithmic acceptance and certifies only what is accepted; the model validates
all of `≡`, so every accepted chain — including `lift f H q ≡ f h` via proof
irrelevance `q ≡ mk h` followed by ι — certifies through `point_of_proof` + T4.)

## 3. There is no uniform clause — three candidates, three obstructions

### 3.1 Candidate A: literal equivalence classes at both ends — **refuted**

§1.2. `quot(1,R) = {1} ∉ U₀`, refutably. Also blocked wholesale by rung 0's lack
of power-set closure. No repair inside `𝒫A` exists: the formation target `U₀`
contains only `0` and `1`, and `quot(A,R)` for inhabited `A` always contains a
nonempty *set of subsets*, which neither `0` nor `1` is (its member `1` is not
`∅` — the expert's observation, exactly).

### 3.2 Candidate B: canonical representatives via choice — mathematically uniform, **foundationally closed off**

Define `quotε(A,R) := {ε([x]∼) : x ∈ A} ⊆ A`, `mkε(x) := ε([x]∼)`,
`liftε(f) := f` restricted to `quotε`. This *is* level-uniform: `quotε ⊆ A`, so
`A ∈ U₀ → quotε ∈ U₀` (subsets of `1` are `0` or `1`) and `A ∈ Uₙ → quotε ∈ Uₙ`
(`Tower::sub`, no power set needed); `mk` is a section of the class map, so a
class is recoverable from its representative (`[ε([x])] = [x]`) and `lift` is
well defined; the ι-rule `f(ε([a])) = f(a)` holds by `compat`. It is the thesis's
own `ε` (thesis.txt:2042, fixed on `Uω`) used one level deeper.

It is unavailable here, and the kernel documents why with unusual precision:
`kernel::thm::define` (kernel/src/thm.rs:1358) demands `⊢ ∀x⃗ ∃!y. φ` — a choice
function is never unique, so `ε` cannot be minted; and the long comment above
`define` (thm.rs:1326–1338) proves the sharper point that a Skolemising
`define_choice` at arity ≥ 1 would be a **genuine unsoundness** in this kernel,
because `ax_replacement` accepts arbitrary formulas and a Skolem symbol is
conservative but not eliminable — a model expanded by an arbitrary choice
function need not satisfy Replacement for formulas mentioning it. `ax_choice`
exists only in existential form (`derived/src/choice/function.rs`), and an
existentially bound `f` cannot appear in the closed terms the interpretation must
produce. So the one mathematically uniform definition is ruled out by the
foundation, on purpose, for reasons that are correct. This is the obstruction the
question asked to be specific about.

### 3.3 Candidate C: one symbol with an internal case split — definable, **pointless**

A single Separation does exist:

```text
Q(A,R) := { c ∈ 𝒫A : (A ⊆ 1 ∧ c ∈ A) ∨ (¬(A ⊆ 1) ∧ ∃x.(x ∈ A ∧ c = class(A,R,x))) }
```

(well-bounded because `A ⊆ 1 → A ⊆ 𝒫A`: the only possible element `∅` is a subset
of everything). With LEM — the kernel is classical — one proves `A ⊆ 1 → Q = A`
and `¬(A ⊆ 1) → Q = quot(A,R)`, and every export can be stated once. But this is
a case split *moved into a formula*, not removed: every proof does the LEM
analysis, `mk` and `lift` need their own `∃!`-by-cases definitions, and — the
decisive point — **it cannot make the checker uniform**, because of §4.1 below:
the ambient proof-split already forces `⟦Quot.mk r a⟧ = •`-up-to-equality at
`u = 0` no matter what set `Q(A,R)` is. The symbol-level uniformity would be
cosmetic, purchased with strictly more theorems than the two-branch reading. A
side effect worth noting: `Q` would also change `Type`-level quotients of
subsingleton carriers (`A = 1 ∈ U₁`, PUnit-shaped) to the identity reading —
still sound, every obligation discharges — which shows the discriminant `A ⊆ 1`
genuinely cannot see the level, and hence also why no set-function of `A` alone
can *literally* agree with the classes clause at `ℓ > 0`: `1 ∈ U₀ ∩ U₁` by
cumulativity, and the two ends demand different values on the same set
(`1` versus `{1}`). The level is extra data, and any uniform-in-the-set clause
must give up literal agreement with classes on subsingleton `Type`s.

### 3.4 Why no fourth candidate exists

A uniform clause would need a ZF-definable (choice-free, case-free) `Q, mk` with:
`mk` collapsing exactly `∼` (forced: `lift` must be single-valued for every
compatible `f`, and at `R = ∅` every `f` is compatible — `witness::compat_at_empty`
— so `mk` must be injective there), and `Q ⊆ 1` whenever `A ⊆ 1` (forced by
formation). On subsingletons `mk` must be the identity-up-to-`•`; on `A = 2` with
`R = ∅`, `mk` must be injective into a two-element `Q`. A definable operation
that is a retraction-free quotient on one side and the identity on the other,
with no case discrimination and no choice, would in particular pick canonical
representatives definably at every `A` where classes are non-trivial — which is
Candidate B without `ε`. First-order definability always permits the disjunction
(Candidate C), so "uniform" in any sense stronger than C means choice, and
choice is closed (§3.2). That exhausts the space.

## 4. The split, and what decides it

### 4.1 The split already exists; `Quot` adds no new decision point

The interpretation is globally split at `ℓ = 0` before quotients enter: the
proof-split language (thesis §6.1, thesis.txt:1985–2005) translates every
application, lambda and binder differently at `sort = 0` vs `≥ 1`, and Theorem
6.7 part 2 (thesis.txt:2186) makes "every proof interprets to `•`" a soundness
invariant. Mini implements exactly this: proof-valued applications and lambdas
go to `•`, every proof is certified `= •` via `prop_subsingleton`
(`point_of_proof`, MINI-DESIGN.md §6.4 clause 1), and Π splits into
`dprod` vs `cond` on the `is_prop` witness (§6.2). `Quot.mk r a` at `u = 0` *is a
proof*; its interpretation is forced to `•` by this invariant regardless of any
choice made for `⟦Quot α r⟧`. So the quotient clause cannot be more uniform than
the application clause, and the case split recommended here is an instance of a
split the design has already paid for.

### 4.2 `provably_nonzero` is the wrong instrument

`provably_nonzero` (`mini/src/zoneb.rs:84`, `checker/src/tg.rs:6255`) answers a
different question: it fixes the translation branch **per declaration**, on the
declaration's own level *expression* (params included), because Lean's eliminator
trichotomy (thesis §2.6.2; LEVEL-POLYMORPHIC-INDUCTIVES.md §2) is per-declaration
— `PUnit.{u}` has one recursor and must take one branch at every `u`. Applied to
`Quot.{u}`, whose own resultant level is a bare `Param u`, it answers `false`,
which would force the `Prop` reading (or a decline) at every instantiation,
including `Type` ones — exactly wrong.

And the per-declaration rule's *rationale* does not reach `Quot`: `Quot` is not
an inductive, has no recursor and no trichotomy — `Quot.lift` is large-eliminating
at **every** `u`, including `u = 0` (that is the §3.1.1 behaviour). Unlike
`PUnit`, `Quot` at `Type` levels has real structure, so no single carrier can
serve all `u` (§3.3's last sentence); and LEVEL-POLYMORPHIC-INDUCTIVES.md §3.1
establishes that per-ground-instantiation interpretations are sound by
themselves — nothing ever compares `⟦c.{0}⟧` with `⟦c.{1}⟧`, levels being ground
per check. The interpretation of `Sort` itself is already per-numeral.

### 4.3 What actually decides, and the evidence

At interpretation time the store key is `(name, ground levels)` (zoneb `ensure`),
so `u` is a numeral. The branch is decided by `u = 0` vs `u = n+1` — a syntactic
fact about a ground numeral, like the `sort/sort` clause — and the house rule's
*evidence* obligation is met per branch by the certificate each branch consumes:

- `u = 0`: the threaded `Γ ⊢ ⟦α⟧ ∈ U₀` — the `is_prop` witness, which is "the
  inference's own certificate, un-discarded" (MINI-DESIGN.md §6.3). Every theorem
  in §2.2 takes it as a premise, so a branch entered wrongly cannot derive
  anything: the evidence is consumed, not re-discovered.
- `u = n+1`: the threaded `Γ ⊢ ⟦α⟧ ∈ U₍ₙ₊₁₎`, same provenance, consumed by the
  formation theorem (§6.1 below) and by `lift_in_funspace`'s premises.

No new predicate, no search. The precedent is the Π clause, which branches the
same way on the same witness. Neither branch subsumes the other, and both
mis-uses are *refutable*, which is the strongest possible justification for a
split: the classes clause at `u = 0` hits `⊢ ¬({1} ∈ U₀)` (§1.2), and the
identity clause at `u ≥ 1` hits `sound`'s obligation `• ∈ [ā = b̄]` for genuinely
distinct related elements — e.g. `A = 2`, `R = {⟨0,1⟩}`, where `[0 = 1]` is
refutable by `u0_two_valued`. One more reason the numeral, not a subsumption
argument, must decide.

`Quot.lift` and `Quot.ind` carry a **second** split on `v` (the motive/target
level): `v = 0` routes to the proof-split (`lift` is itself a proof — §2.2 T5,
§6.2 below), `v ≥ 1` to the set-level function. Same instrument: `v` is ground,
the evidence is `β`'s own sort certificate. This split exists at every `u`, and
the thesis's `n′ ≥ 1` hedge at thesis.txt:2359 is its shadow.

## 5. Statement of the recommended design

- **Two clauses, decided by the ground numeral `u`, evidenced by the threaded
  rung-membership certificate of `α`.**
- `u = 0`: identity interpretation, obligations T1–T8 of §2.2; new `derived/`
  surface ≈ one composed lemma (T6) — suggested home `derived/src/prop/`, since
  it is `Prop` apparatus, not quotient apparatus; `derived/src/quot/` is not
  touched at `u = 0`.
- `u ≥ 1`: the existing `derived/src/quot/` classes construction, unchanged,
  plus the missing formation theorem (§6.1).
- The claims doubling the question worried about does not materialise: the
  `u = 0` branch's "theorems" are almost entirely re-labelings of certificates
  the checker already holds, because `⟦Quot α r⟧ = ⟦α⟧` makes the relevant
  statements syntactically identical.

## 6. Sanity check of the `ℓ > 0` clause

Sound as far as it goes; four findings, in decreasing order of substance.

1. **The formation theorem is missing (known) and rung 1 supports it (checked).**
   `quot.rs`'s "What is not here" records `quot(A,R) ∈ U(c)` as underived. The
   route exists at every rung ≥ 1 including `Sort 0`'s neighbour: `quot_ax`'s
   `c ∈ 𝒫A` conjunct gives `quot(A,R) ⊆ 𝒫A`; `Tower::pow` (`rungs.rs:84`,
   stated for `U(x)`, i.e. all rungs ≥ 1) gives `𝒫A ∈ Uₙ`; `Tower::sub`
   (`rungs.rs:73`) closes: `⊢ ∀A ∀R ∀c. (A ∈ U(c) → quot(A,R) ∈ U(c))`. Note the
   code's single power set is *tighter* than the thesis's "double powerset of ᾱ"
   (thesis.txt:2355) — classes are subsets of `A`, so one `𝒫` suffices; no issue,
   just a coarse bound in the thesis.
2. **`lift` into `Prop` (`u ≥ 1, v = 0`) must bypass the funspace lift.** The
   thesis assumes `n′ ≥ 1` in its `lift` case (thesis.txt:2359); at `v = 0` the
   whole of `lift β f h` is a proof and `f` is one too, so there is no
   `f ∈ fs(A,B)` certificate to feed `lift_in_funspace` — a wiring that tried
   would gap, not err. The set-level fact needed is only:
   `quot(A,R)` inhabited → `B̄` inhabited, i.e. `quot_cases` (`classes.rs`)
   composed with `f`'s conditional-singleton certificate; no `compat` is needed
   (proof irrelevance covers the ι-rule). The `v`-branch is decided as in §4.3.
3. **The `R̄`-graph seam is genuinely unbuilt.** Lean's `r` interprets as a
   curried function `⟦r⟧ ∈ fs(A, fs(A, U₀))`; every theorem in `derived/src/quot/`
   takes `R` as a **set of pairs** (`⟨x,y⟩ ∈ R` in `eqv_incl`, `q_sound`,
   `rcompat`). The conversion
   `rel_graph(A,r) := {p ∈ A² : ∀u∀v. (p = ⟨u,v⟩ → • ∈ app(app(r,u),v))}`
   (one Separation, the `∀`-form for the same reasons as `ker`) and its two
   bridge lemmas — membership of `⟨x,y⟩` from `• ∈ app(app(r,x),y)` and back —
   exist nowhere yet, and `Quot.sound`'s and `Quot.lift`'s wiring both consume
   them (the `h`-certificate arrives in `app(app(r,·),·)` form and must become
   `rcompat`). This is plumbing, not model error, but it is the actual untested
   edge of the `ℓ > 0` clause: every quotient theorem is currently exercised only
   against a pair-set `R` that no Lean-side term yet produces.
4. **Threading for the ι-rule closes properly.** `lift_beta`'s antecedents
   (`compat ∧ x ∈ A`) are dischargeable from certificates the checker holds at
   the redex: `x ∈ A` from the constructor argument's typing, `compat` from
   `h`'s typing certificate via `compat_closure` (through finding 3's bridge).
   Lean's kernel fires the reduction without inspecting `h`; ours needs `h`'s
   typing, which is always available since the redex typechecked. "On the nose"
   in this kernel means an unconditional equation theorem per instance, which is
   what `lift_beta` yields after its antecedents are cut — consistent with how
   every other ι-rule is stored (MINI-DESIGN.md §6.4). Subsingleton carriers at
   `Type` level (`A = 1 ∈ U₁`) are unproblematic for the classes clause:
   `quot(1,R) = {1} ∈ U₁` by finding 1's theorem, and `lift`'s graph is the
   one-pair set; no edge there.

## 7. Honesty notes

- The thesis is silent at `ℓ = 0` for quotients (`n ≥ 1` at thesis.txt:2353) and
  at `v = 0` for `lift` (thesis.txt:2359); §2 and §6.2 above are extensions. Both
  are assembled from clauses the thesis does state (proof-split, Theorem 6.7
  part 2, the `α/R := α` remark at thesis.txt:830), but they are our proof
  obligations, not Carneiro's.
- Candidate B's exclusion (§3.2) rests on the kernel's documented policy that
  `define` requires `∃!` and that Skolem choice at arity ≥ 1 is unsound against
  the unrestricted Replacement scheme. I verified the comment's argument reads
  correctly (eliminability is what licenses extended-scheme instances) but did
  not re-derive the model theory independently.
- I did not compile or run anything; every claim above is from reading the cited
  lines. The countermodel computations (`quot(1,R) = {1}`, `quot(0,R) = 0`,
  `{1} ∉ U₀`) are two-line set calculations against the printed interfaces of
  `eqv.rs`/`classes.rs` and `u0_members`/`u0_two_valued`.
