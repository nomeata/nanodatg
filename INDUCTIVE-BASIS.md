# A basis for Lean's non-mutual inductives

*2026-08-10. Commissioned answer to: propose a small, fixed basis of built-in
type formers such that every non-mutual inductive declaration Lean admits can
be constructed from them — carrier, constructors, recursor at Lean's own
eliminating-universe rule, ι propositionally. Everything marked **compiled**
was compiled this session at the pinned toolchain `leanprover/lean4:v4.29.1`;
the evidence files are `scripts/inductive-basis/*.lean` and §10 gives the
commands. §9 names what is argued but not machine-checked. Line references
`thesis.txt:N` are to Carneiro's thesis as vendored in this repo.*

## Verdict

**Five primitive inductives, plus one level-arithmetic decision:**

    Eq   PSigma   Nat   Acc   PULiftP        (+ either ULift≤ or complete level defeq)

where `PULiftP (p : Prop) : Sort u` is the lift of a proposition to a bare
variable sort — itself a kernel-legal Lean inductive — and the sixth item is
not a type former but a choice: either a level-constrained lift `ULift≤`
(a rule schema, not a Lean constant), or a checker whose level definitional
equality is complete rather than Lean's normal-form comparison. Under the
second option the basis is exactly the five constants.

Four findings reshape the question as posed, all **compiled**:

1. **The "maybe-zero" landscape is governed by two different rules, and the
   brief's `max 1` premise conflates them.** Lean's *elaborator* refuses every
   inductive whose resultant sort can be `Prop` at some instantiations and not
   others (`SortPolyNeg.lean` N2) — that, plus the large-elimination rule, is
   why every core structure carries `max 1`. Lean's *kernel* has no such
   refusal: it checks one per-argument level inequality (`is_geq`) and admits
   `PEmpty`- and `PUnit`-shapes, an Eq at `Sort v`, a Prop-lift, two-constructor
   enums, and even the PSigma shape at `Sort (max u v)` — the last with small
   elimination (`SortPolyProbe.lean` P1–P11). Core itself crosses the
   elaborator line twice, for `PUnit` and `PEmpty`, with
   `set_option bootstrap.inductiveCheckResultingUniverse false`
   (Init/Prelude.lean:123,211). A checker answers to the kernel, so the basis
   covers the kernel's territory.

2. **One new primitive closes the whole maybe-zero territory.** The owner's
   `PEmpty` impossibility argument is confirmed and sharpened: over any basis
   of `max 1`-leveled formers, the only type reachable at a bare variable sort
   is an inhabited singleton, so *some* primitive must live at bare `Sort u`
   and be able to be empty. The right such primitive is not `PEmpty` but the
   Prop-lift `PULiftP (p : Prop) : Sort u` — kernel-admissible, subsingleton,
   large-eliminating. From it plus `{Π, Eq, Nat}` every kernel-admissible
   maybe-zero declaration is constructed — empty, unit, Eq-at-`Sort v`,
   payload, enum, recursive — each at the kernel's own eliminating universe
   (`BareU.lean`, **compiled**, several ι by `rfl`).

3. **The thesis's own reduction has a bug at exactly the point it left open.**
   Thesis §5.3 reduces subsingleton eliminators to `accφ`, and thesis.txt:1838
   claims `accφ_r x := ∃ h : φ x, acc_{r'} (x, h)` with `r'` restricted to the
   φ-subtype. On the thesis's own running example (thesis.txt:1848) that
   carrier is junk-inhabited where the μ-type is empty, and its recursor —
   the part §5.4 "leaves as future work" (thesis.txt:1898) — is underivable:
   any term of its type proves `False` (`AccPhi.lean`, `literal_has_no_rec`,
   **compiled**). The repair is `AccPhi r φ x := Acc r x ∧ ∀ y, Reach r y x → φ y`
   — accessibility over the *full* index space with φ hereditary along the
   Church closure — whose φ-restricted intro and large dependent recursor are
   derivable from `Acc.rec` plus Prop-logic, with ι by `rfl` (**compiled**,
   generic, plus a non-degenerate instance).

4. **Much more of the construction is definitional than the contract asks.**
   The propositional-ι allowance is needed, but sparingly: a `List` model
   over `{Nat, PSigma}` with *both ι rules by `rfl`* (tuple towers, no
   funext), tag-sums with ι by `rfl`, the indexed skeleton-and-carve with ι
   by `rfl` (`TypeRoutes.lean`, `IndexedCarve.lean`, **compiled**). The
   engines are definitional proof irrelevance, structure eta, and K-like
   reduction on `Eq.rec`. No compiled construction in this document consumes
   funext, propext, `Quot`, or choice — pinned with `#print axioms` in each
   file (the one `[propext, Quot.sound]` line is the `AccPhi` *refutation
   proof*, through its `omega` calls, not a construction); funext enters
   exactly once, in the infinite-branching W arm (§3.5).

---

## 1. Scope, and the rule that defines it

A single (non-mutual, non-nested) declaration

    inductive T (params…) : ∀ (ι :: A), Sort ℓ
      | c_j : ∀ (b :: β_j), T p_j[b]

with non-recursive arguments not mentioning `T`, recursive arguments of shape
`∀ (z :: γ), T e` (thesis.txt:647–668 — Lean's strict positivity for a single
inductive admits exactly these, since any dependence of a later argument on a
recursive one would put `T` into its type), any number of constructors
including zero, indices, and a universe-polymorphic resultant level ℓ.

The kernel's admission rule, from `src/kernel/inductive.cpp` at v4.29.1 and
pinned behaviorally in `SortPolyProbe.lean`/`SortPolyNeg.lean`:

* **Formation**: for each constructor argument at level ℓ',
  `is_geq(ℓ, ℓ') || is_zero(ℓ)` — a sound syntactic approximation of
  "ℓ' ≤ ℓ at every instantiation", with literal `Prop` fully impredicative.
  Nothing else. There is no maybe-zero refusal in the kernel.
* **Eliminating universe** (`elim_only_at_universe_zero`): the recursor's
  motive lands in `Sort w` for fresh `w` iff ℓ `is_not_zero`, or the block is
  a single inductive whose constructor count is 0, or is 1 with every
  argument a syntactic Prop or an index variable of the output (the SS rule,
  thesis.txt:700–710). Otherwise the motive lands in `Prop`.
* **K-like reduction** (thesis.txt:786): granted when the block is a single
  inductive at literal `Prop` with one constructor all of whose arguments
  appear among the output indices.

Three consequences pinned by the probes:

* A recursive argument at a maybe-zero sort **kills** the SS grant: its type
  sits at the maybe-zero level and is not a syntactic Prop (`R0` in
  `SortPolyProbe.lean` has a small recursor). So Acc-like large elimination
  exists only at literal `Prop` — maybe-zero SS declarations are never
  recursive, which §3.6 exploits.
* Two constructors at a maybe-zero sort are admitted — small. (They must be:
  a large recursor there would discriminate two proofs of one Prop at the
  zero instantiation and prove `False`.)
* The PSigma shape at `Sort (max u v)` is admitted — small. Core's
  `max 1 u v` buys large elimination (never-zero resultant) and elaborator
  acceptance; it is not a formation boundary.

The classification below is total: every admissible ℓ is literally `0`,
never-zero, or maybe-zero, and the constructor-shape subcases within each are
exhaustive by the elimination rule.

**Ambient theory.** Lean's Π with `imax`, impredicative `Prop`, definitional
proof irrelevance, definitional structure eta, δβη, and the basis members'
own definitional ι and K-like rules. No axioms — the one construction that
needs `funext` (hence `Quot.sound`) is flagged where it occurs (§3.5). Choice
is never used.

## 2. The basis

Each member is a primitive with Lean's own formation/intro/elim/ι, at every
universe level; all five are single universe-polymorphic constants, and all
five are kernel-legal Lean inductives (the fifth behind the bootstrap
option), so "primitive" means exactly what it means for Lean's own `Nat`.

| # | member | signature | elim | why it is in |
|---|--------|-----------|------|--------------|
| 1 | `Eq` | `(α : Sort u) → (a : α) → α → Prop`, `refl : Eq a a` | `Sort w` (SS), K-like | index transport; the Henry-Ford equations of every indexed arm; the self-equalities K-like reduction erases to make ι `rfl` |
| 2 | `PSigma` | `(α : Sort u) → (α → Sort v) → Sort (max 1 u v)`, `mk`, definitional eta | `Sort w` | dependent pairing: field telescopes, subtypes (`Subtype` *is* this shape — `CoreFacts.lean`), index packing |
| 3 | `Nat` | `Type`, `zero`/`succ` | `Sort w` | infinity at `Type 0`; constructor tags with large case-split; lengths/tuple towers; every real Lean checker special-cases `Nat` anyway (GMP literals) |
| 4 | `Acc` | `(α : Sort u) → (r : α → α → Prop) → α → Prop`, `intro` | `Sort w` (SS) | the one SS-recursive large eliminator; well-founded recursion, which also powers the derived W (§3.5) |
| 5 | `PULiftP` | `(p : Prop) → Sort u`, `up : p → PULiftP p` | `Sort w` (SS) | the bare-variable-sort seed: everything maybe-zero (§3.6) |

Derived, not primitive: `False` (Church `∀ p : Prop, p`; its `Sort w`
eliminator comes from `0 = 1` plus a `Nat.rec`-built family to transport
along — `BareU.lean` `PE.elim`), `True`/`PUnit` (`PULiftP` of Church-True),
`PEmpty := PULiftP CFalse`, `And`/`Or`/`Exists`/closures (Church, §3.1–3.2),
`PProd`/`PSum`/`Option`/`Sum` (tag-sums, §3.3), `Subtype` (a `PSigma`
instance), `PLift`/`ULift` (a `PSigma` pad), `List`/`Fin`/vectors (§3.4),
`W` (§3.5), `HEq` (§3.2).

**The sixth item.** Placing a carrier at *exactly* the declared level is a
level-arithmetic problem, not a type-theoretic one. Lean's level defeq is
normal-form comparison, and a `max` does not absorb an `imax` it dominates
semantically (`SortPolyNeg.lean` N3, **compiled**): `max 1 u v` and
`max 1 (imax u v) u v` agree at every instantiation and do not unify. So a
kernel-admissible field whose level keeps a stray `imax` (the `BoxF` shape,
`modelgen/tests/prim_declines.lean:62`) can be *stored* but the chain cannot
be *placed* at the declared level by padding. Two resolutions:

* **`ULift≤`**: a primitive `ULift≤.{v,u} (α : Sort u) : Sort v` whose
  formation carries the side condition `u ≤ v` (kernel `is_geq`), with
  `up`/`down` and eta. This is Carneiro's own shape — his `ulift` is
  constraint-form, `max(1,ℓ) ≤ ℓ'` (thesis.txt:1643) — with the `max 1`
  dropped so the (0,u) instance is `PULiftP`. **It cannot be a Lean
  constant**: instantiated at unconstrained levels it maps `Bool` into
  `Prop` and is inconsistent with proof irrelevance. It exists only as a
  level-indexed family / rule schema — the brief anticipated exactly this
  admission, and it is the honest form of the answer if the checker keeps
  Lean's level arithmetic.
* **Complete level defeq**: semantic equality of level expressions is
  decidable, conservative over Lean's (every Lean-defeq pair is semantically
  equal), and under it `max`-absorption holds, so PSigma chains with
  `False`-Π pads (`(h : False) → False.rec (fun _ => Sort ℓ) h : Sort ℓ`,
  by `imax 0 ℓ = ℓ`, at *any* ℓ) land on every admissible level and `ULift≤`
  becomes derivable where needed. This is a checker-design choice —
  "permissive but consistent" — not a type former.

## 3. Sufficiency: the construction schema, by class

Notation: `m` is the declared resultant level. Every construction is uniform
in the declaration's level variables — the case split below is on the
*syntactic* class of `m` (literal 0 / never-zero / maybe-zero), which is
fixed per declaration, never on instantiations.

### 3.1 `Prop`, not subsingleton — small elimination. Routine, axiom-free.

Carrier: the impredicative Church encoding, indexed by quantifying the motive
over the indices:

    T' ι := ∀ C : (∀ ι, Prop), (minor premises for C) → C ι

Constructors are the folds. The *dependent* Prop-motive recursor: fold at the
predicate `Q ι := ∀ h : T' ι, C ι h` — well-formed because any two proofs are
definitionally equal (proof irrelevance), so `C ι h` does not depend on which
`h`. For recursive declarations the fold must rebuild the element beside the
proof: fold at the Church-pair of ("element", "proof") and re-pair in each
step, every "which proof" question closed by PI. ι is definitional or trivial
(both sides inhabit a Prop). **Compiled** at the recursive case as
`R1'` in `BareU.lean` (the same term works at `u := 0`); the non-recursive
case is `modelgen` §8.1's Prop route, compiled at corpus scale (115 models).
This class costs *nothing* — Π and impredicativity alone.

### 3.2 `Prop`, subsingleton — large elimination. The delicate class.

Shape (thesis.txt:700–710): one constructor; every argument a Prop, an index
variable of the output, or recursive. The schema, repaired from thesis §5.3:

1. Pack the index telescope with `PSigma`: `X := Σ'(ι :: A)` (never-zero
   auxiliary; its level does not appear in the result).
2. From the constructor telescope build, by the thesis's own recursion over
   the ctor judgment (thesis.txt:1874–1879), the Prop `φ : X → Prop`
   (existentially quantified prop-arguments and Henry-Ford index equations
   `x = e`, via Church-∃/∧ and `Eq`) and the edge relation `r : X → X → Prop`
   (one disjunct per recursive argument).
3. Carrier — **the repair**:

       AccPhi r φ x := Acc r x ∧ ∀ y, Reach r y x → φ y

   with `Reach` the Church reflexive-transitive closure. This is the least
   fixed point of `T x ⇐ φ x ∧ ∀ y, r y x → T y`, i.e. the μ-type
   accφ of thesis.txt:1832. The thesis's own `∃ h : φ x, acc_{r'} (x, h)`
   over the φ-subtype (thesis.txt:1838) is **wrong**: restricting `r` to the
   subtype deletes exactly the non-φ predecessors, making μ-empty positions
   vacuously accessible; on the thesis's own example the recursor type then
   proves `False` (`AccPhi.lean` `junk`, `literal_has_no_rec`, **compiled**).
4. Intro: `Acc.intro` on the accessibility component; hereditariness by path
   decomposition of the closure (`AccPhi.intro`, **compiled**).
5. Recursor into `Sort w`: `Acc.rec` (the basis's one SS-recursive large
   eliminator) at the motive "hereditary-φ implies the goal at every
   carrier proof"; the two ∧-components and every ∃-witness are extracted by
   *small* elimination — the extraction's target type is fixed up by PI, so
   no large elimination of ∧/∃ is consumed; index equations are eliminated
   with `Eq.rec`; the recursor's proof argument transports for free because
   the carrier is a Prop. ι: `rfl` for the generic core (`AccPhi.iota`,
   **compiled**); on a concrete declaration the index transports sit on
   `Eq.refl` and K-like reduction erases them.
6. The K-like *propositional* rule for such an eliminator —
   `rec C x a h = x` for `h` with definitionally equal endpoints — is free:
   `h` inhabits a Prop, so any two proofs are definitionally equal and the ι
   theorem applies. Where Lean uses K-like reduction *definitionally*, see
   §6.

Instances compiled: the generic strong-recursion shape `Down` (index +
recursive argument; `Down'.iota` by `rfl`), and the thesis's own
`P : Nat → Nat → Prop` example refuted-then-repaired. `Eq`- and `HEq`-shaped
declarations (index arguments only, no recursion) are the degenerate case
`r := ⊥`: the carrier collapses to `φ` alone and the recursor is `Eq.rec`
transport plus PI; the maybe-zero variant is compiled as `EqS` in
`BareU.lean`.

### 3.3 Never-zero, non-recursive. Routine; compiled at corpus scale.

`Nat`-tagged sums of `PSigma` chains (`modelgen` §8.1, 115/115 of
`init-prelude`'s plain shapes; `PSum'` in `TypeRoutes.lean` re-verifies the
polymorphic two-constructor case at `Sort (max 1 u v)` with ι by `rfl`).
The tag fiber is a `Nat.rec` cases tower — **this is what `Nat`'s large
elimination buys** — with the empty type beyond the constructor count
(Church-False seeded, `CFalse'.elim` giving its `Sort w` eliminator via
`0 = 1` transport). Fields at levels below the carrier ride as chain
components (`max` absorbs them when `m` is never-zero); Prop fields are
`PSigma`-legal directly. Pads are definitionally canonical at
successor/max-built levels (`D1`/`DS`, structure eta + PI + function eta,
**compiled**), giving ι by `rfl`; at other levels the `False`-Π pad
transports and ι stays propositional. The exact-level residue is §2's sixth
item.

### 3.4 Never-zero, recursive, finitely branching. Routine — and definitional.

Two routes. The general one is §3.5. The direct one, **compiled**
(`List'` in `TypeRoutes.lean`): code the recursion structurally — for
`List α`, the carrier `Σ'(n : Nat), V n` with `V` the `Nat.rec` tower of
right-nested pair chains. Constructors are pair-pushes; the dependent
`Sort w` recursor is `Nat.rec` on the length; **both ι rules hold by `rfl`**
— structure eta collapses every tuple onto a constructor image, so the model
is fully definitional, with no funext (unlike the `Σ n, Fin n → α`
representation). The same pattern covers any finite-branching single
inductive (the skeleton is a `List` of node payloads; §3.7 composes the
indexed carve on top — `IndexedCarve.lean` does exactly this for the
thesis's `X` example).

### 3.5 Never-zero, recursive, infinite branching (and the general arm). Delicate.

A recursive field under a binder, `f : (z :: γ) → T e`, forces genuinely
well-founded infinite-branching trees — a W-type, however spelled
(`MODELGEN.md` §8.4's "plan A is W in disguise"). The basis derives W:

* raw trees: partial functions `List (Σ' a : A, B a) → Option A` — paths
  are `List` (§3.4), `Option` a tag-sum (§3.3), all level-exact at
  never-zero `m`;
* well-formedness: prefix-coherence, and well-foundedness *as accessibility
  of the immediate-subtree relation* — `Acc`, not "no infinite path", so no
  dependent choice is consumed;
* `sup` grafts; the recursor is `Acc.rec` over the subtree relation;
* ι propositionally — tree equality is function equality, and **this is the
  one place funext (hence `Quot.sound`) enters the whole construction**.

Evidence: Kha's `LFP.lean` gist compiles W with propositional ι from
`{Eq, False, Option, Sigma, Subtype, List, Acc}` (`W-FROM-LFP.md` §2), and
every member of that closure is compiled to this basis above (`Option`,
`Sum` §3.3; `Subtype` = `PSigma`; `List` §3.4; `False` derived). The
composed, fully general form — arbitrary telescopes, dependent `B`,
levels mixed — is assembled from these compiled pieces but has **not** been
machine-checked end-to-end (§9). Whether a Hugunin-style refinement can
remove the funext (as the tuple-tower `List` removed it at finite branching)
is plausible and unmeasured.

### 3.6 Maybe-zero. Compiled completely; one new idea.

By §1, a maybe-zero declaration either large-eliminates (0 constructors, or
1 constructor with only Prop/index arguments — recursion is impossible here,
probe F3) or small-eliminates (everything else). Either way *the contract
never forces two provably distinct elements*: the large class is
subsingleton-shaped, and the small class cannot discriminate (its motive
lands in `Prop`). So every maybe-zero carrier is `PULiftP` of a Prop:

* 0 constructors: `PULiftP CFalse`; the `Sort w` eliminator via `0 = 1`
  (`PE`, **compiled**).
* SS class: `PULiftP` of the §3.2 Prop (here recursion-free, so just
  ∃/∧/Eq-logic); recursor by projections, `Eq.rec` index transport, and the
  lift's propositional eta `t = up (down t)` — whose minor premise closes by
  PI; ι by `rfl` via K-like erasure (`PU`, `EqS`, **compiled**).
* small class: `PULiftP` of the §3.1 Church encoding; the collapsed carrier
  satisfies constructors, small recursor, and both ι rules — the b-rule's
  two sides are proofs of one Prop (`T3'`, `I0'`, and the recursive `R1'`,
  **compiled**; `R1'.iota` is `rfl`).

The zero instantiation of each model is the Prop-route model; no case split
on levels occurs — one term serves all instantiations, which is what
universe polymorphism demands.

### 3.7 Indexed families at never-zero levels. Compiled on the thesis's example.

Thesis §5.2: erase indices to a skeleton `S` (§3.3–3.5 shapes), define
`good : S → ∀ ι, Prop` by skeleton recursion (large elimination into the
Prop-valued function space, `imax` collapsing to 0), carve
`T ι := Σ'(s : S), good s ι` — level-exact since the Prop component is
absorbed (`Sort (max 1 m 0) = Sort m`). Constructors pack `Eq.refl` for
their index equations. The recursor — §5.4's unwritten part — is skeleton
recursion with `Eq.rec` transport along the stored equations, `good`-proof
positions closed by PI; on constructors the stored equations are `refl`, so
K-like reduction makes **both ι rules `rfl`** (`IndexedCarve.lean` on the
thesis's own `X = μt : N → U1. (one : t 1) + (double : ∀ n, t n → t (2n))`,
**compiled**). Generality beyond the compiled instance (deep index
dependencies, recursive arguments whose index expressions depend on the
binder telescope) follows the same recipe with heterogeneous packing — the
packed-index `Eq` at the `Σ'`-type replaces per-index equalities; assembled,
not machine-checked (§9).

## 4. Minimality, member by member

"Necessary" below means: a model argument or compiled refutation shows the
remaining members cannot reach something Lean admits. The weaker grade is
stated as such.

* **`Nat` — necessary** (infinity). Interpret `Type 0` as V_ω in the
  thesis's ZFC model: `Prop = {0,1}`, Π/PSigma of hereditarily finite is
  hereditarily finite, `Eq`/`Acc`/`PULiftP`-at-successor-levels are
  (sub)finite, and all recursors survive classically. Every closed type of
  the remaining basis at `Type 0` denotes a finite set; Lean admits
  `Nat`, whose contract makes `0, s 0, s (s 0), …` provably pairwise
  distinct via large elimination. Extends `CHURCH-BASIS.md` §5 by the
  `Acc`/`PULiftP` clauses; clause check asserted, not formalized (§9).
  — `Nat` is interchangeable with `W` (+ its tag glue): W-from-Nat is §3.5;
  Nat-from-W tags leaves with Props and carves by a recursive canonicity
  predicate. One of the two must be present; `Nat` is the right one for a
  Lean checker (literals).
* **`PULiftP` — necessary as the bare-sort seed.** Interpret every
  `Sort u`-classified object at instantiations `u ≥ 1` as a *nonempty* set
  (extending `CHURCH-BASIS.md` §4.4): Π, `PSigma`, `Nat` and the
  Sort-valued recursors of `Nat`/`Eq`/`Acc` preserve pointwise
  nonemptiness; `Sort 0` is unconstrained. So no closed
  `C.{u} : Sort u` over `{Π, Eq, PSigma, Nat, Acc}` has an empty instance
  at `u := 1` — and the kernel admits `PEmpty : Sort u`, which demands one.
  (Syntactic sharpening, per the owner's argument: every basis former lands
  at level `0`, `1`, or `max 1 ·`; a Π lands on a bare parameter only
  through `imax`-collapse, whose only seedless `Sort u`-valued family is
  `False.rec`'s over the empty domain — an inhabited singleton.) Model
  clause-check asserted, not formalized (§9). That the seed should be the
  full Prop-lift rather than `PEmpty` alone is the weaker grade: the
  kernel admits `L0 (p : Prop) : Sort u` itself, and over
  `{PEmpty, Π, Eq, Nat, Acc, PSigma}` no construction of it is known — a
  carrier "inhabited iff p" at bare `u` runs into double negation
  constructively — but no model refutation is given. Since `PULiftP`
  subsumes `PEmpty` (`PULiftP CFalse`) and self-models, taking the lift is
  strictly the better member.
* **`Acc` — necessary absent choice; unknown with choice.** Small-eliminating
  Acc is free (impredicative Church; owner's premise re-confirmed by §3.1),
  so `Acc` earns its place solely through SS-recursive large elimination.
  `CHURCH-BASIS.md` §6 compiled the direct failure (`AccLarge.lean`) and
  showed the classical graph route consumes `choose` — witness extraction
  this project does not carry, and *whose availability is itself
  Subtype-mediated*. No derivation from
  `{Π, Eq, PSigma, Nat, PULiftP}` is known; no impossibility proof either
  (§9). The thesis keeps `acc` primitive for the same reason: truncation
  destroys large elimination (thesis.txt:1826–1828).
* **`Eq` — necessary in practice; the missing term is named.** What cannot
  be built from the others is large transport,
  `∀ α (a b : α), CEq a b → ∀ C : α → Sort w, C a → C b` with `CEq` the
  Leibniz Prop. Without it: no index bookkeeping in §3.2/§3.6/§3.7, no
  Henry-Ford equations, and no K-like erasure. Additionally, the contract
  itself states ι rules as `Eq` theorems — a propositional-ι basis without
  an equality former cannot state its own deliverable. No model-theoretic
  impossibility proof is given (§9); every intensional basis in the
  literature keeps identity primitive, including the thesis's eight.
* **`PSigma` — the weakest minimality claim.** Dependent strong pairing with
  both projections at `Sort (max 1 u v)`. The Church encoding is refuted
  (junk inhabitants kill the dependent eliminator — compiled,
  `CHURCH-BASIS.md` §2, and the argument is level-agnostic), the `Quot`
  route fails at possibly-empty instances (`CHURCH-BASIS.md` §4.3), and no
  other route is known; no model refutation. Every literature basis keeps Σ
  primitive. Classified: *do not know how to do without*, not *known
  necessary*.
* **The sixth item — necessary relative to Lean's level defeq.** The `BoxF`
  shape is kernel-admissible and its field's level keeps an `imax` inside a
  `max` that Lean's normal-form defeq will not absorb (`SortPolyNeg.lean`
  N3); no carrier at the declared level over the five is known, and the
  measured precedent is `modelgen`'s decline. Not proved impossible — the
  space of re-encodings is not exhausted (§9). Under complete level defeq
  the problem dissolves, which is why it is presented as a decision, not a
  member.

Dropping any of `Eq`, `PSigma`, `Acc`, `Nat`, `PULiftP` therefore loses,
respectively: index transport (and the contract's own language); dependent
pairing; SS-recursive large elimination; infinity and tags; the entire
maybe-zero territory. The first two impossibilities are argued from known
compiled refutations, the third from compiled evidence modulo choice, the
last two from model arguments (asserted, §9).

## 5. The level story, in one place

* Core's `max 1` on every structure is real but has two separable causes:
  the elaborator's blanket maybe-zero lint, and the wish for large
  elimination (never-zero resultant). The kernel admits maybe-zero freely
  under `is_geq`, with elimination degraded as §1 says. `PSigma` at
  `Sort (max u v)` exists as a kernel declaration — small-eliminating.
* Bare `Sort u` is reached by exactly three routes in this basis:
  `PULiftP p : Sort u` (the seed, possibly empty); Π-types whose codomain
  is already there (`imax u u = u`, `imax 0 u = u` — probe L1/L2); and
  level *instantiation* of polymorphic constants at `u`. Nothing else; over
  the basis-minus-`PULiftP` the only bare-`u` inhabitants are singletons
  (§4).
* `Prop` is reached by ℓ := 0 instantiation and by impredicative Π; the
  Prop-valued classes never need a lift at all (§3.1–3.2 carriers are
  literal Props).
* Exact-level placement at never-zero levels: `max 1` absorbs into any
  never-zero normal form (probe L3), `imax` collapses under a never-zero
  right side (L4), pads exist at every level (`False`-Π at arbitrary ℓ,
  definitionally-canonical `D` at successor/max-built ℓ) — and the one
  genuine residue is the dominated-`imax` (L5/N3), which is the sixth
  item's job. A primitive with signature *exactly* `Sort u` is required —
  `PULiftP` is that primitive — and a primitive with a level *side
  condition* is required unless the checker completes its level arithmetic;
  both statements are the direct answers to the brief's question 4.

## 6. Propositional ι: where it is spent, and what stays definitional

Definitional facts consumed (all Lean facts, usable because basis members
are primitives with Lean's own rules): proof irrelevance — ubiquitously (it
is what makes Prop-motive dependence, SS projections, collapsed small
carriers, and every "which proof" transport free); structure eta — tuple
towers, pads, index packing; K-like reduction on `Eq.rec` — every ι that
came out `rfl` above; the primitives' own ι (e.g. `Nat.rec`'s, inside the
tag towers and `List'`).

Propositional-only spots: the `PULiftP` eta `t = up (down t)` (hence the
maybe-zero recursors' transports — though their ι on constructors still
erases to `rfl`); the `False`-Π pad's uniqueness at non-canonical levels
(funext there — avoided in every compiled file of this document by using
`PULiftP` pads and accepting propositional ι, or `D` pads and `rfl`); tree
equality in the W arm (funext, the construction's only axiom); index
transports on *non-constructor* elements.

**Does propositional ι compose downstream?** Two readings, with opposite
answers, and the distinction is the honest content:

* *Model reading* (this project's): the checker keeps Lean's kernel
  reduction for the declared `T.rec`; the construction is a parallel family
  of definitions whose statements match after renaming and whose ι are
  theorems. Composition is then a fact about the *translation*, not the
  kernel: each next declaration's model is built using the previous models'
  ι theorems, inserting `Eq.rec` casts where Lean used reduction.
  `MODELGEN.md` §1.1's contract and its corpus runs (263 statements
  compared, 0 differ; full replay kernel-checked) are the working proof
  that this composes at scale for the implemented arms.
* *Replacement reading* (compile `T.rec` away, kernel keeps only the
  basis): propositional ι is **not** enough — any downstream term whose
  type correctness relies on `Nat.rec x f (s n) ≡ f n …` fails to check,
  and repairing it is a whole-program cast-inserting translation (setoid/
  observational style), not a local one. Nobody should read this basis as
  license to delete ι reduction from a kernel.

The basis members' *own* ι must be definitional in either reading — that is
part of being primitive — and the many `rfl` ι's above mean the derived
layer degrades less than the contract permits.

## 7. The commissioned refutations

* **"The nested/mutual reduction is free."** Checked, with one measured
  caveat and one real cost. Mutual→indexed-single (fibering over a tag):
  the kernel imposes the same resultant level on every block member, both
  sides of the reduction land in the same elimination class on every probed
  axis — a maybe-zero mutual pair and its fibered form are both admitted
  and both small (P9/P10), and a `Prop` mutual block loses SS on both sides
  (block size > 1 kernel-side; ≥ 2 constructors fibered) — so no
  eliminating universe moves. The tag and index packing are basis material
  (`Nat`/`Fin`-style tags, `PSigma`). Nested→mutual: standard specialization
  (this repo's layer 1; Abbott–Altenkirch–Ghani, *Representing Nested
  Inductive Types Using W-Types*, 2004, is the classical form), but **not
  definitionally free**: the container is duplicated at the nested
  occurrence and consumers must transport across an isomorphism — the
  thesis says exactly this of Coq (thesis.txt:902–903), and under the
  propositional-ι contract that cost is absorbed, while under the
  replacement reading of §6 it is not. So: free here, by contract — not
  free absolutely.
* **"The `max 1` claim generalises."** Refuted as a kernel claim, confirmed
  as an elaborator-plus-large-elimination claim; see §1, §5. The
  consequence drawn from it (no structure basis reaches bare `u`) stands
  and is the reason for `PULiftP`.
* **"Propositional ι is enough downstream."** Split verdict, §6.

## 8. Relation to the literature, checked

* **Dybjer 1997** (*Representing inductively defined sets by wellorderings
  in Martin-Löf's type theory*, TCS 176): strictly positive endofunctors
  have initial algebras built from W — in *extensional* MLTT, non-indexed.
  Our §3.5 is its descendant; Lean replaces extensionality with
  propositional ι plus funext-from-Quot.
* **Abbott–Altenkirch–Ghani 2005** (*Containers: constructing strictly
  positive types*, TCS 342): strictly positive types are containers
  `Σ s : S, P s → X`; W gives their initial algebras; closure under μ needs
  Σ, Π, W and equality — the same quartet this basis keeps primitive
  (with Nat standing in for W). Their setting assumes extensional equality
  where we spend funext once.
* **Gambino–Hyland 2004 / indexed containers (Altenkirch et al., JFP
  2015)**: indexed W-types reduce to W-types; our §3.7 skeleton-and-carve
  is the proof-irrelevant, Henry-Ford-equation version of that reduction —
  simpler than the general one precisely because Lean's `Prop` is
  definitionally irrelevant, so `good`-proofs never obstruct.
* **Hugunin 2020** (*Why Not W?*, TYPES 2020): in intensional type theory
  without funext the naive W-constructions fail their induction principles,
  and a canonicity-predicate refinement repairs them. Two contacts: our
  tuple-tower `List` (§3.4) achieves the funext-free, definitional result
  directly at finite branching; and his refinement is the named candidate
  for de-axiomatizing §3.5 (unmeasured).
* **Carneiro's thesis §5**: the eight-type basis ⊥, Σ, +, ulift, ‖·‖, W,
  =, acc (thesis.txt:1900). This document's basis is smaller because Lean's
  own definitional facts do work the thesis's idealized setting assigns to
  primitives: + and ‖·‖ and ⊥ are derivable here (tags via Nat's large
  elimination; truncation is the §3.1 Church class, which impredicativity
  plus PI makes free; ⊥ via `0 = 1`); W is derivable from Acc (§3.5); ulift
  survives only as the §2 sixth item, in exactly the thesis's
  constraint-form. Two corrections to the thesis surfaced: the
  maybe-zero-polymorphic territory (its translation splits on `1 ≤ ℓ` vs
  `Prop`, a split that is not stable under level instantiation and has no
  arm for `PUnit`-like declarations — `PULiftP` is the missing device), and
  the thesis.txt:1838 accφ reduction, refuted and repaired in §3.2. Both
  sit precisely in §5.4's "left as future work" (thesis.txt:1895–1901),
  which this document partially discharges: recursors and ι are compiled
  for one representative of every class, though not for the general schema.
* **Where Lean diverges from all of the classical answers**: impredicative
  proof-irrelevant `Prop` makes every small-eliminating Prop inductive free
  (no W, no Σ — nothing); the SS rule forces two primitives (`Eq`, `Acc`)
  the W-literature never needs because its eliminators are not
  universe-stratified; `imax` and maybe-zero polymorphism have no
  counterpart in the literature at all, and are exactly where the two
  non-classical members (`PULiftP`, the sixth item) live; and K-like
  reduction hands back definitional ι in the derived layer, which the
  intensional literature has to fight for.

## 9. What is not reached, and what is unmeasured

Not reached, sharply:

* **Definitional ι for the derived layer as a whole.** By contract; the
  replacement reading of §6 is out of reach on principle (a kernel keeping
  only the five primitives' reductions cannot check today's exports).
* **Exact-level carriers for dominated-`imax` field levels over the five
  constants under Lean's level defeq** (`BoxF`). Reached only via the sixth
  item, in either guise.

Unmeasured / argued-only, exhaustively:

* The two model arguments of §4 (V_ω and nonempty-universe) extended over
  `Acc`, `PULiftP` and the Sort-valued recursors: clause-by-clause check
  asserted, not formalized — same status `CHURCH-BASIS.md` §7 already
  records for their ancestors.
* The general §3.5 W arm and the general §3.7 indexed arm end-to-end:
  compiled for representatives (and, for W, for the gist's closure), not
  for the arbitrary-telescope schema. This is the same gap the thesis's
  §5.4 leaves, narrowed but not closed.
* `Acc` with choice (`CHURCH-BASIS.md` §7's open cell) — if that cell
  opened, the basis could shrink by one for a checker willing to carry
  choice; nothing here depends on it either way.
* Impossibility proofs for `PSigma`, for `Eq`-transport, for
  `PULiftP`-over-`PEmpty`, and for the sixth item: none exist; each is
  classified at its honest grade in §4.
* Funext-freedom of the W arm (Hugunin-style): plausible, unattempted.

## 10. Reproducing

    T=~/.elan/toolchains/leanprover--lean4---v4.29.1
    cd scripts/inductive-basis
    for f in SortPolyProbe SortPolyNeg CoreFacts BareU TypeRoutes AccPhi IndexedCarve; do
      env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean $f.lean; done   # 0 errors each

Compile results this session: all seven files, 0 errors (negative probes
pinned inside `#guard_msgs`). Prior compiled evidence cited:
`scripts/church-basis/*` (`CHURCH-BASIS.md` §8), `scripts/prim-basis/`
and the `--prim-models` corpus run (`MODELGEN.md` §8), Kha's `LFP.lean`
gist, md5 `ebea23ac3ac492daf8c1b1467d28b393` (`W-FROM-LFP.md` §9).
