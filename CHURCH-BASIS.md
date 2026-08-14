# Can the gist's basis be modelled out of Π, `Eq`, `False`? — the Church-encoding question

*2026-08-09. Follow-up to `W-FROM-LFP.md` (`8e53b5d`), on the owner's question:
that assessment found the irreducible inductive closure of Kha's `W`-from-LFP
gist to be `{Eq, False, Option, Sigma, Subtype, List, Acc}`, and the owner asks
whether the five non-built-in members can be modelled "based on plain Π
somehow? Church encoding or so?", noting that a propositional model suffices —
the ι rules need not hold by `rfl`. Everything below marked **compiled** was
compiled this session at the pinned toolchain `leanprover/lean4:v4.29.1`; the
five evidence files are committed at `scripts/church-basis/` and §8 gives the
commands. §7 names what is argued but not machine-checked.*

## Verdict

**No. The basis does not encode, the circle stays closed, and layer 3 stays
dead — now for reasons that are proved rather than recalled.** The five types
do not fail for one reason; they fail for four different ones, and two of the
negatives are absolute — they survive `Quot`, `propext`, `funext`, and even
`em` and `choice`:

| type | on the actual basis (Π, `Eq`, `False`, `Quot`, `propext`, derived `funext`) | adding `em` + indefinite description | obstruction |
|---|---|---|---|
| `Option` | **no** | **yes — compiled**, `OptionQuot.lean` | witness extraction (`choose`), which Lean itself derives through `Subtype` |
| `Sigma` | **no** (junk, compiled) | no known route (§4.3) | strong pairing; possibly-empty instances defeat the `Quot` carrier |
| `Subtype` | **no** | **no — model argument** (§4.4) | comprehension: the fragment cannot build a provably empty `Type` |
| `List` | **no** | **no — model argument** (§5) | **infinity: every closed fragment type at universe 0 is finite** |
| `Acc` | partial: formation, `intro`, `inv`, `Prop`-induction **compile**; `Acc.rec` into `Sort v` does not | plausible via graph + `choose`, unverified (§6) | large elimination is a privilege the kernel attaches to the *inductive declaration*, and no fragment rule confers it on a Π-type |

Three sharpenings of the brief, stated early:

1. **The propositional-ι relaxation buys nothing here, anywhere.** What is
   refuted (compiled, §2) is the *bare existence* of a dependent eliminator at
   `Prop` motives with **no computation rules demanded at all** — the weakest
   thing a model recursor must still be. The relaxation is real, but it was
   already spent: it is what makes the gist's own `W` possible, and
   `W-FROM-LFP.md` §4 priced it in.
2. **`Quot` does change one cell, and the brief was right to ask.** With `em`
   and witness extraction, `Option` encodes *fully* — right universe, dependent
   `Sort v` recursor, propositional ι — via a quotient of `A → Prop` (§4.2,
   compiled). Universe inflation is therefore **not** the fundamental
   obstruction for the non-recursive types; comprehension and extraction are.
   But the cell only opens jointly with axioms `mini` did not then carry
   (`clause_for` named exactly one axiom, `Quot.sound`), and opening it would
   still leave `List` and `Subtype` closed. *(**Out of date, 2026-08-14**:
   `clause_for` now has three arms — `propext`, `Quot.sound` **and
   `Classical.choice`** — `checker/src/mini/axiom.rs:295–307`. The `List`/
   `Subtype` half of the sentence is unaffected and is the load-bearing half.)*
3. **`List` is the load-bearing negative, and it is airtight.** Not because
   recursion is hard — the junk argument treats `List` and `Option` identically
   — but because the fragment has **no axiom of infinity at universe 0**:
   replacing `⟦Type 0⟧` by V_ω (hereditarily finite sets) in the thesis's own
   ZFC model soundly interprets everything the basis offers, and no finite set
   models `List Prop` (§5). Lean's `Type 0` is only infinite because inductive
   declarations make it so. This kills any "model simple inductives out of
   nothing" layer on its own, whatever axioms are added.

For calibration, the thesis itself never claims otherwise: its §5 reduction
bottoms out in *eight primitive inductives* — "the eight inductive types ⊥, Σ,
+, ulift, ‖·‖, W, =, acc are indeed sufficient" (`thesis.txt:1900`) — and it
keeps them primitive rather than deriving them from Π. The gist's basis is a
sub-basis of that one. What this note adds is that the primitivity is not a
convenience: most of it is forced.

---

## 1. The criterion, and what "the fragment" means

`mini` interprets Π directly (the dependent-product and conditional clauses),
`Eq` as `eq_set`, `False` as the empty set; `modelgen` splices the `Quot`
quartet and `Quot.sound`, and derives `funext` from it rather than asserting it
(`MODELGEN.md` §1.5); `propext` would be of the same species. `em` was not carried, and
`Classical.choice` **now is** — `checker/src/mini/axiom.rs`'s `clause_for` has
three arms (`propext`, `Quot.sound`, `Classical.choice`, `:295–307`), and
`Clause::Choice` is built on `derived::choice::Epsilon` plus the per-rung
`checker/src/mini/choice_clause.rs`, with its own tests. *(This sentence said
both were absent and its `clause_for` count was one; corrected 2026-08-14. The
fragment named below is what the argument actually uses and is unchanged.)* So "encodable" here means: a term of the fragment
{Π, `Eq`, `False`, `Prop`, `Quot`, `propext`, `funext`} satisfying `MODELGEN.md`
§1.1's contract for the type — property 1, the recursor's declared type **on
the nose** after renaming constants; property 3, every level list the export's
own. The §1.1 relaxation is exactly and only that ι rules are theorems
(`T._model.iota_k_j`), not `rfl`.

Two consequences of §1.1 before any cleverness, both **compiled**:

* **Inflation.** `∀ X : Type u, X → (A → X → X) → X : Type (u+1)`. Lean's
  error, `UniverseNeg.lean`:

  ```
  error: Type mismatch
    (X : Type u) → X → (A → X → X) → X
  has type  Type (u + 1) … but is expected to have type  Type u
  ```

  The carrier `T._model.self` must carry the export's own sort — a universe
  shift is not a renaming, and every downstream declaration in the export
  applies `List` at `Type u`, so the alias `⟦List⟧ := ⟦List._model.self⟧`
  breaks at its first consumer.

* **Fixed elimination universe.** A Church encoding quantifies over one
  universe and can eliminate into no other: the candidate at `u = 0` cannot
  fold into `Type 1` even non-dependently (`ElimUniverseNeg.lean`: "`X` has
  type `Type 1` … but is expected to have type `Type`"). The export's
  `List.rec` carries its motive universe as a level parameter (property 3);
  the Church candidate has nowhere to put it. This alone disqualifies every
  naive Church encoding of a `Type`-level former, before dependency is even
  discussed.

## 2. Junk: no naive Church encoding has a dependent eliminator — Lean proves it

This is the crux the brief flags as obstruction 1, and it is worse for the
encodings than Geuvers's theorem says. Geuvers (*Induction is not derivable in
second order dependent type theory*, TLCA 2001) is a metatheoretic
underivability result. In Lean the classical axioms make it **internal**:
`ChurchRefute.lean` (compiled, 0 errors) proves, for each of `COption`,
`CList`, `CSigma`, `CSub`,

```lean
theorem no_dep_elim_option (A : Type) (a : A) :
    (∀ P : COption A → Prop, P cnone → (∀ b, P (csome b)) → ∀ o, P o) → False
```

— the eliminator's existence, at `Prop` motives, with no ι rules mentioned,
implies `False`. The witness is a classical junk inhabitant that branches on
whether the target type has three pairwise-distinct elements:

```lean
noncomputable def junkO {A : Type} (a : A) : COption A :=
  fun X n s => if Three X then s a else n
```

`junkO` behaves as `csome a` at `Nat` and as `cnone` at `Bool`, so canonicity
— which the eliminator alone already implies — is refutable by two
applications of `congrFun`. Since the whole project assumes Lean + `propext` +
`Quot.sound` + `choice` consistent, no subsystem derives the eliminator.
(`Or`/`∃` in the statement are core's, for convenience; both are
`Prop`-Church-encodable, as the gist itself does.)

Three remarks. First, **the recursive/non-recursive distinction is invisible
here**: `no_dep_elim_list` is the same seven lines as `no_dep_elim_option`.
Second, **this is exactly the failure `derived/`'s semantics predicts**: the
ZFC model validates `em` and `choice`, so the junk element *denotes*; any axiom
scheme strong enough to kill it (internal parametricity) is false in the
intended semantics and unavailable to this project on principle, not just in
practice. Third, the non-dependent recursor is fine and its ι rules hold by
`rfl` (also in the file) — the gap is precisely dependency, as Geuvers says.

## 3. The impredicative repair does not exist in Lean

Awodey–Frey–Speight (*Impredicative Encodings of (Higher) Inductive Types*,
LICS 2018) recover induction by carving the Church type down to its natural
elements. Checked against what it needs, per the brief:

* It works in an **impredicative universe of h-sets**. Lean has exactly one
  impredicative universe, `Prop`, and `Prop` is *definitionally
  proof-irrelevant* — `example (P : Prop) (a b : P) : a = b := rfl` compiles
  (`ChurchRefute.lean`, last line). Every `Prop`-encoded "datatype" is a
  subsingleton; `Option A` provably is not (`none ≠ some a` follows from the
  recursor at `Prop` motives). The AFS setting does not embed in Lean at all;
  in `Type u` the encodings are predicative and §1's universe failures return.
* Even granting the setting, the refinement is `Σ α, natural α` — a
  `Sigma`/`Subtype` carve; the naturality condition is Π-and-`Eq`-statable,
  but the *type* it carves is not Π-formable. And the AFS derivation of
  induction routes through the total space `Σ (n : N), P n` at every motive.
  Both consumptions are circular here.

So obstruction 1 stands, and the owner's relaxation does not touch it: the
missing thing is the eliminator term, not its computation rule.

## 4. `Quot`: what it buys — one full encoding — and where it stops

`Quot` was the brief's obstruction 4, and it is a genuinely stronger setting
than System F: it is the fragment's only former that *identifies* elements,
and quotients of powerset carriers stay at the carrier's universe.

### 4.1 The shape of the trick

`A → Prop : Type u` — same universe as `A`. The junk that comprehension cannot
remove, a quotient can *merge*: relate everything that is not a singleton
predicate, and the classes are exactly `{singletons} + one junk class`. For a
type with a nullary constructor, the junk class **is** that constructor.

### 4.2 `Option` encodes — compiled, but read the axioms

`OptionQuot.lean` (compiled, 0 errors): carrier
`OQ A := Quot (rel A) : Type u` with `rel P Q := P = Q ∨ (¬IsSing P ∧ ¬IsSing Q)`,
`qnone` the junk class, `qsome a` the singleton class; `qsome_ne_qnone`,
`some_inj`, canonicity via `Quot.ind` + `em`; a dependent recursor `qrec` into
`Sort v` for every `v`; ι propositionally (`qrec_none` is even definitional
after `dif_pos`). No universe inflation anywhere. This is a real partial
positive the previous assessments did not have: **for a never-empty,
non-recursive type, the whole interface is reachable from Π + `Eq` + `Quot`**.

The cost is exact and twofold: `em` defines the junk-collapsing normalizer
(`norm P := if IsSing P then P else fun _ => False`), and `Classical.choose`
extracts the witness inside `qrec`. The file's own audit, from the compile:

```
'qrec_some' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— `em` surfaces as `propext` + `choice` because core derives it by
Diaconescu. Neither is carried, and `choose` is not even an innocent
strengthening of `choice`: core derives it as `(indefiniteDescription p
h).val` where `indefiniteDescription … : {x // p x}` — `choice` applied at
`Nonempty {x // p x}` (`Init/Classical.lean:19-30` at v4.29.1). **Witness
extraction from raw `choice` is `Subtype`-mediated — the thing being
bootstrapped.** A basis could instead axiomatize `choose`/`choose_spec`
directly (both are statable with Church-`∃`, which is a Π type), but that is
a new, stronger axiom pair, every model becomes `noncomputable`, and §§4.4–5
show it still does not suffice.

### 4.3 `Sigma` does not follow

The same carrier idea (quotient of graphs `∀ a, B a → Prop`) fails at the
junk-merge: merging the junk class into a canonical class needs a *default
pair*, and `Σ a, B a` can be empty — `em` splits on `∃ a b, True`, but in the
no-pair branch the junk class survives and canonicity (which §2 shows the
eliminator forces) is unprovable. No fragment carrier is in sight that is
empty exactly when `Sigma` is: that is §4.4's problem. Standalone `Sigma` is
the one cell whose negative rests on "the natural routes each fail at a named
point" rather than a model argument — flagged in §7 — but nothing turns on
it: a layer needs `Subtype` and `List` regardless.

### 4.4 `Subtype` cannot exist — the nonempty-universe model

`Subtype` is comprehension itself, and here the negative is absolute.
Interpret the fragment in the thesis's ZFC model (thesis.txt §6) with
`⟦Type u⟧ := the nonempty sets` of the usual universe. Every fragment former
preserves nonemptiness: Π — a product of nonempty fibers is nonempty (meta-AC;
over an empty `Prop`-domain, a singleton); `Quot` — a quotient of a nonempty
set is nonempty; `Prop = P(1)` is nonempty; `Eq`/`False` land in `Sort 0`,
which is unconstrained (propositions may still be empty). `propext`, `funext`,
`Quot.sound`, `em`, `choice`, `choose` all remain valid. So **every closed
fragment term of a `Type`-level type denotes a nonempty set** — with or
without the classical kit. But `Subtype (fun _ : Prop => False)` is forced
empty by its own spec: the `Prop`-motive eliminator gives canonicity, every
element is some `mk x hx` with `hx : False`. No fragment term can satisfy
that. (The same argument disposes of `Empty`-like inductives, which a layer 3
would also have to model — a simpler declaration than any of the five.)

## 5. `List` cannot exist — no axiom of infinity

Same move at the other cardinal end, and this is the negative that closes the
question for good. Interpret the fragment — again *with* `Quot`, `propext`,
`funext`, `em`, `choice`, `choose` — in the thesis's model with
`⟦Type 0⟧ := V_ω`, the hereditarily finite sets. Every former stays inside:
`Prop = {0, 1} ∈ V_ω` (the model is classical, so `Prop` has two elements and
iterated powersets of it are all finite); a dependent product of finite sets
over a finite index is finite; a quotient of a finite set is finite; `Eq` is a
subsingleton. Universes above 0 are untouched. So every closed fragment term
of type `Type 0` denotes a **finite** set.

Now the spec. `List : Type u → Type u` at `u = 0` applied at `A := Prop` (a
closed fragment type) must contain `nil`, `cons True nil`,
`cons True (cons True nil)`, … and these are **pairwise provably distinct
from the contract alone**: `rec` at motive `fun _ => Prop` (motive universe 1,
which property 3 grants) with propositional ι separates `nil` from any `cons`,
and `rec` at motive `fun _ => carrier` gives `tail`, whose iteration reduces
distinctness of any two distinct spine lengths to `nil ≠ cons`. So the
carrier's interpretation has infinitely many elements — and is finite.
Contradiction; no fragment term models `List`, under any of the axiom
extensions considered. The infinitude of Lean's `Type 0` is an artifact of its
inductive types; a fragment with none has models where `Type 0` is finite,
and *that* — not recursion, not ι — is why the one genuinely recursive member
of the basis is unreachable.

(The junk refutation of §2 also applies to `List`, so even the naive encoding
at the wrong universe fails independently.)

## 6. `Acc`: the split cell

The `Prop`-Church `Acc` — the gist's own `lfp` shape — is the one place plain
Π delivers something real, because `Prop`'s impredicativity means **no
universe inflation** and proof irrelevance means the ι rules are free.
Compiled, in `ChurchRefute.lean`: `CAcc` with `Acc`'s exact formation type;
`CAcc.intro` with `Acc.intro`'s exact type; `CAcc.inv`; and `CAcc.recProp` —
the full dependent eliminator at motive universe 0, minor premise in
`Acc.rec`'s own shape, dependency on the proof discharged by definitional
proof irrelevance.

What does not come is exactly the kernel special case the brief names:
`Acc.rec` eliminates into `Sort v`. The naive term fails on impredicativity
(`AccLarge.lean`: "`motive` has type `α → Sort v` … but is expected to have
type `α → Prop`"). The structural route — destruct the proof — is
*subsingleton elimination*, a privilege Lean's kernel grants to the inductive
**declaration** `Acc` after inspecting its constructor; no rule of the
fragment grants it to a Π-type. The classical route — define the recursor's
graph as an impredicative `lfp` (Π-statable), prove `∃!` by `CAcc.recProp`,
extract with `choose` — looks derivable but was not compiled (§7), and it
consumes `choose`, i.e. `Subtype` + `choice` again. The thesis is consistent
with all of this: its own reduction *keeps* `acc` primitive, and reaches for
it precisely where W-types must be abandoned (`thesis.txt:1826`), with large
elimination for its `acc`-variant *derived from* Σ-projections
(`thesis.txt:1844`) — machinery the fragment does not have.

So: `Acc` the *predicate*, with well-founded induction — yes, from Π alone.
`Acc` the *declaration in the contract*, whose `rec` carries a motive
universe — no.

## 7. What is argued but not machine-checked, and what is unmeasured

* The two model arguments (§4.4, §5) are semantic non-derivability proofs,
  not compiles. What is asserted and not formalized: that each clause of the
  thesis's model (thesis.txt §6) preserves "nonempty" resp. "hereditarily
  finite" at the stated universe. Both checks are finite case analyses over
  the fragment's formers — Π, `Eq`, `False`, `Prop`, `Quot` — and both fail
  the moment an inductive declaration enters, which is the point.
* `Acc.rec` into `Sort v` from `CAcc` + `choose`: sketched, not compiled. A
  metatheoretic proof that it is *underivable without* `choose` is also not
  given; no route is known, and the two candidate routes each need a named
  absent thing.
* Standalone `Sigma` (§4.3) has no model-theoretic refutation here — only the
  compiled junk refutation of its Church form and the named failure of the
  `Quot` route. If someone produces a fragment `Sigma`, §§4.4–5 still hold.
* Whether `mini` *could* carry `em`/`choose` as axiom clauses was not
  re-examined beyond `W-FROM-LFP.md` §8's note; it is moot, since carrying
  them opens only the `Option` cell.

## 8. The ledger, and reproducing

**What would `mini` stop needing if all five encoded?** Nothing changes from
`W-FROM-LFP.md` §3's arithmetic except the direction of the bound. Measured on
this tree: the §5.2/§5.3 translation is 16,800 lines across 22 modules —
6,758 in the plain non-indexed arms (`class_s`, `recursor`, `rec_prop`,
`rec_dep`, `rec_trunc`, `iota_dep`, `iota_model`), 6,526 in the indexed arms
(`*_ix`, `minor_ix`), 3,516 in `acc` + `rec_acc*`. The gist covers plain
non-indexed class-P inductives only (`W-FROM-LFP.md` §5), so even the maximal
counterfactual retires at most the 6,758 and keeps the 10,042 — while paying
the unestimated `Expr`-construction cost of `W-FROM-LFP.md` §4 and a
recogniser. That would at least have been a real ledger entry. But the
counterfactual is unreachable twice over — `List` (§5) and `Subtype` (§4.4)
are not encodable under *any* axiom extension this project could accept — so
the actual entry is what it was: **layer 3 deletes nothing, and the basis
exemption it would need costs everything it was for. Closed for good.**

```bash
T=~/.elan/toolchains/leanprover--lean4---v4.29.1
cd scripts/church-basis
for f in ChurchRefute OptionQuot; do          # must compile: 0 errors
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean $f.lean; done
for f in UniverseNeg ElimUniverseNeg AccLarge; do  # must fail: 1 error each, quoted above
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean $f.lean; done
```

Compile results this session: `ChurchRefute` 0 errors, `OptionQuot` 0 errors;
`UniverseNeg`, `ElimUniverseNeg`, `AccLarge` exactly one error each, quoted in
§§1, 6. Gist referenced: `LFP.lean`, md5 `ebea23ac3ac492daf8c1b1467d28b393`,
as in `W-FROM-LFP.md` §9.
