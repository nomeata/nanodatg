# `modelgen` — the model of an inductive Lean's kernel builds by hand, as an export filter

`modelgen` reads a Lean 4 `.ndjson` export, writes the same export back out,
and inserts, beside each declaration whose recursors the kernel had to
*construct* rather than read off the declaration, an ordinary Lean development
that models it: the type formers, the constructors, the recursors, and the ι
rules — all as ordinary declarations, all proved, all checked by Lean's kernel.

**There are two such declarations and therefore two constructions.**

* A **nested** inductive, modelled by specialising it into a mutual block with
  one extra member per nested occurrence, and proving the export's recursors
  over that. `Modelgen/Model.lean`.
* A **plain mutual block**, modelled by packing the members' index telescopes
  into a tag and the members themselves into one *single* inductive over it.
  `Modelgen/Mutual.lean`.

They are not one construction at two settings, and §1.6 says why: a nested
model *keeps* mutuality and a mutual model *removes* it, so the second at zero
mimics would be the identity. What they share is the interface — §1's names and
statements are the same ones, minus the rows that are about nesting.

**And they compose** (§1.7). A nested declaration's model *is* a mutual block,
so the second construction runs on it in the same pass: the output carries the
mutual model of `T` and the simple model of that model. Every mutual block in
the output has a model beside it, the ones this tool wrote included.

```bash
modelgen IN.ndjson -o OUT.ndjson|- [--check-recursors] [--quiet]
```

The input is **trusted and not typechecked**; that is where the speed comes
from. Only the declarations the tool *generates* are checked, and they are
checked one at a time by `Environment.addDeclCore` with checking on. A proof the
generator builds and the kernel rejects is a **decline**, never an emission.

It lives in `modelgen/`, is a separate Lean package pinned to
`leanprover/lean4:v4.29.1` — the toolchain `lean4export` 3.1.0 was built at and
the corpus was exported with, githash `f72c35b3` — and is out of the Rust
build's way entirely.

**It runs on Mathlib**: 5.6 GB, 268.74 s, 23,879,684 KB, **92 models and 0
declines** — all 41 nested declarations, all 41 of their models in turn (§1.7),
and all 10 plain mutual blocks — with `nanoda_bin` accepting the result. §6.

---

# 1. The interface contract

**This section is the deliverable.** A checker that consumes `modelgen`'s output
needs to know the construction only through what is written here. Everything
below is stable; nothing else about the output is.

§1.1 to §1.5 are the model of a **nested** declaration. **§1.6 is the model of
a plain mutual block**, and it is deliberately the same contract with the four
rows that are about mimics removed: same `R_k._model.self`, same
`T._model.ctor_j`, same `T._model.rec_k`, same `T._model.iota_k_j`, same level
lists, same three properties. A consumer written against §1 needs one new fact
and no new shape. **§1.7 is the two composed**: a nested declaration's model is
a mutual block, so the filter models that too, in the same run, and the second
layer is §1.6's names read at a different root.

Let the declaration be a block with **real members** `R₀ … R_{r−1}` — the
export's own `all`, so `r = 1` unless the block is mutual — `numNested > 0`,
`m` mimics (one per distinct nested occurrence), `n = r + m` block members, a
parameter telescope `p⃗` of length `np` and level parameters `ℓ⃗`. Write
`T = R₀`. Write `ι⃗ₖ` for block member `k`'s **index** telescope, which may be
a different length for each member — `ITree.rec` has one index and its `List
(ITree N.z)` mimic's motive has none. A real member's is the export's own; a
**mimic's is the container's**, so `Vec VTree`'s mimic has one and `List
Tree`'s has none. Write `ι⃗ᵢ` for mimic `i`'s, which is `ι⃗_{r+i}`.

**Block index `k` runs `0 … n−1` in the export's own motive order**: the real
members first, in `all` order, then the mimics in discovery order. That is
Lean's order and not a convention chosen here — §4.2 measures it.

**Every generated constant carries `ℓ⃗`**, in the export's own order, and is
written `T._model.x.{ℓ⃗}` at every use; a recursor and its ι theorems carry
their motive universe *in front of* `ℓ⃗`, which is the order Lean itself
writes. `ℓ⃗` is empty for a monomorphic declaration, and every level list below
is elided for readability.

| name | kind | statement |
| --- | --- | --- |
| `T._model.0` … `T._model.{n−1}` | mutual inductive block | member `k < r` is the copy of `R_k`; member `r+i` is the mimic of occurrence `i`. Constructors are `T._model.k.<last component of the original>`. |
| `R_k._model.self`, `k < r` | `def` | `∀p⃗ ι⃗ₖ, Sort u := T._model.k p⃗` — **the carrier of real member `R_k`**. `⟦R_k⟧ := ⟦R_k._model.self⟧` is the keying. **One per real member**, so a one-member block has `T._model.self` and nothing has moved. |
| `T._model.pack_i` | `def` | `∀p⃗ ι⃗ᵢ, occᵢ ι⃗ᵢ → T._model.{r+i} p⃗ ι⃗ᵢ` |
| `T._model.unpack_i` | `def` | `∀p⃗ ι⃗ᵢ, T._model.{r+i} p⃗ ι⃗ᵢ → occᵢ ι⃗ᵢ` |
| `T._model.unpackPack_i` | `theorem` | `∀p⃗ ι⃗ᵢ l, Eq (unpack_i p⃗ ι⃗ᵢ (pack_i p⃗ ι⃗ᵢ l)) l` — the **retraction** |
| `T._model.packUnpack_i` | `theorem` | `∀p⃗ ι⃗ᵢ b, Eq (pack_i p⃗ ι⃗ᵢ (unpack_i p⃗ ι⃗ᵢ b)) b` — the **section** |
| `T._model.ctor_j` | `def` | the **block's** `j`-th constructor's declared type — the real members' constructors concatenated in `all` order — with each `R_k` rewritten to `R_k._model.self` and **nothing else** |
| `T._model.rec_k` | `def` | the declared type of the export's recursor at block index `k`, with the `R`s, their constructors and their recursors rewritten to their model counterparts and **nothing else** |
| `T._model.congrPack_i` | `theorem` | `∀p⃗ ι⃗ᵢ l₀ l, Eq l₀ l → Eq (pack_i p⃗ ι⃗ᵢ l₀) (pack_i p⃗ ι⃗ᵢ l)` |
| `T._model.iota_k_j` | `theorem` | `∀p⃗ M⃗ S⃗ f⃗, Eq (rec_k p⃗ M⃗ S⃗ ι⃗ (c f⃗)) (Sⱼ f⃗ ih⃗)` — the `j`-th rule of `T._model.rec_k`. **A rule binds no index of its own**: `ι⃗` is determined by the constructor's result and is written out from it, exactly as the export's own rule does. |

Here `occᵢ` is the `i`-th nested occurrence, **the container at its
parameters** and written at `p⃗`: `List T._model.self` for `inductive Tree |
node : List Tree → Tree`, `Vec VTree._model.self` for `node : Vec VTree (N.s
N.z) → VTree`. It is a *type* only once `ι⃗ᵢ` is applied, which is why the five
signatures above carry that telescope between `p⃗` and their argument.

> **`ι⃗ᵢ` is empty for every container without indices**, so for `List`, `Box`,
> `Array` and everything else in the corpus these five signatures read exactly
> as they did before an indexed container was supported. A consumer that
> ignores `ι⃗ᵢ` is not wrong about any shape it could already handle; it is
> only unable to key the new one.

The index telescope belongs to the **container**, not to the occurrence: `Vec
WTree N.z` and `Vec WTree (N.s N.z)` are one occurrence at two indices, one
mimic and one `pack_i`, because the occurrence is `Vec WTree`.

Indices are `0`-based throughout, and `Name.num` is used for the block members
(`T._model.0`) while `Name.str` is used for everything else
(`T._model.pack_0`). **The model's recursor index is the block index,
uniformly** — `T._model.rec_k` is always block index `k`. The **export's** name
for that recursor is not uniform once the block is mutual, and this is the one
place a consumer has to do arithmetic:

> the export calls block index `k`'s recursor `R_k.rec` when `k < r`, and
> `R₀.rec_{k−r+1}` when `k ≥ r`.

For `r = 1` that is `T.rec`, `T.rec_1`, … against `T._model.rec_0`,
`T._model.rec_1`, …, exactly as before. For `nest_mutual_both`'s `A`/`B` it is
`A.rec`, `B.rec`, `A.rec_1`, `A.rec_2` against `A._model.rec_0 … rec_3`.

## 1.1 The three properties a consumer may rely on

1. **`T._model.rec_k` is the export's recursor at block index `k`, stated
   about different constants.** Exactly: take that recursor's declared type as
   the export carries it, rewrite `R_k ↦ R_k._model.self` for every real
   member, each of their constructors to its `T._model.ctor_j`, and the
   export's recursor at block index `m` to `T._model.rec_m` (at the same level
   list), and nothing else; the result is `T._model.rec_k`'s declared type on
   the nose. That is what makes `⟦A.rec_1⟧ := ⟦A._model.rec_2⟧` an alias rather
   than a coincidence. The same holds for `T._model.ctor_j` against the block's
   `j`-th constructor.

2. **`T._model.iota_k_j` is `T.rec_k`'s `j`-th rule, in the export's own
   order.** The `j`-th ι theorem is about the constructor the `j`-th rule of the
   export's `T.rec_k` is keyed by — `T.node` at the root, `List.cons` at a
   mimic. Its statement is the rule's, with the same rewriting, and the rule's
   right-hand side appears verbatim modulo that rewriting. **A consumer may
   therefore line ι theorems up with rules by index, and check the key by
   name.**

3. **Every level list is the export's own.** `T._model.rec_k`'s level
   parameters are those of the recursor it models, name for name and in order:
   the motive universe first, then the block's own. `T._model.iota_k_j`
   carries the same list. Everything else carries exactly `ℓ⃗`. The motive
   universe's *name* is not chosen here — Lean mints it, from the same level
   parameter list, for `T._model.0.rec` as for `T.rec` — and property 1's
   syntactic equality is what says the two agree.

   **`monomorph` reads this property rather than the construction**
   (`MONOMORPH.md` §4.1). It takes `ℓ⃗` off the carrier `T._model.self` and
   keeps whatever `rec_k` and `iota_k_j` have beyond it as a level parameter,
   which is what puts all of a model's families under one marker. Two
   consequences for anything that changes the shapes above: the carrier must
   keep carrying exactly `ℓ⃗` and must keep being written **before** the
   recursors and ι theorems that hang off the same prefix; and this holds for
   §1.6's construction too, where the carrier is the only name the two
   constructions agree on (there is no `T._model.0` there).

   **And it reads the same prefix once more, for the instantiation** — this is
   what `MONOMORPH.md` §1.2 property 4 rests on. `T._model.x` is keyed to `T`
   and emitted at exactly `T`'s set of instantiations, because nothing in the
   file references a model and a reference is all the sweep otherwise has. A
   third consequence follows for anything changing the shapes above: a
   declaration a model introduces must keep hanging off `T._model` for a `T`
   the file **declares**, and must keep carrying `ℓ⃗` in `T`'s own order. A
   declaration that does neither is not wrong — a spliced `T._model.funext`
   (§1.5) carries universes that are nobody's motive and is monomorphized by
   its use sites like anything else — but it is outside the property, and
   `monomorph` tells them apart by arity and by nothing else.

Both 1 and 2 are *checked by the tool itself*, against the recursors the kernel
mints for `T`, and reported by the `statements: N compared …, 0 differ` line.
The check is a port of `mini/tests/nested.rs`'s `check_recursors` and
`check_iotas`.

## 1.2 What the contract does **not** say

* **Nothing about `T._model.0`'s constructors, `pack`, `unpack` or the round
  trips beyond their statements above.** Those are the construction, and the
  point of this tool is that the checker stops needing to know it.
* **Nothing about the order of the mimics** except that it is the export's own:
  mimic `i` is the occurrence the export's recursor at block index `r+i`
  eliminates. A consumer reads the correspondence off the recursor index and
  never off the container.
* **The model may not be identified with `T` definitionally.** `T` is a
  primitive inductive and `T._model.self` is a `def` over a different block;
  Lean has no conversion between `M₀ : T._model.self → Sort v` and `m1 : T →
  Sort v`. "Same statement about different constants" is true of the statement
  and false of the type.

## 1.3 When there is no model

`modelgen` emits nothing for a declaration it declines, and says which shape
stopped it **on stderr** (§1.4). **A consumer must therefore treat the absence of
`T._model.self` as "no model", not as an error**, and the presence of a
`T._model.*` name it did not generate as an ordinary declaration of the file —
`mini/tests/fixtures/nested_keying.lean` declares `UTree._model.self := N`
precisely to make that case exist. `modelgen` will not collide with it: the
name guard scans **the whole input file**, not the prefix before the
declaration, and declines `UTree` for `nested model name taken`.

## 1.4 The two streams and the four exit statuses

**This is part of the contract**, and `mini` keys on it: it execs this binary
with `-o -` and streams the result into its parser
(`mini/src/modelgen.rs`).

**The export goes to the `-o` target and nothing else ever does.**

* `-o OUT.ndjson` writes a file.
* **`-o -` is stdout**, first class, so a streaming consumer does not have to
  rely on `/dev/stdout` existing. The bytes are the same either way.
* No `-o` at all runs the filter and writes no export, which is what
  `--check-recursors` alone is for.

**Everything else goes to stderr** — the report, and every error. So the
report does not have to be silenced to keep the export clean:

```
FTree: model of 17 declarations
HTree: model of 18 declarations
HTree: prelude spliced — Quot, Quot.mk, Quot.lift, Quot.ind, Quot.sound, HTree._model.funext
statements: 38 compared against the installed recursors' own rules, 0 differ
```

`--quiet` suppresses the report. It is a preference, not a correctness
requirement; it was the latter while the report was on stdout, and a streaming
consumer then had to pay for a clean export with every decline *reason* — mini
could say `no nested model in the export` and not say why. **The export is not
moved to stderr instead**: `Environment.addDeclCore` `panic!`s to stderr on one
corpus file (§5.5), so stderr is not a stream anything may be parsed out of.
That file is the measurement rather than the worry — `grind-ring-5.ndjson` at
`-o -` exits 0 with a clean 10 MB export on stdout and the panic and its
backtrace on stderr, and had the export been on stderr they would be one
stream.

| status | means | wrote an export? |
| --- | --- | --- |
| `0` | ran to completion — **including every decline** | yes, if `-o` was given |
| `1` | usage: the command line is not one this tool accepts | no |
| `2` | the input could not be read, or is not an export this tool can parse | no |
| `3` | this tool's own failure | no |

The three failures were one status until they were written down here: a bad
flag, a missing file and an escaping exception all exited 1, so a consumer
could not tell a toolchain problem from a bad export. **A decline is not a
failure** and stays 0 — §1.3 is the reason, and the reason is on stderr.

`3` covers an exception out of the filter *and* a generated model whose
statement did not match the rule the installed recursor carries (§4, oracle 3).
The second is the one worth naming: such a model typechecks and states
something other than the export's own rule, which is exactly the model a
consumer must not key on, and it used to be reported in a line of the report
and then written anyway with a 0. Nothing in the tree reaches it — 450
statements, 0 differing.

A run that **passes the input through unchanged** because Lean's kernel would
not load one of its declarations is a `0` with `passed through unchanged — …`
on stderr; the filter did what a filter should when it can do nothing.
`--check-recursors` finding a mismatch is also a `0`: that is a statement about
the *input's* recursors, not about anything this tool generated, and §4.2's
five `bad/` files have ten.

## 1.5 The prelude a model splices, and why the report names it

The model's **proofs** reach four constants that no signature in §1 mentions:
`Eq` (with `Eq.refl` and the `Eq.rec` the kernel mints for it), and — only for
a constructor field at a mimic *under a binder* — `Quot`, `Quot.sound` and
`funext`. An export is not obliged to declare any of them. `Eq` is in most of
the corpus but `modelgen/tests/decline_no_eq.lean` is a file without one, and
**`funext` is in 1 of the 157 corpus files** and not in `init-prelude`.

**A prelude constant the input does not declare is spliced in.** Lean's own,
verbatim: `Eq` and the quotient from `Init/Prelude.lean`, `Quot.sound` and
`funext` from `Init/Core.lean`, and `modelgen/tests/funext_binder.lean` is that
development written out as a fixture so the two can be read side by side. Each
goes through `Environment.addDeclCore` with checking on, like everything else
this tool emits.

**`funext` is derived and not asserted.** It is a theorem in Lean — `congrArg`
on the extensional application of a `Quot`, at `Quot.sound` — and it is a
theorem here, with `congrArg` inlined to one `Eq.rec` the way
[`Modelgen.Gen.congrFunFor`] already is. An **axiom** would have been worse than
useless rather than merely inelegant: `mini` declines a non-standard axiom
anything in the file refers to (`mini/src/axiom.rs`,
`mini/src/unused_axiom.rs`), and a fabricated `funext` would be referred to by
every proof that used it, so it would trade a decline here for a decline
downstream and widen the trust surface to buy nothing. The narrowing at `#121`
does not soften that: it exempts axioms **nothing** depends on, which is exactly
what a spliced `funext` would not be.

Four properties hold this down, and each is measured:

1. **Only when a model is actually being spliced.** Every prelude declaration
   is built inside `Modelgen.iso` or `Modelgen.mutualIso`, so a file with
   nothing to splice is untouched and §3's byte-identity survives: over the 230
   `.ndjson` in the tree, 186 come back byte-identical, among them **155 of the
   157 corpus files** and 31 of the 42 in `mini/tests/fixtures`. Exactly **one**
   file left that set for this feature — `decline_no_eq`, which now gets a
   model — and eleven more left it for §1.6's, all eleven of them mutual
   fixtures under `mini/tests/fixtures`. Filtering an already-spliced output
   again is byte-stable too: the name guard declines the whole file, and a block
   this tool wrote is not modelled a second time (§1.6).
2. **Present beats spliced.** If the input declares one, the input's own is
   used and nothing is written. `funext_binder` declares Lean's development
   itself and its five models are unchanged, byte for byte, from before the
   splice existed. A splice **adds**; it never substitutes.
3. **Once.** The second declaration in a file to need `funext` finds the
   quotient already installed and pays only for its own `funext`.
   `infinitary`'s three binder shapes are 18, 14 and 20 declarations for that
   reason and not 18, 16 and 22.
4. **Reported, always.** A splice is a decision on record:

   ```
   HTree: prelude spliced — Quot, Quot.mk, Quot.lift, Quot.ind, Quot.sound, HTree._model.funext
   RTree: prelude spliced — RTree._model.funext
   ```

   A consumer reading the filtered export is told which of its declarations are
   not the input's, by name, on the same stream as the models and the declines.

**The names, and why one of them is different.** `Eq`, `Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind` and `Quot.sound` are spliced under **Lean's own names**,
because those names are load-bearing beyond this file: §1.1's ι theorems are
stated at `Eq`, the kernel fixes the four quotient names, and
`mini/src/axiom.rs` selects the `Quot.sound` clause **by that exact name** — a
namespaced copy of either would be a non-standard axiom and refused. `funext`
appears in **no** emitted statement, only inside proofs, so it is the one that
can carry the model's namespace and does: **`T._model.funext`**, per §1's
convention. That is also where the collision risk actually was — a file may
declare a `funext` of its own later, and `nested_keying.lean` exists because a
file can declare a name the model wants. The `nested model name taken` guard
covers all of them and scans the whole input file, not the prefix.

**The quotient is emitted as the quotient**, four records of `{"quot": …}` with
`kind` read off the `QuotKind` the kernel stamped on each constant — the same
structural recognition `MONOMORPH.md`'s carried-built-ins set uses on the way
in, and not a name test. `nanoda_bin` accepts the result.

**What this cost in fidelity to Lean's acceptance.** Nothing measured: the
whole `vendor/arena-tests` corpus filtered through this and run under
`nanoda_bin` gives `152 matched, 0 mismatched, 2 declined`, identical to the
unfiltered corpus, and **no `bad/` file flips from rejected to accepted**. That
is not an accident of care — no corpus file splices anything, because every one
with a nested inductive already declares `Eq` and none has a field at a mimic
under a binder — but it is measured rather than argued, because
`MONOMORPH.md` §9's precedent is that a permissiveness change flips `bad/`
files and the honest thing is to name them.

## 1.6 The model of a plain mutual block

A **plain** mutual block is one with `r ≥ 2` members and `numNested = 0` on
every one of them. Lean's kernel constructs its recursors — one per member,
over a *shared* motive and minor vector — and a checker that only knows how to
add a single inductive cannot follow it. So `modelgen` writes the same
development for it that it writes for a nested declaration, over a different
construction.

**It is a different construction and not a specialisation, and this was decided
by reading rather than by guessing.** §1's table above models a nested
declaration by *specialising it into a mutual block* of `r + m` members. Set
`m = 0` — which is exactly what "a plain mutual block is the nested case with no
mimics" would mean — and that block is the declaration itself under fresh
names: the model is the identity and a consumer that could not take a mutual
block still cannot. What is needed here is the opposite operation, removing
mutuality, and `mini/src/mutual_aux.rs` is 1059 lines of it in Rust. This is
that encoding, ported.

Notation as above: parameters `p⃗` of length `np`, level parameters `ℓ⃗`,
resultant sort `Sort u` — the kernel requires every member to land at the same
one — and `ι⃗ₖ` for member `k`'s index telescope, **which may be a different
length for each member**.

| name | kind | statement |
| --- | --- | --- |
| `T._model.tag` | `inductive` | `∀p⃗, Sort W`, with one constructor `T._model.tag.k : ∀p⃗ ι⃗ₖ, T._model.tag p⃗` per member |
| `T._model.aux` | `inductive` | `∀p⃗, T._model.tag p⃗ → Sort u`, carrying **every constructor of every member**, named `T._model.aux.k.<last component of the original>` |
| `R_k._model.self` | `def` | `∀p⃗ ι⃗ₖ, Sort u := fun p⃗ ι⃗ₖ => T._model.aux p⃗ (T._model.tag.k p⃗ ι⃗ₖ)` — **the carrier of member `R_k`**, one per member, and `⟦R_k⟧ := ⟦R_k._model.self⟧` is the keying |
| `T._model.ctor_j` | `def` | the **block's** `j`-th constructor's declared type — the members' constructors concatenated in `all` order — with each `R_k` rewritten to `R_k._model.self` and **nothing else** |
| `T._model.rec_k` | `def` | the declared type of `R_k.rec`, with the `R`s, their constructors and their recursors rewritten to their model counterparts and **nothing else** |
| `T._model.iota_k_j` | `theorem` | `∀p⃗ M⃗ S⃗ f⃗, Eq (rec_k p⃗ M⃗ S⃗ ι⃗ (ctor_j f⃗)) (Sⱼ f⃗ ih⃗)` — the `j`-th rule of `R_k.rec`, in the export's own order |

`W` is the only number here that is not read off the declaration: the tag's
constructors carry the members' index *values* as fields, so `W` is `max 1` of
every index type's own sort. It is `Sort 1` for every block without indices and
is level-polymorphic where an index's type is — `QA` in
`modelgen/tests/mutual_odd_shapes.lean`. It is an over-approximation and is
allowed to be.

**The three properties a consumer may rely on are §1.1's, verbatim**, with one
simplification: **the recursor index *is* the block index**, because there are
no mimics. `T._model.rec_k` is `R_k.rec` — `all[k].rec`, with no arithmetic —
and `T._model.iota_k_j` is its `j`-th rule.

**And what §1.2 does not say.** Nothing about the tag, the carrier, their
constructors or the sort `W` beyond the table; those are the construction, and
the point is that the checker stops needing to know it. `T._model.aux` may not
be identified with any `R_k` definitionally, for §1.2's third reason.

### Where it sits in the output, and the one place that differs

A nested model is emitted **before** the declaration it models. A mutual model
is emitted before it *when it can be*, and otherwise immediately after the
input's own `Eq`.

The reason is mechanical. A nested model restates the recursors of the
*specialised* block, which this tool builds itself, so it can be generated
before the input's block is installed. A plain mutual block has no such second
inductive — `T._model.aux.rec` is not `R_k.rec` at any renaming — so its
statements are read off the recursors **Lean minted for the input's own
block**, which exist only once that block has been replayed. Its ι theorems are
then stated at `Eq`, and an export's dependency order routinely puts `Eq`
*after* a block that does not itself use it: `mini/tests/fixtures`'
`mutual_iota_reduction`, `mutual_parameters` and `mutual_index_sorts` all do,
and `mini/src/mutual_aux.rs`'s `expand` holds its rule theorems back to the end
of the file for exactly this reason. A file that declares **no** `Eq` does not
wait — §1.5 splices one.

So the guarantee a consumer gets is the one dependency order gives it: every
`T._model.*` record precedes any use of it, and the model of a plain mutual
block is a contiguous run of records somewhere at or after its block. It is
never interleaved with anything.

---

## 1.7 The two constructions compose, in one run

**A nested declaration's model is a mutual block**, `T._model.0 … T._model.{n−1}`
(§1). So the filter models that block too, with §1.6's construction, in the
same pass — **two steps, explicitly**, and no attempt at a direct
nested-to-single construction. What the output carries for one nested
declaration is therefore a development twice over:

| layer | what it is | root of the naming |
| --- | --- | --- |
| 1 | §1's mutual model of `T` — the specialised block and everything over it | `T._model` |
| 2 | §1.6's simple model of *that block* — a tag, one carrier, and everything over them | `T._model.0._model` |

**A model is emitted beside the thing it models and never in place of it**, so
the mutual block is still written. What composition buys is not an output with
no mutual block in it; it is that **every mutual block in the output has a
model beside it, the ones this tool wrote included**. A consumer that can add
only a single inductive can now skip all of them.

### The names, and why they need no new rule

The second layer is §1.6's scheme applied at `T._model.0`, so it reads off the
same four builders:

| | layer 1, at `T` | layer 2, at `T._model.0` |
| --- | --- | --- |
| carrier | `R_k._model.self` | `T._model.k._model.self` |
| constructor | `T._model.ctor_j` | `T._model.0._model.ctor_j` |
| recursor | `T._model.rec_k` | `T._model.0._model.rec_k` |
| ι rule | `T._model.iota_k_j` | `T._model.0._model.iota_k_j` |

and the two new inductives are `T._model.0._model.tag` and
`T._model.0._model.aux`. **`mini/src/nested_splice.rs`'s name builders already
spell both columns**: `carrier_name`, `ctor_name`, `rec_name` and `iota_name`
take the root as an argument, so layer 2 is the same four functions at
`t = T._model.0` and `t = T._model.k`. No new rule, and nothing about the
convention moved.

**Nothing can collide.** Layer 1 writes under `T._model` and `R_k._model`;
layer 2 under `T._model.k._model`. `T._model.ctor_0` and
`T._model.0._model.ctor_0` are distinct names, and `R_k._model.self` could only
meet `T._model.k._model.self` if a *declaration* of the input were called
`T._model.k`, which the name guard would already have refused. Both layers'
guards run — `modelgen/tests/nested_keying.lean` reaches layer 1's (`UTree`
declines and gets no layer 2 either, because layer 2 only runs on a layer 1
that succeeded) and `modelgen/tests/mutual_keying.lean` reaches layer 2's.

### The boundary: composed in one run, and still idempotent

This is the part worth stating carefully, because the two requirements pull
against each other. Composition means the tool models a block **it wrote
itself**; idempotence means re-running the filter on its own output must change
nothing. Both hold, and they are separated by *where the block comes from*
rather than by any test on its name:

* **Layer 2 runs from inside layer 1**, on the block that has just been added
  to the environment and is not in the input at all
  (`Modelgen.blockOf` reads it back out of the environment for exactly this
  reason). Nothing about the input drives it.
* **The input scan has no "is this a block I wrote?" test.** On the tool's own
  output the block `T._model.0 …` is an ordinary `induct` record and *does*
  reach §1.6's branch — and declines, because `T._model.0._model.tag` is
  already in the file and the name guard says so. Idempotence is carried by the
  same mechanism that already carried it for a nested declaration.

There used to be a `Modelgen.isOwnModelBlock` guard here, matching a block all
of whose members are `Name.num (Name.str T "_model") k`. It is **gone**: it was
a second mechanism doing what the name guard already does, and a second
mechanism is a second thing to keep in step.

**Measured, not argued.** Filtering an already-composed output declines twice
per nested declaration — once at `mutual model name taken
(T._model.0._model.tag)` for the block and once at `nested model name taken
(T._model.0)` for the declaration — and the file comes back **byte for byte**,
checked with `cmp` on `nested_iota`, `nested_shapes`, `nest_odd_shapes` and
`nest_fam_arg`. Over the whole tree the byte-identity count is **186 of 230,
the same 186 as before composition**, and the eleven `mutual model name taken`
declines in it are the ten already-filtered copies in `mini/tests/fixtures` plus
`mutual_keying`'s deliberate one. §4 has the sweep.

**`mini/tests/fixtures`' five nested exports were regenerated for this**, with
`scripts/export-fixture.sh`, and that is not a side effect to be quiet about:
they are committed *already filtered* so that `cargo test` needs no Lean, and a
generator that writes more has to write it there too or `modelgen/Test.lean`'s
cross-check fails — which is what that check is for. They grew 4114 → 5505,
1774 → 2385, 3856 → 5375, 1164 → 1514 and 1099 → 1449 lines. `mini` reads the
result with no gate of its own and **certifies every declaration of both
layers**: `nested_iota_arm` goes from 45 pairs, 45 `constEv`, 45 `typeEv` to
**63 / 63 / 63** with `waiting` empty, `gapped` 0 and `untranslated` (0, 0), and
`nested_keying` from 45 / 43 / 44 to **63 / 61 / 62** with the same single
`UTree` blockage it always had. Both are `mini/tests/nested.rs` assertions and
both are re-pinned there.

---

# 2. What is generated, and how much of it

Per nested declaration: 1 (block) + `r` (carriers) + 4·m (the maps and round
trips) + one per constructor of the block's **real** members + one per block
member (recursors) + m (congruences) + one per ι rule.

Per plain mutual block (§1.6) the arithmetic is simpler and has no free
parameter: **`2 + 2r + 2c`** for `r` members and `c` constructors — the tag and
the carrier, one type former and one recursor per member, one definition and
one ι theorem per constructor. Plus Lean's `Eq` where the input has none.

| fixture / declaration | mimics | ι rules | declarations |
| --- | --- | --- | --- |
| `nested_iota` / `Tree` | 1 | 4 | 15 |
| `nested_iota` / `BTree` | 2 | 6 | 24 |
| `nested_iota` / `PT α` | 1 | 4 | 15 |
| `nested_deep` / `DTree` | 2 | 6 | 23 |
| `nested_shapes` / `Tree` | 1 | 4 | 15 |
| `nested_shapes` / `PTree` | 1 | 3 | 14 |
| `nested_shapes` / `DTree` | 2 | 6 | 23 |
| `nested_shapes` / `BTree` | 1 | 3 | 14 |
| `nested_iota_arm` / `Tree` | 1 | 4 | 15 |
| `nested_keying` / `Tree` | 1 | 4 | 15 |
| `nested_keying` / `UTree` | — | — | declined, name taken |
| `poly_nested` / `PTree.{u}` | 1 | 4 | 15 |
| `poly_nested` / `QTree.{u,v}` | 2 | 5 | 22 |
| `dependent_fields` / `DTree` | 1 | 4 | 15 |
| `dependent_fields` / `ETree` | 1 | 4 | 15 |
| `dependent_fields` / `KTree` | 1 | 4 | 15 |
| `infinitary` / `FTree` | 1 | 5 | 17 |
| `infinitary` / `GTree` | 1 | 5 | 15 |
| `infinitary` / `ZTree` | 2 | 7 | 22 |
| `infinitary` / `HTree` | 1 | 4 | 15 + 3 spliced |
| `infinitary` / `RTree` | 1 | 3 | 13 + 1 spliced |
| `infinitary` / `OTree` | 2 | 3 | 19 + 1 spliced |
| `indexed_decl` / `ITree` | 1 | 4 | 15 |
| `indexed_decl` / `I2` | 1 | 4 | 15 |
| `indexed_decl` / `I3` | 1 | 4 | 15 |
| `indexed_container` / `VTree` | 1 | 4 | 15 |
| `indexed_container` / `WTree` | 1 | 5 | 17 |
| `indexed_container` / `UTree` | 1 | 5 | 16 |
| `nest_index_cross` / `ITr` | 1 | 4 | 15 |
| `nest_index_cross` / `CTree` | 1 | 4 | 15 |
| `nest_index_cross` / **`PA`/`PB`** | 2 | 8 | 29 |
| `nest_index_cross` / **`XT`** | 2 | 5 | 21 |
| `init-prelude` / **`Lean.Syntax`** | 2 | 7 | 26 |
| `nest_through_mutual` / **`A`/`B`** | 1 | 5 | 19 |
| `nest_mutual_both` / **`A`/`B`** | 2 | 7 | 28 |
| `nest_through_nested` / **`T`** | 2 | 6 | 23 |
| `nest_cycle_group` / **`U`** | 2 | 6 | 23 |
| `nest_cycle_group` / **`V`** | 3 | 7 | 30 |
| `nest_mutual_cycle` / **`P`/`Q`** | 3 | 10 | 37 |
| `nest_mutual_cycle` / **`R.{w}`/`S.{w}`** | 1 | 6 | 21 |
| `nest_family_edges` / **`A1`/`A2`/`A3`** | 2 | 9 | 34 |
| `nest_family_edges` / **`X`** | 2 | 6 | 23 |
| `nest_mutual_index` / **`MA`/`MB`** | 2 | 9 | 32 |
| `funext_binder` / `HTree` | 1 | 4 | 15 |
| `funext_binder` / `RTree` | 1 | 3 | 13 |
| `funext_binder` / `OTree` | 2 | 3 | 19 |
| `funext_binder` / `H2` | 1 | 4 | 15 |
| `funext_binder` / `H3` | 1 | 4 | 15 |
| `nest_binder_cross` / `Tr` | 1 | 4 | 15 |
| `nest_binder_cross` / `DTel` | 1 | 3 | 13 |
| `nest_binder_cross` / `IdxB` | 1 | 3 | 13 |
| `nest_binder_cross` / **`MutB`/`MutC`** | 2 | 5 | 24 |
| `nest_binder_cross` / **`CycB`** | 2 | 5 | 21 |
| `nest_sorts` / `PTree` | 1 | 3 | 13 |
| `nest_sorts` / `STree.{u}` | 1 | 3 | 13 |
| `nest_odd_shapes` / `EmpT` | 1 | 1 | 11 |
| `nest_odd_shapes` / `ImpT` | 1 | 2 | 12 |
| `nest_odd_shapes` / `LetT` | 2 | 5 | 20 |
| `nest_odd_shapes` / `FunP f` | 1 | 4 | 13 |
| `nest_odd_shapes` / `Deep3` | 3 | 7 | 29 |
| `nest_odd_shapes` / **`EvT`/`EvU`** | 2 | 8 | 29 |
| `decline_no_eq` / `Tree` | 1 | 4 | 15 + 1 spliced |

And the plain mutual blocks, at `2 + 2r + 2c`:

| fixture / declaration | members `r` | ctors `c` | declarations |
| --- | --- | --- | --- |
| `mutual_shapes` / `A`/`B`/`C` | 3 | 6 | 20 |
| `mutual_shapes` / `PA`/`PB`/`PC` | 3 | 5 | 18 |
| `mutual_shapes` / `UA`/`UB`/`UC` | 3 | 4 | 16 |
| `mutual_index` / `T0`/`T1`/`T2` | 3 | 4 | 16 |
| `mutual_index` / `MA`/`MB`/`MC` | 3 | 6 | 20 |
| `mutual_index` / `DA`/`DB` | 2 | 4 | 14 |
| `mutual_index` / `SA`/`SB`/`SC` | 3 | 5 | 18 |
| `mutual_index` / `VA`/`VB` | 2 | 3 | 12 |
| `mutual_prop` / `Even`/`Odd` | 2 | 3 | 12 |
| `mutual_prop` / `M0`/`M1`/`M2` | 3 | 4 | 16 |
| `mutual_prop` / `Sa`/`Sb` | 2 | 3 | 12 |
| `mutual_nonrec` / `OA`/`OB`/`OC` | 3 | 5 | 18 |
| `mutual_nonrec` / `EA`/`EB`/`EC` | 3 | 3 | 14 |
| `mutual_nonrec` / `Ka`/`Kb` | 2 | 2 | 10 |
| `mutual_odd_shapes` / `LA`/`LB`/`LC` | 3 | 4 | 16 |
| `mutual_odd_shapes` / `IA`/`IB`/`IC` | 3 | 4 | 16 |
| `mutual_odd_shapes` / `WA`/`WB` | 2 | 3 | 12 |
| `mutual_odd_shapes` / `QA`/`QB` | 2 | 3 | 12 |
| `mutual_odd_shapes` / `FA`/`FB` | 2 | 3 | 12 |
| `mutual_keying` / `GA`/`GB` | 2 | 3 | 12 |
| `mutual_keying` / `KA`/`KB` | — | — | declined, name taken |
| `nest_family_edges` / `C`/`D` | 2 | 4 | 14 |

`nest_family_edges`'s `C`/`D` is the one that was already in the tree: it is the
mutually recursive **pair of containers** `X` nests through, and it acquired a
model of its own without being written for one.

**And every row of the first table has a second model now** (§1.7), because a
nested declaration's model is itself a mutual block: `2 + 2n + 2c′` for the
`n = r + m` members of the specialised block and its `c′` constructors. `Tree`'s
block is two members and four constructors, so `Tree._model.0` is **14**;
`BTree`'s is three and six, so `BTree._model.0` is **20**. Across
`modelgen/tests` that is **80 further models**, 1,262 declarations, 8 to 32
each, and
they are not tabulated here because `modelgen/Test.lean` pins every one of them
by name beside the layer-1 count it belongs to — which is the place a count
should be pinned and the place a drift is caught.

The first eight nested rows are the eight `mini/src/nested_ev.rs` covers, and the counts are
**identical** to the ones `mini/tests/nested.rs` pins for it.

**The four rows with a `+ n spliced`** are the two files whose input lacks a
prelude constant the proofs need (§1.5), and the split is deliberate: the model
proper is the same size as `funext_binder`'s and `nested_shapes`' — the same
shapes with the constant already in the file — and what is added is Lean's own
declaration and nothing about the nested type. `HTree` pays for the quotient
(one kernel declaration, four export records), `Quot.sound` and its `funext`;
`RTree` and `OTree` come after it in the same file and pay for a `funext`
alone.

## 2.1 Equivalence with the Rust generator, and what it does and does not say

Over those eight, `nested_ev::iso`'s `Iso::decls` and `modelgen`'s output name
**the same 190 declarations** — block members, their constructors, and every
`_model` definition and theorem — diffed as sorted sets and identical. On top
of that, §4's statement oracle says the two are *stating the same thing*: both
are compared, syntactically, against the rule the installed `T.rec_k` carries,
which is one object and not two.

What is **not** claimed is that the proof *terms* agree. Both are checked — by
`kernel::add` there and by `Environment.addDeclCore` here — and a proof is not
part of the contract. The output is likewise **not** byte-comparable to the
input: any file with a model is re-interned whole (§3). A file with nothing to
splice is byte-identical, and that was measured over 73 of them.

---

# 3. Why the whole output is re-interned

`nanoda`'s parser — which `mini` uses — rejects a name, level or expression
back-reference whose index is not the current count
(`vendor/nanoda_lib-upstream/src/parser.rs`'s `assert_ie`). So a model **cannot**
be spliced into an existing file with fresh high indices; the whole file is
re-interned when anything is added.

The *reader* is deliberately more permissive than that: `lean4export` does not
promise continuity, and `vendor/arena-tests/good/sparse-name-index.ndjson` and
`level-index-out-of-order.ndjson` are the fixtures that say so. A file with no
nested inductive is copied **byte for byte** rather than re-serialised, so the
filter is exactly the identity where it has nothing to do.

## 3.1 Why the writer is ours and not `lean4export`'s

`lean4export` writes the same format from a `Lean.Environment`; this repository
writes it from parsed records (`Modelgen/Format.lean`). That is a duplicated
format definition and the question of collapsing it is a fair one, so here is
the answer and the reason.

**Reuse is mechanically possible.** `lean4export` exposes a `lean_lib Export`,
its pinned revision is on this repository's toolchain, and its writer *already
streams* — `IO.println` per line, no accumulation — so the memory failure
`MONOMORPH.md` §9.5 records was ours alone. (It prints to stdout with no handle
parameter, so a library user would have to redirect the process's stdout, but
that is a wart and not an obstacle.)

**There are two proposals here and they have different answers.** Writing from
an `Environment` is a fact about `lean4export`'s *driver* — `dumpConstant`,
which resolves a name against `env` and reads a `ConstantInfo`'s fields — and
not about its *emitters*: `getIdx`, `dumpName`, `dumpLevel` and `dumpExprAux`
take a `Name`, a `Level` and an `Expr` and are told nothing else about where
they came from. So:

* **(a) Reuse the driver.** Hand `dumpConstant` an `Environment` and let it
  write the file. **This is refuted, and the three reasons below are its
  refutation** — every one of them is about what the driver can see and in what
  order, and none of them touches (b).
* **(b) Reuse the emitters.** Lift `getIdx`, `dumpName`, `dumpLevel` and
  `dumpExprAux`, and drive them from our own record stream. **Nothing below
  refutes this.** It is a code-duplication question with no correctness or
  performance content, and it is answered on its own terms further down.

### Why not (a)

Three reasons, all about what is being written and not about the format.

1. **Byte-identity would go.** The claim above — a file with nothing to change
   comes back byte-identical, measured over 73 — rests on re-interning the
   *parsed* records in the input's own order. `lean4export` chooses its own
   order (`dumpDeps`, depth-first from a constant list), skips `unsafe`
   declarations unless asked, drops `mdata` unless asked, and reconstructs
   `numNested`, `isRec`, `isReflexive`, `hints` and `all` from what Lean derived
   rather than from what the file said. Where Lean's answer differs from the
   file's the round trip stops being the identity — `monomorph`'s `recRegen`
   counts 2,027 such recursors on Mathlib — and every back-reference index in
   the file shifts regardless. **This is the strongest of the three**, because
   it costs a property that is measured and relied on rather than a case that
   might not arise.
2. **Mode B has no environment.** `monomorph --mono-recursors` renames recursors
   to `…._elim.⟨w⟩`, which no kernel will accept as a recursor at all. It is a
   pure post-pass over records. Writing it requires a record writer, so (a) buys
   one of two writers rather than none — and the writer it does not buy is
   exactly the record-driven one (b) proposes.
3. **The output is not what the environment holds.** Both tools replay into an
   `Environment` — that is why `inferProjType` works — but they emit *records*,
   and the two are deliberately allowed to differ. A declaration the replay
   rejects is reported and still written (`monomorph`'s `rejected`, §4.1's
   oracle; `Mono.lean`'s emission loop pushes the declaration on both arms);
   `dumpConstant` panics on a name the environment does not have, so under (a)
   that declaration is not written at all. Worse, `MONOMORPH.md` §9.7 measures
   the environment **silently losing** declarations on Mathlib — 1,726
   `AsyncConsts.add` panics over 767 name pairs — so (a) would inherit exactly
   the hazard that document names as the thing to be careful about.

### What (b) would buy, and why it is not taken

The writer is **211 lines of code** in `Modelgen/Format.lean`: 6 for `Writer`,
**93** for the name, level and expression emitters, 78 for the six declaration
emitters, 31 for `Export.stream` and its two consumers. Only the 93 are in scope
for (b) — the declaration emitters read `EDecl`, `ECtor`, `ERec` and `EIndType`
where `lean4export`'s read `ConstantInfo`, `InductiveVal` and `RecursorVal`, and
rewriting one into the other is new code and not lifted code. So (b) collapses
the format definition for the **three simplest record kinds** and leaves it
hand-written for the **six with the most fields**, which is where a key-order
mistake is likeliest.

And the 93 are not lifted as they stand. Three edits come first, and after them
what remains of the original is the shape of three JSON objects:

* `dumpExprAux`'s `natVal` and `strVal` arms call `dumpNatDeps` and
  `dumpStrDeps`, which look `Nat`, `Char.ofNat` and `String.ofList` up in the
  environment and emit **their declarations** in the middle of an expression.
  Driven from records that is precisely wrong: it splices environment-derived
  declarations into a file whose declaration order is the input's.
* `getIdx` calls `IO.println`, so the monad is `ReaderT Context (StateT State
  IO)` and `Context` carries an `Environment` these functions otherwise never
  read. `Writer` is a pure `Writer × Nat`, which is what lets `Export.stream` be
  polymorphic in `m` and `Export.render` be a `StateM String`. Taking `getIdx`
  unchanged makes `render` an `IO` action and gives up the one-fold-two-consumers
  property that is what keeps `render` and `writeTo` byte-identical.
* `dumpExpr` strips `mdata` by rebuilding each expression through `removeMData`,
  which needs a 21-line memo (`noMDataExprs`) to be affordable. `Writer.expr`
  strips it at the point of interning — one arm, no rebuild — so that memo comes
  with a cost we do not currently pay.

**Its dedup is ours.** `visitedNames`, `visitedLevels` and `visitedExprs` are
`HashMap Name/Level/Expr Nat` under Lean's own `BEq` and `Hashable`, indexed by
`m.size`, seeded `.anonymous ↦ 0` and `.zero ↦ 0` — the same three tables as
`Writer`, key for key. `noMDataExprs` is the only structure it has that we lack,
and the point above is that it exists to pay for a design we do not have. This
is also **not** the dedup `MONOMORPH.md` §9.8 measures at 2.26×: that is
*in-memory* sharing lost during the rewrite, where the writer's re-interning is
what already brings the output back to 3.2 % larger than the input on 15.8 %
more declarations. `lean4export` has nothing to add to either.

The one difference worth having is presizing — `visitedExprs` is created at
`emptyWithCapacity 10000000` where `Writer.exprs` starts at 4096. That is a
one-line change to our own code, it needs no reuse, and it is unmeasured.

So: **keep the writer, and the reason is (a)'s three, not a general objection to
sharing code.** What was genuinely missing from it was streaming, and that is
`Export.stream` plus its two consumers. The duplication that remains is the
format itself, and it is held in agreement by measurement rather than by
construction: `monotest` checks that `Export.writeTo`, `Export.render` and the
input file all agree byte for byte on a real `lean4export` output, which is the
property that would break first if `lean4export` changed the format under us.

---

# 4. The oracles

Four, and each has an occupant the other three would pass. `modelgen --check-recursors`
runs the last two on every file.

1. **The kernel**, on every generated declaration.
2. **The counts**, pinned in `modelgen/Test.lean` against the same table
   `mini/tests/nested.rs` pins.
3. **The statements** (§1.1), rebuilt from the rule the installed `T.rec_k`
   carries, reading the constructor's field telescope off the recursor's *own*
   major type rather than off the plan. Well-typedness is not the claim: a
   generator that stated the rule of the wrong member, or a minor applied to
   its fields in the wrong order, satisfies oracle 1.

   > **This oracle is weaker for a plain mutual block, and the number does not
   > say so on its own.** A nested model's recursors are read off the
   > *specialised* block's, which Lean minted from a genuinely different
   > inductive, so comparing them against the export's own is a real
   > comparison. A plain mutual block has no second inductive (§1.6), so its
   > recursors and ι rules are the export's own restored, and the **recursor
   > type** half of this check is true by construction. The **ι** half is not:
   > `Modelgen.checkModel` rebuilds each statement through its own telescope
   > walk — opening the recursor's binders, reading the index vector off the
   > major's inferred type — where `Modelgen.mutualIso` builds it through a
   > different one, and a key filed under the wrong constructor, a level list
   > off by a motive universe or a rule count that does not match the
   > recursor's is caught there. What carries the construction is oracle 1:
   > `T._model.rec_k` is checked *at the export's own declared type*, and each
   > ι theorem is checked at the export's own rule with `Eq.refl` as its proof.
4. **The export's recursors against Lean's own.** Lean's kernel performs the
   nested construction itself — given `Tree`'s `inductDecl` it generates *both*
   `Tree.rec` and `Tree.rec_1`, at the export's shapes — so replaying the input
   already compares every recursor in the file against Lean's. Over the whole
   157-file corpus, **474 recursors, and the only five files that differ are in
   `vendor/arena-tests/bad/`**: `nat-rec-rules`, `level-imax-leq`,
   `nat-rec-k-lie`, `rec-k-lie` and `130_misnamed_rec_user`, each named for the
   lie it tells. This is `mini/tests/mutual.rs`'s
   `the_generated_recursors_are_the_ones_lean_exports` for nothing, over the
   corpus rather than the fixtures.

Measured over every `.ndjson` in the tree — `vendor/arena-tests` (157),
`mini/tests/fixtures` (42) and `modelgen/tests` (32): **231 files, 0 failures,
203 models, 1,399 statements compared with 0 differing, 1,108 recursors of which
10 differ and all 10 are in the five `bad/` files named above.** Twenty `bad/`
files stop replaying — Lean's kernel will not load a
deliberately ill-formed *inductive* even with checking off, because the
inductive elaboration is not skippable — and are passed through byte for byte.
**186 of the 230 come back byte-identical**: 155 of the 157 corpus files and
31 of the 42 in `mini/tests/fixtures`.

**§1.6 and §1.7 are what moved those numbers, and neither moved anything in the
corpus.** Three sweeps of the whole tree with the same harness:

| | files | models | ι statements | recursors | byte-identical |
| --- | ---: | ---: | ---: | ---: | ---: |
| before §1.6 | 224 | 78 | 552 | 1,006 | 197 |
| §1.6, the mutual construction | 230 | 117 | 809 | 1,074 | 186 |
| §1.7, composed | 231 | **203** | **1,399** | **1,108** | **186** |

**No file lost a model and no decline was added at either step.** The eleven
files that stopped being byte-identical at §1.6 are exactly
`mini/tests/fixtures`' mutual fixtures — the ten `mutual_*.ndjson` and
`nested_model.ndjson`, which is that encoding written out by hand and so
contains a mutual block of its own. **§1.7 took the count back to the same
186**, because the five nested fixtures it would otherwise have moved were
regenerated with it (§1.7); the intermediate sweep, before they were, read 181
byte-identical and 205 models, and the five files it named were exactly the
five that were then regenerated.

`vendor/arena-tests` is **155/157 across all three**, because it has **0 plain
mutual blocks**: a census over all 157 files counting `induct` records with
more than one member and `numNested = 0` returns nothing. So §1.5's `bad/`
fidelity measurement and the corpus acceptance run below are untouched by
either axis rather than merely re-run under them.

**67 → 78 and 484 → 552 is §5.1's lambda repair**, all of it in
`nest_fam_arg.lean`, and that is the *whole* of its effect on this tree:
running the binary over all 224 files before and after the change and comparing
the outputs byte for byte, **223 are identical and the one that differs is
`nest_fam_arg`**. `init-prelude`'s output is among the 223.

Three of those numbers moved at `6ae6515`, which recommitted
`mini/tests/fixtures`' five nested exports **already filtered**: on an
already-filtered file this tool declines by name, so the tree fell to **51
models and 383 statements** while the recursor total *rose* to 920 — a spliced
model's own recursors are replayed and checked too. `modelgen/tests` now
carries the unfiltered export of each of the five
(`modelgen/tests/export.sh`, `MODELGEN_FILTER=0`), which restored 61 and 450,
and 962 is 920 plus the raw copies' 42.

**61 → 65 and 450 → 473 is the prelude splice** (§1.5), which turned four
declines into models: `decline_no_eq`'s `Tree`, which lacked `Eq`, and
`infinitary`'s `HTree`/`RTree`/`OTree`, which lacked `funext`. Those four are
the *only* declarations in the tree whose outcome changed, and it is measured
rather than reasoned: filtering all 221 files of the tree as it then was with
the binary before and after and diffing the outputs, **two files differ and
they are those two**. The
decline list loses `nested model without funext` (three occurrences) and
`nested model without Eq` (one) and gains nothing; what is left is eleven
`nested model name taken` — every one of them an already-filtered input — and
the one `nested model shape:` in `bad/nested-unused-param` that §5.4 names.

Acceptance is `nanoda_bin` — the same parser `mini` uses — on the filtered
export. It accepts every file this tool wrote a model into, and the negative
control fires: give `Tree._model.iota_0_1` the *statement* of `iota_0_0` and it
stops at `assert_def_eq: not definitionally equal`. That includes the two files
whose model carries a spliced prelude (§1.5): `infinitary` — 214 declarations,
among them the four `{"quot": …}` records this tool wrote and the `Quot.sound`
it derived `funext` from — and `decline_no_eq`, 38 declarations over an `Eq`
the input did not have. Filtered, the whole `vendor/arena-tests` corpus still
gives `152 matched, 0 mismatched, 2 declined`, the same as unfiltered.

**Six files it does not accept, and all six are the same upstream
limitation.** `mini/tests/fixtures`' `mutual_index_sorts`,
`mutual_index_telescopes`, `mutual_one_recursive` and `mutual_prop_even_odd`,
and `modelgen/tests`' `mutual_nonrec`, make `nanoda_bin` panic at
`checker/src/inductive.rs:30`. **The panic fires on the input, before this tool
has written anything** — measured for each of the five, input and output side
by side — so it is not a property of a model. (It *used* to be true that
`modelgen`'s output on the four was byte-identical to the input, because there
was no model in any of them. Since §1.6 there is one in each, and the sentence
that said so has been corrected here rather than appended to.)

The line is `assert_eq!(ind.is_recursive, is_recursive)`, and the reason is
measured rather than guessed: upstream recomputes `isRec` **per member**, by
scanning that member's constructors for a *binder type* mentioning any name in
the block, while Lean sets it for the **whole block**. Each of them has at least
one member whose constructors mention no block member in a binder type —
`mutual_one_recursive`'s `OB`, `mutual_prop_even_odd`'s `Ka`,
`mutual_index_sorts`' `HB`, `mutual_index_telescopes`' `EB`, and
`mutual_nonrec`'s `OB`, `EB`, `EC` and `Ka` — so the export says `true` and the
recomputation says `false`.

`mutual_nonrec.lean` exists to carry that shape and keep it out of the five
mutual fixtures beside it: `mutual_shapes`, `mutual_index`, `mutual_prop`,
`mutual_odd_shapes` and `mutual_keying` are all blocks every member of which
recurses, and `nanoda_bin` accepts every one of them filtered — 46 → 130, 71 →
196, 36 → 99, 60 → 167 and 24 → 43 declarations, and the same on
`nest_family_edges`. **The tag and the carrier this construction emits do not
add a case to the assert**: the tag is a single inductive no constructor of
which mentions it, so Lean and upstream both call it non-recursive, and the
carrier is a single inductive, where "per member" and "the whole block" are the
same question.

> **The sixth is this tool's output**, and a consumer needs to know it.
> `nest_odd_shapes.lean`'s `EmpT.mk : Emp EmpT → EmpT` nests into a container
> with **no constructors**, so the generated block has a member with no
> constructors, and upstream's recomputation calls that member non-recursive
> where Lean calls the block recursive — the *same* assert. Lean's own kernel
> accepts the model (that is oracle 1, and it ran), and `--check-recursors`
> compares its recursors against Lean's with 0 differing; it is only
> `nanoda_bin` that refuses to load it. So `modelgen` **can** emit a block that
> the upstream parser will not take, for a reason that is upstream's and not
> the model's. Every other file this tool writes a model into is accepted, and
> that was measured file by file over `modelgen/tests`.

It is `checker/`'s to fix and not this tool's, and it is recorded here because
the sentence above used to say "every one" and, over the whole tree rather than
the corpus, that is not true.

## 4.1 Speed

`MEASUREMENTS.md`'s table for the Rust generator, and the same work here:

| | Rust (`mini/tests/nested.rs`, test profile) | `modelgen` |
| --- | --- | --- |
| `nested_iota` (`Tree` + `BTree` + `PT`) | 10.3 + 38.0 + 26.5 s | **0.12 s** |
| `nested_deep` (`DTree`) | 91.1 s | **0.11 s** |
| `nested_shapes` (four declarations) | 10.4 + 2.8 + 89.3 + 16.6 s | **0.13 s** |
| all three, end to end | **284 s** (measured) | **0.35 s** |
| `init-prelude` (3.7 MB, 1777 declarations, `Lean.Syntax`) | cannot (see §5) | **0.41 s** |
| `nest_through_mutual` / `nest_mutual_both` | cannot (see §4.2) | **0.11 / 0.12 s** |
| `nest_through_nested` / `nest_cycle_group` | cannot (see §4.2) | **0.12 / 0.13 s** |
| `indexed_container` / `nest_index_cross` | cannot (see §4.2) | **0.08 / 0.08 s** |
| `funext_binder` (five declarations) | cannot (see §4.2) | **0.09 s** |
| `nest_binder_cross` / `nest_sorts` | cannot (see §4.2) | **0.09 / 0.08 s** |
| `nest_odd_shapes` (six declarations) | cannot (see §4.2) | **0.10 s** |
| `mutual_shapes` / `mutual_index` (§1.6) | `mutual_aux.rs`, not timed | **0.13 / 0.16 s** |
| `mutual_prop` / `mutual_nonrec` | `mutual_aux.rs`, not timed | **0.14 / 0.11 s** |
| `mutual_odd_shapes` / `mutual_keying` | `mutual_aux.rs`, not timed | **0.13 / 0.16 s** |

The six mutual fixtures are 20 models and one decline between them, and each
lands inside the
process-start noise. There is no Rust column for them because
`mini/src/mutual_aux.rs` runs inside `mini`'s pipeline and was never timed on
its own; the case for replacing it is duplication rather than speed (§7), which
is the one respect in which this arc is *not* `nested_ev.rs`'s.

The Rust figure is `cargo test --test nested
the_nested_isomorphism_is_generated_and_the_kernel_accepts_it`, which generates
and `kernel::add`s exactly these eight models: 284.12 s. `modelgen`'s figures
are whole-file — parse, replay every declaration, generate, kernel-check, run
both oracles — and include ~0.1 s of process start. **Roughly 800×**, and the
superlinearity is gone: `DTree`, the 91-second case, is not distinguishable
from the others here, and neither are the two family axes — a mutual block of
four members and a cyclic group of mimics both land inside the process-start
noise, and neither is an indexed container. Whole tree, 212 files with
`--check-recursors`: **28.9 s here**, against the **13.7 s** recorded for 208.
The difference is the machine and not the filter — three other seats were
saturating it — and the per-file figures above, measured the same afternoon,
are each *at or below* their recorded value. Process start is ~0.07 s of every
one of the 212.

**The prelude splice (§1.5) is free.** Whole tree, the 221 files it then had,
with
`--check-recursors`, the same binary with and without it, interleaved:
**31.4 / 32.3 s** against **32.9 s** — the splice is not distinguishable from
run-to-run noise, and neither are the four extra models. Per file, on the two
that splice and the two that measure the same shapes without splicing:
`infinitary` 0.10 s (0.08 s before), `decline_no_eq` 0.07 s (0.07 s),
`funext_binder` 0.10 s (0.09 s), `nest_binder_cross` 0.10 s (0.10 s) — which is
what one extra `Eq.rec` and a kernel check should cost.

**Neither §1.6 nor §1.7 is a per-file cost worth a column.** §1.6's six
fixtures are 20 models and land inside process start, above; §1.7 doubles the
model count of every nested fixture and the largest of them, `nest_fam_arg` at
24 models, is 0.17 s. The whole tree at 231 files with `--check-recursors` came
out at **31.7 s** against a 28.9 s recorded for 212, which is **not** a
comparison — two wall clocks from different sittings on a shared machine, and
this one had another seat's `modelgen` over Mathlib on the box.
`MEASUREMENTS.md`'s "counters against clocks" is the rule; the counters here are
that no file gained a decline, and that all 203 models are kernel-checked and
all 1,399 statements compared clean (§4).

---

# 4.2 Coverage, and where the edges are

Every axis the Rust path covers, `modelgen` covers, at the same fixture:
depth-1 recursive container (`Tree`), depth-1 non-recursive container
(`PTree`), depth 2 through the same container twice (`DTree`), depth 2 through
two different containers (`BTree`), two nested positions in one constructor
(`nested_shapes`' `BTree`), a declaration with parameters (`PT α`), and a
container that is a structure (`Box`).

**The `List N` decoy is discriminated.** `nested_shapes` carries `listOfN :
List N` beside `BTree`'s nested `List BTree` — `Lean.Syntax.ident`'s shape — and
a treatment that specialised *every* container application would produce a
block with a member Lean does not have. Two things catch it, and both are
measured rather than argued: the declaration counts (`nested_shapes`' `BTree`
is 14 with **one** mimic, not 24 with two) and the statement oracle, which
compares one generated `rec_k` per block member against the export's own and
would have a spare.

Beyond the Rust path, and new:

* **Universe-polymorphic declarations.** `T._model.*` carries `T`'s own level
  parameters and a recursor carries its motive universe in front of them; the
  statement oracle compares those lists against the export's, so this is not a
  claim about the fixture but about `T.rec_k`'s own type. `poly_nested.lean`:
  `PTree.{u}` at 15 declarations and `QTree.{u,v}` — two parameters at two
  universes, landing at `Type (max u v)`, nesting two deep — at 22, and
  `nanoda` accepts the filtered export. The fixture is arranged so that a
  generator writing a container's *declared* level parameter where the
  occurrence's instantiation belongs cannot pass: `List` and `Box` declare `w`
  and are used at `u` and at `max u v`, so the wrong choice leaves a free
  universe variable the kernel rejects.
* **Universe-polymorphic containers**, which is what `Lean.Syntax` needs.
  `nested_ev.rs`'s `rec_levels` puts the container's *declared* level parameter
  on `C.rec`, as `Level::Param`; the occurrence's own instantiation is what
  belongs there. For every fixture the Rust covers the containers are
  monomorphic and the two coincide, so that guard had no witness in the tree —
  but `Lean.Syntax` nests into `Array.{0} Syntax` over `List.{0} Syntax`, and
  there the declared parameter is a free universe variable in a declaration
  with no level parameters. Measured on a scratch fixture with a polymorphic
  `List`: `nested_ev::iso` returns `Err(nested model shape)`, and `modelgen`
  writes the 15 declarations and `nanoda` accepts them. `modelgen` uses
  `u :: cls` — the occurrence's levels.
* **Dependent constructor fields**, where the dependency is on a field the
  fold does not move — which is every dependency Lean supports (§5.2).
  `dependent_fields.lean`: both orders, and `KTree` for a dependency inside
  the *container's* constructor.
* **Infinitary constructors at the root**, `FTree.branch : (N → FTree) →
  FTree` and `Fn.mk : (N → α) → Fn α` reached through a mimic. Lean gives such
  a field an induction hypothesis `∀ x⃗, motiveₘ (f x⃗)`, so a minor's
  hypothesis vector has an entry for a field that sits at no member;
  `infinitary.lean`'s `ZTree` is the fixture that pins the vector's indexing,
  and it was measured to decline under the indexing that came before.
* **A constructor field the block holds at a *mimic*, under a binder** —
  `HTree.node : (N → List HTree) → HTree`. This is the one shape whose
  obstruction was the *proof* rather than the statement, and closing it is the
  one place this module needs a constant that no §1 statement mentions — the
  input's `funext` if it has one, and a derived `T._model.funext` if it does not
  (§1.5). `funext_binder.lean` is the first and `infinitary.lean` the second. `nest_binder_cross.lean` crosses it with the rest, and the **cycle**
  crossing did not come for free: `packFamMinor` and `retractFamilyValue` are a
  second copy of the one-at-a-time path and were measured refusing `CycB` until
  they were taught the same telescope. Also there: a *dependent* two-binder
  telescope (`DTel`), the binder at an indexed container (`IdxB`), and the
  binder inside a mutual block (`MutB`/`MutC`).
* **The odd corners, swept for rather than waited on.**
  `nest_odd_shapes.lean` is what §5.1's coverage claim is worth — and §5.1
  records what it could not reach: a container with
  **no constructors** (`EmpT`), one with an **implicit** binder (`ImpT`), one
  with a **`let` in a constructor field's type** (`LetT` — Lean accepts it, and
  the member a field sits at is then not the head of the expression as written,
  which is why every such test reads through `Gen.zetaHead`; it was measured
  refusing twice before that), a declaration **parameter that is a function
  type** (`FunP f`), **depth three** with the binder at the deepest level
  (`Deep3`), and `EvT`/`EvU` — a mutual block with a parameter *and* an index
  nesting through an indexed container *and* through `List`, one of them under
  a binder, which is every axis this tool has at once. 11, 12, 20, 13, 29 and
  29 declarations. `EmpT`'s output is the one `nanoda_bin` will not load, for
  upstream's reason and not the model's (§4).
* **The sort the block lands in.** `nest_sorts.lean`'s `PTree : Prop` nests
  `PL PTree` at `PL (α : Prop) : Prop`, and a block that eliminates only into
  `Prop` has **no motive universe at all** — `PTree.rec` carries the
  declaration's own level parameters and nothing in front of them, and so does
  `PL.rec`. Every level list this module writes for a recursor is therefore
  read off the recursor ([`Modelgen.Gen.recLs`], [`Modelgen.Gen.contRecAt`])
  rather than assumed, and before it was, this shape made the tool raise
  `incorrect number of universe levels PL.rec` — an *uncaught exception* rather
  than a decline, which is the worse of the two failures. `Eq` is the atom that
  says the guard is not "the sort is `Prop`": `Eq` is `Prop`-valued and *does*
  support large elimination, so it has a motive universe, and the distinction
  is read off `levelParams`. `STree.{u}` beside it nests through a container
  polymorphic over `Sort` rather than `Type`.
* **A declaration with indices.** `ITree : N → Type` nesting `List (ITree
  N.z)`: `ITree.rec` has `numIndices = 1` while the mimic's motive has none, so
  a block recursor here has a **different index arity per member**, and the
  motive vectors `unpack` and the section are built over each member's own
  index telescope. Every index vector in the model is *read off a type in
  hand* — `Gen.idxOf` — and never rebuilt, which is what keeps this from being
  more de Bruijn arithmetic. `indexed_decl.lean` is three declarations: `I2`
  carries two indices at reversed values so an index *order* is visible, and
  `I3.node : I3 N.z → List (I3 (N.s N.z)) → I3 (N.s (N.s N.z))` makes the
  recursive field's index, the occurrence's and the result's all differ, so
  reading one where another belongs is caught.
* **A *container* with indices**, which is a different matter and used to be
  §5.1's first row. `VTree.node : Vec VTree (N.s N.z) → VTree` nests into a
  container the declaration does not share an index with: the occurrence is
  `Vec VTree._model.self`, which is **not a type**, and `VTree.rec_1`'s motive
  is `(a : N) → Vec VTree a → Sort u`. So the container's index telescope sits
  between `p⃗` and the argument of `pack_i`, `unpack_i`, both round trips and
  `congrPack_i` — the one §1 change this axis cost, and empty for every
  container without indices, so nothing a consumer could already key has moved.
  `indexed_container.lean` is three declarations: `VTree` is the shape,
  `WTree` nests into the *same* container at two different indices and gets
  **one** mimic (the occurrence is the container at its *parameters*), and
  `UTree` at `Tab α : N → N → Type` is the one that pins the telescope rather
  than the fact of one — two indices at differing values, and a container
  recursion that moves them one at a time. 15, 17 and 16 declarations.
  `nest_index_cross.lean` crosses it with the three axes already closed and is
  below.
* **`Lean.Syntax` itself** — three block members, four constructors, three
  recursors, seven ι rules, 26 declarations, `nanoda`-accepted.
* **A container argument that is a lambda**, which is `Lean.Json` and
  `Lean.PrefixTreeNode` and was §5.1's last gap. `nest_fam_arg.lean` is that
  axis swept in both directions: twelve declarations, 73 statements compared
  against the installed recursors' own rules with 0 differing, 36 recursors
  compared against Lean's with 0 differing, `nanoda`-accepted at 364
  declarations. The container's family takes one argument (`RB`) and two
  (`RB2`); the lambda is constant and applied (`fun k => Vec Idx k`); the
  occurrence sits in the family's value and in its **key**; the lambda body
  holds a further container (`fun _ => L Deep`) and a `let`; the declaration is
  parameterised (`PTP`, which is `Lean.PrefixTreeNode` as Lean declares it) and
  indexed (`Ix`); and `Flat` nests at a container with **no recursive field of
  its own**, whose failure before the fix was at an ι rule and not at `unpack`.
  The source's table says which mutation of the repair each one kills, and the
  file's twelfth declaration is the control that was a model before the fix.
* **Nesting inside a mutual block**, and **nesting through a container that is
  itself nested** — the two family-shaped axes, each below.

## Nesting inside a mutual block, and the family it needs

Lean accepts and exports it, and `mini/src/nested.rs` refuses it outright —
"`{root}` is both a mutual block and nested; mini takes one or the other".
Nothing in the 205-file corpus has the shape, so it was neither covered nor
known to decline. **`modelgen` now writes it.**

`nest_mutual_both.lean` is the fixture that could answer the design question,
because `nest_through_mutual.lean` cannot: with only `A` nesting, a single
carrier and a per-member carrier family are the same object. Here `A` nests at
`List B` and `B` at `Box A`, and **Lean's own export is the measurement**:

| | |
| --- | --- |
| block members | `A`, `B`, and the mimics `List B`, `Box A` |
| `numNested` | **2, on every real member** — the mimic count, not a per-member figure |
| `all` | `[A, B]` — the real members only; the mimics are not in it |
| recursors | `A.rec`, `B.rec`, `A.rec_1` (`List B`), `A.rec_2` (`Box A`) |
| motives / minors | **4 and 7 on every one of the four** — one shared vector |

So the answer is **a family, not a carrier**: a real member's recursor lives in
that member's own namespace and a mimic's in the first member's, numbered from
1, and the motive order is `all` first and mimics after, in discovery order.
Two consequences, both now in §1:

* **One carrier per real member**, `A._model.self` and `B._model.self`. A
  consumer keys `⟦A⟧` and `⟦B⟧` separately and a single carrier could stand for
  only one of them.
* **`T.rec_k`'s index is not the block index once the block is mutual**, so §1
  states the export's name for block index `k` as a formula instead of as the
  identity. That is the §1 change this axis cost.

`A._model.rec_0 … rec_3` model `A.rec`, `B.rec`, `A.rec_1`, `A.rec_2`; the
statement oracle compares all four against the installed recursors' own rules,
and 19 and 28 declarations come out of the two fixtures, `nanoda`-accepted.
The block is specialised as **one** block — four members, one shared motive
vector — and not as two blocks glued.

## Nesting through a container that is itself nested, and the sentence it refutes

`mini/src/nested_ev.rs`'s header says the emission order is free: "nesting
strictly decreases, so this is a topological order and a cycle cannot arise".
**That is false**, and it is false in two ways.

* **A backward edge without a cycle.** Mimics are discovered breadth first, so
  a mimic may mention one discovered before it. Descending index is then not a
  topological order at all.
* **A genuine cycle.** `T` nests into `Tree T`; `Tree`'s own `node` field is
  `List (Tree T)`; *that* copy's `cons` head is `Tree T` again. So `pack₀`
  calls `pack₁`, `pack₁` calls `pack₀`, and **no emission order exists**. The
  Rust would meet it as an unbound constant.

The fix is not an ordering. It is that the mutually recursive `pack`s **are not
two recursions**: they are the two components of one, and Lean already
generated the recursors that perform it — `Tree.rec` and `Tree.rec_1`, over a
single vector of two motives and four minors. So `modelgen` groups the mimics
into strongly connected components, orders the *condensation*, and emits a
group of more than one as one simultaneous recursion:

| | |
| --- | --- |
| `pack_i` for `i` in the group | component `j` of the container family's recursion, at one shared motive (`fun _ => B_{r+i}`) and minor vector — so `pack₀` and `pack₁` never mention each other |
| `unpack_i` | unchanged; `unpack` never calls another `unpack` |
| `unpackPack_i` | the same family recursion at `Prop`; a field at a sibling gets the **sibling's own induction hypothesis**, which is its retraction up to proof irrelevance |
| `packUnpack_i` | unchanged; it already goes through the *block's* recursor, which does every member at once, so the whole group is simply live together |

Nothing in §1 moves: the names, the statements and the counts are what they
were, and the change is entirely in how the four are proved.

`nest_through_nested.lean` is the minimal cycle, 23 declarations for `T`.
`nest_cycle_group.lean` is the one that distinguishes the treatment from a
lucky coincidence, because a single two-element cycle cannot:

* `U.mk : List (Tree U) → U` puts a container that anchors **nothing** at
  mimic 0 — `List` is not nested, so its family has one member and cannot be
  the group's. The family has to be found from mimic **1**, and the
  mimic-to-family mapping is then the **transposition**: `pack_0` is
  `Tree.rec_1` and `pack_1` is `Tree.rec`. An implementation that assumed the
  group's first mimic anchors it, or that the mapping is the identity, is
  wrong here and right on `nest_through_nested`.
* `V.mk : Box (Tree V) → V` puts an ordinary mimic **outside** the cycle and
  depending on it, so the condensation is a real DAG: `pack_0` is an ordinary
  one-at-a-time `pack` that calls `pack_1`, and `pack_1`/`pack_2` are one
  recursion that has to be emitted first.

23 and 30 declarations, `nanoda`-accepted, every recursor and ι rule compared
against the installed recursors' own rules.

## The two family axes compose, and that is measured too

Nothing about either axis says it survives the other, and a treatment that
special-cased one would pass both fixtures above and fail this.
`nest_mutual_cycle.lean` is the crossing:

* `P`/`Q` — a **mutual** block that nests **through a nested container**. Five
  block members (`P`, `Q`, `Tree Q`, `List P`, `List (Tree Q)`), five recursors
  `P.rec`, `Q.rec`, `P.rec_1`, `P.rec_2`, `P.rec_3` over one shared vector of
  five motives and ten minors, and a mimic graph whose condensation is a
  genuine DAG: `Tree Q` and `List (Tree Q)` are a cycle and one simultaneous
  recursion, `List P` is neither. **37 declarations.**
* `R.{w}`/`S.{w}` — the mutual axis crossed with a level parameter of the
  declaration's own, at a polymorphic container. **21 declarations.**

Both `nanoda`-accepted, both compared against the installed recursors' own
rules with 0 differing.

`nest_family_edges.lean` is the pair of edges a two-member fixture cannot
reach, and each is a claim in this section that would otherwise be untested:

* **A mutual block of three.** With two members, `A.rec_1` is equally "the
  first member's namespace" and "the previous member's". Here the mimic of
  `List A2` and the mimic of `Box A3` are named `A1.rec_1` and `A1.rec_2` —
  **always the first member**, whichever member the occurrence came from. Five
  block members, five recursors, nine minors, 34 declarations.
* **A cycle whose family is a mutually recursive *pair of containers*.**
  `X.mk : C X → X` with `mutual inductive C | c : D α → C α; inductive D | d :
  C α → D α end` cycles `C X` against `D X`, and the family that answers it has
  two real members and **no** nesting, where `Tree`'s has one real member and
  one nested occurrence. Both arms of `familyRecs` are therefore reached. 23
  declarations.

`nest_mutual_index.lean` crosses the mutual axis with the **declaration's own
indices**, which neither family fixture reaches — `nest_mutual_both` has no
index anywhere and `indexed_decl` is not mutual, so a treatment that read the
first member's index count for every member passes both. `MA : N → Type` and
`MB : N → N → Type` have index telescopes of *different lengths* and their two
mimics have none, so one motive vector carries three distinct arities; each
member has a recursive field whose index differs from its result's, and both
members nest. **32 declarations, and it needed no code**: the composition was
measured, not built.

`nest_index_cross.lean` crosses the **indexed container** with each of the
three, and unlike the two above it is not free — every index vector in the
model is read off a type in hand, and each crossing is a different type.

* `CTree` — the declaration's indices *and* the container's. `CTree.node :
  CTree N.z → Vec (CTree (N.s N.z)) (N.s N.z) → CTree (N.s (N.s N.z))` is
  `I3` with the container indexed too: the recursive field's index, the
  occurrence's parameter's, the mimic's own and the result's are four values
  and all differ. **15 declarations.**
* `PA`/`PB` — a mutual block whose members carry indices and nest through
  *different* indexed containers. Four members, three distinct index arities in
  one motive vector, two carriers, two indexed mimics. **29 declarations.**
* `XT` — the cycle of mimics, over an indexed family. `ITr α : N → Type` is
  itself nested over `Vec`, so `XT.mk : ITr XT N.z → XT` makes `ITr XT` and
  `Vec (ITr XT N.z)` mutually recursive and the recursion that answers them is
  `ITr.rec`/`ITr.rec_1`, **both indexed**. `Modelgen.familyFor` therefore reads
  a family member's occurrence off its motive's *last* binder with the index
  telescope stripped, rather than off the motive's first binder domain, which
  is the same object only when the family is unindexed. **21 declarations.**

All four `nanoda`-accepted, all compared against the installed recursors' own
rules with 0 differing.

## The plain mutual block, and the axes it has

§1.6's construction, and its coverage is its own rather than a corner of the
nested one's. **Every block below has three members wherever three members can
say something**, because two cannot distinguish an ordering from a permutation
of it and this encoding has three orderings to get right at once: which member
is which tag constructor, whose constructors come first in the flattened
`T._model.ctor_j`, and which ι theorem belongs to which recursor. **And the
constructor counts within a block are unequal**, because equal ones let a
generator that flattened the members wrongly still land every minor at a minor
of the right arity.

`mini/src/mutual_aux.rs`'s ten corpus fixtures were the specification. **All ten
shapes are modelled** — measured by running this binary over
`mini/tests/fixtures` directly — and `modelgen/tests` carries each axis again,
non-degenerately:

* **`mutual_shapes.lean`.** `A`/`B`/`C` is a three-way cycle at 2, 1 and 3
  constructors, the last of them **infinitary** (`C.cf : (N → A) → C`), so a
  minor's induction hypothesis is a function and the ι rule writes `fun n =>
  rec_0 … (f n)` at it. `PA`/`PB`/`PC` is two **parameters**, one used by each
  member and one not. `UA`/`UB`/`UC` is two **level parameters** at
  `Type (max u v)`. 20, 18 and 16 declarations.
* **`mutual_index.lean`**, which is where the tag stops being an enumeration.
  `T0`/`T1`/`T2` is one index each; `MA`/`MB`/`MC` is index telescopes of
  **different lengths in one block**, so `MB` contributes a nullary tag
  constructor beside two unary ones and `MB.rec` has no index where its
  siblings have one; `DA`/`DB` differs in the index **type** at the same sort,
  holding that axis apart from the sort of the index; `SA`/`SB`/`SC (α β :
  Type) : Type 1 → N → Prop` is the one shape in the tree where **`W` is not
  `Sort 1`** — a `Prop`-valued family indexed by a large type, where the cheap
  guess `max u (v+1)` gives 1 and the answer is 3 — and it crosses two
  parameters with two indices; `VA`/`VB (α : Type) : Pair α → Prop` has an index
  **type that mentions a parameter**. 16, 20, 14, 18 and 12.
* **`mutual_prop.lean`**, the two elimination questions. A block of several
  members has **no motive universe at all**, so every level list is the
  declaration's own — and the *auxiliary* inductive is one inductive and may
  have a motive universe where the block does not, so the level list handed to
  `T._model.aux.rec` is read off **that** recursor and not off the block's.
  `Even`/`Odd`, `M0`/`M1`/`M2` and `Sa`/`Sb`: 12, 16 and 12.
* **`mutual_nonrec.lean`**, a member that recurses into nothing, which is three
  things: only one member recursive (`OA`/`OB`/`OC`), a member with **no
  constructors at all** (`EA`/`EB`/`EC` — the tag then has a constructor no
  `aux` constructor mentions and `EB.rec` has no rules), and the **K-rule**
  shape (`Ka`/`Kb` — `Ka : Prop | mk : Ka` gets a K-rule when it stands alone;
  in a block it does not, and neither does the carrier, because the carrier
  always has the tag as an *index* and an indexed inductive is never K-like).
  18, 14 and 10. This is the file `nanoda_bin` will not load, for §4's upstream
  reason and on the input as much as on the output.
* **`mutual_odd_shapes.lean`, the sweep** — written by asking what else
  `mutual inductive` allows rather than by waiting for a failure, which is what
  `nest_odd_shapes.lean` is for the other construction. A **`let` in a
  constructor field's type** (`LA`), **implicit and strict-implicit** binders
  and a `Sort`-valued field (`IA`), a **dependent index telescope** where the
  second index's type mentions the first (`WA`/`WB`), an index whose type is a
  **parameter at a level parameter** so that `W` is `max 1 (u+1)` and not a
  numeral (`QA`/`QB`), and a declaration **parameter that is a function type**
  (`FA`/`FB`). 16, 16, 12, 12 and 12, and none of the five was a refusal.
* **`mutual_keying.lean`**, the name guard, at a name that is *not* under the
  namespace the model writes into: the model's namespace is the first member's
  (`KA._model`) but the carriers are one per member, so `KB._model.self` is a
  name the model wants and the file declares it — **after** the block, so a
  guard reading only the environment as it stands would emit a duplicate.
  `GA`/`GB` beside it is the atom saying the guard is not refusing everything.

All of them are compared against the installed recursors' own rules with 0
differing, and all but `mutual_nonrec` are `nanoda`-accepted.

## The two composed, and the axis that only composition has

§1.7 runs the second construction on the block the first one wrote, so **every
nested fixture above is also a mutual fixture** — 80 further models across
`modelgen/tests`, 1,262 declarations, every one of them checked by the kernel
and compared against the installed recursors' own rules with 0 differing. That is a wider input set for §1.6 than its own six files are, and
it is free: the blocks are Lean's own nested specialisations rather than
anything designed, so they carry shapes no fixture was written for — a member
with no constructors (`nest_odd_shapes`' `EmpT`, whose `Emp` mimic is empty),
mimics at containers polymorphic over `Sort` (`nest_sorts`' `STree`), index
telescopes of three distinct arities in one block (`nest_mutual_index`), and
the five-member blocks of `nest_mutual_cycle`.

**The one thing composition can reach that neither construction reaches
alone** is the *interaction*: layer 2's carriers are `def`s over the very block
member layer 1's carriers are `def`s over, so `R_k._model.self` and
`T._model.k._model.self` are two definitions of the same object by two routes,
and the kernel checks both.

It also reaches a **shape**, and that one did need code. `modelgen/tests/
compose_sorts.lean` is the axis: a specialised block whose members' sorts are
the same level written two ways, which an input `mutual` block cannot be
because Lean's elaborator forbids it. Four declarations — the one that
reproduces it, the two guesses that did not, and the control — and under a
mutation that compares levels syntactically exactly one of the four declines.
§5.1 is the finding and the five Mathlib declarations it came from.

---

# 5. What it declines

Every entry names the shape, **what Lean does with it**, and what this does.
Completeness is measured against Lean and not against the fixture set, so a
shape Lean accepts and this refuses is a *gap* and is marked one; a shape Lean
refuses too is a boundary and is marked that.

**§5.1 is empty again**, and this time the sentence is written with the account
of what it is worth beside it, because it was said once when it was not true.
The nested occurrence inside a lambda in a container argument — Mathlib's two
declines — is closed, and so is every shape a sweep over that axis could
reach. **A constant the input does not declare is not a decline** — §1.5
splices it — so what is left is a shape Lean refuses too, a name the input has
already taken, or a prelude constant the input declares at something other than
Lean's statement.

**Every one of these has a fixture that reaches it**, under `modelgen/tests/`,
built by `modelgen/tests/export.sh` with the repository's own exporter,
toolchain and `--#export` convention — except the five §5.2 and §5.3 name as
having none, and each says why. §4.2 lists the fixture that closed each row §5.1
used to have. `--check-recursors` runs on each, so Lean's own
recursors for these shapes are compared against the export's on every test run.

## 5.1 Gaps — shapes Lean supports and this does not

**Empty**, and the rest of this section is what that is worth, because it has
said "empty" twice before and been refuted both times — once by Mathlib within
the hour, and once by §1.7's composition on the same file.

**What was here, and what closing it took.** The nested occurrence inside a
lambda in a container argument: `RBNode α β`'s second parameter is a family, and
`Lean.Json.obj (kvPairs : RBNode String (fun _ => Json))` puts the recursion
inside the lambda that fills it. Specialising the container substitutes that
lambda into `RBNode.node`'s field `β k`, and because the substitution is `Expr`
surgery the block **stores the redex** `(fun _ => B₀) k`. Three readers then
answered a question about the lambda rather than about its reduct —
`Gen.memberOf` (which member?), `Gen.occIdx?` (which occurrence, at which
indices?) and `Gen.idxOf` (which index vector?) — and `Plan.spec`, which sweeps
a constructor type for occurrences, never entered the head of an application at
all, so a nested occurrence *inside* the lambda body got no mimic. The repair is
those four places and nothing else: `Modelgen.headNorm` (β and ζ at the head,
never δ) at each reader, and a descent into a non-constant head in `Plan.spec`.

Two secondary consequences fell out of the same reading and are fixed with it:
the dependent-field guard called a field a dependent one when the *redex*
mentioned an earlier moved field and its reduct did not, and the `funext`
trigger asked for `funext` for a redex that has no binder at all.

**Why it took Mathlib to find it, and what the sweep now is.** No file in
`vendor/arena-tests` and no designed fixture nested under a lambda at a
container argument, so 221 files and every axis of §4.2 passed over a shape two
real declarations have. The lesson was about the sweep: a sweep over *what
`inductive` allows* found six new shapes (`nest_odd_shapes.lean`) and could not
find this one, because this one is about how a container is **applied**.
`nest_fam_arg.lean` is now the sweep over *that* axis, twelve declarations, and
its own table says which mutation of the repair each one kills — the container's
family at one argument and at two, the lambda constant and the lambda applied,
the occurrence in the family's value and in its key, a container inside the
lambda and a `let` inside it, the declaration parameterised and the declaration
indexed, and the container with no recursive field of its own, whose failure
before the fix was at an ι rule and not at `unpack`. **Eleven of the twelve were
red on the commit before the fix and the twelfth is the control**, `OK`, which
was a model before and after.

The sweep found three shapes beside those and **Lean refuses all three**, so
they are §5.2 and not this section. The honest limit of the claim is that a
sweep is still a sweep: what is measured is that the axis Mathlib exposed has
been walked in both directions, that Mathlib's own 41 are 41, and that no shape
tried here is refused.

**The mutual construction (§1.6) does not put a second entry here either, and
this is the sweep that says so rather than the fixture set.** Every shape
`mutual inductive` allows that `inductive` does not is about the *block*: how
many members it has, whether they agree on indices, whether one of them
recurses, whether one of them is empty. §4.2's six mutual files walk that list —
three members, unequal constructor counts, unequal index telescopes, unequal
index types, indices at a large sort, an index type mentioning a parameter, a
dependent index telescope, an index at a level-polymorphic parameter, a `let`,
implicit binders, a `Sort`-valued field, a function-typed parameter, infinitary
fields, `Prop` with and without large elimination, the K-rule shape, a member
that recurses into nothing, a member with no constructors, two parameters, two
level parameters — and **not one of them is a refusal**.
`mini/src/mutual_aux.rs`'s own ten fixtures are modelled too, all ten, including
the two its `Reason` enum was written to refuse. What is left is §5.2's
boundaries: a block whose members land at different sorts or carry different
parameter counts, both of which Lean rejects at the kernel.

The same honest limit applies to it as to the paragraph above, and for the same
reason: a sweep over what a *declaration* may look like is not a sweep over the
environment it arrives in. Mathlib is the control, and there **all 10** plain
mutual blocks are modelled with 0 declines (§6).

**And composition (§1.7) found one that neither sweep could, which is the third
time this section has been corrected by an input rather than by a reading.**
Running §1.6's construction on the blocks §1's construction writes declined
**five of Mathlib's 41**: `Lean.PrefixTreeNode`, `Lean.PersistentHashMap.Node`,
`Lean.Doc.Block`, `Lean.Doc.Part` and `IO.AsyncList`, all at *a mutual block
whose members land at different sorts*. They do not. The sorts are the same
level written two ways — `(max u v)+1` beside `max (u+1) ((max u v)+1)` — because
a mimic's sort is the **container's** level expression instantiated at the
occurrence, and substituting `v := max u v` into the spelling `max (u+1) (v+1)`
does not collapse where substituting into `(max u v)+1` does. The comparison
reads `isLevelDefEq` now and the five are models.

**No fixture over what `inductive` declares could have found it**, and this is
sharper than §6.3's version of the same lesson: the shape is one Lean's
*elaborator* forbids — a source `mutual` whose members disagree does not compile
— and Lean's *kernel* writes, in the auxiliary block it builds for a nested
declaration. It is reachable only by running the second construction on the
first's output. `modelgen/tests/compose_sorts.lean` is it, written afterwards
and red under a mutation that puts `==` back; two of its four declarations are
the guesses that did **not** reproduce it, kept because the difference between
them is the whole content.

Everything else stands, and here is what stands behind it. Every
shape this section has ever listed now has a fixture under `modelgen/tests/`,
exported by Lean's own kernel, generating a model that the kernel accepted,
whose recursors and ι rules were compared against the installed ones with 0
differing, and whose filtered export `nanoda_bin` accepts: universe
polymorphism, universe-polymorphic containers, containers polymorphic over
`Sort`, a block that lands in `Prop` and has no motive universe, dependent
fields, indices on the declaration, indices on the **container**, infinitary
constructors at the root, a field at a mimic **under a binder**, nesting inside
a mutual block, nesting through a nested container, cycles of mimics, a
container with no constructors, a container with implicit binders, a `let` in a
constructor field's type, a parameter that is a function type, depth three, a
container argument that is a **lambda**, and the crossings of all of those.
§4.2 names each with its fixture and its count.

The claim is only worth what was swept for it, and `nest_odd_shapes.lean` is
that sweep written down: each of its six was found by asking what else Lean's
`inductive` allows rather than by a failure arriving, and **two of them were
refusals when they were first written**.

What `modelgen` declines is of exactly two kinds, and neither is a shape:

* **A name the input has already taken** — `nested model name taken`; and a
  prelude constant the input declares at something other than Lean's statement
  — `nested model: the input's N is not Lean's (…)`. A constant the input
  simply *lacks* is not on this list any more: §1.5 splices `Eq`, the quotient,
  `Quot.sound` and `funext`, and `nested model without Eq` and `nested model
  without funext` are gone.
* **Shapes Lean rejects too** — the rest of §5.2.

### The shape that was here before that one, and what closing it cost

`HTree.node : (N → List HTree) → HTree`: a constructor field the block holds at
a mimic *under a binder*. The obstruction was the proof and not the statement.
The block types the field `∀ x⃗, Bₘ ι⃗`, so `T._model.ctor_j` builds `fun x⃗ =>
pack (f x⃗)` and something downstream transports along `(fun x⃗ => pack (unpack
(f x⃗))) = f`. **No choice of `ctor_j` avoids it**: §1 fixes `ctor_j`'s type, so
its value is `B₀.c (h f)` for some `h`, and `h` must satisfy `h (fun x⃗ =>
unpack (g x⃗)) ≡ g` for the recursor's minor to typecheck at a *variable* `g`;
the only candidate is `fun k x⃗ => pack (k x⃗)`, and `pack (unpack (g x⃗))` is a
recursor application stuck on a variable.

So `funext` is asked for **lazily**: only a declaration with such a field asks
for it, because `funext` is in 1 of the 157 corpus files and *not* in
`init-prelude`, and asking every export for one would decline everything that
works today.

**Where it comes from was, for one round, the wrong answer, and this paragraph
is the correction rather than an appendix to it.** The rule was "read from the
export, the way `Eq` is — never fabricated", and a declaration with the shape
and no `funext` in its input declined. The reasoning behind that was sound
about `Eq` and false about `funext`, for one reason: **`funext` is a theorem in
Lean, not an axiom.** It is proved from `Quot.sound` by the standard quotient
trick, so "fabricating" it is not asserting anything — it is emitting a proof,
and this tool emits nothing but kernel-checked proofs. `pack`, `unpack`, the
round trips, `congrPack` and every ι rule are on exactly that footing.

So `modelgen` **derives** `funext` and emits it with its proof when the input
has none, under `T._model.funext`, and uses the input's own when the input has
one. §1.5 is the contract and `Modelgen.ensureFunext` is the code. **§1 does
not move**: no signature changes, and the one new name is namespaced and in no
statement.

The binder can sit in three places and they reach three different proofs, which
is why `funext_binder.lean` carries five declarations and not one:

| witness | where the binder sits | which proof needs funext |
| --- | --- | --- |
| `HTree.node : (N → List HTree) → HTree` | the **root**'s field | `recValue`'s minor, and every ι rule of `HTree.rec`. `pack` and `unpack` need only a lambda |
| `RTree.mk : Rose RTree → RTree`, `Rose.node : (N → Rose α) → Rose α` | the container's **own recursive** field | both **round trips**: `unpack₀ (pack₀ (Rose.node f))` reduces to `Rose.node (fun n => unpack₀ (pack₀ (f n)))`. `pack` and `unpack` need *nothing* — the induction hypothesis already **is** the function they want |
| `OTree.mk : Outer OTree → OTree`, `Outer.mk : (N → Inner α) → Outer α` | a container's field at **another** mimic | both round trips again, but `Outer` is not recursive, so there is no hypothesis to lean on and the proof is `funext (fun n => unpackPack₁ (f n))` outright |

The first cannot reach the other two — a root binder never enters
`retractValue` or `sectionValue` — and the second cannot reach the third,
because its position has an induction hypothesis where the third's has none.
`H2.node : (N → N → List H2) → H2` is a **two**-binder telescope, so closing
only the innermost `funext` is caught, and `H3.node : List H3 → (N → List H3) →
H3` puts a moving position with a binder beside one without in the *same*
constructor, where the congruence fold builds the two steps differently.
`infinitary.lean` is the same three shapes in a file with **no** `funext`, and
is the fixture for the *derivation*: the two files run the same three proofs
over two different `funext`s, `funext_binder`'s own and `infinitary`'s derived
one, and their declaration counts differ by exactly what was spliced.

**The part that is not `funext`, and is the reason this looked harder than it
was.** A single funext'd equation `Eq (fun x⃗ => unpack (pack (f x⃗))) f` is not
enough: the ι rule's other side holds the hypothesis *pointwise*, as
`fun x⃗ => T._model.rec_m (f x⃗)`, and `T._model.rec_m` δ-unfolds to a transport
**at each point**. Abstracting the whole function and transporting it once is a
different term and the kernel says so. What closes it is `congrFun` —
[`Modelgen.Gen.congrFunFor`], built from `Eq.rec` alone and read from nothing —
which recovers `Eq (y x⃗) (f x⃗)` from the funext'd equation; instantiated, that
is the *same proposition* as the retraction at `f x⃗`, so proof irrelevance
identifies the two and the rule's sides meet. That is the same mechanism
`congrPack_i` already used for a position without a binder.

15, 13, 19, 15 and 15 declarations, 29 statements compared against the
installed recursors' own rules with 0 differing, `nanoda_bin` accepts the
filtered export. `nest_binder_cross.lean` crosses the shape with the
declaration's indices, a mutual block and a cycle of mimics, and the cycle is
the one that needed code of its own: `packFamMinor` and `retractFamilyValue`
are a second copy of the one-at-a-time path and refused `CycB` until they were
taught the same telescope.

## 5.2 Boundaries — shapes Lean does not support either

* `nested model with dependent fields` — a constructor field's type mentions
  an earlier field the block holds at a **mimic**. The congruence fold
  replaces one packed position at a time, so such a field is ill-typed at
  every intermediate stage. **No fixture reaches this guard and none can**:
  Lean does not support the shape either. `node : (l : List GTree) → Len l N.z
  → GTree` and `node : Ctr2 JTree2 (fun l => Len l) → JTree2` both fail Lean's
  own nested compilation with `unknown constant`, because the auxiliary block
  replaces the nested occurrence with a fresh member and the dependent field
  is then about a constant that does not yet exist. The guard is kept because
  it says which shape stopped the generator where the kernel would only say
  that a term did not typecheck — but it is an *arm no declaration reaches*,
  and that is stated here rather than left to be discovered.

  A dependency on a field that does **not** move is supported, and
  `dependent_fields.lean` is three declarations of it: `node : (n : N) → Vec N
  n → List DTree → DTree`, `node : List ETree → (n : N) → Vec N n → ETree` —
  both orders, because a guard phrased as "nothing after the last moved field"
  would pass one and fail the other — and `KTree`, where the dependency is
  inside the *container's* constructor and the depended-on field is the
  recursive one, `Ctr.mk : (x : α) → P x → Ctr α P` at
  `Ctr KTree (fun _ => N)`.
* `nested model shape: a mutual block whose members land at different sorts` —
  a mutual block's `Eq`s are written at the one sort `g.u`, and two would need
  two. **Lean rejects it too**: the members of a mutual inductive must land in
  the same universe. A boundary, and deliberately without a fixture, because
  the source would not compile. `mutual model shape:` carries the same message
  for the same reason, from `Modelgen.mutualIso`.
* `mutual model shape: a block member has fewer binders than the block has
  parameters` — the members of one block disagree on their parameter count.
  **Lean rejects it too**, and so does `mini`
  (`mini/src/convert.rs`'s "members with different parameter counts", which
  `vendor/arena-tests/bad/048` exists for). A boundary, and without a fixture
  for the same reason.
* **An `unsafe` mutual block.** Lean has no recursor for an `unsafe` inductive,
  so there is nothing to model, and `lean4export` does not emit one at all
  (§3.1). Measured rather than argued: no `induct` record in the tree — 157
  corpus files, 42 `mini/tests/fixtures`, 31 `modelgen/tests` — nor in the
  5.6 GB Mathlib export carries `isUnsafe: true`. Not a shape this can meet.
* **`nested model without Eq` and `nested model without funext` are gone.** An
  input that declares neither now gets Lean's own, spliced (§1.5), and both
  fixtures are models: `decline_no_eq.lean`'s `Tree` over a spliced `Eq`, and
  `infinitary.lean`'s `HTree`/`RTree`/`OTree` over a `funext` derived from
  `Quot.sound`. What replaces them is narrower and is the next entry.
* `nested model: the input's N is not Lean's (…)` — the input **does** declare
  `Eq`, `Quot` or `Quot.sound`, at something other than Lean's statement. The
  check is the same one the old reasons used: the expected type is built at the
  found declaration's own level parameters and compared with `isDefEq`, so
  binder names and binder info do not matter, and the message says which part
  of the shape is wrong rather than that something was.

  **This is the one case a splice cannot reach**, and the reason is mechanical
  rather than a matter of principle: the name is already bound — in the
  environment the input was replayed into, in the output records already
  written, and in every one of the input's own terms — and `Lean.Environment`
  has no way to rebind a constant, so replacing it would mean replaying the
  whole file a second time. `funext` is *not* on this list, because the derived
  one is namespaced: an input with a wrong-shaped `funext` keeps it, and the
  model uses `T._model.funext` beside it.

  **No file in the corpus or the fixture tree reaches this**, and there is
  deliberately no fixture: a `bad/`-style export with a deliberately-wrong `Eq`
  is a test artefact and not a workload, and the guard exists so that such an
  input is *declined* rather than silently certified against an `Eq` that is
  not Lean's.
* `nested model name taken (N)` — `N` is declared somewhere in the input. Not a
  shape at all: a collision with the file's own names.
  `mini/tests/fixtures/nested_keying.lean`.
* **A nested occurrence whose container parameter mentions a constructor
  field** — `node : (n : N) → List (ITree n) → ITree (N.s n)` — reaches
  `a nested occurrence in ITree depends on a constructor field`. **Lean rejects
  it too**, at the kernel: "nested inductive datatypes parameters cannot
  contain local variables". So this is a boundary and not a gap, and there is
  deliberately no fixture: the source would not compile.

  **A lambda's own binder is a local variable for the same purpose**, which is
  the boundary of §5.1's axis and is measured rather than assumed:
  `Ctr N (fun x => Vec M3 x)` — the recursion inside the lambda, indexed by the
  lambda's binder through a *second* container — fails Lean's own compilation
  with exactly that message, `invalid nested inductive datatype 'Ctr'`. The
  lambda may be applied to the occurrence's parameters (`RB N (fun k => Vec Idx
  k)` is a model) but the occurrence a *further* container introduces cannot
  mention the binder, because the mimic that container needs would be
  parameterised by it. No fixture: the source would not compile.
* **A constructor's result *index* that mentions a field the block holds at a
  mimic.** Every congruence and transport fold in this file takes the goal's
  index vector off the constructor application once and holds it fixed across
  the fold, which would be wrong if a moved field appeared in it. **Lean
  rejects the shape too**, and for §5.2's first reason: `inductive C (α : Type)
  : N → Type | mk : (l : Lst α) → C α (llen l)` nested at `TT.node : C TT N.z →
  TT` fails Lean's own compilation with `(kernel) application type mismatch:
  llen TT l … argument has type _nested.Lst_2`, because the auxiliary block has
  replaced `Lst TT` with a fresh member and `llen` is not about it. A boundary,
  and deliberately without a fixture; measured rather than argued.

## 5.3 An arm no declaration reaches

`nested model with mutually recursive occurrences` is now reached only when a
cyclic group of mimics is **not** the recursor family of any one container —
[`Modelgen.familyFor`] tries every member of the group as the anchor and finds
none whose family covers the group exactly. **No fixture reaches it and the
seat that closed the axis could not construct one**: a cycle among mimics is a
cycle among their containers, and a set of mutually recursive containers is a
Lean block, which has exactly such a family. It is kept because a group this
cannot write is a wrong model rather than a missing one, and it is recorded
here as an *arm nothing reaches* rather than as a covered refusal.

`nested model shape: …'s recursive positions and hypotheses do not line up` is
a second such arm, in `packMinor` and `retractValue`. It counts the container's
recursive positions — occurrence `i` at any index vector and **under any binder
telescope**, which is `Gen.occUnder?` — and asserts that count is the number of
induction hypotheses Lean bound. Those are the same set: Lean gives exactly the
recursive positions a hypothesis, infinitary ones included, which is what
`funext_binder.lean`'s `RTree` over `Rose` measures. Kept because a vector read
off by one is a wrong model rather than a missing one.

## 5.4 What `nested model shape: …` means

A shape the generator cannot write, or a proof the kernel did not accept. It
is the catch-all, so a new occupant of it is a new gap and not a known one —
and that is exactly how §5.1's last gap arrived, as this message on `Lean.Json`
and `Lean.PrefixTreeNode` (§6.3), which is also how it was recognised as one
rather than filed as a boundary. Its only occupant now is **one file in the
whole tree, and it is a lie rather than a shape**:

> `vendor/arena-tests/bad/nested-unused-param.ndjson`'s `E` declines with
> `nested model shape: [E._model.pack_0] rejected by the kernel: (kernel)
> invalid projection`. `E : W → Sort` nests as `E.mk : (w : W) → L (E w)
> (w.[C/0].[C/0]) → E w`, and the container's second parameter is a projection
> **at a structure type `C` the file never declares** — the only mention of
> `C` anywhere in it is that projection's `typeName`. So the occurrence itself
> mentions an undeclared constant, `pack_0` carries it, and `addDeclCore`
> refuses it before anything is emitted. That is the catch-all doing its
> documented job on a `bad/` file; `nanoda_bin` refuses the same input, at
> `checker/src/tc.rs:702`. Not a gap and not a shape.

The two arms §5.3 names are the only other `nested model shape:` messages a
*declaration* could reach, and neither is reached.

## 5.5 One Lean-side wrinkle

`Environment.addDeclCore` maintains an elaborator-side index keyed by
*normalised* names, and `panic!`s when two distinct private names collide
there. An export is many modules flattened into one file, so
`vendor/arena-tests/good/perf/grind-ring-5.ndjson` has
`_private.Init.Grind.Ring.CommSolver.0.PSigma.casesOn._arg_pusher` beside
`_private.Init.Data.Nat.Gcd.0.…` and the panic fires. It is not fatal — the
entry is dropped from an index this tool never reads — and that file's filtered
output is accepted by `nanoda` at 2470 declarations. The kernel-level API
(`Kernel.Environment.addDeclWithoutChecking`) avoids it but is not usable:
`Environment.find?`, which `MetaM`'s `inferType` goes through, reads the
*imported* half of the constant map and then the async map, so a constant added
that way is invisible and the generator cannot name `List.rec`.

**Both of those sentences are measured rather than reasoned, and §6.6 and §6.7
are the measurements** — 418 declarations lost on Mathlib and none of them
reachable from anything this tool looks up; 0 of 12,788 visible after
`Environment.ofKernelEnv`. §6.6 also names a **larger** hole in the same index
that has nothing to do with the panic: `Declaration.getNames` omits the
auxiliary `T.rec_k` of every nested inductive, so those are invisible to
`Environment.find?` in every export, always. `Test.lean`'s `runEnvProbe` pins
both properties on a fixture.

A **mutual** block whose members nest is specialised as one block, under the
first member's `_model` namespace and with one carrier per real member (§1,
§4.2).

---

# 6. Mathlib, measured

**It completes, it models all 92, and nothing about it is near a wall.** The
whole 5,636,308,621-byte export, `-o` and `--check-recursors`, is **268.74 s at
23,879,684 KB and 3,060,522,736,620 instructions**, exit 0, and writes
5,657,412,885 bytes in 100,274,163 lines — 272,758 more than the input's
100,001,405, which is what 92 models cost.

The 92 are **41 + 41 + 10**: Mathlib's 41 nested declarations, all modelled and
none declined (the two that used to decline were `Lean.Json` and
`Lean.PrefixTreeNode`, and §6.3 is what they were); §1.7's composed model of
each of those 41; and its 10 plain mutual blocks (§1.6), all modelled and none
declined. Its two internal oracles hold at that size — **1,365** ι statements
rebuilt from the installed recursors with 0 differing, **6,796** recursors
compared against Lean's own with 0 differing — and `nanoda_bin` accepts the
output.

**What §1.7 costs, in the file.** Against the same binary without the
composition — 51 models, 5,649,813,083 bytes, 100,181,583 lines, 742 ι
statements — the 41 composed models are **1,328 more generated declarations**
(3,170 against 1,842), **+7,599,802 bytes** and **+92,580 lines**. That is
**+0.13 % of the output** for a second, single-inductive development of every
nested declaration in Mathlib, and it is the number to weigh against §7's 1059
lines. Per declaration the composed model is 8 to 210 declarations, the largest
being `Lean.Meta.Grind.Arith.Cutsat.EqCnstr._model.0` at 210 beside its
layer-1's 232.

**Neither construction is distinguishable from run-to-run noise on the clock or
the peak.** Three runs of the whole file, in order: 41 models at **272.36 s /
23,903,180 KB**; §1.6's ten more at **264.97 s / 23,894,540 KB**; §1.7's
forty-one more at **268.74 s / 23,879,684 KB**. The wall goes down, up and
sideways and the peak falls 23,540 KB across a change that added 1,586 generated
declarations.
**None of that is a claim about either change**, and `MEASUREMENTS.md`'s
"counters against clocks" is why: a wall delta between sittings on a shared
machine carries nothing, and this machine had another seat's 22 GB `modelgen` on
it for part of the afternoon. What the runs do say is what the **counters** say
— 92 models, 0 declines, 1,365 ι statements and 6,796 recursors all comparing
clean, and 3,170 generated declarations each checked by the kernel — and that
the peak, which *is* stable across sittings (§6.6), did not move. The
instruction count is recorded as a scale figure and not as a comparison, because
there is no counterpart run of a pre-composition binary taken under `perf`.

> **And ten is the number, which is not what was expected.** The brief for this
> work said "Mathlib has far more mutual blocks than nested ones", and the
> census says otherwise: **41 nested declarations against 10 plain mutual
> blocks**, the first of them not until somewhere between line 10,000,000 and
> line 20,000,000 (§6.1's `mut` column). Mutual blocks are common in Lean
> **source**; what reaches an export as a mutual `induct` record is rarer,
> because a `mutual` whose members nest is one *nested* block and goes the other
> way, and a `mutual` of definitions is not an inductive at all.

For scale, `MONOMORPH.md` §9.5's mode A over the same file with `-o` peaks at
**35,294,528 KB** against this pass's **23,879,684 KB** — **a third less
memory** — and the difference is the work rather than the loading: `monomorph`
materialises 776,723 fresh declarations where this adds 3,170. **There is no
speed ratio here any more.** The one that stood divided by 815.42 s, a row
§9.5 has since superseded with 741.14 s, and two wall clocks from different
sittings on a shared machine do not make a ratio at all — see
`MEASUREMENTS.md`, "Which recorded numbers carry weight: counters against
clocks".

Every number below is `/run/current-system/sw/bin/time -v` around the binary in
a subshell with `ulimit -v`, on `MONOMORPH.md` §9.1's export — the same bytes,
not re-exported.

## 6.1 The ladder

Genuine prefixes of the export, by line count, each with `-o` and
`--check-recursors`. `nested` is `grep -c '"numNested":[1-9]'` on the prefix and
`mut` is a census of `induct` records with more than one member and
`numNested = 0`; **`models` and `declined` add up to their sum at every rung**,
which is how the second column is checked rather than asserted.

`models` is `2·nested + mut`: one layer-1 and one layer-2 model per nested
declaration (§1.7), one per plain mutual block (§1.6).

| lines | bytes | nested | mut | models | declined | ι stmts | recursors | wall | peak RSS |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 9 k | 496,065 | 0 | 0 | 0 | 0 | 0 | 35 | **0.14 s** | 93,628 KB |
| 1 M | 53,134,694 | 2 | 0 | 4 | 0 | 60 | 491 | 2.36 s | 264,428 KB |
| 3 M | 161,692,734 | 9 | 0 | 18 | 0 | 250 | 980 | 7.08 s | 779,520 KB |
| 10 M | 537,800,217 | 13 | 0 | 26 | 0 | 372 | 1,718 | 23.16 s | 2,382,256 KB |
| 20 M | 1,097,064,174 | 27 | 8 | 62 | 0 | 1,046 | 3,128 | 49.43 s | 4,749,160 KB |
| 30 M | 1,653,766,803 | 34 | 9 | 77 | 0 | 1,209 | 4,171 | 73.46 s | 7,112,284 KB |
| 50 M | 2,770,944,883 | 40 | 9 | 89 | 0 | 1,345 | 5,826 | 123.40 s | 11,849,616 KB |
| **all** | **5,636,308,621** | **41** | **10** | **92** | **0** | **1,365** | **6,796** | **268.74 s** | **23,879,684 KB** |

**The `declined` column is zero at every rung**, which is §5.1's repair; before
it, the 3 M rung onwards read `2` and the ι-statement column was 97, 158, 444,
520, 588, 595.

**The `mut` column is zero for the first three rungs**, and that is not an
artefact of where the prefixes fall: Mathlib's **first** plain mutual block is
somewhere between line 10,000,000 and line 20,000,000, and there are ten in the
whole 100-million-line file. §6.2 names them. The `models` column is **not**
zero there, because §1.7's second layer is one per *nested* declaration and
those start at line 9,948.

**Peak RSS is 4.3–5.1× the input and the ratio *falls*** — 5.10, 4.94, 4.54,
4.43, 4.40, 4.38, **4.34** — so the interning tables amortise and there is
no knee, and it is the *same* seven ratios the ladder gave at 39 models, at 41
and at 51: 1,586 more generated declarations in a 5.6 GB file and the memory
does not see them. **Wall is flat in the input**: 0.0444 s/MB at 1 M rising to
0.0477 s/MB on the whole file, a 7 % drift over a 106× range. Neither curve
turns, which is what the ladder was walked to find out.

The rungs are the same file prefixes as every earlier ladder, byte for byte, so
the three are comparable row by row.

## 6.2 What it produced

**92 models, 3,170 generated declarations**, of which **41 are §1.7's composed
layer**: one per nested declaration, **1,328 declarations** between them, 8 to
210 each. The largest is
`Lean.Meta.Grind.Arith.Cutsat.EqCnstr._model.0` at 210, beside the 232 of the
layer-1 model it is about; then `Lean.Doc.Block._model.0` 58,
`Lean.Elab.Term.Do.Code._model.0` 56, `Lean.Compiler.LCNF.Alt._model.0` 52,
`Lean.IR.Alt._model.0` 46, `Lean.IR.IRType._model.0` 42, and
`Lean.Json._model.0` and `Lean.Elab.InfoTree._model.0` at 40 each.

Ten more are the plain mutual blocks (§1.6), **258 declarations** between them:
`Lean.Meta.Grind.Arith.Linear.EqCnstr` 80, `Lean.Meta.Grind.AC.EqCnstr` 42,
`Lean.Meta.Grind.Arith.CommRing.EqCnstr` 24, `Lean.Meta.Grind.AC.DiseqCnstr` 24,
`Mathlib.Tactic.Ring.ExBase` 20, `Lists.Equiv` 14, `Lists.Equiv.below` 14,
`Lean.Meta.Grind.Arith.Linear.RingIneqCnstr` 14,
`Lean.Meta.Grind.Arith.Linear.RingEqCnstr` 14 and
`Lean.Meta.Grind.Arith.Linear.RingDiseqCnstr` 12.
`Lists.Equiv.below` is worth a glance: it is the `below` motive Lean generates
*beside* a mutual inductive, and it is itself a mutual inductive, so the
construction meets its own kind of input without being told.

The remaining **41 are the nested declarations themselves, 1,584 generated
declarations**, 20 to 232 each. The largest is
`Lean.Meta.Grind.Arith.Cutsat.EqCnstr` at 232, a mutual block; then
`Lean.Doc.Block` 78, `Lean.Elab.Term.Do.Code` 71, `Lean.Compiler.LCNF.Alt` 56,
`Lean.Elab.InfoTree` 54, **`Lean.Json` 52**, `Lean.IR.Alt` 50,
`Lean.IR.IRType` 46, `Lean.Widget.HighlightedMsgEmbed` and
`Lean.Server.Test.Runner.Client.HighlightedMsgEmbed` 45 each,
`Lean.Widget.MsgEmbed` and `Lean.Server.Test.Runner.Client.MsgEmbed` 43,
`Lean.Elab.Tactic.TacticParsedSnapshot` 42, `Lean.MessageData` and
`Lean.Doc.Inline` 40, `Lean.Lsp.DocumentSymbol` 35,
`Lean.Language.SnapshotTree` 34, `Lean.PersistentHashMap.Node` and
`IO.AsyncList` 31, `Mathlib.Tactic.Translate.Reorder`,
**`Lean.PrefixTreeNode`**, `Lean.Meta.DiscrTree.Trie` and
`Lean.Language.Lean.CommandParsedSnapshot` 27, `Lean.Syntax`,
`Lean.Compiler.LCNF.UnreachableBranches.Value` and `Aesop.IndexingMode` 26,
`Lean.Elab.Tactic.RCases.RCasesPatt` 25, `Lean.Data.Trie`,
`Lean.Widget.TaggedText` and `ProofWidgets.Html` 24,
`Lean.Parser.Tactic.MCasesPat` and `Lean.Meta.Match.Pattern` 23,
`Lean.PersistentArrayNode` and `Aesop.Script.StepTree` 22, `Lean.Level.PP.Result`,
`Lean.Parser.Tactic.MRefinePat` and `Lean.Meta.Match.Example` 21, and
`Lean.Doc.Part`, `Aesop.Frontend.RuleExpr`, `Lean.Lsp.Ipc.CallHierarchy` and
`Lean.Lsp.Ipc.ModuleHierarchy` 20. The two in bold are the two §6.3 was about.

**No prelude was spliced** (§1.5), at any rung, and that is still true with the
two new models in it. Mathlib declares `Eq`, `Quot.sound` and `funext` itself,
and none of the 41 has a constructor field at a mimic under a binder — so the splice's *"only when a model is actually being
spliced"* clause is what Mathlib exercises, not the splice.

## 6.3 The two declines there used to be, and what closing them took

```
Lean.PrefixTreeNode: declined — nested model shape:
  [Lean.PrefixTreeNode._model.unpack_2] rejected by the kernel: (kernel) application type mismatch
Lean.Json: declined — nested model shape:
  [Lean.Json._model.unpack_2] rejected by the kernel: (kernel) application type mismatch
```

**Both are models now**, at 27 and 52 declarations, and this section is kept
because the shape is the one §5.1 had wrong and the diagnosis is the reason the
repair is where it is.

**One shape.** Both nest through `RBNode α β`, whose second parameter is a
**family**, and both put the recursion *inside the lambda* that fills it:
`Lean.Json.obj (kvPairs : RBNode String (fun _ => Json))`,
`Lean.PrefixTreeNode.node (children : RBNode α (fun _ => PrefixTreeNode α β))`.

What the kernel objected to was the induction hypothesis for the container's own
recursive field arriving at the wrong block member:

```
RB.node N (fun x => JT._model.self) a_ih✝² k a✝¹ a_ih✝¹
argument has type
  JT._model.0
but function has type
  (RB N fun x => JT._model.self) → RB N fun x => JT._model.self
```

`JT._model.0` is the root and the position wants the mimic. Lean's own
`JT.rec_1` says why, and it is worth reading:

```
@JT.rec_1 : {motive_1 : JT → Sort u} → {motive_2 : (RB N fun x => JT) → Sort u} →
  motive_1 JT.null →
  ((a : RB N fun x => JT) → motive_2 a → motive_1 (JT.obj a)) →
  motive_2 RB.leaf →
  ((a : RB N fun x => JT) → (k : N) → (a_1 : (fun x => JT) k) → (a_2 : RB N fun x => JT) →
     motive_2 a → motive_1 a_1 → motive_2 a_2 → motive_2 (a.node k a_1 a_2)) →
  (t : RB N fun x => JT) → motive_2 t
```

**`RB.node`'s minor binds three hypotheses and the middle one is at the root**:
`motive_2 a`, `motive_1 a_1`, `motive_2 a_2`. `a_1 : (fun x => JT) k` is a
recursive position of the *declaration* sitting between two of the container's,
and Lean gives all three a hypothesis over one shared motive vector — because
the kernel's own test for a recursive argument reduces, and `(fun x => JT) k`
reduces to `JT`.

**The tool did not, and that is the whole defect.** `Gen.memberOf` asked
`getAppFn` which member a field is at and got a lambda, so it counted two
hypotheses where the minor binds three and `unpack` put `motive_1 a_1`'s
hypothesis in `RB.node`'s first child slot. The same blindness sat in
`Gen.occIdx?` (which occurrence, at which indices) and `Gen.idxOf` (which index
vector), and a fourth copy of it sat in `Plan.spec`, which sweeps a constructor
type for occurrences and never descended into the **head** of an application —
so an occurrence inside the lambda body, `RB N (fun _ => L T)`, got no mimic and
the block came out ill-typed.

The repair is [`Modelgen.headNorm`] — β and ζ at the head, never δ, because
unfolding a definition there would make a carrier look like a block member — at
each of the three readers, and one line of descent in `Plan.spec`. Nothing else
moved: **230 of the 231 exports in the tree filter to the same bytes as before**
(`vendor/arena-tests`, `modelgen/tests`, `modelgen/monotests`,
`mini/tests/fixtures`), the one that differs being `nest_fam_arg` itself, and
`init-prelude`'s output is byte-identical.

Nothing in `vendor/arena-tests` could see it: no corpus file nests inside a
lambda at a container argument, which is how 221 files and every axis of §4.2
passed over a shape two of Mathlib's 41 have. `nest_fam_arg.lean` is that axis
swept, and §4.2 and §5.1 are what the sweep found.

## 6.4 The oracles at scale

**Both internal oracles ran on the whole file and both hold.** Oracle 3, the ι
statements rebuilt from the rule the *installed* `T.rec_k` carries: **742
compared, 0 differ** — 595 of them before §5.1's repair, 28 more from
`Lean.Json` and `Lean.PrefixTreeNode`, and the rest §1.6's ten mutual blocks.
Oracle 4, `--check-recursors`, every recursor in the input
against the one Lean's kernel regenerated during the replay: **6,796 checked, 0
differ**. Neither needed a prefix, and neither is free-standing — the
`--check-recursors` columns above come from the same runs as the wall clocks, so
their cost is inside every number in this section.

6,796 is not 670,630 because only an **inductive** record carries recursors and
only those can be compared. `MONOMORPH.md` §9.5's 2,027 "recRegen" is a
different question — recursors `lean4export` would regenerate differently under
`monomorph`'s renaming — and says nothing about these.

**`nanoda_bin` accepts the output**, which is the external oracle and the one
that could have gone the other way. On the **whole file**, at all 92 models:

```
Checked 675403 declarations with no typechecker errors, 1 pretty printer errors: [
    "Unable to print axioms",
]
```

**2,711.07 s at 10,720,844 KB and 23,041,411,415,474 instructions, exit 0.**
Four controls, the same binary on the same machine and the same 5.6 GB of
input:

| output | declarations accepted |
| --- | ---: |
| the *unmodified* export (`MONOMORPH.md` §9.7) | 670,630 |
| 39 models, before §5.1's repair and §1.6 | 672,858 |
| 51 models, §1.6's ten added | 673,370 |
| **92 models, §1.7 composed** | **675,403** |

So the filtered file is **4,773 declarations more than the input** and the
composition is **2,033 of them**, for a peak within **+0.09 %** of the input
run's. Every one of them was typechecked twice — by the Lean kernel that minted
it and by this one.

What could have gone wrong and did not: the second layer's tag and carrier are
new inductives in a file that already had the first layer's block, and **they do
not trip the `isRec` assert §4 names** — the tag is a single inductive no
constructor of which mentions it, and the carrier is a single inductive, so
"per member" and "the whole block" are the same question for both. Forty-one
real blocks say so. `MONOMORPH.md` §9.7's `monomorph` output **stops** `nanoda`
at `declaration not found in infer_const`; this one does not.

**§5.1's two new models had a prefix run of their own before this**, and it is
kept because it is the finer measurement: the 3 M rung is the smallest that has
both — it is where `Lean.Json` and `Lean.PrefixTreeNode` first appear — and
filtered it is *"Checked 30126 declarations with no typechecker errors"*,
16.42 s at 287,340 KB, exit 0, against the raw prefix's 29640 at 16.15 s and
294,232 KB. The whole-file run above now covers them too.

That is the whole of §1.5's and §3's re-interning tested at 100 million lines:
every back-reference in a 5.6 GB file was renumbered around 92 spliced models
and a second, independent implementation read all of it in order. And the 3,170
generated declarations are typechecked twice — by the Lean kernel that minted
them and by this one.

## 6.5 The identity property, on Mathlib

§3's byte-identity is measured on 186 of the tree's 231 files. It holds on real
Lean output too. The first **9,000** lines of the export contain no nested
declaration — the first is at line 9,948 — and

```
modelgen pre-9000.ndjson -o out-9000.ndjson --check-recursors   # 0.16 s
cmp pre-9000.ndjson out-9000.ndjson                             # identical
```

with 35 recursors checked and 0 differing. **No larger prefix can test it**: the
ladder's smallest rung already contains two nested declarations, so 9,000 lines
is the whole of what this export has to say about the property.

## 6.6 Where the 272 s and the 24 GB go — and it is not the replay

`modelgen/EnvProbe.lean` runs the pass's front half on its own. Same file, same
cap, same `time -v`, all three in one sitting:

| | wall | peak RSS |
| --- | ---: | ---: |
| `envprobe mathlib.ndjson P` — parse, and stop | **153.56 s** | **23,902,196 KB** |
| `envprobe mathlib.ndjson A` — parse, then replay | 171.57 s | 23,904,544 KB |
| `modelgen mathlib.ndjson -o … --check-recursors` | 268.74 s | 23,879,684 KB |

**The peak is the parse.** All three figures are within **0.04 %** of each
other, and the smallest wall of the three is the one that also builds a
670,630-constant `Environment`. Replaying every declaration through
`Environment.addDeclCore` costs **+18.01 s (+12 %) and does not raise the peak
at all**: `toDeclaration` hands the parsed `Expr`s to the kernel without
copying them, so the environment is overwhelmingly pointers into objects the
parse already allocated, and what it adds fits inside what the parse had
already peaked at. Generation, both oracles and writing 5,657,412,885 bytes
together are **+97.17 s** and **−24,860 KB** on top of that.

So the split is roughly **57 % parse, 7 % replay, 36 % everything this tool
exists to do**. **Only the peak column is stable across sittings**: an earlier
set on the same file, before §5.1's repair, gave 174.30 s / 202.92 s / 267.93 s
— a 65/11/24 split — with the three peaks inside the same 0.3 % of each other.
So the *wall* split moves with what else the machine's disk is doing and the
*memory* conclusion does not. The 23.9 GB is the parsed export — 654,504 records, 670,630
names, 4.34× the input's bytes — held beside the input `String` the parser is
reading from. **The lever on memory is a streaming parser, not the
environment**, and specifically not freeing the input text afterwards: the peak
happens while text and export are necessarily both live. `Export.stream`
(`MONOMORPH.md` §9.5) did this for the writer and the reader has no counterpart.

This settles a question that had only ever been asked of a pass that also
substitutes. `monomorph`'s 34–37 GB is **not** an inherited cost of replaying an
export into a Lean `Environment`; replaying is nearly free on top of holding
the export, and holding the export is 23.9 GB. For comparison, `nanoda_bin`
holds *and typechecks* the same file in 10,711,008 KB, so the Lean-side
representation is **2.2×** a Rust arena's for the same content.

## 6.7 The `AsyncConsts` loss, measured — and the larger hole beside it

§5.5's panic fires on Mathlib **836 times over 418 distinct name pairs**. That
is 418 declarations lost, not 836: `addDeclCore` registers each name in both the
private and the public async map, so a pair panics twice. It matches
`MONOMORPH.md` §9.7's 418 for the input replay exactly.

**What the loss can do was an open question and is not one now.** One reading of
`Lean/Environment.lean` and three measurements:

1. **Nothing is lost from the kernel.** `addDeclCore` calls
   `addDeclWithoutChecking` first and updates `asyncConstsMap` after; the panic
   is in the second step, whose `Inhabited` instance returns the map unchanged.
   So the constant is in `env.constants` — which *is* `env.toKernelEnv.constants`
   — and missing only from `Environment.find?`.
2. **`modelgen` reads the kernel map.** Every environment lookup this tool makes
   is `env.constants.find?` — all **21** of them, four in `Modelgen/Plan.lean`,
   six in `Modelgen/Model.lean` and eleven in `Modelgen/Driver.lean`, the last
   covering `indEDecl`, `checkRecs`, `modelTable` and `checkModel`. **Not one
   goes through `Environment.find?`**; outside `Test.lean` and `EnvProbe.lean`
   the only mention of that name in the package is the comment at
   `Driver.lean:351` explaining why. The
   exposure is `MetaM`'s `inferType`/`whnf`, which resolve the other way — and
   the generator runs *before* the declaration it models is added, and
   `checkModel`'s `restore` rewrites the input's `T.rec_k` out of every term it
   then infers a type for.
3. **A missing entry is never a wrong answer.** `AsyncConsts.findRec?` guards
   with `privateToUserName c ≠ privateToUserName declName` for exactly this
   case, so when privacy is the only difference between the constant it found
   and the one asked for it returns `none` rather than the other member of the
   pair. The failure mode is strictly *absence*, and absence here is an
   `unknown constant` exception — a decline carrying that message, which is
   loud. **Mathlib has no decline at all** now, of that kind or any other, and
   when it had two they were §6.3's, whose fixture reproduces them with **no
   private names and no panic at all**. Nor was a declaration skipped rather
   than declined — §6.1's `nested` column is `models + declined` at every rung,
   so all 41 were reached.

So: **the loss cannot make this tool emit a wrong model, and on Mathlib it did
not make it miss one.** The first half is by construction and the second is by
measurement — but the construction is claim 2, which is a property of the code
as it stands and which nothing enforces. A lookup written `(← getEnv).find?`
instead of `(← getEnv).constants.find?` would acquire the hazard silently.

**And the panic is not the largest thing missing from that index.** Probing the
1-million-line prefix for names in the kernel map and absent from
`Environment.find?` returns **13**, of which only 9 are panic victims; the other
four are `Lean.Syntax.rec_1`, `Lean.Syntax.rec_2`, `Lean.IR.IRType.rec_1` and
`Lean.IR.IRType.rec_2` — **the auxiliary recursors of that prefix's two nested
declarations**, which is to say the constants this tool exists to be about. On
the whole file it is **539 = 418 + 121**, the 121 being every `T.rec_k` of every
one of the 41. They are missing for a documented reason and not a bug;
`Declaration.getNames`, the loop `addDeclCore` registers from, says of itself:

> *"This does not include auxiliary definitions such as projections added by
> the elaborator, **nor auxiliary recursors computed by the kernel for nested
> inductive types**."*

So `T.rec` is registered and `T.rec_1` never is, in every export, always. It is
a larger hole than the panic and `modelgen` is untouched by it for the same
reason — which is what makes claim 2 load-bearing rather than incidental.
`Test.lean`'s `runEnvProbe` pins it on `nested_iota`, with `Tree.rec` beside
`Tree.rec_1` as the atom that says the check is not "nothing is visible".

## 6.8 `lean4checker`'s loading model is not available to this tool

§5.5 says the kernel-level API avoids the panic and is not usable. **Measured
rather than asserted**: `Kernel.Environment.addDeclWithoutChecking` over the
1-million-line prefix, followed by `Environment.ofKernelEnv`, puts **12,788 of
12,788** names in `Kernel.Environment.find?` and **0 of 12,788** within reach of
`Environment.find?`.

Two lines of `Lean/Environment.lean` are the reason. `ofKernelEnv` sets
`base.private := base.public := env` and nothing else; `Environment.find?`
consults `base…constants.map₁` and then the async maps, and `map₁` is the
*imported* half — `mkEmptyEnvironment` builds the constant map as
`SMap.empty.switch`, so every replayed constant lands in `map₂`, which
`Environment.find?` never reads. `Kernel.Environment`'s constructor is
`private mk`, so the staging cannot be flipped from outside `Lean`.

**So the divergence from `lean4checker` is not a choice this repository can
simply undo.** `lean4checker`'s job ends at the kernel; this tool's generator is
`MetaM` — `forallTelescope`, `whnf`, `inferType`, `mkForallFVars` — and `MetaM`
resolves constants through `Environment.find?`. Lean's own upstreamed replay,
`Lean.Environment.replay` in `Lean/Replay.lean`, is on the same path: it calls
`Environment.addDeclCore` and would panic on the same input. Closing this needs
an upstream affordance — an `Environment` whose `find?` falls back to the kernel
map — which is a question for `leanprover/lean4` and not a refactor here.
§6.6 also removes the incentive: the elaborator path is not what the memory is.

## 6.9 What was not measured

* **`mini` over the filtered Mathlib output.** `mini` execs this binary on its
  hot path (§1.4) and nothing has run that pipeline at this size. `nanoda_bin`
  has (§6.4); `mini` has not. What `mini` *has* read is the composed output at
  fixture size, and it certifies all of it (§1.7).
* **Lean's kernel over the generated declarations** is *not* on this list: all
  3,170 go through `Environment.addDeclCore` with checking **on**, which is
  oracle 1, and the wall clock in §6.1 includes it.
* **A second export.** Everything here is `lean4export` 3.1.0 at githash
  `f72c35b3`, Lean v4.29.1, one export made once. Nothing says a newer
  toolchain's Mathlib has the same 41 and 10.
* **A shape outside the three axes swept.** §5.1 is empty against everything
  `nest_odd_shapes.lean`, `nest_fam_arg.lean` and §1.6's six mutual fixtures
  ask, which is what `inductive` *declares*, how a container is **applied**,
  and what a **block** may be. It is not a proof that no fourth axis exists,
  and the last time this section was short one, an export nobody had run was
  what said so.
* **`mini` consuming a mutual model.** §1.6 is a contract and a generator; the
  recogniser on the other side is not written, and §7 is the assessment of what
  writing it would cost and buy.

  What *was* measured is the weaker thing, and it is worth having: `mini`
  **accepts and certifies the model's own declarations**, today, with no
  recogniser at all, because the tag and the carrier are single inductives and
  the rest is ordinary `def`s and theorems. At `--mutual`,
  `mutual_three_way_cycle` goes from `accept 10 declarations` to `accept 31`
  and `mutual_iota_reduction` from 10 to 30. At `--nested`, on the composed
  fixtures, `nested_iota_arm` is 63 pairs / 63 `constEv` / 63 `typeEv` with
  `waiting` empty and `gapped` 0, and `nested_keying` 63 / 61 / 62 — every
  declaration of **both** layers certifying, which is the strongest evidence
  short of the recogniser that §1.7's output is consumable. What is *not* keyed
  is the block itself: `⟦A⟧` is still `A`'s own and not `A._model.self`, which
  is exactly the side table §7 is about.

---

# 7. What `mini` could delete, and what it would need in exchange

`modelgen` gaining these constructions does not by itself remove anything from
`mini`. This section is the assessment, and its conclusion is that the deletion
is **real, whole-file, and available**: with §1.7 in place the one thing that
gated it is gone, and what is left is the recogniser on the other side.

**What would go.** `mini/src/mutual_aux.rs`, **1059 lines**, whole. Every part
of it is about this construction and nothing outside it: `encode` (lines
336–735, the encoding), the syntax helpers and `to_aux` (205–335), `Reason`,
`Encoding` and `Encoding::declares` (134–204), and `expand`/`is_rule_of`/`add`/
`equality` (878–1058). Its three live call sites go with it — `run.rs:261` and
`eq_cash.rs:549` call `expand`, `ledger.rs:1148` calls `encode` only to recover
a decline reason — as do `convert.rs`'s three `facts` fields (`mutual_blocks`,
`mutual_encoded`, `mutual_rules`) and the `--mutual` reporting hung off them.
`ci/check-mutual-blackbox.sh` would drop to two files.

Even the σ fixpoint goes. `demand_over` (788–843) carries a docstring saying
`nested_splice` calls it "rather than carrying a second copy"; **it does not any
more** — `grep -rn demand_over mini/src/` has no hit outside `mutual_aux.rs`,
and `nested_splice.rs` has a `demand` method of its own. That is a stale comment
and a note for whoever does the deletion, not a dependency.

**What it would need in exchange, and it is less than it sounds.**
`mini/src/nested_splice.rs` already recognises a `modelgen` model by §1's naming
convention and keys it: 792 lines whose four name builders are

```rust
fn model_prefix(t) = t ++ "_model"
pub fn carrier_name(t) = model_prefix(t) ++ "self"
fn ctor_name(t, j)     = model_prefix(t) ++ "ctor_{j}"
fn rec_name(t, k)      = model_prefix(t) ++ "rec_{k}"
fn iota_name(t, k, j)  = model_prefix(t) ++ "iota_{k}_{j}"
```

— which are **exactly** §1.6's names, unchanged. `carrier_name(R_k)` is already
`R_k._model.self`, the per-member carrier; `ctor_name(all[0], j)`,
`rec_name(all[0], k)` and `iota_name(all[0], k, j)` are already the rest. And
the one place §1 makes a consumer do arithmetic — the export's name for block
index `k` is `R₀.rec_{k−r+1}` once `k ≥ r` — **does not arise here**, because a
plain mutual block has no mimics and the recursor index is the member index.
So the exchange is an extension of an existing module along a path it already
walks, plus the `Missing` variants relabelled for the second construction. It is
not a second `nested_splice.rs`.

**The `export-fixture.sh` hazard, and composition made it smaller rather than
worse.** `scripts/export-fixture.sh` passes everything it writes through this
binary, because `mini/tests/fixtures` has to arrive already filtered; it is
**not** run in CI — `grep -rn export-fixture ci/` has no hit — so nothing
regenerates those files automatically, and a generator change can sit there as a
latent diff.

§1.6 created one: the ten `mutual_*.ndjson` and `nested_model.ndjson` would
acquire a model on the next regeneration. **§1.7 did not add to it — it
discharged the other half.** The five nested fixtures §1.7 would have moved were
regenerated *in this change*, with the script, and `mini`'s Rust suite was
re-pinned and re-run against them (`nested.rs`'s two live evidence tuples, and
`mutual.rs`'s recursor oracle, which now compares the second layer's recursors
too). What is left latent is the eleven mutual files and nothing else, and
`modelgen/Test.lean`'s cross-check covers the five that matter — it is the check
that failed and said *"regenerate it with `scripts/export-fixture.sh`"*, which is
how the regeneration came to be part of this change rather than a surprise for
somebody else.

The eleven are left because nothing reads them expecting a model: `mutual.rs`'s
fixtures are read at `--mutual`, where `mutual_aux` encodes the block itself.
They should be regenerated **with** the recogniser, in the change that deletes
`mutual_aux.rs`, and not before.

**The gate that stood here is closed.** It read: `run.rs` runs
`nested_splice::recognise` and *then* `mutual_aux::expand`, with a comment
saying why — *"the model contains a `mutual … end` block of its own, and the σ
this pass propagates onto its members have to be in the schedule `expand`
reads"* — so `mutual_aux` was what let `mini` consume `modelgen`'s nested models
at all, and no recogniser could replace it, because that block had **no model to
recognise**. §1.7 is that composition, and there is now no mutual block in a
filtered export without a model beside it. **The deletion is available**: what
it needs is the recogniser and nothing else.

Two consequences to carry with it, neither of them a gate:

* **A mutual block whose model was declined leaves `mini` with nothing.** With
  `mutual_aux` gone there is no fallback, so such a file would decline where it
  used to be checked. The population is measured and it is empty of shapes: over
  the whole tree the only mutual-model declines are eleven `mutual model name
  taken` — ten of them the already-filtered copies declining on *their own*
  model, which is idempotence and not a loss, and one the deliberate
  `mutual_keying` — and Mathlib has none. §5.2's two boundaries are shapes Lean
  rejects, so a valid export cannot carry them.
* **`--no-modelgen` would lose mutual blocks.** `mini` execs the filter on its
  hot path (§1.4) and `--no-modelgen` turns that off; a raw export run that way
  would meet an unmodelled block. That is already the arrangement `mini`'s Rust
  suite is built on — it passes `--no-modelgen` and reads fixtures that are
  committed *already filtered* — so it is a property to state rather than a
  problem to solve, but it is the one thing that stops being true of `mini` the
  program as opposed to `mini` the test suite.

**What it would buy, measured where it can be.** The 1059 lines is the direct
figure. Beyond it: `mutual_aux.rs` is one of the three files
`ci/check-mutual-blackbox.sh` polices, and the reason that check exists is that
the encoder must never name a `Term`, a `Thm` or an `Ev` — a boundary that would
simply cease to have a file to be about. And the construction itself would stop
being maintained twice: this document's §1.6 and that file's header describe the
same tag-and-carrier encoding, arrived at independently, and the `W` paragraph
in each is the same paragraph — **except that they have now diverged on a real
point**, because `mutual_aux.rs` reads the block's sort off the first member and
compares nothing, where §1.6 compares with `isLevelDefEq` (§5.1). On an input
`mutual` block the two agree; on the blocks §1.7 hands the Lean side they do
not, and that is the shape of thing a second implementation is for.

The nested arc is the precedent — 2117 lines of `nested_ev.rs` deleted whole
once `mini` learned to recognise what `modelgen` had written — and the speed
argument that carried it does not transfer here (`mutual_aux` is not slow), so
the case is duplication and trust surface rather than 500×.

**And the recogniser has a measurement waiting for it.** `mini` already reads
the composed fixtures with `mutual_aux` doing the work, and everything
certifies: `nested_iota_arm` at 63 pairs / 63 `constEv` / 63 `typeEv`, waiting
empty, `gapped` 0. Those are the numbers the recogniser has to reproduce, and
they are pinned in `mini/tests/nested.rs` today.

# 8. The third construction: models from four primitives (`--prim-models`)

**Off by default, behind `--prim-models`.** Where §1's constructions remove
*nesting* and *mutuality*, this one removes the inductive declaration itself:
a plain — non-mutual, non-nested — inductive's carrier, constructors,
recursor and ι rules come out as ordinary `def`s and `theorem`s over a fixed
basis of primitive inductives,

    Eq   PSigma   Nat   PULiftP

each spliced into the output at Lean's own shape if the input lacks it,
exactly as §1.5 splices `Eq` and the quotient. The interface is §1's four
names unchanged — `T._model.self`, `ctor_j`, `rec_0`, `iota_0_j`.

**On every arm but one there are no internal declarations at all**: every
helper the construction needs is an inline subterm, so a model is exactly
`2 + 2c` declarations for `c` constructors, plus whichever basis members had
to be spliced. The exception is §8.7's graph arm — the recursive
subsingleton, the arm that took `Acc` out of the basis — which cannot inline
its recursion's *graph*, and emits eight internal declarations beside the
four. They are internal in the contract's sense (`modelgen/README.md`, "what
the contract does not say"): no consumer reads them.

The commission named the basis `{Eq, False, Sigma, Acc, Nat}` and asked for
it to be verified rather than inherited. **The basis it ended at is
`{Eq, PSigma, Nat, PULiftP}`** — `INDUCTIVE-BASIS.md` is the derivation,
and the three changes are that `False` is derived rather than primitive
(Church `∀ p : Prop, p`, with the `Sort w` eliminator from `0 = 1` plus a
`Nat.rec` family), that `PULiftP.{u} (p : Prop) : Sort u` joins, and that
**`Acc` left** — the one grant it was in the basis for, subsingleton-recursive
large elimination, is derived by §8.7's graph route at the cost of
`Classical.choice`. Lean's *elaborator*
refuses `PULiftP`; Lean's *kernel* takes it and grants it large elimination by
the subsingleton rule, and `addDeclCore` is the kernel — core crosses the same
line twice itself, for `PUnit` and `PEmpty`
(`Init/Prelude.lean:123,211`). Three corrections came out of the original
commission, the first two compiled at the pinned toolchain in
`scripts/prim-basis/Derivations.lean`:

* **the Σ must be `PSigma`-shaped** — `{α : Sort u} → (α → Sort v) →
  Sort (max 1 u v)`. `Subtype`, every structure with a `Prop` field, and
  every `Prop`-fibred pair in the encoding need a Σ over `Sort`; Lean's
  `Type`-only `Sigma` cannot give them without `PLift`, a sixth inductive.
  (`init-prelude` declares no `PSigma`, so on the corpus below it is spliced
  — the one basis splice that run needs.)
* **level pads at constructible levels are definitionally canonical, and the
  derivation table's machinery collapses.** The commission's table reached
  `Bool` through `Σ (n : Nat), n < 2` and proof irrelevance; what is actually
  emitted is simpler and stronger. `D 1 := Σ'(_ : ⊤), ⊤` with `⊤ := ∀ C :
  Prop, C → C` has every element *definitionally* equal to its canonical one
  — structure eta turns an element into a `mk` of two proofs and proof
  irrelevance closes the components — and the property survives `D (a+1) :=
  (α : Sort a) → D 1` and `D (max a b) := Σ'(_ : D a), D b`. So at a level
  built from successors and `max`es a pad never needs a transport, and a
  model with only such pads consumes **no `funext`, no `Quot`, and no
  `Eq.rec`** — 113 of the 115 models below are in that class. A pad at any
  *other* level, and the singleton route, transport (§8.1) and splice the
  §1.5 `funext` prelude for it — `PULift` and `PUnit`, the remaining two.
  Every ι theorem is `Eq.refl` regardless.

## 8.1 The three routes

**Type route** — carrier sort `w` never zero. The carrier is a `Nat`-tagged
sum of `PSigma` chains:

```text
T._model.self p⃗ := Σ'(n : Nat), F n
F ȷ̄  = constructor j's field telescope as a right-nested Σ', padded to
       exactly Sort w by a D when the levels demand it
F n  = Σ'(h : False), False.rec h   — empty, at Sort w — for n ≥ c
```

`F` is a `Nat.rec` cases tower, and the recursor is `PSigma.rec`, a
`Nat.rec` tower over the tag — **the large elimination the basis buys, and
the reason `Nat` is in it** — then `PSigma.rec` down the chain. On a
constructor application everything reduces by δβι, so ι is `Eq.refl`. The
pad level is `1` when `max 1 ℓ⃗ ≡ w` already (a `Prop` field under a `Type`
carrier — `Decidable`'s shape) and `w` itself when the carrier is
deliberately raised. At a level built from successors and `max`es the pad
is the definitionally-canonical `D`; at any other level — a bare parameter
in the gap, `PULift`'s shape — it is the **`False`-Π singleton** `(h :
False) → False.rec (fun _ => Sort ℓ) h`, at exactly `Sort ℓ` because
`imax 0 ℓ = ℓ`. That one is not definitionally canonical: its uniqueness is
`funext` at a pointwise `False.rec`, the destructor transports the applied
minor along it, and on a constructor application the proof is a closed
self-equality that the kernel's K-like reduction on `Eq.rec` erases — so ι
stays `Eq.refl` and the model splices §1.5's `funext` prelude.

What no pad absorbs is an **`imax` in a field's level** — a Π-typed field,
`Trans.mk`'s shape — because level defeq is normal-form equality and a
`max` does not subsume an `imax` term even with both sides present. What
collapses an `imax` is a never-`Prop` codomain, so such a field is stored
**boxed**: the same telescope, the codomain `S` wrapped as `Σ'(_ : S),
D 1`, unboxed by projection wherever the minor consumes it. The box pad is
the canonical `D 1`, so `unbox (box v) ≡ v` and `box (unbox y) ≡ y` hold by
βι, structure eta, proof irrelevance and function eta — no transport, no
`funext`. An `imax` sitting on a *domain* of the field's own telescope is
where the box does not reach, and that shape declines
(`tests/prim_declines.lean`'s `BoxF`).

**Prop route** — carrier sort `0`. The impredicative Church encoding
`∀ C : Prop, (∀ f⃗₀, C) → … → C`. At a `Prop` motive the dependent recursor
is the fold itself: the motive's proof argument is definitionally
irrelevant. When the export's recursor is large-eliminating, the
subsingleton rule that minted it says every field is a proposition
(non-indexed, so nothing can appear in the output type), and the recursor
extracts each field by instantiating the encoding at the field's own type —
sequentially, a later field's type instantiated at the earlier extractions,
with proof irrelevance closing the gap.

**Maybe-zero route** — carrier at a **variable** sort: `Prop` at some
instantiations and `Type` at others, `PUnit`'s and `PEmpty`'s shape. This is
the Church route under a lift. `PULiftP p : Sort u` lands at exactly such a
sort for *any* `u`, and — unlike every type the old basis could reach there —
it is **empty exactly when `p` is**. So the whole class is one construction:
the carrier is `PULiftP.{w}` of the Church encoding, the constructors are `up`
of the folds, and the recursor is the `Prop` route's with a `down` at one end.
There is no transport between them: structure eta on `PULiftP` gives
`t ≡ up (down t)` definitionally.

That is also why the pads improved. A pad at a level `dsingOk` cannot build —
a bare parameter in the gap, `PULift`'s shape — used to be the `False`-Π
singleton `(h : False) → False.rec (fun _ => Sort ℓ) h`, whose uniqueness is
`funext` at a pointwise `False.rec`. It is now `PULiftP.{ℓ} ⊤`, every element
of which is **defeq to the canonical one** at every level — structure eta
expands the element against the literal `up` that the canonical element is,
and proof irrelevance closes the `⊤` payload — so the destructor transports
nothing and the model splices no axiom.

**That is narrower than "a definitional singleton", and the difference is
load-bearing.** Eta-for-structures fires only against a side that is already
a constructor application, so `t ≡ canon` holds and `x ≡ y` for two *opaque*
inhabitants does not — the kernel refuses it even when forced past the
unifier with `@Eq.refl _ x`. It is refused as a *conversion* only: `x = y` is
provable with no axiom by routing through `up (down ·)`, where every step is
a redex, so the conversion is simply not transitive at this shape. Every use
in the construction is at a redex — the pad against `unitAtCanon`, the
maybe-zero carrier against `up (down t)` — and none compares two opaque
inhabitants, so nothing rests on the claim that fails.
`scripts/inductive-basis/PULiftPEta.lean` compiles all of it, with the two
refusals pinned by `#guard_msgs`, and records the two generator-side
mutations: routing the lift pad through its propositional transport instead
is **green** (so that branch is a working alternative nothing reaches), and
routing the `D` pad through the *lift's* transport is **red** at `Tri`,
`Opt`, `Dec` and `Big` (so the flag carries real information).

**The strong-induction fold.** A small-eliminating `Prop` that is indexed or
recursive cannot use the plain fold: a minor premise wants
`motive ι⃗_j (c_j f⃗)` where the fold offers `C ι⃗_j`, and proof irrelevance
stops identifying the two once the index moves; and a recursive minor premise
needs a carrier element to apply itself to, which the fold has thrown away.
The repair (INDUCTIVE-BASIS §3.1) is to fold at the Church *pair*

```text
Pair ι⃗ := ∀ D : Prop, (Self ι⃗ → (∀ h : Self ι⃗, motive ι⃗ h) → D) → D
```

of a rebuilt carrier element and a proof about every element at that index.
The `∀ h` is what proof irrelevance collapses; the element is what the
recursive minor premise consumes. `scripts/inductive-basis/PropArms.lean`
compiles it against `Nat.le` and `Nat.le.below` — the latter with two
parameters (one a function type), two indices (one a *proof*), and a
recursive field *followed* by a non-recursive one.

ι is `Eq.refl` on all three routes.

## 8.2 Coverage, measured on `init-prelude`

`vendor/arena-tests/good/init-prelude.ndjson` has 126 inductive types. One
(`Lean.Syntax`) is nested and is §1's business. Of the 125 simple ones,
**122 model and 3 decline**, each decline with its printed reason:

| declined | count | reason |
|---|---|---|
| `Eq`, `Nat` | 2 | the basis itself — the exemption that makes the construction well-founded |
| `Lean.ParserDescr` | 1 | a **branching** recursive constructor (`binary`, `sepBy`, `sepBy1` each take two `ParserDescr`s) — the tuple tower's spine is one `Nat`, so this needs W/path (§8.4) |

plus, on the composed side, `Lean.Syntax._model.0._model.aux` — indexed at a
never-zero sort, thesis §5.2's skeleton-plus-`good` (§8.3).

**Arm G (§8.7) does not appear in this table, and that is the honest result
rather than an omission.** `init-prelude` declares no recursive subsingleton
— no `Acc`, and no `below` beside one — so the arm that took `Acc` out of the
basis has nothing to model here. Coverage before it landed was 122 of 125 and
after it is 122 of 125, with the same three declines. What did change here is
one row that is no longer printed: `Acc` used to decline as a basis primitive
on any input that declared it, and now models. The arm is measured against
`modelgen/tests/prim_graph.lean` and `prim_graph_pre.lean` instead, and the
corpus says nothing about it either way.

**What moved, and why.** The previous tranche modelled 115 and declined 10.
Four of those ten are now models:

* **`False`** left the basis. It is Church `∀ p : Prop, p`, and its `Sort w`
  eliminator is `0 = 1` plus a `Nat.rec`-built family to transport along
  ([`Modelgen.cfalseElim`]) — so it models like any other declaration, and
  the three places the construction used `False` (the empty fibre beyond a
  tag tower, the level pad, the variable-sort carrier) use `PULiftP` of
  Church-`⊥` or Church-`⊤` instead.
* **`PEmpty`** was recorded here as *not constructible*, and that was wrong
  about the basis rather than about the type. Over `{Eq, False, PSigma, Nat,
  Acc}` every type at a bare `Sort u` is inhabited, so the claim held; it
  does not survive the sixth primitive. `PULiftP.{u} (p : Prop) : Sort u` is
  empty exactly when `p` is, and `PEmpty._model.self := PULiftP ⊥`.
* **`Nat.le`** and **`Nat.le.below`** were recorded as indexed families
  needing thesis §5.2. They do not: they are small-eliminating `Prop`s, and
  the Church encoding carries indices by quantifying `C` over the index
  telescope. What they *did* need is the strong-induction fold (§8.1).
* **`List`** and **`Lean.Name`** were recorded as needing W. They do not
  either: both are *linearly* recursive, and the tuple tower (§8.1, §8.4)
  models them with every ι rule `Eq.refl` and no axiom. `Lean.ParserDescr` is
  the one that genuinely branches, and it is the only member of that class
  left.
* **`HEq`** was the last indexed subsingleton. It models by the packed index
  equation (§8.1): the whole index telescope into one `PSigma`, one `Eq` at
  it, one `Eq.rec` to discharge it, resting on `PSigma` structure eta for
  `pack (unpack y) ≡ y`. ι is `Eq.refl`. **The arm takes any number of
  constructor fields** — it shipped bounded at one, and the bound was wrong;
  see the fixture note below, which is the honest part of this row.

`PUnit` models on the maybe-zero route, `PULift` on a `PULiftP ⊤` pad, and
`Trans` on a boxed field.

### The three oracles

Every generated declaration goes through `Environment.addDeclCore` with
checking on. §4's statement oracle runs on all of it: **280 statements
compared against the installed recursors' own rules, 0 differ**. Replaying
the whole output export from bytes, through `addDeclCore` with checking on,
accepts **2344 declarations and rejects 0** — `modelgen/EnvProbe.lean` mode
`C`, which is new; mode `A` deliberately swallows rejections because it is
asking about visibility, and nothing in the tree counted them before.

The run splices exactly two basis members, `PSigma` and `PULiftP`. It
splices **no `funext`, no `Quot.sound` and no quotient**, and no model waits
on the input's quotient any more: the `False`-Π singleton's uniqueness was
`funext` at a pointwise `False.rec`, and `PULiftP`'s is *definitional* against
the canonical element — structure eta on a single-constructor index-free
inductive, plus proof irrelevance on `⊤`, at a redex (§8.1's narrowing: not
between two opaque inhabitants, which the construction never needs). That
retired both axioms and two spliced declarations
(`PUnit`'s model went from 7 declarations to 4, `PULift`'s from 5 to 4).

Filtering the output again with the flag on declines **131 times** — 125 of
them at the name guard (123 `prim model name taken`, one nested, one mutual)
and 6 at a shape: the four basis primitives, which are all present on the
second pass because the first spliced two of them, plus `Lean.ParserDescr`
and the composed `aux`. The file comes back byte-identical — idempotence,
§1.5's mechanism unchanged. (This line used to read "declines 131 times at
the name guard", which was the right total against the wrong reason for six
of them.)

### Fixtures and mutations

`modelgen/tests/prim_shapes.lean` is one positive occupant per route
variant and `modelgen/tests/prim_declines.lean` one per refusal path with
its reason pinned by prefix, both in `Test.lean`'s table. Shapes added with
this tranche: `PE` (empty at `Sort u`), `PM` (two constructors there), `PT`
(three, with *distinguishable* field telescopes), `PF` (a field), `PI` (a
field at the carrier's own sort), `IdxP` (indexed, non-recursive) and `Le3`
(indexed *and* recursive, three constructors, whose front-end-generated
`Le3.below` is the fixture's only two-index witness); and, with the arm-F
field bound (below), `TagS4` and `Conj3`, the three-field dependent occupants
of the two sequential-extraction sites.

Three mutations were run against the new arm and each caught something a
different fixture could not:

| mutation | red | **green**, and why that is right |
|---|---|---|
| fields and induction hypotheses handed to the minor in the wrong order | `Le3` | `IdxP` — no recursive field, so the two orders are the same array |
| Pair premises handed to the fold in reverse constructor order | `IdxP`, `Le3` | `Tor` — three constructors but no indices and no recursion, so it takes the plain-fold path |
| ι stated at reversed index arguments | `Le3.below`, `Nat.le.below` | `Le3`, `IdxP` — one index cannot distinguish an index ordering |
| every step constructor given tag 0 (a non-injective tag collision) | `MNm`, `Weave` | `Lst` — one step constructor, so a collision is a no-op |
| the step constructor storing the predecessor's spine, not its successor | `Lst`, `MNm`, `Weave` | — |
| the packed index telescope unpacked in reverse | `Hq` | `IdxS`, `TagS` — one index, so reversing a singleton is a no-op |
| arm F's extracted fields handed to the minor in reverse | `TagS2`, `TagS3`, `TagS4` | `IdxS`, `TagS`, `Hq` — ≤ 1 field, so reversing is a no-op |
| arm F's extracted fields handed to the *rebuilt carrier* in reverse | `TagS2`, `TagS3`, `TagS4` | the same three, for the same reason |
| arm F's field `i` extracted as field `nf-1-i` | `TagS2`, `TagS3`, `TagS4` | the same three |
| every field's type instantiated at extraction **0** rather than at its own predecessors | **`TagS4` and `Conj3` only** | `TagS2`, `Conj` — two dependent fields, so extraction 0 *is* the only predecessor |

The third is the two-atoms lesson one dimension up, and it is why the
fixture needs a two-index family. Note also that on the Church routes ι is
`Eq.refl` **by proof irrelevance**, so an ι theorem cannot catch a
minor-order bug there at all; what catches a permutation is the minor
premise failing to typecheck, and that needs the constructors' telescopes to
differ — which is why `PT` and `Le3` are built the way they are.

### The arm-F field bound that was a bound and not a defect

Arm F shipped declining above **one** constructor field, on the strength of a
measurement recorded here as "the sequential extraction is wrong at two
fields, dependent and non-dependent alike". **Re-measured, it is not.**
`TagS2` (two dependent fields), `TagS3` (two non-dependent) and the newly
added `TagS4` (three dependent) all model: kernel-accepted through
`addDeclCore`, statements compared against the installed recursors' own
rules with zero differences, ι `Eq.refl`. The bound is gone and the three
shapes are positive occupants rather than boundary markers.

Two things are worth keeping from the episode, because neither is undone by
the bound being wrong.

* **The mutation that found nothing was still the right mutation.** Reversing
  arm F's extracted fields was green because every occupant had at most one
  field, and that is a genuine hole in the fixture set whether or not the code
  under it was broken. It is now red at `TagS2`, `TagS3` and `TagS4`.
* **Two fields are not three, and here that is measurable.** The extraction
  instantiates a later field's type at the *earlier extractions*. A version
  that instantiates every field's type at extraction 0 instead is a real bug
  and is **invisible at two fields** — with two, extraction 0 is the only
  predecessor. It is caught only by `TagS4` and by `Conj3`, the three-field
  dependent occupant added to the *non-indexed* large-eliminating route
  (`Conj`'s site, which threads fields sequentially in the same way and had
  the same two-field blind spot).

What made the difference was not re-reading the extraction but running it: the
bound was believed, the fixtures were written to hold it open, and nothing in
the tree ever asked the kernel. **A decline is a claim about the code and has
to be measured like any other.**

## 8.3 Composition: nested → mutual → primitives, and where it stops today

The chain §1.7 established gains a third step: the mutual model's own single
inductives — `T._model.tag` and `T._model.aux` — are declarations of the
output like any other, so the flag runs the construction on them too, from
both call sites (an input's plain mutual block, and the block a nested
model leaves behind). On `Lean.Syntax` the tag models — it is a plain
enumeration — and **`aux` declines as indexed**, which it always is: the tag
is its index. So the claim "layer 3 composes at the end of the chain" is
**confirmed in mechanism and bounded in coverage**: it will be whole exactly
when indexed families at a never-zero sort are (§8.4), and the decline is
recorded per run rather than asserted here. The `Prop`-valued indexed
families are done — `Nat.le` and `Nat.le.below` model — but `aux` is
`Type`-valued, so it waits on the skeleton-and-carve.

## 8.4 Plan A against plan B — what is settled and what remains

The commission's first question was whether plan A — reach the inductive
from the primitives directly, recursor as `Acc.rec` on the subterm relation
— actually differs from plan B, building W. Settled as follows.

* **For everything non-recursive, plan A is real and is what shipped**: no
  W, no `Acc`, and — for every model but the two that transport, `PUnit`
  and `PULift` (§8.1) — no `funext` either. This is 115 of `init-prelude`'s
  125 simple inductives.
* **For recursive carriers the two plans coincide at infinite branching.**
  A constructor field `f : I → T` with `I` infinite forces the carrier to
  hold every well-founded `I`-branching tree; any type the primitives build
  with a dependent eliminator over those trees *is* a W-type, however it is
  spelled, and the depth route fails exactly as the commission predicted —
  a tree of unbounded finite depths has no `Nat`-indexed approximant. The
  primitives' route to such a carrier is the path encoding
  (`derived/src/wpath.rs`'s precedent; Kha's `LFP.lean` is the Lean-side
  worked form): paths are lists, `List` is `Σ'(n : Nat), Fin n → ·` from
  the basis, `Good` is an impredicative `lfp`, and the recursor is `Acc.rec`
  on the immediate-subtree relation — which is where `Acc`, so far unused,
  enters the basis.
* **At finite branching plan A differs from plan B only in clothing.** The
  measured corpus is entirely finitely-branching (`init-prelude` has no
  reflexive inductive), and there a generic W can be avoided: every
  finitely-branching skeleton is countable and Gödel-codes into `Nat`, with
  well-formedness by `Nat`-strong-recursion. But that is `Nat` serving as a
  W-universe at countable branching — the skeleton type *is* the initial
  algebra, merely coded — at per-shape arithmetic of strictly greater
  generator complexity than one path-W instantiated per inductive, and with
  no shape covered that the path construction does not cover.

**Verdict: plan A was not impossible on the measured corpus; it is W in
disguise plus bookkeeping.** But the corpus is finitely branching, and at
*linear* recursion — every constructor with at most one recursive field, no
recursive field under a binder — there is a third answer that is neither, and
it is fully definitional: the tuple tower. `scripts/inductive-basis/
LinearRec.lean` compiles it on three targets (`List`, a `Lean.Name` copy, and
an interleaved base/step shape with fields on both sides of the recursive
one), **every ι rule by `rfl`, no `funext`, no axiom at all**. The schema is

```text
V 0     := Σ'(tag : Nat), Base_tag          -- a Nat.rec tag tower
V (n+1) := Σ'(tag : Nat), Step_tag (V n)
T       := Σ'(n : Nat), V n
```

with the spine `n` counting the recursive depth, and it needs three repairs
the naive version does not have: every chain terminated by a pad (so a
constructor whose fields are all `Prop`s still lands in `Type u`, and the
zero-field case needs no special rule); the pad being `PULiftP ⊤` rather than
`D`, since that is definitionally canonical at *every* level; and a tag tower
with zero real tags being the constant family rather than a `Nat.rec`, which
would otherwise stick on the bound tag. It genuinely cannot express a
constructor with **two** recursive fields — the spine is a single `Nat` and
`⟨r.1 + 1, …⟩` has one predecessor to take — so `Lean.ParserDescr` (whose
`binary`, `sepBy` and `sepBy1` branch) stays with plan B. That arm **is now wired up**: `List`
and `Lean.Name` model, `recSlotOf` declines the two shapes the tower cannot
express by name, and `prim_declines.lean`'s `Branch` and `Binder` hold both
refusal paths open.

Of the three classes that were declined here, two are constructions now: the
indexed **subsingleton** is arm F (the packed-index-equation model,
`PropArms.lean`'s `HEq'`, one `Eq.rec` at a `PSigma`-packed index telescope,
ι by `rfl`, resting on `PSigma` structure eta), and the **recursive**
subsingleton is §8.7's arm G. What remains is **branching** recursion at a
never-zero sort (above). `AccPhi.lean` compiled the recursive subsingleton
over a primitive `Acc`, and also refutes and repairs the thesis's own `accφ`
reduction at thesis.txt:1838; the arm that shipped does not use it.

**`Acc` no longer has to be primitive for it, and no longer is.**
`scripts/inductive-basis/AccFromChoice.lean` derives `Acc.rec`'s exact type
over no inductive primitive at all, by defining the recursion's **graph** as
an impredicative `Prop`, proving it total and single-valued by the free
`Prop`-motive recursor, and extracting the value *packaged with its graph
proof* using `Classical.choice`. Uniqueness turns ι into a theorem —
propositional rather than `rfl`, which the owner's ruling on axioms permits.
Axioms: `rec'` spends `[Classical.choice]`, ι additionally `[Quot.sound]`
via `funext` in uniqueness, and the encoding, its `intro`, its `Prop`-motive
recursor and both adequacy directions spend none. The naive route — choice
at a bare `Nonempty (motive a t)` — is compiled *as a refutation* in the same
file: the value is provably blind to the step function, so its ι rule derives
`False`, and that path must not be re-attempted. So the basis is **four plus
choice** as a design (`INDUCTIVE-BASIS.md` §4) **and four in this tool**:
`Modelgen.primBasis` is `[Eq, PSigma, Nat, PULiftP]` and the recursive
subsingleton models. §8.7 is the arm.

**And the recipe was uniform, which is what made wiring it mechanical rather
than exploratory.** Two compiled shapes are not enough to conclude that a
generator can emit this for an *arbitrary* recursive subsingleton, so
`scripts/inductive-basis/AccArmShapes.lean` carries the same nine steps
through three more, each pinned twice — once as a transcription of the
kernel's recursor type applied to the Church carrier, once applied to the
real inductive, so the transcription is checked against Lean and not
trusted. It is uniform in the *number* of recursive fields, in recursive
fields with and without binders, in non-recursive proof fields before,
between and after the recursion, in the presence and absence of a data field
that is literally the index, and in indices and parameters generally. Exactly
**two lines are shape-sensitive**, both mechanical: `Graph.unique`'s
congruence must be n-ary in the recursive fields (one `congrArg` factor
each — a single `congrArg (step x h)` is what breaks at two), and the
`funext` chain inside it runs per *binder* of a recursive field.

That second one produces a result worth having on its own: **the axiom cost
is per shape, not per arm.** A recursive field with no binders needs no
`funext`, so the degenerate shape `I1 : Prop | mk : I1 → I1` has an ι costing
`[Classical.choice]` and **no `Quot.sound`**. Totality never needs `funext`
in any shape, so `rec'` is `[Classical.choice]` uniformly and only ι ever
pays. The shapes also *discriminate*: swapping the two recursive fields of
the two-field shape, and swapping the two non-recursive proof fields that
straddle the recursion in the three-field shape, are each a type error — so
a field-order bug in the arm would be caught, which it would not be
against fields of equal type or fields on only one side. Both predictions
held: the arm's own mutations (§8.7) are red at exactly those shapes.

What remains not uniform: constructor arguments that are *data*
occurring inside the conclusion's index *expression* where the index does not
determine them. This was recorded here as "not reachable from this class,
because Lean's subsingleton rule admits only variables there" — and **that
was wrong**, as the arm's own boundary measured. The rule admits any argument
that *occurs* in the result type, so `mk : BadC 0 → BadC 0` and the `below`
Lean mints beside a recursive `Prop` (whose index is `T.mk a`) are both
large-eliminating and both out of reach; §8.7 declines them by name. The
variable-sort carriers, the bare-parameter pad, the `imax`-leveled field and
the indexed and recursive `Prop`s are constructions now, not gaps; the
`imax`-on-a-domain field is a *level-incompleteness* decline and §8.6
cross-checks it against lean4lean.

## 8.5 Cost, measured

`perf stat -e instructions`, `init-prelude`, three runs each; the shared box contends, so the first
run of a batch was discarded as an outlier (3.325 × 10⁹) and the three that
agree to 0.1 % are reported:

| | instructions | output bytes |
|---|---|---|
| `modelgen` (layers 1+2) | 2.565 × 10⁹ | 3,857,568 |
| `modelgen --prim-models` | 3.228 × 10⁹ | 4,779,318 |

**Arm G (§8.7) did not move this**, and it should not have: `init-prelude`
declares no recursive subsingleton — no `Acc`, and no `below` beside one — so
nothing there reaches the arm. Four runs at 3.227–3.229 × 10⁹, spread 0.06 %,
against 3.226 × 10⁹ before it landed; none discarded. The only change on the
measured path is that `primBasis` is one name shorter. The arm's cost is
therefore **unmeasured on a corpus** and only its fixtures exercise it, which
is worth saying rather than implying that "no change" means "cheap".

**+25.8 % instructions and +23.9 % output bytes for 123 models** (122 input
inductives and one composed tag) — about 5.4 × 10⁶ instructions per model.
Against the tranche that first landed layer 3 (3.164 × 10⁹ for 116 models)
this is **+2.1 % for seven more models**, which is the honest shape of the
change: the new arms cost the same order of work per declaration as the old
ones, and nothing in the common path got slower. Reproduce with:

```bash
cd modelgen && lake build
perf stat -e instructions ./.lake/build/bin/modelgen \
  ../vendor/arena-tests/good/init-prelude.ndjson -o /dev/null --prim-models --quiet
```

## 8.6 The level-incompleteness decline, cross-checked against lean4lean

One refusal path is **not** a type error and should not be read as one. A
field whose level keeps an `imax` on a *domain* of its own telescope — the
`BoxF` shape, `modelgen/tests/prim_declines.lean` — declines with

```text
BoxF.mk's fields reach Sort imax (imax u v) v and the carrier is
Sort max 1 u v: no pad or codomain box closes the gap
```

but the gap **is** closed at every instantiation. The planner's own candidate
pad already works semantically:

```text
max 1 (imax (imax u v) v) (max 1 u v)  =  max 1 u v      at every σ
```

Lean does not accept it, because Lean's level definitional equality is
normal-form comparison and a `max` does not absorb an `imax` it dominates
(`scripts/inductive-basis/SortPolyNeg.lean` N3). This is exactly
`INDUCTIVE-BASIS.md` §2's *sixth item*.

**lean4lean** — Lean's kernel reimplemented in Lean 4 — carries an
experimental level normalizer intended to be complete for level algebra, so
it is the right oracle for the question. Pinned at commit `3dc52e0` ("Prove
`Expr` cached flag correctness", #19), whose `lean-toolchain` we set to our
own `leanprover/lean4:v4.29.1`; checked out under `vendor-l4l/` (gitignored,
like `/vendor`). The survey below is `vendor-l4l/lean4lean/LevelSurvey.lean`,
run as

```bash
T=~/.elan/toolchains/leanprover--lean4---v4.29.1
cd vendor-l4l/lean4lean
env -u LEAN_PATH LEAN_SYSROOT=$T LEAN_PATH=$PWD/.lake/build/lib/lean \
  $T/bin/lean LevelSurvey.lean
```

It compares four judgements on each pair: `sem` (brute-force semantic
equality over all assignments in 0..4), `lean` (`Level.isEquiv`), `l4l`
(lean4lean's `Level.isEquiv'`), and `fix` (see below).

| pair | sem | lean | l4l |
|---|---|---|---|
| `imax (max u v) w ~ max (imax u w) (imax v w)` | yes | **no** | yes |
| `imax u (max v w) ~ max (imax u v) (imax u w)` | yes | **no** | yes |
| `imax u (imax v w) ~ imax (max u v) w` | yes | **no** | yes |
| `max 1 (imax u v) ~ max 1 v (imax u v)` | yes | **no** | yes |
| `max 1 u v ~ max 1 (imax u v) u v` | yes | **no** | **no** |
| `max u v ~ max u v (imax u v)` | yes | **no** | **no** |
| `BoxF` padded at `w` | yes | **no** | **no** |
| `BoxF` padded at `max 1 u` | yes | **no** | **no** |
| `max 1 u ~ max 1 (imax v u) u` | no | no | no |
| `max 2 v ~ imax 2 v` | no | no | no |

**Verdict: lean4lean is strictly more complete than Lean and still does not
rescue `BoxF`.** It buys four `imax`-distributivity laws Lean lacks; it does
not buy `max`-absorption of a dominated `imax`, which is the one law this
decline needs. So the decline stands, and it now carries the finer reason:
*rejected by a level checker that is incomplete in a way lean4lean does not
repair either*. Nothing is emitted that Lean's kernel would refuse.

**The decline stands, and since §8.6.2 it is taken one stage later.** The
planner's own level equality is complete now, so `BoxF`'s pad is *planned*
rather than refused, and the refusal comes from `addChecked` — Lean's kernel,
whose `lean::is_equivalent` has exactly the `max`-absorption gap the two
`BoxF` rows above record. The report line moved with it:

```text
before  BoxF: declined — prim model shape: BoxF.mk's fields reach Sort
               imax (imax u v) v and the carrier is Sort max 1 u v: no pad
               or codomain box closes the gap
after   BoxF: declined — prim model shape: [BoxF._model.self] rejected by
               the kernel: (kernel) application type mismatch
```

This is worth stating precisely because it is the answer to an obvious
question — *if the planner stops refusing, can the models be checked by an
unpatched kernel after all?* **No.** The two shapes the planner newly
attempts over the whole 195-file corpus, `BoxF` and `IBox`, are rejected by
the stock kernel, and they are rejected for the same reason the planner used
to refuse them. The two gaps are the same gap in two implementations; closing
the near one only moves which one you hit.

Two further findings, both from reading lean4lean's own notes and source:

* lean4lean **documents** the incompleteness as deliberate-for-now
  (`vendor-l4l/lean4lean/divergences.md`): `Level.normalize'`/`isEquiv'` is
  "an experimental new algorithm … intended to be complete for level algebra
  … currently known to be incomplete in cases where Lean's algorithm is not",
  and the plan of record is to verify Lean's original algorithm and keep the
  new one as a backburner project.
* the `fix` column of the survey is a **candidate repair**, and it turns all
  ten semantically-true pairs true while leaving both false pairs false.
  lean4lean's normal form is a map whose keys are variable sets; the `imax`
  paths leave behind entries with `const = 0` and no variables — keys that
  subsumption emptied but did not erase — and `isEquiv'` compares them
  structurally. Dropping empty entries before the comparison is the whole
  fix. This is a *reading* of `Lean4Lean/Level.lean` plus a measurement of
  the repaired predicate on the twelve pairs, not a proof of completeness,
  and it is offered upstream-shaped rather than as something this repository
  depends on.

### The repair, applied and measured

The repair was applied locally — `vendor-l4l/nanodatg-level-prune.patch`,
against `3dc52e0`, marked unmistakably as a nanodatg-local experimental delta
and not upstreamed, with the stock predicates preserved beside the patched
ones as `isEquiv'Stock`/`geq'Stock` so one binary measures both. It adds
`NormLevel.prune`, which drops entries whose node is `const = 0` with no
variables, and routes `isEquiv'` and `geq'` through it. `normalize'` is
deliberately *not* routed through it: with `paths := true` the map must be
suffix-closed and `toTree` depends on that.

Patching `isEquiv'` breaks lean4lean's own soundness theorem `isEquiv'_wf`,
so the patch carries it across rather than deleting it: a pruned entry
evaluates to `0`, so pruning does not change `NormLevel.eval`, and the
patched predicate is **as verified as the stock one was**. No new `sorry`.
(The pre-existing `subsumption_eval` sorry sits underneath both.)

With the patch, the survey's `l4lPatch` column agrees with `sem` on **every**
row: it closes four pairs stock lean4lean rejects — including both `BoxF` pad
candidates — and leaves all three semantically-false rows false. A 33,670-pair
fuzz (depth-4 random levels, three variables, oracle = every assignment in
0..4) found **0 disagreements with the semantic oracle** for the patched
predicate, against 415 for Lean and 370 for stock lean4lean, and **0**
claims-true-but-semantically-false for any of the three. `geq'` behaviour is
unchanged. That is a measurement on ~34k pairs against a bounded oracle,
**not a completeness proof**, and it is worth saying twice.

### The declaration, through all three kernels

The faithful thing was measured, not a proxy: `PULiftP` added as a raw
inductive (both kernels accept it — the maybe-zero resultant sort is an
*elaborator* refusal, not a kernel one), then the actual model carrier

```lean
def BoxF_model_self.{u,v} (α : Sort u) (β : Sort v) : Sort (max 1 u v) :=
  PSigma (fun _ : ((α → β) → β) => PULiftP.{max 1 u v} CTrue)
```

| checker | verdict |
|---|---|
| Lean's kernel | **reject** — `declaration type mismatch … has type … Sort (max (max 1 (imax (imax u v) v)) 1 u v) but it is expected to have type … Sort (max 1 u v)` |
| stock lean4lean (`3dc52e0`) | **reject** — byte-identical message |
| patched lean4lean | **accept** |

So, precisely: **the `BoxF` carrier is accepted by a repaired level checker
and rejected by Lean's normaliser and by stock lean4lean.** That is a result
about the level algorithm, and by itself it was **not** a licence to emit: the
contract is that a proof Lean's kernel rejects is a decline, never an
emission, so under a stock kernel `BoxF` **remains a decline** and
`prim_declines.lean` still pins it. §8.6.1 is what changes for a *non-stock*
kernel, and it changes only there.

### Two caveats on the lean4lean cross-check, both load-bearing

* **The version gap was checked by diff, not by rebuild.** The clone's
  `origin/master` (`1a16b72`) was 24 commits ahead of the pinned `3dc52e0`,
  and includes `#22` "use the standard library level operations" and `#23`
  "Verify the standard library universe level operations". `Lean4Lean/
  Level.lean` differs across that gap by exactly three things — a docstring,
  an `@[reducible]`, and `isEquivList` switching *away* from `isEquiv'` to
  the stock `isEquiv` — and the `Normalize` namespace (`normalize`, `Node`,
  `NormLevel`, `isEquiv'`, `geq'`) is **byte-identical**. So the survey's
  rows cannot move across the gap; the function under test is the same
  function. `origin/master` needs `v4.33.0-rc2`, which is not installed, so
  it was not rebuilt.
* **lean4lean's own replay tool could not be run.** `lake exe lean4lean Init`
  segfaulted on that clone — *before* the patch as well as after, confirmed by
  reverting to stock and reproducing — most plausibly because the clone's
  `lean-toolchain` was retargeted from upstream's to our `v4.29.1`. So `lake
  build` (150 jobs, clean) and the re-proved soundness lemma were the whole of
  the sanity check; nothing exercised the patched checker over a large real
  corpus. That was the weakest link in the cross-check, and §8.6.1 is what
  removed the need for it: the replacement now runs inside Lean's own kernel
  over the whole corpus.

## 8.6.1 The repair, in Lean's actual kernel, at run time

The cross-check above answers "is the gap real and would a better algorithm
close it" with a *second* checker. `modelgen/interpose/` answers it with the
**first** one: it rewrites Lean's level comparison in the running process, so
the model can be planned and checked by Lean itself rather than argued about
against a reimplementation. Two things come out of that, and the second was
not expected.

### What it is

A shared object, `modelgen/interpose/levelhack.so`, built by `cc -shared` from
two C files and needing no Lean headers or libraries. Loaded by
`Lean.loadDynlib` — a plain `IO` action — or by `LD_PRELOAD`. Its ELF
constructor reads the host executable's own `.symtab` out of `/proc/self/exe`,
finds Lean's level functions, `mprotect`s `.text` writable, and rewrites the
four-byte relative displacement of **selected call sites** so they land on a
replacement. `modelgen --interpose-levels SO` is the supported entry point.

Call sites and not the function prologue, because that leaves each original
byte-identical and callable at its own address. The replacement is therefore
a strict one-sided extension,

```text
hook(u, v)  =  stock(u, v)  ||  complete(u, v)
```

where `stock` is Lean's untouched code and `complete` is a decision procedure
for the level algebra (`modelgen/interpose/level_algebra.h` carries the
algorithm and its correctness argument: push `imax` down until its second
argument is a variable, case-split on whether that variable is zero, and
compare canonical `max`-of-`var + k` forms at the leaves). Everything Lean
accepts is still accepted by Lean's own code, and every *new* acceptance is
counted and reported.

### The finding that was not expected: it took two layers, not one — and now takes one

`modelgen`'s §8.6 decline is **not** a kernel refusal. It is taken by the
planner, in `Modelgen/Simple.lean`, which asks whether the candidate pad
`max (max 1 ℓ⃗) w` equals the carrier's `w`. It used to ask that with
`Lean.Meta.isLevelDefEq` — the **elaborator's** level equality, compiled
Lean, a *different function* from the kernel's C++ `lean::is_equivalent` and
with its own incompleteness. So, as measured when this section was written:

* with the **kernel alone** patched — `lean::is_equivalent`, `lean::is_geq`,
  reachable as `NANODATG_LEVELHACK_META=0` — the corpus did not move at all.
  Measured over 193 files (`vendor/arena-tests` plus `modelgen/tests`,
  `--prim-models`): **193 of 193 exports byte-identical**, 0 reports changed,
  and **0 escapes** anywhere. Not merely "no decline closed": the kernel's
  level comparison never once had an opinion the stock one lacked, because the
  planner refused first and the offending level never reached `addDeclCore`.
* with `Lean.Meta.isLevelDefEq` patched **as well**, `BoxF` is planned, and
  then the (also patched) kernel accepts it — and only then do kernel escapes
  appear at all. The kernel gap is downstream of the elaborator gap.

**The elaborator layer is no longer one of the two.** `Modelgen.LevelAlgebra`
ports the `level_algebra.c` decision procedure into Lean and the planner
consults it directly (§8.6.2), so the planner's own level equality is
complete without anything being interposed. Re-measured on
`tests/prim_declines.ndjson` with the kernel-only patch:

```text
NANODATG_LEVELHACK_META=0, control planner   BoxF: declined — … no pad or
                                                   codomain box closes the gap
NANODATG_LEVELHACK_META=0, complete planner  BoxF: model of 4 declarations
```

The `193 of 193` null above was therefore a statement about the *planner*,
not about the kernel: the kernel's opinion was unreachable because nothing
ever asked it. Ask it, and one layer is enough. What remains load-bearing is
the **kernel** half — six call sites, all in C++ — and the elaborator half,
which is the half that needs an unstripped, statically-Lean-linked host, can
be dropped.

Six call sites are rewritten for the kernel and three for the elaborator; the
banner names each. Deliberately left alone: `lean::is_geq_core`'s recursion
into `lean::is_geq`, and `Lean.Meta.solve`'s recursion into
`lean_is_level_def_eq`. Those are the stock algorithms' own internals and
`stock` has to keep meaning what Lean does.

Only the named callers' own byte ranges are scanned for those nine sites, not
all 135 MB of `.text`. The first version scanned the whole section once per
target and cost about 5 G instructions at load — it more than doubled a short
`modelgen` run. As it stands the flag costs **+2.7 %** on `init-prelude`
(3.465 G → 3.558 G instructions, two runs each), and that is a fixed cost:
parsing the host's symbol table, not comparing levels.

### `BoxF`, closed

```text
stock       BoxF: declined — prim model shape: BoxF.mk's fields reach
                  Sort imax (imax u v) v and the carrier is Sort max 1 u v:
                  no pad or codomain box closes the gap
interposed  BoxF: model of 4 declarations
            statements: 9 compared against the installed recursors' own
                        rules, 0 differ
```

The census for that run: `Meta.isLevelDefEq` 9 calls, **1** decided only by
the interposition — the pad; `is_equivalent` 9 calls, **4** decided only by
the interposition, one of which is the probe, so **3** were the model itself;
`is_geq` 17 calls, **0** escapes.

### What moves, over the whole corpus

193 files (`vendor/arena-tests` plus `modelgen/tests`), `--prim-models`, stock
against interposed, comparing the **exports byte for byte** and not only the
report:

| | |
|---|---|
| exports byte-identical | **189** |
| exports differing | **4** — and they are exactly the four with a real escape |
| reports differing | **1** — `prim_declines`, `BoxF: declined` → `BoxF: model of 4 declarations` |

The other three — `init-prelude`, `perf/grind-ring-5`, `prim_shapes` — model
and decline exactly the same declarations and produce a **smaller** export
(`init-prelude` 4,779,318 → 4,777,140 bytes). The planner reached the same
answer by a cheaper route: `isLevelDefEq raw w` now succeeds where stock needed
a pad, so the padding declaration is not written.

Every run also carries a floor of **2** escapes that are the take-verification's
own two probes, one per layer; the four interesting files show 6.

So `init-prelude` *does* exercise the gap. §8.6 used to say it contained no
`BoxF`-shaped declaration and that the fixture existed precisely to hold the
refusal path open; the first half of that was wrong. What `init-prelude`
contains is a six-universe `imax` chain,

```text
max 1 (imax u₄ (imax u₃ (imax u₂ (imax u₅ (imax u₁ u₀)))))  (max 1 u₅ u₄ u₃ u₂ u₁ u₀)
  ~  max 1 u₅ u₄ u₃ u₂ u₁ u₀
```

on which Lean's normaliser is incomplete for exactly the same reason. It is not
a *decline*, because the planner has a fallback there; it is a comparison Lean
gets wrong and the corpus absorbs.

### What moves on Mathlib

`pre-10000000.ndjson` (538 MB, 10 M lines), `--prim-models`:

| | stock | interposed |
|---|---|---|
| models / declined | 1,668 / 45 | **1,668 / 45** (identical) |
| export | 588,631,425 B | 588,575,119 B |
| `is_equivalent` calls / escapes | — | 25,077 / **19** (1 the probe) |
| `is_geq` calls / escapes | — | 5,101 / **0** |
| `Meta.isLevelDefEq` calls / escapes | — | 1,437 / **7** (1 the probe) |

So on a real Mathlib prefix the gap is hit **24 times**, the models get slightly
cheaper pads for 56 KB, and **no decline closes** — because none of Mathlib's
declines are level-arithmetic ones. The only decline this repair is known to
close is the one `prim_declines.lean` was built to hold open.

### Soundness, measured

A more complete procedure accepts strictly more, so the number that matters is
*false accepts*: pairs the procedure calls equal that a semantic oracle refutes.
Note the asymmetry — an oracle that finds a counterexample has settled the
question, an oracle that finds none has settled nothing — so the false-accept
count is exact and the "missed" counts are upper bounds.

Fuzz, random levels, oracle = every assignment over a bounded range, run
in-process against the real `lean::is_equivalent` and `lean::is_geq`:

| pairs | depth | vars | replacement FALSE ACCEPTS | replacement missed | Lean `is_equivalent` missed | Lean `is_geq` missed |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2,000,000 | 4 | 3 | **0** | 0 | 1,699 | 25,950 |
| 1,000,000 | 4 | 3 | **0** | 0 | 828 | 12,948 |
| 1,000,000 | 5 | 4 | **0** | 0 | 189 | 12,434 |
| 500,000 | 6 | 3 | **0** | 0 | 205 | 9,681 |
| 500,000 | 3 | 3 | **0** | 0 | 592 | 4,385 |
| 500,000 | 6 | 5 | **0** | 0 | 49 | 6,951 |
| 300,000 | 4 | 6 | **0** | 0 | 19 | 2,101 |
| 200,000 | 8 | 3 | **0** | 0 | 70 | 4,763 |

**6,000,000 pairs, zero false accepts, zero `LA_UNKNOWN`** — the latter being
the resource-cap answer, which would have fallen back to stock. Lean's own two
functions also had zero false accepts everywhere, as they must; where they
differ from the replacement is the two rightmost columns, and the `>=` column
is the larger gap by an order of magnitude.

Two honesty notes on that table. The `missed` column is zero only once the
oracle is wide enough: at three variables an oracle over `0..4` — the one §8.6's
lean4lean fuzz used — reported 99 spurious `>=` "misses" per 200,000 pairs,
because `4 >= w` holds on `0..4` and fails at `5`; widening to `0..12` took them
to zero. At four or more variables the range has to shrink again to keep the
point count bounded and the artifact returns: 45 spurious misses at five
variables over `0..4`, **0** over `0..8`, same pairs. And: **this is a
measurement against a bounded oracle, not a completeness proof**, which is worth
saying twice and is said twice.

A third, from §8.6.2's re-run: **`zero LA_UNKNOWN` is a property of this
sample, not of the procedure.** The table above spends 200,000 of its six
million pairs at depth 8; a flat sweep of 250,000 over every depth 3–8 and
every variable count 3–6 spends a million there, and the arena cap does then
fire — **46 pairs**, all at depths 6–8, all in `≥`, 26 of them at depth 8 with
six variables. That is the cap behaving as designed: `LA_UNKNOWN` is "no
opinion", the caller falls back to stock, and nothing unsound follows. It is
worth stating because "zero `LA_UNKNOWN`" invites the reading that the caps
are unreachable, and they are not — they are merely out of reach of the
levels a real declaration produces.

### The claim this costs

Under `--interpose-levels`, "checked by Lean's kernel" is false for anything
that only passed because of an escape. So the flag is off by default; the load
prints a banner naming every rewritten call site; the exit prints a census
splitting every level comparison into *accepted by stock*, *accepted only under
interposition*, and *rejected by both*; and the load **fails hard** unless both
the kernel's verdict and the elaborator's verdict on the §8.6 witness observably
flip from reject to accept. Not "`mprotect` returned 0" — an observed change in
what Lean answers. An interposition that quietly did nothing and let the run
continue would be the tenth instance of `DECISIONS.md` 2026-08-08's "a check
reporting success having done nothing", and the take-verification exists to make
it unreachable.

That check earned itself twice during construction. The first witness used
`PUnit`, which is not in `modelgen`'s `importModules #[] {}` environment, so the
verdict failed to flip for a reason that had nothing to do with the patch. And
the check was first written as a `Bool`-valued *pure* function of the
environment — which it is not, that being the entire point — and Lean's compiler
duly evaluated the before and after calls once, reporting "no flip" on a run
where the flip had happened. Both were caught by the refusal, not by anyone
reading a log.

**`nanodatg`'s own `kernel/` is untouched.** The thing rewritten here is Lean's
C++ kernel inside the `modelgen` process; the Rust trusted computing base is not
involved and is not modified.

### The dependency, stated

The kernel's level functions are **local** symbols (`nm` type `t`), absent from
`.dynsym`. `LD_PRELOAD` symbol interposition cannot reach them — there is no PLT
indirection to hijack — which is why the addresses are read out of `.symtab`
instead. So this works only on a host that is **unstripped** and links Lean
**statically**. The shipped `libleanshared.so` is stripped of local symbols, so
the `lean` CLI cannot be patched this way at all; `modelgen` and Lake
executables generally can. On a host it cannot patch, the library aborts the
process with a diagnostic rather than loading and doing nothing — which is also
why its constructor clears `LD_PRELOAD`, since `Lean.findSysroot` shells out to
that same unpatchable `lean`.

Nothing is hardcoded except the **mangled symbol names**; addresses are resolved
at run time, so rebuilding the host is fine, and a Lean release that renames or
inlines any of the five will make the load fail loudly rather than silently.

### Can lean4lean be dropped? Yes — use and mention

**Use: already gone.** `vendor-l4l/` is not in the tree (it was gitignored, like
`/vendor`), and nothing in the repository builds, runs, or links lean4lean.
What survives is the record: `scripts/inductive-basis/lean4lean-level-prune.patch`
and `scripts/inductive-basis/LevelSurvey.lean`.

**Mention: keep the survey, drop the dependency.** The survey table above is a
true measurement and is the reason anyone believed the gap was real; it stays.
What lean4lean was *for* — an oracle for "would a better algorithm close this,
and is the repair sound" — is superseded on every axis by the interposition:
the replacement runs inside Lean's own kernel rather than beside it, is measured
at 6 million pairs rather than 33,670, and is exercised over the whole corpus,
which is exactly the thing §8.6's second caveat said had never been done.

One thing lean4lean still has that this does not: **a proof**. The prune patch
carried `isEquiv'_wf` across, so its soundness was as machine-checked as stock
lean4lean's. `level_algebra.c` is C with a written correctness argument and six
million measured pairs, and that is a weaker kind of evidence. If the project
ever wants the level repair *proved* rather than measured, lean4lean is where
that work would go, and the prune patch is the head start.

## 8.6.2 The planner's own level equality, complete, with no interposition

§8.6.1 needed to patch two layers because the planner asked its level
questions with `Lean.Meta.isLevelDefEq`. Three calls in `Modelgen/Simple.lean`
and one in `Modelgen/Mutual.lean` — our own lines, asking a question about our
own construction. Nothing about them needs `mprotect`, an unstripped host, or
a loaded `.so`: they can simply call a complete procedure.

`Modelgen/LevelAlgebra.lean` is that procedure, a port of the `imax`
case-split decision procedure in `interpose/level_algebra.c`, working over a
private AST so that Lean's simplifying smart constructors cannot interfere
with the algorithm's invariants. `LevelAlgebra.isLevelDefEqComplete` is what
the planner calls.

### The elaborator gets first refusal, and that ordering is the whole design

The obvious shape — ask completely, everywhere — is **wrong, and was measured
wrong**. A level equality that only the complete procedure can see is one
**Lean's kernel cannot see either**. So a plan reached by the complete
procedure is a plan `addChecked` rejects, and reaching for it *first* trades a
plan that works for one that does not:

| `init-prelude` | models | declines |
|---|---|---|
| control (`NANODATG_PLANNER_STOCK_LEVELS=1`) | 125 | 4 |
| complete procedure asked **first** | **124** | **5** |
| complete procedure asked as a **fallback** | 125 | 4 |

`Trans` is the declaration in the middle row. Its bare chain is one the
complete procedure equates to the carrier and the stock kernel does not, so it
took the unboxed plan and was rejected — where the elaborator's own refusal
had sent it to the boxing retry, which the stock kernel accepts.

So the planner runs its whole three-question cascade with `isLevelDefEq`
first, bare levels then boxed, and only if all of that fails does it run the
same cascade again with the complete procedure. Every declaration that models
today models by the route it took before; the complete procedure is consulted
only where the alternative is a decline. `isLevelDefEqComplete` is likewise a
*widening* — it returns the elaborator's answer whenever that is `true`, so
`unknown` needs no special handling and level metavariables, which it cannot
assign and the elaborator can, are decided entirely by the elaborator.

### What moves: nothing, and that is the measurement

195 files (`vendor/arena-tests` plus `modelgen/tests`), `--prim-models`,
control against the same binary:

| | control | complete |
|---|---|---|
| exports byte-identical | — | **195 of 195** |
| models / declines | 893 / 228 | **893 / 228** |
| escapes | 0 | **2** |

`init-prelude` is 125 / 4 either way, and its export is byte-identical. The
`pre-10000000` Mathlib prefix is 1,686 / 36 either way with **zero** escapes —
the complete procedure never once had an opinion the elaborator lacked there.
Cost is **+0.009 %** on `init-prelude` (3.2329 G → 3.2332 G instructions);
the fallback runs only after a decline would otherwise be taken, so there is
almost nothing to pay for.

The two escapes in the whole corpus are `BoxF` and `IBox`, and **neither
closes a decline** — each moves one from the planner to the kernel (§8.6). A
run reports its own census, always, because zero is as often the interesting
number:

```text
levels: 3 planner comparisons, 1 escapes
levels: escape  max (max 1 (imax (imax u v) v)) 1 u v  ≡  max 1 u v
```

`NANODATG_PLANNER_STOCK_LEVELS=1` is the control and
`NANODATG_PLANNER_LEVEL_TRACE=1` prints each escaping pair, mirroring
`interpose.c`'s `NANODATG_LEVELHACK=off` and `_TRACE` for the same reason: an
A/B should be a property of one binary, not of two builds.

### What it buys: one layer instead of two

Coverage does not move, so the case for the change is not coverage. It is
that **the elaborator half of the interposition is no longer load-bearing**.
With the planner complete, a kernel-only patch closes `BoxF`, where before it
moved nothing at all (§8.6.1's `193 of 193`). The half that is dropped is the
half that needs an unstripped, statically-Lean-linked host.

### The port is fuzzed at the C's own scale

A translation inherits no measurements, so `LevelFuzz.lean` re-runs §8.6.1's
experiment against the port: **6,000,000 pairs**, depths 3–8 over 3–6
variables, 24 configurations, scored against the same bounded semantic
oracle. **0 false accepts**, in both `≡` and `≥`.

`interpose/fuzz_ref.c` drives the C over the *identical* pair stream — same
xorshift64 seed, same generator, left-to-right sequenced so the stream is not
a property of the C compiler — and prints an FNV-1a digest of its verdict
stream. Digests agree on **17 of the 24** configurations. The 7 that differ
are exactly the 7 where the C's arena cap returns `LA_UNKNOWN`: **46 pairs**,
all of them in `≥`, which the planner never asks. The port has no arena and
decides those 46, consistently with the oracle. For equivalence — the
operation the planner actually uses — the port and the C agree on all
6,000,000.

The same fuzz refutes the one other candidate for a second incompleteness.
`Level.isNeverZero` gates the planner's route selector (`Simple.lean`), and it
is a *structural* test where `laGeq ℓ 1` is a complete one. Over the same
6,000,000 levels they disagree **0 times**. It is not a gap, and the four
call sites really were the whole of it.

## 8.7 Arm G: the recursive subsingleton, by the graph — and `Acc` leaves the basis

The class: an inductive `Prop` with **one** constructor, each of whose fields
is a proposition — possibly a recursive occurrence `∀ z⃗, T p⃗ e⃗` — or a piece
of data that occurs in the conclusion. Lean's kernel grants that shape a
`Sort v` motive by the subsingleton rule, and that grant is made to the
*declaration*: the Church carrier §8.1 already emits eliminates only into
`Prop`, so the large eliminator has to be **built**. `Acc` was in the basis
for exactly this, and this arm is what took it out. `Modelgen.primBasis` is
now `[Eq, PSigma, Nat, PULiftP]`.

### What is emitted

The carrier and the constructor are the Church route's own — they cost no
primitive at all — and so is `T._model.ind`, the free `Prop`-motive recursor,
which is *literally* the strong-induction fold of §8.1 at `v := 0`: the arm
forces the small-elimination branch and takes the result as `ind` instead of
as `rec_0`, so there is one fold in the source and not two to keep in step.
On top of that, seven declarations define the recursion by its **graph**:

```text
T._model.graph          Graph ι⃗ t val — the least relation closed under
                        "if the value at every recursive sub-argument is g,
                        then the value at (mk f⃗) is step f⃗ g⃗", encoded
                        impredicatively, so a Prop
T._model.graph_mk       that closure rule, as a theorem: the graph is a fixed
                        point and not merely a pre-fixed point, which is what
                        makes ι's right-hand side a graph point
T._model.graph_inv_ty   inversion, with the constructor's proof fields
                        universally quantified rather than existentially
T._model.graph_inv      inversion holds, by folding at `Graph ∧ GraphInv`
T._model.graph_unique   single-valuedness, by `ind`
T._model.graph_exists   totality, by `ind`, picking sub-values with choice
T._model.rec_graph      the graph fact about `rec_0`
```

and then `rec_0 … t := (Classical.choice (graph_exists … t)).fst` and
`iota_0_0` from `graph_unique`. Twelve declarations in all, four of them the
interface and eight internal. `scripts/inductive-basis/AccFromChoice.lean`
is the derivation and `AccArmShapes.lean` the uniformity argument; §8.4 has
both.

**Universal quantification over the proof fields is the clause that
generalises.** Inversion cannot produce the fields the constructor was
applied to — it has no existential to open — so `GraphInv` quantifies them
and the caller supplies its own. Any two are definitionally equal (they are
proofs of one proposition), so `step f⃗ g⃗` and `step f'⃗ g⃗` are the same term
and the `rfl` at the bottom of `Graph.inv` typechecks. Nothing in the arm
transports along a proof.

**Do not choose at `Nonempty (motive a t)`.** It typechecks, it is total, it
is universe-correct, and it is *wrong*: the two `Nonempty` proofs are
definitionally equal, so the value cannot see the step function, and the
resulting ι rule derives `False`. That is compiled as a refutation in
`AccFromChoice.lean` §4 (`naive_value_indep` is `rfl`). Pairing the value
*with its graph proof* is the whole of the difference.

### ι is propositional here, and only here

The recursor's value is a `Classical.choice` application, which reduces to
nothing, so `iota_0_0` is proved rather than being `Eq.refl`: both sides are
graph points at the constructor and the graph is single-valued. The
*statement* is the shared one — §4's oracle rebuilds it from the installed
recursor's own rule and compares it syntactically, exactly as for every other
arm — so nothing about the contract moves. What moves is that a consumer
recomputing an ι rule *by reduction* rather than reading the theorem is wrong
on this arm. `modelgen/README.md` says so where a consumer will read it.

### The axioms, per shape

| | `rec_0` | `iota_0_0` |
|---|---|---|
| a recursive field **with** binders (`Acc`'s own shape, `G2`, `G3`, `G4`, `G5`) | `Classical.choice` | `Classical.choice`, `funext` (so the quotient and `Quot.sound`) |
| a recursive field with **no** binders (`G1`, `Inf`) | `Classical.choice` | `Classical.choice` |

**And that bill is now payable rather than merely stated.** For a while the
`Classical.choice` in this table read as a *refusal* — the checker's `Sealed`
rejects hypothetical theorems and a choice function is never unique, so
`define` cannot introduce one, so a model spending it was modelled and not
certifiable. That reading was narrower than it looked: the kernel has choice
(`Thm::ax_choice`, set-sized, no consistency cost); what was missing was a way
to **name a witness**, and a **0-ary Henkin constant** — from `⊢ ∃y. φ` with
`FV(φ) ⊆ {y}` — is conservative even over the schemes, because a constant is a
parameter. Skolemising at arity ≥ 1 would not be, since `ax_replacement` takes
an arbitrary `Formula` and a Skolem function need not be amenable. Carneiro
fixes one `ε` on one set, which is that shape exactly. So the price this
section paid to take `Acc` out of the basis is **refunded**, not re-priced,
and §8.16 depends on the refund at exactly one place: `Acc`'s own model, which
every W target's fragment carries.

`funext` is reached from exactly one place — `Graph.unique`'s congruence, to
equate two recursive-argument *functions* pointwise — and
[`Modelgen.funextUp`] runs it once per binder, so at zero binders it is the
identity and nothing is asked for. Totality never needs it in any shape. The
splice is lazy, so this is visible in the report rather than inferred:
`prim_graph.lean`'s `G1` splices `PSigma`, `Nonempty` and `Classical.choice`
and **not** the quotient, and `G4` — the next shape, which does have a
binder — splices the quotient, `Quot.sound` and a derived `funext`. The
counts in `Test.lean` pin it: `G1` is 15 declarations and would be 16 under a
per-arm `funext`.

**`Nonempty` is not a sixth primitive.** It is named because it is
`Classical.choice`'s own domain and there is no way to state the axiom
without it. It is not on `primBasis`, needs no exemption to keep the
construction well-founded, and self-models: it is a non-recursive,
small-eliminating `Prop`, and `prim_graph_pre.lean` emits its model beside
the declaration. What it does cost a consumer is one ordinary inductive
declaration and one axiom beyond the four.

### The boundary, and a correction to §8.4

The arm needs the constructor's **data fields to be the conclusion's indices,
one for one**. `GraphInv ι⃗ t val` concludes `val = step f'⃗ g⃗`, whose
right-hand side lands at the quantified fields' own index expressions; for
that equation to be statable at an arbitrary `ι⃗`, those expressions have to
*be* `ι⃗`. So the arm declines an index that is a constant, or one built from
a field rather than being one.

§8.4 recorded this class as "not reachable, because Lean's subsingleton rule
admits only variables there". **That was wrong**, and the arm's own fixtures
are what measured it: the rule admits any argument that *occurs* in the
result type, so

* `BadC : N → Prop | mk : BadC N.z → BadC N.z` — index a constant — is
  large-eliminating and declines, and
* the `below` Lean mints beside every recursive `Prop` (`Inf.below`,
  `G1.below`, `Ac.below`, …) is a recursive subsingleton whose index is
  `T.mk a` — a proof field inside an index expression — and declines too.

Both are in the fixtures with their printed reason. A data field that occurs
*inside* an index expression without being it — `mk : (x : Nat) → BadD x →
BadD (x+1)` — never reaches the arm at all: Lean gives that one a `Prop`
motive, so it is small-eliminating and takes the strong-induction fold.
Asked of the kernel, not reasoned about.

### Fixtures and mutations

`modelgen/tests/prim_graph.lean` is the arm's positives — `G1` (no
parameters, no indices, a recursive field with no binders), `Ac` (`Acc`'s own
shape, universe-polymorphic, one data field that is the index, a recursive
field under two binders), `G2` (**two** recursive fields at *different*
domains), `G3` (a proof field on **both sides** of the recursive one), `G4`
(the `accφ` shape, where the relation itself depends on an earlier proof
field) and `G5` (**three** indices, the data fields mapping onto them by a
permutation) — plus `BadC` for the refusal. `prim_graph_pre.lean` is the same
arm on an input carrying `PSigma`, `Nonempty` and `Classical.choice` itself.
`Inf`, which `prim_declines.lean` carried as a refusal until this arm landed,
is now a model there.

Six mutations, each red, and the **green** column is what the shapes were
chosen for:

| mutation | red | **green**, and why that is right |
|---|---|---|
| `Graph.unique`'s congruence truncated to one factor | `G2` | every one-recursive-field shape — with one factor the chain *is* the whole congruence |
| the `funext` chain run once instead of per binder | `Ac`, `G2`, `G3`, `G4`, `G5` | `G1` — no binder, so the chain is the identity either way |
| the recursive fields' equations used in reverse order in the congruence | `G2` | every one-recursive-field shape — reversing a singleton is a no-op |
| the proof fields handed to `GraphInv` in reverse | `G2`, `G3`, `G4` | `Ac`, `G1`, `G5` — exactly one proof field, so reversing is a no-op |
| arm G's ι falling back to `Eq.refl` | every arm-G shape (`Inf`, `Ac`, `G1`–`G5`) | — this is the compiled `#guard_msgs (error)` of `AccFromChoice.lean` reproduced in the generator |
| the data-field ↦ index map replaced by the identity | **`G5` only** | `Ac`, `G2`, `G3`, `G4` — one index, so the map is the identity already; `G1` has none |

The last is the two-atoms lesson at its sharpest: five of the six shapes
cannot see the bug, because with a single index every field↦index map is the
identity. `G5` exists for that row and for nothing else, and it needs
**three** indices rather than two — with two, a wrong map is a transposition
and half the shapes still typecheck.

Two notes on how the red/green columns were read, because the first reading
was wrong and the correction is the kind that hides. **A decline moves the
splice**, so comparing "declaration count per model" across a mutation
reports shapes that did not break: when `G1` declines, the `PSigma` it was
splicing falls to the next model that needs it and that model's count
changes. The columns above are from a name-only comparison for that reason —
`N`, the `Type`-route control, appeared to break under the ι mutation and
does not. And the second reading is that the arm-G shapes are the *only*
models any of these six touch: no mutation of this arm moved `P`, `Idx`, `N`
or any of `prim_shapes`, which is what says the arm is additive.

## 8.8 Does W subsume this arm? No — W is built on it. And what `derived/` already has

Two questions were put to this tranche, and both deserve an answer *before*
anybody writes a W arm, because the answers move where that arm starts.

### Arm G is W's prerequisite, not a special case of it

The worry was that arms are being written that a general W construction will
subsume. It is the right worry — but it does not reach this one, and the
reason is structural rather than a judgement call. **W's well-foundedness is
`Acc.rec` on the immediate-subtree relation.** A W arm at the type target
needs that eliminator; `Acc` is no longer a primitive; and arm G is what
gives `Acc` a model, which is what entitles the W arm to use the real `Acc`
and its definitional ι (§8.10). Deleting arm G in favour of W would leave W
with nothing to recurse on. That is also why the order was `Acc` first: not
sequencing
preference, dependency.

Two further points, and the first is a **correction to the brief that
commissioned this**, which named "arm G, the tuple tower" as one thing and
described it as claiming "definitional ι and no axioms". Those are two
different arms with opposite properties:

| | carrier's sort | ι | axioms | subsumed by W? |
|---|---|---|---|---|
| the **tuple tower** (`recSlotOf`, §8.4) — linear recursion | never-zero | `Eq.refl` | none | **plausibly yes, in coverage** — linear recursion is W at one-place branching. The trade is real and measurable: W would replace a definitional ι with a propositional one and add `Classical.choice`. |
| **arm G** (§8.7) — recursive subsingleton | `Sort 0`, large-eliminating | *propositional* | `Classical.choice`, and `funext` per binder | **no** — see above, and below |

So the deletion test the brief describes — "keep it only on a measured
difference, and axiom-freedom is not that difference" — applies to the tuple
tower, where it bites, and not to arm G, where the arm is load-bearing for
the thing that would replace it.

The second point is independent evidence, and it comes from our own set-side
translation: **`derived/` is W-based for class (T) and abandons W for class
(S)** — the subsingleton — which is exactly arm G's class.
`derived/src/inductive/family/le.rs:1` states it: "Class (S) — §5.3's
subsingleton eliminators, as `acc` at a Separation". A construction that
already went general on the set side still keeps a separate arm here. That is
not proof that no W-shaped construction could serve, but it is the strongest
prior available and it was paid for.

### `derived/src/inductive/` — read before designing W, and read carefully

The suggestion that we already have the full translation, "just phrased in
terms of sets rather than types", is **substantially right and wrong in three
specifics**. It was verified against the code rather than inherited; the
citations are to the master checkout.

**Right.** There is a large, mostly-general inductive translation:
`derived/src/inductive.rs` plus 23 modules and a 22-module `family/` subtree.
It consumes a `DeclSpec` (`spec.rs:241–243`: `params`, `ctors` in declaration
order, and `spec.rs:242` verbatim — "The empty list is `Empty`") and produces
carrier, constructors, recursor and ι. The class-(T) carrier really is a W:
`machine.rs:43` imports `crate::wtype::Wtype`, `machine.rs:74–76` holds it,
and `carrier.rs:18–21` gives the decomposition in four lines — per-constructor
Σ-telescopes over the non-recursive fields summed into the tag `A`, a `rec₊`
dispatch on the tag's injections for the fibre `B`, `carrier := W(A, B, u)`.
The recursor packs Lean's `n` minors into **one** step set by Replacement
(`step.rs:14–24`) and keys ι on the tag (`recursor.rs:26–37`, `iota.rs:3–7`),
in Lean's declared field order via `Slot` (`spec.rs:161`). Indexed families
are exactly skeleton-plus-`good`: erase the indices, translate, recurse a
second time over the same skeleton at `𝒫(Idx(p⃗))`, then carve by Separation
(`family.rs:6–19`). **All of that transfers**, and it is the plan the W
tranche should re-target rather than reinvent — including its decline list,
which is a coverage map somebody already paid for (`spec.rs:110–121` nesting
and mutual unrepresentable; `family/spec.rs:57–65` an index mentioning a
recursive field; `family/le_index.rs:69–80` a recursive class-(S) declaration
at `ni ≥ 1`, "no witness anywhere"; `distinct.rs:53–77` injectivity at a
function-typed recursive argument, a named gap).

**Wrong in three specifics**, each of which would have mis-set the W arm's
expectations:

* **"Sets have no analogue of universe levels."** They do, pervasively.
  `derived/src/inductive/family/universe.rs:1` states `ind(p⃗,x⃗) ∈ Uₙ` "at any
  rung of the tower", `universe.rs:48–50` reads the rung off the resultant
  sort (`⟦Sort ℓ⟧ = U_ℓ`), and the (S)/(P)/(T) trichotomy is itself keyed on
  the resultant level (`INDEXED-DESIGN.md:86–92`). What has no set analogue is
  narrower and worth stating precisely: a Lean carrier must land in a
  *specific* `Sort`, so `PULiftP`, the pads and the `imax` field boxing exist
  to hit a level exactly. Levels are not absent from `derived/`; *level
  arithmetic on the carrier's own sort* is.
* **"Sets use well-founded recursion over `∈`."** They do not. The reduction
  principle is W-induction: `W` is the intersection of all closed subsets of a
  bound (`wtype.rs:1–11`, `wtype.rs:69`) and the recursor is
  totality-by-union-of-attempts over that (`wrec_total.rs:1–12`), which needs
  a *set* bound rather than rank or transfinite recursion (`rec_acc.rs:19–25`).
  The only well-founded recursion in the subtree is class (S)'s `acc(A_φ, R)`,
  over the declaration's own edge relation and not over `∈`
  (`family/le.rs:23–37`). The `Acc.rec`/`Classical.choice` dependency at the
  type target is therefore *not* the counterpart of an `∈`-recursion on the
  set side; it is new, and §8.7 is where it is paid for.
* **"One general translation procedure."** General *within* a class; across
  classes it is per-class dispatch with four or five mutually exclusive entry
  points (`carrier.rs:226`, `recursor.rs:168`, `dep.rs:205`, `family.rs:169`,
  `family/le.rs:210`, `family/trunc.rs`), plus `empty_decl.rs` for `n = 0`.
  A W arm here should expect the same shape, and a plan that promises one
  entry point is promising something the set side did not achieve either.

Confirmed as stated: ι is **propositional throughout** `derived/` — every one
is a kernel `Thm` under hypotheses (`recursor.rs:34–37`, `iota.rs:3–7`,
`dep.rs:29–33`), and nothing anywhere is definitional. So definitional ι is a
real gain the type target can have and the set target cannot, which is
precisely the currency the tuple-tower deletion test has to be settled in.

### The building blocks, so nobody re-asks

These are not special cases awaiting generalisation. They are orthogonal to
recursion, or they are what a W arm would be built out of:

* **`PULiftP`, the pads (`dsingAt`/`unitAt`) and the `imax` field boxing** —
  level arithmetic. Every one of them exists to put a carrier or a field at an
  exact `Sort`, which is a problem W does not have and does not solve.
* **the Church routes** (`Sort 0` and maybe-zero) — impredicative `Prop`.
  Cheaper than W at the type target, with no set counterpart at all, and they
  supply arm G's own carrier and `ind`.
* **`Nat`-tagged `PSigma` chains** for a non-recursive declaration — the base
  case. W would technically cover it; modelling `Bool` as a W-type is not an
  improvement.
* **arm F**, the packed index equation — plain W does not carry indexed
  families; those need the skeleton-and-`good` carve, and arm F is that carve
  at `r := ⊥`.

**If a W arm grows the generator rather than shrinking it, that is the signal
to stop and say so** — which is the standing instruction, recorded here so the
next reader does not have to be told twice.

## 8.9 The residue, re-measured — and the index telescope behind a definition

### The census that was on file was from a pre-tranche binary

The Mathlib decline census this tranche inherited was produced before
`PULiftP`, the tuple tower, arm F's widening and arm G. Two of its largest
decline strings **do not exist in the current source** — `"an empty carrier at
Sort"` and `"a recursive Type-valued inductive … plan B"` — which is how it was
caught. It is superseded, and the numbers below replace it.

Re-run like-for-like: the same pre-cut prefixes, the same host, current binary
against the archived one. PANIC counts are identical in each pair, so the
denominator is unchanged and the comparison is honest (`Environment.AsyncConsts
.add` rejects some duplicate-normalized-name declarations in the *input*; they
never reach the filter, in either run).

| | 3M old → new | 30M old → new |
|---|---|---|
| models | 911 → **954** | 3,907 → **4,047** |
| declines | 67 → **24** | 250 → **110** |
| an indexed family | 42 → 9 | 164 → **68** |
| recursive `Type`-valued | 19 → 0 *as such* | 61 → **~39**, only the genuinely branching |
| does not land in a sort | 0 → 0 | 18 → **0** |
| basis primitive | 5 → 3 | 5 → 3 |
| PANICs | — | 176 → 176 |

**Declines at the 30M prefix fell from 250 to 110.** `List` and `Lean.Name`
were in the old census's W cluster and model by tuple tower today.

### The index telescope behind a definition

Eighteen of those declines were one bug, and it was a bug in the *reason* as
much as in the coverage. Lean stores an inductive's type **as declared**, so

```lean
inductive CategoryTheory.Presieve.ofArrows … : Presieve X
```

comes back as `… → Presieve X`, and a syntactic peel finds no `Sort` at the end
and **no indices at all** — while `Presieve.ofArrows.rec` carries them, because
Lean's own `numIndices` counts the *unfolded* telescope. The shape check said
"the declaration does not land in a sort", which named the wrong obstruction.

The fix is to peel syntactically first and, only when that fails to reach a
sort, re-expose the telescope with a **reducing** telescope and continue with
the definitionally-equal type that has its binders written out. The retry is
not the default on purpose: every shape that worked before reaches the same
`memberTy` object it always did, and `init-prelude`'s output is **byte-identical
across the change**, which is the measurement that says so.

The assertion against the recursor's own `numIndices`, which was already there,
is the cross-check on the unfolded count rather than a second opinion.

**It converted all eighteen into models**, which was more than expected: the
`Sv` fixture built for it is an indexed *subsingleton* and reaches arm F, but
the real members are `Prop`-valued relations with several constructors, so they
small-eliminate and take the Church route, which carries field-dependent
indices without complaint. Two fixtures pin the pair — `prim_shapes.lean`'s
`Sv` (hidden telescope, constructor indices from parameters: **models**) and
`prim_declines.lean`'s `SvIx` (hidden telescope, constructor indices are its
own fields: unfolds, then declines at arm F's index-variable field, **at the
right reason**). Two hidden indices rather than one in both, because with one a
model that guessed a fixed count would still pass.

### Sequencing, on the record

At the 30M prefix the remaining 110 declines are:

| cluster | count | share of the 110 | share of the 128 before the not-a-sort fix |
|---|---|---|---|
| **an indexed family at a never-zero sort** | 68 | **62 %** | 53 % |
| branching or under-a-binder recursion | ~39 | 35 % | 30 % |
| the basis itself | 3 | 3 % | 2 % |

**Say which denominator.** Both percentages above are correct and they differ
because the not-a-sort fix removed 18 declines from the *denominator*, not
from this cluster: 68/110 = 62 %, 68/128 = 53 %. The 128 figure is the census
as first re-measured, before that fix landed in the same tranche; the 110 is
current. Quoting either without its denominator turns "half" into "two thirds",
and a sequencing decision hangs on the difference.

Owners: the indexed family is thesis §5.2's skeleton-plus-`good`, with
`IndexedCarve.lean` compiling it on the thesis's own example, and it is **in
goal** rather than a follow-up — the objective for this strand is that
modelgen model every inductive Lean supports and process Mathlib reasonably.
Branching is W (§8.11), taken first because `Lean.ParserDescr` is on
`init-prelude`'s critical path. The basis is the exemption.

W is not the largest cluster and is being done first because `Lean.ParserDescr`
is one of the two declarations standing between `init-prelude` and full
coverage. The indexed family is larger and is deliberately next, not forgotten.

**This table is superseded, and by the arm it sequenced.** Three things it does
not say, all established later:

* The two clusters are *not* stacked. §8.15's arm C carves over a spliced
  index-erased inductive rather than over W, so the indexed arm did not wait
  on the W arm — it **landed first**, and `CarveOverSkeleton.lean` rather than
  `IndexedCarve.lean` is the prototype behind it.
* The indexed cluster is not 68 independent Mathlib shapes: **42 of the 68 are
  this tool's own composed `_model.aux`**, where every one of the 37 branching
  declines is an input declaration.
* **25 of the 68 are now models.** The residue at this prefix is 85, not 110,
  and the row below is the current one:

| cluster | count | of the 110 | erasure linear |
|---|---|---|---|
| an indexed family whose erasure **branches** | 43 | 39 % | no — W's, through the skeleton |
| branching or under-a-binder recursion | 37 | 34 % | — it *is* the erasure |
| the basis, the name guard, and two singletons | 5 | 5 % | — |
| ~~an indexed family with a linear erasure~~ | ~~25~~ | ~~23 %~~ | **closed by arm C** |

So **W is on the critical path for 80 of the original 110 — 73 %** — where
this section read 35 %, because a branching skeleton is exactly what W is for.
What arm C closed is the certifiable quarter; what is left owes an axiom bill
until item E lands or `Classical.choice` is decided (§8.15).

## 8.10 The rule the arms are built under: model in dependency order, then use the real type

This governs every arm from here and it was got wrong twice in one day, so it
is written down rather than left as practice.

**The basis is not a wall around the construction.** `Modelgen.primBasis` is
the set of types that get an *exemption from being modelled at all* — the
exemption that makes the construction well-founded. It is not a restriction on
what a model's *right-hand side* may mention.

**The only condition on everything else is acyclicity**: the model of `X` may
not use `X`, directly or transitively. Emit in dependency order and that holds
automatically, because the filter walks the export in the order the export
carries and the export is topologically sorted.

**And a modelled type may then be used as the real type, not through its
model.** Once `Subtype` has a model, later models use `Subtype` itself — the
Lean inductive, with definitional ι, `rfl` reductions and ordinary pattern
matching. The model *discharges the obligation* for that type; there is
nothing left to prove about it, and routing a later construction through the
derived interface (`rec_0` applications, propositional `iota_0_j`,
single-valuedness arguments) would pay twice for something already bought —
and would infect the later model with propositional ι where definitional ι was
available. **Write each model the way you would write it in ordinary Lean,
against ordinary Lean types.**

So, concretely, for the W arm: use real `Acc` with `Acc.rec` reducing by `rfl`,
and real `List`/`Option`/`Subtype` in the path construction. `Acc` is modelled
by arm G (§8.7) and `List` by the tuple tower (§8.4); W runs after both.

**Two wrong shapes, recorded because both were proposed and neither is
obvious.** The first is treating the basis as a wall and Church-encoding
everything a model needs. The second is subtler and survived a round of
correction: emitting a *bespoke* path tower per declaration, and the graph
route *inlined*, so as to name neither `List` nor `Acc`. Both exist only to
avoid naming types that are already modelled and therefore already paid for.
Neither buys anything, and the second costs the definitional ι that using the
real type gives for free.

What this does *not* relax: the basis exemption itself, acyclicity, and the
oracle bar — a model whose statement does not match the installed recursor's
rule is a decline, never an emission.

**A consequence for the output, and it is the reason dependency order is not
merely hygiene.** If the W arm's construction names `Acc` and the input does
not declare one, the arm must *splice* `Acc` and let it be modelled, rather
than treat it as a primitive: a spliced-but-unmodelled inductive would quietly
put a fifth type back in front of a consumer. `init-prelude` declares no `Acc`,
so this is the live case and not a hypothetical.

## 8.11 Stage 1: the W helper, compiled — `scripts/inductive-basis/WFromPaths.lean`

**Verdict: feasible, and the generic part is genuinely generic.** One
construction, ~130 lines, parameterised by `A : Type u` and `B : A → Type u`;
each target is then ~15 lines of glue. 526 lines, compiles at the pinned
toolchain in ~1 s with 0 errors and every `#guard_msgs` satisfied.

```text
Edge A B  := Σ a : A, B a
PTree     := List (Edge A B) → Option A        -- a partial labelling of paths
Step S t  := ∃ a, t [] = some a ∧ (∀ b : B a, S (subt t ⟨a,b⟩))
                              ∧ ∀ x, x.1 ≠ a → subt t x = nowhere
Good t    := ∀ S, (∀ u, Step S u → S u) → S t  -- impredicative least fixpoint
W A B     := Subtype Good
Wrec      := WellFounded.fix over the immediate-subtree relation
Wrec_iota := from WellFounded.fix_eq — propositional, as expected
```

Three targets, each pinned **twice** — the derived recursor against a
transcription, and Lean's own recursor against the *same* transcription, so
the transcription is checked against Lean rather than trusted:
`BT` (finite branching, two recursive fields, two constructors), `IT`
(infinite branching, recursive field under a binder), and `DT | mk : (n : Nat)
→ (Fin n → DT) → DT` — a non-recursive field the recursive field's binder type
*depends on*, which was expected to resist and does not: `CDT.rec' = Wrec` and
`CDT.iota = Wrec_iota` verbatim. Non-degeneracy is pinned too:
`CBT.leaf_ne_node` is proved from the recursor and its two ι rules alone, so
the recursor is not blind to its step function — the check arm G's refutation
taught us to make.

**The one non-obvious ingredient** is `Step`'s *third* clause, "subtrees
hanging off a label other than the node's own are empty". Without it a good
tree is not determined by its root and its children, `canon` fails, `sup` is
not surjective onto the carrier, and the recursor cannot be built at all.

### Axioms, and the special case worth taking

Every one of the seven derived constants costs `[propext, Classical.choice,
Quot.sound]`. All three come from **one place**: `sup` must decide `x.1 = a`
for an arbitrary `A`. That is `Classical.propDecidable`.

**It is avoidable whenever `B` factors through the constructor tag** — then the
label test is `Fin k` equality, decidable without choice, and the model loses
all three. That covers every declaration whose recursive-field binder types do
not mention its non-recursive fields, which is nearly all of them. A generator
should special-case it, and the general path should be the fallback rather than
the default.

### The dependency list — what must be modelled before W

Measured by a closure walk over types *and* values, pinned with `#guard_msgs`,
with `BT`/`IT`/`DT` asserted absent rather than merely reported. **22
inductives**, and for the generator they group as:

| | |
|---|---|
| load-bearing carriers | `Eq`, `List`, `Option`, `Sigma`, `Subtype`, `Nat`, `Bool` |
| well-foundedness | **`Acc`**, `WellFounded` |
| proof plumbing | `And`, `Or`, `Iff`, `Exists`, `True`, `False`, `HEq`, `PProd`, `PUnit` |
| classical dispatch | `Decidable`, `Nonempty` — and these two go with the special case above |

`Acc` is the interesting entry and it is why arm G came first: the W model
needs a prior model of accessibility (§8.10). `WellFounded` is an artefact of
using `WellFounded.fix` rather than raw `Acc.rec`, and can be dropped at the
price of re-proving the fixpoint equation by hand.

`init-prelude` declares `List`, `Option`, `Subtype`, `Prod`, `PProd`, `Bool`,
`Nat`, `Nonempty` and `Classical.choice`, and **does not declare `Acc`,
`Sigma`, `PSigma`, `WellFounded`, `propext`, `funext` or `Quot.sound`** — so
stage 2 needs a *splice-and-model* step, which the splice machinery does not
have today: it splices, but does not then run the prim pass over what it
spliced.

### What schematises, and the one place a generator breaks first

Free, schematic over the telescope: **arbitrary constructor count**
(`A := Σ' t : Fin k, Args t`, `B` by case on the tag), **arbitrary
non-recursive fields** including dependent ones and ones the recursive binder
depends on, **recursive fields with and without binders** (a bare `T` field
contributes `PUnit`), and **parameters**.

Resists, in the order it will bite:

* **The currying glue.** W hands you `(f : B a → W) → …`; Lean's recursor wants
  the fields *uncurried* (`motive a → motive b → motive (node a b)`). Bridging
  needs, per constructor, a chosen iso `B a ≅ Fin arity` **plus an eta lemma**
  `f = fun i => ⟨case-split⟩ i` proved by case analysis on the index type. It
  is generatable — the index type is a generated finite enumeration and the eta
  lemma is one `rfl` per branch — but it is emitted code per constructor rather
  than a uniform term, and it is where a generator will first break.
* **Indices: not addressed at all.** `W A B` models one non-indexed type. An
  indexed family needs the whole `Good`/`canon` development re-run
  index-aware. Not attempted, and **not to be assumed** from the above. This
  is the same wall as §8.9's 62 % cluster, from the other side.
* **Mutual and nested**: need prior reductions (mutual → indexed, nested →
  mutual), which land in indices.
* **Universes**: a `Prop`-valued or small-eliminating target is a different
  construction, and a `Sort`-polymorphic one would need `A B : Sort u`, which
  `List`-of-`Sigma` paths do not directly support.

## 8.12 The denominator, established — and what the PANICs do and do not cost

A coverage percentage on Mathlib was not quotable, because Lean's own
`Environment.AsyncConsts.add` rejects some of the **input** with
*duplicate normalized declaration name* — 872 non-fatal PANICs on the full
export, 176 at the 30M prefix — so some declarations never reach the filter and
the denominator was unknown. It is now known, and the PANICs do not touch it.

**The population, counted off the export directly** (no Lean, no filter — the
`{"inductive"` records, each of which is a *block*):

| | full export | 30M prefix |
|---|---|---|
| inductive blocks | 6,644 | 4,037 |
| inductive types | 6,675 | 4,067 |
| **simple blocks** (1 member, `numNested = 0`) — layer 3's candidates from the input | **6,593** | **3,994** |
| mutual blocks | 10 (26 types) | 9 (24 types) |
| nested blocks | 41 (56 types) | 34 (49 types) |

**The arithmetic closes at the 30M prefix.** Layer 3 returned 4,047 models and
110 declines — **4,157 verdicts** against 3,994 input candidates. The
difference, 163, is the composition (§8.3): a nested or mutual model emits
single inductives of its own and layer 3 runs on those too. So every input
candidate got a verdict and nothing was silently skipped, and

> **coverage at the 30M prefix is 4,047 / 4,157 = 97.4 %.**

**And no inductive is lost to a PANIC**, by two independent arguments. The
arithmetic above leaves no room for one. And structurally: at the 30M prefix
the PANIC'd names end in `splitter`, `_arg_pusher`, `eq_1`, `eq_def`, `eq_2`,
`wf_lbp`, `_simp_1` and the like — definitions and theorems, every one. An
inductive cannot enter an environment without its recursor and its
constructors entering too, and **not one PANIC at 30M names a `.rec`, a `.mk`
or a constructor**. The duplicate-normalized-name collision is between two
`_private` definitions from different modules (`Init.Data.List.Basic`'s
`List.filter.match_1.splitter` and `Init.Data.List.Lemmas`'), which is a
property of the input export, not of this filter.

**One thing to carry into the full re-run rather than assume.** The *old* full
log — pre-tranche binary — also shows PANICs whose names end in `self`,
`ctor_0`, `rec` and `mk`, 18 or so each. Those are modelgen's **own generated
names** colliding, which would be a real defect and is a different phenomenon
from the input's duplicate privates. They do not appear at the 30M prefix on
the current binary. Whether they survive at full scale is a question for stage
4, and it is flagged here so the re-run looks for it rather than counting
PANICs in aggregate.

## 8.13 Splice-and-model: layer 3 could not model what it introduced

**The hole.** `Modelgen.genPrim` — the entry that runs the third construction
over a declaration — was reachable from exactly two places: the replay of an
*input* declaration, and `primCompose` over the single inductives layers 1 and
2 emit. `ensurePrim` and its siblings put a **spliced** inductive into the
environment and into the output and nothing ever ran the construction over it.
So layer 3 was structurally **unable to model anything it introduced**.

This is the failure shape this project has hit repeatedly: not a wrong number,
but a check that reports success having done nothing. No coverage figure could
have shown it, because a spliced declaration was never a *candidate* — it
appeared in neither the numerator nor the denominator.

**What the earlier figures were measuring, so they stay readable.** Every
coverage figure in §8.2, §8.9 and §8.12 counts input candidates plus composed
ones. None of them counted splices, and **none of them moves with this fix**:
on `init-prelude` the only splices are `PSigma` and `PULiftP`, both on
`primBasis` and therefore exempt by design, so the corpus numbers — 122 of 125,
280 statements, 2344 replayed — are unchanged and the output is unaffected.

**Where it did bite is the contract, not the coverage.** Arm G splices
`Nonempty` when the input lacks one, and `modelgen/README.md` tells a consumer
it needs the four primitives and nothing else. A spliced-but-unmodelled
`Nonempty` put a fifth inductive in front of that consumer. The
`Modelgen.nonemptyDecl` docstring admitted the cost at the time — "what a
spliced `Nonempty` costs is one unmodelled inductive in that run's output" —
which made it honest, and still wrong. It is now modelled, and the claim holds
without a caveat.

**The fix**, in `genPrim`'s success branch: for each name it spliced, if the
name is not on `primBasis`, is a simple inductive block, and does not already
have a model, run `genPrim` on it. Three properties hold it down.

* **The basis stays unmodelled.** `primBasis` members are skipped, which is
  also what **bounds the recursion**: a model's own splices are basis members
  or already present, so the descent terminates. `genPrim` is `partial` for
  that reason and the reason is written at the definition.
* **Once, not once per consumer.** The guard is the presence of
  `X._model.self`. In `prim_graph.lean` two shapes need `Nonempty` and it is
  modelled exactly once.
* **Ordering is safe.** A spliced inductive is emitted before the model that
  needed it and its own model is appended after; the export only requires a
  declaration to precede its uses.

**Fixtures.** `prim_graph.lean` gains a `Nonempty` row — it is *spliced* there
rather than declared, so that row is red the moment layer 3 goes back to being
unable to model what it introduces. `prim_declines.lean` gains one too, from
`Inf`. `prim_graph_pre.lean` is the control: `Nonempty` is in the input, so it
is modelled by the ordinary path and not by this one, and it still appears
exactly once. `lake exe test` 397/0, `init-prelude` byte-unchanged.

**On Mathlib the expected delta is +1 model per run** — arm G fires there and
splices one `Nonempty`, guarded to a single model. The full-file census
reported in §8.14 was taken with a binary that predates this fix, and that is
the one number in it this would move.

**This is also what unblocks W.** `init-prelude` declares no `Acc`, and the W
arm's construction names `Acc` (§8.11's dependency list). Without
splice-and-model, splicing `Acc` would have put an unmodelled fifth inductive
in the output; with it, `Acc` is spliced and then modelled by arm G, and the
consumer's obligation stays at four.

## 8.14 The full Mathlib file: from exit 3 to exit 0, and the census

**Before this fix the full export did not process at all.** The run died at

```text
internal error: Unknown constant
  `_private.Lean.Meta.Sym.AlphaShareCommon.0.Lean.Meta.Sym.State._model.self`
```

exit 3, **zero models emitted**, after 4 minutes and 2.81 T instructions. It is
a regression this tranche caused: coverage rose, `Lean.Meta.Sym.State` began to
model where it had declined, and a second `_model.self` came into existence.

**The mechanism, and it is our names rather than Lean's machinery.** An export
is many modules flattened into one file, so it holds both
`_private.M.0.X` and a public `X`. We model both and emit
`_private.M.0.X._model.self` and `X._model.self`. `Environment.addDeclCore`
type-checks first and *then* registers each name in the async constant map,
which keys on `privateToUserName` — the name with its private prefix stripped.
`AsyncConsts.add` `panic!`s on a duplicate normalized name and returns the map
**unchanged**, so the constant sits in the kernel and is invisible to
`Environment.find?`. `MetaM`'s `inferType` goes through `find?`, so the next
declaration naming it dies.

**Not fixable by dropping to the kernel API**, and that is now measured rather
than inferred — `Test.lean`'s `runCollisionProbe` is the probe and every
sentence below is one of its checks.

`Environment.find?` reads `env.base.constants.map₁` and *then* the async map,
which reads as though a constant could be visible without the async map being
involved at all. **It cannot.** `mkEmptyEnvironment` and `finalizeImport` both
hand out a constant map already switched to **SMap stage 2**, so `SMap.insert`
puts every locally-added constant in `map₂`; `map₁` is the *imported* half and
this tool imports nothing. The base probe never fires for anything we add — so
"in the async map or invisible to `MetaM`" is the whole of the available
space, and that is a property of the map's stage rather than of which field an
add happens to write. `Environment.ofKernelEnv` is strictly worse and is
pinned so: after it, even a non-colliding `Tree.rec` stops resolving.

`Tree.rec_1` is a **different** phenomenon and the two were once run together.
It is invisible because `Declaration.getNames` omits *"auxiliary recursors
computed by the kernel for nested inductive types"* and that list is the loop
`addDeclCore` registers async constants from — no collision is involved, and
`Tree.rec`, which *is* in `getNames`, resolves fine beside it. `runEnvProbe`
pins that pair; `runCollisionProbe` pins this one.

The remaining public routes were read off the pinned toolchain and none is an
escape: `addConstAsync` (`Lean/Environment.lean:1018`) and `replayConsts`
(`:2440`) both insert through the same `AsyncConsts.add`, and `replayConsts`
additionally cannot replay an inductive at all (`panic! "must be
definition/theorem"`); `Kernel.Environment`'s constructor is `private mk ::`,
so its constant map cannot be rebuilt into stage 1 from outside that module.
The async bookkeeping is not a cost we merely pay; `MetaM` depends on it.

**The fix is in `addChecked`: a declaration the kernel accepts but the
environment then loses is a decline.** Checking membership *after* the add is
what catches it whichever order the two declarations arrive in — neither
ordering has the other's name in hand at the time, so no check on the name
alone can work. One subtlety cost a full run: the test must be
`Environment.find?`, **not** `Environment.constants`. `constants` is the
kernel map, which *does* have the constant; `find?` is the async-aware one and
the one `MetaM` uses. The first attempt used `constants`, changed nothing, and
failed identically.

**Result — the full 5.6 GB export, current binary:**

| | old census (pre-tranche) | now |
|---|---|---|
| exit | 0 | **0** |
| models | 6,323 | **6,640** |
| declines | 465 | **147** |
| instructions | 3.288 T | 3.350 T |
| peak RSS | 23.9 GB | 23.9 GB |
| wall | — | 5:59 |

**The denominator closes.** 6,593 simple input blocks + 194 composed = 6,787
verdicts = 6,640 + 147. **Coverage 97.8 %.**

The 147 declines: **82 an indexed family** (56 %, the largest cluster and the
next thing), ~52 branching or under-a-binder recursion (W), **10 name taken**
— the new guard, i.e. exactly the collisions that used to be fatal — and 3
basis primitives.

**The 10 name-taken declines were a coverage loss, and they are closed —
without a contract change.** They were declarations whose model name is
indistinguishable, after private-prefix stripping, from one already emitted.
Turning a fatal into a decline was the right first move; what was recorded
here after it was that the coverage-preserving fix is to disambiguate the
*emitted* name, which changes the four-name contract and is the owner's call.
**That was not the only fix, and the cheaper one was ours alone.**

The four names are a property of the **output**; what collides is a property
of the **environment** the generator builds a model in. Those can be different
names. So the model is generated under a root whose normalized form cannot
collide and the export records are renamed back. The declaration the kernel
accepted and the declaration emitted then differ by an **injective renaming of
constants this run introduced**, so nothing about "only what the tool
generates is checked, one at a time, with checking on" is weakened, and
`T._model.self` still means what `modelgen/README.md` says it means.

Four things about how it is built, each of which was a choice with an
alternative:

* **It is a retry, not a decision taken up front.** `addChecked` now
  distinguishes `Decline.nameLost` — the kernel took it and the environment
  lost it — from `Decline.nameTaken`, which is the input already holding the
  name; the two want opposite responses. `genPrim` re-runs `primIso` under the
  alias root on `nameLost` **and on nothing else**, so every declaration that
  models today takes exactly the path it took before. Deciding up front would
  have meant a normalized-name precomputation over 670,630 input names and a
  changed path for every private inductive in Mathlib, to fix nine.
* **The alias is unique per original name, not per declaration.** The
  collisions here are not only private-against-public: three private
  `Lean.Compiler.LCNF.State`s from three different modules normalize alike, so
  one fixed extra component would have put all three back on top of each
  other. The discriminator is the original name flattened into a single
  component, which survives `privateToUserName` because that only strips a
  prefix.
* **The renaming is over the export records and over the slice of output the
  whole call produced**, not over `Iso.decls`. It has to be: arm C (§8.15)
  splices an inductive of its own and that inductive is modelled by a
  *recursive* `genPrim` whose names are built off the alias root too, and
  renaming the slice catches those without threading a substitution through
  the recursion. `Iso` keeps the alias, because `checkModel` looks its names up
  in the environment and the environment is where the alias lives.
* **The probe's input is built in-process**, because no `.lean` source can
  produce the pair — a private `X` and a public `X` in one module is an error,
  and the collision only exists in an export, which is many modules flattened.
  `Test.lean`'s `runAliasProbe` parses a fixture and adds a second copy of one
  inductive under a private name that normalizes onto the original. It checks
  that both model, that the output carries the contract name, and — the check
  that would catch a half-done renaming — that the alias root appears **nowhere
  in the output**, not as a declaration name, not in an `all` list, not as a
  constant inside any type or value. Neither the kernel nor the statement
  oracle would catch that, because both read the environment, which keeps the
  alias on purpose. With the retry disabled the probe fails on two of its four
  checks, so it is measuring the fix and not the weather.

**Measured on the full export: nine of the ten recovered**, declines 118 → 109
and models 6,698 → 6,707, `_mgalt` occurring **zero** times in the 5.6 GB
output, 16,948 statements compared with none differing, instructions
unchanged at 3.365 T. The tenth was never this class: it is
`Lean.Syntax._model.0._model.tag` wanting the name `PSigma`, which is the
basis exemption doing its job.

**And the upstream bug that was reported here is real but is not the cause.**
Lean's `addDeclCore` does add *private* names to the **public** async-consts
map, behind a commented-out guard:

```lean
    -- TODO
    if true /- !isPrivateName n-/ then
      env := { env with asyncConstsMap.public := ... }
```

That is worth reporting on its own account. It is **not** why our names
collide, and the earlier claim that it was is withdrawn: the insertion into
`asyncConstsMap.private` twenty lines above is *unconditional*, and its trie
is keyed on `privateToUserName` too, so the private view collides whatever the
public guard does. The measurement is direct — one colliding add prints the
panic **twice**, once per view, and `runCollisionProbe` produces exactly four
across its two orderings. Uncommenting the guard would move the loss from the
public name to the private one and lose the same count.

**So patching that guard upstream would retire 18 PANICs, not 854.** 854 on the
full file, of which 18 involve our own `_model` names — the ones the escape
above retires — and the remaining ~836 are the input's own duplicate private
declarations, which are the export's property and not reachable from here at
all: those names are the input's and cannot be rewritten. Anyone who has
carried the earlier version of this paragraph onwards should carry that
sentence after it.

## 8.15 Arm C: the indexed family, carved out of its spliced index erasure

**Verdict: the indexed carve is built over a *spliced index-erased inductive*,
not over a W-type.** It is strictly cheaper on four axes, each of them checked
mechanically rather than argued, and it makes the indexed arm independent of
the W arm instead of stacked on it.
`scripts/inductive-basis/CarveOverSkeleton.lean` is the prototype — 537 lines,
~1 s, 0 errors, 22 `#print axioms`, an asserted dependency closure — and the
arm is **landed**: `Modelgen.primIso`'s `armC`, with `tests/prim_carve.lean`
as its fixture and the census below.

This **refutes a sequencing claim, not a result.** `WIndexedCarve.lean`'s own
verdict — that the indexed carve subsumes the non-indexed case, with
byte-identical glue at `ι := Unit` — stands; it was re-read, not re-run, and
nothing below contradicts it. What does not follow from it is *"build one arm,
not two"*, because that conclusion silently assumes the carve must stand on W.
§8.10's own rule says otherwise: model in dependency order and then use the
**real** type. The thing the carve needs underneath it is a non-indexed
inductive with the same constructor telescopes — and that is a declaration we
can **splice**, which §8.13's splice-and-model landed the machinery for.

### What the prototype pins

| | carve over W (`WIndexedCarve.lean`) | carve over a spliced skeleton |
|---|---|---|
| per-constructor glue | a chosen `B a ≅ Fin k`, an eta lemma, a `cast` | **none** |
| ι | propositional (`WellFounded.fix_eq`) | **`Eq.refl`**, the literal proof term |
| axioms, every derived constant | `propext, Classical.choice, Quot.sound` | **none** |
| inductives the *core* reaches | 20, before any target | `Eq`, `PSigma`, `Nat`, the skeleton |

**The currying glue disappears, and that is the headline.** Both W prototypes
name it as the one part of the design that is not schematic and the place a
generator breaks first: `W` hands you `(f : B a → W) → …` where Lean's
recursor wants the constructor's fields uncurried, so each constructor needs an
index iso plus an eta lemma proved by case analysis. A spliced skeleton *keeps
the field telescope* — the minor premise `STri.rec` wants and the minor premise
`Tri.rec` wants are the same telescope — so there is no iso, no eta lemma, no
`funext`, and nothing emitted per constructor beyond the constructor itself.
The whole of the per-constructor work becomes: repackage each recursive field
as a `PSigma`, and transport the conclusion along the index equation the
`good` proof already carries.

**ι is `Eq.refl`.** Three Lean features carry it and all three are load-bearing:
definitional proof irrelevance (`⟨s, h⟩ ≡ ⟨s, h'⟩`, so the `good` component
never obstructs), ι for the skeleton's *own* recursor — which a real inductive
has and a model does not, which is precisely §8.10's point — and structure eta
for `PSigma`. This matters beyond elegance: `modelgen/README.md`'s carve-out
that *"an ι theorem does not promise `Eq.refl`"* would otherwise have had to
widen from the graph arm to the whole indexed cluster, i.e. to the largest
cluster in the residue.

**The basis is unchanged.** `Eq`, `PSigma` and Church conjunction
(`Modelgen.andCOf`'s shape, whose projections reduce by β alone). Eleven
inductives are reachable across the three targets and only six belong to the
construction; the other five — `Add`, `HAdd`, `OfNat`, `PProd`, `PUnit` —
arrive through the *targets' own index expressions* (`m + n + 1`, the numeral
`0`, `Nat.rec`'s `below`/`brecOn`), which a generator copies verbatim out of
the export. The absence of `List`, `Option`, `Sigma`, `Subtype`, `Acc`,
`WellFounded`, `And`, `Or`, `Iff`, `Exists`, `HEq`, `Decidable`, `Nonempty`,
`Quot`, `Bool`, `True` and `False` is **asserted**, not reported, so this stops
being true the day the arm quietly grows a dependency.

Three targets, each pinned twice — the derived recursor against a
transcription and Lean's own recursor against the *same* transcription:
`Tri` (indexed, branching, two recursive fields at *different* indices),
`Two` (**two constructors at the same index**, so the recursor has to tell them
apart on its own, with `CTwo.l_ne_r` derived from the recursor and its two ι
rules alone), and `Bal` (an index **telescope** of length two, packed into one
`PSigma`, which is `Modelgen.packTyOf` — already built, already used by arm F).

### Certifiable, and by construction rather than by luck

The axiom-clause seat certified `propext` and then **refuted `Classical.choice`
outright** — `ε` cannot be a term of the kernel's language, so a choice
function is carried as a free variable under `IsChoiceFn`, every theorem
through it is hypothetical, and `Sealed` refuses hypothetical theorems. Closing
that needs an owner decision that has not been taken. So a model's bill is now
the difference between *modelled* and *modelled and certifiable*, and it
belongs in the census as a column rather than a remark:

| route | bill | certifiable today |
|---|---|---|
| carve over a spliced skeleton (this section) | **none** | **yes** |
| carve over W (`WIndexedCarve.lean`, all 24) | `propext, Classical.choice, Quot.sound` | no |
| W alone (`WFromPaths.lean`, all 7) | the same three | no |
| arm G (`AccArmShapes.lean`, 6) | `Classical.choice, Quot.sound` | no |

**`propext` on its own closes nothing here**, and the reason is worth stating
because it looks like it should: on the W route `propext` and
`Classical.choice` come from the *same* source — `Classical.propDecidable`,
hence choice, hence `Classical.em`, hence `propext` — so certifying `propext`
alone unblocks no W model, and arm G never spends `propext` at all.

`WFromPaths.lean`'s item E is the lever on the W side: the classical dispatch
is avoidable whenever `B` factors through the constructor tag, because the
label test is then `Fin k` equality. **For this arm it is moot** — there is no
`B`. The carve over a spliced skeleton never decides an equality between
labels, because it never has labels: the skeleton's own recursor does the case
analysis the tag was standing in for. There is nothing to make the default,
because there is no fallback.

Two things that ought to be said to whoever builds the W arm rather than left
here. First, item E's cheap path is a *different construction* and not a
setting: `WCon.mk` opens `Classical` unconditionally (`WFromPaths.lean`, and
`WIndexedCarve.lean:238`), which is why every one of the 31 constants across
the two prototypes carries all three axioms even at targets like `BT` whose
`B` does factor through the tag. Second, item E does not remove `Quot.sound`,
because the **currying glue spends `funext` independently** — every eta lemma
is a `funext` (`CBT.rec'`, `CTri.nodeKids_eq`, and so on), and `funext` in Lean
core is proved from `Quot.sound`. So the best bill item E can reach is
`[Quot.sound]`, which *is* covered. That last is a reading of the two
prototypes and not a measurement; nothing has been built at item E's path.
It is also a third reason the glue is worth not having.

### What it costs, and the rule that keeps the contract honest

One spliced inductive per modelled family, which splice-and-model must then
model. So the arm's reach is *indexed families whose index erasure the existing
routes model*, and a family whose erasure is branching still waits for W — the
erasure of `Lean.Expr`'s aux is still `Lean.Expr`-shaped. This does not make
the arm smaller than the carve-over-W arm would have been; it makes the
dependency **explicit and separable** where W underneath everything made it
invisible.

And the obligation is real: a spliced-but-unmodelled skeleton would put a fifth
inductive in front of a consumer, which is exactly the hole §8.13 closed. So
the rule is **decline the family when its skeleton does not model.** A decline,
never an emission.

### The residue, re-split — and the arm is worth a quarter of it, not nine tenths

Re-measured on `pre-30000000` with the current binary — 110 declines, the same
110 §8.9 sequences, split along two axes that census did not have. The second
axis is now **printed by the decline itself**: the indexed decline carries
`erasure linear: yes|no`, computed by the same test the tuple tower applies
(`Modelgen.recSlotOf`: at most one recursive field per constructor, and no
recursive occurrence under a binder). Erasing indices does not move that test —
a field `∀ z⃗, T p⃗ e⃗` erases to `∀ z⃗, S`, same binders, same count — so it can
be asked of the family itself, and the census measures the arm's reach instead
of estimating it.

| cluster | count | this tool's own composed `_model.aux` | erasure linear |
|---|---|---|---|
| an indexed family at a never-zero sort | 68 | 42 | **25 yes / 43 no** |
| branching or under-a-binder recursion | 37 | 0 | — (it *is* the erasure) |
| basis / name taken / index-variable field | 5 | — | — |

**So the carve arm on its own closes at most 25 of 110 — 23 %, not 91 %.**
That is the number that was not known, and it is an *upper* bound: an erasure
that is linear could still meet a level gap no pad or box closes, which only
building the arm will find. Of the 25, nineteen are input declarations and six
are composed.

**W is on the critical path for 80 of the 110, not 37.** The 37 branching
declines are non-indexed and are W's directly. The 43 indexed families whose
erasure is *not* linear need their skeleton modelled before they can be carved,
and a branching skeleton is exactly what W is for. Adding those: 73 % of the
residue waits on W, where §8.9's table reads as 35 %. The brief this arm was
begun under put the combined figure at ~91 % of the residue and that is right —
25 + 43 + 37 = 105 of 110 — but it attributed it to *one* arm, and the split is
23 / 39 / 34.

**This does not put the carve back on top of W**, and that is the point of
building it over a spliced skeleton instead. The carve arm never names W: it
splices the erasure, `genPrim` models that by whichever arm fits — the tuple
tower where the erasure is linear, the W arm where it branches — and the carve
is written against the real spliced inductive either way, with ι still
`Eq.refl`. What the measurement changes is *sequencing*, not architecture: the
two arms are independent to build and W unblocks more.

**But the 25 and the 80 are not the same kind of coverage**, and after the
axiom table above that difference is the sharper one. The 25 the carve arm
reaches over a *linear* skeleton spend **no axioms**, so they are models and
certificates both. The 43 whose skeleton branches inherit whatever the W arm
spends on that skeleton — all three axioms as W stands today, `[Quot.sound]` at
best — so they would be models that no certificate covers until either item E
lands or `Classical.choice` is decided. Sequenced by certifiable coverage
rather than by coverage, the arm that closes 23 % of the residue outranks the
one that closes 34 %.

**And nearly two thirds of the indexed cluster is our own output.** The 42
composed occupants are the single indexed inductives layer 2 emits when it
packs a mutual block, fed back through layer 3 by `primCompose`; 36 of those 42
are the non-linear-erasure ones, because a mutual block of branching members
packs into a branching aux. Every branching decline, by contrast, is an input
declaration. The indexed cluster is not 68 independent Mathlib shapes — it is
26 of them plus 42 instances of one shape *this tool controls the generation
of*.

### What the arm emits, and the one thing it needs that no other arm did

Six declarations beyond the four interface names, in this order:
`T._model.skel` — **an `inductive`**, the index erasure, spliced — then
`T._model.good`, `T._model.self`, the `ctor_j`, `rec_0` and the `iota_0_j`.
`skel` and `good` are **internal** in `modelgen/README.md`'s sense; no
consumer reads them.

`skel` and `good` are guarded by the same name check as the interface names
and only when the arm fires, exactly as arm G's internals are. The erasure
itself is built by **raw `Expr` surgery on de Bruijn indices rather than by a
telescope walk**, and that is forced rather than stylistic: opening a telescope
means `withLocalDecl` at a type mentioning `T._model.skel`, which `MetaM` would
have to `inferType`, and the constant does not exist yet — it is the one being
declared. The first attempt did it the ordinary way and cost an `Unknown
constant` and exit 3.

**`Iso.requires`, and the rule it makes structural.** Arm C is the first arm
whose output contains an inductive that was in nobody's input, so it is the
first that can leave one *unmodelled* — the hole §8.13 closed, reopened from a
new direction. `Iso.requires` names the skeleton, and `Modelgen.genPrim`
withdraws the **whole** model — environment, records and report — if
splice-and-model did not model it. Checked after the descent rather than
predicted before it: a cheap test that says "this skeleton will model" is the
shape of *skip is not pass*, reporting success and leaving the hole open on
the case it got wrong. The decline carries the **skeleton's own reason** and
not merely the fact of failure.

One thing the arm does *not* have to do, and it is worth naming because the W
route does: **there is no per-constructor glue at all.** The minor premise
`skel.rec` wants is the minor premise `T.rec` wants, because a spliced
skeleton keeps the field telescope. Everything per-constructor is extraction —
`good`'s first conjunct is the index equation, and it is *read off the major*
rather than proved.

### Measured, on Mathlib

Full 5.6 GB export, exit 0, against the census §8.14 recorded:

| | §8.14's census | with arm C | and with §8.14's alias retry | and with §8.16.2's arm W | and with §8.16.3's multi-slot carve |
|---|---|---|---|---|---|
| models | 6,640 | 6,698 | 6,707 | 6,770 | **6,868** |
| declines | 147 | 118 | 109 | 62 | **13** |
| statements compared, differing | 16,928 / 0 | 16,928 / 0 | 16,948 / 0 | 17,270 / 0 | **18,434 / 0** |
| instructions | 3.350 T | 3.371 T | 3.365 T | not re-measured | **3.398 T** |

**Say what the denominator now counts.** The +58 models are 29 families that
used to decline *plus their 29 spliced skeletons*, and a skeleton is a verdict
too — so the denominator moves from 6,787 to 6,816 and the two figures are not
against the same population. Both readings, so neither can be quoted as the
other:

* against §8.14's own denominator — input candidates plus composed, 6,787 —
  6,669 of them model, **98.3 %**, up from 97.8 %;
* against everything the tool now returns a verdict on, skeletons included,
  6,698 / 6,816, also **98.3 %**.

They agree to the decimal because a skeleton that models adds one to each side.
The number to watch is the decline count, and it is **147 → 118** here and
**→ 109** once §8.14's alias retry lands beside it.

**And the split that now matters more than the count.** Every one of the 29
families this arm added, and every one of their 29 skeletons, is
**axiom-free** — `#print axioms` empty, ι by `Eq.refl` — so all 58 are models
*and* certificates. That is the column to carry into any future census:
`Classical.choice` has been refuted as a term of the checker's language, so a
model that spends it is modelled and not covered, and the indexed families
still waiting on W land on the right side of it after all: §8.16 builds the W
they need at `[propext, Quot.sound]`, and only four declarations in Mathlib
force `Classical.choice`.

Of the 109: 53 an indexed family whose erasure is *not* linear (43 of them
composed `_model.aux`), ~50 branching or under a binder, 3 basis, 1 the basis
exemption reached through a composed tag, and 2 singletons. **No withdrawal
fired on Mathlib** — every family arm C admitted, it modelled. The name-taken
cluster is gone; §8.14 is where it went.

At the 30M prefix the same arm closes 25 of 110, which is exactly the count
`erasure linear: yes` predicted before the arm was built. The prediction and
the outcome agreeing to the unit is the one piece of evidence that the
`erasure linear` census measures the arm rather than something adjacent to it.

### A Type-route defect the arm surfaced

`tests/prim_carve.lean`'s `NoBase` is `NoBase : N → Type | mk : (n : N) →
NoBase n → NoBase (N.s n)` — an indexed family whose erasure is `S | mk : N →
S → S`, **linearly recursive with no base constructor**, which Lean accepts
and which is uninhabited. The tuple tower cannot express it: spine 0 is the
tower over the *base* constructors, and with none there is no fibre for
`stepTower` to destruct at.

It did not decline cleanly, it read `cs[0]` of an empty array. The resulting
non-fatal `panic!` returned a default `PCtor` whose chain has no fields, so the
declaration then declined with *"a chain with no fields needs a pad"* — a true
refusal reached by an out-of-bounds read, with a reason that named nothing.
This **predates arm C** and is a gap in the Type route; nothing in the corpus
had reached it, because every linearly recursive occupant there has a base
constructor. It is now a named decline with the guard beside `baseJ`, and
`NoBase` is the fixture that holds it.

### What is not done, and is not to be assumed from the above

* **`Prop`-valued and small-eliminating targets** are a different construction,
  unchanged from `WFromPaths.lean`.
* **Universe polymorphism** is exercised by the arm on Mathlib but not by the
  prototype, whose targets are `Type`-valued at a literal level. The one level
  question the *carrier* raises is asked and answered: the carrier is `PSigma (fun s : S => good s x)`
  with `S : Sort w` and `good … : Prop`, so it lands at `Sort (max 1 w 0)`, and
  the prototype pins that Lean sees that as `w` on the nose at every never-zero
  shape a carrier has — `succ u`, `max 1 u`, `max 1 u v`, and `imax u (v+1)`.
  So the carve layer adds **no** level obligation of its own. The skeleton's
  own model still meets the Type route's pads and boxes, which is that route's
  existing business and not a new one.
* **An index telescope whose later index types depend on earlier ones** uses
  the same `PSigma` packing — `Modelgen.packTyOf`, which arm F already states
  its Henry-Ford equation at for exactly that reason — and I expect no new
  content, but only the independent case is tested (`Bal`, `Bl`).
* **The mutual and nested reductions** still land in indices, so they are
  downstream of this arm rather than beside it.

## 8.16 W without `Classical.choice` — `scripts/inductive-basis/WTagged.lean`, and the ceiling

**Verdict: the W route's axiom bill drops from `[propext, Classical.choice,
Quot.sound]` to `[propext, Quot.sound]`, and that closes the certifiability
question for 99 of the 103 declarations still waiting on W.** 598 lines, 0
errors, 0 warnings, 15 `#print axioms` and an asserted dependency closure.

This matters more than an axiom count usually would, because the three axioms
are no longer interchangeable. `propext` was certified; `Quot.sound` is
covered; **`Classical.choice` had been refuted** as a term of the checker's
language — a choice function is never unique, `define` requires `∃!`, so the
choice function is carried as a free variable under a hypothesis, every theorem
through it stays hypothetical, and `Sealed` refuses hypothetical theorems.
A model that spent it was modelled and not certifiable.

**That ceiling is gone and this paragraph is the historical reading.**
`derived/src/choice/epsilon.rs` (rule 7) stands on `kernel`'s 0-ary Henkin
constant and took `waiting:axiom(Classical.choice)` on
`mini/tests/fixtures/standard_axioms.lean` from 4 to 0 — so all three axioms
are covered, the choice question is a *cost* question rather than a
certifiability one, and §8.16.6 is where the untagged construction the rest of
this section declines is taken up again. What stands unchanged below is the
reason to prefer the tagged construction wherever it reaches: it spends less.
So the bill was the difference between a model and a certificate, and

> a W model at `[propext, Quot.sound]` is both.

### What changes, in one line

```text
WFromPaths.lean   Edge := Σ a : A,  B a      a path step carries the LABEL
WTagged.lean      Edge := Σ t : K,  B' t     a path step carries the TAG
```

A label is a constructor tag together with that constructor's non-recursive
fields, and the fields can be anything, so `a = a'` is not decidable and
`WFromPaths.lean`'s `mk` reaches for `Classical.propDecidable`. **The tag is a
`Fin k`.** Nothing is lost by recording only the tag on the path, because the
label is still stored at the node: `PTree` is `List Edge → Option A` and the
`Option A` at a path is the whole label. `CFT.tip_inj_data` pins that — a model
that recorded the tag and dropped the payload passes every other check in the
file.

**It is a different construction and not a setting**, which is why item E was
worth building rather than assuming: you cannot instantiate `WFromPaths.lean`'s
`W A B` at a decidable `A` and get this, because its `mk` is `open Classical
in` unconditionally. The axiom is in the definition, not in the instance.

### The two survivors, since the point was to know

* **`Quot.sound` is `funext`, and is not removable.** Two trees are equal when
  they agree at every path and `PTree` is a function type, so `mk_sub`, `mk_ne`
  and `canon` are each a `funext`. It is the *same* `Quot.sound` the currying
  glue spends, so the glue's cost is a duplicate rather than an addition —
  which also corrects the shape of §8.15's note: removing the glue would not
  have removed the axiom.
* **`propext` is `simp`'s**, in those same three proofs, and is very likely
  removable by writing them out. It is **not** removed, because `propext` is
  certified and the effort buys nothing. Recorded rather than left unexplained.

Three targets, each pinned twice — the derived recursor against a
transcription and Lean's own recursor against the same transcription: `BT`
(two recursive fields), `FT` (branching **and carrying data**, the case the
file exists for, since `BT`'s label type has decidable equality anyway and a
construction that secretly still decided label equality would pass its pins),
and `IT` (infinite branching under a binder). Non-degeneracy from the recursor
and its ι rules alone. The closure asserts **`Nonempty` is unreachable** —
`Classical.choice`'s own domain — which is the mechanical form of the claim.

### The ceiling, measured

The tagged construction needs the branch type to be a function of the tag
alone, which is exactly: **a recursive field's binder types may not mention the
constructor's own non-recursive fields.** They may mention the parameters,
which are fixed for the declaration. `Modelgen.tagFactored` asks it, and every
decline that names W now prints `B factors through the tag: yes|no`, so the
census reports two populations instead of one.

On the full export, of the 103 declines that wait on W:

| | count | bill the tagged W would give | certifiable |
|---|---|---|---|
| `B` factors through the tag | **99** | `[propext, Quot.sound]` | **yes** |
| it does not | **4** | `[propext, Classical.choice, Quot.sound]` | no |

The 99 split 52 indexed families whose erasure branches — those reach W through
arm C's spliced skeleton — and 47 branching declarations directly.

**And the four are exactly the W-types.** `WType`, `PSet`,
`FirstOrder.Language.Term` and `PFunctor.Approx.CofixA`: in each, the branching
arity is a *datum of the node* rather than a function of the constructor —
`WType.mk : (a : α) → (β a → WType β) → WType β` has its branch type `β a`
mentioning its own field. There is no tag to factor through, because the shape
*is* the general W. That is not an artefact of this encoding, and no
construction is known here that avoids the classical route for it.

So the honest ceiling for the whole thrust, as it stands:

* declines would go **109 → 10** with the W arm built (99 closed, 4 remaining,
  plus the 6 that are the basis exemption and two singletons);
* of the closed ones, **all 99 would be certifiable**;
* the **4** are the irreducible uncertifiable remainder, and they are what
  #150 has to decide about — not a coverage question but a question about what
  a certificate means for a genuinely choice-shaped construction.

### The mechanism is settled, and the foundation is measured

**The core goes in as an export fragment, read and `addChecked`, not compiled
into the tool.** The deciding argument is not the plumbing but the boundary:
this tool's contract is *"the input is trusted; only the declarations the tool
generates are checked, one at a time, by Lean's kernel with checking on"*.
Compiling the core in and copying its `ConstantInfo`s would smuggle 206 of
**our own** constants past that boundary as if they were input — trusted,
unchecked, absent from the report. Reading them and splicing them through
`Modelgen.addChecked` puts them on the checked side, where they belong, and
makes them inspectable data rather than linked code. Confirmed against the
code rather than assumed: `addChecked` is `addDeclCore 0 d none true` and the
input replay is the same call with `false`, so the two sides are exactly one
boolean apart and the fragment lands on the right one.

`modelgen/tests/w_core.ndjson` is the fragment — what `lean4export` emits for
`--#export WT.W WT.sup WT.Wrec WT.Wrec_iota instDecidableEqNat` over
`WTagged.lean`'s core: 528 KB, **19 inductive blocks and 2 axioms**, matching
the closure count exactly. The fifth root is the tag scheme's one demand on the
fragment and is sized below; it adds no inductive, so the 19 is the same 19.

**And every inductive it reaches models.** Run through `--prim-models`, the
fragment gives 18 models and 2 declines, and the two are `Nat` and `Eq` — the
basis exemption doing its job. 40 statements compared, none differing. So the
plan's load-bearing assumption is measured rather than assumed: splicing the
core and modelling what it splices leaves **nothing** unmodelled in front of a
consumer. `Test.lean`'s `w_core` row pins it, so the day one of the 18 stops
modelling is a test failure with a name on it.

### The choice question was one declaration, and it is now none

The fragment's own bill is `[propext, Quot.sound]`. But **`Acc`'s model** is
arm G's graph route, and arm G spends `Classical.choice` — so modelling the
fragment splices the axiom once, at exactly one site, which the report names.
Nothing else in the 18 does: `Nonempty` and `WellFounded` are non-recursive
`Prop`s and take the Church route.

**And that one site is no longer a cost.** `Classical.choice`'s refutation was
narrower than it read: the kernel *has* choice — `Thm::ax_choice`,
`∀x ∃f. IsChoiceFn(f,x)`, set-sized and asserted at no consistency cost. What
was missing was a way to **name a witness**. Skolemising at arity ≥ 1 is
genuinely unsound there, because `ax_replacement` takes an arbitrary `Formula`
and a Skolem function need not be amenable; but a **0-ary Henkin constant** —
from `⊢ ∃y. φ` with `FV(φ) ⊆ {y}` — is conservative *including* over the
schemes, because a constant is a parameter. Carneiro fixes one `ε` on one set,
which is exactly that shape, and the owner has authorised it. So `Acc`'s model
is certifiable and **the price §8.7 paid to take `Acc` out of the basis is
refunded rather than merely re-priced**: the basis stays at four, `Acc` is
modelled, and no horn of the trade remains.

**Keep the distinction that made the trade legible in the first place**, since
it is the kind a later reader collapses: a W target's own model is `[propext,
Quot.sound]` because it depends on the **inductive** `Acc` — spliced and
kernel-checked — and *not* on `Acc`'s model. Those are two different objects
and only one of them ever spent an axiom. That was true when the axiom was a
problem and it is still true now that it is not.

### The carrier's universe is not a boundary, and the first measurement of it was wrong

The core is stated at `A B' : Type u`, so the carrier it produces is a
`Type u` — and a declaration's sort `w` is only required to be *never-zero*.
Those are different conditions, and a `Sort (max 1 u)` carrier would have
needed a `Sort`-polymorphic rebuild of the core (`List` and `Option` replaced
by `Sort`-valued analogues), which is a fragment thrown away and re-made if it
is discovered after the arm is built rather than before.

Asked before building, and the answer is that **all 103 declarations waiting on
W have a `Type u` carrier**, so the core as written reaches every one of them
and no rebuild is needed.

**The first flag said 13 of them did not, and the flag was wrong** — recorded
because the mistake is a standing trap and not a slip. The test was
`w.normalize matches .succ _`, and Lean's level normalizer **pushes `succ`
inward through `max`**: `Type (max u v)` is `Sort (succ (max u v))`, which
normalizes to `max (succ u) (succ v)` and matches no `succ` pattern, even
though it is a `Type` at every instantiation. The right test is
`Level.dec`, which is `w - 1` and answers the question that was being asked.
The 13 were `Lean.RBNode`, `FreeAlgebra.Pre`, `Turing.TM1.Stmt` and the like —
ordinary multi-parameter polymorphic types, and the flag's own shape was what
made them look exceptional. Nothing was designed around it, because it was
measured before anything was built on it.

### What building the arm costs, and the one thing to settle first

Nothing is generated: this is a compiled prototype at three targets and
`Modelgen.primIso` has no W arm. What it settles is the two things that had to
be settled before one is worth building — that the construction exists at a
covered bill, and how much of the residue it reaches.

The mechanism is settled above. What remains is that **the W core cannot be
hand-built as `Expr`s the way every other arm is**, which is why the fragment
exists at all. Arm C's largest emitted term is a
`PSigma` and an `Eq.rec`; W's `canon`, `Wind`, `sub_wf` and `Wrec_key` are
thirty-line tactic proofs over `List`, `Option`, `Sigma`, `Subtype`, `Acc` and
`WellFounded`, and writing them as `Expr` builders is not a bigger version of
what `Simple.lean` already does.

Measured, so the next attempt starts from a number: the tagged core's full
constant closure — types *and* values, from `W`, `sup`, `Wrec`, `Wrec_iota` —
was **195 constants**: 19 inductives, 24 constructors, 19 recursors, 69
definitions, 58 theorems, 4 quotient constants and **2 axioms**, `propext` and
`Quot.sound`. (`WFromPaths.lean`'s classical core is 252; the difference is the
`Classical` machinery.) With `instDecidableEqNat` added as the fifth root it is
**206 constants**: the same 19 inductives, 24 constructors and 19 recursors,
now 78 definitions and 60 theorems.

So the arm's shape is: get those 206 into the output once, splice-and-model the
19 inductives among them — measured above, all of them do — and emit
per-declaration glue against them.

**One module-graph constraint, found while sizing the splice.**
`toDeclaration : Environment → EDecl → Option Declaration` — which is what
turns a parsed fragment record into something `addChecked` takes — lived in
`Driver.lean`, *below* `Simple.lean` in the import order (`Driver` imports
`Simple`), so a splice written where `primIso` can call it could not use it
where it stood. **Done**: it is in `Format.lean`, the shared floor, with the
`hintsOf`/`hintsTo`/`safetyOf` translations it needs, and `Mono.lean`'s
trimmed copy — which existed only because the original was above it — is gone.
Three callers, one definition.

### The splice, built — `Modelgen.ensureWCore`

`Modelgen.ensureWCore : Std.HashSet Name → GenM (Array Declaration)`, in
`Model.lean` beside `ensureEq` and `ensureFunext`, which is the section for
exactly this: a constant the model needs, taken from the input where the input
has it and spliced through `addChecked` where it does not.

**Measured, from empty and on top of Mathlib.**

| | |
|---|---|
| the fragment alone, `envprobe tests/w_core.ndjson C` | **160 records accepted, 0 rejected**, 0.107 s for the whole process |
| onto a fixture input (`prim_carve`) | 159 records added, 203 constants through `addChecked` |
| onto a 1,000,000-line Mathlib prefix | **154 records added, 9 the input already had or the parse folded**, 190 constants through `addChecked`, 0 rejected |
| the splice's own cost | **845 M instructions** for the whole process from empty, once per run — against 272 s for a Mathlib pass |

The five roots — `_wcore.WT.W`, `_wcore.WT.sup`, `_wcore.WT.Wrec`,
`_wcore.WT.Wrec_iota` and `_wcore.instDecidableEqNat` — are visible to
`Environment.find?` afterwards, which is the lookup `MetaM` goes through and not
the same question as the kernel map (§6.6). `Test.lean`'s `runWSpliceProbe` pins
all of it, plus idempotence: the second call adds nothing, because the splice is
once per run and not 160 kernel checks per W target.

**The fifth root, and why the other four's closure cannot reach it.** The core
is `{K : Type} … [DecidableEq K]` and all four roots take the instance as a
*parameter*, so no closure of theirs contains a `DecidableEq` for any concrete
`K`. `scripts/inductive-basis/WGeneric.lean` settles the scheme that decides
which one is needed — `K := Nat` for every declaration, rather than an
enumeration inductive minted per declaration whose `DecidableEq` the generator
would have to prove and whose type `Iso.requires` would then oblige the run to
model in turn — so `--#export` gained `instDecidableEqNat` and nothing else.

It costs **11 ordinary declarations** and, decisively, **no new inductive**:
`Nat.decEq` and its `match_1`, `Nat.beq`'s two soundness lemmas
(`Nat.eq_of_beq_eq_true`, `Nat.ne_of_beq_eq_false`) with their two private match
auxiliaries, the `Nat` and `Bool` `noConfusionType`/`noConfusion` pairs, and the
instance itself. Because the inductive count is unchanged at 19, the
splice-and-model claim above carries over untouched — `Test.lean`'s `w_core` row
is the same 18 models and the same 2 basis declines. Isolated on the same
harness, the added kernel-checking is **28.4 M instructions** (816.5 M → 845.0 M
for the checked replay from empty, +3.5 %).

**Three things about the splice, measured rather than assumed:**

* **`include_str` is free at run time and unsound at build time.** The 528 KB
  fragment is a string literal in the binary's data; there is no runtime file
  lookup and no dependence on the build tree. The alternative — locating the
  `.ndjson` relative to `IO.appPath` — would have made the binary depend on its
  own build layout for no gain. **But `include_str` is not in Lake's trace for
  `Modelgen.Model`**: re-exporting `w_core.ndjson` and running `lake build`
  reports success and leaves the binary carrying the *previous* fragment. This
  was measured, not inferred — the re-export above added 11 declarations and the
  rebuilt tool still spliced the old 149 — and neither `touch` nor a newer mtime
  forces it, because Lake hashes content and the content it hashes is
  `Model.lean`'s. `runWSpliceProbe` therefore compares `Modelgen.wCoreText`
  against the file on disk byte for byte. That one check is the only thing
  between a fragment change and a silently stale tool, and every other check in
  that function passes on a stale one.
* **Everything gets a `_wcore` prefix except twenty names under six roots, and
  the list above six of them was got wrong at the sizing.** (Sixteen under four
  until §8.16.7 added `Classical.choice` and `Nonempty`, by the same argument.)
  The fragment's
  names are Lean core's, so splicing `List` into an input that already declares
  one is a kernel rejection; prefixing makes the core self-contained and costs
  only duplicates.

  The six that were obvious are `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` —
  the kernel special-cases those, and the fragment carries four `quot` records
  — and the two axioms `Quot.sound` and `propext`, because **`mini/src/axiom.rs`
  selects the clause by that exact name, so a namespaced copy is a
  *non-standard axiom* and is declined downstream.** That much was right.

  What it missed is that **an axiom's statement is renamed too.** The
  fragment's `Quot.sound` mentions `Eq`, `Quot` and `Quot.mk`; its `propext`
  mentions `Eq` and `Iff`. Prefixing `Eq` and `Iff` while sharing the two axiom
  names emits

  ```text
  propext    : ∀ {a b : Prop}, _wcore.Iff a b → _wcore.Eq a b
  Quot.sound : ∀ {α r a b}, r a b → _wcore.Eq (Quot.mk r a) (Quot.mk r b)
  ```

  — two axioms **under Lean's exact names carrying statements that are not
  Lean's**. On an input that declares `propext`, which is every real one, that
  is a kernel rejection and the arm reaches nothing. On an input that does not,
  it is *worse than a decline*: the name is what `axiom.rs` keys on, and it
  would take a statement that is not `propext`'s as the standard `propext`
  clause. So `Eq` and `Iff` are shared for the same reason the axioms are, one
  level down, and `Test.lean` pins both halves.

  **`Nat` is the fourth shared root, and the kernel forces that one outright.**
  The fragment holds two `Expr.lit (.natVal _)`, and a literal's type is the
  kernel's own `Nat` by fiat — nothing renames it. A prefixed `_wcore.Nat`
  leaves `_wcore.Bool.ctorIdx` returning it while the literal in its body is at
  `Nat`, and the kernel says `unknown constant 'Nat'`. Sharing costs nothing
  anyone was counting on: `Nat` is already one of `primBasis`'s four, so it was
  never going to be modelled, and sharing takes an unmodelled inductive *out*
  of the output rather than putting one in.

  The list is **names and not prefixes**, and that matters: the fragment
  carries `Eq.symm`, `Eq.mpr`, `Eq.subst`, `Quot.liftOn`, `Nat.brecOn` and nine
  more under those four roots, and sharing *those* would redeclare constants a
  real input has. Sixteen names: `Eq`, `Eq.refl`, `Eq.rec`, `Iff`, `Iff.intro`,
  `Iff.rec`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Quot`, `Quot.mk`,
  `Quot.lift`, `Quot.ind`, `Quot.sound`, `propext`. `funext` is *not* among
  them — it appears in no emitted statement, only inside proofs, which is
  precisely why §1 namespaces its own as `T._model.funext`.

**And the ι-rule conversion §8.16 costed is not owed.** The paragraph this
replaces weighed renaming `Eq` (one `_wcore.Eq → Eq` conversion per ι rule)
against not renaming it (the fragment's 200-odd proofs run at the input's `Eq`),
and recommended renaming for robustness. The axiom statements settle it the
other way, and the robustness argument survives intact in the form that
matters: if the input's `Eq` or `Iff` or `propext` is not Lean's, the
fragment's proofs are checked against it and `addChecked` rejects one of them.
That is a decline with a name on it, not a silent wrong answer — which is why
no shared declaration needs a separate shape check. At the shared `Eq` the
fragment's `Wrec_iota` and the contract's ι theorems are already the same
equality, so the conversion is not written and not paid for.

**One latent bug the splice surfaced, in a function older than it.**
`Modelgen.renameRootE` rewrote `Expr.const` heads and nothing else, but
`Expr.proj` carries a `typeName` — the structure the projection is *of* — and
a `proj` left pointing at the old name after its structure is renamed is
`(kernel) invalid projection`. The fragment's `Sigma.fst` is such a `proj` and
is how it was found. Both renamers now go through `Modelgen.mapConstsE`, which
handles the two node kinds that name a constant; binder names are deliberately
not touched. §8.14's alias renaming was exposed to the same gap on any model
whose emitted terms project a model-owned structure.

One piece of per-declaration glue **is** required here where arm C had none:
the currying eta lemmas, one `funext` per constructor, because `W` hands you
`(f : B' t → W) → …` and Lean's recursor wants the fields uncurried. Both W
prototypes name it as where a generator first breaks. It costs no *axiom*
beyond what the core already spends (§8.16's first correction), but it is
emitted code per constructor rather than a uniform term.

### 8.16.1 The tag scheme — `scripts/inductive-basis/WGeneric.lean`

**The thing a generator hits before the eta lemmas, and that none of the three
prototypes above settles.** `WTagged.lean`'s targets each pick their tag type
by hand — `KBT := Bool`, `KFT := Bool`, `KIT := Unit` — and the core's
signature is `{K : Type} … [DecidableEq K]`. **The fragment carries no
`DecidableEq` for any concrete `K`**, and cannot: the closure of `W`, `sup`,
`Wrec` and `Wrec_iota` takes the instance as a parameter, so it is not in the
closure. A generator must therefore either mint a bespoke enumeration
inductive per declaration and *prove* its `DecidableEq` — an nc × nc case
split, plus an inductive that `Iso.requires` then obliges the run to model in
turn — or fix one tag type for every declaration and get its `DecidableEq`
from the fragment, once.

`WGeneric.lean` builds the second, and it compiles at **0 errors, 0 warnings,
`[propext, Quot.sound]`** on every emitted constant.

```text
K  := Nat                  the tag is the constructor's index
D  : Nat → Type u          tag ↦ that constructor's non-recursive fields
B' : Nat → Type u          tag ↦ that constructor's branch type
A  := Sigma D              the label: a tag and its data
tg := Sigma.fst
```

`Nat` rather than `Fin nc`, and the second reason is the deciding one: `Nat` is
**already shared with the input** by the splice above — the kernel's
`Expr.lit` forces it — so it costs no new fragment inductive and no new
unmodelled constant in the output; and `Fin` is a structure over `Nat` whose
`DecidableEq` reduces to `Nat`'s anyway, so it would buy only the finiteness.

**Finiteness is not needed, because the junk tags are uninhabited**, and that
is the one part of this that is not obvious. `D t` for `t ≥ nc` is an *empty*
type, so `A = Sigma D` has no element whose tag is out of range and `W B' tg`
has no tree whose root label is. Had `D` sent the junk tags to `PUnit`
instead, `W` would have been strictly bigger than the target — trees the
recursor must still eliminate and no constructor produces — and **the model
would be wrong while every constructor and ι check still passed**.
`ATT.no_junk` is the check that fails if that is ever weakened; the mutation
was run and it does. The empty type is `Subtype (fun _ : PUnit => False)`,
built from what the fragment already carries, because `PEmpty` is not in it.

**What the fragment had to gain: exactly one root — and it has it.** A
`DecidableEq Nat`. `w_core.ndjson` carried `Nat.beq` and `noConfusion_of_Nat`
but not the instance, because nothing in the closure of the other four names
it — all four take it as a *parameter*. Re-exporting with `instDecidableEqNat`
as a fifth root was the whole change, so the generator never proves a decidable
equality. `Sigma.fst`, `Subtype`, `PUnit` and `False` were already in. Measured
above: 11 added declarations, no added inductive, +28.4 M instructions.

**The target is four constructors**, and the fourth is the point. Three
*shapes* — data and no children, data and two children, a recursive field under
a binder — because two cannot distinguish a dispatch that is right from one
with its arms swapped. And a fourth constructor **of the first one's shape at
another tag**, because differently-shaped arms cannot be transposed without a
type error in the `Nat.casesOn` cascade, so a file of only those never asks
whether the tag assignment is right — it asks whether it elaborates.
`CTT.leaf_ne_alt` and `CTT.iota_alt` are the two pins with no type error behind
them, and giving `alt` the tag `0` breaks exactly those.

Four mutations were run against the file and all four are caught: transposing
`node`'s children, sending the junk tags to `PUnit`, dropping `leaf`'s payload
(`CFT.tip_inj_data`'s shape, which the brief asked to carry into the generated
arm), and giving `alt` `leaf`'s tag.

### The branch scheme — `WEmitted.lean`, and the cascade does build

`WGeneric.lean` settles the **tag** scheme but picks `B'` by hand at every arm
— `Bool` because `node` happens to have two children, `Nat` because `lim`
happens to be `Nat`-branching. A generator has neither observation, so the
question it hits next is whether a *uniform* branch encoding exists whose eta
lemma can be written from a constructor telescope alone.
`scripts/inductive-basis/WEmitted.lean` answers it, against a six-constructor
target chosen so that every shape the scheme must handle appears once: no
children; no data; two children; **a plain child and an infinitary one in the
same constructor**; **data on both sides of a child**; and one arm of another's
shape at a different tag.

    D t     := Σ (a : nr₁), … Σ (a : nrₖ), PUnit        -- WVoid off the end
    Tel t j := Σ (x : X₁), … Σ (x : Xₘ), PUnit          -- WVoid off the end
    B' t    := Σ j : Nat, Tel t j

**Both towers end in `PUnit`, and that is what makes the universes work.** The
core fixes `A` and `B'` at the *same* `Type u`. A tower over the field types
alone lands at `Type (max v⃗)`, which is below `u` in general and would need a
`ULift` the fragment does not carry; ending at `PUnit.{u+1} : Type u` makes the
max exactly `u` for free, at every arity including zero. This is the reason to
keep the tower even at arity one, where `WGeneric.lean` writes the bare type.

**Every arm of the eta lemma is `rfl`, and no `Sigma.casesOn` is needed.**
Writing `b : B' t` as `⟨b.1, b.2⟩` is `Sigma`'s definitional eta, so it suffices
to prove `∀ j tel, dispatch j tel = f ⟨j, tel⟩` and instantiate at `b.1, b.2`;
at branch `j` the left side is `f ⟨j, ⟨tel.1, …, ⟨⟩⟩⟩` and the right is
`f ⟨j, tel⟩`, definitionally equal by `Sigma` eta again and `PUnit` eta at the
tower's end. The general form is therefore one `funext`, one `Nat.casesOn`
cascade over the branch index, `rfl` at each real branch and `WVoid.elim` off
the end — emittable from the telescope alone. The whole file, including the
six-arm `rec_0`, elaborates in **0.89 s** at `[propext, Quot.sound]`.

**So the brief's load-bearing doubt is refuted rather than confirmed: the
`rec_0` cascade does build in this shape, at six arms, with mixed and
out-of-order fields.**

Seven mutations were run and all seven are caught. The placement is the
surprise: **the junk being uninhabited is load-bearing for elaboration, not
only for correctness.** Sending either junk — the tag tower's or the branch
tower's — to `PUnit` does not quietly produce a `W` bigger than the target; it
fails to elaborate at the constructors and at `rec_0`, because those junk arms
are discharged by `WVoid.elim` and there is no such term at `PUnit`. That is
the inverse of the hazard §8.16 warns about, and it means the scheme resists
the failure mode structurally rather than by test. `GA.no_junk_tag` and
`GA.no_junk_branch` still fail under the mutation, so they are not vacuous;
what they guard is a junk arm discharged some *other* way.

The one mutation with no type error behind it is a **collapsed** tag
assignment: two constructors of the same shape sharing a tag, whose minors have
the same type, so `GC.leaf n` and `GC.alt n` simply become the same term. It is
caught at `GC.iota_alt` — three errors, and the narrowest of the seven. This
corrects §8.16's account above, which credits `CTT.leaf_ne_alt`: the
inequality is *false* under the mutation rather than unproven, and does not
report only because Lean propagates the ι rule's error first. The ι rule is the
pin; the inequality is the statement that says why it matters.

### The target list, measured — and the 99 is two jobs, not one

The residue was re-measured on the full corpus at this commit:
**6,707 models / 109 declines / 16,948 statements compared, none differing.**
Classifying the 109 by the reason the tool itself prints, and by the
`B factors through the tag` flag `Modelgen.tagFactored` already appends to it:

| | count | what it is |
|---|---|---|
| branching constructor, non-indexed | **46** | `recSlotOf`: two recursive fields, the tuple tower's spine is one `Nat` |
| infinitary field, non-indexed | **1** | `Turing.PartrecToTM2.Λ'.read` — a recursive field under a binder |
| indexed family, **branching erasure** | **52** | declines at the `.type` route guard, *before* arm C |
| not tag-factored | **4** | `WType`, `PSet`, `FirstOrder.Language.Term`, `PFunctor.Approx.CofixA` |
| basis exemption | **3** | `Eq`, `Nat`, `PSigma` |
| other | **3** | `Lean.Syntax…tag` (name taken), `CategoryTheory.Functor.IsHomLift`, `Acc.below` |

99 + 4 + 6 = 109, so §8.16's arithmetic is confirmed. What it does **not** show
is that the 99 are two separate jobs:

* **47 are a W arm and nothing else** — the 46 branching constructors plus
  `Turing.PartrecToTM2.Λ'`, whose one awkward field is an infinitary one and so
  is exactly `WEmitted.lean`'s `mix` arm. These are non-indexed and go straight
  through `primIso`.
* **52 need a second change first.** They are indexed families whose *index
  erasure* branches, and `armC` was guarded by `erasureLinear`
  (`armC := route matches .type && ni > 0 && erasureLinear`), so the run
  declined at the route guard **before** arm C spliced anything. A W arm alone
  does not reach them: the guard has to be relaxed so the branching erasure is
  spliced, and the prim descent then hands *it* to W, with `Iso.requires`
  withdrawing the whole model if it does not take. That is §8.15's
  splice-and-model machinery reused unchanged, but it is a second edit and a
  second set of fixtures, and it is where the arm's composition with arm C is
  actually decided. **That second edit is §8.16.3**, and the guard now reads
  `erasureBare`; the count was 51 rather than 52 once `CofixA`'s double count
  was corrected, immediately below.

The 4 not-tag-factored are the irreducible remainder and are unchanged: their
branching arity is a datum of the node, so there is no tag to factor through
and the classical route — `Classical.choice` on every constant — is the only
one that reaches them.

#### Re-measured with the arm — and the 47 closed exactly

*Full corpus, `--prim-models --check-recursors`, at the commit that lands
`armW`. The run completed under a 33 GB `ulimit -v` at about 21 GB resident.*

**6,770 models / 62 declines / 17,270 statements compared, none differing** —
against 6,707 / 109 / 16,948 above. **109 → 62 is exactly the 47** the split
predicted, and the models rise by 63 rather than by 47 because the fragment's
own seventeen inductives are modelled in turn beside them.
`Turing.PartrecToTM2.Λ'` — the one infinitary occupant, the whole reason the
`mix` arm exists — is a 24-declaration model.

| the 62 | count | what it is |
|---|---|---|
| indexed family, **branching** erasure | **51** | declines at the `.type` route guard, before arm C |
| indexed family, **infinitary** erasure | **2** | same guard, and a different second job |
| not tag-factored, non-indexed | **3** | `WType`, `PSet`, `FirstOrder.Language.Term` |
| basis exemption | **3** | `Eq`, `Nat`, `PSigma` |
| other | **3** | `Lean.Syntax…tag` (name taken), `CategoryTheory.Functor.IsHomLift`, `Acc.below` |

**Two corrections to the table above, both from splitting `erasureLinear`'s
answer into its two reasons** (`Simple.lean`'s `erasureWhy`, which the decline
now prints):

* **`PFunctor.Approx.CofixA` was counted twice.** It is *both* indexed with a
  non-linear erasure and not tag-factored, and the earlier classification put
  it in the second bucket while the tool declines it in the first. So the two
  populations were 53 and 3, not 52 and 4, and `99 + 4 + 6` was `100 + 3 + 6`.
* **The 53 are not one job either.** 51 have a *branching* erasure and 2 an
  *infinitary* one, and that is the difference between two edits. Arm C's
  `eraseCtorTy` and `spineSwap` replace a recursive field's whole domain, which
  is right exactly when the occurrence is a bare `T p⃗ e⃗` — so the branching 51
  keep every assumption arm C already makes, and what they need is for
  `ctorIdxAt`, `good`'s minor and the constructor's carve proof to carry *all*
  the recursive slots instead of the last one. The infinitary 2 break the
  erasure itself and are a different question.

  **Both halves of that prediction were carried out and both held** —
  §8.16.3 below is the branching 51, and the hypothesis was tested at the
  *first* target rather than the fifty-first: `tests/prim_carve.lean`'s `Br`
  modelled with no change to `eraseCtorTy`, to `spineSwap`, or to any
  assumption arm C makes beyond the slot count. The infinitary 2 are still
  open and are still a different question.

**What the prototypes settle.** The tag scheme, the label and branch encodings,
both junk hazards, the universe argument, the fragment's one missing root, and
the shape of the emitted `rec_0` — a cascade whose motive must be well-typed at
*every* tag, with the eta `funext` inside each arm and the junk arm discharged
from emptiness. What is left after them is a transcription, and the section
below is it.

### 8.16.2 The arm, generated — `Simple.lean`'s `armW`

*Every design question above was already settled; what follows is what came out
of `Expr`-building it. Three places the generated shape had to differ from the
prototype's, one limit the prototype could not have seen, and the mutation
table re-measured against the generator rather than against the file.*

**Where it fires.**

```text
armW := route .type ∧ ni = 0 ∧ isRec ∧ ¬erasureLinear
        ∧ tagFactored ∧ w.normalize.dec.isSome
```

`¬erasureLinear` is exactly the complement of [`Modelgen.recSlotOf`]'s two
refusals — two recursive fields in one constructor, or a recursive occurrence
that is not a bare `T p⃗` — so the arm fires precisely where the tuple tower
declines and nowhere else. **It is a fallback, not a default.** The tower
reaches every linear shape with no fragment and no axiom; moving six thousand
models onto W would spend both for nothing, and every model that took the tower
before takes it still.

**What it emits**, per target, beside the fragment:

| name | what |
|---|---|
| `T._model.wD` | tag ↦ that constructor's non-recursive fields, a `PSigma` tower |
| `T._model.wTel` | tag ↦ branch index ↦ that child's binder telescope |
| `T._model.wB` | `Σ' j : Nat, wTel p⃗ t j` |
| `T._model.wA` | `Σ' t : Nat, wD p⃗ t` |
| `T._model.wtg` | `PSigma.fst` |
| `T._model.self` | `WT.W Nat (wA p⃗) (wB p⃗) (wtg p⃗)` |
| `T._model.wF` | the core's minor: one `Nat.rec` cascade over the tag |
| `T._model.ctor_j` | `WT.sup ⟨j, tower⟩ dispatch` |
| `T._model.rec_0` | `WT.Wrec … (wF p⃗ C minors)` |
| `T._model.iota_0_j` | `WT.Wrec_iota`, and nothing else |

**`wF` is hoisted rather than inlined**, which is the one structural decision no
prototype could raise: `F` is named once by `rec_0` and once by *every* ι rule
while being itself `nc` arms deep, each arm carrying its own eta lemma and each
eta lemma its own copy of the dispatch cascade. Inlined, the emitted output is
quadratic in the constructor count and the kernel checks the same cascade
`nc + 1` times.

**Three departures from `WEmitted.lean`, each forced.**

1. **`PSigma`, not `Sigma`.** The prototype's towers are `Sigma`, whose domain
   must be a `Type`; a real constructor may have a `Prop` field. `PSigma` is
   already on [`Modelgen.primBasis`], its eta is the same structure eta, and the
   universe argument is unchanged.
2. **`PULiftP ⊤` and `PULiftP ⊥`, not `PUnit` and `Subtype (fun _ => False)`.**
   The prototype is monomorphic at `Type 0`; a real carrier sits at `Sort w` for
   a *variable* `w`, and the terminating unit has to be at exactly `Sort w` for
   the tower's `max` to come out — which is the prototype's own universe
   argument, now load-bearing at a variable level. [`Modelgen.unitAt`] and
   [`Modelgen.emptyAt`] are that at every level and are what the rest of
   `Simple.lean` already uses. The unit is *definitionally* canonical, which is
   what the eta lemma's `rfl` needs at the end of the tower.
3. **`Nat.rec`, not `Nat.casesOn`.** `casesOn` is a fragment definition under
   the prefix; the cascade is written at the shared `Nat.rec` and the succ-minor
   ignores its hypothesis.

**One limit the prototypes could not have shown, and it is real rather than a
detail.** A non-recursive field whose type *mentions a recursive field* has
nowhere to go: the data tower is exactly what the branch type does not see, so
`D` cannot hold it. `tagFactored` is the same question asked of a recursive
field's *binders* and does not reach this one, so the arm asks it separately and
declines by name.

**And the level question is asked before the fragment is spliced.** Both towers
are written with codomain level `w`, so every non-recursive field and every
recursive field's binder must satisfy `max ℓ w ≡ w` — Lean's own constraint on
the declaration, re-asked as a conversion. A field whose level keeps an `imax`
is what fails it, and it fails before 528 KB reaches the environment.

#### The mutations, re-measured against the generator

Seven, all caught, and **where** they are caught differs from `WEmitted.lean`'s
table in one instructive way. `tests/prim_w.lean` is the target: `Wt` is the
prototype's six-constructor shape, `Tree` the same branching at a parameter and
a level parameter, `Br` an infinitary child whose binder is a parameter, `Dep` a
data tower whose second field depends on its first.

| mutation | caught at |
|---|---|
| the last constructor's **label** collapsed onto tag 0 | `wF` (`Wt`, `Br`), `ctor_1` (`Tree`, `Dep`) |
| a two-child constructor's children **transposed in its dispatch** | `wF`, `ctor_3` |
| the junk **tag** inhabited | `wF`, at every target |
| the junk **branch** inhabited | `ctor_0`, at every target |
| the data tower **drops its leading field** | `ctor_4`, `wD` |
| the infinitary child's **branch index dropped** | `wF` |
| the last constructor collapsed onto tag 0 **consistently** | **`iota_0_5` and nothing else** |

**The last row is the pin, and it is the only mutation with no type error behind
it** — exactly as `WEmitted.lean` predicted. A *partial* collapse is caught
early because the generator writes the tag into three places that must agree:
the constructor's label, the recursor arm's target, and the ι rule. Collapse it
in all three at once — both towers a tag shorter, the constructor at tag 0, the
cascade one arm shorter — and the two model constructors simply *become the same
term*, with no type error anywhere. `Wt.leaf` and `Wt.alt` have the same field
telescope, so their minors have the same type; `Br.z` and `Br.lim` likewise once
`lim`'s branch tower is the empty one. The kernel then rejects
`Wt._model.iota_0_5` and `Br._model.iota_0_1` with a *declaration* type
mismatch, and nothing else in the run is red. **The ι rule is the pin, carried
into the generated arm and measured there.**

**The junk being uninhabited is load-bearing for elaboration**, and that
survives the transcription too: both junk mutations are kernel rejections at a
constructor or at `wF`, not wrong models that pass.

#### What the arm leaves behind

The fragment's own inductives — seventeen of them after the two basis
exemptions — are spliced into the output and modelled in turn by §8.13's
descent, and they are `Iso.requires`, so a fragment inductive that does not
model withdraws the whole W model. `requires` is empty for every W target after
the first in a run, and that is not a hole: [`Modelgen.genPrim`] rolls the
environment back on every withdrawal and on every decline, so a fragment that is
*present* was put there by an earlier model whose own `requires` were met.

### 8.16.3 The carve at every recursive slot — arm C's guard, relaxed to bareness

**Verdict: arm C now runs at `erasureBare` instead of `erasureLinear`, so a
constructor may have any number of recursive fields.** The branching 51 of
§8.16.2's table were the tranche; the infinitary 2 were not folded in and are
still open. `tests/prim_carve.lean` gained `Br`, `Mx` and `Sm3`, and `Br` —
which that file already held as arm C's *branching* negative — is now one of
its positives, with the header corrected in place.

**Why this is a subsection of §8.16 and not of §8.15.** The carve stands on a
spliced skeleton, and the skeleton of a *branching* family branches too. Until
arm W landed, nothing modelled a branching non-indexed inductive, so relaxing
this guard would have spliced a skeleton that could not model and
`Iso.requires` would have withdrawn every one of the 51 — a strictly worse
outcome than declining at the guard, because the run would have paid for the
splice first. The dependency is visible in the fixture: `Mx._model.skel` is a
170-declaration model because it is the first W target in `prim_carve` and
therefore the one that carries the W core, and the eighteen `_wcore` rows after
it are the fragment being modelled in turn.

**What moved.** One guard and four sites, and nothing else:

```text
armC := route .type ∧ ni > 0 ∧ erasureBare        -- was erasureLinear
```

`erasureLinear`'s single answer is split into the two reasons it always
printed. `erasureBareWhy` asks only whether every recursive occurrence is a
bare `T p⃗ e⃗`; `branchingWhy` asks whether any constructor has more than one.
Only the first still bounds the arm. `erasureLinear` survives as the
conjunction because it is what `armW`'s guard is stated by and what the census
counts the two populations with.

The four sites all read one array — `ctorIdxAt`'s `slots : Array (Nat × Array
Expr)`, one entry per recursive field in **telescope order**, where it was
`Option (Nat × Array Expr)` holding the last:

| site | at one slot | at many |
|---|---|---|
| `good`'s minor | `Eq … ∧ ih χ` | `Eq …` conjoined with a right-nested chain, one clause per child |
| the constructor | `⟨c f⃗[k ↦ fₖ.1], ⟨refl, fₖ.2⟩⟩` | every recursive field's first component into the skeleton term, every second into the chain |
| the recursor's minor | one `Eq.rec`, one IH | the same `Eq.rec`; the tail split into per-slot components, one IH per slot |
| `eraseCtorTy`, `spineSwap` | unchanged | **unchanged** — they replace a recursive field's whole domain and always did it once per field |

That last row is the load-bearing one and it is why the tranche was small: the
erasure never assumed linearity, only *bareness*. The hypothesis was tested at
the first target rather than the fifty-first — `Br` modelled on the first run
after the guard moved.

**Right-nested, and not by taste.** The tail is `B₀ ∧ (B₁ ∧ B₂)`, so the first
projection of `good` is always the index equation and the second is always
"the rest". The recursor's minor moves that rest through its index transport
**as one proof** and never has to re-associate; only the minor's own arguments
need the per-slot split, and that is the one place `chainSplit` is called.

**The ι rules are untouched.** Every arm C rule is still `Eq.refl`, proved by
the shared block, and the three reductions that carry them — definitional proof
irrelevance, the skeleton's own ι, and `PSigma` structure eta — are the same
three. The carve layer still adds no axiom of its own; what a branching target
now inherits is the *skeleton's* bill, which for a W skeleton is
`[propext, Quot.sound]` plus the `Classical.choice` that `_wcore.Acc`'s own
model spends.

#### The pin, built before the code it pins

"Skip is not pass" has a specific shape here: a carve that drops or permutes a
slot and still passes every check. Four mutations against the three new
occupants, all run interpreted (`lake build Modelgen.Simple` plus a probe, 8 s
and 0.7 s, which is how all four were measured):

| mutation | `Br` (2 slots, different indices) | `Mx` (2 slots, interleaved) | `Sm3` (3 slots, same index and type) |
|---|---|---|---|
| a slot **dropped** | red at `_model.good` | red at `_model.good` | red at `_model.good` |
| the children **permuted** in the constructor | red at `ctor_1` | red at `ctor_1` | **`ctor_1` accepted**, red at `rec_0` |
| the recursor's IH binders **reversed** | red at `rec_0` | red at `rec_0` | red at `rec_0` |
| the chain **left-associated** | **models** | **models** | red at `ctor_1` |

Every single-slot occupant in the file — `Vc`, `Two2`, `Bl`, `Fn`, `Vec`,
`Tri3` — is untouched by all four, which is what makes the table a measurement
of the new code rather than of the arm.

**The two rows that need three recursive fields, and could not be seen with
two.** `Sm3.tri`'s three children all have model type `Sm3._model.self n`, so
permuting them is not a type error anywhere in the constructor: the skeleton
term takes three first components in the wrong order and the carve proof
supplies three `good` clauses in the matching wrong order, and the kernel
accepts `ctor_1`. It is caught one declaration later, because the recursor's
minor concludes at `motive ι⃗ (T._model.ctor_j f⃗)` and the index transport's
motive is written against the skeleton term the model constructor must reduce
to. At `Br` and `Mx` the same mutation dies at the constructor, because their
children sit at different indices — so **only an occupant with interchangeable
children measures the downstream check at all**.

The last row is the sharper one. With two conjuncts there is exactly one
association, so a chain built left and split right is invisible: `Br` and `Mx`
both still model under it, statements compared and no difference. This is
`modelgen/Test.lean`'s own "two atoms cannot distinguish an ordering" in its
associativity form, and it is why the fixture's count is three.

This is §8.16.2's collapsed-tag mutation in the carve's own terms, with one
difference worth recording: there the pin was the ι theorem, because arm W's ι
is a `Wrec_iota` application and the constructors of a collapsed tag are
literally the same term. Here the ι rules are `Eq.refl` and the recursor gets
there first, so the pin is `rec_0`. **Every red cell above is a kernel
rejection with a declaration's name on it and not one is a statement
mismatch** — which is the point of building the pin: axis 3 cannot see any of
these, so if the kernel did not catch them nothing would.

#### Measured, on the full Mathlib export

*5.6 GB export, `--prim-models --check-recursors`, under a 33 GB `ulimit -v`.
Exit 0, 342.9 s wall, 23.9 GB peak RSS, **3.398 T instructions**.*

| | with §8.16.2's arm W | **and with the multi-slot carve** |
|---|---|---|
| models | 6,770 | **6,868** |
| declines | 62 | **13** |
| statements compared / differing | 17,270 / 0 | **18,434 / 0** |
| recursors checked against Lean's own / differing | — | 6,796 / 0 |
| planner level comparisons / escapes | — | 203 / 0 |

**+98 models is 49 families and their 49 skeletons**, so the denominator moves
with the numerator exactly as it did in §8.15: 6,868 / 6,881 is **99.8 %**,
against 6,770 / 6,832 = 99.1 %.

**The 13, in full** — the residue at *this* commit. §8.16.4 takes two of the
three infinitary rows away and reclassifies the third, so the standing census
is the 11 there and not this table.

| what | count | which |
|---|---|---|
| indexed family, **infinitary** erasure | 3 | `Lean.Json…_model.aux`, `Lean.PrefixTreeNode…_model.aux`, `PFunctor.Approx.CofixA` |
| **not tag-factored**, non-indexed | 3 | `WType`, `PSet`, `FirstOrder.Language.Term` |
| basis exemption | 3 | `Eq`, `Nat`, `PSigma` |
| name taken | 2 | `Lean.Syntax…_model.tag`, `Lean.Syntax…_model.aux` |
| singleton boundaries | 2 | `CategoryTheory.Functor.IsHomLift`, `Acc.below` |

**49 and not the 51 §8.16.2 predicted, and the two are both accounted for
rather than lost.** The arithmetic closes exactly: 51 = 49 closed + 1 + 1.

* **`Lean.Syntax._model.0._model.aux` passed the guard and stopped one step
  later**, at `ensurePSigma`'s name guard — that file declares `PSigma`
  itself, and the tuple tower's carrier needs it, which is why its sibling
  `_model.tag` was already declining there. So it moved from the erasure
  bucket to the name-taken bucket, which is a **better** decline: it now names
  the real obstruction instead of one that had merely been reached first.
  The old table's "other 3" is this row's "name taken 2" plus the two
  singletons, and it should have read 4.
* **One was misfiled as branching by the old classifier.** `erasureWhy` used to
  scan constructors in order and return the *first* failing one's reason,
  asking bareness and branching of each constructor together — so a
  declaration whose first offending constructor branches and whose *later*
  constructor is infinitary was reported "branching" and counted among the 51,
  though no slot count would ever have closed it. Splitting the test into
  `erasureBareWhy` (any constructor, anywhere) and `branchingWhy` is what
  makes the two populations countable, and it moves one declaration from 51 to
  the infinitary bucket, which is why that bucket reads 3 here and 2 there.
  **It is `Lean.Json…_model.aux`**, and §8.16.4's dump of that family is what
  says so: its `aux.3.cons` has two bare recursive fields and comes *before*
  `aux.5.inner`, so the old scan reported *branching* and stopped.
  `Lean.PrefixTreeNode…_model.aux` reaches its own redex at `aux.3.inner`
  before any constructor branches, so it was always in the infinitary bucket.

**The certifiability column, which is not the coverage column.** Every one of
the 49 has a *branching* erasure by construction — that is what the guard was
stopping — so every one of their skeletons takes arm W, and none takes the
tuple tower. The target's own model is `[propext, Quot.sound]`; the
`Classical.choice` in the output comes from `_wcore.Acc`'s model (arm G), one
declaration shared by every W target, and `Iso.requires` means it cannot be
dropped. So the two columns for this tranche are **49 closed** and **49
certifiable but none choice-free** — unlike §8.15's original 29, which spend no
axiom at all. The carve layer itself still adds nothing: it is the skeleton's
bill, inherited.

**And the guard's remaining refusal has a fixture again.** `Br` was
`prim_carve`'s occupant of `erasure linear: no`, and this tranche turned it
into a model — which would have left arm C's one live shape guard with nothing
exercising it, the exact shape of a coverage loss that a green suite does not
report. `Inf2` (`inode : (n : N) → (N → Inf2 n) → Inf2 (N.s n)`) replaces it
and declines at `erasure … is not bare`, which is the half of the old reason
that is still open and is what the three infinitary corpus occupants above hit.

### 8.16.4 The infinitary residue — two were a redex, one is a W-type

**Verdict: §8.16.3's "3 infinitary erasures" are two shapes and not one, and
the larger half was never infinitary.** `Lean.Json…_model.aux` and
`Lean.PrefixTreeNode…_model.aux` were declining on an **unreduced application**
that this file's guards read as a lambda; they model now, and nothing about the
erasure had to move. `PFunctor.Approx.CofixA` is the real shape, and it does
not belong in this bucket at all — it belongs with `WType`.

The brief that opened this tranche asked whether the three were one shape. They
are not, and the answer came at the *first* target rather than the third: one
dump of `Lean.Json._model.0._model.aux`'s constructors was enough.

#### What the two were

Lean's nested specialisation instantiates a container's parameters and does not
βζ-normalise what comes out. `Std.DTreeMap.Internal.Impl α β` has a **dependent
value field**

```text
Impl.inner : Nat → (k : α) → β k → Impl α β → Impl α β → Impl α β
```

and both `Lean.Json` and `Lean.PrefixTreeNode` nest through it — through
`Std.TreeMap.Raw`, which is that type — at `β := fun _ => T`. So the
specialised block, and therefore the `_model.aux` family the composition hands
layer 3, carries the field as written:

```text
Lean.Json._model.0._model.aux.5.inner :
  Nat → (k : String) →
    (fun x => Lean.Json._model.0._model.aux Lean.Json._model.0._model.tag.0) k →
      … aux tag.5 → … aux tag.5 → … aux tag.5
```

`Expr.getAppFn` of that third field is a **lambda**, so `erasureBareWhy`'s
`dom.getAppFn.isConstOf tname` answered *no* and the declaration was reported
as having "a recursive occurrence that is not a bare `T`" — an infinitary
field. There is no binder over the occurrence. There is an application nobody
reduced.

**This is §5.1 one layer down, and it is the same function that fixes it.**
§5.1 is exactly this defect at layer 1, where it cost these same two
declarations their *nested* models until [`Modelgen.Gen.occIdx?`] and its two
siblings started reading a type's head through [`Modelgen.headNorm`] — β and ζ,
iterated, no constant unfolded. What §5.1 could not see is that layer 1's
output is layer 3's input: the block it repairs is the block the composition
then hands `primIso`, and the redex is still in it. So the repair is the same
call in four more places and deliberately not a second function.

#### What moved

Four guards, and each asks a question whose answer is invariant under βζ:

| site | the question |
|---|---|
| `erasureBareWhy` | is every recursive occurrence a bare `T p⃗ e⃗`? — arm C's guard |
| arm C's `ctorIdxAt` | what are that occurrence's index arguments? |
| [`Modelgen.recSlotOf`] | the same bareness question, for the tuple tower |
| [`Modelgen.tagFactored`] | what binders does a recursive field have? — a redex has none to peel until it is reduced |

**`mentionsAny` is left on the *written* domain and no emitted type is
normalised.** That is the constraint that keeps the change to four lines:
[`Modelgen.eraseCtorTy`] and [`Modelgen.spineSwap`] replace a recursive field's
**whole domain**, so the only thing they need from the guard is agreement about
*which* fields are recursive — and a domain they replace entirely, they never
read. A declaration whose constructor types are already βζ-normal — every one
that modelled before — therefore takes exactly the path it took before, byte
for byte, and the control run confirms it: with `headNorm` neutralised the
report over a 2.37 M-line Mathlib prefix differs in **exactly these two
declarations and their two skeletons**, and in nothing else.

#### The one that stays, and why it is filed under the wrong heading

```text
PFunctor.Approx.CofixA F : ℕ → Type (max uA uB)
  | continue : CofixA F 0
  | intro {n} : ∀ a, (F.B a → CofixA F n) → CofixA F (n+1)
```

`F.B a → CofixA F n` is a **real** function type: there is a binder, the
occurrence is under it, and there is no whole domain for the erasure to
replace. But the second fact about it is the one that settles the bucket: the
binder's type is `F.B a`, which mentions the constructor's **earlier field**
`a` — so `B` does not factor through the tag, and the run has been printing
`B factors through the tag: no` on this decline all along. Its index erasure,
if one could be taken, is

```text
Skel | intro : ∀ (a : F.A), (F.B a → Skel) → Skel
```

which is `WType F` — the very declaration in the not-tag-factored bucket
beside `PSet` and `FirstOrder.Language.Term`. So closing the erasure for
`CofixA` would splice a skeleton arm W declines, `Iso.requires` would withdraw
the model, and the run would have paid for the splice first. **`CofixA` is a
true W-type wearing an index**, and the honest census files it with the other
three rather than with the two that were an artifact.

#### The residue the guard keeps, named rather than hand-waved

A field can mention `T` **only inside a binder that βζ discards**. A container
at `β := fun _ => N` whose *key* is the recursive one gives

```text
(fun x : T p⃗ e⃗ => N) k
```

whose reduct is `N`: the field is not recursive, and the only occurrence of `T`
is in a binder type the reduction throws away. `mentionsAny` says *recursive*
— it must, because `eraseCtorTy` replaces on that test — and the erasure would
then replace a domain that is not recursive at all. Closing this needs the
erasure to **normalise** a field rather than replace it, which is a different
construction; no declaration in Mathlib is this shape, so it is declined and
named. `nest_fam_arg`'s `OK` and `Key` are the two fixture occupants, and their
message says **vanishing mention** and never *infinitary* — there is no binder
over an occurrence, because there is no occurrence.

#### The pin

`modelgen/tests/nest_fam_arg.lean` is §5.1's own sweep over how a container is
*applied*, so it is already the file that holds this shape — and it has moved
from `expectedOwn` to **`expectedPrim`**, because the redex reaches layer 3 and
that is where it now has to be measured. The row asserts everything the
non-prim row did, in the same order, and the composition's third step besides:
nine `_model.aux` families and their nine skeletons, 337 statements compared
against the installed recursors' own rules with 0 differing, 36 recursors
against Lean's with 0 differing.

Three mutations, all run interpreted (`lake build Modelgen.Simple` plus a
probe):

| mutation | result |
|---|---|
| `headNorm` → identity at all four sites | all nine `_model.aux` rows lost; every one back to `infinitary` |
| `headNorm` → β only, no ζ | **exactly `Zeta` lost**, the other eight unaffected |
| the guard reads through `headNorm`, `ctorIdxAt` does not | all nine lost, and the *failure mode is a decline* — `…'s recursive field is not `T` at n parameters and m indices` — not an emission |

The second is the row that makes the pin a measurement rather than a
restatement: `Zeta.obj : RB N (fun _ => let X := L Zeta; X) → Zeta` is the only
occupant whose reduct needs ζ as well as β, and one `headBeta` loop passes the
other eight. The third is the one that matters for safety: the guard and the
index reader must agree about the same field, and when they do not, arm C
refuses rather than carving against the wrong index vector.

`prim_carve`'s `Inf2` is untouched and is still the erasure guard's live
occupant — `inode : (n : N) → (N → Inf2 n) → Inf2 (N.s n)` is a real binder,
which is exactly the shape `CofixA` is and this tranche does not close. So no
occupant had to be replaced here.

#### Measured, on the full Mathlib export

*5.6 GB export, `--prim-models --check-recursors`, under a 33 GB `ulimit -v`.
Exit 0, 337.8 s wall, 23.9 GB peak RSS, **3.400 T instructions**.*

| | §8.16.3 | **and reading the head through `headNorm`** |
|---|---|---|
| models | 6,868 | **6,872** |
| declines | 13 | **11** |
| statements compared / differing | 18,434 / 0 | **18,474 / 0** |
| recursors checked against Lean's own / differing | 6,796 / 0 | 6,796 / 0 |
| planner level comparisons / escapes | 203 / 0 | 203 / 0 |

**+4 models is 2 families and their 2 skeletons**, so the denominator moves
with the numerator again: 6,872 / 6,883 is **99.84 %**. The instruction count
is +0.06 %, which is the two extra models and not the reduction — `headNorm`
runs only at four guards and is the identity on every βζ-normal domain.

**The whole report diffs in four lines.** Against §8.16.3's run over the same
5.6 GB input, the only changes anywhere in 6,872 models are the two new
`_model.aux` rows, their two `_model.skel` rows, and the two declines those
replace. The recursor count does not move, because these are declarations the
composition emits and not the export's own.

**The 11, in full** — the standing residue of the third construction on
Mathlib, every one classified:

| what | count | which |
|---|---|---|
| **not tag-factored** — the true W-types | 4 | `WType`, `PSet`, `FirstOrder.Language.Term`, `PFunctor.Approx.CofixA` |
| basis exemption | 3 | `Eq`, `Nat`, `PSigma` |
| name taken | 2 | `Lean.Syntax…_model.tag`, `Lean.Syntax…_model.aux` |
| singleton boundaries | 2 | `CategoryTheory.Functor.IsHomLift`, `Acc.below` |

**The infinitary bucket is gone as a bucket.** Two of its three occupants were
an artifact of how the guard read a redex; the third is a W-type and is filed
with the W-types, which is why that row reads 4 where §8.16.3's read 3. The
declaration is *also* indexed and *also* infinitary and the tool still declines
it at the erasure guard — the reclassification is about which job would close
it, and that job is a non-tag-factored W, not an erasure.

**What each remaining class would take**, so that 11 is a plan and not a
remainder:

* **the 4 W-types** need a `B` that can see the label's data, which is
  `WFromPaths.lean`'s decidable-equality step at the label type and costs
  `Classical.choice` on every constant — §8.16 measured that trade and took the
  tagged construction instead. This is the one class where the *certifiability*
  column, not the coverage column, is what is holding.
* **the 3 basis primitives** are the exemption that makes the construction
  well-founded and must stay unmodelled.
* **the 2 name-taken** are not a shape at all: `Lean.Syntax` is replayed at
  line 9,948 of the export and `PSigma` at line 95,424, so when the
  composition's third step reaches `Lean.Syntax._model.0._model.tag` the
  primitive it needs is *reserved by the input and not yet installed*.
  `runFilter` already has the machinery for that — `waitingPrim` holds a model
  back until [`Modelgen.primReady`] — but [`Modelgen.primCompose`] passes
  `canWait := false` and has no way to reach the queue, so a composition-emitted
  declaration cannot wait where an input declaration can. **This is a different
  class from the `_mgalt` alias-root retry**, which fires on
  `Decline.nameLost` (our own name, normalised onto another of ours) and not on
  `Decline.nameTaken` (the input's name, coming later); the retry is working as
  designed and these two were never in its reach.
* **the 2 singleton boundaries** are `Acc.below`'s index that is not one of its
  own data fields, and `IsHomLift`'s index expressions that mention its own
  fields — both `MODELGEN.md` §8.7's and arm F's own limits, unchanged.

### 8.16.5 The two name-taken — a primitive that is late, not a name that is lost

**Verdict: they were a different class from the `_mgalt` alias-root retry, and
the retry was never at fault.** `Lean.Syntax._model.0._model.tag` and
`…_model.aux` decline `prim model name taken (PSigma)`, and that is
[`Modelgen.Decline.nameTaken`] — the **input's** name, which we may not take at
any spelling — where the retry answers [`Modelgen.Decline.nameLost`] — **our**
name, normalised onto another of ours, which we may rename freely because
nothing in the input holds it. Two constructors, two opposite responses, and
§8.14 says so where it introduces them. Nothing here reflects on the alias
root: `_mgalt` occurs zero times in the 5.6 GB output before this change and
zero times after.

#### What it actually is

The Mathlib export replays `Lean.Syntax` at line **9,948** and `PSigma` at line
**95,424**. A prim model's carrier is a right-nested `PSigma` chain, so at line
9,948 the model would have to *splice* `PSigma` — into a file that declares its
own eighty-five thousand lines later. That splice is refused, correctly: the
name is reserved and `Environment` cannot rebind a constant.

`runFilter` has had the answer to exactly this since §1.6: `waitingPrim` holds
a prim model back until [`Modelgen.primReady`] — every basis constant either
installed or not declared by the input at all — and generates it after the
input's own declaration arrives. **What was missing is that the composition's
third step could not reach that queue.** `waitingPrim` is `runFilter`'s local,
and [`Modelgen.primCompose`] is called from inside `genMutual` and from the
nested arm, both of which thread only `(out, rep, pending)`. So it passed
`canWait := false`, and a model of a declaration *the tool itself emitted*
declined at a primitive that was merely late, where a model of one of the
input's own would have waited.

So this is neither a shape nor a name: it is **one queue two of the three
callers could not see**.

#### What moved

`primCompose` and `genMutual` return a second component — the jobs they
deferred, at `waitingPrim`'s own element type — and `runFilter` appends them to
the queue at all four call sites. `canWait := false` at the end-of-file drain,
where nothing more is coming and a decline is the honest answer. The
declaration's type and its constructors' types are read at the block, where the
member is known to be installed; the drain only calls
[`Modelgen.genPrim`] with them.

**The deferred model is emitted after the input's own `PSigma` record** rather
than beside the block it models, and that is sound for the same reason §8.13's
splice ordering is: the export only requires a declaration to precede its uses,
and this one uses `Lean.Syntax._model.0._model.aux` and `PSigma`, both earlier.

`primCompose` defers **only when `primReady` is false**, so every composition
model that ran inline before still runs inline. That condition is a
minimal-disturbance guarantee and not a correctness one, and the fixture says
so rather than implying otherwise: mutating it to defer unconditionally leaves
the suite **green**, because `runFilter` drains the queue immediately after the
very next record and the report order does not move. The mutation that is red
is the one that matters — `canWait := false`, the old behaviour — and it takes
all four composition models in the fixture back to `prim model name taken
(PSigma)`.

#### The fixture

`modelgen/tests/prim_late_basis.lean`, and its layout is the whole claim:
`Eq` first; a three-member **mutual** block `MA`/`MB`/`MC` and a **nested**
`Nd`, both before `PSigma`, because the third step has two callers and a repair
at one would leave the other declining; `PSigma` last, at Lean's own shape, so
[`Modelgen.checkPSigma`] runs on it; and `Pre`, a simple inductive before
`PSigma`, as the control — its model is an *input* declaration's and rides the
queue that already existed, so a repair that broke that wait while adding this
one is red in the same file. `Nat` is deliberately not declared: it is spliced,
and the report says so with a splice line rather than a wait, which is the case
the queue must not fire on.

**The row's order is the assertion.** `MA`, `Nd` and `Nd._model.0` are
generated at their own declarations — layers 1 and 2 need only `Eq` — and
everything from `N` on is the drain at the input's own `PSigma`, in queue
order: the three input declarations that were already waiting, then the four
the composition emitted. A composition row that climbed back above `N` would
mean the third step had stopped waiting.

#### Measured, on the full Mathlib export

*5.6 GB export, `--prim-models --check-recursors`, under a 33 GB `ulimit -v`.
Exit 0, 328.6 s wall, 23.9 GB peak RSS, **3.398 T instructions**.*

| | §8.16.4 | **and with the composition able to wait** |
|---|---|---|
| models | 6,872 | **6,875** |
| declines | 11 | **9** |
| statements compared / differing | 18,474 / 0 | **18,494 / 0** |
| recursors checked against Lean's own / differing | 6,796 / 0 | 6,796 / 0 |
| planner level comparisons / escapes | 203 / 0 | 203 / 0 |

6,875 / 6,884 is **99.87 %**. **+3 models is the tag, the `aux` and the `aux`'s
skeleton**, and the whole report diffs in **four lines**: those three, plus
`Lean.RArray` falling from 166 declarations to 12 because it is no longer the
first W target in the run — `Lean.Syntax…_model.aux._model.skel` now is, and
carries the fragment's splice. That number has been an ordering fact since
§8.16.2 said so of `Tree`, and it moving is the ordering changing, not a model.

**The output was replayed from bytes with the kernel on**, and this is the
oracle the change actually needed: **692,856 declarations accepted, 0
rejected**, over the whole 5.85 GB emitted file, from an empty environment
(`envprobe target/…/wait.out.ndjson C`, 1,263.6 s, 24.8 GB peak). `modelgen`'s
own `addChecked` checks each declaration against the environment *it* has
built, where the `aux` was installed back at the block — so a model emitted at
a **different position in the file** is precisely the kind of change that check
cannot see, and only a replay from nothing can. A deferred model that landed
before something it uses would be a `unknown constant` here and is not.

**The 9, in full** — the residue of the third construction on Mathlib *at this
commit*, every one classified. §8.16.7 is where three of them stop being
declines and the row below that names four is corrected to three:

| what | count | which |
|---|---|---|
| **not tag-factored** — the true W-types | 3 | `WType`, `PSet`, `FirstOrder.Language.Term` |
| **infinitary and indexed** — arm C's erasure guard, not `tagFactored`'s | 1 | `PFunctor.Approx.CofixA` |
| basis exemption | 3 | `Eq`, `Nat`, `PSigma` |
| singleton boundaries | 2 | `CategoryTheory.Functor.IsHomLift`, `Acc.below` |

Four classes, and **two of them are closed by definition**: the basis
exemption is what makes the construction well-founded and must stay unmodelled,
and the two singleton boundaries are arm G's and arm F's own limits — an index
that is not one of the constructor's data fields, and index expressions that
mention the constructor's own fields. So the *whole* remaining question about
this construction's reach on Mathlib is **two classes of four declarations
between them**: three whose `B` needs to see the label's data, which is
`WFromPaths.lean` and costs `Classical.choice` on every constant — §8.16 took
the tagged construction over it deliberately, §8.16.6 found the two are one
construction and §8.16.7 landed it — and one that is indexed and infinitary,
which no arm reaches at all.

### 8.16.6 Stage 1 of the untagged arm — the two constructions are one

**Verdict: `WFromPaths.lean` is `WTagged.lean` at `K := A` and `tg := id`.**
§8.16 has presented them as two constructions with two bills since it was
written, and the *bills* are two — but the construction is one, and the
untagged arm is therefore an instantiation of the fragment already spliced
rather than a second fragment.
`scripts/inductive-basis/WUntagged.lean` is stage 1 and it is green.

**Why now.** §8.16 measured the trade — the untagged path decides `x.1 = a` at
the *label* type, which is `Classical.propDecidable` — and declined it because
`Classical.choice` was uncovered. It is covered: `derived/src/choice/epsilon.rs`
(rule 7) stands on `kernel`'s 0-ary Henkin constant, and
`waiting:axiom(Classical.choice)` on `mini/tests/fixtures/standard_axioms.lean`
went 4 → 2 → 0. So the ceiling §8.16 put on the residue is no longer a ceiling,
and what was a certifiability question is a coverage question again.

#### The two things that had to be checked

* **`K` may live at `Type w`.** The core was written `{K : Type}` because `Nat`
  is, and the untagged instantiation needs `K := A : Type u`. Widening the
  three binders costs **no proof change at all** — `Edge`, `PTree` and `W` land
  at `Type (max w u)`, which normalises to `Type u` at both `w := 0` (the
  tagged arm, `K := Nat`) and `w := u` (untagged, `K := A`). The core in
  `WUntagged.lean` is `w_core.lean`'s with exactly that edit and every proof
  byte-identical.
* **`DecidableEq A` is the entire price.** `WT.decEqAll α := fun a b =>
  Classical.propDecidable (a = b)`, one declaration, and `#print axioms` puts
  the untagged ι rules at `[propext, Classical.choice, Quot.sound]` against the
  tagged ones' `[propext, Quot.sound]`. **Two columns, not an average**: the
  ~50 arm-C skeletons and the arm-W targets that are tag-factored stay
  choice-free at the arm; only a declaration that *needs* the untagged
  instantiation pays.

#### What is actually new — the branch scheme

The carrier is not the hard part. At the tag scheme `Tel` is a function of the
**tag**, which is exactly why a recursive field's binders may not mention the
constructor's fields. Untagged, `B' : A → Type u`, so

```text
Tel a j := Nat.rec (motive := fun t => D t → Nat → Type u) … a.1 a.2
```

— the cascade is still on the tag, but **the data is an argument of the
motive**, and each arm receives that constructor's own `D t` to project out of.
That one change is the whole delta; the dispatch, the eta lemma and the ι rules
follow it. `WUntagged.lean`'s `Tm` carries every hazard at once: a child whose
binder is field 0 (`WType`'s and `Term`'s shape), a constructor with **two**
children of which only the first has binders, a non-recursive field *between*
the one the binder mentions and the child, and a base constructor.

**All three ι rules are `WT.Wrec_iota` and nothing else.** `F`'s arms transport
along their constructor's eta lemma, and at an ι rule that equation is between
a dispatch and itself — so the proof is `rfl` by definitional proof
irrelevance and the `cast` computes away. The recursor is checked against
Lean's own `Tm.rec`: the file substitutes the model's carrier and constructors
into the type Lean minted and asks `isDefEq`, which is §4's oracle 3 in one
step.

#### The mutations, and the one that is green

| mutation | result |
|---|---|
| `Tel` reads a constant bound instead of the label's data | red at three sites |
| `mix`'s second IH read from branch 0 instead of branch 1 | red |
| the eta transport dropped from `F`'s `app` arm | red |
| `D`'s junk-**tag** arm inhabited | red |
| `Tel`'s junk-**branch-index** arm inhabited | red |
| `Tel`'s junk-**tag** arm inhabited | **green** |

The green row is a fact about the scheme and not a hole in the pin. A label at
a junk tag is already impossible — `A = Σ' t, D t` and `D`'s own junk arm is
empty — so `Tel` is never asked at a tag no constructor has. §8.16.2's "junk
uninhabited in both directions" is therefore one requirement on `D` and one on
`Tel`, and only the **branch-index** half of `Tel`'s is a requirement at all;
within a real tag the index does range over all of `Nat`.

#### What it closes, and the one it does not

Three of §8.16.5's nine: `WType`, `PSet` and `FirstOrder.Language.Term`, which
are precisely the declines reading `B factors through the tag: no` with
`carrier is Type u: yes`.

**`PFunctor.Approx.CofixA` is not one of them, and the census row that groups
it with them is about which job would close it rather than which guard stops
it.** It is an **indexed** family and declines at arm C's erasure guard, long
before `tagFactored` is asked:

```text
intro {n} : ∀ (a : F.A), (F.B a → CofixA F n) → CofixA F (n+1)
```

has its recursive occurrence under a binder, and `eraseCtorTy`/`spineSwap`
replace a recursive field's *whole domain* — there is nothing to replace. This
scheme would model the skeleton that erasure *would* produce (`Skel | intro :
∀ a, (F.B a → Skel) → Skel` is `WType F`), so `Iso.requires` would be met; what
is missing is the erasure. That is an **infinitary arm C** — `eraseCtorTy`
walking into a field's own forall-telescope to replace only the final
`T p⃗ e⃗`, and `good`, its minor and the carve proof carrying a slot whose
clause is `∀ b, good (f b) ι⃗` and whose induction hypothesis is
`∀ b, motive ι⃗ (f b)`. **Two jobs, not one**, and the untagged arm alone takes
the census to **6**, not to 5.

#### What remains, named

Stage 1 is done; stage 2 is the transcription, and it is bounded:

1. **The fragment**, `modelgen/tests/w_core.lean`: widen `K` to `Type w`, add
   `WT.decEqAll` and a sixth `--#export` root, re-export. Deliberately **not
   landed here** — it grows the fragment by `Classical.propDecidable`'s closure
   and `Iso.requires` obliges every W target to model whatever inductives that
   brings, so it is dead weight until a consumer exists.
2. **Five level lists in `Simple.lean`** — `wCoreSelf`, `wCoreSup`, `wCoreRec`,
   `wCoreIota` gain the `K` level; the tagged arm passes `0`.
3. **The arm, parameterised rather than duplicated.** `wTelN`'s type becomes
   `∀ p⃗, A p⃗ → Nat → Sort w`, `wTgN` becomes the identity, `wDecEq` becomes
   `decEqAll (A p⃗)`, and `wTelTy`, `wDispAt`, `wCtorParts`, `wMkF` and the eta
   lemma thread the label where they thread the tag. The guard is `armW`'s with
   `tagFactored` **false** instead of true, so the tagged path is untouched and
   stays choice-free.
4. **`envprobe … C` on the emitted file**, as §8.16.5 needed it: the untagged
   arm splices and defers, and `addChecked` cannot see output position.

### 8.16.7 The untagged arm, generated — stage 2

**Verdict: arm W now runs the one core at both instantiations, and the three
declines that were `tagFactored`'s are models.** The four steps above are done
and the estimate held: the guard, four declarations of the six, and one new
shape. [`Modelgen.labelFactored`] is the arm's guard and
[`Modelgen.tagFactored`] picks the bill.

Three and not four: §8.16.5's census row groups `PFunctor.Approx.CofixA` with
the W-types, and §8.16.6 is where that was corrected — it is *indexed* and
declines at arm C's erasure guard, before `tagFactored` is asked. Nothing here
touches it.

#### Where the two instantiations differ, in full

`D` and `A` are literally the same term at both, and so are the constructors,
`wF`, `rec_0` and every ι rule up to which constants they name. What differs:

| | `K := Nat`, `tg := PSigma.fst` | `K := A`, `tg := id` |
|---|---|---|
| `T._model.wTel` | `∀ p⃗, Nat → Nat → Sort w` | `∀ p⃗, A p⃗ → Nat → Sort w` |
| `T._model.wB` | `∀ p⃗, Nat → Sort w` | `∀ p⃗, A p⃗ → Sort w` |
| `T._model.wtg` | `PSigma.fst` | the identity |
| `DecidableEq K` | `instDecidableEqNat` | `WT.decEqAll (A p⃗)` |
| the core's level lists | `…, 0` | `…, u` |
| the ι rules' axioms | `[propext, Quot.sound]` | `+ Classical.choice` |

**The one new shape is `Tel`'s outer cascade**, and it is stage 1's: the
cascade is still a `Nat.rec` on the tag — the tag is still a `Nat`, and `A` is
still `Σ' t : Nat, D t` — but its motive is `fun t => D p⃗ t → Nat → Sort w`, so
each arm receives that constructor's own data and projects out the fields its
children's binders mention. In the generator that is
[`Modelgen.primIso`]'s `wRecDom`: constructor `k`'s recursive field `r` with
its non-recursive fields replaced by whatever the caller has in their place —
the fields themselves inside a constructor's own body, the label's projections
inside `F`. **It is the identity wherever `tagFactored` holds**, because there
the domain mentions no field at all — so every term the tagged path builds is
the term it built before, and the conditional on `A`'s position keeps the
declaration order too. That is an argument and not a measurement: what *is*
measured is that the tagged targets' statements and recursors still compare
clean (`prim_w`: 72 statements, 10 recursors, 0 differing) and that their
`#print axioms` is still `[propext, Quot.sound]`.

`A` is emitted before `Tel` at the untagged instantiation and after `B'` at the
tagged one, which is the only other thing that moves: untagged, `Tel` and `B'`
name `A` in their own types.

#### The guard, and a boundary that cannot be written down

`labelFactored` is `tagFactored` weakened to refuse only a recursive field's
binder mentioning an earlier **recursive** field — the label carries the
constructor's data but no children, so that is the one thing `Tel` cannot read.

**No fixture refuses it, and the reason is worth recording rather than
papering over.** The shape is not writable in Lean source: a genuinely
dependent `(Fam x → T)` needs `Fam : T → Type` before `T`, and the degenerate
`((fun _ : T => P) x → T)` is beta-reduced by the elaborator to `(P → T)`
before it reaches the export — measured, not assumed. What can carry it is an
input that already holds a redex, which is §5.1's class (`nest_fam_arg`'s `Key`
and `Zeta`), so the guard is not dead code; it is a precondition with no
Lean-writable counterexample. And it is not load-bearing for soundness either:
the mutation that removes the substitution `wRecDom` performs is a kernel
*rejection* — `declaration has free variables` — at `wTel`, so a generator that
ignored the precondition declines rather than emits.

Like `tagFactored`, it reads a field's own head through
[`Modelgen.headNorm`] but not its binders' — a binder type that mentions an
earlier field only inside a redex is refused. That is conservative in the safe
direction: a decline, never a model.

#### The mutations, measured against the generator

`tests/prim_w.lean` gained `Wty` — `WType` itself, at a parameter family and a
level parameter, which is what the corpus actually declined — and `Utd`, whose
`mk` has **two** children whose binders read **different** fields of one label
and whose `gap` has data on both sides of a label-dependent child. `Bad`, which
was this file's one decline, is the third.

| mutation | caught at |
|---|---|
| the branch tower stops reading the label's data | `wTel`, at all three |
| it reads the data, but always field 0 | `ctor_1`, at **`Utd` alone** |
| the key's label collapsed onto tag 0 | `ctor_1` (`Bad`, `Utd`) |
| `Tel`'s junk **branch index** inhabited | `ctor_0`, at every W target |
| `F`'s frame keeps the tagged key | `wF`, at all three |
| `Tel`'s junk **tag** inhabited | **green** |

**The second row is why `Utd` exists.** `Bad` and `Wty` have one non-recursive
field each, and a dispatch that reads every child's tower out of field 0 is
*right* when there is only one field to read: both stay green under that
mutation and only `Utd`, whose two children read `k` and `j`, goes red. A
fixture with one datum cannot pin *which* datum is read.

**The last row is stage 1's green and must stay green.** A label at a junk tag
is already impossible — `A = Σ' t, D t` and `D`'s junk arm is empty — so `Tel`
is never asked at a tag no constructor has. §8.16.2's "junk uninhabited in both
directions" is one requirement on `D` and one on `Tel`, and only the
**branch-index** half of `Tel`'s is a requirement at all.

The *consistent* tag collapse — §8.16.2's last row, the one mutation with no
type error behind it — is not re-measured here and does not need to be: the tag
assignment, the cascade arity and the ι rule are the same generator code at
both instantiations, and the untagged analogue of a *partial* collapse is row
three above.

#### Two things the fragment change cost, neither of them free

**`Classical.choice` and `Nonempty` are now shared names.** §8.16's sizing of
`wCoreShared` at six, corrected to sixteen when `Eq` and `Iff` went on it, is
the argument again one level down: `mini/src/axiom.rs`'s `clause_for` selects
the choice clause by the exact name `Classical.choice`, so a `_wcore` copy is a
non-standard axiom and is declined downstream — and its *statement* is
`∀ {α : Sort u}, Nonempty α → α`, so a `Classical.choice` under Lean's name
whose antecedent is `_wcore.Nonempty` is worse than a decline. Twenty names.

**And that made a late primitive of `Nonempty`.** `w_core.ndjson`'s own `Acc`
arrives through `WellFounded.fix`; its `Nonempty` arrives only through
`Classical.propDecidable`, which is later. Arm G's model of `Acc` therefore lost
to `prim model name taken (Nonempty)` — §8.16.5's class exactly, a primitive
that is late rather than a name that is lost. `fxNames` is now
[`Modelgen.lateSpliceNames`] and carries the choice names beside the quotient's;
the wait fires only for a model that has *already declined* at one of them, so
no model that does not touch them moves. `Test.lean`'s `w_core` row is where the
difference shows: `Acc` is last in the list rather than in the middle.

#### Measured, on the full Mathlib export

*5.6 GB export, `--prim-models --check-recursors`, under a 33 GB `ulimit -v`.
Exit 0, **3.436 T instructions** (350.8 s wall on a contended box — the
instruction count is the comparable number).*

| | §8.16.5 | **and with the untagged instantiation** |
|---|---|---|
| models | 6,875 | **6,878** |
| declines | 9 | **6** |
| statements compared / differing | 18,494 / 0 | **18,501 / 0** |
| recursors checked against Lean's own / differing | 6,796 / 0 | 6,796 / 0 |
| planner level comparisons / escapes | 203 / 0 | 203 / 0 |
| instructions | 3.398 T | **3.436 T** (+1.1 %) |

6,878 / 6,884 is **99.91 %**, and **+3 is exactly the three §8.16.6 named**:
`WType` at 10 declarations, `PSet` at 10, `FirstOrder.Language.Term` at 12.
Nothing else in the report moved — the fragment still goes in once, at
`Lean.Syntax._model.0._model.aux._model.skel`, and `Lean.RArray` is still 12.

**The 6, in full:**

| what | count | which |
|---|---|---|
| basis exemption — closed by definition | 3 | `Eq`, `Nat`, `PSigma` |
| singleton boundaries — closed by definition | 2 | `CategoryTheory.Functor.IsHomLift`, `Acc.below` |
| **indexed and infinitary** — the one open class | 1 | `PFunctor.Approx.CofixA` |

Its decline now reads `B factors through the tag: no; through the label: yes;
carrier is Type u: yes; why: infinitary: PFunctor.Approx.CofixA.intro has a
recursive occurrence that is not a bare PFunctor.Approx.CofixA`. That is the
new bill line earning its keep: the label question is *not* what stops it, so
what remains is **arm C's erasure walking into a field's own forall-telescope**
— `eraseCtorTy` replacing only the final `T p⃗ e⃗` rather than the whole domain,
and `good`, its minor and the carve proof carrying a slot whose clause is
`∀ b, good (f b) ι⃗` and whose hypothesis is `∀ b, motive ι⃗ (f b)`. This scheme
would model the skeleton such an erasure produces — `Skel | intro : ∀ a, (F.B a
→ Skel) → Skel` *is* `WType F` — so `Iso.requires` would be met. One
declaration, and the whole of what the third construction does not reach.

**The output was replayed from bytes with the kernel on, and this arm needed it
for the reason §8.16.5 did**: **692,931 declarations accepted, 0 rejected**,
over the whole 5,851,376,351-byte emitted file from an empty environment
(`envprobe target/carve-mathlib.out.ndjson C`, 24.7 GB peak). `modelgen`'s own
`addChecked` checks each declaration against the environment *it* has built, so
a model emitted at a different *position* in the file is exactly what that
check cannot see — and this arm both splices and defers.

**+75 against §8.16.5's 692,856, and it adds up to the record**: the three new
models are 10 + 10 + 12 = 32 declarations, and the fragment grew by 45 records
of which two — `Nonempty` and `Classical.choice` — Mathlib already had and
`ensureWCore` skipped. 32 + 43 = 75.

**On a real input the shared names are shared and nothing is spliced twice.**
The one splice line in the run carries `_wcore.Classical.em`,
`_wcore.Classical.propDecidable`, `_wcore.Classical.choose` and the rest of the
closure under the prefix, and carries **neither** `Classical.choice` nor
`Nonempty` — Mathlib declares both, `ensureWCore` skipped both, and the
fragment's axiom is the input's own.

**The two columns are three declarations and 6,875 declarations.** That the
untagged population is exactly the three is not a separate measurement: the
predicate that selects it is `tagFactored`, which this change did not touch, and
a target with `tagFactored` false that the *tower* reached is unaffected because
arm W fires only at `!erasureLinear`. What is measured is the column itself, on
`tests/prim_w.lean`: `Wt`, `Tree`, `Br` and `Dep` at `[propext, Quot.sound]` and
`Bad`, `Wty`, `Utd` at `[propext, Classical.choice, Quot.sound]`, read off the
emitted file with the kernel on.
