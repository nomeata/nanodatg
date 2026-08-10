# `modelgen` — Lean-to-Lean export filters

Two standalone tools that read a Lean 4 `.ndjson` export, transform it, and
write an export back out. Both exist to move work **out of a proof checker and
into Lean**, so the checker has less to implement and can trust Lean's kernel to
have checked what it is handed.

| tool | what it does |
|---|---|
| `modelgen` | splices in an ordinary Lean development that **models** each inductive whose recursors the kernel had to *construct* — nested inductives and mutual blocks |
| `monomorph` | **erases universe polymorphism**, emitting one copy of each declaration per level instantiation actually used |

Neither typechecks its input. The input is trusted; that is where the speed
comes from. Only the declarations a tool *generates* are checked, one at a time,
by Lean's kernel via `Environment.addDeclCore` with checking on. **A proof the
generator builds and the kernel rejects is a decline, never an emission.**

## Why you might want this

A checker that consumes Lean exports has to reimplement two awkward things:
the construction Lean's kernel performs for nested and mutual inductives, and
universe-level machinery.

These tools remove both from the checker's job:

* After `modelgen`, a checker never needs to *derive* a nested inductive's
  recursors and ι rules. They are in the file, as ordinary declarations, proved,
  under the naming convention below. The checker only needs to recognise names.
* After `monomorph`, a checker never sees a level variable.

In our own case this deleted a 2117-line generator outright and is expected to
delete a further ~500 lines of level scheduling.

## Build and run

```bash
cd modelgen && lake build

.lake/build/bin/modelgen  IN.ndjson [-o OUT.ndjson|-] [--check-recursors]
                                    [--prim-models] [--quiet]
.lake/build/bin/monomorph IN.ndjson [-o OUT.ndjson] [--mono-recursors]
                                    [--default N[,N...]] [--check] [--quiet]
```

`-o -` writes the export to stdout. **The report always goes to stderr**, so a
consumer can stream the export and still read the diagnostics.

Exit statuses are meaningful and stable:

| | |
|---|---|
| `0` | ran to completion, **including every decline** |
| `1` | usage |
| `2` | input unreadable or unparsable |
| `3` | the tool's own failure |

A generated model whose statement does not match the installed recursor's rule
is a `3`, not a silently-written model.

**Toolchain**: pinned to `leanprover/lean4:v4.29.1` — the version `lean4export`
3.1.0 was built at (githash `f72c35b3`). The package is self-contained and does
not participate in any surrounding build.

## `modelgen`

There are **two constructions always on**, because there are two kinds of
declaration whose recursors the kernel constructs:

* **Nested inductive** (`Modelgen/Model.lean`) — specialised into a mutual block
  with one extra *mimic* member per nested occurrence, with the export's own
  recursors proved over that.
* **Plain mutual block** (`Modelgen/Mutual.lean`) — the members' index
  telescopes packed into a tag, and the members themselves into one *single*
  inductive indexed by it.

They are not one construction at two settings: a nested model *keeps*
mutuality, a mutual model *removes* it, so the second at zero mimics would be
the identity.

A **third construction is opt-in** (`--prim-models`, `Modelgen/Simple.lean`):
a plain — non-mutual, non-nested — inductive is modelled as ordinary `def`s
and `theorem`s over five primitive inductives, `Eq`, `PSigma`, `Nat`, `Acc`
and `PULiftP`, each spliced at Lean's shape if the input lacks it. Same four
interface names, no internal declarations at all, every ι theorem `Eq.refl`.
`False` is **not** a primitive — it is derived, Church-encoded, with its
`Sort w` eliminator from `0 = 1` and a `Nat.rec` family. `PULiftP.{u}
(p : Prop) : Sort u` is: it is the one basis type former that reaches a bare
variable sort and can be *empty*, which is what makes `PEmpty` modellable and
retires the `False`-Π pad that used to cost a `funext`. `MODELGEN.md` §8
carries the construction, its measured coverage (122 of `init-prelude`'s 125
simple inductives; every decline with a printed reason), its cost (+26 %
instructions there), and §8.6 the lean4lean cross-check on the one decline
that is a level-arithmetic gap rather than a type error.

**They compose in one pass.** A nested declaration's model *is* a mutual block,
so the second construction runs on it too — and with `--prim-models` the third
runs on the single inductives the second writes. Every mutual block in the
output has a model beside it — including the ones the tool just wrote.

A model is emitted **beside** what it models, never in place of it. The original
declarations are untouched.

### The names

**Four names are the interface.** For a declaration `T`:

```
T._model.self                 the carrier
T._model.ctor_j               the block's j-th constructor
T._model.rec_k                the recursor at block index k
T._model.iota_k_j             the j-th ι rule of rec_k, as a theorem
```

That is the whole of what a consumer reads — measured, not asserted: when our
own checker was wired up as the first consumer it touched these four families
and none of the others.

Build them off `T` rather than pattern-matching them; that is what lets the
convention survive other renaming passes, including `monomorph`'s. **The carrier
`T._model.self` is the one name both constructions agree on**, so key off it.

The output also carries the construction itself — the block (`T._model.0 …
T._model.{n-1}`, real members first then one mimic per nested occurrence, or
`T._model.tag` and `T._model.aux` for the mutual construction), the `pack_i` /
`unpack_i` isomorphism per mimic, both round trips, and `congrPack_i`. **These
are internal.** They exist because the four above have to be *proved* from
something, they are what differs between the two constructions, and **no
consumer needs them.** They are named here only so that nobody wonders what
those declarations are doing in their input.

### What a consumer may rely on

**1. `T._model.rec_k` is the export's recursor at block index `k`, stated about
different constants.** Take that recursor's declared type as the export carries
it; rewrite each real member `R_k ↦ R_k._model.self`, each of their constructors
to its `T._model.ctor_j`, and the export's recursor at block index `m` to
`T._model.rec_m` at the same level list — and nothing else. The result is
`T._model.rec_k`'s declared type **on the nose**. The same holds for
`T._model.ctor_j` against the block's `j`-th constructor. This is what makes
`⟦A.rec_1⟧ := ⟦A._model.rec_2⟧` an alias rather than a coincidence.

**2. `T._model.iota_k_j` is `T.rec_k`'s `j`-th rule, in the export's own
order.** It is about the constructor that rule is keyed by — `T.node` at the
root, `List.cons` at a mimic — and the rule's right-hand side appears verbatim
modulo the same rewriting. **So a consumer may line ι theorems up with rules by
index, and check the key by name.**

**3. Every level list is the export's own.** `T._model.rec_k`'s level parameters
are those of the recursor it models, name for name and in order: the motive
universe first, then the block's own. `iota_k_j` carries the same list.
Everything else carries exactly `ℓ⃗`. The motive universe's *name* is Lean's,
minted from the same list for the model's recursor as for the export's, and
property 1's syntactic equality is what says the two agree.

Properties 1 and 2 are **checked by the tool against the recursors Lean's kernel
mints**, and reported as `statements: N compared …, 0 differ`.

### What the contract does *not* say

* **Nothing at all about the internal names above.** Their statements, their
  order, their existence in a future version — none of it is promised. They are
  the construction, and the point of the tool is that a checker stops needing to
  know it.
* **Nothing about mimic order** except that it is the export's own: mimic `i` is
  the occurrence the export's recursor at block index `r+i` eliminates. Read the
  correspondence off the recursor index, never off the container.
* **The model may not be identified with `T` definitionally.** `T` is a
  primitive inductive and `T._model.self` is a `def` over a different block;
  Lean has no conversion between `M₀ : T._model.self → Sort v` and
  `m1 : T → Sort v`. *"Same statement about different constants"* is true of the
  statement and **false of the type**. This one has cost us a day; do not plan
  around a conversion that does not exist.

### When there is no model

`modelgen` emits nothing for a declaration it declines and says which shape
stopped it, on stderr. **A consumer must treat the absence of `T._model.self` as
"no model", not as an error** — and a `T._model.*` name it did not generate as
an ordinary declaration of the file. `modelgen` will not collide with one: the
name guard scans **the whole input file**, not the prefix before the
declaration, and declines with `nested model name taken`.

### The prelude

A nested or mutual model's proofs need `Eq`, the quotient, `Quot.sound` and
`funext`. A `--prim-models` model needs `Eq` and whichever basis primitives it
actually uses, and **no axiom at all** — the construction stopped needing
`funext` when the `False`-Π pad was replaced by `PULiftP ⊤`, whose uniqueness
is definitional. If the input lacks anything a model needs it is **spliced
in** — `funext` is *derived* from `Quot.sound`, never asserted as an axiom —
and only when a model is actually being generated, so a file with nothing to
model comes back byte-identical.

## `monomorph`

Emits one copy of each declaration per level instantiation used, computed by a
**single backwards pass over declaration groups**: exports are topologically
sorted, so walking from the last declaration backwards means every user of `d`
has been seen by the time you reach `d`, and no fixpoint is needed. Sortedness
is asserted rather than assumed. Declarations nothing references take a
configurable default, `--default 0`.

**Two recursor modes.** By default the eliminating (motive) universe stays a
parameter, which keeps the output acceptable to kernels that require recursors
to be level-polymorphic. `--mono-recursors` folds it into the name too, and
needs a checker liberal enough to accept a monomorphic recursor.

**Built-ins are left alone** — `Eq`, the `Quot` family and the standard axioms
are recognised (structurally, not by name, for the quotient) and passed through,
closed under "mentioned by a carried declaration at a non-numeral level".

Names take a **root prefix** carrying the instantiation, deliberately free of any
dependence on the shape of the name being renamed — so it composes with
`modelgen`'s names without either scheme knowing about the other.

**A model is instantiated with the declaration it models**, at exactly the same
set of instantiations. Nothing in a file *references* a model, so without this
rule every model would fall to the default and only one copy would get one.

Two properties worth knowing if you build on the output: a `Sort u` inductive at
`σ = 0` lands in `Prop`, and the kernel's *derived* flags move with it — so some
recursors legitimately come back different from the input's. And a pass that
erases levels **erases lies told in levels**: a file that was ill-typed only in
its level arguments may become well-typed. Acceptance of the output is not a
claim about the input.

## Coverage

For the two always-on constructions there is no shape Lean accepts that
`modelgen` refuses. That claim is worth exactly what it is measured against,
so: it comes from a sweep of what Lean's `inductive` command actually admits,
and **every refusal path has a fixture**. Three shapes remain that *Lean
itself* rejects, recorded with the error Lean gives. `--prim-models` is
narrower by design — `MODELGEN.md` §8.2's table is the census, and its refusal
paths have fixtures too (`tests/prim_declines.lean`). What it declines today:
**branching** recursion (a constructor with two recursive fields, or one under
a binder), indexed carriers at a **never-zero** sort, *recursive*
subsingletons, an indexed subsingleton with more than one constructor field,
indices or recursion at a maybe-zero sort, and one level-arithmetic gap.
Indexed and recursive small-eliminating `Prop`s model, the whole maybe-zero
class models, *linear* recursion at a never-zero sort models (`List` and
`Lean.Name`, by tuple towers, every ι `Eq.refl`), and so does the indexed
subsingleton up to one field (`HEq`). Every remaining decline names a
compiled prototype under `scripts/inductive-basis/` that would close it.

On Mathlib (5.6 GB export, 670,630 declarations):

| | |
|---|---|
| `modelgen` | 92 models, 0 declined, ~270 s, ~24 GB peak |
| `monomorph` | 670,630 → 776,723 declarations (1.158×), ~690 s, ~20 GB peak |

`init-prelude` (3.7 MB) filters in about a quarter of a second.

One useful downstream number: `nanoda` checks the *monomorphized* file **2.34×
faster** than the original, on 15.8 % more declarations — enough that the pass
pays for itself on a single check.

## Testing and oracles

```bash
lake exe test        # modelgen
lake exe monotest    # monomorph
```

The strongest check is free: **Lean's kernel performs the nested construction
itself**, so replaying an export gives an independent answer for every recursor.
`--check-recursors` compares each generated ι statement against the rule the
*installed* recursor carries, reading the constructor's field telescope off the
recursor's own major premise rather than off the plan. Across our corpus that is
thousands of statements with zero differences, and it has caught real bugs that
no test of ours would have.

`envprobe` is a small diagnostic for the parse and replay phases.

## Design notes worth having before you read the code

* **The output is re-interned.** Any modified file is rewritten whole, because
  the export format's back-references must stay continuous. Files with nothing
  to splice come back byte-identical, and that property is measured.
* **The writer streams.** An earlier version accumulated the whole output as one
  string and died at Mathlib scale — a ~110M-entry array intercalated into a
  6 GB string, out of memory at 44.9 GB. Streaming completes the same file at
  36 GB.
* **The reader streams too**, and this mattered more: the parse was once 2.8× the
  memory of a purpose-built parse-only baseline, and **all of it was the reader
  materialising lines, not the parsed data** — peak was reached before a single
  JSON object was parsed. Chunked reading took the parse from 23.9 GB to 5.5 GB,
  which is 1.00× the file's own bytes.
* **We keep our own writer rather than reusing `lean4export`'s driver.** What is
  ruled out is letting `dumpConstant` write from an `Environment`, and the reason
  is byte-identity: it emits in its own dependency order and re-derives
  `numNested`, `isRec`, `hints` and `all` from what Lean worked out rather than
  from what the file said, so a file with nothing to change would no longer come
  back unchanged. Its *record emitters* are environment-free and could be lifted;
  that is a ~90-line code-sharing question with no correctness content, and
  `MODELGEN.md` §3.1 works through why it is not worth the fork it would need.
* **Level substitution memoises on `(Expr, σ restricted to the expression's own
  level parameters)`.** Pruning σ to what an expression actually mentions is what
  makes entries shared across instantiations that differ elsewhere; memoising
  every node instead was measured as a regression.

## Further reading

Not required to use the tools — `MODELGEN.md` and `MONOMORPH.md` in the parent
directory carry the derivations, the coverage sweep case by case, and the
measurements with the command that produced each. Both are written verdict-first,
with anything unmeasured named as unmeasured.
