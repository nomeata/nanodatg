# `modelgen` — the model of a nested inductive, as an export filter

`modelgen` reads a Lean 4 `.ndjson` export, writes the same export back out,
and inserts **before each nested inductive** an ordinary Lean development that
models it: the specialised block, the type formers, the constructors, the
recursors, and the ι rules — all as ordinary declarations, all proved, all
checked by Lean's kernel.

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

---

# 1. The interface contract

**This section is the deliverable.** A checker that consumes `modelgen`'s output
needs to know the construction only through what is written here. Everything
below is stable; nothing else about the output is.

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
HTree: declined — nested model without funext
statements: 21 compared against the installed recursors' own rules, 0 differ
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

---

# 2. What is generated, and how much of it

Per nested declaration: 1 (block) + `r` (carriers) + 4·m (the maps and round
trips) + one per constructor of the block's **real** members + one per block
member (recursors) + m (congruences) + one per ι rule.

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

The first eight are the eight `mini/src/nested_ev.rs` covers, and the counts are
**identical** to the ones `mini/tests/nested.rs` pins for it.

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
`mini/tests/fixtures` (41) and `modelgen/tests` (18): **216 files, 0 failures,
61 models, 450 statements compared with 0 differing, 897 recursors of which 10
differ and all 10 are in the five `bad/` files named above.** Twenty `bad/`
files stop replaying — Lean's kernel will not load a
deliberately ill-formed *inductive* even with checking off, because the
inductive elaboration is not skippable — and are passed through byte for byte.

Acceptance is `nanoda_bin` — the same parser `mini` uses — on the filtered
export. It accepts every file this tool wrote a model into, and the negative
control fires: give `Tree._model.iota_0_1` the *statement* of `iota_0_0` and it
stops at `assert_def_eq: not definitionally equal`.

**Five files it does not accept, and all five are the same upstream
limitation.** `mini/tests/fixtures`' `mutual_index_sorts`,
`mutual_index_telescopes`, `mutual_one_recursive` and `mutual_prop_even_odd`
make `nanoda_bin` panic at `checker/src/inductive.rs:30`. There is no model in
any of them, so `modelgen`'s output is **byte-identical to the input** —
measured with `cmp` — and the same panic fires on the input.

The line is `assert_eq!(ind.is_recursive, is_recursive)`, and the reason is
measured rather than guessed: upstream recomputes `isRec` **per member**, by
scanning that member's constructors for a *binder type* mentioning any name in
the block, while Lean sets it for the **whole block**. Each of the four has
exactly one member whose constructors mention no block member in a binder type
— `mutual_one_recursive`'s `OB`, `mutual_prop_even_odd`'s `Ka`,
`mutual_index_sorts`' `HB`, `mutual_index_telescopes`' `EB` — so the export
says `true` and the recomputation says `false`.

> **The fifth is this tool's output**, and a consumer needs to know it.
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
  one place this module reads a constant out of the export that no §1 statement
  mentions. `funext_binder.lean` and §5.2's `nested model without funext`
  below. `nest_binder_cross.lean` crosses it with the rest, and the **cycle**
  crossing did not come for free: `packFamMinor` and `retractFamilyValue` are a
  second copy of the one-at-a-time path and were measured refusing `CycB` until
  they were taught the same telescope. Also there: a *dependent* two-binder
  telescope (`DTel`), the binder at an indexed container (`IdxB`), and the
  binder inside a mutual block (`MutB`/`MutC`).
* **The odd corners, swept for rather than waited on.**
  `nest_odd_shapes.lean` is what the "no gaps" claim is worth: a container with
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

---

# 5. What it declines

Every entry names the shape, **what Lean does with it**, and what this does.
Completeness is measured against Lean and not against the fixture set, so a
shape Lean accepts and this refuses is a *gap* and is marked one; a shape Lean
refuses too is a boundary and is marked that.

**There are no gaps.** §5.1 is empty: there is no shape Lean accepts and this
refuses. What is left is a shape Lean refuses too, or a constant the input does
not declare.

**Every one of these has a fixture that reaches it**, under `modelgen/tests/`,
built by `modelgen/tests/export.sh` with the repository's own exporter,
toolchain and `--#export` convention — except the five §5.2 and §5.3 name as
having none, and each says why. §5.1 is **empty**, and §4.2 lists the fixture
that closed each row it used to have. `--check-recursors` runs on each, so Lean's own
recursors for these shapes are compared against the export's on every test run.

## 5.1 Gaps — shapes Lean supports and this does not

**Empty.** There is no shape Lean accepts and `modelgen` refuses.

That sentence has been wrong before, so here is what stands behind it. Every
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
constructor field's type, a parameter that is a function type, depth three, and
the crossings of all of those. §4.2 names each with its fixture and its count.

The claim is only worth what was swept for it, and `nest_odd_shapes.lean` is
that sweep written down: each of its six was found by asking what else Lean's
`inductive` allows rather than by a failure arriving, and **two of them were
refusals when they were first written**.

What `modelgen` still declines is of exactly two other kinds, and neither is a
shape:

* **A constant the input does not declare** — §5.2's `nested model without Eq`
  and `nested model without funext`, and `nested model name taken`.
* **Shapes Lean rejects too** — the rest of §5.2.

### The one shape that was here last, and what closing it cost

`HTree.node : (N → List HTree) → HTree`: a constructor field the block holds at
a mimic *under a binder*. The obstruction was the proof and not the statement.
The block types the field `∀ x⃗, Bₘ ι⃗`, so `T._model.ctor_j` builds `fun x⃗ =>
pack (f x⃗)` and something downstream transports along `(fun x⃗ => pack (unpack
(f x⃗))) = f`. **No choice of `ctor_j` avoids it**: §1 fixes `ctor_j`'s type, so
its value is `B₀.c (h f)` for some `h`, and `h` must satisfy `h (fun x⃗ =>
unpack (g x⃗)) ≡ g` for the recursor's minor to typecheck at a *variable* `g`;
the only candidate is `fun k x⃗ => pack (k x⃗)`, and `pack (unpack (g x⃗))` is a
recursor application stuck on a variable.

So `funext` is read from the export, the way `Eq` is — **never fabricated** —
and **lazily**: only a declaration with such a field asks for it, because
`funext` is in 1 of the 157 corpus files and *not* in `init-prelude`, and an
unconditional requirement would decline everything that works today. A
declaration that has the shape and finds no `funext` declines `nested model
without funext` (§5.2). **§1 does not move**: no signature changes and no new
name is emitted; only *which* declarations get a model does, and §1.3 already
tells a consumer to read a missing `T._model.self` as "no model".

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
is the fixture for the decline.

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
  the source would not compile.
* `nested model without Eq` — the export declares no `Eq`, or one whose
  recursor is not Lean's shape. The round trips are equations and this tool
  does not fabricate an equality Lean never wrote. `decline_no_eq.lean`.
* `nested model without funext` — the declaration has a field at a mimic
  **under a binder** and the export declares no `funext`, or one whose
  statement is not Lean's. The same principle at the other constant, and
  checked the same way: the expected statement is built at the found
  declaration's own two level parameters and compared with `isDefEq`, so binder
  names and binder info do not matter. Read **lazily** — no other shape asks
  for it, and `funext` is in 1 of the 157 corpus files, so an unconditional
  requirement would decline all of them. `infinitary.lean`'s `HTree`, `RTree`
  and `OTree`; `funext_binder.lean` is the same three with a `funext` and they
  are models.
* `nested model name taken (N)` — `N` is declared somewhere in the input. Not a
  shape at all: a collision with the file's own names.
  `mini/tests/fixtures/nested_keying.lean`.
* **A nested occurrence whose container parameter mentions a constructor
  field** — `node : (n : N) → List (ITree n) → ITree (N.s n)` — reaches
  `a nested occurrence in ITree depends on a constructor field`. **Lean rejects
  it too**, at the kernel: "nested inductive datatypes parameters cannot
  contain local variables". So this is a boundary and not a gap, and there is
  deliberately no fixture: the source would not compile.
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
is the catch-all, so a new occupant of it is a new gap and not a known one.
§5.1 is empty, so what is left occupying it is **one file in the whole tree,
and it is a lie rather than a shape**:

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

A **mutual** block whose members nest is specialised as one block, under the
first member's `_model` namespace and with one carrier per real member (§1,
§4.2).
