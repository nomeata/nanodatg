# `modelgen` — the model of a nested inductive, as an export filter

`modelgen` reads a Lean 4 `.ndjson` export, writes the same export back out,
and inserts **before each nested inductive** an ordinary Lean development that
models it: the specialised block, the type formers, the constructors, the
recursors, and the ι rules — all as ordinary declarations, all proved, all
checked by Lean's kernel.

```bash
modelgen IN.ndjson -o OUT.ndjson [--check-recursors] [--quiet]
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

Let `T` be a nested inductive with `numNested > 0`, `n` block members (`T`
itself plus one *mimic* per distinct nested occurrence), parameter telescope
`p⃗` of length `np`, and `m = n − 1` mimics. `T` has no universe parameters and
no indices (§5).

| name | kind | statement |
| --- | --- | --- |
| `T._model.0` … `T._model.{n−1}` | mutual inductive block | member 0 is the copy of `T`; member `i+1` is the mimic of occurrence `i`. Constructors are `T._model.k.<last component of the original>`. |
| `T._model.self` | `def` | `∀p⃗, Sort u := T._model.0 p⃗` — **the carrier**. `⟦T⟧ := ⟦T._model.self⟧` is the keying. |
| `T._model.pack_i` | `def` | `∀p⃗, occᵢ → T._model.{i+1} p⃗` |
| `T._model.unpack_i` | `def` | `∀p⃗, T._model.{i+1} p⃗ → occᵢ` |
| `T._model.unpackPack_i` | `theorem` | `∀p⃗ l, Eq (unpack_i p⃗ (pack_i p⃗ l)) l` — the **retraction** |
| `T._model.packUnpack_i` | `theorem` | `∀p⃗ b, Eq (pack_i p⃗ (unpack_i p⃗ b)) b` — the **section** |
| `T._model.ctor_j` | `def` | `T`'s `j`-th constructor's declared type, with `T` rewritten to `T._model.self` and **nothing else** |
| `T._model.rec_k` | `def` | `T.rec_k`'s declared type, with `T`, `T`'s constructors and `T.rec_*` rewritten to their model counterparts and **nothing else** |
| `T._model.congrPack_i` | `theorem` | `∀p⃗ l₀ l, Eq l₀ l → Eq (pack_i p⃗ l₀) (pack_i p⃗ l)` |
| `T._model.iota_k_j` | `theorem` | `∀p⃗ M⃗ S⃗ f⃗, Eq (rec_k p⃗ M⃗ S⃗ (c f⃗)) (Sⱼ f⃗ ih⃗)` — the `j`-th rule of `T._model.rec_k` |

Here `occᵢ` is the `i`-th nested occurrence — `List T._model.self` for
`inductive Tree | node : List Tree → Tree` — written at `p⃗`.

Indices are `0`-based throughout, and `Name.num` is used for the block members
(`T._model.0`) while `Name.str` is used for everything else
(`T._model.pack_0`). Where the export names `T.rec` and `T.rec_1`, the model
names `T._model.rec_0` and `T._model.rec_1`: **the model's index is the member
index, uniformly.**

## 1.1 The three properties a consumer may rely on

1. **`T._model.rec_k` is `T.rec_k`'s statement about different constants.**
   Exactly: take the declared type of the `T.rec_k` the export carries, rewrite
   `T ↦ T._model.self`, `T.ctorⱼ ↦ T._model.ctor_j`, `T.rec_m ↦
   T._model.rec_m` (at the same level list) and nothing else; the result is
   `T._model.rec_k`'s declared type on the nose. That is what makes
   `⟦T.rec_k⟧ := ⟦T._model.rec_k⟧` an alias rather than a coincidence. The same
   holds for `T._model.ctor_j` against `T`'s `j`-th constructor.

2. **`T._model.iota_k_j` is `T.rec_k`'s `j`-th rule, in the export's own
   order.** The `j`-th ι theorem is about the constructor the `j`-th rule of the
   export's `T.rec_k` is keyed by — `T.node` at the root, `List.cons` at a
   mimic. Its statement is the rule's, with the same rewriting, and the rule's
   right-hand side appears verbatim modulo that rewriting. **A consumer may
   therefore line ι theorems up with rules by index, and check the key by
   name.**

3. **Every level list is the export's own.** `T._model.rec_k` carries `T.rec_k`'s
   single motive-universe parameter, under the same name; `T._model.iota_k_j`
   carries the same one. Everything else is level-monomorphic.

Both 1 and 2 are *checked by the tool itself*, against the recursors the kernel
mints for `T`, and reported by the `statements: N compared …, 0 differ` line.
The check is a port of `mini/tests/nested.rs`'s `check_recursors` and
`check_iotas`.

## 1.2 What the contract does **not** say

* **Nothing about `T._model.0`'s constructors, `pack`, `unpack` or the round
  trips beyond their statements above.** Those are the construction, and the
  point of this tool is that the checker stops needing to know it.
* **Nothing about the order of the mimics** except that it is the export's own:
  mimic `i` is the occurrence the export's `T.rec_{i+1}` eliminates. A consumer
  reads the correspondence off the recursor index and never off the container.
* **The model may not be identified with `T` definitionally.** `T` is a
  primitive inductive and `T._model.self` is a `def` over a different block;
  Lean has no conversion between `M₀ : T._model.self → Sort v` and `m1 : T →
  Sort v`. "Same statement about different constants" is true of the statement
  and false of the type.

## 1.3 When there is no model

`modelgen` emits nothing for a declaration it declines, and says which shape
stopped it on stderr/stdout. **A consumer must therefore treat the absence of
`T._model.self` as "no model", not as an error**, and the presence of a
`T._model.*` name it did not generate as an ordinary declaration of the file —
`mini/tests/fixtures/nested_keying.lean` declares `UTree._model.self := N`
precisely to make that case exist. `modelgen` will not collide with it: the
name guard scans **the whole input file**, not the prefix before the
declaration, and declines `UTree` for `nested model name taken`.

---

# 2. What is generated, and how much of it

Per nested declaration: 1 (block) + 1 (carrier) + 4·m (the maps and round
trips) + one per constructor + one per member (recursors) + m (congruences) +
one per ι rule.

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
| `init-prelude` / **`Lean.Syntax`** | 2 | 7 | 26 |

The first eight are the eight `mini/src/nested_ev.rs` covers, and the counts are
**identical** to the ones `mini/tests/nested.rs` pins for it.

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
   205-file corpus, **682 recursors, and the only five files that differ are in
   `vendor/arena-tests/bad/`**: `nat-rec-rules`, `level-imax-leq`,
   `nat-rec-k-lie`, `rec-k-lie` and `130_misnamed_rec_user`, each named for the
   lie it tells. This is `mini/tests/mutual.rs`'s
   `the_generated_recursors_are_the_ones_lean_exports` for nothing, over the
   corpus rather than the fixtures.

Measured over the whole corpus: **205 files, 0 failures, 12 models, 87
statements compared with 0 differing, 682 recursors with 0 differing outside
`bad/`.** Twenty `bad/` files stop replaying — Lean's kernel will not load a
deliberately ill-formed *inductive* even with checking off, because the
inductive elaboration is not skippable — and are passed through byte for byte.

Acceptance is `nanoda_bin` — the same parser `mini` uses — on the filtered
export. It accepts every one, and the negative control fires: give
`Tree._model.iota_0_1` the *statement* of `iota_0_0` and it stops at
`assert_def_eq: not definitionally equal`.

## 4.1 Speed

`MEASUREMENTS.md`'s table for the Rust generator, and the same work here:

| | Rust (`mini/tests/nested.rs`, test profile) | `modelgen` |
| --- | --- | --- |
| `nested_iota` (`Tree` + `BTree` + `PT`) | 10.3 + 38.0 + 26.5 s | **0.17 s** |
| `nested_deep` (`DTree`) | 91.1 s | **0.22 s** |
| `nested_shapes` (four declarations) | 10.4 + 2.8 + 89.3 + 16.6 s | **0.14 s** |
| all three, end to end | **284 s** (measured) | **0.53 s** |
| `init-prelude` (3.7 MB, 1777 declarations, `Lean.Syntax`) | cannot (see §5) | **0.28 s** |

The Rust figure is `cargo test --test nested
the_nested_isomorphism_is_generated_and_the_kernel_accepts_it`, which generates
and `kernel::add`s exactly these eight models: 284.12 s. `modelgen`'s figures
are whole-file — parse, replay every declaration, generate, kernel-check, run
both oracles — and include ~0.1 s of process start. **Roughly 500×**, and the
superlinearity is gone: `DTree`, the 91-second case, is not distinguishable
from the others here.

---

# 5. What it declines, each a shape

* `nested model with universe parameters` — the declaration has level
  parameters of its own. No fixture has one.

  A **container** with level parameters is fine, and this is where `modelgen`
  reaches something the Rust does not. `nested_ev.rs`'s `rec_levels` puts the
  container's *declared* level parameter on `C.rec`, as `Level::Param`; the
  occurrence's own instantiation is what belongs there. For every committed
  fixture the containers are monomorphic and the two coincide, so the guard has
  no witness in the tree — but `Lean.Syntax` nests into `Array.{0} Syntax` over
  `List.{0} Syntax`, and there the declared parameter is a free universe
  variable in a declaration with no level parameters. Measured on a scratch
  fixture with a polymorphic `List`: `nested_ev::iso` returns
  `Err(nested model shape)`, and `modelgen` writes the 15 declarations and
  `nanoda` accepts them. `modelgen` uses `u :: cls` — the occurrence's levels.
* `nested model with indices` — the declaration or a container has indices.
* `nested model with dependent fields` — a constructor field's type mentions an
  earlier field; the congruence fold replaces one argument of a constructor
  application, which is only well-typed when the rest do not depend on it.
* `nested model without Eq` — the export declares no `Eq`, or one whose
  recursor is not Lean's shape.
* `nested model name taken (N)` — `N` is declared somewhere in the input.
* `nested model shape: …` — a shape the generator cannot write, or a proof the
  kernel did not accept.

## 5.1 One Lean-side wrinkle

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

Mutual-and-nested together is declined by the planner: the specialisation of a
mutual block is not written.
