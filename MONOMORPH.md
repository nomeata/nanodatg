# `monomorph` — universe levels, removed from an export

`monomorph` reads a Lean 4 `.ndjson` export and writes the same export back out
with **one copy of each declaration per universe instantiation it is used at**,
every universe parameter replaced by a numeral, and every constant occurrence
rewritten to name the copy it means. A checker downstream never sees a level
variable, a `max`, an `imax`, or a level substitution.

```bash
monomorph IN.ndjson -o OUT.ndjson [--mono-recursors] [--default N[,N...]] [--check] [--quiet]
```

Like `modelgen`, the input is **trusted and not typechecked**; that is where the
speed comes from. Unlike `modelgen`, the *output* is checked: `--check` replays
every emitted declaration through `Environment.addDeclCore` with checking on,
and mode A's recursors are not written at all — they are the ones Lean's kernel
mints for the monomorphized block (§4).

It lives in `modelgen/`, as a module (`Modelgen/Mono.lean`) and two executables
(`monomorph`, `monotest`) beside the nested-model tool. **The shared layer is
`Modelgen/Format.lean`** — the `.ndjson` reader and the re-interning writer,
which both tools need and neither should have twice. Nothing else is shared:
`Modelgen/Mono.lean` deliberately does not import `Modelgen.Driver`, whose
transitive `Modelgen.Model` is under active development, and re-declares the
twenty-line `toDeclaration` rather than couple to it. A sibling *package* would
have meant vendoring or symlinking `Format.lean`, which is the thing worth
sharing.

---

# 1. The interface contract

**This section is the deliverable.** A checker that consumes `monomorph`'s
output needs to know the pass only through what is written here.

## 1.1 The naming scheme

Let `d` be a declaration with universe parameters `ℓ⃗` and let `σ` be one ground
instantiation of them — a natural number per parameter, in `d`'s own order.
Write `k = |σ|`. Then

> **`mono(d, σ)`** is `d`'s name with `_at ++ ⟨k⟩ ++ ⟨σ₀⟩ ++ … ++ ⟨σₖ₋₁⟩`
> prepended at the **root**, where `_at` is a `Name.str` component and every
> `⟨·⟩` is a `Name.num` component. **`σ` empty is the identity.**

`Wrap.{u}` at `[0]` is `_at.1.0.Wrap`; its constructor `Wrap.mk` is
`_at.1.0.Wrap.mk`; its recursor `Wrap.rec` is `_at.1.0.Wrap.rec`. `Pair.{u,v}`
at `[1,0]` is `_at.2.1.0.Pair`. A monomorphic declaration — `Nat`, `Nat.succ`,
`N.rec` — keeps its name **exactly**.

**Why the prefix, and why it is the whole scheme.** One relationship has to
survive monomorphization: Lean's kernel and `nanoda` both *derive* a recursor's
name from its inductive's rather than reading it, so the copy of `Wrap` at `σ`
must have its recursor named `⟨that copy⟩.rec`. Prepending a fixed prefix to
every name in the file preserves *every* suffix relationship at once — `I`
becomes `p ++ I` and `I ++ rec` becomes `p ++ I ++ rec` — so the derived name
follows with no case for it, and the pass never asks what a name looks like.

That last clause is the property, not a convenience. The scheme this replaced
renamed by substituting an **owner** prefix (a constructor's `induct`, a
recursor's block member) and was therefore the identity whenever the owner was
not a prefix of the name; Mathlib has 142 such constructors — private
constructors of public inductives — and every copy of those blocks came out with
one name (§9.2). A scheme that reads name structure has a shape it cannot
rename; a prefix has none.

**Why the length `⟨k⟩` is there.** So that the marker's extent is known without
looking at what follows it. An inverter reads `_at`, reads `k`, takes the next
`k` components as `σ`, and everything after that is the input's name — whatever
shape it has, including a name whose own root component is numeric. Without the
length, `_at.0` prepended to `1.Foo` and `_at.0.1` prepended to `Foo` are the
same name, and the scheme would only be invertible under an assumption about the
input's names. It makes no such assumption.

**Mode B** adds one suffix, and only to recursors: a recursor whose copy at
eliminating universe `w` is emitted is named `mono(d, σ) ++ _elim ++ ⟨w⟩`.
`_at.1.0.Wrap.rec._elim.2`. Mode B is the one place the output is *not* a
kernel's to re-derive, which §4.2 already says.

**The *renaming* composes with names another pass invented.** The pipeline is
`modelgen`, then `monomorph`, then `mini` (`MODELGEN.md`), so by the time this
scheme runs the file contains names `modelgen` synthesised — `T._model.k`,
`T._model.self`, `T._model.pack_i`, `T.rec_k`. Because the marker is a root
prefix, they are renamed by the same rule as everything else and their internal
structure survives: `poly_nested` through both passes in mode B yields
`_at.1.0.PTree._model.0` and its recursor
`_at.1.0.PTree._model.0.rec._elim.0` — derived from the model's *own* name,
which is itself derived. Nothing about `_model` is known here.

**That is a claim about names and about nothing else. The composition itself is
broken, in two ways, and §1.3 is where they are.** Do not read the paragraph
above as saying the pipeline works.

## 1.2 The three properties a consumer may rely on

1. **Every level in the output is a numeral `succ^n zero`, with exactly two
   exceptions**, and both are visible in the declaration itself.

   * **Mode A only:** a recursor may carry one level parameter — its
     eliminating universe — and it is then the *only* entry of that
     declaration's `levelParams`. Every use of it in the file supplies a
     numeral. Mode B has no exception here: `levelParams` is empty everywhere
     it is not a built-in.
   * **A carried built-in** (§3) keeps its name and its own `levelParams`. Its
     uses, too, are all at numerals.

   So: `levelParams` is empty on every declaration the pass produced, and every
   `Sort` and every `Const`'s level list is `succ^n zero` — modulo those two.

2. **One copy per instantiation, and the instantiation is in the name.** If
   `mono(d, σ)` is in the output then `d` is in the input with the level
   parameter count `|σ|`, and the copy's type and value are `d`'s with `σ`
   substituted and every reference redirected. The map is injective on the
   output: **no two output declarations share a name**, and that is checked
   rather than argued (a file where it would fail is refused whole; five
   `vendor/arena-tests/bad/` files reach it).

3. **The scheme is invertible.** `_at` and `_elim` occur in no name of the
   input — a file that spells either is **refused whole** (§6), which is what
   makes this a theorem rather than a convention. To invert a name: strip a
   trailing `._elim.⟨w⟩` if present; if the **root** component is then the
   `Name.str` `_at`, read the next component as `k`, take the following `k`
   `Name.num` components as `σ` in the declaration's own parameter order, and
   what remains is the input's name; otherwise `σ` is empty and the name is the
   input's unchanged.

   Inversion needs no other fact about the name — not where the declaration
   lives, not whether it is private, not whether it is a constructor. That is
   the same property, read from the other end.

## 1.3 What the contract does **not** say

* **Nothing about the order of the copies.** All copies of one group are
  contiguous and precede every use, but which `σ` comes first is the order the
  backward sweep discovered them in, and a consumer must not read anything into
  it.
* **Nothing about which instantiations exist.** A declaration nothing demands is
  emitted at `--default` (`[0]`), which is a choice and not a theorem (§2.2).
* **The copies are not related to each other.** `_at.1.0.Wrap` and
  `_at.1.1.Wrap` are two unrelated inductive types. There is no coercion, no
  shared recursor, and the pass does not claim `_at.1.0.Wrap = Wrap.{0}` — the
  input's `Wrap` is not in the output at all.
* **Acceptance by `monomorph` is not a claim about the input.** The input is
  trusted, and §7 names two `bad/` files whose defect the pass *erases*.
* **A `modelgen` model does not survive this pass, and task #116 has to fix it
  before the pipeline runs end to end.** Two separate failures, both measured on
  `modelgen/tests/poly_nested_used.ndjson` — a nested `PTree.{u}` *used* at
  universes 0, 1 and 2 — put through `modelgen` and then `monomorph`:

  1. **One model for three copies.** `PTree` comes out three times
     (`_at.1.0.PTree`, `_at.1.1.PTree`, `_at.1.2.PTree`) and the model comes out
     **once**. Nothing in the file *references* a model — `mini` finds it by
     constructing the name, not through a use site — so the backward sweep sees
     no demand on the model's groups and they take `--default`. `_at.1.1.PTree`
     and `_at.1.2.PTree` have no model at all.
  2. **The one model that exists is split across two markers.** The nine name
     families do not share a level-parameter arity: `self`, `pack_i`,
     `unpack_i`, `ctor_j`, `congrPack_i` and the model's inductive block carry
     the block's `[u]`, while `rec_k` and `iota_k_j` carry the motive universe
     too, `[u_1, u]`. So the first group is renamed to `_at.1.0.PTree._model.…`
     and the second to `_at.2.0.0.PTree._model.…`. A consumer that derives the
     whole family from the type's name — `mini`'s `nested_splice.rs` builds
     `Name::str(t, "_model")` and hangs all nine off it — finds seven families
     and misses two, **even for the copy that does have a model.**

  Neither is a property of §1.1's marker. (1) is about demand, not naming. (2)
  is intrinsic to putting `σ` in the name at all, since `|σ|` is the
  declaration's own arity. The owner-prefix scheme this replaced has both and is
  strictly worse at the second: it emits `PTree._at.2` beside
  `PTree._model.self._at.0` and `PTree._model.rec_0._at.0.0`, so the marker
  lands *inside* the family name and a consumer deriving from the type finds
  **nothing, for any copy** — where §1.1 at least keeps seven of the nine
  families reachable for the copy that has them.

  Neither failure is visible to a kernel: that fixture's output replays under
  `--check` with **0 rejected** over all 51 declarations, because a model is a
  `mini`-level artefact and nothing type-checks it against the copy it is
  supposed to model. What the pipeline needs is for `monomorph` to key a model's
  declarations off **the declaration they model**, for the instantiation *and*
  for the marker.

  The one thing that is not a hazard here: `mini` looks a model up by
  *construction* rather than by matching a name prefix, so the root marker is
  transparent to it. For `_at.1.0.PTree` it asks for
  `_at.1.0.PTree._model.self` and that is exactly what the file spells.

---

# 2. The sweep is one backward pass

An export file is **topologically sorted**: a declaration can only mention
declarations that appear before it. So the pass walks the file backwards. By the
time it reaches `d`, every user of `d` has been read, `d`'s demand set is
complete, and emitting `d`'s copies pushes demand only onto declarations still
ahead in the walk. **There is no fixpoint and no revisiting; termination is the
length of the file.** `checker/src/instantiations.rs` does the same job as a
worklist fixpoint, which is what a checker with no file order must do.

Topological sortedness is a property of the *exporter*, not of the format, so
the pass **asserts** it: every constant a group mentions must be declared by a
group at a lower index, and a file that violates it is refused by group index
and name. Measured over `vendor/arena-tests` (154 files outside `perf/`, plus
`init-prelude`): **zero violations.** Measured over Mathlib: **five groups of
654305 violate it**, and the pass refuses the file. §9.3 names them; they are
tactic infrastructure, not mathematics, but the assertion is not a theorem
about `lean4export` and it was wrong to read the corpus as saying it was.

## 2.1 The DAG is over groups

An inductive block, its constructors and its recursors mention one another
cyclically, and so do the members of a mutual `def` block through their `all`
field. Each such set is **one node**: it collects one demand set, shares one
instantiation, and is emitted whole. A group's members must agree on their
level parameters, and a file where they do not is refused.

This is also where the "extra universe parameter" of backlog #18 lives. The
eliminating universe is not an independent axis of the sweep: mode A leaves it
alone, and mode B is a pure post-pass over mode A's output (§4.2).

## 2.2 The default

A declaration nothing demands is emitted at `--default`, which is `[0]` — one
copy, all parameters zero. `--default 0,1` gives two copies of every such
declaration, and closes over each.

The instruction chose `[0]` "to avoid duplication", and the measurement agrees:
on `init-prelude`, 601 of 1777 groups are demanded by nothing.
`checker/src/instantiations.rs`'s `DEFAULT_LEVELS` is `[0, 1]` for a reason that
does not apply here — there the default decides *how a declaration is checked*,
and `Sort 0` and `Sort 1` are two different checking problems, so both are
wanted. Here the default decides only *that an unused declaration is not
dropped*, and one copy is enough for that. The flag is there because the two
readings are both defensible and the caller knows which it wants.

**The padding that cost `mini` a tower is not reachable here.** That failure was
a consumer keying off a padded *schedule* rather than off the file's own
declarations; `monomorph`'s output has no schedule to key off. The demand set is
the names in the file, and a defaulted declaration is one copy with `_at.0` in
its name like any other.

---

# 3. The built-ins, carried through untouched

A kernel recognises some constants **by name** and mints applications of them
itself; it cannot be told about a copy. Those are carried through with their
name and their level parameters intact. The exact list is a **seed** plus a
closure.

**The seed**, in `Modelgen.Mono.builtinSeed`:

| | |
| --- | --- |
| the quotient | `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — recognised **structurally**, by the export's own `quot` record kind, not by name |
| equality | `Eq`, `Eq.refl` (and therefore `Eq.rec`, which is in the same group) |
| the standard axioms | `propext`, `Classical.choice`, `Quot.sound` |
| literal expansion | `eagerReduce`, `Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.mod`, `Nat.div`, `Nat.beq`, `Nat.ble`, `Nat.gcd`, `Nat.xor`, `Nat.land`, `Nat.lor`, `Nat.shiftLeft`, `Nat.shiftRight`, `String`, `String.ofList`, `Bool`, `Bool.true`, `Bool.false`, `Char`, `Char.ofNat`, `List`, `List.nil`, `List.cons` |

The last row is `checker/src/util.rs`'s `mk_name_cache` name for name — the
constants `str_lit_to_constructor`, `nat_lit_to_constructor` and
`reduce_nat_lit` build out of thin air, which therefore occur in no expression
of the file and cannot be renamed away.

**The closure, and why there has to be one.** A carried declaration keeps its
level parameters, so a constant it mentions *at one of them* has no copy to
point at. `Classical.choice.{u} : {α : Sort u} → Nonempty α → α` mentions
`Nonempty.{u}`, which is in nobody's list of built-ins. So: the carried set is
closed under "mentioned by a carried declaration at a level argument that is not
a numeral". On `init-prelude` that closure adds exactly one group, `Nonempty`,
for 22 carried groups in all:

```
Nat  Eq  Nat.add  Nat.mul  Nat.pow  Nonempty  List  Bool  Char  Nat.ble
Nat.beq  Nat.sub  Nat.mod  Nat.div  String  Quot  Quot.mk  Quot.lift
Quot.ind  Char.ofNat  String.ofList  Classical.choice
```

A carried declaration is **not** byte-identical in general: a reference it makes
at *ground* levels does move to the copy it means. In practice the seed's own
bodies mention nothing but each other and `Sort`, so on this corpus they come
out unchanged.

**In our checker a single `Eq` works anyway** — `mini` keys `⟦Eq⟧` at one
interpretation and the level argument is inert there — so `Eq` staying
polymorphic costs nothing. `Quot` is the same. What a consumer must accept is
that these ~22 names, and only these, still carry `levelParams`, always used at
numerals.

---

# 4. The two recursor modes

## 4.1 Mode A — the default

The recursor keeps its eliminating universe as a level parameter. Its block
levels are substituted; its uses supply a numeral for the universe that is left.
**This is the mode whose output a kernel accepts**, because a kernel mints
recursors itself, from the inductive, and always with a universe parameter for
the motive when the block eliminates largely.

Mode A is the default for one reason: **it is the only mode with an external
oracle.** Lean's kernel typechecks its output and `nanoda` accepts it (§5), so
"it works" is a check that can be run rather than a property asserted. Mode B is
what the owner is actually after, and it is one flag away, but it can only be
validated by a checker that does not exist yet.

**Mode A does not substitute the recursor; it asks the kernel for it.** This is
not a nicety, and `modelgen/monotests/mono_prop.ndjson` is the fixture:

* `PU.{u} : Sort u` with one argument-free constructor. At `u = 1` it is a
  `Type`. At `u = 0` it is a **proposition**, and the kernel marks it **K-like**
  — so the export's own `k : false`, substituted, is a *lie* about
  `PU._at.0.rec`, and `nanoda` stops at `assertion failed:
  old_r.aux_data_ck(new_r)`. `vendor/arena-tests/good/tutorial/065_punitRec.ndjson`
  is the corpus occupant of the same shape.
* `Ex.{u} (α : Sort u) (p : α → Prop) : Prop` is **small**-eliminating
  polymorphically — its recursor has no universe of its own, because `w : α` is
  not known to be a proof. At `u = 0` every constructor field is a proof, the
  copy is **large**-eliminating, and the kernel mints
  `Ex._at.0.rec.{u_1}` where the input had no parameter at all. A reference at
  no levels is then ill-formed. `vendor/arena-tests/good/tutorial/070_existsRec.ndjson`
  is the corpus occupant.

Both directions, in one fixture, because either alone is degenerate. The pass
therefore replays each monomorphized block into an environment, reads the
recursors back, and **counts the ones that differ**: `recRegen`. On
`init-prelude` that is **32 of 128**; over `vendor/arena-tests`, **50**. A
`recRegen` of zero would mean the whole effect had gone unseen.

The references follow, because emission is forward and the file is topologically
sorted: the block's answer — how many level parameters its recursor came out
with — is known before anything can mention it, and `RwCtx.recArity` is where
it is remembered. A reference to a recursor that *gained* a universe is emitted
at `0`, which is the universe the small-eliminating original eliminated into.

## 4.2 Mode B — `--mono-recursors`

`T.rec.{w}` becomes `T.rec._elim.w`, at no levels, one copy per `w` the file
uses it at (or per `--default` entry if none). Mode B is a **pure post-pass over
mode A's own output** (`Modelgen.Mono.foldElim`), so "B is A with the
eliminating universe folded into the name" is true by construction rather than
by two parallel implementations. After it, `levelParams` is empty on every
declaration that is not a carried built-in.

**Mode B needs a checker that does not regenerate recursors by name.** `nanoda`
does regenerate them, so it refuses mode B's output with
`Expected (Declar::Recursor, Declar::Recursor)` — it minted `T._at.σ.rec` and
looked for the export's declaration of that name, which mode B renamed. Lean is
the same: run `modelgen --check-recursors` over mode B's `mono_elim` output and
it reports **3 of the 4 recursors as differing from Lean's own**
(`N.rec._elim.0`, `._elim.1`, `._elim.2`; the fourth is the carried `Eq.rec`),
because the kernel mints `N.rec` and nothing else. That refusal is the
measurement that the two modes are genuinely different, and it is expected.

On `init-prelude` mode B is 2365 declarations against mode A's 2244: the
difference is 121 extra recursor copies, and every one of them is a recursor
used at more than one motive universe.

---

# 5. What it costs, measured

## 5.1 Duplication

| | declarations in | mode A | mode B |
| --- | ---: | ---: | ---: |
| `init-prelude` (3.7 MB, 1777 records) | 2059 | **2244** (1.090×) | **2365** (1.149×) |
| `vendor/arena-tests/good`, 99 files outside `perf/` | 2791 | **2982** (1.068×) | **3110** (1.114×) |
| `vendor/arena-tests/bad`, 47 files not refused | 376 | 389 (1.035×) | 391 (1.040×) |

**The blow-up is not severe, and that is the first-class finding.** `init-prelude`'s
copies-per-group histogram is `1 → 1628, 2 → 138, 3 → 9, 4 → 1, 5 → 1`: 92% of
groups are used at exactly one instantiation, and the worst is `Eq.ndrec` at
five.

**On Mathlib the aggregate survives and the reason given for it does not.** The
factor is 1.158× and 93.6% of groups are still used at exactly one
instantiation — but the tail runs to **118**, not five, and it is category
theory. §9 is the measurement.

## 5.2 Speed

| | |
| --- | --- |
| `init-prelude`, mode A | **0.288 s** |
| `init-prelude`, mode A `--check` (Lean's kernel over all 2244) | **0.384 s** |
| `init-prelude`, mode B | **0.306 s** |
| the five `monotests` fixtures, `--check`, end to end (five processes) | 0.688 s |
| `monotest` — all 99 `good/` files, `--check`, one process | **0.367 s** |
| *for reference:* `modelgen` on `init-prelude`, re-measured here | 0.238 s |

Whole-file figures, best of three, including ~0.1 s of process start.
`MODELGEN.md` §4.1 records 0.28 s for its own row; the 0.238 s above is that
same binary on this machine, so the two columns are comparable. The pass
is within 25% of `modelgen` on the same file while doing strictly more: the
replay `modelgen` needs anyway, plus a rewrite of every expression, plus a
second replay of the output.

**The monomorphized file also checks faster.** `nanoda` on `init-prelude` takes
0.152 s; on mode A's output, 2244 declarations rather than 2059, it takes
**0.109 s**. Levels are not free even in a kernel that keeps them.

## 5.3 Acceptance

Over `vendor/arena-tests` outside `perf/`, with `--check` on:

* **`good/`: 99 files, 0 problems, 0 declarations rejected by Lean's kernel, and
  `nanoda` accepts every one of the 99 outputs.**
* `bad/`: 8 files refused whole (§7), and of the 47 that are not, `nanoda`
  still rejects 46. The one exception is §7's.
* `modelgen/monotests/`: five fixtures, mode A and mode B, kernel-checked and
  count-pinned in `modelgen/MonoTest.lean`; `monotest` runs 106 checks in
  0.37 s.

---

# 6. What it declines, each a shape

Completeness is measured against Lean and not against the fixtures, so a shape
Lean accepts and this refuses is a **gap**; a shape Lean refuses too is a
**boundary**. A refusal is whole-file: the output is the input, byte for byte,
and the reason is printed.

## 6.1 Gaps — shapes Lean supports and this does not

| decline | fixture | what Lean does |
| --- | --- | --- |
| `the file already declares N, which spells a marker` | `modelgen/monotests/marker_taken.ndjson` | accepts `def foo._at.bar : N := N.z`, and mints `_at` names itself for specialised code. §1.2's property 3 is a theorem only on a file with no `_at` or `_elim` component, so the pass refuses rather than emit a name a consumer could not invert. |
| `two output declarations are both named N` | `vendor/arena-tests/bad/126_dup_defs`, `127_dup_ind_def`, `128_dup_ctor_def`, `129_dup_rec_def`, `132_dup_ctor_rec` | these five are files Lean would reject too, so as *files* they are a boundary. The guard remains a gap in principle — a legitimate input in which two distinct declarations monomorphize to one name would be refused rather than merged — but §1.1's scheme is injective by construction, so no such input is reachable through the renaming itself: `mono` prepends the same prefix to every name of a copy, and two copies differ in `σ`. Mathlib **was** such an input under the previous scheme and is not under this one (§9.2), and `modelgen/monotests/mono_offname.ndjson` is the shape, kept as a fixture. |

## 6.2 Boundaries — shapes Lean does not support either

* `a duplicate universe parameter in [u, u]` —
  `vendor/arena-tests/bad/tutorial/016_tut06_bad01.ndjson` and
  `045_inductLevelParam.ndjson`. Lean cannot express it and `nanoda` rejects it
  (`no_dupes_all_params`). The guard exists because monomorphization would
  otherwise **erase** the defect: the copy has no parameters at all and is
  perfectly well typed. See §7.
* `an inductive block whose members differ in their level parameters`, `a
  mutual block whose members differ in their level parameters`, `a constructor
  whose level parameters are not its block's` — Lean requires the block to
  share one list.
* `a recursor with more than one elimination universe` — Lean mints exactly one.
* `the file is not topologically sorted: group i mentions N, which group j
  declares` — a property of `lean4export`'s output. Asserted rather than
  assumed; zero occurrences in the corpus, and **five in Mathlib** (§9.3), so
  this clause is reachable on real input and not only in principle.
* `the group demands itself at a new instantiation` / `… at a new eliminating
  universe` — the one place a single backward pass could be incomplete: a group
  whose own copy at `σ` needs a *different* copy of the same group. Lean's
  mutual blocks recurse at their own parameters, so this cannot arise from Lean
  output; the guard is there because the format does not forbid it, and it
  fires on nothing in the corpus.
* `N: eliminates into a nonzero universe, but its copy at this instantiation is
  small-eliminating` — the mode-A recursor move of §4.1 running the *other*
  way. Not observed; the guard is there because the argument that it cannot
  happen is not airtight.
* `a level argument did not evaluate to a numeral` — a constant used at a
  universe parameter that is not the mentioning declaration's own. Malformed;
  `check_declar_info` rejects it too.
* `a projection of N whose type is not an application of a constant` —
  malformed.
* A file the replay will not load at all (a deliberately ill-formed inductive:
  Lean's inductive elaboration is not skippable, which `MODELGEN.md` §4 also
  records) is refused whole and passes through unchanged.

## 6.3 One shape that needed a typechecker, and got one

`Expr.proj` carries the structure's **name** but not its level arguments, and
Lean's `inferProjType` rejects a projection whose name is not the head of the
projected term's inferred type. So the name has to move to the right copy, and
which copy is only recoverable from that type. This is the one place the pass
needs an environment, and it is why the input is replayed at all — a file with
no projection never pays for it.

On `init-prelude` this is not decorative: of 101 distinct projected structures,
**five** have more than one copy — `Subtype` and `Inhabited` and `PProd` at
three each, `PULift` and `Hashable` at two — so a pass that guessed "the only
copy" would be wrong on them. On the 20-million-line Mathlib prefix of §9.1 it
is **405 of 2168** (`scripts/mono-copies.py` counts the copies; the projected
structures are the `typeName`s of the input's `proj` records), so at that scale
guessing is wrong nearly a fifth of the time.
`modelgen/monotests/mono_proj.ndjson` is the fixture, with `P.{u,v}` projected
at `(1,1)`, `(1,2)` and `(2,1)` — three copies, two of them the same two atoms
in opposite orders.

---

# 7. Two `bad/` files the pass launders, and why

**A pass that erases levels erases lies told in levels.** Two files in
`vendor/arena-tests/bad/tutorial/` that `nanoda` rejects have monomorphized
output that `nanoda` accepts:

* `016_tut06_bad01.ndjson` declares `tut06_bad01.{u, u}` — a **duplicate
  universe parameter**. The copy has no parameters, and `Sort 1 := Sort 0` is
  fine. **Guarded** (§6.2): the pass now refuses the file, and it is rejected
  again.
* `049_inductWrongCtorResLevel.ndjson` declares
  `inductWrongCtorResLevel.{u1,u2}` whose constructor returns the type at
  `.{u2,u1}` — the level arguments **swapped**. At `σ = [0,0]` the swap is
  invisible. **Not guarded, and it cannot be guarded by a default**: any
  *diagonal* default assigns every parameter the same numeral, so no choice of
  `--default` distinguishes a permutation. Catching it needs a typechecker at
  symbolic levels, which is exactly the work the pass exists to remove.

So: **`monomorph` accepting a file is not a claim that the file was well typed.**
It trusts its input, like `modelgen`, and this is the sharp edge of that. A
pipeline that wants both should typecheck the original.

---

# 8. What a checker could then delete — an assessment, not an edit

In `mini` and `checker`, if the input were mode B's output:

* **`checker::instantiations` in its entirety.** The 511-line pre-pass, the
  worklist fixpoint, `Inst`, `Stats`, the published `SCHEDULE`, the
  `was_predicted` audit, and `DEFAULT_LEVELS` all exist to answer "which ground
  instantiations must this declaration be checked at". The answer is in the file.
  The 26% single-sweep undercount that module documents is a fact about doing
  this without file order; the export has file order.
* **`mini::ground::eval` and `Gap::SymbolicLevel`.** `ground.rs` evaluates a
  level at an instantiation; there is nothing left to evaluate. `SymbolicLevel`
  — the gap raised when a level is not ground — becomes unreachable.
* **`ConstKey`'s level component.** `mini` keys constants `(name, levels)`
  precisely because one declaration is checked at several instantiations under
  one name. Monomorphization makes the name the key, and `ConstKey` collapses to
  a `NamePtr`. That is the change with the widest blast radius and the largest
  payoff: every memo, every ledger entry and every certificate cache keyed on it
  loses a dimension.
* **`TcCtx::under_sigma` and `subst_expr_levels` at the declaration boundary.**
  Nothing to substitute.
* **`TgBackend::interp_sort`'s hedging, and `TyGap::PiUndet`.**
  `instantiations.rs`'s module doc records that `Level::simplify` never
  simplifies `IMax(l, r)` at a `Param` `r`, so a `Π` in `Sort (imax u v)` is a
  proposition at `v := 0` and a function space otherwise — **2206 `Π` nodes on
  `init-prelude`, 38% of the population**. Every one of them becomes a numeral
  and exactly one clause of §6.2 applies. This is the single largest thing the
  pass buys.

**What could not be deleted:** levels do not disappear from the *language*.
`Sort n` is still a level and the universe tower is still climbed; what goes is
level *variables*, `max`, `imax`, substitution and the schedule. And §3's ~22
carried built-ins still carry `levelParams` — used only at numerals, but a
checker must still accept a level list on `Eq`, `Quot`, `List`, `Nat` and the
axioms. Mode A additionally leaves one parameter per recursor, which is why mode
B exists.

None of this is done. `mini/` is untouched by this work.

---

# 9. Mathlib, measured

**The verdict, in one paragraph.** The blow-up on Mathlib is **1.158×** in mode
A and **1.166×** in mode B, and **93.6 %** of groups are still used at exactly
one instantiation — so "the blow-up is mild" survives, and survives with room to
spare. **The argument §5.1 gave for it does not.** The worst group on
`init-prelude` is used at five instantiations; on Mathlib nine groups are used
at **118**, and the tail past 40 is `CategoryTheory` with one exception. Separately, the
unmodified pass **cannot process Mathlib at all**: it refuses the file twice for
two different reasons, both of them real defects rather than scale, and after
both are patched around it computes the answer but **runs out of memory writing
it out**, at 44.9 GB. Every number below is from the commands named; §9.7 lists
what was not run.

## 9.1 The input, and how it was made

`lean-kernel-arena`'s `tests/mathlib.yaml` pins mathlib4 `v4.29.1` at rev
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`. `lake exe cache get` fetched 8229
prebuilt `.olean`s — **nothing was compiled from source** — and the export is
the arena's own `run_lean4export` invocation, from the Mathlib checkout:

```
lake env <lean4export>/.lake/build/bin/lean4export Mathlib > mathlib.ndjson
```

with `lean4export` at `caccfbe` and toolchain `leanprover/lean4:v4.29.1` —
`scripts/export-fixture.sh`'s pin. The result's meta line carries
`"githash":"f72c35b3f637c8c6571d353742168ab66cc22c00"`, **identical to every
file in `vendor/arena-tests`**, so this input and the corpus differ in content
and in nothing else.

| | |
| --- | --- |
| export wall / peak RSS | **210.69 s** / **12,017,472 KB** |
| bytes / lines | **5,636,308,621** / **100,001,405** |
| declaration records → declarations → groups | 654,504 → **670,630** → **654,305** |
| records | 81,237,178 `app`, 4,954,908 `forallE`, 1,293,582 `const`, 360 `bvar`, 7,848,345 other expressions, 3,971,928 names, 40,599 levels |
| declarations | 470,428 `thm`, 174,339 `def`, 6,644 `inductive`, 3,082 `opaque`, 7 `axiom`, 4 `quot` |

The file is **not** committed; at 5.6 GB it is far over any sane repo size, and
the arena does not ship it either (`lka.py`'s `TEST_SIZE_LIMIT` is 10 MB).

**A prefix of an export is an export.** Back-references only ever point
backwards, so any line-prefix of this file is a valid, self-contained input that
declares a downward-closed set of declarations — no re-export needed to get a
smaller one. That is the ladder in §9.5, and every row of it is genuine Mathlib
content rather than a smaller module standing in for it.

## 9.2 Two refusals, both real defects

Run unmodified, `monomorph` refuses Mathlib twice.

**The first was a bug in the naming scheme, and §1.1 no longer has it.** At 30
million lines, under the *previous* scheme:

```
pre-30000000.ndjson: passed through unchanged — two output declarations are both
named _private.Mathlib.Algebra.Category.MonCat.Basic.0.AddMonCat.Hom.mk
```

**The pass did not, and does not, strip a private prefix.** What happened is the
opposite: it **failed to rename**. The input has no duplicate declaration names
(checked over that same 30 M prefix: 184,960 declaration names, 184,960
distinct), so the pass created the collision. `AddMonCat.Hom` is a **public**
inductive with a **private** constructor
`_private.Mathlib.Algebra.Category.MonCat.Basic.0.AddMonCat.Hom.mk`. The old
§1.1 made a constructor's *owner* its `induct` and renamed by
`full.replacePrefix owner …`, which is **the identity when `owner` is not a
prefix of `full`** — so the constructor kept one name at every instantiation and
the block's second copy collided with its first. Across all of Mathlib: **142 of
9299 constructors** are private under a public inductive, **52** of them in a
block with level parameters, and **0 of 6796 recursors** were affected.

Private names are not the defect and no rule about them is the fix. The defect
was reading name *structure* at all; §1.1's marker is a root prefix and reads
none, and the private constructor is renamed by exactly the same rule as every
other name. `modelgen/monotests/mono_offname.ndjson` is the shape as a fixture —
a public `Off.{u}` with a private `mk`, used at three universes; the old binary
refuses it by name and the current one emits `_at.1.0.Off`,
`_at.1.0._private.MonoOffname.0.Off.mk` and `_at.1.0.Off.rec`, three times over,
with the kernel accepting all of it. On the 30 M prefix the pass now runs to
completion: **184,960 declarations in, 213,727 out, 0 rejected**, 155.72 s at
9,791,652 KB.

**The second is a property of the export.** On the whole file:

```
mathlib.ndjson: passed through unchanged — the file is not topologically sorted:
group 135365 mentions Lean.PrettyPrinter.Delaborator.TopDownAnalyze.AnalyzeAppM,
which group 420402 declares
```

§9.3. Both refusals are *correct behaviour under the contract as written*; what
they refute is the documentation's claim that neither shape occurs.

## 9.3 Sortedness: five groups, and they are tactics

`scripts/mono-sorted.py` enumerates every violation instead of stopping at the
first. It reproduces `monomorph`'s own grouping exactly — same group count, and
it independently names the same pair the pass reports — and on `init-prelude` it
agrees with §2 at **0 of 1777**. On Mathlib, **5 of 654,305 groups** mention a
name a later group declares (8 individual forward references):

```
Mathlib.Tactic.Ring.ExSum.eq          -> Mathlib.Tactic.Ring.ExBase.brecOn                    (+285675)
Lean.…Delaborator.TopDownAnalyze.analyze -> Lean.…TopDownAnalyze.AnalyzeAppM                  (+285037)
Mathlib.Tactic.Ring.ExSum.evalIntCast -> Mathlib.Tactic.Ring.instInhabitedSigmaQuotedExBase   (+116708)
Mathlib.Tactic.Ring.ExSum.cmp         -> Mathlib.Tactic.Ring.ExBase.brecOn                     (+65224)
Mathlib.Tactic.Ring.ExProd.evalNatCast -> Mathlib.Tactic.Ring.instInhabitedSigmaQuotedExBase   (+48828)
```

All five are the mutual machinery of `Mathlib.Tactic.Ring` and one Lean
delaborator — **tactic infrastructure, not mathematics**. So the single backward
pass is *nearly* sound on real input and not quite: `checker/src/instantiations.rs`'s
worklist fixpoint, which §2 presents as the thing file order lets you avoid,
handles these five and the backward pass does not.

**The export is not what is unsorted — §2.1's grouping is.** Checked on the
delaborator row, by line number in `mathlib.ndjson`:

| line | record |
| ---: | --- |
| 21,815,870 | `opaque …TopDownAnalyze.analyze`, `all` = a 12-member mutual block |
| 73,297,786 | `def …TopDownAnalyze.AnalyzeAppM` |
| 73,297,787 | the first reference to it anywhere in the file |
| 73,297,801 | `opaque …TopDownAnalyze.〈another member〉`, **the same `all` list** |

Nothing mentions `AnalyzeAppM` before it is declared, so the file *is*
topologically sorted in record order. What is not sorted is the group: §2.1
makes a mutual block one node, `buildGroups` opens it at its **first** member's
position, and this block's members are 51 million lines apart. Emitting the node
whole therefore moves the member at line 73,297,801 back to line 21,815,870, in
front of a declaration it uses — and the pass then reports the forward reference
it just created. `lean4export` is not implicated: it dumps each `opaque` where
its dependencies are ready, and a mutual `partial def` block need not be
contiguous for that.

Only this row was traced to line numbers; the other four are the same shape
(`Mathlib.Tactic.Ring`'s mutual machinery) but were not checked. **`nanoda`
agrees about the file as a whole**: it accepts all 670,630 declarations of
`mathlib.ndjson` in dependency order without a typechecker error (§9.7), which
it could not do if any of the five were a forward reference in the export.

The consequence for §9.6's `MONO_UNSORTED` is unchanged in size and different in
kind: the right fix is not a fixpoint over the file but a grouping that emits a
mutual `def` block's members where they stand.

## 9.4 Duplication — the answer

Measured with §9.6's `MONO_UNSORTED` on the Mathlib row, and re-measured after
§1.1's naming scheme replaced the other patch: **the counts are unchanged**,
which they must be — the scheme changes what a copy is called and not how many
there are.

| | declarations in | mode A | mode B |
| --- | ---: | ---: | ---: |
| `init-prelude` | 2059 | 2244 (1.090×) | 2365 (1.149×) |
| **Mathlib** | **670,630** | **776,723 (1.158×)** | **781,601 (1.166×)** |

Mode B costs **4,878** extra recursor copies over mode A — 0.63 %, against
5.4 % on `init-prelude`: recursors used at more than one motive universe are
rarer in Mathlib, relative to its size, than in the prelude.

Copies per group, over 654,305 groups:

```
 1 → 612545    7 →   767   13 →  78   19 →  62   25 →  16   34 →   1   51 →  7
 2 →  21342    8 →   340   14 →  85   20 →  21   26 →  20   35 →   3   53 →  1
 3 →   9840    9 →   294   15 →  73   21 →   4   27 →   7   36 →   2   54 →  1
 4 →   3933   10 →   212   16 →  60   22 →  34   28 →   1   43 →  21   57 →  7
 5 →   2808   11 →   157   17 →  35   23 →  12   30 →   1   44 →   1   59 →  2
 6 →   1263   12 →   169   18 →  15   24 →  19   31 →  22   45 →   3   64 →  2
                                                  32 →   1   48 →   2  100 →  1
                                                                       105 →  1
                                                                       113 →  5
                                                                       118 →  9
```

**612,545 of 654,305 = 93.6 % at exactly one instantiation**, against 92 % on
`init-prelude`. The aggregate claim holds. The tail does not:

| copies | groups |
| ---: | --- |
| **118** | `CategoryTheory.Functor.associator` and its eight `_proof_` companions |
| **113** | `CategoryTheory.Functor.comp` and its four `_proof_` companions |
| **105**, **100** | `CategoryTheory.Functor.comp_map`, `…comp_obj` |
| **64**, **59** | `CategoryTheory.Functor.whiskerLeft`, `…whiskerRight` |
| **57**, **51** | `CategoryTheory.Functor.whiskeringRight`, `…whiskeringLeft` (with their proofs) |
| **53** | `Function.comp` |
| **48**–**43** | `CategoryTheory.Functor`, `…Functor.obj`, `…Functor.map`, and the whole `CategoryTheory.NatTrans` family |

**The tail is category theory, and the reason is arity.**
`CategoryTheory.Functor.{v₁,u₁,v₂,u₂}` carries four universe parameters and
`Functor.comp` six; the number of ground instantiations is combinatorial in
them, and Mathlib really does use category theory at many universe
combinations. Nothing in the tail is an artefact of the pass — each copy is a
distinct instantiation the file demands. On the 20-million-line prefix the same
shape appears in miniature: `Function.comp` 28, `PSigma.casesOn` 16, `funext`
12, the `Equiv` and `DFunLike` families 10–11 (`scripts/mono-copies.py`).

**So: is the blow-up mild?** In bulk, yes — 1.158× is close to `init-prelude`'s
1.090× and nothing like the exponential a reader might fear. But a consumer
sizing a data structure per *group* should know that one group in Mathlib
becomes 118 declarations, and the `<= 5` of §5.1 is not a bound.

## 9.5 Speed, memory, and where it stops

| | wall | peak RSS |
| --- | ---: | ---: |
| `lean4export Mathlib` | 210.69 s | 12,017,472 KB |
| mode A, output **not** written | **749.32 s** | **34,426,172 KB** |
| mode A, instrumented (§9.6), output not written | 769.70 s | 34,353,660 KB |
| mode B, output not written | **1053.09 s** | **37,520,836 KB** |
| mode A, `-o` — *accumulating writer* | **fails at 953.28 s** | **44,869,080 KB** |
| **mode A, `-o` — streaming writer** | **815.42 s** | **36,203,968 KB** |
| *30 M prefix:* mode A, `-o`, unpatched binary | 155.72 s | 9,791,652 KB |
| *20 M prefix:* mode A | 86.87 s | 9,308,000 KB |
| *20 M prefix:* mode A `--check` (Lean's kernel over all 144,404) | 213.37 s | 6,380,364 KB |
| *20 M prefix:* mode B | 138.60 s | 9,542,160 KB |

**It used to stop at serialisation, and no longer does.** With `-o`, the pass
would finish the whole computation — printing the full report, all 776,723
declarations accounted for — and then die:

```
INTERNAL PANIC: out of memory
```

in `Export.render`, under a deliberate `ulimit -v` of 46,000,000 KB. Render
built an `Array String` of ~102 million lines and `String.intercalate`d it into
one ~6 GB `String`; that was the step with no streaming in it. `monomorph` could
monomorphize Mathlib and could not serialise it.

`Export.stream` (`Modelgen/Format.lean`) drains the writer's line buffer after
every record and flushes to the handle in 4 MiB chunks, so the largest live
object is that buffer rather than the file. **Mathlib now writes**:
**5,816,574,517 bytes, 101,934,568 lines, in 815.42 s at 36,203,968 KB**, under
a `ulimit -v` of 40,000,000 KB, exit 0. Against the run that wrote nothing at
all, serialising the whole 5.8 GB costs **+66.1 s (+8.8 %) and +1.78 GB
(+5.2 %)** — the extra memory is the writer's three interning tables, which the
`-o`-less run never builds.

Both paths through the writer are the same fold, and `monotest` checks that
`Export.writeTo` and `Export.render` produce the same bytes on every fixture in
both modes and that both reproduce `001_basicDef.ndjson` exactly.

Phase timings, from `monomorphize` entry (`MONO_PHASES=1`, §9.6), mode A:

| phase | cumulative | this phase |
| --- | ---: | ---: |
| groups | 1,289 ms | 1.3 s |
| reference sets | 27,172 ms | 25.9 s |
| **the `proj` replay** | 130,126 ms | **103.0 s** |
| sortedness | 133,910 ms | 3.8 s |
| closure + backward sweep + emission | — | 635.8 s |

Parse and process start are **not** instrumented; by difference between the
`-o`-less instrumented run and the unpatched run that refused at sortedness
(325.23 s), they are **≈ 190 s**, about a quarter of the pass.

**`Expr.proj` was the step flagged as most likely to hurt, and it does not.**
Replaying the input to infer projected types costs **103.0 s, 13.4 %** of a
769.7 s pass — real but not dominant; the backward sweep and emission are 83 %.
It is, however, the reason the pass needs a Lean `Environment` at all, and that
is where §9.7's hazard lives.

The ladder, mode A, `-o` written, on genuine Mathlib prefixes (unmodified binary
except the last row, which needs §9.6's `MONO_UNSORTED`):

| lines | bytes | decls in | out | ratio | groups | worst | recRegen | wall | peak RSS |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 M | 53,134,694 | 12,788 | 13,138 | 1.027× | 11,727 | 5 | 97 | 3.83 s | 490,332 KB |
| 3 M | 161,692,734 | 29,640 | 31,083 | 1.049× | 27,389 | 12 | 175 | 12.93 s | 1,488,672 KB |
| 10 M | 537,800,217 | 72,901 | 80,521 | 1.105× | 69,038 | 25 | 396 | 43.13 s | 4,826,692 KB |
| 20 M | 1,097,064,174 | 132,184 | 144,404 | 1.093× | 124,788 | 28 | 654 | 86.87 s | 9,308,000 KB |
| 30 M | 1,653,766,803 | 184,960 | 213,727 | 1.156× | 175,012 | 44 | 1,032 | 155.72 s | 9,791,652 KB |
| 100 M | 5,636,308,621 | 670,630 | 776,723 | 1.158× | 654,305 | 118 | 2,027 | 815.42 s | 36,203,968 KB |

**Memory is sublinear in the input and time is mildly superlinear.** Peak RSS
per input byte *falls* across the ladder and then flattens — 9.45×, 9.43×,
9.19×, 8.69×, 6.06×, **6.58×** — because the interning tables amortise; the last
two are within GC noise of each other and should not be read as a turn upwards.
Wall per million lines is flat at 3.8–4.3 s up to 20 M, 5.19 s at 30 M and
**8.15 s** at 100 M; the extra is the backward sweep and emission, not the
parse. So the wall clock is a large constant, not an explosion — but a linear
extrapolation from the small end would have *under*-predicted it by half.

**Both external oracles hold at Mathlib scale.** On the 20-million-line prefix,
`monomorph --check` — Lean's own kernel over every emitted declaration — takes
**213.37 s** at **6,380,364 KB** and rejects **0 of 144,404**; and `nanoda`
accepts the mode A output file. That is §4.1's oracle, run at 70× the size of
`init-prelude` rather than argued.

**The monomorphized file still checks faster, and by more.** `nanoda_bin`
handles Mathlib-scale input comfortably — it is far more frugal than the pass
that produced it — so this is measured on the 20-million-line prefix, the
largest mode A output that exists (§9.5: the full one was never written):

| | declarations | wall | peak RSS |
| --- | ---: | ---: | ---: |
| 20 M prefix, input | 132,184 | **331.36 s** | 1,681,672 KB |
| 20 M prefix, mode A output | 144,404 | **163.42 s** | 1,625,104 KB |

**2.03× faster on 9 % more declarations**, against 1.6× on `init-prelude`
(0.13 s → 0.08 s, re-measured here). The saving grows with the input.

## 9.6 The built-ins, and the two patches

**The carried set closed exactly where it does on `init-prelude`.** 31 groups on
Mathlib against 22, and the difference is entirely *seed* members that
`init-prelude` happens not to contain (`propext`, `Quot.sound`, `eagerReduce`,
`Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`).
The **closure** — §3's "mentioned by a carried declaration at a non-numeral
level" — added exactly one group, `Nonempty`, reached from `Classical.choice`,
which is the same single addition it makes on `init-prelude`. Over 654,305
groups the closure did not run away.

**Two patches were needed to measure §9.4 at the time, and one of them is now
unnecessary.**

1. `monoName` falling back to putting the marker at the *end* of the name when
   the owner is not a prefix of it — §9.2's private constructors. **Gone.**
   §1.1's scheme has no owner and no fallback; the shape it worked around is
   `monotests/mono_offname.ndjson` and is handled by the ordinary rule.
2. `MONO_UNSORTED=1` downgrades the sortedness refusal to a counted warning.
   **Still needed, and still not committed** — it lives in `Modelgen/Mono.lean`
   in a scratch worktree marked `EXPERIMENTAL, NOT FOR COMMIT`, inert unless
   triggered. §9.3's five forward references are a real defect in the single
   backward pass and are not fixed here, so the full-file rows of §9.4 and §9.5
   are measured with it on. **This makes the result an undercount**, and the
   size of the undercount is bounded: demand that the 5 violating groups push
   onto the 3 groups they reference forward is dropped, so at most those 3
   groups have fewer copies than they should. 3 of 654,305. Every row up to and
   including the 30 M prefix is the unmodified binary.

A third, `MONO_PHASES=1` and `MONO_TOP=n`, only prints.

## 9.7 What was not run, and one hazard found

* **Lean's kernel over the full mode A output.** Still not run: `--check`
  roughly doubles a pass that already peaks at 36 GB. It **is** run on the
  30-million-line prefix — the scale at which the old naming scheme collided —
  and rejects **0 of 213,727** in 297.36 s at 9,824,728 KB, and on the
  20-million-line prefix (0 of 144,404). §4.1's oracle holds at both.
* **`nanoda` on the full Mathlib mode A output.** **Run, and it stops**, at
  266.89 s / 6,514,308 KB:

  ```
  declaration not found in infer_const,
  Lean.PrettyPrinter.Delaborator.TopDownAnalyze.AnalyzeAppM
  ```

  That name is §9.3's, and it is the `MONO_UNSORTED` undercount made visible
  rather than a defect in the naming or the writer: the pass was told to ignore
  the forward reference, so the member that mentions `AnalyzeAppM` is emitted at
  its group's position rather than its own, and `nanoda` reads a file strictly
  in order. It is the same thing the unpatched binary refuses the file for.
* **`nanoda` on the unmodified Mathlib input** — the control for the row above,
  and not run before either. **It accepts the whole file**: *"Checked 670630
  declarations with no typechecker errors"*, **3011.42 s at 10,711,008 KB**.
  (One pretty-printer complaint, `Unable to print axioms`, which is not a
  checking result.) So the export really is in dependency order and the
  reordering above is `monomorph`'s — §9.3 traces it to the grouping, by line
  number, and this is the independent confirmation.
* **Mode B's output, at any Mathlib scale.** Counted, never written or checked —
  and §4.2 says no checker accepts it anyway.
* **The maximal sorted prefix.** §9.3 puts the first violation at group 135,365
  of 654,305, so a prefix cut exactly there would be the largest input the
  *unpatched* pass could accept. It was not built; the 30 M prefix (175,012
  groups) overshoots it and needs no patch only because the forward reference's
  *target* is not in the prefix either.

**The hazard.** During both replays — the `proj` environment and mode A's
recursor regeneration — Lean panics:

```
PANIC at Lean.AsyncConsts.add: duplicate normalized declaration name
  Lean.Meta.evalList vs. _private.Lean.Meta.ReduceEval.0.Lean.Meta.evalList
```

**1,726 times on the full file, over 767 distinct name pairs.** **This is Lean's
own private-name normalization and nothing the pass asks for.** `AsyncConsts.add`
keys a declaration by `privateToUserName`, which strips a `_private.<module>.<n>.`
root prefix; Mathlib contains public/private pairs that collide once flattened
into one `Environment`. `monomorph` never strips, never inspects and never
special-cases a private name — §1.1 renames one, if it renames it at all, by the
same root prefix as everything else. Do not read this paragraph and §9.2
together as one story: they are two unrelated mechanisms that happen to both
involve Mathlib's private names.

The panic is non-fatal — the pass reports `0` rejected and no errors — which is
precisely the problem: **the environment silently loses a declaration, and it is
the environment `inferProjType` is asked about in §6.3.** No wrong output was
observed and none was looked for. The pass's own duplicate guard compares names
*exactly* and cannot see this; Lean's kernel, which compares them *normalized*,
can. That makes it a real obstacle to §4.1's oracle on full Mathlib and not only
a noisy log.

One side effect of §1.1 is worth naming, because it is a side effect and not a
fix: a renamed declaration's root component is `_at`, so Lean no longer
classifies it as private and `privateToUserName` is the identity on it. The
panic therefore cannot fire between two *monomorphized* declarations, and the
count on the full file falls from **1,726 over 767 distinct pairs to 1,028 over
418**. What remains still fires during the input replay (§6.3), which is where
the hazard actually lives, and between declarations the pass left alone. The
obstacle is unchanged; only the noise is smaller.

None of §8 changes. `mini/` is still untouched by this work.
