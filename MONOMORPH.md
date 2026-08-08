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

**Mode B** adds one suffix, and only to a declaration that carries an
eliminating universe (§4.1): its copy at universe `w` is named `mono(d, σ) ++
_elim ++ ⟨w⟩`. `_at.1.0.Wrap.rec._elim.2`, and equally
`_at.1.0.PTree._model.rec_0._elim.0`. Mode B is the one place the output is
*not* a kernel's to re-derive, which §4.2 already says.

**The *renaming* composes with names another pass invented.** The pipeline is
`modelgen`, then `monomorph`, then `mini` (`MODELGEN.md`), so by the time this
scheme runs the file contains names `modelgen` synthesised — `T._model.k`,
`T._model.self`, `T._model.pack_i`, `T.rec_k`. Because the marker is a root
prefix, they are renamed by the same rule as everything else and their internal
structure survives: `poly_nested` through both passes in mode B yields
`_at.1.0.PTree._model.0` and its recursor
`_at.1.0.PTree._model.0.rec._elim.0` — derived from the model's *own* name,
which is itself derived.

**One thing about `_model` *is* known here, and it is a lookup and not a
rename.** The renaming above asks nothing about a name; §4.1's choice of *which
level parameter to keep* does, for two of the model's families, because nothing
structural distinguishes them. `Mono.modelCarrier` reads the innermost `_model`
prefix of a declaration's name and looks up that model's carrier
`T._model.self`, whose level parameters are `ℓ⃗` (`MODELGEN.md` §1.1 property
3); a parameter this declaration has and the carrier does not is the motive's
universe, and mode A keeps it. That is what puts `T._model.rec_k` and
`T._model.iota_k_j` under the same marker as their seven sibling families
(§1.3). It fails closed: a `_model` name with no carrier beside it is
monomorphized exactly as any other declaration.

**That is a claim about names and about nothing else. The composition is still
broken in one way, and §1.3 is where it is.** Do not read the paragraph above as
saying the pipeline works.

## 1.2 The three properties a consumer may rely on

1. **Every level in the output is a numeral `succ^n zero`, with exactly two
   exceptions**, and both are visible in the declaration itself.

   * **Mode A only:** a declaration may carry one level parameter — its
     eliminating universe, the motive's — and it is then the *only* entry of
     that declaration's `levelParams`. Every use of it in the file supplies a
     numeral. Those declarations are the recursors, and the `T._model.rec_k`
     and `T._model.iota_k_j` of a `modelgen` model, which carry the *same*
     universe for the same reason (§4.1). Mode B has no exception here:
     `levelParams` is empty everywhere it is not a built-in.
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
* **A mutual `def` block does not survive, and its `all` field says so.** Every
  `def`/`thm`/`opaque` in the output has a **singleton** `all` naming itself,
  whatever the input had. The members of one block are separate records that
  §2.1 instantiates independently, so `mono(m₁, σ)` can exist where
  `mono(m₂, σ)` does not, and a list naming both would name something no record
  declares. An `inductive` record's internal `all` lists are unaffected: there
  the copy at `σ` really is the whole block. Neither Lean's kernel nor `nanoda`
  reads the field — the point is that the file does not lie.
* **Acceptance by `monomorph` is not a claim about the input.** The input is
  trusted, and §7 names two `bad/` files whose defect the pass *erases*.
* **A `modelgen` model still does not survive this pass, and task #116 has to
  fix it before the pipeline runs end to end.** There were two failures here,
  both measured on `modelgen/tests/poly_nested_used.ndjson` — a nested
  `PTree.{u}` *used* at universes 0, 1 and 2 — put through `modelgen` and then
  `monomorph`. **One of them is closed and one is open.**

  1. **Open: one model for three copies.** `PTree` comes out three times
     (`_at.1.0.PTree`, `_at.1.1.PTree`, `_at.1.2.PTree`) and the model comes out
     **once**. Nothing in the file *references* a model — `mini` finds it by
     constructing the name, not through a use site — so the backward sweep sees
     no demand on the model's groups and they take `--default`. `_at.1.1.PTree`
     and `_at.1.2.PTree` have no model at all. This is about demand, not naming,
     and it is not a property of §1.1's marker: what it needs is for `monomorph`
     to key a model's declarations off **the declaration they model**, so that a
     model is emitted once per instantiation of it.

  2. **Closed: the marker is uniform across the model's families.** It was not.
     The nine families did not share a level-parameter arity — `self`, `pack_i`,
     `unpack_i`, `ctor_j`, `congrPack_i` and the model's inductive block carried
     the block's `[u]` while `rec_k` and `iota_k_j` carried the motive universe
     too, `[u_1, u]` — so the first group was renamed to
     `_at.1.0.PTree._model.…` and the second to `_at.2.0.0.PTree._model.…`, and
     a consumer deriving the whole family from the type's name (`mini`'s
     `nested_splice.rs` builds `Name::str(t, "_model")` and hangs all nine off
     it) found seven families and missed two, **even for the copy that did have
     a model.**

     §4.1's rule is what closed it: the motive's universe stays a level
     parameter, and `T._model.rec_k`'s motive universe **is** the motive
     universe of the recursor it models. Keeping it leaves those two families at
     `|ℓ⃗|` like the other seven, so the marker commutes with the model. Over
     `modelgen/tests` — every fixture through `modelgen` and then `monomorph` —
     **141 models, of which 90 were split across more than one marker and now 0
     are**, in mode A and in mode B alike.

     The tenth family is not a counterexample: a spliced `T._model.funext`
     (§`MODELGEN.md` 1.5) is genuinely polymorphic in universes that are nobody's
     motive, and it lands at its own marker. It is not one of the nine, nothing
     derives its name, and its uses are rewritten like any other reference.

  Neither failure was visible to a kernel: that fixture's output replays under
  `--check` with **0 rejected** over all 51 declarations, before and after,
  because a model is a `mini`-level artefact and nothing type-checks it against
  the copy it is supposed to model. So (1) is measured and not caught, and a
  green `--check` on that fixture must not be read as the blocker being closed.

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
the pass **asserts** it (`Mono.checkOrder`): every constant a group mentions
must be declared by a group at a lower index, and a file that violates it is
refused by group index and name. Measured over `vendor/arena-tests` (154 files
outside `perf/`, plus `init-prelude`): **zero violations.** Measured over
Mathlib, all 670,630 declarations in 654,504 groups: **zero violations**
(§9.3, and independently by `scripts/mono-sorted.py`).

The assertion is not a theorem about `lean4export` and it stays. It earned its
keep: the five Mathlib violations §9.3 used to report were a defect in §2.1's
*grouping*, and the check is what found it.

## 2.1 The DAG is over groups, and a group is one record

An inductive block's types, constructors and recursors mention one another
cyclically, so they cannot be ordered — and `lean4export` delivers them as a
single `inductive` record. That is the only cycle an export contains, so
**every record is exactly one group**: it collects one demand set, takes one
instantiation, and is emitted where it stands.

**A mutual `def` block is not a group**, and making it one was a defect (§9.3).
Its members share an `all` field, but what they share is provenance, not a
cycle: `lean4export` writes each member where its own dependencies are ready,
and 97 of Mathlib's 202 multi-member blocks are consequently *split* — the
widest across 513,481 records. Grouping by `all` opened each block at its first
member and so carried every later member backwards over that whole distance,
which in five blocks put a member in front of a declaration it uses. The pass
then refused the file for a forward reference it had created itself.

A member that genuinely mentioned a later member would make the export unsorted
in record order, and the assertion above would refuse it — correctly. So there
is nothing to merge, and no fixpoint: `all` is not read.

Two things follow, and both are contract. A split block's members are
instantiated **independently**, each at what its own users demand rather than at
the union. And a copy's `all` field names **that copy alone** (§1.3): with
independent instantiation `mono(m₁, σ)` can exist where `mono(m₂, σ)` does not,
so the input's list cannot be carried across.

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

**The motive's universe stays a level parameter.** Everything else is
substituted; the uses supply a numeral for the universe that is left. **This is
the mode whose output a kernel accepts**, because a kernel mints recursors
itself, from the inductive, and always with a universe parameter for the motive
when the block eliminates largely.

The rule is about *what the universe is* and not about where it sits, and it
therefore reaches past the recursors. Three shapes have one:

| | how the pass knows | what is kept |
| --- | --- | --- |
| a recursor | structurally: it is the record's own `recs` entry, and the parameter is the one its block does not have | that parameter |
| `T._model.rec_k` | by lookup: the parameter its model's carrier `T._model.self` does not have (§1.1) | that parameter |
| `T._model.iota_k_j` | the same | that parameter |

The second and third are not an analogy. `T._model.rec_k` **is** the export's
recursor at block index `k`, restated about the model's constants
(`MODELGEN.md` §1.1 property 1), so the extra universe it carries is that
recursor's motive universe — the very one the first row keeps. Treating it any
other way is what made the model's names non-uniform, and §1.3 is the
measurement.

**Which parameter it is, is decided semantically; that it is the *first* one is
asserted.** `Mono.buildGroups` finds it by set difference — against the block
for a recursor, against the carrier for a model's — because that is what makes
the rule mean "the motive's universe". A use site, though, splits its level
arguments on the head, since that is the hot path; Lean mints recursor
parameters motive-first (`Eq.rec.{u_1, u}`, `List.rec.{u, w}`) and `modelgen`
writes the same order, so the two agree on every export there is. If they ever
stop agreeing, the copy would come out with the right parameter and its uses at
the wrong one and nothing downstream would catch it — so the pass **refuses the
file** instead of assuming. Zero refusals over `vendor/arena-tests/good`'s 99
files and over every fixture in `modelgen/tests`.

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
uses it at (or per `--default` entry if none), and the same for the other two
shapes §4.1 leaves a parameter on — `T._model.rec_k._elim.w`. Mode B is a
**pure post-pass over mode A's own output** (`Modelgen.Mono.foldElim`), so "B is
A with the eliminating universe folded into the name" is true by construction
rather than by two parallel implementations. After it, `levelParams` is empty on
every declaration that is not a carried built-in.

**Which names those are is handed over, not re-derived.** Mode A decided, per
group, which parameter it was keeping; it passes the *output* names of the
non-recursors on. Guessing them back off the file — "a `def` or `theorem` with
exactly one level parameter" — would sweep up the carried built-ins, and
`Classical.choice.{u}` renamed to `Classical.choice._elim.0` is a constant no
kernel would recognise any more.

**Mode B needs a checker that does not regenerate recursors by name.** `nanoda`
does regenerate them, so it refuses mode B's output with
`Expected (Declar::Recursor, Declar::Recursor)` — it minted `T._at.σ.rec` and
looked for the export's declaration of that name, which mode B renamed. Run on
`init-prelude`'s mode B output it panics at `checker/src/inductive.rs:1269`,
exit 101, having retired **371,105,688 instructions** against the
**1,532,217,667** a full check of the same export costs — it dies about a
quarter of the way in, so **no check cost for mode B can be derived from it at
any scale**, and the amortization in §9.5 is measurable for mode A only. Lean is
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
| the six `monotests` fixtures, `--check`, end to end (six processes) | 0.688 s |
| `monotest` — all 99 `good/` files, `--check`, one process | **0.367 s** |
| *for reference:* `modelgen` on `init-prelude`, re-measured here | 0.238 s |

Whole-file figures, best of three, including ~0.1 s of process start.
`MODELGEN.md` §4.1 records 0.28 s for its own row; the 0.238 s above is that
same binary on this machine, so the two columns are comparable. The pass
is within 25% of `modelgen` on the same file while doing strictly more: the
replay `modelgen` needs anyway, plus a rewrite of every expression, plus a
second replay of the output.

**The monomorphized file also checks faster**, and this is a counter rather than
a stopwatch: `nanoda` on `init-prelude` retires **1,532,217,667 instructions**;
on mode A's output, 2244 declarations rather than 2059, it retires
**987,231,746** — **1.55× fewer, for 9 % more declarations**. Levels are not
free even in a kernel that keeps them. (The 0.152 s and 0.109 s this used to
quote were a 43 ms difference between two tenth-of-a-second runs on a shared
machine, which is not a measurement; the instruction counts agree with their
direction and are why the sentence survives.)

## 5.3 Acceptance

Over `vendor/arena-tests` outside `perf/`, with `--check` on:

* **`good/`: 99 files, 0 problems, 0 declarations rejected by Lean's kernel, and
  `nanoda` accepts every one of the 99 outputs.**
* `bad/`: 8 files refused whole (§7), and of the 47 that are not, `nanoda`
  still rejects 46. The one exception is §7's.
* `modelgen/monotests/`: six fixtures, mode A and mode B, kernel-checked and
  count-pinned in `modelgen/MonoTest.lean`; `monotest` runs 108 checks in
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
  constructor whose level parameters are not its block's` — Lean requires the
  block to share one list. There is no longer a clause for a mutual `def`
  block: §2.1 does not group one, so its members need not agree about anything
  and are each instantiated on their own.
* `a recursor with more than one elimination universe` — Lean mints exactly one.
* `an eliminating universe that is not the first level parameter` — §4.1's
  positional assertion. Lean writes a recursor's motive universe first and so
  does `modelgen`; a file where the set difference and the head disagree would
  otherwise be miscompiled silently, so it is refused.
* `the file is not topologically sorted: group i mentions N, which group j
  declares` — a property of `lean4export`'s output. Asserted rather than
  assumed; **zero occurrences in the corpus and zero in Mathlib**. It is *not*
  unreachable: it fired five times on Mathlib until §2.1's grouping stopped
  manufacturing forward references, which is what found that defect (§9.3), and
  `modelgen/monotests/mono_split.ndjson` is the shape it fired on.
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
axioms. Mode A additionally leaves the motive's universe as a parameter on every
recursor and on a model's `rec_k`/`iota_k_j` (§4.1), which is why mode B exists.

None of this is done. `mini/` is untouched by this work.

---

# 9. Mathlib, measured

**The verdict, in one paragraph.** The blow-up on Mathlib is **1.158×** in mode
A and **1.166×** in mode B, and **93.6 %** of groups are still used at exactly
one instantiation — so "the blow-up is mild" survives, and survives with room to
spare. **The argument §5.1 gave for it does not.** The worst group on
`init-prelude` is used at five instantiations; on Mathlib nine groups are used
at **118**, and the tail past 40 is `CategoryTheory` with one exception.
Separately, the pass **could not process Mathlib at all** when this section was
first written: it refused the file twice for two different reasons, both real
defects rather than scale, and after both were patched around it computed the
answer and then **ran out of memory writing it out**, at 44.9 GB. All three are
fixed — §9.2's naming scheme, §9.3's grouping, §9.5's streaming writer — and the
whole file now goes through the **unpatched** binary in 741.14 s at 35.3 GB,
with `nanoda` accepting all 776,723 output declarations (§9.7). Every number
below is from the commands named; §9.7 lists what was not run.

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
| declaration records → declarations → groups | 654,504 → **670,630** → **654,504** (§2.1: one record, one group) |
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

**The second was read as a property of the export and is not one.** On the whole
file:

```
mathlib.ndjson: passed through unchanged — the file is not topologically sorted:
group 135365 mentions Lean.PrettyPrinter.Delaborator.TopDownAnalyze.AnalyzeAppM,
which group 420402 declares
```

The export is sorted; §2.1's grouping was not, and the pass was reporting a
forward reference it had created. §9.3 is the measurement and the fix. So the
two refusals are not the same kind of thing: the first is the guard doing its
job on a real name collision, the second was the guard doing its job on a defect
one section earlier. Both refute the documentation's claim that neither shape
occurs on real input.

## 9.3 Sortedness: the pass was manufacturing the forward references

**Mathlib is topologically sorted and `monomorph` was not reading it that way.**
This section reported five violations for two rounds and blamed two different
things before the third measurement found the grouping. Both earlier readings
are wrong and are not repeated here; what follows is the state after the fix.

`scripts/mono-sorted.py` enumerates every violation instead of stopping at the
first, and reproduces `monomorph`'s grouping. Under the **old** grouping — a
mutual `def` block merged into one node by its `all` field — it found **5 of
654,305 groups** mentioning a name a later group declares (8 individual forward
references):

```
Mathlib.Tactic.Ring.ExSum.eq          -> Mathlib.Tactic.Ring.ExBase.brecOn                    (+285675)
Lean.…Delaborator.TopDownAnalyze.analyze -> Lean.…TopDownAnalyze.AnalyzeAppM                  (+285037)
Mathlib.Tactic.Ring.ExSum.evalIntCast -> Mathlib.Tactic.Ring.instInhabitedSigmaQuotedExBase   (+116708)
Mathlib.Tactic.Ring.ExSum.cmp         -> Mathlib.Tactic.Ring.ExBase.brecOn                     (+65224)
Mathlib.Tactic.Ring.ExProd.evalNatCast -> Mathlib.Tactic.Ring.instInhabitedSigmaQuotedExBase   (+48828)
```

**Every one of them was the grouping's own doing.** Traced on the delaborator
row, by line number in `mathlib.ndjson`:

| line | record |
| ---: | --- |
| 21,815,870 | `opaque …TopDownAnalyze.analyze`, `all` = a 12-member mutual block |
| 73,297,786 | `def …TopDownAnalyze.AnalyzeAppM` |
| 73,297,787 | the first reference to it anywhere in the file |
| 73,297,801 | `opaque …TopDownAnalyze.〈another member〉`, **the same `all` list** |

Nothing mentions `AnalyzeAppM` before it is declared, so the file *is*
topologically sorted in record order. The group was not: §2.1 made the block one
node, `buildGroups` opened it at its **first** member, and emitting the node
whole moved the member at line 73,297,801 back 51 million lines, in front of a
declaration it uses. `lean4export` is not implicated — it writes each `opaque`
where its dependencies are ready, and a mutual `partial def` block need not be
contiguous for that. **`nanoda` agrees about the file as a whole**: it accepts
all 670,630 declarations of `mathlib.ndjson` in file order without a typechecker
error (§9.7), which it could not do if any of the five were a forward reference
in the export.

**The five were the visible part, and the hazard was twenty times larger.**
Scanning every `all` field against record positions: Mathlib has **202 records
whose `all` names more than one declaration**, and **97 of those blocks are not
contiguous**. The distribution of what the old grouping was moving:

| split by | blocks |
| --- | ---: |
| ≥ 400,000 records | 12 |
| 100,000 – 400,000 | 54 |
| 10,000 – 100,000 | 28 |
| < 10,000 | 3 |
| **widest** | `Lean.FindLevelMVar.visit` / `.main`, **513,481 records** (lines 15,421,388 → 96,180,752) |

So the later members of 97 blocks were being carried backwards over up to half
the file, and the five that were caught are simply the ones whose relocation
crossed a declaration they use. The other 92 were relocated too and happened not
to. Reporting "five groups" understated it by a factor of twenty; the number
that matters is 97, and it is now zero.

**The fix is §2.1's: one record, one group.** `all` is not read. The five
disappear, the 97 relocations disappear with them, and the assertion — which is
what made the defect visible — is untouched. `scripts/mono-sorted.py`, updated
to the same grouping and run over the whole 5.6 GB file, is the independent
answer:

```
mathlib.ndjson: 100001405 lines, 654504 groups, 670630 declared names
  topological-sortedness violations: 0 of 654504 groups mention a name that a
  later group declares
```

**0 of 654,504**, in 98.27 s at 1,137,812 KB — one group per record, against
654,305 when 199 of them were merged by `all`.
`modelgen/monotests/mono_split.ndjson` is the shape at 220 lines, kept as a
regression: a `mutual partial def` whose two members are 73 records apart with a
user of the first and the inductive the *second* needs in between. It refuses
under the old grouping with the same message Mathlib gave.

**No prefix of the ladder reaches it.** All five violating blocks have their
later member past line 71 M and the prefixes stop at 50 M. Only **5** of the 97
split blocks lie wholly inside the 50 M prefix (3 inside 30 M), and the
**unmodified** binary passes `checkOrder` on it — measured, not inferred. The
defect was reachable only on the full file, which is why the regression is a
fixture and not a rung.

## 9.4 Duplication — the answer

Measured three times on the Mathlib row — under §9.6's `MONO_UNSORTED`, again
after §1.1's naming scheme replaced the other patch, and again with the
**unpatched** binary after §2.1 stopped grouping mutual `def` blocks — and
**the counts are unchanged at 776,723**. The first two must agree: a naming
scheme changes what a copy is called, not how many there are. The third did not
have to, and the reason it does is worth stating, because it is the size of the
undercount §9.6 used to carry: the 199 blocks that were merged were each used at
**exactly one** instantiation, so splitting them moves 199 groups into the
histogram's `1` bucket and emits the same declarations. The undercount was
bounded at 3 groups and measured at **zero**.

| | declarations in | mode A | mode B |
| --- | ---: | ---: | ---: |
| `init-prelude` | 2059 | 2244 (1.090×) | 2365 (1.149×) |
| **Mathlib** | **670,630** | **776,723 (1.158×)** | **781,601 (1.166×)** |

Mode B costs **4,878** extra recursor copies over mode A — 0.63 %, against
5.4 % on `init-prelude`: recursors used at more than one motive universe are
rarer in Mathlib, relative to its size, than in the prelude.

Copies per group, over 654,504 groups — one per record (§2.1):

```
 1 → 612744    7 →   767   13 →  78   19 →  62   25 →  16   34 →   1   51 →  7
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

**612,744 of 654,504 = 93.6 % at exactly one instantiation**, against 92 % on
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
12, the `Equiv` and `DFunLike` families 10–11.

The table above is `scripts/mono-copies.py` over the **whole** 5.8 GB mode A
output — 15.1 s, 190 MB, and it reproduces every row. That script had been
silently broken since §1.1 moved the marker to the *root*: it took the owner to
be everything *before* `_at`, which is now always empty, so it reported one
owner with 19 copies for `init-prelude` and would have reported one for Mathlib.
It reads the marker's length field now, as §1.1 says an inverter should.

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
| mode A, `-o` — streaming writer, `MONO_UNSORTED` | 815.42 s | 36,203,968 KB |
| **mode A, `-o`, unpatched — after §2.1's grouping fix** | **741.14 s** | **35,294,528 KB** |
| *50 M prefix:* mode A, old grouping | 207.46 s | 16,190,028 KB |
| *50 M prefix:* mode A, one record one group | 205.34 s | 16,113,804 KB |
| *30 M prefix:* mode A, `-o`, unpatched binary | 155.72 s | 9,791,652 KB |
| *20 M prefix:* mode A | 86.87 s | 9,308,000 KB |
| *20 M prefix:* mode A `--check` (Lean's kernel over all 144,404) | 213.37 s | 6,380,364 KB |
| *20 M prefix:* mode B | 138.60 s | 9,542,160 KB |

Re-taken with `perf` on the 20 M prefix, both modes back to back with one pinned
binary and `-o`: mode A **762,754,348,322 instructions** (IPC 2.122, 81.26 s,
6,425,736 KB), mode B **865,036,777,646** (IPC 1.786, 109.39 s, 6,983,276 KB).
**Mode B costs 1.134× the instructions and 1.346× the wall** — the 1.60× the two
rows above imply is a clock, and it overstates the work by two fifths because
mode B is markedly more memory-bound per instruction. **The full-Mathlib mode B
pass with `-o` remains unrun**: it needs ~39 GB, and no window in which that
plus the other seats stayed under the ~50 GB session ceiling has come up.

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
**5,816,542,757 bytes, 101,934,184 lines, in 741.14 s at 35,294,528 KB**, under
a `ulimit -v` of 40,000,000 KB, exit 0. Serialising the whole 5.8 GB costs
**166.2 s (22 % of the pass)** by the phase table below, and **+1.78 GB (+5.2 %)**
by the two rows above it that differ only in `-o` — the extra memory is the
writer's three interning tables, which the `-o`-less run never builds.

**§2.1's grouping fix is not a cost.** It removed the only patched row in this
table: 815.42 s / 36,203,968 KB with `MONO_UNSORTED` became **741.14 s /
35,294,528 KB** with the ordinary binary, and the output is **31,760 bytes and
384 lines smaller** — the `all` lists that no longer name a sibling copy. The
same comparison at the 50 M prefix, where the defect never bit, is 207.46 s →
205.34 s and 16,190,028 KB → 16,113,804 KB for byte-identical declaration counts
(342,668 out either way). One grouping is not measurably cheaper than the other;
the full-file difference is the patched run's overhead going away.

Both paths through the writer are the same fold, and `monotest` checks that
`Export.writeTo` and `Export.render` produce the same bytes on every fixture in
both modes and that both reproduce `001_basicDef.ndjson` exactly.

Phase timings (`MONO_PHASES=1`, §9.6), mode A, `-o`, whole file — the run in the
table above, so these add up to it:

| phase | cumulative | this phase |
| --- | ---: | ---: |
| read the file | 11,583 ms | 11.6 s |
| **parse** | 147,668 ms | **136.1 s** |
| `importModules` + entry | 148,392 ms | 0.7 s |
| reference sets | 174,050 ms | 25.7 s |
| **the `proj` replay** | 276,375 ms | **102.3 s** |
| sortedness + the carried closure | 279,041 ms | 2.7 s |
| the backward sweep | 300,465 ms | 21.4 s |
| **emission** | 564,950 ms | **264.5 s** |
| report | 574,224 ms | 9.3 s |
| **serialise and write** | 740,406 ms | **166.2 s** |

The parse is 18 % and reading the 5.6 GB off disk is another 1.6 %; emission is
36 % and writing the 5.8 GB back is 22 %. **Sortedness costs 2.7 s of a 741 s
pass** — the assertion §2 keeps is not what makes this expensive.

**`Expr.proj` was the step flagged as most likely to hurt, and it does not.**
Replaying the input to infer projected types costs **102.3 s, 13.8 %** of a
741.1 s pass — real but not dominant; the parse and the two serialisation ends
together are 42 % and emission alone is 36 %. It is, however, the reason the
pass needs a Lean `Environment` at all, and that is where §9.7's hazard lives.

The ladder, mode A, on genuine Mathlib prefixes. **Every row is the unmodified
binary**, the last one included — it was the one that needed `MONO_UNSORTED`
before §2.1's grouping fix, and its group count moved from 654,305 to 654,504
because 199 mutual `def` blocks are no longer merged. The 50 M row writes no
output; the rest write with `-o`:

| lines | bytes | decls in | out | ratio | groups | worst | recRegen | wall | peak RSS |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 M | 53,134,694 | 12,788 | 13,138 | 1.027× | 11,727 | 5 | 97 | 3.83 s | 490,332 KB |
| 3 M | 161,692,734 | 29,640 | 31,083 | 1.049× | 27,389 | 12 | 175 | 12.93 s | 1,488,672 KB |
| 10 M | 537,800,217 | 72,901 | 80,521 | 1.105× | 69,038 | 25 | 396 | 43.13 s | 4,826,692 KB |
| 20 M | 1,097,064,174 | 132,184 | 144,404 | 1.093× | 124,788 | 28 | 654 | 86.87 s | 9,308,000 KB |
| 30 M | 1,653,766,803 | 184,960 | 213,727 | 1.156× | 175,012 | 44 | 1,032 | 155.72 s | 9,791,652 KB |
| 50 M | 2,770,944,883 | 286,904 | 342,668 | 1.194× | 273,029 | 75 | 1,427 | 205.34 s | 16,113,804 KB |
| 100 M | 5,636,308,621 | 670,630 | 776,723 | 1.158× | 654,504 | 118 | 2,027 | 741.14 s | 35,294,528 KB |

**Memory is sublinear in the input and time is mildly superlinear.** Peak RSS
per input byte *falls* across the ladder and then flattens — 9.45×, 9.43×,
9.19×, 8.69×, 6.06×, 5.95×, **6.41×** — because the interning tables amortise;
the last three are within GC noise of each other and should not be read as a
turn upwards. Wall per million lines is flat at 3.8–4.3 s up to 20 M, 5.19 s at
30 M, 4.11 s at 50 M (that row writes no output) and **7.41 s** at 100 M; the
extra is the backward sweep and emission, not the parse. So the wall clock is a
large constant, not an explosion — but a linear extrapolation from the small end
would have *under*-predicted it by three quarters.

**Both external oracles hold at Mathlib scale.** On the 20-million-line prefix,
`monomorph --check` — Lean's own kernel over every emitted declaration — takes
**213.37 s** at **6,380,364 KB** and rejects **0 of 144,404**; and `nanoda`
accepts the mode A output file. That is §4.1's oracle, run at 70× the size of
`init-prelude` rather than argued.

**The monomorphized file still checks faster, and the pass pays for itself on a
single check.** Re-taken 2026-08-08 with **`perf stat -e instructions`**, one
pinned `nanoda_bin` for both checks and one pinned `monomorph` for the pass, all
three back to back — because a ratio of two wall clocks on this machine is not
evidence, and the three numbers this claim used to rest on were separate runs
hours apart (`MEASUREMENTS.md`, "Which recorded numbers carry weight").

| | declarations | **instructions** | wall | peak RSS |
| --- | ---: | ---: | ---: | ---: |
| **full Mathlib, input** | **670,630** | **22.823 T** | 2758.08 s | 10,715,200 KB |
| **mode A pass, `-o`** | — | **5.306 T** | 757.45 s | 35,292,700 KB |
| **full Mathlib, mode A output** | **776,723** | **9.760 T** | 1211.37 s | 10,759,940 KB |
| `init-prelude`, input | 2,059 | 1.532 G | 0.12 s | 11,600 KB |
| `init-prelude`, mode A output | 2,244 | 0.987 G | 0.08 s | 10,832 KB |

**The checker alone is 2.34× on 15.8 % more declarations**, and — the claim that
actually matters — **pass plus check is 1.51× the direct check**, so
monomorphizing Mathlib is cheaper than not doing it *on the very first check*,
not only on the second. Break-even is **0.41 of a check**: the pass costs
5.306 T and every check thereafter saves 13.063 T. On `init-prelude` the checker
ratio is **1.55×**, so the saving does grow with the input (1.55× → 2.34×), and
the memory does not: the output costs **0.42 %** more peak RSS than the input it
replaces.

**The wall clock had the direction right and the magnitude wrong.** The
superseded figures were 2.53× and, by implication, 1.56×; instructions say 2.34×
and 1.51×, so the clock overstated the checker ratio by **8 %**. The wall times
of these same three runs give 2.28× and 1.40× — understating it — so three
wall-derived answers to one question span **2.28–2.53×** while the instruction
count sits at 2.34× and does not move. **Peak RSS, by contrast, is
reproducible**: 10,715,200 KB here against 10,711,008 KB recorded for the same
work on a different day is **0.04 %**, the pass reproduces its own peak to
**0.005 %**, and it wrote a **byte-identical** 5,816,542,757-byte output.

The 20 M-prefix row that stood here (331.36 s / 163.42 s, "2.03×") is wall-only
and has not been re-taken; it is not evidence for anything and should be
re-measured with `perf` before it is cited.

## 9.6 The built-ins, and the two patches that are gone

**The carried set closed exactly where it does on `init-prelude`.** 31 groups on
Mathlib against 22, and the difference is entirely *seed* members that
`init-prelude` happens not to contain (`propext`, `Quot.sound`, `eagerReduce`,
`Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`).
The **closure** — §3's "mentioned by a carried declaration at a non-numeral
level" — added exactly one group, `Nonempty`, reached from `Classical.choice`,
which is the same single addition it makes on `init-prelude`. Over 654,504
groups the closure did not run away — and it is the same 31 either way: §2.1's
grouping change moves no group into or out of the carried set, on the full file
or on the 50 M prefix.

**Two patches were once needed to measure §9.4 on Mathlib. Neither exists any
more, and no figure in §9 is measured with a patched binary.**

1. `monoName` falling back to putting the marker at the *end* of the name when
   the owner is not a prefix of it — §9.2's private constructors. **Gone.**
   §1.1's scheme has no owner and no fallback; the shape it worked around is
   `monotests/mono_offname.ndjson` and is handled by the ordinary rule.
2. `MONO_UNSORTED=1` downgraded the sortedness refusal to a counted warning, so
   that the full file could be measured at all. **Gone, and it was never
   committed.** It existed because §9.3's five forward references were read as a
   defect in the backward pass; they were a defect in the *grouping*, and §2.1
   fixes that instead. The full file now passes `checkOrder` with the ordinary
   binary.

   **The undercount it caused is gone with it.** Under the flag, demand that the
   5 violating groups pushed onto the 3 groups they referenced forward was
   dropped, so at most 3 of 654,305 groups had fewer copies than they should —
   and `nanoda` saw exactly that, stopping at `…TopDownAnalyze.AnalyzeAppM`
   (§9.7). There is no caveat left on §9.4 or §9.5.

A third, `MONO_PHASES=1` and `MONO_TOP=n`, only prints.

## 9.7 What was not run, and one hazard found

* **Lean's kernel over the full mode A output.** Still not run: `--check`
  roughly doubles a pass that already peaks at 35 GB. It **is** run on the
  30-million-line prefix — the scale at which the old naming scheme collided —
  and rejects **0 of 213,727** in 297.36 s at 9,824,728 KB, and on the
  20-million-line prefix (0 of 144,404). §4.1's oracle holds at both. `nanoda`
  now covers the full file instead (next bullet), which the kernel does not.
* **`nanoda` on the full Mathlib mode A output.** Under `MONO_UNSORTED` it
  **stopped**, at 266.89 s / 6,514,308 KB:

  ```
  declaration not found in infer_const,
  Lean.PrettyPrinter.Delaborator.TopDownAnalyze.AnalyzeAppM
  ```

  That name is §9.3's. It was not a defect in the naming or the writer: the pass
  had been told to ignore the forward reference, so the member that mentions
  `AnalyzeAppM` was emitted at its *group's* position rather than its own, and
  `nanoda` reads a file strictly in order. It is the same thing the unpatched
  binary refused the file for, and it is the sharpest evidence that the ordering
  was wrong rather than the export.

  **After §2.1's grouping fix it accepts the whole file**: *"Checked 776,723
  declarations with no typechecker errors"*, exit 0, and §9.5 has since re-taken
  it as **9.760 T instructions at 10,759,940 KB** (the 1188.76 s once recorded
  here was a wall clock, and re-running the same work gave 1211.37 s). (The same one pretty-printer complaint, `Unable to print axioms`.)
  Nothing else changed — same naming scheme, same writer, same mode A — so this
  is the undercount and the reordering, gone. It is also the first time an
  external checker has read a **whole** monomorphized Mathlib.
* **`nanoda` on the unmodified Mathlib input** — the control for the row above,
  and not run before either. **It accepts the whole file**: *"Checked 670630
  declarations with no typechecker errors"*, re-taken in §9.5 as **22.823 T
  instructions at 10,715,200 KB**. (The 3011.42 s once recorded here was a wall
  clock; the same work re-run took 2758.08 s, while the peak RSS reproduced to
  0.04 %.)
  (One pretty-printer complaint, `Unable to print axioms`, which is not a
  checking result.) So the export really is in dependency order and the
  reordering above is `monomorph`'s — §9.3 traces it to the grouping, by line
  number, and this is the independent confirmation.
* **Mode B's output, at any Mathlib scale.** Counted, never written or checked —
  and §4.2 says no checker accepts it anyway.
* **The maximal sorted prefix.** Moot: §2.1's grouping accepts the whole file,
  so there is no prefix to find. Under the old grouping the first violation was
  at group 135,365 of 654,305; the 30 M and 50 M prefixes both overshoot that
  index and both pass anyway, because the forward reference's *target* is not in
  either prefix (§9.3).

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

## 9.8 Where the memory goes, counted rather than argued

**The hypothesis this section tests.** The export format is an arena: one line
per node, back-referenced, so a subterm with a hundred parents is stored once.
If the rewrite substitutes into an expression without memoising, that node is
rebuilt a hundred times and the in-memory DAG becomes a tree — which would
explain a peak of 32.8 GiB against 5.25 GiB of input while the *output file* is
only 3.2 % larger than the input, because the writer re-interns on the way out.

**The hypothesis is right about the mechanism and wrong about the magnitude.**
Sharing is lost, by a factor measured exactly; it is not where the memory is;
and restoring it in full costs more memory than it saves.

### Sharing, distinct versus total

`MONO_STATS=1` walks the input and the output twice — once deduplicating by
**pointer**, which is the DAG that is actually in memory, and once by
**structure**, which is the DAG the writer puts in the file. The ratio is the
duplication factor, and it is a count, not an estimate.

| input | input ptr | input struct | output ptr | output struct | **dup** |
| --- | ---: | ---: | ---: | ---: | ---: |
| `init-prelude` | 54,535 | 54,535 | 100,261 | 55,639 | **1.80×** |
| 1 M prefix | 914,195 | 914,195 | 1,712,266 | 845,124 | **2.03×** |
| 3 M prefix | 2,791,102 | 2,791,102 | 5,557,068 | 2,636,963 | **2.11×** |
| 10 M prefix | 9,465,222 | 9,465,222 | 19,546,691 | 8,633,504 | **2.26×** |

**The parser's sharing is perfect** — pointer and structure counts agree to the
node on every input, which is what an arena read by index should give and is
worth having as a fact rather than a belief. **The rewrite's is not**, and the
loss grows with the file: 1.80× on `init-prelude`, 2.26× at ten million lines.
The output has *fewer distinct* nodes than the input (8.63 M against 9.47 M at
10 M) and more than twice as many actual ones.

### Where the 3.30 GB of the 10 M prefix actually is

`MONO_PHASES=1` reports `VmRSS` at each phase boundary. The deltas sum to the
peak with nothing left over, so this is the whole of it:

| | live added | % of peak |
| --- | ---: | ---: |
| Lean runtime, before the file is opened | 93 MB | 2.8 % |
| the input file as a `String`, held to the end of `run` | 525 MB | 15.9 % |
| **the parsed input `Export`** | **1,178 MB** | **35.7 %** |
| the input replay `Environment` + `projCache` | 610 MB | 18.5 % |
| **emission: the output DAG + `monoEnv`** | **854 MB** | **25.9 %** |
| the writer's three interning tables | 38 MB | 1.2 % |
| | **3,298 MB** | |

So the pass is **input-dominated, not substitution-dominated**: reading and
holding the input is 70 % of the peak and emitting the substituted copies is
26 %. Of that 26 %, the *duplication* above accounts for 10.9 M of 19.5 M output
nodes — call it 9 % of the peak at 10 M. **A back-of-envelope that splits the
Mathlib peak as "≈10 GB of replay plus ≈22 GiB of substitution" is refuted by
this table**: at 10 M the substitution is a quarter, and it is the parse and the
input DAG that are the large terms.

**And the split holds at Mathlib scale, without running the pass again.**
`MODELGEN.md` §6.6 measures the same 5,636,308,621-byte export parsed and
stopped: **23,865,020 KB**, and adding the whole replay on top of it raises the
peak by nothing. `monomorph`'s 34,426,172 KB on the same file is therefore
**23.9 GB of input and ≈10.5 GB of emission** — 30 %, against the 26 % this
table measures at ten million lines, which is as close as two different tools
have any right to be. It also settles the arithmetic that motivated this work:
the substitution is *not* ≈22 GiB, and the replay is not ≈10 GB.

Two things that look like they should matter and were measured not to.

* **`IO.FS.readFile` costs the file twice** — `readBinFile` and the `String`
  `String.fromUTF8?` builds from it are live together, +1,050 MB for a 525 MB
  file — and **`text.splitOn "\n"` materialises every line of the file as a
  live list** before the first one is parsed, +587 MB. Both are real, and
  **neither raises the peak**: they are freed before emission and the allocator
  hands the same pages to the replay environment. Dropping `text` immediately
  after the parse (a one-line probe) changed the peak by **0.1 %**.
* **Reading the file a line at a time off a handle** removes all three at once
  and was tried. `IO.FS.Handle.getLine` did not finish the 1-million-line
  prefix in **ten minutes** against 3.6 s for the whole pass. Not a route.

### The memo: the key, the lifetime, and the gate, measured apart

The first cut of this section rejected a memo on the strength of one variant
that changed three things at once. Separated, and measured in **instructions**
(`perf stat`) rather than wall time, because nothing else on this box is
controlled:

* **the key** — the whole `σ`, or `σ` restricted to the level parameters the
  subterm actually mentions;
* **the lifetime** — reset at each copy, or kept for the whole emission;
* **the gate** — an entry for every node, or only for the nodes **the input
  arena shares**.

**The key must be canonical across declarations, and that is a soundness
property, not a tuning one.** The memo is looked up while emitting different
declarations and the `Expr` is shared between them, so naming a level parameter
by its *position in the declaring declaration's own list* gives two
declarations with opposite `levelParams` orders one key and two different right
answers. `monotests/mono_share.lean` is that shape — one shared type
expression, `fwd.{w,x}` and `rev.{x,w}`, used at instantiations that agree
positionally — and it is measured to discriminate: **2 of 13 declarations
rejected by the kernel replay under a positional key, 0 under the global one**,
with the declaration counts identical either way. So `paramIndex` numbers level
parameters **by name, once for the file**, and `RwCtx.binding` is sorted by that
number.

**Pruning is what makes the key pay.** Under the whole `σ`, a subterm mentioning
only `u` gets a different key for every value of every other parameter, and
Mathlib's tail is exactly the shape that punishes this: `Functor` has four
universe parameters, `Functor.comp` six, and `Functor.associator` reaches 118
copies (§9.4).

`MONO_MEMO` selects the variant. On the 10-million-line prefix:

| mode | key | lifetime | entries for | **dup** | memo+gate entries | **instructions** | **peak RSS** |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| `off` | — | per copy | — | 2.264× | ~0 | 407.94 G | 3,288,996 KB |
| `pure` | `e` | level-free only | every node | 2.048× | 1.06 M | 402.54 G | 3,221,304 KB |
| `full` | `(e, σ)` | emission | every node | 1.370× | 18.9 M | **396.70 G** | 4,198,360 KB |
| `prune` | `(e, σ|carrier)` | emission | every node | **1.299×** | 18.3 M | 401.78 G | 4,193,428 KB |
| `full-gate` | `(e, σ)` | emission | shared only | 1.482× | 3.55 M | 399.49 G | 3,175,916 KB |
| **`prune-gate`** | **`(e, σ|carrier)`** | **emission** | **shared only** | **1.413×** | **3.09 M** | **400.97 G** | **3,099,176 KB** |
| `prune-array` | `(e, σ|carrier)` uninterned | emission | shared only | 1.413× | 3.09 M | 406.45 G | 3,174,880 KB |

**Each change on its own.**

* **Lifetime** is the one that moves duplication: `pure` → `full` takes it from
  2.048× to 1.370×. It is also the one that cannot be had for free ungated.
* **Pruning** beats the whole `σ` on both axes wherever they are compared:
  ungated, 8.81 M poly entries against 9.43 M and 1.299× against 1.370×; gated,
  1.39 M against 1.85 M and 1.413× against 1.482×. It buys **25 % fewer entries
  and a better dedup at the same time**, which is what restricting a key to its
  actual dependency should do.
* **The gate decides the memory.** `prune` → `prune-gate` is **6.3× fewer poly
  entries** (8.81 M → 1.39 M) for a dedup that only slips 1.299× → 1.413×, and
  **1,094 MB off the peak**. A node with one parent is rebuilt once per rebuild
  of that parent, so memoising it buys nothing memoising the parent does not
  already buy — and an entry costs about what the node costs. That was the
  arithmetic the first cut got right and applied to the wrong population.
* **Interning the pruned substitution earns its table**: `prune-array` carries
  the sorted `Array (Name-index × Nat)` in the key instead, and pays **+1.4 %
  instructions and +2.4 % peak** for it.

**And the gate has to be built without building what it is gating away.** The
first `prune-gate` was a 4.9 % *regression* whose peak was reached in the
pre-pass, not in emission: computing the carrier of every node materialises an
8.4-million-entry table that is then thrown away. Caching a carrier **only for
the nodes that will keep one** costs nothing in the aggregate — an unshared node
has exactly one parent, so it is still computed once — and it is the difference
between 3,444,772 KB and 3,099,176 KB. Emission itself, under the gate, peaks at
3,081,572 KB against `pure`'s 3,207,756 KB.

The ladder, `off` (what this replaces) against `prune-gate` (the default):

| | instructions, off → prune-gate | peak RSS, off → prune-gate |
| --- | ---: | ---: |
| 1 M | 40.48 G → 40.09 G (−1.0 %) | 351,188 → **339,636 KB** (−3.3 %) |
| 3 M | 124.94 G → 122.15 G (−2.2 %) | 973,948 → **930,684 KB** (−4.4 %) |
| 10 M | 407.94 G → 400.97 G (−1.7 %) | 3,288,996 → **3,099,176 KB** (−5.8 %) |

**Better on both axes, and the margin grows with the file.** It is still not a
large number, and §9.8's opening stands: emission is a quarter of the peak, so
a quarter is all this could ever have been worth. What changed is the sign.

### The first cut, and why it was wrong

The first attempt at this section built two variants and rejected the good one,
and the mistake is worth keeping because it is a general one.

*What was measured.* `pure` (the `pure` row above) against a single memo over
**everything**, keyed on the whole environment and with an entry for every node
— the `full` row. `full` cut duplication 2.048× → 1.370× and cost **+12.6 %
peak RSS**, so it was rejected, and with it the whole idea.

*What was concluded, and why it does not follow.* "A `Std.HashMap` entry costs
about what the `Expr` node it saves costs, so break-even needs the memo to
eliminate more than one duplicate per entry; at 2.26× it eliminates 0.65." The
arithmetic is right. **The population is wrong.** It is the arithmetic of
memoising *every* node, and most nodes have one parent, so most of those entries
could never eliminate anything. Restricted to the nodes the arena actually
shares, the same memo eliminates **5.5 duplicates per poly entry** and the sign
flips. Two other things were bundled into the same rejection and never measured
apart: the key was the whole `σ` rather than the pruned one, and the gate's
pre-pass built the table it existed to avoid.

*The general form.* A memo rejected on a cost-per-entry argument has to say
**which entries**. "Hash-consing does not pay" and "hash-consing every node does
not pay" are different claims, and only the second was tested — here, and
plausibly in `APP-SPINES.md`'s 14 % too, which was also measured over all terms.

### The trap under all of it

The first emission-lifetime memo ran the 1-million-line prefix in **143.36 s**
against **3.93 s**. The memo was not the problem; `IO.Ref.get` was. [`rw`] read the
state with `get` and wrote it back with `set`, which leaves the ref holding the
map as well — so the first `insert` sees a refcount of two and **copies the
whole table**, once per top-level rewrite. With a per-declaration memo that is a
few hundred entries and invisible. With a memo that lives for the file it is
quadratic. `modifyGet` takes the value out of the ref first and the 37× goes
away. The fix is kept regardless of the memo, because the shape is a trap and
the comment on it is the point.

## 9.9 The parse, against an external baseline

`arena.lean-lang.org/test/mathlib` runs every checker on **this same
5,636,308,621-byte export** and publishes a **`parse-only`** entry: **8.5 GB**,
against `official` at 9.2 GB and `lean4lean` at 10.5 GB. So ~8.5 GB is roughly
what holding this export costs, and parsing dominates even a real checker's
memory. `MODELGEN.md` §6.6 measures our parse of the same file at **23,865,020
KB** — **2.8×** the baseline, and larger than the whole of `monomorph`'s
emission side.

**None of the excess is Lean's representation of the export.** Three probes on
the 10-million-line prefix (537,800,217 bytes), each stopping where it says:

| stops after | peak RSS |
| --- | ---: |
| `IO.FS.readFile` | 1,142,880 KB |
| … + `text.splitOn "\n"`, lines counted and dropped | 2,378,760 KB |
| … + `Json.parse` on every line, results dropped | 2,378,720 KB |
| … + the whole `Export` built | **2,381,908 KB** |

**The parse's entire high-water mark is reached before a single JSON object is
parsed.** Adding `Lean.Json` costs **nothing**; adding every `Expr`, `Name`,
`Level` and record in the file costs **3,148 KB, 0.13 %**. The composition:

| | 10 M prefix | × input bytes |
| --- | ---: | ---: |
| Lean runtime | 92 MB | — |
| the file as a `String`, live to the end of `run` | 525 MB | 1.00× |
| `readFile`'s `ByteArray`, freed — and one large block, so the small-object allocator cannot reuse it | 525 MB | 1.00× |
| **`text.splitOn "\n"`'s line list** | **1,236 MB** | **2.35×** |
| the parsed `Export`, in what the above freed | (523 MB) | (1.02×) |

Those four sum to 2,378 MB against a measured 2,379. Extrapolating —
`92 MB + 2 × filesize + 124 bytes × lines`, with 100,001,405 lines — predicts
**22.9 GB** for the full export against `MODELGEN.md`'s measured 23.9 GB, within
4 %. **The reader is the anomaly, and the `Export` at 1.02× the input's bytes is
not.**

### [`Export.parseHandle`], and what it recovers

4 MiB at a time, one chunk's lines held, [`readLine`] untouched. Output
byte-identical on `init-prelude`, on 20 MB, and on the 1 M and 10 M prefixes;
`MONO_SLURP=1` is the A/B.

| 10 M prefix | slurping | chunked |
| --- | ---: | ---: |
| live after the parse | 1,795,700 KB | **614,884 KB** |
| the parse's peak | 2,381,888 KB | **618,580 KB** (−74 %) |
| **the whole pass's peak** | **3,083,532 KB** | **2,170,272 KB** (−29.6 %) |
| instructions | 400.31 G | **395.19 G** (−1.3 %) |

**Less memory and fewer instructions.** The `Export` is now visible on its own:
**523 MB for a 512.9 MiB input, 1.02×**.

This does not make task **#119** — `monomorph` on `nanoda`'s Rust parser —
unnecessary; it removes the part of the case for it that was an accident of
`IO.FS.readFile` and `String.splitOn` rather than of Lean. What is left for
#119 is the 1.02×, which is the honest cost of the data.

### Three refcount traps, all the same shape

Every one of these was a >20× slowdown, none of them changed a byte of output,
and all three are the same mistake: **a second reference to a growing array at
the moment it is pushed to**, which turns an in-place `push` into a copy of the
whole array.

1. `IO.Ref.get` then `.set` around the rewrite memo: the ref still holds the map
   while the update runs. **143.36 s against 3.93 s** on the 1 M prefix.
   `modifyGet` takes the value out of the ref first.
2. Threading `RCtx` as a `mut` through a `for` nested inside a `while`: the
   outer loop's state is the second reference. **78.8 s against 0.49 s** on
   20 MB.
3. `match readLine c j with | .error e => (.error e, c) | ...` — **putting `c`
   back in the failure arm keeps it live across the call it was handed to**.
   **2.30 s against 0.09 s** on `init-prelude`, and the arm never fires.

The third is the one worth remembering, because nothing about it looks like a
performance decision. `MODELGEN.md` and this file both now carry a fourth of the
same family: an `x := y` inside a `match` arm whose sibling arm `return`s does
not escape the match at all, and `x` reads back as `default` — the pass reported
**zero declarations in** and exited 0.
