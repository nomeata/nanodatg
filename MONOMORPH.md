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

Define `d`'s **owner** `o(d)`:

* if `d` is a member, a constructor or a recursor of an inductive block, `o(d)`
  is the block member it belongs to: the member itself; a constructor's
  `induct`; and for a recursor, the **longest** block-member name that is a
  prefix of the recursor's name — a real member's recursor lives in that
  member's own namespace and a nested mimic's in the first member's
  (`modelgen/tests/nest_mutual_both.ndjson` is where that was measured);
* otherwise `o(d)` is `d`'s own name.

Then

> **`mono(d, σ)`** is `d`'s name with the prefix `o(d)` replaced by
> `o(d) ++ _at ++ ⟨σ₀⟩ ++ … ++ ⟨σₖ₋₁⟩`, where `_at` is a `Name.str` component
> and each `⟨σᵢ⟩` is a `Name.num` component. **`σ` empty is the identity.**

`Wrap.{u}` at `[0]` is `Wrap._at.0`; its constructor `Wrap.mk` is
`Wrap._at.0.mk`; its recursor `Wrap.rec` is `Wrap._at.0.rec`. `Pair.{u,v}` at
`[1,0]` is `Pair._at.1.0`. A monomorphic declaration — `Nat`, `Nat.succ`,
`N.rec` — keeps its name **exactly**.

The owner is not a flourish. Lean's kernel and `nanoda` both *derive* a
recursor's name from the inductive's, so `Wrap._at.0`'s recursor has to be
`Wrap._at.0.rec` and cannot be `Wrap.rec._at.0`.

**Mode B** adds one suffix, and only to recursors: a recursor whose copy at
eliminating universe `w` is emitted is named `mono(d, σ) ++ _elim ++ ⟨w⟩`.
`Wrap._at.0.rec._elim.2`.

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
   trailing `._elim.⟨w⟩` if present, then find the unique `_at` component; the
   `Name.num` components immediately after it are `σ`, in the declaration's own
   parameter order, and deleting them gives the input's name.

## 1.3 What the contract does **not** say

* **Nothing about the order of the copies.** All copies of one group are
  contiguous and precede every use, but which `σ` comes first is the order the
  backward sweep discovered them in, and a consumer must not read anything into
  it.
* **Nothing about which instantiations exist.** A declaration nothing demands is
  emitted at `--default` (`[0]`), which is a choice and not a theorem (§2.2).
* **The copies are not related to each other.** `Wrap._at.0` and `Wrap._at.1`
  are two unrelated inductive types. There is no coercion, no shared recursor,
  and the pass does not claim `Wrap._at.0 = Wrap.{0}` — the input's `Wrap` is
  not in the output at all.
* **Acceptance by `monomorph` is not a claim about the input.** The input is
  trusted, and §7 names two `bad/` files whose defect the pass *erases*.

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
`init-prelude`): **zero violations.**

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
looked for the export's declaration of that name, which mode B renamed. Lean's
kernel refuses for the same reason. That refusal is the measurement that the two
modes are genuinely different, and it is expected.

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
five. Mathlib-scale input has not been measured and the shape of the histogram
there is not predicted by this.

## 5.2 Speed

| | |
| --- | --- |
| `init-prelude`, mode A | **0.288 s** |
| `init-prelude`, mode A `--check` (Lean's kernel over all 2244) | **0.384 s** |
| `init-prelude`, mode B | **0.306 s** |
| the five `monotests` fixtures, `--check`, end to end (five processes) | 0.688 s |
| `monotest` — all 99 `good/` files, `--check`, one process | **0.367 s** |
| *for reference:* `modelgen` on `init-prelude` | 0.238 s |

Whole-file figures, best of three, including ~0.1 s of process start. The pass
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
| `two output declarations are both named N` | `vendor/arena-tests/bad/126_dup_defs`, `127_dup_ind_def`, `128_dup_ctor_def`, `129_dup_rec_def`, `132_dup_ctor_rec` | these five are files Lean would reject too, so as *files* they are a boundary — but the guard is a gap in principle: a legitimate input in which two distinct declarations monomorphize to one name would be refused rather than merged. No such input is known. |

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
  assumed; zero occurrences in the corpus.
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
**five** (`Hashable`, `Inhabited`, `PProd`, `PULift`, `Subtype`) have more than
one copy, so a pass that guessed "the only copy" would be wrong on them.
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

* **`checker::instantiations` in its entirety.** The 512-line pre-pass, the
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
