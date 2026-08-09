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
by Lean's kernel.

## Why you might want this

A checker that consumes Lean exports has to reimplement two awkward things:
the construction Lean's kernel performs for nested and mutual inductives, and
universe-level machinery.

These tools remove both from the checker's job:

* After `modelgen`, a checker never needs to *derive* a nested inductive's
  recursors and ι rules. They are in the file, as ordinary declarations, proved,
  under a documented naming convention. The checker only needs to recognise the
  names.
* After `monomorph`, a checker never sees a level variable.

In our own case this deleted a 2117-line Rust generator outright and is expected
to delete a further ~500 lines of level scheduling.

## Build and run

```bash
cd modelgen && lake build          # toolchain is pinned, see below

.lake/build/bin/modelgen  IN.ndjson [-o OUT.ndjson|-] [--check-recursors] [--quiet]
.lake/build/bin/monomorph IN.ndjson [-o OUT.ndjson] [--mono-recursors]
                                    [--default N[,N...]] [--check] [--quiet]
```

`-o -` writes the export to stdout. **The report always goes to stderr**, so a
consumer can stream the export and still read the diagnostics.

Exit statuses are meaningful and stable — `0` ran to completion *including every
decline*, `1` usage, `2` input unreadable or unparsable, `3` the tool's own
failure. A generated model whose statement does not match the installed
recursor's rule is a `3`, not a silently-written model.

**Toolchain**: pinned to `leanprover/lean4:v4.29.1` — the version `lean4export`
3.1.0 was built at (githash `f72c35b3`). The package is self-contained and does
not participate in the surrounding Rust build.

## `modelgen`

There are **two constructions**, because there are two kinds of declaration
whose recursors the kernel constructs:

* **Nested inductive** (`Modelgen/Model.lean`) — specialised into a mutual block
  with one extra *mimic* member per nested occurrence, with the export's own
  recursors proved over that.
* **Plain mutual block** (`Modelgen/Mutual.lean`) — the members' index
  telescopes packed into a tag, and the members into one *single* inductive
  indexed by it.

They are not one construction at two settings: a nested model *keeps*
mutuality, a mutual model *removes* it, so the second at zero mimics would be
the identity.

**They compose in one pass.** A nested declaration's model *is* a mutual block,
so the second construction runs on it too. Every mutual block in the output has
a model beside it — including the ones the tool just wrote.

A model is emitted **beside** what it models, never in place of it. The original
declarations are untouched.

### The interface: a naming convention

The contract is the whole point, and it is specified in `MODELGEN.md` §1 with
three properties a consumer may rely on and three it explicitly may not. In
outline, for a declaration `T`:

```
T._model.0 … T._model.{n-1}   the block
T._model.self                 the carrier
T._model.pack_i / unpack_i    the isomorphism, per mimic
T._model.unpackPack_i / packUnpack_i    both round trips
T._model.ctor_j               constructors
T._model.rec_k                recursors
T._model.iota_k_j             the ι rules, as theorems
T._model.congrPack_i
```

A consumer builds these names off `T` rather than pattern-matching them, which
is what makes the convention survive other renaming passes.

### The prelude

A model's proofs need `Eq`, the quotient, `Quot.sound` and `funext`. If the
input lacks any of them they are **spliced in** — `funext` is *derived* from
`Quot.sound`, not asserted as an axiom — and only when a model is actually being
generated, so a file with nothing to model comes back byte-identical.

## `monomorph`

Emits one copy of each declaration per level instantiation used, computed by a
single backwards pass over declaration groups (exports are topologically sorted,
so no fixpoint is needed). Declarations nothing references take a configurable
default, `--default 0`.

**Two recursor modes.** By default the eliminating universe stays a parameter,
which keeps the output acceptable to kernels that require recursors to be
level-polymorphic. `--mono-recursors` folds it into the name too, and needs a
checker liberal enough to accept a monomorphic recursor.

**Built-ins are left alone** — `Eq`, the `Quot` family and the standard axioms
are recognised (structurally, not by name, for the quotient) and passed through,
closed under "mentioned by a carried declaration at a non-numeral level".

Names are marked with a root prefix carrying the instantiation, which is
deliberately free of any dependence on the shape of the name being renamed.

**A model is instantiated with the declaration it models**, at exactly the same
set of instantiations — nothing in a file *references* a model, so without this
rule every model would take the default.

## Coverage

There is no shape Lean accepts that `modelgen` refuses. That claim is worth
exactly what it is measured against, so: it comes from a sweep of what Lean's
`inductive` command actually admits, and **every refusal path has a fixture**.
Three shapes remain that *Lean itself* rejects, recorded as boundaries with the
error Lean gives.

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

`envprobe` is a small diagnostic for the parse/replay phases.

## Design notes worth knowing before you read the code

* **The output is re-interned.** Any file that is modified is rewritten whole,
  because the export format's back-references must stay continuous. Files with
  nothing to splice come back byte-identical, and that property is measured.
* **The writer streams.** An earlier version accumulated the whole output as one
  string and died at Mathlib scale; `MONOMORPH.md` §9 has the numbers.
* **The reader streams too**, and this mattered more than expected — the parse
  was once 2.8× the memory of a purpose-built parse-only baseline, and all of it
  was the reader materialising lines, not the parsed data.
* **We keep our own writer rather than reusing `lean4export`'s.** It writes from
  an `Environment`; we emit records that deliberately differ, including
  declarations the replay rejected but that must still be written through.

## Where the detail is

* `MODELGEN.md` — the contract (§1), what is generated (§2), the oracles (§4),
  what is declined and why (§5), with gaps, boundaries and unreached arms kept
  apart.
* `MONOMORPH.md` — the naming contract, the backwards pass, the two recursor
  modes, and the Mathlib measurements.

Both are written verdict-first, with every number sourced to the command that
produced it and anything unmeasured named as unmeasured.
