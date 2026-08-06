# The `Nat` chain, measured where `NAT-REPRESENTATION.md` left gaps

`NAT-REPRESENTATION.md` §10 lists seven things it could not settle. This
document closes two of them and corrects one of its framings. Everything below
that is a number was produced in this repository by a command recorded beside
it; where a claim is inferred rather than observed it says so.

**Contents.** §1 is the one that decides the order of the chain: does
`init-prelude` need literal *computation*, or only literal *representation*?
§2 is `NAT-REPRESENTATION.md` §10.1 — whether `mini` can derive `Nat.add`'s
defining equations from the export's `brecOn`/`below` nest — answered on two
axes that must not be conflated. §3 is where Lean declares the characteristic
equations and which of them hold by `rfl`. §4 is the gating design that follows.

---

## 1. `init-prelude` needs computation, not only representation

**Answer: computation.** Making `2⁶⁴` *representable* is necessary and not
sufficient. `init-prelude` contains conversion checks that are decided only
because the checker evaluates `Nat.beq` and `Nat.ble` on literals — at operands
as large as `2⁶⁴` — and it contains no route to those checks that does not
compute.

### 1.1 The experiment

Lean's kernel and `checker/` both key the literal fast path **by name**:
`NameCache` is built by `find_name("Nat.add")` and friends
(`checker/src/util.rs:817–851`), and `try_reduce_nat` (`checker/src/tc.rs:587`)
compares the head constant against those cached pointers. So the acceleration
can be switched off, per operation, **from the input** — rename `Nat.add` to
`Nat.addXX` throughout the export's name table and `find_name` returns `None`,
after which `try_reduce_nat` never fires for it.

Nothing else changes. The declarations, their values, their types and every
literal in the file are byte-for-byte what they were; `Nat.zero` and `Nat.succ`
are untouched, so literal *representation* — `nat_lit_to_constructor`, the
`Nat.succ (lit n)` peel — is entirely unaffected. The renaming is consistent
(`Nat.add.match_1` becomes `Nat.addXX.match_1`), so the file still states the
same theorems.

```sh
# the renamer is 30 lines; it rewrites only the `str` field of the name entries
# whose prefix is `Nat` and whose string is one of the named operations.
python3 rename_ops.py init-prelude.ndjson out.ndjson add sub mul pow div mod beq ble
( ulimit -v 4194304; ./target/release/nanoda_bin cfg.json )
```

`target/release/nanoda_bin`, `nat_extension` and `string_extension` on,
`num_threads: 1`, `unsafe_permit_all_axioms`. This is the acceptance checker
(`NullCertifier`), not the `--features tg` proof backend, which is why the
baseline is 0.13 s rather than the 30–42 s `PERF-REVIEW.md` records.

### 1.2 The result

| accelerated operations switched off | outcome |
| --- | --- |
| *(baseline — none)* | **Checked 2059 declarations with no errors**, 0.13 s |
| `add` | ok, 0.13 s |
| `sub` | ok, 0.13 s |
| `mul` | ok, 0.13 s |
| `pow` | ok, 0.13 s |
| `div` | ok, 0.13 s |
| `mod` | ok, 0.13 s |
| **`beq`** | **abort** — 1 174 405 160-byte allocation refused, 16.9 s |
| **`ble`** | **abort** — same allocation, 17.9 s |
| `pow`, `mul` | ok, 0.14 s |
| `add`, `sub` | ok, 0.14 s |
| `add`, `sub`, `mul` | ok, 0.14 s |
| `div`, `mod` | ok, 0.13 s |
| **`pow`, `mul`, `add`** | **abort** — stack overflow, 2.2 s |
| **all eight** | **abort** — 1.17 GB refused, 17.6 s |
| all but `beq`/`ble` (i.e. only `beq`+`ble` left on) | **abort** — stack overflow, 2.2 s |
| all but `add`/`beq`/`ble` | ok, 0.14 s |
| all but `mul`/`beq`/`ble` | ok, 0.13 s |
| all but `pow`/`beq`/`ble` | ok, 0.13 s |

Only eight of Lean's fifteen names exist in the file at all — the renamer
reports `Nat.pow, Nat.mul, Nat.add, Nat.ble, Nat.beq, Nat.mod, Nat.div,
Nat.sub` and nothing else, which is `NAT-REPRESENTATION.md` §1.4 confirmed from
a second direction.

**Read off the table:**

* **`Nat.beq` and `Nat.ble` are each individually indispensable.** Removing
  either one alone kills the file. They are the only two operations of which
  that is true.
* **The six arithmetic operations are individually dispensable and jointly
  not.** Each of `add`, `sub`, `mul`, `pow`, `div`, `mod` can be switched off
  on its own at no cost, and `{pow, mul}` together is still free — but
  `{pow, mul, add}` is fatal. They form a *cascade*: `Nat.pow` recurses on the
  exponent into `Nat.mul`, `Nat.mul` recurses on its second argument into
  `Nat.add`, and both of those second arguments are small (`2^32` is 32 muls,
  each mul-by-2 is 2 adds), so whichever of the three is still accelerated
  absorbs the other two.
* **The minimal sufficient set is `{beq, ble}` plus any one of
  `{add, mul, pow}`.** `div`, `mod`, `sub` are never needed on this file.

### 1.3 Where, and at what sizes

Bisected by truncating the export at declaration boundaries — 1777 declaration
entries, binary search for the shortest prefix that fails.

**`ble` off — first failure is declaration #496,
`_private.Init.Prelude.0.isValidChar_UInt32`.** Its value is

```
… (of_decide_eq_true (55296 < UInt32.size) (Nat.decLt 55296 UInt32.size)
                     (rfl : Decidable.decide … = true)) …
```

and the same again at `1114112`, with `UInt32.size = 4294967296`.
`Nat.decLt n m` is `Nat.decLe (Nat.succ n) m`, and `Nat.decLe n m` is a `dite`
on `Nat.ble n m = true`, so the conversion the kernel is asked to decide is
**`Nat.ble 55297 4294967296 ≡ true`** and **`Nat.ble 1114113 4294967296 ≡
true`**. Unfolding `Nat.ble` structurally instead means 55 296 unrollings of
the `brecOn` nest, which is where the 1.17 GB goes.

**`beq` off — first failure is declaration #1093, `USize.size_eq`.** Its value
carries

```
of_decide_eq_true (2^32 = 4294967296) (instDecidableEqNat …) (rfl …)
of_decide_eq_true (2^64 = 18446744073709551616) (instDecidableEqNat …) (rfl …)
```

so the demanded conversions are **`Nat.beq (Nat.pow 2 32) 4294967296 ≡ true`**
and **`Nat.beq (Nat.pow 2 64) 18446744073709551616 ≡ true`** — which is also
where the one arithmetic operation is needed, to get `2 ^ numBits` to a literal
in the first place.

So the sizes are the file's largest literals: `2³²` and `2⁶⁴`, and comparisons
against them from 55 296 and 1 114 112.

### 1.4 What this changes

`NAT-REPRESENTATION.md` §11's staging said the binary representation "is
available the moment step 2 lands, before any arithmetic exists". That is right
about *loading* the file and wrong about *checking* it. Corrected staging:

1. **Step 2 (representation)** lifts the load-time gate, `natLits=35`,
   `maxNatLit=18446744073709551616`. The file reaches interpretation.
2. **`beq` and `ble` are then immediately on the critical path**, at operands
   up to `2⁶⁴`. Nothing else about them is optional or deferrable, and they are
   *not* the operations §6.4's order-of-work put first among equals — they now
   go first outright.
3. **One of `add`/`mul`/`pow`** is needed, to evaluate `2 ^ numBits`. `pow` is
   the cheapest single choice for this file (it removes the cascade entirely),
   `add` the cheapest to build.
4. `sub`, `div`, `mod` are not needed by `init-prelude` at all — which puts
   them beside `gcd`/`land`/`lor`/`xor`/`shiftLeft`/`shiftRight` in the "later
   file" bucket, and that is a **correction** to §6.4's order, which listed
   `sub`, `div` and `mod` among the nine that unblock the file.

Both fatal sites are `of_decide_eq_true … (rfl …)`, i.e. *decision procedures
evaluated at literals*, not arithmetic for its own sake. That is worth knowing
for step 3: what `init-prelude` wants is a **comparison** kernel, and `beq`/`ble`
on a canonical binary representation are single Θ(bits) passes — Coq's
`compare_cont`, `NAT-REPRESENTATION.md` §3.1 — which is the cheapest thing in
the whole operation table.

---

## 2. `NAT-REPRESENTATION.md` §10.1, answered: acceptance yes, certification no

The bridge instantiates at `f := ⟦Nat.add⟧` and needs

```
Nat.add n 0       = n
Nat.add n (m+1)   = Nat.succ (Nat.add n m)
```

from the export's own definition. The plan of record synthesises them as
declarations proved by `rfl`, inserted after `Nat.add` is declared. The fixture
`mini/tests/fixtures/nat_char_equations.lean` is that synthesised declaration
written by hand, one step ahead of the generator, for all eight in-scope
operations; `mini/tests/nat_equations.rs` pins the measurement.

### 2.1 What the export actually contains

`Nat.add` is `brecOn`-shaped, not a recursor application. Its value is 90
expression nodes (`vendor/arena-tests/good/init-prelude.ndjson`):

```
fun n m => Nat.brecOn.{1} (motive := fun _ => Nat → Nat) m
             (fun m f n => Nat.add.match_1.{1}
                             (fun a b => Nat.below.{1} … → Nat) n m
                             (fun a _ => a)                          -- zero
                             (fun a b (f : Nat.below … (Nat.succ b)) -- succ
                                 => Nat.succ (f.PProd.0 a))
                             f)
             n
```

with `Nat.brecOn` itself `(Nat.brecOn.go motive t F).PProd.0`, `Nat.brecOn.go`
a `Nat.rec` building the `PProd` tower, `Nat.below` a `Nat.rec` into
`PUnit`/`PProd`, and `Nat.add.match_1` a `Nat.casesOn`. Recursion is on the
**second** argument.

Uniform with it: `Nat.sub` (98 nodes), `Nat.mul` (108), `Nat.pow` (86),
`Nat.beq` (118), `Nat.ble` (104) — all `Nat.brecOn`. Two differences worth
recording, because they turn out not to matter and a later reader would
otherwise re-derive them: `Nat.beq`/`Nat.ble` recurse on the **first**
argument, and `Nat.pow`'s motive is `fun _ => Nat` rather than
`fun _ => Nat → Nat`.

**`Nat.div` and `Nat.mod` are not primitive-recursive and have no such
equations.** `Nat.div x y` is
`dite (0 < y) (fun hy => Nat.div.go x y (Nat.succ x) x _) (fun _ => 0)`, a
fuel-driven inner loop; `Nat.mod` routes through `Nat.mod.match_1` into
`Nat.modCore`, the same shape.

### 2.2 Acceptance — **yes**

```
$ ./target/debug/mini --acceptance-only --verbose mini/tests/fixtures/nat_char_equations.ndjson
nat_char_equations.ndjson  accept  44 declarations
                                                                   exit = 0
```

mini's `whnf`/`defeq` decides all seventeen equations: both `add` equations,
both `sub`, both `mul`, both `pow`, four `beq`, three `ble`. So the
`brecOn`/`below` nest is **not** an acceptance obstacle, and the plan of
synthesising `rfl`-proved declarations is viable at that level. (Lean itself
agrees, at `v4.29.1`: all seventeen elaborate, and so do the notation forms
`Nat.add n 0 = n` and `Nat.add n (m+1) = Nat.add n m + 1`.)

### 2.3 Certification — **no**, for all seventeen

```
$ ./target/debug/mini --verbose mini/tests/fixtures/nat_char_equations.ndjson
nat_char_equations.ndjson  accept  44 declarations
                           uncertified: 24 const typings, 15 type typings, 6 conversions
evidence  pairs=38  typeEv=23  constEv=14  unsealed=0
          library-gap=12  threading-incompleteness=12
          waiting:proj(PProd)=12  waiting:no-endpoint=12
                                                                   exit = 4
```

Per declaration, from `--dump-theorems`:

| declaration | certified | gap |
| --- | --- | --- |
| `recAdd`, `recAddZero`, `recAddSucc` | **yes** | — |
| `Nat.below`, `Nat.brecOn`, `Nat.brecOn.go`, `Nat.casesOn` | **yes** | — |
| `Nat.add.match_1`, `Nat.beq.match_1`, `Nat.ble.match_1` | **yes** | — |
| `Nat.add`, `natAddZero`, `natAddSucc` | no | `proj(PProd)` *[Library]* |
| `Nat.beq`, `natBeqZZ`, `natBeqZS`, `natBeqSZ`, `natBeqSS` | no | `proj(PProd)` |
| `Nat.ble`, `natBleZ`, `natBleSZ`, `natBleSS` | no | `proj(PProd)` |
| `Nat.sub`, `natSubZero`, `natSubSucc` | no | `no-endpoint` *[Threading]* |
| `Nat.mul`, `natMulZero`, `natMulSucc` | no | `no-endpoint` |
| `Nat.pow`, `natPowZero`, `natPowSucc` | no | `no-endpoint` |

**The control is the finding.** `recAdd` is the same recursion — `Nat.rec`
`(fun _ ih => Nat.succ ih)` — written without the elaborator's structural
compiler, and it certifies completely: value, typing, and both equations. So
the obstruction is not `Nat`, not `⟦Nat.rec⟧`, not primitive recursion and not
the equations themselves. It is what Lean's structural-recursion compiler
emits.

Nor is it the nest's *scaffolding*: `Nat.below`, `Nat.brecOn`, `Nat.brecOn.go`,
`Nat.casesOn` and the three `match_1`s used by `add`/`beq`/`ble` all certify on
their own. It is the operation's own value that does not.

### 2.4 Where it stops, by census

The reason string here has to be checked, not trusted — the census is the
instrument, and the *release* binary's census is misleading, because
`blocker::source_line` reads the current tree while the recorded `file:line`
comes from whatever source the binary was compiled from. `target/release/mini`
(15:04) predates `HEAD` (15:58) and printed `kernel.rs:1878 ///`. The debug
binary is consistent with the tree and is what the numbers below come from.

For `Nat.add`, `--block` reports:

```
BLOCKED  Nat.add  proj(PProd)
  obligation   the value's interpretation, ⟦val[σ]⟧
  gap          proj(PProd)   [Library]
  in hand
    ⟦ty[σ]⟧             = dprod₀(dprod₀(⟦Nat.{}⟧, ⟦Nat.{}⟧), ⟦Nat.{}⟧)
    ⟦val[σ]⟧            — absent (proj(PProd))
    ⊢ ⟦val[σ]⟧ ∈ ⟦ty[σ]⟧ — absent (proj(PProd))
  gave up at
    mini/src/kernel.rs:1902   (app_evidence's `blocked`)      ×3
    mini/src/kernel.rs:2208   (lam_evidence's reason forward) ×5
```

Both trailed sites are **forwardings** — `app_evidence`
(`kernel.rs:1890–1910`) and `lam_evidence` each re-mint whichever premise's gap
was missing, so neither is the origin. The origin is not in the trail because
it is an `Err(Gap)` rather than an `Ev::missing`: `proj_data`/`proj_prop` return
`Err(Gap::StructProj)` and `kernel.rs:1812–1814` turns it into the `Ev`. Reading
the trail as a location would have named `app_evidence`, and that would be
wrong.

**And the obvious hypothesis about which projection is wrong.** The natural
guess is that `f.PProd.0` fails because `f`'s type is `Nat.below motive
(Nat.succ n)`, which only *reduces* to `PProd`. Measured: it does not fail.

```lean
noncomputable def belowFst (motive : Nat → Type) (n : Nat)
    (f : Nat.below (motive := motive) (Nat.succ n)) : motive n := f.1
```

certifies. (The probe that holds it — `belowFst` plus a syntactically-`PProd`
projection plus the `recAdd` control — is `pairs=7 typeEv=7 constEv=7`, exit 0,
i.e. everything in it.) So a projection out of a
`below`-typed subject is fine in isolation, and what defeats `Nat.add` is
something about the whole nest rather than that one clause. **This is a real
open item**; it is not "projections are unwired", and the next seat should not
brief it as such.

The `sub`/`mul`/`pow` third of the table is a *different and earlier* blocker,
and the label `no-endpoint` masks it. Isolating `pow` alone:

```
BLOCKED  Nat.pow.match_1  σ = u_1 := 1  no-endpoint  [Threading]
  ty  (∀ _:(∀ _:Nat, Sort 1),
       (∀ _:Nat,
        (∀ _:(∀ _:Unit, (#2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))), …)))
```

`Nat.pow.match_1` — which `Nat.pred` and hence `Nat.sub` also use — carries
`OfNat.ofNat Nat 0 (instOfNatNat 0)` in its motive, and the run records
`convGap:proj(OfNat)=2`. So those three are blocked twice over: once by the
numeral wrapper, and (behind it) by the same nest as the other three.

### 2.5 The eight in scope — are they uniform?

**Three groups, not one.**

| operation | `rfl` in Lean? | mini accepts? | mini certifies? | gap |
| --- | --- | --- | --- | --- |
| `add` | yes | yes | no | `proj(PProd)` |
| `beq` | yes | yes | no | `proj(PProd)` |
| `ble` | yes | yes | no | `proj(PProd)` |
| `sub` | yes | yes | no | `no-endpoint` + `proj(OfNat)` |
| `mul` | yes | yes | no | `no-endpoint` + `proj(OfNat)` |
| `pow` | yes | yes | no | `no-endpoint` + `proj(OfNat)` |
| `div` | **no** | — | — | no such equation exists |
| `mod` | **no** | — | — | no such equation exists |

Six of the eight are uniform in the shape of what has to be fixed. `div` and
`mod` are a different problem entirely — their characterisation is
`div_unique`-shaped (`Nat.div_eq`, §3), proved by induction on the fuel, not by
`rfl` — and §1 says they are not on `init-prelude`'s critical path anyway.

---

## 3. Where the characteristic equations live, at `v4.29.1`

Read from `~/.elan/toolchains/leanprover--lean4---v4.29.1/src/lean`.

| theorem | file:line | proof |
| --- | --- | --- |
| `Nat.add_zero : n + 0 = n` | `Init/Core.lean:745` | `rfl` |
| `Nat.add_succ : n + succ m = succ (n + m)` | `Init/Data/Nat/Basic.lean:146` | `rfl` |
| `Nat.mul_zero : n * 0 = 0` | `Init/Data/Nat/Basic.lean:195` | `rfl` |
| `Nat.mul_succ : n * succ m = n * m + n` | `Init/Data/Nat/Basic.lean:198` | `rfl` |
| `Nat.sub_zero : n - 0 = n` | `Init/Data/Nat/Basic.lean:268` | `rfl` |
| `Nat.sub_succ : n - succ m = pred (n - m)` | `Init/Data/Nat/Basic.lean:285` | `rfl` |
| `Nat.pow_succ : n^(succ m) = n^m * n` | `Init/Data/Nat/Basic.lean:790` | `rfl` |
| `Nat.pow_zero : n^0 = 1` | `Init/Data/Nat/Basic.lean:796` | `rfl` |
| `Nat.zero_add`, `Nat.succ_add` | `Init/Data/Nat/Basic.lean:135, 142` | induction |
| `Nat.div_eq : x / y = if 0 < y ∧ y ≤ x then (x-y)/y + 1 else 0` | `Init/Data/Nat/Div/Basic.lean:39` | `by` |
| `Nat.mod_eq : x % y = if 0 < y ∧ y ≤ x then (x-y) % y else x` | `Init/Data/Nat/Div/Basic.lean:158` | `by` |
| `Nat.beq`, `Nat.ble` | — | **no recursion equations in core at all** |

For `beq`/`ble` Lean proves only `Nat.beq_refl`, `Nat.beq_eq`, `Nat.ble_eq`
(`Init/Data/Nat/Basic.lean:118, 122, 123`) — reflections into `=` and `≤`, not
the four/three defining clauses. Those clauses *are* `rfl` (measured, §2.2),
they simply have no name in Lean. So for the two operations `init-prelude`
actually needs, "the prelude declares them" is false in a stronger sense than
for the rest: they are not declared anywhere in core, under any name.

None of the equations above are in `Init.Prelude`, which is why none of them
are in `init-prelude.ndjson`.

---

## 4. What follows for the gating design

The design is: synthesise the characteristic equations as declarations with an
internal name right after the operation is declared, check them, and only then
store `⟦Nat.add⟧ = primitive_nat_add` and enable the native path. Three things
this measurement says about it.

**4.1 It is more honest than Lean's kernel, and that is a checkable claim.**
Lean's `initialize_type_checker` builds `mk_constant({"Nat","add"})` and never
looks at the definition (`NAT-REPRESENTATION.md` §2). Our version refuses to
accelerate until it holds a *proof about this environment's* `Nat.add`. §2.2
shows the proof obligation is decidable by mini's conversion today, so the gate
is one that can actually close rather than one that will always be open.

**4.2 The gate must be per-operation, and it must fail closed.** §1 says the
operations are not interchangeable: `beq`/`ble` are indispensable, one of
`add`/`mul`/`pow` is needed, `sub`/`div`/`mod` are not needed by this file.
A gate that enabled the whole table on one operation's proof would be
accelerating five operations it has no evidence about. And `div`/`mod` have no
primitive-recursion equation to gate on at all — they need a `div_unique`-shaped
characterisation, and until one exists their native path stays off.

**4.3 It should inherit `mutual_aux`'s discipline.** Synthesising Lean
declarations and pushing them through the pipeline to pluck certificates is what
`mini/src/mutual_aux.rs` already does: `expand` inserts generated declarations
into the stream between the kernel pass and the ledger, under the block's own
names, with no install step. The generator for the `Nat` equations is the same
shape and should inherit the same mechanically-enforced black-box invariant —
`ci/check-mutual-blackbox.sh`, an allowlist by name over `kernel::{add,
sort_under}`, self-tested by planting a `Thm`. A generator that could name a
`Thm` would be able to *assert* `⟦Nat.add⟧ = primitive_nat_add` rather than
prove it, which is precisely the trust the design exists to avoid.

**4.4 Until §2.3's gap closes, the equations are hypotheses.**
`NAT-REPRESENTATION.md` §8's fallback stands and is now the near-term answer:
thread the equations as kernel hypotheses, discharged per file or reported in
the ledger as a named assumption. It decouples the representation and the
arithmetic from the equation derivations, and it is still strictly better than
name-keyed trust — the assumption is *stated*, in the ledger, per file. The
fixture and its test are what will tell us when it can stop being an assumption:
the day `natAddZero` moves from `proj(PProd)` to certified,
`mini/tests/nat_equations.rs` fails, and that failure is the signal to
instantiate the bridge for real.

**4.5 The collapsed representation folds in without changing any of this.**
The owner has replaced the two-carrier design (`B` with `val : B → ⟦Nat⟧`) with
one set: `⟦Nat⟧` stays exactly what the general inductive translation produces,
and the binary operations become further functions on that same set, with both
views' equations proved about it. Nothing in §1–§3 is affected — the equations
in §2 are about `⟦Nat.add⟧` and `⟦Nat.succ⟧` either way, and §1's `beq`/`ble`
requirement is about what has to be *decided*, not about how numerals are
carried. Two consequences worth recording: `NAT-REPRESENTATION.md` §6.3's
(V1)–(V4) collapse — `val` is the identity, so (V1) and (V2) are vacuous and
(V3)/(V4) become statements relating two operations on one carrier — and §10.4's
worry about the cost of `rep` disappears with `rep`.

---

## 5. Reproducing

* §1: `python3 rename_ops.py <in> <out> <ops…>`, then
  `( ulimit -v 4194304; ./target/release/nanoda_bin cfg.json )` with
  `nat_extension` and `string_extension` on. The renamer and the
  prefix-truncation bisector are 30 lines each and are not checked in; the
  method is stated above in enough detail to rewrite them, and the inputs they
  need are all in `vendor/arena-tests/good/init-prelude.ndjson`.
* §2: `mini/tests/fixtures/nat_char_equations.{lean,ndjson}`, regenerable with
  `scripts/export-fixture.sh nat_char_equations.lean`, and
  `cargo test -p mini --test nat_equations`.
* §3: `~/.elan/toolchains/leanprover--lean4---v4.29.1/src/lean`, at the
  file:line given.

## 6. What this still does not settle

1. **Why `Nat.add`'s nest blocks when `belowFst` does not.** §2.4. The
   `proj(PProd)` label is right about the gap's *name* and has not been shown to
   be right about the clause. Whoever picks this up should start from a
   bisection of the nest, not from `proj_data`.
2. **What `Nat.beq`/`Nat.ble` cost on the binary representation, measured.**
   §1.3 says the demanded conversions are comparisons at `2⁶⁴`;
   `NAT-REPRESENTATION.md` §6.4 predicts Θ(bits) for them. Nobody has counted
   the kernel inferences.
3. **Whether any `Nat.rec` in `init-prelude` iterates over a large literal.**
   Still open, and `NAT-REPRESENTATION.md` §10.2 is still the statement of it.
   §1 narrows it: the two fatal sites are `decide`-shaped, so the *known*
   demand is comparison, not iteration.
4. **`div`/`mod`'s characterisation.** No equation exists to gate on. The
   `Acc.rec`/fuel fixpoint equation is the shape, `checker/src/tests/natlit.rs:35`
   already pins the bignum side, and nothing has been designed.
