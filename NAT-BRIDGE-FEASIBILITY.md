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

### 2.3 Certification — **32 of 38 pairs**, and the two named causes are closed

*(Rewritten. This section read "**no**, for all seventeen" and gave the run
below at `constEv = 14`. Both causes it names were general defects in mini's
projection handling that `Nat` merely exposed; `68ed247` and `3071105` close
them, each with a `Nat`-free minimal reproduction in
`mini/tests/fixtures/`. The measurement is redone here rather than appended.)*

```
$ ./target/debug/mini --verbose mini/tests/fixtures/nat_char_equations.ndjson
nat_char_equations.ndjson  accept  44 declarations
                           uncertified: 6 const typings, 32 conversions
evidence  pairs=38  typeEv=38  constEv=32  unsealed=0
          library-gap=5  threading-incompleteness=1
          waiting:proj(PProd)=5  waiting:no-endpoint=1
                                                                   exit = 4
```

Before those two commits it was

```
evidence  pairs=38  typeEv=23  constEv=14  unsealed=0
          waiting:proj(PProd)=12  waiting:no-endpoint=12
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

### 2.4 Where it stopped, and why the trail said otherwise

*(Rewritten. This section reported the blocker trail as naming
`app_evidence` and `lam_evidence`, observed that both are forwarding sites, and
concluded that the origin "is not in the trail because it is an `Err(Gap)`
rather than an `Ev::missing`". The second half is true and is only half the
reason; the first half had a cause nobody had looked for. Both are fixed in
`341ff47` and the census now names the origin directly.)*

The reason string here has to be checked, not trusted — the census is the
instrument, and the *release* binary's census is misleading, because
`blocker::source_line` reads the current tree while the recorded `file:line`
comes from whatever source the binary was compiled from. Use the debug binary.

**Two instrument defects, and between them they hid the answer from three
seats.**

* **`TRAIL_CAP` was 64, and the trail evicts from the front.** Mints arrive
  innermost-first, so the origin is the *oldest* entry and a pair that mints
  more than the cap loses exactly it. `Nat.add` minted exactly 64 — the trail
  was full, and the eviction was silent. It is 4096 now.
* **An `Err(Gap)` was never recorded at all.** `Ev::missing` was the only mint
  the trail saw, so `proj_data::typing` and `proj_prop::typing` were invisible
  in it and the gap reached the report through whichever caller turned it into
  an `Ev`. `mini::gap!` records at the `?` itself — a macro, because these
  routes mint through a per-function `miss` closure and `#[track_caller]` would
  name the closure body.

With both, the same `Nat.add` run reports

```
  gave up at
    mini/src/proj_prop.rs:467
      betas.push((set, field_in_u0(c, &e).ok_or_else(|| miss!())?));
    mini/src/proj_data.rs:425
      let (carrier, spine_eq) = ip.beta_spine(&former, &ps, &param_mems).ok_or_else(|| miss!())?;
```

The first is a correct decline — `PProd`'s field is data, not a `Prop`, so the
`Prop` route says no and the `first_reason` rule passes to `proj_data`. The
second is the defect, and it is where the answer to §6.1 was.

**`beta_spine`'s premise did not match its domain**, and printing the two said
why in one line:

```
concl = … ∈ app(f94(⟦Sort 1⟧, ⟦Nat.{}⟧), ⟨·⟩)
want  = … ∈ ⟦Sort 1⟧
```

`Nat.below motive (Nat.succ k)` reduces to `PProd (motive k) (Nat.rec … k)`,
and that second parameter's inferred type is `motive k` — mini substitutes into
a recursor's `motive major` rather than reducing — where `PProd`'s declaration
says `Sort 1`. Defeq, not identical, and `beta_spine` compares on the nose.
Behind it sat a second, independent cause: the route read the structure's
identity off the acceptance-only `c.whnf(&te.ty)` and then used the
**unreduced** typing as the major premise, so the equation `beta_spine`
produced started at the `PProd` spine while the membership in hand was still
about `Nat.below …`.

**Neither is about `PProd`, `below`, or `Nat`.**
`mini/tests/fixtures/proj_reduced_carrier.lean` reproduces both with a Peano
type it declares itself and no occurrence of the name `Nat` anywhere in the
export — a fact its test checks rather than claims.

A third defect sat under those two and is the reason the *equations* rather
than the operations stayed blocked: `whnf`'s `Expr::Proj` arm reduced the
projection's subject with the acceptance-only `self.whnf(s)` and then required
`s2 == s`. `proj_data::iota`'s header called that decline unreachable, on the
evidence that `093_projRed` satisfies the guard and no corpus member exercises
it. Every projection Lean's structural-recursion compiler emits takes it:
`Nat.brecOn` is `(Nat.brecOn.go motive t F).1`.
`mini/tests/fixtures/proj_reduced_subject.lean` is its `Nat`-free reproduction.

### 2.4.1 `sub`, `mul` and `pow` are blocked twice over

The `no-endpoint` label masks an *earlier* blocker. Isolating `pow`:

```
BLOCKED  Nat.pow.match_1  σ = u_1 := 1  no-endpoint  [Threading]
  ty  (∀ _:(∀ _:Nat, Sort 1),
       (∀ _:Nat,
        (∀ _:(∀ _:Unit, (#2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))), …)))
```

`Nat.pow.match_1` — which `Nat.pred` and hence `Nat.sub` also use — carries
`OfNat.ofNat Nat 0 (instOfNatNat 0)` in its motive. That is a projection out of
the `OfNat` class structure, and it is **still open**: it is the one remaining
`no-endpoint` in the run above, and it is a different shape from the three
closed here.

### 2.5 The eight in scope — are they uniform?

**Yes, and that is a correction.** This section used to say "three groups, not
one" and split the operations by *gap label*: `add`/`beq`/`ble` on
`proj(PProd)`, and `sub`/`mul`/`pow` on a "different and earlier"
`no-endpoint` whose real content was `Nat.pow.match_1`'s
`OfNat.ofNat Nat 0 (instOfNatNat 0)`. **The split was an artefact of two
projection defects, and one change closed both.** `OfNat.ofNat` and
`instOfNatNat` certify; so do `Nat.pow.match_1`, `Nat.mul.match_1`,
`Nat.pred`, and every one of the eight operations' own values and typings.

The real split runs the other way — **across** the operations, between an
operation's *base* equation and its *step* equation:

| operation | value + typing | base equation | step equation |
| --- | --- | --- | --- |
| `add` | ✓ | `natAddZero` ✓ | `natAddSucc` — `proj(PProd)` |
| `sub` | ✓ (and `Nat.pred` ✓) | `natSubZero` ✓ | `natSubSucc` — `no-endpoint` |
| `mul` | ✓ | `natMulZero` ✓ | `natMulSucc` — `proj(PProd)` |
| `pow` | ✓ | `natPowZero` ✓ | `natPowSucc` — `proj(PProd)` |
| `beq` | ✓ | `natBeqZZ` ✓, `natBeqZS` ✓, `natBeqSZ` ✓ | `natBeqSS` — `proj(PProd)` |
| `ble` | ✓ | `natBleZ` ✓, `natBleSZ` ✓ | `natBleSS` — `proj(PProd)` |
| `div` | — | **no such equation exists** | — |
| `mod` | — | **no such equation exists** | — |

Eleven of the seventeen certify. The six that do not are exactly the six whose
left-hand side reduces through the nest's **step** case, where the projection
`f.1` is *applied* to an argument rather than merely typed. `natSubSucc` is the
only one still carrying a different label, and it is no longer the numeral
wrapper: `Nat.sub` and `Nat.pred` both certify.

**For the bridge this means the pair is one short, not two.** §4.4's tripwire
was written to fire "the day `natAddZero` moves from `proj(PProd)` to
certified". It has fired. `natAddSucc` has not.

`div` and `mod` are unchanged and remain a different problem entirely — their
characterisation is `div_unique`-shaped (`Nat.div_eq`, §3), proved by induction
on the fuel rather than by `rfl` — and §1 says they are not on
`init-prelude`'s critical path anyway.

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

**4.4 Until §2.5's *step* equations close, the equations are hypotheses.**
`NAT-REPRESENTATION.md` §8's fallback stands and is now the near-term answer:
thread the equations as kernel hypotheses, discharged per file or reported in
the ledger as a named assumption. It decouples the representation and the
arithmetic from the equation derivations, and it is still strictly better than
name-keyed trust — the assumption is *stated*, in the ledger, per file. The
fixture and its test are what tell us when it can stop being an assumption, and
**half of that signal has now fired**: `natAddZero` certifies and
`mini/tests/nat_equations.rs` was rewritten around it. `natAddSucc` does not,
so the bridge still cannot be instantiated — a uniqueness theorem needs both
equations, and §2.5 says the missing half is the *step* case at every one of
the six operations rather than anything about `add`.

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

1. **~~Why `Nat.add`'s nest blocks when `belowFst` does not.~~ Answered —
   §2.4.** Three defects, none of them about `Nat`, `PProd` or `below`, each
   with a `Nat`-free minimal reproduction in `mini/tests/fixtures/`. The advice
   this item carried — *"start from a bisection of the nest, not from
   `proj_data`"* — was wrong twice over: two of the three **are** in
   `proj_data`, and what actually found them was repairing `blocker`'s trail so
   that it named the origin instead of a forwarding site.

   What replaces it is the **cost**: certifying a `brecOn` nest is about a
   hundred times more work than not certifying one, and no term-keyed memo can
   fix it because every binder entry mints fresh kernel variables.
   `MINI-HANDOFF.md` §40 has the three memos that were tried and what each
   measured.
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
