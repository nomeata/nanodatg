# Efficient `Nat` without extending the theory — research and a recommendation

**Status: the survey (§§1–5, §§8–10) stands; §6's recommendation was
superseded and §6/§7 are corrected below.** The survey of Lean, Coq and
Isabelle is accurate and was not re-opened. What changed is the design it
recommended: §6 called for a **second inductive type `B` with a valuation map
`val : B → ⟦Nat⟧`**, and that was rejected — twice — in favour of **one set
carrying both views**. `derived/src/nat/` is the implementation, and §6.0 below
records what was actually built and which of this document's predictions it
refuted. Do not build the `B`/`val` design; the paragraphs describing it are
kept only because §9's comparison to Coq and Isabelle is stated in their terms.

It also answers a question `QUESTIONS.md` recorded as deferred (*"the
choice between a primitive sort and numerals-as-defined-constants-plus-bignum-rule-schemas
is deferred … worth revisiting **before** any milestone-4 code is written"*), and
answers it against the option `MEASUREMENTS.md:55–60` and `README.md:288`
assumed: **no primitive `ℕ`, no kernel bignum rules, no new axioms.**

Everything below that is a number was measured in this repository or read out of
a named source file. Where I could not settle something I say so, in §10.

---

## 1. What `mini` does with `Nat` today — measured

### 1.1 The literal clause

`mini` expands a nat literal to a unary `succ`-tower and refuses anything over
ten.

* `mini/src/kernel.rs:1836` — `nat_unfold(n)`: `n > 10` → `Err("The mini kernel
  does not support nat literals larger than 10")`; otherwise `Nat.zero` or
  `Nat.succ (natLit (n-1))`.
* `mini/src/kernel.rs:1808` — `infer_type` on `Expr::NatLit(n)` types it `Nat`
  and infers the *expansion*.
* `mini/src/kernel.rs:1254` — `whnf`'s `NatLit` branch peels one `succ` and
  emits **no** `step!`: `⟦natLit n⟧` is *defined* as the interpretation of the
  expansion, so the unfolding is reflexivity at the term level.
* `mini/src/convert.rs:641` — the same guard at load time, mirroring mini-lean's
  `parseExprNatLit`. The counters `facts.nat_lits` / `facts.max_nat_lit` are
  bumped here, which is why they appear in the `--verbose` facts row.

There is **no** arithmetic clause at all. `Nat.add`, `Nat.beq`, … have no fast
path; they would reduce through `Nat.rec` like any other definition.

### 1.2 What that costs, on the corpus

`good/tutorial`, 91 exports, run individually with `--verbose`:

| | |
|---|---|
| accept / decline / reject | 89 / 2 / 0 |
| `pairs` = `constEv` | **218 / 218** |
| exports mentioning the name `Nat` at all | **2** (`097_aNatLit`, `098_natLitEq`) |
| `elim Nat computed=true oracle=true` rows | **2**, in those same two files |
| `natLit` clause occurrences | **3** total |
| largest literal | **3** (`098_natLitEq`) |

The other Peano-shaped exports (`027`–`029`, `067`, `075`) declare their own `N`,
not Lean's `Nat`.

**This corrects an expectation in the brief.** `Nat` is *not* used throughout the
corpus `mini` is green on. Corpus-green at `218/218` bounds essentially nothing
about a new `Nat` path: it exercises `⟦Nat⟧`, `⟦Nat.zero⟧`, `⟦Nat.succ⟧`,
`⟦Nat.rec.{0}⟧`, `⟦Nat.rec.{1}⟧` and the literals `0` and `3` — no arithmetic,
no ι firing on a literal above 3, no `Nat.add`. It remains a necessary
regression (a change that broke it would be broken) but it is nowhere near
sufficient. **The real regression is `init-prelude`.**

### 1.3 `init-prelude` — `mini` cannot load it

```
$ ( ulimit -v 4194304; ./target/release/mini --verbose vendor/arena-tests/good/init-prelude.ndjson )
init-prelude.ndjson	decline	declined: The mini kernel does not support nat literals larger than 10
facts	declars=0	natLits=0	maxNatLit=0	strLits=0	scheduledPairs=0 …
	real 0m0.037s   exit=2
```

No memory risk: the decline happens inside `convert::load`, at the first
offending literal, before any interpretation. **The facts row is therefore not
usable evidence about the file** — `natLits=0` here means "conversion aborted",
not "no literals". The 4 GB cap was never approached.

So the honest statement of where the project is: **the nat-literal work is not a
performance item, it is the load-time gate that keeps `init-prelude` out.**

#### 1.3.1 The rows the aborted conversion was hiding — measured

The paragraph above says the facts row is not usable evidence. Here is the row
that *is*, obtained by lifting `convert.rs`'s guard (and only that guard —
`kernel::nat_unfold`'s second line of defence was left at 10, so no literal can
expand and no unary blow-up is reachable):

```
$ ( ulimit -v 4194304; timeout 600 ./target/release/mini --no-modelgen \
      --nested --mutual --verbose good/init-prelude.ndjson )
init-prelude.ndjson	reject	UInt32
The mini kernel does not support nat literals larger than 10
… while checking type of constructor UInt32.ofBitVec
facts	declars=2059	natLits=35	maxNatLit=18446744073709551615	strLits=25	scheduledPairs=3861
clauses	interpreted=212737	remaining=243	… natLit=3103	strLit=32
```

Three things this settles.

* **The file loads.** `2059` declarations and `3861` scheduled pairs reach the
  checker, against `declars=0` unfiltered and the `1459`/`3078` that
  `scripts/nat-reach.py --write` bought by *deleting* the literal-bearing
  closure. Nothing else in `convert::load` refuses the whole file.
* **`--nested` and `--mutual` are both needed to get there, and nesting is a
  load-time decline, not an interpretation gap.** With the literal guard lifted
  and those flags off, the next refusal is
  `declined: Nested inductive Lean.Syntax not supported` at `convert.rs:489` —
  again before any typechecking. The literal guard was hiding it.
* **The wall after the load gate is `kernel::nat_unfold`'s own copy of the
  guard**, and it is reached while checking a *type*, not a value:
  `UInt32.ofBitVec`, whose blocking literal is the `32` in `BitVec 32`. So the
  two guards are not redundant and the load-time one is not the last thing to
  remove.

#### 1.3.2 Climbing the kernel cap — where unary actually dies

The same run with `kernel::nat_unfold`'s cap raised, each in
`( ulimit -v 4194304; timeout … )`. This is the measurement that says what the
binary literal clause is buying, and it does not say what one expects:

| kernel cap | first literal it must expand | outcome |
|---|---|---|
| 10 (shipped) | — | `reject UInt32.ofBitVec`, ~1 s |
| 11 | 32 | `reject UInt32.ofBitVec`, ~1 s |
| 100 | 55296 | `reject Nat.isValidChar`, ~1 s |
| 1000 | 55296 | `reject Nat.isValidChar`, ~1 s |
| 100000 | 55296 | **no verdict in 600 s**; peak RSS 166 MB |

**Unary is a cost wall long before it is a memory wall.** A 55296-deep
`Nat.succ` tower did not come near the 4 GB cap — 166 MB, two orders of
magnitude under it — and still could not be typed in ten minutes, because
`infer_type` on `natLit n` recurses `n` levels and each level is a full
interpretation. The 3 000 s / 14.8 GB observation recorded elsewhere for this
file is about the *rest* of it; the literal path on its own dies of time.

That matters for how step 3 is briefed. `whnf` peeling one `succ` off a
literal is cheap and always will be; what is not survivable is anything that
peels `n` of them, and at `n = 55296` — a *small* literal by this file's
standards, four orders of magnitude under `UInt32.size` — the failure is
already total. So the accelerated operations are not an optimisation over the
successor path, they are the only path, and a fast path that silently falls
back to `succ` is indistinguishable from having no clause at all.

**And `maxNatLit` is wrong in that row, which is a defect and not a rounding.**
The file's largest literal is `UInt64.size` = 2⁶⁴ = `18446744073709551616`;
`facts` reports `18446744073709551615`. `mini`'s `Expr::NatLit` is a `u64` and
both parse sites spelled the conversion `.parse().unwrap_or(u64::MAX)`, so 2⁶⁴
— **the value this whole exercise is named after** — silently became 2⁶⁴ − 1.
It was harmless only because every value above ten is declined on the next
line. `convert::literal_value` now declines it by name instead, ahead of the
guard being lifted and independently of it; §1.4's table is otherwise
unchanged and its `2⁶⁴` entry is the correct one.

### 1.4 What `init-prelude` actually contains — measured statically

35 literals; the distribution over `init-prelude` ∪ `grind-ring-5`:

```
0..18 (all), 20,22,…,64, 96..128, 192..256, 512, 1000000, 1114112,
2047, 4096, 55296, 57343, 65535, 65536, 262144, 100000000,
4294967296 (2³²), 18446744073709551616 (2⁶⁴)
```

`1000000` occurs in `perf/grind-ring-5.ndjson`; `2⁶⁴` in `init-prelude.ndjson`.

Which declarations hold the large ones (from a JSON walk of the export's
expression DAG):

| declaration | literals |
|---|---|
| `UInt64.size` | 18446744073709551616 |
| `USize.size_pos.match_1_1` | 4294967296, 18446744073709551616 |
| `UInt32.size` | 4294967296 |
| `Nat.isValidChar`, `Char.ofNat`, `isValidChar_UInt32.match_1_1` | 55296, 57343, 1114112 |
| `String.utf8EncodeChar` | 127…65535, 262144 |
| `Char.utf8Size` | 127, 2047, 65535 |
| `UInt16.size` / `UInt8.size` | 65536 / 256 |
| `Lean.defaultMaxRecDepth` | 512 |
| `Lean.Name.hash` | 17, 1723 |

317 of 1899 declarations contain a literal somewhere.

Which of Lean's accelerated operations are even *named* in `init-prelude`
(from the file's own name table, 156 `Nat.*` names): **`add`, `sub`, `mul`,
`pow`, `div`, `mod`, `beq`, `ble`** — plus `decEq`/`decLe`/`decLt`/`pred`/`lt`/`le`
which are not kernel-accelerated. **Not named at all: `gcd`, `land`, `lor`,
`xor`, `shiftLeft`, `shiftRight`.** That bounds step 3: six of the fourteen
binary operations are not needed to unblock this file.

`MEASUREMENTS.md:31` records **340 nat-literal-arithmetic reduction steps** on
`init-prelude` (measured on upstream nanoda with `stepcount`), against 43,463
total reduction steps — under 1%.

*What I could not measure:* the per-operation breakdown, and the argument sizes
at which each fires. `stepcount` has a single `Kind::NatLit` counter
(`checker/src/tc.rs:637`), and getting a breakdown means instrumenting
`checker/`, which this task may not touch. `mini` cannot supply it because it
cannot load the file. So "which ops fire and at what sizes" is **inferred from
the names and literals present, not observed**.

### 1.5 For contrast: what `checker/` already does

`checker/` (untrusted, no certificates) implements Lean's list in full —
`checker/src/tc.rs:563–581`, `NatBinOp::{Add,Sub,Mul,Pow,Div,Mod,Gcd,LAnd,LOr,XOr,Shl,Shr,Beq,Ble}`
over `BigUint`, plus `Nat.succ` at `tc.rs:598`, gated on
`config.nat_extension`. So the arithmetic *semantics* the project must reproduce
is already written down and tested (`checker/src/tests/natlit.rs`), on a bignum
representation, with no proof. The chain's job is to produce the same answers
with certificates.

---

## 2. Lean's accelerated list — verified against source

Read from `leanprover/lean4` at commit **`4a37393b74d177d5e32f06cfd097ff6eb9f507b8`**
(2026-08-06, `master`). **Fifteen operations, no more.**

`src/kernel/type_checker.cpp`: `reduce_nat` (line **639**) dispatching to
`reduce_bin_nat_op<F>` (606), `reduce_bin_nat_pred<F>` (629) and `reduce_pow`
(618). Declared `src/kernel/type_checker.h:109–112`. Called from `whnf`
(line 700, unconditionally) and from `lazy_delta_reduction` (1009/1011, guarded
by `(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce`).

| Lean name | line | kind | result |
|---|---|---|---|
| `Nat.succ` | 643 | unary, inlined in `reduce_nat` | Nat |
| `Nat.add` | 652 | binary | Nat |
| `Nat.sub` | 653 | binary | Nat |
| `Nat.mul` | 654 | binary | Nat |
| `Nat.pow` | 655 | binary, **guarded** | Nat |
| `Nat.gcd` | 656 | binary | Nat |
| `Nat.mod` | 657 | binary | Nat |
| `Nat.div` | 658 | binary | Nat |
| `Nat.beq` | 659 | binary **pred** | Bool |
| `Nat.ble` | 660 | binary **pred** | Bool |
| `Nat.land` | 661 | binary | Nat |
| `Nat.lor` | 662 | binary | Nat |
| `Nat.xor` | 663 | binary | Nat |
| `Nat.shiftLeft` | 664 | binary | Nat |
| `Nat.shiftRight` | 665 | binary | Nat |

**`Nat.log2` is not in the list** — the recollection in the brief is wrong on
that one point. Also absent despite having `@[extern]` in the prelude:
`Nat.pred`, `Nat.decEq`, `Nat.decLe`, `Nat.decLt`, `Nat.blt`, `Nat.modCore`.

Four further facts that matter to us:

* **Matched by name only.** `initialize_type_checker` (`type_checker.cpp:1228–1243`)
  builds `mk_constant({"Nat","add"})` etc.; the kernel never checks that the
  environment's `Nat.add` *is* the prelude's. The fast path is a **trusted
  axiom about those names**. We cannot copy that, and §7 says what to do
  instead.
* **`Nat.zero` counts as a literal.** `type_checker.cpp:599–604`,
  `is_nat_lit_ext` / `get_nat_val`.
* **One guard only, on `pow`.** `#define ReducePowMaxExp 1<<24`
  (`type_checker.cpp:616`); above 2²⁴ the kernel silently falls back to
  unfolding. `Meta`'s mirror is far tighter — `exponentiation.threshold`
  default **256** (`src/Lean/Util/SafeExponentiation.lean:15–22`).
* **`Nat.rec` on a literal peels exactly one layer.**
  `src/kernel/inductive.h:77–104` (`inductive_reduce_rec`) calls
  `nat_lit_to_constructor` (`src/kernel/inductive.cpp:1267–1274`), which turns
  `100` into `Nat.succ (.lit 99)` — the predecessor stays a literal, so no
  100-deep tower is ever built. And `is_def_eq_offset`
  (`type_checker.cpp:973–999`) strips a `succ` off both sides simultaneously,
  absorbing the succ↔literal direction without materialising it.

On the definitions behind the fast path: `Nat.beq`/`Nat.ble`
(`src/Init/Prelude.lean:1810`, `1880`) are ordinary structural recursions and
would reduce without help, just in O(n) steps. `Nat.gcd`
(`src/Init/Data/Nat/Gcd.lean:34–41`) is **well-founded** — its own docstring
says the Euclidean definition "is overridden in both the kernel and the compiler
… The definition provided here is the logical model." `Nat.div`/`Nat.modCore`
are fuel-based structural definitions marked `irreducible` (an elaborator
notion the kernel ignores). `Nat.land`/`lor`/`xor` go through `Nat.bitwise`,
which is well-founded. §8 says why that split matters for the uniqueness bridge.

---

## 3. Rocq/Coq — and how the slow definition is connected to the fast one

Sources: `github.com/coq/coq` (kernel, `theories/Corelib`) and
`github.com/rocq-prover/stdlib` (`theories/PArith`, `NArith`, `Numbers`).

### 3.1 The representation

`Corelib/Numbers/BinNums.v:21–47`:

```coq
Inductive positive := xI : positive -> positive | xO : positive -> positive | xH : positive.
Inductive N := N0 : N | Npos : positive -> N.
```

The **outermost constructor is the least significant bit**; `xH` is the always-1
top bit. No zero and no leading zeros, so the representation is **canonical** —
which is what makes `eqb` structural, `compare` a single pass, and equality
decidable. `N` adds a separate zero.

`succ`, `add`/`add_carry` (a *mutual* `Fixpoint` pair carrying the carry in the
control state rather than as data), `mul`, `compare_cont` (an accumulator so
comparison is one pass despite LSB-first), and `sub_mask` (three-valued, via an
auxiliary `mask` inductive) all live in `Corelib/BinNums/PosDef.v`.

### 3.2 The connection — and it is *not* what one expects

Coq does **not** define `add` by a recursor and then optimise. It defines `add`
directly on the binary shape, and then **proves the Peano equations as
theorems**:

* `Pos.add_1_l : 1 + p = succ p` — `now destruct p`.
* `Pos.add_succ_l : succ p + q = succ (p + q)` — binary structural induction
  (`PArith/BinPos.v:169–200`).

From that moment `add` is used only through its equations. The morphism to
unary `nat` then falls out in three lines (`PArith/Pnat.v:27–61`):

```coq
Theorem inj_add p q : to_nat (p + q) = to_nat p + to_nat q.
Proof. revert q. induction p using peano_ind; intros q.
       - now rewrite add_1_l, inj_succ.
       - now rewrite add_succ_l, !inj_succ, IHp. Qed.
```

**This is exactly the step-4 bridge of our chain, already written down**: an
efficient binary `add` shown to satisfy the two Peano equations, from which
agreement with the slow one follows by induction. The stdlib's fully explicit
version of it is `Numbers/Natural/Abstract/NDefOps.v`:

```coq
Definition def_add (x y : N.t) := recursion y (fun _ => S) x.
Theorem def_add_add : forall n m, n +++ m == n + m.
Proof. intros n m; induct n.
       - now rewrite def_add_0_l, add_0_l.
       - intros n H. now rewrite def_add_succ_l, add_succ_l, H. Qed.
```

Two lines, using **only** the abstract equations `add_0_l` / `add_succ_l`, never
the concrete binary definition. (Deprecated since 8.20 — because Coq decided it
wasn't pulling its weight, not because it was wrong.)

### 3.3 `Pos.peano_rect` — the key device, and its cost

`PArith/BinPos.v:317–341`, due to Daniel Schepler:

```coq
Fixpoint peano_rect (P:positive->Type) (a:P 1)
  (f: forall p, P p -> P (succ p)) (p:positive) : P p :=
  let f2 := peano_rect (fun p => P (p~0)) (f _ a)
              (fun p (x:P (p~0)) => f _ (f _ x))
  in match p with q~1 => f _ (f2 q) | q~0 => f2 q | 1 => a end.

Theorem peano_rect_base P a f : peano_rect P a f 1 = a.
Proof. trivial. Qed.
Theorem peano_rect_succ P a f p : peano_rect P a f (succ p) = f _ (peano_rect P a f p).
Proof. revert P a f. induction p as [p IHp|p IHp|]; trivial. intros. simpl. now rewrite IHp. Qed.
```

Two facts to take away, both load-bearing for us.

1. **Even in Coq the successor ι rule is *propositional*, not definitional.**
   The `xO` and `xH` cases hold by conversion; the `xI` case genuinely needs the
   induction hypothesis *at a different motive* — hence `revert P a f`. Nobody
   gets a Peano ι rule on a binary carrier for free.
2. **Running it is linear in the value.** A faithful transcription of the
   fixpoint (with the `f2` closure shared) gives, for `p`: exactly **`p−1`**
   applications of `f` and **`bits(p)`** unfoldings of `peano_rect`. The
   doubling trick buys a *term* of size O(log p) with sharing, not O(log p)
   work — and it cannot, because the value of type `P p` *is* `f` applied `p−1`
   times to `a` when `f` is opaque.

   The stdlib knows this. `Numbers/Natural/Binary/NBinary.v:29–49` carries a
   commented-out benchmark: `log 500000` (generic recursion) 11 sec vs
   `binlog 500000` (recursion on the notation) 0 sec. **Nothing in the stdlib
   defines a computationally-used function by `Pos.peano_rect`.**

   Coq therefore keeps *two* recursors on `N`: `binary_rect`
   (`NArith/BinNat.v:103–115`, literally `positive_rect`, O(bits), definitional
   ι, used for computation) and `peano_rect` (O(value), propositional ι, used
   for induction) — related by proved equations.

`PeanoView` (`BinPos.v:358–428`) is the earlier McBride-style device: a
proof-relevant certificate `PeanoView p` that `p` is `succ`-reachable from `1`,
built by a doubling fixpoint, consumed by a trivially structural iterator, with
`PeanoViewUnique` (uniqueness of the certificate, obtained from decidable
equality on `positive` ⇒ UIP) and `peano_equiv` reconciling it with
`peano_rect`.

### 3.4 The abstract layer, and what uniqueness Coq actually has

`Numbers/NatInt/NZAxioms.v` + `Numbers/Natural/Abstract/NAxioms.v` give
`NAxiomsSig`: `zero`, `succ`, `pred_succ`, **`bi_induction`**, and each
operation pinned by exactly two equations (`add_0_l`/`add_succ_l`,
`mul_0_l`/`mul_succ_l`, `sub_0_r`/`sub_succ_r`, …). **There is no recursor in
it.** The optional `NAxiomsRec` adds `recursion` with `recursion_0` (Leibniz
`=`) and `recursion_succ` (only up to a caller-supplied setoid relation, with
`Proper` side conditions).

`nat` instantiates it (`Arith/PeanoNat.v:47–82`, `recursion := nat_rect`), and so
does `N` (`NArith/BinNat.v:31–190`, `recursion := peano_rect`,
`recursion_succ` by `peano_rect_succ`).

**There is no general "the recursor is unique" lemma in the stdlib.** Every
`*_unique` is a characterisation of a *specific* operation by its spec
(`div_unique`, `mod_unique`, `gcd_unique`, …). What exists instead is
per-operation uniqueness (`NDefOps`, §3.2), uniqueness of the *certificate*
(`PeanoViewUnique`), and uniqueness of the *model* up to isomorphism
(`Numbers/Natural/Abstract/NIso.v`, `natural_isomorphism := N1.recursion N2.zero (fun _ => N2.succ)`,
`hom_nat_iso`, `iso_nat_iso` — the initial-algebra argument, needing the
recursor to *build* the map and induction to invert it).

### 3.5 Primitive integers — exactly what is trusted

`Corelib/Numbers/Cyclic/Int63/PrimInt63.v` declares `Primitive int := #int63_type`
and ~35 operators; their behaviour is ~25 **axioms** in `Uint63Axioms.v`
(`add_spec : to_Z (add x y) = (to_Z x + to_Z y) mod wB`, …). The documentation
is blunt (`doc/sphinx/language/core/primitive.rst:39`): *"These primitive
declarations are regular axioms. As such, they must be trusted and are listed by
`Print Assumptions`."* The TCB grows by the retroknowledge table
(`kernel/retroknowledge.mli`), the reduction rules (`kernel/cPrimitives.ml`,
`primred.ml`, `uint63_63.ml`), and — for `vm_compute`/`native_compute` — a
bytecode VM and the OCaml compiler, both re-run *by the kernel* at final
checking.

**This whole branch is off the table for us**, and that is the constraint the
chain exists under.

### 3.6 Does Coq's kernel convert a `nat` literal fast? No.

Three independent confirmations:

1. The retroknowledge record has entries for `int63`, `float64`, `string`,
   `array`, `bool`, `carry`, `pair`, `cmp` — **no `nat`, no `positive`, no `N`,
   no `Z`.**
2. `positive`/`N`/`Z` get *zero* kernel help. They are fast purely because the
   *terms* are O(log n) and the *algorithms* are O(log n). **This is the single
   most encouraging fact for this project.**
3. The parser gives up: `Corelib/Init/Nat.v:435–436` declares the `nat` number
   notation `(abstract after 5000)`, so a literal above 5000 elaborates to an
   unreduced `Nat.of_num_uint 12345` with a warning, because walking the tower
   overflows OCaml's stack. **`nat` cannot even be written down past ~5000.**

---

## 4. Isabelle/HOL — and what is proved to relate numerals to `0`/`Suc`

Sources: the Isabelle/dev mirror at tip `75ef739` (2026-08-05), `src/HOL/`.

### 4.1 `Num.num` and `numeral`

`src/HOL/Num.thy:14`: `datatype num = One | Bit0 num | Bit1 num`. Outermost
constructor = least significant bit, `One` = the leading 1. No zero
constructor, for two reasons: canonicity (no leading zeros ⇒ unique
representation, and `num_eq_iff : x = y ⟷ nat_of_num x = nat_of_num y` is
*proved*, `Num.thy:51–61`), and the weakest possible carrier — see below.

`Num.thy:252–300`:

```isabelle
class numeral = one + semigroup_add
begin
primrec numeral :: "num ⇒ 'a" where
    numeral_One:  "numeral One = 1"
  | numeral_Bit0: "numeral (Bit0 n) = numeral n + numeral n"
  | numeral_Bit1: "numeral (Bit1 n) = numeral n + numeral n + 1"
```

Note the class: `one + semigroup_add`. **`num` is the datatype; `numeral` is an
interpretation of it into any structure with `1` and an associative `+`.** `nat`
is one such structure. Numerals are *not* a second constructor set for `nat`.

`Num.thy:63–82` gives a **second induction principle on the same type**:

```isabelle
lemma num_induct [case_names One inc]: "P One ⟹ (⋀x. P x ⟹ P (inc x)) ⟹ P x"
```

with the file's own comment: *"From now on, there are two possible models for
`num`: as positive naturals (rule `num_induct`) and as digit representation
(rules `num.induct`, `num.cases`)."* This dual view is the central proof device
— computation rules are stated on the digit view, morphism laws are proved by
the Peano view.

### 4.2 The bridge, and the `Suc` bridge

The bridge to `nat` is one theorem, `Num.thy:590–597`:

```isabelle
lemma nat_of_num_numeral [code_abbrev]: "nat_of_num = numeral"
```

— the polymorphic `numeral` at `'a = nat` *is* the concrete `primrec
nat_of_num`, proved by a 3-case induction on `num`. That single theorem
justifies essentially every code equation downstream.

The `Suc` bridge is `Num.thy:1065–1099`:

```isabelle
lemma Suc_numeral [simp]: "Suc (numeral n) = numeral (n + One)"
definition pred_numeral k = numeral k - 1
lemma numeral_eq_Suc: "numeral k = Suc (pred_numeral k)"
lemma pred_numeral_simps [simp]:
    "pred_numeral One = 0"  "pred_numeral (Bit0 k) = numeral (BitM k)"
    "pred_numeral (Bit1 k) = numeral (Bit0 k)"
```

`BitM n = 2n − 1` (`Num.thy:200–204`) is the predecessor at the bit level, so
**peeling one `Suc` off a numeral costs O(bit-width), not O(value)**. It is used
for *case analysis*, never for computation: `case_nat_numeral`,
`rec_nat_numeral`, `less_Suc_numeral`, `diff_Suc_numeral` all peel exactly one
`Suc` (`Num.thy:1111–1162`). Full expansion (`eval_nat_numeral`) is **not** a
default simp rule and is opt-in, because it is O(value).

### 4.3 How the arithmetic simp rules are justified — three layers

**Layer 1, digit arithmetic in `num`, defined by transport.** `Num.thy:96–98`:

```isabelle
instantiation num :: {plus,times,linorder}
  definition "m + n = num_of_nat (nat_of_num m + nat_of_num n)"
  definition "m * n = num_of_nat (nat_of_num m * nat_of_num n)"
```

then `nat_of_num_add` (`Num.thy:109`), then the nine digit equations
(`Num.thy:117–136`) each follow **in one line** by `simp add: num_eq_iff
nat_of_num_add`:

```isabelle
lemma add_num_simps [simp, code]:
  "One + One = Bit0 One"        "One + Bit0 n = Bit1 n"    "One + Bit1 n = Bit0 (n + One)"
  "Bit0 m + One = Bit1 m"       "Bit0 m + Bit0 n = Bit0 (m + n)"  "Bit0 m + Bit1 n = Bit1 (m + n)"
  "Bit1 m + One = Bit0 (m + One)"  "Bit1 m + Bit0 n = Bit1 (m + n)"
  "Bit1 m + Bit1 n = Bit0 (m + n + One)"
```

**This is our step-4 bridge run backwards**: define the fast operation *as the
spec composed with the isomorphism*, then **derive** the fast equations. No
termination argument, no well-founded recursion, no ι rule needed. It is the
single most transferable idea in either system.

**Layer 2, transfer into the algebra**, `Num.thy:352–363`, in the class
`one + semigroup_add`:

```isabelle
lemma numeral_add: "numeral (m + n) = numeral m + numeral n"
  by (induct n rule: num_induct) (simp_all only: numeral_One add_One add_inc numeral_inc add.assoc)
```

Proved by the **Peano** view (`num_induct`), not the digit view — which is why
it needs no zero and no commutativity.

**Layer 3, inheritance at `nat`, for free** (`Num.thy:1259–1267`): nothing is
re-proved. `numeral_plus_numeral` is a theorem with a schematic type variable
`'a :: numeral`; using it at `nat` is one kernel `Thm.instantiate` whose sort
constraint is discharged by the class-instance certificate. Cost O(1). §6 says
why this layer does **not** transfer to us.

**How `2 + 3 = 5` is actually proved** — not by a simproc, by three rewrites:
`numeral_plus_numeral` ⟹ `numeral (Bit0 One + Bit1 One)`; `add_num_simps(6)` ⟹
`numeral (Bit1 (One + One))`; `add_num_simps(1)` ⟹ `numeral (Bit1 (Bit0 One))`,
which *prints* as `5`. Goal closes by `reflexive`.

**Proof size as a function of bit width** (simulated faithfully from the
equations; exhaustive to 9 bits, adversarial to 1024):

* addition of two *b*-bit numerals: **exactly 2*b* − 1 rewrite steps** worst
  case — Θ(*b*). Notably there is no `add_carry`; the carry is a trailing
  `+ One` and it is absorbed.
* multiplication: **Θ(*b*²)**, exactly 2*b*² − *b* − 1 for all-ones — 8127 steps
  at *b* = 64, 130815 at *b* = 256. Schoolbook; no Karatsuba on the
  kernel-checked path.

Each "step" is one simplifier rewrite = a handful of kernel inferences.

The **numeral simprocs** (`src/HOL/Tools/numeral_simprocs.ML`) are *not*
evaluators — they are cancellation/normalisation procedures
(`3*x + y + 2*x ⟹ 5*x + y`) that compute the coefficient in ML and then *prove*
the rewrite by `Goal.prove` + `simp_tac`. ML is an oracle for **search**, never
for the **conclusion**.

### 4.4 Code generation — what is proved, what is trusted

`Code_Binary_Nat` (binary inside HOL) declares `code_datatype "0::nat" nat_of_num`
and proves every code equation as an ordinary theorem
(`nat_of_num k + nat_of_num l = nat_of_num (k + l)`, justified by
`nat_of_num_numeral`), including an `option`-returning bit-level truncated
subtraction `sub :: num ⇒ num ⇒ nat option`. **Trusted:** that
`{0, nat_of_num}` really is an exhaustive non-overlapping constructor set — the
`code_datatype` declaration is *not* a theorem.

`Code_Target_Nat` maps `nat` onto the target language's bignums via the
`code_abstype` discipline: choose `Nat : integer ⇒ nat` and
`integer_of_nat : nat ⇒ integer`, **prove** the certificate
`Nat (integer_of_nat n) = n`, and then specify every operation in the form
`integer_of_nat (m + n) = of_nat m + of_nat n` — never with `Nat` on the left.
The representation invariant (`k ≥ 0`) is thereby enforced *structurally*, never
stated. Each obligation is discharged by `transfer` + `simp`. **Trusted:** the
`code_printing` serialisation to `IntInf.int` / `Z.t` / `Integer` / `BigInt`
(`Code_Numeral.thy:889–998`). Confirmed: there is no proof that Poly/ML's
`IntInf.+` implements HOL's `+`.

### 4.5 Does Isabelle's kernel compute with numerals fast? No.

Pure's kernel primitives (`src/Pure/thm.ML:1256ff`) are `assume`,
`implies_intr/elim`, `forall_intr/elim`, `reflexive`, `symmetric`, `transitive`,
`beta_conversion`, `eta_conversion`, `abstract_rule`, `combination`,
`instantiate`, `trivial`, `of_class`, plus axioms and oracles. No arithmetic, no
ι rules, no evaluation. Every fast computation is either

* **proof-producing and kernel-checked** — `simp` with the digit equations, the
  numeral simprocs, `Lin_Arith`, and `code_simp` (`src/Tools/Code/code_simp.ML:95`,
  which runs the *code equations* through the simplifier); or
* **outside the kernel, sealed by an oracle** — `eval` (`holds_by_evaluation`,
  `code_runtime.ML:154`), `normalization` (nbe, `nbe.ML:652`), generated code.

**There is no third path.** The state of the art in an LCF system with thirty
years of investment is "the simplifier with good rewrite rules": Θ(*b*) for
addition, Θ(*b*²) for multiplication, no oracle. That is our realistic target
and it is a *good* one.

---

## 5. Term size, concretely

Take the representation of §6: `B ::= bzero | bpos P`, `P ::= one | dbl P | dbl1 P`,
least-significant bit outermost (Coq's `N`/`positive` shape, Isabelle's `num`
shape with Coq's separate zero).

| numeral | term today (`⟦succ^n zero⟧`) | term proposed (`val(b)`) |
|---|---|---|
| `3` | 4 nodes | `val(bpos(dbl1(one)))` — 4 nodes |
| `512` | 513 | `val(bpos(dbl⁹(one)))` — 12 |
| `1000000` (`0b11110100001001000000`) | 10⁶ + 1 | 20 bits → **22 nodes** |
| `1114112` | 1114113 | 21 bits → 23 |
| `4294967296` (2³²) | 4.3 × 10⁹ | `val(bpos(dbl³²(one)))` — **35 nodes** |
| **`18446744073709551616` (2⁶⁴)** | **1.8 × 10¹⁹ nodes — not representable** | `val(bpos(dbl⁶⁴(one)))` — **67 nodes** |

Spelled out, the term for 2⁶⁴ is

```
val( bpos( dbl( dbl( … dbl( one ) … ) ) ) )        64 nested dbl
```

`val`, `bpos`, `dbl`, `dbl1`, `one` are five defined symbols; the term is
`1 + 1 + 64 + 1 = 67` nodes and its depth is 67. This is what makes 2⁶⁴ go from
*impossible* to *routine*, and it is why this is a blocker rather than a
performance item.

*(A base-2⁸ variant would give 2⁶⁴ in 11 nodes and cut every operation's step
count by 8, at the price of a 256×256 digit table. §9 says why base 2 first.)*

---

## 6.0 What was built instead — and what it refuted

**`derived/src/nat/` is the implementation.** The design is *not* §6's. There is
no second type, no `B`, no `val`, and no injectivity or canonicity obligation,
because there is nothing to relate:

```text
carrier            ω, the concrete least inductive set (derived::recursion)
0, succ            von Neumann's, unchanged
natrec(c,g,n)      a recursor with both ι rules, built here
add(x,y)           succ iterated from x
double(x)          add(x,x)          double1(x)  succ(double x)
addc(x,y)          succ(add(x,y))
num(0)=0   num(2k)=double(num k)   num(2k+1)=double1(num k)
```

`double`/`double1` are **further defined symbols on the same carrier**, so a
numeral is a term of `ω` and every equation between the two views is an equation
in one set. Coq needs `Pos.to_nat` and Isabelle needs `numeral` because in both
systems the digit strings are a *datatype*; here they are notation, and the
relating theorems are simply absent. That removes (V1)–(V4) of §6.3, the whole
of §6.4's step 2, and §10's items 4 and 5 — `rep` does not exist and cannot be
forced to reduce, and there is no `⟦Nat.succ⟧`-as-a-function friction because
`succ` is one symbol used by both views.

Measured, on `derived/tests/nat.rs`:

| | |
|---|---|
| `num(2⁶⁴)` | **66 nodes** — §5's prediction, at a different encoding |
| `add` at two 64-bit numerals | **1031 primitive kernel inferences** |
| the same at 32 / 65 bits | 519 / 1047 — exactly `16·bits + 7` |
| `mul` at two 16- / 32-bit numerals | 4468 / 17140 — Θ(bits²), schoolbook |
| `ble` at two 64-bit numerals | **775** — and at 1/2/4/8/16/32 bits, 19/31/55/103/199/391, exactly `12·bits + 7` |
| `beq` at `2⁶⁴` against itself | **785** (65 bits) |
| `ble 55297 4294967296` | 388 — §1.4's `isValidChar_UInt32` demand |

**Five things this document got wrong, in the order they were found.**

1. **§6.1's "the ι rules come free" is false**, and it was the reason given for
   keeping the general path. They are free for a *declaration the translation
   processed*; they are not free for `ω`, which no declaration produces. The
   recursor here is built, and the reason it is not just
   `crate::recursion::recursion` is §6.0's own finding: that theorem fixes its
   step as a **unary function symbol** of the ambient extension, so neither a
   step supplied as a set nor a step that sees the index can be expressed
   through it. Both move into the *state* instead — iterate on `⟨g,⟨n,v⟩⟩` —
   and one induction recovers both ι rules.
2. **§3.3's warning about `Pos.peano_rect` does not apply and could not.** Coq's
   successor rule is propositional and costs `p−1` applications because `P p` is
   a *dependent type* and the value genuinely is `f` applied `p−1` times. Here
   every statement is an equation between sets, so `succ(double x) = double1 x`
   is definitional and `succ(double1 x) = double(succ x)` is two rewrites. The
   cost of peeling one `succ` off a numeral is Θ(trailing ones), never Θ(value).
3. **Isabelle's "define by transport, then derive the digit equations" (§9's
   highest-leverage idea) is not the cheapest route here.** It needs `rep`, and
   `rep` needs a second type to be the source of. With one carrier the digit
   equations come out of ordinary arithmetic: the four `add` cases are one
   instance of an *exchange law* `add(add a b, add c d) = add(add a c, add b d)`,
   which is five rewrites over associativity and commutativity and no induction
   of its own.
4. **`add`'s Peano equations are not a proof obligation at all.** §8 treats them
   as the expensive half. Defining `add` as iterated `succ` makes both of them
   the recursion theorem's own base and step with one abbreviation unfolded —
   nothing is proved by induction to get them, which is exactly what the
   uniqueness bridge needs. The expensive half of §8 remains expensive, but it is
   entirely on the *other* side: deriving those equations for an imported
   `Nat.add`.
5. **The uniqueness bridge needs no typing hypothesis on `f`.** §8 states it
   under `f ∈ fs(⟦Nat⟧, fs(⟦Nat⟧,⟦Nat⟧))`. The derivation reads `f` only through
   `app`, so `app(app(f,x),y)` is a term whatever `f` is; requiring the
   function-space membership would be an antecedent nothing reads and a caller
   would have to discharge before the bridge could fire.

**Still open, unchanged:** §10's item 1 — whether a checker can derive
`Nat.add`'s two defining equations from an export by δ + ι. Nothing in
`derived/` can answer it, and it is the load-bearing uncertainty for the whole
chain.

## 6. The recommendation — **superseded, see §6.0**

> **Keep `⟦Nat⟧` exactly as the general inductive translation produces it.
> Build the binary numerals as a *separate* derived construction `B` with its
> own recursor, together with an interpretation `val : B → ⟦Nat⟧`, and prove
> `val`'s Peano equations. Hardcode nothing about the type; hardcode the
> *literal clause* and the *fifteen operation names*, keyed by name, at the
> reduction axis.**

That is Coq's `N`/`N.to_nat` and Isabelle's `num`/`numeral`, transposed. Both
systems, independently, refused to re-found their unary natural numbers and
instead made the binary strings a first-class inductive type with a proved
morphism into the unary one. Neither system's kernel knows anything about it.

### 6.1 The carrier — must `⟦Nat⟧` be `ω`? No, and it isn't.

**Confirmed by grep: nothing in this codebase assumes anything about `⟦Nat⟧`.**
`Nat` goes through the general inductive translation like every other
declaration, so `⟦Nat⟧` is the W-type
`W(A, B, U({A,T}))` with `A := Sum_2(1,1)`, `B := rec₊(λ_. finord(0), rec₊(λ_. finord(1), ∅))`
(`derived/src/inductive.rs:16–21`).

Patterns used: `nat_shape|nat_recursor|NatMem|NatUniverse|nat_rec|omega|Omega|infinity|Infinity|\bInf\b`,
`wnat|wnat_rec`, `⟦Nat⟧|⟦N⟧`, `von Neumann`, `NatLit|natLit|nat_lit`, `finord`,
`finset|FinSet|\bFin\b`, `direct::|clause_for|Clause::`.

Two places say the *opposite* of ω explicitly:

* `derived/src/cumul.rs:154` — "`⟦N⟧` is `W(A, B, U(A))` with `A = 1+1`".
* `derived/src/cumul.rs:372`, `derived/src/cumul/finord.rs:27` — "`finord(m) = Sum_m(1,…,1)`
  … which is **not** the von Neumann numeral `m` … `finord(m) ∈ ω` is false".

The ω that is everywhere in `derived/` — `bnd(k)`'s `∃p ∈ ω`, `bounded`'s
`∀k. k ∈ ω → bnd(k)`, `recursion/omega_tower.rs`, `cumul/universe.rs:20`'s
`U₁ = U(ω)` — is the **stage index of the cumulative hierarchy**. It has nothing
to do with `⟦Nat⟧` and this work must not touch it.

The only constructions that *do* hardwire a particular `Nat` carrier are the old
standalone ones — `derived/src/wnat.rs` (`N := W(1+1, B, U(1+1))`,
`zero = ⟨inl •, ∅⟩`, `succ n = ⟨inr •, {⟨•,n⟩}⟩`), `derived/src/wnat_rec.rs`
(both ι rules at those two terms), and their consumers
`checker/src/tg.rs:1782, 4828, 10654` (gated by the hand-written recogniser
`nat_shape`, `tg.rs:4996`) and `derived/src/cumul/witness.rs` (`NatUniverse`,
`NatMem`). **`mini/` does not reference `wnat` at all.** `LIBRARY-BACKLOG.md`
§10 already records those eight files as scheduled for deletion.

So the carrier is genuinely free. The recommendation nevertheless is **do not
change it**, for three reasons:

1. **The ι rules come free.** The general path already proves `Nat.rec`'s
   typing, `step typed`, `ι 0`, `ι 1`, `gen ι 0`, `gen ι 1` — universally
   quantified, per σ (measured, §7). A bespoke binary carrier means re-proving
   all of them, and Coq's `peano_rect_succ` (§3.3) is direct evidence that the
   successor ι rule on a binary carrier is the *hard* one: propositional, by
   induction generalising over the motive.
2. **The `direct::Clause` route is Prop-only today** and carries a standing rule
   against a fourth row (§7).
3. **It keeps `Nat` on the general path**, so the inductive translation is not
   forked and every future improvement to `derived::inductive` applies to `Nat`
   automatically.

The one thing that changes about `⟦Nat⟧` is the *literal* clause:
`⟦natLit n⟧ := val(b_n)` instead of `⟦succ^n zero⟧`.

### 6.2 What `B` is, and why it can be cheap to build

```text
P ::= one | dbl P | dbl1 P          (positive binary, LSB outermost, canonical)
B ::= bzero | bpos P                (zero carved out separately)
```

`B` and `P` are **ordinary two- and three-constructor non-indexed inductive
shapes**. They can be built by the machinery that already exists:
`derived::inductive::{Machine, DeclSpec, CtorSpec, Inductive::build}` supplies
the carrier, `closed`, `Ctor::mem`, `Ctor::inj` and `Inductive::distinct` at
arbitrary arity, and `derived::wrec_total` supplies the recursor with its
**unguarded** ι rules under `closed ∧ step_typed`. That is the same route
`⟦Nat⟧` itself takes. Nothing about `B` needs new W-type theory.

*Caveat, flagged:* `derived::inductive` is driven by *declaration data*
(`DeclSpec`/`CtorSpec`). Whether it can be driven from a synthetic spec that no
export produced — and whether `cumul::DeclUniverse` will supply `⊢ B ∈ U₁` for
it — I did not verify. If it cannot, `B` is a hand-written W-type in the mould
of `wlist.rs` (which is `1 + α` with one recursive argument; `P` is `1 + 1 + 1`
with one recursive argument on two of three — strictly simpler than `List`,
since there is no parameter and no field).

### 6.3 `zero`, `succ` and the ι rules

They are **not restated**. `⟦Nat.zero⟧`, `⟦Nat.succ⟧` and `⟦Nat.rec.{u}⟧` stay
exactly what the general path produces (§7 lists them). What is added is:

```text
dbl_N : ⟦Nat⟧ → ⟦Nat⟧          defined by ⟦Nat.rec⟧:  dbl_N 0 = 0,  dbl_N (succ n) = succ (succ (dbl_N n))
val   : B → ⟦Nat⟧              defined by B's recursor:
          val(bzero)      = ⟦Nat.zero⟧
          val(bpos p)     = pval(p)
          pval(one)       = succ(zero)
          pval(dbl  p)    = dbl_N (pval p)
          pval(dbl1 p)    = succ (dbl_N (pval p))
```

and then, proved once and for all, universally quantified:

```text
(V1)  ⊢ ∀b ∈ B. val(b) ∈ ⟦Nat⟧
(V2)  ⊢ ∀b b′ ∈ B. (val(b) = val(b′) → b = b′)         val is injective — needs canonicity
(V3)  ⊢ ∀b ∈ B. val(bsucc b) = ⟦Nat.succ⟧ (val b)      the successor morphism
(V4)  ⊢ ∀b ∈ B. (b ≠ bzero → val(b) = ⟦Nat.succ⟧ (val (bpred b)))
```

**(V3) is the analogue of Coq's `Pos.add_1_l`/`add_succ_l` and Isabelle's
`numeral_inc`, and it is the one real proof obligation.** It is proved by
induction over `B` (three cases for `P`), generalising nothing — unlike Coq's
`peano_rect_succ`, which had to generalise the motive, because we are proving an
equation between *sets*, not inhabiting a dependent type. That is one place
where the set-theoretic model is genuinely easier than Coq.

**Does the ι rule need a case analysis whose size grows with the numeral? No.**
`Nat.rec`'s ι rules are the general path's, proved once, quantified over the
whole carrier. The per-numeral cost is entirely in **(V4) instantiated at a
concrete `b`**: one `ax_inst` + `mp`, which is **O(1) kernel steps**, followed by
normalising the term `bpred(b)` to a canonical numeral, which is **Θ(bits)**
digit rewriting. Isabelle pays exactly this (`pred_numeral` via `BitM`,
`Num.thy:1090`), and it is what makes `Nat.rec` on a literal cost
Θ(n · bits) for us against Lean's Θ(n).

### 6.4 The operations

For each accelerated name, four things:

1. a **specification** on `⟦Nat⟧`: the two primitive-recursion equations
   (`add x zero = x`, `add x (succ y) = succ (add x y)`);
2. an **implementation** `⊞ : B × B → B`, *defined by transport* —
   `b ⊞ b′ := rep(add(val b, val b′))` where `rep` is `val`'s inverse — which is
   Isabelle's move (§4.3) and needs no termination argument;
3. the **digit equations** for `⊞`, nine of them for addition, derived in one
   line each from injectivity (V2) plus the morphism, exactly as
   `add_num_simps` is;
4. the **bridge**: `⊢ ∀b b′. add(val b, val b′) = val(b ⊞ b′)`.

Then a reduction of `Nat.add ⟨lit⟩ ⟨lit⟩` is: instantiate (4) — O(1) — and
compute `b ⊞ b′ = b″` by the digit equations — **Θ(bits) for `add`/`sub`/
`beq`/`ble`/`land`/`lor`/`xor`/`shiftLeft`/`shiftRight`, Θ(bits²) for
`mul`/`div`/`mod`, Θ(bits² · log exp) for `pow`**, matching Isabelle's measured
2*b* − 1 and 2*b*² − *b* − 1.

At *b* = 64: ~127 kernel-checked rewrites for an addition, ~8000 for a
multiplication. Against 35 literals in `init-prelude` and 340 arithmetic steps,
that is a rounding error next to the file's 43,463 reduction steps.

**Order of work, bounded by measurement (§1.4):** `succ`, `beq`, `ble`, `add`,
`sub`, `mul`, `pow`, `div`, `mod` unblock `init-prelude`. `gcd`, `land`, `lor`,
`xor`, `shiftLeft`, `shiftRight` are not named in it at all and can wait.

Mirror Lean's `pow` guard, and tighten it: Lean's `ReducePowMaxExp = 2²⁴` allows
a 16-million-bit result, which for us is a 16-million-node term. A guard on
*result bit-width* (say 2¹⁶) is the right shape; above it, decline rather than
build the term.

---

## 7. What the hardcoded clause has to supply

The brief's standing exception — a hardcoded `Nat` clause is a special case
justified by Lean's kernel doing the same — still applies, but it lands in a
different place than expected. Both alternatives, measured.

### 7.1 The contract, read off the general path

`./target/release/mini --dump-theorems good/tutorial/097_aNatLit.ndjson` shows
exactly what any replacement would owe. Verbatim:

```
  Nat        ⊢ ⟦Nat.{}⟧ ∈ ⟦Sort 1⟧
  Nat.zero   ⊢ ⟦Nat.zero.{}⟧ ∈ ⟦Nat.{}⟧
  Nat.succ   ⊢ ⟦Nat.succ.{}⟧ ∈ dprod₀(⟦Nat.{}⟧, ⟦Nat.{}⟧)
  Nat.rec σ=[0]  ⊢ ⟦Nat.rec.{0}⟧ ∈ f61(…, dprod₀(⟦Sort 0⟧, ⟦Nat.{}⟧))
  Nat.rec σ=[1]  ⊢ ⟦Nat.rec.{1}⟧ ∈ f92(…, dprod₀(⟦Sort 1⟧, ⟦Nat.{}⟧))

  inductive Nat   2 constructor(s), non-indexed
    carrier / carrier ax / closed
    ctor 0 mem / ctor 1 mem / ctor 1 inj
    universe (built as a local in zoneb::DeclUniv, folded into the constant's typing)
    rec typing / rec step typed / ι 0 / ι 1 / gen ι 0 / gen ι 1
    rec abbrev Nat.rec σ=[1] / rec target Nat.rec σ=[1]
```

Fourteen apparatus slots, **at every σ the file schedules**. That is the whole
of what a replacement carrier owes.

### 7.2 If one nevertheless put `Nat` in `direct::Clause`

`mini/src/direct.rs:165` — `pub enum Clause { Eq, Acc }`. Five things a new
variant must supply:

1. a row in `clause_for` (`direct.rs:204`), matching `Name::Str(Anon, s)`;
2. `fn arity(self) -> (u32, u32, usize)` (`direct.rs:191`) — `(num_params,
   num_indices, num_ctors)`, checked against the export at `direct.rs:230`;
3. an arm in `former_bottom` (`direct.rs:292`) producing `(term, φ, χ)` — the
   denoting `Term`, the `Formula` it is the conditional singleton of, and the
   instantiated defining biconditional;
4. an arm in `ctor_bottom` (`direct.rs:418`, `struct CtorSite`) plus an arm in
   the `step_hyp` match (`direct.rs:445`), yielding `⊢ • ∈ carrier`;
5. an arm in `recursor::ensure` (`mini/src/recursor.rs:157–171`).

Dispatched at `mini/src/zoneb.rs:723–725`, *before* the eliminator trichotomy.

**Two blockers, both real.** First, the mechanism is **Prop-only**:
`former_bottom` types the denotation with `tower.cond_in_u0` (`direct.rs:340`),
and `ctor_bottom`'s whole premise (`direct.rs:412–414`) is *"a direct
constructor's interpretation is `•`, because the declaration denotes a subset of
`1`"*. `Nat` lands in `Type 0`. Both bottoms would need a second, non-`[φ]`
route. Second, the module states a standing rule against exactly this
(`direct.rs:57–62`): *"The table takes **no fourth row** … a declaration that
seems to want one is evidence that the general clause is missing a case."*

**Both blockers were said to vanish under the recommendation, because `Nat`
would keep the general clause. §6.0 chose otherwise, so they do not vanish —
they are the work.** They are not, however, blockers in the sense of §7.2's
paragraph: the standing rule against a fourth row is a rule against a *collapse
that happens to be convenient*, and `⟦Nat⟧ = ω` is not one. It is the same kind
of row `Acc` is — a construction the general route does not have and cannot
reach — and the general route's `⟦Nat⟧` is a W-type carrier that no binary
numeral can be a term of. What is real is the first blocker, and it is
engineering: the two bottoms are `[φ]`/`•`-shaped and need a second route.

### 7.3 What the direct clause has to supply — read off the code

*(This section used to open "Nothing at the **interpretation** axis", which was
the superseded §6 recommendation's answer and is now the wrong one: with one
carrier, the literal clause is only expressible if `⟦Nat⟧` **is** `ω`, so the
interpretation axis is exactly where the change starts.)*

Twelve edits, verified against the tree at `8e2e45b`. `derived/` owes **none**
of them: `nat::Nat` has the carrier, both ι rules and `ω ∈ U₁`, `nat::Eval` has
the numerals and the arithmetic, and `nat::natrec_mem` — added for this — has
the recursor's typing.

**Build the apparatus with `Nat::over`, never `Nat::new`.** `Nat::new` calls
`Tower::new`, a fresh chain of definitional extensions, so it hands back an `ω`
over a *second* `1`, `•`, `app`, `∅` and pairing. Nothing about that is a type
error: `⊢ ω ∈ U₁` would simply be a membership in a `U₁` no interpretation
mentions, and `⟦Nat.zero⟧ = 0` would name an `∅` nothing else does. Row 9 must
thread `ip.prelude.tower` in, which is what `Nat::over` exists for.

| # | site | what it supplies |
|---|---|---|
| 1 | `direct.rs:165` `enum Clause` | a `Nat` variant |
| 2 | `direct.rs:191` `fn arity` | `(0, 0, 2)` — no parameters, no indices, two constructors |
| 3 | `direct.rs:204` `clause_for` | `"Nat"` |
| 4 | `direct.rs:292` `former_bottom` | a **non-`[φ]` route**: the term `ω` and `Nat::omega_mem` raised to `⟦Sort 1⟧`, instead of `tower.cond_in_u0` |
| 5 | `direct.rs:418` `ctor_bottom` | a **non-`•` route**: `Nat.zero ↦ 0` with `Nat::zero_mem`, `Nat.succ ↦ succ(x)` with `Nat::succ_mem_at` |
| 6 | `recursor.rs:157` | `Some(Clause::Nat) => rec_nat::ensure(…)` |
| 7 | new `mini/src/rec_nat.rs` | the bottom of `Nat.rec`'s nest — at `u₁ = 0`, `•` and `induction_scheme` at `φ(z) := • ∈ app(C,z)`; at `u₁ ≥ 1`, `natrec(c,g,t)` and `nat::natrec_mem` |
| 8 | new `mini/src/iota_nat.rs` | `selects`/`fire`, the sibling of `iota_dep` and `iota_model`, out of `Nat::iota_zero`/`iota_succ` |
| 9 | `interp.rs:132`/`154` | a `NatClause` cached beside `direct`/`acc`, lazy with a failure flag (`acc.rs:43–55`) |
| 10 | `kernel.rs:2478` | `⟦natLit n⟧ := Eval::numeral(n)` with `Eval::mem`, replacing `nat_unfold`'s `n`-deep recursion |
| 11 | `kernel.rs:1650` | `whnf`'s `NatLit` arm now **owes a `step!`** — see below |
| 12 | `convert.rs` `> 10` | lift, and state the effect on the exit-2 population |

**The constructors and the recursor do not have to be reified by hand.**
`Checker::lam_nest` (`kernel.rs:2920`) walks the Lean `Π` binders and builds the
function set from whatever the bottom returns, which is how `Acc.intro` gets
`⟦Acc.intro⟧ ∈ dprod₀(…)`. So row 5 owes `⊢ succ(x) ∈ ω` under the scope
`x ∈ ω` and nothing about function spaces, and row 7 owes
`⊢ natrec(c,g,t) ∈ app(C,t)` and nothing about the four-deep nest above it.

**`Eval::succ` is already row 11's evidence.** `whnf`'s `NatLit` arm currently
emits no `step!` at all, on the stated ground that `⟦natLit n⟧` *is* the
interpretation of `Nat.succ (natLit (n−1))` so the unfolding is reflexivity at
the term level. Under the binary clause that ceases to be true and the arm owes
an equation — and the equation is `Eval::succ(n−1)`,
`⊢ succ(num(n−1)) = num(n)`, read backwards, composed with `⟦Nat.succ⟧`'s own
β-rule from `Interp::beta_spine`. Nothing new is needed in `derived/`; the cost
is Θ(trailing ones of `n−1`), `O(1)` on the common case.

The name-keyed table is the same trust surface Lean's kernel has, with one
difference argued in §8.

---

## 8. The uniqueness bridge, and its cost

The step-4 statement, per operation, e.g. addition:

```text
⊢ ∀f. ( f ∈ fs(⟦Nat⟧, fs(⟦Nat⟧,⟦Nat⟧))
      ∧ (∀x ∈ ⟦Nat⟧. app(app(f,x), ⟦Nat.zero⟧) = x)
      ∧ (∀x y ∈ ⟦Nat⟧. app(app(f,x), succ y) = succ (app(app(f,x), y))) )
    → ∀x y ∈ ⟦Nat⟧. app(app(f,x),y) = add(x,y)
```

Proved by induction on `y` using `Inductive::closed` — the induction principle
the general path already produces. **One derivation per operation, independent
of any numeral, memoised.** That is cheap, and it is Coq's `NDefOps.def_add_add`
verbatim (§3.2).

**The expensive half is the other premise, and it is the main risk in the
chain.** Instantiating the bridge at `f := ⟦Nat.add⟧` requires proving that
`⟦Nat.add⟧` *satisfies* those two equations — which must come from the export's
actual definition, by δ + ι, not be assumed. Three tiers:

* **Structural (easy in principle):** `Nat.add`, `Nat.sub`, `Nat.mul`,
  `Nat.pow`, `Nat.beq`, `Nat.ble`, `Nat.pred` are structural recursions in the
  prelude; their equations hold by δ + ι + β. Each is a fixed-size derivation,
  once per `(constant, σ)`, memoised. *But* they elaborate through
  `brecOn`/`below`/`match_n`, and `MEASUREMENTS.md:2107–2109` records
  `Nat.below` at 1077 distinct interpretations and `Nat.brecOn` at 1050 — so the
  derivation is not one ι step, it is a nest. **I have not verified that `mini`
  can produce these equations today**, and I would not brief step 4 without
  checking it on `Nat.add` first.
* **Well-founded (hard):** `Nat.gcd` is `termination_by m`, compiled through
  `WellFounded.fix`/`Acc.rec`. `Nat.land`/`lor`/`xor` go through `Nat.bitwise`,
  likewise. For these the "primitive recursion equations" characterisation does
  not directly apply; the right characterisation is the `Acc.rec` fixpoint
  equation, and `mini` does have that machinery
  (`mini/src/rec_acc_iota.rs`) — but this is a separate design question and it
  is *not* answered here.
* **Fuel-based:** `Nat.div`/`Nat.modCore` use a structural inner `go` with a
  fuel argument. Structural, so tier 1 in principle, but the characterisation to
  bridge against is `div_unique`-shaped (`x/y = if 0 < y ∧ y ≤ x then (x−y)/y + 1
  else 0`), not primitive-recursive. `checker/src/tests/natlit.rs:35` already
  pins exactly that equation for the bignum implementation, which is a useful
  head start.

**The fallback, and it is better than Lean.** Lean's kernel simply *trusts* that
the environment's `Nat.add` is the prelude's (§2). We cannot. But `mini`'s
kernel has Isabelle-style hypotheses (`QUESTIONS.md`), so the equations can be
threaded as **hypotheses on the certificate**, discharged once per file (or left
undischarged and reported in the ledger as an honest, named assumption). That is
strictly more honest than Lean's name-keyed trust, and it decouples step 3 from
step 4: the fast arithmetic can land and be *conditionally* certified while the
equation derivations are still being built.

---

## 9. Which moves I take, and which I reject

**Taken, from Coq:**

* **Canonical representation with zero carved out** — `N = N0 | Npos positive`,
  no leading zeros. Every uniqueness argument downstream (injectivity of `val`,
  decidable equality, single-pass comparison) rests on it. Isabelle agrees, and
  its own §7 lesson is that keeping 0 *inside* the numeral system avoids the
  `*_special` lemma tax it pays for `numeral` starting at 2.
* **LSB-outermost, with an accumulator comparison** (`compare_cont`) — a single
  Θ(bits) pass despite the little-endian layout.
* **Mutual `add`/`add_carry` rather than a carry argument** — keeps the
  recursion structural on both arguments and avoids a boolean-indexed motive in
  every proof.
* **Two recursors, kept apart.** `binary_rect` (cheap, definitional ι, for
  computation) and `peano_rect` (linear in the value, propositional ι, for
  induction). For us: `B`'s own recursor is the cheap one; `⟦Nat.rec⟧` is the
  Peano one; they are related by (V3)/(V4) and never confused. **Coq's
  deprecation of `NDefOps`/`NStrongRec` is the empirical evidence that defining
  computational functions through the Peano recursor is a mistake.**

**Taken, from Isabelle:**

* **Define the fast operation by transport, then *derive* the digit equations**
  (`m + n = num_of_nat (nat_of_num m + nat_of_num n)`, then `add_num_simps` in
  one line each). This is the highest-leverage idea in the whole survey: it
  removes every termination argument and makes the step-4 bridge *hold by
  construction on the `B` side*, leaving only the `⟦Nat⟧`-side equations to
  derive.
* **Two induction principles on `B`** — digit (for stating computation rules)
  and Peano-style One/inc (for proving the morphism laws). `numeral_add` is
  three lines *only* because of `num_induct`.
* **Bit-level predecessor (`BitM`/`pred_numeral`) as a case-analysis interface,
  never a computation path**, and full expansion to `succ`-form guarded behind
  an explicit opt-in.
* **The `code_abstype` discipline as a proof pattern** — prove `A(π n) = n`,
  then state every operation as `π(op x y) = …`. It encodes the representation
  invariant structurally instead of stating it.
* **The `option`-returning bit-level truncated subtraction**
  (`Code_Binary_Nat`'s `sub : num ⇒ num ⇒ nat option`), not Isabelle's own
  `diff_nat_numeral` detour through `int`, which is a layering artefact.

**Rejected:**

* **Coq's `Int63` / retroknowledge / `vm_compute` / `native_compute`.** It is a
  kernel extension plus ~25 unproved axioms plus two extra conversion engines
  re-run by the kernel. Directly forbidden by the brief, and §3.6 shows we lose
  nothing essential: `positive`/`N` get *zero* kernel help and are still fast,
  because the win is entirely in term size and algorithm.
* **Isabelle's `eval`/`nbe`/code serialisation.** Oracles
  (`holds_by_evaluation`, `normalization_by_evaluation`) plus a trusted
  `IntInf`/GMP mapping. Same reason.
* **Isabelle's `code_datatype` declaration.** `code_datatype "0::nat" nat_of_num`
  is a *declaration*, not a theorem — the exhaustiveness of the constructor set
  is unverified. Our premise forbids it. (The `[code]` *equations* are theorems
  and do transfer.)
* **Isabelle's class-polymorphic "prove once, inherit at `nat`".** It requires
  sorts in the kernel (`Thm.of_class`, sort-checked `instantiate`), which we do
  not have and which `kernel/` must not grow to acquire. We can get the same
  *sharing* by explicit universal quantification over the structure, but every
  use pays an application rather than an O(1) sort check. **Do not assume the
  free inheritance carries over** — this is the one place where an Isabelle
  design reads as more transferable than it is.
* **Coq's `Numbers` module-type/functor packaging** (`NAxiomsSig`, `<+`,
  `Include`) and its setoid `Proper`/`_wd` layer. Four of those files are
  deprecated since 8.20. Take the *content* — an operation is pinned by two
  equations plus induction — and drop the packaging. With extensional equality
  we state the successor equation with plain `=` and skip `Proper` entirely.
* **Coq's `eq_dep_eq_positive` / UIP-from-decidable-equality.**
  `PeanoViewUnique` needs it only because `PeanoView` is a dependently indexed
  inductive family. In a set-theoretic model the corresponding uniqueness is a
  plain induction. Do not import the complexity.
* **The `nat`↔`N` conversion layer as a *proof-transport* mechanism.** Despite
  `Pnat.v` + `Nnat.v` being ~50 lemmas, no `N` fact is proved via `nat`; the
  bridge is used outbound (to `ring` coefficients, to `R`, to `zify`). Our
  `val` bridge should be understood the same way: it exists to *state* the
  agreement, not to prove `B` facts from `⟦Nat⟧` facts.
* **Base 2^k, for now.** It cuts every step count by `k` and would make
  multiplication at 64 bits ~130 rewrites instead of ~8000, but it multiplies
  the digit table by `k²` and its carry reasoning is genuinely harder. Base 2
  first. The design is arranged so this is revisable: every `⟦Nat⟧`-side
  statement is about `val`, so changing the base changes `B`, `val` and the
  digit equations and leaves the bridges' *statements* untouched.

---

## 10. What I could not settle

Listed plainly, because the next seat builds from this and a confident
reconstruction costs more than an honest gap.

1. **Whether `mini` can derive `Nat.add`'s two defining equations today.** This
   is the load-bearing uncertainty (§8). The equations must come from the
   export's `brecOn`/`below`/`match_1` nest by δ + ι, and
   `MEASUREMENTS.md:2107–2109` shows that nest is where the interpretation
   already churns. **Verify this on `Nat.add` before briefing step 4.** If it
   fails, the hypothesis-threading fallback in §8 is the answer, and it changes
   step 4's shape.
2. **Which accelerated operations actually fire on `init-prelude`, and at what
   argument sizes.** `stepcount` has a single `Kind::NatLit` counter
   (`checker/src/tc.rs:637`) and instrumenting `checker/` is out of scope here;
   `mini` cannot load the file. §1.4's list is inferred from the names and
   literals present. In particular I do **not** know whether any `Nat.rec`
   iterates over a large literal — if one does, the Θ(n · bits) cost of §6.3
   becomes the binding constraint rather than a footnote, and that would change
   the priority order.
3. **Whether `derived::inductive::Machine` can be driven from a synthetic
   `DeclSpec` that no export produced**, and whether `cumul::DeclUniverse` will
   supply `⊢ B ∈ U₁` for it (§6.2). If not, `B` is hand-written in the mould of
   `wlist.rs`. This changes the size estimate for step 2 but not the design.
4. **The cost of `rep` (`val`'s inverse).** §6.4 defines `⊞` by transport, which
   needs `rep : ⟦Nat⟧ → B` to exist as a *term*. Isabelle gets `num_of_nat` as a
   `primrec` on `nat`; ours would be defined by `⟦Nat.rec⟧`, hence total but not
   computable in fewer than Θ(value) ι steps. **That is fine** — `rep` is never
   evaluated, only used to *define* `⊞` and to state (V2) — but it must be
   checked that nothing forces it to reduce. If it does, the alternative is to
   define `⊞` directly by `B`'s own recursor and prove the digit equations by
   ι rather than deriving them, i.e. Coq's route rather than Isabelle's.
5. **Whether `⟦Nat.succ⟧`-as-a-function vs the constructor *term* causes
   friction.** The dump shows both exist (`⟦Nat.succ⟧ ∈ dprod₀(⟦Nat⟧,⟦Nat⟧)` and
   `ctor 1 mem` at the term `⟨inr •, {⟨•,x₀⟩}⟩`). `val` should be built on the
   term and related to the function by a beta lemma — `wnat` has exactly that
   pair (`succ_in_funspace`, `succ_beta`), so the precedent exists, but I did
   not check what the *general* path names them.
6. **No Isabelle or Coq was executed.** Both agents worked from source. The step
   counts in §3.3 and §4.3 come from faithful transcriptions of the fixpoints
   and rewrite rules into Python (Isabelle's addition bound exhaustively to 9
   bits, adversarially to 1024; Coq's `p−1` count is also forced by the type),
   not from `vm_compute` timings or a kernel-inference count. The constant
   factor between "rewrite step" and "kernel inference" is unmeasured in both.
7. **Mathematical Components' `ssrnat` and `coq-bignums`' `BigN`** were not
   surveyed. Either might be a useful second data point on binary carriers —
   `BigN` in particular is a tree-of-`Int63` instantiating the same `Numbers`
   signatures.

---

## 11. Acceptance criteria for the rest of the chain

Stated here because §1.2 shows the obvious one is nearly vacuous.

* **Necessary but weak:** `good/tutorial` stays at `accept=89 decline=2
  reject=0`, `pairs=218 constEv=218 typeEv=218`, `unsealed=0 gapped=0`. It
  exercises `⟦Nat⟧`, the two constructors, `Nat.rec` at σ=[0] and σ=[1], and the
  literals 0 and 3. Nothing else.
* **The real target:** `mini` *loads* `init-prelude.ndjson` — i.e. the
  `convert.rs:641` guard and the `kernel.rs:1836` guard are gone and the file
  reaches interpretation with `natLits=35`, `maxNatLit=18446744073709551616` in
  its facts row. That is the first honest signal, and it is available the moment
  step 2 lands, before any arithmetic exists.
* **Then:** the 340 nat-literal-arithmetic steps `MEASUREMENTS.md:31` records
  are answered with certificates rather than declined.
