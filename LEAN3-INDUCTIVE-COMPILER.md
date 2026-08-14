# Lean 3's out-of-kernel inductive compiler, read against the source

**What this is.** An archaeology report on `leanprover-community/lean`'s
`src/library/inductive_compiler/`, written so that the nested increment can be
scoped without reading the C++ again. Precision over completeness: every claim
below is either cited to `file:line` or explicitly marked as not established.

**Provenance.** Clone of `https://github.com/leanprover-community/lean` at
`f91b574` ("Warn about deprecation in README (#815)"), read on 2026-08-06. The
clone lives in the session scratchpad and is *not* part of this repository.
Lean 3 was **not** built; nothing here required it, and building it would have
bought nothing that reading the source did not.

---

## 0. The gating question: can a Lean proof of `Eq lhs rhs` be cashed into `⟦lhs⟧ = ⟦rhs⟧`?

**Yes. Uniformly, at every sort, open or closed, and it is already implemented
and already exercised by the corpus.** This is not a reconstruction — the
derivation exists as a function today and two corpus fixtures run it.

### The chain, with the code that performs each step

`Eq` takes §6.2's own interpretation clause (`checker/src/mini/direct.rs`), so

```text
⟦Eq α a b⟧ = eq_set(⟦a⟧, ⟦b⟧) = [ ⟦a⟧ = ⟦b⟧ ]        direct.rs:311-318 (Clause::Eq)
```

a conditional singleton, with its characteristic theorem stored as
`Direct::eq_ax` (`direct.rs:111-112`):

```text
⊢ ∀a ∀b ∀z. ( z ∈ eq_set(a,b) ↔ (z ∈ 1 ∧ a = b) )
```

`derived::prop::cond_elim` is the ← half of that biconditional at `z := •`
(`derived/src/prop.rs` header table, "`• ∈ [φ] → φ`"). So from a typing
`⊢ • ∈ eq_set(⟦lhs⟧, ⟦rhs⟧)` one modus ponens yields `⊢ ⟦lhs⟧ = ⟦rhs⟧`.

Under binders, the statement `∀ x : A, lhs x = rhs x` is a `Π` whose codomain
sort is `Prop`, so `Checker::pi_evidence` takes the **`Prop` clause**
(`checker/src/mini/kernel.rs:1973`, `if (n2 == 0)`) and

```text
⟦∀x:A. β⟧ = chi(h⃗, ⟦A⟧) = [ ∀x. (x ∈ ⟦A⟧ → • ∈ b(h⃗,x)) ]   interp.rs:2334-2368 (cond_site)
```

again a conditional singleton, whose elimination rule is
`Interp::cond_app` (`interp.rs:2472-2506`): from `Γ ⊢ • ∈ chi(h⃗,⟦A⟧)` and
`Γ ⊢ ā ∈ ⟦A⟧` it produces `Γ ⊢ • ∈ ⟦β[a]⟧`.

So the full cashing of `h : ∀ x⃗, lhs x⃗ = rhs x⃗` is: `cond_app` once per binder,
`Interp::beta_spine` to reduce `⟦Eq α (lhs x⃗) (rhs x⃗)⟧` onto `eq_set(…)`,
`cond_elim` + `mp`, then `Scopes::close(..).discharge` to universally quantify
the TG statement over the scope hypotheses `x̄ ∈ ⟦A⟧`.

### It exists as one function today

`checker/src/mini/quot_classes.rs:504-590` (`rcompat_at`) is exactly that pipeline. It
takes `Quot.lift`'s compatibility hypothesis `h : ∀ a b, r a b → f a = f b`,
which is an **arbitrary Lean proof term, not a `rfl`**, and produces

```text
Γ ⊢ ∀x ∀y. ( ⟨x,y⟩ ∈ R̄ → f̄(x) = f̄(y) )
```

— three `cond_app`s (lines 537, 552, 561), one `beta_spine` (569), then
`cond_elim` + `mp` (579-580), then the discharges (583-589). Corpus rows
`122_quotLiftType` and `124_quotLiftReduction` both `accept`, so the derivation
runs on real exports.

`checker/src/mini/recursor.rs:490-507` is the same elimination at `Eq.rec`'s major
premise: it pulls `⊢ a = b` out of `⊢ t ∈ eq_set(a,b)` and uses it to justify
the transport.

### Measured on a purpose-built export

`inductive N | zero | succ`, `add` recursing on its **first** argument, and

```lean
theorem addZero : ∀ n : N, Eq (add n N.zero) n :=
  fun n => N.rec (motive := fun k => Eq (add k N.zero) k)
    (Eq.refl N.zero) (fun k ih => congrArg N.succ ih) n
```

— an equation between two terms that are *not* definitionally equal at a
variable, proved by induction and `congrArg`, not by `rfl`. Exported at the
pinned toolchain (Lean v4.29.1, githash `f72c35b…`, lean4export `caccfbe`,
format 3.1.0) and run through `mini --dump-theorems`:

```text
  addZero   σ = —
    ⟦c.{σ}⟧  ⟦addZero.{}⟧
    typing   ⊢ ⟦addZero.{}⟧ ∈ f154(app(⟦Eq.{1}⟧, ⟦N.{}⟧), ⟦add.{}⟧, ⟦N.zero.{}⟧, ⟦N.{}⟧)
```

`f154`'s last argument is the domain `⟦N⟧` — it is the `chi` symbol for
`∀ n : N, …`. `cond_app` at any `ā ∈ ⟦N⟧` then `cond_elim` gives
`⊢ ⟦add a zero⟧ = ā`. (In the dump, `⟦Eq.refl.{1}⟧` etc. are the printer's
alias for `•`; every proof denotes `•`.)

### The qualifications, stated exactly

1. **Per ground level instantiation.** `direct::build` substitutes ground levels
   (`direct.rs:237`, `ground::subst_ground`) and refuses a symbolic one
   (`Gap::SymbolicLevel`). A universe-polymorphic Lean theorem is cashed once
   per scheduled σ, never once-and-for-all. This is how the whole checker works;
   it is not a restriction the `Eq` route adds.
2. **The cashed equation is hypothetical under the scope.** Under `∀ x : A` the
   result carries `x̄ ∈ ⟦A⟧` as a hypothesis. That is the universally-quantified
   form and is what `discharge` turns into a closed `∀`.
3. **Cashing is only as available as the proof's own typing.** In the same
   witness file, `notNot : ∀ b : Bool, bnot (bnot b) = b` came back
   `waiting on stuck-recursor(Bool.rec)` — the *proof term* had no typing, so
   there was nothing to cash. Nothing about `Eq` failed; a `Prop`-motive
   recursor did. Any plan that depends on plucking a theorem depends on mini
   typing the proof that theorem is built from.
4. **The result is an equation between interpretations, not a Lean conversion.**
   That is exactly what a `derived/` model construction consumes, and it is the
   same shape mini's own definitional-equality certificates have (the dump's
   `defeq ⊢ ⟦a⟧ = ⟦b⟧` lines). **A propositional Lean theorem and a definitional
   one produce the same kind of certificate.** This is the finding that makes
   the rest of this document worth reading.

---

## 1. Where the code actually is

The leads were **right about location and roughly right about size**:

* `leanprover-community/lean`, `src/library/inductive_compiler/` — correct.
* File list `add_decl / basic / compiler / ginductive / mutual / nested / util` —
  correct, plus `ginductive_decl.{h,cpp}` and `init_module`.
* `nested.cpp` is the large one — correct: 2388 lines of 4693 total. `mutual.cpp`
  is 940, `ginductive.cpp` 432, `basic.cpp` 188, `util.cpp` 136; everything else
  is under 130.
* "a pack/unpack construction" — correct, and the names are literally `pack` and
  `unpack`, at three layers (§2.3).

What the leads got **wrong**:

* There is no accompanying paper or design note. `doc/` has no inductive-compiler
  document; the only prose is the 25-line comment block at `nested.cpp:52-77`
  (about δ-reduction invariants and simp performance) and the stage banners
  inside the file. Author line: Daniel Selsam, 2016.
* Function names guessed in the brief — `mk_index_type`, `mk_putative_typed_expr`,
  `to_lhs`, `to_rhs` — **do not exist anywhere in the Lean 3 source**. The real
  ones are `to_sigma_type`, `mk_sum`, `to_maker`, `to_putter`, `mk_put_rest`,
  `compute_new_ind`, `translate_ir` (mutual side) and `find_nested_occ`,
  `pack_type`/`unpack_type`, `construct_inner_decl`, `build_primitive_pack_unpack`,
  `build_nested_pack_unpack`, `build_pi_pack_unpack`, `build_nested_recursor`
  (nested side).

**Staging.** `compiler.cpp:20-38`: nested is tried **first**, then mutual, then
basic. So a nested declaration is rewritten into a *mutual* block, which is then
rewritten into a *single indexed* inductive, which is the only thing the kernel
sees. The recursion is literally `nested.cpp:279` calling
`add_inner_inductive_declaration` back into `compiler.cpp`.

---

## 2. The algorithm, as declarations

Running example throughout, because it is the one the checked-in test output
pins (`tests/lean/non_exhaustive_error.lean.expected.out:24`):

```lean
inductive term | mk : ℕ → list term → term
```

### 2.1 Stage order

`nested.cpp:2317-2345`, `operator()`:

```
find_nested_occ()                 // 463  — bail out (to the mutual/basic path) if none
construct_inner_decl()            // 688
add_inner_decl()                  // 278  — recurses into compiler.cpp → mutual → basic
check_elim_to_type()              // 287
check_prove_inj()                 // 301
define_nested_inds()              // 743
define_nested_sizeof_has_sizeof() // 770
build_primitive_pack_unpack()     // 1257
define_nested_irs()               // 916  — calls pack_ir_arg → build_pi_pack_unpack
define_nested_sizeof_spec()       // 827
define_nested_recursors()         // 1830
define_nested_cases_on()          // 1990
define_nested_injectives()        // 2278
```

### 2.2 The inner declaration (`construct_inner_decl`, `nested.cpp:688-741`)

For each user inductive `Tᵢ` a renamed copy `nest(Tᵢ)` with the *same* type and
with each constructor's type run through `pack_type` (line 697); then **one extra
member, the "mimic"**: a fresh copy of the container the nesting happened in,
specialised to the nested occurrence's parameters.

```
m_nested_occ  = list term                              // find_nested_occ_in_ir_arg_type_core:530
m_replacement = _nest_1_1.list.term                    // :537, via mk_inner_name
mimic type    = update_result_sort(type of `list term`, result level of `term`)   // :715
```

`pack_type = pack_constants ∘ pack_nested_occs` (`:685`) rewrites (a) every
occurrence of a user inductive/constructor to its `nest(·)` name, and (b) every
occurrence of the whole applied `m_nested_occ` to `m_replacement`. `unpack_type`
is the inverse (`:686`).

Name mangling (`nest`, `:179-207`; `mk_inner_name`, `:209-220`): prefix
`_nest_<nest_depth>_<k>`. For a user ind/ir, `nest(n)`. For a foreign atomic name
`list`, `nest(list ++ T₀)` = `_nest_1_1.list.term`. For a foreign qualified name
`list.cons`, `nest(list ++ T₀ ++ "cons")` = `_nest_1_1.list.term.cons`.

So for `term` the inner decl is the **mutual block**

```
_nest_1_1.term            : Type
_nest_1_1.list.term       : Type
_nest_1_1.term.mk         : ℕ → _nest_1_1.list.term → _nest_1_1.term
_nest_1_1.list.term.nil   : _nest_1_1.list.term
_nest_1_1.list.term.cons  : _nest_1_1.term → _nest_1_1.list.term → _nest_1_1.list.term
```

which `mutual.cpp` then collapses to the **one kernel inductive**

```
_nest_1_1._nest_1_1.term._mut_ : psum unit unit → Type
```

with constructors `..._mut_.mk_0`, `..._mut_.nil_1`, `..._mut_.cons_1`. That
double `_nest_1_1._nest_1_1.` and the `_0`/`_1` suffixes are visible in the
checked-in expected output, and they are the whole confirmation that the two
stages compose as described.

**Restrictions enforced while finding the occurrence**
(`find_nested_occ_in_ir_arg_type_core`, `:500-543`):

* the occurrence may only be inside **parameters** of another inductive, never
  an index (`:540`) and never anywhere else (`:542`);
* the container may not itself be a mutual inductive (`:707`);
* the nested occurrence's result universe **must equal** the declared type's
  result universe (`:520-526`) — `inductive T : Type 1 | mk : List T → T` is
  rejected;
* the container and the new type must agree on large elimination
  (`check_elim_to_type`, `:287-299`).

### 2.3 The pack/unpack tower — three layers

The two directions are always built together, and always in the same shape:
motive `λ indices _, <other side> indices`, minors one per container constructor,
built from the container's **dependent recursor**.

| layer | built by | name (running example) | when |
|---|---|---|---|
| **primitive** | `build_primitive_pack_unpack`, `:1257-1440` | `term.primitive.pack`, `term.primitive.unpack` | exactly once, for the nested occurrence itself |
| **nested** | `build_nested_pack_unpack`, `:1030-1256` | `term.nested.pack_<ir>_<arg>_<k>` | when the occurrence sits *inside* a further container, e.g. `vec (list foo) n` |
| **pi** | `build_pi_pack_unpack`, `:964-1029` | `term.pack_<ir>_<arg>`, `term.unpack_<ir>_<arg>` | once per constructor argument that needs packing, wrapping the layer below through the argument's own Π-telescope |

Naming (`:163-177`): `mk_pi_name` is `<T₀ name> ++ <"pack"|"unpack"|"pack_unpack"|"unpack_pack"|"sizeof_pack"> ++ "_<ir_idx>_<ir_arg_idx>"` — note it carries **no** `pi` component, which is why the observed name is `term.pack_0_1` (ind 0, ctor 0, argument 1 = the `list term` field). `mk_nested_name` inserts a `nested` component and appends `_<nest_idx>`. `mk_primitive_name` inserts a `primitive` component and takes no indices.

For the running example only the **pi** and **primitive** layers are
instantiated; the nested layer has zero instances. `build_nested_pack_unpack`
short-circuits to the primitive pair when the container is the nested occurrence
itself (`:1031-1032`).

Types:

```
term.primitive.pack   : list term → _nest_1_1.list.term
term.primitive.unpack : _nest_1_1.list.term → list term
term.pack_0_1         : list term → _nest_1_1.list.term          -- := fun x => primitive.pack x
term.unpack_0_1       : _nest_1_1.list.term → list term
```

Bodies (`:1409-1420`, `:1155-1165`, `:1020-1021`): `primitive.pack` is
`list.rec` at motive `λ _, _nest_1_1.list.term` with minors rebuilding the mimic
constructors and recursing via `primitive.pack`; `primitive.unpack` is the
*mimic*'s recursor the other way. All four are marked
`reducible_status::Irreducible` immediately after definition (`:1422-1423`,
`:1163-1164`, `:1024-1025`).

### 2.4 The user-facing declarations

* `define_nested_inds` (`:743-758`): each user type is a **definition**
  `term := _nest_1_1.term`. It is not an inductive.
* `define_nested_irs` (`:916-952`): each constructor is a **definition** at its
  *declared* type whose body is the inner constructor with each packable
  argument wrapped: `term.mk := λ n l, _mut_.mk_0 n (term.pack_0_1 l)`. Exactly
  what the expected-output line shows.
* `define_nested_recursors` (`:1830-1846`) and `define_nested_cases_on`
  (`:1990-2006`) — §4.
* `define_nested_sizeof_*` (`:770-909`) and `define_nested_injectives`
  (`:2278-2306`) — equation-compiler / simp support, not kernel-relevant.

### 2.5 One declaration-adding helper is unsound-by-fallback

`define_theorem` (`:370-383`) tries the proof, and **on failure adds the
statement as an axiom**:

```cpp
} catch (exception & ex) {
    lean_trace(...);
    m_env = module::add(m_env, check(m_env, mk_axiom(n, to_list(...), ty)));
}
```

Every propositional lemma in §3 goes through this. `tests/lean/run/nested_inductive.lean:1`
turns the failure trace on, which is a strong hint the path was reachable in
practice. **Do not port this.**

---

## 3. Definitional vs propositional — the hinge

### Definitional, by construction (no declaration asserts them)

* `term ≡ _nest_1_1.term ≡ _mut_ (psum.inl punit.star)` — δ through two `def`s.
* `term.mk n l ≡ _mut_.mk_0 n (term.pack_0_1 l)` — δ.
* `_nest_1_1.term.rec`'s ι rule — holds by δ+ι on the aux type; nothing is
  emitted for it (this is `mutual.cpp`'s output, and it is forced by the kernel
  `check` at `mutual.cpp:782`, but no source line states it).

### Proved as theorems, and their proofs

All of these are `mk_definition_inferring_trusted(..., /*is_trusted=*/true)` —
Lean 3 `definition`s whose *type* is an `Eq`, added through `define_theorem`.

| statement | site | proof |
|---|---|---|
| `nested.pack (c a⃗) = c' (…)` — one per container ctor | `:1240-1246` | `mk_eq_refl` — **`rfl`** |
| `primitive.pack (c a⃗) = c' (…)` — one per container ctor, both directions | `:1423-1428` | `force_recursors` (`:1441-1548`), a simp-level ι forcing, because `pack` was just made irreducible; morally `rfl`, syntactically a built proof |
| `term.primitive.pack_unpack : ∀ x : _nest_1_1.list.term, pack (unpack x) = x` | `:1621-1631` | `prove_by_induction_simp` — **induction + simplifier. Propositional.** |
| `term.primitive.unpack_pack : ∀ x : list term, unpack (pack x) = x` | `:1633-1643` | same. **Propositional.** |
| `term.nested.pack_unpack_k`, `…unpack_pack_k` | `:1675-1698` | same. **Propositional.** |
| `term.pack_unpack_0_1`, `term.unpack_pack_0_1` | `:1759-1782` | `prove_by_funext` over the layer below (`:1729-1758`). **Propositional.** |
| `…sizeof_pack` at all three layers | `:1645`, `:1699`, `:1783` | induction + simp. Not kernel-relevant. |
| `term.mk.inj` / `.inj_arrow` / `.inj_eq` | `:2278-2306` | tactic proofs. Not kernel-relevant. |

The two pi-layer round trips are registered as **`inverse` lemmas**
(`add_inverse_lemma`, `:1767` and `:1779`) — this is what lets the equation
compiler and the `cases` tactic later rewrite the stuck `eq.rec`s of §4.

**This is the answer to "propositional is the point".** Lean 3 does exactly what
the brief hoped: it proves the round trips as theorems and does not need them
definitionally. What the brief did *not* anticipate is where the price is paid —
see §4.

---

## 4. The recursor it produces

`define_nested_recursors` (`:1830-1846`) and `build_nested_recursor`
(`:1848-1885`).

**Type.** `Pi(params, unpack_type(<type of the inner recursor>))`. The inner
recursor here is `_nest_1_1.term.rec`, which `mutual.cpp` produced. So:

```
term.rec : Π {C : term → Sort ℓ},
           Π (mk : Π (n : ℕ) (l : list term), C (term.mk n l)),
           Π (x : term), C x
```

**One motive. Minors only for `term`'s own constructors. No induction hypothesis
for the nested `list term` field. No second recursor.**

That last sentence is the structurally load-bearing one and it comes from
`mutual.cpp`, not `nested.cpp`. `mutual.cpp:674`:

```cpp
if (!cases_on && m_mut_decl.is_ind_app(ir_arg, ind_idx, inner_indices)) { /* push an IH */ }
```

`is_ind_app(e, ind_idx)` matches only member `ind_idx`. Arguments typed at a
*sibling* member get no IH; in the aux recursor's minors they receive a dummy
binder of type `Π …, punit` and it is dropped (`mutual.cpp:745-751`, with the
comment *"We only pass recursive arguments of the inductive type in question to
the minor premise"*). Non-selected members' minors return `punit.star`
(`mutual.cpp:760`) and the motive returns `punit` on their branches
(`mutual.cpp:604, 614`).

**Body** (`:1877-1884`): the inner recursor at the same motive, the same indices
and the same major, with each minor premise rewritten by
`build_nested_minor_premise_fn` (`:1911-1985`). For an argument that needed
packing, the rewrite is (`:1962`):

```
mk_eq_rec( motive := λ a, C (inner_ctor … a …),
           rest   := <minor applied to unpack a>,
           proof  := term.pack_unpack_0_1 a )
```

### **The ι rule of `term.rec` is NOT definitional**

Trace it: `term.rec C mp (term.mk n l)` δ-reduces to
`_mut_.rec C' mp' (_mut_.mk_0 n (pack_0_1 l))`, which ι-reduces to
`mp' n (pack_0_1 l)`, which is

```
eq.rec (motive := λ a, C (_mut_.mk_0 n a))
       (mp n (unpack_0_1 (pack_0_1 l)))
       (pack_unpack_0_1 (pack_0_1 l))
```

The major of that `eq.rec` is a **theorem constant applied to an argument**, not
`eq.refl`. It is stuck. `term.rec C mp (term.mk n l) ≢ mp n l`.

Lean 3 recovers it *propositionally*: `prove_eq_rec_invertible` in
`equations_compiler/util.cpp:437-462` documents precisely this pattern —

```
If e is (@eq.rec B (f (g (f a))) C (h (g (f a))) (f a) (f_g_eq (f a)))
… Return (h a) **and a proof that (e = h a)**
```

using the two `inverse` lemmas registered at `nested.cpp:1767,1779`. `nested.cpp`
carries its own copy of that trick (`force_eq_rec`, `:1459-1548`) for the pack
spec lemmas. **No definitional ι rule for a nested recursor exists anywhere in
Lean 3.**

For a constructor with *no* packable argument the wrapper is skipped
(`:1936-1937`) and that constructor's ι rule *is* definitional. So the failure is
per-constructor, exactly at the nested fields.

`cases_on` (`:1990-2087`) is the same construction without IHs; `mutual.cpp:848`
also puts its minors **after** the major, so its argument order differs from
`rec`'s.

---

## 5. Does that match Lean 4's exported shape? **No — not remotely.**

Measured on the pinned toolchain (Lean v4.29.1, lean4export `caccfbe`, format
3.1.0), `inductive Tree | leaf | node : List Tree → Tree`:

```json
{"all":[21],"ctors":[22,23],"isRec":true,"isReflexive":false,"numIndices":0,
 "numNested":1,"numParams":0,...}                                    // Tree
{"name":24,"numMinors":4,"numMotives":2,"rules":[{"ctor":22,...},{"ctor":23,...}]}  // Tree.rec
{"name":29,"numMinors":4,"numMotives":2,"rules":[{"ctor":3,...},{"ctor":4,...}]}    // Tree.rec_1
```

with ctors 3/4 = `List.nil`/`List.cons` — name ids from a *different* inductive
block. Both recursors carry `all = [Tree]`. Types:

```
Tree.rec   : ∀ {motive_1 : Tree → Sort u} {motive_2 : List Tree → Sort u}
             (leaf : motive_1 Tree.leaf)
             (node : ∀ a : List Tree, motive_2 a → motive_1 (Tree.node a))
             (nil  : motive_2 (List.nil Tree))
             (cons : ∀ (a : Tree) (a : List Tree), motive_1 a → motive_2 a →
                     motive_2 (List.cons Tree a a)),
             ∀ t : Tree, motive_1 t
Tree.rec_1 : <same six binders>, ∀ t : List Tree, motive_2 t
```

The docs' claim is **confirmed exactly**, with one wording correction: `numMinors = 4`
is specific to the two-constructor `leaf | node` shape (2 for `Tree` + 2 for `List`).
For the single-constructor `Tree | node : List Tree → Tree` it is 3. `numMotives = 2`
holds for both. No auxiliary type appears anywhere in the export — the full name
table of the unfiltered export is `List, List.cons, List.nil, List.rec, List.recOn,
Tree, Tree.node, Tree.rec, Tree.recOn, Tree.rec_1` plus binder names.

For comparison, genuinely mutual `A`/`B` exports as **one** `Declar::Inductive`
block with two `InductiveVal`s, both carrying `all = [A,B]`, `numNested = 0`, and
two recursors `A.rec`/`B.rec` at `numMotives = 2`, `numMinors = 3`.

### Side by side

| | Lean 4 export | Lean 3 output |
|---|---|---|
| `Tree` | primitive `Declar::Inductive`, `numNested = 1` | a `def` for `_nest_1_1.term` |
| kernel inductives introduced | `Tree` itself; `List` untouched | one, `_nest_1_1._nest_1_1.term._mut_ : psum … → Type`, with a **specialised copy of `List`** as a member |
| motives on `Tree.rec` | **2** (`Tree` and `List Tree`) | **1** |
| minors | 4 (both types' ctors) | 2 (`Tree`'s only) |
| IH on the `List Tree` field | yes, `motive_2 a` | **none** |
| second recursor `Tree.rec_1` | yes, primitive, ι-reduces on `List.nil`/`List.cons` | **does not exist, and nothing in the construction produces it** |
| ι rule for `Tree.node` | primitive kernel rule | **propositional only** (stuck `eq.rec`) |
| `List Tree` in constructor field types | the real `List Tree` | the real `List Tree` in the *declared* types, the mimic `_nest_1_1.list.term` in the *bodies* |

**Conclusion: porting Lean 3's construction would not subsume nested handling and
would not subsume mutual handling either.** It produces neither of the two
declarations Lean 4's export asks a checker to certify.

---

## 6. How much is Lean-3-specific

**Fatal to a direct transcription:**

1. **`Tree` is a `def` in Lean 3 and an `Inductive` in Lean 4.** The entire
   construction rests on the user-facing type being δ-equal to the aux type, so
   that `Tree.mk`'s declared type typechecks against a body built from the aux
   constructor. Lean 4 hands us `Tree` as a primitive inductive; we cannot
   redefine it. This is the same wall `checker/tests/mini_nested.rs` documents from the
   other side.
2. **Lean 3 has no `Tree.rec_1` to produce.** Lean 4's export *declares* one and
   a checker must certify its ι rules. Lean 3's algorithm has no notion of it.
   It would have to be invented (§8).
3. **Lean 3's per-member recursor is weaker than Lean 4's** (§4). Lean 4's mutual
   `A.rec` has one motive per member and IHs across members; Lean 3's has one
   motive and self-IHs only. `checker/src/mini/mutual_aux.rs` already builds the *Lean 4*
   shape; Lean 3's would be a regression.
4. **Universe rigidity.** The nested occurrence must live at the *same* result
   universe (`:520-526`) and must agree on large elimination
   (`check_elim_to_type`). Lean 4 has no such restriction and the corpus will
   contain declarations Lean 3 would have rejected outright.
5. **The proofs are tactic scripts.** `prove_by_induction_simp` runs the
   `induction` tactic and then `sizeof_simplify_fn` with a simp-set. There is
   nothing to transcribe: the *statements* are the transferable content, the
   proofs are not. Plus the axiom fallback (§2.5).

**Survives, and is the transferable content:**

* the **shape** of the reduction: nested ⇒ mutual block `{T…, mimic-of-container}`,
  where the mimic is the container specialised to the occurrence's parameters;
* the **three-layer pack/unpack tower** and its type signatures;
* the **lemma inventory**: per-constructor `pack`/`unpack` spec equations (`rfl`)
  plus `pack_unpack`/`unpack_pack` round trips (propositional), at each layer;
* the observation that the round trips are enough — you never need
  `unpack (pack l) ≡ l`.

**Not load-bearing either way:** structure η. The packing uses `cases_on` and
recursors throughout (`psigma.cases_on`, `psum.cases_on`, `punit.cases_on` in
`mutual.cpp:526-628`), never projections, so nothing in the construction depends
on Lean 4's definitional structure η. `Prop`/`Type` differences show up only in
`check_elim_to_type` and in `mutual.cpp:864-865`'s `elim_to_prop` branch, both of
which are guards rather than steps.

---

## 7. Mutual: what Lean 3 does, and how `mutual_aux.rs` compares

Lean 3 (`mutual.cpp`, entry `operator()` at `:885-910`):

* one aux inductive `<common prefix> ++ <T₀ full name> ++ "_mut_"`, with the
  block's parameters and **exactly one index**;
* the index type is `psum I₀ (psum I₁ (… I_{n-1}))` (`mk_sum`, `:79-85`) where
  each `Iⱼ` is the member's own index telescope packed as a right-nested `psigma`
  terminated by `unit` (`to_sigma_type`, `:65-73`) — so the tag is **unary
  `psum.inr` nesting**, not a `Nat`, and the member's indices ride inside it;
* `to_putter` (`:144-159`) builds `inr^j (inl idx)`; `to_maker` (`:97-126`)
  builds the `psigma` chain; `ginductive.cpp:49-67` decodes by counting `inr`s;
* constructor names: `<aux> ++ <last component of the ctor name> ++ "_<ind_idx>"`
  — `foo.mk` (member 0) becomes `foo._mut_.mk_0`;
* `foo_j := λ p⃗ ix⃗, aux p⃗ (put_j (mk_j ix⃗))` (`:286`), `foo_j.ir := aux.ir_k`
  (`:492`), `foo_j.rec` and `foo_j.cases_on` as `def`s (`:782`, `:856`);
* **no theorem is ever generated for a recursor rule** — `mk_eq`/`mk_eq_refl`
  occur in `mutual.cpp` at exactly lines 418 and 419, both inside
  `sizeof_spec`. The rules hold by δι and are relied on silently.

`checker/src/mini/mutual_aux.rs`, today:

```text
inductive Tag (p⃗)        : Sort W          -- Tag.tᵢ : ∀p⃗ ix⃗ᵢ, Tag p⃗
inductive Aux (p⃗)        : Tag p⃗ → Sort u  -- every ctor of every member
def Tᵢ                   := fun p⃗ ix⃗ᵢ => Aux p⃗ (Tag.tᵢ p⃗ ix⃗ᵢ)
def Tᵢ.ctorⱼ             := fun p⃗ f⃗ => Aux.cᵢⱼ p⃗ f⃗
def Mot                  := fun p⃗ m⃗ => Tag.rec p⃗ (fun t => Aux p⃗ t → Sort v) m⃗
def Tᵢ.rec               := fun p⃗ m⃗ k⃗ ix⃗ᵢ t => Aux.rec p⃗ (Mot p⃗ m⃗) k⃗ (Tag.tᵢ p⃗ ix⃗ᵢ) t
theorem Tᵢ.rec._auxRuleⱼ : <zone A's rule> := Eq.refl _
```

| | Lean 3 `mutual.cpp` | `mutual_aux.rs` |
|---|---|---|
| tag carrier | `psum`/`psigma`/`punit` from the prelude | a purpose-built `Tag` inductive |
| where indices live | inside the tag (`psigma` chain) | inside the tag (`Tag.tᵢ`'s fields) — **the same idea** |
| aux indices | 1 | 1 |
| recursor built at | Lean 3's own weaker single-motive type | **zone A's declared type**, read from `ConstantInfo::Recursor` |
| IHs across members | **no** | yes |
| rule certificate | none; relied on silently | `theorem … := Eq.refl _`, nine fixtures certifying |
| motive packing | `psum.cases_on`+`psigma.cases_on`+`punit.cases_on` nest | `Tag.rec` at the packed motive |

**`mutual_aux.rs` is a strict improvement on `mutual.cpp` and there is nothing in
`mutual.cpp` worth importing.** The one idea they share — put the index telescopes
in the tag — landed here already (commit `5f65268`).

---

## 8. The owner's two fallbacks, costed

The shapes are settled (§5): Lean 3's generated recursors do **not** match Lean
4's, so the risk fired. Both fallbacks stay open.

**(a) Adapt the translation so the generated recursors come from the existing
nanoda-inherited code.** Cost: this means treating `Tree.rec`/`Tree.rec_1` as
declared by the export (which they are) and building their interpretations from
a `derived/` carrier for `⟦Tree⟧`. That is the route
`checker/tests/mini_nested.rs:41-46` already scopes: `⟦Tree⟧` as the initial algebra of
`X ↦ 1 + ⟦List⟧ X` over the **real** `⟦List⟧`, with `⟦Tree.rec⟧`, `⟦Tree.rec_1⟧`
and their ι theorems built in `derived/`. Nothing from Lean 3 is reused except
the confirmation that the two-motive shape is what has to come out. Estimated
shape: a new `derived/` construction of `wtype`/`wrec` size, plus a `mini` zone
for `numNested > 0`.

**(b) Run both translations — one for the model, one for the recursor types —
then prove the ι rules of the recursors we want, in the model, in Lean world.**
This is the one §0 makes viable, and the concrete plan is:

1. Synthesise, in Lean terms, the Lean 3 construction: the mutual block
   `{Tree, mimicList}` (which `mutual_aux.rs` already encodes), `primitive.pack`,
   `primitive.unpack`, the per-constructor spec lemmas (`Eq.refl`), and the two
   round trips `pack_unpack` / `unpack_pack`.
2. **The round trips have to be proved by `List.rec`/`mimic.rec` and `congrArg`
   as synthesised proof terms, not by tactics.** This is the real cost of (b),
   and it is the step Lean 3 discharges with a simplifier. The statements are
   §3's table; the proof terms are induction with a `congrArg` per constructor
   field — the `addZero` witness in §0 is that pattern at arity 1.
3. Define, as Lean terms, `Tree.rec` and — *this Lean 3 does not do* —
   `Tree.rec_1`:
   ```
   Tree.rec_1 mots mins ... (t : List Tree) :=
     Eq.rec (motive := fun y => motive_2 y)
            (aux.rec_mimic … (primitive.pack t))
            (primitive.unpack_pack t)
   ```
4. Run the whole synthesised development through the existing pipeline, take
   `⟦Tree⟧ := ⟦_mut_ (tag Tree)⟧` etc. as the interpretations of the *exported*
   constants, and prove each declared ι rule as a TG equation by **cashing** the
   corresponding round-trip theorem (§0). The stuck `eq.rec` that defeats Lean 3
   (§4) is not an obstacle here, because mini's obligation is a TG equation and
   not a Lean conversion.

Cost of (b) relative to (a): (b) reuses `mutual_aux.rs` and the existing
interpretation of `List`, and its novel content is ~6 synthesised proof terms per
nesting plus one new adoption path in `zoneb`. (a) needs a new `derived/`
initial-algebra construction but produces the recursors directly and owes no
proof terms. (b)'s risk is step 2 — every synthesised proof must itself get a
typing from mini, and §0's caveat 3 says that is not automatic. (a)'s risk is
size.

**Not choosing between them.** What the archaeology adds is: (b) is *not*
blocked by the propositional round trip, and Lean 3 supplies the statement list
for step 2 verbatim.

---

## 9. What I could not settle from the source

* **Whether Lean 3's `define_theorem` axiom fallback ever fires on realistic
  input.** `tests/lean/run/nested_inductive.lean:1` enables the failure trace,
  which suggests it did, but I did not build Lean 3 and did not run it. The code
  path exists; its frequency is unknown.
* **The exact `psum`/`psigma` index term for the running example.** I read
  `to_sigma_type`/`mk_sum`/`to_putter` and the decoder, and the checked-in
  expected output confirms the *names*; I did not obtain a printed index value
  for a nested type. `psum unit unit` for `term` is a reading of the code, not an
  observation.
* **Whether Lean 3's equation compiler ends up with `rfl`-provable equations for
  functions over nested types.** `prove_eq_rec_invertible` returns a proof, so
  they are propositional, but I did not trace the `eqn_lemmas` registration to
  confirm none is marked `rfl`.
* **Nothing was measured about Lean 3's export format for these declarations.**
  `doc/export_format.md` has `#DEF`/`#AX`/`#IND`; the pack/unpack functions and
  round trips are `definition`s and would export with their values, and the
  axiom fallback would export as `#AX`. Not verified against a real Lean 3
  export.
* **`define_nested_sizeof_spec` (`:827-909`) and `define_nested_injectives`
  (`:2278-2306`) were read only for their classification** (equation-compiler /
  simp support), not line by line.

---

## Appendix: files read

`src/library/inductive_compiler/{nested,mutual,basic,util,compiler,add_decl,ginductive,ginductive_decl}.{cpp,h}`,
`src/library/equations_compiler/util.cpp:423-520`, `src/library/inverse.h`,
`tests/lean/non_exhaustive_error.lean{,.expected.out}`,
`tests/lean/run/{nested_inductive,cases_nested}.lean`.

On this side: `mini/src/{direct,interp,kernel,quot_classes,recursor,mutual_aux}.rs`,
`derived/src/prop.rs`, `checker/tests/mini_nested.rs`,
`checker/tests/fixtures/nested_roundtrip.lean`, and live runs of
`mini --dump-theorems` on `vendor/arena-tests/good/tutorial/{040_eqType,
073_boolRecEqns,076_listRecReduction,077_RBTree.id_spec,094_ruleK,
122_quotLiftType,124_quotLiftReduction}.ndjson` plus a purpose-built export.
