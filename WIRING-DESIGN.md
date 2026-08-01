# Wiring the general inductive translation into the checker — design

Task #26, 2026-08-01. Design only; no code, no builds (tree is mid-edit by five
concurrent agents). Written against: `derived/src/inductive/` **with the
general recursor landed** (RECURSOR-DESIGN.md §10 addendum: rungs 1–4 done;
`GenRecursor` at `recursor.rs:82` with `build/step_of/rec_of` and
`carrier_at`, (S1)–(S4) exercised at the witness shapes including interleaved
masks in `derived/tests/genrec.rs`), `checker/src/tg.rs` (the three shape
recognisers, the `RecNest`/`RecBottom`/`derive_iota` stack,
`ind_syms`/`ctor_rules`), `checker/src/{tc,util,instantiations}.rs`,
`RECURSOR-DESIGN.md` including §10, `LEVEL-POLYMORPHIC-INDUCTIVES.md`,
`INDUCTIVES.md`, `LIBRARY-BACKLOG.md`.
Markers as in `RECURSOR-DESIGN.md`: **[read]** (checked against code),
**[believed]** (argued, not derived), and §12 collects what I could not
settle. Interface names on the recursor side may drift — two agents are in
those files now; the arguments do not depend on the names.

---

## 0. Verdict up front

1. **The `FnSym` boundary is real, cheap per symbol, and has one genuinely
   dangerous property nobody has stated yet: symbol stability across
   backends.** A `TgBackend` is built and dropped per declaration
   **[read**, `tg.rs:3919`**]**, and `ind_syms` lives on the backend, not on
   `Shared` **[read**, `tg.rs:3758`**]** — so a `βⱼ` body that mentions
   `⟦Bool⟧` names a *per-backend* symbol, and a general `Inductive` cached
   per-thread would be a package of theorems about symbols the next
   declaration's backend never produces. §3.4 is the fix (move the inductive
   abbreviation store to `Shared`, guarded, following the `const_syms`
   precedent), and it must land **before** anything is cached, not after the
   first confusing measurement.
2. **The eliminator branch is decidable from declaration data alone** and the
   right predicate is a three-line syntactic `provably_nonzero` on the
   declaration's **own** resultant level expression — never on the
   σ-instantiated numeral (§4). This replaces "not syntactically
   `Level::Zero`" and closes the recorded `Sort ℓ → Sort ℓ` hazard.
3. **Per-instantiation needs no change to `instantiations.rs`'s schedule or to
   `tc.rs`** — with **one exception the prior designs missed**: the pre-pass
   collects an `Inductive` declaration's constant edges from its *type only*
   **[read**, `instantiations.rs:410–418`**]**, and the spec builder interprets
   every constructor's field types, so without extending pass A to
   constructor types the unpredicted-instantiation audit row — currently
   pinned at zero by a test — can go nonzero (§7.3). This contradicts
   `RECURSOR-DESIGN.md` §6's "no change to `instantiations.rs` is needed" in
   the letter, though not in the spirit (the schedule shape is unchanged; one
   collection loop gains a case).
4. **Task #22 has landed in this tree**: `ctor_rules` is keyed
   `(NamePtr, Vec<Term>)` with the two-level fixture test cited in its doc
   comment **[read**, `tg.rs:3781`, `3759–3780`**]**. This design assumes the
   fixed key and adds nothing there.
5. **The two-step landing is forced, and step two has a blocker that #26's
   scope statement does not mention**: `derived::cumul`'s chain demands
   fibres `B(a) ∈ ω` *on the nose* **[read**, `cumul.rs:252–253`**]**, and the
   general carrier's fibres are `finord(m) = Sum_m(1,…,1)`, which is **not** a
   von Neumann numeral (`isum/symbols.rs:246` — the recorded `finord(1) ≠ 1`
   trap). So cutting `Bool`/`N`/`Unit`/`Empty` over to the general carrier
   silently loses the four `⟦T⟧ ∈ ⟦Type 0⟧` theorems (`ind_ty_u1`,
   `tg.rs:5155`) unless cumul is generalised first. §8 sequences around this;
   §11 says what it means for #26 as scoped.
6. **`RBTree` is an indexed family and out of scope** — `042`'s declaration
   is `RBTree : Sort u → Color → N → Sort _` with `numIndices: 2`
   (RECURSOR-DESIGN §10, from the export). Everything downstream follows:
   `077`'s ι gaps do **not** close via this work, the "wire RBTree first"
   recommendation is void, and the wiring must **positively decline** it —
   indices are unrepresentable in `DeclSpec`, so the decline lives in the
   checker-side spec builder (§3.2 step 1) with its own counted reason, not
   in `derived/`. The mask remains corpus-demanded, by the preludes:
   `Lean.Name.str` (`Rec,Plain`), `ParserDescr.sepBy/sepBy1`
   (`Rec,Plain,Rec,Plain`), `RArray.branch` (`Plain,Rec,Rec`),
   `Grind.CommRing.Expr.add/sub/mul` (`Rec,Rec`). First ι wiring target:
   **`Lean.Name.str`** on `init-prelude` (§8). The general lesson — twice
   bitten today (`116`'s function-typed field, now `042`'s indices): scope
   is read off the **declaration data** (`numIndices`, field shapes), never
   inferred from a file's reputation.
7. **Riskiest step overall**: the general `fire` (§6) — the same verdict as
   `RECURSOR-DESIGN.md` §8 rung 5, for the same reason: it is where derived
   `∀`-schemas meet nest-computed terms, which is where every recorded late
   surprise lived. Riskiest step *new to this design*: the spec builder's
   dependency discipline (§3.2–3.3), because a wrong `βⱼ` arity or a missed
   decline derives true theorems about the wrong declaration — caught by
   guards, but as diffuse gaps.

---

## 1. What is being replaced, and what replaces it

Checker side today **[read]**:

| piece | where | scope |
|---|---|---|
| `enum_arity` | `tg.rs:5435` | 0 params, 0 uparams, all-nullary, ≤ 2 ctors, not Prop |
| `nat_shape` | `tg.rs:5529` | exactly `N`'s shape, 0 uparams |
| `list_shape` | `tg.rs:5598` | exactly `List`'s shape, 1 uparam |
| `false_shape` | `tg.rs:5480` | the empty Prop — **kept**, it is the threat-model anchor |
| `ind_const`/`list_const` | `tg.rs:6050,6177` | mints abbreviations, registers `ind_mems`/`ctor_rules` |
| `enum_rec_shape`/`nat_rec_shape`/`list_rec_shape` + `rec_bottom` | `tg.rs:5804–5878` | recursor recognition |
| `RecBottom::{Enum,Nat,List}` + `fire_enum/nat/list` | `tg.rs:3906,9278,9343,9598` | the ι firing per shape |
| `Inductives`' `e0/e1/e2/nat/list*/cases/pf` fields | `tg.rs:3169` | the hand-written derived stacks |

Derived side, available now **[read]**:

```text
Machine::new(env)  /  Machine::over(env, wt, bnd)          machine.rs:74,82
Inductive::build(env, &mut machine, &spec)                 carrier.rs:148
  → closed, ty (FnSym arity np), ty_ax, carrier, wty,
    ctors[i].{mem, inj, hyp, term, args, recs}, distinct(i,j)
GenRecursor::build(env, &mach, &ind, rc, iota, funspace)   recursor.rs:111
  → steps, hyp (pointwise HYP), computes (S1), sv (S2),
    step_typed (S3), iota[i] (S4); step_of / rec_of
carrier_at(mach, ind, ps) → (A, B, u, W) at supplied terms recursor.rs:240
CtorSpec { args: Vec<FnSym>, recs, order: Vec<Slot> }      spec.rs — mask landed
```

Two composition facts that everything below leans on:

- `Wtype` and `Bound` are `Clone` **[read**, `wtype/apparatus.rs:38`,
  `bound/chain.rs:38`**]**, and `Machine::over` takes them by value. So the
  checker builds its `Machine` as
  `Machine::over(env, inds.wt.clone(), inds.bnd.clone())` and the machine's
  carriers, `RecCore` (built over `inds.wt`, `tg.rs:5287`) and the whole
  existing signature share one `W`/`fs`/pair/`U`. `GenRecursor::build` takes
  `RecCore`'s `r`, `iota`, `funspace` directly. **This is the single
  coordination point** `RECURSOR-DESIGN.md` §7.4 warned about, and it is
  satisfiable without touching `derived/`.
- The machine mints its **own** `Cases` (`rec₊`) and `PointFun`
  (`machine.rs:84`), distinct from `Inductives.cases`/`.pf`. Harmless —
  nothing may compose a hand-written carrier with a general one anyway
  (`RECURSOR-DESIGN.md` §7.5's seam) — but it is one more reason the cutover
  per inductive must be atomic: carrier + constructors + recursor together,
  never mixed.

---

## 2. Where the pieces live

New state, following the existing lazy/`Option<Option<…>>` discipline:

```text
Shared (per thread, tg.rs:3395):
  machine:  Option<Option<Rc<RefCell<Machine>>>>   // over inds.wt/bnd; RefCell
                                                   // because telescope/isum
                                                   // caches need &mut
  gen_inds: HashMap<(u32, Vec<Term>), Option<Rc<GenInd>>>
            // key: export-arena raw name + interpreted ground levels,
            // the const_syms convention (tg.rs:3494–3517)
  gen_recs: HashMap<(u32, Vec<Term>), Option<Rc<GenRecursor>>>
            // built lazily on first ι demand, RecCore precedent
  ind_syms moves here (§3.4)

struct GenInd {
  spec: DeclSpec,
  beta_bodies: Vec<Vec<Term>>,   // per ctor, the βⱼ defining bodies — the
                                 // guard for cache hits (§3.4)
  ind: Rc<Inductive>,            // theorems included — the memo rule
}

TgBackend (per declaration): no new fields beyond what nests already use;
RecBottom gains one arm:
  RecBottom::General { gi: Rc<GenInd>, gr: Rc<GenRecursor>, t_policy: TPolicy }
```

Borrow discipline: `Inductive::build` needs `&mut Env` and `&mut Machine`
simultaneously; both live in `Shared`, so the builder takes **one**
`borrow_mut()` and destructures (`let Shared { env, machine, .. } = &mut *sh`)
— never two nested `env_mut()`-style borrows. This is the one place the
existing `env_mut()` helper is not usable **[read**, the re-entrancy warning
at `tg.rs:3972–3978`**]**.

Failure caching: every `Option<Option<…>>`/`Option<Rc<…>>` above memoises
`None` — a declaration that declines once must not re-run the walk per
obligation (the `has_types`/`points` precedent).

---

## 3. The `FnSym` boundary — the central design

### 3.1 What must be produced

For inductive `T` with `np` parameters, used at ground levels `ℓ⃗`: a
`DeclSpec` whose `CtorSpec.args[j]` is a symbol `βⱼ` of arity `np + j` — the
parameters, then the **earlier non-recursive** fields only — such that
`βⱼ(p⃗, y₀…y_{j-1})` *is* the interpretation of the field's Lean type with the
binders opened at those variables. Substitution is then application
(`spec.rs:26–50`), which is the whole point: the kernel has `Formula::subst`
but no `Term::subst`, and every downstream instantiation is `ax_inst` at a
`∀`-statement, never a rewrite inside a term.

### 3.2 The builder, concretely

`fn decl_spec(&mut self, ctx, ind_name, levels) -> Option<Rc<GenInd>>`,
called from `ind_const` (and from `rec_bottom` via the inductive name). All
checks are **positive** — the builder verifies the covered shape, it does not
enumerate exclusions (`spec.rs:180`'s contract):

1. **Declaration-level scope checks**, off `InductiveData` only:
   `num_indices == 0`, `!is_nested`, `all_ind_names.len() == 1`,
   `levels.len() == uparams.len()`. Then the **eliminator branch** (§4) on the
   declaration's own resultant level. Any failure → decline with its own
   reason string. The `num_indices` check is not defensive boilerplate: it is
   what declines `RBTree` (`numIndices: 2` in the `042` export —
   RECURSOR-DESIGN §10), and because indices are *unrepresentable* in
   `DeclSpec` there is no derived-side backstop — this line is the whole of
   the scope enforcement for indexed families.
2. **Walk the inductive's own type** at
   `ctx.subst_expr_levels(ind.info.ty, ind.info.uparams, levels)` — exactly
   `rec_nest`'s discipline (`tg.rs:5909–5924`): open each of the `np`
   parameter binders at a `ctx.mk_unique` local, reserve a fresh kernel var
   per local via `self.locals`, interpret each binder type (these become the
   domains of the Lean-facing nest, §5). The codomain must be `Sort ℓ` (it
   is, given `num_indices == 0`; check anyway).
3. **Walk each constructor's type** at the same levels
   (constructor `uparams` are the inductive's). First `num_params` binders:
   check each binder type is *the same expression* as the corresponding
   parameter binder of the inductive (Lean guarantees it; verify, don't
   assume), and open them **at the same locals as step 2** so every
   constructor's `βⱼ` bodies and hypotheses are stated at one set of
   variables. Then per field, in declared order:
   - **Recursive field**: the binder type is the constant `T` at exactly
     `levels`, applied to the `np` parameter locals in order —
     `is_ind_at`'s check generalised to an `np`-spine. Push `Slot::Rec`; open
     the binder at a local whose kernel var is recorded but **never added to
     any abstraction list**.
   - **Function-typed recursive field** (binder type is a `Π` whose
     ultimate codomain is `T p⃗` — `RTree`, `Acc.intro`): **decline**, own
     reason. This test must run *before* any `interp` of the field type,
     because interpreting a self-mentioning type would recurse into
     `ind_const` on the inductive being built (§3.3).
   - **Plain field**: `body := self.interp(ctx, binder_type)`; then
     `define_abbrev(&mut env, &[p_vars…, earlier_plain_y_vars…], &body)`.
     Push the `FnSym` and `Slot::Plain`; open the binder at a local, kernel
     var **in** subsequent abstraction lists.
4. **Codomain check**: after the last field, the remaining expression is
   `T ℓ⃗ p₀ … p_{np-1}` on the nose. (Redundant given `num_indices == 0`;
   it is the cheap guard against a walk bug, so keep it.)
5. `DeclSpec::new(np, ctors)`, assert `well_formed()` (the derived side
   re-checks and declines otherwise — belt and braces), then
   `Inductive::build`.

**Cost note**: one `define_abbrev` per non-recursive field per (declaration,
levels) — `List.cons` contributes exactly the identity `β₀(p) = p` the spec
docs promise **[read**, a de Bruijn field opens at the parameter local and
interps to `Term::var(p₀)`**]**.

### 3.3 Failure modes at the boundary — every one a decline, never a claim

- **A later field depending on an earlier recursive field.** Not checked by
  hand: the recursive field's kernel var is simply absent from every
  abstraction list, and `kernel::thm::define` **refuses a body with free
  variables outside `xs`** **[read**, `derived/src/lib.rs:272–283`: "kernel
  enforces this … returns `None`"**]**. So the decline is automatic and
  sound; the builder's job is only to *count* it distinctly ("spec: field
  type depends on a recursive field") rather than let it fall into a generic
  `None`.
- **Field type mentioning constants with no interpretation.** `interp` is
  total — unknown constants become opaque per-thread symbols
  (`opaque_syms`). This is **not** a decline: `βⱼ` is a perfectly good symbol
  over an opaque body; the constructor's `H` hypotheses may then be
  undischargeable at use sites, which surfaces as conditional certificates or
  gaps downstream. Correct and honest.
- **Field type mentioning the inductive itself in a non-recursive position.**
  Positivity plus `!is_nested` forecloses the cases I can name, but a
  re-entrancy guard costs three lines: keep a `spec_active: Vec<NamePtr>` (the
  `const_active` pattern, `tg.rs:3717`) and decline on re-entry. **[believed**
  that it is unreachable; the guard makes it not matter**]**
- **`interp` classification changing under σ.** A field type that is a `Π`
  lands in `fs`/`dprod`/`chi`/undet by `body_clause` under the ambient σ —
  fine, because the whole spec is keyed per `(name, levels)` (§3.4) and at
  ground levels exactly one clause applies. No hedging needed.
- **Anything else `Inductive::build` dislikes** returns `None` → decline.

The cardinal property: **there is no code path from a decline to a `Thm`**.
Every decline leaves the constant opaque, exactly as today, and opaque
constants produce counted gaps.

### 3.4 Symbol stability — the hazard, and the fix

The problem stated in §0.1. Today's precedent: `opaque_syms`, `const_syms`,
`param_syms`, `idx_syms` were all moved to `Shared` keyed by
`(NamePtr::raw, levels)` precisely so that stored theorems survive backends
**[read**, `tg.rs:3494–3517`**]** — and `declar_typings` depends on that.
`ind_syms` was left per-backend, which was harmless while everything it fed
was rebuilt per backend anyway. The general path breaks that: `gen_inds`
must be per-thread (an `Inductive::build` per obligation would be absurd),
so every term reachable from a cached `Inductive` — the `βⱼ` bodies above
all — must be stated over per-thread-stable symbols.

Fix, in order:

1. **Move `ind_syms` to `Shared`**, keyed `(u32 raw, Vec<Term>)`, entries
   only for export-arena names (the established restriction). Per-backend
   `abbrev_defs` is *populated* from it on first touch (cheap `Thm` clone),
   so `unfolds_to`/`has_type_h` are unchanged. `ind_mems`/`ind_ty_mems` keys
   are term pairs and simply start hitting more often.
2. **Guard the `gen_inds` hit** the way `hoisted` is guarded
   (`tg.rs:3794–3798`): on lookup, re-interpret the field-type bodies and
   compare against the stored `beta_bodies`. A mismatch (an unstable symbol
   crept in — e.g. a temp-arena name) falls back to a **per-backend** build,
   never to using the stored package. Nothing is trusted from the cache; a
   stale entry costs a rebuild, not a wrong theorem.

The alternative — keying `gen_inds` by the interpreted body terms themselves
— was considered and rejected: it silently degrades to per-backend rebuild
frequency whenever any symbol is unstable, which is the failure mode made
invisible. The guard makes it visible (a counter on guard misses).

---

## 4. The eliminator branch, from `InductiveData`

Per `LEVEL-POLYMORPHIC-INDUCTIVES.md` §2–3 and thesis §2.6.2
(`thesis.txt:700–705`): the translation branch is fixed **per declaration**
by Lean's eliminator trichotomy, never by the instantiated sort. Concretely:

```text
provably_nonzero(l):           // on the declaration's OWN level expression,
  Succ _        → true         // read off ind.info.ty's trailing Sort,
  Max(a, b)     → provably_nonzero(a) || provably_nonzero(b)
  IMax(_, b)    → provably_nonzero(b)
  Zero | Param  → false
```

- `provably_nonzero` → class (T), the W branch: build the spec (§3).
- otherwise → **decline the W branch unconditionally**, with reason
  "spec: sort-ambiguous or Prop declaration (class S/P)". `False` keeps its
  own arm (`false_shape` first, unchanged); `Eq`/`And` keep the `prop.rs`
  subsingleton path, unchanged. `PUnit`/`PEmpty` (class S) stay uninterpreted
  until the `⊆ {•}` construction exists — that is
  `LEVEL-POLYMORPHIC-INDUCTIVES.md` §4.2's "small work", explicitly **not**
  in #26. Do not build a W-type for a possibly-Prop inductive even at a
  `Type` instantiation: soundness would survive (declines and guards), but
  the branch would be per-instantiation, which is the design error §3.3 of
  that note closes.

Two things this sharpens against today's code **[read]**:

- `enum_arity`/`nat_shape` test `matches!(…, Level::Zero)` after `simplify` —
  on *monomorphic* declarations that is equivalent to `!provably_nonzero`
  only because there are no parameters; `list_shape` tests the binder's
  `Sort ℓ` the same way and **would** admit a `Sort ℓ → Sort ℓ` list — the
  recorded hazard. The general recogniser uses `provably_nonzero` and the
  hazard closes for every shape it serves. The three old recognisers keep
  their current tests until they are deleted (step two); sharpening them in
  place buys nothing since the general check gates every new shape.
- Consistency guard on the recursor side: for a class-(T) declaration the
  recursor must carry exactly one more uparam than the inductive (the motive
  level — large elimination by reason 1). Check
  `rec.uparams.len() == ind.uparams.len() + 1` and decline the nest
  otherwise; it is one line and it catches an export-format surprise before
  the nest is built. `is_k` recursors: decline, as today.

Small-elimination instantiations need nothing here: a `u₁ = 0` ι site
short-circuits through `proof_eq` before `derive_iota` is consulted
**[read**, `tg.rs:12095–12098`**]**.

---

## 5. The Lean-facing layer: types, constructors, typing rules

`Inductive` speaks in `ind(p⃗)` and `ctor_i(y⃗,r⃗)` at variables. Lean speaks in
curried applications. The bridge generalises `ind_abbrev` + `list_const` +
`wlist_fun`, and the machinery already exists in the `RecNest` builder
(`define_abbrev` + `lambda_n` + `beta_conditional_n` per level,
`tg.rs:5975–5999`); this section is that loop with a different bottom.

- **Type former.** `np = 0`: `⟦T.{ℓ⃗}⟧ := ind_abbrev(name, lv, ind.ty_of([]))`
  — exactly today's shape. `np > 0`: a nest of `np` lambda graphs, domains =
  the parameter binder interpretations from §3.2 step 2, bottom
  `ind.ty_of(p⃗)`; head = `ind_abbrev(name, lv, outermost graph)`. The
  conditional equation `⟦α⃗ typed⟧ → app-spine(⟦T⟧, ⟦α⟧…) = ind.ty_of(⟦α⟧…)` is
  the general `l_beta`, assembled from the per-level betas — this is what the
  general `fire` and `mem_along_c` consume, so derive it once per
  `(name, levels)` and store it beside the nest.
- **Constructors.** Depth `np + kᵢ + mᵢ` nest, domains walked off the
  constructor's own Lean type (same walk as §3.2 step 3 — reuse the recorded
  locals so the domains are *the same terms*), bottom
  `ind.ctor_term(mach, i, plain_args, rec_args)` split out of the variable
  list **by the order mask**. Depth 0 (nullary ctor of a 0-parameter
  inductive): the bare abbreviation, and register `ind_mems[(⟦c⟧, ⟦T⟧)]`
  from `Ctor::mem` (no `H` — `shared.rs`'s `Ctx(None)` discipline guarantees
  the theorem is closed **[read**, hub doc: "absent for a nullary
  constructor"**]**) transported along the two defining equations, guarded
  by conclusion equality as `ind_ty_mem_uncached` does.
- **`CtorRule`s** (the applied-constructor typing rules `has_type_ctor_app`
  instantiates, `tg.rs:7464`): premises must be in **Lean argument order** —
  the rule's `vars`/`prems` are positional against the spine
  **[read**, `tg.rs:7492–7501`**]** — while `Ctor::mem`'s `H` is
  plains-then-recs **[read**, `ctor.rs:60`: `args` then `recs`**]**. So the
  rule builder must (a) instantiate `mem` at the nest's variables, (b)
  **permute the antecedent conjunction into declared order** using the mask —
  a `conj_proj`/`and_intro` shuffle under `u_*` combinators, mechanical but
  it must exist — and (c) transport across the nest's beta equations exactly
  as `list_const` does its Leibniz dance. The premises are then
  `p⃗ typings ++ fields in declared order`, with recursive-field premises
  stated at `app-spine(⟦T⟧, p⃗)` (the redex), since that is what use sites
  state — bridged to `ind(p⃗)` inside the rule via the type former's
  conditional equation.
- **What is *not* attempted**: function-space memberships for partially
  applied constructors (`List.cons α h` alone) — not derived today either
  **[read**, `tg.rs:7460–7463`**]** — with **one exception to preserve**:
  today `N.succ` *unapplied* gets `∈ fs(N,N)` registered (`tg.rs:6045–6049`),
  and `075` uses it (`App: fs` fired 7×). In step one this is moot (N stays
  on the hand-written path); in step two the general path must register the
  same membership for the one-field-no-parameter case via
  `ext::lam_in_funspace` over the single-level nest, or `075` regresses.
  Recorded as a step-two acceptance item.
- **Gating**: `interpreted_shape`/`typeable_shape` (`tg.rs:6015`) gain the
  general recogniser, else applications of new constructors never reach the
  typing rules at all — the exact `N.succ` lesson from the log.

---

## 6. The recursor wiring: `RecBottom::General`

### 6.1 Recognition and construction

`rec_bottom` order: the three hand-written recognisers first (step one
invariant, §8), then general: resolve `r.all_inductives[0]`, require
`gen_inds` hit (or build), `num_motives == 1`, `num_indices == 0`, `!is_k`,
`rec_rules.len() == n == num_minors`, the uparam count guard of §4, and
`n ≥ 1` (`GenRecursor::build` returns `None` for `Empty` **[read**,
`recursor.rs:120`**]** — `Empty.rec` stays opaque; no ι site can demand it,
only typings suffer, which is today's behaviour). Build/fetch the
`GenRecursor` from `gen_recs` over the **same** `Machine`, `Inductive`, and
`RecCore` (§1).

### 6.2 Nest changes (all in existing code, all guarded)

- depth: already `major_idx + 1`; add the loud assertion
  `depth == np + n + 2` (holds for the three existing shapes: 4, 4, 5
  **[read]**) and drop `vars.len() < 4` (`tg.rs:5925`) in favour of it.
- bottom body:
  `app(gr.rec_of(mach, ind, rc, p⃗=vars[0..np], s⃗=vars[np+1..np+1+n], T_policy), major)`.
  `T_policy` is fixed at nest-build time because the bottom mentions it —
  same constraint as today.
- `derive_iota_core`: `idx > 1` (`tg.rs:9215`) becomes `idx >= n`; the
  parameter drop (`ctor_args[cnp..]`) is already general **[read]**.

### 6.3 `T`-policy (decided here, from `RECURSOR-DESIGN.md` §5.2 — adopted
unchanged)

1. every constructor nullary → `T := fin(s⃗)` at the minor variables
   (`Machine.fin`; the `Bool` trick — `HYP` free). This is what keeps `073`
   at 0/0 after step two.
2. else if some constructor `i₀` is nullary → `T := doms[np + 1 + i₀]`, **as
   the nest walked it** — never rebuilt (the twice-recorded `075` lesson).
   `Lean.Name` has `anonymous` → policy 2 covers `Name.str`/`Name.num`.
3. else → **decline the nest** (recursor stays opaque; counted). No corpus
   witness needs option 3's fallback **[read**, RECURSOR-DESIGN §9.3, still
   open per §10**]** — but note the §10 mask witnesses
   (`Grind.CommRing.Expr.add/sub/mul`, mask `Rec,Rec`) belong to an inductive
   whose nullary-constructor status I did not read; if `Expr` has no
   nullary, field-free constructor, those recursors decline under policy 3
   and the census in §12.8 decides whether that matters.

### 6.4 `fire_general`

The generalisation of `fire_list`, consuming `GenRecursor::iota[idx]`:

1. Instantiate `iota[idx]` at
   `(p⃗ := ta[0..np], s⃗ := ta[np+1..np+1+n], T := T_policy, y⃗ := plain fields, t⃗ := rec fields)`
   — fields split by the mask, interpretations of `fields[..]` from
   `derive_iota_core`.
2. Bridge the constructor: `⟦cᵢ p⃗ f⃗⟧`'s spine equals `ctor_i(y⃗,t⃗)` via the
   constructor nest's conditional betas (§5), premises = the parameter and
   field typing obligations. This is `fire_list`'s `nil_beta`/`cons_beta`
   block at general depth, driven by a loop over the mask.
3. Bridge the type: recursive-field hypotheses `tⱼ ∈ ⟦T p⃗⟧` transported to
   `ind(p⃗)` along the type former's conditional equation — `mem_along_c`,
   already general in shape **[read**, `tg.rs:9541`**]**.
4. Discharge `HYP`: per constructor `i`, derive `minor_typed_i` from the
   minor's `fs`-membership asked at the **beta-reduced kernel term** in
   declared order (`fs(β₀, fs(W, … fs(T, T)))` for the mask order), obtained
   via `mem_obligation(ctx, args[np+1+i], …)` as `fire_nat`/`fire_list` do,
   then pointwise-ised by `k+2m` `funspace_app_mem` instances (the curried
   form implies the pointwise form — RECURSOR-DESIGN §3.3 **[read**, the
   premise doc in `premise.rs` confirms pointwise is what is stated**]**).
   A minor whose Lean type does not beta-reduce to an iterated `fs`
   (dependent motive) → the obligation fails → **conditional certificate or
   gap**, with the dedicated reason string
   `"iota: HYP undischargeable — dependent motive"` (RECURSOR-DESIGN §7.3's
   taxonomy request).
5. Rewrite the live recursive calls: the reduct spells `app(grec, tⱼ)` as
   `⟦T.rec ℓ⃗ p⃗ C s⃗ tⱼ⟧` — contract the nest once more per recursive field
   (`fire_nat`'s last step, looped over `mᵢ`).
6. Everything flows back through the existing `derive_iota_core` join and its
   two guards (`final_t != fired_rhs` and `out.proves(l, rr)`), which is what
   turns every mistake above into a gap.

The **helper worth extracting** rather than inlining: the
"instantiate + permute-into-declared-order + transport across nest betas"
move appears in §5's `CtorRule`, §6.4 step 2, and step 4. One shared
function, tested at interleaved masks (`Rec,Plain` and `Plain,Rec,Plain,Rec`
— the shapes `derived/tests/genrec.rs` already pins derived-side, and the
`Name.str`/`sepBy` shapes the preludes demand) before any corpus run
(RECURSOR-DESIGN §7.2's pre-wiring pin).

---

## 7. The per-instantiation story

1. **No schedule change.** Inductive declarations themselves stay excluded
   from σ (`tc.rs:226–230`) — the general path interprets at *use* sites,
   under the using declaration's σ, with ground levels, exactly as
   `list_const` does today. All derived-side theorems are level-free
   `∀`-statements; the per-`(name, levels)` residue is: the `βⱼ` symbols
   (bodies can genuinely differ per level — a field type mentioning
   `PLift.{u}` interprets differently at `u := 0` vs `1`), the abbreviations
   and nests, and the typing rules. Hence every new cache is keyed
   `(name, levels)`, matching `ind_syms`/`ctor_rules`/`rec_nests`.
   Deduplication across levels when bodies coincide (e.g. `List` at `[0]` and
   `[1]` share telescopes if the `βⱼ` symbols coincide) falls out of
   `Machine::telescope`'s `(np, β⃗)` key only if the checker caches `βⱼ` by
   body term; **worth doing** (a `beta_syms: HashMap<(usize, Term), FnSym>`
   beside the skeleton caches) but an optimisation, not correctness.
2. **`ctor_rules` keying**: fixed already (task #22 landed **[read]**).
   The general `CtorRule` builder inherits the fixed key and the
   `subj != ts[i]` premise-position check; the **order-mask permutation of
   §5 is what keeps that check honest** — premises must line up with the
   Lean spine positionally, and an unpermuted rule would fail it on every
   interleaved constructor (gap, not unsoundness, but 100% of the sites at
   every masked prelude shape — `Name.str` alone would make it a
   high-volume miss).
3. **The pre-pass audit gap (new finding).** Pass A collects an `Inductive`
   node's edges from `info.ty` only; `Definition/Theorem/Opaque` add their
   value, `Recursor` adds its rules' values — constructors' types enter only
   as the `Constructor` declarations' own nodes **[read**,
   `instantiations.rs:407–418`**]**. The spec builder interprets **all**
   constructor field types whenever the *inductive* is interpreted at `ℓ⃗`,
   so a file that uses `T.{σ}` without using constructor `c.{σ}` makes the
   backend interpret constants inside `c`'s fields at instantiations the
   schedule never demanded → the unpredicted-instantiation row goes nonzero
   and its pinning test fails. Fix: in pass A, for `Declar::Inductive`, also
   `collect_consts` over each constructor's `info.ty` (attributing the edges
   to the inductive's node — the uparams are shared, so `eval` is correct).
   Cost: a few more edges and pairs; the fixpoint machinery is untouched.
   Do this **in step one, before the first measurement**, or the audit row
   stops being evidence.
4. **σ mechanics**: copy `list_const`/`rec_nest` verbatim —
   `subst_expr_levels(ty, uparams, levels)` for walks,
   `interp_levels(ctx, levels)` for keys. Do not invent a second discipline.

---

## 8. The two-step landing

The seam constraint (RECURSOR-DESIGN §7.5, restated): the hand-written and
general stacks build **different sets** — seed `U(A)` vs `U({A,T})`, fibres
`0`/`1` vs `finord(m)`, `1+α` vs `Sum_2(1, α+0)` — with no bridging theorem,
so nothing may mix them for one inductive, and byte-level corpus stability
for `073/075/076` is only guaranteed while those files' inductives stay on
the old path.

### Step one — general path for shapes the recognisers do not cover

Order of recognition: `false_shape`, then `enum_arity`/`nat_shape`/
`list_shape` (and their `rec_shape`s), then general. Safe because:

- `Bool`/`N`/`List`/`False` declarations hit the old paths first —
  `073/075/076` and the whole `ind_syms`-fed pipeline for them are
  byte-identical, **except** for the three shared edits, each a widening
  that is a no-op on the old shapes **[read**, checked in §6.2: depth
  equation holds at 4/4/5; `idx >= n` equals `idx > 1` at `n = 2`;
  recognition order preserved**]**.
- Newly covered declarations (`RGB`, `TwoBool`, the dependent telescope
  shapes, every enum with > 2 constructors, and the prelude's masked shapes —
  `Name`, `RArray`, `ParserDescr`, …) go from *opaque* to *interpreted*:
  gaps can close, conditional certificates can newly escape (the measured
  `076` pattern, +1 escape against −31 gaps). That satisfies the owner's
  acceptance test only if measured per file — the protocol is §10. `RBTree`
  (`042/068/077`) and `RTree` (`116`) are **declined** — indexed and
  function-typed-recursive respectively — and their files must be
  byte-identical, which is itself an acceptance assertion: movement there
  means a scope leak.
- Landing order inside step one:
  1. `Shared` moves (§2, §3.4's `ind_syms` move) + pre-pass constructor
     edges (§7.3) — **pure refactors, measurable as byte-identical corpus**.
  2. Spec builder + carrier wiring: `gen_inds`, type/constructor nests,
     `ind_mems`/`CtorRule` general builders, gating. Measure: `035/061`
     (TwoBool) improve or hold; `042/068/077/116` byte-identical with the
     decline counters showing `indices` / `function-typed recursive
     argument`; nothing else moves.
  3. Recursor wiring: `RecBottom::General` + `fire_general` + `T`-policy.
     First target: **`Lean.Name.str` on `init-prelude`** — mask `Rec,Plain`,
     `m = 1`, policy 2 via `anonymous`, and ubiquitous, so its ι sites are
     the highest-volume unambiguous credit now that `RBTree` is out. In the
     tutorials the general recursor's new coverage is the > 2-constructor
     and multi-plain-field shapes (`061_twoBoolRec` if it reduces —
     unverified, §12); expect the visible movement on `init-prelude`'s gap
     count rather than a tutorial `HAS_GAPS` flip.
- Explicitly **safe to skip in step one**: `⟦T⟧ ∈ ⟦Sort u⟧` for general
  carriers (nothing has it today), partial-application memberships,
  `Empty.rec`, class-(S)/(P) declarations, `no_confusion` consumers
  (nothing consumes `Ctor::inj`/`distinct` checker-side yet — the recursor
  uses them internally).

### Step two — cut over `Bool`/`N`/`List`/enums, delete the recognisers

Preconditions, each a named blocker:

1. **General recursor proven on the corpus** (step one rung 3 done;
   `Name.str`-class ι sites fire on `init-prelude`; witness shapes per
   RECURSOR-DESIGN §4.4 pinned in `derived/tests/genrec.rs` — already the
   case per §10).
2. **`ind_ty_u1` parity** — the blocker from §0.5. The cumul chain demands
   `B(a) ∈ ω` on the nose; `finord(m) ∉ ω`. Options, in preference order:
   (a) generalise `cumul`'s `Fin`/`bounded` step to fibres *equinumerous* to
   a member of ω (or directly: `bnd(finord(m))` by the same finite induction
   — `bounded_at` is stated per `k`, and its proof walks the elements, so a
   `finord` variant is plausibly the same induction over `Inj_j(•)` members
   **[believed**, not checked against `bounded.rs`'s internals**]**);
   (b) `sums::sum_in_universe` (backlog entry 3) plus a `finord`-aware
   restatement. Either is `derived/`-side work that #26's scope statement
   does not include. **Until it lands, step two regresses
   `⟦N⟧/⟦Bool⟧/⟦Unit⟧/⟦Empty⟧ ∈ ⟦Type 0⟧` and is not acceptable.**
3. **`N.succ`-unapplied parity** (§5, last bullet).
4. **`T`-policy 1 in place** so `073` keeps `HYP` free.

Then, per inductive **atomically**: recogniser arm deleted, `ind_const`
dispatch to general, `RecBottom` arm deleted, `Inductives` field dropped —
in one change per shape (`Enum`, then `Nat`, then `List`), measuring
`073/075/076` at each. Owner's bar: **observable acceptance, not
term-for-term agreement** — the general ι equations differ in spelling from
the hand-written ones by construction (different fibres, seeds, trailing
`+ 0`), so the test is gaps/escapes/arena/fragment, plus ι provenance still
showing real derivations. `derived`'s `enums/wnat/wlist/wnat_rec/wlist_rec/
wbool_rec/twopoint/wlist_fun` are then demoted to cross-check tests or
deleted per the derived-side owner's call; the checker stops referencing
them when the `Inductives` fields go.

---

## 9. Ordered implementation plan

1. `Shared` restructure: `machine`, `gen_inds`/`gen_recs` skeletons,
   `ind_syms` → `Shared` (guarded), borrow-discipline helper. *Corpus
   byte-identical.*
2. Pre-pass: constructor-type edges for `Inductive` nodes
   (`instantiations.rs` pass A). *Audit row stays zero; pair count grows
   slightly — record it.*
3. `provably_nonzero` + `decl_spec` builder + decline taxonomy (reason
   strings: `indices`, `mutual`, `nested`, `sort-ambiguous`,
   `function-typed recursive argument`, `dependency on recursive field`,
   `arity/shape mismatch`, `re-entrant`). Unit-test the builder against
   synthetic `InductiveData` shapes including the interleaved masks
   (`Rec,Plain` and `Plain,Rec,Plain,Rec`), a dependent two-field telescope,
   **and the decline cases**: an indexed family (`RBTree`'s data) and a
   function-typed recursive field (`RTree`'s). **← riskiest step of the new
   checker-side work** — a wrong mask or arity here derives true theorems
   about the wrong declaration, surfacing only as diffuse guard-caught gaps
   later; a missed decline mis-scopes the whole path.
4. Carrier wiring: type/constructor nests, `ind_mems`, general `CtorRule`
   with the order-mask permutation helper, gating. Measure step-one rung 2.
5. Recursor wiring: `RecBottom::General`, nest guard relaxations,
   `T`-policy, `fire_general` with pointwise-`HYP` bridging. **← riskiest
   step overall** (nest-computed terms meet derived schemas; every recorded
   late surprise — `doms`-as-computed, `mem_along_c`, trailing args,
   `derive_beta`, `whnf` recall — lived exactly here). Wire `Lean.Name.str`
   first (§8).
6. Step-two preconditions: cumul generalisation (blocker 2), `N.succ`
   parity, then the three atomic cutovers, then deletion.

---

## 10. Acceptance protocol (observable, per the owner)

Before/after each rung, the standard table: tutorial gaps/escapes per file
(with `073/075/076/077/068/042/035/061/116` called out), files at zero,
fragment 27/27 at 0/0, arena 152/0/2, `init-prelude` gaps/escapes/runtime,
unpredicted-instantiation row **zero**, `stepcount` ι provenance (real rule,
not admit), `HAS_GAPS` flips enumerated. Step one rungs 1–2 additionally
assert byte-identical `073/075/076`. `042/068/077` must **not** move at any
rung (RBTree declines as indexed) and `116` must not move (RTree declines,
function-typed recursive argument) — movement on any of the four means a
scope leak past the spec builder, and the decline counters must show the
matching reasons. The general recursor's positive credit is measured on
`init-prelude` (the `Name.str`-class ι sites), not on those files. No new
`Admit` enum variants; all new failure paths are declines or reason-stringed
iota admits.

---

## 11. Is #26 as scoped right?

Mostly yes, with three corrections of record:

1. "**Replacing** the three hardwired shape recognisers" is achievable only
   as step two of a two-step landing, and step two has a dependency outside
   the checker — the cumul `Fin`-at-`finord` generalisation (§8, blocker 2)
   — that no prior document lists. Scope #26 as step one plus the step-two
   plan; the cumul item should go on `LIBRARY-BACKLOG.md` now (it is
   dispatchable to a `derived/`-only agent alongside entry 3).
2. The claim "no change to `instantiations.rs` is needed"
   (RECURSOR-DESIGN §6) is false for the audit's sake: one collection case
   must be added (§7.3). Small, but it is a trusted-evidence row, so it is
   not optional.
3. `ctor_rules` name-only keying is already fixed in-tree; #26 should drop
   that bullet rather than re-fix it.
4. #26's framing inherited "the mask exists because of `RBTree.red`" from
   RECURSOR-DESIGN §1.6, which its own §10 has since refuted from the
   export: `RBTree` is indexed and out of scope. The mask stays — the
   preludes demand it (`Name.str`, `sepBy`, `RArray.branch`) — but every
   `RBTree`-denominated payoff in the scope statement (`068` staying 0,
   `077`'s ι gaps closing) is void, and the wiring's obligation toward
   `RBTree` is a **counted decline on `numIndices`**, nothing more.

---

## 12. What I could not settle

1. **The `GenRecursor` interface details.** The module is landed
   (RECURSOR-DESIGN §10) but I read it mid-edit; `hyp`'s exact quantifier
   spelling and whether `iota[i]`'s antecedent associates as `HYP ∧ H_ctor`
   must be re-verified at wiring time. The wiring in §6.4 depends on the
   *shapes*, not the names; the instantiation order is documented as
   params, minors, target, then y⃗, t⃗ (`recursor.rs:34`).
2. **Whether `Ctor::mem`'s hypothesis stays plains-then-recs** once the
   recursor agent finishes with the mask, i.e. whether §5's permutation
   helper is permanent or transitional. Currently plains-first **[read]**.
3. **The cumul generalisation's real cost** (§8 blocker 2): that
   `bounded_at`'s induction transfers from `k ∈ ω` to `finord(m)` is argued
   from its statement shape, not from its proof — I did not read
   `bounded.rs` below the header. If it does not transfer, the fallback is
   an equinumerosity layer, which is a session-scale detour.
4. **Whether any export in the corpus has a constructor field type that is
   level-dependent** (making `gen_inds` genuinely per-level rather than
   degenerately so). I found no counterexample but did not sweep; the design
   is correct either way, only the cache economics change.
5. **Whether `define_abbrev`-minted `βⱼ` bodies can ever capture a
   *canonical* hole variable** (`hole_vars`/`x_canon` reuse) if the field
   type's interpretation goes through skeleton machinery mid-walk. The
   `rec_nest` walk has the same exposure today and no recorded incident, so
   I believe the local-reservation discipline covers it — **[believed]**,
   worth one adversarial read during rung 3.
6. **Multi-parameter Lean-facing nests** (§5, `np > 1`) have no in-scope
   corpus witness I identified (every named target is `np ≤ 1`); the first
   `np ≥ 2` declaration will exercise the parameter-spine bridging fresh.
   The witness discipline should add a synthetic two-parameter fixture
   before rung 4 ships.
7. **Thread-count interaction**: `Shared` is thread-local; per-thread
   `Machine`s mint disjoint symbols, as `Inductives` does today, so
   cross-thread composition never arises — but the *cost* multiplies per
   thread, and `Inductive::build` per declaration per thread at
   `init-prelude` scale is unmeasured. If it shows up, the fix is
   scheduling-side (affinity by inductive), not design-side.
8. **The dependent-motive census** (RECURSOR-DESIGN §9.2/§10, still open),
   now to be run over the *in-scope* ι sites — the `Name.str`-class prelude
   sites, not `077`. Sites with a genuinely dependent Type-level motive stay
   gaps by design (`T`-policy + the dedicated reason string); the census
   sets the acceptance expectation for rung 5 before it is judged.
9. **Two facts about the new targets I did not read**: whether
   `061_twoBoolRec` ever reduces its recursor (if not, no tutorial file
   exercises the general ι at all and the whole rung-5 measurement is
   `init-prelude`-only), and whether `Lean.Grind.CommRing.Expr` has a
   nullary, field-free constructor (decides `T`-policy 2 vs the policy-3
   decline for the `Rec,Rec` mask witness, §6.3). Both are one `jq` over the
   exports when the tree is measurable again.
