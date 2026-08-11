# Unifying the global environment — a design and a recommendation

*2026-08-09. A design, on the owner's instruction, for the step after #120:
one global environment for `checker/` and `mini/`, leaning toward nanoda's
design, to unblock choosing one checker or the other per declaration.
Written ahead of the implementation; track B's first rungs have since
landed — B0 as the `explore/b0-shared-env` prototype, B1/B2 as `tg::EnvCore`
at both engine roots (§3.4 item 1, §5) — and the affected sections are kept
current in place. Everything cited was
read in a scratch worktree at `f29c7ef`; nothing here is measured beyond what
the cited documents and tests already measure, and §9 names what is not.
Revised in place the same day: the first version's central negative finding —
"certificates cannot cross engines" — was challenged by the owner and does
not survive re-examination; §0.4 records the overturn and §3 is the
re-derivation.*

## Verdict

**The global environment has two halves, and both unify.** The
recommendation in one paragraph:

* **The syntactic half is `checker/`'s `DeclarMap` + `Env` view**
  (`checker/src/env.rs:236` — the parse-time-complete `FxIndexMap`, the
  `cutoff` visibility slice, the `temp_declars` overlay), **unchanged**. Not
  one line of `checker/src/env.rs` needs to move: this recommendation *adds
  beside* upstream, it does not rewrite it. `mini`'s `Environment` becomes a
  read adapter beside the #120 seam, plus an owned overlay for its generated
  recursors and in-progress groups (§5, track A).
* **The semantic half — the interpretation store — is part of the global
  environment and unifies too**: one kernel `Env` (hence one brand), one
  `derived::prelude` ambient, one `Tower`, one `Machine` and chain, one
  carrier, one constant interpretation and one typing theorem per key, with
  **both engines reading and writing it** behind the adopt-and-check guards
  `checker/` already uses on its own shared stores (§3, §4).
* **The first version's claim that certificates cannot cross engines is
  withdrawn.** The precise fact is that `kernel::FnSym` and `kernel::FreeVar`
  carry the **brand of the `Env` that minted them** (`kernel/src/term.rs:
  36–44`, `:98–106`; `thm.rs:493–541`), so theorems minted over two `Env`s
  are about disjoint objects — a statement-identity requirement, not an
  impossibility. One shared `Env` is exactly what dissolves it, and the tree
  contains three worked precedents of that dissolution, one of them landed
  yesterday with the failure mode pinned by a test (§3.1).
* **The owner's split — mini does the inductive constructions, `checker`
  certifies defs and theorems with its caches, both writing compatible
  certificates into one store — is feasible on this substrate** and is the
  shortest credible path to a certified `init-prelude`, because it routes the
  matcher wall (`List.get.match_1`: ≥ 11.00 T instructions and 8 GB without
  finishing, PRELUDE-COST.md) onto the engine that is three orders of
  magnitude cheaper on measured common input. It has two named dependencies:
  `checker`'s stage-1 evidence threading, without which its def certificates
  are dropped as conditional (§3.6), and one prototype-gated unknown, the
  skeleton normal-form agreement (§3.5).
* **What stays per-engine is real but small**: the clause dispatches, the
  per-declaration working state, the gap taxonomies, and each engine's
  claim-matching guards. None of it appears in any theorem's statement,
  which is why it can stay split while the certificates merge (§3.3).

## 0. Where the brief — and this document's first version — were wrong

Per the standing instruction, before anything is built on it:

1. **There is no `ctor_rules` table in `mini`.** The `ConstKey`-keyed tables
   on the constructor side are `ctor_untranslated` (`mini/src/interp.rs:589`)
   and the per-constructor certificate vectors inside `Translated`
   (`ctor_abbrev`, `field_abbrev`, `rec_dom_abbrev`, `interp.rs:687–717`);
   the per-constructor *rules* live on `ConstantInfo::Recursor::rules`, keyed
   by constructor `Name` inside the entry (`mini/src/env.rs:123`).
2. **The `isRec` panic population is six files, not four-plus-one.** Four
   `mini/tests/fixtures` files, one `modelgen/tests` fixture
   (`mutual_nonrec`), and one `modelgen` *output* shape (`nest_odd_shapes`'
   generated block) — MODELGEN.md §4, measured file by file there. The cause
   is one: upstream recomputes `isRec` per member, Lean sets it per block
   (`checker/src/inductive.rs:30`).
3. Everything else in the brief checked out: `IndApparatus` at
   `interp.rs:395`; `model_of`/`model_iota` (`interp.rs:631`, `:645`, plus
   the `nested` membership table at `:654`); the mode B refusal at
   `inductive.rs:1269`; #116 closed.
4. **This document's own first version.** It split "syntactic environment"
   from "evidence stores", unified only the first, and then concluded that
   certificates cannot cross engines. The conclusion was circular: the
   certificates could not cross *because the design had put the objects they
   refer to on two sides of a wall it drew* — the interpretation store is
   part of the global environment, not an engine's private cache. The owner
   challenged it; the re-derivation is §3; the two citations the first
   version used to defend the wall (`tg.rs:2017–2031` and the
   identity-not-memoisation doctrine) both, read correctly, argue for the
   shared store (§3.1, §3.2). Corrected in place, per the house rule.

## 1. The census

### 1.1 The syntactic stores

**`checker/`** (`checker/src/env.rs`, `parser.rs`, `util.rs`):

* `declars: FxIndexMap<NamePtr, Declar>` — built **complete at parse time**,
  insertion-ordered, one entry per export line. `Declar` has eight kinds:
  Axiom, Quot (×4 entries per quotient), Theorem, Definition (with
  `ReducibilityHint`), Opaque, Inductive (`InductiveData`), Constructor
  (`ConstructorData`), Recursor (`RecursorData` with `rec_rules`, `is_k`).
* `Env<'x,'a>` (`env.rs:236`) — a *view*: the map, a `cutoff` index
  (`EnvLimit`), and an optional `temp_declars` overlay for nested-inductive
  specialisation. Checking never inserts; visibility is sliced per
  declaration (`util.rs:258`) and per thread.
* `mutual_block_sizes: FxHashMap<NamePtr, (start, size)>`
  (`util.rs:221`, filled at `parser.rs:802`) — the block extent an
  inductive's check runs over (`inductive.rs:31`).

**`mini/`** (`mini/src/env.rs`, `kernel.rs`, `convert.rs`):

* `Declaration` (`env.rs:49`) — five kinds: Axiom, Def (`DefKind`), Quot,
  Inductive (constructors **bundled in**), Mutual. Recursors are **not** an
  input kind: `parseRecInfo` is a stub, the export's recursors are dropped at
  load (`convert.rs:20–21`, `:546`).
* `Environment` (`env.rs:156`) — `consts: HashMap<Name, ConstantInfo>` grown
  by `kernel::add` **as declarations are checked**, plus the `owners` index
  (`env.rs:164`, filled at `kernel.rs:4763`, `:4849`).
* `ConstantInfo` (`env.rs:89`) — Opaque, Inductive (with **computed**
  `num_indices`, `is_unit`), Def, Recursor — the last **generated** by
  `add_block` (`kernel.rs:4830–4863`): open-body rules, `num_motives`, and a
  computed `k_type: Option<E>` where the export has `is_k: bool`.
* Since #120, `Name`/`Level`/`E` *are* `NamePtr`/`LevelPtr`/`ExprPtr` in the
  binder-erased normal form (`mini/src/arena.rs`). `convert.rs` already
  reads the parse-time `DeclarMap` — mini is *already* a reader of nanoda's
  store at load time; what it is not yet is a reader at check time.

### 1.2 The run shapes

* `checker`: parse → complete map → check each declaration against `Env` at
  a `ByName` cutoff, serially or on N threads (`tc.rs:255`, `:322`, `:330`).
  Constructors and recursors get a light standalone info-check
  (`tc.rs:280–289`); their real validation is the inductive's own check,
  which **mints** the recursors and def_eq-compares them against the
  export's entries (`inductive.rs:36–95`).
* `mini`: load → zone A, one `kernel::add` per declaration into the growing
  `Environment`, abort on first rejection (`run.rs:181–195`) → zone B, the
  evidence pass over the **completed** environment
  (`nested_splice::recognise`, `mutual_aux::expand` — which clones the
  environment and substitutes encodings (`mutual_aux.rs:940`) — then
  `Ledger::run`, `run.rs:248–265`).

The axes decouple on mini's side already: zone B needs the completed
environment, not the fact that zone A produced it — and `Ledger::run` walks
declarations in file order, which is what lets §3.6's interleaving be a
driver change rather than a redesign.

### 1.3 The semantic state, complete — and which of it was ever global

The distinction the first version failed to draw, and the one that does most
of the work: **one-per-run objects** (the semantic half of the environment)
versus **per-declaration working state** (an engine's scratch, which never
appears in any stored statement).

**One-per-run, `mini`**: `Interp::env` (the kernel `Env` — the brand
source), `prelude` (built by `derived::prelude`, `interp.rs:51`), `cumul`
(the tower table to `CUMUL_HEIGHT`), the skeleton-site tables
(`lams`/`fibres`/`conds` + the by-symbol indexes), the canonical variables
(`x_canon`, `hole_vars`), `consts: HashMap<ConstKey, ConstInterp>` (term,
typing, defining equation per constant), the first-use singletons
(`direct`/`eta`/`quotient`/`acc`/`rec_acc`/`prop_sub`/`dprod_fs`), and the
whole `IndApparatus` (`interp.rs:395`): `mach: Machine`, `chain: IndChain`,
the per-key construction tables (`decls`, `deprecs`, `dep_elims`, `props`,
`truncs`, `trunc_recs`, `prop_fields`, `trunc_fields`, `decl_fields`,
`decl_projs`, `reindex`, `indexed`, `indexed_walks`, `props_ix`,
`truncs_ix`, `trunc_recs_ix`, `prop_recs`, `dep_recs_ix`, each with its
failed-set), the decline records (`untranslated`, `ctor_untranslated`,
`rec_untranslated`), the model routing tables (`model_of`, `model_iota`,
`nested`), and the machine-welded singletons (`acc`, `wrec`, `trunc`).

**One-per-run, `checker`** (per thread today): `Shared` (`tg.rs:1843`) —
`env: Env`, `syms`, the same canonical variables, the skeleton-site tables
(`lam_infos`/`pi_infos`/`prop_infos` + by-symbol indexes), the theorem memos
over them, the singletons (`inds`, `rec_core`, `bool_rec`, `nat_rec`,
`list_rec`, `ind_ty_u1`, `machine`), the per-key stores (`gen_inds`,
`gen_recs`, `gen_ty_nests`, `gen_ctor_nests`, `rec_nests`, `opaque_syms`,
`const_syms`, `param_syms`, `idx_syms`, `lit_syms`, `ind_syms`,
`declar_typings`, `declined_cond`), `false_anchor`.

**Per-declaration working state, never global**: mini's `Checker` (`lenv`
telescope, `frames`, `wt_memo`) and the zone-B walk frames; checker's
`TgBackend` (the `locals` memo, the per-backend adoption layer at
`tg.rs:2397`), `TcCtx` and its caches, the per-declaration `LeanDag`.

The two one-per-run columns are the same list twice. Every row of mini's has
its checker counterpart and vice versa, both engines build their ambient
from the **same** `derived::prelude` (`tg.rs:1056–1064`; `interp.rs:51`),
and both `Machine`s are the same `derived::inductive::Machine` type over the
same construction layer. That is what makes §3's unification an
identification of duplicates, not a marriage of strangers.

## 2. The syntactic differences — the concept table

| concept | `mini` | `checker` (nanoda) | genuine or spelling? |
| --- | --- | --- | --- |
| store lifecycle | grown by `add` as declarations are checked | complete at parse; checking validates, never inserts | **genuine** — nanoda's shape is the one routing and parallelism need |
| visibility | implicit (env = what was accepted so far) | explicit `cutoff` (`EnvLimit`), per-thread slices | genuine; nanoda's generalises mini's |
| input declaration kinds | 5 kinds; ctors bundled, recursors absent, `Mutual` first-class | 8 kinds, flat; blocks linked by `all_ind_names` + `mutual_block_sizes` | genuine at inductives; each derivable from parse data |
| stored constant kinds | 4 (`ConstantInfo`) | the 8 input kinds, validated in place | spelling, except recursors |
| **recursors** | **generated** by the kernel: open-body rules, computed `k_type` | **read** from the export, validated by mint-and-def_eq-compare | **the crux of the syntactic half.** §3.8 is the reconciliation |
| K-rule datum | `k_type` — the type the major must have | `is_k` — a flag | genuine; interconvertible via the inductive (`kernel.rs:4794–4804`), one known divergence class (§3.8) |
| ctor bookkeeping | `owners` index + counts recovered from types | `ConstructorData` explicit, from the export (`bad/048`, `env.rs:87–98`) | both derivable from the map |
| inductive extra data | computed `num_indices`, `is_unit` | export-given fields; `is_recursive` recomputed per member and asserted — the six-file panic (§0.2) | overlapping core; the recomputation is a bug to route around, not a design to adopt |
| reducibility hints | none | `ReducibilityHint`, drives lazy delta | genuine but engine-local: hints steer search order, not the judgement |
| level params | `lparams: Vec<Name>` | `uparams: LevelsPtr` | spelling since #120 |
| quotient | one declaration; kernel generates four constants | four export entries, checked | same trust-direction split as recursors, smaller |
| nested | scratch `Environment`s + restore; model tables | `temp_declars` overlay; specialisation in `inductive.rs` | same role; nanoda's overlay is a first-class `Env` feature |
| duplicates | `insert_new` error | parser `assert!` (mini catches as decline, `convert.rs:255–282`) | spelling at file level; the panic-vs-status difference generalises (§3.9) |

## 3. Certificate compatibility — the object, the requirement, the price

The owner's question, sharpened by the coordinator: *why can the two engines
not produce compatible certificates — mini for the inductive constructions,
`checker` for defs and theorems?* The answer, re-derived: **they can; the
requirement is one signature; one signature is the semantic half of the
environment this document exists to unify; and the residue is a price list
plus one prototype-gated unknown, not an obstruction.**

### 3.1 What precisely fails today — the object, not the axis

Both engines mint `kernel::Thm` from the same untouchable `kernel/`. What
differs is not the theorem type but the **symbols in the statements**: a
`FnSym` is `{ brand, id, arity }` and a `FreeVar` is `{ brand, id }`, where
`brand` is the identity of the `Env` that minted them — load-bearing for
soundness, because two `Env`s both start their counters at zero and an
unbranded id would let one engine's variable alias a variable another
engine's rule assumed fresh, "a demonstrated route to `⊢ ⊥`"
(`kernel/src/term.rs:36–44`, `:59–62`, `:98–106`; `thm.rs:493–541`,
`Env::new` drawing from a global brand counter).

So with two `Env`s — mini's `Interp::env`, checker's `Shared::env` — mini's
`⟦List.{0}⟧` and checker's are **unequal symbols by construction**, whatever
their indices. Composing a mini `Thm` with a checker derivation is not
refused by the kernel — there is nothing to refuse; the result is a valid
theorem in the union signature. It is simply **about the wrong objects**:
no rule finds a common subterm, and the failure surfaces downstream as
claim≠derivation at the single-exit guards. The canonical description is in
the tree, written this week about exactly this shape:

> a second `Tower` is a second `1`, `•`, `app`, `∅`, pairing and `ω`, and
> `⊢ ω ∈ U₁` would then be about a `U₁` no interpretation mentions
> (`derived/src/nat/apparatus.rs:38–42`).

And so is the fix, three times over, each the same move — **take the
caller's apparatus instead of minting your own, and pin the failure mode
with a test**:

1. `Nat::over(env, Rc<Tower>)` (`derived/src/nat/apparatus.rs:213`, landed
   yesterday): `Nat::new` mints its own tower, right for a test and wrong
   for a checker; `over` takes the caller's, with the
   two-apparatuses-over-one-tower-agree / fresh-tower-disagrees test.
2. `Chain::over` (`tg.rs:4615–4625`): "`Chain::new` mints its own tower …
   and a theorem about *those* symbols is not a theorem about anything this
   backend produces", so it takes the prelude's `Tower` and the
   `Inductives`' own `Wtype` and `Bound`.
3. `Shared` itself (`tg.rs:1964–2114`): checker's constant symbols, inductive
   abbreviations, recursor nests and type formers were all **per-backend**
   once — one signature per declaration, in effect — and the measured result
   was thousands of re-mints and cached theorems "about symbols the next
   declaration's backend never produces". The fix was to *share the store*
   per thread, key it by what the Lean side names, and guard every read with
   adopt-and-check so nothing is trusted from it.

The first version cited item 3 (`tg.rs:2017–2031`) as the hazard *of* a
shared container. Read straight, it is the opposite: the mislabelling arose
from **not** sharing, the cure was sharing plus correct keys plus guards,
and the residual drift is counted (`Dt::IndDrift`), not silent. It is the
strongest in-tree precedent **for** the shared interpretation store, and it
is nanoda-side — so adopting its discipline for the joint store is leaning
toward nanoda's design, per the owner's instruction.

### 3.2 The identity invariant cuts the other way

*"Two uses of `List.{0}` must name one carrier, or their definitional
equality needs a theorem where reflexivity should do"* (`interp.rs:403–405`)
— the first version used this to justify per-engine stores. That was
backwards. The invariant is *one carrier per key, per composition domain*.
Two engines with two stores are consistent only so long as no theorem ever
crosses — which is precisely the regime the owner is asking to leave. The
moment certificates are to compose, the domain is the run, and the invariant
**mandates one store**: two stores are two carriers for one key, the exact
state the doctrine forbids. The identity argument is an argument for the
shared store, and the document now says so.

### 3.3 What must be one, what may stay two

From §1.3's census, the unification boundary falls out cleanly:

**Must be one (the semantic half of the global environment):** the kernel
`Env` — this is the whole of §3.1, one brand; the `Prelude`/`Tower`/chain —
both engines already build the *same* `derived::prelude` construction, so
this is "build once, hand to both" (`fast_forward` exists precisely because
the ambient is relocatable, `tg.rs:1060–1062`); the `Machine` — the
coordination point `tg.rs:1941–1953` already names, and the object every
carrier is welded to; the canonical skeleton variables — same-key-same-term
requires them minted once; the per-key stores — constant interpretations and
typings, carriers and construction packages, recursor nests, the model
routing tables (engine-agnostic name-to-name maps); the first-use singletons
(`Acc`, W-recursor, truncation, η, quotient apparatus — each doc-comment
already says "two builds would speak of two different sets").

**May stay two (and should):** the clause dispatches — mini's `Interp`
clause selection and zone-B walk, checker's `TgBackend` interpretation and
`tg.rs` rules; the per-declaration working state (mini's `lenv`/frames,
checker's `TgBackend` locals and `TcCtx` caches, which #120's arena and
PIVOT §3's memo design already govern); the gap taxonomies (diagnostics,
compared by explanation per MINI-DESIGN §11); and **each engine's
claim-matching guards** — a store hit is validated against what *this*
engine would have built (`reuse_rec_nest`, `adopt_ty_nest`,
`const_abbrev`'s discipline), which is per-engine by design and is what
makes cross-engine adoption fail closed: a mismatch mints a private symbol
and counts a drift, today's behaviour, never a mislabelled theorem.

None of the may-stay-two items appears in any stored statement. That is the
whole reason the engines can remain two while the certificates become one.

### 3.4 The price, enumerated

1. **`over`-constructors at the engine roots — paid; this is B1/B2, landed.**
   The shared handle is `tg::EnvCore` (checker/src/tg.rs): one kernel `Env`,
   `x_canon` and the hole series, and the lazily-built `Wtype`/`Bound`/
   `Machine`, behind same-thread `Rc<RefCell<…>>` cells. `Interp::over(core)`
   and `tg::install_shared_core(core)` are the two entries; `Interp::new`
   and the `shared()` fallback mint a private core each, reproducing the
   historical behaviour. The mini-side refactor was indeed the larger half
   and stayed construction plumbing: every `self.env`/`ip.env` access became
   a statement-scoped `env_mut()` guard, `ind_parts` hands zone B a `RefMut`
   it rebinds, and `IndApparatus.mach` holds the core's
   `Rc<RefCell<Machine>>` — the checker's `Inductives::build` takes the same
   pair instead of minting its own `Sums`/`Wtype`/`Bound`.
   `mini/tests/envshare.rs` pins each identity with its disagree direction;
   `mini/tests/envshare_tg.rs` (behind `mini`'s `tg` feature) runs both
   engines over one core in one thread, in either order.
2. **One `Sealed` — paid; B3, landed.** The two were the same newtype with
   the same gate; `mini/src/ev.rs` now re-exports `checker/src/sealed.rs`'s
   type (mini depends on `nanoda_lib` already), and the identity is pinned by
   a witness function (`mini/src/ev.rs::sealed_is_the_checkers_type`) that a
   reintroduced private newtype stops compiling.
3. **One key — paid; B3, landed.** The joint key is
   `const_store::ConstKey = (NameKey, Vec<LevelKey>)`
   (`checker/src/const_store.rs`): the export file's stable name index, and
   per level either `Ground(u32)` — a level that evaluates to a numeral under
   σ, the arm on which mini's ground-only keys and the checker's keys are
   equal values — or `Sym(Term)`, the checker's historical interpreted-level
   spelling for the non-ground residue (eliminator universes inside inductive
   blocks), which mini never produces. The checker's funnel is
   `TgBackend::const_key`/`level_key`; mini's conversion is
   `mini::interp::joint_key`. The `NamePtr::raw` half rests on the two
   engines parsing the same export deterministically — today they parse two
   `ExportFile`s — so every entry also records the name's rendered spelling
   and both `publish` and `get` refuse a disagreeing caller (`alias`,
   measured 0 corpus-wide); a raw-index drift is a counted refusal, never a
   mislabelled theorem.
4. **Concurrency — settled, with the measurement.** Nothing on the evidence
   axis runs multi-threaded today: `Config::num_threads` serde-defaults to 0
   (`checker/src/util.rs:988`), `check_all_declars` goes parallel only above
   1 (`tc.rs:367`), no test or CI configuration sets it, and mini is
   single-threaded throughout. So the decision is: **the evidence axis of a
   mixed run is single-threaded, and the type system says so** — `EnvCore`
   is `Rc`-backed, hence `!Send`. A checker-only run that asks for
   `num_threads > 1` keeps today's behaviour exactly: each thread lazily
   builds its own core and `Shared`. The replication price of that, measured
   (`perf stat -e instructions:u`, tg backend, `good/init-prelude.ndjson`,
   three runs each): 198.20 G instructions serial vs 240.92 G at
   `num_threads 4` — **14.2 G per additional thread, ~7% of the serial run
   each**, dominated by the per-thread re-derivation of skeleton graphs that
   `tg.rs`'s own sharing note quantifies (32388 → 2651 skeletons when one
   thread shares), not by the prelude replay.
5. **Both engines write; both writes are already funnelled.** Mini's
   `fill_declaration` stores terms with their certificates; checker's
   `store_declar_typing` **drops conditional typings** rather than storing
   them (`Dt::Conditional`, `tg.rs:8536–8559`), and both sides' stores admit
   hypothesis-free theorems only. The shared store keeps exactly these
   gates; nothing about writing gets laxer because there are two writers.
6. **Adopt-and-check on every cross-engine read** — the §3.1 item-3
   discipline generalised. Cost: the re-derivation each guard performs on a
   hit; drift counters per engine; unmeasured cross-engine (§9).

### 3.5 The one technical unknown, gating full depth

For the *statements* to coincide where interpretations cross — a mini-built
`⟦T.rec⟧` typing mentions Π-interpretations, which checker must decompose to
apply — the two dispatches must produce the **same skeleton key for the same
shape**, so the shared site tables serve both. Both use `derived::skeleton`
over canonical holes, but whether the two normal forms coincide node-for-node
is **unverified**. If they differ on some shape, the reading engine sees an
opaque head symbol and reports a gap at structure it cannot take apart —
counted incompleteness, never unsoundness — and the shared store still
carries the constant-level theorems (typings, defining equations, ι rules),
which is the bulk of the crossing surface. Prototype before track B5; §9
lists it first.

### 3.6 What the owner's split actually requires

The split — mini for inductive constructions, checker for defs and theorems
— is per-declaration routing *by kind*, **plus** the shared semantic store
so the evidence crosses. That is more sharing than the first version's
acceptance-only routing (which needed none of the apparatus shared) and
**less than the pivot's module-by-module port**: mini's 34,051-line arc
keeps its own dispatch, its own `Checker`, its own walk — it is re-pointed
at shared *handles*, not re-targeted at checker APIs. The crossing surface
is dominated by constants: what checker's def-checking needs from an
inductive is `⟦T⟧`, `⟦T.ctorᵢ⟧`, `⟦T.rec⟧`, their typings and ι theorems —
precisely what `ConstInterp` and the construction tables hold, and mini's
entries are unconditional today (constEv 218/218, sealed, corpus-wide).

Interleaving is a driver change, not a redesign: file order already puts an
inductive before its uses, mini's zone B already walks declarations in
order (§1.2), and the syntactic adapter (track A) gives mini's constructions
their declaration shapes wherever the driver invokes them.

**The dependency that does not go away**: checker's own def certificates are
only storable once its typing obligations discharge. Today they do not —
334 asked, 0 discharged, carried as assumptions on the PIVOT §4 run — and
`store_declar_typing` drops what stands under antecedents. So the split's
payoff *requires* stage-1 evidence threading in `checker/`
(THREADING-CENSUS §2; PIVOT §5 item 1, "safe to start today"). The split
routes **around** mini's matcher wall — `List.get.match_1` is a definition
and goes to the engine that ran all of `nested_model`'s forty declarations
certifying in 3.96 G instructions where mini spent 1,277 G — but it routes
**through** checker's threading gap, and no store design changes that.

### 3.7 What per-declaration choice requires of the syntactic half

Unchanged from the first version, and still necessary — the shared semantic
store does not replace it. Both engines **read** one syntactic store;
neither writes it; "checked" is a status. The handover unit is the
declaration group (the mutual block with its constructors and recursors; the
four `Quot` constants; single declarations otherwise), and routing is
decidable from parse-time facts alone.

### 3.8 The acceptance boundary invariant

When group G is marked checked by engine X, every entry of G in the shared
map must be validated in the sense the other engine relies on: types
well-formed, values typed, and — for inductive groups — the export's
constructor and recursor entries **in agreement with what the checking
engine derived** from the specification. Nanoda enforces this by
construction (mint-and-compare, `inductive.rs:85–94`). Mini today generates
but never compares (`parseRecInfo` stub); on a mixed run that would let
nanoda ι-reduce with export rules nothing checked. The comparison to promote
exists, tested: `mini/tests/mutual.rs::compare_recursors` (`mutual.rs:
590–723`) — counts, K-ness, types and rule bodies at positionally
instantiated levels, with one recorded benign divergence class (parameter-
sort owners: mini-lean K-like, Lean not, `mutual.rs:642–674`; the shared map
holds the export's data, so nanoda reduces as Lean does regardless of who
checked the group).

### 3.9 Panic versus status

Nanoda signals refusal by panicking. Parse-time panics can stay (both
engines agree the file dies; mini already catches them,
`convert.rs:266–282`). The check-time panics on the known-divergence sites —
`inductive.rs:30` (the §0.2 recomputation) and, when PIVOT §2.3's
instantiate-and-compare lands, `:1269` — must become refusals the driver can
catch at group granularity. Two sites, cited, minimal; the only upstream
edits in this design.

## 4. Where the apparatus lives afterwards

**In the unified environment's semantic half, once per run** — not in either
engine. The brief's three options resolve as: *not* a generic parameter
(sharing is by handles at construction, not by type abstraction — a type
parameter would teach upstream's env that evidence exists, for zero shared
code); *not* two parallel structures (§3.2 — that is the forbidden
two-carriers state the moment theorems cross); **a single store keyed by
`NamePtr` (and ground levels until mode B), jointly readable and writable,
with per-engine adopt-and-check at every read**. The correspondence that
merges is §1.3's two one-per-run columns; the model routing tables ride
along unchanged (they map names to names and are filled from the syntactic
environment, `run.rs:248`); the per-declaration working state and the
dispatches stay where they are.

## 5. The recommendation, staged

Lean-toward-nanoda scorecard, per the owner's instruction. **Toward
nanoda**: the syntactic store and its lifecycle, adopted wholesale with zero
edits; the export-trusting entries as shared truth; the mint-and-compare
discipline extended to mini at the boundary; and now also the *store
discipline* of the semantic half — `Shared`'s keying, funnelling and
adopt-and-check guards become the template for the joint store, because
checker already solved the one-carrier-per-key problem once, internally
(§3.1 item 3). **Not toward nanoda, with reasons**: (1) mini keeps
generating recursors (oracle fidelity; the boundary check reconciles);
(2) the per-member `is_recursive` recomputation is not adopted (§0.2);
(3) `Declaration::Mutual` is not pushed into nanoda; (4) the semantic store
is *jointly written* — nanoda's engine never shared a store with a second
writer, and the guard discipline, not single-writership, is what its own
history shows carrying the soundness weight.

Two tracks, parallel, each stage landing green with the ratchet held.
Scheduling constraint, not design: tracks A and B both touch `mini/src`,
where seats are live — sequence or coordinate.

**Track A — the syntactic store** (unchanged from the first version):

* **A0** — extend `compare_recursors`' sweep to the tutorial corpus; pin the
  divergence ledger at zero rows outside the parameter-sort K class.
* **A1** — the read adapter (`mini/src/genv.rs` beside the seam):
  `Environment` becomes map-view + overrides; `add` writes to overrides;
  behaviour bit-identical; corpus and instruction ratchets unchanged.
* **A2** — decouple fill from check, so a group can be filled-but-foreign;
  visibility pinned by a three-element fixture.
* **A3** — the boundary gate: promote §3.8's comparison from test to check
  on mini-checked groups, behind an option; corpus populations must not
  move.

**Track B — the semantic store** (new in this revision; was "optional
stage 6"):

* **B0** — **the prototype that gates depth**: interpret one fixture's
  shapes through both dispatches over one `Env` and diff the skeleton keys
  (§3.5). Done, on `explore/b0-shared-env` (head `fc4fda8`): with the arrow
  alignment in, the inductive-free fragment agrees lam 38/38, fibre 11/11,
  cond 17/17 canonical plain; the residue is recursor-adjacent lambda
  bodies, B5's scope.
* **B1** — one `Env`, one `Prelude`, one `Tower` — **landed**, as
  `tg::EnvCore` + `Interp::over` + `install_shared_core` (§3.4 item 1); the
  `Nat::over` test template (two-over-one agree, fresh disagrees) is pinned
  at this level by `mini/tests/envshare.rs`.
* **B2** — one `Machine` behind the shared `RefCell` — **landed with B1**:
  the machine lives in the `EnvCore`, over a `Wtype`/`Bound` built once on
  the prelude tower's own `Sums`, and both engines' inductive layers take
  that pair — the `tg.rs` coordination point, satisfied without touching
  `derived/`. Mini's chain (`IndChain`) stays mini's: it mints no carrier
  symbols of its own and is checked `is_over` the shared machine.
* **B3** — one key type and one `Sealed` at the seam — **landed**; §3.4
  items 2–3 have the shapes.
* **B4** — the shared constant store — **landed**, as
  `const_store::ConstStore` on the `EnvCore` (`checker/src/const_store.rs`),
  so `mini` — which holds a core but no `Shared` — reaches the same cell.
  What moved where: the checker's per-thread `const_syms` and
  `declar_typings` *are* now slots of the joint entries (`defeq` and
  `typing`, each tagged with the engine that derived it), read and written
  through the same four funnels as before (`const_abbrev`,
  `store_declar_typing`, `has_type_const`, `ty_const`) behind their
  unchanged statement guards; mini's `put_const` publishes carrier, sealed
  typing and defining equation on every fill, and its constant-miss path
  (`Checker::adopt_shared`) adopts a cross-written entry instead of
  constructing a second carrier. The store enforces two facts at `publish` —
  every certificate is about its entry's own carrier (`incoherent`, 0
  corpus-wide), and the spelling agrees (`alias`, 0) — and keeps **at most
  one carrier per key per engine**, merging entries the moment the carriers
  are equal terms (`converged`) and counting keys where the engines' carriers
  differ (`divergent`): the one-carrier doctrine as a measured goal rather
  than an asserted fiction, with `divergent` the B5 work list.

  **The crossing, measured** (91 tutorial exports, mini first, then the
  checker over the same core; `mini/tests/envshare_tg.rs::cross_sweep_tutorial`
  reproduces): mini published 798 entries / 1014 certificate slots, the
  checker 57 / 99. **52 defining equations crossed** — the checker adopted
  mini's carrier and equation outright. **0 typings crossed**: 469 typing
  offers and 57 defeq offers were declined at the statement guards, and 57
  keys hold two carriers — the skeleton-normal-form residue B0 predicted,
  now counted per key instead of argued. Mini-side adoption is mechanism-
  complete (pinned by `kernel.rs::a_foreign_store_entry_is_adopted_on_miss`,
  three atoms) but measures 0 on this corpus shape, because without
  per-declaration routing mini fills every constant itself before any use
  misses; track D's routed run is where it first measures nonzero (7, see
  track D below). The `nested_model` / `init-prelude` measurements stay
  ahead, gated on B5 closing the declined populations.
* **B5** — shared skeleton-site tables, scoped by B0's result: full sharing
  if the normal forms coincide, constant-level sharing with counted
  structural gaps if not. **Re-scoped by the owner's sharpening** ("for a
  merged environment, `interp` must return the same terms — use the same
  code to handle lambdas in both modules") **and by the measurement that
  sizes it** (`mini/tests/route_tg.rs::skeleton_key_divergence_sweep`, both
  engines full-run over one core per export, site-table keys compared as
  terms, then re-compared *nominal-blind* — every `FnSym` id and memoised
  hash blanked, structure, brands and the shared free variables kept):

  | site | mini impl | checker impl | common / one-sided | nominal-blind |
  |------|-----------|--------------|--------------------|---------------|
  | lam  | `Interp::lam_site` (`lams`, `lam_by_sym`) | `lam_info` (`lam_infos`, `lam_by_lam`) | 49 / 919+554 | 140 / 673+440 |
  | Π    | `fibres`, `fibre_by_sym` | `pi_infos`, `pi_by_dprod` | 159 / 467+467 | **621 / 3+3** |
  | cond | `conds`, `cond_by_sym` | `prop_infos`, `prop_by_chi` | 208 / 561+545 | **725 / 41+24** |

  *(The lam row said "build-only — the checker has **no** `as_lam`", and
  that was wrong; corrected here rather than appended to. The tg backend
  had `Shared::lam_by_lam`, the exact by-symbol index, read in three
  places — the beta head in `target_eq` and twice in the target-shape
  classification. What it lacked was `as_lam`'s shape, a decomposition
  returning the occurrence's holes and domain. The two sides were symmetric
  in what they stored and asymmetric only in what they offered, which made
  the λ merge smaller than this row implied.)*

  **The λ third has landed** (task #125): `checker/src/lam_store.rs`, a
  `LamStore` on the `EnvCore` beside `ConstStore`, holding one `lam` symbol
  and one `Graph` per body shape for both engines. `mini`'s `lams` /
  `lam_by_sym` and the tg backend's `lam_infos` / `lam_by_lam` are gone;
  `Interp::lam_site` and the tg λ clause both call
  `EnvCore::lam_site`, which is the only place `define_abbrev` + `lambda_n`
  and the holes-first/binder-last argument order are now written down.
  `mini`'s `as_lam` reads the shared `by_lam` index, so it takes apart a
  lambda the *checker* minted.

  **What the merge bought, measured** (`envshare_tg.rs::cross_sweep_tutorial`,
  the 91 tutorial exports, one thread and one core per file, mini then
  checker):

  ```text
  lamTotal  sites=1481  mintedByMini=968  mintedByChecker=513
            askedByBoth=90  askedByMiniOnly=878  askedByCheckerOnly=513
            crossHitsChecker=616  crossHitsMini=0  inert=0  failed=0
  ```

  **90 shapes now name one symbol where they named two** — against the 49
  the table above predicted, because the duplication *cascades* and merging
  the leaves merges the nests above them. 1481 sites against 1522 keys
  across the two old tables is the same 41 shapes counted the other way.
  `crossHitsMini = 0` is the harness, not a finding: mini runs first, so
  every crossing is the checker reading mini's mint.

  **And what it did not buy, which is the more useful number.** Deleting
  the merge — the mutation that gives each engine its own key space again —
  reddens **one** test, the new one. `mini/tests/{tutorial,designed}.rs`
  stay green, the arena table is unchanged, and no gap or verdict moves.
  The merge removes a *hazard* (two carriers for one shape is now
  unrepresentable) and buys 90 shapes; it does not move a measured
  certificate, because the two engines mostly do not produce the same λ
  shape in the first place.

  **Why they do not**, traced on `034_boolType` and pinned as
  `envshare_tg.rs::the_lam_populations_are_disjoint_on_an_inductive_only_file`:
  nine shapes, four mini and five checker, **zero shared**. The two engines
  are not naming one lambda twice there, they are interpreting *different
  lambdas* — mini generates `Bool`'s recursor itself (the export's
  recursors are dropped at load) and skeletonises its own graph nest's
  bodies, while the checker walks the export's `Expr::Lambda` nodes. The
  shapes do not even share an arity: mini's are single applications of an
  arity-4 nest symbol to three holes and the binder, the checker's are `x`,
  `x h`, and a bare hole. **No change to lambda handling can merge those.**
  The divergence is upstream, in what each engine takes the declaration to
  be — which is what the tg inductive interpretation's deletion and A3's
  boundary gate are about, not this tranche.

  **Π and ∀ are the opposite case and are the obvious follow-on.** Their
  one-sided residues are, per file, *entirely* nominal — `piNomBlind*Only`
  and `condNomBlind*Only` are 0 on all but the four `12x_quot*` exports —
  so the same `LamStore` shape applied to `PiInfo`/`FibreSite` and
  `PropInfo`/`CondSite` collapses ~467 and ~545 duplicate mints
  immediately, which is an order of magnitude more than λ bought. That is
  a measurement in hand, not a plan: the λ merge was done first because it
  was the one named, and it turned out to be the third with the least to
  gain.

  **The Π third has landed** (task #151, 2026-08-11): `checker/src/pi_store.rs`,
  a `PiStore` on the `EnvCore` beside `LamStore`. `mini`'s `fibres` /
  `fibre_by_sym` and the tg backend's `Shared::pi_infos` / `pi_by_dprod` are
  gone; `Interp::fibre_site` and the tg `Π` clause both call `EnvCore::pi_site`.
  `mini`'s `as_pi` reads the shared by-symbol index, so it takes apart a `Π`
  the *checker* minted.

  **The prediction cashed, on the same 91-export sweep:**

  ```text
  piTotal   sites=646  mintedByMini=626  mintedByChecker=20
            askedByBoth=606  askedByMiniOnly=20  askedByCheckerOnly=20
            crossHitsChecker=4783  crossHitsMini=0  upgrades=0  inert=0  failed=0
  ```

  **606 shapes now name one symbol where they named two**, against λ's 90 —
  the order-of-magnitude the table above predicted, and the one-sided residue
  is 20+20 against a predicted 3+3 per file. `crossHitsMini = 0` and
  `upgrades = 0` are the harness, not findings: mini runs first here, so every
  crossing is the checker reading mini's mint and no entry ever needs
  upgrading. The checker-first order is a fixture of its own (below).

  **The one structural difference from `LamStore`: two engines want two
  depths.** The checker's `build_fibre` stopped after `image_symbol_n` +
  `dprod_symbol_n`; `mini` went on through the rest of `DProdN` and four
  universe lemmas, because it needs `dprod(h⃗,A) ∈ U(c)` and the checker never
  asks. Always building the deeper one would charge the checker
  `dprod_members_n`, `dprod_subset_funspace_n` and the universe layer at every
  one of the 621 fibres it interprets. So the site is **tiered** — `Fibre` is
  what the symbol *is*, `Full` is what mini proves about it, built on the first
  ask that wants it and **upgrading the stored entry in place**, keeping the
  symbol. `a_checker_minted_pi_is_upgraded_not_reminted` runs the checker
  first and pins `mintedByChecker=3, upgrades=3, crossHitsMini=14,
  upgradeFailed=0` with mini still accepting the file — without it the upgrade
  arm would be a green cell that cannot go red, since every other cell runs
  mini first.

  **And unlike λ, it moved a verdict.** `003_arrowType` used to carry
  `a_mismatched_defining_equation_is_declined_not_adopted`: its one definition
  interpreted to different bodies under the two dispatches, so the statement
  guard in `const_abbrev` refused mini's defining equation. It now
  **converges** and the equation crosses — because its divergence *was* the
  duplicate mint. The body is an arrow type, both engines built a `dprod` at the
  constant fibre, and the two terms differed **only in the symbol**: exactly
  `pi_store`'s header sentence, *a gap where reflexivity was the whole proof*.

  That cell was therefore passing for the wrong reason — measuring the defect,
  not the guard — and a fixture that green-lights on a defect stops testing the
  moment the defect is fixed. It is **restated, not deleted**: `003` keeps a
  cell (`the_arrow_type_converged_because_its_pi_symbol_is_now_one`) asserting
  the convergence *and* that the two engines ask for the same Π shape, so the
  cell says why rather than merely that; and the guard's falsifier moves to
  `004_dependentType`, whose divergence is genuine. **The guard population is
  not lost with it**: `declinedByCheckerDefeq` is **20** over 20 divergent files
  after the merge.

  Everything else is flat, as λ was: `init-prelude`'s ledger is byte-identical
  (escapes 2 232, gaps 15 734, 159 803 derived), the arena is 152/0/2, and the
  full `mini` and `nanoda_lib` suites are green.

  **`∀` is not in this tranche and is the remaining third.** The checker's
  `prop_infos`/`prop_by_chi` and mini's `conds`/`cond_by_sym`, ~545 more
  duplicate mints, are the same pattern with one hazard `Π` does not have: the
  checker's `build_cond` takes the domain parameter at the canonical slot
  `hole_var(k)`, while mini's `cond_site` takes a `fresh_var()`. The keys agree
  (the key is the fibre skeleton, which mentions neither) but `phi` and
  `params` do not, so the merge needs mini moved onto the canonical slot first
  — a change to a derivation, not a table move. Doing it here would have made
  one commit that both merges a table and alters a proof.

  So the Π divergence is **99.5% same-skeleton-two-symbols** — the one-sided
  counts are equal file-by-file across all 89 exports, and sampled pairs are
  identical terms up to the interior `FnSym` id (the shared canonical
  variables even carry the same ids: B1/B2's hole series is genuinely one) —
  and cond is 94% the same story. That population is erased *by
  construction* by **one mint path per nominal object on the `EnvCore`**,
  not by sharing tables between two minters: a `lambda_n`/`dprod` symbol is
  nominal, so the mint is part of `⟦e⟧`'s answer, and two agreeing
  implementations are a coincidence maintained by hand (`bfaeaa9` was such a
  hand-fix). The genuine skeleton disagreement after blinding is **3+3 Π and
  41+24 cond shapes corpus-wide** — small — while **lam keeps the real
  residue** (673/440), confounded by surface asymmetry: mini interprets
  lambdas the checker's walk never reaches and vice versa, and the checker
  never decomposes at all. Separating lam's surface from its disagreement
  needs the paired per-subterm run the one-parse arena now permits (both
  dispatches over the *same* `ExprPtr`s); that measurement gates the lam
  mint's design and is the first step of the mint-unification tranche.

  **Why the raw one-sided counts are equal file-by-file** — the mint
  duplication *cascades*: leaf keys agree (they are built from the shared
  canonical variables, whose ids are identical on both sides — `Free(4740)`
  in the sampled pairs, so B1/B2's series is confirmed genuinely one), and
  every key that nests an earlier-minted site symbol differs *only through
  that inner symbol's id*. One shape keyed once per engine, at every
  nesting level: equal counts, disjoint keys.

  **The paired-subterm run** (`route_tg.rs::paired_subterm_lam_divergence`),
  which forces the surface equal — both dispatches interpret exactly each
  definition-like declaration's type and value per scheduled σ, the same
  `ExprPtr`s over one parse and one core — de-confounds the lam residue:

  | site | raw common / one-sided | nominal-blind |
  |------|------------------------|---------------|
  | lam  | 39 / 534+81            | 86 / 384+**32** |
  | Π    | 82 / 253+103           | 180 / 153+**5** |
  | cond | 90 / 304+192           | 248 / 145+**33** |

  The remaining mini-only excess is not disagreement but **inference
  closure**: mini's `infer_type` interprets the *types of* subterms and
  mints along its whnf/def_eq work, where the checker's bare `interp(e)`
  touches only `e`'s structure — so a genuinely disagreeing shape, present
  in both inputs, shows up one-sided on *both* sides, and the checker-only
  blind column bounds the disagreement: **≤32 lam, ≤5 Π, ≤33 cond shapes
  corpus-wide**, concentrated and nameable by file — lam: `027/028/029`
  (peano, 4+8+9, Nat-recursor-adjacent values), `076/079/080/081/093/105`
  (1–2 each, projection and recursor-value shapes); Π: `072` (2),
  `081_PSigma` (3); cond: `072` (8), `099/101/102/105` and neighbours (2–4
  each, Prop-valued ∀ in eliminator types). This is B0's "recursor-adjacent
  lambda bodies" scope, now with a per-file work list. The asymmetry worth
  stating for the design: the checker's lam side is **build-only** — no
  `as_lam`, no `lam_by_sym`, because its dispatch only constructs — so
  under one mint path it *gains* a decomposition capability it never had;
  unification here is one side gaining, not two compromising. The
  **nominal-mint census**, one line each: prelude/tower/machine — one
  (B1/B2); canonical binder and hole variables — one (B1/B2, confirmed by
  the measurement); constant carriers — one *store*, still two mint paths
  behind adopt-and-check (B4); lam/Π/cond sites — two each (the table
  above); undetermined-Π (`undet_syms`) — checker-only by construction
  (mini is ground-only); inductive carriers, nests and recursor packages —
  two (`IndApparatus` vs `gen_inds`/`gen_recs`/`rec_nests`), and the
  checker-side pair splits into two subsystems with different fates
  (measured entry counts over the 91 exports, temporary instrument at the
  two entry points): the tg backend's inductive *interpretation*
  (`walk_spec`/`rec_nest`/`gen_*_nest`) was called the straight
  `IndApparatus` duplicate and put in deletion-scope under "inductive
  handling comes from the mini side" — **and that scoping does not survive
  measurement; see the two boxes below**; nanoda's inductive *acceptance* (`checker/src/inductive.rs`,
  1703 lines, + `quot.rs`, 275) is entered **3 times under `Split`** —
  exactly the three fallback inductives, so it is the counted fallback's
  substance, not dead weight — **0 under `ForceMini`**, **102 + 24 under
  `ForceChecker`**, and never on a routed `init-prelude` (zone A
  budget-declines upstream). Mini's zone A does full kernel acceptance on
  inductives — `checkCtorParam`: universe bound then strict positivity
  (`kernel.rs:4398`), recursor synthesis in `add_block` — with rejection
  parity pinned by the `bad/` corpus and `check-mini-vs-nanoda`; what it
  does *not* do is nanoda's mint-and-compare against the export's recursor
  entries (§3.8's boundary, track A3). Deleting `inductive.rs` therefore
  costs three things, priced for the owner's call: the fallback target for
  inductives mini declines (052/113/114 would have no acceptance-side
  cover), the `ForceChecker` comparison path and with it the differential
  oracle for the declaration kind, and the only mint-and-compare validation
  of export recursors until A3 lands.

  ### The tg inductive interpretation is not separable from ι — measured

  Attempted under task #125 and **stopped before the deletion**, because the
  entry-count pricing above measured the wrong entry points. Two findings,
  both instrumented rather than read off the call graph.

  **1. The four functions are one subsystem rooted at `rec_nest`, and
  `rec_nest` is on the conversion path.** The call graph is
  `rec_nest → rec_bottom → gen_rec_bottom → gen_ty_nest → gen_ind →
  walk_spec`, so `walk_spec`/`gen_ty_nest`/`gen_ctor_nest` cannot go without
  `rec_nest`. And `rec_nest` has two callers, *neither* of them a
  declaration-kind dispatch: `interp`'s constant arm (`tg.rs:8172`), which is
  what gives `⟦T.rec⟧` a defining equation and so "is what makes iota
  reachable at all" in that site's own words, and `derive_iota`
  (`tg.rs:11183`) under `Certifier::iota`, which `tc.rs` calls at **every
  recursor redex in every file**, inductive declarations or none.

  **2. The price, counted.** A temporary pair of counters at `derive_iota`'s
  `rec_nest` call, over the 91 tutorial exports, one process per file: ι is
  asked on **8** exports and `rec_nest` answers on **4** —
  `073_boolRecEqns` 2, `075_nRecReduction` 6, `076_listRecReduction` 5,
  `116_rtreeRecReduction` 1 — **14 successful ι derivations** that the
  deletion turns into `Certifier::iota` admitting. With them, **10 functions
  — ~1,782 lines, contiguous at `tg.rs:11052–12962`** — keep compiling and
  stop being reachable: `derive_iota`, `derive_iota_core`, the four `fire_*`
  (`enum`/`nat`/`general`/`list`), `nest_chain`, `gen_minor_typed`,
  `mem_along` and `mem_along_c`. Every `nest_chain` and `mem_along*` call
  site was checked to be inside one of those, so none of them is shared with
  the general typing path.

  *(An earlier draft of this box, and the commit that added it, said "19
  functions (1,774 lines … the five `fire_*`)". Wrong on both counts —
  there are four `fire_*` and ten functions — and the line total was close
  enough to look verified. It came from a delegated census whose report
  never reached the seat that wrote it down, and it is corrected here rather
  than appended to. The findings around it are first-hand: the call graph,
  the two `rec_nest` callers, the 14 ι derivations and the `Unique` counts
  below were each measured in this worktree.)*

  That cost is real and it is not an `IndApparatus` duplicate:
  `IndApparatus` is mini's *declaration-side* construction, while what
  `rec_nest` does at `interp` and `derive_iota` is give the *conversion*
  checker something to ι-reduce with. **It is also #126's substrate** — that
  tranche gives `whnf`/`def_eq` evidence-carrying signatures, and handing it
  a conversion path whose ι step had silently become an admission is
  precisely the interleave the sequencing was meant to prevent. So the
  deletion wants a decision it has not had: *what certifies ι for the checker
  afterwards*. Until that is answered it is not a cleanup, it is a capability
  being dropped.

  ### `LocalKey::Unique` does **not** become unreachable — measured

  The claim under test was that deleting the tg inductive interpretation
  would strand `LocalKey::Unique` (`tg.rs:14178`), because that
  interpretation mints uniques on the certification path while
  `inductive.rs` — which stays — uses them only on the acceptance path. **It
  is false**, and the counter-example needs no argument about reachability.

  There are two construction sites. `unique_key` (`tg.rs:14186`) is the
  inductive-interpretation one and does die with it. The other is `interp`'s
  own `Expr::Local` arm (`tg.rs:8296`), which the deletion does not touch,
  and it is fed by exactly the module that stays: `inductive.rs` (17
  `mk_unique`) and `quot.rs` (11) open every telescope binder at a unique
  local, `TypeChecker` installs the tg backend unconditionally
  (`tc.rs:378`) and routes a bare `Expr::Local` to `certifier.ty_local`
  (`tc.rs:748`), which interprets it. `Dropped::{Inductive,Quot}` discards
  the resulting *certificate*; the `interp` call has already happened.

  Counted at both sites over the 91 exports, the decisive cells are the
  exports where the general site fires and the inductive one never runs at
  all: `036_andType` 4/0, `040_eqType` 2/0, `041_natDef` 2/0,
  `042_rbTreeDef` 24/0, `062_andRec` 4/0, `066_eqRec` 2/0, `067_nRec` 2/0,
  `068_rbTreeRef` 24/0, `070_existsRec` 7/0, `077_RBTree.id_spec` 26/0,
  `094_ruleK` 2/0, `118_accRecReduction` 15/0. So the `Unique` arm stays,
  `LocalKey` keeps both cases, and only `unique_key` itself (6 lines) is
  freed by the deletion. `open_level`'s `FVarId::Unique(_) => 0` arm
  (`tg.rs:4521`) is a read of an existing unique and stays either way.

  Retiring `unique` "completely", or leaving it out of `LocalKey` for
  certification purposes, therefore needs `inductive.rs` and `quot.rs` to
  stop opening telescopes at unique locals — a change to the acceptance path
  this document has just argued should stay.

* **B6** — the first authoritative inductive consumer — **landed for `Nat`**
  (2026-08-11). The declaration loop still dispatches each declaration once:
  mini alone handles the `Nat` group; TG alone handles the following
  definitions and theorems. What changed is the semantic handoff. `Nat`,
  `Nat.zero`, `Nat.succ`, and `Nat.rec` are read from B4's mini-owned entries;
  the two engines share one `NatClause` on `EnvCore`; and TG contracts the
  mini-published successor and recursor nests through B5's `LamStore` beta/body
  certificates. There is no TG Nat carrier, no TG Nat recursor nest, no
  fallback validation pass, and no abbreviation equation invented to bridge
  two interpretations.

  `nat_char_equations.ndjson`, before → after: checker-visible store slots
  **21 → 30**, mini typings adopted by TG **0 → 15**, declined typings
  **16 → 3**, stored definition typings **0 → 9**, and `ty_const`'s no-evidence
  row **116 → 59**. A deliberately incomplete intermediate implementation
  adopted the carriers but retained TG's abbreviation-only iota path: it made
  all 23 Nat iota sites fail and raised total TG gaps **172 → 291**. Consuming
  the shared graph certificates restores **10 zero + 13 successor** iota
  derivations and the total to **172**. Thus the aggregate is neutral while
  real typing evidence moves across the seam; the remaining 172 gaps have the
  same pre-existing provenance rather than being paid for by a second checker.

  The mutation ratchet in `checker/tests/unified_cli.rs` cuts the fixture at
  the declaration boundaries after `recAdd`, `recAddZero`, and `recAddSucc`.
  Their TG totals are **0 / 1 / 7**; the latter two compute **1 zero / 1
  successor** iota site and contain neither "constructor has no defining
  equation" nor "inductive has no defining equation". The next blocker is
  therefore not Nat ownership: it is the TG typing residue around `Eq.refl`
  and conditional lambda/application premises (`ty_premise_missing`, then
  `nat_eq`). Level-polymorphic store reuse remains the separately queued
  tranche; `Nat.ble` synthesis and projections are explicitly outside B6.

* **B7** — the first authoritative projection consumer — **landed for direct
  class-(T) constructor redexes and projection congruence** (2026-08-11).
  Mini publishes the exact `Translated` value it built for the inductive at
  each ground σ; `EnvCore` builds at most one `DeclProj` over that translation,
  lazily on first projection use. `DeclProj` now retains the generalized
  computation rules it already had to derive instead of dropping them after
  constructing its typing/η package. TG interprets every projection of such a
  declaration with the shared machine's tuple projection, lifts structure
  equalities through that same composite by Leibniz, and for a direct
  constructor redex composes the shared lambda contractions, mini's stored
  constructor abbreviation, and the retained computation rule. There is no TG
  structure carrier, no parallel projection theorem, and no second declaration
  check.

  On `proj_reduced_subject.ndjson`, real derivations **210 → 226**, total TG
  gaps **47 → 31**, and `proj_reduce` **7 → 5**. On the independent stuck
  projection/congruence fixture, real derivations **488 → 499**, total gaps
  **47 → 36**, and `proj_reduce` **4 → 3**. The controls are exact:
  `proj_reduced_carrier` remains **139**, `field_in_u0_by_carrier` remains
  **0**, and the full Nat handoff fixture remains **172**. The ratchet in
  `checker/tests/unified_cli.rs` also pins the one-loop route counts and the
  absence of both the retired opaque-projection congruence mismatch and a
  shared-lambda body interpretation drift.

  The cost is measured rather than hidden. Median retired instructions over
  three `perf stat -e instructions:u` runs, same debug-with-optimisation
  binaries: `proj_reduced_subject` **4,254,386,335 → 4,677,391,237**
  (**+9.94%**) for constructing and consuming its first projection package;
  the larger `nat_char_equations` control **9,926,219,756 → 9,976,861,130**
  (**+0.51%**). That is one lazy derived package, not another Lean type-check
  pass; subsequent consumers read the same `Rc` from `EnvCore`.

  The named continuation is subject reduction. A redex such as
  `(mk2 α x y).fst` or `(pick α x y Two.a).fst` reaches a constructor only after
  δ/ι reduction of its subject. `TypeChecker::reduce_proj` computes that whnf
  trace, but `Certifier::proj_red` currently receives only the projection
  endpoints. Until the subject's certificate is threaded into that interface,
  TG can soundly consume the direct constructor theorem but cannot compose it
  in front of the reduced-subject cases.

* **B8** — projection subject traces cross the checker/TG boundary — **landed
  for the non-increasing subset** (2026-08-11). `reduce_proj` now retains the
  exact memoised whnf trace which exposed the constructor. A dedicated trace
  node certifies that subject reduction on demand and passes the reduced
  subject plus its certificate to `Certifier::proj_red`; TG composes it in
  front of B7's shared constructor abbreviation and computation theorem. No
  normalisation is rerun, no backend calls the checker, and a readiness query
  is a pure lookup of mini's already-published translation rather than an eager
  construction of the projection package.

  The readiness gate is load-bearing. An unrestricted version also exposed
  unsupported ι traces and made `proj_reduced_carrier` **139 → 167** gaps
  before the outer projection could decline. The landed gate admits the
  established beta/zeta/delta/sort rules and recursively ready projection
  steps, but not ι or an admitted step. Thus the δ cases and `nestedFst` now
  compose, while `recFst` remains the one `proj_reduce` residue until its
  `Two.rec` ι certificate exists. It also declines projection heads carrying a
  subsequent application spine, whose separate application-congruence leg is
  not yet recorded.

  On `proj_reduced_subject.ndjson`, real derivations **226 → 262**, total TG
  gaps **31 → 12**, and `proj_reduce` **5 → 1**. On
  `proj_stuck_subject.ndjson`, derivations **499 → 541**, gaps **36 → 9**, and
  `proj_reduce` **3 → 0**. The two exact controls are unchanged:
  `proj_reduced_carrier` stays **139** and `field_in_u0_by_carrier` stays
  **0**. The full Nat handoff also benefits from ready PProd projection
  subjects: derivations **2015 → 2035**, gaps **172 → 164**, and
  `proj_reduce` **18 → 14**, while all 10 zero and 13 successor ι ratchets stay
  fixed.

  Median retired `instructions:u` over three runs, same debug-with-optimisation
  binaries, moved from B7's `proj_reduced_subject` **4,677,391,237** to
  **4,740,693,840** (**+1.35%**) and `nat_char_equations`
  **9,976,861,130 → 10,076,244,553** (**+1.00%**). Every substantial command
  was capped at 8 GiB virtual memory. The next projection blocker is now
  precise: certify the currently gated ι subject family (the remaining
  `recFst` cell) before widening the gate; after that, record the application
  congruence leg for projection heads used as functions.

**Track D — the driver** — **landed** ahead of A2/A3, scoped to the evidence
axis, as `mini`'s `--route` flag (`mini/src/route.rs`, the driver;
`checker/src/routed.rs`, the checker's half). The policy function is
`Mode::pick` — `Split` is the owner's split (inductive constructions, the
quotient family and axioms → mini; definitions and theorems → checker), and
`ForceMini`/`ForceChecker` keep both single-engine runs reachable behind the
same flag. The seam is the `GroupEngine` trait: one declaration group in,
the gap/decline ledger out; certificates land in the shared store, and
nothing about dispatch, `whnf` or `def_eq` crosses it. The driver replaces
`Ledger::run`'s single call inside `check_file_with_interp` with an
interleaved walk — declarations in file order, each group handed to the
engine the policy picks, both engines over the run's one `EnvCore` — and the
checker's export entries follow their **route anchor** (constructors and
recursors to their inductive, the quotient family to `Quot`), so one
decision covers one group on either side. The asymmetry is in the return
types: a mini decline falls back to the checker as a counted, named event
(`fellBack:name=reason`), a routed name the export never saw falls back to
mini the same way, and export groups neither engine vouched for are swept,
checked and named (`strays`). What this stage deliberately does **not**
route is the acceptance axis: mini's zone A still checks the whole file
(1.58% of a mini run), because mini's `Environment` is grown by checking —
single-engine acceptance is track A's shared syntactic store, and the two
panic→status sites of §3.9 also remain (a checker rejection is still a
panic). `mini/tests/route_tg.rs` pins the policy (three modes over one
file), both crossing directions, the fallback and the stray sweep.

**The crossing under routing, measured** (`Split`, the same 91 exports,
`--no-modelgen`; the sweep behind the numbers is one `mini --route=split`
run per file): mini published 573 entries / 571 slots, the checker 88 / 156.
**7 typings crossed checker→mini** (`adoptedByMiniTyping=7`, `converged=7`,
on `052`/`072`/`113`/`114`) — the direction B4 measured at **0**, observable
for exactly the reason B4 predicted: with defs routed away, mini's
constructions finally *miss*, and `Checker::adopt_shared` fires in
production. The checker→mini reverse of B4's 52: **0 adopted, 284 typing
offers declined** at the statement guards — B4's 52 defeq adoptions were
mini's *def* equations, which mini no longer derives under `Split`; the
residue is B5's, unchanged. Three files regressed against `ForceMini` and
are named, counted and fallen back rather than netted: `052_reduceCtorParam
.mk`, `113_reduceCtorParamRefl.mk`, `114_reduceCtorParamRefl2.mk` decline
`ind-spec(…: parameter reduction)` under `Split` — and the cause, traced to
the store entry at the miss (first written here as an adoption-guard refusal
and corrected in place on the owner's challenge), is **B5's residue in the
other direction, after a fully successful crossing**: the shared store held
`id` with *both* certificate slots (`carrier_by=Checker`,
`typing=Some(Checker)`, `defeq=Some(Checker)` — `store_declar_typing` and
`const_abbrev` merged onto one carrier), `adopt_shared` took it (two of the
7 adoptions are exactly these), the arm's threaded `whnf_conv` δ-stepped
along the adopted equation — and then mini's β step (`beta_evidence`,
`kernel.rs`) asked `as_lam` to take the **checker's carrier** apart, and
the checker's lambda symbol is in no table of mini's dispatch:
`Gap::NotDecomposable`, seven times on `052`, §3.5's "structure it cannot
take apart" verbatim. Not an ownership failure and not a guard failure —
the environment delivered the def and its equation; what is missing is
B5's shared skeleton-site tables, which now have a production witness in
each direction. (One true code fact noted while ruling the guard out:
`adopt_shared` requires a typing and carries `defeq` only as a passenger,
so a defeq-only entry — e.g. a def whose typing was `Dt::Conditional` — is
invisible to mini. It was not the blocker here and loosening it is B5-scope
work, to be done with a claim-check mutation, not by argument.) The checker
checks all three groups via the counted fallback, and the corpus ratchet
under `Split` is 86 exit-0 + 3 exit-4 + 2 declines against `ForceMini`'s
89 + 0 + 2, which reproduces the unrouted run exactly (798 / 1014
published, B4's numbers, pinned by `route_tg.rs`). **External dependency, unchanged**:
checker's stage-1 scope wiring (THREADING-CENSUS §2) is what would turn the
checker's 156 slots into a typing per def and the 7 into a population
(§3.6); it is independent work, already sequenced first in PIVOT §5.

**The comprehensive merge, in progress** (the owner's correction of this
track's shape: one environment, one parse, one entry per declaration — "it
shouldn't matter which code created it"). The destination is now explicit:
there is one `checker` crate and one declaration loop, inductive groups take
mini's implementation, all other groups take nanoda's, and `--naive` selects
the old mini-only path. The top-level `mini/` crate disappears; its surviving
code becomes modules under `checker/`. Stage 1, **one parse, landed**:
the routed driver drives the checker over the `ExportFile` mini's load
installed as its arena (`mini::arena::installed_export_file`), so the joint
`NameKey` is an identity rather than an agreement between two deterministic
parses — and a real latent bug closed with it: under the `modelgen` filter
the export mini checks exists only in memory, so the replaced re-parse
handed the two engines **two different files**. Next, in order: one mint
path per nominal object on the `EnvCore` (sized above under B5 — deleting
the tg backend's duplicate inductive interpretation is part of it), then
the entry collapse — one carrier, no engine tag in any value, with
`adopt_shared`, the spelling guard, `divergent` and `alias` disappearing as
consequences. When the collapse lands, the crossing counters (B4's 52, this
track's 7/284, the 57 divergent keys) **become meaningless by construction
— a change of unit, not an improvement to zero** — and the ratchet that
must hold is the real one: `accept/decline/reject/exit4`, `gapped`,
`unsealed`, `moved − movedSealed` = 2546. The merge's acceptance test is
the `052/113/114` population: those files go green exactly when mini's β
can decompose the one shared lambda mint's sites.

**What routing does not buy, measured on `init-prelude`**: the routed
`Split` run (`--mutual --nested --no-modelgen`, release, 16 GB cap) stopped
after **22.34 T instructions inside mini's zone A**, at the recursor-type
budget refusal on `ByteArray.IsValidUTF8` — the stop
`NAT-REPRESENTATION.md` records — with the routed evidence axis never
entered. Zone A runs upstream of the routing seam, over the whole file,
because mini's `Environment` is grown by checking (§3.7): routing buys
certificate sharing and the def-evidence escape, not acceptance reach, and
`init-prelude` under `Split` waits on track A exactly as this section
already says. The same run surfaced a latent verdict defect, fixed with it:
since `233bbc1` neither budget site ever attached the `budget: ` prefix the
run seam classifies a *decline* by, so a budget refusal printed `reject` —
a true file in the population of false ones — and no committed fixture
exhausted the budget, so nothing could go red. Both sites now leave through
one funnel (`kernel.rs::budget_refusal`) and
`mini/tests/budget.rs` + its generated fixture are the cell, red before
the funnel and green after.

## 6. σ, and what this design assumes about it

The syntactic environment has no σ dimension on either side (declarations
carry symbolic params; mini's zone A runs symbolic, `interp.rs:39–44`;
nanoda's schedule multiplies checks, not entries, `tc.rs:305–319`). The
semantic store's keys do carry ground levels today, on both sides, in
already-convergent shapes — so B3 defines the joint key once, and mode B
later collapses it to `NamePtr` at that single definition site. Nothing in
either track waits for mode B; mode B consumption itself still waits on the
`inductive.rs:1269` instantiate-and-compare change, unchanged from PIVOT
§2.3.

## 7. Against PIVOT.md — where this agrees, and where it presses

Agreements: `derived/` untouched (every shared object is reached through
`over`-constructors `derived/` already grew); mini remains the acceptance
oracle and executable specification; new capability in new files, two cited
upstream edits; no runtime bridge between the two `Expr`s; mode A now, mode
B behind the recursor change; stage-1 threading as the first checker-side
work item — PIVOT §0.4 already stated that the pivot is "move the inductive
work onto an engine that is already cached **and finish that engine's
threading**", and §3.6 here is the same dependency reached from the other
side.

Where it presses:

1. **The shared store re-orders the pivot: one signature first, one engine
   later — and possibly never, per module.** PIVOT's plan ports mini's arc
   module-by-module onto checker's APIs; track B instead makes mini's arc
   *usable in production* through the joint store while it remains mini's
   code. The port then becomes an optimisation to take per module, by
   measurement, where mini's dispatch cost matters — not a precondition for
   a certified `init-prelude`. Given PRELUDE-COST.md's finding that the wall
   is def-shaped (`List.get.match_1`, ≥ 11.00 T alone) while the inductive
   constructions are not the bottleneck, the re-ordering is the shortest
   path to the owner's active goal.
2. **"Not a marriage of two engines" (PIVOT §1.3) holds with one
   qualifier**: the marriage happens at the environment — signature, store,
   funnels — while the engines remain two dispatches over it. The first
   version located the no-marriage line between the engines' evidence; the
   correct line is between shared statements and private scratch (§3.3).

## 8. If unification were the wrong shape

The first version answered "partially — unify syntax, not evidence", and
that answer was itself the wrong shape: it mistook the semantic half of the
environment for engine property, then read the resulting incompatibility as
a law (§0.4). The corrected finding: **everything that appears in a stored
statement unifies** — syntactic store and interpretation store both —
because the identity doctrine demands exactly one object per key per
composition domain, and the owner's proposal makes the domain the run. What
genuinely stays two is dispatch, per-declaration scratch, and diagnostics,
none of which any theorem mentions. If B0's prototype finds the skeleton
normal forms irreconcilable, the fallback is not separation but *shallower
sharing* (B5 scoped to constant-level objects, structural gaps counted) —
the store remains one, and no finding in this document re-opens the wall.

## 9. Not measured

* **The skeleton normal-form coincidence** — measured by B0
  (`explore/b0-shared-env`): full agreement on the inductive-free fragment
  after the arrow alignment; the recursor-adjacent lambda residue scopes B5.
* **The concurrency price of one store** — measured; §3.4 item 4 has the
  numbers and the decision.
* **Cross-engine adopt-and-check drift rates** — measured; §5 track B4 has
  the corpus numbers (52 adopted, 469 + 57 declined, 57 divergent keys,
  `alias` and `incoherent` 0).
* **The `init-prelude` projection under the split** — checker certifying the
  def population at `nested_model`-like cost is an extrapolation from PIVOT
  §4's 3.96 G vs 1,277 G and PRELUDE-COST.md's wall attribution, not a
  measurement; B4's measurement step is the test.
* **The `Interp::over` refactor size** — done, and it was construction
  plumbing as read: every `env` access became a statement-scoped guard, and
  the corpus ratchet plus one committed fixture
  (`mini/tests/fixtures/quot_lift_reduction.lean`) hold the one dynamic
  hazard that introduced — a guard held across a closure's second borrow.
  Instruction cost of the cells, measured over the whole 91-export tutorial
  loop (release, two runs each): 360.36 G before, 361.86 G after — **+0.42%**.
* **The adapter's cost on a mini-only run** (A1) and **the boundary gate's
  cost** (A3) — expected neutral / bounded by the `keep_export_recursors`
  walk; the ratchets measure them.
* **The K-divergence corner in mixed runs** (§3.8) — needs a designed
  fixture before track D defaults on.
* **The `is_recursive` per-block fix** — small by reading
  (`inductive.rs:12–30`); not prototyped.

Sources: `kernel/src/{term.rs, thm.rs}`; `checker/src/{env.rs, tc.rs,
inductive.rs, tg.rs, util.rs, parser.rs, sealed.rs}`; `mini/src/{env.rs,
kernel.rs, convert.rs, run.rs, interp.rs, ev.rs, arena.rs, mutual_aux.rs,
nested_splice.rs}`; `mini/tests/mutual.rs`; `derived/src/nat/apparatus.rs`
— all read in this tree at `f29c7ef`; PIVOT.md; PRELUDE-COST.md;
MODELGEN.md §4; MONOMORPH.md §1, §8; MINI-DESIGN.md §0, §11;
THREADING-CENSUS.md §2; README.md.
