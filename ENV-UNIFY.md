# Unifying the global environment — a design and a recommendation

*2026-08-09. A design, on the owner's instruction, for the step after #120:
one global environment for `checker/` and `mini/`, leaning toward nanoda's
design, to unblock choosing one checker or the other per declaration. Not an
implementation; nothing is landed except this document. Everything cited was
read in a scratch worktree at `679b213`; nothing here is measured beyond what
the cited documents and tests already measure, and §9 names what is not.*

## Verdict

**Unify the syntactic environment on nanoda's existing store, exactly as it
stands; do not unify the evidence stores.** The recommendation in one
paragraph:

* **The one global environment is `checker/`'s `DeclarMap` + `Env` view**
  (`checker/src/env.rs:236` — the parse-time-complete `FxIndexMap`, the
  `cutoff` visibility slice, the `temp_declars` overlay), **unchanged**. Not
  one line of `checker/src/env.rs` needs to move: this recommendation *adds
  beside* upstream, it does not rewrite it (§5).
* **`mini`'s `Environment` becomes a view of that store** — a read adapter
  beside the #120 seam (`mini/src/arena.rs`), serving `ConstantInfo`-shaped
  answers from the installed export file's `DeclarMap`, plus an owned overlay
  for the two things mini computes that the map does not hold: its generated
  recursors and the in-progress declaration group (§5.2).
* **Mini's evidence apparatus does not move into the environment, on either
  side.** Both codebases already keep the syntactic store evidence-free on
  purpose (`mini/src/env.rs:14–20`; `checker`'s `Shared` lives in `tg.rs`,
  not `env.rs`), and the theorems in `Interp`/`IndApparatus` and in `Shared`
  are over two different kernel signatures and cannot cross by container
  surgery. They stay **parallel per-engine structures behind the same
  `NamePtr` keys** (§4). Per-declaration choice on the *evidence* axis is the
  PIVOT port, not an environment refactor; the unified environment delivers
  per-declaration choice on the **acceptance** axis, and that is what it
  should be judged against (§3).
* **The boundary invariant that makes handover sound** is nanoda's own
  discipline applied at the seam: a group checked by mini is readable by
  nanoda only once mini has compared its *generated* constructors and
  recursors against the *export's* entries — and that comparison already
  exists, tested, in `mini/tests/mutual.rs::compare_recursors` (§3.2).
* **Design for ground input in the sense of not adding a level dimension**:
  the syntactic environment is already σ-free on both sides, so this work
  neither waits for mode B nor changes under it; the `(name, ground levels)`
  dimension lives only in the evidence stores and dies there when mode B
  lands (§6).

## 0. Where the brief is wrong or needs narrowing

Per the standing instruction, before anything is built on it:

1. **There is no `ctor_rules` table in `mini`.** The `ConstKey`-keyed tables
   on the constructor side are `ctor_untranslated` (`mini/src/interp.rs:589`)
   and the per-constructor certificate vectors inside `Translated`
   (`ctor_abbrev`, `field_abbrev`, `rec_dom_abbrev`, `interp.rs:687–717`);
   the per-constructor *rules* live on `ConstantInfo::Recursor::rules`, keyed
   by constructor `Name` inside the entry (`mini/src/env.rs:123`). The census
   below (§1.3) is the complete list.
2. **The `isRec` panic population is six files, not four-plus-one.** Four
   `mini/tests/fixtures` files (`mutual_index_sorts`,
   `mutual_index_telescopes`, `mutual_one_recursive`,
   `mutual_prop_even_odd`), one `modelgen/tests` fixture (`mutual_nonrec`),
   and one `modelgen` *output* shape (`nest_odd_shapes`' generated block, a
   member with no constructors) — MODELGEN.md §4, measured file by file
   there. The cause is one: upstream recomputes `isRec` per member by
   scanning binder types, Lean sets it per block
   (`checker/src/inductive.rs:30`).
3. Everything else in the brief checked out: `IndApparatus` at
   `interp.rs:395` with `mach`/`chain`/`decls` and the identity doctrine;
   `model_of`/`model_iota` (`interp.rs:631`, `:645`, plus the `nested`
   membership table at `:654` the brief did not name); the mode B refusal at
   `inductive.rs:1269`; #116 closed (`MONOMORPH.md` §1.2 property 4, §1.3).

## 1. The census

### 1.1 The syntactic stores

**`checker/`** (`checker/src/env.rs`, `parser.rs`, `util.rs`):

* `declars: FxIndexMap<NamePtr, Declar>` — built **complete at parse time**,
  insertion-ordered, one entry per export line. `Declar` has eight kinds:
  Axiom, Quot (×4 entries per quotient), Theorem, Definition (with
  `ReducibilityHint`), Opaque, Inductive (`InductiveData`), Constructor
  (`ConstructorData`), Recursor (`RecursorData` with `rec_rules`, `is_k`).
* `Env<'x,'a>` (`env.rs:236`) — a *view*: the map, a `cutoff` index
  (`EnvLimit::{Empty, ByIndex, ByName, PpUnlimited}`), and an optional
  `temp_declars` overlay used for nested-inductive specialisation.
  Checking never inserts; visibility is sliced per declaration
  (`util.rs:258`: `EnvLimit::ByName(d.name)`) and per thread.
* `mutual_block_sizes: FxHashMap<NamePtr, (start, size)>`
  (`util.rs:221`, filled at `parser.rs:802`) — the block extent an
  inductive's check runs over (`inductive.rs:31`).
* `notation` — parse artifact, `#[allow(dead_code)]` in the env.

**`mini/`** (`mini/src/env.rs`, `kernel.rs`, `convert.rs`):

* `Declaration` (`env.rs:49`) — five kinds: Axiom, Def (`DefKind`
  Def/Theorem/Opaque), Quot (one entry), Inductive (constructors **bundled
  in**), Mutual (a block as one declaration, `env.rs:67`). Recursors are
  **not** an input kind: `parseRecInfo` is a stub, the export's recursors are
  dropped at load (`convert.rs:20–21`, `:546`).
* `Environment` (`env.rs:156`) — `consts: HashMap<Name, ConstantInfo>` grown
  by `kernel::add` **as declarations are checked**, plus the `owners` index
  (constructor/recursor ↦ its inductive, `env.rs:164`, filled at
  `kernel.rs:4763`, `:4849`).
* `ConstantInfo` (`env.rs:89`) — four kinds: Opaque (axioms, `opaque`,
  constructors), Inductive (with **computed** `num_indices`
  (`kernel.rs:4654`) and `is_unit` (`kernel.rs:4695`)), Def, Recursor —
  the last **generated** by `add_block` (`kernel.rs:4830–4863`): open-body
  rules, `num_motives`, and a computed `k_type: Option<E>` where the export
  has an `is_k: bool` flag.
* Since #120, `Name`/`Level`/`E` *are* `NamePtr`/`LevelPtr`/`ExprPtr` in the
  binder-erased normal form, all in the one installed arena
  (`mini/src/arena.rs`). `convert.rs` already reads the parse-time
  `DeclarMap` to produce `Declaration`s — mini is *already* a reader of
  nanoda's store at load time; what it is not yet is a reader at **check
  time**.

### 1.2 The run shapes, which the design must respect

* `checker`: parse → complete map → check each declaration against
  `Env` at `ByName` cutoff, serially or on N threads
  (`tc.rs:255`, `:322`, `:330`). Constructors and recursors get a light
  standalone info-check (`tc.rs:280–289`); their real validation is the
  inductive's own check, which **mints** the recursors and def_eq-compares
  them against the export's entries (`inductive.rs:36–95`).
* `mini`: load → zone A, one `kernel::add` per declaration into the growing
  `Environment`, abort on first rejection (`run.rs:181–195`) → zone B, the
  evidence pass over the **completed** environment (`nested_splice::recognise`
  at `run.rs:248`, `mutual_aux::expand` at `:261` — which *clones the whole
  environment* and substitutes encodings under the blocks' own names
  (`mutual_aux.rs:940`) — then `Ledger::run` at `:265`).

The two axes decouple on mini's side already: zone B needs the completed
environment, not the fact that zone A produced it. That is load-bearing for
§3: in a mixed run, mini's certification pass can still run over the whole
unified environment regardless of which engine accepted each group.

### 1.3 The evidence-side state, complete

**`mini`**: `Interp` (`interp.rs:76`) — `consts: HashMap<ConstKey,
ConstInterp>`, the lam/fibre/cond site tables ×2 keyings, `cumul`, `prelude`,
`dprod_fs`, the lazily-built `direct`/`eta`/`quotient`/`acc`/`rec_acc`
apparatus slots, `rec_acc_elims`, the label registries, `ConvStats`,
`lazy_fills`. `IndApparatus` (`interp.rs:395`) — `mach: Machine`, `chain:
IndChain`, and the tables: `decls`, `deprecs`(+failed), `dep_elims`, `props`,
`truncs`, `trunc_recs`(+f), `prop_fields`(+f), `trunc_fields`(+f),
`decl_fields`(+f), `decl_projs`(+f), `reindex`(+f), `indexed`,
`indexed_walks`, `props_ix`, `truncs_ix`, `trunc_recs_ix`(+f),
`prop_recs`(+f), `dep_recs_ix`(+f), `ctor_untranslated`, `untranslated`,
`rec_untranslated`, `model_of`, `model_iota`, `nested`, `acc`(+f),
`wrec`(+f), `trunc`(+f). Nearly every doc comment says the same sentence:
*identity, not memoisation* — a second build mints symbols no equation
relates to the first's.

**`checker`**: `Shared` (`tg.rs:1843`) — the same roles over checker's own
signature: `lam_infos`/`pi_infos`/`prop_infos` ×2 keyings, the ext/beta/
bridge theorem memos, `inds`/`rec_core`/`bool_rec`/`nat_rec`/`list_rec`/
`machine`, `gen_inds`, `gen_recs`, `opaque_syms`, `const_syms`, `param_syms`,
`idx_syms`, `lit_syms`, `ind_syms`, `rec_nests`, `gen_ty_nests`,
`gen_ctor_nests`, `declar_typings`, `declined_cond`, `false_anchor` — keyed
`(NamePtr::raw, Vec<Term>)` where mini keys `ConstKey = (Name, Vec<u32>)`
(`interp.rs:60`). Plus per-thread backend maps at `tg.rs:2397`.

Neither side stores evidence in its `env.rs`, and mini's header records that
the once-planned evidence-wrapping `MiniEnv` **was never built and does not
exist** (`env.rs:14–20`). The two codebases already agree on the boundary
this design keeps.

## 2. Where they genuinely differ — the concept table

| concept | `mini` | `checker` (nanoda) | genuine or spelling? |
| --- | --- | --- | --- |
| store lifecycle | grown by `add` as declarations are checked | complete at parse; checking validates, never inserts | **genuine** — and nanoda's shape is the one per-declaration routing and parallelism need |
| visibility | implicit (env = what was accepted so far) | explicit `cutoff` (`EnvLimit`), per-thread slices | genuine; nanoda's generalises mini's (mini = cutoff at the current index) |
| input declaration kinds | 5 kinds; ctors bundled, recursors absent, `Mutual` a first-class variant | 8 kinds, flat, one per export line; blocks linked by `all_ind_names` + `mutual_block_sizes` | genuine at inductives; each side can derive the other's shape from parse data |
| stored constant kinds | 4 (`ConstantInfo`); Theorem folded into Def, ctors into Opaque | the 8 input kinds, validated in place | spelling, except recursors (next row) |
| **recursors** | **generated** by the kernel: `T.rec`, open-body rules, computed `k_type: Option<E>`; export's recursors dropped | **read** from the export (`RecursorData`, closed lambda-nest rule values, `is_k: bool`), validated by mint-and-def_eq-compare | **the crux.** Same mathematics, opposite trust direction, different storage form. §3.2 is the reconciliation |
| K-rule datum | `k_type` — the type the major must have (what the reduction engine needs) | `is_k` — a flag (what the export carries) | genuine; each is computable from the other plus the inductive (`kernel.rs:4794–4804`), with one known semantic divergence (§3.2) |
| ctor bookkeeping | `owners` index + counts recovered from types | `ConstructorData { inductive_name, ctor_idx, num_params, num_fields }`, from the export (`bad/048` is the argument for reading, not inferring — `env.rs:87–98`) | mini's is thinner; both derivable from the map |
| inductive extra data | computed `num_indices`, `is_unit` | export-given `num_indices`, `is_recursive`, `is_nested`, `all_ind_names`, `all_ctor_names`; `is_recursive` **recomputed per member and asserted** — the six-file panic (§0.2) | overlapping core; each computes what the other reads. The recomputation is a bug to route around, not a design to adopt |
| reducibility hints | none (mini-lean has none; unfold order is the engine's own) | `ReducibilityHint` on Definition, drives lazy delta | genuine but engine-local: hints steer search order, not the judgement; the store carries them, mini ignores them |
| level params | `lparams: Vec<Name>` | `uparams: LevelsPtr` | spelling since #120 |
| quotient | one `Declaration::Quot`; kernel **generates** all four constants, `lift`/`ind` recursor-shaped (`kernel.rs:4460–4489`) | four `Declar::Quot` entries from the export, checked by `quot.rs` | same trust-direction split as recursors, smaller; same reconciliation |
| nested inductives | specialisation into scratch `Environment`s + restore (`nested.rs`); models recognised into side tables (`nested_splice.rs`) | `temp_declars` overlay + `is_nested`; specialisation inside `inductive.rs` | same role; nanoda's overlay is a first-class `Env` feature the adapter can reuse |
| duplicates | `insert_new` returns an error (a rejection) | parser `assert!` (a panic; mini catches it as a decline, `convert.rs:255–282`) | spelling at the file level — both kill the file — but the panic-vs-status difference generalises (§3.3) |
| eager vs lazy | `num_indices`/`is_unit`/`k_type`/recursors computed during `add`; literals `u64`, >10 declined | everything parsed up front incl. `BigUint` literals and block extents; `is_recursive` re-derived during check | genuine but small once the store is shared: mini's computed fields move to the adapter, computed once per group |

## 3. The requirement per-declaration choice imposes — stated before the recommendation

The owner's payoff is choosing one checker or the other per declaration. What
that actually requires:

**Both engines must *read* one store; neither engine may need to *write* it.**
Nanoda already never writes (§1.1). Mini writes today, but everything it
writes is either (a) a re-statement of export data (`Def`, `Opaque`,
`Inductive` entries), (b) derivable from export data (`owners`, `is_unit`,
`num_indices`), or (c) its generated recursors — which the export also
carries in its own form, with agreement between the two already tested (§3.2).
So mini's write path dissolves into a read adapter plus one engine-private
side table, and "checked" becomes a *status* on the shared map rather than an
insertion into a private one.

**The handover unit is the declaration group, and routing is decidable at
parse time.** A group is: one export declaration for Axiom/Def/Theorem/
Opaque; the whole mutual block **with its constructors and recursors** for an
inductive (nanoda checks exactly this extent, `inductive.rs:31`; mini takes
it as one `Declaration` and generates the recursors); the four `Quot`
constants together. Nothing smaller can hand over — neither engine can
validate a constructor apart from its block. Every input to the routing
decision (declaration kind, block shape, nestedness, presence of a `modelgen`
model for mini's nested route) is a parse-time fact, so the dispatcher never
needs to start a check to know where to send it.

**The boundary invariant.** When group G is marked checked by engine X, every
entry of G in the shared map must be validated in the sense the *other*
engine relies on downstream — because nanoda will delta-unfold a mini-checked
definition and ι-reduce with a mini-checked block's **export** recursor
rules, and mini will do the converse through the adapter. Concretely:

1. every entry's type is well-formed and its value (if any) has that type at
   the declared level parameters — both engines already do this for their own
   groups; and
2. for an inductive group, the export's constructor and recursor entries
   **agree with what the checking engine derived from the specification**.
   Nanoda already enforces (2) by construction — mint and def_eq-compare
   (`inductive.rs:85–94`). Mini today checks the spec and generates its own
   recursors but never compares them to the export's (`parseRecInfo` stub):
   on a mini-only run that is fidelity; on a mixed run it would be a hole —
   nanoda would ι-reduce with export rules *nothing checked*. Closing it is
   §5.3, and the comparison to promote already exists.

**What per-declaration choice does *not* require — and cannot get from an
environment.** Certificates do not cross engines: a mini theorem is a `Thm`
over mini's kernel `Env`, signature and `Machine`; a checker theorem is over
`Shared`'s. Making one engine's evidence consumable by the other means one
shared signature and one symbol-allocation history — that is precisely the
PIVOT port (the `Machine` coordination point, `tg.rs:1941–1953`), not a
container refactor. So per-declaration choice is an **acceptance-axis**
instrument. On the evidence axis a mixed run degrades gracefully and
observably: a declaration accepted by the other engine has no
`declar_typings` entry, so checker-side uses carry it as counted
assumptions/gaps — exactly the existing escape-ledger discipline — and mini's
certification pass, which reads the completed environment and not the
checker's history (§1.2), can still run over everything. If the owner's
intent was per-declaration choice *of the certifying engine*, the answer is:
that is the pivot itself; this refactor is its substrate, not its substitute.

### 3.2 The recursor boundary, in detail

The generated-vs-export agreement is not hypothetical future work.
`mini/tests/mutual.rs::the_generated_recursors_are_the_ones_lean_exports`
(`mutual.rs:590–749`) compares, for every fixture: the four counts, K-ness,
the type after positional level instantiation, rule count, rule order, and
every rule's right-hand side (peeling the export's
`fun params motives minors fields =>` against mini's open body,
`mutual.rs:694–713`). It passes with **one known divergence class**, recorded
there: a declaration whose resultant sort is a bare level parameter
(`PUnit : Sort u` shapes) is K-like to mini-lean and not to Lean
(`mutual.rs:642–674`). The comment argues it costs nothing observable —
Lean reaches the same conversions through unit-like eta, which mini also has.
For the unified store the direction of the divergence is the safe one: the
**map holds the export's data**, so nanoda reduces exactly as Lean does
regardless of who checked the group; mini's extra K-liberality stays inside
mini's own engine. The residual caveat — mini reading a nanoda-checked
`PUnit`-shaped group through the adapter gets `is_k = false` and is thereby
*less* liberal than mini-alone, i.e. exactly as liberal as Lean — is a
fidelity footnote to record, not a soundness issue, and §9 lists the
unmeasured corner.

### 3.3 Panic versus status

Nanoda signals refusal by panicking (`assert_eq!` at `inductive.rs:30`; the
mode B refusal at `:1269`; parser `assert!`s). A dispatcher that wants to
*fall back* to mini on a group nanoda refuses needs a refusal it can catch as
a value, at group granularity. Parse-time panics can stay (both engines agree
the file dies; mini already catches them, `convert.rs:266–282`). The
check-time ones on the known-divergence sites must become routable outcomes —
two sites, cited, minimal (§5.4). This is the one place the recommendation
touches upstream files at all.

## 4. Where mini's evidence apparatus lives afterwards

The brief's three options: a side table keyed off nanoda's declaration index,
a parallel structure, or a generic parameter. **Recommendation: parallel
structures, converging on shared keys — which is what both sides already
built.** The argument:

* **A generic parameter is the wrong shape.** `Env<Ev>` would make upstream's
  environment know evidence exists — a rewrite-scale upstream edit purchasing
  zero shared code, because `Interp`'s values and `Shared`'s values share no
  type and no signature. It also contradicts the boundary both sides
  independently chose (§1.3).
* **A single side table keyed off the declaration index is half right.** The
  keying is right; the *single* is wrong. The tables cannot merge while there
  are two kernel signatures (§3), and merging the containers without merging
  the signatures would invite exactly the mislabelling this project has paid
  for — a true theorem stored under a key another engine reads as being about
  its own symbols (`Shared::ind_syms`' doc, `tg.rs:2017–2031`, records this
  failure class).
* **What should be unified is the key.** Both stores already key constants by
  name-plus-ground-levels: mini's `ConstKey = (Name, Vec<u32>)`
  (`interp.rs:60`), checker's `(NamePtr::raw, Vec<Term>)` (`tg.rs:1954–2123`).
  Since #120, mini's `Name` *is* a `NamePtr`, so the two are one edit apart.
  Centralising one `ConstKey` definition at the seam (`mini/src/arena.rs`'s
  sibling) gives the mode B collapse — `ConstKey` → `NamePtr`, the brief's
  "widest blast radius" — a single definition site on the mini side instead
  of a crate-wide sweep.
* **The model tables ride along.** `model_of`/`model_iota`/`nested` are
  routing tables *filled from the syntactic environment* by
  `nested_splice::recognise` (`run.rs:248`) and read only by zone B. They
  stay on `IndApparatus`; the unified environment's only obligation to them
  is that `recognise` can read declarations through the adapter — which it
  can, it takes `&Environment` today and the view preserves that signature.

## 5. The recommendation, staged

Lean-toward-nanoda scorecard first, per the owner's instruction. **Toward
nanoda**: the store and its lifecycle (parse-complete, read-only, cutoff
visibility) — adopted wholesale, zero edits; the flat export-trusting
declaration entries as the shared truth, including recursors; the
mint-and-compare discipline, extended to mini at the boundary. **Not toward
nanoda, with reasons**: (1) mini keeps generating its recursors and keeps its
reduction-oriented `ConstantInfo` shapes — that fidelity is mini's entire
role as oracle (PIVOT §6), and the boundary check reconciles the two rather
than either yielding; (2) the per-member `is_recursive` recomputation is not
adopted — it is upstream's known divergence from Lean (§0.2), the map keeps
the export's field, and the assert becomes routable; (3) `Declaration::
Mutual` is not pushed into nanoda — the dispatcher derives the group from
`mutual_block_sizes`, and nanoda's shape is untouched.

The stages, smallest first, each landing green with the ratchet held, in the
#120 style. Note a scheduling constraint, not a design one: stages 1–3 edit
`mini/src`, where two seats are live (#121, the Nat clauses); sequence or
coordinate.

**Stage 0 — the oracle is already in the tree; extend its reach.**
`compare_recursors` runs over `mini/tests/fixtures`. Extend the sweep to the
tutorial corpus when checked out (the test's own header already gestures at
this) and pin the divergence ledger: zero rows outside the parameter-sort K
class. Buys: the boundary invariant's empirical footing, before any code
moves. Risks: none (test only). *(Verified in this study: the comparison
covers types, counts, order, and rule bodies — `mutual.rs:636–714`.)*

**Stage 1 — the read adapter (`mini/`, internal, behaviour-neutral).** A new
module beside the seam — `mini/src/genv.rs`, say — makes `Environment` a
view: `{ export-map access at a cutoff, overrides: HashMap<Name,
ConstantInfo>, owners }`. Reads resolve overrides first, then the map
(convert `Declar` → `ConstantInfo` shape on the fly: Def/Theorem→`Def`,
Axiom/Opaque/Constructor→`Opaque`, `InductiveData`→`Inductive` with `is_unit`
computed once and memoised, `RecursorData`→`Recursor` with rules' open bodies
obtained by peeling `num_params + num_motives + num_minors + num_fields`
binders — the exact arithmetic `compare_recursors` already implements — and
`k_type` computed from the owner when `is_k`). Mini's own `add` keeps writing
— into `overrides` — so **behaviour is bit-identical**: on a mini-only run
every read hits the override before the map. `mutual_aux::expand`'s
clone-and-substitute becomes a clone of the override map (`mutual_aux.rs:940`
— the base is shared and immutable). The in-progress group inside `add_block`
(members visible before constructors are checked, `kernel.rs:4709–4723`)
stays in the overrides exactly as it lands there today. Ratchet: corpus
verdicts (accept 89 / decline 2 / reject 0), the ledger rows, and the
fixture instruction counts, all unchanged. Buys: mini can *see* declarations
it did not itself insert — the precondition for everything after. Risks:
acceptance fidelity through the conversion (the `bad/048` class — which is
why the adapter reads the export's counts from
`ConstructorData`/`RecursorData` rather than inferring, the same rule
`convert.rs:29–36` already states and cites).

**Stage 2 — decouple "in the environment" from "checked by mini".** Split
`kernel::add` into fill (adapter-served, free) and check (the existing
logic), so the driver can mark a group *filled-but-foreign*. On a mini-only
run the two remain fused and nothing moves. Buys: the mixed-run read path.
Risks: the visibility schedule — a foreign-filled group must become visible
to mini at the same index it would have under `add`, which the cutoff
discipline gives for free; pin it with a three-element fixture per the
two-atoms rule.

**Stage 3 — the boundary gate (`mini/`).** Promote `compare_recursors`'
logic from test to a check that runs when — and only when — a mini-checked
group is to be marked usable-by-others: generated-vs-export agreement on
constructors and recursors (counts, K modulo the recorded class, types and
rule bodies at positionally-instantiated levels), quotient constants
likewise. Behind an option first, like `--mutual`; the corpus populations
MINI-DESIGN §0 pins must not move (the gate is off on the plain mini path).
Buys: invariant (2) of §3.2. Risks: cost — the comparison walks recursor
types, the largest expressions in an export; it is pointer-equality first
(one arena, binder-erased — `==` is `u32` comparison since #120) with def_eq
only on mismatch, so the expected cost is the walk `convert.rs` already pays
under `keep_export_recursors`.

**Stage 4 — refusals become values (`checker/`, the only upstream edits).**
The `is_recursive` assert (`inductive.rs:30`) and, when PIVOT §2.3's
instantiate-and-compare lands, the recursor-name match (`:1269`), surface as
catchable refusals at group granularity instead of process death — either a
`Result` out of `check_inductive_declar` or a narrowly-scoped catch in the
new driver. Two sites, cited in the upstream diff, per PIVOT §6's rule (new
capability in new files, minimal cited upstream edits). Buys: fallback
routing; also, independently, the six §0.2 files stop killing `nanoda_bin`.
Risks: upstream-diff growth (two hunks); the alternative — fixing the
recomputation to per-block, matching Lean — is *also* small and MODELGEN §4
calls it "`checker/`'s to fix"; the design works with either, and fixing it
properly shrinks the fallback population, which is the better end state.

**Stage 5 — the dispatcher (new file, no upstream edits).** A driver that
walks the `DeclarMap` in order, partitions into groups
(`mutual_block_sizes`), routes each group by policy — default nanoda;
mini where nanoda refuses; or both, as a differential gate at declaration
granularity (the mini-vs-nanoda comparison, today file-grained, becomes
group-grained for free) — marks status, stops at first rejection. Lives
beside `mini`'s CLI or as its own small crate; it is wiring, and it is the
owner's payoff. Ratchet: on corpora both engines pass, dispatcher verdicts
equal each engine's own; on the six §0.2 files, accepted via fallback — new
capability, new fixtures.

**Stage 6, optional and unblocking nothing above — key centralisation.** One
`ConstKey` at the seam (§4), so the mode B collapse to `NamePtr` is one edit
per crate. Waits on nothing; mode B consumption itself still waits on
stage 4's second site, unchanged from PIVOT.

## 6. σ, and what this design assumes about it

The syntactic environment has no σ dimension on either side and never did:
declarations carry symbolic `lparams`/`uparams`; mini's zone A "runs at
symbolic levels and simply has no `Interp` at all" (`interp.rs:39–44`);
nanoda's schedule multiplies *checks*, not entries (`tc.rs:305–319`). So:

* **This work neither waits for mode B nor is reshaped by it.** It can land
  against today's polymorphic corpus and against mode A output identically.
* **Design for ground input in the negative sense**: nothing new added at the
  seam or in the adapter takes a level key. The `(name, levels)` dimension
  exists only in the evidence stores, stays per-engine there (§4), and dies
  there when mode B lands — `ConstKey` → `NamePtr`, `declar_typings` et al.
  keyed by name, exactly PIVOT §2.1's list. The environment unification
  slightly *shrinks* that blast radius (stage 6) and otherwise does not
  interact with it.

## 7. Against PIVOT.md — where this agrees, and where it presses

Agreements, which are most of it: `derived/` untouched; mini remains the
oracle and executable specification (PIVOT §6) — this design extends that
role to *fallback acceptance engine*, a modest widening that stage 4's proper
`isRec` fix would mostly retire; new capability in new files with minimal
cited upstream edits (§6's rule, kept — the recommendation grows the upstream
diff by two hunks and rewrites nothing); no runtime bridge between the two
`Expr`s (the adapter reads parse artifacts through the #120 seam; the
closed-term bijection runs where it always ran, in `convert.rs`); mode A now,
mode B behind the instantiate-and-compare change (§2.3 there, stage 4 here).

Two places this document presses on PIVOT's framing rather than repeating
it:

1. **"Not a marriage of two engines" (PIVOT §1.3) needs one qualifier.** The
   dispatcher does put both engines in one process over one store. The
   reconciliation is the §3 finding: only the *acceptance* axis is married;
   the evidence axis remains single-engine per run, because theorems cannot
   cross signatures. The unified environment is also precisely the substrate
   PIVOT's own port wants — as coverage moves into `tg.rs` module by module,
   the dispatcher is the migration instrument that routes each inductive
   class to whichever engine has it, with mini's ledger as the
   per-group differential check.
2. **PIVOT reads the environments as already settled and never compares
   them.** Its §1.2 table maps mini's `Interp` store to `Shared` correctly,
   but the zone A stores — the subject of this task — appear only implicitly.
   The comparison here (§2) supports PIVOT's sequencing and adds one fact it
   did not have: mini is already a parse-time reader of nanoda's map, so the
   unification is completing a move #120 started, not opening a new front.

## 8. If unification were the wrong shape

The evidence says it is the wrong shape for the evidence stores and the right
shape for the syntactic store, and the split is the finding. For the
syntactic store, every difference in §2's table is either spelling (levels,
declaration-kind folding), derivable-at-parse (owners, `is_unit`, block
extents), or reconciled by an existing tested comparison (recursors,
quotients) — there is no concept either engine holds that the shared map
plus one engine-private side table cannot serve. For the evidence stores, the
opposite: identity-not-memoisation means every table is welded to its
signature, and a shared container would be a category error the codebase has
already paid to learn (§4). A recommendation that unified both would be
wrong in the second half; a recommendation that unified neither would leave
the owner's per-declaration payoff unreachable for no reason.

## 9. Not measured

* **The adapter's cost on a mini-only run** — expected neutral (reads hit the
  override map first; `ConstantInfo` is `Copy`-cheap since #120), asserted
  not measured. Stage 1's ratchet measures it.
* **The boundary gate's cost** on the largest fixtures — bounded by the
  `keep_export_recursors` walk `convert.rs:174–180` warns about; not
  isolated.
* **The K-divergence corner in mixed runs** (§3.2): no fixture exercises
  "nanoda checks the `PUnit`-shape, mini later reduces at its recursor
  through the adapter". Expected invisible (unit-like eta covers it, per the
  recorded comment); needs a designed fixture before stage 5 defaults on.
* **The `is_recursive` per-block fix** — size read as small
  (`inductive.rs:12–30` is the whole site); not prototyped, same status as
  PIVOT §8's mode B row.
* **Dispatcher overhead and mixed-run evidence-gap counts** — how many
  escape-ledger rows a realistic routing policy produces; nothing exists to
  run yet.

Sources: `checker/src/{env.rs, tc.rs, inductive.rs, tg.rs, util.rs,
parser.rs}`, `mini/src/{env.rs, kernel.rs, convert.rs, run.rs, interp.rs,
arena.rs, mutual_aux.rs, nested_splice.rs}`, `mini/tests/mutual.rs` — all
read in this tree at `679b213`; PIVOT.md; MODELGEN.md §4; MONOMORPH.md §1,
§8; MINI-DESIGN.md §0; CACHING-DESIGN.md; README.md.
