# INDEXED-ROW-AUDIT — five rounds on one declaration, and what would have found them at once

2026-08-06, at `5f65268`. Method: git archaeology over the five rounds
(`93bf2f7` → `df14738` → `45611ab`/`f32bbce` → `f9360d5`/`c234aad` → `eab73e1`),
complete greps with their patterns stated, a shape census over all 91 tutorial
exports, and a worktree probe that drove `IndexedDepRecursor::over_family` end
to end over `family_infinitary`'s declaration with a `?`-census on
`dep_rec.rs`/`dep_guard.rs`/`prop_rec.rs`/`dep_motive.rs`. No source was
edited; the worktree is removed. The sixth layer below is **measured, not
predicted**.

## 1. The common cause: one object, several spellings, identification implicit

The frame hypothesis — "no single answer to *at what binder depth is this
expression stated*, so every construction re-derives it" — is **true of layers
1 and 5 and of nothing else**, and it is stated *as documentation* where it
should be a type: `zoneb::ind_spine_at`'s header says "**The caller owns the de
Bruijn frame.**" `rec_field` returns `(γ⃗, e⃗)` with `e⃗` stated at depth
`d + |γ⃗|` and nothing in the return type records that; `local_type` hands back
a `∀z::γ. T p⃗ d⃗` whose spine is `|γ⃗|` deeper than the nest. Each consumer
redoes the arithmetic: `ctor_spec` got it wrong (layer 1), `ctor_ix::ctor_bottom`
got it wrong one construction later (layer 5), and **`class_p_ix.rs:358` has
the identical unshifted read today** — `ind_spine(&site.ind, &dty, np, ni, nf)`
with no `+ |γ⃗|` — live, fail-closed only because a `Forall` head cannot match a
spine. Found by grepping the seven `ind_spine` call sites, not by running
anything.

But layers 2, 3, 4 are not frame errors. The cause that covers all five, plus
the measured sixth, is one level up:

**One mathematical object is spelled independently at two or more sites; the
spellings are equal as terms on every degenerate shape, unequal on the general
one; and nothing states or checks the identification.** Each layer sits behind
one degeneracy that held over the *entire* corpus:

| degeneracy | spellings that coincide under it | layer it hid |
|---|---|---|
| `np = 0` | abstraction over `f⃗` = abstraction over `p⃗ ++ f⃗` | 2 (`ctor_abbrevs`) |
| every rec slot plain | `ctor_atoms` = `ctor_atoms_at(…, rec_sets(…))`; `minor_typed` = `minor_typed_at` | 3 (`Good::build`), 6 (`dep_guard`) |
| fibre = a point | `r(Injⱼ(•))` atom = `∀z ∈ Aⱼ` atom; point ih = fibre ih | 4 (`gval::matrix_atoms`, `carrier`'s `Hᵢ^skel`) |
| `|γ⃗| = 0` | depth `d` = depth `d + |γ⃗|` | 1, 5, and `class_p_ix.rs:358` |

Two sub-families, two homes for the invariant:

* **(a) Context re-derivation** (layers 1, 2, 5; live: `class_p_ix.rs:358`).
  The invariant: *an expression crossing a construction boundary carries its
  stating context* — binder depth for de Bruijn reads, the abstraction list for
  mints. It belongs in the **types at the zoneb boundary**: `rec_field` /
  `ind_spine` returning a depth-tagged expression (`{ depth, es }`) that
  `index_syms` / `infer_indices` consume by opening exactly that many binders,
  instead of a bare `Vec<E>` plus caller arithmetic. Layer 2 is the same shape
  in free-variable dress: `define_abbrev`'s abstraction list is part of the
  symbol's identity, and its three consumers proved so by all having to move.
* **(b) A degenerate spelling asserted as general** (layers 3, 4, 6). The
  invariant is the one the codebase already states locally — "one builder, so
  the two cannot drift" (`prop_rec::minor_atoms_at`), "a second inference would
  be a second chance to disagree" (`ctor_ix`) — applied globally: **the
  degenerate wrappers should not exist as callable entry points.** Complete
  grep, pattern `ctor_atoms(` excluding `_at` and the definition: exactly four
  callers remain — `family/trunc.rs:297`, `family/prop_rec.rs:807`,
  `family/dep_rec.rs:564`, `family/dep_rec.rs:799` — **all in the indexed
  recursor path, all general-blind**, while the non-indexed `dep.rs:417`
  already takes `ctor_atoms_at(…, rec_sets(…))`. Same for
  `premise::minor_typed` (the no-doms wrapper) at `dep_guard.rs:291`, and
  `dep_guard::typed_atoms`, which hand-spells `tⱼ ∈ W`, `vⱼ ∈ T`. Killing the
  wrappers turns every remaining misalignment into a compile error today.

So: not five independent bugs, and not quite the frame defect — two defect
families with one root (implicit identification of independently-spelled
objects), and the root predicts where the remaining instances are. The greps
above found two (class_p_ix, the ctor_atoms four) without executing anything.

## 2. The corpus is blind by *shape*, and fixtures help only up to consumption

Measured, a full parse of all 91 exports (102 inductive declarations):

* 35 are indexed — but they are `Eq` (no fields), `RBTree` (plain rec only),
  `SortElimProp{,2}` (no rec), `Acc`.
* 4 carry a function-typed recursive field — `RTree` twice (`np = 0`, `ni = 0`:
  non-indexed path, and the very degeneracy that made layer 2's two spellings
  one term) and `Acc` twice (telescope depth **2**, which takes
  `crate::direct`'s clause and is declined by `ctor_spec` before the general
  arm regardless).
* Indexed ∧ `np ≥ 1` ∧ depth-1 function-typed recursive field, the shape all
  six layers live on: **zero of 102**.

So the blindness is a **corpus property**: the code paths were unreachable, and
no strengthening of the checks could have made corpus runs informative about
them. "Corpus unchanged" was a true statement carrying zero bits about this
row — every one of eab73e1's ten mutations survived the corpus for the same
reason.

The caveat that bounds what fixtures buy: even *with* the fixture, one mutation
(`mem-at-raw-slots` — `ctor_abbrevs` naming the raw Lean field) was killed by
**nothing in the tree**, because the consumer declined one construction later,
before anything read the symbol. A fixture kills what its row *consumes*; a row
that ends at a decline shields every mint behind the decline. Three of the five
layers were silent-wrong-term failures precisely because they sat in that
shadow. Conclusion: more fixtures help exactly insofar as they push consumption
to the end of the pipeline (through the eliminator and its ι, into `constEv`);
below that line only exact-term pins and confluence checks (§3) see anything.

## 3. The check class for silent wrong terms: confluence between two routes

`index_congr` is the template and its mechanics generalise. Route 1:
`ctor_spec` mints `d⃗ᵢⱼ` at declaration time, in the γ-opened frame. Route 2:
`ctor_bottom` infers the same expressions at consumption time, in the nest's
frame. The check is `inst_all(axiom).concl().as_eq()?.1 != inferred → decline`,
**on the accept path** — a shifted read becomes a decline instead of a theorem
about another declaration's carrier. That is what caught layer 5, the only
layer with a guard waiting.

It generalises because every wrong-but-well-formed mint in this row *had* a
second route by construction — that is what made it wrong-able — and the
comparison is syntactic term equality on hash-carrying terms: near-free next to
the fixture's 10,267 sealed conversions. Complete grep: 16 `define_abbrev`
sites in `mini/src`. The interpretation-path ones each already have a
consumption site where the independently-derived term exists
(`retarget_subject` / `spine_eq`'s `held` drift check / `index_congr` are the
three existing instances of the pattern); the cost of the discipline is
plumbing, not proof search.

What confluence does **not** cover is the unconsumed mint (eab73e1's
survivor). Two closures: a no-orphan-mints assertion — at end of run, every
interpretation-path symbol's defining axiom was consumed by some sealed
theorem — or the pin-per-mint discipline the row ended up with. The first is a
run-level invariant and catches the class; the second catches one instance per
written test.

## 4. The sixth layer, measured: it is not one defect, and it is not in `dep_rec`

Probe: a worktree at `5f65268`; `family_infinitary`'s declaration (five
constructors, general fibres, `ni = 1`, `np = 1`) built as in the existing
test; then `GenRecursor::build` and
`IndexedDepRecursor::over_family(env, mach, ind, fam, gr, rc)`, with a
`?`-census over the four recursor-path files. One 42-second build. Result:

* `GenRecursor::build` → **Some**. The non-indexed engine (rect, steps,
  recarg_eta_general) is already general.
* `over_family` → **None**, first stop **`dep_guard.rs:366`**, in
  `Lands::lands`: `syl(at.k_h, &conj_proj(&self.h_atoms, j))` fails at
  `i = 1` (the first general constructor), `j = 0` — the *first* atom, a plain
  field. `h_atoms` is `typed_atoms`' plain spelling (`tⱼ ∈ W`, `vⱼ ∈ T`);
  `k_h`'s conclusion carries the skeleton's *general* antecedent (the printed
  operand shows the quantified `∀∀(… ∈ …)` pointwise form), so the two
  conjunctions differ wholesale and even the plain-field projection cannot
  compose. Fail-closed — this is exactly the `#78` decline the fixture records.

§37 sends the successor to census `dep_rec.rs`'s `?`-chain; the measured first
stop is one file earlier, in `dep_guard` — the record is wrong in the same way
the `ih_eqs` comment was in round 3.

Behind that first stop, enumerated by complete grep and by reading the
statements (not run past the first stop): `minor_typed` (no-doms) at
`dep_guard.rs:291` where `premise::minor_typed_at` already exists and documents
this exact use; `guard_atoms_of` → `minor_atoms_at`, whose `Slot::Rec` atom is
unconditionally `tⱼ ∈ ind(p⃗, d⃗ᵢⱼ)` and whose ih atom is the point form
`vⱼ ∈ app(m, d⃗ᵢⱼ, tⱼ)`; `ctor_atoms` (plain) at `dep_rec.rs:564` and `:799`;
`dep_rec`'s ih terms `vs[j] = app(irec, tⱼ)` and `applied_minor` at raw
`ts`/`vs`, where a general slot's minor takes the branch *function* and a
function-valued ih (the shape `dep.rs`'s general arm already builds one index
short); `induction_step`'s hand-built `ratoms` (point `φ(tⱼ)`) against
`rect_parts`' general steps; and `invert_under` /
`IndexedCtor::inv`'s conclusion gaining a bounded universal (§37's one named
prior — real, but several stops deep, not first). Plus `prop_rec.rs:807` and
`trunc.rs:297` for the sibling eliminators, and `class_p_ix.rs:358`'s frame.

So the answer to "is there a sixth layer" is: **there are at least six more
instances behind the sixth stop, all in one family** — the indexed
recursor layer predates `RecArg::general` reaching `family/` and is
plain-spelled throughout. Lifted one decline at a time it will be rounds six
through roughly ten. The alternative: align the whole family against
`premise::minor_typed_at` / `ctor_atoms_at` / `dep.rs`'s general arms in one
pass, driven by extending `family_infinitary` with an `over_family` test —
the probe shows that costs one build cycle per stop and never touches the mini
boundary until the derived side is closed.

## Recommendations, ranked by what they would have caught

1. **Delete the degenerate wrappers; single-source each spelling.**
   `ctor_atoms` → `ctor_atoms_at(…, rec_sets(…))` everywhere (4 sites),
   `minor_typed` → `minor_typed_at` (1 site + `typed_atoms`), point-ih terms →
   the general builders. Would have caught layers 3, both halves of 4, and the
   entire sixth family — ≥ 7 defect sites — at compile time, before any
   witness existed.
2. **Make the frame part of the datum at the zoneb boundary.** Depth-tagged
   expression bundles out of `rec_field`/`ind_spine`/`local_type` reads,
   consumed by opening exactly the recorded binders. Would have caught layers
   1 and 5 and the live `class_p_ix.rs:358`; the same discipline on
   `define_abbrev`'s abstraction list is layer 2.
3. **An arm-coverage census as a CI step.** Per named decline and per
   general/degenerate arm: how many corpus + fixture declarations reach it (the
   §2 census is ~30 lines of Python; a zero row prints as "untested arm").
   Catches nothing by itself — but it would have re-priced every round: "corpus
   green" on this row meant "0 of 102 declarations can see this code", and
   knowing that on day one is the difference between five reactive rounds and
   one deliberate fixture-plus-probe round.
4. **Confluence checks at every interpretation-path mint, plus a
   no-orphan-mints assertion** (§3). Catches the silent-wrong-term class as
   declines: layer 1's shallow mint, layer 4's raw-slot mint, eab73e1's
   survivor — the three incidents with no guard waiting.
5. **Probe the last construction of a row before lifting its first decline.**
   `over_family` was measurable from the derived side the day
   `family_infinitary` landed (round 3); it was measured today in 42 seconds
   and named the sixth layer's real first stop, one file away from where the
   handoff pointed. The five-for-five record of wrong predictions is a record
   of predicting where a census was available.
