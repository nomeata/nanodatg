/-
# Which declarations are *actually* indexed, and what the indexed branch builds

**This fixture is a measured negative twice over, and both negatives are the
point.**

# 1. Lean decides what is even indexed, and it is not what the source says

`Lean.Elab.Command`'s `fixedIndicesToParams` promotes an index that is the same
variable in every constructor result and every recursive occurrence into a
**parameter**. The promotion is invisible in the source and shows up only as
`numIndices` in the export:

| declaration | source says | Lean exports |
| --- | --- | --- |
| `IxVar` | one index `N` | `numParams=2, numIndices=0` — **promoted** |
| `IxRec` | one index `N` | `numParams=2, numIndices=0` — **promoted** |
| `IxConst` | one index `N` | `numParams=1, numIndices=1` |
| `IxComputed` | one index `N` | `numParams=1, numIndices=1` |

All four look identically indexed in Lean source. Two of them are not indexed at
all by the time the checker sees them. **A hand-written `.ndjson` asserting
`numIndices=1` for `IxVar` would be a shape Lean never emits** — the export
would parse, the test would pass, and it would be measuring a declaration that
cannot arise. That is the argument for `scripts/export-fixture.sh` in one table.

The corpus cannot show this: it contains no declaration whose index is a fixed
constructor field, so nothing in 91 files is on the promoted side of the line.

# 2. The indexed branch builds a carrier and no constructors

`zoneb::build_indexed`'s own header says so — "the constructors are not built
here" — and this measures what that costs at declaration level:

| declaration | `⟦T⟧` | `⟦T.ctor⟧` |
| --- | --- | --- |
| `IxVar`, `IxRec` (promoted, so ordinary class (T)) | derives | **derives** |
| `IxConst`, `IxComputed` (genuinely indexed) | derives | `no-interp(IxConst.mk)` |

The split is exactly the promotion, and **not** recursion: `IxRec` is recursive
at two constructors, one with a recursive field, and both its constructors
interpret. Four declarations rather than two because with one promoted and one
indexed example, "is it recursion?" and "is it indexing?" are the same
hypothesis.

The reason string is pinned as it stands, and it is a poor one:
`no-interp(IxConst.mk)` is `zoneb::stored_or_reason_after`'s fallback. The
declaration translated and `⟦IxConst⟧` is in the store; the constructor is
simply absent, and the label says "absent" rather than "the indexed branch
builds no constructors". If it acquires a better name, update this test to it —
do not delete the row.
-/
prelude

--#export N IxVar IxConst IxComputed IxRec
--#export ixVarTy ixVarMk ixConstTy ixConstMk ixComputedMk ixRecBase ixRecStep

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- The index type. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The result index is a fixed field variable, so Lean **promotes** it. -/
inductive IxVar (α : Type) : N → Type where
  | mk : (n : N) → α → IxVar α n

/-- The result index is a **closed constant**, which cannot be a parameter. -/
inductive IxConst (α : Type) : N → Type where
  | mk : α → IxConst α N.z

/-- The result index is a **computed term**, which cannot be a parameter
    either. -/
inductive IxComputed (α : Type) : N → Type where
  | mk : (n : N) → α → IxComputed α (N.s n)

/-- Recursive at both constructors, with the result index a fixed variable at
    both and the recursive occurrence at that same variable — so it is promoted
    too, and recursion is held fixed against `IxVar`. -/
inductive IxRec (α : Type) : N → Type where
  | base : (n : N) → α → IxRec α n
  | step : (n : N) → IxRec α n → IxRec α n

def ixVarTy (α : Type) (n : N) : Type := IxVar α n
def ixVarMk (α : Type) (n : N) (a : α) : IxVar α n := IxVar.mk n a
def ixConstTy (α : Type) (n : N) : Type := IxConst α n
def ixConstMk (α : Type) (a : α) : IxConst α N.z := IxConst.mk a
def ixComputedMk (α : Type) (n : N) (a : α) : IxComputed α (N.s n) := IxComputed.mk n a
def ixRecBase (α : Type) (n : N) (a : α) : IxRec α n := IxRec.base n a
def ixRecStep (α : Type) (n : N) (v : IxRec α n) : IxRec α n := IxRec.step n v
