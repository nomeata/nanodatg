/-
IndexedCarve.lean — the indexed never-zero class (thesis §5.2): skeleton
plus `good`, with the recursor and ι compiled, on the thesis's own example.

The thesis translates an indexed family living at a never-zero universe by
erasing indices to a skeleton type S, carving with a recursively defined
predicate `good : S → indices → Prop`, and taking `T x := {s : S // good s x}`
(thesis.txt:1758-1810). Like §5.3, the recursor construction is §5.4's
"future work". This file compiles it for the thesis's own running example
(thesis.txt:1764):

    X = μ t : N → U1. (one : t 1) + (double : ∀ n : N, t n → t (2n))

Skeleton: a list of the `double` nodes' payloads (the erased tree is a
chain, each node carrying its n; List stands in for its basis model —
TypeRoutes.lean compiles List over {Nat, PSigma} with definitional ι).
`good` is by skeleton recursion exactly as at thesis.txt:1768:

    good one         m := m = 1
    good (double n x) m := m = 2n ∧ good x n

What the compile establishes:
  * carrier at the declared level (Type 0 here; the mechanism is
    level-uniform since PSigma-of-a-Prop-predicate keeps the skeleton's
    never-zero level exactly: Sort (max 1 ℓ 0) = Sort ℓ);
  * both constructors, packing their index equations (`rfl` at the
    constructor, so no equation data is stored — the "Henry Ford"
    x = e clauses of the ctor-translation land as `Eq.refl`);
  * the DEPENDENT LARGE recursor at X.rec's exact shape, by skeleton
    recursion with Eq.rec transport along the stored index equations, the
    Good-proof positions closed by definitional proof irrelevance;
  * both ι rules BY RFL: at a constructor the stored equation is `rfl`,
    and the kernel's K-like reduction on Eq.rec erases the transport.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean IndexedCarve.lean
Expected: 0 errors.
-/
universe w

/-- The target, as Lean's kernel takes it (never-zero sort, indexed,
    recursive): large elimination by reason 1. -/
inductive X : Nat → Type
  | one : X 1
  | double : ∀ n, X n → X (2 * n)

noncomputable example : ∀ {motive : ∀ i, X i → Sort w},
    motive 1 .one → (∀ n x, motive n x → motive (2 * n) (.double n x)) →
    ∀ {i} (x : X i), motive i x := @X.rec

-- ── The model ──────────────────────────────────────────────────────────────

/-- `good`, by skeleton recursion (thesis.txt:1768). -/
def Good : List Nat → Nat → Prop :=
  fun s =>
    List.rec (motive := fun _ => Nat → Prop)
      (fun m => m = 1)
      (fun n _ g m => m = 2 * n ∧ g n)
      s

/-- The carrier: the carve `{s : List Nat // Good s i}`, as a PSigma —
    at the declaration's exact level. -/
def X' (i : Nat) : Type := PSigma (fun s : List Nat => Good s i)

def X'.one : X' 1 := ⟨[], rfl⟩
def X'.double (n : Nat) (x : X' n) : X' (2 * n) := ⟨n :: x.1, rfl, x.2⟩

/-- The dependent large recursor, X.rec's exact shape: skeleton recursion,
    index transport along the stored equations, Good-positions by proof
    irrelevance. -/
noncomputable def X'.elim {motive : ∀ i, X' i → Sort w}
    (m1 : motive 1 .one)
    (md : ∀ n x, motive n x → motive (2 * n) (.double n x))
    {i : Nat} (x : X' i) : motive i x :=
  PSigma.rec (motive := fun x => motive i x)
    (fun s =>
      List.rec (motive := fun s => ∀ i (g : Good s i), motive i ⟨s, g⟩)
        (fun i g =>
          @Eq.rec Nat 1 (fun j _ => (g' : Good [] j) → motive j ⟨[], g'⟩)
            (fun _ => m1) i (g : i = 1).symm g)
        (fun n s ih i g =>
          @Eq.rec Nat (2 * n)
              (fun j _ => (g' : Good (n :: s) j) → motive j ⟨n :: s, g'⟩)
              (fun g' => md n ⟨s, g'.2⟩ (ih n g'.2))
              i (g.1 : i = 2 * n).symm g)
        s i)
    x

noncomputable example : ∀ {motive : ∀ i, X' i → Sort w},
    motive 1 .one → (∀ n x, motive n x → motive (2 * n) (.double n x)) →
    ∀ {i} (x : X' i), motive i x := @X'.elim

/-- Both ι rules by rfl: the stored equations are `Eq.refl`, so K-like
    reduction erases the transports. -/
theorem X'.iota_one {motive : ∀ i, X' i → Sort w}
    (m1 : motive 1 .one)
    (md : ∀ n x, motive n x → motive (2 * n) (.double n x)) :
    X'.elim m1 md .one = m1 := rfl

theorem X'.iota_double {motive : ∀ i, X' i → Sort w}
    (m1 : motive 1 .one)
    (md : ∀ n x, motive n x → motive (2 * n) (.double n x))
    (n : Nat) (x : X' n) :
    X'.elim m1 md (.double n x) = md n x (X'.elim m1 md x) := rfl

-- ── Axiom audit ────────────────────────────────────────────────────────────
/-- info: 'X'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms X'.elim
