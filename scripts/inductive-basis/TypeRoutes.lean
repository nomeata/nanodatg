/-
TypeRoutes.lean — the never-zero classes: tag-sums, Subtype, and a List
model with a full large recursor, over {Nat, PSigma} plus, for one pad,
the Prop-lift PULiftP. No funext, no Quot, no Acc, no core inductive other
than the basis members themselves (Nat, PSigma, Eq) is consumed.

What is compiled here, and what each piece establishes:

  1. `D1`/`DS` — definitionally-canonical pads: every element of
     `Σ'(_ : CTrue), CTrue` is definitionally its canonical element
     (structure eta + proof irrelevance), and the property survives
     `(α : Sort u) → D1` (function eta). These are modelgen §8's pads,
     re-verified here because List's nil case leans on them.

  2. `Subtype` is a PSigma instance, at Lean's own level `Sort (max 1 u)`.

  3. `PSum.{u,v} : Sort (max 1 u v)` — the two-constructor never-zero
     class — as a Nat-tagged sum of PSigma chains with an empty fiber
     beyond the tags: carrier at Lean's exact level, both constructors,
     the dependent recursor into Sort w by Nat.rec on the tag, and both
     ι rules. The inl/inr ι's are `rfl`: the recursor's transport sits on
     a self-equality that K-like reduction on Eq.rec erases.

  4. `List α : Type u` — the recursive finitely-branching class — as
     `Σ'(n : Nat), V n` where `V : Nat → Type u` is the Nat.rec tower of
     right-nested pair chains (`V 0 = D`, `V (n+1) = α ×' V n`). Both
     constructors, the dependent recursor into Sort w (Lean's own List.rec
     shape), and both ι rules hold BY RFL: the entire model is
     definitional, because structure eta collapses every V-element onto a
     constructor image. This is sharper than the Σ(n, Fin n → α)
     representation (which needs funext), and it is the compiled witness
     that {Nat, PSigma} reaches finite sequences — the input to the
     path-encoding of W.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean TypeRoutes.lean
Expected: 0 errors.
-/
universe u v w

def CTrue' : Prop := ∀ p : Prop, p → p
def CTrue'.triv : CTrue' := fun _ h => h
def CFalse' : Prop := ∀ p : Prop, p

-- ── 1. Definitionally-canonical pads ───────────────────────────────────────

/-- The canonical pad at `Type 0`. -/
def D1 : Type := PSigma (fun _ : CTrue' => CTrue')
def D1.pt : D1 := ⟨CTrue'.triv, CTrue'.triv⟩

/-- Structure eta + proof irrelevance: every element IS the point. -/
example (x : D1) : x = D1.pt := rfl

/-- The canonical pad at `Type u` (for the successor of any level). -/
def DS : Type u := (α : Sort u) → D1
def DS.pt : DS.{u} := fun _ => D1.pt

/-- ... still definitionally a singleton (function eta closes it). -/
example (x : DS.{u}) : x = DS.pt := rfl

-- ── 2. Subtype is a PSigma instance, at Lean's own level ───────────────────

def Subtype' {α : Sort u} (p : α → Prop) : Sort (max 1 u) := PSigma p
example {α : Sort u} (p : α → Prop) : Subtype' p = PSigma p := rfl
-- Lean's own Subtype has this exact level:
example {α : Sort u} (p : α → Prop) : Sort (max 1 u) := Subtype p

-- ── 3. PSum at Sort (max 1 u v): the tag-sum construction ──────────────────

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PULiftP' (p : Prop) : Sort u
  | up : p → PULiftP' p

noncomputable def PULiftP'.down {p : Prop} (t : PULiftP'.{u} p) : p :=
  PULiftP'.rec (motive := fun _ => p) (fun h => h) t

theorem PULiftP'.eta {p : Prop} (t : PULiftP'.{u} p) : t = .up (down t) :=
  PULiftP'.rec (motive := fun t => t = .up (down t)) (fun _ => rfl) t

/-- Large elimination out of Church-False: it yields `0 = 1`, and Nat.rec
    builds a Sort-w family to transport along (BareU.lean's PE.elim). -/
noncomputable def CFalse'.elim {C : Sort w} (h : CFalse') : C :=
  @Eq.rec Nat 0
    (fun n _ => Nat.rec (motive := fun _ => Sort w) (PULiftP'.{w} CTrue') (fun _ _ => C) n)
    (.up CTrue'.triv) 1 (h (0 = 1))

noncomputable def Lift₁ (α : Sort u) : Sort (max 1 u v) :=
  PSigma (fun _ : α => PULiftP'.{max 1 u v} CTrue')
noncomputable def Lift₂ (β : Sort v) : Sort (max 1 u v) :=
  PSigma (fun _ : β => PULiftP'.{max 1 u v} CTrue')
noncomputable def EmptyAt : Sort (max 1 u v) :=
  PSigma (fun _ : CFalse' => PULiftP'.{max 1 u v} CTrue')

/-- The tag fiber: 0 ↦ lifted α, 1 ↦ lifted β, else empty. -/
noncomputable def SumFiber (α : Sort u) (β : Sort v) : Nat → Sort (max 1 u v) :=
  fun n =>
    Nat.rec (motive := fun _ => Sort (max 1 u v))
      (Lift₁.{u,v} α)
      (fun n' _ =>
        Nat.rec (motive := fun _ => Sort (max 1 u v))
          (Lift₂.{u,v} β)
          (fun _ _ => EmptyAt.{u,v}) n')
      n

/-- The carrier, at Lean's exact `PSum` level. -/
noncomputable def PSum' (α : Sort u) (β : Sort v) : Sort (max 1 u v) :=
  PSigma (SumFiber.{u,v} α β)

noncomputable def PSum'.inl {α : Sort u} {β : Sort v} (a : α) : PSum'.{u,v} α β :=
  ⟨0, a, .up CTrue'.triv⟩
noncomputable def PSum'.inr {α : Sort u} {β : Sort v} (b : β) : PSum'.{u,v} α β :=
  ⟨1, b, .up CTrue'.triv⟩

/-- The dependent recursor into Sort w: Nat.rec on the tag; the payload's
    pad is rebuilt by `PULiftP'.eta`-transport. -/
noncomputable def PSum'.elim {α : Sort u} {β : Sort v}
    {motive : PSum'.{u,v} α β → Sort w}
    (ml : ∀ a, motive (.inl a)) (mr : ∀ b, motive (.inr b))
    (t : PSum' α β) : motive t :=
  PSigma.rec (motive := fun t => motive t)
    (fun n =>
      Nat.rec (motive := fun n => (x : SumFiber.{u,v} α β n) → motive ⟨n, x⟩)
        (fun x =>
          PSigma.rec (motive := fun x => motive ⟨0, x⟩)
            (fun a pad =>
              @Eq.rec _ (PULiftP'.up (PULiftP'.down pad))
                (fun z _ => motive ⟨0, a, z⟩)
                (ml a) pad (PULiftP'.eta pad).symm)
            x)
        (fun n' _ =>
          Nat.rec (motive := fun n' => (x : SumFiber.{u,v} α β (n'+1)) → motive ⟨n'+1, x⟩)
            (fun x =>
              PSigma.rec (motive := fun x => motive ⟨1, x⟩)
                (fun b pad =>
                  @Eq.rec _ (PULiftP'.up (PULiftP'.down pad))
                    (fun z _ => motive ⟨1, b, z⟩)
                    (mr b) pad (PULiftP'.eta pad).symm)
                x)
            (fun _ _ x => CFalse'.elim x.fst)
            n')
        n)
    t

/-- Both ι rules are `rfl`: on a constructor the transport is along a
    self-equality, erased by K-like reduction on `Eq.rec`. -/
theorem PSum'.iota_inl {α : Sort u} {β : Sort v}
    {motive : PSum'.{u,v} α β → Sort w}
    (ml : ∀ a, motive (.inl a)) (mr : ∀ b, motive (.inr b)) (a : α) :
    PSum'.elim ml mr (.inl a) = ml a := rfl
theorem PSum'.iota_inr {α : Sort u} {β : Sort v}
    {motive : PSum'.{u,v} α β → Sort w}
    (ml : ∀ a, motive (.inl a)) (mr : ∀ b, motive (.inr b)) (b : β) :
    PSum'.elim ml mr (.inr b) = mr b := rfl

-- the model recursor has PSum.rec's exact shape:
noncomputable example : ∀ {α : Sort u} {β : Sort v}
    {motive : PSum'.{u,v} α β → Sort w},
    (∀ a, motive (.inl a)) → (∀ b, motive (.inr b)) →
    ∀ t, motive t := @PSum'.elim

-- ── 4. List with a fully definitional model ────────────────────────────────

/-- The vector tower: `V n` is the type of right-nested n-tuples of α. -/
noncomputable def V (α : Type u) : Nat → Type u :=
  fun n =>
    Nat.rec (motive := fun _ => Type u)
      DS.{u}
      (fun _ Vn => PSigma (fun _ : α => Vn))
      n

/-- The carrier, at Lean's exact `List` level `Type u → Type u`. -/
noncomputable def List' (α : Type u) : Type u := PSigma (V α)

noncomputable def List'.nil {α : Type u} : List' α := ⟨0, DS.pt⟩
noncomputable def List'.cons {α : Type u} (a : α) (l : List' α) : List' α :=
  ⟨l.1 + 1, a, l.2⟩

/-- The dependent recursor, Lean's own `List.rec` shape, by Nat.rec on the
    length. No transport anywhere: at 0 the tuple IS `DS.pt` definitionally
    (pads are canonical), and at n+1 structure eta splits the tuple into a
    definitional constructor image. -/
noncomputable def List'.elim {α : Type u} {motive : List' α → Sort w}
    (h0 : motive .nil) (h1 : ∀ a l, motive l → motive (.cons a l))
    (l : List' α) : motive l :=
  PSigma.rec (motive := fun l => motive l)
    (fun n =>
      Nat.rec (motive := fun n => (x : V α n) → motive ⟨n, x⟩)
        (fun _ => h0)
        (fun n ih x =>
          PSigma.rec (motive := fun x => motive ⟨n+1, x⟩)
            (fun a t => h1 a ⟨n, t⟩ (ih t))
            x)
        n)
    l

/-- Both ι rules hold by `rfl` — the model is fully definitional. -/
theorem List'.iota_nil {α : Type u} {motive : List' α → Sort w}
    (h0 : motive .nil) (h1 : ∀ a l, motive l → motive (.cons a l)) :
    List'.elim h0 h1 .nil = h0 := rfl
theorem List'.iota_cons {α : Type u} {motive : List' α → Sort w}
    (h0 : motive .nil) (h1 : ∀ a l, motive l → motive (.cons a l))
    (a : α) (l : List' α) :
    List'.elim h0 h1 (.cons a l) = h1 a l (List'.elim h0 h1 l) := rfl

-- the model recursor has List.rec's exact shape:
noncomputable example : ∀ {α : Type u} {motive : List' α → Sort w},
    motive .nil → (∀ a l, motive l → motive (.cons a l)) →
    ∀ l, motive l := @List'.elim

-- ── Axiom audit: the constructions are axiom-free (in particular: no
--    funext, despite List's recursor) ────────────────────────────────────────
/-- info: 'PSum'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms PSum'.elim
/-- info: 'List'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms List'.elim
