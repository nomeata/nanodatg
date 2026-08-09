/-!
Compiled refutations: the naive (Church/impredicative) encodings of `Option`,
`Sigma`, `Subtype` and `List` from Π alone admit **no dependent eliminator at
all** — not even with `Prop` motives, and with **no ι rules demanded**.  The
refutation is a theorem of Lean + classical axioms: assuming the eliminator's
bare existence yields `False`.  Since Lean + `propext` + `Quot.sound` +
`Classical.choice` is the consistency baseline this whole project assumes, no
subsystem of it can derive the eliminator.

Also here, positives: the non-dependent recursors *do* exist with `rfl` ι at
the encoding's own universe, and a `Prop`-Church `Acc` supports formation,
`intro`, `inv` and dependent induction with `Prop` motives.

This file must compile with **no errors** at leanprover/lean4:v4.29.1.
-/

universe u v

attribute [local instance] Classical.propDecidable

/-- "X has three pairwise-distinct elements" — the classical discriminator the
junk terms branch on.  Holds for `Nat`, fails for `Bool`. -/
def Three (X : Type) : Prop := ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z

theorem threeNat : Three Nat := ⟨0, 1, 2, by decide, by decide, by decide⟩

theorem notThreeBool : ¬ Three Bool := by
  intro h
  have ⟨x, y, z, hxy, hxz, hyz⟩ := h
  cases x <;> cases y <;> cases z <;>
    first | exact hxy rfl | exact hxz rfl | exact hyz rfl

/-! ## Option -/

def COption (A : Type) : Type 1 := ∀ X : Type, X → (A → X) → X

def cnone {A : Type} : COption A := fun _ n _ => n
def csome {A : Type} (a : A) : COption A := fun _ _ s => s a

/-- The non-dependent recursor exists, with definitional ι — but only into the
encoding's own universe. -/
def crecO {A X} (n : X) (s : A → X) (o : COption A) : X := o X n s
example {A X} (n : X) (s : A → X) : crecO n s cnone = n := rfl
example {A X} (n : X) (s : A → X) (a : A) : crecO n s (csome a) = s a := rfl

/-- A classical junk inhabitant: behaves like `csome a` on types with three
distinct elements and like `cnone` on the rest.  Provably equal to neither. -/
noncomputable def junkO {A : Type} (a : A) : COption A :=
  fun X n s => if Three X then s a else n

/-- **Refutation.**  The mere existence of a dependent eliminator for
`COption` — at `Prop` motives, with no computation rules asked for — is
contradictory.  A model recursor must exist at every motive universe
including `Prop`, so this kills the candidate outright. -/
theorem no_dep_elim_option (A : Type) (a : A) :
    (∀ P : COption A → Prop, P cnone → (∀ b, P (csome b)) → ∀ o, P o) → False := by
  intro ind
  have can := ind (fun o => o = cnone ∨ ∃ b, o = csome b)
      (Or.inl rfl) (fun b => Or.inr ⟨b, rfl⟩) (junkO a)
  cases can with
  | inl h =>
      have e := congrFun (congrFun (congrFun h Nat) 0) (fun _ => 1)
      rw [show junkO a Nat 0 (fun _ => 1) = 1 from dif_pos threeNat] at e
      exact Nat.succ_ne_zero 0 e
  | inr h =>
      have ⟨b, hb⟩ := h
      have e := congrFun (congrFun (congrFun hb Bool) true) (fun _ => false)
      rw [show junkO a Bool true (fun _ => false) = true from dif_neg notThreeBool] at e
      exact Bool.noConfusion e

/-! ## List — the recursive one; the junk argument is unchanged -/

def CList (A : Type) : Type 1 := ∀ X : Type, X → (A → X → X) → X

def cnil {A : Type} : CList A := fun _ n _ => n
def ccons {A : Type} (a : A) (l : CList A) : CList A := fun X n c => c a (l X n c)

def crecL {A X} (n : X) (c : A → X → X) (l : CList A) : X := l X n c
example {A X} (n : X) (c : A → X → X) : crecL n c cnil = n := rfl
example {A X} (n : X) (c : A → X → X) (a : A) (l : CList A) :
    crecL n c (ccons a l) = c a (crecL n c l) := rfl

noncomputable def junkL {A : Type} (a : A) : CList A :=
  fun X n c => if Three X then c a n else n

theorem no_dep_elim_list (A : Type) (a : A) :
    (∀ P : CList A → Prop, P cnil → (∀ b l, P l → P (ccons b l)) → ∀ l, P l) → False := by
  intro ind
  have can := ind (fun l => l = cnil ∨ ∃ b t, l = ccons b t)
      (Or.inl rfl) (fun b t _ => Or.inr ⟨b, t, rfl⟩) (junkL a)
  cases can with
  | inl h =>
      have e := congrFun (congrFun (congrFun h Nat) 0) (fun _ _ => 1)
      rw [show junkL a Nat 0 (fun _ _ => 1) = 1 from dif_pos threeNat] at e
      exact Nat.succ_ne_zero 0 e
  | inr h =>
      have ⟨b, t, hb⟩ := h
      have e := congrFun (congrFun (congrFun hb Bool) true) (fun _ _ => false)
      rw [show junkL a Bool true (fun _ _ => false) = true from dif_neg notThreeBool] at e
      exact Bool.noConfusion e

/-! ## Sigma (refuted at `A := Bool`, `B := fun _ => Unit`) -/

def CSigma (A : Type) (B : A → Type) : Type 1 := ∀ X : Type, (∀ a, B a → X) → X

def cmkS {A : Type} {B : A → Type} (a : A) (b : B a) : CSigma A B := fun _ k => k a b

def crecS {A B X} (k : ∀ a, B a → X) (s : CSigma A B) : X := s X k
example {A : Type} {B : A → Type} {X} (k : ∀ a, B a → X) (a : A) (b : B a) :
    crecS k (cmkS a b) = k a b := rfl

noncomputable def junkS : CSigma Bool (fun _ => Unit) :=
  fun X k => if Three X then k true () else k false ()

theorem no_dep_elim_sigma :
    (∀ P : CSigma Bool (fun _ => Unit) → Prop,
        (∀ a b, P (cmkS a b)) → ∀ s, P s) → False := by
  intro ind
  have can := ind (fun s => ∃ a b, s = cmkS a b) (fun a b => ⟨a, b, rfl⟩) junkS
  have ⟨a, b, h⟩ := can
  cases a with
  | true =>
      have e := congrFun (congrFun h Bool) (fun a _ => a)
      rw [show junkS Bool (fun a _ => a) = false from dif_neg notThreeBool] at e
      exact Bool.noConfusion e
  | false =>
      have e := congrFun (congrFun h Nat) (fun a _ => cond a 1 0)
      rw [show junkS Nat (fun a _ => cond a 1 0) = 1 from dif_pos threeNat] at e
      exact Nat.succ_ne_zero 0 e

/-! ## Subtype (refuted at `A := Nat`, `p := fun _ => True`) -/

def CSub (A : Type) (p : A → Prop) : Type 1 := ∀ X : Type, (∀ x, p x → X) → X

def cmkT {A : Type} {p : A → Prop} (x : A) (hx : p x) : CSub A p := fun _ k => k x hx

def crecT {A p X} (k : ∀ x, p x → X) (s : CSub A p) : X := s X k
example {A : Type} {p : A → Prop} {X} (k : ∀ x, p x → X) (x : A) (hx : p x) :
    crecT k (cmkT x hx) = k x hx := rfl

noncomputable def junkT : CSub Nat (fun _ => True) :=
  fun X k => if Three X then k 1 trivial else k 0 trivial

theorem no_dep_elim_subtype :
    (∀ P : CSub Nat (fun _ => True) → Prop,
        (∀ x hx, P (cmkT x hx)) → ∀ s, P s) → False := by
  intro ind
  have can := ind (fun s => ∃ x hx, s = cmkT x hx) (fun x hx => ⟨x, hx, rfl⟩) junkT
  have ⟨x, hx, h⟩ := can
  cases x with
  | zero =>
      have e := congrFun (congrFun h Nat) (fun y _ => y)
      rw [show junkT Nat (fun y _ => y) = 1 from dif_pos threeNat] at e
      exact Nat.succ_ne_zero 0 e
  | succ n =>
      have e := congrFun (congrFun h Bool) (fun y _ => y == 0)
      rw [show junkT Bool (fun y _ => y == 0) = true from dif_neg notThreeBool] at e
      exact Bool.noConfusion e

/-! ## Acc: the `Prop`-Church encoding — the genuine partial positive.
Formation and `intro` at exactly `Acc`'s declared types, `inv`, and dependent
induction with `Prop` motives (`Acc.rec` at motive universe 0), the last with
its ι rule free by proof irrelevance.  What is missing is elimination into
`Sort v` for `v > 0` — see `AccLarge.lean` for the failing attempt. -/

def CAcc {α : Sort u} (r : α → α → Prop) (x : α) : Prop :=
  ∀ S : α → Prop, (∀ y, (∀ z, r z y → S z) → S y) → S x

def CAcc.intro {α : Sort u} {r : α → α → Prop} (x : α)
    (h : ∀ y, r y x → CAcc r y) : CAcc r x :=
  fun S ih => ih x (fun z hz => h z hz S ih)

/-- Non-dependent well-founded induction, `Prop` motives: immediate. -/
theorem CAcc.ind {α : Sort u} {r : α → α → Prop} {motive : α → Prop}
    (h : ∀ x, (∀ y, r y x → motive y) → motive x) (x : α) (hx : CAcc r x) :
    motive x :=
  hx motive h

theorem CAcc.inv {α : Sort u} {r : α → α → Prop} {x : α}
    (hx : CAcc r x) : ∀ y, r y x → CAcc r y :=
  CAcc.ind (motive := fun x => ∀ y, r y x → CAcc r y)
    (fun _ ih y hy => CAcc.intro y (ih y hy)) x hx

/-- `Acc.rec` at motive universe 0, stated over `CAcc`, minor premise in
`Acc.rec`'s own shape.  Proof irrelevance discharges the dependency on the
proof, so this is the full dependent `Prop` eliminator. -/
theorem CAcc.recProp {α : Sort u} {r : α → α → Prop}
    {motive : ∀ x, CAcc r x → Prop}
    (step : ∀ x (h : ∀ y, r y x → CAcc r y),
      (∀ y (hr : r y x), motive y (h y hr)) → motive x (CAcc.intro x h))
    (x : α) (hx : CAcc r x) : motive x hx :=
  CAcc.ind (motive := fun x => ∀ hx : CAcc r x, motive x hx)
    (fun x ih hx => step x (CAcc.inv hx) (fun y hr => ih y hr (CAcc.inv hx y hr)))
    x hx hx

/-! ## Why no impredicative encoding of a *type* can work in Lean:
the only impredicative universe is `Prop`, and `Prop` is definitionally
proof-irrelevant — every `Prop`-encoded "datatype" is a subsingleton. -/
example (P : Prop) (a b : P) : a = b := rfl
