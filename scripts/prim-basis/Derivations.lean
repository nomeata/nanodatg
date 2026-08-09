/-
# Layer 3 evidence: models from the five primitives, compiled

Every construction the `--prim-models` layer (`modelgen/Modelgen/
Simple.lean`) emits is prototyped here in a `prelude` file — no Init, term
mode only, which is what an `Expr` generator can build. The five primitives
are declared at Lean's own shapes, exactly as the splice inserts them.

Compiled at `leanprover/lean4:v4.29.1` with zero errors. Each `example …
:= rfl' _` line is a definitional-ι check.

Three verified sharpenings of the commission:

* the `Sigma` primitive must be **`PSigma`-shaped** (`{α : Sort u} →
  (α → Sort v) → Sort (max 1 u v)`): `Subtype`, structures with `Prop`
  fields, and every `Prop`-fibred pair below need a Σ over `Sort`, which a
  `Type`-only `Sigma` cannot give without `PLift` — a sixth inductive;
* level pads can be **definitionally canonical**: every element of
  `D 1 := Σ'(_ : ⊤), ⊤` (with `⊤ := ∀ C : Prop, C → C`) is *defeq* to its
  canonical element by structure eta plus proof irrelevance, and the
  same holds through `D (a+1) := (α : Sort a) → D 1` and
  `D (max a b) := Σ'(_ : D a), D b` — so the non-recursive Type route
  consumes **no `funext`, no `Quot`, and not even `Eq.rec`**: the ι
  equations below hold by `rfl` with no transport anywhere;
* the Prop route needs no primitive at all beyond `Eq` for the ι
  statements: the carrier is the impredicative Church encoding, dependent
  elimination at a `Prop` motive is definitional proof irrelevance, and
  large elimination — granted by the subsingleton rule, so every field is
  a proposition — is extraction, `t Tᵢ (fun f⃗ => fᵢ)`.

Elaborator artefacts of `prelude` mode, none of which touches the generator
(it emits explicit `Expr`s and never elaborates): constructor applications
with implicit arguments trip a missing-`CoeFun` path, so constructors are
used through wrapper `def`s (`rfl'`, `pair`, `prec`); the unifier's
Nat-offset fast path looks up `Nat.add`/`HAdd.hAdd`/`OfNat.ofNat` by name
and crashes without them, so stubs are declared (the generator never
mentions them); and everything is `noncomputable` because the compiler
backend is absent.
-/
prelude
set_option autoImplicit false
set_option genCtorIdx false

universe u v w

/- ── the five primitives, at Lean's shapes ─────────────────────────── -/

inductive Eq {α : Sort u} (a : α) : α → Prop
  | refl : Eq a a

inductive False : Prop

inductive PSigma {α : Sort u} (β : α → Sort v) : Sort (max 1 u v)
  | mk (fst : α) (snd : β fst)

inductive Nat : Type
  | zero : Nat
  | succ (n : Nat) : Nat

inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop
  | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

/- Elaborator scaffolding, not part of the basis: the unifier's Nat-offset
fast path looks these constants up by name and crashes in a `prelude` file
without them. The generator never emits or mentions them. -/
noncomputable def Nat.add (a b : Nat) : Nat :=
  Nat.rec a (fun _ ih => Nat.succ ih) b
class Add (α : Type u) where
  add : α → α → α
class HAdd (α : Type u) (β : Type v) (γ : Type w) where
  hAdd : α → β → γ
noncomputable instance instAddNat : Add Nat := ⟨Nat.add⟩
noncomputable instance instHAdd {α : Type u} [Add α] : HAdd α α α :=
  ⟨fun a b => Add.add a b⟩
class OfNat (α : Type u) (n : Nat) where
  ofNat : α
instance instOfNatNat (n : Nat) : OfNat Nat n :=
  ⟨n⟩

/- ── wrappers (prelude-mode elaborator convenience only) ───────────── -/

noncomputable def rfl' {α : Sort u} (a : α) : Eq a a := @Eq.refl α a

noncomputable def pair {α : Sort u} {β : α → Sort v} (fst : α) (snd : β fst) :
    PSigma β := @PSigma.mk α β fst snd

noncomputable def prec {α : Sort u} {β : α → Sort v} {motive : PSigma β → Sort w}
    (m : (fst : α) → (snd : β fst) → motive (pair fst snd)) (t : PSigma β) :
    motive t := @PSigma.rec α β motive m t

/- ── the shared kit, as the generator emits it (inline) ────────────── -/

/-- `⊤ := ∀ C : Prop, C → C` — pure Π, no primitive consumed. -/
abbrev TrueP : Prop := (C : Prop) → C → C
noncomputable def TrueP.I : TrueP := fun _ c => c

/-- `D 1`: every element is **defeq** to `canon1` — structure eta turns it
into a `mk` of two proofs and proof irrelevance closes the components. -/
abbrev D1 : Type := PSigma (fun _ : TrueP => TrueP)
noncomputable def canon1 : D1 := pair TrueP.I TrueP.I

/-- The defeq-singleton property of `D 1`, witnessed definitionally: no
`funext`, no `Eq.rec`. -/
example (s : D1) : Eq s canon1 := rfl' s

/-- `D (a+1) := (α : Sort a) → D 1`, at exactly `Sort (a+1)` because the
body is never `Prop`; still a defeq singleton (η for functions, then the
`D 1` argument). -/
abbrev DS : Sort (u + 1) := (α : Sort u) → D1
noncomputable def DS.canon : DS.{u} := fun _ => canon1

example (s : DS.{u}) : Eq s DS.canon.{u} := rfl' s

/-- `D (max a b) := Σ'(_ : D a), D b` — here at `max (u+1) 1 = u+1` for the
`max`-composition shape; defeq singleton again (structure eta, then the
components). -/
abbrev DM : Sort (max (u + 1) 1) := PSigma (fun _ : DS.{u} => D1)
noncomputable def DM.canon : DM.{u} := pair DS.canon canon1

example (s : DM.{u}) : Eq s DM.canon.{u} := rfl' s

/-- An empty type at exactly `Sort w` for never-zero `w`:
`Σ'(h : False), False.rec h` is at `Sort (max 1 0 w) = Sort w`. -/
abbrev EmptyAt : Sort (max 1 w) :=
  PSigma (fun h : False => False.rec (motive := fun _ => Sort w) h)

noncomputable def EmptyAt.elim {motive : Sort v} (e : EmptyAt.{w}) : motive :=
  False.rec (motive := fun _ => motive)
    (prec (motive := fun _ => False) (fun h _ => h) e)

/- ── Type route, worked: Bool ──────────────────────────────────────── -/

namespace BoolM

/-- The fibre family: tag 0 ↦ `D 1`, tag 1 ↦ `D 1`, else empty — a
`Nat.rec` cases tower, exactly as the generator writes it. -/
abbrev F (n : Nat) : Type :=
  Nat.rec (motive := fun _ => Type)
    D1
    (fun n₁ _ => Nat.rec (motive := fun _ => Type)
      D1
      (fun _ _ => EmptyAt.{1})
      n₁)
    n

abbrev self : Type := PSigma F

noncomputable def ctor_0 : self := pair (β := F) Nat.zero canon1
noncomputable def ctor_1 : self := pair (β := F) (Nat.succ Nat.zero) canon1

/-- `Bool.rec`'s shape at the model's names. The pad binders `f` are used
*nowhere*: the minors' types close by defeq (`f ≡ canon1`), which is the
whole point of the `D`-pads. -/
noncomputable def rec_0 {motive : self → Sort u}
    (h0 : motive ctor_0) (h1 : motive ctor_1) (t : self) : motive t :=
  prec (motive := fun t' => motive t')
    (fun n => Nat.rec
        (motive := fun n' => (f : F n') → motive (pair (β := F) n' f))
        (fun _ => h0)
        (fun n₁ _ => Nat.rec
          (motive := fun n₂ =>
            (f : F (Nat.succ n₂)) → motive (pair (β := F) (Nat.succ n₂) f))
          (fun _ => h1)
          (fun n₂ _ f => EmptyAt.elim f)
          n₁)
        n)
    t

/-- ι, definitional — nothing to erase, because nothing was transported. -/
example {motive : self → Sort u} (h0 : motive ctor_0) (h1 : motive ctor_1) :
    Eq (rec_0 h0 h1 ctor_0) h0 := rfl' h0
example {motive : self → Sort u} (h0 : motive ctor_0) (h1 : motive ctor_1) :
    Eq (rec_0 h0 h1 ctor_1) h1 := rfl' h1

end BoolM

/- ── Type route with parameters, a field, and a pad: Option ────────── -/

namespace OptionM

/-- tag 0 ↦ `none`'s chain — the pad `D (u+1)` alone — tag 1 ↦ `some`'s
chain — the field alone — else empty. All at `Type u` exactly. -/
abbrev F (α : Type u) (n : Nat) : Type u :=
  Nat.rec (motive := fun _ => Type u)
    DS.{u}
    (fun n₁ _ => Nat.rec (motive := fun _ => Type u)
      α
      (fun _ _ => EmptyAt.{u+1})
      n₁)
    n

abbrev self (α : Type u) : Type u := PSigma (F α)

variable {α : Type u}

noncomputable def ctor_0 : self α := pair (β := F α) Nat.zero DS.canon.{u}
noncomputable def ctor_1 (a : α) : self α := pair (β := F α) (Nat.succ Nat.zero) a

noncomputable def rec_0 {motive : self α → Sort v} (hnone : motive ctor_0)
    (hsome : (a : α) → motive (ctor_1 a)) (t : self α) : motive t :=
  prec (motive := fun t' => motive t')
    (fun n => Nat.rec
        (motive := fun n' => (f : F α n') → motive (pair (β := F α) n' f))
        (fun _ => hnone)
        (fun n₁ _ => Nat.rec
          (motive := fun n₂ =>
            (f : F α (Nat.succ n₂)) → motive (pair (β := F α) (Nat.succ n₂) f))
          (fun a => hsome a)
          (fun n₂ _ f => EmptyAt.elim f)
          n₁)
        n)
    t

example {motive : self α → Sort v} (h0 : motive ctor_0)
    (h1 : (a : α) → motive (ctor_1 a)) :
    Eq (rec_0 h0 h1 ctor_0) h0 := rfl' h0
example {motive : self α → Sort v} (h0 : motive ctor_0)
    (h1 : (a : α) → motive (ctor_1 a)) (a : α) :
    Eq (rec_0 h0 h1 (ctor_1 a)) (h1 a) := rfl' (h1 a)

end OptionM

/- ── Type route at a `Sort (max 1 u)` carrier, dependent fields, no pad:
     Subtype ─────────────────────────────────────────────────────────── -/

namespace SubtypeM

abbrev F (α : Sort u) (p : α → Prop) (n : Nat) : Sort (max 1 u) :=
  Nat.rec (motive := fun _ => Sort (max 1 u))
    (PSigma (fun val : α => p val))
    (fun _ _ => EmptyAt.{max 1 u})
    n

abbrev self (α : Sort u) (p : α → Prop) : Sort (max 1 u) := PSigma (F α p)

variable {α : Sort u} {p : α → Prop}

noncomputable def ctor_0 (val : α) (property : p val) : self α p :=
  pair (β := F α p) Nat.zero (pair (β := fun val : α => p val) val property)

noncomputable def rec_0 {motive : self α p → Sort v}
    (hmk : (val : α) → (property : p val) → motive (ctor_0 val property))
    (t : self α p) : motive t :=
  prec (motive := fun t' => motive t')
    (fun n => Nat.rec
        (motive := fun n' => (f : F α p n') → motive (pair (β := F α p) n' f))
        (fun f =>
          prec (motive := fun f' => motive (pair (β := F α p) Nat.zero f'))
            (fun val property => hmk val property) f)
        (fun n₁ _ f => EmptyAt.elim f)
        n)
    t

example {motive : self α p → Sort v}
    (h : (val : α) → (property : p val) → motive (ctor_0 val property))
    (val : α) (property : p val) :
    Eq (rec_0 h (ctor_0 val property)) (h val property) := rfl' (h val property)

end SubtypeM

/- ── Type route, 0 constructors: Empty ─────────────────────────────── -/

namespace EmptyM

abbrev self : Type := PSigma (fun _ : Nat => EmptyAt.{1})

noncomputable def rec_0 {motive : self → Sort u} (t : self) : motive t :=
  prec (motive := fun t' => motive t')
    (fun n f => EmptyAt.elim f)
    t

end EmptyM

/- ── Prop route, small elimination: Or ─────────────────────────────── -/

namespace OrM

abbrev self (a b : Prop) : Prop :=
  (C : Prop) → ((h : a) → C) → ((h : b) → C) → C

variable {a b : Prop}

noncomputable def ctor_0 (h : a) : self a b := fun _ ka _ => ka h
noncomputable def ctor_1 (h : b) : self a b := fun _ _ kb => kb h

/-- Dependent recursion at a `Prop` motive: the motive's proof argument is
definitionally irrelevant, so the Church fold already produces it. -/
noncomputable def rec_0 {motive : self a b → Prop}
    (hl : (h : a) → motive (ctor_0 h)) (hr : (h : b) → motive (ctor_1 h))
    (t : self a b) : motive t :=
  t (motive t) (fun h => hl h) (fun h => hr h)

example {motive : self a b → Prop}
    (hl : (h : a) → motive (ctor_0 h)) (hr : (h : b) → motive (ctor_1 h)) (h : a) :
    Eq (rec_0 hl hr (ctor_0 h)) (hl h) := rfl' (hl h)

end OrM

/- ── Prop route, large elimination by extraction: And ──────────────── -/

namespace AndM

abbrev self (a b : Prop) : Prop := (C : Prop) → ((ha : a) → (hb : b) → C) → C

variable {a b : Prop}

noncomputable def ctor_0 (ha : a) (hb : b) : self a b := fun _ k => k ha hb

/-- `And` is subsingleton-eliminating: both fields are propositions, so
each is extracted by instantiating the Church encoding at the field itself,
and proof irrelevance closes the motive. -/
noncomputable def rec_0 {motive : self a b → Sort u}
    (hmk : (ha : a) → (hb : b) → motive (ctor_0 ha hb)) (t : self a b) :
    motive t :=
  hmk (t a (fun ha _ => ha)) (t b (fun _ hb => hb))

example {motive : self a b → Sort u}
    (hmk : (ha : a) → (hb : b) → motive (ctor_0 ha hb)) (ha : a) (hb : b) :
    Eq (rec_0 hmk (ctor_0 ha hb)) (hmk ha hb) := rfl' (hmk ha hb)

end AndM

/- ── Prop route, small elimination with a data field: Nonempty ─────── -/

namespace NonemptyM

abbrev self (α : Sort u) : Prop := (C : Prop) → ((val : α) → C) → C

variable {α : Sort u}

noncomputable def ctor_0 (val : α) : self α := fun _ k => k val

noncomputable def rec_0 {motive : self α → Prop}
    (hmk : (val : α) → motive (ctor_0 val)) (t : self α) : motive t :=
  t (motive t) (fun val => hmk val)

example {motive : self α → Prop} (hmk : (val : α) → motive (ctor_0 val)) (v : α) :
    Eq (rec_0 hmk (ctor_0 v)) (hmk v) := rfl' (hmk v)

end NonemptyM

/- ── Prop route, large elimination with no fields: True ────────────── -/

namespace TrueM

abbrev self : Prop := (C : Prop) → C → C
noncomputable def ctor_0 : self := fun _ c => c
noncomputable def rec_0 {motive : self → Sort u} (h : motive ctor_0) (t : self) :
    motive t := h

example {motive : self → Sort u} (h : motive ctor_0) :
    Eq (rec_0 h ctor_0) h := rfl' h

end TrueM
