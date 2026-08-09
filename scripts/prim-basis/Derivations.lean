/-
# Layer 3 evidence: models from the five primitives, compiled

Every construction the `--prim-models` layer emits is prototyped here in a
`prelude` file (no Init, term mode only — which is what an `Expr` generator
can build). The five primitives are declared at Lean's own shapes, exactly
as the splice inserts them; `funext` is axiomatized at the statement
`Modelgen.ensureFunext` derives (the layer uses the derived one).

Compiled at `leanprover/lean4:v4.29.1` with zero errors. Each `example …
:= rfl' _` line is a definitional-ι check; each `theorem` is a
propositional one.

Two elaborator artefacts of `prelude` mode, neither of which touches the
generator (it builds explicit `Expr`s and never elaborates): constructor
applications with implicit arguments trip a missing-`CoeFun` path, so the
constructors are used through wrapper `def`s (`rfl'`, `pair`, `prec`, `J`);
and the five wrappers plus every model `def` are `noncomputable` because
the compiler backend is absent.

Sharpening of the commission verified here: the `Sigma` primitive must be
**`PSigma`-shaped** (`{α : Sort u} → (α → Sort v) → Sort (max 1 u v)`).
`Subtype`, structures with `Prop` fields, and every `Prop`-fibred pair
below need a Σ over `Sort`, which Lean's `Type`-only `Sigma` cannot give
without `PLift` — a sixth inductive.
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

/- funext, at the statement the prelude splice derives (from Quot +
Quot.sound in the real layer; an axiom here — same statement). -/
axiom funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
  (h : (x : α) → Eq (f x) (g x)) : Eq f g

/- ── wrappers (prelude-mode elaborator convenience only) ───────────── -/

noncomputable def rfl' {α : Sort u} (a : α) : Eq a a := @Eq.refl α a

noncomputable def pair {α : Sort u} {β : α → Sort v} (fst : α) (snd : β fst) :
    PSigma β := @PSigma.mk α β fst snd

noncomputable def prec {α : Sort u} {β : α → Sort v} {motive : PSigma β → Sort w}
    (m : (fst : α) → (snd : β fst) → motive (pair fst snd)) (t : PSigma β) :
    motive t := @PSigma.rec α β motive m t

noncomputable def J {α : Sort u} {a : α} (motive : (b : α) → Eq a b → Sort v)
    (m : motive a (rfl' a)) {b : α} (h : Eq a b) : motive b h :=
  @Eq.rec α a motive m b h

noncomputable def symmEq {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  J (fun x _ => Eq x a) (rfl' a) h

/- ── shared kit the generator emits inline ─────────────────────────── -/

/-- `Sing (a+1)`: an inhabited, propositionally-singleton type at exactly
`Sort (a+1)`, for any level `a`. The Π's body is never `Prop`, so
`imax (a+1) (max 1 a) = a+1` on the nose. -/
abbrev SingS : Sort (u + 1) :=
  (α : Sort u) → PSigma (fun f : α → α => Eq f (fun x => x))

noncomputable def SingS.canon : SingS.{u} :=
  fun α => pair (fun x => x) (rfl' (fun x => x))

/-- Uniqueness, from `funext` and one `J` per component. The `J` runs along
`symmEq h : id = f`, so the transported pair stays well-typed; its base
case is `rfl'` because the leftover proof component is definitionally
irrelevant. -/
theorem SingS.uniq (s : SingS.{u}) : Eq s SingS.canon.{u} :=
  funext fun α =>
    prec (motive := fun p => Eq p (pair (β := fun f' : α → α => Eq f' (fun x => x))
        (fun x => x) (rfl' (fun x => x))))
      (fun f h =>
        J (fun g _ =>
            (hg : Eq g (fun x : α => x)) →
              Eq (pair (β := fun f' : α → α => Eq f' (fun x => x)) g hg)
                 (pair (fun x => x) (rfl' (fun x => x))))
          (fun _ => rfl' (pair (β := fun f' : α → α => Eq f' (fun x => x))
            (fun x => x) (rfl' (fun x => x))))
          (symmEq h) h)
      (s α)

/-- `Sing (max a b)` from `Sing a` and `Sing b`: at `Sort (max 1 u v)`,
which is `Sort (max u v)` whenever either side is never-zero. -/
abbrev SingM (A : Sort u) (B : Sort v) : Sort (max 1 u v) :=
  PSigma (fun _ : A => B)

noncomputable def SingM.canon (A : Sort u) (B : Sort v) (a : A) (b : B) :
    SingM A B := pair a b

theorem SingM.uniq (A : Sort u) (B : Sort v) (a : A) (b : B)
    (ua : (x : A) → Eq x a) (ub : (x : B) → Eq x b)
    (s : SingM A B) : Eq s (SingM.canon A B a b) :=
  prec (motive := fun p => Eq p (SingM.canon A B a b))
    (fun x y =>
      J (motive := fun a' _ =>
          Eq (pair (β := fun _ : A => B) x y) (pair (β := fun _ : A => B) a' b))
        (J (motive := fun b' _ =>
            Eq (pair (β := fun _ : A => B) x y) (pair (β := fun _ : A => B) x b'))
          (rfl' (pair (β := fun _ : A => B) x y)) (ub y))
        (ua x))
    s

/-- An empty type at exactly `Sort w` for never-zero `w`:
`Σ' (h : False), False.rec h` is at `Sort (max 1 0 w) = Sort w`. -/
abbrev EmptyAt : Sort (max 1 w) :=
  PSigma (fun h : False => False.rec (motive := fun _ => Sort w) h)

noncomputable def EmptyAt.elim {motive : Sort v} (e : EmptyAt.{w}) : motive :=
  False.rec (motive := fun _ => motive)
    (prec (motive := fun _ => False) (fun h _ => h) e)

/- ── Type route, worked: Bool ──────────────────────────────────────── -/


namespace BoolM

/-- The fibre family: tag 0 ↦ nullary chain, tag 1 ↦ nullary chain, else
empty. Written as the generator writes it: a `Nat.rec` cases tower. -/
abbrev F (n : Nat) : Type :=
  Nat.rec (motive := fun _ => Type)
    SingS.{0}
    (fun n₁ _ => Nat.rec (motive := fun _ => Type)
      SingS.{0}
      (fun _ _ => EmptyAt.{1})
      n₁)
    n

abbrev self : Type := PSigma F

noncomputable def ctor_0 : self := pair (β := F) Nat.zero SingS.canon.{0}
noncomputable def ctor_1 : self := pair (β := F) (Nat.succ Nat.zero) SingS.canon.{0}

/-- `Bool.rec`'s shape at the model's names, verbatim modulo renaming. -/
noncomputable def rec_0 {motive : self → Sort u}
    (h0 : motive ctor_0) (h1 : motive ctor_1) (t : self) : motive t :=
  prec (motive := fun t' => motive t')
    (fun n => Nat.rec
        (motive := fun n' => (f : F n') → motive (pair (β := F) n' f))
        (fun f =>
          J (fun s _ => motive (pair (β := F) Nat.zero s)) h0 (symmEq (SingS.uniq f)))
        (fun n₁ _ => Nat.rec
          (motive := fun n₂ =>
            (f : F (Nat.succ n₂)) → motive (pair (β := F) (Nat.succ n₂) f))
          (fun f =>
            J (fun s _ => motive (pair (β := F) (Nat.succ Nat.zero) s)) h1
              (symmEq (SingS.uniq f)))
          (fun n₂ _ f => EmptyAt.elim.{u, 1} f)
          n₁)
        n)
    t

/-- ι, definitional: the transports sit on closed self-equalities, which
proof irrelevance plus ι erase. -/
example {motive : self → Sort u} (h0 : motive ctor_0) (h1 : motive ctor_1) :
    Eq (rec_0 h0 h1 ctor_0) h0 := rfl' h0
example {motive : self → Sort u} (h0 : motive ctor_0) (h1 : motive ctor_1) :
    Eq (rec_0 h0 h1 ctor_1) h1 := rfl' h1

end BoolM

/- ── Type route with parameters, a field, and a pad: Option ────────── -/

namespace OptionM

/-- tag 0 ↦ `none`'s chain (`Sing (u+1)`), tag 1 ↦ `some`'s chain (the
field alone), else empty. All at `Type u` exactly. -/
abbrev F (α : Type u) (n : Nat) : Type u :=
  Nat.rec (motive := fun _ => Type u)
    SingS.{u}
    (fun n₁ _ => Nat.rec (motive := fun _ => Type u)
      α
      (fun _ _ => EmptyAt.{u+1})
      n₁)
    n

abbrev self (α : Type u) : Type u := PSigma (F α)

variable {α : Type u}

noncomputable def ctor_0 : self α := pair (β := F α) Nat.zero SingS.canon.{u}
noncomputable def ctor_1 (a : α) : self α := pair (β := F α) (Nat.succ Nat.zero) a

noncomputable def rec_0 {motive : self α → Sort v} (hnone : motive ctor_0)
    (hsome : (a : α) → motive (ctor_1 a)) (t : self α) : motive t :=
  prec (motive := fun t' => motive t')
    (fun n => Nat.rec
        (motive := fun n' => (f : F α n') → motive (pair (β := F α) n' f))
        (fun f =>
          J (fun s _ => motive (pair (β := F α) Nat.zero s)) hnone
            (symmEq (SingS.uniq f)))
        (fun n₁ _ => Nat.rec
          (motive := fun n₂ =>
            (f : F α (Nat.succ n₂)) → motive (pair (β := F α) (Nat.succ n₂) f))
          (fun a => hsome a)
          (fun n₂ _ f => EmptyAt.elim.{v, u+1} f)
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
        (fun n₁ _ f => EmptyAt.elim.{v, max 1 u} f)
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
    (fun n f => EmptyAt.elim.{u, 1} f)
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
