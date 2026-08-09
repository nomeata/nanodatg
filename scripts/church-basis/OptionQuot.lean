/-!
Partial positive, and the precise location of the obstruction.

`Option A` — non-recursive, never empty — CAN be encoded from Π + `Eq` +
`False` + `Quot`, at the right universe (`Type u`, no inflation), with a full
dependent recursor into `Sort v` and propositional ι rules — PROVIDED the
classical kit is available: `em` (via `Classical.propDecidable`) to define the
junk-collapsing normalizer, and `Classical.choose` (indefinite description) to
extract the witness in the recursor.

`Classical.choose` is not `Classical.choice`: core derives it through
`Classical.indefiniteDescription`, whose result type is `{x // p x}` — a
`Subtype`.  In a basis without `Subtype`, `choose`/`choose_spec` would have to
be primitive axioms (statable: Church-`∃` is a Π type).  `mini` carries
neither `em` nor `choice`.

Carrier: quotient of `A → Prop` identifying everything that is not a
singleton predicate.  Classes = singletons (`some a`) + one junk class
(`none`).  The `∃`/`∨`/`∧` used below are core's inductives for convenience;
all are `Prop`-Church-encodable (the gist does exactly this).

This file must compile with **no errors** at leanprover/lean4:v4.29.1.
-/

universe u v

attribute [local instance] Classical.propDecidable

def IsSing {A : Type u} (P : A → Prop) : Prop := ∃ a, P = fun b => b = a

/-- Everything non-singleton is identified; singletons only with themselves. -/
def rel (A : Type u) (P Q : A → Prop) : Prop := P = Q ∨ (¬ IsSing P ∧ ¬ IsSing Q)

/-- The carrier — same universe as `Option A`, no inflation. -/
def OQ (A : Type u) : Type u := Quot (rel A)

def qnone {A : Type u} : OQ A := Quot.mk _ (fun _ => False)
def qsome {A : Type u} (a : A) : OQ A := Quot.mk _ (fun b => b = a)

theorem notSingEmpty (A : Type u) : ¬ IsSing (fun _ : A => False) := by
  intro h
  have ⟨a, ha⟩ := h
  exact (congrFun ha a).symm ▸ (rfl : a = a)

/-- `em` enters here: the normalizer is a case split on `IsSing`. -/
noncomputable def norm {A : Type u} (P : A → Prop) : A → Prop :=
  if IsSing P then P else fun _ => False

theorem norm_resp {A : Type u} (P Q : A → Prop) (h : rel A P Q) : norm P = norm Q := by
  cases h with
  | inl e => rw [e]
  | inr hpq => unfold norm; rw [if_neg hpq.1, if_neg hpq.2]

noncomputable def valPred {A : Type u} : OQ A → (A → Prop) :=
  Quot.lift norm norm_resp

theorem qsome_ne_qnone {A : Type u} (a : A) : qsome a ≠ qnone := by
  intro h
  have h2 : norm (fun b : A => b = a) = norm (fun _ : A => False) := congrArg valPred h
  rw [show norm (fun b : A => b = a) = fun b => b = a from if_pos ⟨a, rfl⟩,
      show norm (fun _ : A => False) = fun _ => False from if_neg (notSingEmpty A)] at h2
  exact (congrFun h2 a) ▸ (rfl : a = a)

theorem some_inj {A : Type u} {a c : A} (e : qsome a = qsome c) : a = c := by
  have h : norm (fun b : A => b = a) = norm (fun b : A => b = c) := congrArg valPred e
  rw [show norm (fun b : A => b = a) = fun b => b = a from if_pos ⟨a, rfl⟩,
      show norm (fun b : A => b = c) = fun b => b = c from if_pos ⟨c, rfl⟩] at h
  exact (congrFun h a) ▸ (rfl : a = a)

/-- Canonicity — every element is `qnone` or a `qsome` — via `Quot.ind`+`em`. -/
theorem canon {A : Type u} (o : OQ A) : o = qnone ∨ ∃ a, o = qsome a := by
  refine Quot.ind (β := fun o => o = qnone ∨ ∃ a, o = qsome a) (fun P => ?_) o
  cases Classical.em (IsSing P) with
  | inl h =>
      have ⟨a, ha⟩ := h
      exact Or.inr ⟨a, by rw [ha]; rfl⟩
  | inr h => exact Or.inl (Quot.sound (Or.inr ⟨h, notSingEmpty A⟩))

theorem ex_some {A : Type u} {o : OQ A} (h : ¬ o = qnone) : ∃ a, o = qsome a :=
  (canon o).resolve_left h

/-- The dependent recursor, into `Sort v` for every `v` — `choose` enters
here, to extract the witness from canonicity. -/
noncomputable def qrec {A : Type u} {motive : OQ A → Sort v}
    (n : motive qnone) (s : ∀ a, motive (qsome a)) (o : OQ A) : motive o :=
  if h : o = qnone then cast (congrArg motive h.symm) n
  else cast (congrArg motive (Classical.choose_spec (ex_some h)).symm)
         (s (Classical.choose (ex_some h)))

theorem cast_some {A : Type u} {motive : OQ A → Sort v} (s : ∀ a, motive (qsome a))
    {a c : A} (e : qsome a = qsome c) :
    cast (congrArg motive e.symm) (s c) = s a := by
  have hc : a = c := some_inj e
  subst hc
  rfl

/-- ι, propositionally (definitionally, even, at `qnone`). -/
theorem qrec_none {A : Type u} {motive : OQ A → Sort v}
    (n : motive qnone) (s : ∀ a, motive (qsome a)) : qrec n s qnone = n := by
  unfold qrec
  rw [dif_pos rfl]
  rfl

theorem qrec_some {A : Type u} {motive : OQ A → Sort v}
    (n : motive qnone) (s : ∀ a, motive (qsome a)) (a : A) :
    qrec n s (qsome a) = s a := by
  unfold qrec
  rw [dif_neg (qsome_ne_qnone a)]
  exact cast_some s (Classical.choose_spec (ex_some (qsome_ne_qnone a)))

/- The compiled axiom audit: everything above reduces to the three core
axioms — `em` and `choose` are what a from-scratch basis would axiomatize;
in core Lean they surface as `Classical.choice` + `propext` (Diaconescu). -/
#print axioms qrec_none
#print axioms qrec_some
#print axioms canon
