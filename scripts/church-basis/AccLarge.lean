/-!
Expected to FAIL: large elimination for the `Prop`-Church `Acc`.  The naive
term instantiates the impredicative quantifier at the motive, and the motive
lands in `Sort v`, not `Prop`.
-/
universe u v

def CAcc {α : Sort u} (r : α → α → Prop) (x : α) : Prop :=
  ∀ S : α → Prop, (∀ y, (∀ z, r z y → S z) → S y) → S x

noncomputable def CAcc.recLarge {α : Sort u} {r : α → α → Prop}
    (motive : α → Sort v)
    (step : ∀ x, (∀ y, r y x → motive y) → motive x) :
    ∀ x, CAcc r x → motive x :=
  fun x hx => hx motive step
