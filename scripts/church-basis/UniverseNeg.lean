/-!
Expected to FAIL: universe inflation.  The Church carrier for `List` cannot be
given `List`'s own type former type `Type u → Type u` — quantifying over
`Type u` puts the encoding in `Type (u+1)`.
-/
universe u

def ListModel : Type u → Type u := fun A => ∀ X : Type u, X → (A → X → X) → X
