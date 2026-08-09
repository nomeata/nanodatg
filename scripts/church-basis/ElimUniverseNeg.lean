/-!
Expected to FAIL: a Church encoding fixes its elimination universe.  The real
`List.rec` eliminates into `Sort v` for every `v`; the Church candidate at
universe 0 cannot even fold into `Type 1`.
-/

def CList (A : Type) : Type 1 := ∀ X : Type, X → (A → X → X) → X

def crecBig {A : Type} (l : CList A) (X : Type 1) (n : X) (c : A → X → X) : X :=
  l X n c
