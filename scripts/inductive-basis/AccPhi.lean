/-
AccPhi.lean — the subsingleton-eliminating Prop class (thesis §5.3), with a
compiled REFUTATION of the thesis's stated accφ reduction and a compiled
REPAIR that supports the recursor uniformly.

The thesis (thesis.txt:1826-1889) translates a subsingleton-eliminating
Prop-valued inductive to `accφ_r` — accessibility restricted by a predicate
φ — and claims (thesis.txt:1838) that accφ can be built from plain acc as

    accφ_r x := ∃ h : φ x, acc_{r'} (x, h)      r' := r on the subtype {x // φ x}

with the recursor construction "left as future work" (§5.4, thesis.txt:1898).

1. REFUTATION (`section ThesisLiteral`): on the thesis's own running example
   (thesis.txt:1848)

     P := μ t : N → N → Prop. (intro : ∀ n, n > 2 → (∀ m, m < n → t n m) → t 0 n)

   the subtype carrier is WRONG: restricting the relation to the subtype
   deletes exactly the r-predecessors that fail φ, so ⟨0,3⟩ — inaccessible
   in the μ-type, whose recursive premise ranges over the FULL index space —
   becomes vacuously accessible in the subtype. The literal carrier is
   inhabited at (0,3) (`junk`), the μ-type is empty there, and the recursor
   is underivable: `literal_has_no_rec` derives False from any term of the
   recursor's type (even at Prop motives). This is a genuine gap in the
   thesis's §5.3→§5.4 hand-off, visible only when the recursor is actually
   constructed.

2. REPAIR (`section Repair`): take accessibility over the FULL space and
   fold φ into a hereditary condition along the Church-encoded
   reflexive-transitive closure of r:

     AccPhi r φ x := Acc r x ∧ ∀ y, Reach r y x → φ y

   This is the least fixed point of  T x ⇐ φ x ∧ ∀ y, r y x → T y  (the μ
   accφ), and — the §5.4 content — its φ-restricted intro and its LARGE
   dependent recursor with the μ-type's exact minor premise are both
   derivable: `AccPhi.intro`, `AccPhi.elim`, with ι BY RFL
   (`AccPhi.iota`). The derivation consumes Acc.rec (large, basis), Eq,
   Prop-logic (Church-encodable; core ∧/∃ are used below but only ever
   eliminated into Prop), and definitional proof irrelevance — the
   recursor's proof-argument transport is free because the carrier is a
   Prop.

3. INSTANCE (`section Instance`): the generic strong-recursion shape

     inductive Down (lt) : α → Prop | mk : ∀ x, (∀ y, lt y x → Down y) → Down x

   (subsingleton: index argument + recursive argument), modelled by the
   repair with constructor and large recursor at Down.rec's exact shape,
   ι by rfl — the non-degenerate witness that the repair also works where
   the type is inhabited.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean AccPhi.lean
Expected: 0 errors.
-/
universe u w
set_option linter.unusedVariables false

-- ═════════════════════════════════════════════════════════════════════════
section ThesisLiteral
-- ═════════════════════════════════════════════════════════════════════════

/-- The thesis's running example (thesis.txt:1848), as Lean's kernel takes
    it. Subsingleton: `n` appears in the output indices, `hgt` is a Prop,
    `f` is recursive — so `P.rec` eliminates into `Sort w`. -/
inductive P : Nat → Nat → Prop
  | intro : ∀ n, 2 < n → (∀ m, m < n → P n m) → P 0 n

noncomputable example : ∀ {motive : (a b : Nat) → P a b → Sort w},
    (∀ n (hgt : 2 < n) (f : ∀ m, m < n → P n m),
      (∀ m (hm : m < n), motive n m (f m hm)) → motive 0 n (.intro n hgt f)) →
    ∀ {a b} (t : P a b), motive a b t := @P.rec

/-- The packed index space and the thesis's φ and r (thesis.txt:1853-1855). -/
def X : Type := PSigma (fun _ : Nat => Nat)
def phi (x : X) : Prop := ∃ n, x = ⟨0, n⟩ ∧ 2 < n
def r (x' x : X) : Prop := ∃ n m, x = ⟨0, n⟩ ∧ m < n ∧ x' = ⟨n, m⟩

/-- The thesis.txt:1838 carrier, literally: acc on the φ-subtype. -/
def SubT : Type := PSigma phi
def rsub (y x : SubT) : Prop := r y.1 x.1
def Plit (a b : Nat) : Prop := ∃ h : phi ⟨a, b⟩, Acc rsub ⟨⟨a, b⟩, h⟩

/-- Two projection facts about the packed pairs. -/
theorem pair_fst {a b c d : Nat} (h : (⟨a, b⟩ : X) = ⟨c, d⟩) : a = c :=
  congrArg PSigma.fst h
theorem pair_snd {a b c d : Nat} (h : (⟨a, b⟩ : X) = ⟨c, d⟩) : b = d :=
  congrArg (fun p : X => p.2) h

/-- No subtype point is an r-predecessor of a φ-position: an r-edge's
    source is ⟨n, m⟩ with 2 < n, and φ forces first component 0. -/
theorem no_sub_pred {s y : SubT} (hry : rsub y s)
    (hs : ∃ n, s.1 = ⟨0, n⟩ ∧ 2 < n) : False := by
  obtain ⟨n, m, hs1, _hmn, hy1⟩ := hry
  obtain ⟨n', hs1', hn'⟩ := hs
  obtain ⟨n'', hy2, _hn''⟩ := y.2
  -- s.1 = ⟨0,n⟩ and s.1 = ⟨0,n'⟩ force n = n'; y.1 = ⟨n,m⟩ and y.1 = ⟨0,n''⟩
  -- force n = 0; but 2 < n' = n. Contradiction.
  have hnn' : n = n' := pair_snd (hs1.symm.trans hs1')
  have hn0 : n = 0 := pair_fst (hy1.symm.trans hy2)
  omega

/-- The junk inhabitant: (0,3) is vacuously accessible in the subtype. -/
theorem junk : Plit 0 3 :=
  ⟨⟨3, rfl, by decide⟩,
   .intro _ (fun _y hry => (no_sub_pred hry ⟨3, rfl, by decide⟩).elim)⟩

/-- The literal carrier's introduction rule DOES exist (its accessibility
    is vacuous for the same reason `junk` exists) ... -/
theorem introLit (n : Nat) (hgt : 2 < n) (_f : ∀ m, m < n → Plit n m) :
    Plit 0 n :=
  ⟨⟨n, rfl, hgt⟩,
   .intro _ (fun _y hry => (no_sub_pred hry ⟨n, rfl, hgt⟩).elim)⟩

/-- ... but the μ-type's subtree positions are φ-empty, ... -/
theorem plit_sub_empty {n m : Nat} (hn : 2 < n) (h : Plit n m) : False := by
  obtain ⟨⟨n', h1, _⟩, _⟩ := h
  have := pair_fst h1
  omega

/-- ... so the recursor for the literal carrier — stated here at Prop
    motives, which the subsingleton-eliminating `Sort w` recursor
    instantiates to — is underivable: any term of its type proves False.
    The minor premise is dischargeable because its `f` argument maps a
    nonempty domain into φ-empty carriers; the major premise is `junk`. -/
theorem literal_has_no_rec
    (rec : ∀ (motive : ∀ a b, Plit a b → Prop),
      (∀ n (hgt : 2 < n) (f : ∀ m, m < n → Plit n m),
        (∀ m (hm : m < n), motive n m (f m hm)) →
        motive 0 n (introLit n hgt f)) →
      ∀ a b (t : Plit a b), motive a b t) : False :=
  rec (fun _ _ _ => False)
    (fun n hgt f _ => ((plit_sub_empty hgt) (f 0 (by omega))).elim)
    0 3 junk

end ThesisLiteral

-- ═════════════════════════════════════════════════════════════════════════
section Repair
-- ═════════════════════════════════════════════════════════════════════════

variable {α : Sort u}

/-- Church reflexive-transitive closure: `Reach r y x` — y is an iterated
    r-predecessor of x. -/
def Reach (r : α → α → Prop) (y x : α) : Prop :=
  ∀ C : α → Prop, C x → (∀ a b, r a b → C b → C a) → C y

theorem Reach.refl (r : α → α → Prop) (x : α) : Reach r x x :=
  fun _ hx _ => hx
/-- Prepend an edge at the far end (y → z, z reaches x). -/
theorem Reach.head {r : α → α → Prop} {y z x : α}
    (hr : r y z) (hzx : Reach r z x) : Reach r y x :=
  fun C hx hstep => hstep y z hr (hzx C hx hstep)
/-- Append an edge at the near end (z reaches y, y → x). -/
theorem Reach.tail {r : α → α → Prop} {z y x : α}
    (hzy : Reach r z y) (hr : r y x) : Reach r z x :=
  fun C hx hstep => hzy C (hstep y x hr hx) hstep

/-- The repaired accφ: accessibility over the FULL space, φ hereditarily
    along the closure. This is the least fixed point of
    `T x ⇐ φ x ∧ ∀ y, r y x → T y`, i.e. the μ-type accφ_r of
    thesis.txt:1832. -/
def AccPhi (r : α → α → Prop) (φ : α → Prop) (x : α) : Prop :=
  Acc r x ∧ ∀ y, Reach r y x → φ y

variable {r : α → α → Prop} {φ : α → Prop}

/-- Path decomposition for the Church closure: a reach into x is either
    trivial or enters through an r-child of x. (Prop-logic only.) -/
theorem Reach.cases {y x : α} (hyx : Reach r y x) :
    y = x ∨ ∃ c, r c x ∧ Reach r y c :=
  hyx (fun z => z = x ∨ ∃ c, r c x ∧ Reach r z c)
    (Or.inl rfl)
    (fun a b hab hb => hb.elim
      (fun hbx => Or.inr ⟨a, hbx ▸ hab, Reach.refl r a⟩)
      (fun ⟨c, hcx, hbc⟩ => Or.inr ⟨c, hcx, Reach.head hab hbc⟩))

/-- The μ-type's introduction rule: hereditariness at x is φ x at the
    trivial path and the children's hereditariness on the rest.
    (A `def`, not a `theorem`, so that the ι check below can unfold it.) -/
def AccPhi.intro {x : α} (hφ : φ x)
    (f : ∀ y, r y x → AccPhi r φ y) : AccPhi r φ x :=
  ⟨.intro x (fun y hr => (f y hr).1),
   fun y hyx => hyx.cases.elim
     (fun hxy => hxy ▸ hφ)
     (fun ⟨c, hcx, hyc⟩ => (f c hcx).2 y hyc)⟩

/-- The large dependent eliminator, with the μ-type's exact minor premise:
    Acc.rec over the accessibility component; the hereditary component
    supplies φ at every node; the recursor's proof argument needs no
    transport because `AccPhi r φ x` is a Prop (definitional proof
    irrelevance). -/
noncomputable def AccPhi.elim
    {motive : ∀ x, AccPhi r φ x → Sort w}
    (minor : ∀ x (hφ : φ x) (f : ∀ y, r y x → AccPhi r φ y),
      (∀ y (hr : r y x), motive y (f y hr)) → motive x (.intro hφ f))
    (x : α) (t : AccPhi r φ x) : motive x t :=
  @Acc.rec α r
    (fun x _ => (∀ y, Reach r y x → φ y) → ∀ t' : AccPhi r φ x, motive x t')
    (fun x h ih hered _t' =>
      minor x (hered x (Reach.refl r x))
        (fun y hr => ⟨h y hr, fun z hzy => hered z (Reach.tail hzy hr)⟩)
        (fun y hr => ih y hr (fun z hzy => hered z (Reach.tail hzy hr))
          ⟨h y hr, fun z hzy => hered z (Reach.tail hzy hr)⟩))
    x t.1 t.2 t

/-- ι, definitionally. -/
theorem AccPhi.iota
    {motive : ∀ x, AccPhi r φ x → Sort w}
    (minor : ∀ x (hφ : φ x) (f : ∀ y, r y x → AccPhi r φ y),
      (∀ y (hr : r y x), motive y (f y hr)) → motive x (.intro hφ f))
    (x : α) (hφ : φ x) (f : ∀ y, r y x → AccPhi r φ y) :
    AccPhi.elim minor x (.intro hφ f)
      = minor x hφ f (fun y hr => AccPhi.elim minor y (f y hr)) := rfl

end Repair

-- ═════════════════════════════════════════════════════════════════════════
section Instance
-- ═════════════════════════════════════════════════════════════════════════

variable {α : Sort u} (lt : α → α → Prop)

/-- The generic strong-recursion shape: subsingleton (index argument plus
    recursive argument), large-eliminating. -/
inductive Down : α → Prop
  | mk : ∀ x, (∀ y, lt y x → Down y) → Down x

noncomputable example : ∀ {motive : ∀ x, Down lt x → Sort w},
    (∀ x (f : ∀ y, lt y x → Down lt y),
      (∀ y (hy : lt y x), motive y (f y hy)) → motive x (.mk x f)) →
    ∀ {x} (t : Down lt x), motive x t := @Down.rec α lt

/-- Its model by the repair: φ is trivial (the schema's φ for a constructor
    with no Prop arguments and a fully general index), r is lt. -/
def Down' (x : α) : Prop := AccPhi lt (fun _ => ∀ p : Prop, p → p) x

def Down'.mk (x : α) (f : ∀ y, lt y x → Down' lt y) : Down' lt x :=
  AccPhi.intro (fun _ h => h) f

noncomputable def Down'.elim {motive : ∀ x, Down' lt x → Sort w}
    (minor : ∀ x (f : ∀ y, lt y x → Down' lt y),
      (∀ y (hy : lt y x), motive y (f y hy)) → motive x (Down'.mk lt x f))
    {x : α} (t : Down' lt x) : motive x t :=
  AccPhi.elim (fun x _ f ih => minor x f ih) x t

theorem Down'.iota {motive : ∀ x, Down' lt x → Sort w}
    (minor : ∀ x (f : ∀ y, lt y x → Down' lt y),
      (∀ y (hy : lt y x), motive y (f y hy)) → motive x (Down'.mk lt x f))
    (x : α) (f : ∀ y, lt y x → Down' lt y) :
    Down'.elim lt minor (Down'.mk lt x f)
      = minor x f (fun y hy => Down'.elim lt minor (f y hy)) := rfl

end Instance

-- ── Axiom audit: the CONSTRUCTION is axiom-free; the refutation PROOF picks
--    up propext/Quot.sound through the omega/simp machinery it is stated
--    with, which is incidental to its content ───────────────────────────────
/-- info: 'AccPhi.elim' does not depend on any axioms -/
#guard_msgs in #print axioms AccPhi.elim
/-- info: 'Down'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms Down'.elim
/-- info: 'literal_has_no_rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms literal_has_no_rec
