/-
# A constructor spelled through an abbreviation, on both sides of ι

Every recursor use site here states its **minor types** and its **major
premise** through `def`s that unfold to constructors — `nz : N := N.z`,
`ixa : IxA := Ix.ia` — rather than through the constructors themselves. Nothing
else about the file is unusual: two ordinary inductives, one plain and one
tag-indexed, their recursors wrapped, and the computation rules stated as
theorems proved by `Eq.refl _`.

**Lean accepts all of it definitionally, and the point of the fixture is that
mini's evidence axis does too.** Both halves of that used to fail, for two
different reasons, and each is one line of `mini/src`:

* **The minor's type.** `N.rec`'s first minor wants `m N.z`; this file writes
  `m nz`. Converting the two reduces `nz` to `N.z` on one side only, so the
  conversion's two endpoints are `⟦m N.z⟧` — a term the ι/δ chain *built*, by
  `conv::app_cong` inside the kernel — and `⟦m nz⟧`, which came from
  `infer_type` through `Interp::app`. Only the second was in the `parts` table,
  so `Checker::split_app` could take one side apart and not the other, and the
  congruence below it gapped as `no-endpoint`. `app_cong` now records both of
  its endpoints, which is what it owes as a *builder* of applicative terms.

* **The major premise.** `nrec … (ns n)` δ-reduces its major to `N.s n` before
  the ι rule can read the fields off. The ι site reduced the major with an
  acceptance-only `whnf` and then refused outright whenever it had moved, so
  `nrec … (ns n)` was filed `iota(N.rec)` while `nrec … (N.s n)` certified.
  The major is now reduced *with* its certificate and that conversion is
  composed in front of the rule.

# Why an abbreviation is not a spelling anything can avoid

This is the shape the mutual-inductive encoding emits: the aux encoding defines
`A := Aux Tag.ta` and `AmkB b := Aux.aB b`, and the recursor it installs as
`A.rec` **must** state its minors at `A.aB`, because a recursor stated at
`Aux.aB` is a different constant. `mutual_aux_encoding.lean` is the same
measurement at three mutually recursive members; this file is the mechanism
alone, at one plain family and one indexed one, so that a regression names the
mechanism rather than the encoding.

# Three constructors, and a base case among them

`N` and `Ix` each have three constructors and each has a non-recursive one.
Two would not do: a route that handled the first constructor and clamped for
the rest agrees with the correct one on every two-constructor family, and the
recursive/non-recursive split is what separates "the major reduced" from "the
major reduced *and* carried a field".

`Ix` is indexed so that the **other** ι table is exercised — `iota_ix_dep`'s,
not `iota_dep`'s — since the two are separate routes reached by separate arms
of the same match, and a fix applied to one arm only would pass here on `N`
alone.
-/
prelude

--#export Eq N nz ns nd nrec ruleZ ruleS ruleD
--#export Tag NMot nrec2 rule2Z rule2S
--#export Ix IxA IxB IxC ixa ixb ixc ixba irec iruleA iruleB

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

-- ── the plain family ────────────────────────────────────────────────────────

/-- Three constructors, one of them a base case, two of them recursive and
    distinguishable only by which they are. -/
inductive N : Type where
  | z : N
  | s : N → N
  | d : N → N

def nz : N := N.z
def ns (n : N) : N := N.s n
def nd (n : N) : N := N.d n

/-- The minors are stated at `nz`/`ns`/`nd`, never at `N.z`/`N.s`/`N.d`. -/
noncomputable def nrec {m : N → Sort v}
    (hz : m nz) (hs : (n : N) → m n → m (ns n)) (hd : (n : N) → m n → m (nd n))
    (t : N) : m t :=
  @N.rec m hz hs hd t

/-- The base case: the major is an abbreviation with no fields. -/
theorem ruleZ {m : N → Sort v}
    (hz : m nz) (hs : (n : N) → m n → m (ns n)) (hd : (n : N) → m n → m (nd n)) :
    Eq (nrec hz hs hd nz) hz := Eq.refl _

/-- A step: the major is an abbreviation applied to a field. -/
theorem ruleS {m : N → Sort v}
    (hz : m nz) (hs : (n : N) → m n → m (ns n)) (hd : (n : N) → m n → m (nd n)) (n : N) :
    Eq (nrec hz hs hd (ns n)) (hs n (nrec hz hs hd n)) := Eq.refl _

/-- The second step, which a route that clamped to the first would fail. -/
theorem ruleD {m : N → Sort v}
    (hz : m nz) (hs : (n : N) → m n → m (ns n)) (hd : (n : N) → m n → m (nd n)) (n : N) :
    Eq (nrec hz hs hd (nd n)) (hd n (nrec hz hs hd n)) := Eq.refl _

-- ── a motive the recursor has to compute ────────────────────────────────────

/-- The tag, used first to *select* a motive and then to index a family. -/
inductive Tag : Type where
  | ta : Tag
  | tb : Tag
  | tc : Tag

/-- A motive chosen by recursion on the tag.

    This is what separates the two bugs. With a motive handed in directly, the
    minor's expected type `m nz` and the recursor's `m N.z` are both terms
    `infer_type` built through `Interp::app`, and both decompose. With the
    motive *computed*, the expected type only reaches `m₂ N.z` by ι and δ, so
    its interpretation is a term `conv::app_cong` built inside the kernel — and
    an unrecorded one is an endpoint nothing below can take apart. -/
noncomputable def NMot (m1 : N → Sort v) (m2 : N → Sort v) (m3 : N → Sort v) :
    Tag → N → Sort v :=
  @Tag.rec (fun _ => N → Sort v) m1 m2 m3

/-- **`Tag.tb`, the middle one.** A selection that clamped to either end would
    pass at `ta` or at `tc`; only the middle pins that the tag is read. -/
noncomputable def nrec2 (m1 : N → Sort v) (m3 : N → Sort v) {m2 : N → Sort v}
    (hz : m2 nz) (hs : (n : N) → m2 n → m2 (ns n)) (hd : (n : N) → m2 n → m2 (nd n))
    (t : N) : m2 t :=
  @N.rec (NMot m1 m2 m3 Tag.tb) hz hs hd t

/-- Computed motive, abbreviated major, no field. -/
theorem rule2Z (m1 : N → Sort v) (m3 : N → Sort v) {m2 : N → Sort v}
    (hz : m2 nz) (hs : (n : N) → m2 n → m2 (ns n)) (hd : (n : N) → m2 n → m2 (nd n)) :
    Eq (nrec2 m1 m3 hz hs hd nz) hz := Eq.refl _

/-- Computed motive, abbreviated major, one field. -/
theorem rule2S (m1 : N → Sort v) (m3 : N → Sort v) {m2 : N → Sort v}
    (hz : m2 nz) (hs : (n : N) → m2 n → m2 (ns n)) (hd : (n : N) → m2 n → m2 (nd n)) (n : N) :
    Eq (nrec2 m1 m3 hz hs hd (ns n)) (hs n (nrec2 m1 m3 hz hs hd n)) := Eq.refl _

-- ── the indexed family ──────────────────────────────────────────────────────

/-- Indexed, three constructors, one recursive step that changes the tag. -/
inductive Ix : Tag → Type where
  | ia : Ix Tag.ta
  | ib : Ix Tag.tb
  | ic : Ix Tag.tc
  | iba : Ix Tag.ta → Ix Tag.tb

def IxA : Type := Ix Tag.ta
def IxB : Type := Ix Tag.tb
def IxC : Type := Ix Tag.tc

def ixa : IxA := Ix.ia
def ixb : IxB := Ix.ib
def ixc : IxC := Ix.ic
def ixba (a : IxA) : IxB := Ix.iba a

/-- Every minor stated through the abbreviations. -/
noncomputable def irec {m : (t : Tag) → Ix t → Sort v}
    (ha : m Tag.ta ixa) (hb : m Tag.tb ixb) (hc : m Tag.tc ixc)
    (hba : (a : IxA) → m Tag.ta a → m Tag.tb (ixba a))
    (t : Tag) (x : Ix t) : m t x :=
  @Ix.rec m ha hb hc hba t x

/-- A base case at an abbreviated major. -/
theorem iruleA {m : (t : Tag) → Ix t → Sort v}
    (ha : m Tag.ta ixa) (hb : m Tag.tb ixb) (hc : m Tag.tc ixc)
    (hba : (a : IxA) → m Tag.ta a → m Tag.tb (ixba a)) :
    Eq (irec ha hb hc hba Tag.ta ixa) ha := Eq.refl _

/-- A step at an abbreviated major carrying a field. -/
theorem iruleB {m : (t : Tag) → Ix t → Sort v}
    (ha : m Tag.ta ixa) (hb : m Tag.tb ixb) (hc : m Tag.tc ixc)
    (hba : (a : IxA) → m Tag.ta a → m Tag.tb (ixba a)) (a : IxA) :
    Eq (irec ha hb hc hba Tag.tb (ixba a)) (hba a (irec ha hb hc hba Tag.ta a)) := Eq.refl _
