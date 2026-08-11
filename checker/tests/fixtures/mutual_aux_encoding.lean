/-
# The aux encoding, written out by hand — and every rule really is `rfl`

**This fixture contains no `mutual` block.** It is the *output* the mutual
pipeline is meant to produce: the same three-member family as
`mutual_three_way_cycle.lean`, encoded as one tag-indexed inductive with the
type formers, constructors and recursors defined over it as ordinary `def`s and
the recursor rules stated as ordinary theorems. It exists to answer one design
question before any code is written to generate it.

The question is the one the whole design rests on: **does the encoding make the
recursor rules definitional?** If it does, the generator never has to prove
anything — it emits Lean terms and the existing evidence-producing checker turns
them into TG theorems, and the mutual pipeline can be ignorant of what a `Term`
or a `Thm` contains. If it does not, every rule needs a transport and the
pipeline has to know what it is transporting.

**It does.** `ruleA0`, `ruleAB` and `ruleCA` are `Eq.refl _`, and the kernel
takes them.

# Why they are `rfl`, in two ι rules

`Mot` is the motive of `Aux.rec`, and it is defined by recursion **on the tag**:
`Mot m1 m2 m3 Tag.ta` ι-reduces to `m1`. So a minor whose declared type is
`m1 (AmkB b)` is accepted where `Aux.rec` wants `Mot m1 m2 m3 Tag.ta (Aux.aB b)`,
with no coercion — the two are definitionally equal through `Tag.rec`'s ι rule.

Then `Arec … (AmkB b)` unfolds to `Aux.rec (Mot …) … Tag.ta (Aux.aB b)`, which
ι-reduces through `Aux`'s own rule to `haB b (Aux.rec (Mot …) … Tag.tb b)` — and
the second factor is exactly what `Brec … b` unfolds to, because `Arec` and
`Brec` pass `Aux.rec` the *same* motive and the *same* six minors and differ
only in the tag. So both sides reach the same normal form and reflexivity
closes it.

That is why the three `Xrec`s are written as three separate `def`s over one
shared argument list rather than as one function taking a tag: the shared list
is what makes the right-hand sides sayable.

# Three members and three rules, not one

`ruleA0` is a base case with no induction hypothesis. `ruleAB` is a step whose
hypothesis is at the *next* member. `ruleCA` is a step whose hypothesis wraps
around to the *first*. An encoding that got the tag right for the first member
and clamped for the rest passes `ruleA0` and `ruleAB` and fails `ruleCA`.

# What it does not settle

Nothing here says the *generator* is easy, and nothing here is a measurement of
the evidence axis. It says the Lean-side arithmetic works out, which is the
premise the generator would be built on and the cheapest thing to have refuted
early.
-/
prelude

--#export Tag Aux A B C
--#export Amk0 AmkB Bmk0 BmkC Cmk0 CmkA Mot Arec Brec Crec ruleA0 ruleAB ruleCA

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The tag. One constructor per member of the family being encoded. -/
inductive Tag : Type where
  | ta : Tag
  | tb : Tag
  | tc : Tag

/-- The whole family as one indexed inductive: every constructor of every
    member, with the member recorded in the index. -/
inductive Aux : Tag → Type where
  | a0 : Aux Tag.ta
  | aB : Aux Tag.tb → Aux Tag.ta
  | b0 : Aux Tag.tb
  | bC : Aux Tag.tc → Aux Tag.tb
  | c0 : Aux Tag.tc
  | cA : Aux Tag.ta → Aux Tag.tc

def A : Type := Aux Tag.ta
def B : Type := Aux Tag.tb
def C : Type := Aux Tag.tc

def Amk0 : A := Aux.a0
def AmkB (b : B) : A := Aux.aB b
def Bmk0 : B := Aux.b0
def BmkC (c : C) : B := Aux.bC c
def Cmk0 : C := Aux.c0
def CmkA (a : A) : C := Aux.cA a

/-- The three motives, packed into `Aux.rec`'s single tag-indexed one. This is
    the piece that makes the minors typecheck unchanged. -/
noncomputable def Mot (m1 : A → Sort v) (m2 : B → Sort v) (m3 : C → Sort v) :
    (t : Tag) → Aux t → Sort v :=
  @Tag.rec (fun t => Aux t → Sort v) m1 m2 m3

noncomputable def Arec {m1 : A → Sort v} {m2 : B → Sort v} {m3 : C → Sort v}
    (ha0 : m1 Amk0) (haB : (b : B) → m2 b → m1 (AmkB b))
    (hb0 : m2 Bmk0) (hbC : (c : C) → m3 c → m2 (BmkC c))
    (hc0 : m3 Cmk0) (hcA : (a : A) → m1 a → m3 (CmkA a))
    (t : A) : m1 t :=
  @Aux.rec (Mot m1 m2 m3) ha0 haB hb0 hbC hc0 hcA Tag.ta t

noncomputable def Brec {m1 : A → Sort v} {m2 : B → Sort v} {m3 : C → Sort v}
    (ha0 : m1 Amk0) (haB : (b : B) → m2 b → m1 (AmkB b))
    (hb0 : m2 Bmk0) (hbC : (c : C) → m3 c → m2 (BmkC c))
    (hc0 : m3 Cmk0) (hcA : (a : A) → m1 a → m3 (CmkA a))
    (t : B) : m2 t :=
  @Aux.rec (Mot m1 m2 m3) ha0 haB hb0 hbC hc0 hcA Tag.tb t

noncomputable def Crec {m1 : A → Sort v} {m2 : B → Sort v} {m3 : C → Sort v}
    (ha0 : m1 Amk0) (haB : (b : B) → m2 b → m1 (AmkB b))
    (hb0 : m2 Bmk0) (hbC : (c : C) → m3 c → m2 (BmkC c))
    (hc0 : m3 Cmk0) (hcA : (a : A) → m1 a → m3 (CmkA a))
    (t : C) : m3 t :=
  @Aux.rec (Mot m1 m2 m3) ha0 haB hb0 hbC hc0 hcA Tag.tc t

/-- A base case: no induction hypothesis at all. -/
theorem ruleA0 {m1 : A → Sort v} {m2 : B → Sort v} {m3 : C → Sort v}
    (ha0 : m1 Amk0) (haB : (b : B) → m2 b → m1 (AmkB b))
    (hb0 : m2 Bmk0) (hbC : (c : C) → m3 c → m2 (BmkC c))
    (hc0 : m3 Cmk0) (hcA : (a : A) → m1 a → m3 (CmkA a)) :
    Eq (Arec ha0 haB hb0 hbC hc0 hcA Amk0) ha0 := Eq.refl _

/-- A step whose induction hypothesis is at the next member. -/
theorem ruleAB {m1 : A → Sort v} {m2 : B → Sort v} {m3 : C → Sort v}
    (ha0 : m1 Amk0) (haB : (b : B) → m2 b → m1 (AmkB b))
    (hb0 : m2 Bmk0) (hbC : (c : C) → m3 c → m2 (BmkC c))
    (hc0 : m3 Cmk0) (hcA : (a : A) → m1 a → m3 (CmkA a)) (b : B) :
    Eq (Arec ha0 haB hb0 hbC hc0 hcA (AmkB b))
       (haB b (Brec ha0 haB hb0 hbC hc0 hcA b)) := Eq.refl _

/-- A step whose induction hypothesis wraps around to the first. -/
theorem ruleCA {m1 : A → Sort v} {m2 : B → Sort v} {m3 : C → Sort v}
    (ha0 : m1 Amk0) (haB : (b : B) → m2 b → m1 (AmkB b))
    (hb0 : m2 Bmk0) (hbC : (c : C) → m3 c → m2 (BmkC c))
    (hc0 : m3 Cmk0) (hcA : (a : A) → m1 a → m3 (CmkA a)) (a : A) :
    Eq (Crec ha0 haB hb0 hbC hc0 hcA (CmkA a))
       (hcA a (Arec ha0 haB hb0 hbC hc0 hcA a)) := Eq.refl _
