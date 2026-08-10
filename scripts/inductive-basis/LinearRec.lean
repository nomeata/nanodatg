/-
LinearRec.lean — the recursive, never-zero-sorted ("Type route"), LINEARLY
RECURSIVE class, modelled uniformly over {Eq, PSigma, Nat, PULiftP} plus Π,
Prop, proof irrelevance, structure eta and K-like `Eq.rec` reduction.
`False` is NOT used: Church `CFalse` stands in for it.

This is the term-by-term prototype for the `modelgen` generator arm.  Every
term is an EXPLICIT recursor application (`@Nat.rec`, `@PSigma.rec`,
`@Eq.rec`, `@PULiftP.rec`); no tactic is used anywhere, so everything here is
directly emittable as a raw `Expr`.

Generalises `TypeRoutes.lean`'s `List'` (the `Σ'(n : Nat), V n` tuple tower)
and its `PSum'` (the `Nat`-tagged sum with an empty fibre beyond the tag
count) to an arbitrary single inductive in which

  * every constructor has AT MOST ONE recursive field, and
  * no recursive field occurs under a binder.

Constructors split into BASE (no recursive field) and STEP (exactly one, at
an arbitrary position in the field telescope).  The schema is

    V 0       := Σ'(tag : Nat), Base_tag           -- Nat.rec tag tower
    V (n+1)   := Σ'(tag : Nat), Step_tag (V n)     -- Nat.rec tag tower
    T         := Σ'(n : Nat), V n

    base ctor  c_j f₁ … f_k        := ⟨0,      ⟨j, f₁, …, f_k, pad⟩⟩
    step ctor  c_j pre… r post…    := ⟨r.1+1,  ⟨j, pre…, r.2, post…, pad⟩⟩

Three REPAIRS to that schema were forced by compiling it (see the verdict at
the foot of the file):

  R1. Every chain is TERMINATED BY A PAD, including chains of length ≥ 1.
      Without it a constructor all of whose fields are `Prop`s (Tri'.b1)
      would have a `Sort 0` chain, which cannot inhabit a `Type u` fibre;
      and the k = 0 case would need a separate rule.  With it the chain
      rule is uniform in the field count, k = 0 included.

  R2. The pad is `PULiftP.{ℓ} CTrue` at the fibre's own level ℓ, NOT
      TypeRoutes' `D1`/`DS` pair.  `PULiftP.{ℓ} CTrue` is a DEFINITIONAL
      singleton at every ℓ (structure eta on the single-constructor
      `PULiftP` + proof irrelevance on `CTrue`), so one pad serves all
      levels and no `Eq.rec` transport is ever needed for a pad.
      (TypeRoutes' `PULiftP'.eta` transport in `PSum'.elim` is therefore
      also unnecessary.)

  R3. A tag tower with ZERO real tags must be the CONSTANT family
      `fun _ => EmptyF.{ℓ}`, not a `Nat.rec` whose branches both return
      `EmptyF` — otherwise `Fib tag` is stuck on the bound tag variable
      inside `elim`.  See §4.

Three targets, chosen so that no two of them can hide an ordering bug:

  1. `List' α : Type u`  — 1 param, 1 base ctor (0 fields), 1 step ctor with
     the recursive field LAST.  Level-polymorphic in α and in the motive.
  2. `MName' : Type`     — 0 params, 3 ctors, recursive field FIRST, two
     distinct opaque payload types (`String`, `Nat`), two step tags.
  3. `Tri' α p : Type u` — 2 params (one `Type u`, one `Prop`), 4 ctors in
     the INTERLEAVED order base, step, base, step; 2 base + 2 step; a step
     ctor with fields both before and after the recursive one; `Prop`
     fields in both a base chain and a step chain.  `s0` and `s1` are given
     identical telescopes on purpose — that is what makes the mutation
     check at the foot of the file possible.

For each target: the real inductive is declared so Lean mints its recursor;
the model carrier, every constructor and the recursor are defined; the model
recursor is pinned to the real recursor's exact type by an `example`; and
every ι rule is stated as a theorem.  ALL ι RULES HOLD BY `rfl`.

§4 adds the two degenerate arities (zero base ctors, zero step ctors) as
compiled witnesses; §5 records the mutation check; §6 the verdict.

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean LinearRec.lean
Expected: 0 errors.
-/

set_option linter.unusedVariables false

universe u v w

-- ══════════════════════════════════════════════════════════════════════════
-- 0. The basis
-- ══════════════════════════════════════════════════════════════════════════

/-- Church truth. -/
def CTrue : Prop := ∀ p : Prop, p → p
def CTrue.triv : CTrue := fun _ h => h

/-- Church falsity: `False` is not in the basis. -/
def CFalse : Prop := ∀ p : Prop, p

set_option bootstrap.inductiveCheckResultingUniverse false in
/-- The Prop-lift: the one member of the basis that leaves `Prop`. -/
inductive PULiftP (p : Prop) : Sort u
  | up : p → PULiftP p

noncomputable def PULiftP.down {p : Prop} (t : PULiftP.{u} p) : p :=
  @PULiftP.rec p (fun _ => p) (fun h => h) t

/-- Structure eta holds for `PULiftP` DEFINITIONALLY: it is a
    single-constructor, index-free, non-recursive inductive, so the kernel's
    eta-for-structures fires even though it is a large lift. -/
theorem PULiftP.eta {p : Prop} (t : PULiftP.{u} p) : t = PULiftP.up (PULiftP.down t) := rfl

/-- The pad: a chain terminator at an arbitrary level. -/
def Pad : Sort u := PULiftP.{u} CTrue
def Pad.pt : Pad.{u} := PULiftP.up CTrue.triv

/-- The pad is a DEFINITIONAL singleton at every level `u` (including 0):
    structure eta collapses `x` onto `.up (down x)` and proof irrelevance
    collapses `down x` onto `CTrue.triv`.  This is why every ι rule below
    that lands on a pad is `rfl` with no transport. -/
theorem Pad.canonical (x : Pad.{u}) : x = Pad.pt := rfl

/-- The empty fibre, used beyond the tag count of each tag tower. -/
def EmptyF : Sort u := PULiftP.{u} CFalse

/-- Large elimination out of Church-False: `h (0 = 1)` gives a numeral
    equality, and `Nat.rec` builds the `Sort w` family to transport along. -/
noncomputable def CFalse.elim {C : Sort w} (h : CFalse) : C :=
  @Eq.rec Nat 0
    (fun n _ => @Nat.rec (fun _ => Sort w) (PULiftP.{w} CTrue) (fun _ _ => C) n)
    (PULiftP.up CTrue.triv) 1 (h (0 = 1))

noncomputable def EmptyF.elim {C : Sort w} (x : EmptyF.{v}) : C :=
  CFalse.elim (PULiftP.down x)

noncomputable section

-- ══════════════════════════════════════════════════════════════════════════
-- 1. TARGET 1 — List α : Type u
--    1 parameter; base ctors: nil (0 fields); step ctors: cons (α, then the
--    recursive field LAST).  Export ctor index → tower/tag:
--      0 nil  → (base, 0)      1 cons → (step, 0)
-- ══════════════════════════════════════════════════════════════════════════

-- The real inductive, so Lean mints the reference recursor.  (Core `List`
-- would do just as well; `#check @List.rec` prints the same shape.)
inductive RList (α : Type u) : Type u
  | nil  : RList α
  | cons : α → RList α → RList α

/-- info: @RList.rec : {α : Type u_2} →
  {motive : RList α → Sort u_1} →
    motive RList.nil → ((a : α) → (a_1 : RList α) → motive a_1 → motive (RList.cons a a_1)) → (t : RList α) → motive t -/
#guard_msgs in #check @RList.rec

namespace L

/-- Base tag tower.  tag 0 = `nil`: zero fields, so the chain is just the
    pad.  Beyond the tag count: the empty fibre. -/
def BFib : Nat → Type u := fun tag =>
  @Nat.rec (fun _ => Type u)
    Pad.{u+1}
    (fun _ _ => EmptyF.{u+1})
    tag

/-- Step tag tower, parametric in the carrier `R = V n` of the shorter
    spine.  tag 0 = `cons`: field `α`, then the recursive field, then pad. -/
def SFib (α : Type u) (R : Type u) : Nat → Type u := fun tag =>
  @Nat.rec (fun _ => Type u)
    (PSigma (fun _ : α => PSigma (fun _ : R => Pad.{u+1})))
    (fun _ _ => EmptyF.{u+1})
    tag

/-- The spine tower. -/
def V (α : Type u) : Nat → Type u := fun n =>
  @Nat.rec (fun _ => Type u)
    (PSigma BFib.{u})
    (fun _ R => PSigma (SFib α R))
    n

/-- The carrier, at Lean's exact `List` level `Type u → Type u`. -/
def List' (α : Type u) : Type u := PSigma (V α)

def List'.nil {α : Type u} : List' α := ⟨0, ⟨0, Pad.pt⟩⟩

def List'.cons {α : Type u} (a : α) (l : List' α) : List' α :=
  ⟨l.1 + 1, ⟨0, ⟨a, ⟨l.2, Pad.pt⟩⟩⟩⟩

/-- The dependent recursor: `PSigma.rec` on the outer pair, `Nat.rec` on the
    spine, `Nat.rec` tag towers inside each level, `PSigma.rec` down each
    chain.  At the step ctor the recursive argument is rebuilt as `⟨n, r⟩`
    (equal to the original by PSigma eta) and the IH is `ih r`. -/
def List'.elim {α : Type u} {motive : List' α → Sort w}
    (h0 : motive List'.nil)
    (h1 : (head : α) → (tail : List' α) → motive tail → motive (List'.cons head tail))
    (t : List' α) : motive t :=
  @PSigma.rec Nat (V α) (fun t => motive t)
    (fun n =>
      @Nat.rec (fun n => (x : V α n) → motive ⟨n, x⟩)
        -- spine 0: the base tower
        (fun x =>
          @PSigma.rec Nat BFib.{u} (fun x => motive ⟨0, x⟩)
            (fun tag =>
              @Nat.rec (fun tag => (y : BFib.{u} tag) → motive ⟨0, ⟨tag, y⟩⟩)
                (fun _pad => h0)                              -- tag 0: nil
                (fun _ _ y => EmptyF.elim y)                    -- beyond the tags
                tag)
            x)
        -- spine n+1: the step tower
        (fun n ih x =>
          @PSigma.rec Nat (SFib α (V α n)) (fun x => motive ⟨n + 1, x⟩)
            (fun tag =>
              @Nat.rec (fun tag => (y : SFib α (V α n) tag) → motive ⟨n + 1, ⟨tag, y⟩⟩)
                -- tag 0: cons
                (fun y =>
                  @PSigma.rec α (fun _ => PSigma (fun _ : V α n => Pad.{u+1}))
                    (fun y => motive ⟨n + 1, ⟨0, y⟩⟩)
                    (fun a rest =>
                      @PSigma.rec (V α n) (fun _ => Pad.{u+1})
                        (fun rest => motive ⟨n + 1, ⟨0, ⟨a, rest⟩⟩⟩)
                        (fun r _pad => h1 a ⟨n, r⟩ (ih r))
                        rest)
                    y)
                (fun _ _ y => EmptyF.elim y)                    -- beyond the tags
                tag)
            x)
        n)
    t

-- the model recursor has RList.rec's exact type:
example : {α : Type u} →
    {motive : List' α → Sort w} →
      motive List'.nil →
        ((a : α) → (a_1 : List' α) → motive a_1 → motive (List'.cons a a_1)) →
          (t : List' α) → motive t := @List'.elim

-- ── ι rules: both `rfl` ────────────────────────────────────────────────────

theorem List'.iota_nil {α : Type u} {motive : List' α → Sort w}
    (h0 : motive List'.nil)
    (h1 : (head : α) → (tail : List' α) → motive tail → motive (List'.cons head tail)) :
    List'.elim h0 h1 List'.nil = h0 := rfl

theorem List'.iota_cons {α : Type u} {motive : List' α → Sort w}
    (h0 : motive List'.nil)
    (h1 : (head : α) → (tail : List' α) → motive tail → motive (List'.cons head tail))
    (a : α) (l : List' α) :
    List'.elim h0 h1 (List'.cons a l) = h1 a l (List'.elim h0 h1 l) := rfl

end L

-- ══════════════════════════════════════════════════════════════════════════
-- 2. TARGET 2 — Lean.Name : Type
--    0 parameters, 3 constructors, recursive field FIRST, two step tags.
--    Export ctor index → tower/tag:
--      0 anonymous → (base, 0)   1 str → (step, 0)   2 num → (step, 1)
--    `String` and `Nat` appear only as opaque payload types.
-- ══════════════════════════════════════════════════════════════════════════

inductive MName
  | anonymous : MName
  | str : MName → String → MName
  | num : MName → Nat → MName

/-- info: @MName.rec : {motive : MName → Sort u_1} →
  motive MName.anonymous →
    ((a : MName) → (a_1 : String) → motive a → motive (a.str a_1)) →
      ((a : MName) → (a_1 : Nat) → motive a → motive (a.num a_1)) → (t : MName) → motive t -/
#guard_msgs in #check @MName.rec

namespace N

/-- Base tag tower: tag 0 = `anonymous`, zero fields. -/
def BFib : Nat → Type := fun tag =>
  @Nat.rec (fun _ => Type)
    Pad.{1}
    (fun _ _ => EmptyF.{1})
    tag

/-- Step tag tower, two tags.  tag 0 = `str`: recursive field FIRST, then
    `String`, then pad.  tag 1 = `num`: recursive field first, then `Nat`. -/
def SFib (R : Type) : Nat → Type := fun tag =>
  @Nat.rec (fun _ => Type)
    (PSigma (fun _ : R => PSigma (fun _ : String => Pad.{1})))
    (fun tag' _ =>
      @Nat.rec (fun _ => Type)
        (PSigma (fun _ : R => PSigma (fun _ : Nat => Pad.{1})))
        (fun _ _ => EmptyF.{1})
        tag')
    tag

def V : Nat → Type := fun n =>
  @Nat.rec (fun _ => Type)
    (PSigma BFib)
    (fun _ R => PSigma (SFib R))
    n

def MName' : Type := PSigma V

def MName'.anonymous : MName' := ⟨0, ⟨0, Pad.pt⟩⟩

def MName'.str (n : MName') (s : String) : MName' :=
  ⟨n.1 + 1, ⟨0, ⟨n.2, ⟨s, Pad.pt⟩⟩⟩⟩

def MName'.num (n : MName') (k : Nat) : MName' :=
  ⟨n.1 + 1, ⟨1, ⟨n.2, ⟨k, Pad.pt⟩⟩⟩⟩

def MName'.elim {motive : MName' → Sort w}
    (ha : motive MName'.anonymous)
    (hs : (a : MName') → (s : String) → motive a → motive (MName'.str a s))
    (hn : (a : MName') → (k : Nat) → motive a → motive (MName'.num a k))
    (t : MName') : motive t :=
  @PSigma.rec Nat V (fun t => motive t)
    (fun n =>
      @Nat.rec (fun n => (x : V n) → motive ⟨n, x⟩)
        -- spine 0: base tower
        (fun x =>
          @PSigma.rec Nat BFib (fun x => motive ⟨0, x⟩)
            (fun tag =>
              @Nat.rec (fun tag => (y : BFib tag) → motive ⟨0, ⟨tag, y⟩⟩)
                (fun _pad => ha)                              -- tag 0: anonymous
                (fun _ _ y => EmptyF.elim y)
                tag)
            x)
        -- spine n+1: step tower with TWO tags
        (fun n ih x =>
          @PSigma.rec Nat (SFib (V n)) (fun x => motive ⟨n + 1, x⟩)
            (fun tag =>
              @Nat.rec (fun tag => (y : SFib (V n) tag) → motive ⟨n + 1, ⟨tag, y⟩⟩)
                -- tag 0: str
                (fun y =>
                  @PSigma.rec (V n) (fun _ => PSigma (fun _ : String => Pad.{1}))
                    (fun y => motive ⟨n + 1, ⟨0, y⟩⟩)
                    (fun r rest =>
                      @PSigma.rec String (fun _ => Pad.{1})
                        (fun rest => motive ⟨n + 1, ⟨0, ⟨r, rest⟩⟩⟩)
                        (fun s _pad => hs ⟨n, r⟩ s (ih r))
                        rest)
                    y)
                (fun tag' _ =>
                  @Nat.rec (fun tag' => (y : SFib (V n) (tag' + 1)) →
                      motive ⟨n + 1, ⟨tag' + 1, y⟩⟩)
                    -- tag 1: num
                    (fun y =>
                      @PSigma.rec (V n) (fun _ => PSigma (fun _ : Nat => Pad.{1}))
                        (fun y => motive ⟨n + 1, ⟨1, y⟩⟩)
                        (fun r rest =>
                          @PSigma.rec Nat (fun _ => Pad.{1})
                            (fun rest => motive ⟨n + 1, ⟨1, ⟨r, rest⟩⟩⟩)
                            (fun k _pad => hn ⟨n, r⟩ k (ih r))
                            rest)
                        y)
                    (fun _ _ y => EmptyF.elim y)                -- beyond the tags
                    tag')
                tag)
            x)
        n)
    t

-- the model recursor has MName.rec's exact type:
example : {motive : MName' → Sort w} →
    motive MName'.anonymous →
      ((a : MName') → (a_1 : String) → motive a → motive (MName'.str a a_1)) →
        ((a : MName') → (a_1 : Nat) → motive a → motive (MName'.num a a_1)) →
          (t : MName') → motive t := @MName'.elim

-- ── ι rules: all three `rfl` ───────────────────────────────────────────────

theorem MName'.iota_anonymous {motive : MName' → Sort w}
    (ha : motive MName'.anonymous)
    (hs : (a : MName') → (s : String) → motive a → motive (MName'.str a s))
    (hn : (a : MName') → (k : Nat) → motive a → motive (MName'.num a k)) :
    MName'.elim ha hs hn MName'.anonymous = ha := rfl

theorem MName'.iota_str {motive : MName' → Sort w}
    (ha : motive MName'.anonymous)
    (hs : (a : MName') → (s : String) → motive a → motive (MName'.str a s))
    (hn : (a : MName') → (k : Nat) → motive a → motive (MName'.num a k))
    (a : MName') (s : String) :
    MName'.elim ha hs hn (MName'.str a s) = hs a s (MName'.elim ha hs hn a) := rfl

theorem MName'.iota_num {motive : MName' → Sort w}
    (ha : motive MName'.anonymous)
    (hs : (a : MName') → (s : String) → motive a → motive (MName'.str a s))
    (hn : (a : MName') → (k : Nat) → motive a → motive (MName'.num a k))
    (a : MName') (k : Nat) :
    MName'.elim ha hs hn (MName'.num a k) = hn a k (MName'.elim ha hs hn a) := rfl

end N

-- ══════════════════════════════════════════════════════════════════════════
-- 3. TARGET 3 — Tri α p : Type u
--    2 parameters (`α : Type u`, `p : Prop`), 4 constructors INTERLEAVED as
--    base, step, base, step.  Export ctor index → tower/tag:
--      0 b0 → (base, 0)   1 s0 → (step, 0)   2 b1 → (base, 1)   3 s1 → (step, 1)
--    This is the mapping the generator must compute; the other two targets
--    cannot distinguish it from "all bases first".
--
--    b0 has ZERO fields (pad-only base chain).
--    b1 has a SINGLE `Prop` field — its chain is `Σ'(_ : p), Pad.{u+1}`;
--      without the terminating pad the chain would be `Sort 0` and could
--      not inhabit a `Type u` fibre.  This is repair R1.
--    s0 has fields BOTH BEFORE (α) and AFTER (p : Prop) the recursive one.
--    s1 has the SAME telescope as s0 on purpose — see the mutation check.
-- ══════════════════════════════════════════════════════════════════════════

inductive Tri (α : Type u) (p : Prop) : Type u
  | b0 : Tri α p
  | s0 : α → Tri α p → p → Tri α p
  | b1 : p → Tri α p
  | s1 : α → Tri α p → p → Tri α p

/-- info: @Tri.rec : {α : Type u_2} →
  {p : Prop} →
    {motive : Tri α p → Sort u_1} →
      motive Tri.b0 →
        ((a : α) → (a_1 : Tri α p) → (a_2 : p) → motive a_1 → motive (Tri.s0 a a_1 a_2)) →
          ((a : p) → motive (Tri.b1 a)) →
            ((a : α) → (a_1 : Tri α p) → (a_2 : p) → motive a_1 → motive (Tri.s1 a a_1 a_2)) → (t : Tri α p) → motive t -/
#guard_msgs in #check @Tri.rec

namespace R

/-- Base tag tower, TWO tags.  tag 0 = `b0` (0 fields), tag 1 = `b1`
    (one `Prop` field). -/
def BFib (p : Prop) : Nat → Type u := fun tag =>
  @Nat.rec (fun _ => Type u)
    Pad.{u+1}
    (fun tag' _ =>
      @Nat.rec (fun _ => Type u)
        (PSigma (fun _ : p => Pad.{u+1}))
        (fun _ _ => EmptyF.{u+1})
        tag')
    tag

/-- Step tag tower, TWO tags.  Both chains are `α`, then the recursive
    field, then `p`, then pad. -/
def SFib (α : Type u) (p : Prop) (R : Type u) : Nat → Type u := fun tag =>
  @Nat.rec (fun _ => Type u)
    (PSigma (fun _ : α => PSigma (fun _ : R => PSigma (fun _ : p => Pad.{u+1}))))
    (fun tag' _ =>
      @Nat.rec (fun _ => Type u)
        (PSigma (fun _ : α => PSigma (fun _ : R => PSigma (fun _ : p => Pad.{u+1}))))
        (fun _ _ => EmptyF.{u+1})
        tag')
    tag

def V (α : Type u) (p : Prop) : Nat → Type u := fun n =>
  @Nat.rec (fun _ => Type u)
    (PSigma (BFib.{u} p))
    (fun _ Rc => PSigma (SFib α p Rc))
    n

def Tri' (α : Type u) (p : Prop) : Type u := PSigma (V α p)

def Tri'.b0 {α : Type u} {p : Prop} : Tri' α p := ⟨0, ⟨0, Pad.pt⟩⟩

def Tri'.s0 {α : Type u} {p : Prop} (a : α) (r : Tri' α p) (h : p) : Tri' α p :=
  ⟨r.1 + 1, ⟨0, ⟨a, ⟨r.2, ⟨h, Pad.pt⟩⟩⟩⟩⟩

def Tri'.b1 {α : Type u} {p : Prop} (h : p) : Tri' α p := ⟨0, ⟨1, ⟨h, Pad.pt⟩⟩⟩

def Tri'.s1 {α : Type u} {p : Prop} (a : α) (r : Tri' α p) (h : p) : Tri' α p :=
  ⟨r.1 + 1, ⟨1, ⟨a, ⟨r.2, ⟨h, Pad.pt⟩⟩⟩⟩⟩

def Tri'.elim {α : Type u} {p : Prop} {motive : Tri' α p → Sort w}
    (hb0 : motive Tri'.b0)
    (hs0 : (a : α) → (r : Tri' α p) → (h : p) → motive r → motive (Tri'.s0 a r h))
    (hb1 : (h : p) → motive (Tri'.b1 h))
    (hs1 : (a : α) → (r : Tri' α p) → (h : p) → motive r → motive (Tri'.s1 a r h))
    (t : Tri' α p) : motive t :=
  @PSigma.rec Nat (V α p) (fun t => motive t)
    (fun n =>
      @Nat.rec (fun n => (x : V α p n) → motive ⟨n, x⟩)
        -- spine 0: base tower with TWO tags
        (fun x =>
          @PSigma.rec Nat (BFib.{u} p) (fun x => motive ⟨0, x⟩)
            (fun tag =>
              @Nat.rec (fun tag => (y : BFib.{u} p tag) → motive ⟨0, ⟨tag, y⟩⟩)
                (fun _pad => hb0)                             -- tag 0: b0
                (fun tag' _ =>
                  @Nat.rec (fun tag' => (y : BFib.{u} p (tag' + 1)) →
                      motive ⟨0, ⟨tag' + 1, y⟩⟩)
                    -- tag 1: b1
                    (fun y =>
                      @PSigma.rec p (fun _ => Pad.{u+1})
                        (fun y => motive ⟨0, ⟨1, y⟩⟩)
                        (fun h _pad => hb1 h)
                        y)
                    (fun _ _ y => EmptyF.elim y)                -- beyond the tags
                    tag')
                tag)
            x)
        -- spine n+1: step tower with TWO tags
        (fun n ih x =>
          @PSigma.rec Nat (SFib α p (V α p n)) (fun x => motive ⟨n + 1, x⟩)
            (fun tag =>
              @Nat.rec (fun tag => (y : SFib α p (V α p n) tag) →
                  motive ⟨n + 1, ⟨tag, y⟩⟩)
                -- tag 0: s0 — pre field α, recursive field, post field p
                (fun y =>
                  @PSigma.rec α
                    (fun _ => PSigma (fun _ : V α p n => PSigma (fun _ : p => Pad.{u+1})))
                    (fun y => motive ⟨n + 1, ⟨0, y⟩⟩)
                    (fun a rest =>
                      @PSigma.rec (V α p n) (fun _ => PSigma (fun _ : p => Pad.{u+1}))
                        (fun rest => motive ⟨n + 1, ⟨0, ⟨a, rest⟩⟩⟩)
                        (fun r rest' =>
                          @PSigma.rec p (fun _ => Pad.{u+1})
                            (fun rest' => motive ⟨n + 1, ⟨0, ⟨a, ⟨r, rest'⟩⟩⟩⟩)
                            (fun h _pad => hs0 a ⟨n, r⟩ h (ih r))
                            rest')
                        rest)
                    y)
                (fun tag' _ =>
                  @Nat.rec (fun tag' => (y : SFib α p (V α p n) (tag' + 1)) →
                      motive ⟨n + 1, ⟨tag' + 1, y⟩⟩)
                    -- tag 1: s1
                    (fun y =>
                      @PSigma.rec α
                        (fun _ => PSigma (fun _ : V α p n => PSigma (fun _ : p => Pad.{u+1})))
                        (fun y => motive ⟨n + 1, ⟨1, y⟩⟩)
                        (fun a rest =>
                          @PSigma.rec (V α p n) (fun _ => PSigma (fun _ : p => Pad.{u+1}))
                            (fun rest => motive ⟨n + 1, ⟨1, ⟨a, rest⟩⟩⟩)
                            (fun r rest' =>
                              @PSigma.rec p (fun _ => Pad.{u+1})
                                (fun rest' => motive ⟨n + 1, ⟨1, ⟨a, ⟨r, rest'⟩⟩⟩⟩)
                                (fun h _pad => hs1 a ⟨n, r⟩ h (ih r))
                                rest')
                            rest)
                        y)
                    (fun _ _ y => EmptyF.elim y)                -- beyond the tags
                    tag')
                tag)
            x)
        n)
    t

-- the model recursor has Tri.rec's exact type:
example : {α : Type u} →
    {p : Prop} →
      {motive : Tri' α p → Sort w} →
        motive Tri'.b0 →
          ((a : α) → (a_1 : Tri' α p) → (a_2 : p) → motive a_1 → motive (Tri'.s0 a a_1 a_2)) →
            ((a : p) → motive (Tri'.b1 a)) →
              ((a : α) → (a_1 : Tri' α p) → (a_2 : p) → motive a_1 →
                  motive (Tri'.s1 a a_1 a_2)) →
                (t : Tri' α p) → motive t := @Tri'.elim

-- ── ι rules: all four `rfl` ────────────────────────────────────────────────

section
variable {α : Type u} {p : Prop} {motive : Tri' α p → Sort w}
  (hb0 : motive Tri'.b0)
  (hs0 : (a : α) → (r : Tri' α p) → (h : p) → motive r → motive (Tri'.s0 a r h))
  (hb1 : (h : p) → motive (Tri'.b1 h))
  (hs1 : (a : α) → (r : Tri' α p) → (h : p) → motive r → motive (Tri'.s1 a r h))

theorem Tri'.iota_b0 : Tri'.elim hb0 hs0 hb1 hs1 Tri'.b0 = hb0 := rfl

theorem Tri'.iota_s0 (a : α) (r : Tri' α p) (h : p) :
    Tri'.elim hb0 hs0 hb1 hs1 (Tri'.s0 a r h)
      = hs0 a r h (Tri'.elim hb0 hs0 hb1 hs1 r) := rfl

theorem Tri'.iota_b1 (h : p) : Tri'.elim hb0 hs0 hb1 hs1 (Tri'.b1 h) = hb1 h := rfl

theorem Tri'.iota_s1 (a : α) (r : Tri' α p) (h : p) :
    Tri'.elim hb0 hs0 hb1 hs1 (Tri'.s1 a r h)
      = hs1 a r h (Tri'.elim hb0 hs0 hb1 hs1 r) := rfl

end

end R

end -- noncomputable section

-- ══════════════════════════════════════════════════════════════════════════
-- 4. DEGENERATE ARITIES — the two boundary cases of the base/step split,
--    compiled rather than argued.
--
--    Repair R3, forced here: a tag tower with ZERO real tags must be emitted
--    as the CONSTANT family `fun _ => EmptyF.{ℓ}`, not as a `Nat.rec` whose
--    two branches both return `EmptyF`.  With the `Nat.rec` form, `Fib tag`
--    is stuck on the bound tag variable inside `elim` and `EmptyF.elim y`
--    fails to elaborate ("`y` has type `BFib tag` but is expected to have
--    type `EmptyF`").  With ≥ 1 real tag the `Nat.rec` form is required, so
--    the generator needs both shapes.
-- ══════════════════════════════════════════════════════════════════════════

noncomputable section

-- ── 4a. ZERO BASE CONSTRUCTORS: the carrier is empty, and that is correct ──

inductive Z | s : Z → Z

/-- info: @Z.rec : {motive : Z → Sort u_1} → ((a : Z) → motive a → motive a.s) → (t : Z) → motive t -/
#guard_msgs in #check @Z.rec

namespace ZeroBase

def BFib : Nat → Type := fun _ => EmptyF.{1}            -- zero real tags (R3)

def SFib (R : Type) : Nat → Type := fun tag =>
  @Nat.rec (fun _ => Type) (PSigma (fun _ : R => Pad.{1})) (fun _ _ => EmptyF.{1}) tag

def V : Nat → Type := fun n =>
  @Nat.rec (fun _ => Type) (PSigma BFib) (fun _ R => PSigma (SFib R)) n

def Z' : Type := PSigma V

def Z'.s (r : Z') : Z' := ⟨r.1 + 1, ⟨0, ⟨r.2, Pad.pt⟩⟩⟩

def Z'.elim {motive : Z' → Sort w} (hs : (a : Z') → motive a → motive (Z'.s a))
    (t : Z') : motive t :=
  @PSigma.rec Nat V (fun t => motive t)
    (fun n => @Nat.rec (fun n => (x : V n) → motive ⟨n, x⟩)
      -- spine 0: no base ctor at all — every element of `V 0` is absurd
      (fun x => @PSigma.rec Nat BFib (fun x => motive ⟨0, x⟩)
        (fun tag y => EmptyF.elim y) x)
      (fun n ih x => @PSigma.rec Nat (SFib (V n)) (fun x => motive ⟨n + 1, x⟩)
        (fun tag => @Nat.rec (fun tag => (y : SFib (V n) tag) → motive ⟨n + 1, ⟨tag, y⟩⟩)
          (fun y => @PSigma.rec (V n) (fun _ => Pad.{1})
             (fun y => motive ⟨n + 1, ⟨0, y⟩⟩) (fun r _pad => hs ⟨n, r⟩ (ih r)) y)
          (fun _ _ y => EmptyF.elim y) tag) x)
      n) t

example : {motive : Z' → Sort w} → ((a : Z') → motive a → motive (Z'.s a)) →
    (t : Z') → motive t := @Z'.elim

theorem Z'.iota_s {motive : Z' → Sort w} (hs : (a : Z') → motive a → motive (Z'.s a)) (r : Z') :
    Z'.elim hs (Z'.s r) = hs r (Z'.elim hs r) := rfl

end ZeroBase

-- ── 4b. ZERO STEP CONSTRUCTORS: sound, but the spine is dead weight ────────

inductive Two | a : Two | b : Nat → Two

/--
info: @Two.rec : {motive : Two → Sort u_1} → motive Two.a → ((a : Nat) → motive (Two.b a)) → (t : Two) → motive t
-/
#guard_msgs in #check @Two.rec

namespace ZeroStep

def BFib : Nat → Type := fun tag =>
  @Nat.rec (fun _ => Type) Pad.{1}
    (fun tag' _ => @Nat.rec (fun _ => Type) (PSigma (fun _ : Nat => Pad.{1}))
       (fun _ _ => EmptyF.{1}) tag') tag

def SFib (R : Type) : Nat → Type := fun _ => EmptyF.{1}   -- zero real tags (R3)

def V : Nat → Type := fun n =>
  @Nat.rec (fun _ => Type) (PSigma BFib) (fun _ R => PSigma (SFib R)) n

def Two' : Type := PSigma V

def Two'.a : Two' := ⟨0, ⟨0, Pad.pt⟩⟩
def Two'.b (k : Nat) : Two' := ⟨0, ⟨1, ⟨k, Pad.pt⟩⟩⟩

def Two'.elim {motive : Two' → Sort w} (ha : motive Two'.a)
    (hb : (k : Nat) → motive (Two'.b k)) (t : Two') : motive t :=
  @PSigma.rec Nat V (fun t => motive t)
    (fun n => @Nat.rec (fun n => (x : V n) → motive ⟨n, x⟩)
      (fun x => @PSigma.rec Nat BFib (fun x => motive ⟨0, x⟩)
        (fun tag => @Nat.rec (fun tag => (y : BFib tag) → motive ⟨0, ⟨tag, y⟩⟩)
          (fun _pad => ha)
          (fun tag' _ => @Nat.rec (fun tag' => (y : BFib (tag' + 1)) → motive ⟨0, ⟨tag' + 1, y⟩⟩)
            (fun y => @PSigma.rec Nat (fun _ => Pad.{1})
               (fun y => motive ⟨0, ⟨1, y⟩⟩) (fun k _pad => hb k) y)
            (fun _ _ y => EmptyF.elim y) tag') tag) x)
      -- spine n+1: no step ctor at all — every longer spine level is absurd
      (fun n ih x => @PSigma.rec Nat (SFib (V n)) (fun x => motive ⟨n + 1, x⟩)
        (fun tag y => EmptyF.elim y) x)
      n) t

example : {motive : Two' → Sort w} → motive Two'.a → ((k : Nat) → motive (Two'.b k)) →
    (t : Two') → motive t := @Two'.elim

theorem Two'.iota_a {motive : Two' → Sort w} (ha : motive Two'.a)
    (hb : (k : Nat) → motive (Two'.b k)) : Two'.elim ha hb Two'.a = ha := rfl

theorem Two'.iota_b {motive : Two' → Sort w} (ha : motive Two'.a)
    (hb : (k : Nat) → motive (Two'.b k)) (k : Nat) :
    Two'.elim ha hb (Two'.b k) = hb k := rfl

end ZeroStep

end -- noncomputable section

-- ══════════════════════════════════════════════════════════════════════════
-- 5. Axiom audit — no funext, no choice, no propext, nothing.
-- ══════════════════════════════════════════════════════════════════════════

/-- info: 'CFalse.elim' does not depend on any axioms -/
#guard_msgs in #print axioms CFalse.elim
/-- info: 'L.List'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms L.List'.elim
/-- info: 'N.MName'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms N.MName'.elim
/-- info: 'R.Tri'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms R.Tri'.elim

-- and the ι rules themselves, which is where a hidden `funext` would show up:
/-- info: 'L.List'.iota_cons' does not depend on any axioms -/
#guard_msgs in #print axioms L.List'.iota_cons
/-- info: 'N.MName'.iota_num' does not depend on any axioms -/
#guard_msgs in #print axioms N.MName'.iota_num
/-- info: 'R.Tri'.iota_s1' does not depend on any axioms -/
#guard_msgs in #print axioms R.Tri'.iota_s1
/-- info: 'Pad.canonical' does not depend on any axioms -/
#guard_msgs in #print axioms Pad.canonical
/-- info: 'ZeroBase.Z'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms ZeroBase.Z'.elim
/-- info: 'ZeroStep.Two'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms ZeroStep.Two'.elim

-- ══════════════════════════════════════════════════════════════════════════
-- 5. MUTATION CHECK
--
-- Four mutations were run against §3 (all reverted; the file above is the
-- WORKING state).  Every one of them is a tag-assignment or base/step-split
-- break of exactly the kind the generator can make.
--
-- ── MUTATION B — the one that isolates a stated ι rule ─────────────────────
--   `Tri'.s1` is given `Tri'.s0`'s step tag (an off-by-one in the tag
--   counter), and the step tower correspondingly loses its second tag:
--       def Tri'.s1 … := ⟨r.1 + 1, ⟨0, …⟩⟩                 -- was ⟨1, …⟩
--       def SFib …   := Nat.rec  chain  (fun _ _ => EmptyF) tag   -- one tag
--       Tri'.elim's step tower keeps only the tag-0 arm; `hs1` is unused.
--   This is type-correct precisely BECAUSE `s0` and `s1` were given
--   identical telescopes: `Tri'.s1 a r h` and `Tri'.s0 a r h` become DEFEQ
--   model terms, so `motive (Tri'.s1 …)` and `motive (Tri'.s0 …)` are
--   convertible and nothing in any TYPE notices.
--   Measured result:
--     * `Tri'.elim`                                  — GREEN
--     * `example : … := @Tri'.elim` (type ascription) — GREEN
--     * `Tri'.iota_b0`, `Tri'.iota_s0`, `Tri'.iota_b1` — GREEN (`rfl`)
--     * `Tri'.iota_s1`                               — RED, the only red:
--         "Not a definitional equality: the left-hand side
--            elim hb0 hs0 hb1 hs1 (s1 a r h)
--          is not definitionally equal to the right-hand side
--            hs1 a r h (elim hb0 hs0 hb1 hs1 r)"
--       because the left side now reduces through the tag-0 arm to
--       `hs0 a r h (…)`.
--   So the stated ι rule catches what the type ascription cannot.
--
-- ── MUTATIONS A, C, D — caught EARLIER, at `Tri'.elim` itself ──────────────
--   A. `Tri'.s1` given tag 0 but the tower and `elim` left alone: the tag-1
--      handler `hs1 a ⟨n,r⟩ h (ih r)` no longer typechecks
--      ("has type `motive (s1 a ⟨n,r⟩ h)` but is expected to have type
--        … motive ⟨n+1, ⟨1, …⟩⟩").  `iota_s1` is red as a consequence.
--   C. the INJECTIVE swap (s0 ↦ tag 1, s1 ↦ tag 0), `elim` unchanged: BOTH
--      step handlers fail to typecheck, and `iota_s0`/`iota_s1` go red too.
--   D. base/step split broken (`b1` moved to spine level 1): the chain type
--      no longer matches at all ("`h` has type `p` … but is expected to have
--      type `α`"), plus the `hb1` handler and `iota_b1` go red.
--
--   The pattern: because `motive` is applied to the model term itself, every
--   INJECTIVE tag permutation and every base/step misassignment is pinned by
--   TYPING ALONE — it cannot reach the ι rules without first breaking
--   `elim`.  The bugs that survive elaboration are exactly the NON-INJECTIVE
--   ones (two constructors sharing a tower slot), and those are exactly what
--   the ι theorems catch.  Stating the ι rules is therefore NOT redundant
--   with the type ascription — but note that this only works if some pair of
--   constructors has convertible telescopes; that is why `Tri'.s0`/`Tri'.s1`
--   were deliberately given the same one.
-- ══════════════════════════════════════════════════════════════════════════

-- ══════════════════════════════════════════════════════════════════════════
-- 6. GENERALISATION VERDICT
--
-- UNIFORM IN (verified by the three targets above):
--   * parameter count and kind — 1 (`List'`), 0 (`MName'`), 2 (`Tri'`,
--     mixing a `Type u` and a `Prop` parameter).  Parameters are simply
--     carried as arguments of BFib/SFib/V; they never enter the recursion.
--   * constructor count — 1+1, 1+2, 2+2.
--   * constructor ORDER — `Tri'` interleaves base, step, base, step and the
--     export index → (tower, tag) map (0→B0, 1→S0, 2→B1, 3→S1) is produced
--     by counting bases and steps independently in declaration order.
--   * field count per constructor — 0 (`b0`, `nil`), 1 (`b1`), 2 (`cons`,
--     `str`, `num`), 3 (`s0`, `s1`); the terminating pad (repair R1) makes
--     k = 0 need no special case.
--   * recursive-field POSITION — last (`cons`), first (`str`, `num`),
--     middle with fields before and after (`s0`, `s1`).
--   * field types and their levels — `α : Type u`, `String`, `Nat`,
--     `p : Prop`.  A chain of only `Prop` fields (`b1`) still lands in
--     `Type u` because of the pad.
--   * level polymorphism — `α : Type u` and `motive : … → Sort w` are
--     independent universe parameters throughout; the carrier sits at
--     Lean's own level for each target (`Type u`, `Type`, `Type u`).
--   * ALL ι rules are `rfl` in every case, and no axiom (in particular no
--     `funext`) is consumed.
--
-- NOT UNIFORM IN / WHERE IT BREAKS:
--   (a) ZERO BASE CONSTRUCTORS — COMPILED in §4a (`Z | s : Z → Z`).  The
--       schema still works: `V 0 = Σ'(tag : Nat), EmptyF.{ℓ}`, the spine-0
--       branch of `elim` is `fun x => PSigma.rec (fun tag y => EmptyF.elim y) x`,
--       the recursor has `Z.rec`'s exact type and the single ι rule is `rfl`.
--       The carrier is EMPTY, which is correct — an inductive with no base
--       constructor has no closed terms — and it is still a legitimate
--       never-zero-sorted (`Type 0`) empty type, inhabited-refuting only via
--       `CFalse.elim`.  The ONE thing the generator must get right is repair
--       R3: with zero real tags the tower must be the CONSTANT family
--       `fun _ => EmptyF.{ℓ}`.  Emitting the `Nat.rec` shape instead leaves
--       `BFib tag` stuck on the bound tag variable and `elim` fails to
--       elaborate (measured).  So the tower emitter needs two shapes:
--       constant for 0 tags, `Nat.rec` nest for ≥ 1.
--   (b) ZERO STEP CONSTRUCTORS — COMPILED in §4b (`Two | a | b : Nat → Two`).
--       Sound: recursor at the exact type, both ι rules `rfl`, no axioms,
--       with `SFib := fun _ => EmptyF.{ℓ}` again by R3.  But the spine
--       `Nat.rec` still has a successor branch, so `V (n+1)` is empty for
--       every n and the carrier is a `PSigma` over all of `Nat` of which
--       only level 0 is inhabited — REDUNDANT.  A non-recursive inductive
--       should be emitted by the plain tag-sum arm (`PSum'` in
--       TypeRoutes.lean), i.e. `Σ'(tag : Nat), Chain_tag` with no spine at
--       all.  The linear-rec arm should detect "no step ctors" and delegate.
--   (c) TWO RECURSIVE FIELDS IN ONE CONSTRUCTOR.  The schema genuinely
--       cannot express it: the spine is a single `Nat` and the constructor
--       rule `⟨r.1 + 1, …⟩` has exactly one predecessor to take, so a
--       binary constructor would have to place two sub-terms of levels
--       `V n₁` and `V n₂` into one fibre `V n` — impossible unless the
--       spine is generalised from `Nat` to a tree (which is the very
--       inductive one is trying to build).
--
--   Two further boundaries, outside the three questions:
--   (d) NESTED / UNDER-BINDER recursion (`c : (Nat → T) → T`) is out of
--       scope for the same reason as (c): the recursive occurrence has no
--       single spine predecessor.
--   (e) INDICES.  All three targets are index-free.  An indexed family
--       would need the fibre towers to be indexed as well and the ι rules
--       would acquire transports; nothing here tests that.
-- ══════════════════════════════════════════════════════════════════════════
