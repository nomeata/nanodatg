/-
PropArms.lean — generator prototypes for three `modelgen` arms, written the
way the generator will emit them: explicit recursor applications, no tactics,
no `match`, and nothing from core beyond the declared basis.

Basis used here: Π, impredicative `Prop`, `Eq`, `PSigma`, `Nat`, and the
Prop-lift primitive

    inductive PULiftP (p : Prop) : Sort u | up : p → PULiftP p

Result: NEITHER arm here consumes `PULiftP` (both resultant sorts are literal
`Prop`, so the Church encoding is already at the right sort) and neither
consumes `Acc` (neither declaration is recursive at a large-eliminating sort).
`PULiftP` is declared below only to record the basis. `False`/`True`/`And` are
Church: `CFalse`, `CTrue`, `CAnd`; no `Exists` is needed anywhere (see the
verdict block at the end for why the SS class never forces one).

`Nat.le` from core is used *as given data* in arm D/E target 2 — that target
models `Nat.le.below`, whose parameters and indices mention `Nat.le`; `Nat.le`
itself is the thing modelled in target 1, not in target 2. Core inductives also
appear in the `sound`/`complete` adequacy theorems, which are yardsticks, not
part of any construction.

Arms:
  D+E  indexed, recursive, SMALL-eliminating `Prop`  (INDUCTIVE-BASIS §3.1)
       target 1: `Nat.le`            → `Le'`
       target 2: `Nat.le.below`      → `Below'`
  F    indexed, non-recursive, SUBSINGLETON `Prop`   (INDUCTIVE-BASIS §3.2,
       degenerate `r := ⊥` case)
       target 3: `HEq`               → `HEq'`
       target 4: `Tag`  (SS + a genuine `Prop` field)        → `Tag'`
       target 5: `Mix2` (SS + an index-variable field that the front end
                 cannot promote to a parameter, plus a `Prop` field depending
                 on it)                                      → `Mix2'`

Every model is checked against the *real* recursor's verbatim type by an
`example : <shape> := @Model.elim` line, every ι rule is a theorem, and each
model is shown equivalent to the declaration it models (`sound`/`complete`).

Run:
  T=~/.elan/toolchains/leanprover--lean4---v4.29.1
  env -u LEAN_PATH LEAN_SYSROOT=$T $T/bin/lean PropArms.lean
Expected: 0 errors.
-/
universe u v w

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PULiftP (p : Prop) : Sort u
  | up : p → PULiftP p

/-- Church `False`, `True`, `And`. No core inductive is consumed. -/
def CFalse : Prop := ∀ p : Prop, p
def CTrue : Prop := ∀ p : Prop, p → p
def CTrue.triv : CTrue := fun _ h => h
def CAnd (p q : Prop) : Prop := ∀ r : Prop, (p → q → r) → r
def CAnd.intro {p q : Prop} (hp : p) (hq : q) : CAnd p q := fun _ k => k hp hq
def CAnd.left {p q : Prop} (h : CAnd p q) : p := h p (fun hp _ => hp)
def CAnd.right {p q : Prop} (h : CAnd p q) : q := h q (fun _ hq => hq)

-- ═════════════════════════════════════════════════════════════════════════════
-- ARM D+E — indexed, RECURSIVE, SMALL-eliminating `Prop`.
--
-- Class (§3.1): resultant sort literal `Prop`, more than one constructor (or
-- otherwise not subsingleton-shaped), so the kernel gives the recursor a
-- `Prop`-valued motive. Carrier = the impredicative Church encoding with the
-- motive quantified over the whole index telescope; constructors = the folds;
-- recursor = the *strong-induction* fold at the Church pair
-- ("rebuilt element", "proof about it"), exactly `R1'.elim` in `BareU.lean`.
--
-- Because the motive lands in `Prop`, definitional proof irrelevance makes
-- every "which proof of the carrier?" question disappear, and — this is the
-- part worth stating loudly — it makes EVERY ι rule `rfl` for free: the two
-- sides of an ι equation are two proofs of one and the same `Prop`.
-- ═════════════════════════════════════════════════════════════════════════════

-- ─── Target 1: `Nat.le` ──────────────────────────────────────────────────────
-- The real declaration (core):
--   inductive Nat.le (n : Nat) : Nat → Prop
--     | refl : Nat.le n n
--     | step {m} : Nat.le n m → Nat.le n m.succ
-- 1 parameter (`n`), 1 index, 2 constructors, 1 recursive field (last field
-- of ctor 2), and the recursive field's *result* index `m.succ` mentions the
-- constructor's own binder `m`.

/-- Carrier: Church encoding, motive quantified over the index. -/
def Le' (n : Nat) (i : Nat) : Prop :=
  ∀ C : Nat → Prop, C n → (∀ m : Nat, C m → C m.succ) → C i

def Le'.refl {n : Nat} : Le' n n :=
  fun _C c0 _cs => c0

def Le'.step {n : Nat} {m : Nat} (h : Le' n m) : Le' n m.succ :=
  fun C c0 cs => cs m (h C c0 cs)

/--
The dependent recursor at `Nat.le.rec`'s exact shape.

Strong induction: fold at

    Pair i := ∀ D : Prop, (Le' n i → (∀ h : Le' n i, motive i h) → D) → D

the Church pair of a rebuilt carrier element and a proof about *every* carrier
element at that index (the `∀ h` is what proof irrelevance collapses). The
element component is genuinely needed: the `step` minor premise
`∀ {m} (a : Le' n m), motive m a → …` cannot be applied without *some*
`a : Le' n m`, and the plain fold at `motive` alone cannot produce one.
-/
def Le'.elim {n : Nat} {motive : (a : Nat) → Le' n a → Prop}
    (m0 : motive n Le'.refl)
    (ms : ∀ {m : Nat} (a : Le' n m), motive m a → motive m.succ (Le'.step a))
    {a : Nat} (t : Le' n a) : motive a t :=
  let Pair : Nat → Prop :=
    fun i => ∀ D : Prop, (Le' n i → (∀ h : Le' n i, motive i h) → D) → D
  let c0 : Pair n :=
    fun _D k => k Le'.refl (fun _h => m0)
  let cs : ∀ m : Nat, Pair m → Pair m.succ :=
    fun m p _D k =>
      p _D (fun (e : Le' n m) (q : ∀ h : Le' n m, motive m h) =>
        k (Le'.step e) (fun _h => ms e (q e)))
  t Pair c0 cs (motive a t) (fun _e q => q t)

-- The model's recursor has `Nat.le.rec`'s verbatim type (v4.29.1):
--   ∀ {n : Nat} {motive : (a : Nat) → n.le a → Prop},
--     motive n Nat.le.refl →
--     (∀ {m : Nat} (a : n.le m), motive m a → motive m.succ (Nat.le.step a)) →
--     ∀ {a : Nat} (t : n.le a), motive a t
example : ∀ {n : Nat} {motive : (a : Nat) → Le' n a → Prop},
    motive n Le'.refl →
    (∀ {m : Nat} (a : Le' n m), motive m a → motive m.succ (Le'.step a)) →
    ∀ {a : Nat} (t : Le' n a), motive a t := @Le'.elim

-- …and the same sentence with the carrier/constructors swapped back to core's
-- is exactly `Nat.le.rec`, so the two statements differ only in those names:
example : ∀ {n : Nat} {motive : (a : Nat) → Nat.le n a → Prop},
    motive n Nat.le.refl →
    (∀ {m : Nat} (a : Nat.le n m), motive m a → motive m.succ (Nat.le.step a)) →
    ∀ {a : Nat} (t : Nat.le n a), motive a t := @Nat.le.rec

-- Adequacy (NOT part of the construction; uses core `Nat.le` as a yardstick,
-- to show the model is neither over- nor under-inhabited):
theorem Le'.sound {n a : Nat} (t : Le' n a) : Nat.le n a :=
  Le'.elim (motive := fun b (_ : Le' n b) => Nat.le n b)
    Nat.le.refl (fun _x ih => Nat.le.step ih) t

theorem Le'.complete {n a : Nat} (t : Nat.le n a) : Le' n a :=
  Nat.le.rec (motive := fun b (_ : Nat.le n b) => Le' n b)
    Le'.refl (fun _x ih => Le'.step ih) t

/-- ι for `refl`, by `rfl`. It reduces on the nose (the fold hits `c0` and the
    continuation projects the proof component), but even had it not, the two
    sides inhabit the `Prop` `motive n Le'.refl`. -/
theorem Le'.iota_refl {n : Nat} {motive : (a : Nat) → Le' n a → Prop}
    (m0 : motive n Le'.refl)
    (ms : ∀ {m : Nat} (a : Le' n m), motive m a → motive m.succ (Le'.step a)) :
    Le'.elim m0 ms Le'.refl = m0 := rfl

/-- ι for `step`, by `rfl`. Here the two sides do NOT reduce to a common
    normal form — the left side is the pair-fold applied to the projecting
    continuation, the right is `ms` applied to a differently-continued fold —
    but both inhabit the `Prop` `motive m.succ (Le'.step a)`, so definitional
    proof irrelevance closes it. This is the general situation for the whole
    small-eliminating `Prop` class. -/
theorem Le'.iota_step {n : Nat} {motive : (a : Nat) → Le' n a → Prop}
    (m0 : motive n Le'.refl)
    (ms : ∀ {m : Nat} (a : Le' n m), motive m a → motive m.succ (Le'.step a))
    {m : Nat} (a : Le' n m) :
    Le'.elim m0 ms (Le'.step a) = ms a (Le'.elim m0 ms a) := rfl

/-- Diagnostic backing the claim above: in this arm ι is free for a reason that
    has nothing to do with the fold — the carrier is a `Prop`, so any two of its
    inhabitants are definitionally equal, and so are any two inhabitants of the
    `Prop`-valued motive. -/
example {n a : Nat} (t s : Le' n a) : t = s := rfl
example {n a : Nat} {motive : (b : Nat) → Le' n b → Prop} (t : Le' n a)
    (x y : motive a t) : x = y := rfl

-- ─── Target 2: `Nat.le.below` ────────────────────────────────────────────────
-- The real declaration (front-end generated, core):
--   inductive Nat.le.below :
--       {n : Nat} → {motive : (a : Nat) → n.le a → Prop} → {a : Nat} →
--       n.le a → Prop
--   params  = {n : Nat}, {motive : (a : Nat) → n.le a → Prop}   (2, one of
--             them a FUNCTION TYPE whose codomain is the declared sort)
--   indices = {a : Nat}, (t : n.le a)                            (2, the
--             second one a PROOF, and its type mentions the first)
--   ctors:
--     below.refl : below (n:=n) (motive:=motive) Nat.le.refl
--     below.step : ∀ {m} (a : n.le m), below a → motive m a → below a.step
-- 2 constructors; ctor 2 has a RECURSIVE field (`below a`) FOLLOWED BY a
-- non-recursive one (`motive m a`); the recursive field's index expressions
-- (`m`, `a`) and the result's index expression (`Nat.le.step a`) both mention
-- earlier binders of the constructor.

/-- Carrier: the same Church encoding, now with the motive quantified over the
    two-index telescope `(a : Nat) (t : n.le a)`. The non-recursive field
    `motive m x` is just another antecedent of the `step` minor premise, sitting
    *after* the recursive one — the fold does not care about the order. -/
def Below' {n : Nat} (motive : (a : Nat) → n.le a → Prop) :
    {a : Nat} → n.le a → Prop :=
  fun {a} t =>
    ∀ C : (b : Nat) → n.le b → Prop,
      C n Nat.le.refl →
      (∀ (m : Nat) (x : n.le m), C m x → motive m x → C m.succ (Nat.le.step x)) →
      C a t

def Below'.refl {n : Nat} {motive : (a : Nat) → n.le a → Prop} :
    @Below' n motive n Nat.le.refl :=
  fun _C c0 _cs => c0

def Below'.step {n : Nat} {motive : (a : Nat) → n.le a → Prop} {m : Nat}
    (x : n.le m) (ih : @Below' n motive m x) (hm : motive m x) :
    @Below' n motive m.succ (Nat.le.step x) :=
  fun C c0 cs => cs m x (ih C c0 cs) hm

/-- The dependent recursor at `Nat.le.below.rec`'s exact shape. Same strong
    induction as `Le'.elim`; the pair is now indexed by the two-index
    telescope, the second index being a proof. -/
def Below'.elim {n : Nat} {motive : (a : Nat) → n.le a → Prop}
    {motive_1 : {a : Nat} → (t : n.le a) → @Below' n motive a t → Prop}
    (m0 : motive_1 Nat.le.refl Below'.refl)
    (ms : ∀ {m : Nat} (x : n.le m) (ih : @Below' n motive m x) (hm : motive m x),
      motive_1 x ih → motive_1 (Nat.le.step x) (Below'.step x ih hm))
    {a : Nat} {t : n.le a} (t_1 : @Below' n motive a t) : motive_1 t t_1 :=
  let Pair : (b : Nat) → n.le b → Prop :=
    fun b s => ∀ D : Prop,
      (@Below' n motive b s → (∀ h : @Below' n motive b s, motive_1 s h) → D) → D
  let c0 : Pair n Nat.le.refl :=
    fun _D k => k Below'.refl (fun _h => m0)
  let cs : ∀ (m : Nat) (x : n.le m), Pair m x → motive m x →
      Pair m.succ (Nat.le.step x) :=
    fun m x p hm _D k =>
      p _D (fun (e : @Below' n motive m x)
              (q : ∀ h : @Below' n motive m x, motive_1 x h) =>
        k (Below'.step x e hm) (fun _h => ms x e hm (q e)))
  t_1 Pair c0 cs (motive_1 t t_1) (fun _e q => q t_1)

-- The model's recursor has `Nat.le.below.rec`'s verbatim type (v4.29.1):
--   ∀ {n : Nat} {motive : (a : Nat) → n.le a → Prop}
--     {motive_1 : {a : Nat} → (t : n.le a) → Nat.le.below t → Prop},
--     motive_1 Nat.le.refl Nat.le.below.refl →
--     (∀ {m : Nat} (a : n.le m) (ih : Nat.le.below a) (a_ih : motive m a),
--         motive_1 a ih → motive_1 (Nat.le.step a) (Nat.le.below.step a ih a_ih)) →
--     ∀ {a : Nat} {t : n.le a} (t_1 : Nat.le.below t), motive_1 t t_1
example : ∀ {n : Nat} {motive : (a : Nat) → n.le a → Prop}
    {motive_1 : {a : Nat} → (t : n.le a) → @Below' n motive a t → Prop},
    motive_1 Nat.le.refl Below'.refl →
    (∀ {m : Nat} (a : n.le m) (ih : @Below' n motive m a) (a_ih : motive m a),
        motive_1 a ih → motive_1 (Nat.le.step a) (Below'.step a ih a_ih)) →
    ∀ {a : Nat} {t : n.le a} (t_1 : @Below' n motive a t), motive_1 t t_1 :=
  @Below'.elim

-- …and the same sentence over core's `Nat.le.below` is `Nat.le.below.rec`:
example : ∀ {n : Nat} {motive : (a : Nat) → n.le a → Prop}
    {motive_1 : {a : Nat} → (t : n.le a) → @Nat.le.below n motive a t → Prop},
    motive_1 Nat.le.refl Nat.le.below.refl →
    (∀ {m : Nat} (a : n.le m) (ih : @Nat.le.below n motive m a) (a_ih : motive m a),
        motive_1 a ih → motive_1 (Nat.le.step a) (Nat.le.below.step a ih a_ih)) →
    ∀ {a : Nat} {t : n.le a} (t_1 : @Nat.le.below n motive a t), motive_1 t t_1 :=
  @Nat.le.below.rec

-- Adequacy against core's `Nat.le.below` (yardstick, not construction):
theorem Below'.sound {n : Nat} {motive : (a : Nat) → n.le a → Prop}
    {a : Nat} {t : n.le a} (h : @Below' n motive a t) :
    @Nat.le.below n motive a t :=
  Below'.elim
    (motive_1 := fun {b} (s : n.le b) (_ : @Below' n motive b s) =>
      @Nat.le.below n motive b s)
    Nat.le.below.refl
    (fun x _ih hm rec => Nat.le.below.step x rec hm) h

theorem Below'.complete {n : Nat} {motive : (a : Nat) → n.le a → Prop}
    {a : Nat} {t : n.le a} (h : @Nat.le.below n motive a t) :
    @Below' n motive a t :=
  @Nat.le.below.rec n motive
    (fun {b : Nat} (s : n.le b) (_ : @Nat.le.below n motive b s) =>
      @Below' n motive b s)
    Below'.refl
    (fun {_m : Nat} x _ih hm rec => Below'.step x rec hm) a t h

/-- ι for `below.refl`, by `rfl`. -/
theorem Below'.iota_refl {n : Nat} {motive : (a : Nat) → n.le a → Prop}
    {motive_1 : {a : Nat} → (t : n.le a) → @Below' n motive a t → Prop}
    (m0 : motive_1 Nat.le.refl Below'.refl)
    (ms : ∀ {m : Nat} (x : n.le m) (ih : @Below' n motive m x) (hm : motive m x),
      motive_1 x ih → motive_1 (Nat.le.step x) (Below'.step x ih hm)) :
    Below'.elim m0 ms Below'.refl = m0 := rfl

/-- ι for `below.step`, by `rfl` (proof irrelevance, as in `Le'.iota_step`).
    Note the recursive call `Below'.elim m0 ms ih` sits in the *fourth*
    argument slot of `ms`, after the non-recursive `hm` — the generator has to
    thread minor-premise arguments in declaration order while the ih is
    produced from the recursive field only. -/
theorem Below'.iota_step {n : Nat} {motive : (a : Nat) → n.le a → Prop}
    {motive_1 : {a : Nat} → (t : n.le a) → @Below' n motive a t → Prop}
    (m0 : motive_1 Nat.le.refl Below'.refl)
    (ms : ∀ {m : Nat} (x : n.le m) (ih : @Below' n motive m x) (hm : motive m x),
      motive_1 x ih → motive_1 (Nat.le.step x) (Below'.step x ih hm))
    {m : Nat} (x : n.le m) (ih : @Below' n motive m x) (hm : motive m x) :
    Below'.elim m0 ms (Below'.step x ih hm)
      = ms x ih hm (Below'.elim m0 ms ih) := rfl

-- ═════════════════════════════════════════════════════════════════════════════
-- ARM F — indexed, NON-RECURSIVE, SUBSINGLETON `Prop` (large elimination).
--
-- Class (§3.2, degenerate `r := ⊥`): one constructor, every field either a
-- `Prop` or a variable that literally *is* one of the output's index
-- arguments. The kernel then grants a `Sort w` motive.
--
-- Model: pack the whole index telescope with `PSigma` and take the carrier to
-- be a single `Eq` at the packed type (Henry Ford), with the genuine `Prop`
-- fields riding along as Church-`And` conjuncts. The recursor is `Eq.rec` at
-- the packed motive; the `Prop` conjuncts are extracted by SMALL elimination
-- (their target is a `Prop`), and the resulting proof arguments are fixed up
-- by definitional proof irrelevance.
-- ═════════════════════════════════════════════════════════════════════════════

-- ─── Target 3: `HEq` ─────────────────────────────────────────────────────────
-- inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop
--   | refl (a : α) : HEq a a
-- params = 2 ({α : Sort u}, a : α); indices = 2 ({β : Sort u}, b : β);
-- 1 constructor, 0 fields beyond the parameters, 0 recursive fields.

/-- The packed index type: `Σ' (γ : Sort u), γ`, i.e. `Sort u` paired with an
    inhabitant. Lives at `Sort (u+1)`, which does not enter the result. -/
def Pk : Sort (u+1) := PSigma (fun γ : Sort u => γ)

/-- Carrier: one packed-index equation. -/
def HEq' {α : Sort u} (a : α) {β : Sort u} (b : β) : Prop :=
  @Eq Pk.{u} (PSigma.mk α a) (PSigma.mk β b)

def HEq'.refl {α : Sort u} (a : α) : HEq'.{u} a a := rfl

/--
The LARGE dependent recursor, at `HEq.rec`'s exact shape.

`@Eq.rec` at the family `fun y h => motive y.1 y.2 h`. This is the step that
needs **`PSigma` structure eta**: the ascription `h : HEq' a y.2` unfolds to
`@Eq Pk ⟨α,a⟩ ⟨y.1, y.2⟩`, while `h : ⟨α,a⟩ = y`, so the kernel must see
`⟨y.1, y.2⟩ ≡ y`. It does (v4.29.1 has structure eta for `PSigma`), so no
repair is needed.
-/
def HEq'.elim {α : Sort u} {a : α}
    {motive : {β : Sort u} → (b : β) → HEq'.{u} a b → Sort v}
    (m : motive a (HEq'.refl a)) {β : Sort u} {b : β} (t : HEq'.{u} a b) :
    motive b t :=
  @Eq.rec Pk.{u} (PSigma.mk α a)
    (fun (y : Pk.{u}) (h : @Eq Pk.{u} (PSigma.mk α a) y) =>
      @motive (PSigma.fst y) (PSigma.snd y) h)
    m (PSigma.mk β b) t

-- The model's recursor has `HEq.rec`'s verbatim type (v4.29.1):
--   {α : Sort u} → {a : α} →
--     {motive : {β : Sort u} → (b : β) → HEq a b → Sort v} →
--     motive a (HEq.refl a) → {β : Sort u} → {b : β} → (t : HEq a b) → motive b t
example : {α : Sort u} → {a : α} →
    {motive : {β : Sort u} → (b : β) → HEq'.{u} a b → Sort v} →
    motive a (HEq'.refl a) →
    {β : Sort u} → {b : β} → (t : HEq'.{u} a b) → motive b t := @HEq'.elim

-- …and the same sentence over core's `HEq` is `HEq.rec`:
noncomputable example : {α : Sort u} → {a : α} →
    {motive : {β : Sort u} → (b : β) → HEq a b → Sort v} →
    motive a (HEq.refl a) →
    {β : Sort u} → {b : β} → (t : HEq a b) → motive b t := @HEq.rec

/-- The one non-obvious kernel fact this model rests on: `PSigma` structure
    eta. Without it the `Eq.rec` motive above does not typecheck, because the
    ascription of `h : ⟨α,a⟩ = y` to `HEq' a y.2 = (⟨α,a⟩ = ⟨y.1, y.2⟩)`
    needs `⟨y.1, y.2⟩ ≡ y`. v4.29.1 has it, so no repair is needed. -/
example (y : Pk.{u}) : PSigma.mk (PSigma.fst y) (PSigma.snd y) = y := rfl

/-- Generator note: the projections may equally be spelled `@PSigma.rec`, and
    eta still fires — the kernel eta-expands a neutral major premise of a
    structure type before applying the ι rule, so `@PSigma.rec … y` on a
    variable `y` still reduces to `PSigma.fst y`. Emitting `Expr.proj` or
    emitting the recursor are both fine here. -/
noncomputable def rfst (y : Pk.{u}) : Sort u :=
  @PSigma.rec (Sort u) (fun γ => γ) (fun _ => Sort u) (fun a _ => a) y
noncomputable def rsnd (y : Pk.{u}) : rfst y :=
  @PSigma.rec (Sort u) (fun γ => γ) (fun z => rfst z) (fun _ b => b) y
example (y : Pk.{u}) : PSigma.mk (rfst y) (rsnd y) = y := rfl

-- Adequacy against core's `HEq` (yardstick, not construction):
theorem HEq'.sound {α : Sort u} {a : α} {β : Sort u} {b : β}
    (t : HEq'.{u} a b) : HEq a b :=
  HEq'.elim (motive := fun {γ : Sort u} (c : γ) (_ : HEq'.{u} a c) => HEq a c)
    (HEq.refl a) t

theorem HEq'.complete {α : Sort u} {a : α} {β : Sort u} {b : β}
    (t : HEq a b) : HEq'.{u} a b :=
  HEq.rec (motive := fun {γ : Sort u} (c : γ) (_ : HEq a c) => HEq'.{u} a c)
    (HEq'.refl a) t

/-- ι by `rfl`: at the constructor the transport is along `Eq.refl`, and the
    kernel's ι rule for `Eq.rec` erases it. (Note this is a `Sort v` motive —
    proof irrelevance is NOT available here; the rule is genuinely
    definitional.) -/
theorem HEq'.iota {α : Sort u} {a : α}
    {motive : {β : Sort u} → (b : β) → HEq'.{u} a b → Sort v}
    (m : motive a (HEq'.refl a)) :
    HEq'.elim m (HEq'.refl a) = m := rfl

-- ─── Target 4: arm F generalised — a subsingleton with a genuine `Prop` field ─
-- The representative declaration. Beyond `HEq`'s index-determining data it
-- carries one honest `Prop` field `h : φ`, which is NOT an index. The kernel
-- still grants large elimination (SS rule: every field is a `Prop` or an
-- index variable), but the declaration is NOT K-like (K-likeness needs every
-- field to be an index), so the model must really deliver `φ`.

inductive Tag {α : Sort u} (a : α) (φ : Prop) : {β : Sort u} → β → Prop
  | mk (h : φ) : Tag a φ a

/-- Lean's own recursor for it, pinned. -/
noncomputable example : {α : Sort u} → {a : α} → {φ : Prop} →
    {motive : {β : Sort u} → (b : β) → Tag a φ b → Sort v} →
    ((h : φ) → motive a (Tag.mk h)) →
    {β : Sort u} → {b : β} → (t : Tag a φ b) → motive b t := @Tag.rec

/-- Carrier: packed-index equation, Church-`And`ed with the `Prop` field.
    Generally: `φ_ctor ∧ (packed indices = packed ctor index expressions)`,
    with `φ_ctor` the Church conjunction of all genuine `Prop` fields. -/
def Tag' {α : Sort u} (a : α) (φ : Prop) {β : Sort u} (b : β) : Prop :=
  CAnd φ (@Eq Pk.{u} (PSigma.mk α a) (PSigma.mk β b))

def Tag'.mk {α : Sort u} {a : α} {φ : Prop} (h : φ) : Tag'.{u} a φ a :=
  CAnd.intro h rfl

/--
The LARGE dependent recursor at `Tag.rec`'s exact shape.

Two moving parts, and they are independent:
  * the `Prop` field is recovered by `CAnd.left` — SMALL elimination of a
    `Prop` into a `Prop`, so no large eliminator for `And`/`Exists` is
    consumed;
  * the index telescope is discharged by `@Eq.rec` on the packed equation,
    exactly as for `HEq'`.
The motive family must rebuild a carrier proof at each `y`, which is why
`CAnd.intro (CAnd.left t) h` appears inside it; every mismatch between the
rebuilt proof and the one the caller supplied is closed by definitional proof
irrelevance (the carrier is a `Prop`).
-/
def Tag'.elim {α : Sort u} {a : α} {φ : Prop}
    {motive : {β : Sort u} → (b : β) → Tag'.{u} a φ b → Sort v}
    (m : (h : φ) → motive a (Tag'.mk h))
    {β : Sort u} {b : β} (t : Tag'.{u} a φ b) : motive b t :=
  @Eq.rec Pk.{u} (PSigma.mk α a)
    (fun (y : Pk.{u}) (h : @Eq Pk.{u} (PSigma.mk α a) y) =>
      @motive (PSigma.fst y) (PSigma.snd y) (CAnd.intro (CAnd.left t) h))
    (m (CAnd.left t))
    (PSigma.mk β b) (CAnd.right t)

example : {α : Sort u} → {a : α} → {φ : Prop} →
    {motive : {β : Sort u} → (b : β) → Tag'.{u} a φ b → Sort v} →
    ((h : φ) → motive a (Tag'.mk h)) →
    {β : Sort u} → {b : β} → (t : Tag'.{u} a φ b) → motive b t := @Tag'.elim

-- Adequacy against the declared `Tag` (yardstick, not construction):
theorem Tag'.sound {α : Sort u} {a : α} {φ : Prop} {β : Sort u} {b : β}
    (t : Tag'.{u} a φ b) : Tag a φ b :=
  Tag'.elim (motive := fun {γ : Sort u} (c : γ) (_ : Tag'.{u} a φ c) => Tag a φ c)
    (fun h => Tag.mk h) t

theorem Tag'.complete {α : Sort u} {a : α} {φ : Prop} {β : Sort u} {b : β}
    (t : Tag a φ b) : Tag'.{u} a φ b :=
  Tag.rec (motive := fun {γ : Sort u} (c : γ) (_ : Tag a φ c) => Tag'.{u} a φ c)
    (fun h => Tag'.mk h) t

/-- ι by `rfl`: `CAnd.right (Tag'.mk h)` reduces to `Eq.refl`, the `Eq.rec`
    ι rule fires, and `CAnd.left (Tag'.mk h)` reduces to `h`. Again a
    `Sort v` motive, so this is definitional content, not proof irrelevance. -/
theorem Tag'.iota {α : Sort u} {a : α} {φ : Prop}
    {motive : {β : Sort u} → (b : β) → Tag'.{u} a φ b → Sort v}
    (m : (h : φ) → motive a (Tag'.mk h)) (h : φ) :
    Tag'.elim m (Tag'.mk h) = m h := rfl

-- ─── Target 5: arm F, the case that settles the "do we need ∃?" question ─────
-- `Tag` has only a `Prop` field. The other kind of field the SS rule allows is
-- an *index-variable* field: a fresh variable that literally is one of the
-- output's index arguments. Usually Lean's FRONT END promotes such a field to
-- a parameter and it never reaches the kernel as a field at all (probed: for
--   inductive T3 (p : Nat → Prop) : Nat → Prop | mk (n : Nat) (h : p n) : T3 p n
-- Lean reports "number of parameters: 2, number of indices: 0" and `T3.mk` has
-- one field). Promotion is blocked when the fresh index sits AFTER a
-- non-promotable one, because parameters must be a prefix of the telescope.
-- `Mix2` is exactly that: 3 parameters, 3 indices, 2 fields — one an index
-- variable, one a `Prop` DEPENDING on it — and still large-eliminating.

inductive Mix2 {α : Sort u} (a : α) (p : Nat → Prop) :
    {β : Sort u} → β → Nat → Prop
  | mk (k : Nat) (h : p k) : Mix2 a p a k

/-- Lean's own recursor for it, pinned (note `Sort v` — large elimination). -/
noncomputable example : {α : Sort u} → {a : α} → {p : Nat → Prop} →
    {motive : {β : Sort u} → (b : β) → (k : Nat) → Mix2 a p b k → Sort v} →
    ((k : Nat) → (h : p k) → motive a k (Mix2.mk k h)) →
    {β : Sort u} → {b : β} → {k : Nat} → (t : Mix2 a p b k) → motive b k t :=
  @Mix2.rec

/-- Carrier. The index-variable field `k` is NOT existentially quantified: it
    is *substituted by the index it names*, which is legitimate precisely
    because the SS rule demands the output index be that variable itself. The
    `Prop` field's type `p k` then mentions the index, not a bound variable. -/
def Mix2' {α : Sort u} (a : α) (p : Nat → Prop) {β : Sort u} (b : β) (k : Nat) :
    Prop :=
  CAnd (p k) (@Eq Pk.{u} (PSigma.mk α a) (PSigma.mk β b))

def Mix2'.mk {α : Sort u} {a : α} {p : Nat → Prop} (k : Nat) (h : p k) :
    Mix2'.{u} a p a k :=
  CAnd.intro h rfl

/-- The large dependent recursor at `Mix2.rec`'s exact shape. Same two moving
    parts as `Tag'.elim`; the extra index `k` is simply carried, and the
    minor premise's index-variable argument is supplied *from the index*. -/
def Mix2'.elim {α : Sort u} {a : α} {p : Nat → Prop}
    {motive : {β : Sort u} → (b : β) → (k : Nat) → Mix2'.{u} a p b k → Sort v}
    (m : (k : Nat) → (h : p k) → motive a k (Mix2'.mk k h))
    {β : Sort u} {b : β} {k : Nat} (t : Mix2'.{u} a p b k) : motive b k t :=
  @Eq.rec Pk.{u} (PSigma.mk α a)
    (fun (y : Pk.{u}) (h : @Eq Pk.{u} (PSigma.mk α a) y) =>
      @motive (PSigma.fst y) (PSigma.snd y) k (CAnd.intro (CAnd.left t) h))
    (m k (CAnd.left t))
    (PSigma.mk β b) (CAnd.right t)

example : {α : Sort u} → {a : α} → {p : Nat → Prop} →
    {motive : {β : Sort u} → (b : β) → (k : Nat) → Mix2'.{u} a p b k → Sort v} →
    ((k : Nat) → (h : p k) → motive a k (Mix2'.mk k h)) →
    {β : Sort u} → {b : β} → {k : Nat} → (t : Mix2'.{u} a p b k) → motive b k t :=
  @Mix2'.elim

/-- ι by `rfl`, for the same reason as `Tag'.iota`. -/
theorem Mix2'.iota {α : Sort u} {a : α} {p : Nat → Prop}
    {motive : {β : Sort u} → (b : β) → (k : Nat) → Mix2'.{u} a p b k → Sort v}
    (m : (k : Nat) → (h : p k) → motive a k (Mix2'.mk k h))
    (k : Nat) (h : p k) :
    Mix2'.elim m (Mix2'.mk k h) = m k h := rfl

theorem Mix2'.sound {α : Sort u} {a : α} {p : Nat → Prop} {β : Sort u} {b : β}
    {k : Nat} (t : Mix2'.{u} a p b k) : Mix2 a p b k :=
  Mix2'.elim
    (motive := fun {γ : Sort u} (c : γ) (j : Nat) (_ : Mix2'.{u} a p c j) =>
      Mix2 a p c j)
    (fun j h => Mix2.mk j h) t

theorem Mix2'.complete {α : Sort u} {a : α} {p : Nat → Prop} {β : Sort u} {b : β}
    {k : Nat} (t : Mix2 a p b k) : Mix2'.{u} a p b k :=
  Mix2.rec
    (motive := fun {γ : Sort u} (c : γ) (j : Nat) (_ : Mix2 a p c j) =>
      Mix2'.{u} a p c j)
    (fun j h => Mix2'.mk j h) t

-- ─── Shapes probed and rejected as OUT of arm F (they are arm D+E) ───────────
-- Each of these is admitted by the kernel but gets a `Prop`-valued motive, so
-- the packed-`Eq` model is not even called for.

/-- A ctor arg that is not *literally* an index of the output (`n` vs `n+1`):
    SMALL elimination. Pinned. -/
inductive NotSS1 (p : Nat → Prop) : Nat → Prop
  | mk (n : Nat) (h : p n) : NotSS1 p (n+1)

example : ∀ {p : Nat → Prop} {motive : (a : Nat) → NotSS1 p a → Prop},
    (∀ (n : Nat) (h : p n), motive (n+1) (NotSS1.mk n h)) →
    ∀ {a : Nat} (t : NotSS1 p a), motive a t := @NotSS1.rec

/-- A ctor arg that is neither a `Prop` nor an index: SMALL elimination. -/
inductive NotSS2 : Nat → Prop
  | mk (n : Nat) (k : Nat) : NotSS2 n

example : ∀ {a : Nat} {motive : NotSS2 a → Prop},
    (∀ (k : Nat), motive (NotSS2.mk a k)) →
    ∀ (t : NotSS2 a), motive t := @NotSS2.rec

-- ═════════════════════════════════════════════════════════════════════════════
-- What is uniform, and what is not — read this before writing the generator.
--
-- ARM D+E (small-eliminating `Prop`). Between `Le'` and `Below'` the *whole*
-- construction is one schema; the two differ in almost every shape feature and
-- the terms are still the same:
--   * parameter count             1 vs 2                    — uniform
--   * a parameter at a function type whose codomain is the declared sort
--     (`motive : (a : Nat) → n.le a → Prop`)                — uniform: params
--     are just carried into the Church quantifier's context, never analysed
--   * index count                 1 vs 2                    — uniform: the
--     Church motive `C` takes the whole index telescope, and so does `Pair`
--   * an index that is itself a PROOF whose type mentions an earlier index
--     (`(t : n.le a)`)                                      — uniform
--   * constructor count           2 vs 2 — NOT varied here, so uniformity in
--     the constructor count is argued, not measured. The argument: the count
--     enters only as "one Church premise and one `Pair` premise per
--     constructor", with no cross-constructor interaction; `BareU.lean`'s
--     `T3'`/`R1'` cover 2 and 1.
--   * recursive-field count       1 vs 1; position: LAST field in `Le'.step`
--     but FIRST-of-two in `Below'.step` (recursive field followed by a
--     non-recursive one)                                    — uniform: the
--     minor premise takes the fields in declaration order and the pair-fold
--     supplies `(e, q)` only for recursive slots
--   * the recursive field's and the result's index expressions mention the
--     constructor's earlier binders (`m`, `x`, `Nat.le.step x`) — uniform:
--     they are copied verbatim into the Church premise
--   * ι: `rfl` for every constructor, in both — and for a *cheap* reason:
--     the motive is `Prop`-valued, so both sides of every ι equation are
--     proofs of one `Prop`. `Le'.iota_step` does NOT hold by reduction; it
--     holds by definitional proof irrelevance. The generator therefore never
--     has to reason about whether a fold reduces.
-- NOT uniform in this arm:
--   * LEVEL POLYMORPHISM. Both targets are at literal `Prop`; the carrier is
--     `∀ C : … → Prop, …`, which is only a `Prop` because `Prop` is
--     impredicative. At a maybe-zero `Sort u` the same encoding must be
--     wrapped in `PULiftP` (that is `R1'` in `BareU.lean`), and at a
--     never-zero sort the Church encoding is simply wrong (it would not
--     support large elimination). So this arm is gated on the resultant sort
--     being *literal* `Prop`.
--   * A recursive field UNDER A BINDER (`f : γ → T e`) still works (that is
--     `R1'`), but the pair-fold then needs the element component pointwise;
--     neither target here exercises it.
--   * Non-uniform recursion where a later field's TYPE mentions an earlier
--     recursive field cannot occur (strict positivity forbids it), so the
--     "recursive then non-recursive" order in `below.step` is the worst case
--     and it is handled.
--
-- ARM F (subsingleton `Prop`, large elimination). Uniform in:
--   * index count and index kinds: the whole telescope is packed into one
--     `PSigma` chain and discharged by one `Eq.rec`. `HEq`'s telescope
--     `{β : Sort u} (b : β)` is already the dependent worst case (the second
--     index's TYPE is the first index) and `PSigma` handles it.
--   * parameter count and parameter kinds (`α`, `a`, `φ` are all just
--     context).
--   * LEVEL POLYMORPHISM, both in the declaration's own level `u` and in the
--     eliminating level `v`: `Pk.{u} : Sort (u+1)` is an auxiliary whose level
--     never reaches the result, and `Eq.rec` is level-polymorphic in the
--     motive. This arm IS level-polymorphic, unlike arm D+E.
--   * genuine `Prop` fields: they ride as Church-`And` conjuncts and come out
--     by small elimination (`Tag'`, `Mix2'`).
--   * index-variable fields, INCLUDING when a later `Prop` field's type
--     depends on one (`Mix2`: field `k`, field `h : p k`).
--
-- ANSWER TO THE QUESTION THE EXERCISE WAS SET FOR — no, the packed-`Eq` model
-- never needs a `PSigma`-of-Church-`∃` φ component, and it is the SS rule
-- itself that guarantees this. Every ctor field is (a) a `Prop`, or (b) a
-- variable that literally IS an output index. Case (b) fields are not
-- existentially hidden: they are *determined*, so the model SUBSTITUTES the
-- index for the field (`Mix2'` carries `p k` with `k` the index, not
-- `∃ k, p k ∧ …`). Case (a) fields are `Prop`s, so extracting them is small
-- elimination into a `Prop` and is always available. An existential would be
-- forced only by a field that is neither — and that is exactly the shape the
-- SS rule excludes (`NotSS1`, `NotSS2`, pinned above, both get `Prop`
-- motives). So the schema is
--     carrier(ι) := CAnd φ₁ (CAnd φ₂ … (packed-Eq over the index positions))
-- with φ_i the `Prop` fields after substituting index-variable fields by their
-- indices, and the recursor is one `Eq.rec` plus `CAnd.left` projections.
--   * WATCH OUT (measured, not predicted): Lean's FRONT END usually PROMOTES
--     an index-variable field to a parameter, so it never reaches the stored
--     declaration as a field. `inductive T3 (p : Nat → Prop) : Nat → Prop`
--     with `| mk (n : Nat) (h : p n) : T3 p n` is stored with 2 parameters,
--     0 indices and a 1-field constructor. Promotion is blocked only when the
--     fresh index sits after a non-promotable one (parameters must be a
--     prefix) — that is `Mix2`, 3 params / 3 indices / 2 fields, and it is the
--     only reason case (b) needs handling at all. `modelgen` reads the stored
--     declaration, so it will see case (b) rarely; it must still handle it.
--   * ι: `rfl` in both, by the `Eq.rec` ι rule on a stored `Eq.refl` plus
--     `CAnd` beta. NOT by proof irrelevance — the motive is `Sort v` here.
-- NOT uniform in this arm:
--   * RECURSION. `Tag`/`HEq` have none. A recursive subsingleton (only
--     possible at literal `Prop`, per `SortPolyProbe` F3) needs the
--     `AccPhi` carrier of §3.2, not a bare packed `Eq`; the packed-`Eq` model
--     is the degenerate `r := ⊥` case.
--   * A constructor field that is neither a `Prop` nor an index variable
--     breaks the model — but it also breaks Lean's SS grant, so the arm is
--     correctly gated. Two shapes tried and rejected as out of arm, both
--     pinned above as `NotSS1`/`NotSS2`:
--       `| mk (n : Nat) (h : p n) : T p (n+1)` — `n` is not literally an
--         index of the output, so the kernel gives it SMALL elimination;
--       `| mk (n : Nat) (k : Nat) : T n`      — `k` is neither `Prop` nor
--         index, likewise SMALL.
--     Both belong to arm D+E, not arm F.
--   * K-likeness is a *separate* property: `HEq` is K-like (all fields are
--     indices) and `Tag` is not (the `φ` field is not). The model is the same
--     either way; only Lean's definitional `rec`-on-a-variable reduction
--     differs, and the model never had that anyway (see §6 of
--     INDUCTIVE-BASIS.md).
-- ═════════════════════════════════════════════════════════════════════════════

-- ── Axiom audit ──────────────────────────────────────────────────────────────
/-- info: 'Le'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms Le'.elim
/-- info: 'Below'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms Below'.elim
/-- info: 'HEq'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms HEq'.elim
/-- info: 'Tag'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms Tag'.elim
/-- info: 'Mix2'.elim' does not depend on any axioms -/
#guard_msgs in #print axioms Mix2'.elim
