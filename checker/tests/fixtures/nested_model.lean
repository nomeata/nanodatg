/-
# The **model** of a nested inductive, written out

`nested_iota.lean` states the fourteen ι rules of the nested recursors as `rfl`
theorems and measures that mini's kernel reduces them. That is the *acceptance*
axis, and it is exactly as strong as the primitive `Tree.rec_1` mini installs:
the rule is asserted, transported along an isomorphism nothing checks.

This file is the other half. It contains **no nested declaration at all**. It
builds the specialised block as an ordinary `mutual`, defines `Tree`, its
constructors and *both* of its recursors as ordinary definitions over that
block, and then states the same four ι rules — about the **defined** recursors
— as theorems whose proofs are terms rather than `rfl`. Nothing here is
primitive, nothing is assumed, and every equation is checked.

So the two files together say: mini's `Tree.rec_1` computes (`nested_iota`), and
a `Tree.rec_1` that computes **exists**, over the real `List`, with the real
`List.nil`/`List.cons` as its rules (this file). The second is the statement
that the first is not vacuous.

# The encoding, and the two maps that are not the identity

```text
S0 ≅ Tree            S1 ≅ List Tree
```

`S0` *is* `Tree` — one `def`, definitional. `S1` is **not** `List Tree`: the
container already exists with its own constructors, so the two are related by

```text
pack   : List Tree → S1        by List.rec
unpack : S1 → List Tree        by S1.rec
```

and `nested_roundtrip.lean` is the measurement that neither round trip is
definitional. Both are proved here as theorems, `unpackPack` and `packUnpack`,
each by one induction and one `Eq.rec`.

# Where the price is paid, exactly

Of the four rules:

| rule | cost |
| --- | --- |
| `Tree.rec` on `leaf` | **`rfl`** — the block's own ι rule, unchanged |
| `Tree.rec_1` on `List.nil` | **`rfl`** — `pack List.nil` ι-reduces to `S1.nil`, and `unpackPack List.nil` ι-reduces to `Eq.refl`, so the transport in `treeRec1` disappears |
| `Tree.rec` on `Tree.node` | `transportNode` — the **triangle identity** between the two round trips |
| `Tree.rec_1` on `List.cons` | `transportCons` — the transport pushed through a **stuck `Eq.rec`** |

The two hard ones are *one lemma each*, and each lemma is `Eq.rec` on the round
trip landing at `Eq.refl`. What makes that enough is **proof irrelevance**: the
transport `treeRec`'s `node` minor performs is along `packUnpack (pack a)`,
while the lemma is stated along `congrPack (unpackPack a)`, and those are two
proofs of the same `Prop` — so the kernel identifies them and the triangle
identity never has to be proved as an equation between proofs. Lean 3's
compiler, which had to rewrite the stuck `eq.rec` with a simp set
(`LEAN3-INDUCTIVE-COMPILER.md` §4), paid for this and mini does not.

`transportNode` and `transportCons` are the whole extra cost of nesting on the
evidence axis. There is no third lemma.

# What the evidence axis says about it, measured

`mini --mutual` on this export reads

```text
accept 25 declarations   uncertified: 13 const typings, 4 type typings, 3214 conversions
evidence  pairs=41  typeEv=37  constEv=28
          waiting:stuck-recursor(List.rec)=10
          waiting:stuck-recursor(Eq.rec)=2
          waiting:stuck-recursor(S0._auxCarrier.rec)=1
convs     proved=46457589  gapped=3214
          convGap:stuck-recursor(S0._auxCarrier.rec)=2475
          convGap:stuck-recursor(List.rec)=709
          convGap:stuck-recursor(Eq.rec)=26
```

**Every one of the thirteen missing constant typings is `Gap::StuckRecursor`,
and this file is that variant's first occupant** — instrumented over all 91
corpus exports it minted `0`. The shape that reaches it is the round trip
itself: `unpack (pack l)` at an open `l` is a recursor whose *major premise is
another stuck recursor*, so the major reduces underneath without the outer redex
firing, and the certificate owes a congruence over that reduction which `whnf`
performs acceptance-only and does not thread. Nothing here is owed to
`derived/`, and nothing here is a clause of §6.2.

The run is **expensive**: 46 million conversions, tens of minutes, and it stays
inside a 4 GB `ulimit -v`. No test runs the binary on this fixture; the tests in
`mini/tests/nested.rs` add its declarations through `kernel::add`, which takes
about three seconds.

# What this file is not

It is not what mini installs. `mini/src/nested.rs` installs the **primitive**
recursors Lean exports, because a Lean file may rely on `Tree.rec` reducing
definitionally and this `treeRec` does not (`iotaNode` is a theorem, not a
conversion). This file is the *model* those primitives are to be interpreted
by, and it is written as an export so that the model is checked — by Lean at
export time and by mini on every run — rather than described.

`Nat` is avoided throughout, for the reason `infinitary_branching.lean` gives,
and the motives land in `Type` for the reason `nested_iota.lean` gives: a
`Prop`-valued motive would let proof irrelevance close every equation below
whether or not anything reduced.
-/
prelude

--#export Eq N List S0 S1 Tree treeLeaf pack unpack treeNode
--#export unpackPack packUnpack congrPack congrCons transportNode transportCons
--#export ndMinor csMinor treeRec blockRec1 treeRec1
--#export iotaLeaf iota1Nil iotaNode iota1Cons treeSize

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The payload, so that a motive can land in `Type` without `Nat`. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The container being nested into. It exists **before** the block and has its
    own constructors, which is the whole difficulty. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/- The specialised block — `mini/src/nested.rs`'s `Plan`, written by hand.
   `S0` is `Tree` and `S1` is the *mimic* of `List Tree`. -/
mutual
inductive S0 : Type where
  | leaf : S0
  | node : S1 → S0
inductive S1 : Type where
  | nil : S1
  | cons : S0 → S1 → S1
end

/-- Definitional: one `def`, no map. -/
def Tree : Type := S0

def treeLeaf : Tree := S0.leaf

/-- `List Tree → S1`, by the **real** container's recursor. -/
noncomputable def pack : List Tree → S1 :=
  @List.rec Tree (fun _ => S1) S1.nil (fun h _ ih => S1.cons h ih)

/-- `S1 → List Tree`, by the **block's** recursor at the mimic.

    The motive at `S0` is `fun _ => S0` and its minors rebuild `S0`'s own
    constructors — the identity. That is not padding: a mutual recursor carries
    one motive per member at **one** motive universe, so the unused member needs
    a motive at the same sort as the used one, and `fun _ => S0` is the only
    choice that is inhabited for every block whatever its constructors are. -/
noncomputable def unpack : S1 → List Tree :=
  @S1.rec (fun _ => S0) (fun _ => List Tree)
    S0.leaf
    (fun b _ => S0.node b)
    List.nil
    (fun a _ _ ih2 => List.cons a ih2)

/-- `Tree.node : List Tree → Tree`, at its **declared** type. The packing is
    what makes this a definition rather than a constructor. -/
noncomputable def treeNode (l : List Tree) : Tree := S0.node (pack l)

/-- **The retraction.** Propositional, by induction on the real list. -/
theorem unpackPack : ∀ l : List Tree, Eq (unpack (pack l)) l :=
  @List.rec Tree (fun l => Eq (unpack (pack l)) l)
    (Eq.refl (@List.nil Tree))
    (fun h t ih =>
      @Eq.rec (List Tree) (unpack (pack t))
        (fun x _ => Eq (@List.cons Tree h (unpack (pack t))) (@List.cons Tree h x))
        (Eq.refl (@List.cons Tree h (unpack (pack t)))) t ih)

/-- **The section.** Propositional, by induction on the mimic. -/
theorem packUnpack : ∀ b : S1, Eq (pack (unpack b)) b :=
  @S1.rec (fun a => Eq a a) (fun b => Eq (pack (unpack b)) b)
    (Eq.refl S0.leaf)
    (fun b _ => Eq.refl (S0.node b))
    (Eq.refl S1.nil)
    (fun a b _ ih2 =>
      @Eq.rec S1 (pack (unpack b))
        (fun x _ => Eq (S1.cons a (pack (unpack b))) (S1.cons a x))
        (Eq.refl (S1.cons a (pack (unpack b)))) b ih2)

section

variable (m1 : Tree → Type) (m2 : List Tree → Type)
variable (lf : m1 treeLeaf)
variable (nd : ∀ a : List Tree, m2 a → m1 (treeNode a))
variable (nl : m2 (@List.nil Tree))
variable (cs : ∀ (a : Tree) (b : List Tree), m1 a → m2 b → m2 (@List.cons Tree a b))

/-- The block's `node` minor. **The one place a transport appears**: the caller
    hands over `nd` at the real `List Tree` and the block asks for it at the
    mimic, so the value is carried along the section `packUnpack`. -/
noncomputable def ndMinor : ∀ b : S1, m2 (unpack b) → m1 (S0.node b) :=
  fun b ih =>
    @Eq.rec S1 (pack (unpack b)) (fun b' _ => m1 (S0.node b'))
      (nd (unpack b) ih) b (packUnpack b)

/-- The block's `cons` minor, at the block's own type and **with no transport**:
    `unpack (S1.cons a b)` ι-reduces to `List.cons a (unpack b)`, so the
    caller's `cs` fits on the nose. `S1.nil`'s minor is `nl` for the same
    reason and needs no wrapper at all. -/
noncomputable def csMinor :
    ∀ (a : S0) (b : S1), m1 a → m2 (unpack b) → m2 (unpack (S1.cons a b)) :=
  fun a b ih1 ih2 => cs a (unpack b) ih1 ih2

/-- `Tree.rec`, at the type the export declares for it.

    The `S0` motive is the caller's own; the `S1` motive is the caller's
    composed with `unpack`. Three of the four minors go through untouched —
    `nil` and `cons` because `unpack` ι-reduces on the mimic's constructors to
    the real ones, and `leaf` because `treeLeaf` is `S0.leaf` by δ. -/
noncomputable def treeRec : ∀ t : Tree, m1 t :=
  @S0.rec m1 (fun b => m2 (unpack b))
    lf (ndMinor m1 m2 nd) nl (csMinor m1 m2 cs)

/-- The same recursor at the **mimic**, which is the half `Tree.rec_1` runs. -/
noncomputable def blockRec1 : ∀ b : S1, m2 (unpack b) :=
  @S1.rec m1 (fun b => m2 (unpack b))
    lf (ndMinor m1 m2 nd) nl (csMinor m1 m2 cs)

/-- `Tree.rec_1`, at the type the export declares for it — **a recursor for one
    declaration whose major premise is another declaration's type**. It runs the
    block's recursor at the packed major and transports the result back along
    the retraction. -/
noncomputable def treeRec1 : ∀ l : List Tree, m2 l :=
  fun l =>
    @Eq.rec (List Tree) (unpack (pack l)) (fun x _ => m2 x)
      (blockRec1 m1 m2 lf nd nl cs (pack l)) l (unpackPack l)

end

/-- `congrArg pack`, spelled out — the file has no `congrArg`. -/
theorem congrPack : ∀ (l0 l : List Tree), Eq l0 l → Eq (pack l0) (pack l) :=
  fun l0 l h =>
    @Eq.rec (List Tree) l0 (fun x _ => Eq (pack l0) (pack x)) (Eq.refl (pack l0)) l h

/-- `congrArg (List.cons a)`, spelled out. -/
theorem congrCons : ∀ (a : Tree) (l0 l : List Tree), Eq l0 l →
    Eq (@List.cons Tree a l0) (@List.cons Tree a l) :=
  fun a l0 l h =>
    @Eq.rec (List Tree) l0 (fun x _ => Eq (@List.cons Tree a l0) (@List.cons Tree a x))
      (Eq.refl (@List.cons Tree a l0)) l h

section

variable (m1 : Tree → Type) (m2 : List Tree → Type)
variable (nd : ∀ a : List Tree, m2 a → m1 (treeNode a))
variable (cs : ∀ (a : Tree) (b : List Tree), m1 a → m2 b → m2 (@List.cons Tree a b))

/-- **The triangle identity**, in the only form the `node` rule needs: the
    transport `ndMinor` performs commutes with applying the minor. `Eq.rec` on
    `h`, landing at `Eq.refl`. -/
theorem transportNode :
    ∀ (l0 l : List Tree) (h : Eq l0 l) (ih : m2 l0),
      Eq (@Eq.rec S1 (pack l0) (fun b' _ => m1 (S0.node b'))
            (nd l0 ih) (pack l) (congrPack l0 l h))
         (nd l (@Eq.rec (List Tree) l0 (fun x _ => m2 x) ih l h)) :=
  fun l0 l h ih =>
    @Eq.rec (List Tree) l0
      (fun x hx =>
        Eq (@Eq.rec S1 (pack l0) (fun b' _ => m1 (S0.node b'))
              (nd l0 ih) (pack x) (congrPack l0 x hx))
           (nd x (@Eq.rec (List Tree) l0 (fun y _ => m2 y) ih x hx)))
      (Eq.refl (nd l0 ih)) l h

/-- **The stuck `Eq.rec` pushed through**, in the only form the `cons` rule
    needs. Same proof, one constructor along. -/
theorem transportCons :
    ∀ (a : Tree) (l0 l : List Tree) (h : Eq l0 l) (u : m1 a) (v : m2 l0),
      Eq (@Eq.rec (List Tree) (@List.cons Tree a l0) (fun x _ => m2 x)
            (cs a l0 u v) (@List.cons Tree a l) (congrCons a l0 l h))
         (cs a l u (@Eq.rec (List Tree) l0 (fun x _ => m2 x) v l h)) :=
  fun a l0 l h u v =>
    @Eq.rec (List Tree) l0
      (fun x hx =>
        Eq (@Eq.rec (List Tree) (@List.cons Tree a l0) (fun y _ => m2 y)
              (cs a l0 u v) (@List.cons Tree a x) (congrCons a l0 x hx))
           (cs a x u (@Eq.rec (List Tree) l0 (fun y _ => m2 y) v x hx)))
      (Eq.refl (cs a l0 u v)) l h

end

section

variable (m1 : Tree → Type) (m2 : List Tree → Type)
variable (lf : m1 treeLeaf)
variable (nd : ∀ a : List Tree, m2 a → m1 (treeNode a))
variable (nl : m2 (@List.nil Tree))
variable (cs : ∀ (a : Tree) (b : List Tree), m1 a → m2 b → m2 (@List.cons Tree a b))

/-- ι, `Tree.rec` on `Tree.leaf`. **Definitional.** -/
theorem iotaLeaf : Eq (treeRec m1 m2 lf nd nl cs treeLeaf) lf :=
  Eq.refl _

/-- ι, `Tree.rec_1` on `List.nil` — the **real** `List`'s constructor.
    **Definitional**: the transport collapses because `unpackPack List.nil`
    ι-reduces to `Eq.refl`. -/
theorem iota1Nil : Eq (treeRec1 m1 m2 lf nd nl cs (@List.nil Tree)) nl :=
  Eq.refl _

/-- ι, `Tree.rec` on `Tree.node` — **not** definitional, and this is the
    triangle identity being spent. The induction hypothesis for the nested field
    is `treeRec1` itself, which is what Lean 3's construction does not have. -/
theorem iotaNode (a : List Tree) :
    Eq (treeRec m1 m2 lf nd nl cs (treeNode a))
       (nd a (treeRec1 m1 m2 lf nd nl cs a)) :=
  transportNode m1 m2 nd (unpack (pack a)) a (unpackPack a)
    (blockRec1 m1 m2 lf nd nl cs (pack a))

/-- ι, `Tree.rec_1` on `List.cons` — **not** definitional. Both recursors appear
    on the right: `treeRec` on the head and `treeRec1` on the tail. -/
theorem iota1Cons (a : Tree) (b : List Tree) :
    Eq (treeRec1 m1 m2 lf nd nl cs (@List.cons Tree a b))
       (cs a b (treeRec m1 m2 lf nd nl cs a) (treeRec1 m1 m2 lf nd nl cs b)) :=
  transportCons m1 m2 cs a (unpack (pack b)) b (unpackPack b)
    (treeRec m1 m2 lf nd nl cs a)
    (blockRec1 m1 m2 lf nd nl cs (pack b))

end

/-- A use of the model's own recursor at a closed motive, so the file measures
    the recursor being *applied* and not only being declared. The same term
    `nested_iota.lean`'s `treeSize` is, one encoding down. -/
noncomputable def treeSize : Tree → N :=
  treeRec (fun _ => N) (fun _ => N)
    N.z
    (fun _ ih => N.s ih)
    N.z
    (fun _ _ ih1 _ => N.s (N.s ih1))
