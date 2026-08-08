/-
# **Reducing a proof, at four declarations**

`whnf` on a *proof-valued* spine is the residual this file pins. §6.2 sends a
proof-valued application to `•`, so `Checker::split_app` — which peels
`app(⟦f⟧,⟦a⟧)` — hands back nothing on it, and every endpoint after the first
`App` node of such a spine is gone. The walk then gives up at whichever step
comes next, and the reasons it files (`delta_evidence`'s first line,
`beta_evidence`'s, the stuck-recursor arm's) are all correct reports of an
absence decided upstream. **The absence is not real**: `⟦e⟧` and `⟦whnf e⟧` are
both `•`, so the equation owed is `• = •`.

# What has to be in the file for the hole to be reached

Three things, and the two files next door each have two of them.

* the reduction must run **through** a proof — `delta_inside_a_proof.lean` has
  that, and certifies, because proof irrelevance closes its pair before the δ
  leg is needed;
* the proof must **reduce and stay stuck** rather than reach `Eq.refl`, so that
  the walk really does peel it — `myCongr a b h` at an open `h` δβ-reduces to an
  `Eq.rec` on `h`, which is stuck;
* and the *conversion* must be **consumed**. This is the one
  `transport_through_eq_rec.lean` does not have: there the two sides of the pair
  that gaps are the same expression, so `def_eq_struct`'s `App` arm answers
  reflexivity (`#90(b)`) and no leg through the proof is ever asked for.

`twoProofs` supplies the third. Its left side is a **`def`**, so seeing the two
sides agree costs a δ step and then a reduction of `Eq.rec`'s major; its right
side transports along a *different* proof of the same proposition, so the two
majors are two distinct stuck terms that only **proof irrelevance** identifies.
The conversion is therefore non-trivial, it is consumed by the constant typing,
and it runs through two proof-valued spines.

`nested_model.lean`'s `iotaNode` is this shape with the nesting on:
`treeRec … (treeNode l)` δι-reduces to a transport along `packUnpack (pack l)`
while the theorem states one along `congrPack (unpack (pack l)) l (unpackPack l)`.
That file is 3.1 million conversions; this one is a few thousand.

`Nat` is avoided for the reason `infinitary_branching.lean` gives, and the
motive lands in `Type` for the reason `nested_iota.lean` gives — a `Prop`-valued
motive would let proof irrelevance close the whole equation without reducing
anything.
-/
prelude

--#export Eq N myCongr sameEq altCongr moveA twoProofs

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The payload, so that a motive can land in `Type` without `Nat`. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- `congrArg N.s`, spelled out — the file has no `congrArg`. -/
theorem myCongr : ∀ (a b : N), Eq a b → Eq (N.s a) (N.s b) :=
  fun a b h =>
    @Eq.rec N a (fun x _ => Eq (N.s a) (N.s x)) (Eq.refl (N.s a)) b h

/-- The identity on proofs, written as a transport so that it **reduces**
    rather than disappearing: `altCongr` must be a different term from
    `myCongr`, not a different name for it. -/
theorem sameEq : ∀ (a b : N), Eq a b → Eq a b :=
  fun a b h => @Eq.rec N a (fun x _ => Eq a x) (Eq.refl a) b h

/-- The **second** proof of `myCongr`'s statement. -/
theorem altCongr : ∀ (a b : N), Eq a b → Eq (N.s a) (N.s b) :=
  fun a b h => myCongr a b (sameEq a b h)

section

variable (m : N → Type)

/-- The transport, behind a **δ step**: this is what makes the conversion below
    non-trivial, so that the certificate for it is actually consumed. -/
noncomputable def moveA : ∀ (a b : N) (h : Eq a b), m (N.s a) → m (N.s b) :=
  fun a b h v => @Eq.rec N (N.s a) (fun y _ => m y) v (N.s b) (myCongr a b h)

/-- **Two transports along two different proofs of one proposition.** The
    kernel identifies the two majors by proof irrelevance; getting there means
    reducing both of them, and reducing a proof is what this file is about. -/
theorem twoProofs : ∀ (a b : N) (h : Eq a b) (v : m (N.s a)),
    Eq (moveA m a b h v)
       (@Eq.rec N (N.s a) (fun y _ => m y) v (N.s b) (altCongr a b h)) :=
  fun a b h v => Eq.refl _

end
