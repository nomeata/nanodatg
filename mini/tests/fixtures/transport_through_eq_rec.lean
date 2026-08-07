/-
# **`transportNode`'s shape, at twenty lines**

`nested_model.lean` leaves four `waiting:no-endpoint` constant typings —
`transportNode`, `transportCons`, and the two ι rules `iotaNode`/`iota1Cons`
that are those two lemmas applied. This file is the first of them with the
nesting taken out: no `pack`, no `unpack`, no mimic, no round trip. `N.s`
stands in for `pack` and `g a` for the `node` minor's value, and the proof is
`transportNode`'s own, one constructor along.

```text
transportS : ∀ a b (h : Eq a b),
  Eq (@Eq.rec N (N.s a) (fun y _ => m y) (g a) (N.s b) (myCongr a b h))  (g b)
```

**Both `Eq.rec`s are load-bearing and the two are at different motive sorts.**
The inner one — the transport being commuted past — has a motive `fun y _ => m y`
into `Type`, so its value is data and the equation is about two genuinely
different terms. The outer one — the proof — has a motive into `Prop` that
*mentions its own proof binder* `hx`, which is what makes the statement a family
over `h` rather than a statement about one proof, and what makes the whole value
interpret to `•`.

`myCongr` is `congrPack`: `congrArg` written out, because the file has no
`congrArg` and because the transport's major premise has to be a **named** proof
rather than a constructor.

# What this is for

`delta_inside_a_proof.lean` is the same question at four lines and **certifies
cleanly** — a data-valued `Eq.rec` whose major premise is a named proof needs a
δ step on a proof, and that step is threaded. So the residual is *not* "δ inside
a proof", which was the first hypothesis and is refuted by that file. This one
carries whatever the residual actually is, at a twentieth of `nested_model`'s
size and a four-hundredth of its conversions.

`Nat` is avoided for the reason `infinitary_branching.lean` gives, and the
motive lands in `Type` for the reason `nested_iota.lean` gives.
-/
prelude

--#export Eq N myCongr transportS

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

/-- `congrArg N.s`, spelled out — this file's `congrPack`. -/
theorem myCongr : ∀ (a b : N), Eq a b → Eq (N.s a) (N.s b) :=
  fun a b h =>
    @Eq.rec N a (fun x _ => Eq (N.s a) (N.s x)) (Eq.refl (N.s a)) b h

section

variable (m : N → Type)
variable (g : ∀ a : N, m (N.s a))

/-- **The triangle identity**, in `transportNode`'s exact shape: the transport
    along `myCongr a b h` commutes with applying `g`. `Eq.rec` on `h`, landing
    at `Eq.refl`. -/
theorem transportS : ∀ (a b : N) (h : Eq a b),
    Eq (@Eq.rec N (N.s a) (fun y _ => m y) (g a) (N.s b) (myCongr a b h))
       (g b) :=
  fun a b h =>
    @Eq.rec N a
      (fun x hx =>
        Eq (@Eq.rec N (N.s a) (fun y _ => m y) (g a) (N.s x) (myCongr a x hx))
           (g x))
      (Eq.refl (g a)) b h

end
