/-
# **δ inside a proof**, at four lines

`nested_model.lean` leaves four `waiting:no-endpoint` constant typings —
`transportNode`, `transportCons` and the two ι rules built on them — and the
whole of that residual is one shape. This file is that shape and nothing else:
no nesting, no round trip, no recursor of its own.

```text
transported a  =  @Eq.rec N a (fun _ _ => N) (N.s a) a (myRefl a)
```

The redex is a **data**-valued `Eq.rec` whose *major premise is a named proof*.
Firing it needs `myRefl a` reduced to `Eq.refl a` first, which is a δ step **on
a term that is a proof**. `mini/src/kernel.rs`'s `whnf` peels the applied spine
with `Checker::split_app`, and §6.2 sends a proof-valued application to `•`,
which is not an `app` — so the peel hands back `None`, `cur_tm` is `None` at the
`Const` node, and `delta_evidence` mints `Gap::NoEndpoint` for a step it has no
endpoints to state.

Acceptance is unaffected: `theShape` is checked and the file is accepted. What
is missing is the *certificate* for a reduction the checker performed.

# Why the reduct is data and the major is a proof, deliberately

Both halves are load-bearing and a fixture with either one dropped measures
nothing:

* if the **reduct** were a proof too, the equation the conversion owes would be
  between two `•`s and proof irrelevance would close it whatever `whnf` did;
* if the **major** were `Eq.refl a` written out, no δ would be needed and the ι
  rule would fire on a constructor at once.

`myRefl` therefore exists only to put a name in front of `Eq.refl`, and the
motive `fun _ _ => N` lands in `Type` for the same reason `nested_iota.lean`
gives about `Prop`-valued motives.

`Nat` is avoided for the reason `infinitary_branching.lean` gives.
-/
prelude

--#export Eq N myRefl transported theShape

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

/-- **A proof behind a name.** Reducing it is a δ step on a proof. -/
theorem myRefl (a : N) : Eq a a := Eq.refl a

/-- A **data**-valued transport whose major premise is that named proof. -/
noncomputable def transported (a : N) : N :=
  @Eq.rec N a (fun _ _ => N) (N.s a) a (myRefl a)

/-- The conversion the checker has to perform, and the certificate it owes. -/
theorem theShape (a : N) : Eq (transported a) (N.s a) :=
  Eq.refl (N.s a)
