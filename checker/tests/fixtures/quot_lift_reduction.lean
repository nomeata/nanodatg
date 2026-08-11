/-
# **Quot.lift of Quot.mk**, as a committed fixture

`good/tutorial/124_quotLiftReduction.ndjson` is the corpus file that
exercises `mini/src/quot_iota.rs` — the quotient ι step, whose certificate is
a three-equation chain (`β` down the lift's nest, `β` down `Quot.mk`'s, then
`lift_beta` with its two antecedents discharged). Until this file, it was
the *only* input reaching that chain, and the corpus is gitignored — so a
defect on the quot-ι path was invisible to a corpus-less `cargo test`.

That is not hypothetical. When the kernel `Env` moved behind the shared
`EnvCore` cell (ENV-UNIFY.md §3.4 item 1), the chain's composition read

```text
eq_trans(&mut ip.env_mut(), …).and_then(|t| eq_trans(&mut ip.env_mut(), …))
```

and the first guard is a statement-long temporary, so the closure's second
borrow was re-entrant: `RefCell already borrowed`, a panic, on exactly this
shape and nowhere else in the corpus. The committed export makes that path a
fixture-suite fact rather than a corpus-only one.

# What the theorem forces

`Quot.lift f h (Quot.mk r a)` is definitionally `f a` by the kernel's
quotient reduction and by nothing weaker, so proving the equation by
`Eq.refl (f a)` forces `whnf` through the quot-ι arm during `def_eq` — the
`quot_iota::fire` chain above, antecedents and all.
-/
prelude

--#export Eq quotLiftBeta

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

init_quot

/-- The conversion the checker must perform via the quotient ι step. -/
theorem quotLiftBeta {α : Sort u} {β : Sort v} (r : α → α → Prop) (f : α → β)
    (h : ∀ a b : α, r a b → Eq (f a) (f b)) (a : α) :
    Eq (Quot.lift f h (Quot.mk r a)) (f a) :=
  Eq.refl (f a)
