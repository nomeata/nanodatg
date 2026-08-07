/-
# A recursor whose major **reduces and stays stuck**

`mini::kernel`'s `whnf` reduces a recursor's major and then either fires ι or
gives up. The giving-up branch minted `Gap::StuckRecursor` whenever the major
had moved, on the stated grounds that

> the major's own reduction is not threaded (it is the acceptance-only `whnf`
> above), so this is a named absence

and that was true when it was written. It stopped being true when the `whnf`
above became `whnf_conv`: the ι arm forty lines up already composes the major's
conversion `mconv` through `Checker::spine_cong`, and this arm kept declining
for a reason that had been repaired underneath it. The comment and the code had
drifted apart, and nothing caught it because **no corpus declaration reaches
the branch** — the note beside it says so: *"instrumented over all 91 exports
this branch mints `0`"*.

`nested_model.ndjson` reaches it 3 214 times and is where it was found. This
file is the same branch in four declarations, so that it can be *measured*:
`nested_model` needs over 4 GB and half an hour once the certificate is
actually built, and a fixture nobody can afford to run is not a regression.

## What makes the major move without firing

`dbl n` at a variable `n` is a stuck `N.rec` application. `outer`'s major is
`dbl n`, so reducing it δ-unfolds `dbl` into that stuck `N.rec` — the major
**changed** and is still not a constructor application, which is exactly the
branch. `outerEq` states the two spellings equal, so the conversion has to
carry a certificate across the change rather than merely decide it.

| declaration | what it exercises |
| --- | --- |
| `dbl` | the inner stuck recursor, on its own — the **control**, which certified before |
| `outer` | a recursor whose major δ-reduces to a stuck recursor |
| `outerEq` | the conversion that has to compose across the moved major |
| `outerTwice` | the major moves **twice** — `dbl (dbl n)` — so a fix that composed one congruence and stopped is not passed |

`outerTwice` is the third element: with one nesting level a chain and a single
step are indistinguishable, which is this project's standing reason for three
rather than two.

**It is `Nat`-free and structure-free.** The defect is in the recursor arm of
`whnf`, so the fixture declares a Peano type and nothing else; there is no
projection anywhere in it, which is what distinguishes this bug from the two in
`proj_reduced_carrier.lean` and `proj_reduced_subject.lean`.
-/
prelude

--#export Eq N dbl outer outerEq outerTwice outerTwiceEq

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

/-- Stuck at a variable major: `N.rec … n` with `n` a binder. The control. -/
noncomputable def dbl (n : N) : N :=
  N.rec (motive := fun _ => N) N.z (fun _ ih => N.s (N.s ih)) n

/-- **The branch.** The major `dbl n` δ-reduces to a stuck `N.rec` application:
    it changed, and it is not a constructor. -/
noncomputable def outer (n : N) : N :=
  N.rec (motive := fun _ => N) N.z (fun _ ih => N.s ih) (dbl n)

/-- The conversion that has to compose across the moved major, rather than
    merely decide it. -/
theorem outerEq (n : N) :
    Eq (outer n) (N.rec (motive := fun _ => N) N.z (fun _ ih => N.s ih) (dbl n)) :=
  Eq.refl _

/-- The major moves **twice**. A fix that lifted one congruence and stopped
    passes `outerEq` and fails here. -/
noncomputable def outerTwice (n : N) : N :=
  N.rec (motive := fun _ => N) N.z (fun _ ih => N.s ih) (dbl (dbl n))

theorem outerTwiceEq (n : N) :
    Eq (outerTwice n) (N.rec (motive := fun _ => N) N.z (fun _ ih => N.s ih) (dbl (dbl n))) :=
  Eq.refl _
