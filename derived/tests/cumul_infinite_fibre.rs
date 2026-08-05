//! **Where the `ω`-tower stops** — `bnd` at a fibre that is not finite, pinned
//! at the terms rather than at a reason string.
//!
//! `NTree.node : (N → NTree) → NTree` is ordinary Lean and its carrier cannot
//! be placed. [`derived::cumul::bnd`] is why:
//!
//! ```text
//! bnd(k) := ∀g. ((∀b. b ∈ k → g(b) ∈ T) → ∃p ∈ ω. ∀b. b ∈ k → g(b) ∈ Vₚ)
//! ```
//!
//! holds exactly when `|k| < cf(ω)`, i.e. when `k` is **finite**; at `k = ⟦N⟧`
//! it is refutable, not merely underived. See `cumul/bounded.rs`'s header and
//! the thesis §6.2.1, which answers it with a tower at a regular `κ` such that
//! `cf(κ) > sup_{a∈A}|B(a)|`.
//!
//! # What this file measures that `cumul_decl_fibres.rs` does not
//!
//! That file takes the chain apart at `⟦Bool⟧`, where every step succeeds, and
//! asserts one refusal beside it — `bnd_nullary_tags` at `N`. **One refusal
//! cannot say which of the two things `bnd_nullary_tags` refuses fired**: its
//! guard is `!c.args.is_empty() || c.recs != 0`, a disjunction of two
//! independent conditions, and a single failing declaration is compatible with
//! either disjunct, with both, and with a guard that refuses everything
//! non-nullary for one reason. Three declarations separate them, and they must
//! be three declarations that differ in *one* coordinate each:
//!
//! | `γ` | args | recs | `bnd_nullary_tags` | is `bnd(⟦γ⟧)` true? |
//! |---|---:|---:|---|---|
//! | `B2` | 0 | 0 | derives | yes, and derived |
//! | `P1` | 1 | 0 | refuses — a field | **yes**, and unbuilt |
//! | `N`  | 0 | 1 | refuses — recursion | **no** |
//!
//! The fourth column is what the third cannot say, and that gap is the whole
//! point of this file: `P1` is a **missing lemma** at a finite fibre and `N` is
//! a **missing construction** at an infinite one. A round of work that closes
//! `bnd_nullary_tags`' field case moves the second row and must leave the third
//! exactly where it is.
//!
//! # Only one of the two disjuncts is load-bearing, and that is measured
//!
//! Mutation-tested, and the result corrects what the paragraph above would
//! otherwise be read as claiming. Dropping `|| c.recs != 0` from the guard
//! **fails this file and `cumul_decl_fibres.rs`**: `N`'s two tag summands are
//! both `1`, so with that disjunct gone the derivation *succeeds* and returns a
//! real `⊢ bnd(A_N)`. Dropping `!c.args.is_empty()` fails **nothing, anywhere**
//! — `P1`'s tag summand is a one-binder telescope, so the `base_ax` comparison
//! four lines further down refuses it regardless.
//!
//! So the field disjunct is *over-determined*, exactly as `bnd_carrier`'s
//! `recs` guard is and for the same kind of reason, and no test at this
//! interface can kill it. What is asserted below instead is the fact the guard
//! is standing in for — `P1`'s summand is not `1` and `N`'s are — which is
//! checkable, is the thing a reader needs, and is what makes the two refusals
//! different rather than the guard's shape.
//!
//! # The interface measurement, for the `κ`-tower
//!
//! [`derived::cumul::FibreFacts`] has two components per recursive slot,
//! `⊢ bnd(Aᵢⱼ)` and `⊢ Aᵢⱼ ∈ Uₙ`. At `NTree` the **second is available today**
//! — [`the_universe_half_of_the_fibre_facts_survives_an_infinite_domain`]
//! derives it — and the first is not. So the obstruction is exactly one of the
//! two components, and the question a `κ`-tower answers is whether that
//! component still needs to exist. Recorded here so it is re-measurable rather
//! than argued.

use kernel::{Env, Formula, Term};

use derived::cumul::{bnd, bnd_unit, nullary_summands_in_u1, tags_in_u1, DeclUniverse, IndChain};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine};

/// The three domain declarations, over one apparatus: `B2` (two nullary
/// constructors), `P1` (one constructor with one field, of type `⟦B2⟧`) and
/// `N` (`zero` and `succ : N → N`).
///
/// One coordinate apart each: `P1` differs from `B2` only by having a field,
/// `N` only by having a recursive argument.
fn domains(env: &mut Env, mach: &mut Machine) -> (Inductive, Inductive, Inductive) {
    let b2 = Inductive::build(
        env,
        mach,
        &DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]),
    )
    .expect("B2");
    let p1 = Inductive::build(
        env,
        mach,
        &DeclSpec::new(0, vec![CtorSpec::new(vec![b2.ty], 0)]),
    )
    .expect("P1");
    let n = Inductive::build(
        env,
        mach,
        &DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(Vec::new(), 1)]),
    )
    .expect("N");
    (b2, p1, n)
}

/// **Three declarations, one coordinate apart each, and two different reasons
/// for the same refusal.**
///
/// `B2` derives; `P1` and `N` refuse, and they refuse for different reasons
/// that this test separates by construction — `P1` has no recursion and `N` has
/// no fields, so neither refusal can be blamed on the other's coordinate.
///
/// The reasons, and not the guard's two disjuncts: see the module header for
/// the mutation that shows the field disjunct is over-determined and the
/// recursion disjunct is not.
#[test]
fn the_nullary_tags_guard_refuses_a_field_and_a_recursion_separately() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");
    let (b2, p1, n) = domains(&mut env, &mut mach);

    // ── `B2`: both coordinates zero, and it derives ─────────────────────────
    let b2_tags =
        derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &b2).expect("bnd(A) for B2");
    assert!(b2_tags.hyps().is_empty(), "rests on nothing");
    assert_eq!(*b2_tags.concl(), bnd(&mut env, &ic.chain.r, &ic.chain.st, &b2.tags));

    // ── `P1`: a field, no recursion ─────────────────────────────────────────
    assert_eq!(p1.spec.ctors[0].args.len(), 1, "the field coordinate");
    assert_eq!(p1.spec.ctors[0].recs, 0, "and only that one");
    assert!(
        derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &p1).is_none(),
        "a constructor with a field has the tag summand `Σ y:⟦B2⟧. 1`, not `1`"
    );

    // ── `N`: recursion, no field ────────────────────────────────────────────
    assert!(n.spec.ctors.iter().all(|c| c.args.is_empty()), "no field coordinate");
    assert_eq!(n.spec.ctors[1].recs, 1, "and one recursive argument");
    assert!(
        derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &n).is_none(),
        "and the recursion is refused too — by the other disjunct"
    );

    // **The two refusals are not the same fact.** `N`'s tag summands *are* both
    // `1` — recursion moves into the fibre value, not into the tag sum — so
    // `bnd(A_N)` is true and buildable, and the guard that refuses it is
    // conservative. `P1`'s is not `1`, and its refusal is a real missing lemma
    // one layer down. Measured on the summands themselves:
    let unit = mach.wt.sums.unit();
    for i in 0..n.summands.len() {
        let at = derived::inst_all(&n.telescopes[i].base_ax, &[]).expect("base_ax");
        assert_eq!(
            *at.concl(),
            Formula::eq(n.summands[i].clone(), unit.clone()),
            "N's tag summand {i} is `1`, recursion or not — so its `bnd` is not the obstruction"
        );
    }
    let p1_at = derived::inst_all(&p1.telescopes[0].base_ax, &[]).expect("base_ax");
    assert_ne!(
        *p1_at.concl(),
        Formula::eq(p1.summands[0].clone(), unit),
        "P1's tag summand is a one-binder telescope and not `1`, which is the whole of why \
         the same guard rejects it for a different reason"
    );
}

/// **`⊢ Σ z:⟦N⟧. 1 ∈ U₁` derives while its `bnd` does not** — the two halves of
/// [`derived::cumul::FibreFacts`] come apart at an infinite domain, and only
/// one of them is the tower's.
///
/// This is the `NTree` composition, run as far as it goes:
///
/// ```text
/// ⟦N⟧ ∈ U₁                DeclUniverse::over     over the N declaration    ✓
/// Σ z:⟦N⟧. 1 ∈ U₁         unary_telescope_at     the fibre telescope       ✓
/// bnd(⟦N⟧)                bnd_carrier            over the N declaration    ✗
/// bnd(Σ z:⟦N⟧. 1)         bnd_telescope1         has no input              ✗
/// ```
///
/// The `bnd_carrier` refusal is **not** the `κ`-tower's to fix on its own: with
/// `bnd_nullary_tags`' conservative guard lifted, `bnd_carrier` refuses again
/// on `recs`, and that guard is load-bearing — a recursive declaration's fibres
/// are not empty, so the pullback along `mk(x) = ⟨x,∅⟩` has nothing to say. It
/// is refused for a true reason and the goal beyond it is *false*: this is the
/// end of the road at `ω`, not a gap in the plumbing.
#[test]
fn the_universe_half_of_the_fibre_facts_survives_an_infinite_domain() {
    let mut env = Env::new();
    let (ic, mut mach) = IndChain::new(&mut env).expect("the chain and the apparatus");
    let inversion = derived::wtype::w_inversion(&mut env, &mach.wt).expect("W3");
    let (_b2, _p1, n) = domains(&mut env, &mut mach);

    // ── `⟦N⟧ ∈ U₁` — the universe half, over `N`'s own declaration ──────────
    let n_su = nullary_summands_in_u1(&mut env, &ic, &mach, &n).expect("N's summands");
    let n_tags = tags_in_u1(&mut env, &ic, &mach, &n, None, &n_su).expect("A_N ∈ U₁");
    let n_u1 = DeclUniverse::over(&mut env, &ic, &mach, &n, None, &n_tags)
        .expect("⟦N⟧ ∈ U₁ — a recursive declaration places perfectly well")
        .ty_in_u1;
    assert_eq!(*n_u1.concl(), Formula::mem(n.carrier.clone(), ic.chain.u1.set.clone()));

    // ── `NTree.node : (⟦N⟧ → NTree) → NTree`, over that carrier's symbol ────
    let spec = DeclSpec::new(
        0,
        vec![CtorSpec::nullary(), CtorSpec::with_rec_doms(Vec::new(), vec![vec![n.ty]])],
    );
    let ntree = Inductive::build(&mut env, &mut mach, &spec).expect("NTree");
    let tel = mach.telescope(&mut env, 0, &[n.ty]).expect("the fibre telescope");
    let summand = ntree.recargs[1].summands[0].clone();
    assert_eq!(summand, tel.ty_of(Vec::new()), "the fibre summand is this telescope's type");

    // ── the half that survives ──────────────────────────────────────────────
    let fib_mem = derived::cumul::unary_telescope_at(
        &mut env,
        &ic,
        &mach,
        &tel,
        &[],
        None,
        &ic.chain.u1,
        &n_u1,
    )
    .expect("Σ z:⟦N⟧. 1 ∈ U₁ — the universe side never asked for finiteness");
    assert!(fib_mem.hyps().is_empty(), "rests on nothing");
    assert_eq!(*fib_mem.concl(), Formula::mem(summand.clone(), ic.chain.u1.set.clone()));

    // ── the half that does not ──────────────────────────────────────────────
    //
    // `bnd(A_N)` is supplied by hand — `bnd_nullary_tags` refuses `N` on its
    // conservative `recs` disjunct, and handing `bnd_carrier` a *different*
    // declaration's `bnd(A)` would make it refuse on the conclusion comparison
    // and pin nothing about recursion.
    let n_tags_bnd = {
        let unit_bnd =
            bnd_unit(&mut env, &ic.chain.r, &ic.chain.st, &mach.wt.sums).expect("bnd(1)");
        let bnds: Vec<kernel::Thm> = (0..n.summands.len())
            .map(|i| {
                let base_at = derived::inst_all(&n.telescopes[i].base_ax, &[]).expect("base_ax");
                let hole = env.fresh_var();
                let body = bnd(&mut env, &ic.chain.r, &ic.chain.st, &Term::var(hole));
                kernel::Thm::mp(
                    &kernel::Thm::mp(
                        &kernel::Thm::eq_leibniz(
                            mach.wt.sums.unit(),
                            n.summands[i].clone(),
                            hole,
                            body,
                        ),
                        &derived::eq_symm(&mut env, &base_at).expect("symm"),
                    )
                    .expect("leibniz"),
                    &unit_bnd,
                )
                .expect("bnd of the summand")
            })
            .collect();
        derived::cumul::bnd_isum(
            &mut env,
            &ic.chain.r,
            &ic.chain.st,
            &mach.wt.sums,
            &mach.syms,
            &ic.bnd_sum,
            &n.summands,
            &bnds,
        )
        .expect("bnd(A_N), built without `bnd_nullary_tags`")
    };
    assert_eq!(*n_tags_bnd.concl(), bnd(&mut env, &ic.chain.r, &ic.chain.st, &n.tags));
    assert!(
        derived::cumul::bnd_carrier(&mut env, &ic, &mach, &n, &inversion, &n_tags_bnd).is_none(),
        "even with `bnd(A_N)` in hand there is no `bnd(⟦N⟧)`: the conclusion is false at the \
         `ω`-tower, and the guard that refuses it is telling the truth"
    );

    // ── and so the placement declines, with the universe half in hand ───────
    let su = nullary_summands_in_u1(&mut env, &ic, &mach, &ntree).expect("NTree's summands");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ntree, None, &su).expect("A ∈ U₁");
    assert!(
        DeclUniverse::over(&mut env, &ic, &mach, &ntree, None, &tags).is_none(),
        "the plain path refuses a non-unit fibre summand"
    );

    // The control: the *same* composition at a finite domain goes through, so
    // the decline above is about `⟦N⟧` and not about the shape of `NTree`.
    // `cumul_decl_fibres.rs` derives it in full; here it is enough that the
    // input `bnd_telescope1` wants exists there and does not exist here.
    assert!(
        derived::cumul::bnd_nullary_tags(&mut env, &ic, &mach, &ntree).is_none(),
        "NTree's own tag sum is refused on the same conservative disjunct — a second reason \
         the placement declines, and one the κ-tower does not touch"
    );
}
