//! **`bnd` at an iterated sum with arbitrary summands** —
//! `derived::cumul::sum_bnd`, the reader `DeclUniverse` needs once a
//! constructor's fibre value stops being `finord(m)`.
//!
//! Three things have to hold at once and one file has to show all three:
//!
//! * the **binary** closure lemma is about the sum's own symbol, not about the
//!   union it unfolds to — otherwise `bnd_isum`'s fold does not compose;
//! * the **iterated** form at `m` copies of `1` produces *literally*
//!   `bnd(finord(m))`, the same conclusion `cumul::bnd_finord` produces, so the
//!   general reader subsumes the special one rather than sitting beside it;
//! * a summand that is **not** `1` — the shape a function-typed recursive
//!   argument produces — goes through, and its conclusion is about a set no
//!   arity can name.
//!
//! The last is the whole point of the file: `finord` is definable from a
//! `usize` and `Sum_1(Σz:Bool.1)` is not.

use kernel::{Env, Formula, Term};

use derived::cumul::{bnd, bnd_finord, bnd_isum, bnd_isums, bnd_sum, bnd_tagged_copy, bnd_unit};
use derived::isum::ISumSyms;

struct Fix {
    env: Env,
    c: derived::cumul::Chain,
    s: derived::sums::Sums,
    syms: ISumSyms,
}

fn fixture(depth: usize) -> Fix {
    let mut env = Env::new();
    let c = derived::cumul::Chain::new(&mut env).expect("Chain");
    let s = c.wt.sums.clone();
    let mut syms = ISumSyms::new();
    syms.ensure(&mut env, &s, depth).expect("ensure");
    Fix { env, c, s, syms }
}

/// **`⊢ ∀t ∀a. (bnd(a) → bnd({t} × a))`** — the one new derivation.
#[test]
fn a_tagged_copy_is_no_bigger_than_what_it_copies() {
    let mut f = fixture(1);
    let th = bnd_tagged_copy(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd_tagged_copy");
    assert!(th.hyps().is_empty(), "rests on nothing");
    assert!(kernel::thm::debug_locally_closed(th.concl()));

    // The statement, rebuilt from the outside: two binders, and the body is an
    // implication between two `bnd`s about the two sets named in the header.
    let (tv, av) = (f.env.fresh_var(), f.env.fresh_var());
    let (tt, ta) = (Term::var(tv), Term::var(av));
    let copy = f.s.prod.of(derived::singleton(f.s.ap.sets.up, tt.clone()), ta.clone());
    let want = Formula::forall(
        tv,
        Formula::forall(
            av,
            Formula::imp(
                bnd(&mut f.env, &f.c.r, &f.c.st, &ta),
                bnd(&mut f.env, &f.c.r, &f.c.st, &copy),
            ),
        ),
    );
    assert_eq!(*th.concl(), want, "bnd_tagged_copy has the wrong shape");

    // Non-vacuity: the two sides are two different formulas, so this is not a
    // reflexivity dressed up as a transport.
    assert_ne!(
        bnd(&mut f.env, &f.c.r, &f.c.st, &ta),
        bnd(&mut f.env, &f.c.r, &f.c.st, &copy),
        "the conclusion must be about the copy, not about the original"
    );
}

/// **`⊢ ∀a ∀b. ((bnd a ∧ bnd b) → bnd(a + b))`**, at the sum's own symbol.
///
/// The derivation goes through `sum_def`, so the risk this pins is that the
/// conclusion is left on the *unfolding* `({∅}×a) ∪ ({1}×b)` — which is a
/// different term, and would compose with nothing downstream.
#[test]
fn the_binary_sum_is_bounded_and_the_conclusion_is_about_the_symbol() {
    let mut f = fixture(1);
    let th = bnd_sum(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd_sum");
    assert!(th.hyps().is_empty(), "rests on nothing");

    let (av, bv) = (f.env.fresh_var(), f.env.fresh_var());
    let (ta, tb) = (Term::var(av), Term::var(bv));
    let summed = f.s.sum_of(ta.clone(), tb.clone());
    let want = Formula::forall(
        av,
        Formula::forall(
            bv,
            Formula::imp(
                Formula::and(
                    bnd(&mut f.env, &f.c.r, &f.c.st, &ta),
                    bnd(&mut f.env, &f.c.r, &f.c.st, &tb),
                ),
                bnd(&mut f.env, &f.c.r, &f.c.st, &summed),
            ),
        ),
    );
    assert_eq!(*th.concl(), want, "bnd_sum has the wrong shape");

    // The unfolding is a *different term*, so the assertion above is not
    // satisfied by leaving the conclusion on the union.
    let un = derived::funspace::bin_union(
        &f.s.ap.sets,
        f.s.prod.of(derived::singleton(f.s.ap.sets.up, f.s.zero()), ta),
        f.s.prod.of(derived::singleton(f.s.ap.sets.up, f.s.unit()), tb),
    );
    assert_ne!(summed, un, "`a + b` is the symbol; the union is what it abbreviates");
}

/// **The general reader subsumes the special one.** At `m` copies of `1` the
/// conclusion is the same formula `cumul::bnd_finord` produces.
///
/// Four arities, because `m = 0` is the symbol `Sum_0()` rather than the term
/// `∅` and `m = 1` is `Sum_1(1)` rather than `1`; a route that got the
/// unfolding wrong passes at neither, and one that ignored the nesting passes
/// at `m ≤ 1` and fails at `2` and `3`.
#[test]
fn the_unit_summands_give_back_the_finite_ordinal() {
    let mut f = fixture(3);
    let unit_bnd = bnd_unit(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd(1)");
    assert_eq!(
        *unit_bnd.concl(),
        bnd(&mut f.env, &f.c.r, &f.c.st, &f.s.unit()),
        "bnd_unit is about `1`"
    );

    let sum2 = bnd_sum(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd_sum");
    for m in 0..=3 {
        let summands = vec![f.s.unit(); m];
        let bnds = vec![unit_bnd.clone(); m];
        let general =
            bnd_isum(&mut f.env, &f.c.r, &f.c.st, &f.s, &f.syms, &sum2, &summands, &bnds)
                .expect("bnd_isum at unit summands");
        let special = bnd_finord(&mut f.env, &f.c.r, &f.c.st, &f.s, &f.syms, m)
            .expect("bnd_finord");
        assert!(general.hyps().is_empty());
        assert_eq!(
            *general.concl(),
            *special.concl(),
            "the general reader must produce `bnd(finord({m}))` on the nose"
        );
    }
}

/// **The shape that motivated the file**: a summand that is not `1`.
///
/// `Σz:Bool. 1` is what §5.2's recursive-argument rule gives
/// `RTree.node : (Bool → RTree) → RTree`, and `Sum_1(Σz:Bool.1)` is provably
/// **not** `finord(m)` for any `m` — which is exactly why the reader stated at
/// `finord(mᵢ)` could not be instantiated here.
#[test]
fn a_summand_that_is_not_the_unit_goes_through() {
    let mut f = fixture(3);

    // A closed named set standing in for `⟦Bool⟧`, and one for `Σz:Bool. 1`.
    // Nothing below inspects either: the reader takes `bnd(Aⱼ)` as an input.
    let boolean = f.syms.finord(&f.s, 2).expect("finord(2)");
    let bnd_boolean = {
        // `bnd(1 + (1 + 0))` — two summands, each `1`.
        let unit_bnd = bnd_unit(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd(1)");
        let sum2 = bnd_sum(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd_sum");
        bnd_isum(
            &mut f.env,
            &f.c.r,
            &f.c.st,
            &f.s,
            &f.syms,
            &sum2,
            &[f.s.unit(), f.s.unit()],
            &[unit_bnd.clone(), unit_bnd],
        )
        .expect("bnd(finord(2))")
    };
    assert_eq!(
        *bnd_boolean.concl(),
        bnd(&mut f.env, &f.c.r, &f.c.st, &boolean),
        "the stand-in summand's own bnd"
    );

    // The declaration's shape: `leaf` (no recursive argument), `succ` (one
    // plain one) and `node` (one whose domain is `Bool`).
    let unit_bnd = bnd_unit(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd(1)");
    let summands: Vec<Vec<Term>> =
        vec![Vec::new(), vec![f.s.unit()], vec![boolean.clone()]];
    let bnds = vec![Vec::new(), vec![unit_bnd], vec![bnd_boolean]];
    let sum2 = bnd_sum(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd_sum");
    let out = bnd_isums(&mut f.env, &f.c.r, &f.c.st, &f.s, &f.syms, &sum2, &summands, &bnds)
        .expect("bnd_isums over a whole declaration");
    assert_eq!(out.len(), 3);

    for (i, th) in out.iter().enumerate() {
        assert!(th.hyps().is_empty(), "constructor {i} rests on nothing");
        let value = f.syms.sum(&summands[i]).expect("the fibre value");
        assert_eq!(*th.concl(), bnd(&mut f.env, &f.c.r, &f.c.st, &value));
    }

    // The first two constructors' values *are* finite ordinals; the third is
    // not, at any arity. That is the whole distinction the old reader could
    // not express.
    assert_eq!(f.syms.sum(&summands[0]).unwrap(), f.syms.finord(&f.s, 0).unwrap());
    assert_eq!(f.syms.sum(&summands[1]).unwrap(), f.syms.finord(&f.s, 1).unwrap());
    let node = f.syms.sum(&summands[2]).unwrap();
    for m in 0..=3 {
        assert_ne!(node, f.syms.finord(&f.s, m).unwrap(), "not finord({m})");
    }
}

/// **What the reader refuses.** Each input is checked at the term it is used
/// at, and a mismatched or hypothetical one is rejected rather than composed.
#[test]
fn a_bnd_about_the_wrong_set_is_refused() {
    let mut f = fixture(2);
    let unit_bnd = bnd_unit(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd(1)");
    let sum2 = bnd_sum(&mut f.env, &f.c.r, &f.c.st, &f.s).expect("bnd_sum");
    let zero_bnd = derived::cumul::bnd_empty(&mut f.env, &f.c.r, &f.c.st).expect("bnd(∅)");

    // A `bnd` about `∅` offered as the `bnd` of `1`.
    assert!(
        bnd_isum(
            &mut f.env,
            &f.c.r,
            &f.c.st,
            &f.s,
            &f.syms,
            &sum2,
            &[f.s.unit()],
            std::slice::from_ref(&zero_bnd),
        )
        .is_none(),
        "the input is checked at the summand it is used at"
    );

    // One summand, no theorem.
    assert!(bnd_isum(
        &mut f.env,
        &f.c.r,
        &f.c.st,
        &f.s,
        &f.syms,
        &sum2,
        &[f.s.unit()],
        &[]
    )
    .is_none());

    // An arity the symbol cache has not reached.
    let wide = vec![f.s.unit(); 5];
    let wide_bnds = vec![unit_bnd; 5];
    assert!(
        bnd_isum(&mut f.env, &f.c.r, &f.c.st, &f.s, &f.syms, &sum2, &wide, &wide_bnds).is_none(),
        "`ensure` reached 2, not 5"
    );

    // A second sum family in the same `Env` is not this one.
    let s2 = derived::sums::Sums::new(&mut f.env).expect("a second Sums");
    assert!(bnd_tagged_copy(&mut f.env, &f.c.r, &f.c.st, &s2).is_none());
    assert!(bnd_unit(&mut f.env, &f.c.r, &f.c.st, &s2).is_none());
}
