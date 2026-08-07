//! Cantor's theorem in surjective form, and the universe fact it unlocks.

use kernel::{Env, Formula, Term};

use derived::cantor;
use derived::universe as uni;

/// `⊢ ∀I ∀k. ¬(DOM ∧ (SV ∧ ONTO))`, with all three clauses spelled out here
/// rather than taken from the module that proves the theorem.
#[test]
fn no_set_surjects_onto_its_own_subsets() {
    let mut env = Env::new();
    let (_, empty_ax) = derived::empty::empty(&mut env);
    let thm = cantor::no_surjection_onto_subsets(&mut env, &empty_ax).expect("Cantor");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (i, k) = (env.fresh_var(), env.fresh_var());
    let (ti, tk) = (Term::var(i), Term::var(k));

    let (x, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tb, tc) = (Term::var(x), Term::var(b), Term::var(c));

    let dom = {
        let p = kernel::thm::pair_in(&mut env, tk.clone(), tx.clone(), tb.clone());
        Formula::forall(
            x,
            Formula::forall(b, Formula::imp(p, Formula::mem(tx.clone(), ti.clone()))),
        )
    };
    let sv = {
        let p1 = kernel::thm::pair_in(&mut env, tk.clone(), tx.clone(), tb.clone());
        let p2 = kernel::thm::pair_in(&mut env, tk.clone(), tx.clone(), tc.clone());
        Formula::forall(
            x,
            Formula::forall(
                b,
                Formula::forall(
                    c,
                    Formula::imp(Formula::and(p1, p2), Formula::eq(tb.clone(), tc.clone())),
                ),
            ),
        )
    };
    let onto = {
        let sub = kernel::thm::subset(&mut env, tb.clone(), ti.clone());
        let p = kernel::thm::pair_in(&mut env, tk.clone(), tx.clone(), tb.clone());
        Formula::forall(b, Formula::imp(sub, Formula::exists(x, p)))
    };

    let want = Formula::not(Formula::and(dom.clone(), Formula::and(sv.clone(), onto.clone())));
    let mut cur = thm.clone();
    for v in [i, k] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want, "Cantor has the wrong shape");

    // The builders agree with the spelled-out clauses, so downstream callers
    // that use them are talking about this theorem.
    assert_eq!(cantor::pairs_start_in(&mut env, &tk, &ti), dom);
    assert_eq!(cantor::single_valued(&mut env, &tk), sv);
    assert_eq!(cantor::onto_subsets(&mut env, &tk, &ti), onto);

    // Non-vacuity: the three clauses are genuinely different formulas, so the
    // refuted conjunction is not a disguised `φ ∧ φ`.
    assert_ne!(dom, sv);
    assert_ne!(dom, onto);
    assert_ne!(sv, onto);
    assert_ne!(*thm.concl(), Formula::false_());
}

/// `⊢ ∀u ∀y. ((is_universe(u) ∧ y ∈ u) → ¬(y ≈ u))`, pinned to the kernel's own
/// `equinumerous` rather than to a look-alike rebuilt here.
#[test]
fn no_member_of_a_universe_is_equinumerous_with_it() {
    let mut env = Env::new();
    let (_, empty_ax) = derived::empty::empty(&mut env);
    let thm =
        cantor::member_not_equinumerous(&mut env, &empty_ax).expect("member_not_equinumerous");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (u, y) = (env.fresh_var(), env.fresh_var());
    let (tu, ty) = (Term::var(u), Term::var(y));
    let equi = kernel::thm::equinumerous(&mut env, ty.clone(), tu.clone());
    let want = Formula::imp(
        Formula::and(uni::is_universe(&mut env, &tu), Formula::mem(ty.clone(), tu.clone())),
        Formula::not(equi.clone()),
    );

    let mut cur = thm.clone();
    for v in [u, y] {
        cur = derived::inst_self(v, &cur).expect("reopen");
    }
    assert_eq!(*cur.concl(), want, "member_not_equinumerous has the wrong shape");

    // Non-vacuity: the negated formula is the kernel's equinumerosity, and it is
    // not the antecedent under another name.
    assert_ne!(equi, Formula::false_());
    assert_ne!(equi, uni::is_universe(&mut env, &tu));

    // A theorem that is not an empty-set axiom is refused, so the Separation
    // that builds the diagonal cannot be fed something else.
    //
    // **This is the pin that flipped.** It previously asserted an *assembly*
    // failure named `crate::funcs::separation_full`, with a comment saying the
    // verdict was wrong — `empty` is a parameter of a public entry, so a wrong
    // one is the contract working — and that it was not this module's to fix,
    // because the refusal came back through `err::imported` from a module that
    // had not been migrated and whose reason was therefore dropped at the
    // boundary. `crate::funcs` moved to `DResult` in the commit that changed
    // this line, so the reason now survives the whole way and the verdict is
    // the right one. Nothing in `cantor/` changed.
    let e = cantor::member_not_equinumerous(&mut env, &thm)
        .expect_err("that theorem is not an empty-set axiom");
    assert!(e.is_decline(), "a wrong premise is the contract working, not a mis-assembly");
    assert_eq!(e.reason(), "the emptiness premise does not state a negation at the probe variable");
}

/// The two facts compose into the decision procedure `C₄` becomes: for
/// `y ⊆ u`, membership and equinumerosity are mutually exclusive, so `C₄`'s
/// disjunction is really a dichotomy.
#[test]
fn c4_becomes_a_dichotomy() {
    let mut env = Env::new();
    let (_, empty_ax) = derived::empty::empty(&mut env);
    let ne = cantor::member_not_equinumerous(&mut env, &empty_ax).expect("ne");

    // Instantiating at concrete constants keeps the statement free of the
    // module's own variables.
    let tu = Term::apply(env.declare(0), vec![]);
    let ty = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&ne, &[tu.clone(), ty.clone()]).expect("instantiate");
    let want = Formula::imp(
        Formula::and(uni::is_universe(&mut env, &tu), Formula::mem(ty.clone(), tu.clone())),
        Formula::not(kernel::thm::equinumerous(&mut env, ty, tu)),
    );
    assert_eq!(*at.concl(), want);
}

/// `⊢ ((is_universe(u) ∧ (I ∈ u ∧ S ⊆ u)) ∧ (DOM ∧ (SV ∧ ONTO))) → S ∈ u` —
/// regularity: a subset of `u` surjected onto by a member of `u` is a member.
///
/// Instantiated at constants and at a *relation symbol* `R(x,b) := rel(x,b) ∈ w`
/// that the theorem knows nothing about, so nothing about the particular shape
/// of `R` can have leaked into the derivation.
#[test]
fn the_image_of_a_member_is_a_member() {
    let mut env = Env::new();
    let (_, empty_ax) = derived::empty::empty(&mut env);

    let tu = Term::apply(env.declare(0), vec![]);
    let ti = Term::apply(env.declare(0), vec![]);
    let ts = Term::apply(env.declare(0), vec![]);
    let rel = env.declare(2);
    let tw = Term::apply(env.declare(0), vec![]);

    let (x, b, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tb) = (Term::var(x), Term::var(b));
    let r = Formula::mem(Term::apply(rel, vec![tx.clone(), tb.clone()]), tw);

    let thm = cantor::image_in_universe(&mut env, &empty_ax, &tu, &ti, &ts, x, b, &r)
        .expect("image_in_universe");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let surj = cantor::surjects_onto(&r, x, b, c, &ti, &ts).expect("the surjection package");
    let want = Formula::imp(
        Formula::and(
            Formula::and(
                uni::is_universe(&mut env, &tu),
                Formula::and(
                    Formula::mem(ti.clone(), tu.clone()),
                    kernel::thm::subset(&mut env, ts.clone(), tu.clone()),
                ),
            ),
            surj.clone(),
        ),
        Formula::mem(ts.clone(), tu.clone()),
    );
    assert_eq!(*thm.concl(), want, "image_in_universe has the wrong shape");

    // Non-vacuity: the antecedent is not the conclusion, the three clauses of
    // the surjection package are distinct, and none of them is `⊥`.
    assert_ne!(thm.concl().as_imp().expect("an implication").0, Formula::mem(ts.clone(), tu.clone()));
    let dom = cantor::r_dom(&r, x, b, &ti);
    let sv = cantor::r_sv(&r, x, b, c).expect("SV");
    let onto = cantor::r_onto(&r, x, b, &ts);
    assert_eq!(surj, Formula::and(dom.clone(), Formula::and(sv.clone(), onto.clone())));
    assert_ne!(dom, sv);
    assert_ne!(dom, onto);
    assert_ne!(sv, onto);
    // `ONTO` at a set is not `ONTO` at that set's subsets — the two targets the
    // module offers are genuinely different clauses.
    assert_ne!(onto, cantor::r_onto_subsets(&mut env, &r, x, b, &ts));

    // The two distinguished variables must differ, and must not occur in the
    // sets; a caller that breaks either is refused rather than served.
    assert!(cantor::image_in_universe(&mut env, &empty_ax, &tu, &ti, &ts, x, x, &r)
        .expect_err("the two distinguished variables coincide")
        .is_decline());
    assert!(cantor::image_in_universe(&mut env, &empty_ax, &tu, &tx, &ts, x, b, &r)
        .expect_err("a distinguished variable occurs in the sets")
        .is_decline());
}
