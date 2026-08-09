//! The order theory of `ω` (`derived::levels::order`), checked shape by shape.
//!
//! Every test pins the **exact** conclusion of the lemma it covers, rebuilt
//! independently from the kernel's formula constructors. The concrete-pair
//! test additionally runs `max` on `(1, 2)` — the arguments in the "wrong"
//! order for a lazy proof — and forces `1 ∪ 2 = 2` out of the exported
//! theorems, so `max` really computes the maximum and not a projection.

use derived::funcs::or_intro_right;
use derived::funspace::bin_union;
use derived::levels::order::{order, Order};
use derived::recursion::Rec;
use derived::{
    a1i, and_elim_right, and_intro, ex_falso, hyp_or_elim, iff_mpr, imp_refl, inst_all, mpd_const,
    syl,
};
use kernel::{Env, Formula, Term, Thm};

fn setup() -> (Env, Rec, Order) {
    let mut env = Env::new();
    let r = Rec::new(&mut env).expect("Rec");
    let ord = order(&mut env, &r).expect("order");
    (env, r, ord)
}

/// Each exported conclusion, pinned against an independently rebuilt formula.
#[test]
fn exported_shapes() {
    let (mut env, r, ord) = setup();
    let om = r.omega();
    let zero = r.zero();

    let (m, n, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, tn, tz) = (Term::var(m), Term::var(n), Term::var(z));
    let m_om = Formula::mem(tm.clone(), om.clone());
    let n_om = Formula::mem(tn.clone(), om.clone());
    let j = Formula::and(m_om.clone(), n_om.clone());
    let bu = ord.max(tm.clone(), tn.clone());
    assert_eq!(bu, bin_union(&r.ap.sets, tm.clone(), tn.clone()), "max is not the crate's ∪");

    for thm in [
        &ord.trichotomy,
        &ord.cases,
        &ord.sub_iff,
        &ord.max_in_omega,
        &ord.max_ub,
        &ord.max_absorb,
        &ord.zero_least,
        &ord.succ_mono_mem,
        &ord.mem_bin_union_iff,
    ] {
        assert!(thm.hyps().is_empty(), "an export carries hypotheses");
        assert!(kernel::thm::debug_locally_closed(thm.concl()));
    }

    // ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n ∨ (m = n ∨ n ∈ m)))
    let d = Formula::or(
        Formula::mem(tm.clone(), tn.clone()),
        Formula::or(Formula::eq(tm.clone(), tn.clone()), Formula::mem(tn.clone(), tm.clone())),
    );
    assert_eq!(
        *ord.trichotomy.concl(),
        Formula::forall(m, Formula::forall(n, Formula::imp(j.clone(), d))),
        "trichotomy has the wrong shape"
    );

    // ⊢ ∀n. (n ∈ ω → (n = ∅ ∨ ∃m. (m ∈ ω ∧ n = succ(m))))
    let mv = env.fresh_var();
    let tmv = Term::var(mv);
    let ex = Formula::exists(
        mv,
        Formula::and(
            Formula::mem(tmv.clone(), om.clone()),
            Formula::eq(tn.clone(), r.succ_of(tmv)),
        ),
    );
    assert_eq!(
        *ord.cases.concl(),
        Formula::forall(
            n,
            Formula::imp(n_om.clone(), Formula::or(Formula::eq(tn.clone(), zero.clone()), ex))
        ),
        "cases has the wrong shape"
    );

    // ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ⊆ n ↔ (m ∈ n ∨ m = n)))
    let sub = kernel::thm::subset(&mut env, tm.clone(), tn.clone());
    let ab = Formula::or(Formula::mem(tm.clone(), tn.clone()), Formula::eq(tm.clone(), tn.clone()));
    assert_eq!(
        *ord.sub_iff.concl(),
        Formula::forall(
            m,
            Formula::forall(n, Formula::imp(j.clone(), Formula::iff(sub, ab)))
        ),
        "sub_iff has the wrong shape"
    );

    // ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∪ n) ∈ ω)
    assert_eq!(
        *ord.max_in_omega.concl(),
        Formula::forall(
            m,
            Formula::forall(n, Formula::imp(j.clone(), Formula::mem(bu.clone(), om.clone())))
        ),
        "max_in_omega has the wrong shape"
    );

    // ⊢ ∀m ∀n. (m ⊆ (m ∪ n) ∧ n ⊆ (m ∪ n)) — unconditional.
    let sub_m_bu = kernel::thm::subset(&mut env, tm.clone(), bu.clone());
    let sub_n_bu = kernel::thm::subset(&mut env, tn.clone(), bu.clone());
    assert_eq!(
        *ord.max_ub.concl(),
        Formula::forall(m, Formula::forall(n, Formula::and(sub_m_bu, sub_n_bu))),
        "max_ub has the wrong shape"
    );

    // ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → ((m ∪ n) = m ∨ (m ∪ n) = n))
    assert_eq!(
        *ord.max_absorb.concl(),
        Formula::forall(
            m,
            Formula::forall(
                n,
                Formula::imp(
                    j.clone(),
                    Formula::or(
                        Formula::eq(bu.clone(), tm.clone()),
                        Formula::eq(bu.clone(), tn.clone())
                    )
                )
            )
        ),
        "max_absorb has the wrong shape"
    );

    // ⊢ ∀n. (n ∈ ω → (∅ ∈ n ∨ ∅ = n))
    assert_eq!(
        *ord.zero_least.concl(),
        Formula::forall(
            n,
            Formula::imp(
                n_om,
                Formula::or(
                    Formula::mem(zero.clone(), tn.clone()),
                    Formula::eq(zero.clone(), tn.clone())
                )
            )
        ),
        "zero_least has the wrong shape"
    );

    // ⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (m ∈ n → succ(m) ∈ succ(n)))
    assert_eq!(
        *ord.succ_mono_mem.concl(),
        Formula::forall(
            m,
            Formula::forall(
                n,
                Formula::imp(
                    j.clone(),
                    Formula::imp(
                        Formula::mem(tm.clone(), tn.clone()),
                        Formula::mem(r.succ_of(tm.clone()), r.succ_of(tn.clone()))
                    )
                )
            )
        ),
        "succ_mono_mem has the wrong shape"
    );

    // ⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))
    assert_eq!(
        *ord.mem_bin_union_iff.concl(),
        Formula::forall(
            m,
            Formula::forall(
                n,
                Formula::forall(
                    z,
                    Formula::iff(
                        Formula::mem(tz.clone(), bin_union(&r.ap.sets, tm.clone(), tn.clone())),
                        Formula::or(Formula::mem(tz.clone(), tm), Formula::mem(tz, tn))
                    )
                )
            )
        ),
        "mem_bin_union_iff has the wrong shape"
    );

    // The case principle instantiates cleanly at `∅`, left disjunct shape.
    let at_zero = inst_all(&ord.cases, std::slice::from_ref(&zero)).expect("cases at ∅");
    let (guard, disj) = at_zero.concl().as_imp().expect("cases at ∅ is an implication");
    assert_eq!(guard, Formula::mem(zero.clone(), om));
    let mv2 = env.fresh_var();
    let tmv2 = Term::var(mv2);
    assert_eq!(
        disj,
        Formula::or(
            Formula::eq(zero.clone(), zero.clone()),
            Formula::exists(
                mv2,
                Formula::and(
                    Formula::mem(tmv2.clone(), r.omega()),
                    Formula::eq(zero, r.succ_of(tmv2))
                )
            )
        ),
        "cases at ∅ does not open to the expected disjunction"
    );
}

/// `max` on the concrete pair `(1, 2)`: from `max_absorb`, `max_ub` and an
/// explicitly derived `⊢ 1 ∈ 2`, force `⊢ 1 ∪ 2 = 2`.
#[test]
fn max_on_a_concrete_pair() {
    let (mut env, r, ord) = setup();
    let core = r.core();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let two = r.succ_of(one.clone());

    // `1 ∈ ω` and `2 ∈ ω`, from the base point and closure.
    let one_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&zero)).expect("succ_closed at ∅"),
        &core.zero_mem,
    )
    .expect("1 ∈ ω");
    let two_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&one)).expect("succ_closed at 1"),
        &one_om,
    )
    .expect("2 ∈ ω");

    // `⊢ 1 ∈ 2`, explicitly: the right disjunct of `1 ∈ succ(1) ↔ (1 ∈ 1 ∨ 1 = 1)`.
    let succ_at = inst_all(&core.succ_ax, &[one.clone(), one.clone()]).expect("succ_ax at (1,1)");
    let right = Thm::mp(
        &or_intro_right(
            Formula::mem(one.clone(), one.clone()),
            Formula::eq(one.clone(), one.clone()),
        ),
        &Thm::eq_refl(one.clone()),
    )
    .expect("1 = 1 injects");
    let one_in_two = Thm::mp(&iff_mpr(&succ_at).expect("mpr"), &right).expect("1 ∈ 2");
    assert_eq!(*one_in_two.concl(), Formula::mem(one.clone(), two.clone()));

    // `max_absorb` at `(1, 2)`.
    let disj = Thm::mp(
        &inst_all(&ord.max_absorb, &[one.clone(), two.clone()]).expect("max_absorb at (1,2)"),
        &and_intro(&one_om, &two_om),
    )
    .expect("1∪2 = 1 ∨ 1∪2 = 2");
    let u12 = ord.max(one.clone(), two.clone());
    let e1 = Formula::eq(u12.clone(), one.clone());
    let e2 = Formula::eq(u12.clone(), two.clone());
    assert_eq!(*disj.concl(), Formula::or(e1.clone(), e2.clone()));

    // Refute the left disjunct: `1∪2 = 1` plus `2 ⊆ 1∪2` gives `2 ⊆ 1`, which
    // sends `1 ∈ 2` to `1 ∈ 1` against Regularity.
    let sub2 = and_elim_right(&inst_all(&ord.max_ub, &[one.clone(), two.clone()]).expect("max_ub"))
        .expect("2 ⊆ 1∪2");
    let hole = env.fresh_var();
    let zv = env.fresh_var();
    let tzv = Term::var(zv);
    let sub_hole = Formula::forall(
        zv,
        Formula::imp(
            Formula::mem(tzv.clone(), two.clone()),
            Formula::mem(tzv, Term::var(hole)),
        ),
    );
    let leib = Thm::eq_leibniz(u12.clone(), one.clone(), hole, sub_hole);
    let to_sub21 = mpd_const(&leib, &sub2).expect("e1 → 2 ⊆ 1");
    let sub21 = kernel::thm::subset(&mut env, two.clone(), one.clone());
    let sub_at_one = Thm::ax_inst(sub21, one.clone()).expect("2⊆1 at 1");
    let e1_one_one = mpd_const(&syl(&to_sub21, &sub_at_one).expect("chain"), &one_in_two)
        .expect("e1 → 1 ∈ 1");
    let no_self_one =
        inst_all(&r.peano.no_self_mem, std::slice::from_ref(&one)).expect("¬(1 ∈ 1)");
    let e1_e2 = syl(
        &syl(&e1_one_one, &no_self_one).expect("e1 → ⊥"),
        &ex_falso(e2.clone()),
    )
    .expect("e1 → e2");

    let or_f = Formula::or(e1, e2.clone());
    let elim = hyp_or_elim(
        &imp_refl(or_f.clone()),
        &a1i(&e1_e2, or_f.clone()),
        &a1i(&imp_refl(e2), or_f),
    )
    .expect("or-elim");
    let max12 = Thm::mp(&elim, &disj).expect("1∪2 = 2");
    assert_eq!(
        *max12.concl(),
        Formula::eq(ord.max(one, two.clone()), two),
        "max(1,2) did not come out as 2"
    );
}
