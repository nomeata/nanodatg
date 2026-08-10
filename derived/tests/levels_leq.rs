//! The `≤`-kit (`derived::levels::leq`), checked shape by shape and **computed
//! at ground instances on both sides of every split**.
//!
//! Every asserted formula is rebuilt independently from the kernel's formula
//! constructors, never read off the theorem. The ground tests use **three
//! distinct atoms** `1, 2, 3` for `union_sub`/`imax_sub` — a two-element
//! witness cannot see a dropped or swapped argument — and `imax_absorb` runs
//! on **both** sides of its guard: at `(∅, 1̄)` the guarded premise is really
//! consulted, and at `(1̄, ∅)` it is discharged vacuously even though `1̄ ⊆ ∅`
//! is false, which is the atom proving the guard is doing work (an unguarded
//! premise would make that instantiation impossible).
//!
//! # Mutation record
//!
//! Two deliberate breaks were run against this file and reverted, each
//! turning it red:
//!
//! * dropping the `¬(v = ∅)` guard from `imax_absorb`'s premise (deriving the
//!   weaker `… ∧ u ⊆ v` form, the case split's discharge step removed with
//!   it) — `exported_shapes` fails its `imax_absorb` rebuild, and
//!   `imax_absorb_computes_on_both_sides_of_the_guard` dies at the `(∅,1̄)`
//!   premise `Thm::mp` ("premise discharged"; the conjunction no longer
//!   matches), before ever reaching the `(1̄,∅)` cell, whose discharge would
//!   not exist at all since `1̄ ⊆ ∅` is false;
//! * swapping `p` and `q` in `imax_sub`'s conclusion term (building
//!   `ite0(p, ∅, q ∪ p)` instead of `ite0(q, ∅, p ∪ q)`) — the `when_zero`
//!   instantiation inside the derivation no longer matches the case split on
//!   `q = ∅`; all four tests die in `leq` itself at its `debug_assert`
//!   ("imax_sub: when_zero instantiated to an unexpected shape"), and under
//!   release asserts `leq` would return `None`, so every test dies at
//!   `expect("leq")` instead.

use derived::funcs::{or_intro_left, or_intro_right};
use derived::funspace::bin_union;
use derived::levels::ite0::{ite0, Ite0};
use derived::levels::leq::{leq, Leq};
use derived::levels::order::{order, Order};
use derived::recursion::Rec;
use derived::{a1i, and_intro, ex_falso, iff_mpr, inst_all, mp_const, syl};
use kernel::{Env, Formula, Term, Thm};

fn setup() -> (Env, Rec, Ite0, Order, Leq) {
    let mut env = Env::new();
    let r = Rec::new(&mut env).expect("Rec");
    let i = ite0(&mut env, &r.ap).expect("ite0");
    let ord = order(&mut env, &r).expect("order");
    let l = leq(&mut env, &r, &i, &ord).expect("leq");
    (env, r, i, ord, l)
}

/// `⊢ n ∈ succ(n)` — the right disjunct of the successor's membership
/// condition, discharged by reflexivity.
fn mem_succ_self(r: &Rec, n: &Term) -> Thm {
    let at = inst_all(&r.core().succ_ax, &[n.clone(), n.clone()]).expect("succ_ax");
    let inj = Thm::mp(
        &or_intro_right(Formula::mem(n.clone(), n.clone()), Formula::eq(n.clone(), n.clone())),
        &Thm::eq_refl(n.clone()),
    )
    .expect("n = n injects");
    Thm::mp(&iff_mpr(&at).expect("mpr"), &inj).expect("n ∈ succ(n)")
}

/// `⊢ z ∈ succ(n)` from `⊢ z ∈ n` — the left disjunct of the same condition.
fn widen(r: &Rec, n: &Term, mem: &Thm) -> Thm {
    let (z, _) = mem.concl().as_mem().expect("widen: not a membership");
    let at = inst_all(&r.core().succ_ax, &[n.clone(), z.clone()]).expect("succ_ax");
    let inj = Thm::mp(
        &or_intro_left(Formula::mem(z.clone(), n.clone()), Formula::eq(z, n.clone())),
        mem,
    )
    .expect("z ∈ n injects");
    Thm::mp(&iff_mpr(&at).expect("mpr"), &inj).expect("z ∈ succ(n)")
}

/// `⊢ m ⊆ n` from `⊢ m ∈ n` and the `ω`-memberships, through `sub_iff`.
fn sub_of_mem(ord: &Order, m_om: &Thm, n_om: &Thm, mem: &Thm) -> Thm {
    let (m, n) = mem.concl().as_mem().expect("sub_of_mem: not a membership");
    let iff = Thm::mp(
        &inst_all(&ord.sub_iff, &[m.clone(), n.clone()]).expect("sub_iff"),
        &and_intro(m_om, n_om),
    )
    .expect("guard discharged");
    Thm::mp(
        &iff_mpr(&iff).expect("mpr"),
        &Thm::mp(&or_intro_left(Formula::mem(m.clone(), n.clone()), Formula::eq(m, n)), mem)
            .expect("m ∈ n injects"),
    )
    .expect("m ⊆ n")
}

/// `x ∈ a` and `a = b` give `x ∈ b` (used with the equation reversed to carry
/// a membership backwards onto the `ite0` term).
fn set_rw(env: &mut Env, eq: &Thm, mem: &Thm) -> Thm {
    let (a, b) = eq.concl().as_eq().expect("set_rw: not an equation");
    let (x, _) = mem.concl().as_mem().expect("set_rw: not a membership");
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(a, b, w, Formula::mem(x, Term::var(w)));
    Thm::mp(&Thm::mp(&leib, eq).expect("set_rw"), mem).expect("set_rw")
}

/// Every exported conclusion, pinned against an independently rebuilt formula.
#[test]
fn exported_shapes() {
    let (mut env, r, i, ord, l) = setup();
    let om = r.omega();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());

    for thm in [
        &l.empty_sub,
        &l.sub_refl,
        &l.one_sub_nonzero,
        &l.union_sub,
        &l.imax_sub,
        &l.imax_absorb,
    ] {
        assert!(thm.hyps().is_empty(), "an export carries hypotheses");
        assert!(kernel::thm::debug_locally_closed(thm.concl()));
    }

    // ⊢ ∀x. ∅ ⊆ x
    let x = env.fresh_var();
    let tx = Term::var(x);
    let sub_0x = kernel::thm::subset(&mut env, zero.clone(), tx.clone());
    assert_eq!(*l.empty_sub.concl(), Formula::forall(x, sub_0x), "empty_sub has the wrong shape");

    // ⊢ ∀x. x ⊆ x
    let sub_xx = kernel::thm::subset(&mut env, tx.clone(), tx.clone());
    assert_eq!(*l.sub_refl.concl(), Formula::forall(x, sub_xx), "sub_refl has the wrong shape");

    // ⊢ ∀v. ((v ∈ ω ∧ ¬(v = ∅)) → succ(∅) ⊆ v)
    let v = env.fresh_var();
    let tv = Term::var(v);
    let sub_1v = kernel::thm::subset(&mut env, one.clone(), tv.clone());
    assert_eq!(
        *l.one_sub_nonzero.concl(),
        Formula::forall(
            v,
            Formula::imp(
                Formula::and(
                    Formula::mem(tv.clone(), om.clone()),
                    Formula::not(Formula::eq(tv.clone(), zero.clone()))
                ),
                sub_1v
            )
        ),
        "one_sub_nonzero has the wrong shape"
    );

    // ⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → (p ∪ q) ⊆ v), with `∪` the crate's one
    // binary-union spelling.
    let (p, q) = (env.fresh_var(), env.fresh_var());
    let (tp, tq) = (Term::var(p), Term::var(q));
    let bu = ord.max(tp.clone(), tq.clone());
    assert_eq!(bu, bin_union(&r.ap.sets, tp.clone(), tq.clone()), "max is not the crate's ∪");
    let sub_pv = kernel::thm::subset(&mut env, tp.clone(), tv.clone());
    let sub_qv = kernel::thm::subset(&mut env, tq.clone(), tv.clone());
    let h = Formula::and(sub_pv.clone(), sub_qv.clone());
    let sub_buv = kernel::thm::subset(&mut env, bu.clone(), tv.clone());
    assert_eq!(
        *l.union_sub.concl(),
        Formula::forall(
            p,
            Formula::forall(q, Formula::forall(v, Formula::imp(h.clone(), sub_buv)))
        ),
        "union_sub has the wrong shape"
    );

    // ⊢ ∀p ∀q ∀v. ((p ⊆ v ∧ q ⊆ v) → ite0(q, ∅, p ∪ q) ⊆ v)
    let imax_pq = i.at(tq.clone(), zero.clone(), bu.clone());
    let sub_iv = kernel::thm::subset(&mut env, imax_pq, tv.clone());
    assert_eq!(
        *l.imax_sub.concl(),
        Formula::forall(p, Formula::forall(q, Formula::forall(v, Formula::imp(h, sub_iv)))),
        "imax_sub has the wrong shape"
    );

    // ⊢ ∀u ∀v. (((u ∈ ω ∧ v ∈ ω) ∧ (¬(v = ∅) → u ⊆ v)) → ite0(v, ∅, u ∪ v) = v)
    let u = env.fresh_var();
    let tu = Term::var(u);
    let muv = ord.max(tu.clone(), tv.clone());
    let sub_uv = kernel::thm::subset(&mut env, tu.clone(), tv.clone());
    let j = Formula::and(Formula::mem(tu, om.clone()), Formula::mem(tv.clone(), om));
    let guard = Formula::imp(Formula::not(Formula::eq(tv.clone(), zero.clone())), sub_uv);
    assert_eq!(
        *l.imax_absorb.concl(),
        Formula::forall(
            u,
            Formula::forall(
                v,
                Formula::imp(
                    Formula::and(j, guard),
                    Formula::eq(i.at(tv.clone(), zero, muv), tv)
                )
            )
        ),
        "imax_absorb has the wrong shape"
    );
}

/// `sub_refl` and `one_sub_nonzero`, instantiated and computed to ground
/// membership facts: `∅ ∈ ω` through `ω ⊆ ω`, and `∅ ∈ 2̄` through `1̄ ⊆ 2̄` —
/// a lemma true of everything could not produce the latter.
#[test]
fn refl_and_one_sub_compute_to_ground_memberships() {
    let (mut env, r, _i, _ord, l) = setup();
    let core = r.core();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let two = r.succ_of(one.clone());
    let omega = r.omega();

    // `ω ⊆ ω` applied to `⊢ ∅ ∈ ω` gives `⊢ ∅ ∈ ω` back.
    let refl_om = inst_all(&l.sub_refl, std::slice::from_ref(&omega)).expect("sub_refl at ω");
    let sub_ww = kernel::thm::subset(&mut env, omega.clone(), omega.clone());
    assert_eq!(*refl_om.concl(), sub_ww);
    let apply = syl(
        &derived::imp_refl(sub_ww.clone()),
        &Thm::ax_inst(sub_ww, zero.clone()).expect("at ∅"),
    )
    .expect("chain");
    let zero_om_again =
        Thm::mp(&Thm::mp(&apply, &refl_om).expect("open"), &core.zero_mem).expect("∅ ∈ ω");
    assert_eq!(*zero_om_again.concl(), Formula::mem(zero.clone(), omega.clone()));

    // `1̄ ⊆ 2̄` from the export, then applied to `⊢ ∅ ∈ 1̄`.
    let one_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&zero)).expect("succ_closed at ∅"),
        &core.zero_mem,
    )
    .expect("1̄ ∈ ω");
    let two_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&one)).expect("succ_closed at 1̄"),
        &one_om,
    )
    .expect("2̄ ∈ ω");
    let ne2 = Thm::mp(
        &inst_all(&r.peano.succ_ne_zero, std::slice::from_ref(&one)).expect("succ_ne_zero at 1̄"),
        &one_om,
    )
    .expect("¬(2̄ = ∅)");
    let sub_12 = Thm::mp(
        &inst_all(&l.one_sub_nonzero, std::slice::from_ref(&two)).expect("one_sub_nonzero at 2̄"),
        &and_intro(&two_om, &ne2),
    )
    .expect("1̄ ⊆ 2̄");
    let want_sub = kernel::thm::subset(&mut env, one.clone(), two.clone());
    assert_eq!(*sub_12.concl(), want_sub, "1̄ ⊆ 2̄ has the wrong shape");

    let zero_in_one = mem_succ_self(&r, &zero); // ⊢ ∅ ∈ 1̄
    let at_zero = Thm::ax_inst(want_sub, zero.clone()).expect("1̄ ⊆ 2̄ at ∅");
    let out = Thm::mp(&Thm::mp(&at_zero, &sub_12).expect("open"), &zero_in_one).expect("∅ ∈ 2̄");
    assert_eq!(*out.concl(), Formula::mem(zero, two), "∅ ∈ 2̄ did not come out");
    assert!(out.hyps().is_empty());
}

/// `union_sub` and `imax_sub` at the three distinct atoms `(1̄, 2̄, 3̄)` —
/// dropping an argument, swapping `p` and `q`, or reordering the premises all
/// fail here — and computed down to the ground fact `⊢ ∅ ∈ 3̄` through the
/// bound, `imax_sub`'s route passing through the `ite0` term itself.
#[test]
fn union_sub_and_imax_sub_compute_at_three_atoms() {
    let (mut env, r, i, ord, l) = setup();
    let core = r.core();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());
    let two = r.succ_of(one.clone());
    let three = r.succ_of(two.clone());

    let one_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&zero)).expect("succ_closed"),
        &core.zero_mem,
    )
    .expect("1̄ ∈ ω");
    let two_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&one)).expect("succ_closed"),
        &one_om,
    )
    .expect("2̄ ∈ ω");
    let three_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&two)).expect("succ_closed"),
        &two_om,
    )
    .expect("3̄ ∈ ω");

    // The two premises, built through `sub_iff` from explicit memberships.
    let one_in_two = mem_succ_self(&r, &one);
    let two_in_three = mem_succ_self(&r, &two);
    let one_in_three = widen(&r, &two, &one_in_two);
    assert_eq!(*one_in_three.concl(), Formula::mem(one.clone(), three.clone()));
    let sub_13 = sub_of_mem(&ord, &one_om, &three_om, &one_in_three);
    let sub_23 = sub_of_mem(&ord, &two_om, &three_om, &two_in_three);
    let premise = and_intro(&sub_13, &sub_23);

    // `union_sub` at `(1̄, 2̄, 3̄)`: `⊢ (1̄ ∪ 2̄) ⊆ 3̄`, pinned then applied.
    let u12 = ord.max(one.clone(), two.clone());
    let sub_u12_3 = Thm::mp(
        &inst_all(&l.union_sub, &[one.clone(), two.clone(), three.clone()])
            .expect("union_sub at (1̄,2̄,3̄)"),
        &premise,
    )
    .expect("(1̄ ∪ 2̄) ⊆ 3̄");
    let want = kernel::thm::subset(&mut env, u12.clone(), three.clone());
    assert_eq!(*sub_u12_3.concl(), want, "union_sub instantiated to the wrong bound");

    // `⊢ ∅ ∈ 1̄ ∪ 2̄`, injected through the membership condition, then pushed
    // through the bound: `⊢ ∅ ∈ 3̄`.
    let zero_in_one = mem_succ_self(&r, &zero);
    let bin_at = inst_all(&ord.mem_bin_union_iff, &[one.clone(), two.clone(), zero.clone()])
        .expect("mem_bin_union_iff at (1̄,2̄,∅)");
    let zero_in_u12 = Thm::mp(
        &iff_mpr(&bin_at).expect("mpr"),
        &Thm::mp(
            &or_intro_left(
                Formula::mem(zero.clone(), one.clone()),
                Formula::mem(zero.clone(), two.clone()),
            ),
            &zero_in_one,
        )
        .expect("inject"),
    )
    .expect("∅ ∈ 1̄ ∪ 2̄");
    let at_zero = Thm::ax_inst(want, zero.clone()).expect("bound at ∅");
    let out = Thm::mp(&Thm::mp(&at_zero, &sub_u12_3).expect("open"), &zero_in_u12)
        .expect("∅ ∈ 3̄");
    assert_eq!(*out.concl(), Formula::mem(zero.clone(), three.clone()));

    // `imax_sub` at the same three atoms: `⊢ ite0(2̄, ∅, 1̄ ∪ 2̄) ⊆ 3̄`, and the
    // same ground fact through the `ite0` term: compute the term to `1̄ ∪ 2̄`
    // by the refuted guard, carry `∅ ∈ 1̄ ∪ 2̄` backwards onto it, and push it
    // through the bound.
    let t = i.at(two.clone(), zero.clone(), u12.clone());
    let sub_t3 = Thm::mp(
        &inst_all(&l.imax_sub, &[one.clone(), two.clone(), three.clone()])
            .expect("imax_sub at (1̄,2̄,3̄)"),
        &premise,
    )
    .expect("ite0(2̄, ∅, 1̄ ∪ 2̄) ⊆ 3̄");
    let want_t = kernel::thm::subset(&mut env, t.clone(), three.clone());
    assert_eq!(*sub_t3.concl(), want_t, "imax_sub instantiated to the wrong bound");

    let ne2 = Thm::mp(
        &inst_all(&r.peano.succ_ne_zero, std::slice::from_ref(&one)).expect("succ_ne_zero"),
        &one_om,
    )
    .expect("¬(2̄ = ∅)");
    let t_eq = Thm::mp(
        &inst_all(&i.when_nonzero, &[two.clone(), zero.clone(), u12.clone()])
            .expect("when_nonzero"),
        &ne2,
    )
    .expect("ite0(2̄, ∅, 1̄ ∪ 2̄) = 1̄ ∪ 2̄");
    assert_eq!(*t_eq.concl(), Formula::eq(t.clone(), u12.clone()));
    let u12_eq_t = derived::eq_symm(&mut env, &t_eq).expect("reversed");
    let zero_in_t = set_rw(&mut env, &u12_eq_t, &zero_in_u12);
    assert_eq!(*zero_in_t.concl(), Formula::mem(zero.clone(), t));
    let at_zero_t = Thm::ax_inst(want_t, zero.clone()).expect("bound at ∅");
    let out_t = Thm::mp(&Thm::mp(&at_zero_t, &sub_t3).expect("open"), &zero_in_t)
        .expect("∅ ∈ 3̄ through the ite0 term");
    assert_eq!(*out_t.concl(), Formula::mem(zero, three));
    assert!(out_t.hyps().is_empty());
}

/// The flagship on **both** sides of its guard. At `(∅, 1̄)` the guarded
/// premise is really consulted (`empty_sub` discharges it) and the conclusion
/// is the ground equation `⊢ ite0(1̄, ∅, ∅ ∪ 1̄) = 1̄`. At `(1̄, ∅)` the premise
/// is discharged **vacuously** — `1̄ ⊆ ∅` is false, so no unguarded variant
/// could be instantiated here at all — and the conclusion is
/// `⊢ ite0(∅, ∅, 1̄ ∪ ∅) = ∅`. This pair is what makes the lemma usable at
/// the corpus's `imax(1, u) = u` chains including `u = 0`.
#[test]
fn imax_absorb_computes_on_both_sides_of_the_guard() {
    let (mut env, r, i, ord, l) = setup();
    let core = r.core();
    let zero = r.zero();
    let one = r.succ_of(zero.clone());

    let one_om = Thm::mp(
        &inst_all(&core.succ_closed, std::slice::from_ref(&zero)).expect("succ_closed"),
        &core.zero_mem,
    )
    .expect("1̄ ∈ ω");

    // ── `(u, v) := (∅, 1̄)`: the guard is live ───────────────────────────────
    let guard_f = Formula::not(Formula::eq(one.clone(), zero.clone()));
    let sub_01 = inst_all(&l.empty_sub, std::slice::from_ref(&one)).expect("empty_sub at 1̄");
    let guarded = a1i(&sub_01, guard_f);
    let concl = Thm::mp(
        &inst_all(&l.imax_absorb, &[zero.clone(), one.clone()]).expect("imax_absorb at (∅,1̄)"),
        &and_intro(&and_intro(&core.zero_mem, &one_om), &guarded),
    )
    .expect("premise discharged");
    assert_eq!(
        *concl.concl(),
        Formula::eq(i.at(one.clone(), zero.clone(), ord.max(zero.clone(), one.clone())), one.clone()),
        "imax(∅, 1̄) did not come out as 1̄"
    );
    assert!(concl.hyps().is_empty());

    // ── `(u, v) := (1̄, ∅)`: the guard fires vacuously ───────────────────────
    // `1̄ ⊆ ∅` is FALSE; the premise `¬(∅ = ∅) → 1̄ ⊆ ∅` is discharged from
    // `⊢ ∅ = ∅` alone. An unguarded premise would make this cell impossible.
    let sub_10 = kernel::thm::subset(&mut env, one.clone(), zero.clone());
    let refute = mp_const(&Thm::eq_refl(zero.clone()), Formula::false_());
    let vacuous = syl(&refute, &ex_falso(sub_10)).expect("¬(∅ = ∅) → 1̄ ⊆ ∅");
    let concl0 = Thm::mp(
        &inst_all(&l.imax_absorb, &[one.clone(), zero.clone()]).expect("imax_absorb at (1̄,∅)"),
        &and_intro(&and_intro(&one_om, &core.zero_mem), &vacuous),
    )
    .expect("premise discharged vacuously");
    assert_eq!(
        *concl0.concl(),
        Formula::eq(i.at(zero.clone(), zero.clone(), ord.max(one, zero.clone())), zero),
        "imax(1̄, ∅) did not come out as ∅"
    );
    assert!(concl0.hyps().is_empty());
}
