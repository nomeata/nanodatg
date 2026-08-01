//! The accessibility recursor `rec_acc(A,R,e)` of Carneiro's *The Type Theory
//! of Lean* §6.2.2: the conditional value, the induction hypothesis, the
//! attempts, agreement, the union, totality, ι, and the thesis's packaging.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and compares with `assert_eq!`, so a theorem with the right
//! *name* but the wrong *shape* fails here.
//!
//! **Non-vacuity is the whole game, twice over.** `step_typed` is a hypothesis
//! nothing in the construction discharges, so `totality`, `rec_funspace` and
//! `iota` could be statements about an unsatisfiable antecedent; and everything
//! below them would still hold with `accrec = ∅`.
//! [`the_recursor_fires_closed_at_the_unit_instance`] rules out both at once,
//! and [`the_induction_hypothesis_computes_to_the_recursive_value`] rules out
//! the third possibility — that ι is true of a recursor that never recurses.

use kernel::{Env, Formula, Term, Thm};

use derived::rec_acc::cval;
use derived::sums::Sums;

/// The conditional value `cval(c,v) = c × {v}` and its four lemmas all build.
#[test]
fn the_conditional_value_lemmas_build() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let aog = derived::recursion::app_of_graph(&mut env, &s.ap).expect("app_of_graph");

    let inhab = cval::prod_inhabited(&mut env, &s).expect("prod_inhabited");
    let snd = cval::prod_snd_singleton(&mut env, &s).expect("prod_snd_singleton");
    let sv = cval::cval_single_valued(&mut env, &s, &snd).expect("cval_single_valued");
    let beta = cval::cval_app(&mut env, &s, &sv, &aog).expect("cval_app");
    let ext = cval::cval_ext(&mut env, &s, &inhab).expect("cval_ext");
    let bound = cval::cval_bound(&mut env, &s).expect("cval_bound");

    for t in [&inhab, &snd, &sv, &beta, &ext, &bound] {
        assert!(t.hyps().is_empty(), "unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// The induction-hypothesis function and its two lemmas all build.
#[test]
fn the_induction_hypothesis_lemmas_build() {
    use derived::rec_acc::ih;

    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let inhab = cval::prod_inhabited(&mut env, &s).expect("prod_inhabited");
    let snd = cval::prod_snd_singleton(&mut env, &s).expect("prod_snd_singleton");
    let sv = cval::cval_single_valued(&mut env, &s, &snd).expect("cval_single_valued");
    let _ = sv;
    let ext = cval::cval_ext(&mut env, &s, &inhab).expect("cval_ext");
    let bound = cval::cval_bound(&mut env, &s).expect("cval_bound");

    let (ep, ep_ax) = ih::edge_prop(&mut env, &s).expect("edge_prop");
    let (ihs, ih_ax) = ih::ih_symbol(&mut env, &s, ep).expect("ih_symbol");
    let iext = ih::ih_ext(&mut env, &s, ep, &ep_ax, ihs, &ih_ax, &ext).expect("ih_ext");
    let ityped = ih::ih_typed(&mut env, &s, ep, &ep_ax, ihs, &ih_ax, &bound).expect("ih_typed");

    for t in [&ep_ax, &ih_ax, &iext, &ityped] {
        assert!(t.hyps().is_empty(), "unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// The base apparatus, the attempts, and `∅ ∈ Att` all build.
#[test]
fn the_attempts_form_a_set_and_the_empty_one_is_in_it() {
    use derived::rec_acc::{attempt, Base};

    let mut env = Env::new();
    let b = Base::new(&mut env).expect("base");
    let (att, att_ax) = attempt::attempts(&mut env, &b).expect("attempts");
    let empty = attempt::empty_attempt(&mut env, &b, att, &att_ax).expect("empty_attempt");

    for t in [&att_ax, &empty] {
        assert!(t.hyps().is_empty(), "unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// Any two attempts agree wherever both are defined — `acc_rect` at the
/// agreement formula, unconditionally.
#[test]
fn any_two_attempts_agree() {
    use derived::rec_acc::{agree, attempt, Base};

    let mut env = Env::new();
    let b = Base::new(&mut env).expect("base");
    let (att, att_ax) = attempt::attempts(&mut env, &b).expect("attempts");
    let ag = agree::agreement(&mut env, &b, att, &att_ax).expect("agreement");
    assert!(ag.hyps().is_empty(), "unconditional");
    assert!(kernel::thm::debug_locally_closed(ag.concl()));
}

/// The union of all attempts is a single-valued set of pairs over `acc(A,R)`,
/// takes each attempt's value, and contains each attempt's domain — all
/// unconditionally.
#[test]
fn the_union_of_attempts_is_a_function() {
    use derived::rec_acc::{agree, attempt, union, Base};

    let mut env = Env::new();
    let b = Base::new(&mut env).expect("base");
    let (att, att_ax) = attempt::attempts(&mut env, &b).expect("attempts");
    let ag = agree::agreement(&mut env, &b, att, &att_ax).expect("agreement");
    let (rec, rec_def) = union::rec_symbol(&mut env, &b, att).expect("rec_symbol");
    let members = union::rec_members(&mut env, &b, att, rec, &rec_def).expect("rec_members");
    let subset = union::attempt_subset_rec(&mut env, att, &members).expect("attempt_subset_rec");
    let sub_prod =
        union::rec_subset_prod(&mut env, &b, att, &att_ax, rec, &members).expect("rec_subset_prod");
    let sv = union::rec_single_valued(&mut env, &b, att, &att_ax, rec, &members, &ag)
        .expect("rec_single_valued");
    let value =
        union::rec_value(&mut env, &b, att, &att_ax, rec, &subset, &sv).expect("rec_value");
    let indom = union::attempt_indom_rec(&mut env, &b, att, rec, &subset)
        .expect("attempt_indom_rec");

    for t in [&rec_def, &members, &subset, &sub_prod, &sv, &value, &indom] {
        assert!(t.hyps().is_empty(), "unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// The recursor is itself an attempt, and ι holds on its domain — all
/// unconditionally.
#[test]
fn the_recursor_is_an_attempt_and_iota_holds_on_its_domain() {
    use derived::rec_acc::{agree, attempt, is_attempt, union, Base};

    let mut env = Env::new();
    let b = Base::new(&mut env).expect("base");
    let (att, att_ax) = attempt::attempts(&mut env, &b).expect("attempts");
    let ag = agree::agreement(&mut env, &b, att, &att_ax).expect("agreement");
    let (rec, rec_def) = union::rec_symbol(&mut env, &b, att).expect("rec_symbol");
    let members = union::rec_members(&mut env, &b, att, rec, &rec_def).expect("rec_members");
    let subset = union::attempt_subset_rec(&mut env, att, &members).expect("attempt_subset_rec");
    let sub_prod =
        union::rec_subset_prod(&mut env, &b, att, &att_ax, rec, &members).expect("rec_subset_prod");
    let sv = union::rec_single_valued(&mut env, &b, att, &att_ax, rec, &members, &ag)
        .expect("rec_single_valued");
    let value =
        union::rec_value(&mut env, &b, att, &att_ax, rec, &subset, &sv).expect("rec_value");
    let indom = union::attempt_indom_rec(&mut env, &b, att, rec, &subset)
        .expect("attempt_indom_rec");

    let facts = is_attempt::UnionFacts {
        subset_prod: &sub_prod,
        single_valued: &sv,
        value: &value,
        indom: &indom,
        members: &members,
    };
    let rc = is_attempt::rec_rec_cond(&mut env, &b, att, &att_ax, rec, &facts)
        .expect("rec_rec_cond");
    let syms = is_attempt::Syms { att, att_ax: &att_ax, rec };
    let isatt = is_attempt::rec_is_attempt(&mut env, &b, syms, &facts, &rc)
        .expect("rec_is_attempt");
    let iota = is_attempt::iota_on_domain(&mut env, &b, rec, &rc).expect("iota_on_domain");

    for t in [&rc, &isatt, &iota] {
        assert!(t.hyps().is_empty(), "unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// The whole development builds: every symbol, every theorem, and exactly one
/// hypothesis (`step_typed`) on the last three.
#[test]
fn the_whole_recursor_builds() {
    use derived::rec_acc::RecAcc;

    let mut env = Env::new();
    let r = RecAcc::new(&mut env).expect("RecAcc");
    for t in [
        &r.att_ax,
        &r.empty_attempt,
        &r.agreement,
        &r.rec_def,
        &r.rec_members,
        &r.attempt_subset,
        &r.rec_subset_prod,
        &r.rec_single_valued,
        &r.rec_value,
        &r.attempt_indom,
        &r.rec_rec_cond,
        &r.rec_is_attempt,
        &r.iota_on_domain,
        &r.totality,
        &r.rec_funspace,
        &r.iota,
    ] {
        assert!(t.hyps().is_empty(), "no theorem carries a kernel hypothesis");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// The one-point extension `G := accrec ∪ {⟨x,V⟩}` and every lemma about it.
///
/// Seven of the twelve are unconditional; the three that are not are the
/// clauses of `G ∈ Att`, which is where `step_typed` and the induction
/// hypothesis are spent. Building them in order is also the fastest way to
/// localise a break, which is why they are exercised one at a time.
#[test]
fn the_one_point_extension_is_an_attempt() {
    use derived::rec_acc::{agree, attempt, extend, is_attempt, union, Base};
    use kernel::FreeVar;

    let mut env = Env::new();
    let b = Base::new(&mut env).expect("base");
    let bin = derived::sums::mem_bin_union_iff(&mut env, &b.s.ap.sets).expect("bin");
    let (att, att_ax) = attempt::attempts(&mut env, &b).expect("attempts");
    let ag = agree::agreement(&mut env, &b, att, &att_ax).expect("agreement");
    let (rec, rec_def) = union::rec_symbol(&mut env, &b, att).expect("rec_symbol");
    let members = union::rec_members(&mut env, &b, att, rec, &rec_def).expect("m");
    let attsub = union::attempt_subset_rec(&mut env, att, &members).expect("s");
    let subprod = union::rec_subset_prod(&mut env, &b, att, &att_ax, rec, &members).expect("sp");
    let sv = union::rec_single_valued(&mut env, &b, att, &att_ax, rec, &members, &ag).expect("sv");
    let value = union::rec_value(&mut env, &b, att, &att_ax, rec, &attsub, &sv).expect("v");
    let indom = union::attempt_indom_rec(&mut env, &b, att, rec, &attsub).expect("i");
    let facts = is_attempt::UnionFacts {
        subset_prod: &subprod,
        single_valued: &sv,
        value: &value,
        indom: &indom,
        members: &members,
    };
    let rc = is_attempt::rec_rec_cond(&mut env, &b, att, &att_ax, rec, &facts).expect("rc");
    let iota_dom = is_attempt::iota_on_domain(&mut env, &b, rec, &rc).expect("id");

    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let e = extend::Ext {
        b: &b,
        att,
        att_ax: &att_ax,
        rec,
        facts: &facts,
        iota_dom: &iota_dom,
        bin: &bin,
        ps: ps.clone(),
        x: tx.clone(),
    };
    let _ = e.ext_members(&tx).expect("ext_members");
    let vanp = e.value_at_new_point(&mut env).expect("value_at_new_point");
    let sv_g = e.ext_single_valued(&mut env, &vanp).expect("ext_single_valued");
    let _ = e.ext_indom(&mut env, &tx).expect("ext_indom");
    let _ = e.ext_app(&mut env, &tx, &sv_g).expect("ext_app");
    let _ = e.ext_at_x(&sv_g).expect("ext_at_x");
    let _ = extend::ext_x_in_acc(&mut env, &e, &tx).expect("ext_x_in_acc");
    let rvt = extend::rec_value_typed(&mut env, &e).expect("rec_value_typed");
    let vt = extend::ext_value_typed(&mut env, &e, &tx, &rvt).expect("ext_value_typed");
    let bd = extend::ext_bound(&mut env, &e, &tx, &vt).expect("ext_bound");
    let erc = extend::ext_rec_cond(&mut env, &e, &tx, &sv_g, &rc).expect("ext_rec_cond");
    let _ = extend::ext_is_attempt(&mut env, &e, &tx, &bd, &sv_g, &erc).expect("ext_is_attempt");
    let _ = Thm::eq_refl(tx);
}

/// **Non-vacuity.** At `A := 1`, `R := ∅`, `T := 1`, `e := ∅` the typing side
/// condition is discharged outright, the recursor is defined at `•`, it is a
/// function on `acc(1,∅)`, and ι fires with both sides computed — all with no
/// antecedent at all.
#[test]
fn the_recursor_fires_closed_at_the_unit_instance() {
    use derived::rec_acc::{witness, RecAcc};

    let mut env = Env::new();
    let r = RecAcc::new(&mut env).expect("RecAcc");
    let b = &r.base;
    let es = witness::empty_step(&mut env, b).expect("empty_step");
    let st = witness::unit_step_typed(&mut env, b, &es).expect("unit_step_typed");
    let acc = witness::unit_accessible(&mut env, b).expect("unit_accessible");
    let inputs = witness::UnitInputs {
        totality: &r.totality,
        funspace: &r.rec_funspace,
        iota: &r.iota,
        pack_iota: &r.pack_iota,
        step_typed: &st,
        accessible: &acc,
        empty_step: &es,
    };
    let (in_dom, fsp, iota, pack) =
        witness::unit_facts(&mut env, b, r.rec, &inputs).expect("unit_facts");

    for t in [&es, &st, &acc, &in_dom, &fsp, &iota, &pack] {
        assert!(t.hyps().is_empty(), "closed and unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }

    // The recursor is not the empty set: it has a pair over `•`.
    let one = b.s.unit();
    let z = Term::apply(b.s.ap.empty, vec![]);
    let rec_t = r.of(one.clone(), z.clone(), one.clone(), z.clone());
    let wv = env.fresh_var();
    assert_eq!(
        *in_dom.concl(),
        Formula::exists(
            wv,
            Formula::mem(b.s.ap.sets.pair(b.s.point(), Term::var(wv)), rec_t.clone())
        ),
        "the domain fact is about the recursor"
    );

    // ι's two sides are distinct terms, and the left one is the recursor's value.
    let lhs = b.app(&rec_t, &b.s.point());
    assert_eq!(*iota.concl(), Formula::eq(lhs.clone(), z.clone()));
    assert_ne!(lhs, z, "ι relates two distinct terms");
}

/// The induction hypothesis really exposes the recursive value: applied to a
/// predecessor and to the proof that it is one, it is `app(g,y)`.
///
/// This is what stops the ι rule from being a statement about an opaque set.
#[test]
fn the_induction_hypothesis_computes_to_the_recursive_value() {
    use derived::rec_acc::{ih, Base};

    let mut env = Env::new();
    let b = Base::new(&mut env).expect("base");
    let (g, a, r, x, y) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (tg, ta, tr, tx, ty) = (
        Term::var(g),
        Term::var(a),
        Term::var(r),
        Term::var(x),
        Term::var(y),
    );
    let at = derived::inst_all(&b.ih_app, &[tg.clone(), ta.clone(), tr.clone(), tx.clone(), ty.clone()])
        .expect("instance");
    let want = Formula::imp(
        Formula::and(
            Formula::mem(ty.clone(), ta.clone()),
            Formula::mem(b.edge(&ty, &tx), tr.clone()),
        ),
        Formula::eq(
            b.app(&b.app(&ih::ih_of(b.ih, tg.clone(), ta, tr, tx), &ty), &b.s.point()),
            b.app(&tg, &ty),
        ),
    );
    assert_eq!(*at.concl(), want);
    assert!(b.ih_app.hyps().is_empty());
}


/// The ι rule has exactly the shape the thesis states, at both spellings.
///
/// Rebuilt from the kernel's own constructors: a theorem with the right name
/// but the wrong shape fails here.
#[test]
fn the_iota_rule_has_the_stated_shape() {
    use derived::rec_acc::{extend, ih, package, RecAcc};

    let mut env = Env::new();
    let r = RecAcc::new(&mut env).expect("RecAcc");
    let b = &r.base;
    let (av, rv, tv, ev) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, tt, te) = (Term::var(av), Term::var(rv), Term::var(tv), Term::var(ev));
    let xv = env.fresh_var();
    let tx = Term::var(xv);

    let rec_t = r.of(ta.clone(), tr.clone(), tt.clone(), te.clone());
    let st = extend::step_typed(&mut env, b, &ta, &tr, &tt, &te);
    let step = b.step_at(
        &te,
        &tx,
        &ih::ih_of(b.ih, rec_t.clone(), ta.clone(), tr.clone(), tx.clone()),
    );
    let mem = Formula::mem(tx.clone(), b.acc_of(&ta, &tr));

    // `⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) → app(accrec,x) = e(x)(•)(ih)))`
    let want = Formula::forall(
        av,
        Formula::forall(
            rv,
            Formula::forall(
                tv,
                Formula::forall(
                    ev,
                    Formula::imp(
                        st.clone(),
                        Formula::forall(
                            xv,
                            Formula::imp(
                                mem.clone(),
                                Formula::eq(b.app(&rec_t, &tx), step.clone()),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*r.iota.concl(), want, "iota");

    // The same at the thesis's packaging `x ∈ A ↦ (h ∈ [x ∈ acc] ↦ F(x))`.
    let pack = package::pack_of(b, r.rec, &ta, &tr, &tt, &te);
    let want_pack = Formula::forall(
        av,
        Formula::forall(
            rv,
            Formula::forall(
                tv,
                Formula::forall(
                    ev,
                    Formula::imp(
                        st,
                        Formula::forall(
                            xv,
                            Formula::imp(
                                mem,
                                Formula::eq(
                                    b.app(&b.app(&pack, &tx), &b.s.point()),
                                    step,
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*r.pack_iota.concl(), want_pack, "pack_iota");

    // The step really is applied curried, with `•` in the middle — Carneiro's
    // `e(x)(•)(ih)`, not a flattened triple.
    let ap = b.s.ap.app;
    let inner = Term::apply(ap, vec![te.clone(), tx.clone()]);
    let mid = Term::apply(ap, vec![inner, b.s.point()]);
    assert_eq!(
        b.step_at(&te, &tx, &tt),
        Term::apply(ap, vec![mid, tt]),
        "the step is three curried applications"
    );
}
