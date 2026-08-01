//! The accessibility recursor `rec_acc(A,R,T,e)`.

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
    let _ = (Formula::false_(), Term::var(env.fresh_var()), Thm::eq_refl(Term::var(env.fresh_var())));
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
    let isatt = is_attempt::rec_is_attempt(&mut env, &b, att, &att_ax, rec, &sub_prod, &sv, &rc)
        .expect("rec_is_attempt");
    let iota = is_attempt::iota_on_domain(&mut env, &b, rec, &rc).expect("iota_on_domain");

    for t in [&rc, &isatt, &iota] {
        assert!(t.hyps().is_empty(), "unconditional");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}
