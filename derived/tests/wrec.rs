//! The W-type recursor and its ι rule.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and pins it at **fresh constants**, so a theorem with the right
//! name and the wrong shape fails here rather than downstream.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::funcs::Apply;
use derived::wrec;
use derived::wtype::Wtype;

/// The apparatus every test needs, over one shared `Sets`.
struct Fix {
    wt: Wtype,
    comp: FnSym,
    comp_ax: Thm,
}

impl Fix {
    fn ap(&self) -> &Apply { &self.wt.sums.ap }
}

fn fixture(env: &mut Env) -> Fix {
    let sums = derived::sums::Sums::new(env).expect("sums");
    let wt = Wtype::over(env, sums).expect("wtype");
    let (comp, comp_ax) = wrec::compose(env, &wt.sums.ap).expect("comp");
    Fix { wt, comp, comp_ax }
}

/// A fresh nullary constant, so a statement mentions nothing of the module's.
fn konst(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

// ─────────────────────────────────────────────────────────────────────────────
// comp(g,f,d) = { ⟨b, g(f b)⟩ : b ∈ d }
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn composite_has_the_intended_members() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.comp_ax.concl()));

    let (tg, tf, td, tp) = (konst(&mut env), konst(&mut env), konst(&mut env), konst(&mut env));
    let at = derived::inst_all(&f.comp_ax, &[tg.clone(), tf.clone(), td.clone(), tp.clone()])
        .expect("instantiate");

    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let ap = f.ap();
    let value = ap.apply(tg.clone(), ap.apply(tf.clone(), tb.clone()));
    let want = Formula::iff(
        Formula::mem(tp.clone(), wrec::comp_of(f.comp, tg, tf, td.clone())),
        Formula::exists(
            bv,
            Formula::and(
                Formula::mem(tb.clone(), td),
                Formula::eq(tp, ap.sets.pair(tb, value)),
            ),
        ),
    );
    assert_eq!(*at.concl(), want, "comp's membership condition is not the intended one");
}

// ─────────────────────────────────────────────────────────────────────────────
// Agreement on the values determines the composite.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn composites_agree_when_the_values_do() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = wrec::compose_ext(&mut env, f.ap(), f.comp, &f.comp_ax).expect("compose_ext");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (tg, th, tf, td) = (konst(&mut env), konst(&mut env), konst(&mut env), konst(&mut env));
    let at = derived::inst_all(&thm, &[tg.clone(), th.clone(), tf.clone(), td.clone()])
        .expect("instantiate");

    let ante = wrec::agree_on(&mut env, f.ap(), &tg, &th, &tf, &td);
    let want = Formula::imp(
        ante,
        Formula::eq(
            wrec::comp_of(f.comp, tg.clone(), tf.clone(), td.clone()),
            wrec::comp_of(f.comp, th.clone(), tf.clone(), td.clone()),
        ),
    );
    assert_eq!(*at.concl(), want, "compose_ext is not the stated implication");

    // Non-vacuity: the two sides are *different terms*, so this is not
    // reflexivity wearing an antecedent.
    assert_ne!(
        wrec::comp_of(f.comp, tg, tf.clone(), td.clone()),
        wrec::comp_of(f.comp, th, tf, td),
    );
}

/// The antecedent of [`wrec::compose_ext`] is satisfiable: at `g := h` it is
/// `∀b. (b ∈ d → app(g,app(f,b)) = app(g,app(f,b)))`, which is reflexivity, so
/// the implication really does fire.
#[test]
fn the_agreement_hypothesis_is_satisfiable() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = wrec::compose_ext(&mut env, f.ap(), f.comp, &f.comp_ax).expect("compose_ext");

    let (tg, tf, td) = (konst(&mut env), konst(&mut env), konst(&mut env));
    let at = derived::inst_all(&thm, &[tg.clone(), tg.clone(), tf.clone(), td.clone()])
        .expect("instantiate");

    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let ap = f.ap();
    let val = ap.apply(tg.clone(), ap.apply(tf.clone(), tb.clone()));
    let refl = Thm::gen(
        bv,
        &derived::a1i(&Thm::eq_refl(val), Formula::mem(tb, td.clone())),
    );
    let out = Thm::mp(&at, &refl).expect("discharge the agreement");
    assert_eq!(
        *out.concl(),
        Formula::eq(
            wrec::comp_of(f.comp, tg.clone(), tf.clone(), td.clone()),
            wrec::comp_of(f.comp, tg, tf, td)
        )
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The set of attempts.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn attempts_are_separated_by_the_intended_condition() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (att, att_ax) = wrec::attempts(&mut env, &f.wt, f.comp).expect("attempts");
    assert!(kernel::thm::debug_locally_closed(att_ax.concl()));

    let (ta, tb, tu, tt, te, tg) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &att_ax,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone(), tg.clone()],
    )
    .expect("instantiate");

    let s = &f.wt.sums;
    let bound = wrec::attempt_bound(s, &f.wt, &ta, &tb, &tu, &tt);
    let cond = wrec::attempt_cond(&mut env, s, f.comp, &tb, &te, &tg);
    let want = Formula::iff(
        Formula::mem(tg.clone(), wrec::att_of(att, ta, tb, tu, tt, te)),
        Formula::and(Formula::mem(tg, bound), cond),
    );
    assert_eq!(*at.concl(), want, "Att is not carved by the attempt condition");
}

/// The recursion condition is spelled out here, independently of
/// [`wrec::rec_cond`], so that a change to the module's own builder that
/// silently altered the meaning would fail.
#[test]
fn the_recursion_condition_says_what_it_should() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (tb, te, tg) = (konst(&mut env), konst(&mut env), konst(&mut env));
    let built = wrec::rec_cond(&mut env, f.ap(), f.comp, &tb, &te, &tg);

    let ap = f.ap();
    let (av, fv, bv, y1, y2) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tf, tbb) = (Term::var(av), Term::var(fv), Term::var(bv));
    let fibre = ap.apply(tb.clone(), ta.clone());
    let w = ap.sets.pair(ta.clone(), tf.clone());

    // `∀b. (b ∈ B(a) → ∃y. ⟨app(f,b), y⟩ ∈ g)`
    let subterms = Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tbb.clone(), fibre.clone()),
            Formula::exists(
                y1,
                Formula::mem(
                    ap.sets.pair(ap.apply(tf.clone(), tbb), Term::var(y1)),
                    tg.clone(),
                ),
            ),
        ),
    );
    // `app(g,⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(g,f,B(a))⟩⟩)`
    let equation = Formula::eq(
        ap.apply(tg.clone(), w.clone()),
        ap.apply(
            te,
            ap.sets.pair(
                ta,
                ap.sets.pair(tf.clone(), wrec::comp_of(f.comp, tg.clone(), tf, fibre)),
            ),
        ),
    );
    let want = Formula::forall(
        av,
        Formula::forall(
            fv,
            Formula::imp(
                Formula::exists(y2, Formula::mem(ap.sets.pair(w, Term::var(y2)), tg)),
                Formula::and(subterms, equation),
            ),
        ),
    );
    assert_eq!(built, want, "rec_cond is not the intended formula");
}

// ─────────────────────────────────────────────────────────────────────────────
// Any two attempts agree.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole chain up to the agreement lemma, built once.
struct Chain {
    att: FnSym,
    agree: Thm,
}

fn chain(env: &mut Env, f: &Fix) -> Chain {
    let ext = wrec::compose_ext(env, f.ap(), f.comp, &f.comp_ax).expect("compose_ext");
    let (att, att_ax) = wrec::attempts(env, &f.wt, f.comp).expect("attempts");
    let agree = wrec::agreement(env, &f.wt, &ext, att, &att_ax).expect("agreement");
    Chain { att, agree }
}

#[test]
fn any_two_attempts_agree_on_the_w_type() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain(&mut env, &f);
    assert!(kernel::thm::debug_locally_closed(c.agree.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &c.agree,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");

    let s = &f.wt.sums;
    let att_t = wrec::att_of(c.att, ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone());
    let zv = env.fresh_var();
    let phi = wrec::agree_formula(&mut env, f.ap(), &att_t, zv);
    let w_t = f.wt.of(ta.clone(), tb.clone(), tu.clone());
    let want = Formula::imp(
        derived::wtype::closed(&mut env, s, &ta, &tb, &tu),
        Formula::forall(zv, Formula::imp(Formula::mem(Term::var(zv), w_t), phi)),
    );
    assert_eq!(*at.concl(), want, "the agreement lemma is not the stated one");
}

// ─────────────────────────────────────────────────────────────────────────────
// The recursor as the union of all attempts.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn the_recursor_is_the_union_of_the_attempts() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (att, _att_ax) = wrec::attempts(&mut env, &f.wt, f.comp).expect("attempts");
    let s = &f.wt.sums;
    let (rec, rec_def) = wrec::wrec_symbol(&mut env, s, att).expect("wrec");
    let members = wrec::wrec_members(&mut env, s, att, rec, &rec_def).expect("members");
    assert!(kernel::thm::debug_locally_closed(members.concl()));

    let (ta, tb, tu, tt, te, tp) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let args = [ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()];
    let at = derived::inst_all(
        &members,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone(), tp.clone()],
    )
    .expect("instantiate");

    let gv = env.fresh_var();
    let tg = Term::var(gv);
    let att_t = wrec::att_of(att, ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone());
    let want = Formula::iff(
        Formula::mem(tp.clone(), Term::apply(rec, args.to_vec())),
        Formula::exists(
            gv,
            Formula::and(Formula::mem(tg.clone(), att_t), Formula::mem(tp, tg)),
        ),
    );
    assert_eq!(*at.concl(), want, "wrec's members are not the members of the attempts");
}

#[test]
fn the_recursor_is_single_valued() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let ext = wrec::compose_ext(&mut env, f.ap(), f.comp, &f.comp_ax).expect("compose_ext");
    let (att, att_ax) = wrec::attempts(&mut env, &f.wt, f.comp).expect("attempts");
    let agree = wrec::agreement(&mut env, &f.wt, &ext, att, &att_ax).expect("agreement");
    let s = &f.wt.sums;
    let (rec, rec_def) = wrec::wrec_symbol(&mut env, s, att).expect("wrec");
    let members = wrec::wrec_members(&mut env, s, att, rec, &rec_def).expect("members");
    let sv = wrec::wrec_single_valued(&mut env, &f.wt, att, &att_ax, rec, &members, &agree)
        .expect("single-valued");
    assert!(kernel::thm::debug_locally_closed(sv.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &sv,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");
    let f_t = wrec::wrec_of(rec, ta.clone(), tb.clone(), tu.clone(), tt, te);
    let want = Formula::imp(
        derived::wtype::closed(&mut env, s, &ta, &tb, &tu),
        derived::funspace::is_single_valued(&mut env, &s.ap.sets, &f_t),
    );
    assert_eq!(*at.concl(), want, "wrec's single-valuedness is not the stated one");
}

/// The whole chain, up to the value-transfer lemma.
struct Full {
    ext: Thm,
    att: FnSym,
    att_ax: Thm,
    rec: FnSym,
    members: Thm,
    #[allow(dead_code)]
    agree: Thm,
    sv: Thm,
    subset: Thm,
    value: Thm,
    mono: Thm,
}

fn full(env: &mut Env, f: &Fix) -> Full {
    let ext = wrec::compose_ext(env, f.ap(), f.comp, &f.comp_ax).expect("compose_ext");
    let (att, att_ax) = wrec::attempts(env, &f.wt, f.comp).expect("attempts");
    let agree = wrec::agreement(env, &f.wt, &ext, att, &att_ax).expect("agreement");
    let s = &f.wt.sums;
    let (rec, rec_def) = wrec::wrec_symbol(env, s, att).expect("wrec");
    let members = wrec::wrec_members(env, s, att, rec, &rec_def).expect("members");
    let sv = wrec::wrec_single_valued(env, &f.wt, att, &att_ax, rec, &members, &agree)
        .expect("single-valued");
    let subset = wrec::attempt_subset_wrec(env, att, &members).expect("subset");
    let value = wrec::wrec_value(env, &f.wt, att, &att_ax, rec, &subset, &sv).expect("value");
    let mono = wrec::attempt_indom_wrec(env, f.ap(), att, rec, &subset).expect("mono");
    Full { ext, att, att_ax, rec, members, agree, sv, subset, value, mono }
}

#[test]
fn the_recursor_takes_each_attempts_value() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    assert!(kernel::thm::debug_locally_closed(d.value.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let args = [ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()];
    let at = derived::inst_all(&d.value, &args).expect("instantiate");

    let s = &f.wt.sums;
    let ap = f.ap();
    let (gv, xv) = (env.fresh_var(), env.fresh_var());
    let (tg, tx) = (Term::var(gv), Term::var(xv));
    let f_t = wrec::wrec_of(d.rec, ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone());
    let att_t = wrec::att_of(d.att, ta.clone(), tb.clone(), tu.clone(), tt, te);
    let want = Formula::imp(
        derived::wtype::closed(&mut env, s, &ta, &tb, &tu),
        Formula::forall(
            gv,
            Formula::imp(
                Formula::mem(tg.clone(), att_t),
                Formula::forall(
                    xv,
                    Formula::imp(
                        wrec::indom(&mut env, ap, &tg, &tx),
                        Formula::eq(ap.apply(f_t, tx.clone()), ap.apply(tg, tx)),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*at.concl(), want, "the value-transfer lemma is not the stated one");
}

#[test]
fn the_recursor_is_a_set_of_pairs_over_the_w_type() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let s = &f.wt.sums;
    let sub = wrec::wrec_subset_prod(&mut env, &f.wt, d.att, &d.att_ax, d.rec, &d.members)
        .expect("subset_prod");
    assert!(kernel::thm::debug_locally_closed(sub.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &sub,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");
    let w_t = f.wt.of(ta.clone(), tb.clone(), tu.clone());
    let f_t = wrec::wrec_of(d.rec, ta, tb, tu, tt.clone(), te);
    assert_eq!(
        *at.concl(),
        kernel::thm::subset(&mut env, f_t, s.prod.of(w_t, tt)),
        "wrec is not stated to be included in W × T"
    );
}

#[test]
fn the_recursor_satisfies_the_recursion_equation_on_its_domain() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let thm = wrec::wrec_rec_cond(
        &mut env,
        &f.wt,
        f.comp,
        &d.ext,
        d.att,
        &d.att_ax,
        d.rec,
        &d.members,
        &d.value,
        &d.mono,
    )
    .expect("rec_cond");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &thm,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");
    let f_t = wrec::wrec_of(d.rec, ta.clone(), tb.clone(), tu.clone(), tt, te.clone());
    let want = Formula::imp(
        derived::wtype::closed(&mut env, &f.wt.sums, &ta, &tb, &tu),
        wrec::rec_cond(&mut env, f.ap(), f.comp, &tb, &te, &f_t),
    );
    assert_eq!(*at.concl(), want, "wrec's recursion condition is not the stated one");
}

#[test]
fn the_recursor_is_itself_an_attempt() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let rec_cond = wrec::wrec_rec_cond(
        &mut env, &f.wt, f.comp, &d.ext, d.att, &d.att_ax, d.rec, &d.members, &d.value, &d.mono,
    )
    .expect("rec_cond");
    let sub_prod =
        wrec::wrec_subset_prod(&mut env, &f.wt, d.att, &d.att_ax, d.rec, &d.members)
            .expect("subset_prod");
    let thm = wrec::wrec_is_attempt(
        &mut env, &f.wt, &d.att_ax, d.rec, &sub_prod, &d.sv, &rec_cond,
    )
    .expect("is_attempt");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &thm,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");
    let f_t = wrec::wrec_of(d.rec, ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone());
    let att_t = wrec::att_of(d.att, ta.clone(), tb.clone(), tu.clone(), tt, te);
    assert_eq!(
        *at.concl(),
        Formula::imp(
            derived::wtype::closed(&mut env, &f.wt.sums, &ta, &tb, &tu),
            Formula::mem(f_t.clone(), att_t)
        )
    );
    // Not reflexivity in disguise: `wrec` and `Att` are different terms.
    assert_ne!(f_t, wrec::att_of(d.att, ta, tb, tu, konst(&mut env), konst(&mut env)));
}

/// Weak non-vacuity: the attempt condition is satisfiable, so `Att` is not
/// empty and the whole development is not about the empty family.
#[test]
fn the_empty_set_is_an_attempt() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (att, att_ax) = wrec::attempts(&mut env, &f.wt, f.comp).expect("attempts");
    let thm = wrec::empty_attempt(&mut env, &f.wt, f.comp, &att_ax).expect("empty attempt");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &thm,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");
    assert_eq!(
        *at.concl(),
        Formula::mem(f.wt.empty(), wrec::att_of(att, ta, tb, tu, tt, te)),
        "∅ is not stated to be an attempt"
    );
}

#[test]
fn iota_holds_wherever_the_recursor_is_defined() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let rec_cond = wrec::wrec_rec_cond(
        &mut env, &f.wt, f.comp, &d.ext, d.att, &d.att_ax, d.rec, &d.members, &d.value, &d.mono,
    )
    .expect("rec_cond");
    let iota = wrec::iota_on_domain(&mut env, &f.wt.sums, &rec_cond).expect("iota");
    assert!(kernel::thm::debug_locally_closed(iota.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &iota,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");

    let ap = f.ap();
    let f_t = wrec::wrec_of(d.rec, ta.clone(), tb.clone(), tu.clone(), tt, te.clone());
    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (tpa, tpf) = (Term::var(pa), Term::var(pf));
    let fibre = ap.apply(tb.clone(), tpa.clone());
    let w = ap.sets.pair(tpa.clone(), tpf.clone());
    let lhs = ap.apply(f_t.clone(), w.clone());
    let rhs = wrec::step_at(ap, f.comp, &te, &f_t, &tpa, &tpf, &fibre);
    let want = Formula::imp(
        derived::wtype::closed(&mut env, &f.wt.sums, &ta, &tb, &tu),
        Formula::forall(
            pa,
            Formula::forall(
                pf,
                Formula::imp(
                    wrec::indom(&mut env, ap, &f_t, &w),
                    Formula::eq(lhs.clone(), rhs.clone()),
                ),
            ),
        ),
    );
    assert_eq!(*at.concl(), want, "the guarded ι rule is not the stated one");

    // Non-vacuity of the *equation*: the two sides are distinct terms, so this
    // is not reflexivity with an antecedent painted on.
    assert_ne!(lhs, rhs, "ι would be reflexivity in disguise");
}

// ─────────────────────────────────────────────────────────────────────────────
// ι fires: the recursor computes at the unit W-type.
//
// Everything above is true of an empty recursor. These tests are what rule that
// out — see the header of `derived/src/wrec_unit.rs`.
// ─────────────────────────────────────────────────────────────────────────────

use derived::wrec_unit;

/// `⊢ ∀g ∀f. comp(g,f,∅) = ∅` — and the two sides are different terms.
#[test]
fn a_composite_over_an_empty_domain_is_empty() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = wrec_unit::comp_empty_domain(&mut env, f.ap(), f.comp, &f.comp_ax)
        .expect("comp_empty_domain");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (tg, tf) = (konst(&mut env), konst(&mut env));
    let at = derived::inst_all(&thm, &[tg.clone(), tf.clone()]).expect("instantiate");
    let e_t = f.wt.empty();
    let lhs = wrec::comp_of(f.comp, tg, tf, e_t.clone());
    assert_eq!(*at.concl(), Formula::eq(lhs.clone(), e_t.clone()));
    assert_ne!(lhs, e_t, "the composite would be ∅ by construction");
}

/// The bound hypothesis discharged and the W-type inhabited, at `U(c)`.
#[test]
fn the_unit_wtype_over_a_universe_is_inhabited() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let tc = konst(&mut env);
    let uw = wrec_unit::unit_wtype(&mut env, &f.wt, &bnd, &tc).expect("unit_wtype");
    assert!(kernel::thm::debug_locally_closed(uw.closed.concl()));
    assert!(kernel::thm::debug_locally_closed(uw.sup.concl()));

    let up = f.ap().sets.up;
    let z = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());
    let u = Term::apply(bnd.lu, vec![tc.clone()]);

    assert_eq!(
        *uw.closed.concl(),
        derived::wtype::closed(&mut env, &f.wt.sums, &sing_c, &z, &u),
        "the bound hypothesis is not the one the W-type states"
    );
    assert_eq!(
        *uw.sup.concl(),
        Formula::mem(f.wt.sup(tc, z.clone()), f.wt.of(sing_c, z, u)),
        "⟨c,∅⟩ is not stated to be in the W-type"
    );
}

/// The one-point graph really is an attempt, and its value at `⟨c,∅⟩` is `V`.
#[test]
fn the_one_point_graph_is_an_attempt() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let (tc, te) = (konst(&mut env), konst(&mut env));
    let uw = wrec_unit::unit_wtype(&mut env, &f.wt, &bnd, &tc).expect("unit_wtype");
    let u = Term::apply(bnd.lu, vec![tc.clone()]);
    let ua = wrec_unit::singleton_attempt(
        &mut env, &f.wt, f.comp, &f.comp_ax, &d.att_ax, &uw.sup, &tc, &u, &te,
    )
    .expect("singleton_attempt");
    assert!(kernel::thm::debug_locally_closed(ua.att.concl()));
    assert!(kernel::thm::debug_locally_closed(ua.value.concl()));

    let ap = f.ap();
    let up = ap.sets.up;
    let z = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());
    let v = ap.apply(te.clone(), ap.sets.pair(tc.clone(), ap.sets.pair(z.clone(), z.clone())));
    let t_t = derived::singleton(up, v.clone());
    let w0 = f.wt.sup(tc.clone(), z.clone());
    let g = derived::singleton(up, ap.sets.pair(w0.clone(), v.clone()));

    assert_eq!(
        *ua.att.concl(),
        Formula::mem(g.clone(), wrec::att_of(d.att, sing_c, z, u, t_t, te)),
        "the one-point graph is not stated to be an attempt"
    );
    // The attempt is non-empty, and its value there is the step's — computed.
    let lhs = ap.apply(g, w0);
    assert_eq!(*ua.value.concl(), Formula::eq(lhs.clone(), v.clone()));
    assert_ne!(lhs, v, "the attempt's value would be reflexivity in disguise");
}

/// **ι fires.**
///
/// ```text
/// ⊢ app(wrec({c}, ∅, U(c), {V}, e), ⟨c,∅⟩) = app(e, ⟨c, ⟨∅,∅⟩⟩)
/// ```
///
/// Both sides computed, at fresh constants `c` and `e`, with no hypothesis
/// left. This is the theorem that stops every other statement in `wrec` from
/// being vacuously true of `wrec = ∅`.
#[test]
fn iota_fires_at_the_unit_wtype() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let (tc, te) = (konst(&mut env), konst(&mut env));

    let thm = wrec_unit::iota_fires(
        &mut env, &f.wt, &bnd, f.comp, &f.comp_ax, &d.att_ax, d.rec, &d.value, &tc, &te,
    )
    .expect("ι fires");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ap = f.ap();
    let up = ap.sets.up;
    let z = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());
    let u = Term::apply(bnd.lu, vec![tc.clone()]);
    let v = ap.apply(te.clone(), ap.sets.pair(tc.clone(), ap.sets.pair(z.clone(), z.clone())));
    let t_t = derived::singleton(up, v.clone());
    let w0 = f.wt.sup(tc.clone(), z.clone());
    let lhs = ap.apply(wrec::wrec_of(d.rec, sing_c, z, u, t_t, te.clone()), w0);

    assert_eq!(
        *thm.concl(),
        Formula::eq(lhs.clone(), v.clone()),
        "ι does not compute to the step's value"
    );

    // Non-vacuity, twice over. The equation is not reflexivity: its two sides
    // are different terms. And it is *unconditional* — no `closed`, no
    // `indom` — so it is not an implication whose antecedent might be empty.
    assert_ne!(lhs, v, "ι would be reflexivity in disguise");
    assert!(thm.concl().as_imp().is_none(), "ι fires only under a hypothesis");
    assert!(thm.concl().as_eq().is_some(), "ι is not an equation");
}

/// **The recursor has a member**, at the same instance — the set-level form of
/// the same non-vacuity.
#[test]
fn the_recursor_is_not_empty() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let (tc, te) = (konst(&mut env), konst(&mut env));
    let uw = wrec_unit::unit_wtype(&mut env, &f.wt, &bnd, &tc).expect("unit_wtype");
    let u = Term::apply(bnd.lu, vec![tc.clone()]);
    let ua = wrec_unit::singleton_attempt(
        &mut env, &f.wt, f.comp, &f.comp_ax, &d.att_ax, &uw.sup, &tc, &u, &te,
    )
    .expect("singleton_attempt");
    let thm = wrec_unit::wrec_member(&f.wt, &bnd, d.rec, &d.subset, &ua, &tc, &te)
        .expect("wrec_member");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ap = f.ap();
    let up = ap.sets.up;
    let z = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());
    let v = ap.apply(te.clone(), ap.sets.pair(tc.clone(), ap.sets.pair(z.clone(), z.clone())));
    let t_t = derived::singleton(up, v.clone());
    let w0 = f.wt.sup(tc.clone(), z.clone());
    assert_eq!(
        *thm.concl(),
        Formula::mem(
            ap.sets.pair(w0, v),
            wrec::wrec_of(d.rec, sing_c, z, u, t_t, te)
        ),
        "the recursor is not stated to contain the one point"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The composite is a function — the lemma totality needs.
// ─────────────────────────────────────────────────────────────────────────────

use derived::wrec_typing;

/// `⊢ ∀g ∀f ∀d ∀x ∀y. (⟨x,y⟩ ∈ comp(g,f,d) → y = app(g, app(f,x)))`.
#[test]
fn the_composite_has_the_values_replacement_put_there() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = wrec_typing::composite_value(&mut env, f.ap(), f.comp, &f.comp_ax)
        .expect("composite_value");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (tg, tf, td, tx, ty) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &thm,
        &[tg.clone(), tf.clone(), td.clone(), tx.clone(), ty.clone()],
    )
    .expect("instantiate");
    let ap = f.ap();
    let want = Formula::imp(
        Formula::mem(
            ap.sets.pair(tx.clone(), ty.clone()),
            wrec::comp_of(f.comp, tg.clone(), tf.clone(), td),
        ),
        Formula::eq(ty.clone(), ap.apply(tg, ap.apply(tf, tx))),
    );
    assert_eq!(*at.concl(), want, "composite_value is not the stated implication");
}

/// `⊢ ∀g ∀f ∀d. sv(comp(g,f,d))`, pinned against the very formula
/// `is_single_valued` builds.
#[test]
fn the_composite_is_single_valued() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = wrec_typing::composite_single_valued(&mut env, f.ap(), f.comp, &f.comp_ax)
        .expect("composite_single_valued");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (tg, tf, td) = (konst(&mut env), konst(&mut env), konst(&mut env));
    let at = derived::inst_all(&thm, &[tg.clone(), tf.clone(), td.clone()]).expect("instantiate");
    let c_t = wrec::comp_of(f.comp, tg, tf, td);
    let sets = f.ap().sets.clone();
    let want = derived::funspace::is_single_valued(&mut env, &sets, &c_t);
    assert_eq!(*at.concl(), want, "composite_single_valued is not `sv(comp(g,f,d))`");
}

/// **The composite computes**:
/// `⊢ ∀g ∀f ∀d ∀b. (b ∈ d → app(comp(g,f,d), b) = app(g, app(f,b)))`.
///
/// The lemma `Bool.rec` never needed and `N.rec` cannot avoid — see
/// [`derived::wrec_typing::composite_app`]. Pinned at fresh constants, with the
/// two sides checked to be different terms.
#[test]
fn the_composite_computes() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm =
        wrec_typing::composite_app(&mut env, f.ap(), f.comp, &f.comp_ax).expect("composite_app");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (tg, tf, td, tb) =
        (konst(&mut env), konst(&mut env), konst(&mut env), konst(&mut env));
    let at = derived::inst_all(&thm, &[tg.clone(), tf.clone(), td.clone(), tb.clone()])
        .expect("instantiate");
    let ap = f.ap();
    let c_t = wrec::comp_of(f.comp, tg.clone(), tf.clone(), td.clone());
    let lhs = ap.apply(c_t, tb.clone());
    let rhs = ap.apply(tg, ap.apply(tf, tb.clone()));
    assert_ne!(lhs, rhs, "the equation would be reflexivity");
    assert_eq!(
        *at.concl(),
        Formula::imp(Formula::mem(tb, td), Formula::eq(lhs, rhs)),
        "composite_app is not the stated equation"
    );
}

/// The instance `N.rec` needs, with the antecedent **discharged**: at the
/// `succ` fibre `1 = {•}` the subterm family is the one-point graph
/// `{⟨•,n⟩}`, and the composite's value at `•` is the recursive call
/// `app(g, n)`.
///
/// This is the exact shape [`derived::wrec_total`]'s ι rule produces for a
/// constructor with one recursive argument, and it is why
/// [`derived::wrec_unit::comp_empty_domain`] — which collapses the composite to
/// `∅` and was all `Bool` needed — does not suffice here.
#[test]
fn the_composite_at_a_one_point_fibre_is_the_recursive_call() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm =
        wrec_typing::composite_app(&mut env, f.ap(), f.comp, &f.comp_ax).expect("composite_app");
    let pf = derived::point_fun::PointFun::over(&mut env, &f.wt.sums, &f.wt.app_pair)
        .expect("point_fun");

    let (tg, tn) = (konst(&mut env), konst(&mut env));
    let (point, one) = (f.wt.sums.point(), f.wt.sums.unit());
    let ap = f.ap();
    let graph = derived::singleton(ap.sets.up, ap.sets.pair(point.clone(), tn.clone()));

    let at = derived::inst_all(
        &thm,
        &[tg.clone(), graph.clone(), one.clone(), point.clone()],
    )
    .expect("instantiate");
    // `• ∈ 1` discharges the antecedent outright.
    let fired = Thm::mp(&at, &f.wt.sums.unit_mem).expect("• ∈ 1");

    // …and `app({⟨•,n⟩}, •) = n` rewrites the recursive call into its intended
    // shape, so the conclusion mentions `n` rather than an application.
    let point_app =
        derived::inst_all(&pf.app, &[point.clone(), tn.clone()]).expect("point_app");
    let want = Formula::eq(
        ap.apply(wrec::comp_of(f.comp, tg.clone(), graph.clone(), one), point.clone()),
        ap.apply(tg.clone(), ap.apply(graph.clone(), point.clone())),
    );
    assert_eq!(*fired.concl(), want, "the composite does not compute at the one-point fibre");

    let app_sym = ap.app;
    let inner = ap.apply(graph.clone(), point.clone());
    let congr = derived::congr_arg(&mut env, app_sym, &[tg.clone(), inner], 1, &point_app)
        .expect("congruence on the recursive call");
    let rewritten = derived::eq_trans(&mut env, &fired, &congr).expect("rewrite");
    assert_eq!(
        rewritten.concl().as_eq().expect("an equation").1,
        ap.apply(tg, tn),
        "the composite's value at • is not the recursive call app(g,n)"
    );
}

/// `⊢ ∀g ∀f ∀d ∀T. ((∀b ∈ d. app(g,app(f,b)) ∈ T) → comp(g,f,d) ∈ fs(d,T))`,
/// and the hypothesis discharged at `d := ∅`, where it is vacuous — so the
/// implication really fires.
#[test]
fn the_composite_is_a_function_into_any_set_its_values_land_in() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = wrec_typing::composite_typed(&mut env, &f.wt.sums, f.comp, &f.comp_ax)
        .expect("composite_typed");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (tg, tf, td, tt) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(&thm, &[tg.clone(), tf.clone(), td.clone(), tt.clone()])
        .expect("instantiate");

    let ap = f.ap();
    let s = &f.wt.sums;
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let ante = Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tb.clone(), td.clone()),
            Formula::mem(ap.apply(tg.clone(), ap.apply(tf.clone(), tb.clone())), tt.clone()),
        ),
    );
    let want = Formula::imp(
        ante,
        Formula::mem(
            wrec::comp_of(f.comp, tg.clone(), tf.clone(), td.clone()),
            s.fs.of(td, tt.clone()),
        ),
    );
    assert_eq!(*at.concl(), want, "composite_typed is not the stated implication");

    // Non-vacuity: at `d := ∅` the hypothesis is vacuous, so the conclusion is
    // unconditional. `comp(g,f,∅) ∈ fs(∅,T)` for arbitrary `g`, `f` and `T`.
    let e_t = f.wt.empty();
    let at_e = derived::inst_all(&thm, &[tg.clone(), tf.clone(), e_t.clone(), tt.clone()])
        .expect("instantiate at ∅");
    let vacuous = Thm::gen(
        bv,
        &derived::syl(
            &derived::inst_all(&ap.empty_ax, std::slice::from_ref(&tb)).expect("∅ is empty"),
            &derived::ex_falso(Formula::mem(
                ap.apply(tg.clone(), ap.apply(tf.clone(), tb)),
                tt.clone(),
            )),
        )
        .expect("ex falso"),
    );
    let out = Thm::mp(&at_e, &vacuous).expect("discharge the typing hypothesis");
    assert_eq!(
        *out.concl(),
        Formula::mem(
            wrec::comp_of(f.comp, tg, tf, e_t.clone()),
            s.fs.of(e_t, tt)
        ),
        "the composite over an empty domain is not stated to be a function"
    );
}

/// `⊢ closed(A,B,u) → ∀x. (indom(wrec,x) → app(wrec,x) ∈ T)`, and the same
/// statement **discharged** at the unit instance — where the antecedent is
/// known to hold, so the conclusion is a fact and not a promise.
#[test]
fn the_recursors_values_lie_in_the_target() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let sub_prod = wrec::wrec_subset_prod(&mut env, &f.wt, d.att, &d.att_ax, d.rec, &d.members)
        .expect("subset_prod");
    let thm = wrec_typing::wrec_value_typed(&mut env, &f.wt, d.rec, &sub_prod, &d.sv)
        .expect("wrec_value_typed");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &thm,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");
    let ap = f.ap();
    let f_t = wrec::wrec_of(d.rec, ta.clone(), tb.clone(), tu.clone(), tt.clone(), te);
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let want = Formula::imp(
        derived::wtype::closed(&mut env, &f.wt.sums, &ta, &tb, &tu),
        Formula::forall(
            xv,
            Formula::imp(
                wrec::indom(&mut env, ap, &f_t, &tx),
                Formula::mem(ap.apply(f_t.clone(), tx), tt),
            ),
        ),
    );
    assert_eq!(*at.concl(), want, "wrec_value_typed is not the stated implication");

    // ── Discharged, at the instance where ι fires ───────────────────────────
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let (tc, te2) = (konst(&mut env), konst(&mut env));
    let uw = wrec_unit::unit_wtype(&mut env, &f.wt, &bnd, &tc).expect("unit_wtype");
    let u = Term::apply(bnd.lu, vec![tc.clone()]);
    let ua = wrec_unit::singleton_attempt(
        &mut env, &f.wt, f.comp, &f.comp_ax, &d.att_ax, &uw.sup, &tc, &u, &te2,
    )
    .expect("singleton_attempt");
    let member = wrec_unit::wrec_member(&f.wt, &bnd, d.rec, &d.subset, &ua, &tc, &te2)
        .expect("wrec_member");

    let up = ap.sets.up;
    let z = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());
    let v = ap.apply(te2.clone(), ap.sets.pair(tc.clone(), ap.sets.pair(z.clone(), z.clone())));
    let t_unit = derived::singleton(up, v.clone());
    let w0 = f.wt.sup(tc.clone(), z.clone());
    let rec_t = wrec::wrec_of(d.rec, sing_c.clone(), z.clone(), u.clone(), t_unit.clone(), te2.clone());

    let at_unit = Thm::mp(
        &derived::inst_all(&thm, &[sing_c, z, u, t_unit.clone(), te2]).expect("instantiate"),
        &uw.closed,
    )
    .expect("discharge closed");
    let yv = env.fresh_var();
    let in_dom = Thm::mp(
        &derived::exists_intro_imp(
            yv,
            Formula::mem(ap.sets.pair(w0.clone(), Term::var(yv)), rec_t.clone()),
            v.clone(),
        )
        .expect("∃-intro"),
        &member,
    )
    .expect("the recursor's domain contains ⟨c,∅⟩");
    let out = Thm::mp(
        &derived::inst_all(&at_unit, std::slice::from_ref(&w0)).expect("instantiate"),
        &in_dom,
    )
    .expect("discharge indom");
    assert_eq!(
        *out.concl(),
        Formula::mem(ap.apply(rec_t, w0), t_unit),
        "the recursor's value at ⟨c,∅⟩ is not stated to be in the target"
    );
}

/// `⊢ closed → ∀a ∀f. ((∀b ∈ B(a). indom(wrec, app(f,b)))
///                        → comp(wrec,f,B(a)) ∈ fs(B(a),T))` — the bridge from
/// the induction hypothesis of step 4 to the typing premise on the step.
#[test]
fn the_recursors_composite_is_a_function_into_the_target() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let d = full(&mut env, &f);
    let sub_prod = wrec::wrec_subset_prod(&mut env, &f.wt, d.att, &d.att_ax, d.rec, &d.members)
        .expect("subset_prod");
    let vt = wrec_typing::wrec_value_typed(&mut env, &f.wt, d.rec, &sub_prod, &d.sv)
        .expect("wrec_value_typed");
    let ct = wrec_typing::composite_typed(&mut env, &f.wt.sums, f.comp, &f.comp_ax)
        .expect("composite_typed");
    let thm = wrec_typing::wrec_composite_typed(&mut env, &f.wt, f.comp, d.rec, &vt, &ct)
        .expect("wrec_composite_typed");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (ta, tb, tu, tt, te) = (
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
        konst(&mut env),
    );
    let at = derived::inst_all(
        &thm,
        &[ta.clone(), tb.clone(), tu.clone(), tt.clone(), te.clone()],
    )
    .expect("instantiate");

    let ap = f.ap();
    let s = &f.wt.sums;
    let f_t = wrec::wrec_of(d.rec, ta.clone(), tb.clone(), tu.clone(), tt.clone(), te);
    let (pa, pf, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, tbv) = (Term::var(pa), Term::var(pf), Term::var(bv));
    let fibre = ap.apply(tb.clone(), tpa.clone());
    let ih = Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tbv.clone(), fibre.clone()),
            wrec::indom(&mut env, ap, &f_t, &ap.apply(tpf.clone(), tbv)),
        ),
    );
    let want = Formula::imp(
        derived::wtype::closed(&mut env, s, &ta, &tb, &tu),
        Formula::forall(
            pa,
            Formula::forall(
                pf,
                Formula::imp(
                    ih,
                    Formula::mem(
                        wrec::comp_of(f.comp, f_t.clone(), tpf, fibre.clone()),
                        s.fs.of(fibre, tt),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*at.concl(), want, "wrec_composite_typed is not the stated implication");
}
