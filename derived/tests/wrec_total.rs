//! Totality of the W-type recursor, the one-point extension it runs on, and
//! the ι rule with its guard discharged.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and pins it at **fresh constants**.

use kernel::{Env, Formula, Term};

use derived::wrec_extend;
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;

/// The W-type and the whole recursor chain, over one shared `Sets`.
struct Fix {
    wt: Wtype,
    r: Recursor,
}

fn fixture(env: &mut Env) -> Fix {
    let sums = derived::sums::Sums::new(env).expect("sums");
    let wt = Wtype::over(env, sums).expect("wtype");
    let r = Recursor::new(env, &wt).expect("recursor");
    Fix { wt, r }
}

/// A fresh nullary constant, so a statement mentions nothing of the module's.
fn konst(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

/// Seven fresh constants: `A`, `B`, `u`, `T`, `e`, `a`, `f`.
fn seven(env: &mut Env) -> Vec<Term> { (0..7).map(|_| konst(env)).collect() }

#[test]
fn the_one_point_extension_is_single_valued() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let ext = wrec_extend::extension(&mut env, &f.wt, &f.r).expect("extension");
    let thm = ext.sv;
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ts = seven(&mut env);
    let at = derived::inst_all(&thm, &ts).expect("instantiate");

    let s = &f.wt.sums;
    let k = wrec_extend::hypothesis(&mut env, &f.wt, &f.r, &ts[0..5], &ts[5], &ts[6]);
    let g = wrec_extend::ext_of(s, &f.r, &ts[0..5], &ts[5], &ts[6]);
    let want = Formula::imp(
        k,
        derived::funspace::is_single_valued(&mut env, &s.ap.sets, &g),
    );
    assert_eq!(*at.concl(), want, "the extension's single-valuedness is not the stated one");
}

#[test]
fn the_one_point_extension_lies_in_the_product() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let ext = wrec_extend::extension(&mut env, &f.wt, &f.r).expect("extension");
    let thm = ext.in_pow;
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ts = seven(&mut env);
    let at = derived::inst_all(&thm, &ts).expect("instantiate");

    let s = &f.wt.sums;
    let k = wrec_extend::hypothesis(&mut env, &f.wt, &f.r, &ts[0..5], &ts[5], &ts[6]);
    let g = wrec_extend::ext_of(s, &f.r, &ts[0..5], &ts[5], &ts[6]);
    let w_t = f.wt.of(ts[0].clone(), ts[1].clone(), ts[2].clone());
    let want = Formula::imp(
        k,
        Formula::mem(g, Term::apply(s.pow, vec![s.prod.of(w_t, ts[3].clone())])),
    );
    assert_eq!(*at.concl(), want, "the extension's inclusion is not the stated one");
}

#[test]
fn the_one_point_extension_satisfies_the_recursion_condition() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let ext = wrec_extend::extension(&mut env, &f.wt, &f.r).expect("extension");
    let thm = ext.rec_cond;
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ts = seven(&mut env);
    let at = derived::inst_all(&thm, &ts).expect("instantiate");

    let s = &f.wt.sums;
    let k = wrec_extend::hypothesis(&mut env, &f.wt, &f.r, &ts[0..5], &ts[5], &ts[6]);
    let g = wrec_extend::ext_of(s, &f.r, &ts[0..5], &ts[5], &ts[6]);
    let want = Formula::imp(
        k,
        derived::wrec::rec_cond(&mut env, &s.ap, f.r.comp, &ts[1], &ts[4], &g),
    );
    assert_eq!(*at.concl(), want, "the extension's recursion condition is not the stated one");
}

#[test]
fn the_one_point_extension_puts_the_new_point_in_the_domain() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let ext = wrec_extend::extension(&mut env, &f.wt, &f.r).expect("extension");
    assert!(kernel::thm::debug_locally_closed(ext.attempt.concl()));
    assert!(kernel::thm::debug_locally_closed(ext.indom.concl()));

    let ts = seven(&mut env);
    let s = &f.wt.sums;
    let k = wrec_extend::hypothesis(&mut env, &f.wt, &f.r, &ts[0..5], &ts[5], &ts[6]);
    let g = wrec_extend::ext_of(s, &f.r, &ts[0..5], &ts[5], &ts[6]);

    let att = derived::inst_all(&ext.attempt, &ts).expect("instantiate");
    assert_eq!(
        *att.concl(),
        Formula::imp(
            k.clone(),
            Formula::mem(g, f.r.att_of(&ts[0], &ts[1], &ts[2], &ts[3], &ts[4]))
        ),
        "the extension is not stated to be an attempt"
    );

    let ind = derived::inst_all(&ext.indom, &ts).expect("instantiate");
    let rec_t = f.r.of(&ts[0], &ts[1], &ts[2], &ts[3], &ts[4]);
    let w0 = s.ap.sets.pair(ts[5].clone(), ts[6].clone());
    assert_eq!(
        *ind.concl(),
        Formula::imp(k, derived::wrec::indom(&mut env, &s.ap, &rec_t, &w0)),
        "the induction step is not the stated one"
    );
}

#[test]
fn the_recursor_is_defined_everywhere_on_the_wtype() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let ext = wrec_extend::extension(&mut env, &f.wt, &f.r).expect("extension");
    let thm = derived::wrec_total::totality(&mut env, &f.wt, &f.r, &ext).expect("totality");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ts: Vec<Term> = (0..5).map(|_| konst(&mut env)).collect();
    let at = derived::inst_all(&thm, &ts).expect("instantiate");

    let s = &f.wt.sums;
    let rec_t = f.r.of(&ts[0], &ts[1], &ts[2], &ts[3], &ts[4]);
    let w_t = f.wt.of(ts[0].clone(), ts[1].clone(), ts[2].clone());
    let zv = env.fresh_var();
    let want = Formula::imp(
        derived::wrec_total::premise(&mut env, &f.wt, &ts),
        Formula::forall(
            zv,
            Formula::imp(
                Formula::mem(Term::var(zv), w_t),
                derived::wrec::indom(&mut env, &s.ap, &rec_t, &Term::var(zv)),
            ),
        ),
    );
    assert_eq!(*at.concl(), want, "totality is not the stated implication");
}

/// The whole chain, once, so the four consequences share one recursor.
struct Chain {
    ext: derived::wrec_extend::Extension,
    total: kernel::Thm,
}

fn chain(env: &mut Env, f: &Fix) -> Chain {
    let ext = wrec_extend::extension(env, &f.wt, &f.r).expect("extension");
    let total = derived::wrec_total::totality(env, &f.wt, &f.r, &ext).expect("totality");
    Chain { ext, total }
}

#[test]
fn the_recursor_is_a_function_into_the_target() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain(&mut env, &f);
    let thm = derived::wrec_total::wrec_funspace(&mut env, &f.wt, &f.r, &c.total)
        .expect("wrec_funspace");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ts: Vec<Term> = (0..5).map(|_| konst(&mut env)).collect();
    let at = derived::inst_all(&thm, &ts).expect("instantiate");

    let s = &f.wt.sums;
    let rec_t = f.r.of(&ts[0], &ts[1], &ts[2], &ts[3], &ts[4]);
    let w_t = f.wt.of(ts[0].clone(), ts[1].clone(), ts[2].clone());
    let want = Formula::imp(
        derived::wrec_total::premise(&mut env, &f.wt, &ts),
        Formula::mem(rec_t, s.fs.of(w_t, ts[3].clone())),
    );
    assert_eq!(*at.concl(), want, "the function-space statement is not the stated one");
    let _ = c.ext;
}

#[test]
fn iota_holds_at_every_constructor() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain(&mut env, &f);
    let thm = derived::wrec_total::iota(&mut env, &f.wt, &f.r, &c.total).expect("iota");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let ts: Vec<Term> = (0..5).map(|_| konst(&mut env)).collect();
    let at = derived::inst_all(&thm, &ts).expect("instantiate");

    let s = &f.wt.sums;
    let ap = &s.ap;
    let rec_t = f.r.of(&ts[0], &ts[1], &ts[2], &ts[3], &ts[4]);
    let w_t = f.wt.of(ts[0].clone(), ts[1].clone(), ts[2].clone());
    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(pa), Term::var(pf));
    let fibre = ap.apply(ts[1].clone(), ta.clone());
    let body = Formula::imp(
        Formula::and(
            Formula::mem(ta.clone(), ts[0].clone()),
            Formula::mem(tf.clone(), s.fs.of(fibre.clone(), w_t)),
        ),
        Formula::eq(
            ap.apply(rec_t.clone(), ap.sets.pair(ta.clone(), tf.clone())),
            derived::wrec::step_at(ap, f.r.comp, &ts[4], &rec_t, &ta, &tf, &fibre),
        ),
    );
    let want = Formula::imp(
        derived::wrec_total::premise(&mut env, &f.wt, &ts),
        Formula::forall(pa, Formula::forall(pf, body)),
    );
    assert_eq!(*at.concl(), want, "the iota rule is not the stated one");

    // Non-vacuity of the *equation*: the two sides are different terms, so this
    // cannot be reflexivity wearing an antecedent.
    let lhs = ap.apply(rec_t.clone(), ap.sets.pair(ta.clone(), tf.clone()));
    let rhs = derived::wrec::step_at(ap, f.r.comp, &ts[4], &rec_t, &ta, &tf, &fibre);
    assert_ne!(lhs, rhs);
    let _ = c.ext;
}

// ─────────────────────────────────────────────────────────────────────────────
// Non-vacuity: the hypothesis is satisfiable, and discharging it gives an
// unconditional theorem.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ step_typed({c}, ∅, U(c), {V}, e)` — the hypothesis of [`totality`],
/// [`wrec_funspace`] and [`iota`] is not one no five sets satisfy.
#[test]
fn the_step_typing_hypothesis_is_satisfiable() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let (tc, te) = (konst(&mut env), konst(&mut env));
    let thm = derived::wrec_unit::unit_step_typed(&mut env, &f.wt, &bnd, &tc, &te)
        .expect("unit_step_typed");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let s = &f.wt.sums;
    let up = s.ap.sets.up;
    let z = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());
    let u = Term::apply(bnd.lu, vec![tc.clone()]);
    let v = s.ap.apply(
        te.clone(),
        s.ap.sets.pair(tc.clone(), s.ap.sets.pair(z.clone(), z.clone())),
    );
    let t_t = derived::singleton(up, v);
    let want =
        derived::wrec_total::step_typed(&mut env, s, &f.wt, &sing_c, &z, &u, &t_t, &te);
    assert_eq!(*thm.concl(), want, "the discharged hypothesis is not step_typed");
}

/// The premise of [`wrec_funspace`] discharged outright, leaving
/// `⊢ wrec({c},∅,U(c),{V},e) ∈ fs(W({c},∅,U(c)), {V})` with no antecedent.
#[test]
fn the_recursor_is_unconditionally_a_function_at_the_unit_instance() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain(&mut env, &f);
    let fs_thm = derived::wrec_total::wrec_funspace(&mut env, &f.wt, &f.r, &c.total)
        .expect("wrec_funspace");
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let (tc, te) = (konst(&mut env), konst(&mut env));
    let thm =
        derived::wrec_unit::unit_funspace(&mut env, &f.wt, &bnd, f.r.rec, &fs_thm, &tc, &te)
            .expect("unit_funspace");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let s = &f.wt.sums;
    let up = s.ap.sets.up;
    let z = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());
    let u = Term::apply(bnd.lu, vec![tc.clone()]);
    let v = s.ap.apply(
        te.clone(),
        s.ap.sets.pair(tc.clone(), s.ap.sets.pair(z.clone(), z.clone())),
    );
    let t_t = derived::singleton(up, v);
    let rec_t = f.r.of(&sing_c, &z, &u, &t_t, &te);
    let want = Formula::mem(rec_t, s.fs.of(f.wt.of(sing_c, z, u), t_t));
    assert_eq!(*thm.concl(), want, "the unit instance's function-space claim is wrong");

    // And it really is unconditional: the conclusion is a membership, not an
    // implication.
    assert!(thm.concl().as_imp().is_none(), "a hypothesis survived");
    let _ = c.ext;
}

/// The general ι rule, fired at the unit instance, is **literally** the
/// equation [`derived::wrec_unit::iota_fires`] proves by hand.
#[test]
fn the_general_iota_agrees_with_the_hand_built_instance() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain(&mut env, &f);
    let iota = derived::wrec_total::iota(&mut env, &f.wt, &f.r, &c.total).expect("iota");
    let bnd = derived::bound::Bound::new(&mut env, &f.wt).expect("bound");
    let (tc, te) = (konst(&mut env), konst(&mut env));

    let general = derived::wrec_unit::unit_iota(
        &mut env, &f.wt, &bnd, f.r.comp, &f.r.comp_ax, f.r.rec, &iota, &tc, &te,
    )
    .expect("unit_iota");
    let by_hand = derived::wrec_unit::iota_fires(
        &mut env, &f.wt, &bnd, f.r.comp, &f.r.comp_ax, &f.r.att_ax, f.r.rec, &f.r.value, &tc,
        &te,
    )
    .expect("iota_fires");

    assert_eq!(
        general.concl(),
        by_hand.concl(),
        "the general recursor and the hand-built instance compute differently"
    );
    assert!(general.concl().as_imp().is_none(), "a hypothesis survived");

    // Both sides are computed, and they are different terms.
    let s = &f.wt.sums;
    let ap = &s.ap;
    let z = f.wt.empty();
    let v = ap.apply(te.clone(), ap.sets.pair(tc.clone(), ap.sets.pair(z.clone(), z.clone())));
    let sing_c = derived::singleton(ap.sets.up, tc.clone());
    let u = Term::apply(bnd.lu, vec![tc.clone()]);
    let t_t = derived::singleton(ap.sets.up, v.clone());
    let rec_t = f.r.of(&sing_c, &z, &u, &t_t, &te);
    let lhs = ap.apply(rec_t, f.wt.sup(tc, z));
    assert_eq!(*general.concl(), Formula::eq(lhs.clone(), v.clone()));
    assert_ne!(lhs, v);
    let _ = c.ext;
}
