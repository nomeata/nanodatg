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

// ─────────────────────────────────────────────────────────────────────────────
// The house rule. A `Thm` is a sequent `Γ ⊢ φ`; this module's header says
// "everything up to and including the guarded ι rule is unconditional", "`ST`
// is the only hypothesis", and — of the four unit witnesses — "**every one of
// these has no antecedent at all**". An antecedent spelled out inside `concl()`
// is honest; a formula in `hyps()` is the undeclared one, and `Thm::mp` puts it
// there without a word.
// ─────────────────────────────────────────────────────────────────────────────

/// `{scope} ⊢ φ` from `⊢ φ`, with `concl()` untouched — the shape a
/// conclusion-only pin cannot see.
fn under_scope(env: &mut Env, t: &Thm) -> Thm {
    let scope = Formula::mem(Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let out = Thm::mp(&derived::a1i(t, scope.clone()), &Thm::assume(scope.clone()))
        .expect("weaken into the scope");
    assert_eq!(*out.concl(), *t.concl());
    assert_eq!(out.hyps(), &[scope]);
    out
}

/// [`Base::over`] refuses an `Acc` carrying a hypothetical theorem — **all
/// seven fields**, not the four the recursion happens to read.
///
/// The guard used to cover `acc_ax`, `acc_subset`, `acc_induction` and
/// `acc_intro` only, while its doc claimed all seven. The gap was reachable:
/// `Acc`'s fields are `pub`, `empty_relation` is read nowhere else, and
/// `witness::unit_accessible` consumed it with a conclusion-only pin — so a
/// `Thm::assume(∀A. acc(A,∅) = A)` walked through `Base::over`, was never
/// touched by `RecAcc::over`, and came back out of `witness::unit_facts` inside
/// all four theorems the hub calls closed.
///
/// The `Sums` half is here for the same reason: `rec_acc` reads nine of its
/// `⊢ …` fields, `Base` is the boundary at which they enter, and none of them
/// was checked either.
#[test]
fn the_base_refuses_an_apparatus_with_any_hypothetical_theorem() {
    use derived::acc::Acc;
    use derived::rec_acc::Base;

    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let ac = Acc::with_apply(&mut env, &s.ap).expect("acc");
    assert!(ac.all_unconditional());
    assert!(Base::over(&mut env, s.clone(), ac.clone()).is_some());

    for which in 0..7 {
        let mut bad = ac.clone();
        {
            let f: &mut Thm = match which {
                0 => &mut bad.empty_ax,
                1 => &mut bad.acc_ax,
                2 => &mut bad.acc_subset,
                3 => &mut bad.acc_induction,
                4 => &mut bad.acc_intro,
                5 => &mut bad.minimal,
                _ => &mut bad.empty_relation,
            };
            *f = Thm::assume(f.concl().clone());
        }
        assert!(!bad.all_unconditional(), "Acc field {which}");
        assert!(
            Base::over(&mut env, s.clone(), bad).is_none(),
            "Base::over accepted a hypothetical Acc field {which}"
        );
    }

    // And the nine `Sums` theorems this module reads.
    for which in 0..9 {
        let mut bad = s.clone();
        {
            let f: &mut Thm = match which {
                0 => &mut bad.pow_ax,
                1 => &mut bad.pair_in_prod,
                2 => &mut bad.unit_mem,
                3 => &mut bad.prod.prod_ax,
                4 => &mut bad.fs.fs_ax,
                5 => &mut bad.ap.empty_ax,
                6 => &mut bad.ap.mem_sing,
                7 => &mut bad.ap.pair_inj,
                _ => &mut bad.ap.sets.un_ax,
            };
            *f = Thm::assume(f.concl().clone());
        }
        assert!(
            Base::over(&mut env, bad, ac.clone()).is_none(),
            "Base::over accepted a hypothetical Sums field {which}"
        );
    }
}

/// The seven theorems `unit_facts` instantiates, as one view.
fn unit_inputs<'a>(
    r: &'a derived::rec_acc::RecAcc,
    accessible: &'a Thm,
    step: &'a Thm,
    st: &'a Thm,
) -> derived::rec_acc::UnitInputs<'a> {
    derived::rec_acc::UnitInputs {
        totality: &r.totality,
        funspace: &r.rec_funspace,
        iota: &r.iota,
        pack_iota: &r.pack_iota,
        step_typed: st,
        accessible,
        empty_step: step,
    }
}

/// The four unit witnesses refuse a hypothetical input, at both ends of the
/// path the seven-field gap opened.
///
/// `Base::over` is not the only door: `Base`'s fields are `pub` too, so
/// `witness::unit_accessible` gets a `derived::establishes` pin of its own, and
/// `witness::unit_facts` checks all seven of its inputs. Without them, a `Γ` on
/// `empty_relation` — or on any one of the seven theorems `unit_facts` consumes
/// — was threaded into *all four* returns, each still labelled "closed and
/// unconditional".
#[test]
fn the_unit_witnesses_refuse_a_hypothetical_input() {
    use derived::rec_acc::{witness, RecAcc};

    let mut env = Env::new();
    let r = RecAcc::new(&mut env).expect("recacc");
    let b = r.base.clone();

    let step = witness::empty_step(&mut env, &b).expect("empty_step");
    let st = witness::unit_step_typed(&mut env, &b, &step).expect("unit_step_typed");
    let acc_pt = witness::unit_accessible(&mut env, &b).expect("unit_accessible");
    let (d, f, i, p) =
        witness::unit_facts(&mut env, &b, r.rec, &unit_inputs(&r, &acc_pt, &step, &st))
            .expect("unit_facts");
    for t in [&d, &f, &i, &p] {
        assert!(t.hyps().is_empty(), "closed and unconditional");
    }

    // 1. A `Γ` on `Acc::empty_relation`, reached past `Base::over` by writing
    //    the `pub` field directly. `unit_accessible`'s pin now reads `hyps()`.
    let mut poisoned = b.clone();
    poisoned.ac.empty_relation = Thm::assume(b.ac.empty_relation.concl().clone());
    assert!(witness::unit_accessible(&mut env, &poisoned).is_none());
    assert!(witness::empty_step(&mut env, &poisoned).is_none());
    assert!(witness::unit_step_typed(&mut env, &poisoned, &step).is_none());
    assert!(witness::unit_facts(
        &mut env,
        &poisoned,
        r.rec,
        &unit_inputs(&r, &acc_pt, &step, &st)
    )
    .is_none());

    // 2. A `Γ` on any one of `unit_facts`' own seven inputs. The three it takes
    //    loose first…
    let hyp_acc = under_scope(&mut env, &acc_pt);
    let hyp_step = under_scope(&mut env, &step);
    let hyp_st = under_scope(&mut env, &st);
    for inp in [
        unit_inputs(&r, &hyp_acc, &step, &st),
        unit_inputs(&r, &acc_pt, &hyp_step, &st),
        unit_inputs(&r, &acc_pt, &step, &hyp_st),
    ] {
        assert!(!inp.all_unconditional());
        assert!(witness::unit_facts(&mut env, &b, r.rec, &inp).is_none());
    }
    // …then the four general theorems it instantiates.
    let hyps: Vec<Thm> = [&r.totality, &r.rec_funspace, &r.iota, &r.pack_iota]
        .iter()
        .map(|t| under_scope(&mut env, t))
        .collect();
    for (slot, hyp) in hyps.iter().enumerate() {
        let mut inp = unit_inputs(&r, &acc_pt, &step, &st);
        match slot {
            0 => inp.totality = hyp,
            1 => inp.funspace = hyp,
            2 => inp.iota = hyp,
            _ => inp.pack_iota = hyp,
        }
        assert!(!inp.all_unconditional(), "slot {slot}");
        assert!(
            witness::unit_facts(&mut env, &b, r.rec, &inp).is_none(),
            "unit_facts accepted a hypothetical input {slot}"
        );
    }
}

/// `cval::cval_app`'s advertised equation — the whole consequent — is read off
/// the caller's `app_of_graph` by one `syl`. Everything the function derives is
/// the *antecedent*. So the final shape is pinned in **release**, not only under
/// `debug_assert`: CI's sweeps run in debug, but `scripts/arena.sh`, the
/// `stepcount` binary and `cargo build --release` do not.
///
/// The confusable premise is a genuine unconditional theorem with exactly
/// `app_of_graph`'s antecedent and a different consequent — the shape
/// `∀f ∀a ∀b. ((sv(f) ∧ ⟨a,b⟩ ∈ f) → C(f,a,b))` the audit names — so nothing
/// before the pin can refuse it.
#[test]
fn the_conditional_value_beta_rule_pins_its_equation_in_release() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let aog = derived::recursion::app_of_graph(&mut env, &s.ap).expect("app_of_graph");
    let snd = cval::prod_snd_singleton(&mut env, &s).expect("prod_snd_singleton");
    let sv = cval::cval_single_valued(&mut env, &s, &snd).expect("cval_single_valued");
    assert!(cval::cval_app(&mut env, &s, &sv, &aog).is_some());

    // `C(f,a,b) := sv(f) ∧ ⟨a,b⟩ ∈ f` — same antecedent, different consequent.
    let (fv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tb) = (Term::var(fv), Term::var(av), Term::var(bv));
    let sv_f = derived::funspace::is_single_valued(&mut env, &s.ap.sets, &tf);
    let pair_in = Formula::mem(s.ap.sets.pair(ta, tb), tf);
    let conj = Formula::and(sv_f, pair_in);
    let bogus = derived::gen_all(&[fv, av, bv], &derived::imp_refl(conj));
    assert!(bogus.hyps().is_empty(), "a real theorem, just the wrong one");
    assert!(cval::cval_app(&mut env, &s, &sv, &bogus).is_none());

    // The hypothesis leg, at both premises.
    let hyp_sv = under_scope(&mut env, &sv);
    let hyp_aog = under_scope(&mut env, &aog);
    assert!(cval::cval_app(&mut env, &s, &hyp_sv, &aog).is_none());
    assert!(cval::cval_app(&mut env, &s, &sv, &hyp_aog).is_none());
}

/// `attempt::empty_attempt`'s claim is the *set* `∅` is shown to be in, and that
/// set comes from the left-hand side of the caller's biconditional: `iff_mpr`
/// hands back whatever membership was there. So the final shape is pinned in
/// **release**.
///
/// The confusable premise here is not contrived — `attempt::attempts` mints a
/// fresh symbol per call, so calling it twice gives two genuine, unconditional
/// biconditionals with the *same* right-hand side and different left-hand
/// sides. Feeding one symbol's axiom alongside the other symbol is exactly the
/// "foreign `∀…(g ∈ FOO ↔ same-RHS)`" the audit describes.
#[test]
fn the_empty_attempt_pins_the_set_it_belongs_to_in_release() {
    use derived::rec_acc::{attempt, Base};

    let mut env = Env::new();
    let b = Base::new(&mut env).expect("base");
    let (att1, ax1) = attempt::attempts(&mut env, &b).expect("attempts");
    let (att2, ax2) = attempt::attempts(&mut env, &b).expect("attempts again");
    assert_ne!(att1, att2);

    // Matched pairs build; crossed ones do not.
    assert!(attempt::empty_attempt(&mut env, &b, att1, &ax1).is_some());
    assert!(attempt::empty_attempt(&mut env, &b, att2, &ax2).is_some());
    assert!(attempt::empty_attempt(&mut env, &b, att1, &ax2).is_none());
    assert!(attempt::empty_attempt(&mut env, &b, att2, &ax1).is_none());

    // And the hypothesis leg.
    let hyp = under_scope(&mut env, &ax1);
    assert!(attempt::empty_attempt(&mut env, &b, att1, &hyp).is_none());
}

/// `witness::unit_facts` returns four theorems and used to pin only two.
///
/// Returns 3 and 4 (`app(F,•) = ∅` and its packaged form) were compared with a
/// rebuilt equation; returns 1 and 2 were compared with nothing, in either
/// profile. `in_dom` is whatever `inp.totality`'s inner consequent happens to
/// be, and `fsp` is whatever `inp.funspace` concludes once `ST` is discharged —
/// so a `funspace` of shape `ST → anything` handed "anything" back under the
/// label `F ∈ fs(acc(1,∅),1)`.
///
/// The two wrong inputs below are not junk: each is another *real* theorem of
/// this very development with the right outer shape, which is precisely the
/// confusion a label is supposed to prevent.
#[test]
fn the_unit_facts_pin_all_four_returns_in_release() {
    use derived::rec_acc::{witness, RecAcc, UnitInputs};

    let mut env = Env::new();
    let r = RecAcc::new(&mut env).expect("recacc");
    let b = r.base.clone();
    let step = witness::empty_step(&mut env, &b).expect("empty_step");
    let st = witness::unit_step_typed(&mut env, &b, &step).expect("unit_step_typed");
    let accessible = witness::unit_accessible(&mut env, &b).expect("unit_accessible");

    let good = unit_inputs(&r, &accessible, &step, &st);
    assert!(witness::unit_facts(&mut env, &b, r.rec, &good).is_some());

    // `iota` in the `totality` slot: `ST → ∀x. (x ∈ acc(A,R) → …)` either way,
    // so the derivation runs — return 1 came out as the ι equation labelled
    // "the recursor is defined at `•`".
    let wrong_totality = UnitInputs { totality: &r.iota, ..unit_inputs(&r, &accessible, &step, &st) };
    assert!(witness::unit_facts(&mut env, &b, r.rec, &wrong_totality).is_none());

    // `totality` in the `funspace` slot: `ST → …` either way, so return 2 came
    // out as `∀z. (z ∈ acc(1,∅) → indom(F,z))` labelled `F ∈ fs(acc(1,∅),1)`.
    let wrong_funspace =
        UnitInputs { funspace: &r.totality, ..unit_inputs(&r, &accessible, &step, &st) };
    assert!(witness::unit_facts(&mut env, &b, r.rec, &wrong_funspace).is_none());
}

/// Every public constructor in `derived::rec_acc` that takes a `&Thm` refuses a
/// premise carrying a `Γ`, and still accepts the same theorem once it is
/// discharged — so the guards are refusing the *sequent*, not the statement.
///
/// One pass over the whole layered build, poisoning one input at each rung.
/// None of these was checked before: the twenty-odd constructors here pinned
/// conclusions and never read `hyps()`, so a single hypothetical premise
/// anywhere in the chain surfaced in `iota`, in `pack_iota` and in the closed
/// unit witnesses alike.
#[test]
fn every_recursor_entry_refuses_a_hypothetical_premise() {
    use derived::rec_acc::{
        agree, attempt, extend, ih, is_attempt, package, total, union, Base, RecAcc, Syms,
        UnionFacts,
    };

    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let b = Base::new(&mut env).expect("base");

    // ── cval and ih ─────────────────────────────────────────────────────────
    let inhab = cval::prod_inhabited(&mut env, &s).expect("prod_inhabited");
    let snd = cval::prod_snd_singleton(&mut env, &s).expect("prod_snd_singleton");
    let sv = cval::cval_single_valued(&mut env, &s, &snd).expect("cval_single_valued");
    let cext = cval::cval_ext(&mut env, &s, &inhab).expect("cval_ext");
    let cbound = cval::cval_bound(&mut env, &s).expect("cval_bound");
    let hyp_snd = under_scope(&mut env, &snd);
    let hyp_inhab = under_scope(&mut env, &inhab);
    assert!(cval::cval_single_valued(&mut env, &s, &hyp_snd).is_none());
    assert!(cval::cval_ext(&mut env, &s, &hyp_inhab).is_none());

    let (ep, ep_ax) = ih::edge_prop(&mut env, &s).expect("edge_prop");
    let (ihs, ih_ax) = ih::ih_symbol(&mut env, &s, ep).expect("ih_symbol");
    let hyp_ep = under_scope(&mut env, &ep_ax);
    let hyp_ih = under_scope(&mut env, &ih_ax);
    let hyp_cext = under_scope(&mut env, &cext);
    let hyp_cbound = under_scope(&mut env, &cbound);
    assert!(ih::ih_ext(&mut env, &s, ep, &hyp_ep, ihs, &ih_ax, &cext).is_none());
    assert!(ih::ih_ext(&mut env, &s, ep, &ep_ax, ihs, &hyp_ih, &cext).is_none());
    assert!(ih::ih_ext(&mut env, &s, ep, &ep_ax, ihs, &ih_ax, &hyp_cext).is_none());
    assert!(ih::ih_typed(&mut env, &s, ep, &hyp_ep, ihs, &ih_ax, &cbound).is_none());
    assert!(ih::ih_typed(&mut env, &s, ep, &ep_ax, ihs, &ih_ax, &hyp_cbound).is_none());

    let value = ih::ih_value(&mut env, &s, ep, ihs, &ih_ax).expect("ih_value");
    assert!(ih::ih_value(&mut env, &s, ep, ihs, &hyp_ih).is_none());
    let hyp_value = under_scope(&mut env, &value);
    assert!(ih::ih_single_valued(&mut env, &s, ihs, &hyp_value).is_none());
    let ihsv = ih::ih_single_valued(&mut env, &s, ihs, &value).expect("ih_single_valued");
    let aog = derived::recursion::app_of_graph(&mut env, &s.ap).expect("aog");
    let capp = cval::cval_app(&mut env, &s, &sv, &aog).expect("cval_app");
    let hyp_ihsv = under_scope(&mut env, &ihsv);
    let hyp_capp = under_scope(&mut env, &capp);
    assert!(ih::ih_app(&mut env, &s, ep, &ep_ax, ihs, &ih_ax, &hyp_ihsv, &capp).is_none());
    assert!(ih::ih_app(&mut env, &s, ep, &ep_ax, ihs, &ih_ax, &ihsv, &hyp_capp).is_none());
    assert!(ih::ih_app(&mut env, &s, ep, &ep_ax, ihs, &ih_ax, &ihsv, &capp).is_some());

    // ── the recursor, one rung at a time ────────────────────────────────────
    let (att, att_ax) = attempt::attempts(&mut env, &b).expect("attempts");
    let hyp_att = under_scope(&mut env, &att_ax);
    assert!(agree::agreement(&mut env, &b, att, &hyp_att).is_none());
    let ag = agree::agreement(&mut env, &b, att, &att_ax).expect("agreement");
    let hyp_ag = under_scope(&mut env, &ag);

    let (rec, rec_def) = union::rec_symbol(&mut env, &b, att).expect("rec_symbol");
    let hyp_def = under_scope(&mut env, &rec_def);
    assert!(union::rec_members(&mut env, &b, att, rec, &hyp_def).is_none());
    let members = union::rec_members(&mut env, &b, att, rec, &rec_def).expect("rec_members");
    let hyp_members = under_scope(&mut env, &members);
    assert!(union::attempt_subset_rec(&mut env, att, &hyp_members).is_none());
    let subset = union::attempt_subset_rec(&mut env, att, &members).expect("attempt_subset_rec");
    assert!(union::rec_subset_prod(&mut env, &b, att, &hyp_att, rec, &members).is_none());
    assert!(union::rec_subset_prod(&mut env, &b, att, &att_ax, rec, &hyp_members).is_none());
    let sub_prod =
        union::rec_subset_prod(&mut env, &b, att, &att_ax, rec, &members).expect("subset_prod");
    assert!(
        union::rec_single_valued(&mut env, &b, att, &att_ax, rec, &members, &hyp_ag).is_none()
    );
    let recsv = union::rec_single_valued(&mut env, &b, att, &att_ax, rec, &members, &ag)
        .expect("rec_single_valued");
    let hyp_recsv = under_scope(&mut env, &recsv);
    assert!(union::rec_value(&mut env, &b, att, &att_ax, rec, &subset, &hyp_recsv).is_none());
    let value_thm =
        union::rec_value(&mut env, &b, att, &att_ax, rec, &subset, &recsv).expect("rec_value");
    let hyp_subset = under_scope(&mut env, &subset);
    assert!(union::attempt_indom_rec(&mut env, &b, att, rec, &hyp_subset).is_none());
    let indom =
        union::attempt_indom_rec(&mut env, &b, att, rec, &subset).expect("attempt_indom_rec");

    // ── the union-layer bundle ──────────────────────────────────────────────
    let facts = UnionFacts {
        subset_prod: &sub_prod,
        single_valued: &recsv,
        value: &value_thm,
        indom: &indom,
        members: &members,
    };
    assert!(facts.all_unconditional());
    let bad_facts = UnionFacts {
        subset_prod: &sub_prod,
        single_valued: &recsv,
        value: &value_thm,
        indom: &indom,
        members: &hyp_members,
    };
    assert!(!bad_facts.all_unconditional());
    assert!(is_attempt::rec_rec_cond(&mut env, &b, att, &att_ax, rec, &bad_facts).is_none());
    assert!(is_attempt::rec_rec_cond(&mut env, &b, att, &hyp_att, rec, &facts).is_none());
    let rc =
        is_attempt::rec_rec_cond(&mut env, &b, att, &att_ax, rec, &facts).expect("rec_rec_cond");
    let hyp_rc = under_scope(&mut env, &rc);
    let syms = Syms { att, att_ax: &att_ax, rec };
    assert!(is_attempt::rec_is_attempt(&mut env, &b, syms, &facts, &hyp_rc).is_none());
    assert!(is_attempt::rec_is_attempt(&mut env, &b, syms, &bad_facts, &rc).is_none());
    assert!(is_attempt::rec_is_attempt(&mut env, &b, syms, &facts, &rc).is_some());
    assert!(is_attempt::iota_on_domain(&mut env, &b, rec, &hyp_rc).is_none());
    let iota_dom = is_attempt::iota_on_domain(&mut env, &b, rec, &rc).expect("iota_on_domain");
    let hyp_iota_dom = under_scope(&mut env, &iota_dom);

    // ── totality, ι and the packaging ───────────────────────────────────────
    let bin = derived::sums::mem_bin_union_iff(&mut env, &b.s.ap.sets).expect("bin");
    let hyp_bin = under_scope(&mut env, &bin);
    let m = total::Machinery {
        att,
        att_ax: &att_ax,
        rec,
        facts: &facts,
        iota_dom: &iota_dom,
        rec_rc: &rc,
        bin: &bin,
    };
    assert!(m.all_unconditional());
    for bad in [
        total::Machinery { facts: &bad_facts, ..m },
        total::Machinery { rec_rc: &hyp_rc, ..m },
        total::Machinery { bin: &hyp_bin, ..m },
        total::Machinery { att_ax: &hyp_att, ..m },
        total::Machinery { iota_dom: &hyp_iota_dom, ..m },
    ] {
        assert!(!bad.all_unconditional());
        assert!(total::totality(&mut env, &b, &bad).is_none());
    }
    let tot = total::totality(&mut env, &b, &m).expect("totality");
    let hyp_tot = under_scope(&mut env, &tot);
    assert!(total::rec_funspace(&mut env, &b, rec, &facts, &hyp_tot).is_none());
    assert!(total::rec_funspace(&mut env, &b, rec, &bad_facts, &tot).is_none());
    assert!(total::rec_funspace(&mut env, &b, rec, &facts, &tot).is_some());
    assert!(total::iota(&mut env, &b, rec, &hyp_tot, &iota_dom).is_none());
    assert!(total::iota(&mut env, &b, rec, &tot, &hyp_iota_dom).is_none());
    let io = total::iota(&mut env, &b, rec, &tot, &iota_dom).expect("iota");
    let pa = package::pack_app(&mut env, &b, rec).expect("pack_app");
    let hyp_pa = under_scope(&mut env, &pa);
    let hyp_io = under_scope(&mut env, &io);
    assert!(package::pack_iota(&mut env, &b, rec, &hyp_pa, &io).is_none());
    assert!(package::pack_iota(&mut env, &b, rec, &pa, &hyp_io).is_none());
    assert!(package::pack_iota(&mut env, &b, rec, &pa, &io).is_some());

    // ── the one-point extension ─────────────────────────────────────────────
    let ps: Vec<Term> = (0..4).map(|_| Term::var(env.fresh_var())).collect();
    let x = Term::var(env.fresh_var());
    let good = extend::Ext {
        b: &b,
        att,
        att_ax: &att_ax,
        rec,
        facts: &facts,
        iota_dom: &iota_dom,
        bin: &bin,
        ps: ps.clone(),
        x: x.clone(),
    };
    assert!(good.inputs_unconditional());
    let vanp = good.value_at_new_point(&mut env).expect("value_at_new_point");
    let sv_g = good.ext_single_valued(&mut env, &vanp).expect("ext_single_valued");
    for bad in [
        extend::Ext { facts: &bad_facts, ps: ps.clone(), x: x.clone(), ..good },
        extend::Ext { iota_dom: &hyp_iota_dom, ps: ps.clone(), x: x.clone(), ..good },
        extend::Ext { bin: &hyp_bin, ps: ps.clone(), x: x.clone(), ..good },
        extend::Ext { att_ax: &hyp_att, ps: ps.clone(), x: x.clone(), ..good },
    ] {
        assert!(!bad.inputs_unconditional());
        assert!(bad.ext_members(&x).is_none());
        assert!(bad.rec_subset_ext(&x).is_none());
        assert!(bad.new_point_in_ext(&x).is_none());
        assert!(bad.value_at_new_point(&mut env).is_none());
        assert!(bad.ext_single_valued(&mut env, &vanp).is_none());
        assert!(bad.ext_indom(&mut env, &x).is_none());
        assert!(bad.ext_app(&mut env, &x, &sv_g).is_none());
        assert!(bad.ext_at_x(&sv_g).is_none());
        assert!(extend::ext_x_in_acc(&mut env, &bad, &x).is_none());
        assert!(extend::rec_value_typed(&mut env, &bad).is_none());
    }
    let hyp_vanp = under_scope(&mut env, &vanp);
    let hyp_sv_g = under_scope(&mut env, &sv_g);
    assert!(good.ext_single_valued(&mut env, &hyp_vanp).is_none());
    assert!(good.ext_at_x(&hyp_sv_g).is_none());
    assert!(good.ext_app(&mut env, &x, &hyp_sv_g).is_none());
    let rvt = extend::rec_value_typed(&mut env, &good).expect("rec_value_typed");
    let hyp_rvt = under_scope(&mut env, &rvt);
    assert!(extend::ext_value_typed(&mut env, &good, &x, &hyp_rvt).is_none());
    let vt = extend::ext_value_typed(&mut env, &good, &x, &rvt).expect("ext_value_typed");
    let hyp_vt = under_scope(&mut env, &vt);
    assert!(extend::ext_bound(&mut env, &good, &x, &hyp_vt).is_none());
    let bound = extend::ext_bound(&mut env, &good, &x, &vt).expect("ext_bound");
    let hyp_bound = under_scope(&mut env, &bound);
    assert!(extend::ext_rec_cond(&mut env, &good, &x, &hyp_sv_g, &rc).is_none());
    assert!(extend::ext_rec_cond(&mut env, &good, &x, &sv_g, &hyp_rc).is_none());
    let erc = extend::ext_rec_cond(&mut env, &good, &x, &sv_g, &rc).expect("ext_rec_cond");
    let hyp_erc = under_scope(&mut env, &erc);
    assert!(extend::ext_is_attempt(&mut env, &good, &x, &hyp_bound, &sv_g, &erc).is_none());
    assert!(extend::ext_is_attempt(&mut env, &good, &x, &bound, &hyp_sv_g, &erc).is_none());
    assert!(extend::ext_is_attempt(&mut env, &good, &x, &bound, &sv_g, &hyp_erc).is_none());
    assert!(extend::ext_is_attempt(&mut env, &good, &x, &bound, &sv_g, &erc).is_some());

    // ── and the whole apparatus, over a poisoned `Base` ─────────────────────
    let mut bad_base = b.clone();
    bad_base.ih_app = Thm::assume(b.ih_app.concl().clone());
    assert!(!bad_base.all_unconditional());
    assert!(RecAcc::over(&mut env, bad_base).is_none());
    let r = RecAcc::over(&mut env, b.clone()).expect("RecAcc::over");
    assert!(r.all_unconditional());
}

/// `Bounded` — the two theorems a *consumer* of the recursion needs and that
/// `rec_acc` itself never did: `accrec`'s values are in `T`, and its own
/// induction hypothesis is in `ih_bound(A,T)`. Both carry `ST` and nothing
/// else, which is the whole point: instantiating a step equation guarded by
/// `c ∈ ih_bound(A,T)` at `c := ih(accrec,…)` must not cost a second
/// hypothesis.
#[test]
fn the_recursions_own_induction_hypothesis_is_inside_the_bound() {
    use derived::rec_acc::{Bounded, RecAcc};
    let mut env = Env::new();
    let ra = RecAcc::new(&mut env).expect("RecAcc::new");
    let bd = Bounded::build(&mut env, &ra).expect("Bounded::build");
    assert!(bd.all_unconditional());

    // Each is `∀A ∀R ∀T ∀e. (ST → …)`, so four instantiations reach the body.
    let vs: Vec<kernel::FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ts: Vec<kernel::Term> = vs.iter().map(|v| kernel::Term::var(*v)).collect();
    let st = ra.step_typed(&mut env, &ts[0], &ts[1], &ts[2], &ts[3]);
    for t in [&bd.value_typed, &bd.in_bound] {
        let at = derived::inst_all(t, &ts).expect("at A, R, T and e");
        assert_eq!(at.concl().as_imp().expect("an implication").0, st, "ST is the only guard");
    }

    // A hypothetical `RecAcc` is refused: `ST` is advertised as the only
    // antecedent, and five of its fields are spent through `mp` and `syl`.
    let mut bad = ra.clone();
    bad.totality = kernel::Thm::assume(bad.totality.concl().clone());
    assert!(Bounded::build(&mut env, &bad).is_none());
}

// ─────────────────────────────────────────────────────────────────────────────
// `ep(rel_graph(A,r), y, x) = app(app(r,y),x)` — the edge proposition against
// the relation's own value.
// ─────────────────────────────────────────────────────────────────────────────

/// Everything `edge_is_relation_value` needs, over one `Sums`.
struct Edge {
    s: Sums,
    ep: kernel::FnSym,
    ep_ax: Thm,
    graph: kernel::FnSym,
    graph_ax: Thm,
    graph_pair: Thm,
    pair_in_graph: Thm,
}

fn edge_inputs(env: &mut Env) -> Edge {
    use derived::quot::graph::{graph_pair, pair_in_graph, rel_graph_symbol, RelGraph};

    let s = Sums::new(env).expect("sums");
    let (ep, ep_ax) = derived::rec_acc::ih::edge_prop(env, &s).expect("edge_prop");
    let (graph, graph_ax) = rel_graph_symbol(env, &s).expect("rel_graph");
    let (gp, pig) = {
        let g = RelGraph { s: &s, graph, graph_ax: &graph_ax };
        (graph_pair(env, &g).expect("graph_pair"), pair_in_graph(env, &g).expect("pair_in_graph"))
    };
    Edge { s, ep, ep_ax, graph, graph_ax, graph_pair: gp, pair_in_graph: pig }
}

/// The edge proposition **is** Lean's relation value, and it computes to both
/// truth values.
///
/// The statement is rebuilt from the kernel's constructors, so a theorem with
/// the right name and the wrong antecedent fails here. Then it is fired twice
/// closed, at a relation that holds and one that does not, and the two results
/// are shown *distinct* — which is what rules out its being an equation between
/// two constants.
#[test]
fn the_edge_proposition_is_the_relations_own_value() {
    use derived::point_fun::PointFun;

    let mut env = Env::new();
    let e = edge_inputs(&mut env);
    let g = derived::quot::graph::RelGraph { s: &e.s, graph: e.graph, graph_ax: &e.graph_ax };
    let thm = derived::rec_acc::edge_is_relation_value(
        &mut env,
        &g,
        e.ep,
        &e.ep_ax,
        &e.graph_pair,
        &e.pair_in_graph,
    )
    .expect("edge_is_relation_value");

    // ── the statement, rebuilt ──────────────────────────────────────────────
    let (av, rv, yv, xv) = {
        let mut f = || env.fresh_var();
        (f(), f(), f(), f())
    };
    let (a, r, y, x) = (Term::var(av), Term::var(rv), Term::var(yv), Term::var(xv));
    let value = e.s.ap.apply(e.s.ap.apply(r.clone(), y.clone()), x.clone());
    let edge = derived::rec_acc::ep_of(
        e.ep,
        Term::apply(e.graph, vec![a.clone(), r.clone()]),
        y.clone(),
        x.clone(),
    );
    let body = Formula::imp(
        derived::conj_of(&[
            Formula::mem(y.clone(), a.clone()),
            Formula::mem(x.clone(), a.clone()),
            Formula::mem(value.clone(), derived::anchor::truth_values(&e.s)),
        ])
        .expect("conj"),
        Formula::eq(edge, value),
    );
    let want = [av, rv, yv, xv].iter().rev().fold(body, |f, v| Formula::forall(*v, f));
    assert!(derived::establishes(&thm, &want), "unexpected statement: {:?}", thm.concl());

    // ── fired closed, at both truth values ──────────────────────────────────
    let aog = derived::recursion::app_of_graph(&mut env, &e.s.ap).expect("app_of_graph");
    let pf = PointFun::over(&mut env, &e.s, &aog).expect("point_fun");
    let one = e.s.unit();
    let zero = e.s.zero();
    let pt = e.s.point();

    // `⊢ ep(rel_graph(1, r_v), •, •) = v` for `r_v := {⟨•, {⟨•,v⟩}⟩}`.
    let mut fired = |v: Term| -> (Thm, Term) {
        let inner = PointFun::of(&e.s, pt.clone(), v.clone());
        let rel = PointFun::of(&e.s, pt.clone(), inner.clone());
        // `app(app(r_v,•),•) = v`, in two beta steps.
        let outer = derived::inst_all(&pf.app, &[pt.clone(), inner.clone()]).expect("beta 1");
        let step = derived::congr_arg(
            &mut env,
            e.s.ap.app,
            &[e.s.ap.apply(rel.clone(), pt.clone()), pt.clone()],
            0,
            &outer,
        )
        .expect("congr");
        let beta = derived::inst_all(&pf.app, &[pt.clone(), v.clone()]).expect("beta 2");
        let val_eq = derived::eq_trans(&mut env, &step, &beta).expect("trans");

        // The three hypotheses: `• ∈ 1` twice, and `v ∈ ⟦Prop⟧` carried back
        // along `val_eq` to the *unreduced* application the statement mentions.
        let w = env.fresh_var();
        let in_prop = if v == one {
            derived::anchor::true_in_prop(&e.s).expect("1 ∈ Prop")
        } else {
            derived::anchor::false_in_prop(&e.s).expect("0 ∈ Prop")
        };
        let back = derived::eq_symm(&mut env, &val_eq).expect("symm");
        let leib = Thm::eq_leibniz(
            v.clone(),
            e.s.ap.apply(e.s.ap.apply(rel.clone(), pt.clone()), pt.clone()),
            w,
            Formula::mem(Term::var(w), derived::anchor::truth_values(&e.s)),
        );
        let hyp_prop = Thm::mp(&Thm::mp(&leib, &back).expect("mp"), &in_prop).expect("mp");
        let hyps = derived::and_intro(
            &e.s.unit_mem,
            &derived::and_intro(&e.s.unit_mem, &hyp_prop),
        );

        let at = derived::inst_all(&thm, &[one.clone(), rel.clone(), pt.clone(), pt.clone()])
            .expect("inst");
        let got = Thm::mp(&at, &hyps).expect("discharge");
        let out = derived::eq_trans(&mut env, &got, &val_eq).expect("trans out");
        let lhs = derived::rec_acc::ep_of(
            e.ep,
            Term::apply(e.graph, vec![one.clone(), rel]),
            pt.clone(),
            pt.clone(),
        );
        (out, lhs)
    };

    let (holds, lhs_true) = fired(one.clone());
    let (fails, lhs_false) = fired(zero.clone());
    assert!(holds.hyps().is_empty() && fails.hyps().is_empty(), "closed");
    assert_eq!(
        *holds.concl(),
        Formula::eq(lhs_true.clone(), one.clone()),
        "the true instance does not compute to 1"
    );
    assert_eq!(
        *fails.concl(),
        Formula::eq(lhs_false.clone(), zero.clone()),
        "the false instance does not compute to 0"
    );
    assert_ne!(lhs_true, lhs_false, "the two instances are the same term");

    // And the two answers are *provably* different, so no instantiation of the
    // theorem is a constant: `¬(0 = 1)`.
    let two_valued = derived::anchor::prop_two_valued(&e.s).expect("0 ≠ 1");
    assert!(two_valued.hyps().is_empty());
}

/// The three ways to hand `edge_is_relation_value` something it cannot state,
/// and it refuses each.
///
/// Three, not two: a hypothetical input, a swapped bridge pair, and a symbol
/// minted over a *second* `Sums` — whose `⟨y,x⟩` is a different term, so no
/// theorem here would be about the caller's relation. Each trips a different
/// check, and the first is the one that would otherwise let a `Γ` ride into a
/// theorem documented `⊢ …`.
#[test]
fn the_edge_value_refuses_what_it_cannot_state() {
    let mut env = Env::new();
    let e = edge_inputs(&mut env);
    let g = derived::quot::graph::RelGraph { s: &e.s, graph: e.graph, graph_ax: &e.graph_ax };

    let call = |env: &mut Env, ep_ax: &Thm, gp: &Thm, pig: &Thm| {
        derived::rec_acc::edge_is_relation_value(env, &g, e.ep, ep_ax, gp, pig)
    };
    assert!(
        call(&mut env, &e.ep_ax, &e.graph_pair, &e.pair_in_graph).is_some(),
        "the control case must build"
    );

    // 1. A hypothetical input.
    let tainted = Thm::assume(Formula::false_());
    let tainted = Thm::mp(&derived::ex_falso(e.graph_pair.concl().clone()), &tainted)
        .expect("ex falso");
    assert!(tainted.concl() == e.graph_pair.concl() && !tainted.hyps().is_empty());
    assert!(call(&mut env, &e.ep_ax, &tainted, &e.pair_in_graph).is_none(), "hypothetical");

    // 2. The two bridges swapped.
    assert!(call(&mut env, &e.ep_ax, &e.pair_in_graph, &e.graph_pair).is_none(), "swapped");

    // 3. An `edge_prop` over a second, unrelated `Sums`.
    let other = edge_inputs(&mut env);
    assert!(call(&mut env, &other.ep_ax, &e.graph_pair, &e.pair_in_graph).is_none(), "foreign");
}
