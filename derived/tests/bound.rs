//! The bound hypothesis of the W-type, discharged: a universe is closed under
//! `sup`.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here. The statements are pinned at **fresh constants** wherever the module's
//! own variables would otherwise be doing the talking.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::bound;
use derived::sums::Sums;
use derived::wtype::Wtype;
use derived::universe as uni;

/// The pieces every test needs: a `Sums` (pairing, product, function space,
/// application) and the universe operator over the *same* `Sets`.
struct Fix {
    wt: Wtype,
    lu: FnSym,
    lu_ax: Thm,
    pairing: Thm,
}

impl Fix {
    /// The one `Sums` everything in the fixture is built over.
    fn sums(&self) -> &Sums { &self.wt.sums }
}

fn fixture(env: &mut Env) -> Fix {
    let sums = Sums::new(env).expect("sums");
    let wt = Wtype::over(env, sums).expect("wtype");
    let sums = &wt.sums;
    let (lu, lu_ax) = uni::least_universe(env).expect("U(x)");
    let pairing = uni::universe_pairing(
        env,
        sums.ap.sets.up,
        &sums.ap.sets.up_ax,
        sums.ap.empty,
        &sums.ap.empty_ax,
        sums.pow,
        &sums.pow_ax,
    )
    .expect("universe_pairing");
    Fix { wt, lu, lu_ax, pairing }
}

/// The whole chain, up to `closed(A,B,u)` for an arbitrary universe.
fn closed_thm(env: &mut Env, f: &Fix) -> Thm {
    let pair = bound::universe_opair(env, f.sums().ap.sets.up, &f.pairing).expect("opair");
    let mem_mem = uni::universe_mem_mem(env).expect("C₁ applied");
    let pairs = bound::funspace_pairs(env, f.sums()).expect("funspace_pairs");
    let sub = bound::funspace_subset_universe(env, f.sums(), &pairs, &mem_mem, &pair)
        .expect("subset");
    let fs_mem = bound::funspace_mem_universe(env, f.sums(), &f.sums().ap.empty_ax, &pairs, &sub)
        .expect("member");
    bound::universe_closed(env, f.sums(), &mem_mem, &pair, &fs_mem).expect("universe_closed")
}

/// The same chain, transferred to `U(c)`.
fn least_closed_thm(env: &mut Env, f: &Fix) -> Thm {
    let general = closed_thm(env, f);
    bound::least_universe_closed(env, f.sums(), f.lu, &f.lu_ax, &f.wt.fs_mono, &general)
        .expect("least_universe_closed")
}

/// `⊢ ∀u ∀a ∀b. ((is_universe(u) ∧ (a ∈ u ∧ b ∈ u)) → ⟨a,b⟩ ∈ u)`.
#[test]
fn a_universe_is_closed_under_ordered_pairs() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = bound::universe_opair(&mut env, f.sums().ap.sets.up, &f.pairing)
        .expect("universe_opair");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    // Fresh constants, so the statement mentions nothing of the module's own.
    let tu = Term::apply(env.declare(0), vec![]);
    let ta = Term::apply(env.declare(0), vec![]);
    let tb = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tu.clone(), ta.clone(), tb.clone()]).expect("instantiate");

    let ante = Formula::and(
        uni::is_universe(&mut env, &tu),
        Formula::and(
            Formula::mem(ta.clone(), tu.clone()),
            Formula::mem(tb.clone(), tu.clone()),
        ),
    );
    let concl = Formula::mem(
        derived::opair(f.sums().ap.sets.up, ta.clone(), tb.clone()),
        tu.clone(),
    );
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));

    // Non-vacuity: the conclusion is about the Kuratowski pair, which is not
    // either component, and it is not one of the conjuncts of the antecedent.
    assert_ne!(derived::opair(f.sums().ap.sets.up, ta.clone(), tb.clone()), ta);
    assert_ne!(derived::opair(f.sums().ap.sets.up, ta, tb), tu);
    assert_ne!(ante, concl);

    // A theorem that is not `universe_pairing` is refused.
    assert!(bound::universe_opair(&mut env, f.sums().ap.sets.up, &thm).is_none());
    let _ = (f.lu, f.lu_ax);
}

/// `⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ⊆ u)`.
#[test]
fn a_function_into_a_universe_is_a_subset_of_it() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let pair = bound::universe_opair(&mut env, f.sums().ap.sets.up, &f.pairing).expect("opair");
    let mem_mem = uni::universe_mem_mem(&mut env).expect("C₁ applied");
    let pairs = bound::funspace_pairs(&mut env, f.sums()).expect("funspace_pairs");
    let thm = bound::funspace_subset_universe(&mut env, f.sums(), &pairs, &mem_mem, &pair)
        .expect("funspace_subset_universe");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let tu = Term::apply(env.declare(0), vec![]);
    let tx = Term::apply(env.declare(0), vec![]);
    let tf = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tu.clone(), tx.clone(), tf.clone()]).expect("instantiate");

    let ante = Formula::and(
        uni::is_universe(&mut env, &tu),
        Formula::and(
            Formula::mem(tx.clone(), tu.clone()),
            Formula::mem(tf.clone(), f.sums().fs.of(tx.clone(), tu.clone())),
        ),
    );
    let concl = kernel::thm::subset(&mut env, tf.clone(), tu.clone());
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));

    // Non-vacuity: `f ⊆ u` is not `f ∈ fs(x,u)` under another name, and the
    // conclusion is not a conjunct of the antecedent.
    assert_ne!(concl, Formula::mem(tf.clone(), f.sums().fs.of(tx.clone(), tu.clone())));
    assert_ne!(ante, concl);

    // The antecedent is satisfiable: Tarski hands over a universe containing
    // any set, and `∅ ∈ fs(∅, u)` is a function into it.
    let tarski = Thm::ax_tarski(&mut env);
    assert!(kernel::thm::debug_locally_closed(tarski.concl()));
    let w = &f.wt;
    let e = w.empty();
    let empty_fun =
        derived::inst_all(&w.empty_fun, std::slice::from_ref(&tu)).expect("empty function");
    assert_eq!(*empty_fun.concl(), Formula::mem(e.clone(), w.sums.fs.of(e, tu)));

    // Swapped arguments are refused.
    assert!(bound::funspace_subset_universe(&mut env, f.sums(), &pairs, &pair, &mem_mem).is_none());
    assert!(bound::funspace_subset_universe(&mut env, f.sums(), &mem_mem, &mem_mem, &pair).is_none());
}

/// `⊢ ∀u ∀x ∀f. ((is_universe(u) ∧ (x ∈ u ∧ f ∈ fs(x,u))) → f ∈ u)`.
#[test]
fn a_function_into_a_universe_is_a_member_of_it() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let pair = bound::universe_opair(&mut env, f.sums().ap.sets.up, &f.pairing).expect("opair");
    let mem_mem = uni::universe_mem_mem(&mut env).expect("C₁ applied");
    let pairs = bound::funspace_pairs(&mut env, f.sums()).expect("funspace_pairs");
    let sub = bound::funspace_subset_universe(&mut env, f.sums(), &pairs, &mem_mem, &pair)
        .expect("subset");
    let thm =
        bound::funspace_mem_universe(&mut env, f.sums(), &f.sums().ap.empty_ax, &pairs, &sub)
            .expect("funspace_mem_universe");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let tu = Term::apply(env.declare(0), vec![]);
    let tx = Term::apply(env.declare(0), vec![]);
    let tf = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tu.clone(), tx.clone(), tf.clone()]).expect("instantiate");

    let ante = Formula::and(
        uni::is_universe(&mut env, &tu),
        Formula::and(
            Formula::mem(tx.clone(), tu.clone()),
            Formula::mem(tf.clone(), f.sums().fs.of(tx.clone(), tu.clone())),
        ),
    );
    let concl = Formula::mem(tf.clone(), tu.clone());
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));

    // Non-vacuity: membership in `u` is neither the inclusion the previous
    // lemma proves nor a conjunct of the antecedent.
    assert_ne!(concl, kernel::thm::subset(&mut env, tf.clone(), tu.clone()));
    assert_ne!(concl, Formula::mem(tf.clone(), f.sums().fs.of(tx, tu)));
    assert_ne!(ante, concl);

    // Neither a wrong empty-set theorem nor swapped lemmas are accepted.
    assert!(bound::funspace_mem_universe(&mut env, f.sums(), &sub, &pairs, &sub).is_none());
    assert!(
        bound::funspace_mem_universe(&mut env, f.sums(), &f.sums().ap.empty_ax, &sub, &pairs)
            .is_none()
    );
}

/// `⊢ ∀u ∀A ∀B. ((is_universe(u) ∧ (A ∈ u ∧ ∀a. (a ∈ A → app(B,a) ∈ u)))
///                 → closed(A,B,u))` — the bound hypothesis, discharged.
#[test]
fn a_universe_is_closed_under_sup() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = closed_thm(&mut env, &f);
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let tu = Term::apply(env.declare(0), vec![]);
    let ta = Term::apply(env.declare(0), vec![]);
    let tb = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tu.clone(), ta.clone(), tb.clone()]).expect("instantiate");

    let fam = bound::fibres_in(&mut env, f.sums(), &ta, &tb, &tu);
    let ante = Formula::and(
        uni::is_universe(&mut env, &tu),
        Formula::and(Formula::mem(ta.clone(), tu.clone()), fam.clone()),
    );
    // The conclusion is `wtype::closed` itself, rebuilt here from the W-type
    // module rather than from the module under test.
    let concl = derived::wtype::closed(&mut env, f.sums(), &ta, &tb, &tu);
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));

    // Non-vacuity: the family condition is not the conclusion, and the
    // conclusion is not the trivially true formula.
    assert_ne!(fam, concl);
    assert_ne!(ante, concl);
    assert_ne!(concl, Formula::imp(Formula::false_(), Formula::false_()));
}

/// **The cross-check.** `wtype::unit_bound_closed` proves `closed(1,∅,{⟨•,∅⟩})`
/// by hand at a concrete instance; the general theorem's conclusion,
/// instantiated at those same three terms, must be *that very formula*.
///
/// This is what rules out the general theorem having drifted into a
/// look-alike predicate that nothing else in the development means.
#[test]
fn the_general_theorem_agrees_with_the_worked_instance() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let general = closed_thm(&mut env, &f);
    let w = &f.wt;

    // The instance `unit_bound_closed` settles: `A := 1`, `B := ∅`, `u := {⟨•,∅⟩}`.
    let one = w.sums.unit();
    let e = w.empty();
    let sup0 = w.sup(e.clone(), e.clone());
    let u = derived::singleton(w.sums.ap.sets.up, sup0);

    let at = derived::inst_all(&general, &[u.clone(), one.clone(), e.clone()])
        .expect("instantiate");
    let concl = at.concl().as_imp().expect("an implication").1;
    assert_eq!(
        concl,
        *w.bound_closed.concl(),
        "the general theorem does not conclude what the worked instance proves"
    );

    // And that instance is not vacuous: `⟨•,∅⟩ ∈ W(1,∅,{⟨•,∅⟩})`, so the
    // predicate both theorems speak about is satisfied by an inhabited W-type.
    assert!(kernel::thm::debug_locally_closed(w.inhabited.concl()));
}

/// `⊢ ∀c ∀A ∀B. ((A ∈ U(c) ∧ ∀a. (a ∈ A → app(B,a) ∈ U(c))) → closed(A,B,U(c)))`
/// — the same, at the canonical universe, with `is_universe(U(c))` nowhere in
/// sight.
#[test]
fn the_least_universe_is_closed_under_sup() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let thm = least_closed_thm(&mut env, &f);
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let tc = Term::apply(env.declare(0), vec![]);
    let ta = Term::apply(env.declare(0), vec![]);
    let tb = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tc.clone(), ta.clone(), tb.clone()]).expect("instantiate");

    let w = Term::apply(f.lu, vec![tc.clone()]);
    let fam = bound::fibres_in(&mut env, f.sums(), &ta, &tb, &w);
    let ante = Formula::and(Formula::mem(ta.clone(), w.clone()), fam.clone());
    let concl = derived::wtype::closed(&mut env, f.sums(), &ta, &tb, &w);
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));

    // Non-vacuity: `is_universe(U(c))` does not appear — the antecedent is two
    // membership conditions and nothing else.
    assert_ne!(ante, uni::is_universe(&mut env, &w));
    assert_ne!(ante, concl);

    // The antecedent is satisfiable at `A := U(c)`'s own member `c`… and in
    // particular `c ∈ U(c)` is a theorem, so `A ∈ U(c)` is not empty talk.
    let mem_lu = uni::mem_least_universe(&mut env, f.lu, &f.lu_ax).expect("c ∈ U(c)");
    let at_c = derived::inst_all(&mem_lu, std::slice::from_ref(&tc)).expect("instantiate");
    assert_eq!(*at_c.concl(), Formula::mem(tc, w));
}

/// **W1 with no `closed` antecedent**, pinned in full.
#[test]
fn sup_has_an_unconditional_typing_rule() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let least = least_closed_thm(&mut env, &f);
    let thm = bound::sup_mem_at(&mut env, &f.wt, f.lu, &least).expect("sup_mem_at");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let tc = Term::apply(env.declare(0), vec![]);
    let ta = Term::apply(env.declare(0), vec![]);
    let tb = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tc.clone(), ta.clone(), tb.clone()]).expect("instantiate");

    let u = Term::apply(f.lu, vec![tc.clone()]);
    let w_t = f.wt.of(ta.clone(), tb.clone(), u.clone());
    let ante = Formula::and(
        Formula::mem(ta.clone(), u.clone()),
        bound::fibres_in(&mut env, f.sums(), &ta, &tb, &u),
    );
    // The conclusion is `closed(A,B,W(A,B,U(c)))` — `sup`'s rule verbatim.
    let concl = derived::wtype::closed(&mut env, f.sums(), &ta, &tb, &w_t);
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));

    // Non-vacuity: the antecedent no longer mentions `closed` at the bound,
    // which is exactly the hypothesis that has been discharged.
    let old = derived::wtype::closed(&mut env, f.sums(), &ta, &tb, &u);
    assert_ne!(ante, old);
    assert_ne!(concl, old);

    // And the conclusion is not the antecedent restated.
    assert_ne!(ante, concl);
}

/// **W3 with no `closed` antecedent.**
#[test]
fn inversion_is_unconditional() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let least = least_closed_thm(&mut env, &f);
    let inversion = f.wt.inversion(&mut env).expect("w_inversion");
    let thm = bound::w_inversion_at(&mut env, &f.wt, f.lu, &least, &inversion)
        .expect("w_inversion_at");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let tc = Term::apply(env.declare(0), vec![]);
    let ta = Term::apply(env.declare(0), vec![]);
    let tb = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tc.clone(), ta.clone(), tb.clone()]).expect("instantiate");

    let u = Term::apply(f.lu, vec![tc.clone()]);
    let w_t = f.wt.of(ta.clone(), tb.clone(), u.clone());
    let ante = Formula::and(
        Formula::mem(ta.clone(), u.clone()),
        bound::fibres_in(&mut env, f.sums(), &ta, &tb, &u),
    );
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let concl = Formula::forall(
        zv,
        Formula::imp(
            Formula::mem(tz.clone(), w_t.clone()),
            derived::wtype::is_sup(&mut env, f.sums(), &w_t, &ta, &tb, &tz),
        ),
    );
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));
    assert_ne!(ante, concl);

    // A theorem that is not `w_inversion` is refused.
    assert!(bound::w_inversion_at(&mut env, &f.wt, f.lu, &least, &least).is_none());
}

/// **Structural induction with no `closed` antecedent**, at a formula that
/// mentions the bound — so the substitution `u := U(c)` really has to reach
/// inside `φ`.
#[test]
fn structural_induction_is_unconditional() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let least = least_closed_thm(&mut env, &f);

    let (av, bv, uv, zv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tu, tz) = (Term::var(av), Term::var(bv), Term::var(uv), Term::var(zv));
    // `φ(z) := z ∈ u`, which mentions the bound and nothing else.
    let phi = Formula::mem(tz.clone(), tu.clone());
    let rect = derived::wtype::w_rect(
        &mut env,
        &f.wt,
        &[av, bv, uv],
        derived::wtype::Params { a: av, b: bv, u: uv },
        zv,
        &phi,
    )
    .expect("w_rect");

    let tc = Term::apply(env.declare(0), vec![]);
    let thm =
        bound::w_rect_at(&mut env, f.sums(), f.lu, &least, &rect, uv, &bound::At { c: &tc, a: &ta, b: &tb })
            .expect("w_rect_at");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let u = Term::apply(f.lu, vec![tc.clone()]);
    let w_t = f.wt.of(ta.clone(), tb.clone(), u.clone());
    let phi_u = Formula::mem(tz.clone(), u.clone());
    let ante = Formula::and(
        Formula::mem(ta.clone(), u.clone()),
        bound::fibres_in(&mut env, f.sums(), &ta, &tb, &u),
    );
    let step = derived::wtype::ind_step(&mut env, f.sums(), &w_t, &ta, &tb, zv, &phi_u);
    let concl = Formula::imp(
        step.clone(),
        Formula::forall(zv, Formula::imp(Formula::mem(tz, w_t), phi_u.clone())),
    );
    assert_eq!(*thm.concl(), Formula::imp(ante, concl));

    // The substitution really happened: `φ` now speaks about `U(c)`, not about
    // the variable `w_rect` was given.
    assert_ne!(phi_u, phi);
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → fs(a,b) ⊆ U(c))` — every function
/// between members of `U(c)` is a member of `U(c)`.
///
/// Note what is asserted: `⊆`, not `∈`. The stronger `fs(a,b) ∈ U(c)` is *not*
/// proved; see `bound::funspace_subset_least_universe` for the remaining
/// obligation.
#[test]
fn functions_between_members_of_a_universe_are_members() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let pair = bound::universe_opair(&mut env, f.sums().ap.sets.up, &f.pairing).expect("opair");
    let mem_mem = uni::universe_mem_mem(&mut env).expect("C₁ applied");
    let pairs = bound::funspace_pairs(&mut env, f.sums()).expect("funspace_pairs");
    let sub = bound::funspace_subset_universe(&mut env, f.sums(), &pairs, &mem_mem, &pair)
        .expect("subset");
    let fs_mem =
        bound::funspace_mem_universe(&mut env, f.sums(), &f.sums().ap.empty_ax, &pairs, &sub)
            .expect("member");
    let lu_mem = bound::least_universe_funspace_mem(
        &mut env,
        f.sums(),
        f.lu,
        &f.lu_ax,
        &f.wt.fs_mono,
        &fs_mem,
    )
    .expect("least_universe_funspace_mem");
    let c1 = uni::least_universe_transitive(&mut env, f.lu, &f.lu_ax).expect("C₁(U(c))");
    let thm = bound::funspace_subset_least_universe(
        &mut env,
        f.sums(),
        f.lu,
        &c1,
        &f.wt.fs_mono,
        &lu_mem,
    )
    .expect("funspace_subset_least_universe");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let tc = Term::apply(env.declare(0), vec![]);
    let ta = Term::apply(env.declare(0), vec![]);
    let tb = Term::apply(env.declare(0), vec![]);
    let at = derived::inst_all(&thm, &[tc.clone(), ta.clone(), tb.clone()]).expect("instantiate");

    let w = Term::apply(f.lu, vec![tc]);
    let ante = Formula::and(
        Formula::mem(ta.clone(), w.clone()),
        Formula::mem(tb.clone(), w.clone()),
    );
    let fs_t = f.sums().fs.of(ta, tb);
    let concl = kernel::thm::subset(&mut env, fs_t.clone(), w.clone());
    assert_eq!(*at.concl(), Formula::imp(ante.clone(), concl.clone()));

    // The weaker `⊆` really is what is proved: `∈` is a different formula, and
    // this test would fail if the two were confused.
    assert_ne!(concl, Formula::mem(fs_t, w));
    assert_ne!(ante, concl);

    // And the `U(c)` form of the membership lemma is genuinely universe-free in
    // its statement: no `is_universe(U(c))` anywhere.
    let (tc2, tx, tf2) = (
        Term::apply(env.declare(0), vec![]),
        Term::apply(env.declare(0), vec![]),
        Term::apply(env.declare(0), vec![]),
    );
    let at2 = derived::inst_all(&lu_mem, &[tc2.clone(), tx.clone(), tf2.clone()])
        .expect("instantiate");
    let w2 = Term::apply(f.lu, vec![tc2]);
    assert_eq!(
        *at2.concl(),
        Formula::imp(
            Formula::and(
                Formula::mem(tx.clone(), w2.clone()),
                Formula::mem(tf2.clone(), f.sums().fs.of(tx, w2.clone()))
            ),
            Formula::mem(tf2, w2)
        )
    );
}

/// The bundle builds, and its two headline fields say what the module
/// documentation says they say.
#[test]
fn the_bundle_assembles() {
    let mut env = Env::new();
    let sums = Sums::new(&mut env).expect("sums");
    let wt = Wtype::over(&mut env, sums).expect("wtype");
    let b = bound::Bound::new(&mut env, &wt).expect("Bound");

    let tc = Term::apply(env.declare(0), vec![]);
    let ta = Term::apply(env.declare(0), vec![]);
    let tb = Term::apply(env.declare(0), vec![]);
    let w = b.universe_of(tc.clone());

    let ante = Formula::and(
        Formula::mem(ta.clone(), w.clone()),
        bound::fibres_in(&mut env, &wt.sums, &ta, &tb, &w),
    );
    let lc = derived::inst_all(&b.least_universe_closed, &[tc.clone(), ta.clone(), tb.clone()])
        .expect("instantiate");
    assert_eq!(
        *lc.concl(),
        Formula::imp(
            ante.clone(),
            derived::wtype::closed(&mut env, &wt.sums, &ta, &tb, &w)
        )
    );

    let sup = derived::inst_all(&b.sup_mem, &[tc, ta.clone(), tb.clone()]).expect("instantiate");
    let w_t = wt.of(ta.clone(), tb.clone(), w);
    assert_eq!(
        *sup.concl(),
        Formula::imp(ante, derived::wtype::closed(&mut env, &wt.sums, &ta, &tb, &w_t))
    );

    // Every theorem in the bundle is a closed formula.
    for t in [
        &b.universe_opair,
        &b.funspace_pairs,
        &b.funspace_subset,
        &b.funspace_mem,
        &b.universe_closed,
        &b.least_universe_closed,
        &b.sup_mem,
        &b.w_inversion,
        &b.funspace_mem_lu,
        &b.funspace_subset_lu,
    ] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
}

/// **The whole chain is non-vacuous**, and here is a W-type bounded by a
/// *universe* to prove it:
///
/// ```text
/// ⊢ ⟨c,∅⟩ ∈ W({c}, ∅, U(c))
/// ```
///
/// `wtype::unit_wtype_inhabited` does this at a hand-picked bound `{⟨•,∅⟩}`
/// chosen to make `closed` true by fiat. This one takes the bound `U(c)` — an
/// arbitrary set's canonical universe, nothing tailored about it — and gets
/// `closed({c}, ∅, U(c))` from `least_universe_closed`, so the antecedent of
/// every unconditional rule above is exhibited as *satisfied*, not merely
/// non-refutable.
#[test]
fn a_universe_bounded_wtype_is_inhabited() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let least = least_closed_thm(&mut env, &f);
    let sup = bound::sup_mem_at(&mut env, &f.wt, f.lu, &least).expect("sup_mem_at");

    let tc = Term::apply(env.declare(0), vec![]);
    let up = f.sums().ap.sets.up;
    let w = Term::apply(f.lu, vec![tc.clone()]);
    let e = f.wt.empty();
    let sing_c = derived::singleton(up, tc.clone());

    // `c ∈ U(c)`.
    let mem_lu = uni::mem_least_universe(&mut env, f.lu, &f.lu_ax).expect("c ∈ U(c)");
    let c_in_w = derived::inst_all(&mem_lu, std::slice::from_ref(&tc)).expect("instantiate");

    // `∅ ⊆ c`, hence `∅ ∈ U(c)` by `C₂(U(c))`.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let not_in_e = derived::inst_all(&f.sums().ap.empty_ax, std::slice::from_ref(&tz))
        .expect("∅ has no members");
    let sub_body = derived::syl(
        &not_in_e,
        &derived::ex_falso(Formula::mem(tz.clone(), tc.clone())),
    )
    .expect("ex falso");
    let e_sub_c = Thm::gen(zv, &sub_body);
    assert_eq!(*e_sub_c.concl(), kernel::thm::subset(&mut env, e.clone(), tc.clone()));

    let c2 = uni::least_universe_closed_sub(&mut env, f.lu, &f.lu_ax).expect("C₂(U(c))");
    let c2_at = derived::inst_all(&c2, std::slice::from_ref(&tc)).expect("instantiate");
    let c2_c = derived::inst_all(&c2_at, std::slice::from_ref(&tc)).expect("at y := c");
    let all_sub = Thm::mp(&c2_c, &c_in_w).expect("c is a member");
    let e_in_w = Thm::mp(
        &derived::inst_all(&all_sub, std::slice::from_ref(&e)).expect("at z := ∅"),
        &e_sub_c,
    )
    .expect("∅ ⊆ c");
    assert_eq!(*e_in_w.concl(), Formula::mem(e.clone(), w.clone()));

    // `{c} ∈ U(c)` by pairing.
    let pairing_lu =
        uni::least_universe_pairing(&mut env, f.lu, &f.lu_ax, up, &f.pairing).expect("pairing");
    let sing_in_w = Thm::mp(
        &derived::inst_all(&pairing_lu, &[tc.clone(), tc.clone(), tc.clone()])
            .expect("instantiate"),
        &derived::and_intro(&c_in_w, &c_in_w),
    )
    .expect("{c} ∈ U(c)");
    assert_eq!(*sing_in_w.concl(), Formula::mem(sing_c.clone(), w.clone()));

    // Every fibre of the constant-empty family is `∅ ∈ U(c)`.
    let av = env.fresh_var();
    let ta = Term::var(av);
    let app_e = derived::inst_all(&f.wt.app_empty, std::slice::from_ref(&ta))
        .expect("app(∅,a) = ∅");
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        e.clone(),
        f.wt.fibre(e.clone(), ta.clone()),
        hole,
        Formula::mem(Term::var(hole), w.clone()),
    );
    let fibre_in_w = Thm::mp(
        &Thm::mp(&carry, &derived::eq_symm(&mut env, &app_e).expect("symm")).expect("leibniz"),
        &e_in_w,
    )
    .expect("fibre ∈ U(c)");
    let fam = Thm::gen(
        av,
        &derived::a1i(&fibre_in_w, Formula::mem(ta.clone(), sing_c.clone())),
    );
    assert_eq!(
        *fam.concl(),
        bound::fibres_in(&mut env, f.sums(), &sing_c, &e, &w),
        "the family condition is not the one the theorems state"
    );

    // The antecedent of every unconditional rule, **proved**.
    let ante = derived::and_intro(&sing_in_w, &fam);

    // `closed({c}, ∅, U(c))` — an unconditional instance of the bound.
    let closed_at = Thm::mp(
        &derived::inst_all(&least, &[tc.clone(), sing_c.clone(), e.clone()])
            .expect("instantiate"),
        &ante,
    )
    .expect("closed");
    assert_eq!(
        *closed_at.concl(),
        derived::wtype::closed(&mut env, f.sums(), &sing_c, &e, &w)
    );

    // And `sup`'s typing rule, applied at `a := c` and `f := ∅`.
    let rule = Thm::mp(
        &derived::inst_all(&sup, &[tc.clone(), sing_c.clone(), e.clone()]).expect("instantiate"),
        &ante,
    )
    .expect("sup rule");
    let w_t = f.wt.of(sing_c.clone(), e.clone(), w.clone());

    let mem_sing =
        derived::inst_all(&f.sums().ap.mem_sing, &[tc.clone(), tc.clone()]).expect("instantiate");
    let c_in_sing =
        Thm::mp(&derived::iff_mpr(&mem_sing).expect("mpr"), &Thm::eq_refl(tc.clone()))
            .expect("c ∈ {c}");
    let at_c = Thm::mp(
        &derived::inst_all(&rule, std::slice::from_ref(&tc)).expect("instantiate"),
        &c_in_sing,
    )
    .expect("at a := c");

    // `∅ ∈ fs(app(∅,c), W)`, by rewriting the fibre to `∅`.
    let empty_fun =
        derived::inst_all(&f.wt.empty_fun, std::slice::from_ref(&w_t)).expect("empty function");
    let hole2 = env.fresh_var();
    let carry2 = Thm::eq_leibniz(
        e.clone(),
        f.wt.fibre(e.clone(), tc.clone()),
        hole2,
        Formula::mem(e.clone(), f.sums().fs.of(Term::var(hole2), w_t.clone())),
    );
    let app_e_c =
        derived::inst_all(&f.wt.app_empty, std::slice::from_ref(&tc)).expect("app(∅,c) = ∅");
    let empty_in_fs = Thm::mp(
        &Thm::mp(&carry2, &derived::eq_symm(&mut env, &app_e_c).expect("symm")).expect("leibniz"),
        &empty_fun,
    )
    .expect("∅ is a function out of the fibre");

    let out = Thm::mp(
        &derived::inst_all(&at_c, std::slice::from_ref(&e)).expect("instantiate"),
        &empty_in_fs,
    )
    .expect("at f := ∅");

    assert_eq!(
        *out.concl(),
        Formula::mem(f.wt.sup(tc, e), w_t),
        "the W-type over a universe bound is not inhabited by ⟨c,∅⟩"
    );
    assert!(kernel::thm::debug_locally_closed(out.concl()));
}
