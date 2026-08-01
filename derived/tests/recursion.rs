//! `ω` and recursion along it, checked step by step.
//!
//! Every test pins the **exact** conclusion of the lemma it covers, rebuilt
//! independently from the kernel's formula constructors, and several also check
//! that the statement is not satisfied vacuously — a lemma whose two sides are
//! literally the same term proves nothing.

use derived::funcs::Sets;
use derived::recursion;
use kernel::{Env, Formula, Term};

/// The pairing/union apparatus and the singleton lemma every test needs.
fn base(env: &mut Env) -> (Sets, kernel::Thm) {
    let sets = Sets::new(env);
    let mem_sing = derived::mem_singleton(env, sets.up, &sets.up_ax).expect("mem_singleton");
    (sets, mem_sing)
}

/// `⊢ ∀n ∀z. (z ∈ ⋃{n,{n}} ↔ (z ∈ n ∨ z = n))`.
#[test]
fn union_of_a_set_with_its_singleton() {
    let mut env = Env::new();
    let (sets, mem_sing) = base(&mut env);
    let thm = recursion::mem_union_succ(&mut env, &sets, &mem_sing).expect("mem_union_succ");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (n, z) = (env.fresh_var(), env.fresh_var());
    let (tn, tz) = (Term::var(n), Term::var(z));
    let sn = derived::singleton(sets.up, tn.clone());
    let u = sets.union_of(Term::apply(sets.up, vec![tn.clone(), sn]));
    let expected = Formula::forall(
        n,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), u),
                Formula::or(Formula::mem(tz.clone(), tn.clone()), Formula::eq(tz, tn)),
            ),
        ),
    );
    assert_eq!(*thm.concl(), expected, "mem_union_succ has the wrong shape");
}

/// `⊢ ∀n ∀z. (z ∈ succ(n) ↔ (z ∈ n ∨ z = n))`, and `succ` really is a new
/// unary symbol rather than one of the ones it was built from.
#[test]
fn successor_membership() {
    let mut env = Env::new();
    let (sets, mem_sing) = base(&mut env);
    let (succ, ax) = recursion::successor(&mut env, &sets, &mem_sing).expect("successor");
    assert!(kernel::thm::debug_locally_closed(ax.concl()));
    assert_eq!(succ.arity(), 1);

    let (n, z) = (env.fresh_var(), env.fresh_var());
    let (tn, tz) = (Term::var(n), Term::var(z));
    let expected = Formula::forall(
        n,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), Term::apply(succ, vec![tn.clone()])),
                Formula::or(Formula::mem(tz.clone(), tn.clone()), Formula::eq(tz, tn)),
            ),
        ),
    );
    assert_eq!(*ax.concl(), expected, "successor has the wrong shape");

    // Non-vacuity: `succ(c)` is not the term `c`, so the biconditional is not
    // an identity in disguise.
    let c = Term::apply(env.declare(0), vec![]);
    assert_ne!(Term::apply(succ, vec![c.clone()]), c);
}

/// The full apparatus needed for the two transitivity lemmas.
fn with_succ(env: &mut Env) -> (Sets, kernel::FnSym, kernel::Thm, kernel::FnSym, kernel::Thm) {
    let (sets, mem_sing) = base(env);
    let (pow, pow_ax) = derived::power(env);
    let (succ, succ_ax) = recursion::successor(env, &sets, &mem_sing).expect("successor");
    (sets, pow, pow_ax, succ, succ_ax)
}

/// `⊢ ∀q. (Trans(q) → succ(q) ⊆ 𝒫q)` — the step that gets `succ` inside a
/// Tarski universe at all.
#[test]
fn successor_of_a_transitive_set_is_a_subset_of_its_power_set() {
    let mut env = Env::new();
    let (_sets, pow, pow_ax, succ, succ_ax) = with_succ(&mut env);
    let thm = recursion::succ_subset_pow(&mut env, pow, &pow_ax, succ, &succ_ax)
        .expect("succ_subset_pow");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let q = env.fresh_var();
    let tq = Term::var(q);
    let trans = derived::empty::transitive(&mut env, &tq);
    let sub = kernel::thm::subset(
        &mut env,
        Term::apply(succ, vec![tq.clone()]),
        Term::apply(pow, vec![tq]),
    );
    assert_eq!(
        *thm.concl(),
        Formula::forall(q, Formula::imp(trans, sub)),
        "succ_subset_pow has the wrong shape"
    );
}

/// `⊢ ∀q. (Trans(q) → Trans(succ(q)))`, and the two sides are genuinely
/// different formulas — this is not reflexivity in disguise.
#[test]
fn successor_preserves_transitivity() {
    let mut env = Env::new();
    let (_sets, _pow, _pow_ax, succ, succ_ax) = with_succ(&mut env);
    let thm = recursion::trans_succ(&mut env, succ, &succ_ax).expect("trans_succ");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let q = env.fresh_var();
    let tq = Term::var(q);
    let trans_q = derived::empty::transitive(&mut env, &tq);
    let trans_sq = derived::empty::transitive(&mut env, &Term::apply(succ, vec![tq]));
    assert_ne!(trans_q, trans_sq, "the two sides must not coincide");
    assert_eq!(
        *thm.concl(),
        Formula::forall(q, Formula::imp(trans_q, trans_sq)),
        "trans_succ has the wrong shape"
    );
}

/// `⊢ ∃m. Least(∅, m)` — the least inductive set exists.
#[test]
fn least_inductive_set_over_the_empty_set_exists() {
    let mut env = Env::new();
    let (sets, mem_sing) = base(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let (succ, succ_ax) = recursion::successor(&mut env, &sets, &mem_sing).expect("successor");
    let (empty, empty_ax) = derived::empty::empty(&mut env);

    let thm = recursion::omega_exists(&mut env, pow, &pow_ax, succ, &succ_ax, &empty_ax)
        .expect("omega_exists");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let zero = Term::apply(empty, vec![]);
    let m = env.fresh_var();
    let expected = Formula::exists(
        m,
        recursion::least_inductive(&mut env, succ, &zero, &Term::var(m)),
    );
    assert_eq!(*thm.concl(), expected, "omega_exists has the wrong shape");

    // Non-vacuity: `Least` really constrains — its inductive half mentions both
    // `∅` and `succ`, and is not the trivially true formula.
    let ind = recursion::inductive(&mut env, succ, &zero, &Term::var(m));
    assert_ne!(ind, Formula::imp(Formula::false_(), Formula::false_()));
}

/// `⊢ Least(∅, ω)` — the symbol exists and is characterised.
#[test]
fn omega_is_the_least_inductive_set() {
    let mut env = Env::new();
    let (sets, mem_sing) = base(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let (succ, succ_ax) = recursion::successor(&mut env, &sets, &mem_sing).expect("successor");
    let (empty, empty_ax) = derived::empty::empty(&mut env);

    let (om, thm) = recursion::omega(&mut env, pow, &pow_ax, succ, &succ_ax, &empty_ax)
        .expect("omega");
    assert_eq!(om.arity(), 0);
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let zero = Term::apply(empty, vec![]);
    let w = Term::apply(om, vec![]);
    assert_ne!(zero, w, "ω and ∅ must be different terms");
    let expected = recursion::least_inductive(&mut env, succ, &zero, &w);
    assert_eq!(*thm.concl(), expected, "omega has the wrong shape");
}

/// `⊢ 0 ∈ ω`, `⊢ ∀n. (n ∈ ω → succ(n) ∈ ω)` and minimality, projected off
/// `Least(∅, ω)`.
#[test]
fn omega_core_projections() {
    let mut env = Env::new();
    let core = recursion::OmegaCore::new(&mut env).expect("OmegaCore");
    let (zero, w) = (core.zero(), core.set());

    assert_eq!(*core.zero_mem.concl(), Formula::mem(zero.clone(), w.clone()));

    let n = env.fresh_var();
    let tn = Term::var(n);
    assert_eq!(
        *core.succ_closed.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), w.clone()),
                Formula::mem(core.succ_of(tn.clone()), w.clone())
            )
        ),
        "succ_closed has the wrong shape"
    );

    // Minimality: `∀w. (Ind(∅,w) → ∀q. (q ∈ ω → q ∈ w))`.
    let (v, q) = (env.fresh_var(), env.fresh_var());
    let (tv, tq) = (Term::var(v), Term::var(q));
    let ind_v = core.ind_of(&mut env, &tv);
    let contained = Formula::forall(
        q,
        Formula::imp(Formula::mem(tq.clone(), w.clone()), Formula::mem(tq, tv)),
    );
    assert_eq!(
        *core.minimal.concl(),
        Formula::forall(v, Formula::imp(ind_v, contained)),
        "minimal has the wrong shape"
    );

    // Non-vacuity: `succ(0)` is not `0`, so the successor really moves.
    assert_ne!(core.succ_of(zero.clone()), zero);
}

/// `⊢ ∀S. ((0 ∈ S ∧ ∀n. ((n ∈ ω ∧ n ∈ S) → succ(n) ∈ S)) → ∀n. (n ∈ ω → n ∈ S))`.
#[test]
fn induction_over_omega() {
    let mut env = Env::new();
    let core = recursion::OmegaCore::new(&mut env).expect("OmegaCore");
    let thm = recursion::induction_principle(&mut env, &core).expect("induction_principle");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (zero, w) = (core.zero(), core.set());
    let (s, n) = (env.fresh_var(), env.fresh_var());
    let (ts, tn) = (Term::var(s), Term::var(n));
    let n_in_om = Formula::mem(tn.clone(), w);
    let n_in_s = Formula::mem(tn.clone(), ts.clone());
    let step = Formula::forall(
        n,
        Formula::imp(
            Formula::and(n_in_om.clone(), n_in_s.clone()),
            Formula::mem(core.succ_of(tn), ts.clone()),
        ),
    );
    let hyp = Formula::and(Formula::mem(zero, ts), step.clone());
    let concl = Formula::forall(n, Formula::imp(n_in_om.clone(), n_in_s.clone()));
    assert_ne!(hyp, concl, "the induction principle must not be trivial");
    assert_eq!(
        *thm.concl(),
        Formula::forall(s, Formula::imp(hyp, concl)),
        "induction_principle has the wrong shape"
    );

    // Non-vacuity: the step hypothesis is a real constraint, not `⊤`. Its body
    // mentions `succ`, which the conclusion does not.
    assert_ne!(step, Formula::imp(Formula::false_(), Formula::false_()));
}

/// `⊢ ∀n. (n ∈ ω → Trans(n))`, by induction.
#[test]
fn every_natural_number_is_transitive() {
    let mut env = Env::new();
    let core = recursion::OmegaCore::new(&mut env).expect("OmegaCore");
    let thm = recursion::omega_trans(&mut env, &core).expect("omega_trans");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let n = env.fresh_var();
    let tn = Term::var(n);
    let trans = derived::empty::transitive(&mut env, &tn);
    assert_eq!(
        *thm.concl(),
        Formula::forall(n, Formula::imp(Formula::mem(tn, core.set()), trans)),
        "omega_trans has the wrong shape"
    );
}

/// `⊢ ∀n. (n ∈ ω → ¬(succ(n) = 0))`, and `succ(0) ≠ 0` follows at a term.
#[test]
fn zero_is_not_a_successor() {
    let mut env = Env::new();
    let core = recursion::OmegaCore::new(&mut env).expect("OmegaCore");
    let thm = recursion::succ_ne_zero(&mut env, &core).expect("succ_ne_zero");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (zero, w) = (core.zero(), core.set());
    let n = env.fresh_var();
    let tn = Term::var(n);
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), w),
                Formula::not(Formula::eq(core.succ_of(tn), zero.clone()))
            )
        ),
        "succ_ne_zero has the wrong shape"
    );

    // Instantiated at `0`: `⊢ 0 ∈ ω → ¬(succ(0) = 0)`, and `0 ∈ ω` is proved,
    // so `succ(0) ≠ 0` outright. The two terms compared are genuinely
    // distinct, so this is not a vacuous negation of an identity.
    let at_zero = derived::inst_all(&thm, std::slice::from_ref(&zero)).expect("instantiate");
    let ne = kernel::Thm::mp(&at_zero, &core.zero_mem).expect("0 ∈ ω discharges it");
    assert_ne!(core.succ_of(zero.clone()), zero.clone());
    assert_eq!(
        *ne.concl(),
        Formula::not(Formula::eq(core.succ_of(zero.clone()), zero)),
        "succ(0) ≠ 0 has the wrong shape"
    );
}

/// `⊢ ∀m ∀n. ((m ∈ ω ∧ n ∈ ω) → (succ(m) = succ(n) → m = n))`.
#[test]
fn the_successor_is_injective_on_omega() {
    let mut env = Env::new();
    let core = recursion::OmegaCore::new(&mut env).expect("OmegaCore");
    let om_trans = recursion::omega_trans(&mut env, &core).expect("omega_trans");
    let no_self = derived::empty::no_self_mem(&mut env, core.sets.up, &core.mem_sing)
        .expect("no_self_mem");
    let thm = recursion::succ_inj(&mut env, &core, &om_trans, &no_self).expect("succ_inj");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (m, n) = (env.fresh_var(), env.fresh_var());
    let (tm, tn) = (Term::var(m), Term::var(n));
    let w = core.set();
    let hyp = Formula::and(
        Formula::mem(tm.clone(), w.clone()),
        Formula::mem(tn.clone(), w),
    );
    let eq_succ = Formula::eq(core.succ_of(tm.clone()), core.succ_of(tn.clone()));
    let eq_plain = Formula::eq(tm, tn);
    assert_ne!(eq_succ, eq_plain, "the two equations must not coincide");
    assert_eq!(
        *thm.concl(),
        Formula::forall(m, Formula::forall(n, Formula::imp(hyp, Formula::imp(eq_succ, eq_plain)))),
        "succ_inj has the wrong shape"
    );
}

/// The whole `ω` package builds from one chain of definitional extensions.
#[test]
fn peano_package() {
    let mut env = Env::new();
    let p = recursion::Peano::new(&mut env).expect("Peano");
    for t in [&p.induction, &p.trans, &p.succ_ne_zero, &p.succ_inj, &p.no_self_mem] {
        assert!(kernel::thm::debug_locally_closed(t.concl()));
    }
    // Sharing: every theorem talks about the *same* `ω` and the same `succ`.
    let n = env.fresh_var();
    let tn = Term::var(n);
    let inst = derived::inst_all(&p.succ_ne_zero, std::slice::from_ref(&tn)).expect("instantiate");
    let (ante, _) = inst.concl().as_imp().expect("an implication");
    assert_eq!(ante, Formula::mem(tn, p.core.set()));
}

/// `⊢ ∀f ∀a ∀b. ((SingleValued(f) ∧ ⟨a,b⟩ ∈ f) → app(f,a) = b)`.
#[test]
fn application_reads_a_value_off_a_single_valued_graph() {
    let mut env = Env::new();
    let ap = derived::funcs::Apply::new(&mut env).expect("Apply");
    let thm = recursion::app_of_graph(&mut env, &ap).expect("app_of_graph");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (f, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tb) = (Term::var(f), Term::var(a), Term::var(b));
    let sv = derived::funspace::is_single_valued(&mut env, &ap.sets, &tf);
    let hyp = Formula::and(
        sv,
        Formula::mem(ap.sets.pair(ta.clone(), tb.clone()), tf.clone()),
    );
    let concl = Formula::eq(ap.apply(tf, ta), tb);
    assert_eq!(
        *thm.concl(),
        Formula::forall(f, Formula::forall(a, Formula::forall(b, Formula::imp(hyp, concl)))),
        "app_of_graph has the wrong shape"
    );
}

/// Non-vacuity, end to end: `ω` provably contains two *distinct* elements, so
/// the induction principle's conclusion `∀n. (n ∈ ω → n ∈ S)` is a claim about
/// a non-empty domain, and its `n ∈ ω` antecedent is not idle.
#[test]
fn omega_is_not_vacuous() {
    let mut env = Env::new();
    let p = recursion::Peano::new(&mut env).expect("Peano");
    let core = &p.core;
    let zero = core.zero();
    let one = core.succ_of(zero.clone());

    // `⊢ 0 ∈ ω` and `⊢ succ(0) ∈ ω`.
    assert_eq!(*core.zero_mem.concl(), Formula::mem(zero.clone(), core.set()));
    let closed_at_zero =
        derived::inst_all(&core.succ_closed, std::slice::from_ref(&zero)).expect("instantiate");
    let one_mem = kernel::Thm::mp(&closed_at_zero, &core.zero_mem).expect("0 ∈ ω discharges it");
    assert_eq!(*one_mem.concl(), Formula::mem(one.clone(), core.set()));

    // `⊢ ¬(succ(0) = 0)`, so the two are distinct *as proved*, not just as
    // syntactically different terms.
    let ne_at_zero =
        derived::inst_all(&p.succ_ne_zero, std::slice::from_ref(&zero)).expect("instantiate");
    let ne = kernel::Thm::mp(&ne_at_zero, &core.zero_mem).expect("0 ∈ ω discharges it");
    assert_eq!(*ne.concl(), Formula::not(Formula::eq(one.clone(), zero.clone())));

    // The induction principle instantiated at a constant `S` really delivers
    // `0 ∈ S` from its hypothesis: the conclusion is not the empty statement.
    let s = Term::apply(env.declare(0), vec![]);
    let at_s = derived::inst_all(&p.induction, std::slice::from_ref(&s)).expect("instantiate");
    let (_hyp, concl) = at_s.concl().as_imp().expect("an implication");
    let inner = derived::empty::open_forall(&concl, &zero).expect("open the ∀n");
    assert_eq!(
        inner,
        Formula::imp(
            Formula::mem(zero.clone(), core.set()),
            Formula::mem(zero.clone(), s.clone())
        ),
        "the induction conclusion does not instantiate to `0 ∈ ω → 0 ∈ S`"
    );
}

/// [`Rec`] is one chain of definitional extensions: the `0` of `ω` **is** the
/// `∅` that `app` returns off a domain.
///
/// Built separately they would not be — `Apply` and `Peano` each call
/// `empty::empty`, and every call mints a new symbol — and then `app(f,0) = c`
/// and `0 ∈ ω` would be claims about two unrelated constants. This is the
/// hazard [`derived::funcs::Apply::with_sets`] exists for, one level up.
#[test]
fn recursion_shares_one_empty_set() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");

    // The `0` of `ω` is `∅`, as a term.
    assert_eq!(r.zero(), Term::apply(r.ap.empty, vec![]));
    // And it is provably a member of `ω`.
    assert_eq!(
        *r.core().zero_mem.concl(),
        Formula::mem(r.zero(), r.omega()),
        "0 ∈ ω is not about the shared zero"
    );
    // `app` off the domain returns that very term.
    let off = derived::funcs::app_off_domain(&mut env, &r.ap).expect("app_off_domain");
    let (f, a) = (env.fresh_var(), env.fresh_var());
    let inst = derived::inst_all(&off, &[Term::var(f), Term::var(a)]).expect("instantiate");
    let (_, eq) = inst.concl().as_imp().expect("an implication");
    let (_, rhs) = eq.as_eq().expect("an equation");
    assert_eq!(rhs, r.zero(), "app off the domain does not return the shared zero");

    // The pairing is shared too: `Rec::pair` is `Apply`'s pairing.
    let (u, v) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    assert_eq!(r.pair(u.clone(), v.clone()), r.ap.sets.pair(u, v));
}

/// `Approx(m,h)` has the five conjuncts it claims, and each projects out.
#[test]
fn the_approximation_predicate_has_its_five_parts() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let (m, h) = (Term::var(env.fresh_var()), Term::var(env.fresh_var()));
    let ax = recursion::approx(&mut env, &r, g, &c, &m, &h).expect("approx");

    // A2 is exactly the single-valuedness `funspace` already defines.
    assert_eq!(ax.single, derived::funspace::is_single_valued(&mut env, &r.ap.sets, &h));
    // A4 is `⟨0,c⟩ ∈ h`, at the *shared* zero.
    assert_eq!(ax.base, Formula::mem(r.pair(r.zero(), c.clone()), h.clone()));

    // A5 mentions `succ`, `G` and `app` — it is a real constraint, not `⊤`.
    let k = env.fresh_var();
    let tk = Term::var(k);
    let sk = r.succ_of(tk.clone());
    assert_eq!(
        ax.step,
        Formula::forall(
            k,
            Formula::imp(
                Formula::mem(sk.clone(), m.clone()),
                Formula::mem(
                    r.pair(sk, Term::apply(g, vec![r.apply(h.clone(), tk)])),
                    h.clone()
                )
            )
        ),
        "the step conjunct has the wrong shape"
    );

    // The whole is the right-nested conjunction, and every part projects out.
    let whole = ax.formula();
    assert!(kernel::thm::debug_locally_closed(&whole));
    for (i, part) in ax.parts().iter().enumerate() {
        let proj = ax.proj(i).expect("projection");
        assert_eq!(
            *proj.concl(),
            Formula::imp(whole.clone(), part.clone()),
            "conjunct {i} does not project"
        );
    }
    assert!(ax.proj(5).is_none(), "there are only five conjuncts");

    // Non-vacuity: the conjuncts are pairwise distinct formulas.
    let parts = ax.parts();
    for i in 0..5 {
        for j in (i + 1)..5 {
            assert_ne!(parts[i], parts[j], "conjuncts {i} and {j} coincide");
        }
    }
}

/// `⊢ ∀m. (m ∈ ω → ∀k. (succ(k) ∈ m → k ∈ m))`.
#[test]
fn a_natural_contains_the_predecessors_of_its_successor_members() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let thm = recursion::pred_in_omega_member(&mut env, &r).expect("pred_in_omega_member");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (m, k) = (env.fresh_var(), env.fresh_var());
    let (tm, tk) = (Term::var(m), Term::var(k));
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            m,
            Formula::imp(
                Formula::mem(tm.clone(), r.omega()),
                Formula::forall(
                    k,
                    Formula::imp(
                        Formula::mem(r.succ_of(tk.clone()), tm.clone()),
                        Formula::mem(tk, tm)
                    )
                )
            )
        ),
        "pred_in_omega_member has the wrong shape"
    );

    // Non-vacuity: at `m := succ(succ 0)` and `k := 0` the antecedent
    // `succ(0) ∈ succ(succ 0)` is *provable*, so the lemma really fires.
    let (zero, one) = (r.zero(), r.succ_of(r.zero()));
    let two = r.succ_of(one.clone());
    let two_in_om = {
        let c = r.core();
        let at0 = derived::inst_all(&c.succ_closed, std::slice::from_ref(&zero)).expect("inst");
        let one_mem = kernel::Thm::mp(&at0, &c.zero_mem).expect("0 ∈ ω");
        let at1 = derived::inst_all(&c.succ_closed, std::slice::from_ref(&one)).expect("inst");
        kernel::Thm::mp(&at1, &one_mem).expect("succ 0 ∈ ω")
    };
    assert_eq!(*two_in_om.concl(), Formula::mem(two.clone(), r.omega()));
    let at_two = derived::inst_all(&thm, std::slice::from_ref(&two)).expect("inst");
    let all_k = kernel::Thm::mp(&at_two, &two_in_om).expect("succ(succ 0) ∈ ω");
    let at_zero = derived::inst_all(&all_k, std::slice::from_ref(&zero)).expect("inst");
    let one_in_two = recursion::mem_succ_self(r.core(), &one).expect("succ 0 ∈ succ(succ 0)");
    let concl = kernel::Thm::mp(&at_zero, &one_in_two).expect("the antecedent is proved");
    assert_eq!(*concl.concl(), Formula::mem(zero, two), "0 ∈ succ(succ 0) not derived");
}

/// `⊢ ∀k. (k ∈ ω → ∀m₁ ∀h₁ ∀m₂ ∀h₂. ((m₁ ∈ ω ∧ Approx(m₁,h₁) ∧ m₂ ∈ ω
/// ∧ Approx(m₂,h₂) ∧ k ∈ m₁ ∧ k ∈ m₂) → app(h₁,k) = app(h₂,k)))`.
#[test]
fn approximations_agree_where_their_domains_overlap() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let thm = recursion::approx_agree(&mut env, &r, g, &c).expect("approx_agree");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let k = env.fresh_var();
    let (m1, h1, m2, h2) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tk, tm1, th1, tm2, th2) =
        (Term::var(k), Term::var(m1), Term::var(h1), Term::var(m2), Term::var(h2));
    let a1 = recursion::approx(&mut env, &r, g, &c, &tm1, &th1).expect("approx");
    let a2 = recursion::approx(&mut env, &r, g, &c, &tm2, &th2).expect("approx");
    let hyp = Formula::and(
        Formula::mem(tm1.clone(), r.omega()),
        Formula::and(
            a1.formula(),
            Formula::and(
                Formula::mem(tm2.clone(), r.omega()),
                Formula::and(
                    a2.formula(),
                    Formula::and(
                        Formula::mem(tk.clone(), tm1),
                        Formula::mem(tk.clone(), tm2),
                    ),
                ),
            ),
        ),
    );
    let concl = Formula::eq(r.apply(th1, tk.clone()), r.apply(th2, tk.clone()));
    assert_ne!(hyp, concl, "the lemma must not be trivial");
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            k,
            Formula::imp(
                Formula::mem(tk, r.omega()),
                Formula::forall(
                    m1,
                    Formula::forall(
                        h1,
                        Formula::forall(
                            m2,
                            Formula::forall(h2, Formula::imp(hyp, concl))
                        )
                    )
                )
            )
        ),
        "approx_agree has the wrong shape"
    );
}

/// `⊢ ∀n. (n ∈ ω → ∀a. (a ∈ n → a ∈ ω))` — `ω` is transitive, which is *not*
/// what `omega_trans` says.
#[test]
fn omega_is_transitive() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let thm = recursion::omega_is_transitive(&mut env, &r).expect("omega_is_transitive");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (n, a) = (env.fresh_var(), env.fresh_var());
    let (tn, ta) = (Term::var(n), Term::var(a));
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), r.omega()),
                Formula::forall(
                    a,
                    Formula::imp(Formula::mem(ta.clone(), tn), Formula::mem(ta, r.omega()))
                )
            )
        ),
        "omega_is_transitive has the wrong shape"
    );

    // Non-vacuity, and distinctness from `omega_trans`: applied at
    // `n := succ(0)`, whose member `0` really is in `ω`.
    let (zero, one) = (r.zero(), r.succ_of(r.zero()));
    let one_mem = {
        let c = r.core();
        let at0 = derived::inst_all(&c.succ_closed, std::slice::from_ref(&zero)).expect("inst");
        kernel::Thm::mp(&at0, &c.zero_mem).expect("0 ∈ ω")
    };
    let at_one = derived::inst_all(&thm, std::slice::from_ref(&one)).expect("inst");
    let all_a = kernel::Thm::mp(&at_one, &one_mem).expect("succ 0 ∈ ω");
    let at_zero = derived::inst_all(&all_a, std::slice::from_ref(&zero)).expect("inst");
    let zero_in_one = recursion::mem_succ_self(r.core(), &zero).expect("0 ∈ succ 0");
    let got = kernel::Thm::mp(&at_zero, &zero_in_one).expect("the antecedent is proved");
    assert_eq!(*got.concl(), Formula::mem(zero, r.omega()));
}

/// The apparatus every approximation lemma below needs.
fn approx_base(env: &mut Env) -> (recursion::Rec, kernel::FnSym, Term, kernel::Thm, kernel::Thm) {
    let r = recursion::Rec::new(env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let agree = recursion::approx_agree(env, &r, g, &c).expect("approx_agree");
    let om_trans = recursion::omega_is_transitive(env, &r).expect("omega_is_transitive");
    (r, g, c, agree, om_trans)
}

/// `⊢ ∀m ∀h₁ ∀h₂ ∀p. ((m ∈ ω ∧ (Approx(m,h₁) ∧ Approx(m,h₂))) → (p ∈ h₁ → p ∈ h₂))`.
#[test]
fn one_approximation_is_contained_in_the_other() {
    let mut env = Env::new();
    let (r, g, c, agree, om_trans) = approx_base(&mut env);
    let thm = recursion::approx_subset(&mut env, &r, g, &c, &agree, &om_trans)
        .expect("approx_subset");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (m, h1, h2, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, th1, th2, tp) = (Term::var(m), Term::var(h1), Term::var(h2), Term::var(p));
    let a1 = recursion::approx(&mut env, &r, g, &c, &tm, &th1).expect("approx");
    let a2 = recursion::approx(&mut env, &r, g, &c, &tm, &th2).expect("approx");
    let hyp = Formula::and(
        Formula::mem(tm, r.omega()),
        Formula::and(a1.formula(), a2.formula()),
    );
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            m,
            Formula::forall(
                h1,
                Formula::forall(
                    h2,
                    Formula::forall(
                        p,
                        Formula::imp(
                            hyp,
                            Formula::imp(
                                Formula::mem(tp.clone(), th1),
                                Formula::mem(tp, th2)
                            )
                        )
                    )
                )
            )
        ),
        "approx_subset has the wrong shape"
    );
}

/// `⊢ ∀m ∀h₁ ∀h₂. ((m ∈ ω ∧ (Approx(m,h₁) ∧ Approx(m,h₂))) → h₁ = h₂)`.
#[test]
fn an_approximation_is_determined_by_its_domain() {
    let mut env = Env::new();
    let (r, g, c, agree, om_trans) = approx_base(&mut env);
    let subset = recursion::approx_subset(&mut env, &r, g, &c, &agree, &om_trans)
        .expect("approx_subset");
    let thm = recursion::approx_unique(&mut env, &r, g, &c, &subset).expect("approx_unique");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (m, h1, h2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, th1, th2) = (Term::var(m), Term::var(h1), Term::var(h2));
    let a1 = recursion::approx(&mut env, &r, g, &c, &tm, &th1).expect("approx");
    let a2 = recursion::approx(&mut env, &r, g, &c, &tm, &th2).expect("approx");
    let hyp = Formula::and(
        Formula::mem(tm, r.omega()),
        Formula::and(a1.formula(), a2.formula()),
    );
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            m,
            Formula::forall(
                h1,
                Formula::forall(h2, Formula::imp(hyp, Formula::eq(th1, th2)))
            )
        ),
        "approx_unique has the wrong shape"
    );
}

/// `⊢ ∀s ∀e ∀z. (z ∈ s ∪ {e} ↔ (z ∈ s ∨ z = e))`.
#[test]
fn membership_in_a_set_with_one_element_adjoined() {
    let mut env = Env::new();
    let (sets, mem_sing) = base(&mut env);
    let thm = recursion::mem_adjoin(&mut env, &sets, &mem_sing).expect("mem_adjoin");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (s, e, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ts, te, tz) = (Term::var(s), Term::var(e), Term::var(z));
    let un = recursion::adjoin(&sets, ts.clone(), te.clone());
    assert_ne!(un, ts, "the adjunction must not be the set itself");
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            s,
            Formula::forall(
                e,
                Formula::forall(
                    z,
                    Formula::iff(
                        Formula::mem(tz.clone(), un),
                        Formula::or(Formula::mem(tz.clone(), ts), Formula::eq(tz, te)),
                    )
                )
            )
        ),
        "mem_adjoin has the wrong shape"
    );
}

/// `⊢ ∀m ∀h ∀a ∀b. ((Approx(m,h) ∧ ⟨a,b⟩ ∈ h) → a ∈ m)`.
#[test]
fn an_approximation_holds_no_pair_outside_its_domain() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let thm = recursion::approx_dom(&mut env, &r, g, &c).expect("approx_dom");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (m, h, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tm, th, ta, tb) = (Term::var(m), Term::var(h), Term::var(a), Term::var(b));
    let ax = recursion::approx(&mut env, &r, g, &c, &tm, &th).expect("approx");
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            m,
            Formula::forall(
                h,
                Formula::forall(
                    a,
                    Formula::forall(
                        b,
                        Formula::imp(
                            Formula::and(
                                ax.formula(),
                                Formula::mem(r.pair(ta.clone(), tb), th)
                            ),
                            Formula::mem(ta, tm)
                        )
                    )
                )
            )
        ),
        "approx_dom has the wrong shape"
    );
}

/// `⊢ Approx(succ 0, {⟨0,c⟩})` — the base case of the existence induction.
#[test]
fn the_one_point_graph_approximates_over_the_one_point_domain() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let thm = recursion::approx_one(&mut env, &r, g, &c).expect("approx_one");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let h0 = recursion::one_point_graph(&r, &c);
    let s0 = r.succ_of(r.zero());
    let ax = recursion::approx(&mut env, &r, g, &c, &s0, &h0).expect("approx");
    assert_eq!(*thm.concl(), ax.formula(), "approx_one has the wrong shape");

    // Non-vacuity: the domain really is `succ 0` and not `0`, and the graph
    // really is a singleton rather than the empty set.
    assert_ne!(s0, r.zero());
    assert_ne!(h0, r.zero());
}

/// `⊢ ∀n ∀h. ((n ∈ ω ∧ Approx(succ n,h)) → Approx(succ(succ n), h ∪ {⟨succ n, G(app(h,n))⟩}))`.
#[test]
fn one_more_step_extends_an_approximation() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let dom = recursion::approx_dom(&mut env, &r, g, &c).expect("approx_dom");
    let om_trans = recursion::omega_is_transitive(&mut env, &r).expect("omega_is_transitive");
    let thm = recursion::approx_extend(&mut env, &r, g, &c, &dom, &om_trans)
        .expect("approx_extend");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (n, h) = (env.fresh_var(), env.fresh_var());
    let (tn, th) = (Term::var(n), Term::var(h));
    let sn = r.succ_of(tn.clone());
    let hp = recursion::extension(&r, g, &tn, &th);
    let before = recursion::approx(&mut env, &r, g, &c, &sn, &th).expect("approx");
    let after =
        recursion::approx(&mut env, &r, g, &c, &r.succ_of(sn.clone()), &hp).expect("approx");
    assert_ne!(hp, th, "the extension must not be the graph it extends");
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            n,
            Formula::forall(
                h,
                Formula::imp(
                    Formula::and(Formula::mem(tn, r.omega()), before.formula()),
                    after.formula()
                )
            )
        ),
        "approx_extend has the wrong shape"
    );
}

/// `⊢ ∀n. (n ∈ ω → ∃h. Approx(succ n, h))`.
#[test]
fn every_natural_has_an_approximation_one_step_longer() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let dom = recursion::approx_dom(&mut env, &r, g, &c).expect("approx_dom");
    let om_trans = recursion::omega_is_transitive(&mut env, &r).expect("omega_is_transitive");
    let thm = recursion::approx_exists(&mut env, &r, g, &c, &dom, &om_trans)
        .expect("approx_exists");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (n, h) = (env.fresh_var(), env.fresh_var());
    let (tn, th) = (Term::var(n), Term::var(h));
    let ax = recursion::approx(&mut env, &r, g, &c, &r.succ_of(tn.clone()), &th).expect("approx");
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn, r.omega()),
                Formula::exists(h, ax.formula())
            )
        ),
        "approx_exists has the wrong shape"
    );
}

/// The Replacement instance: `⊢ ∀x. (x ∈ ω → ∃!y. φ)` and the resulting symbol
/// `⊢ ∀y. (y ∈ Γ ↔ ∃x. (x ∈ ω ∧ φ))`.
#[test]
fn the_recursion_has_a_graph() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let dom = recursion::approx_dom(&mut env, &r, g, &c).expect("approx_dom");
    let om_trans = recursion::omega_is_transitive(&mut env, &r).expect("omega_is_transitive");
    let agree = recursion::approx_agree(&mut env, &r, g, &c).expect("approx_agree");
    let subset = recursion::approx_subset(&mut env, &r, g, &c, &agree, &om_trans)
        .expect("approx_subset");
    let unique = recursion::approx_unique(&mut env, &r, g, &c, &subset).expect("approx_unique");
    let exists = recursion::approx_exists(&mut env, &r, g, &c, &dom, &om_trans)
        .expect("approx_exists");
    let fam = recursion::family(&mut env, &r, g, &c, &exists, &unique, &[]).expect("family");

    assert!(kernel::thm::debug_locally_closed(fam.functional.concl()));
    assert!(kernel::thm::debug_locally_closed(fam.members.concl()));
    assert_eq!(fam.graph.arity(), 0);

    let tx = Term::var(fam.x);
    let ty = Term::var(fam.y);
    let x_om = Formula::mem(tx.clone(), r.omega());
    assert_eq!(
        *fam.functional.concl(),
        Formula::forall(
            fam.x,
            Formula::imp(x_om.clone(), kernel::thm::exists_unique(&mut env, fam.y, &fam.phi))
        ),
        "Family::functional has the wrong shape"
    );
    assert_eq!(
        *fam.members.concl(),
        Formula::forall(
            fam.y,
            Formula::iff(
                Formula::mem(ty, fam.set()),
                Formula::exists(fam.x, Formula::and(x_om, fam.phi.clone()))
            )
        ),
        "Family::members has the wrong shape"
    );
}

/// The whole existence half: `⊢ RecFn(Γ)`.
#[test]
fn the_graph_is_the_recursion() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let dom = recursion::approx_dom(&mut env, &r, g, &c).expect("approx_dom");
    let om_trans = recursion::omega_is_transitive(&mut env, &r).expect("omega_is_transitive");
    let agree = recursion::approx_agree(&mut env, &r, g, &c).expect("approx_agree");
    let subset = recursion::approx_subset(&mut env, &r, g, &c, &agree, &om_trans)
        .expect("approx_subset");
    let unique = recursion::approx_unique(&mut env, &r, g, &c, &subset).expect("approx_unique");
    let exists = recursion::approx_exists(&mut env, &r, g, &c, &dom, &om_trans)
        .expect("approx_exists");
    let fam = recursion::family(&mut env, &r, g, &c, &exists, &unique, &[]).expect("family");
    let it = recursion::iterate(&mut env, &r, g, &c, fam, &unique, &exists, &agree)
        .expect("iterate");

    assert!(kernel::thm::debug_locally_closed(it.property.concl()));
    let spec = recursion::rec_fn(&mut env, &r, g, &c, &it.set()).expect("rec_fn");
    assert_eq!(*it.property.concl(), spec.formula(), "RecFn(Γ) has the wrong shape");

    // The two equations, spelled out, are really about `app` and not vacuous.
    let n = env.fresh_var();
    let tn = Term::var(n);
    assert_eq!(spec.base, Formula::eq(r.apply(it.set(), r.zero()), c.clone()));
    assert_ne!(r.apply(it.set(), r.zero()), c);
    assert_eq!(
        spec.step,
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), r.omega()),
                Formula::eq(
                    r.apply(it.set(), r.succ_of(tn.clone())),
                    Term::apply(g, vec![r.apply(it.set(), tn)])
                )
            )
        )
    );
}

/// `⊢ ∀f₁ ∀f₂. ((RecFn(f₁) ∧ RecFn(f₂)) → f₁ = f₂)` — the recursion is unique.
#[test]
fn there_is_at_most_one_recursion() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let c = Term::apply(env.declare(0), vec![]);
    let agree = recursion::rec_agree(&mut env, &r, g, &c).expect("rec_agree");
    let subset = recursion::rec_subset(&mut env, &r, g, &c, &agree).expect("rec_subset");
    let thm = recursion::rec_unique(&mut env, &r, g, &c, &subset).expect("rec_unique");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (f1, f2) = (env.fresh_var(), env.fresh_var());
    let (tf1, tf2) = (Term::var(f1), Term::var(f2));
    let s1 = recursion::rec_fn(&mut env, &r, g, &c, &tf1).expect("rec_fn");
    let s2 = recursion::rec_fn(&mut env, &r, g, &c, &tf2).expect("rec_fn");
    assert_ne!(s1.formula(), s2.formula(), "the two sides must not coincide");
    assert_eq!(
        *thm.concl(),
        Formula::forall(
            f1,
            Formula::forall(
                f2,
                Formula::imp(
                    Formula::and(s1.formula(), s2.formula()),
                    Formula::eq(tf1, tf2)
                )
            )
        ),
        "rec_unique has the wrong shape"
    );
}

/// The recursion theorem itself, over a **free** base variable, so `iter` comes
/// out unary: `⊢ ∀c. RecFn(iter(c))`, with both equations projected off it.
#[test]
fn the_recursion_theorem() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let cv = env.fresh_var();
    let c = Term::var(cv);
    let rec = recursion::recursion(&mut env, &r, g, &c, &[cv]).expect("recursion");

    assert_eq!(rec.iter.arity(), 1);
    assert!(kernel::thm::debug_locally_closed(rec.exists_unique.concl()));
    assert!(kernel::thm::debug_locally_closed(rec.iter_ax.concl()));

    let f = env.fresh_var();
    let phi = recursion::rec_fn(&mut env, &r, g, &c, &Term::var(f)).expect("rec_fn").formula();
    assert_eq!(
        *rec.exists_unique.concl(),
        kernel::thm::exists_unique(&mut env, f, &phi),
        "the ∃! has the wrong shape"
    );

    // The base equation, and the step equation, at the defined symbol.
    let it = rec.set();
    assert_eq!(*rec.base.concl(), Formula::eq(r.apply(it.clone(), r.zero()), c.clone()));
    let n = env.fresh_var();
    let tn = Term::var(n);
    assert_eq!(
        *rec.step.concl(),
        Formula::forall(
            n,
            Formula::imp(
                Formula::mem(tn.clone(), r.omega()),
                Formula::eq(
                    r.apply(it.clone(), r.succ_of(tn.clone())),
                    Term::apply(g, vec![r.apply(it, tn)])
                )
            )
        ),
        "the step equation has the wrong shape"
    );
}

/// **Non-vacuity.** At `c := ∅` and `G := 𝒫`, the first two values of `iter`
/// are *provably distinct*: `⊢ ¬(app(iter,0) = app(iter, succ 0))`.
///
/// Without this the whole construction could be satisfied by a constant
/// function and every equation above would still hold.
#[test]
fn the_iteration_of_the_power_set_actually_moves() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let pow = r.core().pow;
    let zero = r.zero();
    let rec = recursion::recursion(&mut env, &r, pow, &zero, &[]).expect("recursion");

    let it = rec.set();
    let a0 = r.apply(it.clone(), zero.clone());
    let a1 = r.apply(it, r.succ_of(zero.clone()));
    let pow_of = |t: Term| Term::apply(pow, vec![t]);

    // `⊢ app(iter, succ 0) = 𝒫(app(iter, 0))`, then `= 𝒫∅` by the base equation.
    let step0 = kernel::Thm::mp(
        &kernel::Thm::ax_inst(rec.step.concl().clone(), zero.clone()).expect("inst"),
        &rec.step,
    )
    .expect("mp");
    let s = kernel::Thm::mp(&step0, &r.core().zero_mem).expect("0 ∈ ω");
    let w = env.fresh_var();
    let congr = derived::mpd_const(
        &kernel::Thm::eq_leibniz(
            a0.clone(),
            zero.clone(),
            w,
            Formula::eq(pow_of(a0.clone()), pow_of(Term::var(w))),
        ),
        &kernel::Thm::eq_refl(pow_of(a0.clone())),
    )
    .expect("congruence");
    let a1_pow = derived::eq_trans(&mut env, &s, &kernel::Thm::mp(&congr, &rec.base).expect("mp"))
        .expect("a1 = 𝒫∅");
    assert_eq!(*a1_pow.concl(), Formula::eq(a1.clone(), pow_of(zero.clone())));

    // `⊢ ∅ ∈ 𝒫∅`, because `∅ ⊆ ∅`.
    let v = env.fresh_var();
    let sub = kernel::Thm::gen(
        v,
        &derived::imp_refl(Formula::mem(Term::var(v), zero.clone())),
    );
    assert_eq!(*sub.concl(), kernel::thm::subset(&mut env, zero.clone(), zero.clone()));
    let in_pow = kernel::Thm::mp(
        &derived::iff_mpr(
            &derived::inst_all(&r.core().pow_ax, &[zero.clone(), zero.clone()]).expect("inst"),
        )
        .expect("mpr"),
        &sub,
    )
    .expect("∅ ∈ 𝒫∅");

    // Under `H := app(iter,0) = app(iter,succ 0)` we get `∅ = 𝒫∅`, hence `∅ ∈ ∅`.
    let hyp = Formula::eq(a0.clone(), a1.clone());
    let h_zero_a0 = derived::a1i(
        &derived::eq_symm(&mut env, &rec.base).expect("symm"),
        hyp.clone(),
    );
    let h_a0_a1 = derived::imp_refl(hyp.clone());
    let h_left = derived::recursion::hyp_eq_trans(&mut env, &h_zero_a0, &h_a0_a1).expect("trans");
    let h_pow = derived::recursion::hyp_eq_trans(
        &mut env,
        &h_left,
        &derived::a1i(&a1_pow, hyp.clone()),
    )
    .expect("trans");
    let h_sym = derived::recursion::hyp_eq_symm(&mut env, &h_pow).expect("symm");
    let w2 = env.fresh_var();
    let leib = kernel::Thm::eq_leibniz(
        pow_of(zero.clone()),
        zero.clone(),
        w2,
        Formula::mem(zero.clone(), Term::var(w2)),
    );
    let h_self = derived::hyp_mp(
        &derived::hyp_mp(&derived::a1i(&leib, hyp.clone()), &h_sym).expect("mp"),
        &derived::a1i(&in_pow, hyp.clone()),
    )
    .expect("∅ ∈ ∅");
    let empty_at =
        derived::inst_all(&r.core().empty_ax, std::slice::from_ref(&zero)).expect("inst");
    let out = derived::syl(&h_self, &empty_at).expect("contradiction");

    assert_eq!(*out.concl(), Formula::not(hyp), "the two values were not separated");
    assert!(kernel::thm::debug_locally_closed(out.concl()));
}

/// `⊢ ∀z. (z ∈ tower(c) ↔ ∃n. (n ∈ ω ∧ z ∈ app(iter(c), n)))`.
#[test]
fn the_tower_is_the_union_of_the_iteration() {
    let mut env = Env::new();
    let r = recursion::Rec::new(&mut env).expect("Rec");
    let g = env.declare(1);
    let cv = env.fresh_var();
    let c = Term::var(cv);
    let rec = recursion::recursion(&mut env, &r, g, &c, &[cv]).expect("recursion");
    let tw = recursion::omega_tower(&mut env, &r, &rec, &[cv]).expect("omega_tower");

    assert_eq!(tw.tower.arity(), 1);
    assert!(kernel::thm::debug_locally_closed(tw.members.concl()));
    assert_ne!(tw.set(), rec.set(), "the tower must not be the iteration itself");

    let (z, n) = (env.fresh_var(), env.fresh_var());
    let (tz, tn) = (Term::var(z), Term::var(n));
    assert_eq!(
        *tw.members.concl(),
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), tw.set()),
                Formula::exists(
                    n,
                    Formula::and(
                        Formula::mem(tn.clone(), r.omega()),
                        Formula::mem(tz, r.apply(rec.set(), tn))
                    )
                )
            )
        ),
        "the tower has the wrong shape"
    );
}
