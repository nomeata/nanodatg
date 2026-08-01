//! The conditional singleton `[φ]`, and `Eq` / `And` as subsingletons.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and compares with `assert_eq!`, so a theorem with the right
//! *name* but the wrong *shape* fails here.
//!
//! The module is a subsingleton development, which is exactly where a vacuous
//! result hides: if `[φ]` were always `∅`, or always `1`, every lemma would
//! still be provable and none would say anything. So both polarities are pinned
//! on concrete instances — see the "non-vacuity" section at the bottom.

use kernel::{Env, Formula, Term, Thm};

use derived::prop::{self, Props, Trunc};
use derived::sums::Sums;

/// A conditional singleton to exercise the generic lemmas on: `[• ∈ a]`, over
/// the single parameter `a`.
struct Probe {
    s: Sums,
    /// The symbol `[·]` was defined as.
    f: kernel::FnSym,
    /// The parameter variable `a`.
    a: kernel::FreeVar,
    /// `φ = • ∈ a`.
    phi: Formula,
    /// The term `[φ]`.
    c: Term,
    /// `⊢ ∀z. (z ∈ [φ] ↔ (z ∈ 1 ∧ φ))`, already instantiated at `a`.
    chi: Thm,
}

fn probe(env: &mut Env) -> Probe {
    let s = Sums::new(env).expect("sums");
    let a = env.fresh_var();
    let phi = Formula::mem(s.point(), Term::var(a));
    let (f, ax) = prop::conditional_singleton(env, &s, &[a], &phi).expect("conditional singleton");
    let c = Term::apply(f, vec![Term::var(a)]);
    let chi = derived::inst_all(&ax, &[Term::var(a)]).expect("instantiate");
    Probe { s, f, a, phi, c, chi }
}

/// The defining property: `⊢ ∀a ∀z. (z ∈ [φ] ↔ (z ∈ 1 ∧ φ))`.
#[test]
fn the_conditional_singleton_has_its_defining_property() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let a = env.fresh_var();
    let phi = Formula::mem(s.point(), Term::var(a));
    let (f, ax) = prop::conditional_singleton(&mut env, &s, &[a], &phi).expect("conditional singleton");
    assert!(kernel::thm::debug_locally_closed(ax.concl()));

    let z = env.fresh_var();
    let (tz, ta) = (Term::var(z), Term::var(a));
    let want = Formula::forall(
        a,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz.clone(), Term::apply(f, vec![ta])),
                Formula::and(Formula::mem(tz, s.unit()), phi.clone()),
            ),
        ),
    );
    assert_eq!(*ax.concl(), want);

    // The guard really is membership in the unit set, not in something else.
    assert_ne!(s.unit(), s.point());
}

/// `⊢ φ → • ∈ [φ]`.
#[test]
fn a_proof_inhabits_the_denotation() {
    let mut env = Env::new();
    let p = probe(&mut env);
    let out = prop::cond_intro(&p.s, &p.phi, &p.c, &p.chi).expect("cond_intro");
    assert!(kernel::thm::debug_locally_closed(out.concl()));
    assert_eq!(
        *out.concl(),
        Formula::imp(p.phi.clone(), Formula::mem(p.s.point(), p.c.clone()))
    );
}

/// `⊢ • ∈ [φ] → φ` — the denotation is not vacuously inhabited.
#[test]
fn the_denotation_is_sound() {
    let mut env = Env::new();
    let p = probe(&mut env);
    let out = prop::cond_elim(&p.s, &p.phi, &p.c, &p.chi).expect("cond_elim");
    assert!(kernel::thm::debug_locally_closed(out.concl()));
    assert_eq!(
        *out.concl(),
        Formula::imp(Formula::mem(p.s.point(), p.c.clone()), p.phi.clone())
    );
}

/// `⊢ [φ] ⊆ 1` — a conditional singleton is a `Prop`.
#[test]
fn the_denotation_is_a_prop() {
    let mut env = Env::new();
    let p = probe(&mut env);
    let out = prop::cond_subset_unit(&mut env, &p.s, &p.phi, &p.c, &p.chi).expect("cond_subset_unit");
    assert!(kernel::thm::debug_locally_closed(out.concl()));

    let z = env.fresh_var();
    let tz = Term::var(z);
    let want = Formula::forall(
        z,
        Formula::imp(Formula::mem(tz.clone(), p.c.clone()), Formula::mem(tz, p.s.unit())),
    );
    assert_eq!(*out.concl(), want);
    assert_eq!(*out.concl(), kernel::thm::subset(&mut env, p.c.clone(), p.s.unit()));
}

/// `⊢ ∀x ∀y. ((x ∈ [φ] ∧ y ∈ [φ]) → x = y)` — proof irrelevance.
#[test]
fn the_denotation_is_a_subsingleton() {
    let mut env = Env::new();
    let p = probe(&mut env);
    let out = prop::cond_subsingleton(&mut env, &p.s, &p.phi, &p.c, &p.chi).expect("cond_subsingleton");
    assert!(kernel::thm::debug_locally_closed(out.concl()));

    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let want = Formula::forall(
        x,
        Formula::forall(
            y,
            Formula::imp(
                Formula::and(
                    Formula::mem(tx.clone(), p.c.clone()),
                    Formula::mem(ty.clone(), p.c.clone()),
                ),
                Formula::eq(tx, ty),
            ),
        ),
    );
    assert_eq!(*out.concl(), want);
}

/// `⊢ ¬φ → [φ] = 0`.
#[test]
fn a_false_proposition_denotes_zero() {
    let mut env = Env::new();
    let p = probe(&mut env);
    let out = prop::cond_false(&mut env, &p.s, &p.phi, &p.c, &p.chi).expect("cond_false");
    assert!(kernel::thm::debug_locally_closed(out.concl()));
    assert_eq!(
        *out.concl(),
        Formula::imp(Formula::not(p.phi.clone()), Formula::eq(p.c.clone(), p.s.zero()))
    );
    // Not the same conclusion as `cond_true`'s: `0` and `1` are different terms.
    assert_ne!(p.s.zero(), p.s.unit());
}

/// `⊢ φ → [φ] = 1`.
#[test]
fn a_true_proposition_denotes_one() {
    let mut env = Env::new();
    let p = probe(&mut env);
    let out = prop::cond_true(&mut env, &p.s, &p.phi, &p.c, &p.chi).expect("cond_true");
    assert!(kernel::thm::debug_locally_closed(out.concl()));
    assert_eq!(
        *out.concl(),
        Formula::imp(p.phi.clone(), Formula::eq(p.c.clone(), p.s.unit()))
    );
}

/// Both polarities of the probe are actually reached, so neither `cond_true`
/// nor `cond_false` is vacuous: at `a := 1` the condition `• ∈ a` is proved by
/// `unit_mem`, and at `a := 0` it is refuted by the empty set. The two
/// instances of `[φ]` are therefore proved equal to *different* sets.
#[test]
fn both_polarities_are_reachable_on_the_probe() {
    let mut env = Env::new();
    let p = probe(&mut env);

    let true_case = Thm::gen(p.a, &prop::cond_true(&mut env, &p.s, &p.phi, &p.c, &p.chi).expect("cond_true"));
    let false_case = Thm::gen(p.a, &prop::cond_false(&mut env, &p.s, &p.phi, &p.c, &p.chi).expect("cond_false"));

    // At `a := 1`: `φ` is `• ∈ 1`, which `unit_mem` proves, so `[φ] = 1`.
    let c_one = Term::apply(p.f, vec![p.s.unit()]);
    let at_one = derived::inst_all(&true_case, &[p.s.unit()]).expect("inst");
    let eq_one = Thm::mp(&at_one, &p.s.unit_mem).expect("mp");
    assert_eq!(*eq_one.concl(), Formula::eq(c_one.clone(), p.s.unit()));

    // At `a := 0`: `φ` is `• ∈ 0`, which the empty set refutes, so `[φ] = 0`.
    let c_zero = Term::apply(p.f, vec![p.s.zero()]);
    let not_mem = derived::inst_all(&p.s.ap.empty_ax, &[p.s.point()]).expect("empty");
    let at_zero = derived::inst_all(&false_case, &[p.s.zero()]).expect("inst");
    let eq_zero = Thm::mp(&at_zero, &not_mem).expect("mp");
    assert_eq!(*eq_zero.concl(), Formula::eq(c_zero.clone(), p.s.zero()));

    assert_ne!(c_one, c_zero);
    assert_ne!(p.s.unit(), p.s.zero());
}

// ─────────────────────────────────────────────────────────────────────────────
// `Eq`.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀a. • ∈ eq_set(a,a)` — the typing of `Eq.refl`.
#[test]
fn eq_refl_is_typed() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(p.eq_refl.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let want = Formula::forall(a, Formula::mem(p.sums.point(), p.eq_of(ta.clone(), ta)));
    assert_eq!(*p.eq_refl.concl(), want);
}

/// `⊢ ∀a ∀b. (• ∈ eq_set(a,b) → a = b)` — soundness.
#[test]
fn eq_is_sound() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(p.eq_sound.concl()));

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::imp(
                Formula::mem(p.sums.point(), p.eq_of(ta.clone(), tb.clone())),
                Formula::eq(ta, tb),
            ),
        ),
    );
    assert_eq!(*p.eq_sound.concl(), want);
}

/// `⊢ ∀a ∀b. eq_set(a,b) ⊆ 1`.
#[test]
fn eq_is_a_prop() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(p.eq_subset.concl()));

    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz.clone(), p.eq_of(ta, tb)),
                    Formula::mem(tz, p.sums.unit()),
                ),
            ),
        ),
    );
    assert_eq!(*p.eq_subset.concl(), want);
}

/// `⊢ ∀a ∀b ∀x ∀y. ((x ∈ eq_set(a,b) ∧ y ∈ eq_set(a,b)) → x = y)`.
#[test]
fn eq_is_a_subsingleton() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(p.eq_irrel.concl()));

    let (a, b, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx, ty) = (Term::var(a), Term::var(b), Term::var(x), Term::var(y));
    let e = p.eq_of(ta, tb);
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                x,
                Formula::forall(
                    y,
                    Formula::imp(
                        Formula::and(
                            Formula::mem(tx.clone(), e.clone()),
                            Formula::mem(ty.clone(), e),
                        ),
                        Formula::eq(tx, ty),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*p.eq_irrel.concl(), want);
}

/// The defining property of `Eq`: `⊢ ∀a ∀b ∀z. (z ∈ eq_set(a,b) ↔ (z ∈ 1 ∧ a = b))`.
#[test]
fn eq_has_its_defining_property() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(p.eq_ax.concl()));

    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                z,
                Formula::iff(
                    Formula::mem(tz.clone(), p.eq_of(ta.clone(), tb.clone())),
                    Formula::and(Formula::mem(tz, p.sums.unit()), Formula::eq(ta, tb)),
                ),
            ),
        ),
    );
    assert_eq!(*p.eq_ax.concl(), want);
}

// ─────────────────────────────────────────────────────────────────────────────
// `And`.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀p ∀q. ((• ∈ p ∧ • ∈ q) → • ∈ and_set(p,q))` — the typing of `And.intro`.
#[test]
fn and_intro_is_typed() {
    let mut env = Env::new();
    let pr = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(pr.and_intro.concl()));

    let (p, q) = (env.fresh_var(), env.fresh_var());
    let (tp, tq) = (Term::var(p), Term::var(q));
    let pt = pr.sums.point();
    let want = Formula::forall(
        p,
        Formula::forall(
            q,
            Formula::imp(
                Formula::and(
                    Formula::mem(pt.clone(), tp.clone()),
                    Formula::mem(pt.clone(), tq.clone()),
                ),
                Formula::mem(pt, pr.and_of(tp, tq)),
            ),
        ),
    );
    assert_eq!(*pr.and_intro.concl(), want);
}

/// `⊢ ∀p ∀q. (• ∈ and_set(p,q) → • ∈ p)` and the right projection.
#[test]
fn and_projects_both_ways() {
    let mut env = Env::new();
    let pr = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(pr.and_proj_l.concl()));
    assert!(kernel::thm::debug_locally_closed(pr.and_proj_r.concl()));

    let (p, q) = (env.fresh_var(), env.fresh_var());
    let (tp, tq) = (Term::var(p), Term::var(q));
    let pt = pr.sums.point();
    let mem_and = Formula::mem(pt.clone(), pr.and_of(tp.clone(), tq.clone()));

    let want_l = Formula::forall(
        p,
        Formula::forall(q, Formula::imp(mem_and.clone(), Formula::mem(pt.clone(), tp))),
    );
    let want_r =
        Formula::forall(p, Formula::forall(q, Formula::imp(mem_and, Formula::mem(pt, tq))));
    assert_eq!(*pr.and_proj_l.concl(), want_l);
    assert_eq!(*pr.and_proj_r.concl(), want_r);
    assert_ne!(want_l, want_r);
}

/// `⊢ ∀p ∀q. and_set(p,q) ⊆ 1`.
#[test]
fn and_is_a_prop() {
    let mut env = Env::new();
    let pr = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(pr.and_subset.concl()));

    let (p, q, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tq, tz) = (Term::var(p), Term::var(q), Term::var(z));
    let want = Formula::forall(
        p,
        Formula::forall(
            q,
            Formula::forall(
                z,
                Formula::imp(
                    Formula::mem(tz.clone(), pr.and_of(tp, tq)),
                    Formula::mem(tz, pr.sums.unit()),
                ),
            ),
        ),
    );
    assert_eq!(*pr.and_subset.concl(), want);
}

/// The defining property of `And`:
/// `⊢ ∀p ∀q ∀z. (z ∈ and_set(p,q) ↔ (z ∈ 1 ∧ (• ∈ p ∧ • ∈ q)))`.
#[test]
fn and_has_its_defining_property() {
    let mut env = Env::new();
    let pr = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(pr.and_ax.concl()));

    let (p, q, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tq, tz) = (Term::var(p), Term::var(q), Term::var(z));
    let pt = pr.sums.point();
    let want = Formula::forall(
        p,
        Formula::forall(
            q,
            Formula::forall(
                z,
                Formula::iff(
                    Formula::mem(tz.clone(), pr.and_of(tp.clone(), tq.clone())),
                    Formula::and(
                        Formula::mem(tz, pr.sums.unit()),
                        Formula::and(Formula::mem(pt.clone(), tp), Formula::mem(pt, tq)),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*pr.and_ax.concl(), want);
}

/// `⊢ ∀p ∀q ∀x ∀y. ((x ∈ and_set(p,q) ∧ y ∈ and_set(p,q)) → x = y)`.
#[test]
fn and_is_a_subsingleton() {
    let mut env = Env::new();
    let pr = Props::new(&mut env).expect("props");
    assert!(kernel::thm::debug_locally_closed(pr.and_irrel.concl()));

    let (p, q, x, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tp, tq, tx, ty) = (Term::var(p), Term::var(q), Term::var(x), Term::var(y));
    let c = pr.and_of(tp, tq);
    let want = Formula::forall(
        p,
        Formula::forall(
            q,
            Formula::forall(
                x,
                Formula::forall(
                    y,
                    Formula::imp(
                        Formula::and(
                            Formula::mem(tx.clone(), c.clone()),
                            Formula::mem(ty.clone(), c),
                        ),
                        Formula::eq(tx, ty),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*pr.and_irrel.concl(), want);
}

// ─────────────────────────────────────────────────────────────────────────────
// Non-vacuity — the whole game.
//
// `∅` and `1 = {∅}` are distinct sets (`Sums::tags_distinct`), so `eq_set(∅,∅)`
// is a true equation's denotation and `eq_set(∅,1)` a false one's. Both
// polarities are derived, and the two denotations are proved *unequal*.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ • ∈ eq_set(∅,∅)` and `⊢ ¬(• ∈ eq_set(∅,1))`.
#[test]
fn eq_is_inhabited_exactly_when_it_should_be() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    let (zero, one, pt) = (p.sums.zero(), p.sums.unit(), p.sums.point());

    // True: `∅ = ∅`.
    let inhabited = derived::inst_all(&p.eq_refl, std::slice::from_ref(&zero)).expect("inst");
    assert_eq!(*inhabited.concl(), Formula::mem(pt.clone(), p.eq_of(zero.clone(), zero.clone())));

    // False: `∅ = 1` is refuted, so nothing inhabits its denotation.
    let sound = derived::inst_all(&p.eq_sound, &[zero.clone(), one.clone()]).expect("inst");
    let empty = derived::syl(&sound, &p.sums.tags_distinct).expect("syl");
    assert_eq!(
        *empty.concl(),
        Formula::not(Formula::mem(pt, p.eq_of(zero.clone(), one.clone())))
    );

    // And the two denotations are different terms.
    assert_ne!(p.eq_of(zero.clone(), zero.clone()), p.eq_of(zero, one));
}

/// `⊢ ¬(eq_set(∅,∅) = eq_set(∅,1))` — the denotations differ *as sets*, not
/// merely as terms. Without this the whole module could be vacuous.
#[test]
fn a_true_equation_denotes_a_different_set_from_a_false_one() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    let (zero, one) = (p.sums.zero(), p.sums.unit());

    assert!(kernel::thm::debug_locally_closed(p.eq_distinct.concl()));
    let at = derived::inst_all(&p.eq_distinct, &[zero.clone(), one.clone()]).expect("inst");
    let out = Thm::mp(&at, &p.sums.tags_distinct).expect("mp");
    assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(
            p.eq_of(zero.clone(), zero.clone()),
            p.eq_of(zero, one)
        ))
    );
}

/// `⊢ • ∈ and_set(1,1)` and `⊢ ¬(• ∈ and_set(1,0))` — both polarities again.
#[test]
fn and_is_inhabited_exactly_when_it_should_be() {
    let mut env = Env::new();
    let p = Props::new(&mut env).expect("props");
    let (zero, one, pt) = (p.sums.zero(), p.sums.unit(), p.sums.point());

    // True: `• ∈ 1 ∧ • ∈ 1`.
    let at = derived::inst_all(&p.and_intro, &[one.clone(), one.clone()]).expect("inst");
    let both = derived::and_intro(&p.sums.unit_mem, &p.sums.unit_mem);
    let inhabited = Thm::mp(&at, &both).expect("mp");
    assert_eq!(*inhabited.concl(), Formula::mem(pt.clone(), p.and_of(one.clone(), one.clone())));

    // False: nothing is in `0`, so the right projection is refuted.
    let proj = derived::inst_all(&p.and_proj_r, &[one.clone(), zero.clone()]).expect("inst");
    let not_in_zero = derived::inst_all(&p.sums.ap.empty_ax, std::slice::from_ref(&pt)).expect("inst");
    let empty = derived::syl(&proj, &not_in_zero).expect("syl");
    assert_eq!(
        *empty.concl(),
        Formula::not(Formula::mem(pt, p.and_of(one.clone(), zero.clone())))
    );

    assert_ne!(p.and_of(one.clone(), one.clone()), p.and_of(one, zero));
}

// ─────────────────────────────────────────────────────────────────────────────
// Propositional truncation `‖a‖ = [∃x. x ∈ a]` — the third instance.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀a ∀z. (z ∈ ‖a‖ ↔ (z ∈ 1 ∧ ∃x. x ∈ a))` — the defining property,
/// rebuilt from the kernel's constructors.
#[test]
fn the_truncation_has_its_defining_property() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let t = Trunc::new(&mut env, &s).expect("trunc");
    assert!(kernel::thm::debug_locally_closed(t.trunc_ax.concl()));

    let (a, z, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let ta = Term::var(a);
    let want = Formula::forall(
        a,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(Term::var(z), t.of(ta.clone())),
                Formula::and(
                    Formula::mem(Term::var(z), s.unit()),
                    Formula::exists(x, Formula::mem(Term::var(x), ta)),
                ),
            ),
        ),
    );
    assert_eq!(*t.trunc_ax.concl(), want);
}

/// `⊢ ∀a ∀w. (w ∈ a → • ∈ ‖a‖)` — the typing of `|e|`, stated at an element
/// rather than at an existential, and discharged at `• ∈ 1`.
#[test]
fn an_element_puts_the_point_in_the_truncation() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let t = Trunc::new(&mut env, &s).expect("trunc");
    assert!(kernel::thm::debug_locally_closed(t.intro.concl()));

    let (a, w) = (env.fresh_var(), env.fresh_var());
    let (ta, tw) = (Term::var(a), Term::var(w));
    let want = Formula::forall(
        a,
        Formula::forall(
            w,
            Formula::imp(Formula::mem(tw, ta.clone()), Formula::mem(s.point(), t.of(ta))),
        ),
    );
    assert_eq!(*t.intro.concl(), want);

    // Not vacuous: `• ∈ 1` really does yield `• ∈ ‖1‖`.
    let (one, pt) = (s.unit(), s.point());
    let at = derived::inst_all(&t.intro, &[one.clone(), pt.clone()]).expect("inst");
    let inhabited = Thm::mp(&at, &s.unit_mem).expect("mp");
    assert_eq!(*inhabited.concl(), Formula::mem(pt, t.of(one)));
}

/// `⊢ ∀a. (• ∈ ‖a‖ → ∃x. x ∈ a)` — soundness. Composed with `¬∃x. x ∈ 0` it
/// refutes `• ∈ ‖0‖`, so the truncation is not inhabited regardless.
#[test]
fn the_truncation_is_inhabited_only_when_its_argument_is() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let t = Trunc::new(&mut env, &s).expect("trunc");
    assert!(kernel::thm::debug_locally_closed(t.elim.concl()));

    let (a, x) = (env.fresh_var(), env.fresh_var());
    let ta = Term::var(a);
    let want = Formula::forall(
        a,
        Formula::imp(
            Formula::mem(s.point(), t.of(ta.clone())),
            Formula::exists(x, Formula::mem(Term::var(x), ta)),
        ),
    );
    assert_eq!(*t.elim.concl(), want);

    let (zero, pt) = (s.zero(), s.point());
    let at = derived::inst_all(&t.elim, std::slice::from_ref(&zero)).expect("inst");
    let empty = derived::syl(&at, &s.zero_empty).expect("syl");
    assert_eq!(*empty.concl(), Formula::not(Formula::mem(pt, t.of(zero))));
}

/// `⊢ ‖a‖ ⊆ 1` and proof irrelevance: a truncation is a `Prop`.
#[test]
fn a_truncation_is_a_proposition() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let t = Trunc::new(&mut env, &s).expect("trunc");
    assert!(kernel::thm::debug_locally_closed(t.subset.concl()));
    assert!(kernel::thm::debug_locally_closed(t.irrel.concl()));

    let (a, z) = (env.fresh_var(), env.fresh_var());
    let (ta, tz) = (Term::var(a), Term::var(z));
    assert_eq!(
        *t.subset.concl(),
        Formula::forall(
            a,
            Formula::forall(
                z,
                Formula::imp(Formula::mem(tz.clone(), t.of(ta.clone())), Formula::mem(tz, s.unit()))
            )
        )
    );

    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    assert_eq!(
        *t.irrel.concl(),
        Formula::forall(
            a,
            Formula::forall(
                x,
                Formula::forall(
                    y,
                    Formula::imp(
                        Formula::and(
                            Formula::mem(tx.clone(), t.of(ta.clone())),
                            Formula::mem(ty.clone(), t.of(ta)),
                        ),
                        Formula::eq(tx, ty),
                    )
                )
            )
        )
    );
}

/// `⊢ ‖1‖ = 1`, `⊢ ‖0‖ = 0` and `⊢ ¬(‖0‖ = ‖1‖)` — **both polarities**, and
/// the fact that they are different sets. Without the last one every lemma
/// above would survive `‖·‖` being constant.
#[test]
fn the_truncation_computes_at_both_polarities() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let t = Trunc::new(&mut env, &s).expect("trunc");
    let (zero, one) = (s.zero(), s.unit());

    assert!(kernel::thm::debug_locally_closed(t.unit.concl()));
    assert!(kernel::thm::debug_locally_closed(t.zero.concl()));
    assert_eq!(*t.unit.concl(), Formula::eq(t.of(one.clone()), one.clone()));
    assert_eq!(*t.zero.concl(), Formula::eq(t.of(zero.clone()), zero.clone()));

    // The two answers are different sets, not merely different terms — which is
    // what stops `‖·‖` from being constant and every lemma above from being
    // vacuous.
    assert!(kernel::thm::debug_locally_closed(t.distinct.concl()));
    assert_eq!(
        *t.distinct.concl(),
        Formula::not(Formula::eq(t.of(zero.clone()), t.of(one.clone())))
    );
    assert_ne!(t.of(zero), t.of(one));
}

// ─────────────────────────────────────────────────────────────────────────────
// `∀`-extensionality, and the house rule.
// ─────────────────────────────────────────────────────────────────────────────

/// A conditional singleton `chi(p⃗,A) = [∀x ∈ A. • ∈ b(p⃗,x)]` over a body
/// symbol of arity `k+1` — the shape [`derived::prop::cond_ext_n`] relates.
fn cond_over(env: &mut Env, s: &Sums, b: kernel::FnSym) -> (kernel::FnSym, Thm) {
    let k = b.arity() as usize - 1;
    let mut params: Vec<kernel::FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let (x, a) = (env.fresh_var(), env.fresh_var());
    let mut bargs: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    bargs.push(Term::var(x));
    let phi = Formula::forall(
        x,
        Formula::imp(
            Formula::mem(Term::var(x), Term::var(a)),
            Formula::mem(s.point(), Term::apply(b, bargs)),
        ),
    );
    params.push(a);
    let (chi, ax) =
        prop::conditional_singleton(env, s, &params, &phi).expect("conditional_singleton");
    (chi, ax)
}

/// A characteristic theorem that holds only **under an open hypothesis** is
/// refused, even though it concludes exactly the right formula.
///
/// This is the guard the [`derived::hyp::Hyp`] layer cannot supply. `Hyp`
/// tracks the antecedents `cond_ext_n` introduces itself, all of which it
/// discharges; a `Γ` that arrives *on* `chi_ax` is invisible to it, because
/// `Hyp::lift` records `hyps: []` for whatever theorem it is handed and
/// `Hyp::into_thm` only checks that list. So without the hypothesis half of
/// [`derived::establishes`] this returns a theorem stated `⊢ ∀p⃗ ∀q⃗ ∀A ∀A'. (…)`
/// that in fact still assumes `x ∈ A`.
#[test]
fn a_hypothetical_singleton_axiom_does_not_prove_extensionality() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let (b, b2) = (env.declare(2), env.declare(2)); // b(p,x), b'(q,x)
    let (chi, chi_ax) = cond_over(&mut env, &s, b);
    let (chi2, chi2_ax) = cond_over(&mut env, &s, b2);

    let good = prop::cond_ext_n(&mut env, &s, (b, chi, &chi_ax), (b2, chi2, &chi2_ax))
        .expect("the unconditional pair goes through");
    assert!(good.hyps().is_empty());

    // The genuine axiom, weakened so that it holds only under an open scope
    // hypothesis: same conclusion, non-empty `Γ`.
    let scope = Formula::mem(Term::var(env.fresh_var()), Term::apply(env.declare(0), vec![]));
    let weaken = |thm: &Thm| {
        let w = Thm::mp(&derived::a1i(thm, scope.clone()), &Thm::assume(scope.clone()))
            .expect("weaken into an open scope hypothesis");
        assert_eq!(*w.concl(), *thm.concl(), "the conclusion is unchanged");
        assert_eq!(w.hyps(), std::slice::from_ref(&scope), "but the sequent now assumes something");
        w
    };
    let bad_chi_ax = weaken(&chi_ax);
    let bad_chi2_ax = weaken(&chi2_ax);

    assert!(
        prop::cond_ext_n(&mut env, &s, (b, chi, &bad_chi_ax), (b2, chi2, &chi2_ax)).is_none(),
        "a Γ-carrying axiom on the left must be refused"
    );
    assert!(
        prop::cond_ext_n(&mut env, &s, (b, chi, &chi_ax), (b2, chi2, &bad_chi2_ax)).is_none(),
        "…and on the right"
    );
}
