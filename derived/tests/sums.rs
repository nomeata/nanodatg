//! The unit type `1` and the binary sum `A + B`.
//!
//! Every test rebuilds the formula it expects from the kernel's own
//! constructors and compares with `assert_eq!`, so a theorem that came out with
//! the right *name* but the wrong *shape* fails here. Where a lemma could be
//! vacuous — two sides that are literally the same term — the inequality is
//! asserted too.

use kernel::{Env, Formula, Term, Thm};

use derived::funcs::Sets;
use derived::funspace as fsp;
use derived::sums::{self, Sums};
use derived::tower::Tower;

// ─────────────────────────────────────────────────────────────────────────────
// The unit type.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ • ∈ 1`, spelled out as `⊢ ∅ ∈ {∅}`.
#[test]
fn the_point_inhabits_the_unit_type() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.unit_mem.concl()));

    let e = Term::apply(s.ap.empty, vec![]);
    let one = derived::singleton(s.ap.sets.up, e.clone());
    assert_eq!(*s.unit_mem.concl(), Formula::mem(e.clone(), one.clone()));

    // Non-vacuity: `•` and `1` are different *terms*, so this is not `x ∈ x`.
    assert_ne!(e, one);
    assert_eq!(e, s.point());
    assert_eq!(one, s.unit());
}

/// `⊢ ∀x. (x ∈ 1 → x = •)` — the unit type is a subsingleton.
#[test]
fn the_unit_type_is_a_subsingleton() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.unit_eta.concl()));

    let x = env.fresh_var();
    let tx = Term::var(x);
    let want = Formula::forall(
        x,
        Formula::imp(Formula::mem(tx.clone(), s.unit()), Formula::eq(tx, s.point())),
    );
    assert_eq!(*s.unit_eta.concl(), want);
}

/// `⊢ ¬(∃x. x ∈ 0)` — the empty type has no inhabitants.
#[test]
fn the_empty_type_has_no_inhabitants() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.zero_empty.concl()));

    let x = env.fresh_var();
    let want = Formula::not(Formula::exists(x, Formula::mem(Term::var(x), s.zero())));
    assert_eq!(*s.zero_empty.concl(), want);
}

/// `⊢ ¬(∅ = 1)` — the two tags of the sum are genuinely different sets.
///
/// Disjointness is worthless if the tags coincide, so this is proved outright
/// rather than left implicit.
#[test]
fn the_two_tags_are_distinct() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.tags_distinct.concl()));

    let want = Formula::not(Formula::eq(s.tag_l(), s.tag_r()));
    assert_eq!(*s.tags_distinct.concl(), want);
    assert_ne!(s.tag_l(), s.tag_r(), "the tags must not be the same term either");
}

// ─────────────────────────────────────────────────────────────────────────────
// The two membership lemmas the sum is assembled from.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))`.
#[test]
fn binary_union_membership_is_a_disjunction() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let thm = sums::mem_bin_union_iff(&mut env, &sets).expect("mem_bin_union_iff");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (u, v, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tv, tz) = (Term::var(u), Term::var(v), Term::var(z));
    let want = Formula::forall(
        u,
        Formula::forall(
            v,
            Formula::forall(
                z,
                Formula::iff(
                    Formula::mem(tz.clone(), fsp::bin_union(&sets, tu.clone(), tv.clone())),
                    Formula::or(
                        Formula::mem(tz.clone(), tu),
                        Formula::mem(tz, tv),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

/// `⊢ ∀t ∀a ∀z. (z ∈ prod({t}, a) ↔ ∃y. (y ∈ a ∧ z = ⟨t,y⟩))`.
#[test]
fn a_product_over_a_singleton_is_a_tagged_copy() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let mem_sing = derived::mem_singleton(&mut env, sets.up, &sets.up_ax).expect("mem_singleton");
    let p = fsp::product(&mut env, &sets).expect("product");
    let thm = sums::tagged_copy_members(&mut env, &sets, &mem_sing, &p).expect("tagged_copy_members");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (t, a, z, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tt, ta, tz, ty) = (Term::var(t), Term::var(a), Term::var(z), Term::var(y));
    let cond = Formula::exists(
        y,
        Formula::and(
            Formula::mem(ty.clone(), ta.clone()),
            Formula::eq(tz.clone(), sets.pair(tt.clone(), ty)),
        ),
    );
    let want = Formula::forall(
        t,
        Formula::forall(
            a,
            Formula::forall(
                z,
                Formula::iff(
                    Formula::mem(tz, p.of(derived::singleton(sets.up, tt), ta)),
                    cond,
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

/// Nothing here is an axiom: the whole apparatus is reachable, in one `Env`,
/// from the kernel's rules and `kernel::thm::define` alone.
#[test]
fn the_whole_construction_is_derivable() {
    let mut env = Env::new();
    let s = Sums::new(&mut env);
    assert!(s.is_some());
    let _: Thm = s.expect("sums").tags_distinct;
}

// ─────────────────────────────────────────────────────────────────────────────
// The sum type.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A ∀B. A + B = ({∅} × A) ∪ ({1} × B)` — the defining equation, and the
/// two tag sets really are different sets.
#[test]
fn the_sum_is_the_union_of_two_tagged_copies() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.sum_def.concl()));

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let left = s.prod.of(derived::singleton(s.ap.sets.up, s.tag_l()), ta.clone());
    let right = s.prod.of(derived::singleton(s.ap.sets.up, s.tag_r()), tb.clone());
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::eq(s.sum_of(ta.clone(), tb.clone()), fsp::bin_union(&s.ap.sets, left.clone(), right.clone())),
        ),
    );
    assert_eq!(*s.sum_def.concl(), want);
    assert_eq!(s.sum_term(ta.clone(), tb.clone()), fsp::bin_union(&s.ap.sets, left.clone(), right.clone()));
    // Non-vacuity: the two halves are distinct terms, so the union is not a
    // roundabout way of writing one of them twice.
    assert_ne!(left, right);
    assert_ne!(s.sum_of(ta, tb), s.sum_term(Term::var(a), Term::var(b)));
}

/// The master lemma:
/// `⊢ ∀A ∀B ∀z. (z ∈ A + B ↔ ((∃a. (a ∈ A ∧ z = inl(a))) ∨ (∃b. (b ∈ B ∧ z = inr(b)))))`.
#[test]
fn sum_membership_is_exactly_the_two_injections() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.sum_ax.concl()));

    let (a, b, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz) = (Term::var(a), Term::var(b), Term::var(z));
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let cond = Formula::or(
        Formula::exists(
            u,
            Formula::and(
                Formula::mem(Term::var(u), ta.clone()),
                Formula::eq(tz.clone(), s.inl(Term::var(u))),
            ),
        ),
        Formula::exists(
            v,
            Formula::and(
                Formula::mem(Term::var(v), tb.clone()),
                Formula::eq(tz.clone(), s.inr(Term::var(v))),
            ),
        ),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(z, Formula::iff(Formula::mem(tz, s.sum_of(ta, tb)), cond)),
        ),
    );
    assert_eq!(*s.sum_ax.concl(), want);
}

/// `⊢ ∀A ∀B ∀a. (a ∈ A → inl(a) ∈ A + B)` and
/// `⊢ ∀A ∀B ∀b. (b ∈ B → inr(b) ∈ A + B)`.
#[test]
fn the_injections_land_in_the_sum() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.inl_mem.concl()));
    assert!(kernel::thm::debug_locally_closed(s.inr_mem.concl()));

    let (a, b, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx) = (Term::var(a), Term::var(b), Term::var(x));
    let sum = s.sum_of(ta.clone(), tb.clone());

    let mk = |dom: Formula, elem: Term| {
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(x, Formula::imp(dom, Formula::mem(elem, sum.clone()))),
            ),
        )
    };
    assert_eq!(*s.inl_mem.concl(), mk(Formula::mem(tx.clone(), ta), s.inl(tx.clone())));
    assert_eq!(*s.inr_mem.concl(), mk(Formula::mem(tx.clone(), tb), s.inr(tx.clone())));

    // Non-vacuity: the two conclusions are about different elements.
    assert_ne!(s.inl(tx.clone()), s.inr(tx));
}

/// `⊢ ∀a ∀b. ¬(inl(a) = inr(b))` — the two injections never collide.
#[test]
fn the_injections_are_disjoint() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.disjoint.concl()));

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let want = Formula::forall(
        a,
        Formula::forall(b, Formula::not(Formula::eq(s.inl(ta.clone()), s.inr(tb.clone())))),
    );
    assert_eq!(*s.disjoint.concl(), want);

    // Non-vacuity: `¬(t = t)` would be false, so the two sides must differ even
    // at the same argument.
    assert_ne!(s.inl(ta.clone()), s.inr(tb));
    assert_ne!(s.inl(ta.clone()), s.inr(ta));
}

/// `⊢ ∀a ∀a′. (inl(a) = inl(a′) → a = a′)`, and the same for `inr`.
#[test]
fn the_injections_are_injective() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.inl_inj.concl()));
    assert!(kernel::thm::debug_locally_closed(s.inr_inj.concl()));

    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let mk = |l: Term, r: Term| {
        Formula::forall(
            x,
            Formula::forall(y, Formula::imp(Formula::eq(l, r), Formula::eq(tx.clone(), ty.clone()))),
        )
    };
    assert_eq!(*s.inl_inj.concl(), mk(s.inl(tx.clone()), s.inl(ty.clone())));
    assert_eq!(*s.inr_inj.concl(), mk(s.inr(tx.clone()), s.inr(ty.clone())));

    // Non-vacuity: the antecedent is not reflexivity in disguise.
    assert_ne!(tx, ty);
    assert_ne!(s.inl(tx.clone()), s.inl(ty.clone()));
    assert_ne!(s.inr(tx), s.inr(ty));
}

/// `⊢ ∀A ∀B ∀p. (p ∈ A + B → ((∃a. (a ∈ A ∧ p = inl(a))) ∨ (∃b. (b ∈ B ∧ p = inr(b)))))`
/// — no junk.
#[test]
fn the_sum_has_no_junk() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    assert!(kernel::thm::debug_locally_closed(s.sum_cases.concl()));

    let (a, b, p) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tp) = (Term::var(a), Term::var(b), Term::var(p));
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let cond = Formula::or(
        Formula::exists(
            u,
            Formula::and(
                Formula::mem(Term::var(u), ta.clone()),
                Formula::eq(tp.clone(), s.inl(Term::var(u))),
            ),
        ),
        Formula::exists(
            v,
            Formula::and(
                Formula::mem(Term::var(v), tb.clone()),
                Formula::eq(tp.clone(), s.inr(Term::var(v))),
            ),
        ),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                p,
                Formula::imp(Formula::mem(tp, s.sum_of(ta, tb)), cond),
            ),
        ),
    );
    assert_eq!(*s.sum_cases.concl(), want);
}

/// `⊢ ∀A ∀T ∀u ∀v. (⟨u,v⟩ ∈ A × T ↔ (u ∈ A ∧ v ∈ T))` — the product's
/// characterisation, restated for a pair already in hand.
#[test]
fn a_pair_is_in_a_product_iff_its_components_are() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let thm = sums::pair_in_product(&mut env, &s.ap, &s.prod).expect("pair_in_product");
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (a, t, u, v) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tt, tu, tv) = (Term::var(a), Term::var(t), Term::var(u), Term::var(v));
    let want = Formula::forall(
        a,
        Formula::forall(
            t,
            Formula::forall(
                u,
                Formula::forall(
                    v,
                    Formula::iff(
                        Formula::mem(s.ap.sets.pair(tu.clone(), tv.clone()), s.prod.of(ta.clone(), tt.clone())),
                        Formula::and(Formula::mem(tu, ta), Formula::mem(tv, tt)),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

// ─────────────────────────────────────────────────────────────────────────────
// The case function `rec₊`.
// ─────────────────────────────────────────────────────────────────────────────

/// The whole eliminator, built once and shared by the tests below.
fn build(env: &mut Env) -> (Sums, sums::Cases) {
    let s = Sums::new(env).expect("sums");
    let c = sums::Cases::new(env, &s).expect("cases");
    (s, c)
}

/// The defining axiom of `case`:
/// `⊢ ∀A ∀B ∀T ∀f ∀g ∀z. (z ∈ case(A,B,T,f,g) ↔ (z ∈ (A+B) × T ∧ D(z)))`,
/// with `D` spelled out.
#[test]
fn the_case_function_is_the_two_graphs_retagged() {
    let mut env = Env::new();
    let (s, c) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(c.case_ax.concl()));

    let (a, b, t, f, g) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));
    let z = env.fresh_var();
    let tz = Term::var(z);
    let (u, w) = (env.fresh_var(), env.fresh_var());
    let (tu, tw) = (Term::var(u), Term::var(w));

    let cond = Formula::exists(
        u,
        Formula::exists(
            w,
            Formula::or(
                Formula::and(
                    Formula::eq(tz.clone(), s.ap.sets.pair(s.inl(tu.clone()), tw.clone())),
                    Formula::mem(s.ap.sets.pair(tu.clone(), tw.clone()), tf.clone()),
                ),
                Formula::and(
                    Formula::eq(tz.clone(), s.ap.sets.pair(s.inr(tu.clone()), tw.clone())),
                    Formula::mem(s.ap.sets.pair(tu, tw), tg.clone()),
                ),
            ),
        ),
    );
    let sup = s.prod.of(s.sum_of(ta.clone(), tb.clone()), tt.clone());
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                t,
                Formula::forall(
                    f,
                    Formula::forall(
                        g,
                        Formula::forall(
                            z,
                            Formula::iff(
                                Formula::mem(tz.clone(), c.of(ta, tb, tt, tf, tg)),
                                Formula::and(Formula::mem(tz, sup), cond),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*c.case_ax.concl(), want);
}

/// `⊢ ∀A ∀B ∀T ∀f ∀g ∀a ∀y. (f ∈ fs(A,T) → (⟨inl(a),y⟩ ∈ case ↔ ⟨a,y⟩ ∈ f))`,
/// and the `inr` mirror image — the lemma the computation rules rest on.
#[test]
fn the_case_function_retags_pairs_bijectively() {
    let mut env = Env::new();
    let (s, c) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(c.left_pairs.concl()));
    assert!(kernel::thm::debug_locally_closed(c.right_pairs.concl()));

    let (a, b, t, f, g) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let case_t = c.of(ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone());

    let mk = |dom: Term, fn_t: Term, tagged: Term| {
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(
                    t,
                    Formula::forall(
                        f,
                        Formula::forall(
                            g,
                            Formula::forall(
                                x,
                                Formula::forall(
                                    y,
                                    Formula::imp(
                                        Formula::mem(fn_t.clone(), s.fs.of(dom, tt.clone())),
                                        Formula::iff(
                                            Formula::mem(
                                                s.ap.sets.pair(tagged, ty.clone()),
                                                case_t.clone(),
                                            ),
                                            Formula::mem(
                                                s.ap.sets.pair(tx.clone(), ty.clone()),
                                                fn_t,
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    };
    assert_eq!(*c.left_pairs.concl(), mk(ta.clone(), tf.clone(), s.inl(tx.clone())));
    assert_eq!(*c.right_pairs.concl(), mk(tb, tg.clone(), s.inr(tx.clone())));

    // Non-vacuity: the two lemmas are about different tagged pairs, and each
    // biconditional relates two genuinely different memberships.
    assert_ne!(s.inl(tx.clone()), s.inr(tx.clone()));
    assert_ne!(
        Formula::mem(s.ap.sets.pair(s.inl(tx.clone()), ty.clone()), case_t.clone()),
        Formula::mem(s.ap.sets.pair(tx.clone(), ty.clone()), tf)
    );
    assert_ne!(
        Formula::mem(s.ap.sets.pair(s.inr(tx.clone()), ty.clone()), case_t),
        Formula::mem(s.ap.sets.pair(tx, ty), tg)
    );
}

/// `⊢ ∀A ∀B ∀T ∀f ∀g. ((f ∈ fs(A,T) ∧ g ∈ fs(B,T)) → case(A,B,T,f,g) ∈ fs(A+B,T))`.
#[test]
fn the_case_function_is_a_function_on_the_sum() {
    let mut env = Env::new();
    let (s, c) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(c.in_funspace.concl()));

    let (a, b, t, f, g) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));
    let hyp = Formula::and(
        Formula::mem(tf.clone(), s.fs.of(ta.clone(), tt.clone())),
        Formula::mem(tg.clone(), s.fs.of(tb.clone(), tt.clone())),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                t,
                Formula::forall(
                    f,
                    Formula::forall(
                        g,
                        Formula::imp(
                            hyp,
                            Formula::mem(
                                c.of(ta.clone(), tb.clone(), tt.clone(), tf, tg),
                                s.fs.of(s.sum_of(ta, tb), tt),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(*c.in_funspace.concl(), want);
}

/// **The computation rules.**
///
/// `⊢ ∀A ∀B ∀T ∀f ∀g ∀a. (f ∈ fs(A,T) → (a ∈ A → app(case, inl(a)) = app(f,a)))`
/// and the `inr` mirror image. Both antecedents are explicit; see the module
/// documentation for which of them the derivation actually consumes.
#[test]
fn the_case_function_computes() {
    let mut env = Env::new();
    let (s, c) = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(c.beta_left.concl()));
    assert!(kernel::thm::debug_locally_closed(c.beta_right.concl()));

    let (a, b, t, f, g) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));
    let x = env.fresh_var();
    let tx = Term::var(x);
    let case_t = c.of(ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone());

    let mk = |dom: Term, fn_t: Term, tagged: Term| {
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(
                    t,
                    Formula::forall(
                        f,
                        Formula::forall(
                            g,
                            Formula::forall(
                                x,
                                Formula::imp(
                                    Formula::mem(fn_t.clone(), s.fs.of(dom.clone(), tt.clone())),
                                    Formula::imp(
                                        Formula::mem(tx.clone(), dom),
                                        Formula::eq(
                                            s.ap.apply(case_t.clone(), tagged),
                                            s.ap.apply(fn_t, tx.clone()),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    };
    assert_eq!(*c.beta_left.concl(), mk(ta.clone(), tf.clone(), s.inl(tx.clone())));
    assert_eq!(*c.beta_right.concl(), mk(tb, tg.clone(), s.inr(tx.clone())));

    // Non-vacuity: the two sides of each equation are different terms, so
    // neither rule is reflexivity in disguise.
    assert_ne!(s.ap.apply(case_t.clone(), s.inl(tx.clone())), s.ap.apply(tf.clone(), tx.clone()));
    assert_ne!(s.ap.apply(case_t, s.inr(tx.clone())), s.ap.apply(tg, tx));
}

/// The eliminator too is reachable, in one `Env`, from the kernel's rules
/// alone — no axiom is added anywhere in this module.
#[test]
fn the_eliminator_is_derivable() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let c = sums::Cases::new(&mut env, &s);
    assert!(c.is_some());
    let _: Thm = c.expect("cases").beta_left;
}

// ─────────────────────────────────────────────────────────────────────────────
// Closure of a universe under the sum.
// ─────────────────────────────────────────────────────────────────────────────

/// Build the sum-closure lemma over the tower, which is the one place all four
/// of its ingredients already sit on a single chain of definitional extensions.
fn sum_closure(env: &mut Env) -> (Tower, Thm) {
    let t = Tower::new(env).expect("Tower::new");
    let thm = sums::sum_in_universe(
        env,
        &t.sums,
        t.space.lu,
        &t.empty_in,
        &t.pairing,
        &t.product,
        &t.bin_union,
    )
    .expect("sum_in_universe");
    (t, thm)
}

/// `⊢ ∀c ∀a ∀b. ((a ∈ U(c) ∧ b ∈ U(c)) → (a + b) ∈ U(c))`, rebuilt from the
/// kernel's constructors.
#[test]
fn a_sum_of_two_members_is_a_member() {
    let mut env = Env::new();
    let (t, thm) = sum_closure(&mut env);
    assert!(kernel::thm::debug_locally_closed(thm.concl()));

    let (c, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(c), Term::var(a), Term::var(b));
    let u = Term::apply(t.space.lu, vec![tc]);
    let want = Formula::forall(
        c,
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::imp(
                    Formula::and(
                        Formula::mem(ta.clone(), u.clone()),
                        Formula::mem(tb.clone(), u.clone()),
                    ),
                    Formula::mem(t.sums.sum_of(ta, tb), u),
                ),
            ),
        ),
    );
    assert_eq!(*thm.concl(), want);

    // Not vacuous: at any three sets the antecedent and the conclusion are
    // different formulas, so this is not `φ → φ` in disguise.
    let inst = derived::inst_all(&thm, &[Term::var(c), Term::var(a), Term::var(b)])
        .expect("instantiate");
    let (ante, concl) = inst.concl().as_imp().expect("an implication");
    assert_ne!(ante, concl);
}

/// The antecedent discharged at concrete terms: `⊢ (U₀ + U₀) ∈ U₁`, with `U₁`
/// demonstrably not containing everything.
#[test]
fn the_sum_closure_discharges_at_concrete_terms() {
    let mut env = Env::new();
    let (t, thm) = sum_closure(&mut env);
    let (omega, u0, u1) = (t.omega(), t.u0(), t.level(1));

    let u0_in_u1 = derived::inst_all(&t.u0_in, std::slice::from_ref(&omega)).expect("instantiate");
    assert_eq!(*u0_in_u1.concl(), Formula::mem(u0.clone(), u1.clone()));

    let at = derived::inst_all(&thm, &[omega, u0.clone(), u0.clone()]).expect("instantiate");
    let out = Thm::mp(&at, &derived::and_intro(&u0_in_u1, &u0_in_u1)).expect("mp");
    assert_eq!(*out.concl(), Formula::mem(t.sums.sum_of(u0.clone(), u0.clone()), u1.clone()));

    // The conclusion says something: `U₁` is not a set everything belongs to.
    let no_self = derived::inst_all(&t.no_self_mem, std::slice::from_ref(&u1)).expect("instantiate");
    assert_eq!(*no_self.concl(), Formula::not(Formula::mem(u1.clone(), u1.clone())));
    // And the sum is a different set from its summand, as a term.
    assert_ne!(t.sums.sum_of(u0.clone(), u0), u1);
}

/// A stack that does not fit together is refused rather than described: handing
/// the pairing lemma where the product lemma belongs returns `None`.
#[test]
fn the_sum_closure_refuses_a_foreign_stack() {
    let mut env = Env::new();
    let t = Tower::new(&mut env).expect("Tower::new");
    assert!(sums::sum_in_universe(
        &mut env,
        &t.sums,
        t.space.lu,
        &t.empty_in,
        &t.pairing,
        &t.pairing, // not the product closure
        &t.bin_union,
    )
    .is_none());
    // And a universe operator of the wrong arity is refused outright.
    let binary = env.declare(2);
    assert!(sums::sum_in_universe(
        &mut env,
        &t.sums,
        binary,
        &t.empty_in,
        &t.pairing,
        &t.product,
        &t.bin_union,
    )
    .is_none());
}
