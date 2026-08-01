//! `List` as a W-type — Lean's
//! `inductive List (α : Type u) | nil | cons (h : α) (t : List α)`.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! Two things are being checked beyond "it builds".
//!
//! **The memberships are unconditional in `α`.** `INDUCTIVES.md` predicted that
//! parameterising the type would put a hypothesis `α ∈ ⟦Sort u⟧` on every
//! statement. [`the_bound_is_unconditional_in_the_parameter`] and
//! [`both_constructors_land_in_the_list_type`] pin the exact conclusions, at a
//! *free* `α` with nothing assumed about it, which refutes that.
//!
//! **Non-vacuity.** `nil ∈ lt(α)` and the `cons` rule are both true of a
//! one-element `lt(α)`, so [`lists_are_not_a_singleton`] cashes the two
//! injectivity theorems at three concrete lists and checks they are pairwise
//! distinct *and* all three in the type, given only an element of `α`.

use kernel::{Env, Formula, Term, Thm};

use derived::bound::Bound;
use derived::point_fun::PointFun;
use derived::sums::Cases;
use derived::wlist::WList;
use derived::wtype::Wtype;

struct Dev {
    wt: Wtype,
    bnd: Bound,
    cases: Cases,
    lst: WList,
}

fn build(env: &mut Env) -> Dev {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let cases = Cases::new(env, &wt.sums).expect("rec₊");
    let pf = PointFun::over(env, &wt.sums, &wt.app_pair).expect("point functions");
    let empty_u = derived::enums::empty_in_least_universe(env, &wt, &bnd).expect("∅ ∈ U(A)");
    let lst = WList::over(env, &wt, &bnd, &cases, &pf, &empty_u).expect("List");
    Dev { wt, bnd, cases, lst }
}

/// The two `rec₊` computation rules. The `nil` branch is unconditional; the
/// `cons` branch carries `h ∈ α`, which is the hypothesis Lean's constructor
/// states and the only one anywhere in this file.
#[test]
fn the_fibre_family_computes() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;

    assert!(kernel::thm::debug_locally_closed(d.lst.fibre_nil.concl()));
    assert!(kernel::thm::debug_locally_closed(d.lst.fibre_cons.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let fam = d.lst.fam_of(s, &d.cases, ta.clone());

    let nil_at = derived::inst_all(&d.lst.fibre_nil, std::slice::from_ref(&ta)).expect("inst");
    assert_eq!(
        *nil_at.concl(),
        Formula::eq(d.wt.fibre(fam.clone(), s.inl(s.point())), s.zero())
    );

    let h = env.fresh_var();
    let th = Term::var(h);
    let cons_at =
        derived::inst_all(&d.lst.fibre_cons, &[ta.clone(), th.clone()]).expect("inst");
    assert_eq!(
        *cons_at.concl(),
        Formula::imp(
            Formula::mem(th.clone(), ta.clone()),
            Formula::eq(d.wt.fibre(fam, s.inr(th)), s.unit())
        )
    );
    // The two fibres are genuinely different sets, so `B` is not constant.
    assert_ne!(s.zero(), s.unit());
}

/// `⊢ ∀α. closed(1+α, fam(α), U(1+α))` — with **no** hypothesis on `α`.
///
/// This is the claim the `N` report doubted for a parameterised type. Nothing in
/// [`derived::bound::least_universe_closed`]'s antecedent mentions `α`'s own
/// type, so nothing asks for one.
#[test]
fn the_bound_is_unconditional_in_the_parameter() {
    let mut env = Env::new();
    let d = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(d.lst.closed.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let tags = WList::tags_of(&d.wt.sums, ta.clone());
    let fam = d.lst.fam_of(&d.wt.sums, &d.cases, ta.clone());
    let u = d.bnd.universe_of(tags.clone());

    let at = derived::inst_all(&d.lst.closed, std::slice::from_ref(&ta)).expect("inst");
    // No implication: the conclusion *is* `closed(…)`, not `something → closed(…)`.
    assert!(at.concl().as_imp().is_none());
    let want = derived::wtype::closed(&mut env, &d.wt.sums, &tags, &fam, &u);
    assert_eq!(*at.concl(), want);

    // And the type really is the W-type carved out of that universe.
    let unfold = derived::inst_all(&d.lst.lt_ax, std::slice::from_ref(&ta)).expect("inst");
    assert_eq!(
        *unfold.concl(),
        Formula::eq(d.lst.ty_of(ta), d.wt.of(tags, fam, u))
    );
}

/// `⊢ ∀α. nil ∈ lt(α)` and `⊢ ∀α ∀h ∀t. ((h ∈ α ∧ t ∈ lt(α)) → cons h t ∈ lt(α))`.
///
/// `nil` carries nothing at all — in particular nothing about `α` — and `cons`
/// carries exactly the two hypotheses its Lean type states.
#[test]
fn both_constructors_land_in_the_list_type() {
    let mut env = Env::new();
    let d = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(d.lst.nil.concl()));
    assert!(kernel::thm::debug_locally_closed(d.lst.cons.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let ty = d.lst.ty_of(ta.clone());

    let nil_at = derived::inst_all(&d.lst.nil, std::slice::from_ref(&ta)).expect("inst");
    assert!(nil_at.concl().as_imp().is_none());
    assert_eq!(*nil_at.concl(), Formula::mem(d.lst.nil_t.clone(), ty.clone()));

    let (h, t) = (env.fresh_var(), env.fresh_var());
    let (th, tt) = (Term::var(h), Term::var(t));
    let cons_at =
        derived::inst_all(&d.lst.cons, &[ta.clone(), th.clone(), tt.clone()]).expect("inst");
    assert_eq!(
        *cons_at.concl(),
        Formula::imp(
            Formula::and(
                Formula::mem(th.clone(), ta.clone()),
                Formula::mem(tt.clone(), ty.clone())
            ),
            Formula::mem(WList::cons_term(&d.wt, th, tt), ty)
        )
    );
}

/// Three concrete lists, pairwise distinct and all in the type — the check that
/// stops the two memberships above from being satisfied by a singleton.
///
/// Distinctness needs nothing at all; membership needs one element of `α`.
#[test]
fn lists_are_not_a_singleton() {
    let mut env = Env::new();
    let d = build(&mut env);

    let (a, h) = (env.fresh_var(), env.fresh_var());
    let (ta, th) = (Term::var(a), Term::var(h));
    let ty = d.lst.ty_of(ta.clone());

    let nil = d.lst.nil_t.clone();
    let c1 = WList::cons_term(&d.wt, th.clone(), nil.clone());
    let c2 = WList::cons_term(&d.wt, th.clone(), c1.clone());
    assert_ne!(nil, c1);
    assert_ne!(c1, c2);
    assert_ne!(nil, c2);

    // Pairwise distinct, with no hypothesis left.
    // `¬φ` is `φ → ⊥` in this kernel, so "no hypothesis" is checked by the
    // exact-formula assertion below rather than by `as_imp`.
    let dis = derived::inst_all(&d.lst.distinct3, std::slice::from_ref(&th)).expect("inst");
    assert_eq!(
        *dis.concl(),
        Formula::and(
            Formula::not(Formula::eq(nil.clone(), c1.clone())),
            Formula::and(
                Formula::not(Formula::eq(nil.clone(), c2.clone())),
                Formula::not(Formula::eq(c1.clone(), c2.clone()))
            )
        )
    );

    // All three in `lt(α)`, given only `h ∈ α`.
    let mem = derived::inst_all(&d.lst.three_in, &[ta.clone(), th.clone()]).expect("inst");
    assert_eq!(
        *mem.concl(),
        Formula::imp(
            Formula::mem(th.clone(), ta.clone()),
            Formula::and(
                Formula::mem(nil.clone(), ty.clone()),
                Formula::and(
                    Formula::mem(c1.clone(), ty.clone()),
                    Formula::mem(c2.clone(), ty.clone())
                )
            )
        )
    );
}

/// `cons` is injective in **both** arguments, which is what makes `α`'s elements
/// visible inside the list. `N`'s `succ_inj` had no counterpart for the head.
#[test]
fn cons_is_injective_in_head_and_tail() {
    let mut env = Env::new();
    let d = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(d.lst.cons_inj.concl()));

    let (h1, t1, h2, t2) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (th1, tt1, th2, tt2) =
        (Term::var(h1), Term::var(t1), Term::var(h2), Term::var(t2));
    let at = derived::inst_all(
        &d.lst.cons_inj,
        &[th1.clone(), tt1.clone(), th2.clone(), tt2.clone()],
    )
    .expect("inst");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::eq(
                WList::cons_term(&d.wt, th1.clone(), tt1.clone()),
                WList::cons_term(&d.wt, th2.clone(), tt2.clone())
            ),
            Formula::and(Formula::eq(th1, th2), Formula::eq(tt1, tt2))
        )
    );

    // Two distinct heads over the same tail give distinct lists — the statement
    // that says `lt(α)` sees `α` and not merely its being non-empty.
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let nil = d.lst.nil_t.clone();
    let inj = derived::inst_all(
        &d.lst.cons_inj,
        &[tx.clone(), nil.clone(), ty.clone(), nil.clone()],
    )
    .expect("inst");
    let heads = derived::syl(
        &inj,
        &derived::and_left(
            Formula::eq(tx.clone(), ty.clone()),
            Formula::eq(nil.clone(), nil.clone()),
        ),
    )
    .expect("syl");
    assert_eq!(
        *heads.concl(),
        Formula::imp(
            Formula::eq(
                WList::cons_term(&d.wt, tx.clone(), nil.clone()),
                WList::cons_term(&d.wt, ty.clone(), nil)
            ),
            Formula::eq(tx, ty)
        )
    );
}

/// `nil` is not a `cons`, for **every** head and tail — the tags differ, so no
/// hypothesis on `α` or on `h` is needed.
#[test]
fn nil_is_not_a_cons() {
    let mut env = Env::new();
    let d = build(&mut env);
    assert!(kernel::thm::debug_locally_closed(d.lst.nil_ne_cons.concl()));

    let (h, t) = (env.fresh_var(), env.fresh_var());
    let (th, tt) = (Term::var(h), Term::var(t));
    let at =
        derived::inst_all(&d.lst.nil_ne_cons, &[th.clone(), tt.clone()]).expect("inst");
    assert_eq!(
        *at.concl(),
        Formula::not(Formula::eq(
            d.lst.nil_t.clone(),
            WList::cons_term(&d.wt, th, tt)
        ))
    );
}

/// The one piece of machinery the parameter cost: `λ_ : A. 1` as a lambda graph
/// over an **arbitrary** `A`, where `N`'s constant fibres were one-point graphs
/// on the singleton `1`.
#[test]
fn the_constant_fibre_function_is_a_function() {
    let mut env = Env::new();
    let d = build(&mut env);
    let s = &d.wt.sums;
    assert!(kernel::thm::debug_locally_closed(d.lst.const_fun_fs.concl()));

    let a = env.fresh_var();
    let ta = Term::var(a);
    let at = derived::inst_all(&d.lst.const_fun_fs, std::slice::from_ref(&ta)).expect("inst");
    assert!(at.concl().as_imp().is_none());
    assert_eq!(
        *at.concl(),
        Formula::mem(
            Term::apply(d.lst.lam_co, vec![ta.clone()]),
            s.fs.of(ta, d.lst.two.clone())
        )
    );
    // And the graph is not the empty one: `2` has two members, so a function
    // into it is not vacuously typed.
    assert_ne!(s.zero(), d.lst.two);
}

/// A guard against the file being about the wrong `Thm`: the `cons` rule really
/// does *fire*, producing `cons h nil ∈ lt(α)` from `h ∈ α` alone — the `nil`
/// premise being discharged outright.
#[test]
fn the_cons_rule_fires() {
    let mut env = Env::new();
    let d = build(&mut env);

    let (a, h) = (env.fresh_var(), env.fresh_var());
    let (ta, th) = (Term::var(a), Term::var(h));
    let ty = d.lst.ty_of(ta.clone());
    let h_in = Formula::mem(th.clone(), ta.clone());
    let nil_at = derived::inst_all(&d.lst.nil, std::slice::from_ref(&ta)).expect("inst");

    let rule = derived::inst_all(&d.lst.cons, &[ta.clone(), th.clone(), d.lst.nil_t.clone()])
        .expect("inst");
    // `⊢ h ∈ α → (h ∈ α ∧ nil ∈ lt(α))`, then modus ponens under the hypothesis.
    let premises = derived::hyp_and(
        &derived::imp_refl(h_in.clone()),
        &derived::a1i(&nil_at, h_in.clone()),
    )
    .expect("premises");
    let out = derived::hyp_mp(&derived::a1i(&rule, h_in.clone()), &premises).expect("mp");
    assert_eq!(
        *out.concl(),
        Formula::imp(
            h_in,
            Formula::mem(WList::cons_term(&d.wt, th, d.lst.nil_t.clone()), ty)
        )
    );
    let _: Option<Thm> = None;
}

// ─────────────────────────────────────────────────────────────────────────────
// The function layer: `List`, `List.nil` and `List.cons` as **sets**.
// ─────────────────────────────────────────────────────────────────────────────

use derived::wlist_fun::ListFun;

fn build_fun(env: &mut Env) -> (Dev, ListFun) {
    let d = build(env);
    let lf = ListFun::over(env, &d.wt, &d.lst).expect("List as a function");
    (d, lf)
}

/// The type former computes: `app(L(S), α) = lt(α)` on the domain.
#[test]
fn the_type_former_is_a_graph_that_computes() {
    let mut env = Env::new();
    let (d, lf) = build_fun(&mut env);
    let ap = &d.wt.sums.ap;
    assert!(kernel::thm::debug_locally_closed(lf.l_beta.concl()));

    let (s, a) = (env.fresh_var(), env.fresh_var());
    let (ts, ta) = (Term::var(s), Term::var(a));
    let at = derived::inst_all(&lf.l_beta, &[ts.clone(), ta.clone()]).expect("inst");
    assert_eq!(
        *at.concl(),
        Formula::imp(
            Formula::mem(ta.clone(), ts.clone()),
            Formula::eq(ap.apply(lf.l_of(ts), ta.clone()), d.lst.ty_of(ta))
        )
    );
}

/// The two rules a checker consumes, pinned to their exact conclusions —
/// stated in terms of `app(L(S),α)`, which is what `⟦List α⟧` interprets to.
#[test]
fn the_constructor_rules_have_the_stated_shape() {
    let mut env = Env::new();
    let (d, lf) = build_fun(&mut env);
    let ap = &d.wt.sums.ap;
    assert!(kernel::thm::debug_locally_closed(lf.nil_rule.concl()));
    assert!(kernel::thm::debug_locally_closed(lf.cons_rule.concl()));

    let (s, a, h, t) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ts, ta, th, tt) = (Term::var(s), Term::var(a), Term::var(h), Term::var(t));
    let app_l = ap.apply(lf.l_of(ts.clone()), ta.clone());

    let nil_at = derived::inst_all(&lf.nil_rule, &[ts.clone(), ta.clone()]).expect("inst");
    assert_eq!(
        *nil_at.concl(),
        Formula::imp(
            Formula::mem(ta.clone(), ts.clone()),
            Formula::mem(ap.apply(lf.nil_of(ts.clone()), ta.clone()), app_l.clone())
        )
    );

    let cons_at =
        derived::inst_all(&lf.cons_rule, &[ts.clone(), ta.clone(), th.clone(), tt.clone()])
            .expect("inst");
    let spine = ap.apply(
        ap.apply(ap.apply(lf.cons_of(ts.clone()), ta.clone()), th.clone()),
        tt.clone(),
    );
    assert_eq!(
        *cons_at.concl(),
        Formula::imp(
            Formula::and(
                Formula::mem(ta.clone(), ts.clone()),
                Formula::and(
                    Formula::mem(th.clone(), ta.clone()),
                    Formula::mem(tt.clone(), app_l.clone())
                )
            ),
            Formula::mem(spine, app_l)
        )
    );
}

/// **Non-vacuity of the function layer.** Both rules would hold of an `S` with
/// no members, so `S := U(α)` is instantiated — where `α ∈ U(α)` is free — and
/// the `nil` membership comes out with **no hypothesis left**, followed by one
/// `cons` on top of it.
#[test]
fn the_graphs_compute_at_a_real_argument() {
    let mut env = Env::new();
    let (d, lf) = build_fun(&mut env);
    let ap = &d.wt.sums.ap;

    let mem_lu = derived::universe::mem_least_universe(&mut env, d.bnd.lu, &d.bnd.lu_ax)
        .expect("x ∈ U(x)");
    let a = env.fresh_var();
    let ta = Term::var(a);
    let ts = d.bnd.universe_of(ta.clone());
    let a_in_s = derived::inst_all(&mem_lu, std::slice::from_ref(&ta)).expect("inst");
    assert_eq!(*a_in_s.concl(), Formula::mem(ta.clone(), ts.clone()));

    let app_l = ap.apply(lf.l_of(ts.clone()), ta.clone());

    // `⊢ app(Nil(U(α)), α) ∈ app(L(U(α)), α)`, unconditionally.
    let nil_at = Thm::mp(
        &derived::inst_all(&lf.nil_rule, &[ts.clone(), ta.clone()]).expect("inst"),
        &a_in_s,
    )
    .expect("nil");
    let nil_term = ap.apply(lf.nil_of(ts.clone()), ta.clone());
    assert_eq!(*nil_at.concl(), Formula::mem(nil_term.clone(), app_l.clone()));

    // And one `cons` on top of it, given any head in `α`.
    let h = env.fresh_var();
    let th = Term::var(h);
    let h_in = Formula::mem(th.clone(), ta.clone());
    let rule = derived::inst_all(
        &lf.cons_rule,
        &[ts.clone(), ta.clone(), th.clone(), nil_term.clone()],
    )
    .expect("inst");
    let premises = derived::hyp_and(
        &derived::a1i(&a_in_s, h_in.clone()),
        &derived::hyp_and(
            &derived::imp_refl(h_in.clone()),
            &derived::a1i(&nil_at, h_in.clone()),
        )
        .expect("inner"),
    )
    .expect("premises");
    let out = derived::hyp_mp(&derived::a1i(&rule, h_in.clone()), &premises).expect("mp");
    let spine = ap.apply(
        ap.apply(ap.apply(lf.cons_of(ts.clone()), ta.clone()), th.clone()),
        nil_term.clone(),
    );
    assert_eq!(*out.concl(), Formula::imp(h_in, Formula::mem(spine.clone(), app_l)));

    // The two elements are different terms, so this is not one membership twice.
    assert_ne!(nil_term, spine);
}

/// The two **equations** behind those rules, which is what the ι rule consumes:
/// a membership says the applied graph lands in the type, but the recursor's
/// computation rule is stated at the W-type element itself, so the equation is
/// what joins them.
#[test]
fn the_constructor_graphs_compute_to_the_w_type_elements() {
    let mut env = Env::new();
    let (d, lf) = build_fun(&mut env);
    let ap = &d.wt.sums.ap;
    assert!(kernel::thm::debug_locally_closed(lf.nil_beta.concl()));
    assert!(kernel::thm::debug_locally_closed(lf.cons_beta.concl()));

    let (s, a, h, t) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ts, ta, th, tt) = (Term::var(s), Term::var(a), Term::var(h), Term::var(t));
    let app_l = ap.apply(lf.l_of(ts.clone()), ta.clone());

    let nil_at = derived::inst_all(&lf.nil_beta, &[ts.clone(), ta.clone()]).expect("inst");
    assert_eq!(
        *nil_at.concl(),
        Formula::imp(
            Formula::mem(ta.clone(), ts.clone()),
            Formula::eq(
                ap.apply(lf.nil_of(ts.clone()), ta.clone()),
                derived::wlist::WList::nil_term(&d.wt)
            )
        )
    );

    let cons_at =
        derived::inst_all(&lf.cons_beta, &[ts.clone(), ta.clone(), th.clone(), tt.clone()])
            .expect("inst");
    let spine = ap.apply(
        ap.apply(ap.apply(lf.cons_of(ts.clone()), ta.clone()), th.clone()),
        tt.clone(),
    );
    let elem = derived::wlist::WList::cons_term(&d.wt, th.clone(), tt.clone());
    assert_ne!(spine, elem, "the cons equation would be reflexivity");
    assert_eq!(
        *cons_at.concl(),
        Formula::imp(
            Formula::and(
                Formula::mem(ta.clone(), ts.clone()),
                Formula::and(
                    Formula::mem(th.clone(), ta.clone()),
                    Formula::mem(tt.clone(), app_l)
                )
            ),
            Formula::eq(spine, elem)
        )
    );
}
