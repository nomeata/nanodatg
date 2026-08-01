//! **The anchor of the project's threat model.**
//!
//! `README.md` states the guarantee as: if a development translates and the
//! kernel accepts every step, it proves no contradiction — *as long as the
//! translation of `False` is genuinely refutable in the target*. These tests are
//! that clause. If any of them starts failing, the guarantee has become vacuous,
//! whatever else still passes.
//!
//! Each test rebuilds the formula it expects from the kernel's own constructors
//! and compares with `assert_eq!`, so a theorem with the right name and the
//! wrong shape fails here rather than downstream.
//!
//! # What is tied to the backend and what is not
//!
//! `⟦Empty⟧` **is** tied. `checker/src/tg.rs` recognises a zero-constructor,
//! non-`Prop`, non-recursive, unparameterised inductive as an enumeration of
//! arity `0` and hands back `Inductives::ty(0)`, which is
//! `derived::enums::enum0(&wt, &bnd)`. [`the_backends_empty_type_is_empty`]
//! states its theorem at the term that function returns, and
//! [`the_anchor_is_about_the_backends_term`] additionally pins that term's
//! spelling, so a change to `enum0` breaks the test rather than silently
//! detaching the anchor.
//!
//! `⟦False⟧` is **not** tied, and cannot be today. Two things stand in the way,
//! both in `checker/src/tg.rs`, neither of which this crate may change:
//!
//! 1. `interp_sort` maps `Level::Zero` to the opaque nullary symbol
//!    `self.syms.sort0`, about which the kernel knows nothing at all. The thesis
//!    identifies `Prop` with the zeroth universe, `U₀ = {∅, {•}}` with `• = ∅`
//!    (*The Type Theory of Lean* §6.2), so the intended clause is
//!
//!    ```text
//!    Level::Zero => { let zero = self.mk(self.pre.ap.empty, vec![]);
//!                     let one  = self.mk(self.pre.ap.sets.up, vec![zero.clone(), zero.clone()]);
//!                     self.mk(self.pre.ap.sets.up, vec![zero, one]) }
//!    ```
//!
//!    i.e. `⟦Sort 0⟧ := upair(∅, {∅})`, which is exactly
//!    [`derived::anchor::truth_values`]. Every symbol it needs is already on
//!    `Prelude`.
//! 2. `False` is a `Prop`-valued inductive with no value, so `ind_const` declines
//!    it (correctly — a `Prop` is a subset of `{•}`, not a W-type) and `interp`
//!    falls through to a fresh opaque nullary symbol. It needs a clause of its
//!    own giving `⟦False⟧ := ∅`, which is [`derived::anchor::false_set`], and the
//!    thesis's own clause (`⟦Γ ⊢ ⊥⟧γ = ∅`).
//!
//! Until both land, the tests below about `False` are about the term the
//! interpretation *should* produce. That is stated here rather than implied,
//! because an anchor stated at the wrong term is worth nothing.

use kernel::{Env, Formula, Term};

use derived::anchor::{falsity, wtype as anchor_wtype};
use derived::bound::Bound;
use derived::sums::Sums;
use derived::wtype::Wtype;

/// The W-type development, built once per test.
fn build(env: &mut Env) -> (Wtype, Bound) {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    (wt, bnd)
}

/// The whole `Empty` chain: `closed`, uninhabitedness, and the equation.
fn empty_chain(env: &mut Env, wt: &Wtype) -> (kernel::Thm, kernel::Thm) {
    let closed0 = anchor_wtype::empty_closed(env, wt).expect("closed(∅,B,∅)");
    let uninhabited =
        anchor_wtype::empty_wtype_uninhabited(env, wt, &closed0).expect("W(∅,B,u) uninhabited");
    let eq = anchor_wtype::empty_wtype_eq(env, wt, &uninhabited).expect("W(∅,B,u) = ∅");
    (uninhabited, eq)
}

// ─────────────────────────────────────────────────────────────────────────────
// Empty
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀B. closed(∅, B, ∅)` — and it is the *same* `closed` formula the W-type
/// rules are stated with, not a lookalike.
#[test]
fn an_empty_tag_set_closes_everything() {
    let mut env = Env::new();
    let (wt, _) = build(&mut env);
    let t = anchor_wtype::empty_closed(&mut env, &wt).expect("closed(∅,B,∅)");
    assert!(kernel::thm::debug_locally_closed(t.concl()));

    let b = env.fresh_var();
    let z = wt.empty();
    let want = Formula::forall(
        b,
        derived::wtype::closed(&mut env, &wt.sums, &z, &Term::var(b), &z),
    );
    assert_eq!(*t.concl(), want);
}

/// `⊢ ∀B ∀u ∀x. ¬(x ∈ W(∅, B, u))` — for **every** family and **every** bound.
#[test]
fn a_w_type_over_no_tags_has_no_elements() {
    let mut env = Env::new();
    let (wt, _) = build(&mut env);
    let (uninhabited, _) = empty_chain(&mut env, &wt);
    assert!(kernel::thm::debug_locally_closed(uninhabited.concl()));

    let (b, u, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let want = Formula::forall(
        b,
        Formula::forall(
            u,
            Formula::forall(
                x,
                Formula::not(Formula::mem(
                    Term::var(x),
                    wt.of(wt.empty(), Term::var(b), Term::var(u)),
                )),
            ),
        ),
    );
    assert_eq!(*uninhabited.concl(), want);
}

/// `⊢ ∀B ∀u. W(∅, B, u) = ∅`.
#[test]
fn a_w_type_over_no_tags_is_the_empty_set() {
    let mut env = Env::new();
    let (wt, _) = build(&mut env);
    let (_, eq) = empty_chain(&mut env, &wt);
    assert!(kernel::thm::debug_locally_closed(eq.concl()));

    let (b, u) = (env.fresh_var(), env.fresh_var());
    let want = Formula::forall(
        b,
        Formula::forall(
            u,
            Formula::eq(wt.of(wt.empty(), Term::var(b), Term::var(u)), wt.empty()),
        ),
    );
    assert_eq!(*eq.concl(), want);
}

/// **The anchor, at the backend's own term.** `⊢ ∀x. ¬(x ∈ ⟦Empty⟧)` and
/// `⊢ ⟦Empty⟧ = ∅`, where `⟦Empty⟧` is `derived::enums::enum0`.
#[test]
fn the_backends_empty_type_is_empty() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let (uninhabited, eq) = empty_chain(&mut env, &wt);

    let e0 = derived::enums::enum0(&wt, &bnd);
    let no_mem = anchor_wtype::enum0_uninhabited(&mut env, &wt, &bnd, &uninhabited)
        .expect("⟦Empty⟧ uninhabited");
    let is_empty = anchor_wtype::enum0_eq(&wt, &bnd, &eq).expect("⟦Empty⟧ = ∅");

    assert!(kernel::thm::debug_locally_closed(no_mem.concl()));
    assert!(kernel::thm::debug_locally_closed(is_empty.concl()));

    let x = env.fresh_var();
    assert_eq!(
        *no_mem.concl(),
        Formula::forall(x, Formula::not(Formula::mem(Term::var(x), e0.clone())))
    );
    assert_eq!(*is_empty.concl(), Formula::eq(e0, wt.empty()));
}

/// The tie itself: `⟦Empty⟧` is `W(0, ∅, U(0))`, spelled out.
///
/// `checker/src/tg.rs` reaches this term through `Inductives::ty(0)`, which is
/// `derived::enums::enum0(&wt, &bnd)`. If `enum0` is ever redefined, this fails
/// and the anchor must be re-tied — which is the point: the failure mode being
/// guarded is not "the theorem became false" but "the theorem stopped being
/// about the interpretation".
#[test]
fn the_anchor_is_about_the_backends_term() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let z = wt.empty();
    assert_eq!(
        derived::enums::enum0(&wt, &bnd),
        wt.of(z.clone(), z.clone(), Term::apply(bnd.lu, vec![z]))
    );
}

/// The last step an interpretation needs: the anchor carried along an
/// abbreviation's defining equation.
///
/// `checker/src/tg.rs` does not use `enum(0)` directly — `ind_abbrev` mints a
/// symbol `⟦Empty⟧` with `⊢ ⟦Empty⟧ = W(0,∅,U(0))` and uses *that*. This is the
/// one Leibniz step from the theorem proved here to a theorem about the symbol
/// the rest of the backend speaks of.
#[test]
fn the_anchor_travels_to_the_abbreviation() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let (uninhabited, _) = empty_chain(&mut env, &wt);
    let no_mem = anchor_wtype::enum0_uninhabited(&mut env, &wt, &bnd, &uninhabited)
        .expect("⟦Empty⟧ uninhabited");

    // Stand in for `ind_abbrev`: a fresh symbol defined to be `enum(0)`.
    let e0 = derived::enums::enum0(&wt, &bnd);
    let (sym, def) = derived::define_abbrev(&mut env, &[], &e0).expect("abbreviation");
    let c = Term::apply(sym, vec![]);
    assert_eq!(*def.concl(), Formula::eq(c.clone(), e0));

    let t = anchor_wtype::uninhabited_along(&mut env, &def, &no_mem).expect("transport");
    assert!(kernel::thm::debug_locally_closed(t.concl()));
    let x = env.fresh_var();
    assert_eq!(
        *t.concl(),
        Formula::forall(x, Formula::not(Formula::mem(Term::var(x), c)))
    );
}

/// `⊢ ∀T. ∅ ∈ fs(⟦Empty⟧, T)` — the eliminator for the empty type is the empty
/// function, as the thesis has it (`⟦Γ ⊢ rec⊥⟧γ = ∅`).
#[test]
fn the_empty_types_recursor_is_the_empty_function() {
    let mut env = Env::new();
    let (wt, bnd) = build(&mut env);
    let (_, eq) = empty_chain(&mut env, &wt);
    let e0_eq = anchor_wtype::enum0_eq(&wt, &bnd, &eq).expect("⟦Empty⟧ = ∅");
    let t = anchor_wtype::enum0_rec(&mut env, &wt, &bnd, &e0_eq).expect("rec⊥ = ∅");
    assert!(kernel::thm::debug_locally_closed(t.concl()));

    let ty = env.fresh_var();
    let e0 = derived::enums::enum0(&wt, &bnd);
    let want = Formula::forall(
        ty,
        Formula::mem(wt.empty(), wt.sums.fs.of(e0, Term::var(ty))),
    );
    assert_eq!(*t.concl(), want);
}

// ─────────────────────────────────────────────────────────────────────────────
// False
// ─────────────────────────────────────────────────────────────────────────────

/// **The anchor for `False`.** `⊢ ∀x. ¬(x ∈ ⟦False⟧)`, stated at `⟦False⟧ = ∅`.
#[test]
fn nothing_inhabits_false() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let t = falsity::false_uninhabited(&mut env, &s).expect("⟦False⟧ uninhabited");
    assert!(kernel::thm::debug_locally_closed(t.concl()));

    let x = env.fresh_var();
    let want = Formula::forall(
        x,
        Formula::not(Formula::mem(Term::var(x), falsity::false_set(&s))),
    );
    assert_eq!(*t.concl(), want);
}

/// **The consequence that matters**: from `t ∈ ⟦False⟧`, every formula follows.
///
/// Checked at a formula that is *not* provable — `1 = 0`, refuted by
/// [`derived::sums::tags_distinct`] — so the test cannot pass because the
/// conclusion happened to be a theorem anyway.
#[test]
fn an_inhabitant_of_false_proves_anything() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let witness = env.fresh_var();
    let tw = Term::var(witness);
    let absurdity = Formula::eq(s.unit(), s.zero());

    let t = falsity::false_absurd(&s, &tw, absurdity.clone()).expect("ex falso");
    assert!(kernel::thm::debug_locally_closed(t.concl()));
    assert_eq!(
        *t.concl(),
        Formula::imp(Formula::mem(tw, falsity::false_set(&s)), absurdity)
    );
}

/// `⊢ ⟦False⟧ ∈ ⟦Prop⟧`, `⊢ ⟦True⟧ ∈ ⟦Prop⟧`, and — the non-vacuity check —
/// `⊢ ¬(⟦False⟧ = ⟦True⟧)`.
///
/// Without the third, `⟦Prop⟧` could be a singleton and "denotes `1`" would say
/// nothing about a proposition.
#[test]
fn prop_is_a_two_element_set_of_truth_values() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let pv = falsity::truth_values(&s);
    let (f, t) = (falsity::false_set(&s), falsity::true_set(&s));

    // The term really is the unordered pair `{0, 1}`.
    assert_eq!(pv, Term::apply(s.ap.sets.up, vec![s.zero(), s.unit()]));
    assert_ne!(f, t);

    let ff = falsity::false_in_prop(&s).expect("0 ∈ {0,1}");
    let tt = falsity::true_in_prop(&s).expect("1 ∈ {0,1}");
    let distinct = falsity::prop_two_valued(&s).expect("¬(0 = 1)");
    for th in [&ff, &tt, &distinct] {
        assert!(kernel::thm::debug_locally_closed(th.concl()));
    }
    assert_eq!(*ff.concl(), Formula::mem(f.clone(), pv.clone()));
    assert_eq!(*tt.concl(), Formula::mem(t.clone(), pv));
    assert_eq!(*distinct.concl(), Formula::not(Formula::eq(f, t)));
}

/// `⊢ ∀p ∀x. ((p ∈ ⟦Prop⟧ ∧ x ∈ p) → x = •)` — proof irrelevance, for every
/// proposition, with no axiom and no appeal to how the proposition was built.
#[test]
fn every_proposition_is_a_subsingleton() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let t = falsity::prop_subsingleton(&mut env, &s).expect("proof irrelevance");
    assert!(kernel::thm::debug_locally_closed(t.concl()));

    let (p, x) = (env.fresh_var(), env.fresh_var());
    let (tp, tx) = (Term::var(p), Term::var(x));
    let want = Formula::forall(
        p,
        Formula::forall(
            x,
            Formula::imp(
                Formula::and(
                    Formula::mem(tp.clone(), falsity::truth_values(&s)),
                    Formula::mem(tx.clone(), tp),
                ),
                Formula::eq(tx, s.point()),
            ),
        ),
    );
    assert_eq!(*t.concl(), want);
}

/// `⊢ [φ] ∈ ⟦Prop⟧` — the denotation of a proposition is a truth value.
///
/// Checked at two instances with *opposite* polarity, because a lemma that put
/// every `[φ]` in `{0,1}` by always landing on the same value would prove
/// nothing: `[⊥]` is `0` and `[⊤]` is `1`, and the two are different terms with
/// different memberships.
#[test]
fn the_denotation_of_a_proposition_is_a_truth_value() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let pv = falsity::truth_values(&s);

    for phi in [Formula::false_(), Formula::not(Formula::false_())] {
        let (sym, ax) =
            derived::prop::conditional_singleton(&mut env, &s, &[], &phi).expect("[φ]");
        let c = Term::apply(sym, vec![]);
        let t = falsity::cond_in_prop(&mut env, &s, &phi, &c, &ax).expect("[φ] ∈ {0,1}");
        assert!(kernel::thm::debug_locally_closed(t.concl()));
        assert_eq!(*t.concl(), Formula::mem(c, pv.clone()));
    }
}

/// `⊢ [⊥] = ⟦False⟧` — the two candidate readings of `False` agree.
///
/// Whether the interpretation reads `False` as the empty `Prop`-inductive (`0`,
/// the thesis's clause) or as the conditional singleton `{x ∈ 1 : ⊥}`, the
/// anchor holds: they are the same set.
#[test]
fn the_conditional_singleton_at_bottom_is_false() {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let bot = Formula::false_();
    let (sym, ax) = derived::prop::conditional_singleton(&mut env, &s, &[], &bot).expect("[⊥]");
    let c = Term::apply(sym, vec![]);

    let t = falsity::bot_is_false(&mut env, &s, &c, &ax).expect("[⊥] = 0");
    assert!(kernel::thm::debug_locally_closed(t.concl()));
    assert_eq!(*t.concl(), Formula::eq(c, falsity::false_set(&s)));
}
