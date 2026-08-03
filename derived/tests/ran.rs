//! The range `ran(g) = { y : ∃a. ⟨a,y⟩ ∈ g }` — the codomain a dispatcher over
//! branch *variables* has to build for itself.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! **Non-vacuity is the whole game, and it needs both directions.**
//! [`Ran::subset`] alone is satisfied by `ran(g) := ∅` and [`Ran::retarget`]
//! alone by `ran(g) := V`. [`the_empty_graph_has_an_empty_range`] and
//! [`a_one_point_graph_holds_its_value_in_its_range`] pin the symbol between the
//! two: it is provably empty at one graph and provably inhabited at another, and
//! at the second the inclusion still forces the value into any real codomain.

use kernel::{Env, Formula, Term, Thm};

use derived::ran::Ran;
use derived::sums::Sums;
use derived::{
    all_unconditional, establishes, exists_intro_imp, iff_mp, iff_mpr, inst_all, mpd_const,
    notnot_intro, singleton, syl,
};

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

fn setup() -> (Env, Sums, Ran) {
    let mut env = Env::new();
    let s = Sums::new(&mut env).expect("sums");
    let r = Ran::new(&mut env, &s).expect("ran");
    (env, s, r)
}

#[test]
fn the_range_is_characterised_by_its_pairs() {
    let (mut env, s, r) = setup();
    let (g, y, a) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, ty, ta) = (Term::var(g), Term::var(y), Term::var(a));

    let want = Formula::forall(
        g,
        Formula::forall(
            y,
            Formula::iff(
                Formula::mem(ty.clone(), r.of(tg.clone())),
                Formula::exists(a, Formula::mem(s.ap.sets.pair(ta, ty), tg)),
            ),
        ),
    );
    assert!(closed(&want));
    assert!(establishes(&r.mem, &want), "ran's membership rule is not the stated one");
}

#[test]
fn the_range_is_included_in_every_codomain() {
    let (mut env, s, r) = setup();
    let (a, t, g) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tt, tg) = (Term::var(a), Term::var(t), Term::var(g));

    let inner = Formula::imp(
        Formula::mem(tg.clone(), s.fs.of(ta.clone(), tt.clone())),
        kernel::thm::subset(&mut env, r.of(tg), tt),
    );
    let want = Formula::forall(a, Formula::forall(t, Formula::forall(g, inner)));
    assert!(closed(&want));
    assert!(establishes(&r.subset, &want), "ran's inclusion is not the stated one");
}

#[test]
fn a_function_is_a_function_onto_its_range() {
    let (mut env, s, r) = setup();
    let (a, t, g) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tt, tg) = (Term::var(a), Term::var(t), Term::var(g));

    let inner = Formula::imp(
        Formula::mem(tg.clone(), s.fs.of(ta.clone(), tt)),
        Formula::mem(tg.clone(), s.fs.of(ta, r.of(tg))),
    );
    let want = Formula::forall(a, Formula::forall(t, Formula::forall(g, inner)));
    assert!(closed(&want));
    assert!(establishes(&r.retarget, &want), "ran's retarget is not the stated one");
    assert!(all_unconditional(&[&r.mem, &r.subset, &r.retarget]));
}

/// `⊢ ¬(y ∈ ran(∅))` — the range of the empty graph is empty.
///
/// Half of the non-vacuity pin: a `ran` that returned the universe, or any
/// fixed inhabited set, would satisfy [`Ran::retarget`] and fail here.
#[test]
fn the_empty_graph_has_an_empty_range() {
    let (mut env, s, r) = setup();
    let (y, b) = (env.fresh_var(), env.fresh_var());
    let (ty, tb) = (Term::var(y), Term::var(b));
    let zero = s.zero();

    let pair = s.ap.sets.pair(tb, ty.clone());
    let body = Formula::mem(pair.clone(), zero.clone());
    let nothing = Thm::gen(b, &inst_all(&s.ap.empty_ax, &[pair]).expect("∅ has no members"));
    let no_witness = Thm::mp(
        &notnot_intro(Formula::forall(b, Formula::not(body.clone()))),
        &nothing,
    )
    .expect("¬∃ is ¬¬∀¬");

    let at = inst_all(&r.mem, &[zero.clone(), ty.clone()]).expect("ran at ∅");
    let out = Thm::mp(
        &derived::contrapos(&iff_mp(&at).expect("forward")).expect("contraposition"),
        &no_witness,
    )
    .expect("nothing is in the range of ∅");
    assert_eq!(*out.concl(), Formula::not(Formula::mem(ty, r.of(zero))));
    assert!(out.hyps().is_empty());
}

/// `⊢ r ∈ ran({⟨•,r⟩})` and `⊢ {⟨•,r⟩} ∈ fs(A,T) → r ∈ T`.
///
/// The other half. A `ran` that returned `∅` would satisfy [`Ran::subset`] and
/// fail the first; and the second is the shape a codomain-builder spends —
/// the inclusion carries a *value* out of the range into the real codomain,
/// which is only true because the range is small enough.
#[test]
fn a_one_point_graph_holds_its_value_in_its_range() {
    let (mut env, s, r) = setup();
    let (v, b) = (env.fresh_var(), env.fresh_var());
    let (tv, tb) = (Term::var(v), Term::var(b));
    let point = s.point();

    let pair = s.ap.sets.pair(point.clone(), tv.clone());
    let g = singleton(s.ap.sets.up, pair.clone());

    // ⟨•,v⟩ ∈ {⟨•,v⟩}
    let self_mem = Thm::mp(
        &iff_mpr(
            &inst_all(&s.ap.mem_sing, &[pair.clone(), pair.clone()]).expect("mem_sing"),
        )
        .expect("backward"),
        &Thm::eq_refl(pair),
    )
    .expect("the graph holds its own pair");

    let intro = exists_intro_imp(
        b,
        Formula::mem(s.ap.sets.pair(tb, tv.clone()), g.clone()),
        point,
    )
    .expect("existential introduction");
    let to_ran = syl(
        &intro,
        &iff_mpr(&inst_all(&r.mem, &[g.clone(), tv.clone()]).expect("ran at the graph"))
            .expect("backward"),
    )
    .expect("a pair puts its value in the range");
    let in_ran = Thm::mp(&to_ran, &self_mem).expect("modus ponens");
    assert_eq!(*in_ran.concl(), Formula::mem(tv.clone(), r.of(g.clone())));

    // …and the inclusion carries it back out into any real codomain.
    let (a, t) = (env.fresh_var(), env.fresh_var());
    let (ta, tt) = (Term::var(a), Term::var(t));
    let sub = inst_all(&r.subset, &[ta.clone(), tt.clone(), g.clone()]).expect("inclusion");
    let (h, sub_f) = sub.concl().as_imp().expect("an implication");
    let out = mpd_const(
        &syl(&sub, &Thm::ax_inst(sub_f, tv.clone()).expect("instantiate the inclusion"))
            .expect("compose"),
        &in_ran,
    )
    .expect("the value is in the codomain");
    assert_eq!(h, Formula::mem(g, s.fs.of(ta, tt.clone())));
    assert_eq!(*out.concl(), Formula::imp(h, Formula::mem(tv, tt)));
    assert!(out.hyps().is_empty());
}
