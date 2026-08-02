//! **A declaration with no constructors** — `derived/src/inductive/empty_decl.rs`,
//! at `Empty` (`059_emptyRec`) and at a parameterised analogue.
//!
//! # Non-vacuity, in the direction that matters here
//!
//! Every theorem in this file has a vacuously true conclusion, which makes it
//! the easiest kind of thing in this library to prove by accident. Two things
//! are therefore pinned rather than assumed:
//!
//! * the carrier is `0` **as an equation at a concrete set**, and `⊢ ¬(0 = 1)`
//!   says that is a different answer from `1` — a *membership* statement about
//!   a carrier would have survived either;
//! * `rec_typed`'s schema is shown **equivalent** to emptiness, by deriving the
//!   converse `⊢ schema → ∀z. ¬(z ∈ C)` at an arbitrary `C` with nothing about
//!   `Empty` in scope. That is what rules out the reading the coordinator
//!   warned about: a "for all `t ∈ ind()`, anything" theorem that would also
//!   hold of a carrier equal to `1` under a constant motive. It would not — take
//!   the motive `∅`, whose value everywhere is `∅`.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::{CtorSpec, DeclSpec, EmptyDecl, Inductive, Machine};
use derived::tower::Tower;
use derived::wtype::Wtype;
use derived::wrec_total::Recursor;
use derived::{
    conjoin, eq_symm, establishes, gen_all, imp_refl, inst_all, syl, uncurry,
};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed_f(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// From `⊢ x = y` and `⊢ φ(x)` infer `⊢ φ(y)`, the hole possibly occurring
/// more than once.
fn rw(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), base).expect("mp")
}

/// `⊢ H → φ` to `⊢ H → ∀v. φ`, for `v` not free in `H` — `gen_under`, which is
/// `pub(crate)`.
fn gen_under(v: FreeVar, h: &Formula, t: &Thm) -> Thm {
    let (_, body) = t.concl().as_imp().expect("an implication");
    Thm::mp(&Thm::ax_dist(v, h.clone(), body).expect("dist"), &Thm::gen(v, t)).expect("mp")
}

/// `⊢ H → ∀v₀…. φ` to `⊢ H → φ[t⃗]` — `hyp_inst`, likewise.
fn hyp_inst(t: &Thm, ts: &[Term]) -> Thm {
    let mut cur = t.clone();
    for x in ts {
        let (_, all) = cur.concl().as_imp().expect("an implication");
        cur = syl(&cur, &Thm::ax_inst(all, x.clone()).expect("inst")).expect("syl");
    }
    cur
}

struct Fix {
    tow: Tower,
    mach: Machine,
}

fn fixture(env: &mut Env) -> Fix {
    let tow = Tower::new(env).expect("tower");
    let wt = Wtype::over(env, tow.sums.clone()).expect("W-type over the same sums");
    let bnd =
        Bound::over(env, &wt, tow.space.lu, tow.space.lu_ax.clone()).expect("bound over U(·)");
    let mach = Machine::over(env, wt, bnd).expect("machine");
    Fix { tow, mach }
}

// ─────────────────────────────────────────────────────────────────────────────
// `Empty` — the corpus shape
// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable.** `inductive Empty` has an empty carrier, a
/// `∀f ∀g`-quantified eliminator typing, and **no ι rules**.
#[test]
fn the_empty_declaration_has_an_empty_carrier_and_a_typed_eliminator() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let (one, zero) = (s.unit(), s.zero());

    let spec = DeclSpec::new(0, Vec::new());
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("Empty");
    assert!(ind.ctors.is_empty(), "no constructors, hence no ι rule to state");

    let ed = EmptyDecl::over_declaration(&mut env, &mach, &ind).expect("the empty declaration");
    assert!(ed.rests_on_nothing(), "every field is a ⊢ with nothing on the left");

    // ── `⊢ ∀z. ¬(z ∈ Empty)` ────────────────────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    assert_eq!(
        *ed.empty.concl(),
        Formula::forall(zv, Formula::not(Formula::mem(tz.clone(), ind.carrier.clone())))
    );
    assert!(closed_f(ed.empty.concl()));

    // ── `⊢ Empty = 0`, and that is **not** `1` ──────────────────────────────
    assert_eq!(*ed.is_zero.concl(), Formula::eq(ind.carrier.clone(), zero.clone()));
    let back = eq_symm(&mut env, &ed.is_zero).expect("symm");
    let not_unit =
        rw(&mut env, &back, |t| Formula::not(Formula::eq(t, one.clone())), &s.tags_distinct);
    assert_eq!(
        *not_unit.concl(),
        Formula::not(Formula::eq(ind.carrier.clone(), one.clone())),
        "⊢ ¬(⟦Empty⟧ = 1) — the carrier is not a one-point set"
    );
    assert!(closed_f(not_unit.concl()) && not_unit.hyps().is_empty());

    // ── the eliminator's typing, at any term and any motive ─────────────────
    let (ev, gv) = (env.fresh_var(), env.fresh_var());
    let (te, tg) = (Term::var(ev), Term::var(gv));
    assert_eq!(
        *ed.rec_typed.concl(),
        Formula::forall(
            ev,
            Formula::forall(
                gv,
                Formula::forall(
                    zv,
                    Formula::imp(
                        Formula::mem(tz.clone(), ind.carrier.clone()),
                        Formula::mem(
                            s.ap.apply(te.clone(), tz.clone()),
                            s.ap.apply(tg.clone(), tz.clone()),
                        ),
                    ),
                ),
            ),
        ),
        "⊢ ∀f ∀g ∀z. (z ∈ ⟦Empty⟧ → app(f,z) ∈ app(g,z))"
    );
    assert!(closed_f(ed.rec_typed.concl()));

    // …and the empty function is a function out of it, at any target.
    let tv = env.fresh_var();
    let tt = Term::var(tv);
    assert_eq!(
        *ed.rec_in_funspace.concl(),
        Formula::forall(
            tv,
            Formula::mem(zero.clone(), s.fs.of(ind.carrier.clone(), tt.clone()))
        ),
        "⊢ ∀T. ∅ ∈ fs(⟦Empty⟧, T)"
    );
    assert!(closed_f(ed.rec_in_funspace.concl()));

    // ── there is no ι rule, and the general recursor says so ────────────────
    let rc = Recursor::new(&mut env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(&mut env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(&mut env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(&mut env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(&mut env, &mach.wt, &rc, &total).expect("funspace");
    assert!(
        derived::inductive::GenRecursor::build(&mut env, &mach, &ind, &rc, &iota, &funspace)
            .is_none(),
        "the general recursor declines a declaration with no constructors, by decision"
    );
}

/// **`rec_typed` is equivalent to emptiness**, so it is not the tautology its
/// vacuous conclusion makes it look like.
///
/// The converse is derived at an **arbitrary** set `C`, with nothing about
/// `Empty` in scope: take the motive `∅`, whose value at every argument is `∅`
/// (`wtype::app_of_empty`), and the schema puts something into the empty set for
/// every member of `C`. So `C` has none. Instantiating that at `⟦Empty⟧` and
/// discharging it with `rec_typed` reproduces `EmptyDecl::empty` on the nose —
/// the two statements carry the same content, and a carrier equal to `1` could
/// satisfy neither.
#[test]
fn the_eliminator_typing_is_equivalent_to_the_carrier_being_empty() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let ap = s.ap.clone();
    let zero = s.zero();

    // The schema, at an arbitrary `C`.
    let (cv, ev, gv, zv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, te, tg, tz) = (Term::var(cv), Term::var(ev), Term::var(gv), Term::var(zv));
    let mem_c = Formula::mem(tz.clone(), tc.clone());
    let schema = Formula::forall(
        ev,
        Formula::forall(
            gv,
            Formula::forall(
                zv,
                Formula::imp(
                    mem_c.clone(),
                    Formula::mem(ap.apply(te.clone(), tz.clone()), ap.apply(tg, tz.clone())),
                ),
            ),
        ),
    );

    // At `f := ∅` and `g := ∅`, both sides of the membership compute to `∅`.
    let at = hyp_inst(&imp_refl(schema.clone()), &[zero.clone(), zero.clone(), tz.clone()]);
    let app_zero = inst_all(
        &derived::wtype::app_of_empty(&mut env, &s).expect("⊢ ∀a. app(∅,a) = ∅"),
        std::slice::from_ref(&tz),
    )
    .expect("app(∅,z) = ∅");
    let (sc, mc) = (schema.clone(), mem_c.clone());
    let collapsed = rw(
        &mut env,
        &app_zero,
        move |h| {
            Formula::imp(
                sc.clone(),
                Formula::imp(mc.clone(), Formula::mem(h.clone(), h)),
            )
        },
        &at,
    );
    let no_self = inst_all(&s.ap.empty_ax, std::slice::from_ref(&zero)).expect("¬(∅ ∈ ∅)");
    let refuted = uncurry(
        &syl(&conjoin(&collapsed).expect("conjoin"), &no_self).expect("syl"),
    )
    .expect("uncurry");
    let converse = gen_under(zv, &schema, &refuted);
    assert_eq!(
        *converse.concl(),
        Formula::imp(
            schema.clone(),
            Formula::forall(zv, Formula::not(mem_c))
        ),
        "⊢ schema(C) → ∀z. ¬(z ∈ C), at an arbitrary C"
    );
    assert!(converse.hyps().is_empty());

    // Now at `⟦Empty⟧`: the schema *is* `rec_typed`, and it gives back `empty`.
    let spec = DeclSpec::new(0, Vec::new());
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("Empty");
    let ed = EmptyDecl::over_declaration(&mut env, &mach, &ind).expect("the empty declaration");

    let at_empty = inst_all(&Thm::gen(cv, &converse), std::slice::from_ref(&ind.carrier))
        .expect("at C := ⟦Empty⟧");
    let (ante, _) = at_empty.concl().as_imp().expect("an implication");
    assert_eq!(ante, *ed.rec_typed.concl(), "the schema at ⟦Empty⟧ is rec_typed");

    let back = Thm::mp(&at_empty, &ed.rec_typed).expect("mp");
    assert!(
        establishes(&back, ed.empty.concl()),
        "rec_typed recovers `empty` — the two say the same thing"
    );
}

/// **What a real consumer has to hold.** `rec_typed` fixes the *shape* of the
/// obligation — `app(f,z) ∈ app(g,z)`, which is what a **dependent** motive
/// produces. A non-dependent one asks for `app(f,z) ∈ T`, which is not an
/// instance of it, and a wiring stating its typing some third way asks for
/// something else again.
///
/// `EmptyDecl::anything` is the scheme all of them are instances of, and this
/// derives the non-dependent form through it — the shape
/// `wrec_total::wrec_funspace` produces for every other declaration, so it is
/// the one a uniform recursor path will actually have in hand.
#[test]
fn any_obligation_guarded_by_the_carrier_is_one_ex_falso() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();

    let ind = Inductive::build(&mut env, &mut mach, &DeclSpec::new(0, Vec::new())).expect("Empty");
    let ed = EmptyDecl::over_declaration(&mut env, &mach, &ind).expect("the empty declaration");

    // The **non-dependent** target: `app(f,z) ∈ T`.
    let (ev, tv, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (te, tt, tz) = (Term::var(ev), Term::var(tv), Term::var(zv));
    let phi = Formula::mem(s.ap.apply(te.clone(), tz.clone()), tt.clone());
    let got = ed.anything(&ind, zv, &phi).expect("ex falso at the empty carrier");
    assert_eq!(
        *got.concl(),
        Formula::forall(
            zv,
            Formula::imp(Formula::mem(tz.clone(), ind.carrier.clone()), phi.clone())
        ),
        "⊢ ∀z. (z ∈ ⟦Empty⟧ → app(f,z) ∈ T)"
    );
    assert!(got.hyps().is_empty());
    // `f` and `T` are still free, so the caller closes over whatever it owns.
    let closed_over = gen_all(&[ev, tv], &got);
    assert!(closed_f(closed_over.concl()));

    // `rec_typed` is the same scheme at the dependent motive — checked, so the
    // field and the scheme cannot drift apart.
    let gv = env.fresh_var();
    let dep = Formula::mem(
        s.ap.apply(te.clone(), tz.clone()),
        s.ap.apply(Term::var(gv), tz.clone()),
    );
    let via_scheme = gen_all(&[ev, gv], &ed.anything(&ind, zv, &dep).expect("the scheme"));
    assert!(
        establishes(&via_scheme, ed.rec_typed.concl()),
        "rec_typed is `anything` at the dependent motive"
    );

    // The guards: a parameter as the bound variable would capture, and a
    // declaration this was not built over is refused.
    let ind2 = Inductive::build(&mut env, &mut mach, &DeclSpec::new(1, Vec::new()))
        .expect("a second, parameterised Empty");
    assert!(ed.anything(&ind2, zv, &phi).is_none(), "another declaration's carrier");
    let ed2 = EmptyDecl::over_declaration(&mut env, &mach, &ind2).expect("the second one");
    assert!(
        ed2.anything(&ind2, ind2.params[0], &phi).is_none(),
        "the bound variable must not be a parameter"
    );
    assert!(ed2.anything(&ind2, zv, &phi).is_some());
}

// ─────────────────────────────────────────────────────────────────────────────
// Parameters, and the guards
// ─────────────────────────────────────────────────────────────────────────────

/// The construction is general in `np`, and every theorem is `∀p⃗`-closed.
///
/// `Empty` itself has no parameters; a zero-constructor declaration with two is
/// perfectly expressible (`inductive Foo (α β : Type) : Type`) and the `∀p⃗`
/// prefix is the only thing that changes.
#[test]
fn the_parameters_are_generalised() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();

    let spec = DeclSpec::new(2, Vec::new());
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("a parameterised Empty");
    let ed = EmptyDecl::over_declaration(&mut env, &mach, &ind).expect("the empty declaration");
    assert!(ed.rests_on_nothing());

    let ps: Vec<Term> = ind.params.iter().map(|v| Term::var(*v)).collect();
    assert_eq!(ps.len(), 2);
    let at = inst_all(&ed.is_zero, &ps).expect("at the declaration's own parameters");
    assert_eq!(*at.concl(), Formula::eq(ind.carrier.clone(), s.zero()));
    assert!(closed_f(ed.is_zero.concl()), "closed once the parameters are generalised");

    // The carrier is the same set at *any* two instantiations, since it is `0`
    // — which is worth having in writing, because a parameterised declaration
    // whose carrier did not mention its parameters would be a bug elsewhere.
    let (one, zero) = (s.unit(), s.zero());
    let at_11 = inst_all(&ed.is_zero, &[one.clone(), one.clone()]).expect("at (1,1)");
    let at_10 = inst_all(&ed.is_zero, &[one.clone(), zero.clone()]).expect("at (1,0)");
    assert_eq!(
        at_11.concl().as_eq().expect("an equation").1,
        at_10.concl().as_eq().expect("an equation").1
    );
    assert_ne!(
        at_11.concl().as_eq().expect("an equation").0,
        at_10.concl().as_eq().expect("an equation").0,
        "the two instantiations are different terms, both equal to 0"
    );
}

/// What the build refuses, and why each refusal is a decision.
#[test]
fn the_empty_declaration_refuses_what_it_cannot_state() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let one = s.unit();

    // A declaration *with* a constructor has an inhabited carrier, and every
    // theorem here would be false of it.
    let (b0, _) = derived::define_abbrev(&mut env, &[], &one).expect("β₀ = 1");
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0], 0)]);
    let ind = Inductive::build(&mut env, &mut mach, &spec).expect("a one-constructor declaration");
    assert!(
        EmptyDecl::over_declaration(&mut env, &mach, &ind).is_none(),
        "a declaration with constructors was accepted"
    );

    // The honest one builds, and a foreign apparatus does not.
    let empty_spec = DeclSpec::new(0, Vec::new());
    let empty_ind = Inductive::build(&mut env, &mut mach, &empty_spec).expect("Empty");
    assert!(EmptyDecl::over_declaration(&mut env, &mach, &empty_ind).is_some());

    let m2 = Machine::over(&mut env, mach.wt.clone(), mach.bnd.clone()).expect("a second machine");
    assert!(!empty_ind.is_over(&m2));
    assert!(
        EmptyDecl::over_declaration(&mut env, &m2, &empty_ind).is_none(),
        "a foreign machine was accepted"
    );

    // The tower is the fixture's own — a second signature would give `‖·‖`,
    // `U₀` and `W` different unit sets, and the emptiness argument runs on
    // `Sum_0()` from exactly one of them.
    assert_eq!(s.ap.sets.up, f.tow.sums.ap.sets.up, "one signature");
}
