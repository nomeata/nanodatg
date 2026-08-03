//! **A declaration's fibre values, read off the spec** —
//! `derived::inductive::carrier::fibre_values`, and what `CtorSpec::rec_doms`
//! buys.
//!
//! The thesis's recursive-argument rule gives the `j`-th recursive argument the
//! fibre summand `Σ(z :: γⱼ)`, so a constructor's fibre is
//! `Sum_m(Σ(z::γ₀) … Σ(z::γ_{m-1}))`. `#37`'s restriction was that `γⱼ` could
//! not be named: `CtorSpec::recs` is a `usize`, so every `γⱼ` was `∅` and every
//! fibre was `finord(m)`.
//!
//! Two things have to hold at once, and one declaration has to show both:
//!
//! * a **plain** recursive argument still produces *literally* `finord(m)`, not
//!   something provably equal to it — otherwise every constructor term in the
//!   project changes shape;
//! * a **function-typed** one produces `Sum_m` of the telescope's type, which no
//!   count can name.
//!
//! So the fixture is a three-constructor declaration with a nullary, a plain
//! recursive and a function-typed recursive constructor. Two would not do it:
//! a computation that ignored `rec_doms` passes on the first two, and one that
//! applied a telescope uniformly passes on the last two.

use kernel::{Env, FnSym, FreeVar, Term};

use derived::bound::Bound;
use derived::inductive::carrier::fibre_values;
use derived::inductive::{CtorSpec, DeclSpec, Machine};
use derived::sigma::Telescope;
use derived::wtype::Wtype;

fn fixture(env: &mut Env) -> Machine {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 4).expect("the sum symbols");
    mach
}

/// A symbol of the given arity whose body is a fixed closed set.
fn konst(env: &mut Env, arity: usize, v: Term) -> FnSym {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    derived::define_abbrev(env, &vars, &v).expect("an abbreviation").0
}

/// **The plain case is unchanged, and the named case is expressible.**
#[test]
fn a_named_domain_gives_a_fibre_no_count_can_produce() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let s = mach.wt.sums.clone();
    let boolean = mach.syms.finord(&s, 2).expect("finord(2)");
    // `Bool()` — a named closed set, how an interpretation arrives.
    let bool_sym = konst(&mut env, 0, boolean);

    let spec = DeclSpec::new(
        0,
        vec![
            // `leaf`
            CtorSpec::nullary(),
            // `succ : T → T` — one *plain* recursive argument, `γ₀ = ∅`.
            CtorSpec::new(Vec::new(), 1),
            // `node : (Bool → T) → T` — `RTree`'s constructor, `γ₀ = [Bool]`.
            CtorSpec::with_rec_doms(Vec::new(), vec![vec![bool_sym]]),
        ],
    );
    assert!(spec.well_formed(), "a named domain is well formed");

    let vs = fibre_values(&mut env, &mut mach, &spec, &[]).expect("the fibre values");
    assert_eq!(vs.len(), 3);

    // ── the plain constructors: *literally* the finite ordinals ─────────────
    assert_eq!(vs[0], mach.syms.finord(&s, 0).expect("finord(0)"), "leaf");
    assert_eq!(
        vs[1],
        mach.syms.finord(&s, 1).expect("finord(1)"),
        "a plain recursive argument still spells its fibre `finord(1)` — not \
         something provably equal to it, or every constructor term would move"
    );

    // ── the function-typed constructor: `Sum_1(Σz:Bool. 1)` ─────────────────
    let tel = mach.telescope(&mut env, 0, &[bool_sym]).expect("the domain telescope");
    let want = mach.syms.sum(&[tel.ty_of(Vec::new())]).expect("Sum_1");
    assert_eq!(vs[2], want, "the fibre is `Sum_1` of the telescope's type");

    // …and it is not any finite ordinal, which is the whole point.
    for m in 0..5 {
        assert_ne!(vs[2], mach.syms.finord(&s, m).expect("finord"), "not finord({m})");
    }
    assert_ne!(vs[2], vs[1], "the two recursive constructors branch differently");
}

/// **`Σ(z::γ)` at a parameter**, so the telescope really is applied to the
/// declaration's parameters and not to nothing.
///
/// This is also the shape that meets `fibre.rs`'s *other* boundary: the value
/// is now **open** in `α`, and `Fibre::new` refuses an open value because its
/// branches are constant-body lambda graphs. Recording that here means the two
/// findings meet in one test rather than in two headers.
#[test]
fn the_domain_telescope_is_applied_to_the_parameters() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    // `γ₀ = [α]` — the binder's type *is* the parameter, arity `np + 0 = 1`.
    let vars = vec![env.fresh_var()];
    let dom = derived::define_abbrev(&mut env, &vars, &Term::var(vars[0]))
        .expect("γ₀(α) = α")
        .0;
    let spec = DeclSpec::new(1, vec![CtorSpec::with_rec_doms(Vec::new(), vec![vec![dom]])]);
    assert!(spec.well_formed());

    let pv = env.fresh_var();
    let ps = vec![Term::var(pv)];
    let vs = fibre_values(&mut env, &mut mach, &spec, &ps).expect("the fibre values");

    let tel = mach.telescope(&mut env, 1, &[dom]).expect("the telescope");
    assert_eq!(vs[0], mach.syms.sum(&[tel.ty_of(ps.clone())]).expect("Sum_1"));

    // The value mentions the parameter — the infinitary shape `α → T α`.
    let mut fv = Vec::new();
    vs[0].free_vars(&mut fv);
    assert_eq!(fv, vec![pv], "the fibre is open in the declaration's parameter");
}

/// **What the spec refuses.** `rec_doms` is either absent — every `γⱼ` empty —
/// or exactly one telescope per recursive argument, each binder type at the
/// arity `Telescope` applies it at.
#[test]
fn a_mismatched_domain_list_is_not_well_formed() {
    let mut env = Env::new();
    let mut mach = fixture(&mut env);
    let s = mach.wt.sums.clone();
    let unit = konst(&mut env, 0, s.unit());
    let unit1 = konst(&mut env, 1, s.unit());

    // Two recursive arguments, one domain named.
    let mut short = CtorSpec::new(Vec::new(), 2);
    short.rec_doms = vec![vec![unit]];
    assert!(!DeclSpec::new(0, vec![short]).well_formed(), "one domain, two arguments");

    // A binder type of the wrong arity: `γ₀[0]` must be `np + 0 = 0`.
    let bad_arity = CtorSpec::with_rec_doms(Vec::new(), vec![vec![unit1]]);
    assert!(
        !DeclSpec::new(0, vec![bad_arity]).well_formed(),
        "`γⱼ[i]` has arity `np + i`, as everywhere else in the spec"
    );

    // Absent is fine and means every `γⱼ` is empty.
    let plain = CtorSpec::new(Vec::new(), 2);
    assert!(plain.rec_doms.is_empty() && plain.rec_dom(0).is_empty());
    let spec = DeclSpec::new(0, vec![plain]);
    assert!(spec.well_formed());
    let vs = fibre_values(&mut env, &mut mach, &spec, &[]).expect("values");
    assert_eq!(vs[0], mach.syms.finord(&s, 2).expect("finord(2)"), "absent ⇒ finord(m)");

    let _ = Telescope::tuple_of(&s, &[]);
}
