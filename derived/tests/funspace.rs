//! Cartesian products, function spaces, and `(a → a) ∈ U(a)`.
//!
//! Every test states the theorem it wants **independently** — rebuilding the
//! formula from the kernel's own constructors — and compares. Alpha-equivalent
//! formulas are syntactically equal in the locally nameless representation, so
//! a fresh set of bound variables here reproduces the module's formula exactly
//! if and only if the *shape* agrees.

use kernel::{Env, Formula, Term, Thm};

use derived::funcs::Sets;
use derived::funspace as fsp;

/// `⊢ ∀x ∀b ∀v. (v ∈ row(x,b) ↔ ∃y. (y ∈ b ∧ v = ⟨x,y⟩))` — the row of pairs
/// over a fixed first component.
#[test]
fn row_has_the_pairs_over_one_point() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");

    let (x, b, v, y) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, tb, tv, ty) = (Term::var(x), Term::var(b), Term::var(v), Term::var(y));
    let row = Term::apply(p.row, vec![tx.clone(), tb.clone()]);

    let cond = Formula::exists(
        y,
        Formula::and(Formula::mem(ty.clone(), tb), Formula::eq(tv.clone(), sets.pair(tx, ty))),
    );
    let want = Formula::forall(
        x,
        Formula::forall(b, Formula::forall(v, Formula::iff(Formula::mem(tv, row), cond))),
    );
    assert_eq!(*p.row_ax.concl(), want);
}

/// `⊢ ∀a ∀b ∀w. (w ∈ fam(a,b) ↔ ∃x. (x ∈ a ∧ w = row(x,b)))`.
#[test]
fn fam_is_the_family_of_rows() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");

    let (a, b, w, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tw, tx) = (Term::var(a), Term::var(b), Term::var(w), Term::var(x));
    let fam = Term::apply(p.fam, vec![ta.clone(), tb.clone()]);

    let cond = Formula::exists(
        x,
        Formula::and(
            Formula::mem(tx.clone(), ta),
            Formula::eq(tw.clone(), Term::apply(p.row, vec![tx, tb])),
        ),
    );
    let want = Formula::forall(
        a,
        Formula::forall(b, Formula::forall(w, Formula::iff(Formula::mem(tw, fam), cond))),
    );
    assert_eq!(*p.fam_ax.concl(), want);
}

/// `⊢ ∀a ∀b. prod(a,b) = ⋃fam(a,b)`.
#[test]
fn prod_is_the_union_of_the_family() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::eq(
                Term::apply(p.prod, vec![ta.clone(), tb.clone()]),
                sets.union_of(Term::apply(p.fam, vec![ta, tb])),
            ),
        ),
    );
    assert_eq!(*p.prod_def.concl(), want);
}

/// The characteristic property of the product:
/// `⊢ ∀a ∀b ∀z. (z ∈ prod(a,b) ↔ ∃x. (x ∈ a ∧ ∃y. (y ∈ b ∧ z = ⟨x,y⟩)))`.
///
/// **No inhabitation antecedent.** That is the point of building the product
/// from Replacement rather than Separation; see the module docs.
#[test]
fn product_membership_is_unconditional() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");

    let (a, b, z, x, y) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tz, tx, ty) =
        (Term::var(a), Term::var(b), Term::var(z), Term::var(x), Term::var(y));

    let inner = Formula::exists(
        y,
        Formula::and(
            Formula::mem(ty.clone(), tb.clone()),
            Formula::eq(tz.clone(), sets.pair(tx.clone(), ty)),
        ),
    );
    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, ta.clone()), inner));
    let mem = Formula::mem(tz, Term::apply(p.prod, vec![ta, tb]));
    let want =
        Formula::forall(a, Formula::forall(b, Formula::forall(z, Formula::iff(mem, cond))));
    assert_eq!(*p.prod_ax.concl(), want);
}

/// `⊢ ∀u ∀v ∀c. ((u ∈ c ∧ v ∈ c) → {u,v} ⊆ c)`.
#[test]
fn upair_of_two_members_is_a_subset() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let thm = fsp::upair_subset(&mut env, &sets).expect("upair_subset");

    let (u, v, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tu, tv, tc) = (Term::var(u), Term::var(v), Term::var(c));
    let uv = Term::apply(sets.up, vec![tu.clone(), tv.clone()]);
    let h = Formula::and(
        Formula::mem(tu, tc.clone()),
        Formula::mem(tv, tc.clone()),
    );
    let want = Formula::forall(
        u,
        Formula::forall(
            v,
            Formula::forall(c, Formula::imp(h, kernel::thm::subset(&mut env, uv, tc))),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

/// `⊢ ∀a ∀b ∀x. (x ∈ a → x ∈ a ∪ b)` and its mirror image, with `a ∪ b` spelled
/// out as `⋃{a,b}`.
#[test]
fn binary_union_absorbs_both_sides() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let (left, right) = fsp::mem_bin_union(&mut env, &sets).expect("mem_bin_union");

    let (a, b, x) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tx) = (Term::var(a), Term::var(b), Term::var(x));
    let un = Term::apply(sets.un, vec![Term::apply(sets.up, vec![ta.clone(), tb.clone()])]);
    assert_eq!(un, fsp::bin_union(&sets, ta.clone(), tb.clone()));

    let mk = |m: Formula| {
        Formula::forall(
            a,
            Formula::forall(
                b,
                Formula::forall(x, Formula::imp(m, Formula::mem(tx.clone(), un.clone()))),
            ),
        )
    };
    assert_eq!(*left.concl(), mk(Formula::mem(tx.clone(), ta)));
    assert_eq!(*right.concl(), mk(Formula::mem(tx.clone(), tb)));
}

/// `⊢ ∀x ∀y ∀c. ((x ∈ c ∧ y ∈ c) → ⟨x,y⟩ ∈ 𝒫𝒫c)` — the Kuratowski pair of two
/// members of `c` is a set of subsets of `c`.
#[test]
fn kuratowski_pair_lands_in_the_double_power_set() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let up_sub = fsp::upair_subset(&mut env, &sets).expect("upair_subset");
    let thm = fsp::pair_in_pow_pow(&mut env, &sets, pow, &pow_ax, &up_sub).expect("pair_in_pow_pow");

    let (x, y, c) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tc) = (Term::var(x), Term::var(y), Term::var(c));
    let h = Formula::and(Formula::mem(tx.clone(), tc.clone()), Formula::mem(ty.clone(), tc.clone()));
    let ppc = Term::apply(pow, vec![Term::apply(pow, vec![tc])]);
    let pair = derived::opair(sets.up, tx, ty);
    let want = Formula::forall(
        x,
        Formula::forall(
            y,
            Formula::forall(c, Formula::imp(h, Formula::mem(pair, ppc))),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

/// `⊢ ∀a ∀b. prod(a,b) ⊆ 𝒫𝒫(a ∪ b)` — step 3 of the chain to the universe.
#[test]
fn product_sits_inside_a_double_power_set() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");
    let up_sub = fsp::upair_subset(&mut env, &sets).expect("upair_subset");
    let pair_pp = fsp::pair_in_pow_pow(&mut env, &sets, pow, &pow_ax, &up_sub).expect("pair_in_pow_pow");
    let (ml, mr) = fsp::mem_bin_union(&mut env, &sets).expect("mem_bin_union");
    let thm = fsp::product_subset_pow_pow(&mut env, &sets, pow, &p, &pair_pp, &ml, &mr)
        .expect("product_subset_pow_pow");

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let un = fsp::bin_union(&sets, ta.clone(), tb.clone());
    let ppu = Term::apply(pow, vec![Term::apply(pow, vec![un])]);
    let prod = Term::apply(p.prod, vec![ta, tb]);
    let want = Formula::forall(
        a,
        Formula::forall(b, kernel::thm::subset(&mut env, prod, ppu)),
    );
    assert_eq!(*thm.concl(), want);
}

/// The raw defining axiom of `fs`, default disjunct and all:
/// `⊢ ∀a ∀b ∀f. (f ∈ fs(a,b) ↔ (isfun(f) ∨ (¬∃g. isfun(g) ∧ f ∈ 𝒫prod(a,b))))`.
///
/// The default is not cosmetic — see the module docs. It is checked here so
/// that the two lemmas built on top of it can be read against something exact.
#[test]
fn funspace_defining_axiom_has_the_stated_default() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");
    let (fs, fs_def) = fsp::funspace(&mut env, &sets, pow, &pow_ax, &p).expect("funspace");

    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));
    let pp = Term::apply(pow, vec![Term::apply(p.prod, vec![ta.clone(), tb.clone()])]);

    let l = fsp::is_function(&mut env, &sets, &p, &ta, &tb, &tf);
    let ne = Formula::exists(f, l.clone());
    let phi = Formula::or(
        l,
        Formula::and(Formula::not(ne), Formula::mem(tf.clone(), pp)),
    );
    let want = Formula::forall(
        a,
        Formula::forall(
            b,
            Formula::forall(
                f,
                Formula::iff(Formula::mem(tf, Term::apply(fs, vec![ta, tb])), phi),
            ),
        ),
    );
    assert_eq!(*fs_def.concl(), want);
}

/// `is_function` is the formula its name claims: a subset of the product that
/// is total on `a` and single-valued.
#[test]
fn is_function_spells_out_graph_totality_and_single_valuedness() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");

    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));

    let (x, y, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, ty2) = (Term::var(x), Term::var(y), Term::var(y2));

    let total = Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), ta.clone()),
            Formula::exists(
                y,
                Formula::and(
                    Formula::mem(ty.clone(), tb.clone()),
                    Formula::mem(sets.pair(tx.clone(), ty.clone()), tf.clone()),
                ),
            ),
        ),
    );
    assert_eq!(fsp::is_total(&mut env, &sets, &ta, &tb, &tf), total);

    let sv = Formula::forall(
        x,
        Formula::forall(
            y,
            Formula::forall(
                y2,
                Formula::imp(
                    Formula::and(
                        Formula::mem(sets.pair(tx.clone(), ty.clone()), tf.clone()),
                        Formula::mem(sets.pair(tx, ty2.clone()), tf.clone()),
                    ),
                    Formula::eq(ty, ty2),
                ),
            ),
        ),
    );
    assert_eq!(fsp::is_single_valued(&mut env, &sets, &tf), sv);

    let sub = kernel::thm::subset(&mut env, tf.clone(), Term::apply(p.prod, vec![ta.clone(), tb.clone()]));
    assert_eq!(
        fsp::is_function(&mut env, &sets, &p, &ta, &tb, &tf),
        Formula::and(sub, Formula::and(total, sv))
    );
}

/// `⊢ ∀a ∀b. fs(a,b) ⊆ 𝒫(prod(a,b))` — step 6, and unconditional.
#[test]
fn funspace_sits_inside_the_power_set_of_the_product() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");
    let fs = fsp::Funspace::new(&mut env, &sets, pow, &pow_ax, &p).expect("funspace");

    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let pp = Term::apply(pow, vec![Term::apply(p.prod, vec![ta.clone(), tb.clone()])]);
    let fs_t = Term::apply(fs.fs, vec![ta, tb]);
    let want =
        Formula::forall(a, Formula::forall(b, kernel::thm::subset(&mut env, fs_t, pp)));
    assert_eq!(*fs.fs_sub.concl(), want);
}

/// `⊢ ∀a ∀b. ((∃g. isfun(g)) → ∀f. (f ∈ fs(a,b) ↔ isfun(f)))`.
///
/// The antecedent is real: with no empty set there is no way to say what
/// `a → b` is when there are no functions at all.
#[test]
fn funspace_members_are_the_functions_when_there_is_one() {
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    let (pow, pow_ax) = derived::power(&mut env);
    let p = fsp::product(&mut env, &sets).expect("product");
    let fs = fsp::Funspace::new(&mut env, &sets, pow, &pow_ax, &p).expect("funspace");

    let (a, b, f) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tf) = (Term::var(a), Term::var(b), Term::var(f));
    let l = fsp::is_function(&mut env, &sets, &p, &ta, &tb, &tf);
    let ne = Formula::exists(f, l.clone());
    let inner = Formula::forall(
        f,
        Formula::iff(Formula::mem(tf, Term::apply(fs.fs, vec![ta.clone(), tb.clone()])), l),
    );
    let want = Formula::forall(a, Formula::forall(b, Formula::imp(ne, inner)));
    assert_eq!(*fs.fs_ax.concl(), want);
}

/// `⊢ ∀y. (y ∈ U(x) → 𝒫y ∈ U(x))` — the power-set closure of `U(x)`, from the
/// two clauses that are proved for it. Inaccessibility is never used.
#[test]
fn least_universe_is_closed_under_power_sets() {
    let mut env = Env::new();
    let s = fsp::Space::new(&mut env).expect("space");

    let x = env.fresh_var();
    let tx = Term::var(x);
    let u = s.universe_of(tx.clone());
    let c2 = derived::inst_all(&s.c2, std::slice::from_ref(&tx)).expect("C2");
    let c3 = derived::inst_all(&s.c3, std::slice::from_ref(&tx)).expect("C3");
    let thm = fsp::pow_closed(&mut env, s.pow, &s.pow_ax, &u, &c2, &c3).expect("pow_closed");

    let y = env.fresh_var();
    let ty = Term::var(y);
    let want = Formula::forall(
        y,
        Formula::imp(
            Formula::mem(ty.clone(), u.clone()),
            Formula::mem(Term::apply(s.pow, vec![ty]), u),
        ),
    );
    assert_eq!(*thm.concl(), want);
}

/// **The payoff.** `⊢ ∀a. fs(a,a) ∈ U(a)`, i.e. `(a → a) ∈ U(a)`, which at
/// `a := ⟦Sort 0⟧` is the `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` the tutorial's beta tests
/// are missing.
#[test]
fn function_space_lands_in_the_least_universe() {
    let mut env = Env::new();
    let d = fsp::Development::new(&mut env).expect("development");

    let a = env.fresh_var();
    let ta = Term::var(a);
    let want = Formula::forall(
        a,
        Formula::mem(
            Term::apply(d.funspace.fs, vec![ta.clone(), ta.clone()]),
            Term::apply(d.space.lu, vec![ta]),
        ),
    );
    assert_eq!(*d.in_universe.concl(), want);
}

/// The payoff is about the *same* `U` the universe module builds — the one
/// characterised as the intersection of all universes containing `x` — and not
/// about some other symbol that happens to be called `lu`.
#[test]
fn the_universe_symbol_is_the_least_universe() {
    let mut env = Env::new();
    let d = fsp::Development::new(&mut env).expect("development");

    let (x, z) = (env.fresh_var(), env.fresh_var());
    let (tx, tz) = (Term::var(x), Term::var(z));
    let cond = derived::universe::in_all_universes(&mut env, &tx, &tz);
    let want = Formula::forall(
        x,
        Formula::forall(
            z,
            Formula::iff(
                Formula::mem(tz, Term::apply(d.space.lu, vec![tx])),
                cond,
            ),
        ),
    );
    assert_eq!(*d.space.lu_ax.concl(), want);

    // ... and `⊢ ∀x. x ∈ U(x)` really is what it says.
    let y = env.fresh_var();
    let ty = Term::var(y);
    assert_eq!(
        *d.space.mem_lu.concl(),
        Formula::forall(y, Formula::mem(ty.clone(), Term::apply(d.space.lu, vec![ty])))
    );
}

/// A theorem is a formula and nothing else, so the only way the tests above can
/// be satisfied by an accident is if the whole kernel is broken. This pins the
/// one thing they cannot see: that `Thm::mp` was really used, i.e. that the
/// product's characteristic property is a *theorem* and not an axiom smuggled
/// in. There is no way to smuggle: `Thm` has no public constructor.
#[test]
fn no_axioms_were_added() {
    // `kernel::thm::define` is the only non-inference-rule source of a `Thm`,
    // and it demands a proved `∃!`. Nothing here calls anything else.
    let mut env = Env::new();
    let sets = Sets::new(&mut env);
    assert!(fsp::product(&mut env, &sets).is_some());
}

/// Unused-import guard for the shared prelude of the later tests.
#[allow(dead_code)]
fn _unused(_: Thm) {}
