//! **`⊢ Aᵢ ∈ U₁` for a constructor summand of any depth** —
//! `derived/src/cumul/sigma_n.rs`, exercised at a genuine three-argument
//! dependent telescope, and pinned against the `k = 1` fast path it must not
//! regress.
//!
//! The `k = 3` declaration below is
//!
//! ```text
//! β₀        = U₀ = {0,1}          two elements
//! β₁(y₀)    = 𝒫y₀                 𝒫0 = 1 = {0} and 𝒫1 = U₀ = {0,1} — the fibre
//!                                 genuinely varies with y₀
//! β₂(y₀,y₁) = {y₁}                a third, different shape
//! ```
//!
//! so it is dependent at *both* levels and the three families are pairwise
//! different. Two things are checked rather than assumed, because a `k ≥ 2`
//! derivation that silently only worked at a *constant* fibre would pass a
//! test that omitted them:
//!
//! * `⊢ ¬(β₁(1) = β₁(0))` — the fibre really varies with `y₀`;
//! * **two provably distinct** elements of the telescope, one packed through
//!   `β₁(0)` and the other through `β₁(1)`, so both branches are used and the
//!   set placed in `U₁` is not a point.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::anchor::falsity;
use derived::cumul::{
    arg_obligations, summand_in_u1, summand_obligation, summand_obligations,
    unary_summand_in_u1, IndChain,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine};
use derived::sigma::Telescope;
use derived::{
    a1i, and_intro, and_left, and_right, eq_symm, ex_falso, gen_all, hyp_and, hyp_mp, imp_refl,
    iff_mpr, inst_all, singleton, syl,
};

/// Everything a test needs, over one signature.
struct Fix {
    ic: IndChain,
    mach: Machine,
}

impl Fix {
    fn new(env: &mut Env) -> Fix {
        let (ic, mach) = IndChain::new(env).expect("the chain and the apparatus");
        Fix { ic, mach }
    }

    fn u1(&self) -> Term { self.ic.chain.u1.set.clone() }
}

/// `⊢ b ∈ U₁ → a ∈ U₁` for a defining equation `⊢ a = b` — the step that turns
/// a fact about the *definition* into the fact about the *symbol application*
/// the telescope is stated at.
fn back_along(env: &mut Env, u1: &Term, def_eq: &Thm) -> Thm {
    let (lhs, rhs) = def_eq.concl().as_eq().expect("a defining equation");
    let hole = env.fresh_var();
    Thm::mp(
        &Thm::eq_leibniz(rhs, lhs, hole, Formula::mem(Term::var(hole), u1.clone())),
        &eq_symm(env, def_eq).expect("symm"),
    )
    .expect("leibniz")
}

/// `⊢ a ∈ U₁` from `⊢ b ∈ U₁` and `⊢ a = b`.
fn along(env: &mut Env, u1: &Term, def_eq: &Thm, rhs_in: &Thm) -> Thm {
    Thm::mp(&back_along(env, u1, def_eq), rhs_in).expect("mp")
}

/// `⊢ H → a ∈ U₁` from `⊢ H → b ∈ U₁` and `⊢ a = b`.
fn along_hyp(env: &mut Env, u1: &Term, def_eq: &Thm, rhs_in: &Thm) -> Thm {
    syl(rhs_in, &back_along(env, u1, def_eq)).expect("syl")
}

/// `⊢ t ∈ β(args)` from `⊢ t ∈ <definition>` and `⊢ β(args) = <definition>`.
fn into_sym(env: &mut Env, def_eq: &Thm, t: &Term, mem: &Thm) -> Thm {
    let (lhs, rhs) = def_eq.concl().as_eq().expect("a defining equation");
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(rhs, lhs, hole, Formula::mem(t.clone(), Term::var(hole)));
    Thm::mp(
        &Thm::mp(&carry, &eq_symm(env, def_eq).expect("symm")).expect("leibniz"),
        mem,
    )
    .expect("mp")
}


/// The `k = 3` declaration: `β₀ = U₀`, `β₁(y₀) = 𝒫y₀`, `β₂(y₀,y₁) = {y₁}`.
fn triple(env: &mut Env, f: &Fix) -> (FnSym, Thm, FnSym, Thm, FnSym, Thm) {
    let s = &f.mach.wt.sums;
    let up = s.ap.sets.up;
    let pow = f.ic.chain.space.pow;

    let (b0, b0_ax) =
        derived::define_abbrev(env, &[], &falsity::truth_values(s)).expect("β₀ = U₀");
    let y0 = env.fresh_var();
    let (b1, b1_ax) =
        derived::define_abbrev(env, &[y0], &Term::apply(pow, vec![Term::var(y0)]))
            .expect("β₁(y₀) = 𝒫y₀");
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (b2, b2_ax) =
        derived::define_abbrev(env, &[a, b], &singleton(up, Term::var(b))).expect("β₂ = {y₁}");
    (b0, b0_ax, b1, b1_ax, b2, b2_ax)
}

/// **The deliverable.** A three-argument, genuinely dependent constructor
/// summand lands in `U₁`, with the two Replacement instances the induction
/// spends actually spent.
#[test]
fn a_three_argument_dependent_telescope_lands_in_u1() {
    let mut env = Env::new();
    let mut f = Fix::new(&mut env);
    let (b0, b0_ax, b1, b1_ax, b2, b2_ax) = triple(&mut env, &f);
    assert!(b0 != b1 && b1 != b2 && b0 != b2, "three different argument families");

    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0, b1, b2], 0)]);
    let ind = Inductive::build(&mut env, &mut f.mach, &spec).expect("the translation");
    let u1 = f.u1();
    let s = f.mach.wt.sums.clone();
    let up = s.ap.sets.up;

    // The telescope really is three `Σ`s over four levels, and the innermost
    // one is the constant `1`.
    let tel: &Telescope = &ind.telescopes[0];
    assert_eq!(tel.betas.len(), 3);
    assert_eq!(tel.levels.len(), 4);
    assert_eq!(tel.sums.len(), 3);

    // ── The three obligations, built at the shapes `arg_obligations` gives ──
    let want = arg_obligations(&mut env, &f.ic, &f.mach, &ind, 0, None).expect("obligations");
    assert_eq!(want.len(), 3);

    // `⊢ β₀() ∈ U₁`.
    let p0 = along(&mut env, &u1, &b0_ax, &f.ic.chain.u1.u0_mem);

    // `⊢ ∀y₀. (y₀ ∈ β₀() → β₁(y₀) ∈ U₁)`.
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let p1 = {
        let in_b0 = Formula::mem(ty.clone(), Term::apply(b0, vec![]));
        let hole = env.fresh_var();
        let to_u0 = Thm::mp(
            &Thm::eq_leibniz(
                Term::apply(b0, vec![]),
                falsity::truth_values(&s),
                hole,
                Formula::mem(ty.clone(), Term::var(hole)),
            ),
            &b0_ax,
        )
        .expect("β₀() = U₀");
        let u0_sub = Thm::mp(
            &inst_all(&f.ic.chain.u1.transitive, &[falsity::truth_values(&s)]).expect("C₁"),
            &f.ic.chain.u1.u0_mem,
        )
        .expect("mp");
        let to_u1 = inst_all(&u0_sub, std::slice::from_ref(&ty)).expect("at y₀");
        let pow_at = inst_all(&f.ic.chain.u1.pow, std::slice::from_ref(&ty)).expect("𝒫");
        let chained = syl(&syl(&to_u0, &to_u1).expect("syl"), &pow_at).expect("syl");
        assert_eq!(chained.concl().as_imp().expect("imp").0, in_b0);
        let b1_at = inst_all(&b1_ax, std::slice::from_ref(&ty)).expect("β₁(y₀) = 𝒫y₀");
        Thm::gen(yv, &along_hyp(&mut env, &u1, &b1_at, &chained))
    };
    assert_eq!(*p1.concl(), want[1], "the second obligation, at our own variable");

    // `⊢ ∀y₀ ∀y₁. ((y₀ ∈ β₀() ∧ y₁ ∈ β₁(y₀)) → β₂(y₀,y₁) ∈ U₁)`.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let p2 = {
        let b1_at = Term::apply(b1, vec![ty.clone()]);
        let h = Formula::and(
            Formula::mem(ty.clone(), Term::apply(b0, vec![])),
            Formula::mem(tz.clone(), b1_at.clone()),
        );
        let h_left = and_left(
            Formula::mem(ty.clone(), Term::apply(b0, vec![])),
            Formula::mem(tz.clone(), b1_at.clone()),
        );
        let h_right = and_right(
            Formula::mem(ty.clone(), Term::apply(b0, vec![])),
            Formula::mem(tz.clone(), b1_at.clone()),
        );
        // `H → β₁(y₀) ∈ U₁`, from the second obligation.
        let b1_in = hyp_mp(
            &a1i(&inst_all(&p1, std::slice::from_ref(&ty)).expect("at y₀"), h.clone()),
            &h_left,
        )
        .expect("hyp_mp");
        // `H → y₁ ∈ U₁`, by `C₁`.
        let all_z = hyp_mp(
            &a1i(
                &inst_all(&f.ic.chain.u1.transitive, std::slice::from_ref(&b1_at))
                    .expect("C₁ at β₁(y₀)"),
                h.clone(),
            ),
            &b1_in,
        )
        .expect("hyp_mp");
        let z_in = hyp_mp(
            &syl(
                &all_z,
                &Thm::ax_inst(all_z.concl().as_imp().expect("imp").1, tz.clone()).expect("inst"),
            )
            .expect("syl"),
            &h_right,
        )
        .expect("hyp_mp");
        // `H → {y₁} ∈ U₁`.
        let sing_in = hyp_mp(
            &a1i(
                &inst_all(&f.ic.chain.u1.pairing, &[tz.clone(), tz.clone()]).expect("pairing"),
                h,
            ),
            &hyp_and(&z_in, &z_in).expect("and"),
        )
        .expect("hyp_mp");
        assert_eq!(
            sing_in.concl().as_imp().expect("imp").1,
            Formula::mem(singleton(up, tz.clone()), u1.clone())
        );
        let b2_at = inst_all(&b2_ax, &[ty.clone(), tz.clone()]).expect("β₂ = {y₁}");
        gen_all(&[yv, zv], &along_hyp(&mut env, &u1, &b2_at, &sing_in))
    };
    assert_eq!(*p2.concl(), want[2], "the third obligation, at our own variables");
    assert_eq!(*p0.concl(), want[0], "the first obligation");

    // ── The construction ────────────────────────────────────────────────────
    let out = summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &[p0, p1.clone(), p2])
        .expect("Σy₀:β₀. Σy₁:β₁. Σy₂:β₂. 1 ∈ U₁");
    assert!(out.hyps().is_empty(), "unconditional");
    assert_eq!(*out.concl(), Formula::mem(ind.summands[0].clone(), u1.clone()));
    let mut vs = Vec::new();
    out.concl().free_vars(&mut vs);
    assert!(vs.is_empty(), "and closed: the declaration has no parameters");

    // ── Non-vacuity: two provably distinct elements, through both fibres ────
    let zero = s.zero();
    let one = s.unit();
    let pow = f.ic.chain.space.pow;

    // `⊢ 0 ∈ β₀()` and `⊢ 1 ∈ β₀()`.
    let zero_in_b0 = into_sym(
        &mut env,
        &b0_ax,
        &zero,
        &falsity::false_in_prop(&s).expect("0 ∈ U₀"),
    );
    let one_in_b0 =
        into_sym(&mut env, &b0_ax, &one, &falsity::true_in_prop(&s).expect("1 ∈ U₀"));

    // `⊢ 0 ∈ 𝒫0` (from `0 ⊆ 0`) and `⊢ 0 ∈ 𝒫1` (from `0 ⊆ 1`).
    let sub_refl = {
        let v = env.fresh_var();
        let t = Thm::gen(v, &imp_refl(Formula::mem(Term::var(v), zero.clone())));
        assert_eq!(*t.concl(), kernel::thm::subset(&mut env, zero.clone(), zero.clone()));
        t
    };
    let sub_one = {
        let v = env.fresh_var();
        let not_in =
            inst_all(&s.ap.empty_ax, &[Term::var(v)]).expect("nothing is a member of ∅");
        let t = Thm::gen(
            v,
            &syl(&not_in, &ex_falso(Formula::mem(Term::var(v), one.clone()))).expect("syl"),
        );
        assert_eq!(*t.concl(), kernel::thm::subset(&mut env, zero.clone(), one.clone()));
        t
    };
    let in_pow = |env: &mut Env, x: &Term, sub: &Thm| -> Thm {
        let ax = inst_all(&f.ic.chain.space.pow_ax, &[x.clone(), zero.clone()]).expect("𝒫");
        let _ = env;
        Thm::mp(&iff_mpr(&ax).expect("mpr"), sub).expect("mp")
    };
    let zero_in_p0 = in_pow(&mut env, &zero, &sub_refl);
    let zero_in_p1 = in_pow(&mut env, &one, &sub_one);
    assert_eq!(
        *zero_in_p0.concl(),
        Formula::mem(zero.clone(), Term::apply(pow, vec![zero.clone()]))
    );
    assert_eq!(
        *zero_in_p1.concl(),
        Formula::mem(zero.clone(), Term::apply(pow, vec![one.clone()]))
    );
    let zero_in_b1_0 = into_sym(
        &mut env,
        &inst_all(&b1_ax, std::slice::from_ref(&zero)).expect("β₁(0)"),
        &zero,
        &zero_in_p0,
    );
    let zero_in_b1_1 = into_sym(
        &mut env,
        &inst_all(&b1_ax, std::slice::from_ref(&one)).expect("β₁(1)"),
        &zero,
        &zero_in_p1,
    );

    // `⊢ 0 ∈ {0}`, hence `⊢ 0 ∈ β₂(y₀,0)` at either `y₀`.
    let zero_in_sing = Thm::mp(
        &iff_mpr(&inst_all(&s.ap.mem_sing, &[zero.clone(), zero.clone()]).expect("{0}"))
            .expect("mpr"),
        &Thm::eq_refl(zero.clone()),
    )
    .expect("mp");
    let in_b2 = |env: &mut Env, y: &Term| -> Thm {
        into_sym(
            env,
            &inst_all(&b2_ax, &[y.clone(), zero.clone()]).expect("β₂"),
            &zero,
            &zero_in_sing,
        )
    };

    // Pack both tuples with `Telescope::intro`.
    let tel: &Telescope = &ind.telescopes[0];
    let pack = |env: &mut Env, y: &Term, h0: &Thm, h1: &Thm| -> Thm {
        let rule = inst_all(&tel.intro, &[y.clone(), zero.clone(), zero.clone()])
            .expect("the introduction rule");
        let h2 = in_b2(env, y);
        Thm::mp(&rule, &and_intro(h0, &and_intro(h1, &h2))).expect("mp")
    };
    let tuple_a = pack(&mut env, &zero, &zero_in_b0, &zero_in_b1_0);
    let tuple_b = pack(&mut env, &one, &one_in_b0, &zero_in_b1_1);

    let t_of = |y: &Term| {
        Telescope::tuple_of(&s, &[y.clone(), zero.clone(), zero.clone()])
    };
    assert_eq!(
        *tuple_a.concl(),
        Formula::mem(t_of(&zero), ind.summands[0].clone()),
        "⟨0,⟨0,⟨0,•⟩⟩⟩ is in the summand, through the fibre 𝒫0 = 1"
    );
    assert_eq!(
        *tuple_b.concl(),
        Formula::mem(t_of(&one), ind.summands[0].clone()),
        "⟨1,⟨0,⟨0,•⟩⟩⟩ is in it too, through the *other* fibre 𝒫1 = U₀"
    );

    // ── The fibre really does vary: `⊢ ¬(β₁(1) = β₁(0))` ────────────────────
    //
    // This is the assertion a `k ≥ 2` derivation that silently only worked at a
    // *constant* fibre would fail to be tested against. `1 ∈ 𝒫1` because
    // `1 ⊆ 1`; `1 ∉ 𝒫0` because `1 ⊄ 0` — `0 ∈ 1` but `0 ∉ 0`.
    let p_of = |t: &Term| Term::apply(pow, vec![t.clone()]);
    let one_in_p1 = {
        let v = env.fresh_var();
        let refl = Thm::gen(v, &imp_refl(Formula::mem(Term::var(v), one.clone())));
        assert_eq!(*refl.concl(), kernel::thm::subset(&mut env, one.clone(), one.clone()));
        Thm::mp(
            &iff_mpr(&inst_all(&f.ic.chain.space.pow_ax, &[one.clone(), one.clone()]).expect("𝒫"))
                .expect("mpr"),
            &refl,
        )
        .expect("mp")
    };
    let one_not_in_p0 = {
        let fwd = derived::iff_mp(
            &inst_all(&f.ic.chain.space.pow_ax, &[zero.clone(), one.clone()]).expect("𝒫"),
        )
        .expect("mp");
        let at_zero = Thm::ax_inst(
            kernel::thm::subset(&mut env, one.clone(), zero.clone()),
            zero.clone(),
        )
        .expect("inst");
        let zero_in_one = Thm::mp(
            &iff_mpr(&inst_all(&s.ap.mem_sing, &[zero.clone(), zero.clone()]).expect("{0} = 1"))
                .expect("mpr"),
            &Thm::eq_refl(zero.clone()),
        )
        .expect("0 ∈ 1");
        let to_absurd = derived::mpd_const(
            &syl(&fwd, &at_zero).expect("syl"),
            &zero_in_one,
        )
        .expect("mpd");
        syl(&to_absurd, &inst_all(&s.ap.empty_ax, std::slice::from_ref(&zero)).expect("0 ∉ 0"))
            .expect("syl")
    };
    let fibres_differ = {
        let hole = env.fresh_var();
        let step = derived::mpd_const(
            &Thm::eq_leibniz(
                p_of(&one),
                p_of(&zero),
                hole,
                Formula::mem(one.clone(), Term::var(hole)),
            ),
            &one_in_p1,
        )
        .expect("mpd");
        syl(&step, &one_not_in_p0).expect("¬(𝒫1 = 𝒫0)")
    };
    assert_eq!(
        *fibres_differ.concl(),
        Formula::not(Formula::eq(p_of(&one), p_of(&zero))),
        "the two fibres of β₁ are provably different sets"
    );
    let at_b1 = {
        let (e1, e0) = (
            inst_all(&b1_ax, std::slice::from_ref(&one)).expect("β₁(1) = 𝒫1"),
            inst_all(&b1_ax, std::slice::from_ref(&zero)).expect("β₁(0) = 𝒫0"),
        );
        let (b1_1, b1_0) = (Term::apply(b1, vec![one.clone()]), Term::apply(b1, vec![zero.clone()]));
        let h1 = env.fresh_var();
        let move_l = derived::mpd_const(
            &Thm::eq_leibniz(
                b1_1.clone(),
                b1_0.clone(),
                h1,
                Formula::eq(p_of(&one), Term::var(h1)),
            ),
            &eq_symm(&mut env, &e1).expect("symm"),
        )
        .expect("mpd");
        let h2 = env.fresh_var();
        let move_r = Thm::mp(
            &Thm::eq_leibniz(b1_0, p_of(&zero), h2, Formula::eq(p_of(&one), Term::var(h2))),
            &e0,
        )
        .expect("leibniz");
        syl(&syl(&move_l, &move_r).expect("syl"), &fibres_differ).expect("syl")
    };
    assert_eq!(
        *at_b1.concl(),
        Formula::not(Formula::eq(
            Term::apply(b1, vec![one.clone()]),
            Term::apply(b1, vec![zero.clone()])
        )),
        "so the telescope's second level is genuinely dependent on its first"
    );

    // And the two elements are provably different, so the set placed in `U₁`
    // is not a point: one ordered-pair injectivity and `⊢ ¬(0 = 1)`.
    let tail = Telescope::tuple_of(&s, &[zero.clone(), zero.clone()]);
    let inj = inst_all(&s.ap.pair_inj, &[zero.clone(), tail.clone(), one.clone(), tail])
        .expect("pair injectivity");
    let ne = syl(
        &syl(
            &inj,
            &and_left(
                Formula::eq(zero.clone(), one.clone()),
                Formula::eq(
                    Telescope::tuple_of(&s, &[zero.clone(), zero.clone()]),
                    Telescope::tuple_of(&s, &[zero.clone(), zero.clone()]),
                ),
            ),
        )
        .expect("syl"),
        &falsity::prop_two_valued(&s).expect("¬(0 = 1)"),
    )
    .expect("syl");
    assert_eq!(
        *ne.concl(),
        Formula::not(Formula::eq(t_of(&zero), t_of(&one))),
        "the two elements are provably distinct"
    );
}

/// The `k = 1` fast path is **not** regressed: the general construction agrees
/// with `unary_summand_in_u1` on the nose, at the same declaration and under
/// the same antecedent.
///
/// `List`'s shape, as `derived/tests/cumul_decl.rs` runs it: `β₀(α) = α`, and
/// the antecedent `α ∈ U₁` is genuinely needed.
#[test]
fn at_one_argument_the_general_route_agrees_with_the_fast_path() {
    let mut env = Env::new();
    let mut f = Fix::new(&mut env);
    let pv = env.fresh_var();
    let (id, id_ax) =
        derived::define_abbrev(&mut env, &[pv], &Term::var(pv)).expect("β₀(p) = p");
    let spec = DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::new(vec![id], 1)]);
    let ind = Inductive::build(&mut env, &mut f.mach, &spec).expect("List");

    let alpha = Term::var(ind.params[0]);
    let u1 = f.u1();
    let h = Formula::mem(alpha.clone(), u1.clone());
    let id_at = inst_all(&id_ax, std::slice::from_ref(&alpha)).expect("β₀(α) = α");
    let arg = along_hyp(&mut env, &u1, &id_at, &imp_refl(h.clone()));

    let want = arg_obligations(&mut env, &f.ic, &f.mach, &ind, 1, Some(&h)).expect("obligations");
    assert_eq!(want.len(), 1, "one argument, one obligation");
    assert_eq!(*arg.concl(), want[0], "and it is exactly the fast path's input");

    let fast = unary_summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 1, Some(&h), &arg)
        .expect("the k = 1 route");
    let general = summand_in_u1(
        &mut env,
        &f.ic,
        &f.mach,
        &ind,
        1,
        Some(&h),
        std::slice::from_ref(&arg),
    )
    .expect("the general route");

    assert_eq!(fast.concl(), general.concl(), "the same theorem, both ways");
    assert_eq!(
        *general.concl(),
        Formula::imp(h, Formula::mem(ind.summands[1].clone(), u1)),
        "⊢ α ∈ U₁ → A₁ ∈ U₁"
    );
    assert!(general.hyps().is_empty());
}

/// At `k = 2` the second Replacement premise is a real one, and the guard chain
/// is what carries it: the second argument's obligation is stated **under**
/// `y₀ ∈ β₀`, not outright.
#[test]
fn at_two_arguments_the_second_obligation_is_guarded() {
    let mut env = Env::new();
    let mut f = Fix::new(&mut env);
    let (b0, b0_ax, b1, b1_ax, _, _) = triple(&mut env, &f);
    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0, b1], 0)]);
    let ind = Inductive::build(&mut env, &mut f.mach, &spec).expect("the translation");
    let u1 = f.u1();
    let s = f.mach.wt.sums.clone();

    let want = arg_obligations(&mut env, &f.ic, &f.mach, &ind, 0, None).expect("obligations");
    assert_eq!(want.len(), 2);
    assert!(
        want[1].as_imp().is_none(),
        "the second obligation is a `∀y₀. …`, not a bare implication"
    );

    let p0 = along(&mut env, &u1, &b0_ax, &f.ic.chain.u1.u0_mem);
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let hole = env.fresh_var();
    let to_u0 = Thm::mp(
        &Thm::eq_leibniz(
            Term::apply(b0, vec![]),
            falsity::truth_values(&s),
            hole,
            Formula::mem(ty.clone(), Term::var(hole)),
        ),
        &b0_ax,
    )
    .expect("β₀() = U₀");
    let u0_sub = Thm::mp(
        &inst_all(&f.ic.chain.u1.transitive, &[falsity::truth_values(&s)]).expect("C₁"),
        &f.ic.chain.u1.u0_mem,
    )
    .expect("mp");
    let chained = syl(
        &syl(&to_u0, &inst_all(&u0_sub, std::slice::from_ref(&ty)).expect("at y₀")).expect("syl"),
        &inst_all(&f.ic.chain.u1.pow, std::slice::from_ref(&ty)).expect("𝒫"),
    )
    .expect("syl");
    let b1_at = inst_all(&b1_ax, std::slice::from_ref(&ty)).expect("β₁(y₀) = 𝒫y₀");
    let p1 = Thm::gen(yv, &along_hyp(&mut env, &u1, &b1_at, &chained));
    assert_eq!(*p1.concl(), want[1]);

    let out = summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &[p0.clone(), p1.clone()])
        .expect("Σy₀:U₀. Σy₁:𝒫y₀. 1 ∈ U₁");
    assert_eq!(*out.concl(), Formula::mem(ind.summands[0].clone(), u1.clone()));

    // A theorem with the right shape but a non-empty hypothesis set is refused.
    let assumed = Thm::assume(want[1].clone());
    assert!(
        summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &[p0.clone(), assumed]).is_none(),
        "a caller-supplied theorem with a Γ is refused"
    );
    // So is one with the wrong conclusion.
    assert!(
        summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &[p1.clone(), p0.clone()])
            .is_none(),
        "the obligations are not interchangeable"
    );
    assert!(
        summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &[p0]).is_none(),
        "the wrong number of obligations is refused"
    );
}

/// At `k = 0` the induction has no steps and the answer is `⊢ 1 ∈ U₁` moved
/// onto the summand — the same set `cumul::nullary_summand_in_u1` produces.
#[test]
fn at_zero_arguments_the_induction_is_empty() {
    let mut env = Env::new();
    let mut f = Fix::new(&mut env);
    let spec = DeclSpec::new(0, vec![CtorSpec::nullary()]);
    let ind = Inductive::build(&mut env, &mut f.mach, &spec).expect("the translation");

    let want = arg_obligations(&mut env, &f.ic, &f.mach, &ind, 0, None).expect("obligations");
    assert!(want.is_empty(), "nothing to supply");

    let out = summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &[]).expect("A₀ = 1 ∈ U₁");
    let fast = derived::cumul::nullary_summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0)
        .expect("the nullary route");
    assert_eq!(out.concl(), fast.concl(), "the same theorem, both ways");
}

// ─────────────────────────────────────────────────────────────────────────────
// The interleaved-to-prenex bridge — `derived/src/cumul/interleaved.rs`.
//
// A consumer that opens and closes one binder at a time produces
// `⊢ [H →] ∀y₀. (H₀ → ∀y₁. (H₁ → …))`; `arg_obligations` states
// `⊢ ∀y⃗. (Dⱼ → …)` with `Dⱼ` **left-nested**. These tests pin the conversion,
// and pin the nesting at four conjuncts — two cannot tell left from right.
// ─────────────────────────────────────────────────────────────────────────────

/// `∀x₀ … ∀x_{n-1}. φ`, as a formula — the test's own copy of what
/// `arg_obligations` quantifies with.
fn quantify(xs: &[kernel::FreeVar], phi: Formula) -> Formula {
    xs.iter().rev().fold(phi, |acc, x| Formula::forall(*x, acc))
}

/// From `⊢ D → φ` infer `⊢ D → ∀v. φ`, for `v` not free in `D`.
fn hyp_gen(v: kernel::FreeVar, t: &Thm) -> Thm {
    let (h, phi) = t.concl().as_imp().expect("an implication");
    Thm::mp(&Thm::ax_dist(v, h, phi).expect("dist"), &Thm::gen(v, t)).expect("mp")
}

/// **The nesting.** A depth-three guard chain under an outer antecedent — so
/// `D₃` has **four** conjuncts — is prenexed to the *left*-nested
/// `(((H ∧ G₀) ∧ G₁) ∧ G₂)`, and to none of the three other groupings or the
/// one reordering that two conjuncts could not have distinguished.
///
/// The three guards are pairwise different and genuinely dependent — `G₁`
/// mentions `v₀` and `G₂` mentions `v₁` — so the peel really has to instantiate
/// under each binder rather than strip the quantifiers and hope.
#[test]
fn the_bridge_left_nests_a_four_conjunct_antecedent() {
    let mut env = Env::new();
    let f = Fix::new(&mut env);
    let s = f.mach.wt.sums.clone();
    let (up, pow) = (s.ap.sets.up, f.ic.chain.space.pow);

    let pv = env.fresh_var();
    let h = Formula::mem(Term::var(pv), f.u1());
    let (v0, v1, v2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (t0, t1, t2) = (Term::var(v0), Term::var(v1), Term::var(v2));
    let g0 = Formula::mem(t0.clone(), falsity::truth_values(&s));
    let g1 = Formula::mem(t1.clone(), Term::apply(pow, vec![t0.clone()]));
    let g2 = Formula::mem(t2.clone(), singleton(up, t1.clone()));
    assert!(g0 != g1 && g1 != g2 && g0 != g2, "three different guards");

    // `⊢ H → ∀v₀. (G₀ → ∀v₁. (G₁ → ∀v₂. (G₂ → G₂)))` — the interleaved shape,
    // built by weakening so that only its *shape* is under test.
    let given = a1i(
        &Thm::gen(
            v0,
            &a1i(
                &Thm::gen(v1, &a1i(&Thm::gen(v2, &imp_refl(g2.clone())), g1.clone())),
                g0.clone(),
            ),
        ),
        h.clone(),
    );

    let out = summand_obligation(&mut env, &given, Some(&h), 3).expect("the bridge");
    assert!(out.hyps().is_empty(), "the bridge introduces no hypothesis");

    let left_nested = Formula::and(
        Formula::and(Formula::and(h.clone(), g0.clone()), g1.clone()),
        g2.clone(),
    );
    assert_eq!(
        *out.concl(),
        quantify(&[v0, v1, v2], Formula::imp(left_nested.clone(), g2.clone())),
        "∀v₀∀v₁∀v₂. ((((H ∧ G₀) ∧ G₁) ∧ G₂) → G₂)"
    );

    // The three groupings and the one reordering that are *not* the answer.
    for (label, other) in [
        (
            "right-nested",
            Formula::and(h.clone(), Formula::and(g0.clone(), Formula::and(g1.clone(), g2.clone()))),
        ),
        (
            "balanced",
            Formula::and(Formula::and(h.clone(), g0.clone()), Formula::and(g1.clone(), g2.clone())),
        ),
        (
            "H innermost",
            Formula::and(Formula::and(Formula::and(g0.clone(), g1.clone()), g2.clone()), h.clone()),
        ),
        (
            "guards swapped",
            Formula::and(
                Formula::and(Formula::and(h.clone(), g1.clone()), g0.clone()),
                g2.clone(),
            ),
        ),
    ] {
        assert_ne!(other, left_nested, "{label} is a different formula from the answer");
        assert_ne!(
            *out.concl(),
            quantify(&[v0, v1, v2], Formula::imp(other, g2.clone())),
            "the bridge does not produce the {label} antecedent"
        );
    }

    // Depth 0 is the identity, and one layer too many is refused rather than
    // guessed at.
    let id = summand_obligation(&mut env, &given, Some(&h), 0).expect("depth 0");
    assert_eq!(id.concl(), given.concl());
    assert!(
        summand_obligation(&mut env, &given, Some(&h), 4).is_none(),
        "there is no fourth ∀/→ layer"
    );
    // A `Γ ⊢` with the right conclusion is refused: the output is labelled `⊢`.
    let assumed = Thm::assume(given.concl().clone());
    assert!(summand_obligation(&mut env, &assumed, Some(&h), 3).is_none());
    // And the outer antecedent is not optional, nor is it taken on trust:
    // without it the first peel finds an implication where it wanted a `∀`, and
    // with the wrong one the accumulated `Dⱼ` would not be the theorem's own.
    assert!(summand_obligation(&mut env, &given, None, 3).is_none());
    let wrong = Formula::mem(Term::var(pv), falsity::truth_values(&s));
    assert_ne!(wrong, h);
    assert!(summand_obligation(&mut env, &given, Some(&wrong), 3).is_none());
}

/// **The deliverable.** The three interleaved obligations of the `k = 3`
/// dependent telescope are bridged and fed straight to `summand_in_u1`, which
/// returns the theorem the prenex route returns — the same set, in `U₁`.
///
/// The `j = 2` leg is the one with content: at depth 0 and 1 the two shapes
/// coincide, and at depth 2 they differ. Both packagings come from one
/// `⊢ (G₀ ∧ G₁) → β₂(y₀,y₁) ∈ U₁`, by two independent pieces of bookkeeping.
#[test]
fn the_bridge_feeds_the_three_argument_telescope() {
    let mut env = Env::new();
    let mut f = Fix::new(&mut env);
    let (b0, b0_ax, b1, b1_ax, b2, b2_ax) = triple(&mut env, &f);

    let spec = DeclSpec::new(0, vec![CtorSpec::new(vec![b0, b1, b2], 0)]);
    let ind = Inductive::build(&mut env, &mut f.mach, &spec).expect("the translation");
    let u1 = f.u1();
    let s = f.mach.wt.sums.clone();
    let up = s.ap.sets.up;
    let want = arg_obligations(&mut env, &f.ic, &f.mach, &ind, 0, None).expect("obligations");
    assert_eq!(want.len(), 3);

    // ── `j = 0` and `j = 1`: the two shapes coincide ───────────────────────
    let i0 = along(&mut env, &u1, &b0_ax, &f.ic.chain.u1.u0_mem);
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let i1 = {
        let hole = env.fresh_var();
        let to_u0 = Thm::mp(
            &Thm::eq_leibniz(
                Term::apply(b0, vec![]),
                falsity::truth_values(&s),
                hole,
                Formula::mem(ty.clone(), Term::var(hole)),
            ),
            &b0_ax,
        )
        .expect("β₀() = U₀");
        let u0_sub = Thm::mp(
            &inst_all(&f.ic.chain.u1.transitive, &[falsity::truth_values(&s)]).expect("C₁"),
            &f.ic.chain.u1.u0_mem,
        )
        .expect("mp");
        let chained = syl(
            &syl(&to_u0, &inst_all(&u0_sub, std::slice::from_ref(&ty)).expect("at y₀"))
                .expect("syl"),
            &inst_all(&f.ic.chain.u1.pow, std::slice::from_ref(&ty)).expect("𝒫"),
        )
        .expect("syl");
        let b1_at = inst_all(&b1_ax, std::slice::from_ref(&ty)).expect("β₁(y₀) = 𝒫y₀");
        Thm::gen(yv, &along_hyp(&mut env, &u1, &b1_at, &chained))
    };
    assert_eq!(*i1.concl(), want[1], "at depth 1 interleaved and prenex agree");

    // ── `j = 2`: one fact, two packagings ──────────────────────────────────
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let core = {
        let b1_at = Term::apply(b1, vec![ty.clone()]);
        let (l, r) = (
            Formula::mem(ty.clone(), Term::apply(b0, vec![])),
            Formula::mem(tz.clone(), b1_at.clone()),
        );
        let conj = Formula::and(l.clone(), r.clone());
        // `G₀ ∧ G₁ → β₁(y₀) ∈ U₁`, then `C₁` at it, then the pairing.
        let b1_in = hyp_mp(
            &a1i(&inst_all(&i1, std::slice::from_ref(&ty)).expect("at y₀"), conj.clone()),
            &and_left(l.clone(), r.clone()),
        )
        .expect("hyp_mp");
        let all_z = hyp_mp(
            &a1i(
                &inst_all(&f.ic.chain.u1.transitive, std::slice::from_ref(&b1_at)).expect("C₁"),
                conj.clone(),
            ),
            &b1_in,
        )
        .expect("hyp_mp");
        let z_in = hyp_mp(
            &syl(
                &all_z,
                &Thm::ax_inst(all_z.concl().as_imp().expect("imp").1, tz.clone()).expect("inst"),
            )
            .expect("syl"),
            &and_right(l, r),
        )
        .expect("hyp_mp");
        let sing_in = hyp_mp(
            &a1i(
                &inst_all(&f.ic.chain.u1.pairing, &[tz.clone(), tz.clone()]).expect("pairing"),
                conj,
            ),
            &hyp_and(&z_in, &z_in).expect("and"),
        )
        .expect("hyp_mp");
        assert_eq!(
            sing_in.concl().as_imp().expect("imp").1,
            Formula::mem(singleton(up, tz.clone()), u1.clone())
        );
        let b2_at = inst_all(&b2_ax, &[ty.clone(), tz.clone()]).expect("β₂ = {y₁}");
        along_hyp(&mut env, &u1, &b2_at, &sing_in)
    };
    let p2 = gen_all(&[yv, zv], &core);
    assert_eq!(*p2.concl(), want[2], "the prenex packaging is the obligation");
    let i2 = Thm::gen(yv, &hyp_gen(zv, &derived::uncurry(&core).expect("uncurry")));
    assert_ne!(i2.concl(), p2.concl(), "and the interleaved packaging is a different formula");

    // ── The bridge, and the induction on top of it ─────────────────────────
    let bridged =
        summand_obligations(&mut env, &f.ic, &f.mach, &ind, 0, None, &[i0.clone(), i1.clone(), i2])
            .expect("the three obligations, prenexed");
    for (j, t) in bridged.iter().enumerate() {
        assert!(derived::establishes(t, &want[j]), "leg {j} is the obligation on the nose");
    }
    let out = summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &bridged)
        .expect("Σy₀:β₀. Σy₁:β₁. Σy₂:β₂. 1 ∈ U₁");
    let direct = summand_in_u1(&mut env, &f.ic, &f.mach, &ind, 0, None, &[i0.clone(), i1, p2])
        .expect("the prenex route");
    assert_eq!(out.concl(), direct.concl(), "the same theorem, both ways");
    assert_eq!(*out.concl(), Formula::mem(ind.summands[0].clone(), u1));
    assert!(out.hyps().is_empty());

    // The bundle refuses a leg that is the wrong obligation, rather than
    // converting it into a well-shaped statement about another family.
    assert!(
        summand_obligations(&mut env, &f.ic, &f.mach, &ind, 0, None, &[i0.clone(), i0.clone(), i0])
            .is_none(),
        "an obligation at the wrong depth is refused"
    );
}
