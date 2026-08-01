//! **Class (S)'s recursor, fired closed.**
//!
//! [`LeRecursor`] states four rules; three of them would be true and empty if
//! the edge relation `R` never contained an edge, if `acc(A_φ,R)` were empty, or
//! if `minor_eq` were unsatisfiable. This file rules all three out at once, by
//! building an actual step `e` and an actual minor `m`, discharging `ST` and
//! `minor_eq` from them, firing `minor_iota` with nothing on the left, and then
//! showing the recursor's two values **differ**:
//!
//! ```text
//! ⊢ ¬(app(F, tup(e⃗₁)) = app(F, tup(e⃗₀)))
//! ```
//!
//! ## Why the witness has two constructors
//!
//! Lean's large-elimination rule admits only **one** constructor, and the module
//! under test is general in `n` only because [`LeCarrier`] is. But a
//! one-constructor witness cannot exhibit a *recursion* over a finite index set.
//! With one constructor `A_φ` is exactly the image of `e⃗`, and `R` is exactly
//! `{⟨tup(d⃗(y⃗)), tup(e⃗(y⃗))⟩}`; for `minor_iota` to fire the child index must be
//! in `A_φ` — so in the image of `e⃗` — while some *other* result index must have
//! its child **outside** the image, or nothing is accessible at all. Over an
//! index type with two points and no fields those two demands are contradictory.
//!
//! (Over `N` they are not: `mk : ∀n. P n → P (n+1)` is exactly the shape a
//! recursive class-(S) declaration takes, with `A_φ = {succ n}` and `0 ∉ A_φ`
//! providing the escape. It needs Peano's `0 ≠ succ n`, which is a lot of
//! apparatus to drag in for a non-vacuity check.) So the witness splits the two
//! roles across a base constructor and a step constructor, which is the same
//! recursion with the escape made explicit.
//!
//! ## The declaration
//!
//! ```text
//! ι₀ := finord(2) = {ff, tt}          np = 0,  ni = 1
//! base :                P ff
//! step : P ff        →  P tt
//! ```
//!
//! so `A_φ = {tup(ff), tup(tt)}` and `R = {⟨tup(ff), tup(tt)⟩}`. `tup(ff)` is
//! accessible because nothing points at it; `tup(tt)` because its one
//! predecessor is. The step constructor's child index is the **same symbol**
//! the base constructor produces, which is what puts the child inside `A_φ`.
//!
//! ## The step, the minor, and the diagonal
//!
//! With `T := 𝒫(1)` the typing side condition is free — every value is a
//! Separation on `1`, hence a subset of `1`:
//!
//! ```text
//! M(v)  := { z ∈ 1 : ¬(• ∈ v) }              a symbol, one Separation
//! H(c)  := M(app(app(c, tup(ff)), •))        the step's body, read off the ih
//! e     := { ⟨q, cval(1, {⟨c, H(c)⟩ : c ∈ ih_bound(A_φ,T)})⟩ : q ∈ A_φ }
//! m     := cval(1, { ⟨v, M(v)⟩ : v ∈ T })    the minor for `step`
//! ```
//!
//! `e` is **uniform in `q`** — it does not read the index tuple at all — which
//! is why only the `step` constructor's `minor_eq` is discharged here and the
//! `base` constructor's is not: the base clause would need the step to be
//! constant in `c`, and this one is not. That is enough, and it is the right
//! half: it is the *recursive* clause whose firing is in doubt.
//!
//! Rather than compute either value, the last test runs Cantor's diagonal on the
//! ι equation alone: if the two values were equal, calling the common value `u`
//! gives `u = M(u)`, hence `• ∈ u ↔ ¬(• ∈ u)`. So the recursor is **not**
//! constant, and the value at the step constructor genuinely depends on the
//! value at the base one.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::acc::Acc;
use derived::bound::Bound;
use derived::funcs::{beta_conditional, lambda, separation_full};
use derived::inductive::family::{
    minor_app, slot_at, CtorIndices, IndexSpace, IndexedDeclSpec, LeCarrier, LeRecursor,
};
use derived::inductive::{CtorSpec, DeclSpec, Machine};
use derived::rec_acc::{cval_of, ih_bound, Base, Bounded, RecAcc};
use derived::sums::Sums;
use derived::wtype::Wtype;
use derived::{
    a1i, and_intro, and_left, and_right, clavius, conj_of, conj_proj, gen_all, hyp_and, hyp_mp,
    iff_mp, iff_mpr, imp_mono_r, imp_refl, inst_all, syl, syl_imp, uncurry,
};

// ── combinators the test needs and the crate keeps private ──────────────────

fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

fn abbrev(env: &mut Env, arity: usize, body: impl Fn(&[Term]) -> Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = body(&args);
    derived::define_abbrev(env, &vars, &t).expect("an abbreviation")
}

/// From `⊢ x = y` and `⊢ φ(x)` infer `⊢ φ(y)`.
fn rw(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), base).expect("mp")
}

/// From `⊢ y = x` and `⊢ φ(x)` infer `⊢ φ(y)`.
fn rw_back(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let back = derived::eq_symm(env, eq).expect("symm");
    rw(env, &back, ctx, base)
}

/// From `⊢ x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
fn rw_h(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    syl(base, &Thm::mp(&leib, eq).expect("mp")).expect("syl")
}

/// From `⊢ H → x = y` infer `⊢ H → y = x`.
fn h_symm(env: &mut Env, h: &Thm) -> Thm {
    let (_, eq) = h.concl().as_imp().expect("imp");
    let (x, y) = eq.as_eq().expect("eq");
    syl(h, &derived::eq_symm_imp(env, x, y)).expect("syl")
}

/// From `⊢ H → x = y` and `⊢ H → y = z` infer `⊢ H → x = z`.
fn h_trans(env: &mut Env, xy: &Thm, yz: &Thm) -> Thm {
    let (k, e1) = xy.concl().as_imp().expect("imp");
    let (_, e2) = yz.concl().as_imp().expect("imp");
    let (x, y) = e1.as_eq().expect("eq");
    let (_, z) = e2.as_eq().expect("eq");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(y, z, hole, Formula::eq(x, Term::var(hole)));
    hyp_mp(&hyp_mp(&a1i(&leib, k), yz).expect("mp"), xy).expect("mp")
}

/// From `⊢ H → x = y` infer `⊢ H → ctx(x) = ctx(y)`, for a term context.
fn h_congr(env: &mut Env, h: &Thm, ctx: impl Fn(Term) -> Term) -> Thm {
    let (k, eq) = h.concl().as_imp().expect("imp");
    let (x, y) = eq.as_eq().expect("eq");
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let phi = Formula::eq(lhs.clone(), ctx(Term::var(hole)));
    let leib = Thm::eq_leibniz(x, y, hole, phi);
    hyp_mp(&hyp_mp(&a1i(&leib, k.clone()), h).expect("mp"), &a1i(&Thm::eq_refl(lhs), k))
        .expect("mp")
}

/// From `⊢ H → x = y` infer `⊢ H → (φ(x) → φ(y))`.
fn h_leib(env: &mut Env, h: &Thm, ctx: impl Fn(Term) -> Formula) -> Thm {
    let (k, eq) = h.concl().as_imp().expect("imp");
    let (x, y) = eq.as_eq().expect("eq");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    hyp_mp(&a1i(&leib, k), h).expect("mp")
}

/// From `⊢ H → (A → B)` and `⊢ H → (B → C)` infer `⊢ H → (A → C)`.
fn chain(ab: &Thm, bc: &Thm) -> Thm {
    let (h, i1) = ab.concl().as_imp().expect("imp");
    let (a, b) = i1.as_imp().expect("imp");
    let (_, i2) = bc.concl().as_imp().expect("imp");
    let (_, c) = i2.as_imp().expect("imp");
    hyp_mp(&hyp_mp(&a1i(&syl_imp(a, b, c), h), ab).expect("mp"), bc).expect("mp")
}

/// From `⊢ H → φ` with `v` not free in `H`, infer `⊢ H → ∀v. φ`.
fn gen_under(v: FreeVar, h: &Thm) -> Thm {
    let (hyp, phi) = h.concl().as_imp().expect("imp");
    Thm::mp(&Thm::ax_dist(v, hyp, phi).expect("dist"), &Thm::gen(v, h)).expect("mp")
}

// ── the fixture ─────────────────────────────────────────────────────────────

struct Fix {
    mach: Machine,
    ac: Acc,
    ra: RecAcc,
    bd: Bounded,
    s: Sums,
    spec: IndexedDeclSpec,
    ix: IndexSpace,
    le: LeCarrier,
    lr: LeRecursor,
    ity_ax: Thm,
    res_ax: Vec<Thm>,
    pts: Vec<Term>,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let s = mach.wt.sums.clone();
    mach.syms.ensure(env, &s, 2).expect("two summands");
    let ac = Acc::with_apply(env, &s.ap).expect("acc over the same pairing");
    let base = Base::over(env, s.clone(), ac.clone()).expect("rec_acc's base");
    let ra = RecAcc::over(env, base).expect("the accessibility recursor");
    let bd = Bounded::build(env, &ra).expect("the bounding lemmas");

    let boolean = mach.syms.finord(&s, 2).expect("finord(2)");
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let tt = mach.syms.inj(1, s.point()).expect("Inj₁");
    let (i0, ity_ax) = abbrev(env, 0, |_| boolean.clone());
    let (e0, e0_ax) = abbrev(env, 0, |_| ff.clone());
    let (e1, e1_ax) = abbrev(env, 0, |_| tt.clone());

    let spec = IndexedDeclSpec::new(
        DeclSpec::new(0, vec![CtorSpec::new(Vec::new(), 0), CtorSpec::new(Vec::new(), 1)]),
        vec![i0],
        vec![
            CtorIndices::nonrecursive(vec![e0]),
            CtorIndices { result: vec![e1], rec_args: vec![vec![e0]] },
        ],
    );
    assert!(spec.well_formed());
    let ix = IndexSpace::build(env, &mut mach, &spec, &[]).expect("the index space");
    let le = LeCarrier::build(env, &mach, &ac, &spec, &ix, &[]).expect("the (S) carrier");
    assert!(le.degenerate.is_none(), "a recursive declaration has a non-empty R");
    let lr =
        LeRecursor::build(env, &mach, &ra, &bd, &spec, &ix, &le, &[]).expect("the (S) recursor");
    assert!(lr.all_unconditional());

    Fix { mach, ac, ra, bd, s, spec, ix, le, lr, ity_ax, res_ax: vec![e0_ax, e1_ax], pts: vec![ff, tt] }
}

impl Fix {
    /// `tup(e⃗ᵢ)`.
    fn res(&self, i: usize) -> Term {
        IndexedDeclSpec::tup(&self.s, &self.spec.result_vec(i, &[], &[]).expect("indices"))
    }

    /// The bare result index `eᵢ₀()`.
    fn ix_of(&self, i: usize) -> Term {
        self.spec.result_vec(i, &[], &[]).expect("indices")[0].clone()
    }

    /// `antᵢ`, which for a fieldless constructor is the one index typing.
    fn ant(&self, i: usize) -> Formula {
        Formula::mem(self.ix_of(i), Term::apply(self.spec.indices[0], Vec::new()))
    }

    /// `⊢ antᵢ`, with both symbols unfolded to `Injᵢ(•) ∈ finord(2)`.
    fn ant_thm(&self, env: &mut Env, i: usize) -> Thm {
        let s = &self.s;
        let base = Thm::mp(
            &inst_all(
                self.mach.syms.inj_mem(2, i).expect("inj_mem"),
                &[s.unit(), s.unit(), s.point()],
            )
            .expect("inst"),
            &s.unit_mem,
        )
        .expect("mp");
        let set = Term::apply(self.spec.indices[0], Vec::new());
        let pt = self.pts[i].clone();
        let at_set = rw_back(env, &self.ity_ax, |x| Formula::mem(pt.clone(), x), &base);
        rw_back(env, &self.res_ax[i], move |x| Formula::mem(x, set.clone()), &at_set)
    }
}

// ── the step and the minor ──────────────────────────────────────────────────

struct Step {
    /// `T = 𝒫(1)`.
    tgt: Term,
    /// `M`, with `⊢ ∀v ∀z. (z ∈ M(v) ↔ (z ∈ 1 ∧ ¬(• ∈ v)))`.
    m: FnSym,
    m_ax: Thm,
    /// The step set `e`.
    e: Term,
    /// The minor for the `step` constructor.
    minor: Term,
    /// `⊢ ∀x ∀c. ((x ∈ A_φ ∧ c ∈ ih_bound(A_φ,T)) → step(e,x,c) = M(slot(c)))`.
    step_value: Thm,
    /// `⊢ ∀v. (v ∈ T → app(app(minor, •), v) = M(v))`.
    minor_value: Thm,
    /// `tup(d⃗₁₀)`, the step constructor's child index.
    child: Term,
}

fn build_step(env: &mut Env, f: &Fix) -> Step {
    let s = f.s.clone();
    let ap = s.ap.clone();
    let (unit, point) = (s.unit(), s.point());
    let tgt = Term::apply(s.pow, vec![unit.clone()]);

    // ── M(v) := { z ∈ 1 : ¬(• ∈ v) } ────────────────────────────────────────
    let (vv, zv) = (env.fresh_var(), env.fresh_var());
    let (tv, tz) = (Term::var(vv), Term::var(zv));
    let matrix = Formula::not(Formula::mem(point.clone(), tv.clone()));
    let ex = separation_full(env, zv, &matrix, &unit, &ap.empty_ax).expect("a Separation on 1");
    let (m, m_ax) = derived::define_by_membership(
        env,
        &[vv],
        &ex,
        zv,
        &Formula::and(Formula::mem(tz, unit.clone()), matrix),
    )
    .expect("M");

    // ── the minor: `cval(1, {⟨v, M(v)⟩ : v ∈ T})` ────────────────────────────
    let (mlam, mlam_ax) = lambda(env, &ap, m).expect("λv. M(v)");
    let mbeta = beta_conditional(env, &ap, m, mlam, &mlam_ax).expect("β");
    let mgraph = Term::apply(mlam, vec![tgt.clone()]);
    let minor = cval_of(&s, unit.clone(), mgraph.clone());

    let minor_value = {
        let outer = Thm::mp(
            &inst_all(&f.ra.base.cval_app, &[unit.clone(), mgraph.clone()]).expect("inst"),
            &s.unit_mem,
        )
        .expect("mp"); // ⊢ app(minor,•) = mgraph
        let inner = inst_all(&mbeta, &[tgt.clone(), tv.clone()]).expect("inst");
        let (ap_c, tgt_c, tv_c) = (ap.clone(), tgt.clone(), tv.clone());
        let lifted = rw_back(
            env,
            &outer,
            move |hole| {
                Formula::imp(
                    Formula::mem(tv_c.clone(), tgt_c.clone()),
                    Formula::eq(ap_c.apply(hole, tv_c.clone()), Term::apply(m, vec![tv_c.clone()])),
                )
            },
            &inner,
        );
        Thm::gen(vv, &lifted)
    };

    // ── H(c) := M(app(app(c, tup(d⃗)), •)) ───────────────────────────────────
    let child = IndexedDeclSpec::tup(&s, &f.spec.rec_index_vec(1, 0, &[], &[]).expect("child"));
    let (h, h_ax) = {
        let (s_c, child_c) = (s.clone(), child.clone());
        abbrev(env, 1, move |args| {
            Term::apply(m, vec![slot_at(&s_c, &args[0], &child_c)])
        })
    };
    let (hlam, hlam_ax) = lambda(env, &ap, h).expect("λc. H(c)");
    let hbeta = beta_conditional(env, &ap, h, hlam, &hlam_ax).expect("β");
    let ihb = ih_bound(&s, &f.le.a_phi, &tgt);
    let hgraph = Term::apply(hlam, vec![ihb.clone()]);

    // ── e := { ⟨q, cval(1, hgraph)⟩ : q ∈ A_φ } — uniform in `q` ────────────
    let (esym, e_ax) = {
        let (s_c, unit_c, hg) = (s.clone(), unit.clone(), hgraph.clone());
        abbrev(env, 1, move |_| cval_of(&s_c, unit_c.clone(), hg.clone()))
    };
    let (elam, elam_ax) = lambda(env, &ap, esym).expect("λq. E(q)");
    let ebeta = beta_conditional(env, &ap, esym, elam, &elam_ax).expect("β");
    let e = Term::apply(elam, vec![f.le.a_phi.clone()]);

    // ── `step(e,x,c) = M(slot(c))` under `x ∈ A_φ ∧ c ∈ ih_bound` ───────────
    let (xv, cv) = (env.fresh_var(), env.fresh_var());
    let (tx, tc) = (Term::var(xv), Term::var(cv));
    let x_in = Formula::mem(tx.clone(), f.le.a_phi.clone());
    let c_in = Formula::mem(tc.clone(), ihb.clone());
    let hyp = Formula::and(x_in.clone(), c_in.clone());
    let h_x = and_left(x_in.clone(), c_in.clone());
    let h_c = and_right(x_in, c_in);

    let s1 = syl(&h_x, &inst_all(&ebeta, &[f.le.a_phi.clone(), tx.clone()]).expect("inst"))
        .expect("syl");
    let s2 = h_trans(
        env,
        &s1,
        &a1i(&inst_all(&e_ax, std::slice::from_ref(&tx)).expect("inst"), hyp.clone()),
    );
    let s3 = {
        let (ap_c, pt) = (ap.clone(), point.clone());
        h_congr(env, &s2, move |hole| ap_c.apply(hole, pt.clone()))
    };
    let cv_app = Thm::mp(
        &inst_all(&f.ra.base.cval_app, &[unit.clone(), hgraph.clone()]).expect("inst"),
        &s.unit_mem,
    )
    .expect("mp");
    let s4 = h_trans(env, &s3, &a1i(&cv_app, hyp.clone()));
    let s5 = {
        let (ap_c, tc_c) = (ap.clone(), tc.clone());
        h_congr(env, &s4, move |hole| ap_c.apply(hole, tc_c.clone()))
    };
    let s6 = h_trans(
        env,
        &s5,
        &syl(&h_c, &inst_all(&hbeta, &[ihb.clone(), tc.clone()]).expect("inst")).expect("syl"),
    );
    let s7 = h_trans(
        env,
        &s6,
        &a1i(&inst_all(&h_ax, std::slice::from_ref(&tc)).expect("inst"), hyp.clone()),
    );
    assert_eq!(
        *s7.concl(),
        Formula::imp(
            hyp,
            Formula::eq(
                f.ra.base.step_at(&e, &tx, &tc),
                Term::apply(m, vec![slot_at(&s, &tc, &child)])
            )
        ),
        "the step computes to the minor's body"
    );
    let step_value = gen_all(&[xv, cv], &s7);

    Step { tgt, m, m_ax, e, minor, step_value, minor_value, child }
}

/// `⊢ M(w) ∈ 𝒫(1)` — every value of the step is a Separation on `1`.
fn m_in_target(env: &mut Env, f: &Fix, st: &Step, w: &Term) -> Thm {
    let s = &f.s;
    let mv = Term::apply(st.m, vec![w.clone()]);
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let at = inst_all(&st.m_ax, &[w.clone(), tz.clone()]).expect("inst");
    let sub = Thm::gen(
        zv,
        &syl(
            &iff_mp(&at).expect("fwd"),
            &and_left(
                Formula::mem(tz.clone(), s.unit()),
                Formula::not(Formula::mem(s.point(), w.clone())),
            ),
        )
        .expect("syl"),
    );
    Thm::mp(
        &iff_mpr(&inst_all(&s.pow_ax, &[s.unit(), mv]).expect("inst")).expect("mpr"),
        &sub,
    )
    .expect("mp")
}

// ── the tests ───────────────────────────────────────────────────────────────

/// `R` really contains the step constructor's edge, and the induction
/// hypothesis really computes to the recursive value there. These are the rules
/// that would be vacuous if the `LE ctor` recursion had emitted the wrong
/// disjunct — everything else in the module would still hold, about an opaque
/// set.
#[test]
fn the_edge_is_in_the_relation_and_the_ih_slot_is_the_recursive_value() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (child, res) = (f.res(0), f.res(1));
    let edge = f.ac.edge(child.clone(), res.clone());

    // `tup(d⃗) ∈ A_φ` is the base constructor's own introduction rule.
    let child_in = Thm::mp(&f.le.intro[0], &f.ant_thm(&mut env, 0)).expect("(A_φ-intro)");
    assert_eq!(*child_in.concl(), Formula::mem(child.clone(), f.le.a_phi.clone()));

    let k = conj_of(&[f.ant(1), Formula::mem(child.clone(), f.le.a_phi.clone())]).expect("K");
    let k_thm = and_intro(&f.ant_thm(&mut env, 1), &child_in);
    assert_eq!(*k_thm.concl(), k);

    let in_r = Thm::mp(&f.lr.rel_intro[1][0], &k_thm).expect("the edge is in R");
    assert_eq!(*in_r.concl(), Formula::mem(edge, f.le.r.clone()));
    assert!(closed(in_r.concl()) && in_r.hyps().is_empty());

    // The slot rule is stated over `T` and `e`; at any of them it computes.
    let (tv, ev) = (env.fresh_var(), env.fresh_var());
    let (tt, te) = (Term::var(tv), Term::var(ev));
    let slot = inst_all(&f.lr.ih_slot[1][0], &[tt.clone(), te.clone()]).expect("inst");
    let out = Thm::mp(&slot, &k_thm).expect("the slot computes");
    let rec = f.ra.of(f.le.a_phi.clone(), f.le.r.clone(), tt, te);
    let ih = f.ra.base.ih_at(&rec, &f.le.a_phi, &f.le.r, &res);
    assert_eq!(
        *out.concl(),
        Formula::eq(slot_at(&f.s, &ih, &child), f.ra.base.app(&rec, &child)),
        "app(app(IH, tup(d⃗)), •) is the recursive value"
    );
    assert!(out.hyps().is_empty());
}

/// Both index tuples are accessible — so `acc(A_φ,R)` is not empty and the
/// recursor is not a function on nothing. The base point is accessible because
/// `R` has no edge into it; the step point because its one predecessor is.
#[test]
fn both_index_tuples_are_accessible() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let (base, step) = accessible(&mut env, &f);
    assert_eq!(*base.concl(), Formula::mem(f.res(0), f.le.acc_set.clone()));
    assert_eq!(*step.concl(), Formula::mem(f.res(1), f.le.acc_set.clone()));
    assert!(closed(base.concl()) && base.hyps().is_empty());
    assert!(closed(step.concl()) && step.hyps().is_empty());
}

/// **The recursor is not constant.** `minor_iota` fires with nothing on the
/// left, and the value at the step constructor is the minor applied to the
/// value at the base constructor — from which a diagonal argument refutes their
/// being equal.
#[test]
fn the_recursor_fires_and_its_two_values_differ() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let st = build_step(&mut env, &f);
    let s = f.s.clone();
    let (base_i, step_i) = (f.res(0), f.res(1));

    // ── `ST`, from the step's own computation ───────────────────────────────
    let st_thm = step_typed_holds(&mut env, &f, &st);
    let st_f = f.ra.step_typed(&mut env, &f.le.a_phi, &f.le.r, &st.tgt, &st.e);
    assert_eq!(*st_thm.concl(), st_f, "step_typed, as rec_acc states it");
    assert!(closed(st_thm.concl()) && st_thm.hyps().is_empty());

    // ── `minor_eq` for the step constructor ─────────────────────────────────
    let me_thm = minor_eq_holds(&mut env, &f, &st);
    assert!(closed(me_thm.concl()) && me_thm.hyps().is_empty());

    // ── fire `minor_iota[1]` ────────────────────────────────────────────────
    let mi = inst_all(&f.lr.minor_iota[1], &[st.tgt.clone(), st.e.clone(), st.minor.clone()])
        .expect("at T, e and the minor");
    assert_eq!(
        mi.concl().as_imp().expect("imp").0,
        Formula::and(st_f, me_thm.concl().clone()),
        "the recursor's two antecedents are exactly what was discharged"
    );
    let fired = Thm::mp(&mi, &and_intro(&st_thm, &me_thm)).expect("both antecedents");

    let (acc_base, acc_step) = accessible(&mut env, &f);
    let k = Thm::mp(
        &fired,
        &and_intro(&f.ant_thm(&mut env, 1), &and_intro(&acc_step, &acc_base)),
    )
    .expect("the Lean-shaped antecedent");

    let rec = f.ra.of(f.le.a_phi.clone(), f.le.r.clone(), st.tgt.clone(), st.e.clone());
    let v_base = f.ra.base.app(&rec, &base_i);
    let v_step = f.ra.base.app(&rec, &step_i);
    assert_eq!(
        *k.concl(),
        Formula::eq(
            v_step.clone(),
            minor_app(&s, &f.spec, 1, &st.minor, &[], std::slice::from_ref(&v_base))
                .expect("the minor's spine")
        ),
        "ι: the value at `step` is the minor applied to the value at `base`"
    );
    assert!(closed(k.concl()) && k.hyps().is_empty());

    // ── `app(app(minor,•), v_base) = M(v_base)`, since `v_base ∈ T` ─────────
    let v_base_typed = {
        let vt = Thm::mp(
            &inst_all(
                &f.bd.value_typed,
                &[f.le.a_phi.clone(), f.le.r.clone(), st.tgt.clone(), st.e.clone()],
            )
            .expect("inst"),
            &st_thm,
        )
        .expect("ST");
        Thm::mp(&inst_all(&vt, std::slice::from_ref(&base_i)).expect("inst"), &acc_base)
            .expect("the base value is in T")
    };
    let unfolded = Thm::mp(
        &inst_all(&st.minor_value, std::slice::from_ref(&v_base)).expect("inst"),
        &v_base_typed,
    )
    .expect("the minor computes");
    let v_step_c = v_step.clone();
    let diag = rw(&mut env, &unfolded, move |hole| Formula::eq(v_step_c.clone(), hole), &k);
    assert_eq!(
        *diag.concl(),
        Formula::eq(v_step.clone(), Term::apply(st.m, vec![v_base.clone()])),
        "the recursor's value at `step` is M of its value at `base`"
    );

    // ── the diagonal ────────────────────────────────────────────────────────
    let out = diagonal(&mut env, &f, &st, &diag, &v_step, &v_base);
    assert_eq!(*out.concl(), Formula::not(Formula::eq(v_step, v_base)));
    assert!(closed(out.concl()) && out.hyps().is_empty());
}

// ── the pieces the last test is made of ─────────────────────────────────────

/// `⊢ tup(e⃗₀) = tup(e⃗₁) → ⊥`.
fn index_tuples_differ(env: &mut Env, f: &Fix) -> Thm {
    let s = &f.s;
    let (a, b) = (f.ix_of(0), f.ix_of(1));
    let inj = inst_all(&s.ap.pair_inj, &[a.clone(), s.point(), b.clone(), s.point()])
        .expect("pair injectivity");
    let heads = syl(
        &inj,
        &and_left(
            Formula::eq(a.clone(), b.clone()),
            Formula::eq(s.point(), s.point()),
        ),
    )
    .expect("the heads");
    let b_c = b.clone();
    let step = rw_h(env, &f.res_ax[0], move |hole| Formula::eq(hole, b_c.clone()), &heads);
    let ff = f.pts[0].clone();
    let unfolded = rw_h(env, &f.res_ax[1], move |hole| Formula::eq(ff.clone(), hole), &step);
    let ne = f.mach.syms.inj_distinct(env, s, 0, 1).expect("Inj₀ ≠ Inj₁");
    syl(&unfolded, &inst_all(&ne, &[s.point(), s.point()]).expect("at •")).expect("⊥")
}

/// `⊢ tup(e⃗₀) ∈ acc(A_φ,R)` and `⊢ tup(e⃗₁) ∈ acc(A_φ,R)`.
fn accessible(env: &mut Env, f: &Fix) -> (Thm, Thm) {
    let s = &f.s;
    let (base_i, step_i) = (f.res(0), f.res(1));
    let base_in = Thm::mp(&f.le.intro[0], &f.ant_thm(env, 0)).expect("base ∈ A_φ");
    let step_in = Thm::mp(&f.le.intro[1], &f.ant_thm(env, 1)).expect("step ∈ A_φ");
    let differ = index_tuples_differ(env, f);

    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let the_edge = f.ac.edge(base_i.clone(), step_i.clone());
    let sq = s.prod.of(f.ix.idx.clone(), f.ix.idx.clone());

    // `⟨y,x⟩ ∈ R → ⟨y,x⟩ = ⟨tup(e⃗₀), tup(e⃗₁)⟩`: ρ has one disjunct and the
    // constructor has no fields, so the matrix is the bare edge equality.
    let matrix_of = |x: &Term| {
        let edge = f.ac.edge(ty.clone(), x.clone());
        let at = inst_all(&f.le.rel_ax, std::slice::from_ref(&edge)).expect("inst");
        let (l, r) = (
            Formula::mem(edge.clone(), sq.clone()),
            Formula::eq(edge.clone(), the_edge.clone()),
        );
        assert_eq!(
            *at.concl(),
            Formula::iff(
                Formula::mem(edge, f.le.r.clone()),
                Formula::and(l.clone(), r.clone())
            ),
            "ρ at a fieldless recursive constructor is its own edge equality"
        );
        syl(&iff_mp(&at).expect("fwd"), &and_right(l, r)).expect("the matrix")
    };

    // Nothing points at the base index: that would force `tup(e⃗₀) = tup(e⃗₁)`.
    let no_edge_into_base = {
        let m = matrix_of(&base_i);
        let inj = inst_all(
            &s.ap.pair_inj,
            &[ty.clone(), base_i.clone(), base_i.clone(), step_i.clone()],
        )
        .expect("inst");
        let snd = syl(
            &syl(&m, &inj).expect("syl"),
            &and_right(
                Formula::eq(ty.clone(), base_i.clone()),
                Formula::eq(base_i.clone(), step_i.clone()),
            ),
        )
        .expect("the second components");
        Thm::gen(yv, &syl(&snd, &differ).expect("⊥"))
    };
    let base_acc = Thm::mp(
        &inst_all(&f.ac.minimal, &[f.le.a_phi.clone(), f.le.r.clone(), base_i.clone()])
            .expect("inst"),
        &and_intro(&base_in, &no_edge_into_base),
    )
    .expect("the base index is R-minimal, hence accessible");

    // Every edge into the step index comes from the base index.
    let preds = {
        let m = matrix_of(&step_i);
        let inj = inst_all(
            &s.ap.pair_inj,
            &[ty.clone(), step_i.clone(), base_i.clone(), step_i.clone()],
        )
        .expect("inst");
        let fst = syl(
            &syl(&m, &inj).expect("syl"),
            &and_left(
                Formula::eq(ty.clone(), base_i.clone()),
                Formula::eq(step_i.clone(), step_i.clone()),
            ),
        )
        .expect("the first components");
        let acc_set = f.le.acc_set.clone();
        let fst_back = h_symm(env, &fst);
        let carry = h_leib(env, &fst_back, move |hole| Formula::mem(hole, acc_set.clone()));
        let edge_in = fst.concl().as_imp().expect("imp").0;
        let got = hyp_mp(&carry, &a1i(&base_acc, edge_in)).expect("mp");
        Thm::gen(yv, &a1i(&got, Formula::mem(ty.clone(), f.le.a_phi.clone())))
    };
    let step_acc = Thm::mp(
        &inst_all(&f.ac.acc_intro, &[f.le.a_phi.clone(), f.le.r.clone(), step_i.clone()])
            .expect("inst"),
        &and_intro(&step_in, &preds),
    )
    .expect("every predecessor is accessible");
    (base_acc, step_acc)
}

/// `⊢ step_typed(A_φ, R, T, e)`, from the step's computation and the fact that
/// every one of its values is a Separation on `1`.
fn step_typed_holds(env: &mut Env, f: &Fix, st: &Step) -> Thm {
    let s = &f.s;
    let (xv, cv) = (env.fresh_var(), env.fresh_var());
    let (tx, tc) = (Term::var(xv), Term::var(cv));
    let ihb = ih_bound(s, &f.le.a_phi, &st.tgt);

    let x_acc = Formula::mem(tx.clone(), f.le.acc_set.clone());
    let c_in = Formula::mem(tc.clone(), ihb.clone());
    let hyp = Formula::and(x_acc.clone(), c_in.clone());
    let h_x = syl(
        &and_left(x_acc.clone(), c_in.clone()),
        &inst_all(&f.ac.acc_subset, &[f.le.a_phi.clone(), f.le.r.clone(), tx.clone()])
            .expect("inst"),
    )
    .expect("acc ⊆ A_φ");
    let h_c = and_right(x_acc.clone(), c_in.clone());
    let value = syl(
        &hyp_and(&h_x, &h_c).expect("both"),
        &inst_all(&st.step_value, &[tx.clone(), tc.clone()]).expect("inst"),
    )
    .expect("the step computes");

    let w = slot_at(s, &tc, &st.child);
    let typed = a1i(&m_in_target(env, f, st, &w), hyp.clone());
    let tgt = st.tgt.clone();
    let value_back = h_symm(env, &value);
    let carry = h_leib(env, &value_back, move |hole| Formula::mem(hole, tgt.clone()));
    let per = hyp_mp(&carry, &typed).expect("mp");
    Thm::gen(xv, &gen_under(cv, &uncurry(&per).expect("uncurry")))
}

/// `⊢ minor_eq(1)` — both sides of the step constructor's contract are
/// `M(slot(c))`.
fn minor_eq_holds(env: &mut Env, f: &Fix, st: &Step) -> Thm {
    let s = &f.s;
    let cv = env.fresh_var();
    let tc = Term::var(cv);
    let ihb = ih_bound(s, &f.le.a_phi, &st.tgt);
    let slot = slot_at(s, &tc, &st.child);
    let res = f.res(1);

    let atoms = [
        f.ant(1),
        Formula::mem(tc.clone(), ihb.clone()),
        Formula::mem(slot.clone(), st.tgt.clone()),
    ];
    let guard = conj_of(&atoms).expect("the guard");
    let g_ihb = conj_proj(&atoms, 1).expect("proj");
    let g_slot = conj_proj(&atoms, 2).expect("proj");

    // LHS: the step at this constructor's index computes to `M(slot)`.
    let res_in = a1i(
        &Thm::mp(&f.le.intro[1], &f.ant_thm(env, 1)).expect("intro"),
        guard.clone(),
    );
    let lhs = syl(
        &hyp_and(&res_in, &g_ihb).expect("both"),
        &inst_all(&st.step_value, &[res.clone(), tc.clone()]).expect("inst"),
    )
    .expect("the step computes");

    // RHS: the minor at a value of `T` computes to `M` of it.
    let rhs = syl(
        &g_slot,
        &inst_all(&st.minor_value, std::slice::from_ref(&slot)).expect("inst"),
    )
    .expect("the minor computes");
    let rhs_back = h_symm(env, &rhs);
    let body = h_trans(env, &lhs, &rhs_back);

    let out = Thm::gen(cv, &body);
    assert_eq!(
        *out.concl(),
        f.lr.minor_eq_at(1, &st.tgt, &st.e, &st.minor).expect("the contract"),
        "the contract, as the recursor states it"
    );
    out
}

/// `⊢ ¬(v_step = v_base)`, from `⊢ v_step = M(v_base)` alone — Cantor's
/// diagonal, with no computation of either value.
fn diagonal(env: &mut Env, f: &Fix, st: &Step, diag: &Thm, v_step: &Term, v_base: &Term) -> Thm {
    let s = &f.s;
    let point = s.point();
    let sup = Formula::eq(v_step.clone(), v_base.clone());

    // `⊢ S → v_base = M(v_base)`.
    let h_diag = a1i(diag, sup.clone());
    let h_sup = imp_refl(sup.clone());
    let sup_back = h_symm(env, &h_sup);
    let u_eq = h_trans(env, &sup_back, &h_diag);

    // `⊢ S → (• ∈ v_base ↔ (• ∈ 1 ∧ ¬(• ∈ v_base)))`.
    let at = inst_all(&st.m_ax, &[v_base.clone(), point.clone()]).expect("inst");
    let unit_mem_f = Formula::mem(point.clone(), s.unit());
    let p = Formula::mem(point.clone(), v_base.clone());
    let rhs = Formula::and(unit_mem_f.clone(), Formula::not(p.clone()));
    let (rhs_c, p_c, pt_c) = (rhs.clone(), p.clone(), point.clone());
    let u_back = h_symm(env, &u_eq);
    let carry = h_leib(env, &u_back, move |hole| {
        Formula::iff(Formula::mem(pt_c.clone(), hole), rhs_c.clone())
    });
    let bicond = hyp_mp(&carry, &a1i(&at, sup.clone())).expect("mp");
    let _ = p_c;

    let fwd_f = Formula::imp(p.clone(), rhs.clone());
    let bwd_f = Formula::imp(rhs.clone(), p.clone());
    let fwd = syl(
        &syl(&bicond, &and_left(fwd_f.clone(), bwd_f.clone())).expect("syl"),
        &imp_mono_r(
            &and_right(unit_mem_f.clone(), Formula::not(p.clone())),
            p.clone(),
        )
        .expect("mono"),
    )
    .expect("S → (P → ¬P)");
    let bwd = syl(&bicond, &and_right(fwd_f, bwd_f)).expect("S → ((⊤ ∧ ¬P) → P)");

    // `⊢ ¬P → (⊤ ∧ ¬P)`, hence `⊢ S → (¬P → P)`, hence `⊢ S → P` by Clavius.
    let into_rhs = hyp_and(
        &a1i(&s.unit_mem, Formula::not(p.clone())),
        &imp_refl(Formula::not(p.clone())),
    )
    .expect("¬P → (⊤ ∧ ¬P)");
    let neg_to_p = chain(&a1i(&into_rhs, sup.clone()), &bwd);
    let s_p = syl(&neg_to_p, &clavius(p.clone())).expect("Clavius");
    let s_np = hyp_mp(&fwd, &s_p).expect("mp");
    hyp_mp(&s_np, &s_p).expect("P and ¬P")
}
