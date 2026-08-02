//! **The indexed class-(T) eliminator at a `Prop` motive** —
//! `derived/src/inductive/family/prop_rec.rs`, the construction `068`'s
//! `RBTree.rec.{u,u}` blocks on.
//!
//! Two shapes, and both polarities:
//!
//! * `RBTree` itself — one parameter, two indices, three constructors, the
//!   interleaved mask `Plain, Rec, Plain, Rec` and a six-field constructor. The
//!   rule is **fired end to end** at a *concrete* motive, built as a nest of
//!   three lambda graphs so that every minor is genuinely dischargeable, and the
//!   conclusion comes out at closed terms.
//! * a synthetic family whose constructor has **two recursive arguments at
//!   swapped indices** — `l` at `(a, zero)` and `r` at `(zero, a)`, concluding
//!   at `(b, a)`. Three distinct index vectors, because two cannot tell an
//!   ordering from its reverse — and they stay distinct **after unfolding**,
//!   which is the spelling that matters and the one `RBTree.red` cannot supply:
//!   its two children both land on `(b, n)`. `RBTree` is not blind — `black`'s
//!   children sit at `c₁`/`c₂` and catch both pairing mutations — and at
//!   `derived`'s own spelling nothing is blind at all, since the two `d⃗ᵢⱼ` are
//!   always different `FnSym`s. All three of those are measured in the tests
//!   below rather than asserted here; prose about this has been wrong twice.
//!
//! **Non-vacuity cuts both ways.** A rule whose minors were decoration would be
//! satisfied by every motive: what rules that out is the same nest with its
//! innermost value changed from `1` to `∅`, at which `MINOR_leaf` is
//! **refutable**. And a rule about a carrier that were constantly inhabited
//! would say something everywhere: what rules that out is the conclusion at
//! `(b, Inj₂(•))`, an index no constructor produces, where `empty_at_index`
//! makes it a theorem outright with no minor spent.
//!
//! Each test rebuilds the formula it expects from the kernel's own constructors
//! and from the theorem's own exported atoms, so a rule with the right name and
//! the wrong binder arithmetic fails here rather than downstream.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::funcs::{beta_conditional, lambda, Apply};
use derived::inductive::family::{
    empty_at_index, guard_atoms_of, icod, idep_minor, motive_app, motive_congr, motive_congr_of,
    CtorIndices, IndexedDeclSpec, IndexedGuardedMinors, IndexedInductive, IndexedPropRecursor,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine, Slot};
use derived::sums::Sums;
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{
    a1i, and_intro, conj_of, define_abbrev, eq_symm, gen_all, hyp_mp, inst_all, syl,
};

// ─────────────────────────────────────────────────────────────────────────────
// Rewriting helpers — with and without an ambient hypothesis
// ─────────────────────────────────────────────────────────────────────────────

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

/// From `⊢ x = y` infer `⊢ ctx(x) = ctx(y)`.
fn cong(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Term) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let lhs = ctx(x.clone());
    let leib = Thm::eq_leibniz(x, y, hole, Formula::eq(lhs.clone(), ctx(Term::var(hole))));
    Thm::mp(&Thm::mp(&leib, eq).expect("mp"), &Thm::eq_refl(lhs)).expect("mp")
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
    let back = eq_symm(env, eq).expect("symm");
    rw(env, &back, ctx, base)
}

/// From `⊢ [H →] x = y` and `⊢ [H →] φ(x)` infer `⊢ [H →] φ(y)`.
///
/// One helper for both, because every step of the motive computation below has
/// to run under `MINORᵢ`'s antecedent for a constructor with fields and without
/// one for a constructor with none.
fn rw_o(
    env: &mut Env,
    h: Option<&Formula>,
    eq: &Thm,
    ctx: impl Fn(Term) -> Formula,
    base: &Thm,
) -> Thm {
    let src = match h {
        None => eq.concl().clone(),
        Some(_) => eq.concl().as_imp().expect("an implication").1,
    };
    let (x, y) = src.as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    match h {
        None => Thm::mp(&Thm::mp(&leib, eq).expect("mp"), base).expect("mp"),
        Some(_) => hyp_mp(&syl(eq, &leib).expect("syl"), base).expect("hyp_mp"),
    }
}

/// From `⊢ [H →] x = y` infer `⊢ [H →] y = x`.
fn symm_o(env: &mut Env, h: Option<&Formula>, eq: &Thm) -> Thm {
    let src = match h {
        None => eq.concl().clone(),
        Some(_) => eq.concl().as_imp().expect("an implication").1,
    };
    let (x, _) = src.as_eq().expect("an equation");
    let refl = lift(h, &Thm::eq_refl(x.clone()));
    rw_o(env, h, eq, move |q| Formula::eq(q, x.clone()), &refl)
}

/// From `⊢ [H →] a = b` and `⊢ [H →] b = c` infer `⊢ [H →] a = c`.
fn trans_o(env: &mut Env, h: Option<&Formula>, ab: &Thm, bc: &Thm) -> Thm {
    let src = match h {
        None => ab.concl().clone(),
        Some(_) => ab.concl().as_imp().expect("an implication").1,
    };
    let (a, _) = src.as_eq().expect("an equation");
    rw_o(env, h, bc, move |q| Formula::eq(a.clone(), q), ab)
}

/// From `⊢ [H →] x = y` infer `⊢ [H →] ctx(x) = ctx(y)`.
fn cong_o(env: &mut Env, h: Option<&Formula>, eq: &Thm, ctx: impl Fn(Term) -> Term) -> Thm {
    let src = match h {
        None => eq.concl().clone(),
        Some(_) => eq.concl().as_imp().expect("an implication").1,
    };
    let (x, _) = src.as_eq().expect("an equation");
    let lhs = ctx(x);
    let refl = lift(h, &Thm::eq_refl(lhs.clone()));
    rw_o(env, h, eq, move |q| Formula::eq(lhs.clone(), ctx(q)), &refl)
}

/// `⊢ φ` weakened to `⊢ H → φ`, or left alone.
fn lift(h: Option<&Formula>, t: &Thm) -> Thm {
    match h {
        None => t.clone(),
        Some(f) => a1i(t, f.clone()),
    }
}

/// From an unconditional `⊢ A → B` and `⊢ [H →] A`, infer `⊢ [H →] B`.
fn mp_o(h: Option<&Formula>, rule: &Thm, arg: &Thm) -> Thm {
    match h {
        None => Thm::mp(rule, arg).expect("mp"),
        Some(f) => hyp_mp(&a1i(rule, f.clone()), arg).expect("hyp_mp"),
    }
}

/// `app(app(app(m,a),b),c)` — three application nodes, **written out**.
///
/// Deliberately not `motive_app`, and deliberately not a fold: the convention
/// under test *is* the order and the nesting, so an expectation built with the
/// same loop that builds the thing would be blind to a reversal — which is
/// exactly what happened to this file's shape tests once already.
fn spine3(s: &Sums, m: &Term, a: &Term, b: &Term, c: &Term) -> Term {
    let ap = &s.ap;
    ap.apply(ap.apply(ap.apply(m.clone(), a.clone()), b.clone()), c.clone())
}

/// `app(app(app(app(m,a),b),c),d)` — four application nodes, written out.
fn spine4(s: &Sums, m: &Term, a: &Term, b: &Term, c: &Term, d: &Term) -> Term {
    let ap = &s.ap;
    ap.apply(
        ap.apply(ap.apply(ap.apply(m.clone(), a.clone()), b.clone()), c.clone()),
        d.clone(),
    )
}

/// Right-nested conjunction of closed theorems, matching `conj_of`.
fn conj_thms(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = and_intro(t, &acc);
    }
    acc
}

/// `⊢ tup(u⃗) = tup(v⃗) → uₖ = vₖ`.
fn tup_proj(s: &Sums, us: &[Term], vs: &[Term], k: usize) -> Thm {
    let ap = &s.ap;
    let mut cur = derived::imp_refl(Formula::eq(
        IndexedDeclSpec::tup(s, us),
        IndexedDeclSpec::tup(s, vs),
    ));
    for lvl in 0..=k {
        let (tu, tv) = (
            IndexedDeclSpec::tup(s, &us[lvl + 1..]),
            IndexedDeclSpec::tup(s, &vs[lvl + 1..]),
        );
        let inj = inst_all(
            &ap.pair_inj,
            &[us[lvl].clone(), tu.clone(), vs[lvl].clone(), tv.clone()],
        )
        .expect("pair injectivity");
        let both = syl(&cur, &inj).expect("syl");
        let (l, r) = (Formula::eq(us[lvl].clone(), vs[lvl].clone()), Formula::eq(tu, tv));
        cur = if lvl == k {
            syl(&both, &derived::and_left(l, r)).expect("head")
        } else {
            syl(&both, &derived::and_right(l, r)).expect("tail")
        };
    }
    cur
}

/// From `⊢ uₖ = vₖ` for each `k`, infer `⊢ tup(u⃗) = tup(v⃗)`.
fn tup_congr(env: &mut Env, s: &Sums, eqs: &[Thm]) -> Thm {
    let mut cur = Thm::eq_refl(s.point());
    for eq in eqs.iter().rev() {
        let (_, new) = eq.concl().as_eq().expect("an equation");
        let (old_tail, _) = cur.concl().as_eq().expect("an equation");
        let one = cong(env, eq, |x| s.ap.sets.pair(x, old_tail.clone()));
        let two = cong(env, &cur, |x| s.ap.sets.pair(new.clone(), x));
        cur = derived::eq_trans(env, &one, &two).expect("trans");
    }
    cur
}

// ─────────────────────────────────────────────────────────────────────────────
// The apparatus
// ─────────────────────────────────────────────────────────────────────────────

struct Fix {
    mach: Machine,
    rc: Recursor,
    iota: Thm,
    funspace: Thm,
}

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 3).expect("three summands");
    let rc = Recursor::new(env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(env, &mach.wt, &rc, &total).expect("funspace");
    Fix { mach, rc, iota, funspace }
}

/// A symbol of the given arity whose value is `body`.
fn abbrev(env: &mut Env, arity: usize, body: impl Fn(&[Term]) -> Term) -> (FnSym, Thm) {
    let vars: Vec<FreeVar> = (0..arity).map(|_| env.fresh_var()).collect();
    let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let t = body(&args);
    define_abbrev(env, &vars, &t).expect("an abbreviation")
}

/// `⊢ Injⱼ(•) ∈ finord(m)`.
fn inj_pt_mem(mach: &Machine, m: usize, j: usize) -> Thm {
    let s = &mach.wt.sums;
    let mut args = vec![s.unit(); m];
    args.push(s.point());
    Thm::mp(
        &inst_all(mach.syms.inj_mem(m, j).expect("inj_mem"), &args).expect("instantiate"),
        &s.unit_mem,
    )
    .expect("mp")
}

// ─────────────────────────────────────────────────────────────────────────────
// `RBTree`
// ─────────────────────────────────────────────────────────────────────────────

/// The declaration, and every defining equation a test needs to unfold.
struct Rb {
    spec: IndexedDeclSpec,
    /// `⊢ ∀α. ι₀(α) = finord(2)` and `⊢ ∀α ∀c. ι₁(α,c) = finord(3)`.
    ity_ax: Vec<Thm>,
    /// The `β` axioms, per constructor.
    beta_ax: Vec<Vec<Thm>>,
    /// The result-index axioms, `[ctor][k]`.
    res_ax: Vec<Vec<Thm>>,
    /// The recursive-argument index axioms, `[ctor][rec slot][k]`.
    rec_ax: Vec<Vec<Vec<Thm>>>,
}

/// `RBTree`, as an [`IndexedDeclSpec`] — the same decoding
/// `derived/tests/family.rs` uses, and faithful in every respect the derived
/// layer can see:
///
/// ```text
/// leaf                : RBTree α  b  zero
/// red   n l x r       : RBTree α  r  n           l, r at (b, n)
/// black c₁ c₂ n l x r : RBTree α  b  (succ n)    l at (c₁,n), r at (c₂,n)
/// ```
fn rbtree(env: &mut Env, mach: &Machine) -> Rb {
    let s = &mach.wt.sums;
    let pt = s.point();
    let color = mach.syms.finord(s, 2).expect("finord(2)");
    let nat = mach.syms.finord(s, 3).expect("finord(3)");
    let b = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let r = mach.syms.inj(1, pt.clone()).expect("Inj₁");

    let (i0, i0_ax) = abbrev(env, 1, |_| color.clone());
    let (i1, i1_ax) = abbrev(env, 2, |_| nat.clone());

    let (rb0, rb0_ax) = abbrev(env, 1, |_| nat.clone());
    let (rb1, rb1_ax) = abbrev(env, 2, |a| a[0].clone());
    let (bb0, bb0_ax) = abbrev(env, 1, |_| color.clone());
    let (bb1, bb1_ax) = abbrev(env, 2, |_| color.clone());
    let (bb2, bb2_ax) = abbrev(env, 3, |_| nat.clone());
    let (bb3, bb3_ax) = abbrev(env, 4, |a| a[0].clone());

    let base = DeclSpec::new(
        1,
        vec![
            CtorSpec::nullary(),
            CtorSpec::with_order(
                vec![rb0, rb1],
                2,
                vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
            )
            .expect("red's mask"),
            CtorSpec::with_order(
                vec![bb0, bb1, bb2, bb3],
                2,
                vec![Slot::Plain, Slot::Plain, Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
            )
            .expect("black's mask"),
        ],
    );

    let mk = |env: &mut Env, arity: usize, pick: Option<usize>, k: Term| match pick {
        None => abbrev(env, arity, move |_| k.clone()),
        Some(i) => abbrev(env, arity, move |a| a[i].clone()),
    };

    let (l0, l0a) = mk(env, 1, None, b.clone());
    let (l1, l1a) = mk(env, 1, None, b.clone());
    let leaf_idx = CtorIndices::nonrecursive(vec![l0, l1]);

    let (r0, r0a) = mk(env, 3, None, r.clone());
    let (r1, r1a) = mk(env, 3, Some(1), pt.clone());
    let (d00, d00a) = mk(env, 2, None, b.clone());
    let (d01, d01a) = mk(env, 2, Some(1), pt.clone());
    let (d10, d10a) = mk(env, 3, None, b.clone());
    let (d11, d11a) = mk(env, 3, Some(1), pt.clone());
    let red_idx =
        CtorIndices { result: vec![r0, r1], rec_args: vec![vec![d00, d01], vec![d10, d11]] };

    let (k0, k0a) = mk(env, 5, None, b.clone());
    let (k1, k1a) = mk(env, 5, None, r.clone());
    let (e00, e00a) = mk(env, 4, Some(1), pt.clone());
    let (e01, e01a) = mk(env, 4, Some(3), pt.clone());
    let (e10, e10a) = mk(env, 5, Some(2), pt.clone());
    let (e11, e11a) = mk(env, 5, Some(3), pt.clone());
    let black_idx =
        CtorIndices { result: vec![k0, k1], rec_args: vec![vec![e00, e01], vec![e10, e11]] };

    Rb {
        spec: IndexedDeclSpec::new(base, vec![i0, i1], vec![leaf_idx, red_idx, black_idx]),
        ity_ax: vec![i0_ax, i1_ax],
        beta_ax: vec![vec![], vec![rb0_ax, rb1_ax], vec![bb0_ax, bb1_ax, bb2_ax, bb3_ax]],
        res_ax: vec![vec![l0a, l1a], vec![r0a, r1a], vec![k0a, k1a]],
        rec_ax: vec![
            Vec::new(),
            vec![vec![d00a, d01a], vec![d10a, d11a]],
            vec![vec![e00a, e01a], vec![e10a, e11a]],
        ],
    }
}

struct Built {
    f: Fix,
    rb: Rb,
    ind: Inductive,
    fam: IndexedInductive,
}

fn build(env: &mut Env) -> Built {
    let f = fixture(env);
    let mut mach = f.mach;
    let rb = rbtree(env, &mach);
    assert!(rb.spec.well_formed(), "the RBTree spec is well formed");
    let ind = Inductive::build(env, &mut mach, &rb.spec.base).expect("the skeleton");
    let fam = IndexedInductive::build(env, &mut mach, &ind, &rb.spec, &f.rc, &f.iota, &f.funspace)
        .expect("the indexed family");
    Built { f: Fix { mach, ..f }, rb, ind, fam }
}

impl Built {
    fn s(&self) -> &Sums { &self.f.mach.wt.sums }
    /// `α := 1`.
    fn p(&self) -> Term { self.s().unit() }
    fn b(&self) -> Term { self.f.mach.syms.inj(0, self.s().point()).expect("Inj₀") }
    /// `Inj₂(•)`, a height no constructor produces.
    fn two(&self) -> Term { self.f.mach.syms.inj(2, self.s().point()).expect("Inj₂") }
    fn leaf(&self) -> Term { self.ind.ctor_term(&self.f.mach, 0, &[], &[]).expect("leaf") }
    fn pv(&self) -> Term { Term::var(self.ind.params[0]) }
    fn fam_at(&self, xs: &[Term]) -> Term {
        self.fam.carrier.ty_of(&[self.p()], xs).expect("the carrier")
    }
    /// `W` at `α := 1`, read off the skeleton's own defining equation.
    fn w1(&self) -> Term {
        inst_all(&self.ind.ty_ax, &[self.p()])
            .expect("at α := 1")
            .concl()
            .as_eq()
            .expect("an equation")
            .1
    }
    /// `e⃗ᵢ(1, y⃗)` as symbol applications, with their unfolding equations.
    fn res(&self, i: usize, ys: &[Term]) -> (Vec<Term>, Vec<Thm>) {
        let ps = [self.p()];
        let ts = self.rb.spec.result_vec(i, &ps, ys).expect("result indices");
        let mut args = ps.to_vec();
        args.extend(ys.iter().cloned());
        let eqs =
            self.rb.res_ax[i].iter().map(|ax| inst_all(ax, &args).expect("unfold")).collect();
        (ts, eqs)
    }
    fn res_at(&self, ps: &[Term], i: usize, ys: &[Term]) -> (Vec<Term>, Vec<Thm>) {
        let ts = self.rb.spec.result_vec(i, ps, ys).expect("result indices");
        let mut args = ps.to_vec();
        args.extend(ys.iter().cloned());
        let eqs =
            self.rb.res_ax[i].iter().map(|ax| inst_all(ax, &args).expect("unfold")).collect();
        (ts, eqs)
    }
    /// `d⃗ᵢⱼ(1, y⃗)` **unfolded** — what a consumer sees once the index
    /// abbreviations are folded away, which is not what `derived/` states.
    fn rec_vals(&self, i: usize, j: usize, ys: &[Term]) -> Vec<Term> {
        let pb = self.rb.spec.plains_before(i, j).expect("a Rec slot");
        let mut args = vec![self.p()];
        args.extend(ys[..pb].iter().cloned());
        self.rb.rec_ax[i][j]
            .iter()
            .map(|ax| inst_all(ax, &args).expect("unfold").concl().as_eq().expect("eq").1)
            .collect()
    }

    /// `⊢ βⱼ(1, y<ⱼ) = value`.
    fn beta_unfold(&self, i: usize, j: usize, ys: &[Term]) -> Thm {
        let mut args = vec![self.p()];
        args.extend(ys[..j].iter().cloned());
        inst_all(&self.rb.beta_ax[i][j], &args).expect("unfold")
    }
}

/// `⊢ leaf ∈ ind(1, ⟨b, ⟨zero, •⟩⟩)` — the positive polarity, closed, with the
/// index written at the *values*.
///
/// The two `Eᵢ` antecedents (M) carries are discharged by walking both
/// abbreviations: the index expression `eₖ`'s and the index type `ιₖ`'s.
fn leaf_canon(env: &mut Env, b: &Built) -> Thm {
    let c = &b.fam.carrier.ctors[0];
    let vals = [inj_pt_mem(&b.f.mach, 2, 0), inj_pt_mem(&b.f.mach, 3, 0)];
    let (res, eqs) = b.res(0, &[]);
    let mut hyps = Vec::new();
    for k in 0..2 {
        let mut ia = vec![b.p()];
        ia.extend(res[..k].iter().cloned());
        let set = Term::apply(b.rb.spec.indices[k], ia.clone());
        let ity = inst_all(&b.rb.ity_ax[k], &ia).expect("the index type unfolds");
        let (_, value) = eqs[k].concl().as_eq().expect("an equation");
        let at_set = rw_back(env, &ity, move |x| Formula::mem(value.clone(), x), &vals[k]);
        hyps.push(rw_back(env, &eqs[k], move |x| Formula::mem(x, set.clone()), &at_set));
    }
    let at = inst_all(&c.mem, &[b.p()]).expect("(M) at α := 1");
    let mem = Thm::mp(&at, &conj_thms(&hyps)).expect("the discharged hypotheses are (M)'s");
    // Move the conclusion's indices onto the values.
    let mut cur = mem;
    let mut ix = res.clone();
    for (k, eq) in eqs.iter().enumerate() {
        let (_, new) = eq.concl().as_eq().expect("an equation");
        let (shape, leaf, pc, ty) = (ix.clone(), b.leaf(), b.p(), b.fam.carrier.ty);
        cur = rw(
            env,
            eq,
            move |hole| {
                let mut a = vec![pc.clone()];
                let mut v = shape.clone();
                v[k] = hole;
                a.extend(v);
                Formula::mem(leaf.clone(), Term::apply(ty, a))
            },
            &cur,
        );
        ix[k] = new;
    }
    cur
}

// ─────────────────────────────────────────────────────────────────────────────
// A concrete motive: three lambda graphs, constant at every level
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ ∀A ∀a. (a ∈ A → app(lam(A), a) = body)` — the constant function `λ_:A. body`.
fn const_fun(env: &mut Env, ap: &Apply, body: Term) -> (FnSym, Thm) {
    let (bsym, bax) = abbrev(env, 1, |_| body.clone());
    let (lam, lam_ax) = lambda(env, ap, bsym).expect("the lambda graph");
    let beta = beta_conditional(env, ap, bsym, lam, &lam_ax).expect("beta");
    let (av, xv) = (env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(av), Term::var(xv));
    let at = inst_all(&beta, &[ta.clone(), tx.clone()]).expect("at (A,x)");
    let unf = inst_all(&bax, std::slice::from_ref(&tx)).expect("unfold");
    let lhs = ap.apply(Term::apply(lam, vec![ta.clone()]), tx.clone());
    let h = Formula::mem(tx.clone(), ta.clone());
    let hr = Some(&h);
    let step = lift(hr, &unf);
    let out = {
        let lhs = lhs.clone();
        rw_o(env, hr, &step, move |q| Formula::eq(lhs.clone(), q), &at)
    };
    assert_eq!(*out.concl(), Formula::imp(h, Formula::eq(lhs, body)));
    (lam, gen_all(&[av, xv], &out))
}

/// The motive `m = λc:Color. λn:N. λt:W. val`, curried exactly as
/// [`motive_app`] applies it.
struct Motive {
    m: Term,
    /// `⊢ ∀A ∀a. (a ∈ A → app(lam_o(A), a) = lam_m(N))`.
    outer: Thm,
    /// `⊢ ∀A ∀a. (a ∈ A → app(lam_m(A), a) = lam_i(W))`.
    mid: Thm,
    /// `⊢ ∀A ∀a. (a ∈ A → app(lam_i(A), a) = val)`.
    inner: Thm,
    color: Term,
    nat: Term,
    w1: Term,
    val: Term,
}

fn motive_of(env: &mut Env, b: &Built, val: Term) -> Motive {
    let ap = b.s().ap.clone();
    let color = b.f.mach.syms.finord(b.s(), 2).expect("finord(2)");
    let nat = b.f.mach.syms.finord(b.s(), 3).expect("finord(3)");
    let w1 = b.w1();
    let (lam_i, inner) = const_fun(env, &ap, val.clone());
    let (lam_m, mid) = const_fun(env, &ap, Term::apply(lam_i, vec![w1.clone()]));
    let (lam_o, outer) = const_fun(env, &ap, Term::apply(lam_m, vec![nat.clone()]));
    Motive {
        m: Term::apply(lam_o, vec![color.clone()]),
        outer,
        mid,
        inner,
        color,
        nat,
        w1,
        val,
    }
}

impl Motive {
    /// `⊢ [H →] app(app(app(m,c),n),t) = val`, from `[H →] c ∈ Color`,
    /// `[H →] n ∈ N` and `[H →] t ∈ W`.
    #[allow(clippy::too_many_arguments)]
    fn compute(
        &self,
        env: &mut Env,
        s: &Sums,
        h: Option<&Formula>,
        c: &Term,
        n: &Term,
        t: &Term,
        cm: &Thm,
        nm: &Thm,
        tm: &Thm,
    ) -> Thm {
        let ap = s.ap.clone();
        let e1 = mp_o(
            h,
            &inst_all(&self.outer, &[self.color.clone(), c.clone()]).expect("outer"),
            cm,
        );
        let e2 = mp_o(
            h,
            &inst_all(&self.mid, &[self.nat.clone(), n.clone()]).expect("mid"),
            nm,
        );
        let e3 = mp_o(
            h,
            &inst_all(&self.inner, &[self.w1.clone(), t.clone()]).expect("inner"),
            tm,
        );
        let (a1, n1, t1) = (ap.clone(), n.clone(), t.clone());
        let c1 = cong_o(env, h, &e1, move |q| a1.apply(a1.apply(q, n1.clone()), t1.clone()));
        let (a2, t2) = (ap.clone(), t.clone());
        let c2 = cong_o(env, h, &e2, move |q| a2.apply(q, t2.clone()));
        let half = trans_o(env, h, &c1, &c2);
        trans_o(env, h, &half, &e3)
    }

    /// `⊢ [H →] • ∈ app(app(app(m,c),n),t)`, given the computation and
    /// `⊢ • ∈ val`.
    fn holds(
        &self,
        env: &mut Env,
        s: &Sums,
        h: Option<&Formula>,
        chain: &Thm,
        val_mem: &Thm,
    ) -> Thm {
        let back = symm_o(env, h, chain);
        let pt = s.point();
        rw_o(env, h, &back, move |q| Formula::mem(pt.clone(), q), &lift(h, val_mem))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The shapes — the binder arithmetic, pinned position by position
// ─────────────────────────────────────────────────────────────────────────────

/// **The deliverable's statement.** `minor_atoms` is the constructor's fields in
/// *declared* order followed by the induction hypotheses, `minors` quantifies in
/// that same order, and `rec` is
/// `⊢ ∀α ∀m. (⋀ᵢ MINORᵢ → ∀x⃗ ∀t. (t ∈ ind(α,x⃗) → • ∈ app(m,x⃗,t)))`.
///
/// Every atom is rebuilt from the spec's own symbols, so a permutation, a
/// mis-paired induction hypothesis or a motive applied in the wrong order fails
/// here.
#[test]
fn the_minor_antecedent_is_lean_positional_at_every_constructor() {
    let mut env = Env::new();
    let b = build(&mut env);
    let pr = IndexedPropRecursor::over_family(&mut env, &b.f.mach, &b.ind, &b.fam)
        .expect("the Prop-motive rule");
    let s = b.s().clone();
    let pt = s.point();
    let tm = Term::var(pr.motive);
    let ps = [b.pv()];

    assert_eq!(pr.minor_atoms.len(), 3);
    assert_eq!(pr.minor_vars.len(), 3);
    assert_eq!(pr.xvs.len(), 2, "two indices in the conclusion");

    // The application spine itself, written out — every other assertion here
    // builds its expectation with `motive_app`, so without this one the
    // convention `app(m, x₀, x₁, t)` would be pinned only by the end-to-end
    // firing test. Three positions, because two cannot tell an order from its
    // reverse.
    let (u, v, w) = (s.zero(), s.unit(), s.point());
    assert_eq!(
        motive_app(&s, &tm, &[u.clone(), v.clone()], &w),
        s.ap.apply(s.ap.apply(s.ap.apply(tm.clone(), u.clone()), v.clone()), w.clone()),
        "the motive takes its indices in order, then the major premise"
    );
    assert_ne!(
        motive_app(&s, &tm, &[u.clone(), v.clone()], &w),
        motive_app(&s, &tm, &[v, u], &w)
    );

    // Field counts: `leaf` none, `red` four fields and two children, `black`
    // six fields and two children.
    assert_eq!(pr.minor_atoms[0].len(), 0);
    assert_eq!(pr.minor_atoms[1].len(), 4 + 2);
    assert_eq!(pr.minor_atoms[2].len(), 6 + 2);
    assert_eq!(pr.minor_vars[1].len(), 4);
    assert_eq!(pr.minor_vars[2].len(), 6);

    for i in 0..3 {
        let c = &b.rb.spec.base.ctors[i];
        let (k, m) = (c.args.len(), c.recs);
        // Split the declared binders back into plains and recs by the mask.
        let (mut ys, mut ts) = (Vec::new(), Vec::new());
        for (q, slot) in c.order.iter().enumerate() {
            match slot {
                Slot::Plain => ys.push(Term::var(pr.minor_vars[i][q])),
                Slot::Rec => ts.push(Term::var(pr.minor_vars[i][q])),
            }
        }
        assert_eq!((ys.len(), ts.len()), (k, m));
        let childs: Vec<Vec<Term>> = (0..m)
            .map(|j| b.rb.spec.rec_index_vec(i, j, &ps, &ys).expect("child indices"))
            .collect();

        // The field atoms, in declared order.
        let (mut plains, mut recs) = (0usize, 0usize);
        for (q, slot) in c.order.iter().enumerate() {
            let want = match slot {
                Slot::Plain => {
                    let mut a = ps.to_vec();
                    a.extend(ys[..plains].iter().cloned());
                    let f = Formula::mem(ys[plains].clone(), Term::apply(c.args[plains], a));
                    plains += 1;
                    f
                }
                Slot::Rec => {
                    let f = Formula::mem(
                        ts[recs].clone(),
                        b.fam.carrier.ty_of(&ps, &childs[recs]).expect("the carrier"),
                    );
                    recs += 1;
                    f
                }
            };
            assert_eq!(pr.minor_atoms[i][q], want, "ctor {i} field {q}");
        }
        // Then one induction hypothesis per recursive field, at that child's
        // **own** indices.
        for j in 0..m {
            assert_eq!(
                pr.minor_atoms[i][k + m + j],
                Formula::mem(pt.clone(), motive_app(&s, &tm, &childs[j], &ts[j])),
                "ctor {i} induction hypothesis {j}"
            );
        }
        // **Which constructor can certify what, and at which spelling** —
        // measured, because prose about this has now been wrong twice.
        //
        // At `derived`'s own spelling the two children are *never* at the same
        // index vector, `red` included: `d⃗ᵢ₀` and `d⃗ᵢ₁` are built from different
        // `FnSym`s, of different arities whenever a plain field sits between the
        // two `Rec` slots (`plains_before`). So every two-child constructor here
        // distinguishes an index-vector swap, and the earlier claim that `red`
        // could not was wrong at this layer — for a different reason than the
        // correction that prompted the check.
        //
        // Once the abbreviations are folded away — the spelling a *consumer*
        // sees — it is `black` that distinguishes them, at `c₁`/`c₂`, and `red`
        // that does not, both children landing on `(b, n)`. That is what the
        // synthetic swapped family below is for.
        if m == 2 {
            assert_ne!(
                childs[0], childs[1],
                "ctor {i}: distinct index symbols even where the values agree"
            );
            assert_ne!(
                pr.minor_atoms[i][k + m],
                pr.minor_atoms[i][k + m + 1],
                "ctor {i}: the two induction hypotheses are distinguishable"
            );
            let (v0, v1) = (b.rec_vals(i, 0, &ys), b.rec_vals(i, 1, &ys));
            assert_eq!(
                v0 != v1,
                i == 2,
                "ctor {i}: after unfolding, only black's children differ"
            );
        }
        // And `MINORᵢ` is that antecedent, quantified in declared order.
        let concl = Formula::mem(
            pt.clone(),
            motive_app(
                &s,
                &tm,
                &b.rb.spec.result_vec(i, &ps, &ys).expect("result indices"),
                &b.ind.ctor_term(&b.f.mach, i, &ys, &ts).expect("the constructor"),
            ),
        );
        let body = match conj_of(&pr.minor_atoms[i]) {
            Some(h) => Formula::imp(h, concl),
            None => concl,
        };
        let want = pr.minor_vars[i]
            .iter()
            .rev()
            .fold(body, |acc, v| Formula::forall(*v, acc));
        assert_eq!(pr.minors[i], want, "MINOR{i}");
    }

    // The conclusion: `∀x⃗ ∀t. (t ∈ ind(α,x⃗) → • ∈ app(m,x⃗,t))`, under `⋀MINORᵢ`.
    let xs: Vec<Term> = pr.xvs.iter().map(|v| Term::var(*v)).collect();
    let tt = Term::var(pr.major);
    let body = Formula::forall(
        pr.major,
        Formula::imp(
            Formula::mem(
                tt.clone(),
                b.fam.carrier.ty_of(&ps, &xs).expect("the carrier"),
            ),
            Formula::mem(pt.clone(), motive_app(&s, &tm, &xs, &tt)),
        ),
    );
    let inner = pr.xvs.iter().rev().fold(body, |acc, v| Formula::forall(*v, acc));
    let want = Formula::forall(
        b.ind.params[0],
        Formula::forall(pr.motive, Formula::imp(pr.hyp.clone(), inner)),
    );
    assert_eq!(*pr.rec.concl(), want);
    assert!(pr.rec.hyps().is_empty(), "unconditional");
    assert_eq!(pr.hyp, conj_of(&pr.minors).expect("three minors"));
}

// ─────────────────────────────────────────────────────────────────────────────
// Firing it, at a concrete motive
// ─────────────────────────────────────────────────────────────────────────────

/// What a constructor owes about its own result indices: given the antecedent
/// and the plain fields' typings at their unfolded sets, the `ni` memberships
/// `H → value(eᵢₖ) ∈ ιₖ`'s value.
type ResMem = dyn Fn(&mut Env, &Built, &Formula, &[Thm]) -> Vec<Thm>;

/// `MINORᵢ` at `α := 1` and a concrete motive, for a constructor with fields.
///
/// `res_mem` is handed the antecedent and the plain fields' typings at their
/// **unfolded** sets, and owes `⊢ H → value(eᵢₖ) ∈ ιₖ`'s value — the only thing
/// that differs between `red` and `black`.
fn fire_minor(
    env: &mut Env,
    b: &Built,
    pr: &IndexedPropRecursor,
    mo: &Motive,
    i: usize,
    res_mem: &ResMem,
) -> Thm {
    let s = b.s().clone();
    let one = b.p();
    let c = &b.rb.spec.base.ctors[i];
    let (k, m) = (c.args.len(), c.recs);

    // The antecedent, at `α := 1` and this motive.
    let atoms: Vec<Formula> = pr.minor_atoms[i]
        .iter()
        .map(|f| f.subst(b.ind.params[0], &one).subst(pr.motive, &mo.m))
        .collect();
    let h = conj_of(&atoms).expect("a constructor with fields");
    let hr = Some(&h);

    // Split the declared binders by the mask, and locate each atom.
    let (mut ys, mut ts) = (Vec::new(), Vec::new());
    let (mut ypos, mut tpos) = (Vec::new(), Vec::new());
    for (q, slot) in c.order.iter().enumerate() {
        match slot {
            Slot::Plain => {
                ys.push(Term::var(pr.minor_vars[i][q]));
                ypos.push(q);
            }
            Slot::Rec => {
                ts.push(Term::var(pr.minor_vars[i][q]));
                tpos.push(q);
            }
        }
    }

    // The plain typings, at the `β` symbols and at their values.
    let mut beta_syms = Vec::with_capacity(k);
    let mut beta_vals = Vec::with_capacity(k);
    for j in 0..k {
        let at = derived::conj_proj(&atoms, ypos[j]).expect("the plain typing");
        beta_syms.push(at.clone());
        let unf = b.beta_unfold(i, j, &ys);
        let y = ys[j].clone();
        beta_vals.push(rw_o(env, hr, &lift(hr, &unf), move |q| Formula::mem(y.clone(), q), &at));
    }

    // The children, weakened to the skeleton.
    let to_skel = eq_symm(env, &inst_all(&b.ind.ty_ax, std::slice::from_ref(&one)).expect("at 1"))
        .expect("symm"); // `W = skel(1)`
    let mut child_skel = Vec::with_capacity(m);
    for j in 0..m {
        let at = derived::conj_proj(&atoms, tpos[j]).expect("the child's typing");
        let childs = b.rb.spec.rec_index_vec(i, j, std::slice::from_ref(&one), &ys).expect("child indices");
        let mut a = vec![one.clone()];
        a.extend(childs);
        a.push(ts[j].clone());
        let in_w = syl(&at, &inst_all(&b.fam.carrier.subset_w, &a).expect("subset")).expect("syl");
        let tj = ts[j].clone();
        child_skel.push(rw_o(
            env,
            hr,
            &lift(hr, &to_skel),
            move |q| Formula::mem(tj.clone(), q),
            &in_w,
        ));
    }

    // The constructor is in the skeleton, hence in `W`.
    let ctor = b.ind.ctor_term(&b.f.mach, i, &ys, &ts).expect("the constructor");
    let ctor_w = {
        let mut a = vec![one.clone()];
        a.extend(ys.iter().cloned());
        a.extend(ts.iter().cloned());
        let mut prem = beta_syms.clone();
        prem.extend(child_skel.iter().cloned());
        let rule = inst_all(&b.ind.ctors[i].mem, &a).expect("the skeleton's ctor rule");
        let in_skel = syl(&conj_under(&prem), &rule).expect("syl");
        let unf = inst_all(&b.ind.ty_ax, std::slice::from_ref(&one)).expect("at 1"); // skel(1) = W
        let cc = ctor.clone();
        rw_o(env, hr, &lift(hr, &unf), move |q| Formula::mem(cc.clone(), q), &in_skel)
    };

    // The motive, at the result indices' **values**.
    let (res, res_eqs) = b.res(i, &ys);
    let vals: Vec<Term> =
        res_eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
    let rm = res_mem(env, b, &h, &beta_vals);
    let chain = mo.compute(
        env,
        &s,
        hr,
        &vals[0],
        &vals[1],
        &ctor,
        &rm[0],
        &rm[1],
        &ctor_w,
    );
    let val_mem = point_in(b, &mo.val);
    let at_vals = mo.holds(env, &s, hr, &chain, &val_mem);

    // Fold the values back onto the index symbols — **one** call to the spine
    // congruence `prop_rec` exports, with the subject reflexive. This is the
    // consumer's move, made the way a consumer is meant to make it.
    let mut eqs: Vec<Thm> =
        res_eqs.iter().map(|e| eq_symm(env, e).expect("symm")).collect();
    eqs.push(Thm::eq_refl(ctor.clone()));
    let congr = motive_congr_of(env, &s, &mo.m, &eqs).expect("the spine congruence");
    assert_eq!(
        *congr.concl(),
        Formula::eq(
            spine3(&s, &mo.m, &vals[0], &vals[1], &ctor),
            spine3(&s, &mo.m, &res[0], &res[1], &ctor)
        ),
        "the congruence moves every index and leaves the subject alone"
    );
    let ptc = s.point();
    let cur = rw_o(
        env,
        hr,
        &lift(hr, &congr),
        move |q| Formula::mem(ptc.clone(), q),
        &at_vals,
    );

    let out = gen_all(&pr.minor_vars[i], &cur);
    assert_eq!(
        *out.concl(),
        pr.minors[i].subst(b.ind.params[0], &one).subst(pr.motive, &mo.m),
        "MINOR{i} as the rule states it"
    );
    out
}

/// Fold `⊢ H → φᵢ` into `⊢ H → ⋀φᵢ`.
fn conj_under(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = derived::hyp_and(t, &acc).expect("hyp_and");
    }
    acc
}

/// `⊢ • ∈ val`, for the two values the tests use: `1` and `∅`.
fn point_in(b: &Built, val: &Term) -> Thm {
    assert_eq!(*val, b.s().unit(), "only the true motive has an inhabited value");
    b.s().unit_mem.clone()
}

/// **The deliverable, fired.** All three minors are discharged at the concrete
/// motive `λc.λn.λt. 1`, and the conclusion comes out at closed terms:
/// `⊢ • ∈ app(app(app(m, b), zero), leaf)`.
///
/// The minors are not decoration: `red`'s needs its `n` at `N` and both children
/// in the skeleton before the motive computes, and `black`'s needs six fields.
#[test]
fn the_rule_fires_at_the_rbtree_spec() {
    let mut env = Env::new();
    let b = build(&mut env);
    let pr = IndexedPropRecursor::over_family(&mut env, &b.f.mach, &b.ind, &b.fam)
        .expect("the Prop-motive rule");
    let s = b.s().clone();
    let one = b.p();
    let mo = motive_of(&mut env, &b, s.unit());

    // `leaf`: no fields, so `MINOR₀` is unconditional.
    let leaf = {
        let (res, res_eqs) = b.res(0, &[]);
        let vals: Vec<Term> =
            res_eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
        let leaf_t = b.leaf();
        let in_w = {
            let rule = inst_all(&b.ind.ctors[0].mem, std::slice::from_ref(&one)).expect("leaf ∈ skel(1)");
            let unf = inst_all(&b.ind.ty_ax, std::slice::from_ref(&one)).expect("at 1");
            let lc = leaf_t.clone();
            rw(&mut env, &unf, move |q| Formula::mem(lc.clone(), q), &rule)
        };
        let chain = mo.compute(
            &mut env,
            &s,
            None,
            &vals[0],
            &vals[1],
            &leaf_t,
            &inj_pt_mem(&b.f.mach, 2, 0),
            &inj_pt_mem(&b.f.mach, 3, 0),
            &in_w,
        );
        let at_vals = mo.holds(&mut env, &s, None, &chain, &point_in(&b, &mo.val));
        let mut eqs: Vec<Thm> =
            res_eqs.iter().map(|e| eq_symm(&mut env, e).expect("symm")).collect();
        eqs.push(Thm::eq_refl(leaf_t.clone()));
        let congr =
            motive_congr_of(&mut env, &s, &mo.m, &eqs).expect("the spine congruence");
        let ptc = s.point();
        let cur = rw(&mut env, &congr, move |q| Formula::mem(ptc.clone(), q), &at_vals);
        let _ = &res;
        assert_eq!(
            *cur.concl(),
            pr.minors[0].subst(b.ind.params[0], &one).subst(pr.motive, &mo.m)
        );
        cur
    };

    // `red`: the first result index is the constant `Color.r`, the second is the
    // plain field `n`, whose typing comes out of the antecedent.
    let red = fire_minor(&mut env, &b, &pr, &mo, 1, &|_env, bb, h, plains| {
        vec![a1i(&inj_pt_mem(&bb.f.mach, 2, 1), h.clone()), plains[0].clone()]
    });
    // `black`: both result indices are constants.
    let black = fire_minor(&mut env, &b, &pr, &mo, 2, &|_env, bb, h, _plains| {
        vec![
            a1i(&inj_pt_mem(&bb.f.mach, 2, 0), h.clone()),
            a1i(&inj_pt_mem(&bb.f.mach, 3, 1), h.clone()),
        ]
    });

    // The rule, at `α := 1` and this motive, with every minor discharged.
    let at = inst_all(&pr.rec, &[one.clone(), mo.m.clone()]).expect("at (1, m)");
    let concl = Thm::mp(&at, &conj_thms(&[leaf, red, black])).expect("the three minors");

    // …and it applies to a real inhabitant.
    let canon = leaf_canon(&mut env, &b);
    let leaf_t = b.leaf();
    let out = Thm::mp(
        &inst_all(&concl, &[b.b(), b.b(), leaf_t.clone()]).expect("at (b, zero, leaf)"),
        &canon,
    )
    .expect("leaf really is in the carrier there");

    assert_eq!(
        *out.concl(),
        Formula::mem(s.point(), motive_app(&s, &mo.m, &[b.b(), b.b()], &leaf_t))
    );
    assert!(out.hyps().is_empty() && closed(out.concl()), "closed and unconditional");
}

/// **The minors are not decoration.** The same nest with its innermost value
/// changed from `1` to `∅` makes `MINOR_leaf` **refutable** — so a rule that
/// held at every motive would be a different, and false, theorem.
#[test]
fn the_leaf_minor_is_refutable_at_a_false_motive() {
    let mut env = Env::new();
    let b = build(&mut env);
    let pr = IndexedPropRecursor::over_family(&mut env, &b.f.mach, &b.ind, &b.fam)
        .expect("the Prop-motive rule");
    let s = b.s().clone();
    let one = b.p();
    let mo = motive_of(&mut env, &b, s.zero());

    let (res, res_eqs) = b.res(0, &[]);
    let vals: Vec<Term> =
        res_eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
    let leaf_t = b.leaf();
    let in_w = {
        let rule = inst_all(&b.ind.ctors[0].mem, std::slice::from_ref(&one)).expect("leaf ∈ skel(1)");
        let unf = inst_all(&b.ind.ty_ax, std::slice::from_ref(&one)).expect("at 1");
        let lc = leaf_t.clone();
        rw(&mut env, &unf, move |q| Formula::mem(lc.clone(), q), &rule)
    };
    let chain = mo.compute(
        &mut env,
        &s,
        None,
        &vals[0],
        &vals[1],
        &leaf_t,
        &inj_pt_mem(&b.f.mach, 2, 0),
        &inj_pt_mem(&b.f.mach, 3, 0),
        &in_w,
    );
    // `• ∉ ∅`, carried back along the computation and then along the spine.
    let empty = inst_all(&s.ap.empty_ax, &[s.point()]).expect("• ∉ ∅");
    let back = eq_symm(&mut env, &chain).expect("symm");
    let ptc = s.point();
    let at_vals =
        rw(&mut env, &back, move |q| Formula::not(Formula::mem(ptc.clone(), q)), &empty);
    let mut eqs: Vec<Thm> =
        res_eqs.iter().map(|e| eq_symm(&mut env, e).expect("symm")).collect();
    eqs.push(Thm::eq_refl(leaf_t.clone()));
    let congr = motive_congr_of(&mut env, &s, &mo.m, &eqs).expect("the spine congruence");
    let ptc = s.point();
    let cur = rw(
        &mut env,
        &congr,
        move |q| Formula::not(Formula::mem(ptc.clone(), q)),
        &at_vals,
    );
    let _ = &res;

    let want = pr.minors[0].subst(b.ind.params[0], &one).subst(pr.motive, &mo.m);
    assert_eq!(*cur.concl(), Formula::not(want));
    assert!(cur.hyps().is_empty() && closed(cur.concl()));
}

/// **The other polarity.** At `(b, Inj₂(•))` — a height no constructor produces
/// — the rule's conclusion is a theorem *outright*, with no minor spent: the
/// carrier is empty there, so `t ∈ ind(1,x⃗) → anything` holds. A rule proved
/// about a family that were constantly inhabited would say something here.
#[test]
fn the_rule_is_vacuous_at_an_index_no_constructor_produces() {
    let mut env = Env::new();
    let b = build(&mut env);
    let pr = IndexedPropRecursor::over_family(&mut env, &b.f.mach, &b.ind, &b.fam)
        .expect("the Prop-motive rule");
    let s = b.s().clone();
    let pv = b.pv();
    let xs = [b.b(), b.two()];

    // One refutation per constructor, at the values, re-folded onto the symbols.
    let mut refutations = Vec::new();
    for i in 0..3 {
        let yvs: Vec<FreeVar> =
            (0..b.rb.spec.base.ctors[i].args.len()).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let (res, eqs) = b.res_at(std::slice::from_ref(&pv), i, &ys);
        let vals: Vec<Term> =
            eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
        let (k, ne) = match i {
            1 => (0usize, b.f.mach.syms.inj_distinct(&mut env, &s, 0, 1).expect("b ≠ r")),
            0 => (1usize, b.f.mach.syms.inj_distinct(&mut env, &s, 2, 0).expect("two ≠ zero")),
            _ => (1usize, b.f.mach.syms.inj_distinct(&mut env, &s, 2, 1).expect("two ≠ succ")),
        };
        let ne_at = inst_all(&ne, &[s.point(), s.point()]).expect("at •");
        let at_vals = syl(&tup_proj(&s, &xs, &vals, k), &ne_at).expect("the components differ");
        let fold = tup_congr(&mut env, &s, &eqs);
        let tx = IndexedDeclSpec::tup(&s, &xs);
        let at_syms = rw_back(
            &mut env,
            &fold,
            move |hole| Formula::not(Formula::eq(tx.clone(), hole)),
            &at_vals,
        );
        assert_eq!(
            *at_syms.concl(),
            Formula::not(Formula::eq(
                IndexedDeclSpec::tup(&s, &xs),
                IndexedDeclSpec::tup(&s, &res)
            ))
        );
        refutations.push(gen_all(&yvs, &at_syms));
    }

    let empty = empty_at_index(
        &mut env,
        &b.f.mach,
        &b.ind,
        &b.rb.spec,
        &b.fam.ix,
        &b.fam.gv,
        &b.fam.gs,
        &b.fam.good,
        &b.fam.carrier,
        &b.f.rc,
        &xs,
        &refutations,
    )
    .expect("the carrier is empty at (b, two)");

    // The formula the rule would *deliver* at this index — read off the rule
    // itself, so it cannot drift from what the theorem says — proved here with
    // no minor spent at all.
    let mv = env.fresh_var();
    let tm = Term::var(mv);
    let at = inst_all(&pr.rec, &[b.p(), tm.clone()]).expect("at (1, m)");
    let (_, all) = at.concl().as_imp().expect("an implication");
    let mut delivered = all;
    for x in xs.iter() {
        delivered = Thm::ax_inst(delivered, x.clone())
            .expect("the conclusion quantifies over the indices")
            .concl()
            .as_imp()
            .expect("an implication")
            .1;
    }

    let tv = env.fresh_var();
    let tt = Term::var(tv);
    let vac = {
        let no = inst_all(&inst_all(&empty, &[b.p()]).expect("at 1"), std::slice::from_ref(&tt))
            .expect("at t");
        let ex = derived::ex_falso(Formula::mem(s.point(), motive_app(&s, &tm, &xs, &tt)));
        Thm::gen(tv, &syl(&no, &ex).expect("syl"))
    };
    assert_eq!(
        *vac.concl(),
        delivered,
        "the rule's conclusion at this index, proved without a single minor"
    );
    assert!(vac.hyps().is_empty());
    assert_ne!(b.fam_at(&xs), b.fam_at(&[b.b(), b.b()]));
}

// ─────────────────────────────────────────────────────────────────────────────
// The congruence along the motive's spine
// ─────────────────────────────────────────────────────────────────────────────

/// **Every position of the spine moves, and each equation lands on its own
/// node.** Four nodes — three indices and the subject — with four pairwise
/// different terms on each side, because a positional claim about a curried
/// spine is invisible at two arguments and only barely visible at three.
///
/// The expectation is [`spine4`], written out; building it with `motive_app`
/// would test the fold against itself.
#[test]
fn the_motive_spine_congruence_moves_every_position() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let ap = s.ap.clone();
    let tm = Term::var(env.fresh_var());

    // Four pairwise different values, and a 0-ary symbol for each.
    let vals = [
        s.unit(),
        f.mach.syms.inj(0, s.point()).expect("Inj₀"),
        f.mach.syms.inj(1, s.point()).expect("Inj₁"),
        f.mach.syms.inj(2, s.point()).expect("Inj₂"),
    ];
    for i in 0..4 {
        for j in i + 1..4 {
            assert_ne!(vals[i], vals[j], "the four values are distinguishable");
        }
    }
    let mut syms = Vec::new();
    let mut eqs = Vec::new();
    for v in vals.iter() {
        let (sym, ax) = abbrev(&mut env, 0, |_| v.clone());
        syms.push(Term::apply(sym, vec![]));
        eqs.push(ax);
    }

    // The scheme's antecedent pairs the *left* spine with the *right* one, in
    // that order — which is what the quantifier prefix has to deliver.
    let rule = motive_congr(&mut env, &s, 3).expect("the scheme at three indices");
    let mut args = vec![tm.clone()];
    args.extend(syms.iter().cloned());
    args.extend(vals.iter().cloned());
    let at = inst_all(&rule, &args).expect("instantiate");
    let (ante, _) = at.concl().as_imp().expect("an implication");
    assert_eq!(
        ante,
        conj_of(&(0..4)
            .map(|k| Formula::eq(syms[k].clone(), vals[k].clone()))
            .collect::<Vec<_>>())
        .expect("four equations")
    );

    // …and the applied form, against a hand-written spine.
    let out = motive_congr_of(&mut env, &s, &tm, &eqs).expect("the congruence");
    let lhs = spine4(&s, &tm, &syms[0], &syms[1], &syms[2], &syms[3]);
    let rhs = spine4(&s, &tm, &vals[0], &vals[1], &vals[2], &vals[3]);
    assert_eq!(*out.concl(), Formula::eq(lhs.clone(), rhs.clone()));
    assert!(out.hyps().is_empty());

    // Nothing weaker and nothing permuted would do.
    assert_ne!(
        rhs,
        spine4(&s, &tm, &vals[0], &vals[2], &vals[1], &vals[3]),
        "two index nodes transposed"
    );
    assert_ne!(
        rhs,
        spine4(&s, &tm, &vals[3], &vals[0], &vals[1], &vals[2]),
        "the subject rotated to the front"
    );
    assert_ne!(
        rhs,
        spine4(&s, &tm, &vals[0], &vals[1], &vals[2], &syms[3]),
        "a fold that stops before the subject"
    );
    assert_ne!(
        rhs,
        spine4(&s, &tm, &syms[0], &syms[1], &syms[2], &vals[3]),
        "a fold that moves only the subject"
    );

    // The degenerate ends: no indices at all, and a wholly reflexive call.
    let only_subject =
        motive_congr_of(&mut env, &s, &tm, std::slice::from_ref(&eqs[0])).expect("ni = 0");
    assert_eq!(
        *only_subject.concl(),
        Formula::eq(
            ap.apply(tm.clone(), syms[0].clone()),
            ap.apply(tm.clone(), vals[0].clone())
        )
    );
    let refls: Vec<Thm> = syms.iter().map(|x| Thm::eq_refl(x.clone())).collect();
    let noop = motive_congr_of(&mut env, &s, &tm, &refls).expect("a reflexive no-op");
    assert_eq!(*noop.concl(), Formula::eq(lhs.clone(), lhs));

    // And what it refuses.
    assert!(motive_congr_of(&mut env, &s, &tm, &[]).is_none(), "no subject equation");
    assert!(
        motive_congr_of(&mut env, &s, &tm, std::slice::from_ref(&s.unit_mem)).is_none(),
        "a membership is not an equation"
    );
}

/// `Γ ⊢ φ` for `Γ = {γ}` — a theorem carrying a *sequent* hypothesis, which is
/// the shape a β down a constructor's λ-nest arrives in and is a different thing
/// from an implication antecedent.
fn under_scope(gamma: &Formula, t: &Thm) -> Thm {
    Thm::mp(&a1i(t, gamma.clone()), &Thm::assume(gamma.clone())).expect("mp")
}

/// **An equation may carry the caller's own `Γ`, and the result carries exactly
/// that and nothing else.**
///
/// The minor's subject equation is a β down the constructor's λ-nest and comes
/// with that nest's scope assumptions as a sequent; refusing it forced a second
/// copy of this fold into `mini`. What the relax must *not* do is buy a
/// `Γ`-carrying input any leniency about the fold, so the conclusion is pinned
/// against a hand-written spine here exactly as on the unconditional path.
#[test]
fn the_spine_congruence_takes_the_callers_sequent_and_adds_none() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let s = f.mach.wt.sums.clone();
    let tm = Term::var(env.fresh_var());

    let vals = [
        s.unit(),
        f.mach.syms.inj(0, s.point()).expect("Inj₀"),
        f.mach.syms.inj(1, s.point()).expect("Inj₁"),
        f.mach.syms.inj(2, s.point()).expect("Inj₂"),
    ];
    let mut syms = Vec::new();
    let mut plain = Vec::new();
    for v in vals.iter() {
        let (sym, ax) = abbrev(&mut env, 0, |_| v.clone());
        syms.push(Term::apply(sym, vec![]));
        plain.push(ax);
    }

    // Two scopes, on an index position and on the **subject** — the position
    // that actually needs this, since the constructor's β is the one carrying a
    // nest's assumptions.
    let g1 = Formula::mem(Term::var(env.fresh_var()), s.unit());
    let g2 = Formula::mem(Term::var(env.fresh_var()), vals[1].clone());
    assert_ne!(g1, g2);
    let eqs = vec![
        plain[0].clone(),
        under_scope(&g1, &plain[1]),
        plain[2].clone(),
        under_scope(&g2, &plain[3]),
    ];

    let out = motive_congr_of(&mut env, &s, &tm, &eqs).expect("a sequent is not a refusal");
    assert_eq!(
        *out.concl(),
        Formula::eq(
            spine4(&s, &tm, &syms[0], &syms[1], &syms[2], &syms[3]),
            spine4(&s, &tm, &vals[0], &vals[1], &vals[2], &vals[3])
        ),
        "the fold is guarded no less than on the unconditional path"
    );

    // Exactly the caller's own `Γ`: both present, and nothing else.
    let mut got: Vec<Formula> = out.hyps().to_vec();
    let mut want = vec![g1.clone(), g2.clone()];
    got.sort_unstable();
    want.sort_unstable();
    assert_eq!(got, want, "the union of the inputs' sequents, and no more");

    // The unconditional path did not become conditional.
    let clean = motive_congr_of(&mut env, &s, &tm, &plain).expect("all unconditional");
    assert!(clean.hyps().is_empty());
    assert_eq!(clean.concl(), out.concl(), "same equation, fewer assumptions");

    // A sequent buys nothing else: a non-equation under a scope is still refused.
    let not_an_eq = under_scope(&g1, &s.unit_mem);
    assert!(
        motive_congr_of(&mut env, &s, &tm, &[plain[0].clone(), not_an_eq]).is_none(),
        "a membership under a scope is still not an equation"
    );
    // …and so is a scope on an otherwise empty list.
    assert!(motive_congr_of(&mut env, &s, &tm, &[]).is_none());
}

/// **The constructor moved out of an *argument*.** A consumer's minor premise
/// arrives with the index expressions at their interpretations *and* the
/// constructor at its own spelling; both sit inside `app(m, …)`'s spine, so
/// neither is reachable by a subject retarget.
///
/// Here `MINOR_leaf` is produced at the concrete motive starting from a
/// `leaf` **abbreviation** and the index values, and one call to
/// `motive_congr_of` moves all three positions at once onto the spelling the
/// rule states — checked against `IndexedPropRecursor::minors` itself.
#[test]
fn the_spine_congruence_moves_a_constructor_out_of_an_argument() {
    let mut env = Env::new();
    let b = build(&mut env);
    let pr = IndexedPropRecursor::over_family(&mut env, &b.f.mach, &b.ind, &b.fam)
        .expect("the Prop-motive rule");
    let s = b.s().clone();
    let one = b.p();
    let mo = motive_of(&mut env, &b, s.unit());
    let leaf_t = b.leaf();

    // The consumer's spelling: an abbreviation for the constructor term.
    let (ls, ls_ax) = abbrev(&mut env, 0, |_| leaf_t.clone());
    let lt = Term::apply(ls, vec![]);
    assert_ne!(lt, leaf_t, "the abbreviation is a different term");

    let in_w = {
        let rule = inst_all(&b.ind.ctors[0].mem, std::slice::from_ref(&one)).expect("leaf ∈ skel(1)");
        let unf = inst_all(&b.ind.ty_ax, std::slice::from_ref(&one)).expect("at 1");
        let lc = leaf_t.clone();
        let at_leaf = rw(&mut env, &unf, move |q| Formula::mem(lc.clone(), q), &rule);
        let (_, w) = at_leaf.concl().as_mem().expect("a membership");
        rw_back(&mut env, &ls_ax, move |q| Formula::mem(q, w.clone()), &at_leaf)
    };

    // `• ∈ app(app(app(m, b), zero), ls)` — at the values and the abbreviation.
    let (res, res_eqs) = b.res(0, &[]);
    let vals: Vec<Term> =
        res_eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
    let chain = mo.compute(
        &mut env,
        &s,
        None,
        &vals[0],
        &vals[1],
        &lt,
        &inj_pt_mem(&b.f.mach, 2, 0),
        &inj_pt_mem(&b.f.mach, 3, 0),
        &in_w,
    );
    let at_vals = mo.holds(&mut env, &s, None, &chain, &point_in(&b, &mo.val));
    assert_eq!(
        *at_vals.concl(),
        Formula::mem(s.point(), spine3(&s, &mo.m, &vals[0], &vals[1], &lt))
    );

    // One congruence: two index positions and the subject, all at once.
    let eqs = vec![
        eq_symm(&mut env, &res_eqs[0]).expect("symm"),
        eq_symm(&mut env, &res_eqs[1]).expect("symm"),
        ls_ax.clone(),
    ];
    let congr = motive_congr_of(&mut env, &s, &mo.m, &eqs).expect("the spine congruence");
    assert_eq!(
        *congr.concl(),
        Formula::eq(
            spine3(&s, &mo.m, &vals[0], &vals[1], &lt),
            spine3(&s, &mo.m, &res[0], &res[1], &leaf_t)
        )
    );

    let ptc = s.point();
    let out = rw(&mut env, &congr, move |q| Formula::mem(ptc.clone(), q), &at_vals);
    assert_eq!(
        *out.concl(),
        pr.minors[0].subst(b.ind.params[0], &one).subst(pr.motive, &mo.m),
        "MINOR_leaf, exactly as the rule states it"
    );
    assert!(out.hyps().is_empty() && closed(out.concl()));
}

// ─────────────────────────────────────────────────────────────────────────────
// A synthetic family whose children sit at swapped indices
// ─────────────────────────────────────────────────────────────────────────────

/// `Sw : Πα. N → N → Sort`, two indices over the **same** type so the swap is
/// expressible:
///
/// ```text
/// nil                 : Sw α zero zero
/// sw  a l b r         : Sw α b a        l at (a, zero),  r at (zero, a)
/// ```
///
/// Why a synthetic shape at all: `red`'s two children unfold to the *same*
/// vector `(b, n)`, so `red` cannot tell an induction hypothesis stated at its
/// own child's indices from one stated at the other's once the abbreviations
/// are folded away. `black` can, at `c₁`/`c₂`, so the *declaration* is not
/// blind — only that constructor is. What neither supplies is a **reversal**:
/// here the two child vectors are each other's reverse and differ from the
/// result, so the claim rests on a shape chosen for it rather than on a
/// coincidence of the corpus.
fn swapped(env: &mut Env, mach: &Machine) -> (IndexedDeclSpec, Vec<Vec<Thm>>) {
    let s = &mach.wt.sums;
    let pt = s.point();
    let nat = mach.syms.finord(s, 3).expect("finord(3)");
    let zero = mach.syms.inj(0, pt.clone()).expect("Inj₀");

    let (i0, _) = abbrev(env, 1, |_| nat.clone());
    let (i1, _) = abbrev(env, 2, |_| nat.clone());
    let (a0, _) = abbrev(env, 1, |_| nat.clone());
    let (a1, _) = abbrev(env, 2, |_| nat.clone());

    let base = DeclSpec::new(
        1,
        vec![
            CtorSpec::nullary(),
            CtorSpec::with_order(
                vec![a0, a1],
                2,
                vec![Slot::Plain, Slot::Rec, Slot::Plain, Slot::Rec],
            )
            .expect("sw's mask"),
        ],
    );

    let mk = |env: &mut Env, arity: usize, pick: Option<usize>, k: Term| match pick {
        None => abbrev(env, arity, move |_| k.clone()),
        Some(i) => abbrev(env, arity, move |a: &[Term]| a[i].clone()),
    };
    let (n0, _) = mk(env, 1, None, zero.clone());
    let (n1, _) = mk(env, 1, None, zero.clone());
    let nil = CtorIndices::nonrecursive(vec![n0, n1]);

    // `l` at `(a, zero)`; `r` at `(zero, a)`; the result at `(b, a)`.
    let (d00, d00a) = mk(env, 2, Some(1), pt.clone());
    let (d01, d01a) = mk(env, 2, None, zero.clone());
    let (d10, d10a) = mk(env, 3, None, zero.clone());
    let (d11, d11a) = mk(env, 3, Some(1), pt.clone());
    let (r0, _) = mk(env, 3, Some(2), pt.clone());
    let (r1, _) = mk(env, 3, Some(1), pt.clone());
    let sw = CtorIndices {
        result: vec![r0, r1],
        rec_args: vec![vec![d00, d01], vec![d10, d11]],
    };

    (
        IndexedDeclSpec::new(base, vec![i0, i1], vec![nil, sw]),
        vec![vec![d00a, d01a], vec![d10a, d11a]],
    )
}

/// **Each induction hypothesis is paired with its own child, at its own
/// index.** Three distinct index vectors — `(a, zero)`, `(zero, a)` and
/// `(b, a)` — so a swap, a shared index or a motive applied in the wrong order
/// all show up.
#[test]
fn the_swapped_child_indices_are_paired_with_their_own_hypotheses() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let (spec, rec_ax) = swapped(&mut env, &mach);
    assert!(spec.well_formed());
    let ind = Inductive::build(&mut env, &mut mach, &spec.base).expect("the skeleton");
    let fam = IndexedInductive::build(&mut env, &mut mach, &ind, &spec, &f.rc, &f.iota, &f.funspace)
        .expect("the indexed family");
    let s = mach.wt.sums.clone();
    let pt = s.point();
    let pr = IndexedPropRecursor::over_family(&mut env, &mach, &ind, &fam)
        .expect("the Prop-motive rule");
    let tm = Term::var(pr.motive);
    let ps = [Term::var(ind.params[0])];

    let vars = &pr.minor_vars[1];
    assert_eq!(vars.len(), 4, "a, l, b, r — in declared order");
    let (a, l, bb, r) = (
        Term::var(vars[0]),
        Term::var(vars[1]),
        Term::var(vars[2]),
        Term::var(vars[3]),
    );
    let ys = [a.clone(), bb.clone()];
    let ts = [l.clone(), r.clone()];

    let d0 = spec.rec_index_vec(1, 0, &ps, &ys).expect("l's indices");
    let d1 = spec.rec_index_vec(1, 1, &ps, &ys).expect("r's indices");
    let e = spec.result_vec(1, &ps, &ys).expect("the result indices");
    // Three different index vectors — the whole point of the shape.
    assert_ne!(d0, d1);
    assert_ne!(d0, e);
    assert_ne!(d1, e);
    // …and they stay different **after unfolding**, in swapped order, which is
    // the spelling a consumer works at and the one `RBTree.red` cannot supply:
    // its two children both land on `(b, n)`.
    let unfold = |k: usize, j: usize, args: &[Term]| {
        inst_all(&rec_ax[k][j], args).expect("unfold").concl().as_eq().expect("eq").1
    };
    let v0 = [unfold(0, 0, &[ps[0].clone(), a.clone()]), unfold(0, 1, &[ps[0].clone(), a.clone()])];
    let v1 = [
        unfold(1, 0, &[ps[0].clone(), a.clone(), bb.clone()]),
        unfold(1, 1, &[ps[0].clone(), a.clone(), bb.clone()]),
    ];
    assert_ne!(v0, v1, "the children's index values differ, not only their symbols");
    assert_eq!(v0[0], v1[1], "and they are each other's reverse");
    assert_eq!(v0[1], v1[0]);
    assert_ne!(
        fam.carrier.ty_of(&ps, &d0).expect("l's type"),
        fam.carrier.ty_of(&ps, &d1).expect("r's type"),
        "the two children are typed at different index vectors"
    );

    let atoms = &pr.minor_atoms[1];
    assert_eq!(atoms.len(), 4 + 2);
    // Declared order: a, l, b, r.
    assert_eq!(atoms[0], Formula::mem(a.clone(), Term::apply(spec.base.ctors[1].args[0], ps.to_vec())));
    assert_eq!(atoms[1], Formula::mem(l.clone(), fam.carrier.ty_of(&ps, &d0).expect("ty")));
    assert_eq!(
        atoms[2],
        Formula::mem(bb.clone(), Term::apply(spec.base.ctors[1].args[1], vec![ps[0].clone(), a.clone()]))
    );
    assert_eq!(atoms[3], Formula::mem(r.clone(), fam.carrier.ty_of(&ps, &d1).expect("ty")));
    // Then the induction hypotheses, each at its own child's indices.
    assert_eq!(atoms[4], Formula::mem(pt.clone(), motive_app(&s, &tm, &d0, &l)));
    assert_eq!(atoms[5], Formula::mem(pt.clone(), motive_app(&s, &tm, &d1, &r)));
    // Swapping either the pairing or the index order would give a different
    // formula — pinned, so that the assertions above cannot be satisfied by an
    // accident of symmetry.
    assert_ne!(atoms[4], Formula::mem(pt.clone(), motive_app(&s, &tm, &d1, &l)));
    assert_ne!(atoms[5], Formula::mem(pt.clone(), motive_app(&s, &tm, &d0, &r)));
    assert_ne!(
        atoms[4],
        Formula::mem(pt.clone(), motive_app(&s, &tm, &[d0[1].clone(), d0[0].clone()], &l))
    );

    // And the conclusion is at the result indices, in their own order.
    let concl = Formula::mem(
        pt.clone(),
        motive_app(&s, &tm, &e, &ind.ctor_term(&mach, 1, &ys, &ts).expect("sw")),
    );
    let want = vars.iter().rev().fold(
        Formula::imp(conj_of(atoms).expect("six atoms"), concl),
        |acc, v| Formula::forall(*v, acc),
    );
    assert_eq!(pr.minors[1], want);
}

// ─────────────────────────────────────────────────────────────────────────────
// What it refuses
// ─────────────────────────────────────────────────────────────────────────────

/// The rule is for **indexed** class-(T) families over their own skeleton; a
/// family built over one machine is not a rule about another declaration's.
#[test]
fn the_rule_refuses_a_foreign_skeleton() {
    let mut env = Env::new();
    let b = build(&mut env);
    // A second declaration over the same machine: `Bool`, two nullary
    // constructors and no indices. Its skeleton is not `RBTree`'s.
    let mut mach = b.f.mach;
    let other = DeclSpec::new(1, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let other_ind = Inductive::build(&mut env, &mut mach, &other).expect("the other skeleton");
    assert!(
        IndexedPropRecursor::over_family(&mut env, &mach, &other_ind, &b.fam).is_none(),
        "a family and a skeleton from two declarations do not make a rule"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The value motive: the indexed guarded minors
// ─────────────────────────────────────────────────────────────────────────────

/// **The guard tests the *indexed* induction hypothesis, and `HYP` comes out.**
///
/// `psiᵢ` is the two things `minor_typedᵢ`'s antecedent does not carry — the
/// recursive fields at `ind(p⃗, d⃗ᵢⱼ)` rather than at `W`, and the induction
/// hypotheses at the motive's *own index vector* — and both are taken from the
/// same `minor_atoms_at` builder the `Prop` rule uses, so `IDEPᵢ`'s antecedent
/// and the guard cannot drift.
#[test]
fn the_indexed_guard_discharges_the_recursors_hypothesis() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let n = 3;
    let mv = env.fresh_var();
    let minors: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
    let tv = env.fresh_var();
    let g = IndexedGuardedMinors::build(
        &mut env, &b.f.mach, &b.ind, &b.rb.spec, &b.fam.carrier, mv, &minors, tv,
    )
    .expect("the indexed guarded minors");

    assert_eq!(g.terms.len(), n);
    assert_eq!(g.guard_atoms.len(), n);
    // `leaf` has no recursive arguments, so it needs no guard and `gmin₀` *is*
    // `S₀`; `red` and `black` have two each, so four guard atoms apiece.
    assert!(g.fires[0].is_none());
    assert_eq!(g.terms[0], Term::var(minors[0]));
    assert_eq!(g.guard_atoms[0].len(), 0);
    for i in [1usize, 2] {
        assert!(g.fires[i].is_some(), "ctor {i} is guarded");
        assert_eq!(g.guard_atoms[i].len(), 4, "two children, two hypotheses");
        assert_ne!(g.terms[i], Term::var(minors[i]), "ctor {i}'s minor is wrapped");
    }

    // The guard is `minor_atoms_at`'s entries, not a restatement of them.
    let ps = [b.pv()];
    let tm = Term::var(mv);
    for i in [1usize, 2] {
        let (yvs, tvs, vvs) = &g.vars[i];
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let ts: Vec<Term> = tvs.iter().map(|v| Term::var(*v)).collect();
        let vs: Vec<Term> = vvs.iter().map(|v| Term::var(*v)).collect();
        let want =
            guard_atoms_of(&s, &b.rb.spec, &b.fam.carrier, i, &tm, &ps, &ys, &ts, &vs)
                .expect("the guard atoms");
        assert_eq!(g.guard_atoms[i], want);
        // The two halves say what the header claims.
        for j in 0..2 {
            let d = b.rb.spec.rec_index_vec(i, j, &ps, &ys).expect("child indices");
            assert_eq!(
                g.guard_atoms[i][j],
                Formula::mem(ts[j].clone(), b.fam.carrier.ty_of(&ps, &d).expect("ty")),
                "ctor {i} child {j} at its own index, not at W"
            );
            assert_eq!(
                g.guard_atoms[i][2 + j],
                Formula::mem(vs[j].clone(), motive_app(&s, &tm, &d, &ts[j])),
                "ctor {i} hypothesis {j} at its own index"
            );
        }
        // …and neither is what `minor_typedᵢ` already carries.
        assert_ne!(
            g.guard_atoms[i][0],
            Formula::mem(ts[0].clone(), b.ind.wty.clone()),
            "the guard is stronger than `tⱼ ∈ W`"
        );
    }

    // `PRE` is `ICOD ∧ IDEP`, rebuilt here, and `HYP` follows from it.
    let want_cod = icod(&mut env, &s, &b.ind.wty, 2, &tm, &Term::var(tv));
    assert_eq!(g.cod, want_cod);
    for (i, sv) in minors.iter().enumerate() {
        let want =
            idep_minor(&mut env, &b.f.mach, &b.ind, &b.rb.spec, &b.fam.carrier, i, &tm,
                       &Term::var(*sv))
                .expect("IDEPᵢ");
        assert_eq!(g.dep_parts[i], want);
    }
    let pre = Formula::and(g.cod.clone(), g.dep.clone());
    let (ante, _) = g.hyp.concl().as_imp().expect("an implication");
    assert_eq!(ante, pre);
    assert!(g.hyp.hyps().is_empty(), "unconditional");
    for th in g.fires.iter().flatten() {
        assert!(th.hyps().is_empty());
    }
}
