//! Indexed inductive families, exercised at `RBTree` — the only shape in the
//! tutorial corpus that needs a genuine `good` (`INDEXED-DESIGN.md` §2.2).
//!
//! `RBTree : ∀(α : Sort u+1), Color → N → Sort u+1` has **one parameter, two
//! indices and three constructors**, one of them with the interleaved mask
//! `Plain, Rec, Plain, Rec` and one with six fields. That combination is what
//! the tests below are built from, because every simpler shape hides at least
//! one of the things that can go wrong: a single index hides the tuple spine, a
//! parameterless declaration hides the arity bookkeeping, and a family whose
//! constructors all land at the same index hides `good` entirely.
//!
//! **Both polarities are cashed, and the negative one twice.** A `good` that
//! returned all of `Idx` at every skeleton element would satisfy every
//! membership theorem here; what rules it out is
//!
//! * inversion, at a *wrong* index for a constructor that does exist — `leaf`
//!   is not in the carrier at `(red, zero)`; and
//! * emptiness, at an index **no** constructor can produce, quantified over
//!   every element of the skeleton.
//!
//! Each test rebuilds the formula it expects from the kernel's own
//! constructors, so a theorem with the right name and the wrong shape fails
//! here rather than downstream.
//!
//! # Why the tests are full of unfolding
//!
//! Every index expression reaches `derived/` as a **`FnSym`**, per the
//! convention `inductive/spec.rs` explains: the kernel has `Formula::subst` and
//! no `Term::subst`, so dependence is application. The theorems therefore talk
//! about `e₁₀(α, n, x)`, not about `Color.r`, and a test that wants to
//! *discharge* `e₁₀(1,·,·) ∈ ι₀(1)` has to walk the abbreviation's defining
//! equation to get there. That walk is exactly what a checker does at the
//! boundary, and doing it here is the only way to find out whether the
//! antecedents the theorems carry are dischargeable at all.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::cumul::{
    arg_obligations_at, nullary_summand_at, nullary_summands_in_u1, summand_at, tags_at,
    tags_in_u1, DeclUniverse, IndChain,
};
use derived::inductive::family::{
    empty_at_index, CtorIndices, Good, IndexedDeclSpec, IndexedInductive, IndexedUniverse,
};
use derived::inductive::{CtorSpec, DeclSpec, GenRecursor, Inductive, Machine, Slot};
use derived::isum::finord_in_universe;
use derived::sums::Sums;
use derived::tower::{Cumul, Rung, Tower};
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{
    a1i, and_left, and_right, conj_of, conj_proj, define_abbrev, eq_symm, eq_trans, gen_all,
    imp_refl, inst_all, syl, uncurry,
};

/// A formula with no free variables — an *unconditional, closed* statement.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
}

// ─────────────────────────────────────────────────────────────────────────────
// Rewriting helpers — the boundary work, done by hand
// ─────────────────────────────────────────────────────────────────────────────

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

/// From `⊢ y = x` and `⊢ φ(x)` infer `⊢ φ(y)` — the direction an unfolding
/// equation `f(args) = value` is used in when the *value* side is what holds.
fn rw_back(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let back = eq_symm(env, eq).expect("symm");
    rw(env, &back, ctx, base)
}

/// [`rw_back`] whether or not the base carries an antecedent — the same
/// rewriting step, with `H` present or absent.
fn rw_back_opt(
    env: &mut Env,
    eq: &Thm,
    ctx: impl Fn(Term) -> Formula,
    base: &Thm,
    h: Option<&Formula>,
) -> Thm {
    match h {
        None => rw_back(env, eq, ctx, base),
        Some(_) => {
            let back = eq_symm(env, eq).expect("symm");
            rw_h(env, &back, ctx, base)
        }
    }
}

/// From `⊢ x = y` and `⊢ H → φ(x)` infer `⊢ H → φ(y)`.
fn rw_h(env: &mut Env, eq: &Thm, ctx: impl Fn(Term) -> Formula, base: &Thm) -> Thm {
    let (x, y) = eq.concl().as_eq().expect("an equation");
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(x, y, hole, ctx(Term::var(hole)));
    syl(base, &Thm::mp(&leib, eq).expect("mp")).expect("syl")
}

/// `tup(x⃗) = ⟨x₀,⟨x₁,…,•⟩⟩`, the index tuple.
fn tup(s: &Sums, xs: &[Term]) -> Term { IndexedDeclSpec::tup(s, xs) }

/// From `⊢ uₖ = vₖ` for each `k`, infer `⊢ tup(u⃗) = tup(v⃗)`.
fn tup_congr(env: &mut Env, s: &Sums, eqs: &[Thm]) -> Thm {
    let mut cur = Thm::eq_refl(s.point());
    for eq in eqs.iter().rev() {
        let (_, new) = eq.concl().as_eq().expect("an equation");
        let (old_tail, _) = cur.concl().as_eq().expect("an equation");
        let one = cong(env, eq, |x| s.ap.sets.pair(x, old_tail.clone()));
        let two = cong(env, &cur, |x| s.ap.sets.pair(new.clone(), x));
        cur = eq_trans(env, &one, &two).expect("trans");
    }
    cur
}

/// `⊢ tup(u⃗) = tup(v⃗) → uₖ = vₖ` — walk `k` steps down the tuple spine with
/// Kuratowski injectivity, then take the head.
fn tup_proj(s: &Sums, us: &[Term], vs: &[Term], k: usize) -> Thm {
    let ap = &s.ap;
    let mut cur = imp_refl(Formula::eq(tup(s, us), tup(s, vs)));
    for lvl in 0..=k {
        let (tu, tv) = (tup(s, &us[lvl + 1..]), tup(s, &vs[lvl + 1..]));
        let inj = inst_all(
            &ap.pair_inj,
            &[us[lvl].clone(), tu.clone(), vs[lvl].clone(), tv.clone()],
        )
        .expect("pair injectivity");
        let both = syl(&cur, &inj).expect("syl");
        let (l, r) =
            (Formula::eq(us[lvl].clone(), vs[lvl].clone()), Formula::eq(tu, tv));
        cur = if lvl == k {
            syl(&both, &and_left(l, r)).expect("head")
        } else {
            syl(&both, &and_right(l, r)).expect("tail")
        };
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

fn fixture_over(env: &mut Env, mut mach: Machine) -> Fix {
    // `finord(3)` and `Inj₀ … Inj₂` — the index types below are built from
    // them, before any declaration is translated.
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

fn fixture(env: &mut Env) -> Fix {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mach = Machine::over(env, wt, bnd).expect("machine");
    fixture_over(env, mach)
}

/// A symbol of the given arity whose value is `body` — how a checker turns a
/// Lean expression into the `FnSym` the spec convention wants.
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

/// Right-nested conjunction of closed theorems, matching `conj_of`.
fn conj_thms(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = derived::and_intro(t, &acc);
    }
    acc
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

/// `RBTree`, as an [`IndexedDeclSpec`].
///
/// Faithful in every respect the derived layer can see: one parameter, two
/// indices, three constructors, `red`'s mask `Plain, Rec, Plain, Rec`,
/// `black`'s six fields with two `Color`s and a `N` before its recursive
/// arguments, and the index expressions decoded from `042_rbTreeDef`:
///
/// ```text
/// leaf                : RBTree α  b  zero
/// red   n l x r       : RBTree α  r  n           l, r at (b, n)
/// black c₁ c₂ n l x r : RBTree α  b  (succ n)    l at (c₁,n), r at (c₂,n)
/// ```
///
/// `Color := finord(2)` with `b = Inj₀(•)`, `r = Inj₁(•)`; `N := finord(3)`
/// with `zero = Inj₀(•)` and a **constant** `succ := Inj₁(•)`. The successor
/// being constant simplifies the index *arithmetic*, not the index
/// *structure*: what the tests need of it is that it lies in `N` and differs
/// from `zero`, and a genuine successor would add nothing this module can see,
/// since every index expression arrives as an opaque `FnSym` either way.
fn rbtree(env: &mut Env, mach: &Machine) -> Rb {
    let s = &mach.wt.sums;
    let pt = s.point();
    let color = mach.syms.finord(s, 2).expect("finord(2)");
    let nat = mach.syms.finord(s, 3).expect("finord(3)");
    let b = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let r = mach.syms.inj(1, pt.clone()).expect("Inj₁");

    let (i0, i0_ax) = abbrev(env, 1, |_| color.clone());
    let (i1, i1_ax) = abbrev(env, 2, |_| nat.clone());

    let (rb0, rb0_ax) = abbrev(env, 1, |_| nat.clone()); // red's   n : N
    let (rb1, rb1_ax) = abbrev(env, 2, |a| a[0].clone()); // red's   x : α
    let (bb0, bb0_ax) = abbrev(env, 1, |_| color.clone()); // black's c₁
    let (bb1, bb1_ax) = abbrev(env, 2, |_| color.clone()); // black's c₂
    let (bb2, bb2_ax) = abbrev(env, 3, |_| nat.clone()); // black's n
    let (bb3, bb3_ax) = abbrev(env, 4, |a| a[0].clone()); // black's x : α

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

    // The index expressions: `mk(arity, None, k)` is the constant `k`,
    // `mk(arity, Some(i), _)` is the `i`-th argument.
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
    let red_idx = CtorIndices {
        result: vec![r0, r1],
        rec_args: vec![vec![d00, d01], vec![d10, d11]],
    };

    let (k0, k0a) = mk(env, 5, None, b.clone());
    let (k1, k1a) = mk(env, 5, None, r.clone());
    let (e00, e00a) = mk(env, 4, Some(1), pt.clone());
    let (e01, e01a) = mk(env, 4, Some(3), pt.clone());
    let (e10, e10a) = mk(env, 5, Some(2), pt.clone());
    let (e11, e11a) = mk(env, 5, Some(3), pt.clone());
    let black_idx = CtorIndices {
        result: vec![k0, k1],
        rec_args: vec![vec![e00, e01], vec![e10, e11]],
    };

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

/// The spec, the skeleton and the family.
struct Built {
    f: Fix,
    rb: Rb,
    ind: Inductive,
    fam: IndexedInductive,
}

fn build_over(env: &mut Env, f: Fix) -> Built {
    let mut mach = f.mach;
    let rb = rbtree(env, &mach);
    assert!(rb.spec.well_formed(), "the RBTree spec is well formed");
    let ind = Inductive::build(env, &mut mach, &rb.spec.base).expect("the skeleton");
    let fam = IndexedInductive::build(env, &mut mach, &ind, &rb.spec, &f.rc, &f.iota, &f.funspace)
        .expect("the indexed family");
    Built { f: Fix { mach, ..f }, rb, ind, fam }
}

fn build(env: &mut Env) -> Built {
    let f = fixture(env);
    build_over(env, f)
}

impl Built {
    fn s(&self) -> &Sums { &self.f.mach.wt.sums }
    /// `α := 1`.
    fn p(&self) -> Term { self.s().unit() }
    /// `Color.b = N.zero = Inj₀(•)`.
    fn b(&self) -> Term { self.f.mach.syms.inj(0, self.s().point()).expect("Inj₀") }
    /// `Color.r = succ = Inj₁(•)`.
    fn r(&self) -> Term { self.f.mach.syms.inj(1, self.s().point()).expect("Inj₁") }
    /// `Inj₂(•)`, a height no constructor produces.
    fn two(&self) -> Term { self.f.mach.syms.inj(2, self.s().point()).expect("Inj₂") }
    fn leaf(&self) -> Term { self.ind.ctor_term(&self.f.mach, 0, &[], &[]).expect("leaf") }
    /// `ind(1, x⃗)`.
    fn fam_at(&self, xs: &[Term]) -> Term {
        self.fam.carrier.ty_of(&[self.p()], xs).expect("the carrier")
    }
    /// The declaration's parameter variable — what the theorems that are *not*
    /// `∀`-closed over the parameters are stated at.
    fn pv(&self) -> Term { Term::var(self.ind.params[0]) }
    /// `e⃗ᵢ(p, y⃗)` as symbol applications, with their unfolding equations.
    fn res_at(&self, ps: &[Term], i: usize, ys: &[Term]) -> (Vec<Term>, Vec<Thm>) {
        let ts = self.rb.spec.result_vec(i, ps, ys).expect("result indices");
        let mut args = ps.to_vec();
        args.extend(ys.iter().cloned());
        let eqs =
            self.rb.res_ax[i].iter().map(|ax| inst_all(ax, &args).expect("unfold")).collect();
        (ts, eqs)
    }
    /// The same at `α := 1`.
    fn res(&self, i: usize, ys: &[Term]) -> (Vec<Term>, Vec<Thm>) {
        self.res_at(&[self.p()], i, ys)
    }
    /// `d⃗ᵢⱼ(1, y⃗)` and their unfolding equations.
    fn rec(&self, i: usize, j: usize, ys: &[Term]) -> (Vec<Term>, Vec<Thm>) {
        let ps = [self.p()];
        let pb = self.rb.spec.plains_before(i, j).expect("a Rec slot");
        let ts = self.rb.spec.rec_index_vec(i, j, &ps, ys).expect("child indices");
        let mut args = ps.to_vec();
        args.extend(ys[..pb].iter().cloned());
        let eqs =
            self.rb.rec_ax[i][j].iter().map(|ax| inst_all(ax, &args).expect("unfold")).collect();
        (ts, eqs)
    }
    /// `⊢ yⱼ ∈ βⱼ(1, y<ⱼ)`, from a membership at the argument type's *value*.
    fn beta_typing(&self, env: &mut Env, i: usize, j: usize, ys: &[Term], val: &Thm) -> Thm {
        let mut args = vec![self.p()];
        args.extend(ys[..j].iter().cloned());
        let eq = inst_all(&self.rb.beta_ax[i][j], &args).expect("unfold");
        let y = ys[j].clone();
        rw_back(env, &eq, move |x| Formula::mem(y.clone(), x), val)
    }
}

/// Rewrite the index arguments of `⊢ z ∈ ind(1, x⃗)` along `eqs[k] : xₖ = x′ₖ`.
fn rw_index(env: &mut Env, b: &Built, z: &Term, xs: &[Term], eqs: &[Thm], base: &Thm) -> Thm {
    let (ty, p) = (b.fam.carrier.ty, b.p());
    let mut cur = base.clone();
    let mut ix = xs.to_vec();
    for (k, eq) in eqs.iter().enumerate() {
        let (_, new) = eq.concl().as_eq().expect("an equation");
        let (shape, zc, pc) = (ix.clone(), z.clone(), p.clone());
        cur = rw(
            env,
            eq,
            move |hole| {
                let mut a = vec![pc.clone()];
                let mut s = shape.clone();
                s[k] = hole;
                a.extend(s);
                Formula::mem(zc.clone(), Term::apply(ty, a))
            },
            &cur,
        );
        ix[k] = new;
    }
    cur
}

/// `⊢ [H →] eᵢₖ(p⃗,y⃗) ∈ ιₖ(p⃗, e⃗<ₖ)` — the result-index typings, which are (M)'s
/// extra antecedent (`family/carrier.rs`'s header explains why they are there)
/// and which [`IndexedCtor::mem_lean`] takes as its input.
///
/// `vals[k]` is `⊢ [H →] eᵢₖ(p⃗,y⃗)'s value ∈ finord(mₖ)`; everything else here
/// is folding the two abbreviations — the index expression and the index type
/// — back onto the symbols the theorems are stated over.
fn index_typings_at(
    env: &mut Env,
    b: &Built,
    ps: &[Term],
    i: usize,
    ys: &[Term],
    h: Option<&Formula>,
    vals: &[Thm],
) -> Vec<Thm> {
    let (res, res_eqs) = b.res_at(ps, i, ys);
    let mut out = Vec::with_capacity(res.len());
    for k in 0..res.len() {
        let mut ia = ps.to_vec();
        ia.extend(res[..k].iter().cloned());
        let set = Term::apply(b.rb.spec.indices[k], ia.clone());
        let ity = inst_all(&b.rb.ity_ax[k], &ia).expect("the index type unfolds");
        let (_, value) = res_eqs[k].concl().as_eq().expect("an equation");
        let at_set =
            rw_back_opt(env, &ity, move |x| Formula::mem(value.clone(), x), &vals[k], h);
        let s2 = set.clone();
        out.push(rw_back_opt(env, &res_eqs[k], move |x| Formula::mem(x, s2.clone()), &at_set, h));
    }
    out
}

/// [`index_typings_at`] at `α := 1`, unconditional.
fn index_typings(env: &mut Env, b: &Built, i: usize, ys: &[Term], vals: &[Thm]) -> Vec<Thm> {
    index_typings_at(env, b, &[b.p()], i, ys, None, vals)
}

/// `⊢ leaf ∈ ind(1, ⟨b, ⟨zero, •⟩⟩)` — the positive polarity, closed, with the
/// index written at the *values* rather than the symbols, so that it can be
/// re-folded into whatever a parent constructor's `d⃗` asks for.
fn leaf_canon(env: &mut Env, b: &Built) -> Thm {
    let c = &b.fam.carrier.ctors[0];
    assert_eq!(c.mem_atoms.len(), 2, "leaf's antecedent is the index typings alone");
    let vals = [inj_pt_mem(&b.f.mach, 2, 0), inj_pt_mem(&b.f.mach, 3, 0)];
    let hyps = index_typings(env, b, 0, &[], &vals);
    let at = inst_all(&c.mem, &[b.p()]).expect("(M) at α := 1");
    let mem = Thm::mp(&at, &conj_thms(&hyps)).expect("the discharged hypotheses are (M)'s");
    let (res, eqs) = b.res(0, &[]);
    rw_index(env, b, &b.leaf(), &res, &eqs, &mem)
}

// ─────────────────────────────────────────────────────────────────────────────
// The spec, and what it refuses
// ─────────────────────────────────────────────────────────────────────────────

/// `plains_before` is the arity budget of a recursive argument's indices, and
/// it reads the **mask**, not the field counts.
#[test]
fn the_rec_argument_arities_come_from_the_mask() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let rb = rbtree(&mut env, &f.mach);
    assert_eq!(rb.spec.plains_before(0, 0), None, "leaf has no recursive argument");
    assert_eq!(rb.spec.plains_before(1, 0), Some(1));
    assert_eq!(rb.spec.plains_before(1, 1), Some(2));
    assert_eq!(rb.spec.plains_before(2, 0), Some(3));
    assert_eq!(rb.spec.plains_before(2, 1), Some(4));
}

/// A result-index symbol of the wrong arity is refused at the door, and the
/// construction refuses with it.
#[test]
fn a_mis_arity_index_symbol_is_declined() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let mut rb = rbtree(&mut env, &mach);
    let pt = mach.wt.sums.point();
    // `red`'s first result index must have arity `np + k = 3`; give it 2.
    rb.spec.ctors_idx[1].result[0] = abbrev(&mut env, 2, |_| pt.clone()).0;
    assert!(!rb.spec.well_formed());
    let ind = Inductive::build(&mut env, &mut mach, &rb.spec.base).expect("the skeleton");
    assert!(IndexedInductive::build(
        &mut env, &mut mach, &ind, &rb.spec, &f.rc, &f.iota, &f.funspace
    )
    .is_none());
}

/// **The non-indexed path stays a special case.** A spec with no indices is
/// *well formed* and is nevertheless declined, deliberately: routing `ni = 0`
/// through a vacuous Separation would re-derive the zero-gap non-indexed
/// fragment through a subset carving (`INDEXED-DESIGN.md` §7.2).
#[test]
fn an_unindexed_spec_is_declined() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let mut mach = f.mach;
    let base = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::new(vec![], 1)]);
    let spec = IndexedDeclSpec::new(
        base,
        Vec::new(),
        vec![
            CtorIndices::nonrecursive(Vec::new()),
            CtorIndices { result: Vec::new(), rec_args: vec![Vec::new()] },
        ],
    );
    assert!(spec.well_formed(), "vacuously well formed — nothing to check");
    let ind = Inductive::build(&mut env, &mut mach, &spec.base).expect("the skeleton");
    assert!(
        IndexedInductive::build(&mut env, &mut mach, &ind, &spec, &f.rc, &f.iota, &f.funspace)
            .is_none(),
        "ni = 0 must take the non-indexed path, not a vacuous subset"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// The `good` recursion
// ─────────────────────────────────────────────────────────────────────────────

/// **`step_typed` is unconditional** — the design's central claim about why the
/// indexed carrier is cheap. The conclusion is `step_typed(…)` on the nose,
/// with no implication in front of it, and it rests on nothing.
#[test]
fn the_good_steps_typing_carries_no_hypothesis() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let want = derived::wrec_total::step_typed(
        &mut env,
        &s,
        &b.f.mach.wt,
        &b.ind.tags,
        &b.ind.fibre.fam,
        &b.ind.bound,
        &b.fam.ix.target,
        &b.fam.gs.step,
    );
    assert_eq!(*b.fam.gs.step_typed.concl(), want);
    assert!(b.fam.gs.step_typed.concl().as_imp().is_none(), "an antecedent crept in");
    assert!(b.fam.rests_on_nothing(), "every theorem is a ⊢ with nothing on the left");

    // And therefore the recursor is a total function, unconditionally.
    assert_eq!(
        *b.fam.good.funspace.concl(),
        Formula::mem(b.fam.good.rec.clone(), s.fs.of(b.ind.wty.clone(), b.fam.ix.target.clone()))
    );
}

/// `leaf`'s `good`-ι is a **closed equation**: no `HYP`, and no constructor
/// hypotheses either, because `leaf` is nullary.
#[test]
fn the_nullary_good_iota_is_closed() {
    let mut env = Env::new();
    let b = build(&mut env);
    let at = inst_all(&b.fam.good.iota[0], &[b.p()]).expect("at α := 1");
    assert!(at.concl().as_imp().is_none(), "leaf's ι should carry no hypothesis");
    assert!(closed(at.concl()), "leaf's ι should be closed at a closed parameter");
    let (lhs, rhs) = at.concl().as_eq().expect("an equation");
    assert_ne!(lhs, rhs, "leaf's ι would be reflexivity");
}

/// The three `good` values are **different sets** — the minimum a
/// per-constructor `good` has to be.
#[test]
fn the_good_values_are_per_constructor() {
    let mut env = Env::new();
    let b = build(&mut env);
    let ps = [b.p()];
    let (sig, r) = (b.s().point(), b.s().zero());
    let terms: Vec<Term> = (0..3).map(|i| b.fam.gv.of(i, &ps, &sig, &r).expect("Gᵢ")).collect();
    assert_ne!(terms[0], terms[1]);
    assert_ne!(terms[1], terms[2]);
    assert_ne!(terms[0], terms[2]);
}

// ─────────────────────────────────────────────────────────────────────────────
// Membership and inversion — both polarities
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn leaf_is_in_the_carrier_at_its_own_index() {
    let mut env = Env::new();
    let b = build(&mut env);
    let thm = leaf_canon(&mut env, &b);
    assert_eq!(*thm.concl(), Formula::mem(b.leaf(), b.fam_at(&[b.b(), b.b()])));
    assert!(closed(thm.concl()) && thm.hyps().is_empty(), "closed and unconditional");
}

/// **The negative polarity at a constructor that exists**: `leaf` is *not* in
/// the carrier at `(red, zero)`. Inversion forces `⟨r,…⟩ = ⟨b,…⟩`, which the
/// injections refute. Without this a `good` returning all of `Idx` would
/// satisfy everything above.
#[test]
fn leaf_is_not_in_the_carrier_at_the_wrong_colour() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let c = &b.fam.carrier.ctors[0];

    let at = inst_all(&c.inv, &[b.p(), b.r(), b.b()]).expect("(I) at x⃗ := (r, zero)");
    let (ante, _) = at.concl().as_imp().expect("an implication");
    assert_eq!(ante, Formula::mem(b.leaf(), b.fam_at(&[b.r(), b.b()])));

    // Fold the result symbols away: the conclusion becomes `tup(r,b) = tup(b,b)`.
    let (res, eqs) = b.res(0, &[]);
    let tup_x = tup(&s, &[b.r(), b.b()]);
    let mut cur = at;
    let mut ix = res.clone();
    for (k, eq) in eqs.iter().enumerate() {
        let (_, new) = eq.concl().as_eq().expect("an equation");
        let (shape, txc, sc) = (ix.clone(), tup_x.clone(), s.clone());
        cur = rw_h(
            &mut env,
            eq,
            move |hole| {
                let mut v = shape.clone();
                v[k] = hole;
                Formula::eq(txc.clone(), tup(&sc, &v))
            },
            &cur,
        );
        ix[k] = new;
    }
    assert_eq!(
        *cur.concl(),
        Formula::imp(ante.clone(), Formula::eq(tup_x, tup(&s, &[b.b(), b.b()])))
    );

    // …and the colours differ.
    let ne = b.f.mach.syms.inj_distinct(&mut env, &s, 1, 0).expect("Inj₁ ≠ Inj₀");
    let ne_at = inst_all(&ne, &[s.point(), s.point()]).expect("at •");
    let out = syl(
        &syl(&cur, &tup_proj(&s, &[b.r(), b.b()], &[b.b(), b.b()], 0)).expect("syl"),
        &ne_at,
    )
    .expect("⊥");
    assert_eq!(*out.concl(), Formula::not(ante));
    assert!(closed(out.concl()) && out.hyps().is_empty());
}

/// **The interleaved constructor, at the index it really produces.** `red`'s
/// mask is `Plain, Rec, Plain, Rec`, its children must be *black-rooted at the
/// same height*, and its own index is red-at-that-height. All of that has to
/// line up for this to fire, and the theorem is closed.
#[test]
fn red_fires_at_its_own_index_over_two_leaves() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let pt = s.point();
    let leaf = b.leaf();
    let canon = leaf_canon(&mut env, &b);

    // `n := zero`, `x := •`.
    let ys = [b.b(), pt.clone()];
    let c = &b.fam.carrier.ctors[1];
    assert_eq!(c.mem_atoms.len(), 2 + 2 + 2, "two fields, two children, two indices");

    let n_mem = b.beta_typing(&mut env, 1, 0, &ys, &inj_pt_mem(&b.f.mach, 3, 0));
    let x_mem = b.beta_typing(&mut env, 1, 1, &ys, &s.unit_mem);
    let mut children = Vec::new();
    for j in 0..2 {
        let (ts, eqs) = b.rec(1, j, &ys);
        let back: Vec<Thm> = eqs.iter().map(|e| eq_symm(&mut env, e).expect("symm")).collect();
        let vals: Vec<Term> = ts
            .iter()
            .zip(&eqs)
            .map(|(_, e)| e.concl().as_eq().expect("an equation").1)
            .collect();
        children.push(rw_index(&mut env, &b, &leaf, &vals, &back, &canon));
    }
    let idx = index_typings(
        &mut env,
        &b,
        1,
        &ys,
        &[inj_pt_mem(&b.f.mach, 2, 1), inj_pt_mem(&b.f.mach, 3, 0)],
    );
    let hyps = conj_thms(&[
        n_mem,
        x_mem,
        children[0].clone(),
        children[1].clone(),
        idx[0].clone(),
        idx[1].clone(),
    ]);

    let mut args = vec![b.p()];
    args.extend(ys.iter().cloned());
    args.extend([leaf.clone(), leaf.clone()]);
    let fired = Thm::mp(&inst_all(&c.mem, &args).expect("(M)"), &hyps)
        .expect("the discharged hypotheses are (M)'s");

    // The conclusion, at the result symbols; fold them to `(r, zero)`.
    let red = b.ind.ctor_term(&b.f.mach, 1, &ys, &[leaf.clone(), leaf.clone()]).expect("red");
    let (res, eqs) = b.res(1, &ys);
    let out = rw_index(&mut env, &b, &red, &res, &eqs, &fired);
    assert_eq!(*out.concl(), Formula::mem(red, b.fam_at(&[b.r(), b.b()])));
    assert!(closed(out.concl()) && out.hyps().is_empty());
    assert_ne!(
        b.fam_at(&[b.r(), b.b()]),
        b.fam_at(&[b.b(), b.b()]),
        "red's index is not leaf's"
    );
}

/// `black` has six fields and moves the height index: its membership rule
/// concludes at `(b, succ n)`, not at the children's `(c, n)`.
#[test]
fn black_lands_at_the_successor_height() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let pt = s.point();
    let leaf = b.leaf();
    let canon = leaf_canon(&mut env, &b);

    // `c₁ = c₂ = b`, `n = zero`, `x = •`; both children are `leaf`, which sits
    // at `(b, zero)` — exactly what `black`'s `d⃗` asks for.
    let ys = [b.b(), b.b(), b.b(), pt.clone()];
    let c = &b.fam.carrier.ctors[2];
    assert_eq!(c.mem_atoms.len(), 4 + 2 + 2);

    let plain = [
        b.beta_typing(&mut env, 2, 0, &ys, &inj_pt_mem(&b.f.mach, 2, 0)),
        b.beta_typing(&mut env, 2, 1, &ys, &inj_pt_mem(&b.f.mach, 2, 0)),
        b.beta_typing(&mut env, 2, 2, &ys, &inj_pt_mem(&b.f.mach, 3, 0)),
        b.beta_typing(&mut env, 2, 3, &ys, &s.unit_mem),
    ];
    let mut children = Vec::new();
    for j in 0..2 {
        let (_, eqs) = b.rec(2, j, &ys);
        let back: Vec<Thm> = eqs.iter().map(|e| eq_symm(&mut env, e).expect("symm")).collect();
        let vals: Vec<Term> =
            eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
        children.push(rw_index(&mut env, &b, &leaf, &vals, &back, &canon));
    }
    let idx = index_typings(
        &mut env,
        &b,
        2,
        &ys,
        &[inj_pt_mem(&b.f.mach, 2, 0), inj_pt_mem(&b.f.mach, 3, 1)],
    );
    let hyps = conj_thms(&[
        plain[0].clone(),
        plain[1].clone(),
        plain[2].clone(),
        plain[3].clone(),
        children[0].clone(),
        children[1].clone(),
        idx[0].clone(),
        idx[1].clone(),
    ]);

    let mut args = vec![b.p()];
    args.extend(ys.iter().cloned());
    args.extend([leaf.clone(), leaf.clone()]);
    let fired = Thm::mp(&inst_all(&c.mem, &args).expect("(M)"), &hyps)
        .expect("the discharged hypotheses are (M)'s");

    let black = b.ind.ctor_term(&b.f.mach, 2, &ys, &[leaf.clone(), leaf.clone()]).expect("black");
    let (res, eqs) = b.res(2, &ys);
    let out = rw_index(&mut env, &b, &black, &res, &eqs, &fired);
    // `(b, succ zero)`, **not** `(b, zero)`.
    assert_eq!(*out.concl(), Formula::mem(black, b.fam_at(&[b.b(), b.r()])));
    assert!(closed(out.concl()) && out.hyps().is_empty());
    assert_ne!(b.fam_at(&[b.b(), b.r()]), b.fam_at(&[b.b(), b.b()]));
}

/// **The negative polarity in its strong form**: the carrier is *provably
/// empty* at `(b, Inj₂(•))`, a height no constructor produces — `leaf` lands at
/// `zero`, `black` at the constant successor, and `red` is never black.
///
/// Inversion alone could not say this: it speaks about a given constructor
/// term. This quantifies over every element of the skeleton.
#[test]
fn the_carrier_is_empty_at_an_index_no_constructor_produces() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let pv = b.pv();
    let xs = [b.b(), b.two()];

    // One refutation per constructor, at the *values*, then re-folded onto the
    // index symbols the theorem is stated over. Everything here is at the
    // declaration's own parameter **variable**, which `empty_at_index` closes
    // over at the end.
    let mut refutations = Vec::new();
    for i in 0..3 {
        let yvs: Vec<FreeVar> =
            (0..b.rb.spec.base.ctors[i].args.len()).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let (res, eqs) = b.res_at(std::slice::from_ref(&pv), i, &ys);
        let vals: Vec<Term> =
            eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
        // `leaf` and `black` agree with `x⃗` on the colour and differ on the
        // height; `red` differs on the colour.
        let (k, ne) = match i {
            1 => (0usize, b.f.mach.syms.inj_distinct(&mut env, &s, 0, 1).expect("b ≠ r")),
            0 => (1usize, b.f.mach.syms.inj_distinct(&mut env, &s, 2, 0).expect("two ≠ zero")),
            _ => (1usize, b.f.mach.syms.inj_distinct(&mut env, &s, 2, 1).expect("two ≠ succ")),
        };
        let ne_at = inst_all(&ne, &[s.point(), s.point()]).expect("at •");
        let at_vals = syl(&tup_proj(&s, &xs, &vals, k), &ne_at).expect("the components differ");
        // `tup(e⃗ᵢ(p,y⃗)) = tup(values)`, so the refutation transports.
        let fold = tup_congr(&mut env, &s, &eqs);
        let tx = tup(&s, &xs);
        let at_syms = rw_back(
            &mut env,
            &fold,
            move |hole| Formula::not(Formula::eq(tx.clone(), hole)),
            &at_vals,
        );
        assert_eq!(
            *at_syms.concl(),
            Formula::not(Formula::eq(tup(&s, &xs), tup(&s, &res)))
        );
        refutations.push(gen_all(&yvs, &at_syms));
    }
    // `red`'s height index is its own field, so its refutation really is
    // quantified over the fields.
    assert!(inst_all(&refutations[1], &[b.two(), s.point()]).is_some());

    let general = empty_at_index(
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

    // At `α := 1` it is a closed statement about a closed set.
    let out = inst_all(&general, &[b.p()]).expect("at α := 1");
    let zv = env.fresh_var();
    assert_eq!(
        *out.concl(),
        Formula::forall(zv, Formula::not(Formula::mem(Term::var(zv), b.fam_at(&xs))))
    );
    assert!(out.hyps().is_empty() && closed(out.concl()));
    // …and it is a *different* set from the one `leaf` inhabits.
    assert_ne!(b.fam_at(&xs), b.fam_at(&[b.b(), b.b()]));
}

// ─────────────────────────────────────────────────────────────────────────────
// D6 — the erased recursor is the indexed one's engine
// ─────────────────────────────────────────────────────────────────────────────

/// **`INDEXED-DESIGN.md` §5.1, at the derived layer.** The indexed family's
/// recursor engine is the *erased* declaration's [`GenRecursor`], and the only
/// derived lemma the reuse needs is the weakening bridge: Lean's minor premises
/// arrive with recursive arguments typed at `ind(p⃗, d⃗ᵢⱼ)`, and (S4) wants them
/// at the skeleton.
///
/// Here that is run end to end: `red`'s ι is fired with both children supplied
/// as *indexed* memberships, and what is left is `HYP` — the erased recursor's
/// own standing hypothesis, which the indices have nothing to do with.
#[test]
fn the_erased_recursor_iota_fires_on_indexed_arguments() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let pt = s.point();
    let gr = GenRecursor::build(&mut env, &b.f.mach, &b.ind, &b.f.rc, &b.f.iota, &b.f.funspace)
        .expect("the erased recursor");
    let leaf = b.leaf();
    let canon = leaf_canon(&mut env, &b);

    // The bridge: `leaf ∈ ind(1, (b,zero))` ⟹ `leaf ∈ skel(1)`.
    let bridged = Thm::mp(
        &inst_all(&b.fam.carrier.bridge, &[b.p(), b.b(), b.b(), leaf.clone()])
            .expect("the bridge"),
        &canon,
    )
    .expect("mp");
    assert_eq!(*bridged.concl(), Formula::mem(leaf.clone(), b.ind.ty_of(vec![b.p()])));

    let ys = [b.b(), pt.clone()];
    let n_mem = b.beta_typing(&mut env, 1, 0, &ys, &inj_pt_mem(&b.f.mach, 3, 0));
    let x_mem = b.beta_typing(&mut env, 1, 1, &ys, &s.unit_mem);
    let hctor = conj_thms(&[n_mem, x_mem, bridged.clone(), bridged]);

    let minors = [pt.clone(), pt.clone(), pt.clone()];
    let target = s.unit();
    let mut args = vec![b.p()];
    args.extend(minors.iter().cloned());
    args.push(target.clone());
    args.extend([b.b(), pt.clone(), leaf.clone(), leaf.clone()]);
    let at = inst_all(&gr.iota[1], &args).expect("(S4) at red");

    let (_, _, _, skel_w) =
        derived::inductive::carrier_at(&b.f.mach, &b.ind, &[b.p()]).expect("the raw carrier");
    let hyp = derived::inductive::premise::hyp_of(
        &mut env,
        &s,
        &b.rb.spec.base.ctors,
        &[b.p()],
        &skel_w,
        &minors,
        &target,
    )
    .expect("HYP");

    let out = derived::hyp_mp(
        &uncurry(&at).expect("uncurry"),
        &derived::a1i(&hctor, hyp.clone()),
    )
    .expect("the discharged hypotheses are (S4)'s");
    let (left, eq) = out.concl().as_imp().expect("an implication");
    assert_eq!(left, hyp, "only HYP is left — the indices cost nothing");
    let (lhs, rhs) = eq.as_eq().expect("an equation");
    assert_ne!(lhs, rhs, "the fired ι is reflexivity");

    // The recursive calls are live, and are at the *skeleton* recursor.
    let grec = gr
        .rec_of(&b.f.mach, &b.ind, &b.f.rc, &[b.p()], &minors, &target)
        .expect("grec");
    assert_eq!(
        rhs,
        derived::inductive::applied_minor(
            &s.ap,
            &b.rb.spec.base.ctors[1].order,
            &pt,
            &[b.b(), pt.clone()],
            &[leaf.clone(), leaf.clone()],
            &[s.ap.apply(grec.clone(), leaf.clone()), s.ap.apply(grec, leaf)],
        )
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// D4 — the universe statement
// ─────────────────────────────────────────────────────────────────────────────

/// **One `C₂` over the unchanged non-indexed chain, and the antecedent list is
/// unchanged.** At a *closed* indexed family — `V : Bool → Type` with `a : V ff`
/// and `b : V tt` — the tag membership is unconditional, so
/// `⊢ ∀x. ind(x) ∈ U₁` comes out closed.
///
/// Note what is *not* in the statement: nothing about `Idx`, nothing about
/// `goodrec`, and no index typing. `ind(x⃗) ⊆ W` holds at junk index vectors
/// too, so the `∀x⃗` closure is free.
#[test]
fn the_indexed_carrier_lands_in_u1_at_one_c2_step() {
    let mut env = Env::new();
    let (ic, mach) = IndChain::new(&mut env).expect("the chain and the apparatus");
    let f = fixture_over(&mut env, mach);
    let mut mach = f.mach;
    let s = mach.wt.sums.clone();
    let color = mach.syms.finord(&s, 2).expect("finord(2)");
    let (ity, _) = abbrev(&mut env, 0, |_| color.clone());
    let ff = mach.syms.inj(0, s.point()).expect("Inj₀");
    let tt = mach.syms.inj(1, s.point()).expect("Inj₁");
    let (ea, _) = abbrev(&mut env, 0, |_| ff.clone());
    let (eb, _) = abbrev(&mut env, 0, |_| tt.clone());

    let base = DeclSpec::new(0, vec![CtorSpec::nullary(), CtorSpec::nullary()]);
    let spec = IndexedDeclSpec::new(
        base,
        vec![ity],
        vec![CtorIndices::nonrecursive(vec![ea]), CtorIndices::nonrecursive(vec![eb])],
    );
    assert!(spec.well_formed());

    let ind = Inductive::build(&mut env, &mut mach, &spec.base).expect("the skeleton");
    let fam =
        IndexedInductive::build(&mut env, &mut mach, &ind, &spec, &f.rc, &f.iota, &f.funspace)
            .expect("the family");

    let summands = nullary_summands_in_u1(&mut env, &ic, &mach, &ind).expect("each summand is 1");
    let tags = tags_in_u1(&mut env, &ic, &mach, &ind, None, &summands).expect("A ∈ U₁");
    let du = DeclUniverse::over(&mut env, &ic, &mach, &ind, None, &tags).expect("W ∈ U₁");
    let iu = IndexedUniverse::over(&mut env, &ic, &mach, &ind, &fam.carrier, &du, None)
        .expect("ind(x) ∈ U₁");

    let u1 = ic.chain.u1.set.clone();
    let xv = fam.carrier.xvs[0];
    assert_eq!(
        *iu.ty_in_u1.concl(),
        Formula::forall(
            xv,
            Formula::mem(
                fam.carrier.ty_of(&[], &[Term::var(xv)]).expect("the carrier"),
                u1
            )
        )
    );
    assert!(closed(iu.ty_in_u1.concl()) && iu.ty_in_u1.hyps().is_empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// D4, at `RBTree`'s own shape: under a parameter hypothesis, and at any rung
//
// The test above is at `np = 0`, `hyp = None` and two nullary constructors —
// which is the `None` branch of `IndexedUniverse` (two `mp`s) at a declaration
// with no fields. `042` needs the other branch (`syl`/`ax_inst`/`hyp_mp`) at
// `np = 1` with `H := α ∈ Uₙ`, and it needs it at rung 2 as well as rung 1,
// because `RBTree`'s resultant sort is `Sort u+1` and `042` schedules `u := 1`.
// ─────────────────────────────────────────────────────────────────────────────

/// The family, and the **tower and chain it lives over** — which `fixture` does
/// not build and `IndChain::new` does not hand back, and which is where both a
/// size statement and a rung above `U₁` come from.
struct Chained {
    tower: Tower,
    cumul: Cumul,
    ic: IndChain,
    b: Built,
}

fn build_over_a_tower(env: &mut Env) -> Chained {
    let tower = Tower::new(env).expect("the tower");
    let wt = Wtype::over(env, tower.sums.clone()).expect("the W-type");
    let bound =
        Bound::over(env, &wt, tower.space.lu, tower.space.lu_ax.clone()).expect("the bound");
    let ic = IndChain::over(env, &tower, &wt, &bound).expect("the chain");
    let cumul = Cumul::new(env, &tower, 3).expect("the cumulativity table");
    let mach = Machine::over(env, wt, bound).expect("the apparatus");
    let f = fixture_over(env, mach);
    let b = build_over(env, f);
    assert!(ic.is_over(&b.f.mach), "one signature");
    Chained { tower, cumul, ic, b }
}

/// One field's smallness obligation, `⊢ ∀y₀ … ∀y_{j-1}. (Dⱼ → βⱼ(α,y⃗) ∈ Uₙ)`
/// — exactly what `cumul::arg_obligations_at` asks of `summand_at`.
///
/// `RBTree`'s fields are of two kinds and both are here: a **closed** one
/// (`Color`, `N` — `isum::finord_in_universe` is a `∀c` statement, so it is
/// instantiated at this rung's own seed and weakened under `Dⱼ`) and the
/// **parameter** (`α` — for which the obligation *is* the declaration's one
/// hypothesis, projected out of the left-nested `Dⱼ`).
fn field_obligation(
    env: &mut Env,
    c: &Chained,
    h: &Formula,
    rung: &Rung,
    ci: usize,
    j: usize,
) -> Thm {
    let s = c.b.f.mach.wt.sums.clone();
    let alpha = Term::var(c.b.ind.params[0]);
    let un = rung.set.clone();
    let betas = c.b.rb.spec.base.ctors[ci].args.clone();

    let zvs: Vec<FreeVar> = (0..j).map(|_| env.fresh_var()).collect();
    let zs: Vec<Term> = zvs.iter().map(|v| Term::var(*v)).collect();

    // `D₀ = H`, `Dᵢ₊₁ = Dᵢ ∧ (zᵢ ∈ βᵢ(α, z⃗<ᵢ))` — left-nested, which is how
    // `cumul::sigma_n` builds it and is why the projection below is `and_left`.
    let mut ds = vec![h.clone()];
    let mut guards = Vec::with_capacity(j);
    for i in 0..j {
        let mut a = vec![alpha.clone()];
        a.extend(zs[..i].iter().cloned());
        let g = Formula::mem(zs[i].clone(), Term::apply(betas[i], a));
        ds.push(Formula::and(ds[i].clone(), g.clone()));
        guards.push(g);
    }

    let mut a = vec![alpha.clone()];
    a.extend(zs.iter().cloned());
    let beta_at = inst_all(&c.b.rb.beta_ax[ci][j], &a).expect("the field type unfolds");
    let (_, value) = beta_at.concl().as_eq().expect("an equation");

    let base = if value == alpha {
        let mut th = imp_refl(ds[j].clone());
        for i in (0..j).rev() {
            th = syl(&th, &and_left(ds[i].clone(), guards[i].clone())).expect("Dⱼ → H");
        }
        th
    } else {
        let m = (2..=3)
            .find(|m| value == c.b.f.mach.syms.finord(&s, *m).expect("finord(m)"))
            .expect("a closed field type is Color or N");
        let all = finord_in_universe(env, &c.ic.clo, &s, &c.b.f.mach.syms, m)
            .expect("⊢ ∀c. finord(m) ∈ U(c)");
        a1i(
            &inst_all(&all, std::slice::from_ref(&rung.seed)).expect("at this rung's seed"),
            ds[j].clone(),
        )
    };
    let out = rw_back_opt(
        env,
        &beta_at,
        move |x| Formula::mem(x, un.clone()),
        &base,
        Some(&ds[j]),
    );
    gen_all(&zvs, &out)
}

/// `⊢ H → A ∈ Uₙ` for `RBTree`'s tag set, at any rung, with `H := α ∈ Uₙ`.
///
/// The three summands are `1`, `Σn:N. Σx:α. 1` and
/// `Σc₁:Color. Σc₂:Color. Σn:N. Σx:α. 1`, so this runs `cumul::summand_at` at
/// telescope depths 0, 2 and **4** — the deepest any test in the tree reaches.
fn rbtree_tags_at(env: &mut Env, c: &Chained, h: &Formula, rung: &Rung) -> Thm {
    let (ic, mach, ind) = (&c.ic, &c.b.f.mach, &c.b.ind);
    let mut summands = Vec::with_capacity(3);
    for ci in 0..ind.spec.ctors.len() {
        let obs = arg_obligations_at(env, ic, mach, ind, ci, Some(h), rung)
            .expect("the obligations this constructor's summand needs");
        let sm = if obs.is_empty() {
            let nul = nullary_summand_at(env, ic, mach, ind, ci, rung).expect("Aᵢ = 1");
            a1i(&nul, h.clone())
        } else {
            let mut args = Vec::with_capacity(obs.len());
            for (j, want) in obs.iter().enumerate() {
                let t = field_obligation(env, c, h, rung, ci, j);
                assert_eq!(t.concl(), want, "the obligation the pipeline asks for");
                args.push(t);
            }
            summand_at(env, ic, mach, ind, ci, Some(h), rung, &args).expect("Aᵢ ∈ Uₙ")
        };
        summands.push(sm);
    }
    tags_at(env, ic, mach, ind, Some(h), rung, &summands).expect("A ∈ Uₙ")
}

/// `∀p ∀x₀ ∀x₁. (p ∈ Uₙ → ind(p,x₀,x₁) ∈ Uₙ)`, rebuilt from the kernel's own
/// constructors.
fn want_universe_statement(c: &Chained, un: &Term) -> Formula {
    let pv = c.b.ind.params[0];
    let xvs = &c.b.fam.carrier.xvs;
    assert_eq!(xvs.len(), 2, "RBTree has two indices");
    let carrier = c
        .b
        .fam
        .carrier
        .ty_of(&[Term::var(pv)], &[Term::var(xvs[0]), Term::var(xvs[1])])
        .expect("the carrier");
    let body = Formula::imp(
        Formula::mem(Term::var(pv), un.clone()),
        Formula::mem(carrier, un.clone()),
    );
    Formula::forall(pv, Formula::forall(xvs[0], Formula::forall(xvs[1], body)))
}

/// **`042`'s first scheduled pair, at the derived layer.** `RBTree`'s carrier
/// lands in `U₁` under the declaration's one antecedent `α ∈ U₁`, and nothing
/// is left on the left.
///
/// This is `IndexedUniverse`'s `Some(h)` branch — `syl`/`ax_inst`/`hyp_mp`,
/// where the `None` branch is `mp`/`mp` — at `np = 1`, three constructors and
/// two indices, i.e. at the shape the checker will actually hand it.
#[test]
fn the_indexed_carrier_lands_in_u1_under_the_parameter_hypothesis() {
    let mut env = Env::new();
    let c = build_over_a_tower(&mut env);
    let alpha = Term::var(c.b.ind.params[0]);
    let u1 = c.ic.chain.u1.set.clone();
    let h = Formula::mem(alpha.clone(), u1.clone());

    let tags = rbtree_tags_at(&mut env, &c, &h, &c.ic.chain.u1);
    assert_eq!(
        *tags.concl(),
        Formula::imp(h.clone(), Formula::mem(c.b.ind.tags.clone(), u1.clone()))
    );
    let du = DeclUniverse::over(&mut env, &c.ic, &c.b.f.mach, &c.b.ind, Some(&h), &tags)
        .expect("the skeleton W ∈ U₁");
    let iu = IndexedUniverse::over(
        &mut env,
        &c.ic,
        &c.b.f.mach,
        &c.b.ind,
        &c.b.fam.carrier,
        &du,
        Some(&h),
    )
    .expect("ind(α,x₀,x₁) ∈ U₁");

    assert_eq!(iu.universe, u1, "the rung it was asked for");
    assert_eq!(*iu.ty_in_u1.concl(), want_universe_statement(&c, &u1));
    assert!(closed(iu.ty_in_u1.concl()), "closed once α is generalised");
    assert!(
        iu.ty_in_u1.hyps().is_empty() && iu.at_vars.hyps().is_empty(),
        "the antecedent is in the conclusion, not in a Γ"
    );
    assert!(
        iu.at_vars.concl().as_imp().is_some(),
        "the parameter hypothesis really is carried, not dropped"
    );

    // **Non-vacuity.** At `α := 1` — and `1 ∈ U₁` discharges the antecedent —
    // the set placed in `U₁` is the one `leaf` inhabits, not the empty set.
    let one_small = inst_all(&c.ic.clo.unit, std::slice::from_ref(&c.ic.chain.u1.seed))
        .expect("⊢ 1 ∈ U₁");
    let at = inst_all(&iu.ty_in_u1, &[c.b.p(), c.b.b(), c.b.b()]).expect("at (1, b, zero)");
    let out = Thm::mp(&at, &one_small).expect("the antecedent is 1 ∈ U₁");
    assert_eq!(*out.concl(), Formula::mem(c.b.fam_at(&[c.b.b(), c.b.b()]), u1));
    let canon = leaf_canon(&mut env, &c.b);
    assert_eq!(*canon.concl(), Formula::mem(c.b.leaf(), c.b.fam_at(&[c.b.b(), c.b.b()])));
}

/// **`042`'s second scheduled pair, and the reason `over_at` exists.**
/// `⟦Sort ℓ⟧ = U_ℓ`, so at `u := 1` the declaration's parameter is in `U₂` and
/// the carrier lands in `U₂`. The whole statement moves up a rung, antecedent
/// included, and the derivation does not change: the one step is `C₂`, which
/// every rung has.
///
/// Three rungs, not two — the tower's rungs are provably distinct
/// (`Cumul::strict`), so these are three different statements rather than one
/// restated, and two could not tell "the rung is threaded" from "the rung is
/// `at(1)` unless asked otherwise".
#[test]
fn the_indexed_carrier_lands_at_every_rung_of_the_tower() {
    let mut env = Env::new();
    let c = build_over_a_tower(&mut env);
    let alpha = Term::var(c.b.ind.params[0]);

    for n in 1..3 {
        assert_ne!(c.tower.u(n), c.tower.u(n + 1));
        assert!(c.cumul.strict(n).is_some(), "¬(U₍ₙ₊₁₎ ⊆ Uₙ)");
    }

    let mut first: Option<(Formula, DeclUniverse)> = None;
    for n in 1..=3 {
        let rung = c.tower.at(n).expect("a rung of this tower");
        let h = Formula::mem(alpha.clone(), rung.set.clone());
        let tags = rbtree_tags_at(&mut env, &c, &h, &rung);
        let du =
            DeclUniverse::over_at(&mut env, &c.ic, &c.b.f.mach, &c.b.ind, Some(&h), &rung, &tags)
                .expect("the skeleton W ∈ Uₙ");
        let iu = IndexedUniverse::over_at(
            &mut env,
            &c.ic,
            &c.b.f.mach,
            &c.b.ind,
            &c.b.fam.carrier,
            &du,
            Some(&h),
            &rung,
        )
        .expect("ind(α,x₀,x₁) ∈ Uₙ");

        assert_eq!(iu.universe, c.tower.u(n));
        assert_eq!(*iu.ty_in_u1.concl(), want_universe_statement(&c, &rung.set));
        assert!(closed(iu.ty_in_u1.concl()) && iu.ty_in_u1.hyps().is_empty());

        // A `DeclUniverse` built at *another* rung is refused rather than
        // composed into a statement about the wrong universe.
        if let Some((h1, du1)) = &first {
            assert!(
                IndexedUniverse::over_at(
                    &mut env,
                    &c.ic,
                    &c.b.f.mach,
                    &c.b.ind,
                    &c.b.fam.carrier,
                    du1,
                    Some(h1),
                    &rung,
                )
                .is_none(),
                "a U₁ skeleton membership was accepted at rung {n}"
            );
        } else {
            first = Some((h, du));
        }
    }

    // And `over` really is `over_at` at rung 1.
    let (h1, du1) = first.as_ref().expect("rung 1 ran first");
    let plain = IndexedUniverse::over(
        &mut env,
        &c.ic,
        &c.b.f.mach,
        &c.b.ind,
        &c.b.fam.carrier,
        du1,
        Some(h1),
    )
    .expect("ind(α,x⃗) ∈ U₁");
    assert_eq!(plain.universe, c.ic.chain.u1.set);
    assert_eq!(*plain.ty_in_u1.concl(), want_universe_statement(&c, &c.ic.chain.u1.set));
}

// ─────────────────────────────────────────────────────────────────────────────
// (M) with `Eᵢ` pre-discharged, and the Lean-positional antecedent
//
// `INDEXED-DESIGN.md` §8.1's open question: (M)'s `ni` index typings are not
// positional against the constructor's Lean field spine, so a positionally
// instantiated premise list cannot carry them. `mem_lean` discharges them at
// rule-build time and hands back an antecedent that *is* positional.
// ─────────────────────────────────────────────────────────────────────────────

/// The mask, read off the three constructors — and the permutation it induces
/// on (M)'s antecedent.
///
/// `red`'s mask is `Plain, Rec, Plain, Rec` and `black`'s is
/// `Plain, Plain, Plain, Rec, Plain, Rec`, so both put a plain field *after* a
/// recursive one; the carrier's own order is all plains then all recs, and the
/// two disagree at four and six positions respectively.
#[test]
fn the_lean_field_order_permutes_the_membership_antecedent() {
    let mut env = Env::new();
    let b = build(&mut env);
    let want: [Vec<usize>; 3] = [vec![], vec![0, 2, 1, 3], vec![0, 1, 2, 4, 3, 5]];
    for (i, w) in want.iter().enumerate() {
        let c = &b.fam.carrier.ctors[i];
        assert_eq!(c.lean_order, *w, "constructor {i}'s field mask");
        let lean = c.mem_atoms_lean();
        assert_eq!(lean.len(), c.yvs.len() + c.tvs.len(), "Eᵢ is not a field");
        assert_eq!(lean.len() + b.rb.spec.num_indices(), c.mem_atoms.len());
        for (q, j) in w.iter().enumerate() {
            assert_eq!(lean[q], c.mem_atoms[*j]);
        }
    }
    // The two orders really do differ where the mask interleaves.
    assert_ne!(b.fam.carrier.ctors[1].mem_atoms_lean(), b.fam.carrier.ctors[1].mem_atoms[..4]);
}

/// **A nullary constructor: `Eᵢ` discharged and nothing left at all.**
///
/// `leaf`'s index expressions mention neither a parameter nor a field, so its
/// two witnesses are closed and `mem_lean` returns the unconditional
/// `⊢ ∀α. leaf ∈ ind(α, b, zero)`. Discharging that at `α := 1` reproduces
/// `leaf_canon` — the statement the rest of this file builds by hand at the use
/// site, which is exactly what `mem_lean` exists to stop.
#[test]
fn the_nullary_membership_rule_needs_no_antecedent_once_its_indices_are_typed() {
    let mut env = Env::new();
    let b = build(&mut env);
    let c = &b.fam.carrier.ctors[0];
    assert!(c.mem_atoms_lean().is_empty(), "leaf has no fields");
    assert_eq!(c.mem_atoms.len(), 2, "only the two index typings");

    let vals = [inj_pt_mem(&b.f.mach, 2, 0), inj_pt_mem(&b.f.mach, 3, 0)];
    let ws: Vec<Thm> = index_typings_at(&mut env, &b, &[b.pv()], 0, &[], None, &vals)
        .iter()
        .map(|w| gen_all(&b.ind.params, w))
        .collect();
    let lean = c.mem_lean(&ws).expect("(M) with Eᵢ discharged");

    let at = inst_all(&lean, &[b.p()]).expect("at α := 1");
    assert!(at.concl().as_imp().is_none(), "nothing is left on the left");
    let (res, eqs) = b.res(0, &[]);
    let out = rw_index(&mut env, &b, &b.leaf(), &res, &eqs, &at);
    assert_eq!(*out.concl(), Formula::mem(b.leaf(), b.fam_at(&[b.b(), b.b()])));
    assert!(closed(out.concl()) && out.hyps().is_empty());

    // One witness short, and one witness too many, are both refused.
    assert!(c.mem_lean(&ws[..1]).is_none());
    let mut too_many = ws.clone();
    too_many.push(ws[0].clone());
    assert!(c.mem_lean(&too_many).is_none());
    // A witness that merely *concludes* what the real one concludes is refused.
    let fake = Thm::assume(ws[1].concl().clone());
    assert!(c.mem_lean(&[ws[0].clone(), fake]).is_none());
}

/// **The interleaved constructor.** `red`'s two index witnesses are of the two
/// kinds §8.1 named: `Color.r ∈ Color` is closed, and `n ∈ N` *is* the first
/// plain field's own typing, projected out of the antecedent (M) already
/// carries. Nothing else is needed, and what comes back takes its hypotheses in
/// **Lean field order** — `n, l, x, r`, not the carrier's `n, x, l, r`.
#[test]
fn the_membership_rule_takes_its_hypotheses_in_lean_field_order() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let pt = s.point();
    let leaf = b.leaf();
    let canon = leaf_canon(&mut env, &b);
    let c = &b.fam.carrier.ctors[1];

    let pv = b.pv();
    let ys: Vec<Term> = c.yvs.iter().map(|v| Term::var(*v)).collect();
    let lean = c.mem_atoms_lean();
    let h = conj_of(&lean).expect("red has four fields");

    // `⊢ H → Color.r ∈ Color`, closed and weakened.
    let v0 = a1i(&inj_pt_mem(&b.f.mach, 2, 1), h.clone());
    // `⊢ H → n ∈ N`, out of the *first Lean field*'s own typing.
    let field0 = conj_proj(&lean, 0).expect("red's first Lean field");
    let beta0 = inst_all(&b.rb.beta_ax[1][0], std::slice::from_ref(&pv)).expect("β₀(α) = N");
    let y0 = ys[0].clone();
    let v1 = rw_h(&mut env, &beta0, move |x| Formula::mem(y0.clone(), x), &field0);

    let mut quant = b.ind.params.clone();
    quant.extend(c.yvs.iter().copied());
    quant.extend(c.tvs.iter().copied());
    let ws: Vec<Thm> =
        index_typings_at(&mut env, &b, std::slice::from_ref(&pv), 1, &ys, Some(&h), &[v0, v1])
            .iter()
            .map(|w| gen_all(&quant, w))
            .collect();
    let mem_lean = c.mem_lean(&ws).expect("(M) with Eᵢ discharged");

    // Fire it: `n := zero`, `x := •`, both children `leaf`.
    let yvals = [b.b(), pt.clone()];
    let n_mem = b.beta_typing(&mut env, 1, 0, &yvals, &inj_pt_mem(&b.f.mach, 3, 0));
    let x_mem = b.beta_typing(&mut env, 1, 1, &yvals, &s.unit_mem);
    let mut children = Vec::new();
    for j in 0..2 {
        let (_, eqs) = b.rec(1, j, &yvals);
        let back: Vec<Thm> = eqs.iter().map(|e| eq_symm(&mut env, e).expect("symm")).collect();
        let vals: Vec<Term> =
            eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
        children.push(rw_index(&mut env, &b, &leaf, &vals, &back, &canon));
    }

    let mut args = vec![b.p()];
    args.extend(yvals.iter().cloned());
    args.extend([leaf.clone(), leaf.clone()]);
    let at = inst_all(&mem_lean, &args).expect("(M′) at the values");

    // **The pin.** `n, l, x, r` fires; the carrier's `n, x, l, r` does not.
    let in_lean_order = conj_thms(&[
        n_mem.clone(),
        children[0].clone(),
        x_mem.clone(),
        children[1].clone(),
    ]);
    let fired = Thm::mp(&at, &in_lean_order).expect("the fields in declared order");
    let in_carrier_order =
        conj_thms(&[n_mem, x_mem, children[0].clone(), children[1].clone()]);
    assert!(
        Thm::mp(&at, &in_carrier_order).is_none(),
        "the antecedent is in Lean field order, not the carrier's"
    );

    let red = b.ind.ctor_term(&b.f.mach, 1, &yvals, &[leaf.clone(), leaf.clone()]).expect("red");
    let (res, eqs) = b.res(1, &yvals);
    let out = rw_index(&mut env, &b, &red, &res, &eqs, &fired);
    assert_eq!(*out.concl(), Formula::mem(red, b.fam_at(&[b.r(), b.b()])));
    assert!(closed(out.concl()) && out.hyps().is_empty());
    assert_ne!(b.fam_at(&[b.r(), b.b()]), b.fam_at(&[b.b(), b.b()]));
}

/// The same at `black`, whose mask puts a plain field between the two recursive
/// ones and whose antecedent therefore permutes at **six** positions.
#[test]
fn the_six_field_constructor_permutes_at_every_position_the_mask_moves() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let pt = s.point();
    let leaf = b.leaf();
    let canon = leaf_canon(&mut env, &b);
    let c = &b.fam.carrier.ctors[2];

    let pv = b.pv();
    let ys: Vec<Term> = c.yvs.iter().map(|v| Term::var(*v)).collect();
    let lean = c.mem_atoms_lean();
    let h = conj_of(&lean).expect("black has six fields");

    // Both of `black`'s index expressions are constants: `Color.b` and the
    // constant successor.
    let vals = [
        a1i(&inj_pt_mem(&b.f.mach, 2, 0), h.clone()),
        a1i(&inj_pt_mem(&b.f.mach, 3, 1), h.clone()),
    ];
    let mut quant = b.ind.params.clone();
    quant.extend(c.yvs.iter().copied());
    quant.extend(c.tvs.iter().copied());
    let ws: Vec<Thm> = index_typings_at(&mut env, &b, &[pv], 2, &ys, Some(&h), &vals)
        .iter()
        .map(|w| gen_all(&quant, w))
        .collect();
    let mem_lean = c.mem_lean(&ws).expect("(M) with Eᵢ discharged");

    let yvals = [b.b(), b.b(), b.b(), pt.clone()];
    let plain = [
        b.beta_typing(&mut env, 2, 0, &yvals, &inj_pt_mem(&b.f.mach, 2, 0)),
        b.beta_typing(&mut env, 2, 1, &yvals, &inj_pt_mem(&b.f.mach, 2, 0)),
        b.beta_typing(&mut env, 2, 2, &yvals, &inj_pt_mem(&b.f.mach, 3, 0)),
        b.beta_typing(&mut env, 2, 3, &yvals, &s.unit_mem),
    ];
    let mut children = Vec::new();
    for j in 0..2 {
        let (_, eqs) = b.rec(2, j, &yvals);
        let back: Vec<Thm> = eqs.iter().map(|e| eq_symm(&mut env, e).expect("symm")).collect();
        let vs: Vec<Term> =
            eqs.iter().map(|e| e.concl().as_eq().expect("an equation").1).collect();
        children.push(rw_index(&mut env, &b, &leaf, &vs, &back, &canon));
    }

    let mut args = vec![b.p()];
    args.extend(yvals.iter().cloned());
    args.extend([leaf.clone(), leaf.clone()]);
    let at = inst_all(&mem_lean, &args).expect("(M′) at the values");

    // `c₁, c₂, n, l, x, r` — the mask's order, with `x` between the children.
    let fired = Thm::mp(
        &at,
        &conj_thms(&[
            plain[0].clone(),
            plain[1].clone(),
            plain[2].clone(),
            children[0].clone(),
            plain[3].clone(),
            children[1].clone(),
        ]),
    )
    .expect("the fields in declared order");
    assert!(
        Thm::mp(
            &at,
            &conj_thms(&[
                plain[0].clone(),
                plain[1].clone(),
                plain[2].clone(),
                plain[3].clone(),
                children[0].clone(),
                children[1].clone(),
            ])
        )
        .is_none(),
        "the carrier's plains-then-recs order is not the declared one"
    );

    let black = b.ind.ctor_term(&b.f.mach, 2, &yvals, &[leaf.clone(), leaf.clone()]).expect("black");
    let (res, eqs) = b.res(2, &yvals);
    let out = rw_index(&mut env, &b, &black, &res, &eqs, &fired);
    assert_eq!(*out.concl(), Formula::mem(black, b.fam_at(&[b.b(), b.r()])));
    assert!(closed(out.concl()) && out.hyps().is_empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// The house rule at `Good::build`'s door
// ─────────────────────────────────────────────────────────────────────────────

/// **A `Thm` is a sequent, and `Good::build` takes two of them from its
/// caller.**
///
/// `iota` and `funspace` are consumed by `Thm::mp`, which unions the two sides'
/// hypothesis sets in silence, and every field of [`Good`] is documented `⊢ …`
/// — [`Good::funspace`] says "unconditional" in as many words. A theorem that
/// merely *concludes* what `wrec_total::iota` concludes is refused at the door.
///
/// **This test passes with the door check removed too**, and that is worth
/// recording rather than hiding: the per-constructor `eq.hyps().is_empty()`
/// check inside the build loop already catches a hypothesis that has travelled
/// all the way through `iota_core`, so there is no exploit here, only a
/// coincidence. The door check is what stops the coincidence from being load
/// bearing — the loop's check exists to catch *its own* mistakes, not to
/// validate the caller — and it refuses before any of the work.
#[test]
fn the_good_recursion_refuses_a_merely_assumed_w_recursor_theorem() {
    let mut env = Env::new();
    let b = build(&mut env);

    let fake_iota = Thm::assume(b.f.iota.concl().clone());
    let fake_funspace = Thm::assume(b.f.funspace.concl().clone());
    assert_eq!(fake_iota.concl(), b.f.iota.concl(), "the fake must be conclusion-exact");
    assert!(!fake_iota.hyps().is_empty() && !fake_funspace.hyps().is_empty());

    let good = |env: &mut Env, mach: &Machine, iota: &Thm, funspace: &Thm| {
        Good::build(
            env, mach, &b.ind, &b.rb.spec, &b.fam.ix, &b.fam.gv, &b.fam.gs, &b.f.rc, iota,
            funspace,
        )
    };
    assert!(
        good(&mut env, &b.f.mach, &fake_iota, &b.f.funspace).is_none(),
        "a hypothetical ι was accepted"
    );
    assert!(
        good(&mut env, &b.f.mach, &b.f.iota, &fake_funspace).is_none(),
        "a hypothetical funspace was accepted"
    );

    // The honest pair still builds, and both stored theorems are `⊢`.
    let g = good(&mut env, &b.f.mach, &b.f.iota, &b.f.funspace).expect("the good recursion");
    assert!(g.funspace.hyps().is_empty() && g.wrec_iota.hyps().is_empty());
}

/// **`Good::build` resolves every term against `mach`, so `mach` is not a free
/// choice either.**
///
/// A second [`Machine`] over the same `Wtype` and `Bound` has its own `rec₊`,
/// its own `⋂` and its own injections; handed one, the build used to walk into
/// `iota_core` and construct a constructor term out of the *other* apparatus's
/// `Inj` before some join downstream noticed. `Inductive::is_over` exists for
/// exactly this and is now consulted at the door — so the refusal is by
/// decision rather than by accident, and costs nothing.
#[test]
fn the_good_recursion_refuses_a_foreign_machine() {
    let mut env = Env::new();
    let b = build(&mut env);
    let m2 = Machine::over(&mut env, b.f.mach.wt.clone(), b.f.mach.bnd.clone())
        .expect("a second machine");
    let other = fixture_over(&mut env, m2);
    assert!(!b.ind.is_over(&other.mach), "the two apparatuses must differ");
    assert!(
        Good::build(
            &mut env, &other.mach, &b.ind, &b.rb.spec, &b.fam.ix, &b.fam.gv, &b.fam.gs, &b.f.rc,
            &b.f.iota, &b.f.funspace
        )
        .is_none(),
        "the good recursion was built over a foreign apparatus"
    );
}
