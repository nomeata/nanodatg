//! An indexed family with a **function-typed recursive argument** — the shape
//! `derived/tests/family.rs` cannot reach.
//!
//! ```text
//! inductive IxT (α : Type) : N → Type
//!   | leaf : α → IxT α zero                      1 plain, 0 rec
//!   | node : {n} → (B2 → IxT α n) → IxT α (s n)  1 plain, 1 rec over Σ(z::B2)
//!   | wide : {n} → (T3 → IxT α n) → IxT α (s n)  1 plain, 1 rec over Σ(z::T3)
//! ```
//!
//! `RBTree` is the corpus's indexed witness and every one of its recursive
//! slots is a **plain** occurrence, so it exercises `Aⱼ = 1` and nothing else.
//! At [`RecArg::general`](derived::recarg::RecArg::general) the `j`-th fibre
//! summand is `Σ(z::γⱼ)`, the ih row holds a whole family rather than a value,
//! and the good-set matrix's `j`-th conjunct is the bounded universal
//! `∀z. (z ∈ Aⱼ → tup(d⃗ᵢⱼ) ∈ app(r, Injⱼ(z)))`. Everything below is about that
//! conjunct and the four rules that read it.
//!
//! # Why three constructors, and why two of them branch
//!
//! The fibre summand row is read off the declaration **by constructor index**,
//! and a clamp `i ↦ min(i,1)` is the identity on `{0,1}`: with `leaf` and
//! `node` alone nothing could say the row was picked correctly. `node` and
//! `wide` are identical in every other respect — same plain field, same result
//! index, same child index — so the only thing that distinguishes them is the
//! fibre, which is exactly the thing under test.
//!
//! Their domains are **closed** (`finord(2)`, `finord(3)`): a domain mentioning
//! a parameter is a different question and would confound this one.
//!
//! # Both polarities
//!
//! Membership alone is satisfied by a carrier that is all of `W` at every
//! index. What rules that out here is `empty_at_index` at `Inj₂(•)` — a height
//! no constructor produces — quantified over every element of the skeleton,
//! which has to refute all three constructors including the two branching ones.
//! And `node` really fires, over a genuinely two-element fibre, at a constant
//! function whose value is a `leaf`.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use derived::bound::Bound;
use derived::inductive::family::{
    empty_at_index, CtorIndices, IndexedDeclSpec, IndexedInductive,
};
use derived::inductive::{CtorSpec, DeclSpec, Inductive, Machine, Slot};
use derived::sums::Sums;
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;
use derived::{a1i, and_left, define_abbrev, eq_symm, gen_all, inst_all, syl};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers — the boundary work, done by hand
// ─────────────────────────────────────────────────────────────────────────────

/// A formula with no free variables.
fn closed(f: &Formula) -> bool {
    let mut vs = Vec::new();
    f.free_vars(&mut vs);
    vs.is_empty()
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

/// Right-nested conjunction of closed theorems, matching `conj_of`.
fn conj_thms(thms: &[Thm]) -> Thm {
    let mut acc = thms.last().expect("non-empty").clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = derived::and_intro(t, &acc);
    }
    acc
}

// ─────────────────────────────────────────────────────────────────────────────
// The declaration
// ─────────────────────────────────────────────────────────────────────────────

/// The spec, and every defining equation a test needs to unfold.
struct Decl {
    spec: IndexedDeclSpec,
    /// `⊢ ∀α. ι₀(α) = finord(4)`.
    ity_ax: Thm,
    /// The `β` axioms, per constructor.
    beta_ax: Vec<Vec<Thm>>,
    /// The result-index axioms, per constructor (one index).
    res_ax: Vec<Thm>,
    /// The child-index axioms, per constructor with a recursive argument.
    rec_ax: Vec<Option<Thm>>,
}

/// `N := finord(4)`, `zero := Inj₀(•)`, a constant `succ := Inj₁(•)`, and a
/// `B2`/`T3` pair of closed fibre domains that are visibly different sets.
fn declaration(env: &mut Env, mach: &Machine) -> Decl {
    let s = &mach.wt.sums;
    let pt = s.point();
    let nat = mach.syms.finord(s, 4).expect("finord(4)");
    let b2 = mach.syms.finord(s, 2).expect("finord(2)");
    let t3 = mach.syms.finord(s, 3).expect("finord(3)");
    let zero = mach.syms.inj(0, pt.clone()).expect("Inj₀");
    let succ = mach.syms.inj(1, pt.clone()).expect("Inj₁");

    let (i0, i0_ax) = abbrev(env, 1, |_| nat.clone());

    // `leaf`'s field is the parameter; `node`/`wide`'s is the index type.
    let (lb0, lb0_ax) = abbrev(env, 1, |a| a[0].clone());
    let (nb0, nb0_ax) = abbrev(env, 1, |_| nat.clone());
    let (wb0, wb0_ax) = abbrev(env, 1, |_| nat.clone());
    // The two recursive arguments' domain telescopes, `γ` of arity `np + 0`.
    let (ng0, _) = abbrev(env, 1, |_| b2.clone());
    let (wg0, _) = abbrev(env, 1, |_| t3.clone());

    let mut node = CtorSpec::with_rec_doms(vec![nb0], vec![vec![ng0]]);
    node.order = vec![Slot::Plain, Slot::Rec];
    let mut wide = CtorSpec::with_rec_doms(vec![wb0], vec![vec![wg0]]);
    wide.order = vec![Slot::Plain, Slot::Rec];
    let base = DeclSpec::new(1, vec![CtorSpec::new(vec![lb0], 0), node, wide]);

    let (le0, le0_ax) = abbrev(env, 2, move |_| zero.clone());
    let (ne0, ne0_ax) = abbrev(env, 2, {
        let succ = succ.clone();
        move |_| succ.clone()
    });
    let (we0, we0_ax) = abbrev(env, 2, move |_| succ.clone());
    // `d⃗ᵢ₀(α, n) = n` — arity `np + plains_before = 2` at both.
    let (nd0, nd0_ax) = abbrev(env, 2, |a| a[1].clone());
    let (wd0, wd0_ax) = abbrev(env, 2, |a| a[1].clone());

    Decl {
        spec: IndexedDeclSpec::new(
            base,
            vec![i0],
            vec![
                CtorIndices::nonrecursive(vec![le0]),
                CtorIndices { result: vec![ne0], rec_args: vec![vec![nd0]] },
                CtorIndices { result: vec![we0], rec_args: vec![vec![wd0]] },
            ],
        ),
        ity_ax: i0_ax,
        beta_ax: vec![vec![lb0_ax], vec![nb0_ax], vec![wb0_ax]],
        res_ax: vec![le0_ax, ne0_ax, we0_ax],
        rec_ax: vec![None, Some(nd0_ax), Some(wd0_ax)],
    }
}

/// The apparatus, the skeleton and the family.
struct Built {
    mach: Machine,
    rc: Recursor,
    decl: Decl,
    ind: Inductive,
    fam: IndexedInductive,
}

fn build(env: &mut Env) -> Built {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let mut mach = Machine::over(env, wt, bnd).expect("machine");
    let sums = mach.wt.sums.clone();
    mach.syms.ensure(env, &sums, 4).expect("four summands");
    let rc = Recursor::new(env, &mach.wt).expect("W-recursor");
    let ext = derived::wrec_extend::extension(env, &mach.wt, &rc).expect("extension");
    let total = derived::wrec_total::totality(env, &mach.wt, &rc, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &mach.wt, &rc, &total).expect("iota");
    let funspace =
        derived::wrec_total::wrec_funspace(env, &mach.wt, &rc, &total).expect("funspace");

    let decl = declaration(env, &mach);
    assert!(decl.spec.well_formed(), "the spec is well formed");
    let ind = Inductive::build(env, &mut mach, &decl.spec.base).expect("the skeleton");
    let fam = IndexedInductive::build(env, &mut mach, &ind, &decl.spec, &rc, &iota, &funspace)
        .expect("the indexed family");
    Built { mach, rc, decl, ind, fam }
}

impl Built {
    fn s(&self) -> &Sums { &self.mach.wt.sums }
    /// `α := 1`.
    fn p(&self) -> Term { self.s().unit() }
    /// The declaration's own parameter **variable** — what the theorems that
    /// are not `∀`-closed over the parameters are stated at.
    fn pv(&self) -> Term { Term::var(self.ind.params[0]) }
    fn zero(&self) -> Term { self.mach.syms.inj(0, self.s().point()).expect("Inj₀") }
    fn succ(&self) -> Term { self.mach.syms.inj(1, self.s().point()).expect("Inj₁") }
    /// A height no constructor produces.
    fn two(&self) -> Term { self.mach.syms.inj(2, self.s().point()).expect("Inj₂") }
    /// `ind(1, x)`.
    fn fam_at(&self, x: &Term) -> Term {
        self.fam.carrier.ty_of(&[self.p()], std::slice::from_ref(x)).expect("the carrier")
    }
    /// `Aⱼ = Σ(z::γⱼ)`, the `j`-th fibre summand of constructor `i`, at
    /// caller-supplied parameters. **Not** `recargs[i].summands[j]`, which is
    /// at the declaration's parameter variable and is the wrong term once a
    /// theorem has been instantiated at `α := 1`.
    fn summand_at(&self, ps: &[Term], i: usize, j: usize) -> Term {
        self.ind
            .fibre_summands_at(self.s(), ps)
            .expect("the fibre summands")[i][j]
            .clone()
    }
    /// `⊢ eᵢ₀(p⃗, y⃗) = its value`.
    fn res_eq_at(&self, ps: &[Term], i: usize, ys: &[Term]) -> Thm {
        let mut a = ps.to_vec();
        a.extend(ys.iter().cloned());
        inst_all(&self.decl.res_ax[i], &a).expect("unfold")
    }
    /// The same at `α := 1`.
    fn res_eq(&self, i: usize, ys: &[Term]) -> Thm {
        self.res_eq_at(&[self.p()], i, ys)
    }
}

/// `⊢ eᵢ₀(1,y⃗) ∈ ι₀(1)` — (M)'s extra antecedent, folded back onto the
/// symbols from a membership at the values.
fn index_typing(env: &mut Env, b: &Built, i: usize, ys: &[Term], val: &Thm) -> Thm {
    let set = Term::apply(b.decl.spec.indices[0], vec![b.p()]);
    let ity = inst_all(&b.decl.ity_ax, &[b.p()]).expect("the index type unfolds");
    let res_eq = b.res_eq(i, ys);
    let (_, value) = res_eq.concl().as_eq().expect("an equation");
    let at_set = rw_back(env, &ity, move |x| Formula::mem(value.clone(), x), val);
    rw_back(env, &res_eq, move |x| Formula::mem(x, set.clone()), &at_set)
}

/// `⊢ βᵢⱼ(1, y<ⱼ)`-typed, from a membership at the argument type's value.
fn beta_typing(env: &mut Env, b: &Built, i: usize, j: usize, ys: &[Term], val: &Thm) -> Thm {
    let mut a = vec![b.p()];
    a.extend(ys[..j].iter().cloned());
    let eq = inst_all(&b.decl.beta_ax[i][j], &a).expect("unfold");
    let y = ys[j].clone();
    rw_back(env, &eq, move |x| Formula::mem(y.clone(), x), val)
}

/// `⊢ leaf(•) ∈ ind(1, Inj₀(•))` — closed, with the index at its **value**, so
/// that a parent constructor's `d⃗` can be folded onto it.
fn leaf_canon(env: &mut Env, b: &Built) -> Thm {
    let pt = b.s().point();
    let ys = [pt.clone()];
    let c = &b.fam.carrier.ctors[0];
    assert_eq!(c.mem_atoms.len(), 2, "one plain field and one index typing");
    let y_mem = beta_typing(env, b, 0, 0, &ys, &b.s().unit_mem);
    let e_mem = index_typing(env, b, 0, &ys, &inj_pt_mem(&b.mach, 4, 0));
    let at = inst_all(&c.mem, &[b.p(), pt]).expect("(M) at α := 1, y := •");
    let mem = Thm::mp(&at, &conj_thms(&[y_mem, e_mem])).expect("(M)'s antecedent");
    let leaf = b.ind.ctor_term(&b.mach, 0, &ys, &[]).expect("leaf(•)");
    let res_eq = b.res_eq(0, &ys);
    rw(env, &res_eq, move |x| Formula::mem(leaf.clone(), b.fam_at(&x)), &mem)
}

/// `⊢ g ∈ fs(A, C)` for the constant function `g = λ_:A. v`, given `⊢ v ∈ C`.
///
/// One [`derived::funcs::lambda_n`] over the body `co(v,x) = v`, typed by
/// [`derived::ext::lam_in_funspace_n`]. It is the cheapest genuine inhabitant
/// of a function space over a domain with more than one element, which is what
/// a `node` needs and what a one-point graph cannot supply.
fn const_fun(env: &mut Env, b: &Built, a: &Term, v: &Term, v_mem: &Thm) -> (Term, Thm) {
    let s = b.s().clone();
    let (co, co_ax) = abbrev(env, 2, |args| args[0].clone());
    let (lam, lam_ax) = derived::funcs::lambda_n(env, &s.ap, co).expect("the lambda graph");
    let typing = derived::ext::lam_in_funspace_n(env, &s.ap, &s.prod, &s.fs, co, lam, &lam_ax)
        .expect("a lambda graph is a function");

    let (_, cod) = v_mem.concl().as_mem().expect("a membership");
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let body = {
        let at = inst_all(&co_ax, &[v.clone(), tx.clone()]).expect("co(v,x) = v");
        let cod = cod.clone();
        rw_back(env, &at, move |t| Formula::mem(t, cod.clone()), v_mem)
    };
    let vals = Thm::gen(xv, &a1i(&body, Formula::mem(tx, a.clone())));
    let g = Term::apply(lam, vec![v.clone(), a.clone()]);
    let fs = Thm::mp(
        &inst_all(&typing, &[v.clone(), a.clone(), cod]).expect("instantiate"),
        &vals,
    )
    .expect("the values land");
    (g, fs)
}

// ─────────────────────────────────────────────────────────────────────────────
// The construction
// ─────────────────────────────────────────────────────────────────────────────

/// **The family builds at all** — which it did not before the good-set matrix
/// learned the general fibre, and which is what
/// `mini/tests/fixtures/indexed_infinitary_ctor` was exported to ask for.
#[test]
fn an_indexed_family_with_a_function_typed_recursive_argument_builds() {
    let mut env = Env::new();
    let b = build(&mut env);
    assert!(b.fam.rests_on_nothing(), "every exported theorem is a `⊢`");
    assert_eq!(b.fam.carrier.ctors.len(), 3);
}

/// **The matrix quantifies over the constructor's own fibre.**
///
/// `node` and `wide` differ in nothing but their recursive argument's domain,
/// so the two atoms below are the whole content of "the fibre summand row is
/// read at the right constructor index". A clamp `i ↦ min(i,1)` is the
/// identity on `leaf`/`node` and is caught here and only here.
#[test]
fn each_branching_constructor_takes_its_own_fibre() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let pv = b.pv();

    let a_node = b.summand_at(std::slice::from_ref(&pv), 1, 0);
    let a_wide = b.summand_at(std::slice::from_ref(&pv), 2, 0);
    assert_ne!(a_node, a_wide, "a two-element fibre is not a three-element one");
    assert!(b.ind.recargs[0].summands.is_empty(), "leaf has no recursive argument");

    for (i, aj) in [(1usize, a_node), (2usize, a_wide)] {
        let c = &b.fam.carrier.ctors[i];
        assert_eq!(c.mem_atoms.len(), 1 + 1 + 1, "one field, one child, one index");
        let (yv, tv) = (Term::var(c.yvs[0]), Term::var(c.tvs[0]));
        let child = Term::apply(b.decl.spec.ctors_idx[i].rec_args[0][0], vec![pv.clone(), yv]);
        let at_child = b.fam.carrier.ty_of(std::slice::from_ref(&pv), &[child]).expect("the carrier");
        let want = Formula::mem(tv.clone(), s.fs.of(aj.clone(), at_child.clone()));
        assert_eq!(
            c.mem_atoms[1], want,
            "constructor {i}'s recursive premise is a **function into** the family"
        );
        // Inversion hands the same set back — the two rules are the two
        // directions of one atom and must agree on it literally.
        let xs: Vec<Term> = c.xvs.iter().map(|v| Term::var(*v)).collect();
        let res = Term::apply(b.decl.spec.ctors_idx[i].result[0], vec![pv.clone(), Term::var(c.yvs[0])]);
        let want_inv = derived::conj_of(&[
            Formula::eq(
                IndexedDeclSpec::tup(&s, &xs),
                IndexedDeclSpec::tup(&s, &[res]),
            ),
            Formula::mem(tv, s.fs.of(aj, at_child)),
        ])
        .expect("two atoms");
        assert_eq!(
            inv_conclusion(&b, i),
            want_inv,
            "constructor {i}'s inversion returns the field at the set (M) assumed"
        );
    }
}

/// (I)'s conclusion at the working variables — the index equality, then one
/// atom per recursive argument.
fn inv_conclusion(b: &Built, i: usize) -> Formula {
    let c = &b.fam.carrier.ctors[i];
    let mut args: Vec<Term> = c.pvs.iter().map(|v| Term::var(*v)).collect();
    args.extend(c.yvs.iter().map(|v| Term::var(*v)));
    args.extend(c.tvs.iter().map(|v| Term::var(*v)));
    args.extend(c.xvs.iter().map(|v| Term::var(*v)));
    let at = inst_all(&c.inv, &args).expect("(I) at its own variables");
    at.concl().as_imp().expect("an implication").1
}

/// `leaf` lands in the carrier at `zero` — the plain constructor of the same
/// declaration, and the value every branching test hangs its children on.
#[test]
fn leaf_lands_at_zero() {
    let mut env = Env::new();
    let b = build(&mut env);
    let thm = leaf_canon(&mut env, &b);
    let leaf = b.ind.ctor_term(&b.mach, 0, &[b.s().point()], &[]).expect("leaf(•)");
    assert_eq!(*thm.concl(), Formula::mem(leaf, b.fam_at(&b.zero())));
    assert!(closed(thm.concl()) && thm.hyps().is_empty(), "closed and unconditional");
}

/// **`node` fires over a genuinely two-element fibre**, at a constant function
/// whose value is a `leaf`, and the resulting membership is closed.
///
/// The recursive premise is `g ∈ fs(Σ(z::B2), ind(1, zero))` — a *function into*
/// the family, not an element of it — so this is the first indexed constructor
/// in the project whose child obligation is discharged pointwise.
#[test]
fn node_fires_over_a_two_element_fibre() {
    let mut env = Env::new();
    let b = build(&mut env);
    let pt = b.s().point();
    let leaf = b.ind.ctor_term(&b.mach, 0, std::slice::from_ref(&pt), &[]).expect("leaf(•)");
    let canon = leaf_canon(&mut env, &b);

    // The child's index is the plain field `n`, so `n := zero` puts the
    // children at `ind(1, zero)` — where a `leaf` lives.
    let ys = [b.zero()];
    let child_set = {
        let d = Term::apply(b.decl.spec.ctors_idx[1].rec_args[0][0], vec![b.p(), b.zero()]);
        b.fam.carrier.ty_of(&[b.p()], &[d]).expect("the carrier")
    };
    let d_eq = inst_all(b.decl.rec_ax[1].as_ref().expect("node has one"), &[b.p(), b.zero()])
        .expect("d(α,n) = n");
    let at_sym = {
        let (leaf, ty, p) = (leaf.clone(), b.fam.carrier.ty, b.p());
        rw_back(
            &mut env,
            &d_eq,
            move |x| Formula::mem(leaf.clone(), Term::apply(ty, vec![p.clone(), x])),
            &canon,
        )
    };
    assert_eq!(*at_sym.concl(), Formula::mem(leaf.clone(), child_set.clone()));

    let a_node = b.summand_at(&[b.p()], 1, 0);
    let (g, g_fs) = const_fun(&mut env, &b, &a_node, &leaf, &at_sym);
    assert_eq!(*g_fs.concl(), Formula::mem(g.clone(), b.s().fs.of(a_node, child_set)));

    let c = &b.fam.carrier.ctors[1];
    let n_mem = beta_typing(&mut env, &b, 1, 0, &ys, &inj_pt_mem(&b.mach, 4, 0));
    let e_mem = index_typing(&mut env, &b, 1, &ys, &inj_pt_mem(&b.mach, 4, 1));
    assert_eq!(c.mem_atoms.len(), 3, "one field, one child, one index typing");
    let at = inst_all(&c.mem, &[b.p(), b.zero(), g.clone()]).expect("(M) at α := 1");
    // (M)'s antecedent is the carrier's order: the plain field, then the
    // recursive one, then the result-index typing.
    let have = conj_thms(&[n_mem, g_fs, e_mem]);
    assert_eq!(
        *have.concl(),
        at.concl().as_imp().expect("an implication").0,
        "the discharged conjunction is (M)'s own antecedent"
    );
    let mem = Thm::mp(&at, &have).expect("(M)'s antecedent, discharged");

    // **`ctor_term_at`, at `α := 1`.** A constructor taking `RecArg::general`
    // dispatches over `Σ(z::γⱼ(p⃗))`, so its term mentions the parameters even
    // at parameter-free arguments — and `ctor_term` states it at the
    // *declaration's* variable, which is not what `mem` was instantiated at.
    let node = b
        .ind
        .ctor_term_at(&b.mach, 1, &ys, &[g], &[b.p()])
        .expect("node(zero, g)");
    let res_eq = b.res_eq(1, &ys);
    let out = rw(&mut env, &res_eq, |x| Formula::mem(node.clone(), b.fam_at(&x)), &mem);
    assert_eq!(*out.concl(), Formula::mem(node, b.fam_at(&b.succ())));
    assert!(closed(out.concl()) && out.hyps().is_empty(), "closed and unconditional");
    // …at a different index from the one its children live at, so the family
    // really is indexed and the successor really moved.
    assert_ne!(b.fam_at(&b.succ()), b.fam_at(&b.zero()));
}

/// **The negative polarity, quantified over the whole skeleton**: the carrier
/// is empty at a height no constructor produces.
///
/// Every constructor has to be refuted, the two branching ones included, and
/// the refutation reads the matrix's **base-case** conjunct — atom `0`, whose
/// position is what "still one atom" buys.
#[test]
fn the_carrier_is_empty_at_a_height_no_constructor_produces() {
    let mut env = Env::new();
    let b = build(&mut env);
    let s = b.s().clone();
    let two = b.two();
    let pv = b.pv();

    // Per constructor, `⊢ ∀y⃗. ¬(tup(two) = tup(eᵢ₀(p⃗,y⃗)))`, at the
    // declaration's own parameter variable — which `empty_at_index` closes
    // over at the end.
    let mut refutations = Vec::with_capacity(3);
    for i in 0..3 {
        let k = b.decl.spec.base.ctors[i].args.len();
        let yvs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let ys: Vec<Term> = yvs.iter().map(|v| Term::var(*v)).collect();
        let res_eq = b.res_eq_at(std::slice::from_ref(&pv), i, &ys);
        let (sym, value) = res_eq.concl().as_eq().expect("an equation");
        // `tup(two) = tup(value)` forces `two = value` by pair injectivity.
        let inj = inst_all(
            &s.ap.pair_inj,
            &[two.clone(), s.point(), value.clone(), s.point()],
        )
        .expect("pair injectivity");
        let head = syl(
            &inj,
            &and_left(
                Formula::eq(two.clone(), value.clone()),
                Formula::eq(s.point(), s.point()),
            ),
        )
        .expect("syl");
        // `Inj₂(•) ≠ Inj₀(•)` and `Inj₂(•) ≠ Inj₁(•)`.
        let other = if i == 0 { 0 } else { 1 };
        let ne = b.mach.syms.inj_distinct(&mut env, &s, 2, other).expect("distinct");
        let ne_at = inst_all(&ne, &[s.point(), s.point()]).expect("at •");
        let refuted = syl(&head, &ne_at).expect("⊥");
        // …stated back at the index **symbol**, which is what `vacuous` reads.
        let tup_two = IndexedDeclSpec::tup(&s, std::slice::from_ref(&two));
        let sc = s.clone();
        let back = rw_back(
            &mut env,
            &res_eq,
            move |x| {
                Formula::not(Formula::eq(tup_two.clone(), IndexedDeclSpec::tup(&sc, &[x])))
            },
            &refuted,
        );
        assert_eq!(
            *back.concl(),
            Formula::not(Formula::eq(
                IndexedDeclSpec::tup(&s, std::slice::from_ref(&two)),
                IndexedDeclSpec::tup(&s, &[sym])
            ))
        );
        refutations.push(gen_all(&yvs, &back));
    }

    let thm = empty_at_index(
        &mut env,
        &b.mach,
        &b.ind,
        &b.decl.spec,
        &b.fam.ix,
        &b.fam.gv,
        &b.fam.gs,
        &b.fam.good,
        &b.fam.carrier,
        &b.rc,
        std::slice::from_ref(&two),
        &refutations,
    )
    .expect("the carrier is empty there");
    let at = inst_all(&thm, &[b.p()]).expect("at α := 1");
    let zv = env.fresh_var();
    assert_eq!(
        *at.concl(),
        Formula::forall(
            zv,
            Formula::not(Formula::mem(Term::var(zv), b.fam_at(&two)))
        ),
        "nothing at all is in the carrier at Inj₂(•)"
    );
    assert!(closed(at.concl()) && at.hyps().is_empty());
    // …and it is a *different* set from the one a `leaf` inhabits.
    assert_ne!(b.fam_at(&two), b.fam_at(&b.zero()));
}
