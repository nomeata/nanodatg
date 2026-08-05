//! The bijection, built at the fixed point — and Cantor–Schröder–Bernstein as a
//! scheme.
//!
//! # Interface
//!
//! With `F`, `G`, `a`, `b` as in [`super::clauses`] and the eight clauses in the
//! order [`csb_clauses`] lists them,
//!
//! ```text
//! H  :=  DOM(F) ∧ (TOT(F) ∧ (SV(F) ∧ (INJ(F)
//!          ∧ (DOM(G) ∧ (TOT(G) ∧ (SV(G) ∧ INJ(G)))))))
//!
//! ⊢ H → a ≈ b                                                    [csb_scheme]
//! ```
//!
//! with `≈` the `kernel::thm::equinumerous` of Tarski's fourth clause. The
//! conclusion is not generalised over anything: `F` and `G` may carry arbitrary
//! further parameters, and it is the caller's business what to do with them.
//! [`super::graph`] and [`super::sandwich`] are the two instances.
//!
//! # The graph
//!
//! Let `c` be [`super::fixpoint::csb_fixpoint`]'s fixed point, so that
//! `z ∈ c ↔ (z ∈ a ∧ ¬∃y. ((y ∈ b ∧ ¬(y ∈ F[c])) ∧ G(y,z)))`. Then
//!
//! ```text
//! Φ(x,y)  :=  (x ∈ c ∧ F(x,y))  ∨  (¬(x ∈ c) ∧ ((y ∈ b ∧ ¬(y ∈ F[c])) ∧ G(y,x)))
//! φ       :=  { p ∈ a × b : ∃x ∃y. (p = ⟨x,y⟩ ∧ Φ(x,y)) }
//! ```
//!
//! — `F` on `c`, and `G`'s converse off it. One
//! [`crate::funcs::separation_full`] over `crate::funspace`'s Cartesian product,
//! which is unconditional, so nothing here needs `a × b` to be inhabited.
//!
//! The **right** disjunct is written with the fixed point's own body rather than
//! as "`x` is a `G`-value of something outside `F[c]`" spelled afresh. That is
//! not cosmetic: it is what makes the two facts the fixed point supplies plug
//! straight in with no rewriting, and it is why `y ∈ b` and `¬(y ∈ F[c])` are
//! carried *inside* the disjunct instead of being recovered later.
//!
//! # Where each of the ten inputs is spent
//!
//! | input | what it does |
//! |---|---|
//! | `DOM(F)` | the pairs of `φ` on `c` land in `a × b` |
//! | `TOT(F)` | `φ` is defined at every `x ∈ c` |
//! | `SV(F)` | `φ` is single-valued on `c` |
//! | `INJ(F)` | `φ` is injective on `c` |
//! | `DOM(G)` | the pairs of `φ` off `c` land in `a × b` |
//! | `TOT(G)` | every `y ∈ b` outside `F[c]` has a preimage — `φ`'s ontoness |
//! | `SV(G)` | `φ` is **injective** off `c` — crosswise, because `G` runs backwards |
//! | `INJ(G)` | `φ` is **single-valued** off `c` — likewise crosswise |
//! | `c` pre-fixed | `¬(x ∈ c)` yields a `G`-preimage: `φ`'s totality off `c` |
//! | `c` post-fixed | `x ∈ c` refutes a `G`-preimage outside `F[c]`: `φ`'s ontoness |
//!
//! `SV(G)` giving injectivity and `INJ(G)` giving single-valuedness is not a
//! transcription slip. `G` runs from `b` to `a`, so what pins `φ`'s *value* off
//! `c` is what pins `G`'s *argument*, which is `G`'s injectivity; and what pins
//! `φ`'s *argument* is what pins `G`'s value, which is `G`'s single-valuedness.
//!
//! Two of the five clauses are where the cases *cross*, and they are the two
//! that would go through without the fixed point being fixed: single-valuedness
//! needs the cases to be mutually exclusive, which they are by construction
//! (`x ∈ c` against `¬(x ∈ c)`), and injectivity needs the *values* not to
//! collide, which is where `¬(y ∈ F[c])` on the right meets `x ∈ c ∧ F(x,y)` on
//! the left.
//!
//! # Why the graph is characterised at fresh variables
//!
//! `⟨u,v⟩ ∈ φ ↔ Φ(u,v)` is proved at two variables `u`, `v` that are **not**
//! `F`'s and `G`'s own `x` and `y`, and that is load-bearing rather than tidy.
//! The separation condition binds `x` and `y`; stating the biconditional at them
//! would put the term `⟨x,y⟩` on the left of an equation inside those binders,
//! and generalising would capture it. Everything below is therefore proved at
//! `u`, `v` and generalised there.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::funcs::separation_full;
use crate::funcs::{or_intro_left, or_intro_right};
use crate::separation::hyp_syl;
use crate::{
    a1i, and_intro_imp, and_left, and_right, com12, conj_of, conj_proj, eq_symm_imp, ex_falso,
    exists_intro_imp, hyp_and, hyp_iff_mp, hyp_iff_mpr, hyp_mp, hyp_or_elim, iff_mp, iff_mpr,
    imp_mono_r, imp_refl, inst_all, notnot_elim, syl, uncurry,
};

use super::clauses::{in_image, injection_clauses};
use super::fixpoint::csb_fixpoint;
use super::prereq::Csb;
use super::shared::{
    discharge, hyp_contrapos, hyp_exists_mono, hyp_gen, inst_all_imp, open_exists,
    or_left_of_not_right,
};

/// The eight clauses of the scheme's hypothesis, in the order it lists them:
/// `F`'s four from `a` to `b`, then `G`'s four from `b` to `a`.
///
/// Callers need this: [`csb_scheme`] is a scheme, so a caller has to build the
/// very same formulas to use its conclusion, and building them here in one place
/// is what makes the caller's copy match syntactically. The result depends only
/// on `(F, G, xv, bv, a, b)` — the four extra variables the clauses need are all
/// bound in it.
pub fn csb_clauses(
    env: &mut Env,
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    a: &Term,
    codom: &Term,
) -> Option<[Formula; 8]> {
    let (cv1, yv1, cv2, yv2) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let [d1, t1, s1, i1] = injection_clauses(f, xv, bv, cv1, yv1, a, codom)?;
    let [d2, t2, s2, i2] = injection_clauses(g, bv, xv, yv2, cv2, codom, a)?;
    Some([d1, t1, s1, i1, d2, t2, s2, i2])
}

/// Everything the five clauses below share: the working hypothesis `K`, the
/// graph's characteristic biconditional, and the pieces of `Φ` at the two
/// variables the argument runs at.
///
/// Scaffolding, not a construction — it holds no theorem a caller could want and
/// it is private. Its only job is to keep the five clause proofs from each
/// carrying twenty arguments.
struct Ctx<'a> {
    /// `K := (H ∧ FIXED(c)) ∧ MEMQ(φ)`.
    k: Formula,
    /// The eight hypothesis clauses.
    atoms: [Formula; 8],
    /// `⊢ K → atoms[i]`.
    k_cl: Vec<Thm>,
    /// `⊢ K → FIXED(c)`.
    k_fixed: Thm,
    /// `FIXED(c)`.
    fixed_c: Formula,
    /// `⊢ K → ∀u ∀v. (⟨u,v⟩ ∈ φ ↔ Φ(u,v))`, in described-pair form.
    k_pair_all: Thm,
    /// `∀u ∀v. (⟨u,v⟩ ∈ φ ↔ Φ(u,v))`.
    pair_all: Formula,
    /// `⊢ K → (Φ(u,v) → (u ∈ a ∧ v ∈ b))`.
    phi_range: Thm,

    /// `Φ(x,y)` and its two disjuncts, at `F`'s and `G`'s own variables.
    phi_rel: Formula,
    phi_l: Formula,
    phi_r: Formula,
    /// `(y ∈ b ∧ ¬(y ∈ F[c])) ∧ G(y,x)` — the fixed point's own body.
    wit: Formula,
    /// `y ∈ F[c]`.
    img_c: Formula,

    f: &'a Formula,
    g: &'a Formula,
    a: &'a Term,
    codom: &'a Term,
    tc: Term,
    xv: FreeVar,
    bv: FreeVar,
    wv: FreeVar,
    uv: FreeVar,
    vv: FreeVar,
}

impl Ctx<'_> {
    fn under(&self, t: &Thm) -> Thm { a1i(t, self.k.clone()) }

    /// `Φ(s,t)`, `L(s,t)`, `R(s,t)`, `WIT(s,t)` and `y ∈ F[c]` at `t`.
    fn phi_at(&self, s: &Term, t: &Term) -> Formula {
        self.phi_rel.subst(self.xv, s).subst(self.bv, t)
    }
    fn left_at(&self, s: &Term, t: &Term) -> Formula {
        self.phi_l.subst(self.xv, s).subst(self.bv, t)
    }
    fn right_at(&self, s: &Term, t: &Term) -> Formula {
        self.phi_r.subst(self.xv, s).subst(self.bv, t)
    }
    fn wit_at(&self, s: &Term, t: &Term) -> Formula {
        self.wit.subst(self.xv, s).subst(self.bv, t)
    }
    fn img_at(&self, t: &Term) -> Formula { self.img_c.subst(self.bv, t) }
    fn mem_c(&self, s: &Term) -> Formula { Formula::mem(s.clone(), self.tc.clone()) }
    fn f_at(&self, s: &Term, t: &Term) -> Formula {
        self.f.subst(self.xv, s).subst(self.bv, t)
    }
    fn g_at(&self, t: &Term, s: &Term) -> Formula {
        self.g.subst(self.xv, s).subst(self.bv, t)
    }
    /// `Φ(c)(s)`, the fixed point's operator — `s ∈ a ∧ ¬∃y. WIT(s,y)`.
    fn step_at(&self, s: &Term) -> Formula {
        Formula::and(
            Formula::mem(s.clone(), self.a.clone()),
            Formula::not(Formula::exists(self.bv, self.wit.subst(self.xv, s))),
        )
    }
    /// `⊢ K → (s ∈ c ↔ Φ(c)(s))`.
    fn fixed_at(&self, s: &Term) -> Option<Thm> {
        syl(&self.k_fixed, &Thm::ax_inst(self.fixed_c.clone(), s.clone())?)
    }
    /// `⊢ K → (⟨s,t⟩ ∈ φ ↔ Φ(s,t))`, in the described-pair form `equinumerous`
    /// is written with.
    fn pair_at(&self, s: &Term, t: &Term) -> Option<Thm> {
        let one = Thm::ax_inst(self.pair_all.clone(), s.clone())?;
        let two = Thm::ax_inst(one.concl().as_imp()?.1, t.clone())?;
        syl(&syl(&self.k_pair_all, &one)?, &two)
    }
}

/// `⊢ H → a ≈ b` — **Cantor–Schröder–Bernstein**, as a scheme in two
/// two-variable formulas.
///
/// `xv` and `bv` are the distinguished variables: `F(x,y)` runs from `a` to `b`
/// and `G(y,x)` back. `a` and `codom` must mention neither. See the module
/// header for the graph and for where each hypothesis is spent.
#[allow(clippy::too_many_arguments)]
pub fn csb_scheme(
    env: &mut Env,
    s: &Csb,
    f: &Formula,
    g: &Formula,
    xv: FreeVar,
    bv: FreeVar,
    a: &Term,
    codom: &Term,
) -> Option<Thm> {
    if xv == bv
        || a.occurs_free(xv)
        || a.occurs_free(bv)
        || codom.occurs_free(xv)
        || codom.occurs_free(bv)
    {
        return None
    }
    let atoms = csb_clauses(env, f, g, xv, bv, a, codom)?;
    let h = conj_of(&atoms)?;
    let (tx, ty) = (Term::var(xv), Term::var(bv));

    // The working variables. Every one of them is bound in the conclusion.
    let (dv, wv) = (env.fresh_var(), env.fresh_var());
    let (cset, phiv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (uv, vv, uv2, vv2) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (x3, y3, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    for v in [dv, wv, cset, phiv, pv, uv, vv, uv2, vv2, x3, y3, fv] {
        if f.occurs_free(v)
            || g.occurs_free(v)
            || a.occurs_free(v)
            || codom.occurs_free(v)
            || v == xv
            || v == bv
        {
            return None
        }
    }
    let (tc, tphi) = (Term::var(cset), Term::var(phiv));
    let (tu, tv) = (Term::var(uv), Term::var(vv));
    let (tu2, tv2) = (Term::var(uv2), Term::var(vv2));
    let (tx3, ty3) = (Term::var(x3), Term::var(y3));

    // ── The fixed point, and the graph written with its own body ────────────
    let fixpt = csb_fixpoint(env, &s.ap.empty_ax, f, g, xv, bv, a, codom)?;
    let fixed_c = super::clauses::fixed(f, g, xv, bv, dv, wv, &tc, a, codom)?;
    debug_assert_eq!(
        *fixpt.concl(),
        Formula::exists(cset, fixed_c.clone()),
        "csb_scheme: the fixed point is not the statement expected"
    );

    let img_c = in_image(f, xv, wv, &tc)?;
    let wit = Formula::and(
        Formula::and(Formula::mem(ty.clone(), codom.clone()), Formula::not(img_c.clone())),
        g.clone(),
    );
    let mem_x_c = Formula::mem(tx.clone(), tc.clone());
    let phi_l = Formula::and(mem_x_c.clone(), f.clone());
    let phi_r = Formula::and(Formula::not(mem_x_c.clone()), wit.clone());
    let phi_rel = Formula::or(phi_l.clone(), phi_r.clone());
    debug_assert_eq!(
        Thm::ax_inst(fixed_c.clone(), tx.clone())?.concl().as_imp()?.1,
        Formula::iff(
            mem_x_c.clone(),
            Formula::and(
                Formula::mem(tx.clone(), a.clone()),
                Formula::not(Formula::exists(bv, wit.clone()))
            )
        ),
        "csb_scheme: the graph is not written with the fixed point's own body"
    );

    // ── `φ := { p ∈ a × b : ∃x ∃y. (p = ⟨x,y⟩ ∧ Φ(x,y)) }` ──────────────────
    let prod_t = s.prod.of(a.clone(), codom.clone());
    let tp = Term::var(pv);
    let sep_body = Formula::exists(
        xv,
        Formula::exists(
            bv,
            Formula::and(
                Formula::eq(tp.clone(), s.ap.sets.pair(tx.clone(), ty.clone())),
                phi_rel.clone(),
            ),
        ),
    );
    let sep = separation_full(env, pv, &sep_body, &prod_t, &s.ap.empty_ax)?;
    let memq = Formula::forall(
        pv,
        Formula::iff(
            Formula::mem(tp.clone(), tphi.clone()),
            Formula::and(Formula::mem(tp.clone(), prod_t.clone()), sep_body.clone()),
        ),
    );
    debug_assert_eq!(
        *sep.concl(),
        Formula::exists(phiv, memq.clone()),
        "csb_scheme: separation_full did not produce the graph's characteristic property"
    );

    // ── `K := (H ∧ FIXED(c)) ∧ MEMQ(φ)` ─────────────────────────────────────
    let h2 = Formula::and(h.clone(), fixed_c.clone());
    let k = Formula::and(h2.clone(), memq.clone());
    let k_h2 = and_left(h2.clone(), memq.clone());
    let k_memq = and_right(h2.clone(), memq.clone());
    let k_h = syl(&k_h2, &and_left(h.clone(), fixed_c.clone()))?;
    let k_fixed = syl(&k_h2, &and_right(h.clone(), fixed_c.clone()))?;
    let k_cl: Vec<Thm> =
        (0..8).map(|i| syl(&k_h, &conj_proj(&atoms, i)?)).collect::<Option<_>>()?;

    // A context with the two derived facts still missing; they are filled in
    // below, since building them is what the rest of this block does.
    let mut cx = Ctx {
        k: k.clone(),
        atoms: atoms.clone(),
        k_cl,
        k_fixed,
        fixed_c: fixed_c.clone(),
        k_pair_all: imp_refl(k.clone()),
        pair_all: Formula::false_(),
        phi_range: imp_refl(k.clone()),
        phi_rel: phi_rel.clone(),
        phi_l: phi_l.clone(),
        phi_r: phi_r.clone(),
        wit: wit.clone(),
        img_c: img_c.clone(),
        f,
        g,
        a,
        codom,
        tc: tc.clone(),
        xv,
        bv,
        wv,
        uv,
        vv,
    };

    // ── `⊢ K → (Φ(u,v) → (u ∈ a ∧ v ∈ b))` ──────────────────────────────────
    let (mem_u_a, mem_v_b) =
        (Formula::mem(tu.clone(), a.clone()), Formula::mem(tv.clone(), codom.clone()));
    let phi_uv = cx.phi_at(&tu, &tv);
    let (l_uv, r_uv) = (cx.left_at(&tu, &tv), cx.right_at(&tu, &tv));
    let wit_uv = cx.wit_at(&tu, &tv);
    let phi_range_thm = {
        let kp = Formula::and(k.clone(), phi_uv.clone());
        let kp_k = and_left(k.clone(), phi_uv.clone());
        let kp_phi = and_right(k.clone(), phi_uv.clone());
        let goal = Formula::and(mem_u_a.clone(), mem_v_b.clone());

        let fdom_at = inst_all_imp(&atoms[0], &[tu.clone(), tv.clone()])?;
        let left = hyp_syl(
            &a1i(&and_right(cx.mem_c(&tu), cx.f_at(&tu, &tv)), kp.clone()),
            &syl(&syl(&kp_k, &cx.k_cl[0])?, &fdom_at)?,
        )?;

        let head_uv = Formula::and(mem_v_b.clone(), Formula::not(cx.img_at(&tv)));
        let get_g = syl(
            &and_right(Formula::not(cx.mem_c(&tu)), wit_uv.clone()),
            &and_right(head_uv.clone(), cx.g_at(&tv, &tu)),
        )?;
        let swap = hyp_and(
            &and_right(mem_v_b.clone(), mem_u_a.clone()),
            &and_left(mem_v_b.clone(), mem_u_a.clone()),
        )?;
        let gdom_at = syl(
            &inst_all_imp(&atoms[4], &[tv.clone(), tu.clone()])?,
            &imp_mono_r(&swap, cx.g_at(&tv, &tu))?,
        )?;
        let right =
            hyp_syl(&a1i(&get_g, kp.clone()), &syl(&syl(&kp_k, &cx.k_cl[4])?, &gdom_at)?)?;

        let both = hyp_or_elim(&kp_phi, &left, &right)?;
        debug_assert_eq!(both.concl().as_imp()?.1, goal, "csb_scheme: phi_range's shape");
        uncurry(&both)?
    };
    cx.phi_range = phi_range_thm;

    // ── `⊢ K → ∀u ∀v. (⟨u,v⟩ ∈ φ ↔ Φ(u,v))` ─────────────────────────────────
    let pair_uv = s.ap.sets.pair(tu.clone(), tv.clone());
    let sep_at_uv = sep_body.subst(pv, &pair_uv);
    let backward = {
        let kp = Formula::and(k.clone(), phi_uv.clone());
        let kp_k = and_left(k.clone(), phi_uv.clone());
        let kp_phi = and_right(k.clone(), phi_uv.clone());
        let kp_range = hyp_mp(&syl(&kp_k, &cx.phi_range)?, &kp_phi)?;
        let pip = inst_all(&s.pair_in_prod, &[a.clone(), codom.clone(), tu.clone(), tv.clone()])?;
        let kp_prod = hyp_mp(&a1i(&iff_mpr(&pip)?, kp.clone()), &kp_range)?;

        let inner = Formula::and(
            Formula::eq(pair_uv.clone(), s.ap.sets.pair(tu.clone(), ty.clone())),
            phi_rel.subst(xv, &tu),
        );
        let outer = Formula::exists(
            bv,
            Formula::and(
                Formula::eq(pair_uv.clone(), s.ap.sets.pair(tx.clone(), ty.clone())),
                phi_rel.clone(),
            ),
        );
        let step1 = exists_intro_imp(bv, inner.clone(), tv.clone())?;
        let step2 = exists_intro_imp(xv, outer.clone(), tu.clone())?;
        let kp_body = hyp_and(&a1i(&Thm::eq_refl(pair_uv.clone()), kp.clone()), &kp_phi)?;
        let kp_wit = syl(&syl(&kp_body, &step1)?, &step2)?;
        debug_assert_eq!(
            kp_wit.concl().as_imp()?.1,
            sep_at_uv,
            "csb_scheme: the separation witness has the wrong shape"
        );
        let memq_at = syl(&syl(&kp_k, &k_memq)?, &Thm::ax_inst(memq.clone(), pair_uv.clone())?)?;
        uncurry(&hyp_mp(&hyp_iff_mpr(&memq_at)?, &hyp_and(&kp_prod, &kp_wit)?)?)?
    };

    let forward = {
        let mem_pair = Formula::mem(pair_uv.clone(), tphi.clone());
        let k2 = Formula::and(k.clone(), mem_pair.clone());
        let k2_k = and_left(k.clone(), mem_pair.clone());
        let k2_mem = and_right(k.clone(), mem_pair.clone());
        let memq_at = syl(&syl(&k2_k, &k_memq)?, &Thm::ax_inst(memq.clone(), pair_uv.clone())?)?;
        let in_prod = Formula::mem(pair_uv.clone(), prod_t.clone());
        let k2_ex = hyp_mp(
            &hyp_syl(
                &hyp_iff_mp(&memq_at)?,
                &a1i(&and_right(in_prod.clone(), sep_at_uv.clone()), k2.clone()),
            )?,
            &k2_mem,
        )?;

        let inner_x3 = open_exists(&sep_at_uv, &tx3)?;
        let body_33 = open_exists(&inner_x3, &ty3)?;
        let k3 = Formula::and(k2.clone(), inner_x3.clone());
        let k3_inner = and_right(k2.clone(), inner_x3.clone());
        let k4 = Formula::and(k3.clone(), body_33.clone());
        let k4_body = and_right(k3.clone(), body_33.clone());
        let eq_pairs = Formula::eq(pair_uv.clone(), s.ap.sets.pair(tx3.clone(), ty3.clone()));
        let phi_33 = cx.phi_at(&tx3, &ty3);
        debug_assert_eq!(
            body_33,
            Formula::and(eq_pairs.clone(), phi_33.clone()),
            "csb_scheme: the separation body opened to an unexpected shape"
        );
        let k4_eq = syl(&k4_body, &and_left(eq_pairs.clone(), phi_33.clone()))?;
        let k4_phi33 = syl(&k4_body, &and_right(eq_pairs.clone(), phi_33.clone()))?;
        let inj_at =
            inst_all(&s.ap.pair_inj, &[tu.clone(), tv.clone(), tx3.clone(), ty3.clone()])?;
        let k4_both = hyp_mp(&a1i(&inj_at, k4.clone()), &k4_eq)?;
        let (eq_u, eq_v) =
            (Formula::eq(tu.clone(), tx3.clone()), Formula::eq(tv.clone(), ty3.clone()));
        let k4_u = syl(
            &syl(&k4_both, &and_left(eq_u.clone(), eq_v.clone()))?,
            &eq_symm_imp(env, tu.clone(), tx3.clone()),
        )?;
        let k4_v = syl(
            &syl(&k4_both, &and_right(eq_u.clone(), eq_v.clone()))?,
            &eq_symm_imp(env, tv.clone(), ty3.clone()),
        )?;
        let leib_u = Thm::eq_leibniz(tx3.clone(), tu.clone(), xv, phi_rel.subst(bv, &ty3));
        let leib_v = Thm::eq_leibniz(ty3.clone(), tv.clone(), bv, phi_rel.subst(xv, &tu));
        let k4_mid = hyp_mp(&hyp_mp(&a1i(&leib_u, k4.clone()), &k4_u)?, &k4_phi33)?;
        let k4_phi = hyp_mp(&hyp_mp(&a1i(&leib_v, k4.clone()), &k4_v)?, &k4_mid)?;
        debug_assert_eq!(
            k4_phi.concl().as_imp()?.1,
            phi_uv,
            "csb_scheme: the transported condition has the wrong shape"
        );

        let k3_goal = discharge(y3, &k3_inner, &k4_phi)?;
        uncurry(&discharge(x3, &k2_ex, &k3_goal)?)?
    };

    // Translate the constructed pair into the described one `equinumerous` uses.
    let bridge = inst_all(&s.pair_in_bridge, &[tphi.clone(), tu.clone(), tv.clone()])?;
    let described = iff_mp(&bridge)?.concl().as_imp()?.0;
    let iff_uv = hyp_and(
        &hyp_syl(&cx.under(&iff_mp(&bridge)?), &forward)?,
        &hyp_syl(&backward, &cx.under(&iff_mpr(&bridge)?))?,
    )?;
    debug_assert_eq!(
        iff_uv.concl().as_imp()?.1,
        Formula::iff(described.clone(), phi_uv.clone()),
        "csb_scheme: the described-pair biconditional has the wrong shape"
    );
    let pair_all_thm = hyp_gen(uv, &hyp_gen(vv, &iff_uv)?)?;
    cx.pair_all = pair_all_thm.concl().as_imp()?.1;
    cx.k_pair_all = pair_all_thm;

    // ── The five clauses of `equinumerous`, at `φ` ──────────────────────────
    let clause_1 = {
        let at = cx.pair_at(&tu, &tv)?;
        hyp_gen(uv, &hyp_gen(vv, &hyp_syl(&hyp_iff_mp(&at)?, &cx.phi_range)?)?)?
    };
    let clause_2 = total_clause(&cx, &tu, &tv, &mem_u_a, &l_uv, &r_uv, &wit_uv)?;
    let clause_3 = onto_clause(&cx, &tu, &tv, &mem_v_b)?;
    let clause_4 = sv_clause(&cx, &tu, &tv, &tv2, vv2)?;
    let clause_5 = inj_clause(&cx, &tu, &tu2, &tv, uv2)?;

    // ── Assemble, then discharge `φ` and `c` ────────────────────────────────
    let body = bijection_body(env, &Term::var(fv), a, codom);
    let want = conj_of(&body)?;
    debug_assert_eq!(
        Formula::exists(fv, want.clone()),
        kernel::thm::equinumerous(env, a.clone(), codom.clone()),
        "csb_scheme: the bijection body is not the one equinumerous is written with"
    );
    let proved = hyp_and(
        &clause_1,
        &hyp_and(&clause_2, &hyp_and(&clause_3, &hyp_and(&clause_4, &clause_5)?)?)?,
    )?;
    debug_assert_eq!(
        proved.concl().as_imp()?.1,
        want.subst(fv, &tphi),
        "csb_scheme: the five clauses do not assemble into the bijection body"
    );
    let k_equi = syl(&proved, &exists_intro_imp(fv, want, tphi.clone())?)?;

    let h2_goal = discharge(phiv, &a1i(&sep, h2.clone()), &k_equi)?;
    let out = discharge(cset, &a1i(&fixpt, h.clone()), &h2_goal)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, kernel::thm::equinumerous(env, a.clone(), codom.clone())),
        "csb_scheme: wrong shape"
    );
    Some(out)
}

/// `⊢ K → ∀u. (u ∈ a → ∃v. ⟨u,v⟩ ∈ φ)` — the graph is **total** on `a`.
///
/// On `c` that is `TOT(F)`. Off it, it is the fixed point's *pre-fixed* half:
/// `¬(u ∈ c)` refutes `Φ(c)(u)`, and with `u ∈ a` in hand what is left is
/// exactly a `G`-preimage of something outside `F[c]`.
fn total_clause(
    cx: &Ctx<'_>,
    tu: &Term,
    tv: &Term,
    mem_u_a: &Formula,
    l_uv: &Formula,
    r_uv: &Formula,
    wit_uv: &Formula,
) -> Option<Thm> {
    let (k, bv, vv) = (&cx.k, cx.bv, cx.vv);
    let mem_u_c = cx.mem_c(tu);
    let phi_uv = cx.phi_at(tu, tv);
    let t = Formula::and(k.clone(), mem_u_a.clone());
    let t_k = and_left(k.clone(), mem_u_a.clone());
    let t_ua = and_right(k.clone(), mem_u_a.clone());

    let pos = {
        let p = Formula::and(t.clone(), mem_u_c.clone());
        let p_t = and_left(t.clone(), mem_u_c.clone());
        let p_uc = and_right(t.clone(), mem_u_c.clone());
        let ftot_at = Thm::ax_inst(cx.atoms[1].clone(), tu.clone())?;
        let p_ex_f = hyp_mp(
            &syl(&syl(&p_t, &syl(&t_k, &cx.k_cl[1])?)?, &ftot_at)?,
            &syl(&p_t, &t_ua)?,
        )?;
        let mk = hyp_mp(
            &a1i(&and_intro_imp(mem_u_c.clone(), cx.f_at(tu, tv)), p.clone()),
            &p_uc,
        )?;
        let to_phi = hyp_syl(&mk, &a1i(&or_intro_left(l_uv.clone(), r_uv.clone()), p.clone()))?;
        hyp_mp(&hyp_exists_mono(vv, &to_phi)?, &p_ex_f)?
    };

    let neg = {
        let not_uc = Formula::not(mem_u_c.clone());
        let n = Formula::and(t.clone(), not_uc.clone());
        let n_t = and_left(t.clone(), not_uc.clone());
        let n_nuc = and_right(t.clone(), not_uc.clone());
        let step_u = cx.step_at(tu);
        let stop_u = Formula::not(Formula::exists(bv, cx.wit.subst(cx.xv, tu)));
        debug_assert_eq!(step_u, Formula::and(mem_u_a.clone(), stop_u.clone()));
        let n_not_step = hyp_mp(
            &hyp_contrapos(&hyp_iff_mpr(&syl(&syl(&n_t, &t_k)?, &cx.fixed_at(tu)?)?)?)?,
            &n_nuc,
        )?;
        let n_mk = hyp_mp(
            &a1i(&and_intro_imp(mem_u_a.clone(), stop_u.clone()), n.clone()),
            &syl(&n_t, &t_ua)?,
        )?;
        let n_not_stop = hyp_syl(&n_mk, &n_not_step)?;
        let ex_wit = Formula::exists(bv, cx.wit.subst(cx.xv, tu));
        let n_ex = syl(&n_not_stop, &notnot_elim(ex_wit))?;
        let mk = hyp_mp(&a1i(&and_intro_imp(not_uc.clone(), wit_uv.clone()), n.clone()), &n_nuc)?;
        let to_phi = hyp_syl(&mk, &a1i(&or_intro_right(l_uv.clone(), r_uv.clone()), n.clone()))?;
        hyp_mp(&hyp_exists_mono(vv, &to_phi)?, &n_ex)?
    };

    let split = a1i(&imp_refl(Formula::not(mem_u_c)), t.clone());
    let t_ex_phi = hyp_or_elim(&split, &uncurry(&pos)?, &uncurry(&neg)?)?;
    debug_assert_eq!(
        t_ex_phi.concl().as_imp()?.1,
        Formula::exists(vv, phi_uv),
        "total_clause: the case split produced an unexpected shape"
    );
    let to_pair = syl(&t_k, &hyp_iff_mpr(&cx.pair_at(tu, tv)?)?)?;
    let t_ex_pair = hyp_mp(&hyp_exists_mono(vv, &to_pair)?, &t_ex_phi)?;
    hyp_gen(cx.uv, &uncurry(&t_ex_pair)?)
}

/// `⊢ K → ∀v. (v ∈ b → ∃u. ⟨u,v⟩ ∈ φ)` — the graph is **onto** `b`.
///
/// Inside `F[c]` the preimage is the one `F` already had. Outside it, `TOT(G)`
/// supplies a preimage, and the fixed point's *post-fixed* half is what shows
/// that preimage lies outside `c` — which is the case the graph uses `G` on.
fn onto_clause(cx: &Ctx<'_>, tu: &Term, tv: &Term, mem_v_b: &Formula) -> Option<Thm> {
    let (k, xv, bv, wv, uv) = (&cx.k, cx.xv, cx.bv, cx.wv, cx.uv);
    let tw = Term::var(wv);
    let img_v = cx.img_at(tv);
    let phi_uv = cx.phi_at(tu, tv);
    let t = Formula::and(k.clone(), mem_v_b.clone());
    let t_k = and_left(k.clone(), mem_v_b.clone());
    let t_vb = and_right(k.clone(), mem_v_b.clone());

    let pos = {
        let p = Formula::and(t.clone(), img_v.clone());
        let p_img = and_right(t.clone(), img_v.clone());
        let body_w = Formula::and(cx.mem_c(&tw), cx.f_at(&tw, tv));
        debug_assert_eq!(
            img_v,
            Formula::exists(wv, body_w.clone()),
            "onto_clause: the image is not the one the graph is written with"
        );
        debug_assert_eq!(body_w, cx.left_at(&tw, tv), "onto_clause: the image body is not `L`");
        let at_w =
            a1i(&or_intro_left(cx.left_at(&tw, tv), cx.right_at(&tw, tv)), p.clone());
        hyp_mp(&hyp_exists_mono(wv, &at_w)?, &p_img)?
    };

    let neg = {
        let not_img = Formula::not(img_v.clone());
        let n = Formula::and(t.clone(), not_img.clone());
        let n_t = and_left(t.clone(), not_img.clone());
        let n_nimg = and_right(t.clone(), not_img.clone());
        let gtot_at = Thm::ax_inst(cx.atoms[5].clone(), tv.clone())?;
        let n_ex_g = hyp_mp(
            &syl(&syl(&n_t, &syl(&t_k, &cx.k_cl[5])?)?, &gtot_at)?,
            &syl(&n_t, &t_vb)?,
        )?;

        let g_at = cx.g_at(tv, tu);
        debug_assert_eq!(
            gtot_at.concl().as_imp()?.1.as_imp()?.1,
            Formula::exists(xv, cx.g.subst(bv, tv)),
            "onto_clause: TOT(G) instantiated to an unexpected shape"
        );
        let m = Formula::and(n.clone(), g_at.clone());
        let m_n = and_left(n.clone(), g_at.clone());
        let m_g = and_right(n.clone(), g_at.clone());
        let m_wit = hyp_and(
            &hyp_and(&syl(&syl(&m_n, &n_t)?, &t_vb)?, &syl(&m_n, &n_nimg)?)?,
            &m_g,
        )?;
        debug_assert_eq!(
            m_wit.concl().as_imp()?.1,
            cx.wit_at(tu, tv),
            "onto_clause: the stopper body has the wrong shape"
        );
        let wit_u = cx.wit.subst(xv, tu);
        let ex_wit = Formula::exists(bv, wit_u.clone());
        let m_ex_wit = syl(&m_wit, &exists_intro_imp(bv, wit_u, tv.clone())?)?;
        let stop_u = Formula::not(ex_wit.clone());
        let m_step = hyp_iff_mp(&syl(&syl(&m_n, &n_t)?, &syl(&t_k, &cx.fixed_at(tu)?)?)?)?;
        let m_stop = hyp_syl(
            &m_step,
            &a1i(&and_right(Formula::mem(tu.clone(), cx.a.clone()), stop_u.clone()), m.clone()),
        )?;
        let clash = syl(&m_ex_wit, &com12(&imp_refl(stop_u.clone()))?)?;
        let m_nuc = hyp_syl(&m_stop, &clash)?;
        let m_r = hyp_and(&m_nuc, &m_wit)?;
        let m_phi = hyp_mp(
            &a1i(&or_intro_right(cx.left_at(tu, tv), cx.right_at(tu, tv)), m.clone()),
            &m_r,
        )?;
        let m_ex = syl(&m_phi, &exists_intro_imp(uv, phi_uv.clone(), tu.clone())?)?;
        discharge(uv, &n_ex_g, &m_ex)?
    };

    let split = a1i(&imp_refl(Formula::not(img_v)), t.clone());
    let t_ex_phi = hyp_or_elim(&split, &uncurry(&pos)?, &uncurry(&neg)?)?;
    debug_assert_eq!(
        t_ex_phi.concl().as_imp()?.1,
        Formula::exists(uv, phi_uv),
        "onto_clause: the case split produced an unexpected shape"
    );
    let to_pair = syl(&t_k, &hyp_iff_mpr(&cx.pair_at(tu, tv)?)?)?;
    let t_ex_pair = hyp_mp(&hyp_exists_mono(uv, &to_pair)?, &t_ex_phi)?;
    hyp_gen(cx.vv, &uncurry(&t_ex_pair)?)
}

/// `⊢ K → ∀u ∀v ∀v'. ((⟨u,v⟩ ∈ φ ∧ ⟨u,v'⟩ ∈ φ) → v = v')` — **single-valued**.
///
/// The two cases cannot mix, because they are `u ∈ c` and its negation. On `c`
/// this is `SV(F)`; off it, `INJ(G)`.
fn sv_clause(cx: &Ctx<'_>, tu: &Term, tv: &Term, tv2: &Term, vv2: FreeVar) -> Option<Thm> {
    let k = &cx.k;
    let mem_u_c = cx.mem_c(tu);
    let (phi1, phi2) = (cx.phi_at(tu, tv), cx.phi_at(tu, tv2));
    let both = Formula::and(phi1.clone(), phi2.clone());
    let s = Formula::and(k.clone(), both.clone());
    let s_k = and_left(k.clone(), both.clone());
    let s_1 = syl(&and_right(k.clone(), both.clone()), &and_left(phi1.clone(), phi2.clone()))?;
    let s_2 = syl(&and_right(k.clone(), both.clone()), &and_right(phi1.clone(), phi2.clone()))?;

    let pos = {
        let p = Formula::and(s.clone(), mem_u_c.clone());
        let p_s = and_left(s.clone(), mem_u_c.clone());
        let p_uc = and_right(s.clone(), mem_u_c.clone());
        let clash = syl(&p_uc, &com12(&imp_refl(Formula::not(mem_u_c.clone())))?)?;
        let kill = |t: &Term| -> Option<Thm> {
            let get = and_left(Formula::not(mem_u_c.clone()), cx.wit_at(tu, t));
            hyp_syl(&a1i(&get, p.clone()), &clash)
        };
        let p_l1 = or_left_of_not_right(&syl(&p_s, &s_1)?, &kill(tv)?)?;
        let p_l2 = or_left_of_not_right(&syl(&p_s, &s_2)?, &kill(tv2)?)?;
        let get_f = |t: &Term| and_right(mem_u_c.clone(), cx.f_at(tu, t));
        let p_f1 = syl(&p_l1, &get_f(tv))?;
        let p_f2 = syl(&p_l2, &get_f(tv2))?;
        let fsv_at = inst_all_imp(&cx.atoms[2], &[tu.clone(), tv.clone(), tv2.clone()])?;
        hyp_mp(&syl(&syl(&p_s, &syl(&s_k, &cx.k_cl[2])?)?, &fsv_at)?, &hyp_and(&p_f1, &p_f2)?)?
    };

    let neg = {
        let not_uc = Formula::not(mem_u_c.clone());
        let n = Formula::and(s.clone(), not_uc.clone());
        let n_s = and_left(s.clone(), not_uc.clone());
        let n_nuc = and_right(s.clone(), not_uc.clone());
        let not_left = |t: &Term| -> Option<Thm> {
            hyp_syl(&a1i(&and_left(mem_u_c.clone(), cx.f_at(tu, t)), n.clone()), &n_nuc)
        };
        let n_r1 = hyp_mp(&syl(&n_s, &s_1)?, &not_left(tv)?)?;
        let n_r2 = hyp_mp(&syl(&n_s, &s_2)?, &not_left(tv2)?)?;
        let get_g = |t: &Term| -> Thm {
            let head = Formula::and(
                Formula::mem(t.clone(), cx.codom.clone()),
                Formula::not(cx.img_at(t)),
            );
            let inner = and_right(head, cx.g_at(t, tu));
            syl(&and_right(not_uc.clone(), cx.wit_at(tu, t)), &inner).expect("wit's shape")
        };
        let n_g1 = syl(&n_r1, &get_g(tv))?;
        let n_g2 = syl(&n_r2, &get_g(tv2))?;
        let ginj_at = inst_all_imp(&cx.atoms[7], &[tv.clone(), tv2.clone(), tu.clone()])?;
        hyp_mp(&syl(&syl(&n_s, &syl(&s_k, &cx.k_cl[7])?)?, &ginj_at)?, &hyp_and(&n_g1, &n_g2)?)?
    };

    let split = a1i(&imp_refl(Formula::not(mem_u_c)), s.clone());
    let s_eq = uncurry(&hyp_or_elim(&split, &uncurry(&pos)?, &uncurry(&neg)?)?)?;
    from_pairs(cx, &s_eq, &[(tu.clone(), tv.clone()), (tu.clone(), tv2.clone())], &[cx.uv, cx.vv, vv2])
}

/// `⊢ K → ∀u ∀u' ∀v. ((⟨u,v⟩ ∈ φ ∧ ⟨u',v⟩ ∈ φ) → u = u')` — **injective**.
///
/// Four cases: `INJ(F)` on `c`, `SV(G)` off it, and the two mixed ones, which
/// are impossible — a value `F` takes on `c` is in `F[c]`, and the right
/// disjunct says its value is not.
fn inj_clause(cx: &Ctx<'_>, tu: &Term, tu2: &Term, tv: &Term, uv2: FreeVar) -> Option<Thm> {
    let (k, wv) = (&cx.k, cx.wv);
    let tw = Term::var(wv);
    let (phi1, phi2) = (cx.phi_at(tu, tv), cx.phi_at(tu2, tv));
    let both = Formula::and(phi1.clone(), phi2.clone());
    let s = Formula::and(k.clone(), both.clone());
    let s_k = and_left(k.clone(), both.clone());
    let s_1 = syl(&and_right(k.clone(), both.clone()), &and_left(phi1.clone(), phi2.clone()))?;
    let s_2 = syl(&and_right(k.clone(), both.clone()), &and_right(phi1.clone(), phi2.clone()))?;
    let goal = Formula::eq(tu.clone(), tu2.clone());
    let body_w = Formula::and(cx.mem_c(&tw), cx.f_at(&tw, tv));
    let img_v = cx.img_at(tv);

    // Under a hypothesis `hh` carrying `s`, split on `t ∈ c`, refuting the
    // disjunct the case excludes.
    let get_left = |hh: &Formula, h_s: &Thm, h_in: &Thm, side: &Thm, t: &Term| -> Option<Thm> {
        let clash = syl(h_in, &com12(&imp_refl(Formula::not(cx.mem_c(t))))?)?;
        let kill = hyp_syl(
            &a1i(&and_left(Formula::not(cx.mem_c(t)), cx.wit_at(t, tv)), hh.clone()),
            &clash,
        )?;
        or_left_of_not_right(&syl(h_s, side)?, &kill)
    };
    let get_right = |hh: &Formula, h_s: &Thm, h_out: &Thm, side: &Thm, t: &Term| -> Option<Thm> {
        let not_l = hyp_syl(
            &a1i(&and_left(cx.mem_c(t), cx.f_at(t, tv)), hh.clone()),
            h_out,
        )?;
        hyp_mp(&syl(h_s, side)?, &not_l)
    };
    let to_img = |t: &Term| -> Option<Thm> { exists_intro_imp(wv, body_w.clone(), t.clone()) };
    let not_img_from_right = |t: &Term| -> Thm {
        let head = Formula::and(
            Formula::mem(tv.clone(), cx.codom.clone()),
            Formula::not(img_v.clone()),
        );
        syl(
            &and_right(Formula::not(cx.mem_c(t)), cx.wit_at(t, tv)),
            &syl(&and_left(head.clone(), cx.g_at(tv, t)), &and_right(
                Formula::mem(tv.clone(), cx.codom.clone()),
                Formula::not(img_v.clone()),
            ))
            .expect("wit's head"),
        )
        .expect("wit's shape")
    };

    let in1 = cx.mem_c(tu);
    let pos = {
        // `u ∈ c`, then split on `u' ∈ c`.
        let p = Formula::and(s.clone(), in1.clone());
        let p_s = and_left(s.clone(), in1.clone());
        let p_in = and_right(s.clone(), in1.clone());
        let in2 = cx.mem_c(tu2);

        let pp = {
            let q = Formula::and(p.clone(), in2.clone());
            let q_p = and_left(p.clone(), in2.clone());
            let q_in2 = and_right(p.clone(), in2.clone());
            let q_l1 = get_left(&q, &syl(&q_p, &p_s)?, &syl(&q_p, &p_in)?, &s_1, tu)?;
            let q_l2 = get_left(&q, &syl(&q_p, &p_s)?, &q_in2, &s_2, tu2)?;
            let q_f1 = syl(&q_l1, &and_right(cx.mem_c(tu), cx.f_at(tu, tv)))?;
            let q_f2 = syl(&q_l2, &and_right(cx.mem_c(tu2), cx.f_at(tu2, tv)))?;
            let finj_at = inst_all_imp(&cx.atoms[3], &[tu.clone(), tu2.clone(), tv.clone()])?;
            hyp_mp(
                &syl(&syl(&syl(&q_p, &p_s)?, &syl(&s_k, &cx.k_cl[3])?)?, &finj_at)?,
                &hyp_and(&q_f1, &q_f2)?,
            )?
        };
        let pn = {
            let not_in2 = Formula::not(in2.clone());
            let q = Formula::and(p.clone(), not_in2.clone());
            let q_p = and_left(p.clone(), not_in2.clone());
            let q_out = and_right(p.clone(), not_in2.clone());
            let q_l1 = get_left(&q, &syl(&q_p, &p_s)?, &syl(&q_p, &p_in)?, &s_1, tu)?;
            let q_r2 = get_right(&q, &syl(&q_p, &p_s)?, &q_out, &s_2, tu2)?;
            let q_img = syl(&q_l1, &to_img(tu)?)?;
            let q_nimg = syl(&q_r2, &not_img_from_right(tu2))?;
            let bad = hyp_mp(&syl(&q_img, &com12(&imp_refl(Formula::not(img_v.clone())))?)?, &q_nimg)?;
            syl(&bad, &ex_falso(goal.clone()))?
        };
        let split2 = a1i(&imp_refl(Formula::not(in2)), p.clone());
        hyp_or_elim(&split2, &uncurry(&pp)?, &uncurry(&pn)?)?
    };

    let neg = {
        let not_in1 = Formula::not(in1.clone());
        let n = Formula::and(s.clone(), not_in1.clone());
        let n_s = and_left(s.clone(), not_in1.clone());
        let n_out = and_right(s.clone(), not_in1.clone());
        let in2 = cx.mem_c(tu2);

        let np = {
            let q = Formula::and(n.clone(), in2.clone());
            let q_n = and_left(n.clone(), in2.clone());
            let q_in2 = and_right(n.clone(), in2.clone());
            let q_r1 = get_right(&q, &syl(&q_n, &n_s)?, &syl(&q_n, &n_out)?, &s_1, tu)?;
            let q_l2 = get_left(&q, &syl(&q_n, &n_s)?, &q_in2, &s_2, tu2)?;
            let q_img = syl(&q_l2, &to_img(tu2)?)?;
            let q_nimg = syl(&q_r1, &not_img_from_right(tu))?;
            let bad = hyp_mp(&syl(&q_img, &com12(&imp_refl(Formula::not(img_v.clone())))?)?, &q_nimg)?;
            syl(&bad, &ex_falso(goal.clone()))?
        };
        let nn = {
            let not_in2 = Formula::not(in2.clone());
            let q = Formula::and(n.clone(), not_in2.clone());
            let q_n = and_left(n.clone(), not_in2.clone());
            let q_out2 = and_right(n.clone(), not_in2.clone());
            let q_r1 = get_right(&q, &syl(&q_n, &n_s)?, &syl(&q_n, &n_out)?, &s_1, tu)?;
            let q_r2 = get_right(&q, &syl(&q_n, &n_s)?, &q_out2, &s_2, tu2)?;
            let get_g = |t: &Term| -> Thm {
                let head = Formula::and(
                    Formula::mem(tv.clone(), cx.codom.clone()),
                    Formula::not(img_v.clone()),
                );
                syl(
                    &and_right(Formula::not(cx.mem_c(t)), cx.wit_at(t, tv)),
                    &and_right(head, cx.g_at(tv, t)),
                )
                .expect("wit's shape")
            };
            let q_g1 = syl(&q_r1, &get_g(tu))?;
            let q_g2 = syl(&q_r2, &get_g(tu2))?;
            let gsv_at = inst_all_imp(&cx.atoms[6], &[tv.clone(), tu.clone(), tu2.clone()])?;
            hyp_mp(
                &syl(&syl(&syl(&q_n, &n_s)?, &syl(&s_k, &cx.k_cl[6])?)?, &gsv_at)?,
                &hyp_and(&q_g1, &q_g2)?,
            )?
        };
        let split2 = a1i(&imp_refl(Formula::not(in2)), n.clone());
        hyp_or_elim(&split2, &uncurry(&np)?, &uncurry(&nn)?)?
    };

    let split = a1i(&imp_refl(Formula::not(in1)), s.clone());
    let s_eq = uncurry(&hyp_or_elim(&split, &uncurry(&pos)?, &uncurry(&neg)?)?)?;
    from_pairs(cx, &s_eq, &[(tu.clone(), tv.clone()), (tu2.clone(), tv.clone())], &[cx.uv, uv2, cx.vv])
}

/// From `⊢ K → ((Φ(s₁,t₁) ∧ Φ(s₂,t₂)) → χ)` build
/// `⊢ K → ∀⃗v. ((⟨s₁,t₁⟩ ∈ φ ∧ ⟨s₂,t₂⟩ ∈ φ) → χ)`.
///
/// The two clauses that take *two* pairs share this last step; the ones that
/// take one do it inline.
fn from_pairs(cx: &Ctx<'_>, s_eq: &Thm, pts: &[(Term, Term); 2], gens: &[FreeVar; 3]) -> Option<Thm> {
    let k = &cx.k;
    let p1 = hyp_iff_mp(&cx.pair_at(&pts[0].0, &pts[0].1)?)?;
    let p2 = hyp_iff_mp(&cx.pair_at(&pts[1].0, &pts[1].1)?)?;
    let d1 = p1.concl().as_imp()?.1.as_imp()?.0;
    let d2 = p2.concl().as_imp()?.1.as_imp()?.0;
    let dd = Formula::and(d1.clone(), d2.clone());
    let kd_k = and_left(k.clone(), dd.clone());
    let kd_1 = syl(&and_right(k.clone(), dd.clone()), &and_left(d1.clone(), d2.clone()))?;
    let kd_2 = syl(&and_right(k.clone(), dd.clone()), &and_right(d1, d2))?;
    let kd_phi = hyp_and(
        &hyp_mp(&syl(&kd_k, &p1)?, &kd_1)?,
        &hyp_mp(&syl(&kd_k, &p2)?, &kd_2)?,
    )?;
    let kd_eq = hyp_mp(&syl(&kd_k, s_eq)?, &kd_phi)?;
    let out = uncurry(&kd_eq)?;
    hyp_gen(gens[0], &hyp_gen(gens[1], &hyp_gen(gens[2], &out)?)?)
}

/// The five clauses of `kernel::thm::equinumerous`'s body, rebuilt at a term.
///
/// Kept beside the proof rather than imported, so that [`csb_scheme`]'s
/// `debug_assert` compares against a spelling this file owns: a drift in the
/// kernel's clause order is then caught here rather than downstream.
pub(super) fn bijection_body(env: &mut Env, f: &Term, x: &Term, m: &Term) -> [Formula; 5] {
    let (a1, b1) = (env.fresh_var(), env.fresh_var());
    let in_xm = {
        let p = kernel::thm::pair_in(env, f.clone(), Term::var(a1), Term::var(b1));
        let concl = Formula::and(
            Formula::mem(Term::var(a1), x.clone()),
            Formula::mem(Term::var(b1), m.clone()),
        );
        Formula::forall(a1, Formula::forall(b1, Formula::imp(p, concl)))
    };
    let (a2, b2) = (env.fresh_var(), env.fresh_var());
    let total = {
        let p = kernel::thm::pair_in(env, f.clone(), Term::var(a2), Term::var(b2));
        Formula::forall(
            a2,
            Formula::imp(Formula::mem(Term::var(a2), x.clone()), Formula::exists(b2, p)),
        )
    };
    let (a3, b3) = (env.fresh_var(), env.fresh_var());
    let onto = {
        let p = kernel::thm::pair_in(env, f.clone(), Term::var(a3), Term::var(b3));
        Formula::forall(
            b3,
            Formula::imp(Formula::mem(Term::var(b3), m.clone()), Formula::exists(a3, p)),
        )
    };
    let (a4, b4, c4) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let single_valued = {
        let p1 = kernel::thm::pair_in(env, f.clone(), Term::var(a4), Term::var(b4));
        let p2 = kernel::thm::pair_in(env, f.clone(), Term::var(a4), Term::var(c4));
        let concl = Formula::eq(Term::var(b4), Term::var(c4));
        Formula::forall(
            a4,
            Formula::forall(b4, Formula::forall(c4, Formula::imp(Formula::and(p1, p2), concl))),
        )
    };
    let (a5, b5, c5) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let injective = {
        let p1 = kernel::thm::pair_in(env, f.clone(), Term::var(a5), Term::var(c5));
        let p2 = kernel::thm::pair_in(env, f.clone(), Term::var(b5), Term::var(c5));
        let concl = Formula::eq(Term::var(a5), Term::var(b5));
        Formula::forall(
            a5,
            Formula::forall(b5, Formula::forall(c5, Formula::imp(Formula::and(p1, p2), concl))),
        )
    };
    [in_xm, total, onto, single_valued, injective]
}
