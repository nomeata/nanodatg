//! **The dependent sum `Σx : dom(p⃗). fib(p⃗,x)`**, as one Replacement and one
//! Separation, with its introduction rule and both projections.
//!
//! # What the thesis asks for
//!
//! §5.2's rule for a constructor's *non-recursive* argument
//! (`thesis.txt:1795–1797`) is
//!
//! ```text
//! Γ ⊢ β : U_ℓ'    Γ, y : β; t : ∀x :: α. U_ℓ ⊢ τ ctor ⇒ A; p.B; pgx.G
//! ─────────────────────────────────────────────────────────────────────────
//! Γ; t : ∀x :: α. U_ℓ ⊢ ∀y : β. τ ctor ⇒ Σy' : β. A[y'/y];
//!                                        p'. B[π₁p'/y][π₂p'/p];
//!                                        p'gx. G[π₁p'/y][π₂p'/p]
//! ```
//!
//! Three things in that rule are load-bearing and this file supplies all three:
//! the `Σ` is **dependent** (`A` is derived in the extended context `Γ, y : β`,
//! so a later argument's type may mention an earlier one *and* the ambient
//! parameters `Γ`); the packing is by **pairing**; and the unpacking is by the
//! **projections** `π₁`, `π₂` — literal term-formers, substituted into `B` and
//! `G`, not an existential saying what the components would have been.
//!
//! # The construction
//!
//! ```text
//! img(p⃗)  := { fib(p⃗,x) : x ∈ dom(p⃗) }                          Replacement
//! Σ(p⃗)    := { q ∈ dom(p⃗) × ⋃img(p⃗) : π₂q ∈ fib(p⃗, π₁q) }        Separation
//! ```
//!
//! which is `INDUCTIVES.md`'s glue-type definition
//! `Σ_{x∈A} B(x) := { p ∈ A × ⋃img(B) : snd p ∈ B(fst p) }` with a parameter
//! list added. `⋃img` is the same codomain trick [`crate::ext::dprod`] uses for
//! the dependent *product*, and for the same reason: the second component has
//! to live in *some* set before Separation can speak of it, and the union of
//! the fibres is the cheapest total choice.
//!
//! # Why `dom` and `fib` are symbols and `p⃗` is a list
//!
//! The kernel exposes substitution into a *formula* but not into a *term*
//! ([`kernel::Formula::subst`] has no `Term` counterpart), so `fib(p⃗, a)` at an
//! arbitrary `a` — which is exactly what `B[π₁p'/y]` needs — can only be
//! written if the fibre is a function **symbol**. That is not a workaround: it
//! is what makes [`super::telescope`] able to state the `i`-th projection's
//! type as `dom_i(p⃗, π₁q, π₁π₂q, …)`, i.e. the thesis's iterated
//! `[π₁p'/y][π₂p'/p]`.
//!
//! The parameter list `p⃗` carries two different things at once and both are
//! needed: the inductive's own parameters (`α` in `List α`), which are fixed
//! throughout a declaration, and the *earlier telescope variables*, which is
//! what makes the `Σ` dependent.
//!
//! # Interface
//!
//! With `k = dom.arity()` and `fib.arity() = k + 1`:
//!
//! ```text
//! ⊢ ∀p⃗ ∀w. (w ∈ img(p⃗) ↔ ∃x. (x ∈ dom(p⃗) ∧ w = fib(p⃗,x)))               [DSum::img_ax]
//! ⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) ↔ (q ∈ dom(p⃗) × ⋃img(p⃗) ∧ π₂q ∈ fib(p⃗,π₁q)))      [DSum::sigma_ax]
//! ⊢ ∀p⃗ ∀a ∀v. ((a ∈ dom(p⃗) ∧ v ∈ fib(p⃗,a)) → ⟨a,v⟩ ∈ Σ(p⃗))             [DSum::intro]
//! ⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) → π₁q ∈ dom(p⃗))                                   [DSum::fst_mem]
//! ⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) → π₂q ∈ fib(p⃗,π₁q))                               [DSum::snd_mem]
//! ⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) → ⟨π₁q,π₂q⟩ = q)                                  [DSum::eta]
//! ```
//!
//! The last three are the thesis's projection and η rules at a `Σ`, which
//! [`crate::proj`] has only at a term already written as a pair;
//! [`super::pair_parts`] is what bridges the two, and `snd_mem` is the *only*
//! one of the three that reads straight off the defining axiom.
//!
//! # Nothing here is an axiom
//!
//! One Replacement (`img`, whose `∃!` premise is
//! [`crate::exists_unique_eq`] and costs nothing) and one Separation
//! ([`crate::funcs::separation_full`], unconditional, so the symbol is the
//! intended set whether or not anything is in it). Two definitional
//! extensions, no new axiom.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::proj::Proj;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all,
    syl,
};

/// The dependent sum over a `k`-ary domain symbol and a `(k+1)`-ary fibre
/// symbol, with everything derived about it.
pub struct DSum {
    /// The `k` parameter variables every statement is quantified over.
    pub params: Vec<FreeVar>,
    /// The domain symbol, arity `k`.
    pub dom: FnSym,
    /// The fibre symbol, arity `k + 1`.
    pub fib: FnSym,
    /// `img(p⃗) = { fib(p⃗,x) : x ∈ dom(p⃗) }`, arity `k`.
    pub img: FnSym,
    /// `⊢ ∀p⃗ ∀w. (w ∈ img(p⃗) ↔ ∃x. (x ∈ dom(p⃗) ∧ w = fib(p⃗,x)))`.
    pub img_ax: Thm,
    /// The `Σ` symbol itself, arity `k`.
    pub sigma: FnSym,
    /// `⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) ↔ (q ∈ dom(p⃗) × ⋃img(p⃗) ∧ π₂q ∈ fib(p⃗,π₁q)))`.
    pub sigma_ax: Thm,
    /// `⊢ ∀p⃗ ∀a ∀v. ((a ∈ dom(p⃗) ∧ v ∈ fib(p⃗,a)) → ⟨a,v⟩ ∈ Σ(p⃗))`.
    pub intro: Thm,
    /// `⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) → π₁q ∈ dom(p⃗))`.
    pub fst_mem: Thm,
    /// `⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) → π₂q ∈ fib(p⃗,π₁q))`.
    pub snd_mem: Thm,
    /// `⊢ ∀p⃗ ∀q. (q ∈ Σ(p⃗) → ⟨π₁q,π₂q⟩ = q)` — the thesis's η rule at a `Σ`.
    pub eta: Thm,
}

impl DSum {
    /// The term `Σ(p⃗)` at caller-supplied parameters.
    pub fn of(&self, args: Vec<Term>) -> Term { Term::apply(self.sigma, args) }
}

/// Introduce `img` and `Σ` and derive all six theorems.
///
/// `pparts` must be [`super::product_parts`] over the same product and
/// projections — it is instantiated and its shape checked, so a theorem about
/// a different pairing is refused rather than silently used. Returns `None`
/// unless `fib.arity() == dom.arity() + 1`.
pub fn dsum(env: &mut Env, s: &Sums, proj: &Proj, pparts: &Thm, dom: FnSym, fib: FnSym) -> Option<DSum> {
    let k = dom.arity() as usize;
    if fib.arity() as usize != k + 1 {
        return None
    }
    let ap = &s.ap;
    let params: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    let d = Term::apply(dom, ps.clone());
    let fib_at = |t: Term| {
        let mut args = ps.clone();
        args.push(t);
        Term::apply(fib, args)
    };

    // ── `img(p⃗) = { fib(p⃗,x) : x ∈ dom(p⃗) }`, by Replacement ───────────────
    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let fib_x = fib_at(tx.clone());
    let (wv, phi, exu) = crate::exists_unique_eq(env, &[], &fib_x);
    let repl = Thm::ax_replacement(env, xv, wv, phi.clone())?;
    let repl_at = inst_all(&repl, std::slice::from_ref(&d))?;
    let premise = Thm::gen(xv, &a1i(&exu, Formula::mem(tx.clone(), d.clone())));
    let img_ex = Thm::mp(&repl_at, &premise)?;
    let img_cond = Formula::exists(
        xv,
        Formula::and(Formula::mem(tx.clone(), d.clone()), phi.clone()),
    );
    let (img, img_ax) = crate::define_by_membership(env, &params, &img_ex, wv, &img_cond)?;
    let base = ap.sets.union_of(Term::apply(img, ps.clone()));

    // ── `Σ(p⃗) = { q ∈ dom(p⃗) × ⋃img(p⃗) : π₂q ∈ fib(p⃗, π₁q) }` ─────────────
    let qv = env.fresh_var();
    let tq = Term::var(qv);
    let carrier = s.prod.of(d.clone(), base.clone());
    let psi = Formula::mem(
        proj.snd_of(ap, tq.clone()),
        fib_at(proj.fst_of(ap, tq.clone())),
    );
    let sig_ex = crate::funcs::separation_full(env, qv, &psi, &carrier, &ap.empty_ax)?;
    let guard = Formula::and(Formula::mem(tq.clone(), carrier.clone()), psi.clone());
    let (sigma, sigma_ax) = crate::define_by_membership(env, &params, &sig_ex, qv, &guard)?;

    // ── The introduction rule ───────────────────────────────────────────────
    let (aav, vvv) = (env.fresh_var(), env.fresh_var());
    let (taa, tvv) = (Term::var(aav), Term::var(vvv));
    let fib_a = fib_at(taa.clone());
    let h = Formula::and(
        Formula::mem(taa.clone(), d.clone()),
        Formula::mem(tvv.clone(), fib_a.clone()),
    );
    let h_a = and_left(
        Formula::mem(taa.clone(), d.clone()),
        Formula::mem(tvv.clone(), fib_a.clone()),
    );
    let h_v = and_right(
        Formula::mem(taa.clone(), d.clone()),
        Formula::mem(tvv.clone(), fib_a.clone()),
    );

    // `H → fib(p⃗,a) ∈ img(p⃗)`, witnessed by `x := a`.
    let h_img = {
        let mut args = ps.clone();
        args.push(fib_a.clone());
        let img_at = inst_all(&img_ax, &args)?;
        let body = Formula::and(
            Formula::mem(tx.clone(), d.clone()),
            Formula::eq(fib_a.clone(), fib_x.clone()),
        );
        let witness = exists_intro_imp(xv, body, taa.clone())?;
        let h_body = hyp_and(&h_a, &a1i(&Thm::eq_refl(fib_a.clone()), h.clone()))?;
        syl(&syl(&h_body, &witness)?, &iff_mpr(&img_at)?)?
    };

    // `H → v ∈ ⋃img(p⃗)`.
    let h_base = {
        let ui = crate::funcs::union_intro(
            env,
            &ap.sets,
            Term::apply(img, ps.clone()),
            fib_a.clone(),
            tvv.clone(),
        )?;
        hyp_mp(&a1i(&ui, h.clone()), &hyp_and(&h_img, &h_v)?)?
    };

    // `H → ⟨a,v⟩ ∈ dom(p⃗) × ⋃img(p⃗)`.
    let pav = ap.sets.pair(taa.clone(), tvv.clone());
    let h_prod = {
        let pip = inst_all(
            &s.pair_in_prod,
            &[d.clone(), base.clone(), taa.clone(), tvv.clone()],
        )?;
        hyp_mp(&a1i(&iff_mpr(&pip)?, h.clone()), &hyp_and(&h_a, &h_base)?)?
    };

    // `H → π₂⟨a,v⟩ ∈ fib(p⃗, π₁⟨a,v⟩)`, by rewriting both projections away.
    let h_guard = {
        let e_fst = inst_all(&proj.fst, &[taa.clone(), tvv.clone()])?;
        let e_snd = inst_all(&proj.snd, &[taa.clone(), tvv.clone()])?;
        let (fst_p, snd_p) = (proj.fst_of(ap, pav.clone()), proj.snd_of(ap, pav.clone()));
        let hole = env.fresh_var();
        let move_snd = Thm::mp(
            &Thm::eq_leibniz(
                tvv.clone(),
                snd_p.clone(),
                hole,
                Formula::mem(Term::var(hole), fib_a.clone()),
            ),
            &crate::eq_symm(env, &e_snd)?,
        )?;
        let hole2 = env.fresh_var();
        let move_fst = Thm::mp(
            &Thm::eq_leibniz(
                taa.clone(),
                fst_p.clone(),
                hole2,
                Formula::mem(snd_p.clone(), fib_at(Term::var(hole2))),
            ),
            &crate::eq_symm(env, &e_fst)?,
        )?;
        syl(&h_v, &syl(&move_snd, &move_fst)?)?
    };

    let h_mem = {
        let mut args = ps.clone();
        args.push(pav.clone());
        let sig_at = inst_all(&sigma_ax, &args)?;
        hyp_mp(&a1i(&iff_mpr(&sig_at)?, h.clone()), &hyp_and(&h_prod, &h_guard)?)?
    };
    debug_assert_eq!(
        *h_mem.concl(),
        Formula::imp(h, Formula::mem(pav, Term::apply(sigma, ps.clone()))),
        "dsum: intro has the wrong shape"
    );
    let mut intro_quant = params.clone();
    intro_quant.push(aav);
    intro_quant.push(vvv);
    let intro = gen_all(&intro_quant, &h_mem);

    // ── The two projections and η ───────────────────────────────────────────
    let mut elim_quant = params.clone();
    elim_quant.push(qv);
    let mut args_q = ps.clone();
    args_q.push(tq.clone());
    let fwd = iff_mp(&inst_all(&sigma_ax, &args_q)?)?;
    let mem_carrier = Formula::mem(tq.clone(), carrier.clone());
    let h_carrier = syl(&fwd, &and_left(mem_carrier.clone(), psi.clone()))?;
    let snd_mem = gen_all(&elim_quant, &syl(&fwd, &and_right(mem_carrier, psi.clone()))?);

    let pp = inst_all(pparts, &[d.clone(), base.clone(), tq.clone()])?;
    let (fst_q, snd_q) = (proj.fst_of(ap, tq.clone()), proj.snd_of(ap, tq.clone()));
    let in_dom = Formula::mem(fst_q.clone(), d.clone());
    let in_base = Formula::mem(snd_q.clone(), base.clone());
    let is_eta = Formula::eq(ap.sets.pair(fst_q, snd_q), tq.clone());
    if *pp.concl()
        != Formula::imp(
            Formula::mem(tq.clone(), carrier),
            Formula::and(in_dom.clone(), Formula::and(in_base.clone(), is_eta.clone())),
        )
    {
        return None
    }
    let three = syl(&h_carrier, &pp)?;
    let fst_mem = gen_all(
        &elim_quant,
        &syl(&three, &and_left(in_dom.clone(), Formula::and(in_base.clone(), is_eta.clone())))?,
    );
    let eta = gen_all(
        &elim_quant,
        &syl(
            &syl(&three, &and_right(in_dom, Formula::and(in_base.clone(), is_eta.clone())))?,
            &and_right(in_base, is_eta),
        )?,
    );

    Some(DSum { params, dom, fib, img, img_ax, sigma, sigma_ax, intro, fst_mem, snd_mem, eta })
}
