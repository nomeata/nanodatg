//! **Totality of the W-type recursor**, and the ι rule with its guard removed.
//!
//! # What this file is
//!
//! [`crate::wrec`] builds the recursor as the union of all attempts and proves
//! everything about it *except* that its domain is all of `W`. That last step —
//! step 4 of `INDUCTIVES.md`'s recipe — is here, together with the two things
//! it immediately buys: `wrec ∈ fs(W,T)` and the **unguarded** ι equation.
//!
//! The induction itself is [`crate::wtype::w_rect`] at `φ(z) := indom(wrec,z)`;
//! its step is the one-point extension of [`crate::wrec_extend`], which is the
//! long half and lives in its own file.
//!
//! # The typing hypothesis, and why there has to be one
//!
//! An attempt is by definition a subset of `W × T`, so extending one by
//! `⟨⟨a,f⟩, app(e,⟨a,⟨f,r⟩⟩)⟩` needs the step's value to lie in `T`, and `e` is
//! an arbitrary set. Hence
//!
//! ```text
//! step_typed(A,B,u,T,e) := ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a),W) →
//!                            ∀r. (r ∈ fs(B(a),T) → app(e,⟨a,⟨f,r⟩⟩) ∈ T)))
//! ```
//!
//! is carried alongside `closed(A,B,u)` by everything below. It is not a defect
//! of the construction — Lean's recursor is typed the same way, `e` being the
//! packed minor premise and the motive supplying `T` — but it *is* a hypothesis,
//! and a theorem whose antecedent no five sets satisfy would prove nothing. So
//! [`crate::wrec_unit::unit_step_typed`] discharges it, at the instance where ι
//! already fires, and derives `⊢ wrec ∈ fs(W,T)` there with no hypotheses left.
//!
//! # Interface
//!
//! Writing `W` for `W(A,B,u)`, `wrec` for `wrec(A,B,u,T,e)` and `H` for
//! `closed(A,B,u) ∧ step_typed(A,B,u,T,e)`:
//!
//! ```text
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (H → ∀z. (z ∈ W → indom(wrec, z)))              [totality]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (H → wrec ∈ fs(W, T))                      [wrec_funspace]
//! ⊢ ∀A ∀B ∀u ∀T ∀e. (H → ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a),W)) →
//!       app(wrec,⟨a,f⟩) = app(e, ⟨a,⟨f, comp(wrec,f,B(a))⟩⟩)))          [iota]
//! ```
//!
//! [`Recursor`] bundles the whole chain of [`crate::wrec`] and
//! [`crate::wrec_typing`] into one value, so that a caller needs one
//! constructor rather than fourteen.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funspace::is_total;
use crate::sums::Sums;
use crate::wrec;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, exists_mono, gen_all, hyp_and, hyp_mp, iff_mpr, inst_all, syl,
    uncurry,
};

// ─────────────────────────────────────────────────────────────────────────────
// The whole recursor development, in one value.
// ─────────────────────────────────────────────────────────────────────────────

/// Every symbol and theorem [`crate::wrec`] and [`crate::wrec_typing`] produce,
/// assembled once.
///
/// The construction mints new symbols — `comp`, `Att`, `wrec`, and whatever the
/// Replacement and Separation instances beneath them introduce — so it must be
/// built **once** per development and shared; building it twice gives two
/// unrelated recursors whose terms do not compare equal.
pub struct Recursor {
    /// The composite symbol, `comp(g,f,d)`.
    pub comp: FnSym,
    /// `⊢ ∀g ∀f ∀d ∀p. (p ∈ comp(g,f,d) ↔ ∃b. (b ∈ d ∧ p = ⟨b, app(g,app(f,b))⟩))`.
    pub comp_ax: Thm,
    /// `⊢ ∀g ∀h ∀f ∀d. (agree_on(g,h,f,d) → comp(g,f,d) = comp(h,f,d))`.
    pub ext: Thm,
    /// The symbol `Att(A,B,u,T,e)`.
    pub att: FnSym,
    /// `⊢ ∀… ∀g. (g ∈ Att ↔ (g ∈ 𝒫(prod(W,T)) ∧ (sv(g) ∧ rec_cond(B,e,g))))`.
    pub att_ax: Thm,
    /// The symbol `wrec(A,B,u,T,e)`.
    pub rec: FnSym,
    /// `⊢ ∀… ∀p. (p ∈ wrec ↔ ∃g. (g ∈ Att ∧ p ∈ g))`.
    pub members: Thm,
    /// `⊢ ∀…. (closed(A,B,u) → sv(wrec))`.
    pub sv: Thm,
    /// `⊢ ∀… ∀g ∀p. ((g ∈ Att ∧ p ∈ g) → p ∈ wrec)`.
    pub subset: Thm,
    /// `⊢ ∀…. (closed → ∀g. (g ∈ Att → ∀x. (indom(g,x) → app(wrec,x) = app(g,x))))`.
    pub value: Thm,
    /// `⊢ ∀… ∀g. (g ∈ Att → ∀x. (indom(g,x) → indom(wrec,x)))`.
    pub mono: Thm,
    /// `⊢ ∀…. wrec ⊆ prod(W,T)`.
    pub subset_prod: Thm,
    /// `⊢ ∀…. (closed → rec_cond(B,e,wrec))`.
    pub rec_cond: Thm,
    /// `⊢ ∀…. (closed → ∀a ∀f. ((∀b ∈ B(a). indom(wrec,app(f,b)))
    ///        → comp(wrec,f,B(a)) ∈ fs(B(a),T)))`.
    pub comp_typed: Thm,
}

impl Recursor {
    /// Build the whole chain over a caller-supplied [`Wtype`].
    pub fn new(env: &mut Env, wt: &Wtype) -> Option<Recursor> {
        let (comp, comp_ax) = wrec::compose(env, &wt.sums.ap)?;
        let ext = wrec::compose_ext(env, &wt.sums.ap, comp, &comp_ax)?;
        let (att, att_ax) = wrec::attempts(env, wt, comp)?;
        let agree = wrec::agreement(env, wt, &ext, att, &att_ax)?;
        let (rec, rec_def) = wrec::wrec_symbol(env, &wt.sums, att)?;
        let members = wrec::wrec_members(env, &wt.sums, att, rec, &rec_def)?;
        let sv = wrec::wrec_single_valued(env, wt, att, &att_ax, rec, &members, &agree)?;
        let subset = wrec::attempt_subset_wrec(env, att, &members)?;
        let value = wrec::wrec_value(env, wt, att, &att_ax, rec, &subset, &sv)?;
        let mono = wrec::attempt_indom_wrec(env, &wt.sums.ap, att, rec, &subset)?;
        let subset_prod = wrec::wrec_subset_prod(env, wt, att, &att_ax, rec, &members)?;
        let rec_cond = wrec::wrec_rec_cond(
            env, wt, comp, &ext, att, &att_ax, rec, &members, &value, &mono,
        )?;
        let value_typed = crate::wrec_typing::wrec_value_typed(env, wt, rec, &subset_prod, &sv)?;
        let ct = crate::wrec_typing::composite_typed(env, &wt.sums, comp, &comp_ax)?;
        let comp_typed =
            crate::wrec_typing::wrec_composite_typed(env, wt, comp, rec, &value_typed, &ct)?;
        Some(Recursor {
            comp,
            comp_ax,
            ext,
            att,
            att_ax,
            rec,
            members,
            sv,
            subset,
            value,
            mono,
            subset_prod,
            rec_cond,
            comp_typed,
        })
    }

    /// The term `wrec(A,B,u,T,e)`.
    pub fn of(&self, a: &Term, b: &Term, u: &Term, t: &Term, e: &Term) -> Term {
        Term::apply(self.rec, vec![a.clone(), b.clone(), u.clone(), t.clone(), e.clone()])
    }

    /// The term `Att(A,B,u,T,e)`.
    pub fn att_of(&self, a: &Term, b: &Term, u: &Term, t: &Term, e: &Term) -> Term {
        Term::apply(self.att, vec![a.clone(), b.clone(), u.clone(), t.clone(), e.clone()])
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The typing hypothesis on the step.
// ─────────────────────────────────────────────────────────────────────────────

/// ```text
/// step_typed(A,B,u,T,e) := ∀a. (a ∈ A → ∀f. (f ∈ fs(B(a),W(A,B,u)) →
///                            ∀r. (r ∈ fs(B(a),T) → app(e,⟨a,⟨f,r⟩⟩) ∈ T)))
/// ```
///
/// The step lands in the target whenever it is handed a constructor, a family
/// of subterms and a family of recursive values of the right types. Its third
/// premise is discharged at the point of use by
/// [`crate::wrec_typing::wrec_composite_typed`] — that lemma exists for no other
/// reason.
#[allow(clippy::too_many_arguments)]
pub fn step_typed(
    env: &mut Env,
    s: &Sums,
    wt: &Wtype,
    a: &Term,
    b: &Term,
    u: &Term,
    t: &Term,
    e: &Term,
) -> Formula {
    let (pa, pf, pr) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tpa, tpf, tpr) = (Term::var(pa), Term::var(pf), Term::var(pr));
    let w_t = wt.of(a.clone(), b.clone(), u.clone());
    let fibre = s.ap.apply(b.clone(), tpa.clone());
    let val = s.ap.apply(
        e.clone(),
        s.ap.sets.pair(tpa.clone(), s.ap.sets.pair(tpf.clone(), tpr.clone())),
    );
    let inner_r = Formula::forall(
        pr,
        Formula::imp(
            Formula::mem(tpr, s.fs.of(fibre.clone(), t.clone())),
            Formula::mem(val, t.clone()),
        ),
    );
    let inner_f = Formula::forall(
        pf,
        Formula::imp(Formula::mem(tpf, s.fs.of(fibre, w_t)), inner_r),
    );
    Formula::forall(pa, Formula::imp(Formula::mem(tpa, a.clone()), inner_f))
}

/// `closed(A,B,u) ∧ step_typed(A,B,u,T,e)` — the two hypotheses everything
/// below carries, in the order they are carried.
pub fn premise(env: &mut Env, wt: &Wtype, ps: &[Term]) -> Formula {
    let s = &wt.sums;
    Formula::and(
        crate::wtype::closed(env, s, &ps[0], &ps[1], &ps[2]),
        step_typed(env, s, wt, &ps[0], &ps[1], &ps[2], &ps[3], &ps[4]),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 4: totality.
// ─────────────────────────────────────────────────────────────────────────────

/// From `⊢ H → φ` infer `⊢ H → ∀v. φ`, for `v` not free in `H`.
fn gen_under(v: kernel::FreeVar, h: &Formula, thm: &Thm) -> Option<Thm> {
    let (_, body) = thm.concl().as_imp()?;
    Thm::mp(&Thm::ax_dist(v, h.clone(), body)?, &Thm::gen(v, thm))
}

/// From `⊢ H → ∀v₁ … ∀vₙ. φ` infer `⊢ H → φ[t₁ … tₙ]`.
fn hyp_inst(h_all: &Thm, ts: &[Term]) -> Option<Thm> {
    let mut cur = h_all.clone();
    for t in ts {
        let (_, all) = cur.concl().as_imp()?;
        cur = syl(&cur, &Thm::ax_inst(all, t.clone())?)?;
    }
    Some(cur)
}

/// **The recursor is defined everywhere on the W-type.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. ((closed(A,B,u) ∧ step_typed(A,B,u,T,e))
///                        → ∀z. (z ∈ W(A,B,u) → indom(wrec(A,B,u,T,e), z)))
/// ```
///
/// [`crate::wtype::w_rect`] at `φ(z) := indom(wrec, z)`, and nothing else. The
/// minor premise it wants is *exactly*
/// [`crate::wrec_extend::Extension::indom`] with the four conjuncts of the
/// hypothesis bundle peeled off one at a time — which is why
/// [`crate::wrec_extend::hypothesis`] is nested the way it is.
pub fn totality(
    env: &mut Env,
    wt: &Wtype,
    r: &Recursor,
    ext: &crate::wrec_extend::Extension,
) -> Option<Thm> {
    let s = &wt.sums;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let w_t = wt.of(ps[0].clone(), ps[1].clone(), ps[2].clone());
    let rec_t = r.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);

    let zv = env.fresh_var();
    let phi = crate::wrec::indom(env, &s.ap, &rec_t, &Term::var(zv));
    let h = premise(env, wt, &ps);
    let cl = and_left(
        crate::wtype::closed(env, s, &ps[0], &ps[1], &ps[2]),
        step_typed(env, s, wt, &ps[0], &ps[1], &ps[2], &ps[3], &ps[4]),
    );

    // ── The minor premise, from the one-point extension ─────────────────────
    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let mut at = ps.clone();
    at.push(Term::var(pa));
    at.push(Term::var(pf));
    let step = inst_all(&ext.indom, &at)?;
    let s1 = uncurry(&step)?;
    let s2 = uncurry(&s1)?;
    let (h_ma, _) = s2.concl().as_imp()?;
    let inner = gen_under(pf, &h_ma, &s2)?;
    let outer = gen_under(pa, &h, &uncurry(&inner)?)?;
    debug_assert_eq!(
        *outer.concl(),
        Formula::imp(
            h.clone(),
            crate::wtype::ind_step(env, s, &w_t, &ps[0], &ps[1], zv, &phi)
        ),
        "totality: the minor premise has the wrong shape"
    );

    // ── Structural induction ────────────────────────────────────────────────
    let abu = crate::wtype::Params { a: vars[0], b: vars[1], u: vars[2] };
    let rect = crate::wtype::w_rect(env, wt, &vars, abu, zv, &phi)?;
    let out = hyp_mp(&syl(&cl, &rect)?, &outer)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            h,
            Formula::forall(zv, Formula::imp(Formula::mem(Term::var(zv), w_t), phi))
        ),
        "totality: the conclusion has the wrong shape"
    );
    Some(gen_all(&vars, &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 5: the recursor is a function from the W-type to the target.
// ─────────────────────────────────────────────────────────────────────────────

/// **The recursor is a function `W(A,B,u) → T`.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. ((closed(A,B,u) ∧ step_typed(A,B,u,T,e))
///                        → wrec(A,B,u,T,e) ∈ fs(W(A,B,u), T))
/// ```
///
/// The three clauses of [`crate::funspace::is_function`]: inclusion in the
/// product is [`crate::wrec::wrec_subset_prod`] and needs no hypothesis;
/// single-valuedness is [`crate::wrec::wrec_single_valued`]; totality is
/// [`totality`], with the value's membership in `T` read off the inclusion —
/// which is why the existential has to be re-witnessed rather than merely
/// renamed.
pub fn wrec_funspace(env: &mut Env, wt: &Wtype, r: &Recursor, total: &Thm) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let w_t = wt.of(ps[0].clone(), ps[1].clone(), ps[2].clone());
    let tt = ps[3].clone();
    let rec_t = r.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);
    let h = premise(env, wt, &ps);
    let cl = and_left(
        crate::wtype::closed(env, s, &ps[0], &ps[1], &ps[2]),
        step_typed(env, s, wt, &ps[0], &ps[1], &ps[2], &ps[3], &ps[4]),
    );

    // ── Totality, with the value typed ──────────────────────────────────────
    let (zv, yv) = (env.fresh_var(), env.fresh_var());
    let (tz, ty) = (Term::var(zv), Term::var(yv));
    let pzy = ap.sets.pair(tz.clone(), ty.clone());
    let mem_zy = Formula::mem(pzy.clone(), rec_t.clone());

    let sp = inst_all(&r.subset_prod, &ps)?;
    let at_p = Thm::mp(&Thm::ax_inst(sp.concl().clone(), pzy.clone())?, &sp)?;
    let y_in_t = syl(
        &at_p,
        &syl(
            &crate::iff_mp(&inst_all(
                &s.pair_in_prod,
                &[w_t.clone(), tt.clone(), tz.clone(), ty.clone()],
            )?)?,
            &and_right(
                Formula::mem(tz.clone(), w_t.clone()),
                Formula::mem(ty, tt.clone()),
            ),
        )?,
    )?;
    let witnessed = hyp_and(&y_in_t, &crate::imp_refl(mem_zy))?;
    let mono = exists_mono(yv, &Thm::gen(yv, &witnessed))?;
    let at_z = crate::separation::hyp_syl(
        &hyp_inst(&inst_all(total, &ps)?, std::slice::from_ref(&tz))?,
        &a1i(&mono, h.clone()),
    )?;
    let tot = gen_under(zv, &h, &at_z)?;
    debug_assert_eq!(
        *tot.concl(),
        Formula::imp(h.clone(), is_total(env, &ap.sets, &w_t, &tt, &rec_t)),
        "wrec_funspace: totality has the wrong shape"
    );

    // ── The three clauses ───────────────────────────────────────────────────
    let sv = syl(&cl, &inst_all(&r.sv, &ps)?)?;
    let isfun = hyp_and(&a1i(&sp, h.clone()), &hyp_and(&tot, &sv)?)?;
    let out = syl(
        &isfun,
        &iff_mpr(&inst_all(&s.fs.fs_ax, &[w_t.clone(), tt.clone(), rec_t.clone()])?)?,
    )?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(rec_t, s.fs.of(w_t, tt))),
        "wrec_funspace: the conclusion has the wrong shape"
    );
    Some(gen_all(&vars, &out))
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 6: ι, unguarded.
// ─────────────────────────────────────────────────────────────────────────────

/// **The ι rule.**
///
/// ```text
/// ⊢ ∀A ∀B ∀u ∀T ∀e. ((closed(A,B,u) ∧ step_typed(A,B,u,T,e)) →
///       ∀a ∀f. ((a ∈ A ∧ f ∈ fs(B(a), W(A,B,u))) →
///           app(wrec,⟨a,f⟩) = app(e, ⟨a, ⟨f, comp(wrec,f,B(a))⟩⟩)))
/// ```
///
/// [`crate::wrec::iota_on_domain`] with its guard discharged: `⟨a,f⟩ ∈ W` by
/// W1 ([`crate::wtype::sup_mem`]), and then `indom(wrec,⟨a,f⟩)` by
/// [`totality`]. That is the whole content of this function — the equation
/// itself was proved two files ago.
pub fn iota(env: &mut Env, wt: &Wtype, r: &Recursor, total: &Thm) -> Option<Thm> {
    let s = &wt.sums;
    let ap = &s.ap;
    let on_dom = wrec::iota_on_domain(env, s, &r.rec_cond)?;

    let vars: Vec<kernel::FreeVar> = (0..5).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let w_t = wt.of(ps[0].clone(), ps[1].clone(), ps[2].clone());
    let h = premise(env, wt, &ps);
    let cl = and_left(
        crate::wtype::closed(env, s, &ps[0], &ps[1], &ps[2]),
        step_typed(env, s, wt, &ps[0], &ps[1], &ps[2], &ps[3], &ps[4]),
    );

    let (pa, pf) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(pa), Term::var(pf));
    let w0 = ap.sets.pair(ta.clone(), tf.clone());
    let fibre = ap.apply(ps[1].clone(), ta.clone());
    let ma = Formula::mem(ta.clone(), ps[0].clone());
    let mf = Formula::mem(tf.clone(), s.fs.of(fibre, w_t));
    let both = Formula::and(ma.clone(), mf.clone());

    let p = Formula::and(h.clone(), both.clone());
    let p_h = and_left(h.clone(), both.clone());
    let p_both = and_right(h.clone(), both);
    let p_ma = syl(&p_both, &and_left(ma, mf.clone()))?;
    let p_mf = syl(&p_both, &and_right(Formula::mem(ta.clone(), ps[0].clone()), mf))?;
    let p_cl = syl(&p_h, &cl)?;

    let in_w = hyp_mp(
        &hyp_inst(
            &hyp_mp(
                &hyp_inst(
                    &syl(&p_cl, &inst_all(&wt.sup_mem, &ps[0..3])?)?,
                    std::slice::from_ref(&ta),
                )?,
                &p_ma,
            )?,
            std::slice::from_ref(&tf),
        )?,
        &p_mf,
    )?;
    let ind = hyp_mp(
        &hyp_inst(&syl(&p_h, &inst_all(total, &ps)?)?, std::slice::from_ref(&w0))?,
        &in_w,
    )?;
    let eq = hyp_mp(
        &hyp_inst(
            &syl(&p_cl, &inst_all(&on_dom, &ps)?)?,
            &[ta.clone(), tf.clone()],
        )?,
        &ind,
    )?;
    debug_assert_eq!(
        *eq.concl(),
        Formula::imp(
            p,
            Formula::eq(
                ap.apply(r.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]), w0),
                wrec::step_at(
                    ap,
                    r.comp,
                    &ps[4],
                    &r.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]),
                    &ta,
                    &tf,
                    &ap.apply(ps[1].clone(), ta.clone()),
                ),
            )
        ),
        "iota: the equation has the wrong shape"
    );
    let body = uncurry(&eq)?;
    let out = gen_under(pa, &h, &gen_under(pf, &h, &body)?)?;
    Some(gen_all(&vars, &out))
}
