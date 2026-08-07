//! `rec₊` — the case function `case(A,B,T,f,g)`, packaged as [`Cases`].
//!
//! # Interface
//!
//! [`Cases::new`] introduces the symbol and derives everything; the fields are
//! the theorems, and [`Cases::of`] builds the term `case(A,B,T,f,g)`:
//!
//! ```text
//! ⊢ ∀A ∀B ∀T ∀f ∀g ∀a ∀y. (f ∈ fs(A,T) → (⟨inl(a),y⟩ ∈ case ↔ ⟨a,y⟩ ∈ f))   [left_pairs]
//! ⊢ ∀A ∀B ∀T ∀f ∀g ∀b ∀y. (g ∈ fs(B,T) → (⟨inr(b),y⟩ ∈ case ↔ ⟨b,y⟩ ∈ g))   [right_pairs]
//! ⊢ ∀A ∀B ∀T ∀f ∀g. ((f ∈ fs(A,T) ∧ g ∈ fs(B,T)) → case ∈ fs(A+B,T))        [in_funspace]
//! ⊢ ∀A ∀B ∀T ∀f ∀g ∀a. (f ∈ fs(A,T) → (a ∈ A → app(case, inl(a)) = app(f,a)))  [beta_left]
//! ⊢ ∀A ∀B ∀T ∀f ∀g ∀b. (g ∈ fs(B,T) → (b ∈ B → app(case, inr(b)) = app(g,b)))  [beta_right]
//! ```
//!
//! Callers need none of the derivations below. `case` carries `A`, `B` and `T`
//! as parameters because Separation needs a superset and the sum needs its two
//! summands; `case(A,B,T,f,g)` is the `case(f,g)` of the informal statement.
//!
//! # What the symbol is
//!
//! `case(A,B,T,f,g)` is carved out of `(A+B) × T` by Separation at
//!
//! ```text
//! D(z) := ∃u ∃w. ((z = ⟨inl(u),w⟩ ∧ ⟨u,w⟩ ∈ f) ∨ (z = ⟨inr(u),w⟩ ∧ ⟨u,w⟩ ∈ g))
//! ```
//!
//! so it is literally the two graphs, retagged and glued. Separation is
//! unconditional — [`crate::funcs::separation_full`] covers the vacuous case
//! with `∅` — so the symbol is the intended set whether or not there is
//! anything in it, and no default disjunct is needed.
//!
//! # Why this is one file and not three
//!
//! The one lemma that matters is [`case_pairs`]: `⟨inl(a),y⟩ ∈ case ↔ ⟨a,y⟩ ∈ f`.
//! It says the retagging is a bijection on pairs, and **both** other results
//! read straight off it — [`case_in_funspace`] uses it twice per branch and
//! [`case_beta`] is [`crate::funcs::beta_conditional`]'s argument with
//! [`case_pairs`] in place of the pair-injectivity step. Splitting them apart
//! would put an interface between a lemma and its only two consumers, so they
//! stay together.
//!
//! # The antecedents on the computation rules, and which are real
//!
//! [`case_beta`] concludes
//!
//! ```text
//! ⊢ ∀A ∀B ∀T ∀f ∀g ∀a. (f ∈ fs(A,T) → (a ∈ A → app(case(A,B,T,f,g), inl(a)) = app(f,a)))
//! ```
//!
//! * `f ∈ fs(A,T)` **is** consumed, in one place: [`case_pairs`] runs backwards
//!   through `f ⊆ A × T`, which is what supplies `a ∈ A` and `y ∈ T` and hence
//!   puts `⟨inl(a),y⟩` into `(A+B) × T`. Without some such hypothesis the pair
//!   cannot be shown to satisfy the Separation guard. Note the `inl` rule needs
//!   only `f`'s membership, not `g`'s.
//! * `a ∈ A` is **not** consumed. The derivation establishes the equation
//!   outright and the antecedent is added afterwards by weakening, because it is
//!   the shape a caller reducing `rec₊` will have to hand. The stronger
//!   statement is one `Thm::ax_k` step away inside [`case_beta`].

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::{hyp_syl, or_intro_left, or_intro_right, Apply};
use crate::funspace::{self as fsp};
use crate::{
    a1i, and_left, and_right, com12, eq_symm, eq_symm_imp, ex_falso, exists_elim_imp,
    exists_intro_imp, gen_all, hyp_and, hyp_mp, hyp_or_elim, iff_mp, iff_mpr, imp_refl, inst_all,
    mpd_const, syl, uncurry,
};

use super::shared::{carry_elem, carry_eq_rhs, discharge, inl_of, inr_of};
use super::sum::Sums;

/// `D(z)` — the Separation condition that carves `case` out of `(A+B) × T`.
fn case_cond(env: &mut Env, ap: &Apply, f: &Term, g: &Term, z: &Term) -> Formula {
    let (u, w) = (env.fresh_var(), env.fresh_var());
    let (tu, tw) = (Term::var(u), Term::var(w));
    let body = Formula::or(
        Formula::and(
            Formula::eq(z.clone(), ap.sets.pair(inl_of(ap, tu.clone()), tw.clone())),
            Formula::mem(ap.sets.pair(tu.clone(), tw.clone()), f.clone()),
        ),
        Formula::and(
            Formula::eq(z.clone(), ap.sets.pair(inr_of(ap, tu.clone()), tw.clone())),
            Formula::mem(ap.sets.pair(tu, tw), g.clone()),
        ),
    );
    Formula::exists(u, Formula::exists(w, body))
}

/// The three clauses of `f ∈ fs(A,T)`, each in implication form:
/// `⊢ f ∈ fs(A,T) → f ⊆ A × T`, `⊢ … → f is total on A`, `⊢ … → f is
/// single-valued`.
fn fs_clauses(env: &mut Env, s: &Sums, a: &Term, t: &Term, f: &Term) -> Option<(Thm, Thm, Thm)> {
    let l = fsp::is_function(env, &s.ap.sets, &s.prod, a, t, f);
    let sub = kernel::thm::subset(env, f.clone(), s.prod.of(a.clone(), t.clone()));
    let total = fsp::is_total(env, &s.ap.sets, a, t, f);
    let sv = fsp::is_single_valued(env, &s.ap.sets, f);
    let rest = Formula::and(total.clone(), sv.clone());
    debug_assert_eq!(l, Formula::and(sub.clone(), rest.clone()), "fs_clauses: isfun shape drift");

    let at = inst_all(&s.fs.fs_ax, &[a.clone(), t.clone(), f.clone()])?;
    let isfun = iff_mp(&at)?;
    let h_sub = syl(&isfun, &and_left(sub.clone(), rest.clone()))?;
    let h_rest = syl(&isfun, &and_right(sub, rest))?;
    let h_total = syl(&h_rest, &and_left(total.clone(), sv.clone()))?;
    let h_sv = syl(&h_rest, &and_right(total, sv))?;
    Some((h_sub, h_total, h_sv))
}

/// Introduce `case(A,B,T,f,g)`, with
/// `⊢ ∀A ∀B ∀T ∀f ∀g ∀z. (z ∈ case(A,B,T,f,g) ↔ (z ∈ (A+B) × T ∧ D(z)))`.
///
/// Separation is unconditional — [`crate::funcs::separation_full`] covers the
/// vacuous case with `∅` — so the symbol is the intended set whether or not
/// there is anything in it, and no default disjunct is needed.
pub fn case_symbol(env: &mut Env, s: &Sums) -> Option<(FnSym, Thm)> {
    let (a, b, t, f, g) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));
    let z = env.fresh_var();
    let tz = Term::var(z);

    let sup = s.prod.of(Term::apply(s.sum, vec![ta, tb]), tt);
    let d = case_cond(env, &s.ap, &tf, &tg, &tz);
    let sep = crate::funcs::separation_full(env, z, &d, &sup, &s.ap.empty_ax).ok()?;
    let phi = Formula::and(Formula::mem(tz, sup), d);
    crate::define_by_membership(env, &[a, b, t, f, g], &sep, z, &phi)
}

/// `⊢ ∀A ∀B ∀T ∀f ∀g ∀a ∀y. (f ∈ fs(A,T) → (⟨inl(a),y⟩ ∈ case(A,B,T,f,g) ↔ ⟨a,y⟩ ∈ f))`
/// when `left`, and the `inr`/`g` mirror image otherwise.
///
/// **The lemma the rest depends on.** Forward it is disjointness and
/// injectivity of the tags: a pair tagged `inl` can only have come from the
/// `inl` disjunct, and there the tag cancels. Backward it needs the antecedent:
/// to put `⟨inl(a),y⟩` into `case` one must know it lies in `(A+B) × T`, and
/// `a ∈ A`, `y ∈ T` are only available from `f ⊆ A × T`.
pub fn case_pairs(env: &mut Env, s: &Sums, case: FnSym, case_ax: &Thm, left: bool) -> Option<Thm> {
    let (a, b, t, f, g) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));
    let (x, y, u, w) = (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty, tu, tw) = (Term::var(x), Term::var(y), Term::var(u), Term::var(w));

    let sum_t = Term::apply(s.sum, vec![ta.clone(), tb.clone()]);
    let sup = s.prod.of(sum_t.clone(), tt.clone());
    let case_t =
        Term::apply(case, vec![ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone()]);

    let dom = if left { ta.clone() } else { tb.clone() };
    let fn_t = if left { tf.clone() } else { tg.clone() };
    let inj = |z: Term| if left { inl_of(&s.ap, z) } else { inr_of(&s.ap, z) };
    let other = |z: Term| if left { inr_of(&s.ap, z) } else { inl_of(&s.ap, z) };
    let other_fn = if left { tg.clone() } else { tf.clone() };

    let pair_xy = s.ap.sets.pair(tx.clone(), ty.clone());
    let pair_uw = s.ap.sets.pair(tu.clone(), tw.clone());
    let elem = s.ap.sets.pair(inj(tx.clone()), ty.clone());
    let target = Formula::mem(pair_xy.clone(), fn_t.clone());
    let h = Formula::mem(fn_t.clone(), s.fs.of(dom.clone(), tt.clone()));

    // The Separation condition, rebuilt with our own witness variables.
    let l_disj = Formula::and(
        Formula::eq(elem.clone(), s.ap.sets.pair(inl_of(&s.ap, tu.clone()), tw.clone())),
        Formula::mem(pair_uw.clone(), tf.clone()),
    );
    let r_disj = Formula::and(
        Formula::eq(elem.clone(), s.ap.sets.pair(inr_of(&s.ap, tu.clone()), tw.clone())),
        Formula::mem(pair_uw.clone(), tg.clone()),
    );
    let body = Formula::or(l_disj.clone(), r_disj.clone());
    let d = Formula::exists(u, Formula::exists(w, body.clone()));

    let case_at = inst_all(
        case_ax,
        &[ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone(), elem.clone()],
    )?;
    debug_assert_eq!(
        *case_at.concl(),
        Formula::iff(
            Formula::mem(elem.clone(), case_t.clone()),
            Formula::and(Formula::mem(elem.clone(), sup.clone()), d.clone())
        ),
        "case_pairs: the defining condition has an unexpected shape"
    );

    // ── forward: the matching disjunct ───────────────────────────────────────
    let m_eqf = Formula::eq(elem.clone(), s.ap.sets.pair(inj(tu.clone()), tw.clone()));
    let m_memf = Formula::mem(pair_uw.clone(), fn_t.clone());
    let match_disj = Formula::and(m_eqf.clone(), m_memf.clone());
    debug_assert_eq!(match_disj, if left { l_disj.clone() } else { r_disj.clone() });

    let m_eq = and_left(m_eqf.clone(), m_memf.clone());
    let m_mem = and_right(m_eqf, m_memf);
    let inj_pair =
        inst_all(&s.ap.pair_inj, &[inj(tx.clone()), ty.clone(), inj(tu.clone()), tw.clone()])?;
    let m_conj = syl(&m_eq, &inj_pair)?;
    let e_tag = Formula::eq(inj(tx.clone()), inj(tu.clone()));
    let e_val = Formula::eq(ty.clone(), tw.clone());
    let m_tag = syl(&m_conj, &and_left(e_tag.clone(), e_val.clone()))?;
    let m_yw = syl(&m_conj, &and_right(e_tag, e_val))?;

    let injective = if left { &s.inl_inj } else { &s.inr_inj };
    let m_xu = syl(&m_tag, &inst_all(injective, &[tx.clone(), tu.clone()])?)?;
    let m_ux = syl(&m_xu, &eq_symm_imp(env, tx.clone(), tu.clone()))?;
    let m_wy = syl(&m_yw, &eq_symm_imp(env, ty.clone(), tw.clone()))?;

    // `u = x` and `w = y` rewrite `⟨u,w⟩` into `⟨x,y⟩`, one component at a time.
    let pair_xw = s.ap.sets.pair(tx.clone(), tw.clone());
    let h1 = env.fresh_var();
    let congr_l = mpd_const(
        &Thm::eq_leibniz(
            tu.clone(),
            tx.clone(),
            h1,
            Formula::eq(pair_uw.clone(), s.ap.sets.pair(Term::var(h1), tw.clone())),
        ),
        &Thm::eq_refl(pair_uw.clone()),
    )?;
    let h2 = env.fresh_var();
    let congr_r = mpd_const(
        &Thm::eq_leibniz(
            tw.clone(),
            ty.clone(),
            h2,
            Formula::eq(pair_xw.clone(), s.ap.sets.pair(tx.clone(), Term::var(h2))),
        ),
        &Thm::eq_refl(pair_xw.clone()),
    )?;
    let m_p1 = syl(&m_ux, &congr_l)?;
    let m_p2 = syl(&m_wy, &congr_r)?;
    let bridge = carry_eq_rhs(env, pair_uw.clone(), pair_xw, pair_xy.clone());
    let m_pair_eq = hyp_mp(&hyp_mp(&a1i(&bridge, match_disj.clone()), &m_p2)?, &m_p1)?;
    let carry_f = carry_elem(env, pair_uw.clone(), pair_xy.clone(), fn_t.clone());
    let m_target = hyp_mp(&hyp_mp(&a1i(&carry_f, match_disj.clone()), &m_pair_eq)?, &m_mem)?;

    // ── forward: the other disjunct is refuted by disjointness ───────────────
    let o_eqf = Formula::eq(elem.clone(), s.ap.sets.pair(other(tu.clone()), tw.clone()));
    let o_memf = Formula::mem(pair_uw.clone(), other_fn);
    let other_disj = Formula::and(o_eqf.clone(), o_memf.clone());
    debug_assert_eq!(other_disj, if left { r_disj.clone() } else { l_disj.clone() });

    let o_eq = and_left(o_eqf, o_memf);
    let inj_pair2 =
        inst_all(&s.ap.pair_inj, &[inj(tx.clone()), ty.clone(), other(tu.clone()), tw.clone()])?;
    let o_conj = syl(&o_eq, &inj_pair2)?;
    let f_tag = Formula::eq(inj(tx.clone()), other(tu.clone()));
    let f_val = Formula::eq(ty.clone(), tw.clone());
    let o_tag = syl(&o_conj, &and_left(f_tag, f_val))?;
    let refute = if left {
        inst_all(&s.disjoint, &[tx.clone(), tu.clone()])?
    } else {
        syl(
            &eq_symm_imp(env, inr_of(&s.ap, tx.clone()), inl_of(&s.ap, tu.clone())),
            &inst_all(&s.disjoint, &[tu.clone(), tx.clone()])?,
        )?
    };
    let o_target = syl(&syl(&o_tag, &refute)?, &ex_falso(target.clone()))?;

    let (case_l, case_r) = if left { (&m_target, &o_target) } else { (&o_target, &m_target) };
    let body_goal = hyp_or_elim(
        &imp_refl(body.clone()),
        &a1i(case_l, body.clone()),
        &a1i(case_r, body.clone()),
    )?;
    let ex_w = exists_elim_imp(w, &Thm::gen(w, &body_goal), &target)?;
    let ex_u = exists_elim_imp(u, &Thm::gen(u, &ex_w), &target)?;
    let fwd = syl(
        &syl(
            &iff_mp(&case_at)?,
            &and_right(Formula::mem(elem.clone(), sup.clone()), d.clone()),
        )?,
        &ex_u,
    )?;

    // ── backward: needs `f ∈ fs(A,T)`, for the components ────────────────────
    let k = Formula::and(h.clone(), target.clone());
    let k_h = and_left(h.clone(), target.clone());
    let k_t = and_right(h.clone(), target.clone());

    let (h_sub, _, _) = fs_clauses(env, s, &dom, &tt, &fn_t)?;
    let sub_f = kernel::thm::subset(env, fn_t.clone(), s.prod.of(dom.clone(), tt.clone()));
    let k_sub_at = syl(&syl(&k_h, &h_sub)?, &Thm::ax_inst(sub_f, pair_xy.clone())?)?;
    let k_in_prod = hyp_mp(&k_sub_at, &k_t)?;

    let pip = inst_all(&s.pair_in_prod, &[dom.clone(), tt.clone(), tx.clone(), ty.clone()])?;
    let k_comp = syl(&k_in_prod, &iff_mp(&pip)?)?;
    let mem_xd = Formula::mem(tx.clone(), dom.clone());
    let mem_yt = Formula::mem(ty.clone(), tt.clone());
    let k_xd = syl(&k_comp, &and_left(mem_xd.clone(), mem_yt.clone()))?;
    let k_yt = syl(&k_comp, &and_right(mem_xd, mem_yt))?;

    let inj_mem = if left { &s.inl_mem } else { &s.inr_mem };
    let k_inj_sum = syl(&k_xd, &inst_all(inj_mem, &[ta.clone(), tb.clone(), tx.clone()])?)?;
    let pip2 = inst_all(&s.pair_in_prod, &[sum_t, tt.clone(), inj(tx.clone()), ty.clone()])?;
    let k_in_sup = syl(&hyp_and(&k_inj_sum, &k_yt)?, &iff_mpr(&pip2)?)?;

    // `D(elem)` at the witnesses `u := x`, `w := y`, where the equation is
    // reflexivity and the membership is the hypothesis itself.
    let l_at = l_disj.subst(u, &tx).subst(w, &ty);
    let r_at = r_disj.subst(u, &tx).subst(w, &ty);
    let match_at = Formula::and(Formula::eq(elem.clone(), elem.clone()), target.clone());
    debug_assert_eq!(
        if left { l_at.clone() } else { r_at.clone() },
        match_at,
        "case_pairs: the witness instance has an unexpected shape"
    );
    let k_match = hyp_and(&a1i(&Thm::eq_refl(elem.clone()), k.clone()), &k_t)?;
    let k_body = if left {
        syl(&k_match, &or_intro_left(l_at, r_at))?
    } else {
        syl(&k_match, &or_intro_right(l_at, r_at))?
    };
    let k_ex_w = syl(&k_body, &exists_intro_imp(w, body.subst(u, &tx), ty.clone())?)?;
    let k_d = syl(&k_ex_w, &exists_intro_imp(u, Formula::exists(w, body), tx.clone())?)?;
    let k_case = syl(&hyp_and(&k_in_sup, &k_d)?, &iff_mpr(&case_at)?)?;
    let bwd = uncurry(&k_case)?;

    let out = hyp_and(&a1i(&fwd, h.clone()), &bwd)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::iff(Formula::mem(elem, case_t), target)),
        "case_pairs: unexpected shape"
    );
    Some(gen_all(&[a, b, t, f, g, x, y], &out))
}

/// From `⊢ (K ∧ E) → φ` infer `⊢ K → ((∃v. E) → φ)` — a case of an `∃`-shaped
/// disjunct, in the form [`crate::hyp_or_elim`] consumes.
fn or_branch(v: FreeVar, ke_goal: &Thm) -> Option<Thm> {
    let ekg = com12(&uncurry(ke_goal)?)?; // ⊢ E → (K → φ)
    let (_, kg) = ekg.concl().as_imp()?;
    com12(&exists_elim_imp(v, &Thm::gen(v, &ekg), &kg)?)
}

/// `⊢ ∀A ∀B ∀T ∀f ∀g ∀a. (f ∈ fs(A,T) → (a ∈ A → app(case(A,B,T,f,g), inl(a)) = app(f,a)))`
/// when `left`, and the `inr`/`g` mirror image otherwise — **the computation
/// rules**.
///
/// Two antecedents, and only one of them is load-bearing. `f ∈ fs(A,T)` is
/// needed because [`case_pairs`] needs it; `a ∈ A` is *not* — the derivation
/// establishes the equation without it — but it is carried anyway, because it
/// is the shape a caller reducing `rec₊` will have to hand and the stronger
/// statement is available as an intermediate.
///
/// The argument is [`crate::funcs::beta_conditional`]'s, with [`case_pairs`] in
/// place of the pair-injectivity step: `coll(case, inl(a))` and `coll(f,a)` have
/// the same members, so they are equal, so their unions are — and `app` is that
/// union.
pub fn case_beta(
    env: &mut Env,
    s: &Sums,
    case: FnSym,
    case_pairs_thm: &Thm,
    left: bool,
) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (a, b, t, f, g) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));

    let case_t =
        Term::apply(case, vec![ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone()]);
    let dom = if left { ta.clone() } else { tb.clone() };
    let fn_t = if left { tf.clone() } else { tg.clone() };
    let inj_x = if left { inl_of(&s.ap, tx.clone()) } else { inr_of(&s.ap, tx.clone()) };
    let h = Formula::mem(fn_t.clone(), s.fs.of(dom.clone(), tt.clone()));

    let coll_case = s.ap.coll_of(case_t.clone(), inj_x.clone());
    let coll_f = s.ap.coll_of(fn_t.clone(), tx.clone());
    let app_case = s.ap.apply(case_t.clone(), inj_x.clone());
    let app_f = s.ap.apply(fn_t.clone(), tx.clone());

    // ── the two collections have the same members ────────────────────────────
    let c_case = inst_all(&s.ap.coll_members, &[case_t.clone(), inj_x.clone(), ty.clone()])?;
    let c_f = inst_all(&s.ap.coll_members, &[fn_t.clone(), tx.clone(), ty.clone()])?;
    let cp = inst_all(
        case_pairs_thm,
        &[ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone(), tx.clone(), ty.clone()],
    )?;

    let h_case = a1i(&c_case, h.clone());
    let h_f = a1i(&c_f, h.clone());
    let fwd = hyp_syl(
        &hyp_syl(&crate::hyp_iff_mp(&h_case)?, &crate::hyp_iff_mp(&cp)?)?,
        &crate::hyp_iff_mpr(&h_f)?,
    )?;
    let bwd = hyp_syl(
        &hyp_syl(&crate::hyp_iff_mp(&h_f)?, &crate::hyp_iff_mpr(&cp)?)?,
        &crate::hyp_iff_mpr(&h_case)?,
    )?;
    let mem_case = Formula::mem(ty.clone(), coll_case.clone());
    let mem_f = Formula::mem(ty.clone(), coll_f.clone());
    let h_all = Thm::mp(
        &Thm::ax_dist(y, h.clone(), Formula::iff(mem_case, mem_f))?,
        &Thm::gen(y, &hyp_and(&fwd, &bwd)?),
    )?;
    let h_coll_eq = syl(&h_all, &inst_all(&ext, &[coll_case.clone(), coll_f.clone()])?)?;

    // ── … so their unions are equal, and `app` is that union ─────────────────
    let ucase = s.ap.sets.union_of(coll_case.clone());
    let uf = s.ap.sets.union_of(coll_f.clone());
    let hv = env.fresh_var();
    let congr_u = mpd_const(
        &Thm::eq_leibniz(
            coll_case,
            coll_f,
            hv,
            Formula::eq(ucase.clone(), s.ap.sets.union_of(Term::var(hv))),
        ),
        &Thm::eq_refl(ucase.clone()),
    )?;
    let h_u_eq = syl(&h_coll_eq, &congr_u)?;

    let def_case = inst_all(&s.ap.app_ax, &[case_t.clone(), inj_x.clone()])?;
    let def_f = inst_all(&s.ap.app_ax, &[fn_t.clone(), tx.clone()])?;
    debug_assert_eq!(*def_case.concl(), Formula::eq(app_case.clone(), ucase.clone()));
    debug_assert_eq!(*def_f.concl(), Formula::eq(app_f.clone(), uf.clone()));

    let bridge = carry_eq_rhs(env, app_case.clone(), ucase, uf.clone());
    let h_app_uf = hyp_mp(&hyp_mp(&a1i(&bridge, h.clone()), &h_u_eq)?, &a1i(&def_case, h.clone()))?;
    let close = Thm::mp(
        &carry_eq_rhs(env, app_case.clone(), uf, app_f.clone()),
        &eq_symm(env, &def_f)?,
    )?;
    let eq_goal = Formula::eq(app_case.clone(), app_f.clone());
    let h_eq = hyp_mp(&a1i(&close, h.clone()), &h_app_uf)?;

    // The membership antecedent, which the derivation did not need.
    let out = syl(&h_eq, &Thm::ax_k(eq_goal.clone(), Formula::mem(tx.clone(), dom.clone())))?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::imp(Formula::mem(tx, dom), eq_goal)),
        "case_beta: unexpected shape"
    );
    Some(gen_all(&[a, b, t, f, g, x], &out))
}

/// `⊢ ∀A ∀B ∀T ∀f ∀g. ((f ∈ fs(A,T) ∧ g ∈ fs(B,T)) → case(A,B,T,f,g) ∈ fs(A+B,T))`.
///
/// All three clauses of `isfun`:
///
/// * **a set of pairs**: immediate, since Separation carved `case` out of
///   `(A+B) × T` in the first place;
/// * **total**: a member of `A + B` is `inl(a)` or `inr(b)` ([`Sums::sum_cases`]),
///   `f` (resp. `g`) supplies a value there, and [`case_pairs`] puts the
///   retagged pair into `case`;
/// * **single-valued**: the first component of a member of `case` lies in
///   `A + B`, so it is `inl(u)` or `inr(u)`; [`case_pairs`] moves both pairs
///   back into `f` (resp. `g`), which is single-valued. Only *one* case split is
///   needed, not the four a naive argument would take, because the second pair
///   is transported along the same equation as the first.
pub fn case_in_funspace(
    env: &mut Env,
    s: &Sums,
    case: FnSym,
    case_ax: &Thm,
    cp_l: &Thm,
    cp_r: &Thm,
) -> Option<Thm> {
    let (a, b, t, f, g) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tb, tt, tf, tg) =
        (Term::var(a), Term::var(b), Term::var(t), Term::var(f), Term::var(g));

    let sum_t = Term::apply(s.sum, vec![ta.clone(), tb.clone()]);
    let sup = s.prod.of(sum_t.clone(), tt.clone());
    let case_t =
        Term::apply(case, vec![ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone()]);

    let hf = Formula::mem(tf.clone(), s.fs.of(ta.clone(), tt.clone()));
    let hg = Formula::mem(tg.clone(), s.fs.of(tb.clone(), tt.clone()));
    let h = Formula::and(hf.clone(), hg.clone());
    let h_to_f = and_left(hf.clone(), hg.clone());
    let h_to_g = and_right(hf, hg);

    // ── (1) case ⊆ (A+B) × T ─────────────────────────────────────────────────
    let v = env.fresh_var();
    let tv = Term::var(v);
    let at_v = inst_all(case_ax, &[ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone(), tv.clone()])?;
    let (c_mem, c_d) = crate::empty::split_and(&iff_mp(&at_v)?.concl().as_imp()?.1)?;
    debug_assert_eq!(c_mem, Formula::mem(tv.clone(), sup.clone()), "case_in_funspace: superset drift");
    let sub_thm = Thm::gen(v, &syl(&iff_mp(&at_v)?, &and_left(c_mem, c_d))?);
    debug_assert_eq!(
        *sub_thm.concl(),
        kernel::thm::subset(env, case_t.clone(), sup.clone()),
        "case_in_funspace: the subset clause has an unexpected shape"
    );
    let h_sub = a1i(&sub_thm, h.clone());

    // ── (2) total on A + B ───────────────────────────────────────────────────
    let (p, y) = (env.fresh_var(), env.fresh_var());
    let (tp, ty) = (Term::var(p), Term::var(y));
    let p_in_sum = Formula::mem(tp.clone(), sum_t.clone());
    let goal_body = Formula::and(
        Formula::mem(ty.clone(), tt.clone()),
        Formula::mem(s.ap.sets.pair(tp.clone(), ty.clone()), case_t.clone()),
    );
    let goal = Formula::exists(y, goal_body.clone());

    let k = Formula::and(h.clone(), p_in_sum.clone());
    let k_h = and_left(h.clone(), p_in_sum.clone());
    let k_p = and_right(h.clone(), p_in_sum.clone());
    let k_disj = syl(&k_p, &inst_all(&s.sum_cases, &[ta.clone(), tb.clone(), tp.clone()])?)?;

    let mut branches = Vec::new();
    for left in [true, false] {
        let dom = if left { ta.clone() } else { tb.clone() };
        let fn_t = if left { tf.clone() } else { tg.clone() };
        let h_proj = if left { &h_to_f } else { &h_to_g };
        let cp = if left { cp_l } else { cp_r };
        let x = env.fresh_var();
        let tx = Term::var(x);
        let inj_x = if left { inl_of(&s.ap, tx.clone()) } else { inr_of(&s.ap, tx.clone()) };

        // `E := x ∈ dom ∧ p = inj(x)`, the disjunct `sum_cases` supplies.
        let mem_xd = Formula::mem(tx.clone(), dom.clone());
        let eq_p = Formula::eq(tp.clone(), inj_x.clone());
        let e = Formula::and(mem_xd.clone(), eq_p.clone());
        let ke = Formula::and(k.clone(), e.clone());
        let ke_k = and_left(k.clone(), e.clone());
        let ke_e = and_right(k.clone(), e.clone());
        let ke_hf = syl(&syl(&ke_k, &k_h)?, h_proj)?;
        let ke_xd = syl(&ke_e, &and_left(mem_xd, eq_p.clone()))?;

        // `f` is total on `dom`, so it has a value at `x`.
        let (_, h_total, _) = fs_clauses(env, s, &dom, &tt, &fn_t)?;
        let total_f = fsp::is_total(env, &s.ap.sets, &dom, &tt, &fn_t);
        let total_at = Thm::ax_inst(total_f, tx.clone())?;
        let ke_ex = hyp_mp(&syl(&ke_hf, &syl(&h_total, &total_at)?)?, &ke_xd)?;

        // `M := KE ∧ (y ∈ T ∧ ⟨x,y⟩ ∈ f)`.
        let pair_xy = s.ap.sets.pair(tx.clone(), ty.clone());
        let inner = Formula::and(Formula::mem(ty.clone(), tt.clone()), Formula::mem(pair_xy.clone(), fn_t.clone()));
        debug_assert_eq!(
            ke_ex.concl().as_imp()?.1,
            Formula::exists(y, inner.clone()),
            "case_in_funspace: the totality witness has an unexpected shape"
        );
        let m = Formula::and(ke.clone(), inner.clone());
        let m_ke = and_left(ke.clone(), inner.clone());
        let m_inner = and_right(ke.clone(), inner.clone());
        let m_yt = syl(&m_inner, &and_left(Formula::mem(ty.clone(), tt.clone()), Formula::mem(pair_xy.clone(), fn_t.clone())))?;
        let m_mem = syl(&m_inner, &and_right(Formula::mem(ty.clone(), tt.clone()), Formula::mem(pair_xy, fn_t)))?;

        let cp_at = inst_all(cp, &[ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone(), tx.clone(), ty.clone()])?;
        let m_hf = syl(&m_ke, &ke_hf)?;
        let m_case = hyp_mp(&crate::hyp_iff_mpr(&syl(&m_hf, &cp_at)?)?, &m_mem)?;

        // Transport `⟨inj(x),y⟩ ∈ case` along `p = inj(x)`.
        let pair_ij = s.ap.sets.pair(inj_x.clone(), ty.clone());
        let pair_py = s.ap.sets.pair(tp.clone(), ty.clone());
        let m_eq = syl(&syl(&m_ke, &ke_e)?, &and_right(Formula::mem(tx.clone(), dom.clone()), eq_p))?;
        let m_eq_symm = syl(&m_eq, &eq_symm_imp(env, tp.clone(), inj_x.clone()))?;
        let hv = env.fresh_var();
        let congr = mpd_const(
            &Thm::eq_leibniz(
                inj_x.clone(),
                tp.clone(),
                hv,
                Formula::eq(pair_ij.clone(), s.ap.sets.pair(Term::var(hv), ty.clone())),
            ),
            &Thm::eq_refl(pair_ij.clone()),
        )?;
        let m_pair_eq = hyp_mp(&a1i(&congr, m.clone()), &m_eq_symm)?;
        let carry = carry_elem(env, pair_ij, pair_py, case_t.clone());
        let m_p_case = hyp_mp(&hyp_mp(&a1i(&carry, m.clone()), &m_pair_eq)?, &m_case)?;

        let m_goal = syl(&hyp_and(&m_yt, &m_p_case)?, &exists_intro_imp(y, goal_body.clone(), ty.clone())?)?;
        let ke_goal = discharge(y, &ke_ex, &m_goal)?;
        branches.push(or_branch(x, &ke_goal)?);
    }
    let k_goal = hyp_or_elim(&k_disj, &branches[0], &branches[1])?;
    let h_total_case = Thm::mp(
        &Thm::ax_dist(p, h.clone(), Formula::imp(p_in_sum, goal))?,
        &Thm::gen(p, &uncurry(&k_goal)?),
    )?;
    debug_assert_eq!(
        h_total_case.concl().as_imp()?.1,
        fsp::is_total(env, &s.ap.sets, &sum_t, &tt, &case_t),
        "case_in_funspace: the totality clause has an unexpected shape"
    );

    // ── (3) single-valued ────────────────────────────────────────────────────
    let (xv, y1, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (txv, ty1, ty2) = (Term::var(xv), Term::var(y1), Term::var(y2));
    let m1 = Formula::mem(s.ap.sets.pair(txv.clone(), ty1.clone()), case_t.clone());
    let m2 = Formula::mem(s.ap.sets.pair(txv.clone(), ty2.clone()), case_t.clone());
    let both = Formula::and(m1.clone(), m2.clone());
    let n = Formula::and(h.clone(), both.clone());
    let n_h = and_left(h.clone(), both.clone());
    let n_both = and_right(h.clone(), both.clone());
    let n_m1 = syl(&n_both, &and_left(m1.clone(), m2.clone()))?;
    let n_m2 = syl(&n_both, &and_right(m1, m2))?;

    // The first component lies in `A + B`, so `sum_cases` applies to it.
    let pair_x1 = s.ap.sets.pair(txv.clone(), ty1.clone());
    let at_p1 = inst_all(case_ax, &[ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone(), pair_x1.clone()])?;
    let (d_mem, d_rest) = crate::empty::split_and(&iff_mp(&at_p1)?.concl().as_imp()?.1)?;
    let n_in_sup = syl(&n_m1, &syl(&iff_mp(&at_p1)?, &and_left(d_mem, d_rest))?)?;
    let pip = inst_all(&s.pair_in_prod, &[sum_t.clone(), tt.clone(), txv.clone(), ty1.clone()])?;
    let n_x_sum = syl(
        &syl(&n_in_sup, &iff_mp(&pip)?)?,
        &and_left(Formula::mem(txv.clone(), sum_t.clone()), Formula::mem(ty1.clone(), tt.clone())),
    )?;
    let n_disj = syl(&n_x_sum, &inst_all(&s.sum_cases, &[ta.clone(), tb.clone(), txv.clone()])?)?;

    let mut sv_branches = Vec::new();
    for left in [true, false] {
        let dom = if left { ta.clone() } else { tb.clone() };
        let fn_t = if left { tf.clone() } else { tg.clone() };
        let h_proj = if left { &h_to_f } else { &h_to_g };
        let cp = if left { cp_l } else { cp_r };
        let u = env.fresh_var();
        let tu = Term::var(u);
        let inj_u = if left { inl_of(&s.ap, tu.clone()) } else { inr_of(&s.ap, tu.clone()) };

        let mem_ud = Formula::mem(tu.clone(), dom.clone());
        let eq_x = Formula::eq(txv.clone(), inj_u.clone());
        let e = Formula::and(mem_ud.clone(), eq_x.clone());
        let ne = Formula::and(n.clone(), e.clone());
        let ne_n = and_left(n.clone(), e.clone());
        let ne_eq = syl(&and_right(n.clone(), e.clone()), &and_right(mem_ud, eq_x))?;
        let ne_hf = syl(&syl(&ne_n, &n_h)?, h_proj)?;

        // `x = inj(u)` moves both pairs onto the tagged form.
        let mut tagged = Vec::new();
        for (tyv, n_mi) in [(ty1.clone(), &n_m1), (ty2.clone(), &n_m2)] {
            let pair_x = s.ap.sets.pair(txv.clone(), tyv.clone());
            let pair_u = s.ap.sets.pair(inj_u.clone(), tyv.clone());
            let hv = env.fresh_var();
            let congr = mpd_const(
                &Thm::eq_leibniz(
                    txv.clone(),
                    inj_u.clone(),
                    hv,
                    Formula::eq(pair_x.clone(), s.ap.sets.pair(Term::var(hv), tyv.clone())),
                ),
                &Thm::eq_refl(pair_x.clone()),
            )?;
            let ne_pair_eq = hyp_mp(&a1i(&congr, ne.clone()), &ne_eq)?;
            let carry = carry_elem(env, pair_x, pair_u, case_t.clone());
            let ne_case = hyp_mp(&hyp_mp(&a1i(&carry, ne.clone()), &ne_pair_eq)?, &syl(&ne_n, n_mi)?)?;
            let cp_at = inst_all(cp, &[ta.clone(), tb.clone(), tt.clone(), tf.clone(), tg.clone(), tu.clone(), tyv])?;
            tagged.push(hyp_mp(&crate::hyp_iff_mp(&syl(&ne_hf, &cp_at)?)?, &ne_case)?);
        }

        // `f` is single-valued, so the two values coincide.
        let (_, _, h_sv) = fs_clauses(env, s, &dom, &tt, &fn_t)?;
        let sv_f = fsp::is_single_valued(env, &s.ap.sets, &fn_t);
        let i1 = Thm::ax_inst(sv_f, tu.clone())?;
        let i2 = Thm::ax_inst(i1.concl().as_imp()?.1, ty1.clone())?;
        let i3 = Thm::ax_inst(i2.concl().as_imp()?.1, ty2.clone())?;
        let sv_at = syl(&syl(&i1, &i2)?, &i3)?;
        let ne_goal = hyp_mp(
            &syl(&ne_hf, &syl(&h_sv, &sv_at)?)?,
            &hyp_and(&tagged[0], &tagged[1])?,
        )?;
        sv_branches.push(or_branch(u, &ne_goal)?);
    }
    let n_goal = hyp_or_elim(&n_disj, &sv_branches[0], &sv_branches[1])?;
    let inner_sv = Formula::imp(both, Formula::eq(ty1.clone(), ty2.clone()));
    let s1 = Thm::mp(&Thm::ax_dist(y2, h.clone(), inner_sv.clone())?, &Thm::gen(y2, &uncurry(&n_goal)?))?;
    let f1 = Formula::forall(y2, inner_sv);
    let s2 = Thm::mp(&Thm::ax_dist(y1, h.clone(), f1.clone())?, &Thm::gen(y1, &s1))?;
    let f2 = Formula::forall(y1, f1);
    let h_sv_case = Thm::mp(&Thm::ax_dist(xv, h.clone(), f2)?, &Thm::gen(xv, &s2))?;
    debug_assert_eq!(
        h_sv_case.concl().as_imp()?.1,
        fsp::is_single_valued(env, &s.ap.sets, &case_t),
        "case_in_funspace: the single-valuedness clause has an unexpected shape"
    );

    // ── assemble ─────────────────────────────────────────────────────────────
    let isfun = hyp_and(&h_sub, &hyp_and(&h_total_case, &h_sv_case)?)?;
    debug_assert_eq!(
        isfun.concl().as_imp()?.1,
        fsp::is_function(env, &s.ap.sets, &s.prod, &sum_t, &tt, &case_t),
        "case_in_funspace: isfun was not assembled in the expected shape"
    );
    let fs_at = inst_all(&s.fs.fs_ax, &[sum_t.clone(), tt.clone(), case_t.clone()])?;
    let out = syl(&isfun, &iff_mpr(&fs_at)?)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(h, Formula::mem(case_t, s.fs.of(sum_t, tt))),
        "case_in_funspace: unexpected shape"
    );
    Some(gen_all(&[a, b, t, f, g], &out))
}

/// `rec₊` — the case function `case(A,B,T,f,g)`, with everything proved about
/// it.
///
/// Built separately from [`Sums`] because it consumes the whole of it: the sum
/// symbol, both injections' theorems, the function space and `app`.
pub struct Cases {
    /// The symbol itself.
    pub case: FnSym,
    /// `⊢ ∀A ∀B ∀T ∀f ∀g ∀z. (z ∈ case(A,B,T,f,g) ↔ (z ∈ (A+B) × T ∧ D(z)))` —
    /// the defining axiom.
    pub case_ax: Thm,
    /// `⊢ ∀A ∀B ∀T ∀f ∀g ∀a ∀y. (f ∈ fs(A,T) → (⟨inl(a),y⟩ ∈ case ↔ ⟨a,y⟩ ∈ f))`.
    pub left_pairs: Thm,
    /// `⊢ ∀A ∀B ∀T ∀f ∀g ∀b ∀y. (g ∈ fs(B,T) → (⟨inr(b),y⟩ ∈ case ↔ ⟨b,y⟩ ∈ g))`.
    pub right_pairs: Thm,
    /// `⊢ ∀A ∀B ∀T ∀f ∀g. ((f ∈ fs(A,T) ∧ g ∈ fs(B,T)) → case ∈ fs(A+B,T))`.
    pub in_funspace: Thm,
    /// `⊢ ∀A ∀B ∀T ∀f ∀g ∀a. (f ∈ fs(A,T) → (a ∈ A → app(case, inl(a)) = app(f,a)))`.
    pub beta_left: Thm,
    /// `⊢ ∀A ∀B ∀T ∀f ∀g ∀b. (g ∈ fs(B,T) → (b ∈ B → app(case, inr(b)) = app(g,b)))`.
    pub beta_right: Thm,
}

impl Cases {
    /// Introduce the symbol and derive every theorem.
    pub fn new(env: &mut Env, s: &Sums) -> Option<Cases> {
        let (case, case_ax) = case_symbol(env, s)?;
        let left_pairs = case_pairs(env, s, case, &case_ax, true)?;
        let right_pairs = case_pairs(env, s, case, &case_ax, false)?;
        let in_funspace = case_in_funspace(env, s, case, &case_ax, &left_pairs, &right_pairs)?;
        let beta_left = case_beta(env, s, case, &left_pairs, true)?;
        let beta_right = case_beta(env, s, case, &right_pairs, false)?;
        Some(Cases { case, case_ax, left_pairs, right_pairs, in_funspace, beta_left, beta_right })
    }

    /// The term `case(A,B,T,f,g)`.
    pub fn of(&self, a: Term, b: Term, t: Term, f: Term, g: Term) -> Term {
        Term::apply(self.case, vec![a, b, t, f, g])
    }
}
