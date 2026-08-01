//! The recursion's graph, as a set, by Replacement over `ω`.
//!
//! # Interface
//!
//! [`family`] builds, for a base `c` and a unary step symbol `G`, the relation
//!
//! ```text
//! φ(x,y)  :=  ∃h. (Approx(succ x, h) ∧ y = ⟨x, app(h,x)⟩)
//! ```
//!
//! together with
//!
//! ```text
//! ⊢ ∀x. (x ∈ ω → ∃!y. φ(x,y))                              [Family::functional]
//! ⊢ ∀y. (y ∈ Γ ↔ ∃x. (x ∈ ω ∧ φ(x,y)))                     [Family::members]
//! ```
//!
//! where `Γ` is a fresh nullary symbol. Callers need none of the derivation.
//!
//! # Why the relation carries the pair rather than the approximation
//!
//! The obvious Replacement instance sends `n` to *the approximation* with domain
//! `succ n`, and then the recursion's graph is `⋃` of the resulting set. That
//! works, but it makes single-valuedness of the union a statement about two
//! approximations with **different** domains, which is a strictly stronger
//! agreement lemma than uniqueness needs.
//!
//! Sending `n` to the *pair* `⟨n, app(h,n)⟩` instead makes the image already be
//! the graph. Single-valuedness is then immediate from
//! [`crate::recursion::approx_unique`] — two pairs over the same `n` come from
//! two approximations over the same domain — and no union is taken at all. The
//! cross-domain form of [`crate::recursion::approx_agree`] is still needed, but
//! only once, for the step equation, rather than for the whole function
//! property.
//!
//! # What discharges Replacement's antecedent
//!
//! Existence is [`crate::recursion::approx_exists`] and uniqueness is
//! [`crate::recursion::approx_unique`]; the `∃!` is assembled from them at the
//! *pair*, so the value's uniqueness is inherited from the approximation's. Both
//! are handed in and instantiated, never rebuilt, so a mismatch surfaces as
//! `None`.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::{
    a1i, and_left, and_right, define_by_membership, hyp_and, hyp_mp, inst_all, uncurry,
};
use super::approximation::approx;
use super::rec::Rec;

/// The recursion's graph, with the Replacement instance that produced it.
pub struct Family {
    /// The index variable of the relation.
    pub x: FreeVar,
    /// The value variable of the relation.
    pub y: FreeVar,
    /// `φ(x,y) := ∃h. (Approx(succ x, h) ∧ y = ⟨x, app(h,x)⟩)`.
    pub phi: Formula,
    /// `⊢ ∀x. (x ∈ ω → ∃!y. φ)` — Replacement's antecedent, discharged.
    pub functional: Thm,
    /// The graph symbol `Γ`, of arity `params.len()`.
    pub graph: FnSym,
    /// `⊢ ∀y. (y ∈ Γ(params) ↔ ∃x. (x ∈ ω ∧ φ))` — already instantiated back at
    /// the parameters, so callers see the `∀y` form whatever the arity is.
    pub members: Thm,
    /// The term `Γ(params)`.
    pub term: Term,
}

impl Family {
    /// The term `Γ(params)`.
    pub fn set(&self) -> Term { self.term.clone() }
}

/// Build the [`Family`]: the relation, its `∃!`, the Replacement instance and
/// the resulting symbol.
///
/// `exists` must be [`crate::recursion::approx_exists`]'s theorem and `unique`
/// [`crate::recursion::approx_unique`]'s, both at the same `g` and `c`.
///
/// `params` are the free variables `Γ` is to depend on — `[]` for a closed base
/// value, `[cv]` when `c` is the variable `cv` and the eventual symbol is to be
/// `iter(c)`. They must cover every free variable of `c`, or
/// [`kernel::thm::define`] refuses.
pub fn family(
    env: &mut Env,
    r: &Rec,
    g: FnSym,
    c: &Term,
    exists: &Thm,
    unique: &Thm,
    params: &[FreeVar],
) -> Option<Family> {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (vh, vh2, y2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let (tvh, tvh2, ty2) = (Term::var(vh), Term::var(vh2), Term::var(y2));
    let sx = r.succ_of(tx.clone());

    let ax1 = approx(env, r, g, c, &sx, &tvh)?;
    let ax2 = approx(env, r, g, c, &sx, &tvh2)?;
    let pair_of = |ht: &Term| r.pair(tx.clone(), r.apply(ht.clone(), tx.clone()));
    let yv = pair_of(&tvh);
    let phi = Formula::exists(
        vh,
        Formula::and(ax1.formula(), Formula::eq(ty.clone(), pair_of(&tvh))),
    );

    let x_om = Formula::mem(tx.clone(), r.omega());
    let w = Formula::and(x_om.clone(), ax1.formula());
    let w_xom = and_left(x_om.clone(), ax1.formula());
    let w_ax = and_right(x_om.clone(), ax1.formula());

    // ── `φ` holds at `y := ⟨x, app(h,x)⟩`, with `h` itself as the witness ────
    let body_yv = Formula::and(ax2.formula(), Formula::eq(yv.clone(), pair_of(&tvh2)));
    debug_assert_eq!(
        Formula::exists(vh2, body_yv.clone()),
        phi.subst(y, &yv),
        "family: the instance of φ at the intended value drifted"
    );
    let w_phi = hyp_mp(
        &a1i(&crate::exists_intro_imp(vh2, body_yv, tvh.clone())?, w.clone()),
        &hyp_and(&w_ax, &a1i(&Thm::eq_refl(yv.clone()), w.clone()))?,
    )?;

    // ── and nothing else does, because the approximation is unique ───────────
    let body_y2 = Formula::and(ax2.formula(), Formula::eq(ty2.clone(), pair_of(&tvh2)));
    let phi_y2 = Formula::exists(vh2, body_y2.clone());
    debug_assert_eq!(phi_y2, phi.subst(y, &ty2), "family: the uniqueness instance drifted");

    let u = Formula::and(w.clone(), phi_y2.clone());
    let v = Formula::and(u.clone(), body_y2.clone());
    let v_u = and_left(u.clone(), body_y2.clone());
    let v_b = and_right(u.clone(), body_y2.clone());
    let v_w = crate::syl(&v_u, &and_left(w.clone(), phi_y2.clone()))?;
    let eq_y2 = Formula::eq(ty2.clone(), pair_of(&tvh2));
    let v_ax2 = crate::syl(&v_b, &and_left(ax2.formula(), eq_y2.clone()))?;
    let v_eq = crate::syl(&v_b, &and_right(ax2.formula(), eq_y2))?;
    let v_ax1 = crate::syl(&v_w, &w_ax)?;
    let v_sx_om = hyp_mp(
        &a1i(&inst_all(&r.core().succ_closed, std::slice::from_ref(&tx))?, v.clone()),
        &crate::syl(&v_w, &w_xom)?,
    )?;
    let uniq_at = inst_all(unique, &[sx.clone(), tvh2.clone(), tvh.clone()])?;
    let v_same = hyp_mp(
        &a1i(&uniq_at, v.clone()),
        &hyp_and(&v_sx_om, &hyp_and(&v_ax2, &v_ax1)?)?,
    )?;
    let wv = env.fresh_var();
    let leib = Thm::eq_leibniz(
        tvh2.clone(),
        tvh.clone(),
        wv,
        Formula::eq(ty2.clone(), pair_of(&Term::var(wv))),
    );
    let v_goal = hyp_mp(&hyp_mp(&a1i(&leib, v.clone()), &v_same)?, &v_eq)?;
    let u_goal = crate::funspace::discharge(vh2, &and_right(w.clone(), phi_y2.clone()), &v_goal)?;
    let w_uniq = Thm::mp(
        &Thm::ax_dist(
            y2,
            w.clone(),
            Formula::imp(phi_y2.clone(), Formula::eq(ty2.clone(), yv.clone())),
        )?,
        &Thm::gen(y2, &uncurry(&u_goal)?),
    )?;

    // ── Assemble `∃!y. φ`, then discharge the approximation ──────────────────
    let eu_body = Formula::and(
        phi.clone(),
        Formula::forall(y2, Formula::imp(phi.subst(y, &ty2), Formula::eq(ty2.clone(), ty.clone()))),
    );
    let w_eu = hyp_mp(
        &a1i(&crate::exists_intro_imp(y, eu_body.clone(), yv)?, w.clone()),
        &hyp_and(&w_phi, &w_uniq)?,
    )?;
    let ex_h = Thm::mp(&Thm::ax_inst(exists.concl().clone(), tx.clone())?, exists)?;
    let functional_body = crate::funspace::discharge(vh, &ex_h, &w_eu)?;
    debug_assert_eq!(
        *functional_body.concl(),
        Formula::imp(x_om.clone(), Formula::exists(y, eu_body)),
        "family: the ∃! obligation drifted"
    );
    let functional = Thm::gen(x, &functional_body);

    // ── Replacement, then the symbol ─────────────────────────────────────────
    let repl = Thm::ax_replacement(env, x, y, phi.clone())?;
    let at_omega = Thm::mp(&Thm::ax_inst(repl.concl().clone(), r.omega())?, &repl)?;
    let ex_graph = Thm::mp(&at_omega, &functional)?;
    let image = Formula::exists(x, Formula::and(x_om, phi.clone()));
    let (graph, closed) = define_by_membership(env, params, &ex_graph, y, &image)?;
    let args: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
    let term = Term::apply(graph, args.clone());
    let members = inst_all(&closed, &args)?;
    debug_assert_eq!(
        *members.concl(),
        Formula::forall(y, Formula::iff(Formula::mem(ty.clone(), term.clone()), image)),
        "family: unexpected shape"
    );
    Some(Family { x, y, phi, functional, graph, members, term })
}
