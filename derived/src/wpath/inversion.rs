//! **P3** — no junk: every member of `paths` arises from one of the two rules.
//!
//! # Interface
//!
//! ```text
//! arises_root(p) := ∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a),W) ∧ p = ⟨⟨a,f⟩, ⟨∅,a⟩⟩))
//! arises_step(p) := ∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a),W) ∧ ∃b. (b ∈ B(a) ∧ ∃s ∃x.
//!                      (⟨app(f,b), ⟨s,x⟩⟩ ∈ paths ∧ p = ⟨⟨a,f⟩, ⟨⟨b,s⟩,x⟩⟩))))
//! path_arises(p) := arises_root(p) ∨ arises_step(p)
//!
//! ⊢ ∀A ∀B ∀u ∀Q. ((closed(A,B,u) ∧ amb(A,B,Q))
//!                     → ∀p. (p ∈ paths → path_arises(p)))     [paths_inversion]
//! ```
//!
//! Callers need none of the derivation below.
//!
//! # The construction
//!
//! [`super::paths_induction`] at
//!
//! ```text
//! C := { p ∈ Bnd : p ∈ paths ∧ path_arises(p) }
//! ```
//!
//! — the standard reading of a least-closed-set definition backwards, and the
//! analogue of [`crate::wtype::w_inversion`]. `C` is closed under both rules
//! because their conclusions are in `paths` ([`super::paths_intro`]) and *arise*
//! by the very rule that produced them; the step rule's premise is in `C`, hence
//! in `paths`, which is exactly the form the right disjunct asks for.
//!
//! **`C ⊆ Bnd` costs nothing here, and that is why this file is short.** A rule's
//! conclusion is shown to be in `paths` first, and [`super::paths_subset`] then
//! places it in the ambient product — so none of [`super::paths_intro`]'s
//! product-membership work is repeated. Doing it the other way round would
//! double the file.
//!
//! # Why the right disjunct mentions `paths` and not `C`
//!
//! Because that is what a consumer needs: [`super::paths_injective`] takes a
//! member of `paths` apart and immediately recurses on the premise, which has to
//! be a member of `paths` again. Stating the premise at `C` would be provable
//! just as easily and would say nothing, since `C` is an artefact of this proof
//! and is not exported.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::{or_intro_left, or_intro_right, separation_full};
use crate::sums::Sums;
use crate::wtype::Wtype;
use crate::{
    a1i, and_left, and_right, exists_intro_imp, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr,
    inst_all, syl, uncurry,
};

use super::condition::{path_closed, path_root, path_step, At};
use super::shared::{gen_under, hyp_inst};

/// `f ∈ fs(B(a),W) ∧ p = ⟨⟨a,f⟩, ⟨∅,a⟩⟩` — the root disjunct's innermost matrix,
/// at caller-supplied terms for `a` and `f`.
///
/// Exported because both the proof that builds the disjunct and the proofs that
/// take it apart have to name *this* formula: they quantify it at their own
/// fresh variables, and a second spelling would stop matching.
pub fn root_inner(s: &Sums, at: &At, p: &Term, a_t: &Term, f_t: &Term) -> Formula {
    Formula::and(
        Formula::mem(
            f_t.clone(),
            s.fs.of(s.ap.apply(at.b.clone(), a_t.clone()), at.w.clone()),
        ),
        Formula::eq(
            p.clone(),
            at.pair(
                s,
                at.pair(s, a_t.clone(), f_t.clone()),
                at.pair(s, s.zero(), a_t.clone()),
            ),
        ),
    )
}

/// `a ∈ A ∧ ∃f. root_inner(p,a,f)` — the root disjunct under its outer binder.
pub fn root_matrix(s: &Sums, at: &At, p: &Term, a_t: &Term, fv: kernel::FreeVar) -> Formula {
    Formula::and(
        Formula::mem(a_t.clone(), at.a.clone()),
        Formula::exists(fv, root_inner(s, at, p, a_t, &Term::var(fv))),
    )
}

/// `∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a),W) ∧ p = ⟨⟨a,f⟩, ⟨∅,a⟩⟩))` — "`p` is the root
/// rule's conclusion at some node".
pub fn arises_root(env: &mut Env, s: &Sums, at: &At, p: &Term) -> Formula {
    let (av, fv) = (env.fresh_var(), env.fresh_var());
    Formula::exists(av, root_matrix(s, at, p, &Term::var(av), fv))
}

/// `⟨f(b),⟨s,x⟩⟩ ∈ paths ∧ p = ⟨⟨a,f⟩, ⟨⟨b,s⟩,x⟩⟩` — the step disjunct's
/// innermost matrix, at caller-supplied terms.
#[allow(clippy::too_many_arguments)]
pub fn step_inner(
    s: &Sums,
    at: &At,
    ps: &Term,
    p: &Term,
    a_t: &Term,
    f_t: &Term,
    b_t: &Term,
    s_t: &Term,
    x_t: &Term,
) -> Formula {
    Formula::and(
        Formula::mem(
            at.pair(
                s,
                s.ap.apply(f_t.clone(), b_t.clone()),
                at.pair(s, s_t.clone(), x_t.clone()),
            ),
            ps.clone(),
        ),
        Formula::eq(
            p.clone(),
            at.pair(
                s,
                at.pair(s, a_t.clone(), f_t.clone()),
                at.pair(s, at.pair(s, b_t.clone(), s_t.clone()), x_t.clone()),
            ),
        ),
    )
}

/// `b ∈ B(a) ∧ ∃s ∃x. step_inner(…)` — the step disjunct under its `b` binder.
#[allow(clippy::too_many_arguments)]
pub fn step_matrix_b(
    s: &Sums,
    at: &At,
    ps: &Term,
    p: &Term,
    a_t: &Term,
    f_t: &Term,
    b_t: &Term,
    sv: kernel::FreeVar,
    xv: kernel::FreeVar,
) -> Formula {
    Formula::and(
        Formula::mem(b_t.clone(), s.ap.apply(at.b.clone(), a_t.clone())),
        Formula::exists(
            sv,
            Formula::exists(
                xv,
                step_inner(s, at, ps, p, a_t, f_t, b_t, &Term::var(sv), &Term::var(xv)),
            ),
        ),
    )
}

/// `f ∈ fs(B(a),W) ∧ ∃b. step_matrix_b(…)` — the step disjunct under its `f`
/// binder.
#[allow(clippy::too_many_arguments)]
pub fn step_matrix_f(
    s: &Sums,
    at: &At,
    ps: &Term,
    p: &Term,
    a_t: &Term,
    f_t: &Term,
    bv: kernel::FreeVar,
    sv: kernel::FreeVar,
    xv: kernel::FreeVar,
) -> Formula {
    Formula::and(
        Formula::mem(
            f_t.clone(),
            s.fs.of(s.ap.apply(at.b.clone(), a_t.clone()), at.w.clone()),
        ),
        Formula::exists(
            bv,
            step_matrix_b(s, at, ps, p, a_t, f_t, &Term::var(bv), sv, xv),
        ),
    )
}

/// `a ∈ A ∧ ∃f. step_matrix_f(…)` — the step disjunct under its outer binder.
#[allow(clippy::too_many_arguments)]
pub fn step_matrix(
    s: &Sums,
    at: &At,
    ps: &Term,
    p: &Term,
    a_t: &Term,
    fv: kernel::FreeVar,
    bv: kernel::FreeVar,
    sv: kernel::FreeVar,
    xv: kernel::FreeVar,
) -> Formula {
    Formula::and(
        Formula::mem(a_t.clone(), at.a.clone()),
        Formula::exists(
            fv,
            step_matrix_f(s, at, ps, p, a_t, &Term::var(fv), bv, sv, xv),
        ),
    )
}

/// `∃a. (a ∈ A ∧ ∃f. (f ∈ fs(B(a),W) ∧ ∃b. (b ∈ B(a) ∧ ∃s ∃x.
/// (⟨f(b),⟨s,x⟩⟩ ∈ paths ∧ p = ⟨⟨a,f⟩, ⟨⟨b,s⟩,x⟩⟩))))` — "`p` is the step
/// rule's conclusion, and its premise is again a member of `paths`".
pub fn arises_step(env: &mut Env, s: &Sums, at: &At, ps: &Term, p: &Term) -> Formula {
    let (av, fv, bv, sv, xv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    Formula::exists(av, step_matrix(s, at, ps, p, &Term::var(av), fv, bv, sv, xv))
}

/// `arises_root(p) ∨ arises_step(p)`.
pub fn path_arises(env: &mut Env, s: &Sums, at: &At, ps: &Term, p: &Term) -> Formula {
    let root = arises_root(env, s, at, p);
    let step = arises_step(env, s, at, ps, p);
    Formula::or(root, step)
}

/// The membership condition of the auxiliary set `C` at a term:
/// `p ∈ Bnd ∧ (p ∈ paths ∧ path_arises(p))`.
fn c_body(env: &mut Env, s: &Sums, at: &At, ps: &Term, p: &Term) -> Formula {
    Formula::and(
        Formula::mem(p.clone(), at.bnd.clone()),
        Formula::and(
            Formula::mem(p.clone(), ps.clone()),
            path_arises(env, s, at, ps, p),
        ),
    )
}

/// Split `φ ∧ ψ`, which is `¬(φ → ¬ψ)`.
fn split_and(f: &Formula) -> Option<(Formula, Formula)> {
    let (inner, fls) = f.as_imp()?;
    if fls != Formula::false_() {
        return None
    }
    let (phi, npsi) = inner.as_imp()?;
    let (psi, fls2) = npsi.as_imp()?;
    if fls2 != Formula::false_() {
        return None
    }
    Some((phi, psi))
}

/// The four terms and theorems every helper below needs, so that the two
/// closure proofs take one argument rather than nine.
struct Ctx<'a> {
    s: Sums,
    at: At,
    ps: Term,
    tcs: Term,
    h: Formula,
    cs_ax: Thm,
    paths_sub: &'a Thm,
}

impl Ctx<'_> {
    /// `⊢ K → p ∈ C` from `⊢ K → p ∈ paths` and `⊢ K → path_arises(p)`.
    fn place_in_c(&self, env: &mut Env, p: &Term, k_paths: &Thm, k_arises: &Thm) -> Option<Thm> {
        let at = &self.at;
        let ax = inst_all(
            &self.cs_ax,
            &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), p.clone()],
        )?;
        if *ax.concl()
            != Formula::iff(
                Formula::mem(p.clone(), self.tcs.clone()),
                c_body(env, &self.s, at, &self.ps, p),
            )
        {
            return None
        }
        let k_bnd = syl(
            k_paths,
            &inst_all(
                self.paths_sub,
                &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), p.clone()],
            )?,
        )?;
        syl(&hyp_and(&k_bnd, &hyp_and(k_paths, k_arises)?)?, &iff_mpr(&ax)?)
    }
}

/// **P3, inversion.**
/// `⊢ ∀A ∀B ∀u ∀Q. ((closed ∧ amb) → ∀p. (p ∈ paths → path_arises(p)))`
///
/// `paths_ax`, `paths_ind`, `paths_sub` and `intro` must be
/// [`super::paths_symbol`]'s biconditional, [`super::paths_induction`],
/// [`super::paths_subset`] and [`super::paths_intro`] over the same `paths`;
/// all four are checked at their conclusions and for an empty hypothesis set,
/// since this header promises `⊢ …`.
pub fn paths_inversion(
    env: &mut Env,
    wt: &Wtype,
    paths: FnSym,
    paths_ind: &Thm,
    paths_sub: &Thm,
    intro: &Thm,
) -> Option<Thm> {
    if !crate::all_unconditional(&[paths_ind, paths_sub, intro]) {
        return None
    }
    let s = wt.sums.clone();
    let (av, bv, uv, qv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let at = At::new(wt, Term::var(av), Term::var(bv), Term::var(uv), Term::var(qv));
    let ps = Term::apply(paths, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);

    // ── `C := { p ∈ Bnd : p ∈ paths ∧ path_arises(p) }` ─────────────────────
    let pv = env.fresh_var();
    let tp = Term::var(pv);
    let inner = Formula::and(
        Formula::mem(tp.clone(), ps.clone()),
        path_arises(env, &s, &at, &ps, &tp),
    );
    let existence = separation_full(env, pv, &inner, &at.bnd, &s.ap.empty_ax)?;
    let carved = Formula::and(Formula::mem(tp.clone(), at.bnd.clone()), inner.clone());
    let (cs, cs_ax) =
        crate::define_by_membership(env, &[av, bv, uv, qv], &existence, pv, &carved)?;
    let tcs = Term::apply(cs, vec![at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()]);

    let closed = wt.closed_at(env, &at.a, &at.b, &at.u);
    let ambient = super::intro::amb(env, &s, &at);
    let h = Formula::and(closed, ambient);
    let ctx = Ctx {
        s: s.clone(),
        at: at.clone(),
        ps: ps.clone(),
        tcs: tcs.clone(),
        h: h.clone(),
        cs_ax: cs_ax.clone(),
        paths_sub,
    };

    // `⊢ C ⊆ Bnd`, the left conjunct of the defining biconditional.
    let ax_p = inst_all(
        &cs_ax,
        &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), tp.clone()],
    )?;
    let mem_bnd = Formula::mem(tp.clone(), at.bnd.clone());
    if *ax_p.concl() != Formula::iff(Formula::mem(tp.clone(), tcs.clone()), carved.clone()) {
        return None
    }
    let c_sub = Thm::gen(
        pv,
        &syl(&iff_mp(&ax_p)?, &and_left(mem_bnd.clone(), inner.clone()))?,
    );
    if *c_sub.concl() != kernel::thm::subset(env, tcs.clone(), at.bnd.clone()) {
        return None
    }
    // ── `C` is closed under both rules, under `H` ───────────────────────────
    let intro_at = inst_all(intro, &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone()])?;
    let closure = path_closed(env, &s, &at, &ps);
    if *intro_at.concl() != Formula::imp(h.clone(), closure.clone()) {
        return None
    }
    let (root_ps, step_ps) = split_and(&closure)?;
    let h_root = syl(&intro_at, &and_left(root_ps.clone(), step_ps.clone()))?;
    let h_step = syl(&intro_at, &and_right(root_ps, step_ps))?;

    let root_c = root_closed(env, &ctx, &h_root)?;
    let step_c = step_closed(env, &ctx, &h_step)?;
    // ── P2 at `C`, then read the disjunction back off `C` ───────────────────
    let ind_at = inst_all(
        paths_ind,
        &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), tcs.clone()],
    )?;
    let h_sub = hyp_mp(
        &a1i(&ind_at, h.clone()),
        &hyp_and(&a1i(&c_sub, h.clone()), &hyp_and(&root_c, &step_c)?)?,
    )?;
    let arises = path_arises(env, &s, &at, &ps, &tp);
    let from_c = syl(
        &syl(&iff_mp(&ax_p)?, &and_right(mem_bnd, inner))?,
        &and_right(Formula::mem(tp.clone(), ps.clone()), arises.clone()),
    )?;
    let mem_paths = Formula::mem(tp.clone(), ps.clone());
    let h_p = syl(
        &hyp_inst(&h_sub, &tp)?,
        &crate::imp_mono_r(&from_c, mem_paths)?,
    )?;
    let body = Formula::imp(Formula::mem(tp.clone(), ps), arises);
    let out = gen_under(pv, &h, &body, &h_p)?;
    if *out.concl() != Formula::imp(h, Formula::forall(pv, body)) {
        return None
    }
    Some(gen_all(&[av, bv, uv, qv], &out))
}

/// `⊢ H → path_root(C)`.
fn root_closed(env: &mut Env, ctx: &Ctx<'_>, h_root: &Thm) -> Option<Thm> {
    let (s, at, h) = (&ctx.s, &ctx.at, &ctx.h);
    let (av2, fv) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av2), Term::var(fv));
    let fibre = s.ap.apply(at.b.clone(), ta.clone());
    let mem_a = Formula::mem(ta.clone(), at.a.clone());
    let mem_f = Formula::mem(tf.clone(), s.fs.of(fibre, at.w.clone()));
    let guard = Formula::and(mem_a.clone(), mem_f.clone());
    let k = Formula::and(h.clone(), guard.clone());
    let k_h = and_left(h.clone(), guard.clone());
    let k_g = and_right(h.clone(), guard.clone());
    let k_a = syl(&k_g, &and_left(mem_a.clone(), mem_f.clone()))?;
    let k_f = syl(&k_g, &and_right(mem_a.clone(), mem_f.clone()))?;

    let node = at.pair(s, ta.clone(), tf.clone());
    let entry = at.pair(s, s.zero(), ta.clone());
    let p = at.pair(s, node, entry);

    let k_paths = {
        let at_f = hyp_inst(&hyp_inst(&syl(&k_h, h_root)?, &ta)?, &tf)?;
        hyp_mp(&at_f, &hyp_and(&k_a, &k_f)?)?
    };
    // The left disjunct, witnessed at this `a` and this `f`.
    //
    // **The two witness variables are fresh, and have to be.** `p` mentions `a`
    // and `f`, so quantifying over *those* variables would capture their
    // occurrences inside `p` and produce `∃a ∃f. (… ∧ p = p)` — trivially true
    // and not [`arises_root`].
    let k_arises = {
        let (wa, wf) = (env.fresh_var(), env.fresh_var());
        let (twa, twf) = (Term::var(wa), Term::var(wf));
        let f_body = |a_t: &Term, f_t: &Term| {
            Formula::and(
                Formula::mem(
                    f_t.clone(),
                    s.fs.of(s.ap.apply(at.b.clone(), a_t.clone()), at.w.clone()),
                ),
                Formula::eq(
                    p.clone(),
                    at.pair(
                        s,
                        at.pair(s, a_t.clone(), f_t.clone()),
                        at.pair(s, s.zero(), a_t.clone()),
                    ),
                ),
            )
        };
        let ex_f = exists_intro_imp(wf, f_body(&ta, &twf), tf.clone())?;
        let k_fb = hyp_and(&k_f, &a1i(&Thm::eq_refl(p.clone()), k.clone()))?;
        let k_exf = syl(&k_fb, &ex_f)?;
        let a_body =
            Formula::and(Formula::mem(twa.clone(), at.a.clone()), Formula::exists(wf, f_body(&twa, &twf)));
        let ex_a = exists_intro_imp(wa, a_body, ta.clone())?;
        let at_a = syl(&hyp_and(&k_a, &k_exf)?, &ex_a)?;
        let left = arises_root(env, s, at, &p);
        let right = arises_step(env, s, at, &ctx.ps, &p);
        if at_a.concl().as_imp()?.1 != left {
            return None
        }
        syl(&at_a, &or_intro_left(left, right))?
    };

    let k_c = ctx.place_in_c(env, &p, &k_paths, &k_arises)?;
    let body = Formula::imp(guard, Formula::mem(p, ctx.tcs.clone()));
    let h_f = gen_under(fv, h, &body, &uncurry(&k_c)?)?;
    let (_, inner) = h_f.concl().as_imp()?;
    let out = gen_under(av2, h, &inner, &h_f)?;
    let want = path_root(env, s, at, &ctx.tcs);
    (*out.concl() == Formula::imp(h.clone(), want)).then_some(out)
}

/// `⊢ H → path_step(C)`.
fn step_closed(env: &mut Env, ctx: &Ctx<'_>, h_step: &Thm) -> Option<Thm> {
    let (s, at, h, ps) = (&ctx.s, &ctx.at, &ctx.h, &ctx.ps);
    let (av2, fv, bv2, sv, xv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tf, tb, ts, tx) =
        (Term::var(av2), Term::var(fv), Term::var(bv2), Term::var(sv), Term::var(xv));
    let fibre = s.ap.apply(at.b.clone(), ta.clone());
    let mem_a = Formula::mem(ta.clone(), at.a.clone());
    let mem_f = Formula::mem(tf.clone(), s.fs.of(fibre.clone(), at.w.clone()));
    let node_f = Formula::and(mem_a.clone(), mem_f.clone());

    let entry = at.pair(s, ts.clone(), tx.clone());
    let child = at.pair(s, s.ap.apply(tf.clone(), tb.clone()), entry);
    let mem_b = Formula::mem(tb.clone(), fibre.clone());
    let mem_child_c = Formula::mem(child.clone(), ctx.tcs.clone());
    let prem = Formula::and(mem_b.clone(), mem_child_c.clone());
    let guard = Formula::and(node_f.clone(), prem.clone());

    let k = Formula::and(h.clone(), guard.clone());
    let k_h = and_left(h.clone(), guard.clone());
    let k_g = and_right(h.clone(), guard.clone());
    let k_node = syl(&k_g, &and_left(node_f.clone(), prem.clone()))?;
    let k_prem = syl(&k_g, &and_right(node_f, prem))?;
    let k_a = syl(&k_node, &and_left(mem_a.clone(), mem_f.clone()))?;
    let k_f = syl(&k_node, &and_right(mem_a.clone(), mem_f.clone()))?;
    let k_b = syl(&k_prem, &and_left(mem_b.clone(), mem_child_c.clone()))?;
    let k_child_c = syl(&k_prem, &and_right(mem_b.clone(), mem_child_c))?;

    // The premise is in `C`, hence in `paths`.
    let k_child = {
        let ax = inst_all(
            &ctx.cs_ax,
            &[at.a.clone(), at.b.clone(), at.u.clone(), at.q.clone(), child.clone()],
        )?;
        let body = c_body(env, s, at, ps, &child);
        if *ax.concl() != Formula::iff(Formula::mem(child.clone(), ctx.tcs.clone()), body.clone())
        {
            return None
        }
        let (bnd_c, rest_c) = split_and(&body)?;
        let (in_paths_c, arises_c) = split_and(&rest_c)?;
        syl(
            &syl(&k_child_c, &syl(&iff_mp(&ax)?, &and_right(bnd_c, rest_c))?)?,
            &and_left(in_paths_c, arises_c),
        )?
    };

    let node = at.pair(s, ta.clone(), tf.clone());
    let path = at.pair(s, tb.clone(), ts.clone());
    let p = at.pair(s, node, at.pair(s, path, tx.clone()));

    let k_paths = {
        let mut cur = syl(&k_h, h_step)?;
        for t in [&ta, &tf, &tb, &ts, &tx] {
            cur = hyp_inst(&cur, t)?;
        }
        hyp_mp(&cur, &hyp_and(&hyp_and(&k_a, &k_f)?, &hyp_and(&k_b, &k_child)?)?)?
    };

    // The right disjunct, witnessed at this `a`, `f`, `b`, `s`, `x`.
    //
    // Five **fresh** witness variables, for the reason [`root_closed`] records:
    // `p` mentions all five of the concrete ones.
    let k_arises = {
        let (wa, wf, wb, ws, wx) = (
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
            env.fresh_var(),
        );
        let (twa, twf, twb, tws, twx) =
            (Term::var(wa), Term::var(wf), Term::var(wb), Term::var(ws), Term::var(wx));
        let x_body = |a_t: &Term, f_t: &Term, b_t: &Term, s_t: &Term, x_t: &Term| {
            Formula::and(
                Formula::mem(
                    at.pair(
                        s,
                        s.ap.apply(f_t.clone(), b_t.clone()),
                        at.pair(s, s_t.clone(), x_t.clone()),
                    ),
                    ps.clone(),
                ),
                Formula::eq(
                    p.clone(),
                    at.pair(
                        s,
                        at.pair(s, a_t.clone(), f_t.clone()),
                        at.pair(s, at.pair(s, b_t.clone(), s_t.clone()), x_t.clone()),
                    ),
                ),
            )
        };
        let s_body = |a_t: &Term, f_t: &Term, b_t: &Term, s_t: &Term| {
            Formula::exists(wx, x_body(a_t, f_t, b_t, s_t, &twx))
        };
        let b_body = |a_t: &Term, f_t: &Term, b_t: &Term| {
            Formula::exists(ws, s_body(a_t, f_t, b_t, &tws))
        };
        let f_body = |a_t: &Term, f_t: &Term| {
            Formula::and(
                Formula::mem(
                    f_t.clone(),
                    s.fs.of(s.ap.apply(at.b.clone(), a_t.clone()), at.w.clone()),
                ),
                Formula::exists(
                    wb,
                    Formula::and(
                        Formula::mem(twb.clone(), s.ap.apply(at.b.clone(), a_t.clone())),
                        b_body(a_t, f_t, &twb),
                    ),
                ),
            )
        };
        let a_body = Formula::and(
            Formula::mem(twa.clone(), at.a.clone()),
            Formula::exists(wf, f_body(&twa, &twf)),
        );

        let k_xb = hyp_and(&k_child, &a1i(&Thm::eq_refl(p.clone()), k.clone()))?;
        let k_ex_x = syl(&k_xb, &exists_intro_imp(wx, x_body(&ta, &tf, &tb, &ts, &twx), tx.clone())?)?;
        let k_ex_s = syl(&k_ex_x, &exists_intro_imp(ws, s_body(&ta, &tf, &tb, &tws), ts.clone())?)?;
        let k_ex_b = syl(
            &hyp_and(&k_b, &k_ex_s)?,
            &exists_intro_imp(
                wb,
                Formula::and(
                    Formula::mem(twb.clone(), s.ap.apply(at.b.clone(), ta.clone())),
                    b_body(&ta, &tf, &twb),
                ),
                tb.clone(),
            )?,
        )?;
        let k_ex_f = syl(
            &hyp_and(&k_f, &k_ex_b)?,
            &exists_intro_imp(wf, f_body(&ta, &twf), tf.clone())?,
        )?;
        let at_a = syl(&hyp_and(&k_a, &k_ex_f)?, &exists_intro_imp(wa, a_body, ta.clone())?)?;
        let left = arises_root(env, s, at, &p);
        let right = arises_step(env, s, at, ps, &p);
        if at_a.concl().as_imp()?.1 != right {
            return None
        }
        syl(&at_a, &or_intro_right(left, right))?
    };

    let k_c = ctx.place_in_c(env, &p, &k_paths, &k_arises)?;
    let mut cur = uncurry(&k_c)?;
    for v in [xv, sv, bv2, fv, av2] {
        let (_, body) = cur.concl().as_imp()?;
        cur = gen_under(v, h, &body, &cur)?;
    }
    let want = path_step(env, s, at, &ctx.tcs);
    (*cur.concl() == Formula::imp(h.clone(), want)).then_some(cur)
}
