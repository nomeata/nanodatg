//! From a **described** set to a **constructed** one.
//!
//! # Interface
//!
//! Private to [`crate::choice`]. `opair_described` and `pair_in_bridge` are the
//! translation between the kernel's `is_opair(p,a,b)` — a membership condition
//! spelling out `p = {{a},{a,b}}` — and this crate's *term*
//! `⟨a,b⟩ = upair(upair(a,a), upair(a,b))`.
//!
//! # Why a bridge is needed at all
//!
//! `kernel::Thm::ax_choice` and `kernel::thm::pair_in` *describe* ordered pairs,
//! because the kernel has no `upair` symbol: it cannot, since `upair` is a
//! definitional extension introduced in this crate. But everything downstream —
//! [`crate::funspace::is_single_valued`], [`crate::ext::app_of_pair`], `app`
//! itself — is written with the term. Nothing relates the two automatically, so
//! the equivalence has to be derived, and derived under an ambient hypothesis
//! because the description is only ever available inside one.
//!
//! This is **not specific to choice**. It is the first place in the development
//! where a described pair meets a constructed one, and `ax_tarski`'s
//! equinumerosity clause will want the same bridge the day anyone tries to use
//! it — see [`crate::cantor`], which avoids the question by never leaving the
//! described form.

use kernel::{Env, Formula, FreeVar, Term, Thm};
use crate::funcs::Sets;
use crate::{
    a1i, and_intro, and_left, and_right, eq_symm_imp, exists_elim_imp, exists_intro_imp, gen_all,
    hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, inst_self, mpd_const, syl,
};

use super::shared::{hyp_iff_trans, hyp_leibniz, iff_symm, iff_trans, or_cong};

/// Given `⊢ ∀z. (z ∈ t ↔ ψ(z))`, derive `⊢ ∀q. ((∀z. (z ∈ q ↔ ψ(z))) ↔ q = t)`.
///
/// "The set described by `ψ` is `t`, and only `t`." Forward is Extensionality —
/// `q` and `t` have the same members — and backward is Leibniz against the
/// hypothesis itself.
///
/// The premise is *checked* against the shape this expects rather than assumed,
/// since a caller supplying `ψ` and `t_char` separately could easily supply two
/// that do not match.
fn described_is(
    env: &mut Env,
    ext: &Thm,
    t: &Term,
    z: FreeVar,
    psi: &Formula,
    t_char: &Thm,
) -> Option<Thm> {
    let tz = Term::var(z);
    let prop =
        |s: &Term| Formula::forall(z, Formula::iff(Formula::mem(tz.clone(), s.clone()), psi.clone()));
    if *t_char.concl() != prop(t) {
        return None
    }
    let q = env.fresh_var();
    let tq = Term::var(q);
    let h = prop(&tq);

    // ── forward: H → q = t ───────────────────────────────────────────────────
    let h_inst = Thm::ax_inst(h.clone(), tz.clone())?; // ⊢ H → (z ∈ q ↔ ψ)
    let t_at_z = Thm::mp(&Thm::ax_inst(t_char.concl().clone(), tz.clone())?, t_char)?;
    let h_same = hyp_iff_trans(&h_inst, &iff_symm(&t_at_z)?)?; // ⊢ H → (z ∈ q ↔ z ∈ t)
    let same = Formula::iff(
        Formula::mem(tz.clone(), tq.clone()),
        Formula::mem(tz.clone(), t.clone()),
    );
    let h_all = Thm::mp(&Thm::ax_dist(z, h.clone(), same)?, &Thm::gen(z, &h_same))?;
    let fwd = syl(&h_all, &inst_all(ext, &[tq.clone(), t.clone()])?)?;

    // ── backward: q = t → H ──────────────────────────────────────────────────
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(t.clone(), tq.clone(), w, prop(&Term::var(w)));
    let bwd = syl(&eq_symm_imp(env, tq, t.clone()), &mpd_const(&leib, t_char)?)?;

    Some(Thm::gen(q, &and_intro(&fwd, &bwd)))
}

/// From `⊢ ∀z. (A(z) ↔ B(z))` infer
/// `⊢ (∀z. (z ∈ p ↔ A(z))) ↔ (∀z. (z ∈ p ↔ B(z)))`.
fn rewrite_char(z: FreeVar, p: &Term, a: &Formula, b: &Formula, ab: &Thm) -> Option<Thm> {
    let ba = Thm::gen(z, &iff_symm(&inst_self(z, ab)?)?);
    let fwd = rewrite_char_dir(z, p, a, b, ab)?;
    let bwd = rewrite_char_dir(z, p, b, a, &ba)?;
    Some(and_intro(&fwd, &bwd))
}

/// One direction of `rewrite_char`.
fn rewrite_char_dir(
    z: FreeVar,
    p: &Term,
    a: &Formula,
    b: &Formula,
    ab: &Thm,
) -> Option<Thm> {
    let mem = Formula::mem(Term::var(z), p.clone());
    let h = Formula::forall(z, Formula::iff(mem.clone(), a.clone()));
    let h_inst = Thm::ax_inst(h.clone(), Term::var(z))?;
    let h_new = hyp_iff_trans(&h_inst, &inst_self(z, ab)?)?;
    Thm::mp(&Thm::ax_dist(z, h, Formula::iff(mem, b.clone()))?, &Thm::gen(z, &h_new))
}

/// `⊢ ∀a ∀b ∀p. (is_opair(p,a,b) ↔ p = ⟨a,b⟩)` — the kernel's *described*
/// ordered pair is the *constructed* one.
///
/// Three applications of `described_is`, one per layer of the Kuratowski
/// encoding: `{a}`, `{a,b}`, and `{{a},{a,b}}`. The outermost needs its
/// membership condition rewritten first — `is_opair` describes the members of
/// `p` as *sets satisfying* `is_singleton`/`is_upair`, while `upair`'s defining
/// theorem describes them as *equal to* `{a}`/`{a,b}` — which is what
/// `rewrite_char` does, over the disjunction congruence `or_cong`.
pub fn opair_described(env: &mut Env, sets: &Sets, mem_sing: &Thm) -> Option<Thm> {
    let ext = Thm::ax_extensionality(env);
    let (a, b) = (env.fresh_var(), env.fresh_var());
    let (ta, tb) = (Term::var(a), Term::var(b));
    let sa = crate::singleton(sets.up, ta.clone());
    let uab = Term::apply(sets.up, vec![ta.clone(), tb.clone()]);
    let pair = crate::opair(sets.up, ta.clone(), tb.clone());

    // `{a}` and `{a,b}`, each pinned by its membership condition.
    let r = env.fresh_var();
    let psi_s = Formula::eq(Term::var(r), ta.clone());
    let sing_char = inst_all(mem_sing, std::slice::from_ref(&ta))?;
    let sing_is = described_is(env, &ext, &sa, r, &psi_s, &sing_char)?;

    let r2 = env.fresh_var();
    let psi_u = Formula::or(Formula::eq(Term::var(r2), ta.clone()), Formula::eq(Term::var(r2), tb.clone()));
    let up_char = inst_all(&sets.up_ax, &[ta.clone(), tb.clone()])?;
    let up_is = described_is(env, &ext, &uab, r2, &psi_u, &up_char)?;

    // ⊢ ∀q. ((is_singleton(q,a) ∨ is_upair(q,a,b)) ↔ (q = {a} ∨ q = {a,b}))
    let q = env.fresh_var();
    let tq = Term::var(q);
    let disj_iff =
        Thm::gen(q, &or_cong(&inst_all(&sing_is, std::slice::from_ref(&tq))?, &inst_all(&up_is, std::slice::from_ref(&tq))?)?);

    // ⊢ is_opair(p,a,b) ↔ (∀q. (q ∈ p ↔ (q = {a} ∨ q = {a,b})))
    let p = env.fresh_var();
    let tp = Term::var(p);
    let lhs_body = Formula::or(
        kernel::thm::is_singleton(env, tq.clone(), ta.clone()),
        kernel::thm::is_upair(env, tq.clone(), ta.clone(), tb.clone()),
    );
    let rhs_body = Formula::or(Formula::eq(tq.clone(), sa), Formula::eq(tq, uab.clone()));
    let rewritten = rewrite_char(q, &tp, &lhs_body, &rhs_body, &disj_iff)?;
    // The left side must be exactly what the kernel builds, or this bridges
    // nothing.
    let is_op = kernel::thm::is_opair(env, tp.clone(), ta.clone(), tb.clone());
    if iff_mp(&rewritten)?.concl().as_imp()?.0 != is_op {
        return None
    }

    // ⊢ (∀q. (q ∈ p ↔ (q = {a} ∨ q = {a,b}))) ↔ p = ⟨a,b⟩
    let pair_char = inst_all(&sets.up_ax, &[crate::singleton(sets.up, ta.clone()), uab])?;
    let pair_is = described_is(env, &ext, &pair, q, &rhs_body, &pair_char)?;

    let out = iff_trans(&rewritten, &inst_all(&pair_is, &[tp])?)?;
    Some(gen_all(&[a, b, p], &out))
}

/// `⊢ ∀f ∀a ∀b. ((∃p. (p ∈ f ∧ is_opair(p,a,b))) ↔ ⟨a,b⟩ ∈ f)` — the described
/// pair *is in* `f` exactly when the constructed one is.
///
/// This is the form the choice axiom's clauses are stated in, translated into
/// the form `app` and [`crate::funspace::is_single_valued`] are stated in.
pub fn pair_in_bridge(env: &mut Env, sets: &Sets, opair_desc: &Thm) -> Option<Thm> {
    let (f, a, b) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tf, ta, tb) = (Term::var(f), Term::var(a), Term::var(b));
    let pair = sets.pair(ta.clone(), tb.clone());
    let mem_pair = Formula::mem(pair.clone(), tf.clone());

    let p = env.fresh_var();
    let tp = Term::var(p);
    let mem_p = Formula::mem(tp.clone(), tf.clone());
    let is_op = kernel::thm::is_opair(env, tp.clone(), ta.clone(), tb.clone());
    let body = Formula::and(mem_p.clone(), is_op.clone());
    let described = kernel::thm::pair_in(env, tf.clone(), ta.clone(), tb.clone());
    if described != Formula::exists(p, body.clone()) {
        return None
    }

    // ── forward ──────────────────────────────────────────────────────────────
    // Under the body: `p = ⟨a,b⟩` by `opair_desc`, and `p ∈ f`, so Leibniz
    // carries the membership onto the constructed pair.
    let desc_at_p = inst_all(opair_desc, &[ta.clone(), tb.clone(), tp.clone()])?;
    let h_eq = syl(&and_right(mem_p.clone(), is_op.clone()), &iff_mp(&desc_at_p)?)?;
    let w = env.fresh_var();
    let carry = hyp_leibniz(&h_eq, w, &Formula::mem(Term::var(w), tf.clone()))?;
    let h_mem = hyp_mp(&carry, &and_left(mem_p, is_op))?;
    let fwd = exists_elim_imp(p, &Thm::gen(p, &h_mem), &mem_pair)?;

    // ── backward ─────────────────────────────────────────────────────────────
    // `⟨a,b⟩` satisfies its own description, by reflexivity.
    let desc_at_pair = inst_all(opair_desc, &[ta.clone(), tb.clone(), pair.clone()])?;
    let is_op_pair = Thm::mp(&iff_mpr(&desc_at_pair)?, &Thm::eq_refl(pair.clone()))?;
    let conj = hyp_and(&imp_refl(mem_pair.clone()), &a1i(&is_op_pair, mem_pair.clone()))?;
    let bwd = syl(&conj, &exists_intro_imp(p, body, pair)?)?;

    Some(gen_all(&[f, a, b], &and_intro(&fwd, &bwd)))
}

/// `⊢ (A ∧ B) → A`, reading `A` and `B` off the conjunction itself.
pub(super) fn and_left_of(conj: &Formula) -> Thm {
    let (x, y) = crate::empty::split_and(conj).expect("and_left_of: not a conjunction");
    and_left(x, y)
}
