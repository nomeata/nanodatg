//! `lift` — the eliminator: a function on `A/∼` that computes as `f` does on
//! representatives.
//!
//! # Interface
//!
//! Writing `[x]` for `class(A,R,x)`, `A/∼` for `quot(A,R)` and `f·x` for
//! `app(f,x)`,
//!
//! ```text
//! lift(A,R,f) := { ⟨[x], f·x⟩ : x ∈ A }                    (Replacement over A)
//! compat(A,R,f) := ∀x ∀y. (⟨x,y⟩ ∈ eqv(A,R) → f·x = f·y)
//! ```
//!
//! ```text
//! ⊢ ∀A ∀R ∀f ∀p. (p ∈ lift(A,R,f) ↔ ∃x. (x ∈ A ∧ p = ⟨[x], f·x⟩))  [lift_symbol]
//! ⊢ ∀A ∀R ∀f ∀x. (x ∈ A → ⟨[x], f·x⟩ ∈ lift(A,R,f))               [lift_pair]
//! ⊢ ∀A ∀R ∀f. (compat(A,R,f) → sv(lift(A,R,f)))                   [lift_single_valued]
//! ⊢ ∀A ∀R ∀f ∀x. ((compat(A,R,f) ∧ x ∈ A)
//!                     → app(lift(A,R,f), [x]) = f·x)              [lift_beta]
//! ⊢ ∀A ∀R ∀B ∀f. ((f ∈ fs(A,B) ∧ compat(A,R,f))
//!                     → lift(A,R,f) ∈ fs(A/∼, B))                 [lift_in_funspace]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # The thesis clause, and which half is which
//!
//! Carneiro writes `⟦lift_R β f h⟧γ` as "the function such that
//! `⟦lift_R β f h⟧γ([x]∼) = ⟦f⟧γ(x)`" (thesis §6.2, the quotient bullet list).
//! That sentence has two obligations hiding in it, and they are separated here:
//!
//! * **that such a function exists** — i.e. that the relation
//!   `[x] ↦ f·x` is *well defined*. That is [`lift_single_valued`], and it is
//!   where the compatibility hypothesis `h` is spent: two representatives of the
//!   same class have equal classes, [`super::classes::class_exact`] turns that
//!   back into `⟨x,x′⟩ ∈ ∼`, and `compat` closes it.
//! * **that it computes** — [`lift_beta`], the ι-rule the corpus's
//!   `124_quotLiftReduction` needs, which is [`crate::ext::app_of_pair`] applied
//!   to the pair [`lift_pair`] puts in the graph.
//!
//! [`lift_in_funspace`] is the typing rule on top: given `f : A → B` in the
//! set-theoretic sense, `lift(A,R,f) : A/∼ → B`.
//!
//! # Why Replacement here and Separation for `quot`
//!
//! [`super::classes`] carves `quot(A,R)` out of `𝒫A`, because every class is a
//! subset of `A` and so the image is already inside a set the development names.
//! No such superset is to hand for the *graph* of `lift`: its members are pairs
//! `⟨[x], f·x⟩`, and bounding them would need `prod(quot(A,R), ran f)` — which
//! means knowing a codomain before the function is built. Replacement along
//! `x ↦ ⟨[x], f·x⟩` needs none: the relation is an equation between terms, so
//! the `∃!` premise is [`crate::exists_unique_eq`] and costs nothing.
//!
//! Note the consequence: **`lift(A,R,f)` is a set for every `f`**, compatible or
//! not, and `compat` is an antecedent on the theorems rather than a condition on
//! the construction. An incompatible `f` gives a perfectly good set that simply
//! is not single-valued.
//!
//! # The compatibility hypothesis is about `∼`, not about `R`
//!
//! Lean's `Quot.lift` asks for `∀ a b, r a b → f a = f b`, i.e. compatibility
//! with `R` itself. That is the *weaker*-looking hypothesis, and
//! [`super::compat::compat_closure`] derives [`compat`] from it, so a caller
//! holding the Lean-shaped hypothesis can use everything here. The `∼`-form is
//! what the derivations below actually consume.
//!
//! # Hypothetical premises
//!
//! Every entry below refuses a premise carrying hypotheses, including the
//! `lift_ax` inside a [`Lift`] and every theorem field of the [`Sums`] it points
//! at. See [`super::apparatus`] for why. [`lift_beta`] additionally pins its
//! own **consequent**, for the reason given there.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funspace::{is_function, is_single_valued, is_total};
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, define_by_membership, eq_symm_imp,
    exists_intro_imp, exists_unique_eq, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl,
    inst_all, syl, uncurry,
};

use super::shared::{carry_elem, eq_chain, hyp_gen, hyp_obtain, inst_formula, sums_unconditional};

/// `∀x ∀y. (⟨x,y⟩ ∈ eqv(A,R) → app(f,x) = app(f,y))` — "`f` respects `∼`", as a
/// formula.
///
/// No `x ∈ A` or `y ∈ A` guard: `eqv(A,R) ⊆ prod(A,A)`
/// ([`super::eqv::eqv_subset`]) already puts both inside `A`, so a guard would
/// be a second copy of a fact the antecedent carries.
pub fn compat(env: &mut Env, s: &Sums, eqv: FnSym, a: &Term, r: &Term, f: &Term) -> Formula {
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let related = Formula::mem(
        s.ap.sets.pair(tx.clone(), ty.clone()),
        Term::apply(eqv, vec![a.clone(), r.clone()]),
    );
    let eq = Formula::eq(s.ap.apply(f.clone(), tx), s.ap.apply(f.clone(), ty));
    Formula::forall(x, Formula::forall(y, Formula::imp(related, eq)))
}

/// The graph entry `⟨class(A,R,x), app(f,x)⟩`.
fn entry(s: &Sums, class: FnSym, a: &Term, r: &Term, f: &Term, x: &Term) -> Term {
    s.ap.sets.pair(
        Term::apply(class, vec![a.clone(), r.clone(), x.clone()]),
        s.ap.apply(f.clone(), x.clone()),
    )
}

/// The symbols every derivation in this file is *about*, bundled so that they
/// travel as one argument.
///
/// Same discipline as [`super::classes::Classes`] and, one level up,
/// [`crate::sums::Sums`]: `lift`, `class`, `quot` and `eqv` must all come from
/// the *same* chain of definitional extensions or none of the theorems compose,
/// and [`Lift::parts`] refuses a `lift_ax` that does not match the `class` it
/// was handed.
#[derive(Clone, Copy)]
pub struct Lift<'a> {
    /// Pairing, product, power set and function space.
    pub s: &'a Sums,
    /// The equivalence closure, from [`super::eqv::eqv_symbol`].
    pub eqv: FnSym,
    /// The class symbol, from [`super::classes::class_symbol`].
    pub class: FnSym,
    /// The quotient set, from [`super::classes::quot_symbol`].
    pub quot: FnSym,
    /// The eliminator's graph, from [`lift_symbol`].
    pub lift: FnSym,
    /// `⊢ ∀A ∀R ∀f ∀p. (p ∈ lift(A,R,f) ↔ ∃x. (x ∈ A ∧ p = ⟨class(A,R,x), app(f,x)⟩))`.
    pub lift_ax: &'a Thm,
}

impl Lift<'_> {
    /// The hypothesis half of the house rule for this bundle: the [`Sums`] it
    /// points at and its own `lift_ax` all **establish** what they say.
    ///
    /// [`Lift::parts`] is the conclusion half. Neither implies the other, and
    /// every entry taking a `Lift` runs both, because each returns a theorem
    /// documented `⊢ …` and no caller re-reads `hyps()`.
    fn unconditional(&self) -> bool {
        sums_unconditional(self.s) && crate::all_unconditional(&[self.lift_ax])
    }

    /// The term `lift(A,R,f)`.
    fn of(&self, a: &Term, r: &Term, f: &Term) -> Term {
        Term::apply(self.lift, vec![a.clone(), r.clone(), f.clone()])
    }

    /// `compat(A,R,f)`, over this development's `eqv`.
    fn compat(&self, env: &mut Env, a: &Term, r: &Term, f: &Term) -> Formula {
        compat(env, self.s, self.eqv, a, r, f)
    }

    /// The defining biconditional, instantiated and split.
    ///
    /// Returns `(condition, p ∈ lift → condition, condition → p ∈ lift)`.
    fn parts(
        &self,
        a: &Term,
        r: &Term,
        f: &Term,
        p: &Term,
        xv: kernel::FreeVar,
    ) -> Option<(Formula, Thm, Thm)> {
        let cond = lift_cond(self.s, self.class, a, r, f, p, xv);
        let at = inst_all(self.lift_ax, &[a.clone(), r.clone(), f.clone(), p.clone()])?;
        let mem = Formula::mem(p.clone(), self.of(a, r, f));
        if *at.concl() != Formula::iff(mem, cond.clone()) {
            return None
        }
        Some((cond, iff_mp(&at)?, iff_mpr(&at)?))
    }
}

/// Introduce `lift(A,R,f) = { ⟨class(A,R,x), app(f,x)⟩ : x ∈ A }`, with
/// `⊢ ∀A ∀R ∀f ∀p. (p ∈ lift(A,R,f) ↔ ∃x. (x ∈ A ∧ p = ⟨class(A,R,x), app(f,x)⟩))`.
///
/// Replacement at its cheapest, exactly as [`crate::funspace::identity_graph`]
/// and [`crate::funcs::lambda`]: the relation is `p = t(x)` for a term `t`, so
/// the `∃!` premise is [`crate::exists_unique_eq`] and is free.
///
/// **The one entry in [`crate::quot`] with no hypothesis check**, and the
/// reason is that it consumes no caller-supplied theorem at all: `s` is read
/// only to build the graph *entry* as a term, and the two proofs that go into
/// the definitional extension — the Replacement instance and
/// [`crate::exists_unique_eq`] — are minted here. Being Replacement rather than
/// Separation, it does not even want `s.ap.empty_ax`, which is what every other
/// symbol in this module needs a `Sums` theorem for.
pub fn lift_symbol(env: &mut Env, s: &Sums, class: FnSym) -> Option<(FnSym, Thm)> {
    let (av, rv, fv, xv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tf, tx) = (Term::var(av), Term::var(rv), Term::var(fv), Term::var(xv));

    let target = entry(s, class, &ta, &tr, &tf, &tx);
    let (pv, phi, exu) = exists_unique_eq(env, &[], &target);

    let repl = Thm::ax_replacement(env, xv, pv, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(xv, &a1i(&exu, Formula::mem(tx.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(xv, Formula::and(Formula::mem(tx, ta), phi));
    define_by_membership(env, &[av, rv, fv], &img, pv, &cond)
}

/// `∃x. (x ∈ A ∧ p = ⟨class(A,R,x), app(f,x)⟩)` — the membership condition of
/// [`lift_symbol`], rebuilt at explicit terms.
fn lift_cond(
    s: &Sums,
    class: FnSym,
    a: &Term,
    r: &Term,
    f: &Term,
    p: &Term,
    xv: kernel::FreeVar,
) -> Formula {
    let tx = Term::var(xv);
    Formula::exists(
        xv,
        Formula::and(
            Formula::mem(tx.clone(), a.clone()),
            Formula::eq(p.clone(), entry(s, class, a, r, f, &tx)),
        ),
    )
}

/// `⊢ ∀A ∀R ∀f ∀x. (x ∈ A → ⟨class(A,R,x), app(f,x)⟩ ∈ lift(A,R,f))` — the graph
/// really contains the entry it was built from.
///
/// `l` must be unconditional; see [`Lift::unconditional`].
pub fn lift_pair(env: &mut Env, l: &Lift<'_>) -> Option<Thm> {
    if !l.unconditional() {
        return None
    }
    let s = l.s;
    let class = l.class;
    let (av, rv, fv, xv, wv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, tf, tx) = (Term::var(av), Term::var(rv), Term::var(fv), Term::var(xv));
    let p = entry(s, class, &ta, &tr, &tf, &tx);
    let mem_a = Formula::mem(tx.clone(), ta.clone());

    let (_, _, bwd) = l.parts(&ta, &tr, &tf, &p, wv)?;
    let body = Formula::and(
        Formula::mem(Term::var(wv), ta.clone()),
        Formula::eq(p.clone(), entry(s, class, &ta, &tr, &tf, &Term::var(wv))),
    );
    let intro = exists_intro_imp(wv, body, tx.clone())?;
    let witnessed =
        hyp_and(&imp_refl(mem_a.clone()), &a1i(&Thm::eq_refl(p), mem_a))?;
    let out = syl(&syl(&witnessed, &intro)?, &bwd)?;
    Some(gen_all(&[av, rv, fv, xv], &out))
}

/// `⊢ ∀A ∀R ∀f. (compat(A,R,f) → sv(lift(A,R,f)))` — **`lift` is well defined**.
///
/// The one place the compatibility hypothesis does any work. Two entries over
/// the same class, `⟨u,v⟩` and `⟨u,v′⟩`, come from representatives `x` and `x′`
/// with `class(x) = u = class(x′)`; [`super::classes::class_exact`] turns that
/// into `⟨x,x′⟩ ∈ ∼`, `compat` gives `f·x = f·x′`, and `v = f·x`, `v′ = f·x′`
/// finish it.
///
/// Both existentials are opened with [`super::shared::hyp_obtain`], nested, so
/// the two witnesses are in scope together at the point where their classes are
/// compared.
///
/// `l` and `class_exact` must be unconditional; see [`Lift::unconditional`].
/// `l`'s check covers `s.ap.pair_inj`, which splits the two pair equations
/// below.
pub fn lift_single_valued(env: &mut Env, l: &Lift<'_>, class_exact: &Thm) -> Option<Thm> {
    if !l.unconditional() || !crate::all_unconditional(&[class_exact]) {
        return None
    }
    let (s, class, lift) = (l.s, l.class, l.lift);
    let (av, rv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (uv, v1, v2) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (xv, x2) = (env.fresh_var(), env.fresh_var());
    let (ta, tr, tf) = (Term::var(av), Term::var(rv), Term::var(fv));
    let (tu, tv, tw) = (Term::var(uv), Term::var(v1), Term::var(v2));
    let (tx, ty) = (Term::var(xv), Term::var(x2));

    let c = l.compat(env, &ta, &tr, &tf);
    let p1 = s.ap.sets.pair(tu.clone(), tv.clone());
    let p2 = s.ap.sets.pair(tu.clone(), tw.clone());
    let (_, fwd1, _) = l.parts(&ta, &tr, &tf, &p1, xv)?;
    let (_, fwd2, _) = l.parts(&ta, &tr, &tf, &p2, x2)?;
    let lift_t = Term::apply(lift, vec![ta.clone(), tr.clone(), tf.clone()]);
    let (mem1, mem2) =
        (Formula::mem(p1.clone(), lift_t.clone()), Formula::mem(p2.clone(), lift_t));

    // H := compat ∧ (⟨u,v⟩ ∈ lift ∧ ⟨u,v′⟩ ∈ lift).
    let pair_mems = Formula::and(mem1.clone(), mem2.clone());
    let h = Formula::and(c.clone(), pair_mems.clone());
    let h_c = and_left(c.clone(), pair_mems.clone());
    let h_m1 =
        syl(&and_right(c.clone(), pair_mems.clone()), &and_left(mem1.clone(), mem2.clone()))?;
    let h_m2 = syl(&and_right(c.clone(), pair_mems), &and_right(mem1, mem2))?;

    // The two witness bodies, as formulas.
    let e1 = Formula::and(
        Formula::mem(tx.clone(), ta.clone()),
        Formula::eq(p1, entry(s, class, &ta, &tr, &tf, &tx)),
    );
    let e2 = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::eq(p2, entry(s, class, &ta, &tr, &tf, &ty)),
    );

    let h1 = Formula::and(h.clone(), e1.clone());
    let h2 = Formula::and(h1.clone(), e2.clone());

    // Projections out of the innermost hypothesis `H ∧ E1(x) ∧ E2(x′)`.
    let to_h1 = and_left(h1.clone(), e2.clone());
    let to_e2 = and_right(h1.clone(), e2.clone());
    let to_h = syl(&to_h1, &and_left(h.clone(), e1.clone()))?;
    let to_e1 = syl(&to_h1, &and_right(h.clone(), e1.clone()))?;
    let to_c = syl(&to_h, &h_c)?;

    let (in_a_x, eq_p1) = (
        Formula::mem(tx.clone(), ta.clone()),
        Formula::eq(
            s.ap.sets.pair(tu.clone(), tv.clone()),
            entry(s, class, &ta, &tr, &tf, &tx),
        ),
    );
    let (in_a_y, eq_p2) = (
        Formula::mem(ty.clone(), ta.clone()),
        Formula::eq(
            s.ap.sets.pair(tu.clone(), tw.clone()),
            entry(s, class, &ta, &tr, &tf, &ty),
        ),
    );
    // `x ∈ A` is not needed — only `x′ ∈ A`, which is what `class_exact` asks
    // for — so the left conjunct of `E1(x)` is dropped here.
    let g_eq1 = syl(&to_e1, &and_right(in_a_x, eq_p1))?;
    let g_y = syl(&to_e2, &and_left(in_a_y.clone(), eq_p2.clone()))?;
    let g_eq2 = syl(&to_e2, &and_right(in_a_y, eq_p2))?;

    // Split the two pair equations with injectivity of the Kuratowski pair.
    let cls = |t: &Term| Term::apply(class, vec![ta.clone(), tr.clone(), t.clone()]);
    let app = |t: &Term| s.ap.apply(tf.clone(), t.clone());

    let inj1 = inst_all(&s.ap.pair_inj, &[tu.clone(), tv.clone(), cls(&tx), app(&tx)])?;
    let inj2 = inst_all(&s.ap.pair_inj, &[tu.clone(), tw.clone(), cls(&ty), app(&ty)])?;
    let parts1 = syl(&g_eq1, &inj1)?;
    let parts2 = syl(&g_eq2, &inj2)?;
    let (u_c1, v_a1) = (Formula::eq(tu.clone(), cls(&tx)), Formula::eq(tv.clone(), app(&tx)));
    let (u_c2, v_a2) = (Formula::eq(tu.clone(), cls(&ty)), Formula::eq(tw.clone(), app(&ty)));
    let g_u1 = syl(&parts1, &and_left(u_c1.clone(), v_a1.clone()))?;
    let g_v1 = syl(&parts1, &and_right(u_c1, v_a1))?;
    let g_u2 = syl(&parts2, &and_left(u_c2.clone(), v_a2.clone()))?;
    let g_v2 = syl(&parts2, &and_right(u_c2, v_a2))?;

    // `class(x) = u` then `= class(x′)`.
    let flip_u1 = syl(&g_u1, &eq_symm_imp(env, tu.clone(), cls(&tx)))?;
    let chain = eq_chain(env, cls(&tx), tu.clone(), cls(&ty));
    let g_cls = hyp_mp(&syl(&g_u2, &chain)?, &flip_u1)?;

    // Exactness, then compatibility.
    let exact = inst_all(class_exact, &[ta.clone(), tr.clone(), tx.clone(), ty.clone()])?;
    let g_rel = syl(&hyp_and(&g_y, &g_cls)?, &exact)?;
    let g_app = hyp_mp(&syl(&to_c, &inst_formula(&c, &[tx.clone(), ty.clone()])?)?, &g_rel)?;

    // `v = f·x = f·x′ = v′`.
    let chain2 = eq_chain(env, tv.clone(), app(&tx), app(&ty));
    let g_v_ay = hyp_mp(&syl(&g_app, &chain2)?, &g_v1)?;
    let flip_v2 = syl(&g_v2, &eq_symm_imp(env, tw.clone(), app(&ty)))?;
    let chain3 = eq_chain(env, tv.clone(), app(&ty), tw.clone());
    let g_eq = hyp_mp(&syl(&flip_v2, &chain3)?, &g_v_ay)?;
    debug_assert_eq!(
        *g_eq.concl(),
        Formula::imp(h2, Formula::eq(tv.clone(), tw.clone())),
        "lift_single_valued: innermost shape"
    );

    // Close the two existentials, innermost first.
    let inner = uncurry(&g_eq)?; // H ∧ E1(x) → (E2(x′) → v = v′)
    let ex2 = syl(&and_left(h.clone(), e1.clone()), &syl(&h_m2, &fwd2)?)?;
    let got2 = hyp_obtain(x2, &ex2, &inner)?; // H ∧ E1(x) → v = v′
    let outer = uncurry(&got2)?; // H → (E1(x) → v = v′)
    let ex1 = syl(&h_m1, &fwd1)?;
    let got1 = hyp_obtain(xv, &ex1, &outer)?; // H → v = v′

    // `compat → sv(lift)`.
    let curried = uncurry(&got1)?;
    let mut out = curried;
    for v in [v2, v1, uv] {
        out = hyp_gen(v, &out)?;
    }
    let want = is_single_valued(env, &s.ap.sets, &Term::apply(lift, vec![ta.clone(), tr.clone(), tf.clone()]));
    if out.concl().as_imp()?.1 != want {
        return None
    }
    Some(gen_all(&[av, rv, fv], &out))
}

/// `⊢ ∀A ∀R ∀f ∀x. ((compat(A,R,f) ∧ x ∈ A) → app(lift(A,R,f), class(A,R,x)) = app(f,x))`
/// — **the computation rule**.
///
/// `⟦lift_R β f h⟧γ([x]∼) = ⟦f⟧γ(x)`, which is the step
/// `124_quotLiftReduction` reduces through. Given [`lift_single_valued`] and
/// [`lift_pair`] it is one application of [`crate::ext::app_of_pair`]: the graph
/// relates `[x]` to `f·x` and is single-valued, so `app` returns `f·x`.
///
/// # Both ends are pinned, and why the consequent is the important one
///
/// All three premises must be unconditional; see [`Lift::unconditional`].
///
/// The *antecedent* has always been compared against a freshly built
/// `compat(A,R,f) ∧ x ∈ A`. The **consequent** is now compared too, and in
/// release rather than under a `debug_assert`, because it arrives verbatim from
/// `app_pair`: the derivation is `syl` against `app_pair` instantiated at
/// `lift(A,R,f)`, `[x]` and `f·x`, so the kernel forces only that the middle
/// formulas agree — that `app_pair`'s antecedent is `sv(lift) ∧ ⟨[x],f·x⟩ ∈
/// lift`. An `app_pair` concluding `app(f,x) = app(f,x)` instead of
/// `app(f,x) = y` has exactly that antecedent, is provable by weakening
/// `Thm::eq_refl`, and composes; the result is a correctly-proved reflexivity
/// handed back as the ι-rule.
///
/// That equation *is* the claim — it is the whole of what the checker's
/// `124_quotLiftReduction` story rests on — so leaving it to a `debug_assert`
/// would drop it in exactly the builds that produce the headline numbers
/// (`scripts/arena.sh`, the `stepcount` binary, any `--release` run), which are
/// the ones a reader is most likely to take at face value.
pub fn lift_beta(
    env: &mut Env,
    l: &Lift<'_>,
    lift_sv: &Thm,
    lift_pair: &Thm,
    app_pair: &Thm,
) -> Option<Thm> {
    if !l.unconditional() || !crate::all_unconditional(&[lift_sv, lift_pair, app_pair]) {
        return None
    }
    let (s, class, lift) = (l.s, l.class, l.lift);
    let (av, rv, fv, xv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tf, tx) = (Term::var(av), Term::var(rv), Term::var(fv), Term::var(xv));
    let c = l.compat(env, &ta, &tr, &tf);
    let mem_a = Formula::mem(tx.clone(), ta.clone());
    let h = Formula::and(c.clone(), mem_a.clone());

    let lift_t = Term::apply(lift, vec![ta.clone(), tr.clone(), tf.clone()]);
    let cls_x = Term::apply(class, vec![ta.clone(), tr.clone(), tx.clone()]);
    let val = s.ap.apply(tf.clone(), tx.clone());

    let sv = syl(&and_left(c.clone(), mem_a.clone()), &inst_all(lift_sv, &[ta.clone(), tr.clone(), tf.clone()])?)?;
    let has = syl(
        &and_right(c, mem_a),
        &inst_all(lift_pair, &[ta.clone(), tr.clone(), tf.clone(), tx.clone()])?,
    )?;
    let ap = inst_all(app_pair, &[lift_t.clone(), cls_x.clone(), val.clone()])?;
    let out = syl(&hyp_and(&sv, &has)?, &ap)?;
    let want = Formula::imp(h, Formula::eq(s.ap.apply(lift_t, cls_x), val));
    if *out.concl() != want {
        return None
    }
    Some(gen_all(&[av, rv, fv, xv], &out))
}

/// `⊢ ∀A ∀R ∀B ∀f. ((f ∈ fs(A,B) ∧ compat(A,R,f)) → lift(A,R,f) ∈ fs(quot(A,R), B))`
/// — **`lift`'s typing rule**.
///
/// The three clauses of `isfun`, in order:
///
/// * *subset*: a member of the graph is `⟨[x], f·x⟩` for some `x ∈ A`, and
///   `[x] ∈ A/∼` by [`super::classes::mk_mem`] while `f·x ∈ B` by
///   [`crate::ext::funspace_app_mem`];
/// * *total*: a member of `A/∼` is `[x]` for some `x ∈ A`
///   ([`super::classes::quot_cases`] — the no-junk lemma), and `⟨[x], f·x⟩` is
///   in the graph;
/// * *single-valued*: [`lift_single_valued`].
///
/// `f ∈ fs(A,B)` is used only for `f·x ∈ B`; the other two clauses need nothing
/// about `f` at all.
///
/// All five premises must be unconditional, as must `l`; see
/// [`Lift::unconditional`], which also covers the `s.pair_in_prod` and
/// `s.fs.fs_ax` this consumes. Five premises is five chances to import a `Γ`
/// through the joins below, and the result is documented `⊢ …`.
pub fn lift_in_funspace(
    env: &mut Env,
    l: &Lift<'_>,
    mk_mem: &Thm,
    quot_cases: &Thm,
    lift_pair: &Thm,
    lift_sv: &Thm,
    app_mem: &Thm,
) -> Option<Thm> {
    if !l.unconditional()
        || !crate::all_unconditional(&[mk_mem, quot_cases, lift_pair, lift_sv, app_mem])
    {
        return None
    }
    let (s, class, quot, lift) = (l.s, l.class, l.quot, l.lift);
    let (av, rv, bv, fv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tb, tf) = (Term::var(av), Term::var(rv), Term::var(bv), Term::var(fv));
    let c = l.compat(env, &ta, &tr, &tf);
    let in_fs = Formula::mem(tf.clone(), s.fs.of(ta.clone(), tb.clone()));
    let h = Formula::and(in_fs.clone(), c.clone());
    let h_fs = and_left(in_fs.clone(), c.clone());
    let h_c = and_right(in_fs, c.clone());

    let lift_t = Term::apply(lift, vec![ta.clone(), tr.clone(), tf.clone()]);
    let quot_t = Term::apply(quot, vec![ta.clone(), tr.clone()]);
    let cls = |t: &Term| Term::apply(class, vec![ta.clone(), tr.clone(), t.clone()]);
    let app = |t: &Term| s.ap.apply(tf.clone(), t.clone());

    // ── Clause 1: lift(A,R,f) ⊆ prod(quot(A,R), B) ───────────────────────────
    let (pv, xv) = (env.fresh_var(), env.fresh_var());
    let (tp, tx) = (Term::var(pv), Term::var(xv));
    let (_, fwd, _) = l.parts(&ta, &tr, &tf, &tp, xv)?;
    let mem_p = Formula::mem(tp.clone(), lift_t.clone());
    let goal_p = Formula::mem(tp.clone(), s.prod.of(quot_t.clone(), tb.clone()));

    let hp = Formula::and(h.clone(), mem_p.clone());
    let e = Formula::and(
        Formula::mem(tx.clone(), ta.clone()),
        Formula::eq(tp.clone(), entry(s, class, &ta, &tr, &tf, &tx)),
    );
    let hpe = Formula::and(hp.clone(), e.clone());
    let to_hp = and_left(hp.clone(), e.clone());
    let to_e = and_right(hp.clone(), e.clone());
    let to_h = syl(&to_hp, &and_left(h.clone(), mem_p.clone()))?;
    let in_a = Formula::mem(tx.clone(), ta.clone());
    let eq_p = Formula::eq(tp.clone(), entry(s, class, &ta, &tr, &tf, &tx));
    let g_x = syl(&to_e, &and_left(in_a.clone(), eq_p.clone()))?;
    let g_eq = syl(&to_e, &and_right(in_a, eq_p))?;

    let g_cls = syl(&g_x, &inst_all(mk_mem, &[ta.clone(), tr.clone(), tx.clone()])?)?;
    let am = inst_all(app_mem, &[ta.clone(), tb.clone(), tf.clone(), tx.clone()])?;
    let g_val = hyp_mp(&a1i(&am, hpe.clone()), &hyp_and(&syl(&to_h, &h_fs)?, &g_x)?)?;
    let pip = inst_all(&s.pair_in_prod, &[quot_t.clone(), tb.clone(), cls(&tx), app(&tx)])?;
    let g_entry = syl(&hyp_and(&g_cls, &g_val)?, &iff_mpr(&pip)?)?;
    // `p = ⟨[x], f·x⟩` moves the membership onto `p`; the rewrite is on the
    // *element*, not on the set, so it is [`carry_elem`] and not [`carry_mem`].
    let back = syl(
        &eq_symm_imp(env, tp.clone(), entry(s, class, &ta, &tr, &tf, &tx)),
        &carry_elem(
            env,
            entry(s, class, &ta, &tr, &tf, &tx),
            tp.clone(),
            s.prod.of(quot_t.clone(), tb.clone()),
        ),
    )?;
    let g_in = hyp_mp(&syl(&g_eq, &back)?, &g_entry)?;
    debug_assert_eq!(*g_in.concl(), Formula::imp(hpe, goal_p.clone()));

    let obtained = hyp_obtain(xv, &syl(&and_right(h.clone(), mem_p.clone()), &fwd)?, &uncurry(&g_in)?)?;
    let sub_body = uncurry(&obtained)?; // h → (p ∈ lift → p ∈ prod(quot,B))
    let clause_sub = hyp_gen(pv, &sub_body)?;
    debug_assert_eq!(
        clause_sub.concl().as_imp()?.1,
        kernel::thm::subset(env, lift_t.clone(), s.prod.of(quot_t.clone(), tb.clone())),
        "lift_in_funspace: subset clause shape"
    );

    // ── Clause 2: total on quot(A,R) ─────────────────────────────────────────
    let (cv, x2, yv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ty) = (Term::var(cv), Term::var(x2));
    let mem_c = Formula::mem(tc.clone(), quot_t.clone());
    let hc = Formula::and(h.clone(), mem_c.clone());
    let e2 = Formula::and(
        Formula::mem(ty.clone(), ta.clone()),
        Formula::eq(tc.clone(), cls(&ty)),
    );
    let hce = Formula::and(hc.clone(), e2.clone());
    let t_hc = and_left(hc.clone(), e2.clone());
    let t_e = and_right(hc.clone(), e2.clone());
    let t_h = syl(&t_hc, &and_left(h.clone(), mem_c.clone()))?;
    let in_a2 = Formula::mem(ty.clone(), ta.clone());
    let eq_c = Formula::eq(tc.clone(), cls(&ty));
    let t_y = syl(&t_e, &and_left(in_a2.clone(), eq_c.clone()))?;
    let t_eq = syl(&t_e, &and_right(in_a2, eq_c))?;

    let am2 = inst_all(app_mem, &[ta.clone(), tb.clone(), tf.clone(), ty.clone()])?;
    let t_val = hyp_mp(&a1i(&am2, hce.clone()), &hyp_and(&syl(&t_h, &h_fs)?, &t_y)?)?;
    let t_entry =
        syl(&t_y, &inst_all(lift_pair, &[ta.clone(), tr.clone(), tf.clone(), ty.clone()])?)?;
    // Rewrite the first component `class(y)` to `c`.
    let w = env.fresh_var();
    let move_fst = Thm::eq_leibniz(
        cls(&ty),
        tc.clone(),
        w,
        Formula::mem(s.ap.sets.pair(Term::var(w), app(&ty)), lift_t.clone()),
    );
    let t_flip = syl(&t_eq, &eq_symm_imp(env, tc.clone(), cls(&ty)))?;
    let t_in = hyp_mp(&syl(&t_flip, &move_fst)?, &t_entry)?;

    let body_y = Formula::and(
        Formula::mem(Term::var(yv), tb.clone()),
        Formula::mem(s.ap.sets.pair(tc.clone(), Term::var(yv)), lift_t.clone()),
    );
    let intro = exists_intro_imp(yv, body_y.clone(), app(&ty))?;
    let t_ex = syl(&hyp_and(&t_val, &t_in)?, &intro)?;
    debug_assert_eq!(*t_ex.concl(), Formula::imp(hce, Formula::exists(yv, body_y)));

    let t_obtained =
        hyp_obtain(x2, &syl(&and_right(h.clone(), mem_c.clone()), &inst_all(quot_cases, &[ta.clone(), tr.clone(), tc.clone()])?)?, &uncurry(&t_ex)?)?;
    let total_body = uncurry(&t_obtained)?;
    let clause_total = hyp_gen(cv, &total_body)?;
    debug_assert_eq!(
        clause_total.concl().as_imp()?.1,
        is_total(env, &s.ap.sets, &quot_t, &tb, &lift_t),
        "lift_in_funspace: totality clause shape"
    );

    // ── Clause 3, and the assembly ───────────────────────────────────────────
    let clause_sv =
        syl(&h_c, &inst_all(lift_sv, &[ta.clone(), tr.clone(), tf.clone()])?)?;
    let inner = hyp_and(&clause_total, &clause_sv)?;
    let isfun_thm = hyp_and(&clause_sub, &inner)?;
    let isfun = is_function(env, &s.ap.sets, &s.prod, &quot_t, &tb, &lift_t);
    if isfun_thm.concl().as_imp()?.1 != isfun {
        return None
    }

    let fs_at = inst_all(&s.fs.fs_ax, &[quot_t.clone(), tb.clone(), lift_t.clone()])?;
    let out = syl(&isfun_thm, &iff_mpr(&fs_at)?)?;
    if out.concl().as_imp()?.0 != h {
        return None
    }
    Some(gen_all(&[av, rv, bv, fv], &out))
}
