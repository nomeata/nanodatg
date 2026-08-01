//! Equivalence classes, the quotient set `A/∼`, and `mk`/`sound`.
//!
//! # Interface
//!
//! Writing `∼` for [`super::eqv::eqv_symbol`]'s `eqv(A,R)`,
//!
//! ```text
//! class(A,R,x) := { y ∈ A : ⟨x,y⟩ ∈ eqv(A,R) }      one Separation on `A`
//! quot(A,R)    := { c ∈ 𝒫A : ∃x. (x ∈ A ∧ c = class(A,R,x)) }
//!                                                   one Separation on `𝒫A`
//! ```
//!
//! ```text
//! ⊢ ∀A ∀R ∀x ∀y. (y ∈ class(A,R,x) ↔ (y ∈ A ∧ ⟨x,y⟩ ∈ eqv(A,R)))  [class_symbol]
//! ⊢ ∀A ∀R ∀x. class(A,R,x) ⊆ A                                    [class_subset]
//! ⊢ ∀A ∀R ∀x. (x ∈ A → x ∈ class(A,R,x))                          [class_self]
//! ⊢ ∀A ∀R ∀a ∀b. (⟨a,b⟩ ∈ eqv(A,R) → class(A,R,a) = class(A,R,b)) [class_eq]
//! ⊢ ∀A ∀R ∀a ∀b. ((b ∈ A ∧ class(A,R,a) = class(A,R,b))
//!                     → ⟨a,b⟩ ∈ eqv(A,R))                        [class_exact]
//!
//! ⊢ ∀A ∀R ∀c. (c ∈ quot(A,R) ↔ (c ∈ 𝒫A ∧ ∃x. (x ∈ A ∧ c = class(A,R,x))))
//!                                                                 [quot_symbol]
//! ⊢ ∀A ∀R ∀x. (x ∈ A → class(A,R,x) ∈ quot(A,R))                  [mk_mem]
//! ⊢ ∀A ∀R ∀c. (c ∈ quot(A,R) → ∃x. (x ∈ A ∧ c = class(A,R,x)))    [quot_cases]
//! ⊢ ∀A ∀R ∀a ∀b. ((a ∈ A ∧ (b ∈ A ∧ ⟨a,b⟩ ∈ R))
//!                     → class(A,R,a) = class(A,R,b))              [q_sound]
//! ```
//!
//! Callers need none of the derivations below.
//!
//! # Why `quot` is a Separation on `𝒫A` and not a Replacement over `A`
//!
//! The obvious reading of `{ [x]∼ : x ∈ A }` is Replacement along
//! `x ↦ class(A,R,x)`. It is not needed: every class is a **subset of `A`** by
//! [`class_subset`], so the whole image already sits inside `𝒫A`, and one
//! Separation carves it out. That trades a Replacement instance for a power set,
//! which is the cheaper of the two here because `𝒫A` is a term the development
//! already has and the `∃!` bookkeeping Replacement wants is not free.
//!
//! Replacement *is* used, once, for [`super::lift`] — there the image is a set
//! of *pairs*, not of subsets of anything already named.
//!
//! # `sound` and the interpretation
//!
//! Carneiro (thesis §6.2, the quotient clauses) gives `⟦sound_R⟧γ = •`: the
//! *proof* `sound` carries no information, because `α/R`'s equality is a
//! set-theoretic equality that either holds or does not. What has to be true for
//! that clause to be sound is exactly [`q_sound`] — `⟨a,b⟩ ∈ ⟦R⟧` really does
//! force `[a]∼ = [b]∼` — and that is a statement about *sets*, proved here, not
//! a statement about the proof term. So the `Prop`-valued side of `sound` costs
//! nothing and the set-valued side is [`q_sound`].
//!
//! [`class_exact`] is the converse and is **not** a Lean primitive
//! (`Quot.exact` holds only for `Quot.mk` of an equivalence relation). It is
//! derived here because it is what [`super::lift`]'s single-valuedness needs,
//! and because it is the statement that makes every theorem in this file
//! non-vacuous: without it, `class` could be constant.
//!
//! # Hypothetical premises
//!
//! Every entry below refuses a premise carrying hypotheses, including the
//! `class_ax` inside a [`Classes`] and every theorem field of the [`Sums`] it
//! points at. See [`super::apparatus`] for why, and for the `pow_ax` case that
//! runs through [`mk_mem`] in particular.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::separation_full;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, define_by_membership, eq_symm_imp, exists_intro_imp, gen_all,
    hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all, syl, uncurry,
};

use super::shared::{carry_mem, sums_unconditional};

/// Introduce `class(A,R,x) = { y ∈ A : ⟨x,y⟩ ∈ eqv(A,R) }`, with
/// `⊢ ∀A ∀R ∀x ∀y. (y ∈ class(A,R,x) ↔ (y ∈ A ∧ ⟨x,y⟩ ∈ eqv(A,R)))`.
///
/// One Separation on `A`. Unconditional — [`crate::funcs::separation_full`]
/// does not ask the class to be inhabited, which matters because
/// `class(A,R,x)` for `x ∉ A` is empty and is still a perfectly good set.
///
/// `s` must be unconditional throughout: Separation consumes `s.ap.empty_ax`,
/// and its `Γ` would land on the biconditional every other lemma here starts
/// from.
pub fn class_symbol(env: &mut Env, s: &Sums, eqv: FnSym) -> Option<(FnSym, Thm)> {
    if !sums_unconditional(s) {
        return None
    }
    let (av, rv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx, ty) = (Term::var(av), Term::var(rv), Term::var(xv), Term::var(yv));

    let eqv_t = Term::apply(eqv, vec![ta.clone(), tr.clone()]);
    let cond = Formula::mem(s.ap.sets.pair(tx, ty.clone()), eqv_t);
    let existence = separation_full(env, yv, &cond, &ta, &s.ap.empty_ax)?;
    let guard = Formula::and(Formula::mem(ty, ta), cond);
    define_by_membership(env, &[av, rv, xv], &existence, yv, &guard)
}

/// The symbols and defining axiom every derivation in this file is *about*,
/// bundled so that they travel as one argument.
///
/// This is [`crate::sums::Sums`]'s and [`crate::wtype::Wtype`]'s discipline at
/// a smaller scale: a class is a set built from *the* `eqv` of *the* Separation
/// whose theorem is `class_ax`, and passing the three separately invites a
/// caller to mix a `class` from one definitional extension with an `eqv` from
/// another, which would type-check and prove nothing. [`Classes::parts`] is the
/// guard: it rebuilds the biconditional and refuses a stack that does not match.
#[derive(Clone, Copy)]
pub struct Classes<'a> {
    /// Pairing, product, power set and function space.
    pub s: &'a Sums,
    /// The equivalence closure, from [`super::eqv::eqv_symbol`].
    pub eqv: FnSym,
    /// The class symbol, from [`class_symbol`].
    pub class: FnSym,
    /// `⊢ ∀A ∀R ∀x ∀y. (y ∈ class(A,R,x) ↔ (y ∈ A ∧ ⟨x,y⟩ ∈ eqv(A,R)))`.
    pub class_ax: &'a Thm,
}

impl Classes<'_> {
    /// The hypothesis half of the house rule for this bundle: the [`Sums`] it
    /// points at and its own `class_ax` all **establish** what they say, rather
    /// than merely concluding it.
    ///
    /// [`Classes::parts`] is the conclusion half — it rebuilds the defining
    /// biconditional and refuses a `class_ax` that is not the theorem of this
    /// `class` over this `eqv`. Neither half implies the other, and every entry
    /// taking a `Classes` runs both before deriving anything from it, because
    /// each returns a theorem documented `⊢ …` and no caller re-reads `hyps()`.
    fn unconditional(&self) -> bool {
        sums_unconditional(self.s) && crate::all_unconditional(&[self.class_ax])
    }

    /// The term `class(A,R,x)`.
    fn of(&self, a: &Term, r: &Term, x: &Term) -> Term {
        Term::apply(self.class, vec![a.clone(), r.clone(), x.clone()])
    }

    /// `⟨x,y⟩ ∈ eqv(A,R)`, as a formula.
    fn related(&self, a: &Term, r: &Term, x: &Term, y: &Term) -> Formula {
        Formula::mem(
            self.s.ap.sets.pair(x.clone(), y.clone()),
            Term::apply(self.eqv, vec![a.clone(), r.clone()]),
        )
    }

    /// The defining biconditional, instantiated at explicit terms and split
    /// into its two halves plus the two conjuncts.
    ///
    /// Returns `(y ∈ A, ⟨x,y⟩ ∈ eqv(A,R), forward, backward)`, or `None` if
    /// `class_ax` is not the theorem of `class` over this `eqv`.
    fn parts(
        &self,
        a: &Term,
        r: &Term,
        x: &Term,
        y: &Term,
    ) -> Option<(Formula, Formula, Thm, Thm)> {
        let mem_a = Formula::mem(y.clone(), a.clone());
        let related = self.related(a, r, x, y);
        let at = inst_all(self.class_ax, &[a.clone(), r.clone(), x.clone(), y.clone()])?;
        let mem_class = Formula::mem(y.clone(), self.of(a, r, x));
        if *at.concl() != Formula::iff(mem_class, Formula::and(mem_a.clone(), related.clone())) {
            return None
        }
        Some((mem_a, related, iff_mp(&at)?, iff_mpr(&at)?))
    }
}

/// `⊢ ∀A ∀R ∀x. class(A,R,x) ⊆ A` — a class is a subset of the carrier.
///
/// The left conjunct of the defining biconditional, generalised back into the
/// shape `kernel::thm::subset` builds, so it can be fed straight to the power
/// set axiom in [`mk_mem`].
///
/// `c` must be unconditional; see [`Classes::unconditional`].
///
/// The subset formula is rebuilt and compared **in release too**, not under a
/// `debug_assert`: `class(A,R,x) ⊆ A` is the whole of what this function
/// advertises, it is the last step before the theorem is handed out, and no
/// caller looks at it again — [`mk_mem`] feeds it to the power set axiom, where
/// a differently-shaped subset formula would compose or not according to what
/// `pow_ax` happens to say rather than according to what was proved here.
pub fn class_subset(env: &mut Env, c: &Classes<'_>) -> Option<Thm> {
    if !c.unconditional() {
        return None
    }
    let (av, rv, xv, yv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx, ty) = (Term::var(av), Term::var(rv), Term::var(xv), Term::var(yv));
    let (mem_a, related, fwd, _) = c.parts(&ta, &tr, &tx, &ty)?;
    let body = syl(&fwd, &and_left(mem_a, related))?;

    let out = Thm::gen(yv, &body);
    if *out.concl() != kernel::thm::subset(env, c.of(&ta, &tr, &tx), Term::var(av)) {
        return None
    }
    Some(gen_all(&[av, rv, xv], &out))
}

/// `⊢ ∀A ∀R ∀x. (x ∈ A → x ∈ class(A,R,x))` — every point of the carrier is in
/// its own class.
///
/// Reflexivity of the closure, and nothing else. It is the lemma that makes
/// [`quot_cases`] usable: a class is not merely *named* by a representative, it
/// *contains* one.
///
/// `c` and `eqv_refl` must be unconditional; see [`Classes::unconditional`].
pub fn class_self(env: &mut Env, c: &Classes<'_>, eqv_refl: &Thm) -> Option<Thm> {
    if !c.unconditional() || !crate::all_unconditional(&[eqv_refl]) {
        return None
    }
    let (av, rv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx) = (Term::var(av), Term::var(rv), Term::var(xv));
    let (_, _, _, bwd) = c.parts(&ta, &tr, &tx, &tx)?;
    let refl = inst_all(eqv_refl, &[ta.clone(), tr.clone(), tx.clone()])?;
    let mem_a = Formula::mem(tx.clone(), ta.clone());
    let out = syl(&hyp_and(&imp_refl(mem_a), &refl)?, &bwd)?;
    Some(gen_all(&[av, rv, xv], &out))
}

/// `⊢ ∀A ∀R ∀a ∀b. (⟨a,b⟩ ∈ eqv(A,R) → class(A,R,a) = class(A,R,b))` — related
/// points have the same class.
///
/// Extensionality over the two Separations: `y ∈ class(a)` says `⟨a,y⟩ ∈ ∼`,
/// and `⟨b,a⟩ ∈ ∼` (symmetry) composes with it by transitivity to give
/// `⟨b,y⟩ ∈ ∼`. The other direction is the same argument with `a` and `b`
/// exchanged, using `⟨a,b⟩ ∈ ∼` directly.
///
/// **No `a ∈ A`, no `b ∈ A`.** Both follow from `⟨a,b⟩ ∈ ∼ ⊆ A²`, so asking for
/// them would be asking twice.
///
/// `c`, `eqv_sym` and `eqv_trans` must all be unconditional; see
/// [`Classes::unconditional`].
pub fn class_eq(
    env: &mut Env,
    c: &Classes<'_>,
    eqv_sym: &Thm,
    eqv_trans: &Thm,
) -> Option<Thm> {
    if !c.unconditional() || !crate::all_unconditional(&[eqv_sym, eqv_trans]) {
        return None
    }
    let (av, rv, a1, b1, yv) = (
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
        env.fresh_var(),
    );
    let (ta, tr, taa, tbb, ty) =
        (Term::var(av), Term::var(rv), Term::var(a1), Term::var(b1), Term::var(yv));

    let h = c.related(&ta, &tr, &taa, &tbb);

    // `h → ⟨b,a⟩ ∈ ∼`.
    let h_ba = syl(
        &imp_refl(h.clone()),
        &inst_all(eqv_sym, &[ta.clone(), tr.clone(), taa.clone(), tbb.clone()])?,
    )?;

    // One direction of the extensional comparison. `from` is the class we start
    // in and `bridge` proves `⟨to,from⟩ ∈ ∼` under `h`; transitivity does the
    // rest.
    let half = |from: &Term, to: &Term, bridge: &Thm| -> Option<Thm> {
        let (mem_y_a, rel_from, fwd, _) = c.parts(&ta, &tr, from, &ty)?;
        let (_, _, _, bwd_to) = c.parts(&ta, &tr, to, &ty)?;
        let mem_from = Formula::mem(ty.clone(), c.of(&ta, &tr, from));
        let (bl, br) = (
            and_left(h.clone(), mem_from.clone()),
            and_right(h.clone(), mem_from.clone()),
        );

        let big_ya =
            syl(&br, &syl(&fwd, &and_right(mem_y_a.clone(), rel_from.clone()))?)?;
        let big_mem_a = syl(&br, &syl(&fwd, &and_left(mem_y_a, rel_from))?)?;
        let both = hyp_and(&syl(&bl, bridge)?, &big_ya)?;
        let trans =
            inst_all(eqv_trans, &[ta.clone(), tr.clone(), to.clone(), from.clone(), ty.clone()])?;
        let big_to = syl(&both, &trans)?;
        let target = syl(&hyp_and(&big_mem_a, &big_to)?, &bwd_to)?;
        uncurry(&target)
    };

    let fwd_half = half(&taa, &tbb, &h_ba)?;
    let bwd_half = half(&tbb, &taa, &imp_refl(h.clone()))?;
    let iff_body = hyp_and(&fwd_half, &bwd_half)?;

    let mem_a_cls = Formula::mem(ty.clone(), c.of(&ta, &tr, &taa));
    let mem_b_cls = Formula::mem(ty.clone(), c.of(&ta, &tr, &tbb));
    let same = Formula::iff(mem_a_cls, mem_b_cls);
    let all_same = Thm::mp(&Thm::ax_dist(yv, h.clone(), same)?, &Thm::gen(yv, &iff_body))?;

    let ext = inst_all(
        &Thm::ax_extensionality(env),
        &[c.of(&ta, &tr, &taa), c.of(&ta, &tr, &tbb)],
    )?;
    let out = syl(&all_same, &ext)?;
    Some(gen_all(&[av, rv, a1, b1], &out))
}

/// `⊢ ∀A ∀R ∀a ∀b. ((b ∈ A ∧ class(A,R,a) = class(A,R,b)) → ⟨a,b⟩ ∈ eqv(A,R))`
/// — **exactness**: equal classes come from related points.
///
/// `b ∈ class(b)` by [`class_self`]; rewriting along the equation puts `b` in
/// `class(a)`, which is precisely `⟨a,b⟩ ∈ ∼`. Only `b ∈ A` is needed — `a ∈ A`
/// would be redundant, and in fact does not follow, since for `a ∉ A` both
/// classes are empty and the hypothesis is satisfiable without `a` being
/// anywhere near `A`.
///
/// `c` and `class_self` must be unconditional; see [`Classes::unconditional`].
pub fn class_exact(env: &mut Env, c: &Classes<'_>, class_self: &Thm) -> Option<Thm> {
    if !c.unconditional() || !crate::all_unconditional(&[class_self]) {
        return None
    }
    let (av, rv, a1, b1) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, taa, tbb) = (Term::var(av), Term::var(rv), Term::var(a1), Term::var(b1));
    let cls = |t: &Term| c.of(&ta, &tr, t);

    let eq_ab = Formula::eq(cls(&taa), cls(&tbb));
    let mem_b = Formula::mem(tbb.clone(), ta.clone());
    let h = Formula::and(mem_b.clone(), eq_ab.clone());

    // `h → b ∈ class(b)`.
    let self_b = inst_all(class_self, &[ta.clone(), tr.clone(), tbb.clone()])?;
    let h_in_b = syl(&and_left(mem_b.clone(), eq_ab.clone()), &self_b)?;

    // `h → class(b) = class(a)`, then carry the membership across.
    let flip = eq_symm_imp(env, cls(&taa), cls(&tbb));
    let h_flip = syl(&and_right(mem_b, eq_ab), &flip)?;
    let carry = carry_mem(env, tbb.clone(), cls(&tbb), cls(&taa));
    let h_in_a = hyp_mp(&syl(&h_flip, &carry)?, &h_in_b)?;

    let (mem_a_b, related, fwd, _) = c.parts(&ta, &tr, &taa, &tbb)?;
    let out = syl(&h_in_a, &syl(&fwd, &and_right(mem_a_b, related.clone()))?)?;
    if *out.concl() != Formula::imp(h, related) {
        return None
    }
    Some(gen_all(&[av, rv, a1, b1], &out))
}

/// Introduce `quot(A,R) = { c ∈ 𝒫A : ∃x. (x ∈ A ∧ c = class(A,R,x)) }`, with
/// `⊢ ∀A ∀R ∀c. (c ∈ quot(A,R) ↔ (c ∈ 𝒫A ∧ ∃x. (x ∈ A ∧ c = class(A,R,x))))`.
///
/// This is `A/∼`. One Separation on the power set; see the module header for
/// why that beats a Replacement.
///
/// `s` must be unconditional throughout: Separation consumes `s.ap.empty_ax`.
pub fn quot_symbol(env: &mut Env, s: &Sums, class: FnSym) -> Option<(FnSym, Thm)> {
    if !sums_unconditional(s) {
        return None
    }
    let (av, rv, cv, xv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tc) = (Term::var(av), Term::var(rv), Term::var(cv));
    let cond = quot_cond(class, &ta, &tr, &tc, xv);
    let pow_a = Term::apply(s.pow, vec![ta.clone()]);
    let existence = separation_full(env, cv, &cond, &pow_a, &s.ap.empty_ax)?;
    let guard = Formula::and(Formula::mem(tc, pow_a), cond);
    define_by_membership(env, &[av, rv], &existence, cv, &guard)
}

/// `∃x. (x ∈ A ∧ c = class(A,R,x))` — "`c` is a class", as a formula.
pub(super) fn quot_cond(
    class: FnSym,
    a: &Term,
    r: &Term,
    c: &Term,
    xv: kernel::FreeVar,
) -> Formula {
    let tx = Term::var(xv);
    Formula::exists(
        xv,
        Formula::and(
            Formula::mem(tx.clone(), a.clone()),
            Formula::eq(c.clone(), Term::apply(class, vec![a.clone(), r.clone(), tx])),
        ),
    )
}

/// `⊢ ∀A ∀R ∀x. (x ∈ A → class(A,R,x) ∈ quot(A,R))` — **`mk`'s typing rule**.
///
/// `⟦mk_R x⟧γ = [⟦x⟧γ]∼`, and this is the statement that the right-hand side
/// really is a member of `⟦α/R⟧γ`. Two halves: the class is in `𝒫A` by
/// [`class_subset`] and the power set axiom — *unconditionally*, since the
/// subset holds for every `x` — and it satisfies the existential with itself as
/// witness, which is where `x ∈ A` is spent.
///
/// This is the entry the audit's worked case runs through: the `Thm::mp`
/// against `s.pow_ax` below is what imports a hypothetical `Sums`'s `Γ` into
/// `mk_mem`, and from there into `lift_in_funspace` and every non-vacuity
/// theorem. So all three theorems it consumes — `s.pow_ax` via
/// `sums_unconditional`, `class_sub` and `quot_ax` — are checked here.
pub fn mk_mem(
    env: &mut Env,
    s: &Sums,
    class: FnSym,
    class_sub: &Thm,
    quot: FnSym,
    quot_ax: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[class_sub, quot_ax]) {
        return None
    }
    let (av, rv, xv, wv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tx, tw) = (Term::var(av), Term::var(rv), Term::var(xv), Term::var(wv));
    let cls_x = Term::apply(class, vec![ta.clone(), tr.clone(), tx.clone()]);
    let mem_a = Formula::mem(tx.clone(), ta.clone());

    // `class(A,R,x) ∈ 𝒫A`, with no hypothesis at all.
    let pow_a = Term::apply(s.pow, vec![ta.clone()]);
    let pow_at = inst_all(&s.pow_ax, &[ta.clone(), cls_x.clone()])?;
    let sub = inst_all(class_sub, &[ta.clone(), tr.clone(), tx.clone()])?;
    let in_pow = Thm::mp(&iff_mpr(&pow_at)?, &sub)?;
    debug_assert_eq!(*in_pow.concl(), Formula::mem(cls_x.clone(), pow_a.clone()));

    // `x ∈ A → ∃w. (w ∈ A ∧ class(A,R,x) = class(A,R,w))`, witnessed by `x`.
    let body = Formula::and(
        Formula::mem(tw.clone(), ta.clone()),
        Formula::eq(cls_x.clone(), Term::apply(class, vec![ta.clone(), tr.clone(), tw])),
    );
    let intro = exists_intro_imp(wv, body, tx.clone())?;
    let refl = Thm::eq_refl(cls_x.clone());
    let witnessed = hyp_and(&imp_refl(mem_a.clone()), &a1i(&refl, mem_a.clone()))?;
    let h_ex = syl(&witnessed, &intro)?;

    let at = inst_all(quot_ax, &[ta.clone(), tr.clone(), cls_x.clone()])?;
    let out = syl(&hyp_and(&a1i(&in_pow, mem_a), &h_ex)?, &iff_mpr(&at)?)?;
    let goal = Formula::mem(cls_x, Term::apply(quot, vec![ta, tr]));
    if out.concl().as_imp()?.1 != goal {
        return None
    }
    Some(gen_all(&[av, rv, xv], &out))
}

/// `⊢ ∀A ∀R ∀c. (c ∈ quot(A,R) → ∃x. (x ∈ A ∧ c = class(A,R,x)))` — **no junk**:
/// every member of the quotient is a class of a point of `A`.
///
/// The right conjunct of the defining biconditional. Together with [`mk_mem`]
/// it says `quot(A,R)` is exactly the image of `mk`, which is what makes the
/// eliminator in [`super::lift`] total on it.
///
/// `quot_ax` must **establish** the defining biconditional: the shape is pinned
/// a few lines below, and the `hyps()` check here is the other half.
pub fn quot_cases(
    env: &mut Env,
    s: &Sums,
    class: FnSym,
    quot: FnSym,
    quot_ax: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[quot_ax]) {
        return None
    }
    let (av, rv, cv, xv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tc) = (Term::var(av), Term::var(rv), Term::var(cv));
    let cond = quot_cond(class, &ta, &tr, &tc, xv);
    let mem_pow = Formula::mem(tc.clone(), Term::apply(s.pow, vec![ta.clone()]));
    let at = inst_all(quot_ax, &[ta.clone(), tr.clone(), tc.clone()])?;
    let mem_q = Formula::mem(tc, Term::apply(quot, vec![ta.clone(), tr.clone()]));
    if *at.concl() != Formula::iff(mem_q, Formula::and(mem_pow.clone(), cond.clone())) {
        return None
    }
    let out = syl(&iff_mp(&at)?, &and_right(mem_pow, cond))?;
    Some(gen_all(&[av, rv, cv], &out))
}

/// `⊢ ∀A ∀R ∀a ∀b. ((a ∈ A ∧ (b ∈ A ∧ ⟨a,b⟩ ∈ R)) → class(A,R,a) = class(A,R,b))`
/// — **`sound`**.
///
/// [`super::eqv::eqv_incl`] followed by [`class_eq`]: `R` restricted to `A` is
/// inside the closure, and the closure identifies classes. This is the set-level
/// content of `⟦sound_R⟧γ = •`.
///
/// # Why it takes `s` and `class`
///
/// The derivation is `syl(eqv_incl, class_eq)` and nothing else, so *the kernel
/// forces only the middle formula* — that the two premises meet at
/// `⟨a,b⟩ ∈ eqv(A,R)`. Both ends come verbatim from the caller: a `class_eq`
/// concluding `class(A,R,a) = class(A,R,a)` — provable by weakening
/// `Thm::eq_refl`, and so a plausible thing to hold — composes just as well and
/// yields a correctly-proved reflexivity **labelled `sound`**. Since `sound` is
/// the claim that related points really are identified, that is the whole
/// content of the theorem going missing under a name that says otherwise.
///
/// So the two symbols needed to rebuild the statement are arguments, and the
/// conclusion is pinned in release rather than under a `debug_assert`: the
/// checker's `sound` story rests on this formula, and the measurement builds
/// that would drop the assertion are exactly the ones that produce the headline
/// numbers.
pub fn q_sound(
    env: &mut Env,
    s: &Sums,
    class: FnSym,
    eqv_incl: &Thm,
    class_eq: &Thm,
) -> Option<Thm> {
    if !sums_unconditional(s) || !crate::all_unconditional(&[eqv_incl, class_eq]) {
        return None
    }
    let (av, rv, a1, b1) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, taa, tbb) = (Term::var(av), Term::var(rv), Term::var(a1), Term::var(b1));
    let incl = inst_all(eqv_incl, &[ta.clone(), tr.clone(), taa.clone(), tbb.clone()])?;
    let ceq = inst_all(class_eq, &[ta.clone(), tr.clone(), taa.clone(), tbb.clone()])?;
    let out = syl(&incl, &ceq)?;

    let cls = |t: &Term| Term::apply(class, vec![ta.clone(), tr.clone(), t.clone()]);
    let hyp = Formula::and(
        Formula::mem(taa.clone(), ta.clone()),
        Formula::and(
            Formula::mem(tbb.clone(), ta.clone()),
            Formula::mem(s.ap.sets.pair(taa.clone(), tbb.clone()), tr.clone()),
        ),
    );
    if *out.concl() != Formula::imp(hyp, Formula::eq(cls(&taa), cls(&tbb))) {
        return None
    }
    Some(gen_all(&[av, rv, a1, b1], &out))
}
