//! **The graph of a curried relation** — the bridge between Lean's `r` and the
//! set of pairs every theorem in [`super::super::quot`] takes.
//!
//! # The seam this closes
//!
//! `eqv_incl`, `q_sound` and [`rcompat`](super::compat::rcompat) all speak of
//! `⟨x,y⟩ ∈ R`: `R` is a **set of pairs**. Lean's `r : α → α → Prop` interprets
//! curried, `⟦r⟧ ∈ fs(A, fs(A, U₀))`, and "`r x y` holds" is
//! `• ∈ app(app(⟦r⟧,x),y)` — the denotation of a `Prop` being inhabited. So no
//! Lean-side term produces the `R` the quotient machinery consumes, and until
//! this file the whole of it was exercised only against pair-sets built by hand.
//! The theorems were right; nothing could reach them.
//!
//! ```text
//! rel_graph(A, r) := { p ∈ A² : ∀u ∀v. (p = ⟨u,v⟩ → • ∈ app(app(r,u),v)) }
//! ```
//!
//! # Why the `∀u ∀v` form and not `fst`/`snd`
//!
//! The projection reading — `• ∈ app(app(r, π₁p), π₂p)` — is shorter to write
//! and worse to use: it drags [`crate::proj`]'s projection functions and their
//! computation rules into every consumer, and those compute only on pairs, so
//! each use site would owe a "this is a pair" side condition anyway. The
//! quantified form costs exactly one pair-injectivity step, on the *forward*
//! bridge only, and [`crate::sums::Sums`] already carries `pair_inj`. It is also
//! the shape [`super::compat::ker_symbol`] already uses for the same job, so the
//! two Separations in this module read alike.
//!
//! # One symbol, not one per use site
//!
//! `A` and `r` are **arguments**, so [`rel_graph_symbol`] is called once — by
//! [`super::apparatus::Quotient::over`] — and every use site is an application
//! of the same arity-2 symbol. There is no per-site minting here and hence
//! nothing for a caller-side keyed table to deduplicate; contrast a formulation
//! that baked `r` into the symbol, which would mint one Separation per relation
//! and would need exactly such a table. That is why `r` is a parameter and not
//! a `FnSym`.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀A ∀r ∀p. (p ∈ rel_graph(A,r) ↔ (p ∈ A² ∧ ∀u ∀v. (p = ⟨u,v⟩ → • ∈ app(app(r,u),v))))
//!                                                              [rel_graph_symbol]
//! ⊢ ∀A ∀r ∀u ∀v. (⟨u,v⟩ ∈ rel_graph(A,r) → • ∈ app(app(r,u),v))   [graph_pair]
//! ⊢ ∀A ∀r ∀u ∀v. ((u ∈ A ∧ (v ∈ A ∧ • ∈ app(app(r,u),v)))
//!                     → ⟨u,v⟩ ∈ rel_graph(A,r))                   [pair_in_graph]
//! ⊢ ∀A ∀r. rel_graph(A,r) ⊆ prod(A,A)                             [graph_subset]
//! ```
//!
//! The two membership guards on [`pair_in_graph`] are not removable and are the
//! same ones [`rcompat`](super::compat::rcompat) carries: `⟦r⟧` is an arbitrary
//! curried function, so `app(app(r,u),v)` is constrained by nothing when `u` or
//! `v` lies outside `A`, and the Separation is over `A²`.
//!
//! # Nothing here is an axiom
//!
//! One Separation on `prod(A,A)`, and instances of `pair_inj`, `pair_in_prod`
//! and the pair's own reflexivity. No new axiom and no new apparatus.

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::funcs::separation_full;
use crate::sums::Sums;
use crate::{
    a1i, and_left, and_right, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, inst_all, syl, uncurry,
};

use super::shared::{hyp_gen, inst_formula, sums_unconditional};

/// The `rel_graph` symbol and its defining axiom, bundled.
///
/// The same discipline as [`super::compat::Ker`]: [`RelGraph::parts`] rebuilds
/// the biconditional and refuses a `graph_ax` that is not the theorem of this
/// symbol over this pairing.
#[derive(Clone, Copy)]
pub struct RelGraph<'a> {
    /// Pairing, product, power set and function space.
    pub s: &'a Sums,
    /// The graph symbol, from [`rel_graph_symbol`].
    pub graph: FnSym,
    /// `⊢ ∀A ∀r ∀p. (p ∈ rel_graph(A,r) ↔ (p ∈ A² ∧ ∀u ∀v. (p = ⟨u,v⟩ → …)))`.
    pub graph_ax: &'a Thm,
}

impl RelGraph<'_> {
    /// The hypothesis half of the house rule for this bundle: the [`Sums`] it
    /// points at and its own `graph_ax` all **establish** what they say.
    ///
    /// [`RelGraph::parts`] is the conclusion half. Neither implies the other,
    /// and every entry below runs both, because each returns a theorem
    /// documented `⊢ …` and no caller re-reads `hyps()`.
    fn unconditional(&self) -> bool {
        sums_unconditional(self.s) && crate::all_unconditional(&[self.graph_ax])
    }

    /// The term `rel_graph(A,r)`.
    pub fn of(&self, a: &Term, r: &Term) -> Term {
        Term::apply(self.graph, vec![a.clone(), r.clone()])
    }

    /// The defining biconditional, instantiated and split.
    ///
    /// Returns `(p ∈ A², cond, forward, backward)`.
    fn parts(
        &self,
        env: &mut Env,
        a: &Term,
        r: &Term,
        p: &Term,
    ) -> Option<(Formula, Formula, Thm, Thm)> {
        let mem_prod = Formula::mem(p.clone(), self.s.prod.of(a.clone(), a.clone()));
        let cond = graph_cond(env, self.s, r, p);
        let at = inst_all(self.graph_ax, &[a.clone(), r.clone(), p.clone()])?;
        let mem_g = Formula::mem(p.clone(), self.of(a, r));
        if *at.concl() != Formula::iff(mem_g, Formula::and(mem_prod.clone(), cond.clone())) {
            return None
        }
        Some((mem_prod, cond, iff_mp(&at)?, iff_mpr(&at)?))
    }
}

/// `• ∈ app(app(r,u),v)` — "`r u v` holds", at the curried interpretation.
pub fn holds(s: &Sums, r: &Term, u: &Term, v: &Term) -> Formula {
    Formula::mem(s.point(), s.ap.apply(s.ap.apply(r.clone(), u.clone()), v.clone()))
}

/// `∀u ∀v. (p = ⟨u,v⟩ → • ∈ app(app(r,u),v))`, as a formula.
fn graph_cond(env: &mut Env, s: &Sums, r: &Term, p: &Term) -> Formula {
    let (u, v) = (env.fresh_var(), env.fresh_var());
    let (tu, tv) = (Term::var(u), Term::var(v));
    Formula::forall(
        u,
        Formula::forall(
            v,
            Formula::imp(
                Formula::eq(p.clone(), s.ap.sets.pair(tu.clone(), tv.clone())),
                holds(s, r, &tu, &tv),
            ),
        ),
    )
}

/// Introduce
/// `rel_graph(A,r) = { p ∈ A² : ∀u ∀v. (p = ⟨u,v⟩ → • ∈ app(app(r,u),v)) }`.
///
/// One Separation on `prod(A,A)`, unconditional, and **one symbol for every
/// relation** — see the module header.
///
/// `s` must be unconditional throughout: Separation consumes `s.ap.empty_ax`.
pub fn rel_graph_symbol(env: &mut Env, s: &Sums) -> Option<(FnSym, Thm)> {
    if !sums_unconditional(s) {
        return None
    }
    let (av, rv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tp) = (Term::var(av), Term::var(rv), Term::var(pv));
    let prod_aa = s.prod.of(ta.clone(), ta.clone());
    let cond = graph_cond(env, s, &tr, &tp);
    let existence = separation_full(env, pv, &cond, &prod_aa, &s.ap.empty_ax)?;
    let guard = Formula::and(Formula::mem(tp, prod_aa), cond);
    define_graph(env, &[av, rv], &existence, pv, &guard)
}

/// [`crate::define_by_membership`], named so the call above reads.
fn define_graph(
    env: &mut Env,
    params: &[kernel::FreeVar],
    existence: &Thm,
    zv: kernel::FreeVar,
    guard: &Formula,
) -> Option<(FnSym, Thm)> {
    crate::define_by_membership(env, params, existence, zv, guard)
}

/// **`⊢ ∀A ∀r ∀u ∀v. (⟨u,v⟩ ∈ rel_graph(A,r) → • ∈ app(app(r,u),v))`** — read
/// the relation off a member of the graph.
///
/// One instantiation of the `∀u ∀v`, discharged against `Thm::eq_refl`. This is
/// the direction a consumer needs when it *has* a pair in the quotient's `R`
/// and owes Lean's `r u v`.
///
/// `g` must be unconditional; see [`RelGraph::unconditional`].
pub fn graph_pair(env: &mut Env, g: &RelGraph<'_>) -> Option<Thm> {
    if !g.unconditional() {
        return None
    }
    let (av, rv, uv, vv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tu, tv) = (Term::var(av), Term::var(rv), Term::var(uv), Term::var(vv));
    let p = g.s.ap.sets.pair(tu.clone(), tv.clone());
    let (mem_prod, cond, fwd, _) = g.parts(env, &ta, &tr, &p)?;
    let to_cond = syl(&fwd, &and_right(mem_prod, cond.clone()))?;
    let at = inst_formula(&cond, &[tu.clone(), tv.clone()])?;
    let disch = syl(&to_cond, &at)?;
    let mem_g = Formula::mem(p.clone(), g.of(&ta, &tr));
    let out = hyp_mp(&disch, &a1i(&Thm::eq_refl(p), mem_g))?;
    if *out.concl() != Formula::imp(
        Formula::mem(g.s.ap.sets.pair(tu.clone(), tv.clone()), g.of(&ta, &tr)),
        holds(g.s, &tr, &tu, &tv),
    ) {
        return None
    }
    Some(gen_all(&[av, rv, uv, vv], &out))
}

/// **`⊢ ∀A ∀r ∀u ∀v. ((u ∈ A ∧ (v ∈ A ∧ • ∈ app(app(r,u),v)))
/// → ⟨u,v⟩ ∈ rel_graph(A,r))`** — put a related pair into the graph.
///
/// This is the direction the `h`-certificate takes: Lean hands over
/// `r a b` as `• ∈ app(app(⟦r⟧,a),b)`, and what
/// [`super::classes::q_sound`] and [`super::compat::rcompat`] want is
/// `⟨a,b⟩ ∈ R`.
///
/// The only step with content is turning `⟨u,v⟩ = ⟨u′,v′⟩` into `u = u′` and
/// `v = v′` (injectivity of the Kuratowski pair) and transporting the
/// membership along both — the one pair-injectivity step the header trades the
/// projection formulation for.
///
/// `g` must be unconditional; see [`RelGraph::unconditional`]. That covers
/// `s.ap.pair_inj` and `s.pair_in_prod`, the two `Sums` theorems this consumes.
pub fn pair_in_graph(env: &mut Env, g: &RelGraph<'_>) -> Option<Thm> {
    if !g.unconditional() {
        return None
    }
    let s = g.s;
    let (av, rv, uv, vv) =
        (env.fresh_var(), env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (u2, v2) = (env.fresh_var(), env.fresh_var());
    let (ta, tr, tu, tv) = (Term::var(av), Term::var(rv), Term::var(uv), Term::var(vv));
    let (tu2, tv2) = (Term::var(u2), Term::var(v2));
    let p = s.ap.sets.pair(tu.clone(), tv.clone());

    let (mem_u, mem_v, rel_uv) = (
        Formula::mem(tu.clone(), ta.clone()),
        Formula::mem(tv.clone(), ta.clone()),
        holds(s, &tr, &tu, &tv),
    );
    let tail = Formula::and(mem_v.clone(), rel_uv.clone());
    let h = Formula::and(mem_u.clone(), tail.clone());
    let h_u = and_left(mem_u.clone(), tail.clone());
    let h_v =
        syl(&and_right(mem_u.clone(), tail.clone()), &and_left(mem_v.clone(), rel_uv.clone()))?;
    let h_rel = syl(&and_right(mem_u, tail), &and_right(mem_v, rel_uv))?;

    // `⟨u,v⟩ ∈ A²`.
    let pip = inst_all(&s.pair_in_prod, &[ta.clone(), ta.clone(), tu.clone(), tv.clone()])?;
    let h_prod = syl(&hyp_and(&h_u, &h_v)?, &iff_mpr(&pip)?)?;

    // `∀u′ ∀v′. (⟨u,v⟩ = ⟨u′,v′⟩ → • ∈ app(app(r,u′),v′))`.
    let is_eq = Formula::eq(p.clone(), s.ap.sets.pair(tu2.clone(), tv2.clone()));
    let big = Formula::and(h.clone(), is_eq.clone());
    let inj = inst_all(&s.ap.pair_inj, &[tu.clone(), tv.clone(), tu2.clone(), tv2.clone()])?;
    let parts = syl(&and_right(h.clone(), is_eq.clone()), &inj)?;
    let (e_u, e_v) = (Formula::eq(tu.clone(), tu2.clone()), Formula::eq(tv.clone(), tv2.clone()));
    let g_u = syl(&parts, &and_left(e_u.clone(), e_v.clone()))?;
    let g_v = syl(&parts, &and_right(e_u, e_v))?;
    let g_rel = syl(&and_left(h.clone(), is_eq), &h_rel)?;

    let w1 = env.fresh_var();
    let (r1, v1t) = (tr.clone(), tv.clone());
    let move_l = Thm::eq_leibniz(tu.clone(), tu2.clone(), w1, {
        let hole = Term::var(w1);
        holds(s, &r1, &hole, &v1t)
    });
    let step1 = hyp_mp(&syl(&g_u, &move_l)?, &g_rel)?;
    let w2 = env.fresh_var();
    let (r2, u2t) = (tr.clone(), tu2.clone());
    let move_r = Thm::eq_leibniz(tv.clone(), tv2.clone(), w2, {
        let hole = Term::var(w2);
        holds(s, &r2, &u2t, &hole)
    });
    let step2 = hyp_mp(&syl(&g_v, &move_r)?, &step1)?;
    if *step2.concl() != Formula::imp(big, holds(s, &tr, &tu2, &tv2)) {
        return None
    }

    let mut cond_thm = uncurry(&step2)?;
    for v in [v2, u2] {
        cond_thm = hyp_gen(v, &cond_thm)?;
    }
    let (_, _, _, bwd) = g.parts(env, &ta, &tr, &p)?;
    let out = syl(&hyp_and(&h_prod, &cond_thm)?, &bwd)?;
    if *out.concl() != Formula::imp(h, Formula::mem(p, g.of(&ta, &tr))) {
        return None
    }
    Some(gen_all(&[av, rv, uv, vv], &out))
}

/// `⊢ ∀A ∀r. rel_graph(A,r) ⊆ prod(A,A)` — the graph is a relation **on `A`**.
///
/// The immediate content of the Separation, and what distinguishes
/// `rel_graph(A,r)` from "every pair `r` relates": a pair either of whose
/// components lies outside `A` is not in the graph however `r` behaves at it.
/// A consumer feeding the graph to [`super::eqv::eqv_induction`], whose guard is
/// `E ⊆ A²`, needs exactly this.
///
/// The subset formula is rebuilt and compared **in release too**: it is the
/// whole of what this advertises, and its consumer matches it against whatever
/// the induction happens to say rather than against what was proved here — the
/// same reasoning [`super::compat::ker_subset`] records.
pub fn graph_subset(env: &mut Env, g: &RelGraph<'_>) -> Option<Thm> {
    if !g.unconditional() {
        return None
    }
    let (av, rv, pv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ta, tr, tp) = (Term::var(av), Term::var(rv), Term::var(pv));
    let (mem_prod, cond, fwd, _) = g.parts(env, &ta, &tr, &tp)?;
    let body = syl(&fwd, &and_left(mem_prod, cond))?;
    let out = Thm::gen(pv, &body);
    if *out.concl()
        != kernel::thm::subset(env, g.of(&ta, &tr), g.s.prod.of(ta.clone(), ta.clone()))
    {
        return None
    }
    Some(gen_all(&[av, rv], &out))
}
