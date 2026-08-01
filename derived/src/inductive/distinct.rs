//! **Injectivity and pairwise distinctness of the constructors** — what stops
//! the translation from being about a one-element set.
//!
//! # Why this is the load-bearing half
//!
//! `INDUCTIVES.md`'s non-negotiables ask every derived lemma to be "checked for
//! non-vacuity", and a family of membership theorems is exactly the shape that
//! fails that test silently: `⊢ ctor_i(…) ∈ carrier` holds for every `i` when
//! `carrier` is a singleton, and holds for *no* `i` when it is empty. The two
//! theorems here are the ones with content:
//!
//! ```text
//! ⊢ ctor_i(y⃗,r⃗) = ctor_i(y⃗′,r⃗′) → (⋀ⱼ yⱼ = yⱼ′) ∧ (⋀ⱼ rⱼ = rⱼ′)   [ctor_injective]
//! ⊢ ¬(ctor_i(y⃗,r⃗) = ctor_j(y⃗′,r⃗′))                    for i ≠ j    [ctors_distinct]
//! ```
//!
//! Together they say the carrier has one element per (constructor, argument
//! tuple): distinctness separates the constructors, injectivity separates the
//! arguments within one. An `n`-constructor enumeration therefore has `n`
//! provably different elements, and a tree type sees its subtrees.
//!
//! # Both are read off the Kuratowski pair, twice
//!
//! `ctor_i(y⃗,r⃗)` is `⟨inj_i⟨y⃗⟩, f(r⃗)⟩`, so
//! [`Apply::pair_inj`](crate::funcs::Apply::pair_inj) — which is **W4**, the
//! W-type's `sup_inj` — splits any equation between two constructor
//! applications into an equation between tags and one between functions. Then:
//!
//! * *distinctness* needs only the tag half, and
//!   [`crate::isum::inj_distinct`] refutes it outright, because `inj_i` and
//!   `inj_j` have disjoint ranges for `i ≠ j`. No hypothesis survives, and in
//!   particular the arguments are arbitrary — distinctness does not care whether
//!   either side is well-typed.
//! * *injectivity* uses both halves. The tag half goes through
//!   [`crate::isum::inj_injective`] to `⟨y⃗⟩ = ⟨y⃗′⟩` and then down the pair spine,
//!   one [`Apply::pair_inj`](crate::funcs::Apply::pair_inj) per argument. The
//!   function half is where the recursive arguments come back: `f(r⃗) = f(r⃗′)`
//!   gives `app(f(r⃗), inj_j •) = app(f(r⃗′), inj_j •)` by congruence, and
//!   [`RecArg::app`](crate::recarg::RecArg::app) computes **both sides
//!   unconditionally** to `rⱼ` and `rⱼ′`.
//!
//! That last point is why [`crate::recarg`]'s computation rules were derived
//! without a hypothesis even though its typing rule has `m` of them: an
//! injectivity statement carrying `rⱼ ∈ carrier` would be strictly weaker, and
//! would not compose with distinctness at arbitrary arguments.
//!
//! # Interface
//!
//! Private to [`super`]; surfaced as [`Ctor::inj`](super::Ctor::inj) and
//! [`Inductive::distinct`](super::Inductive::distinct).

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::recarg::RecArg;
use crate::recursion::hyp::hyp_eq_trans;
use crate::sigma::Telescope;
use crate::sums::Sums;
use crate::{a1i, and_left, and_right, eq_symm, gen_all, hyp_and, inst_all, mpd_const, syl};

use super::carrier::{Frame, Inductive};
use super::machine::Machine;

/// One side of an equation between constructor applications: fresh variables,
/// the packed tuple, the tag, the recursive-argument function and the whole
/// term.
struct Side {
    args: Vec<FreeVar>,
    recs: Vec<FreeVar>,
    ys: Vec<Term>,
    rs: Vec<Term>,
    tuple: Term,
    tag: Term,
    fun: Term,
    term: Term,
}

fn side(env: &mut Env, mach: &Machine, i: usize, k: usize, m: usize) -> Option<Side> {
    let s = &mach.wt.sums;
    let args: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let recs: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
    let ys: Vec<Term> = args.iter().map(|v| Term::var(*v)).collect();
    let rs: Vec<Term> = recs.iter().map(|v| Term::var(*v)).collect();
    let tuple = Telescope::tuple_of(s, &ys);
    let tag = mach.syms.inj(i, tuple.clone())?;
    let fun = RecArg::of(s, &mach.cases, &rs);
    let term = mach.wt.sup(tag.clone(), fun.clone());
    Some(Side { args, recs, ys, rs, tuple, tag, fun, term })
}

/// `⊢ ⟨tag,f⟩ = ⟨tag′,f′⟩ → tag = tag′` and `… → f = f′`, from **W4**.
fn split(s: &Sums, l: &Side, r: &Side) -> Option<(Thm, Thm)> {
    let both = inst_all(
        &s.ap.pair_inj,
        &[l.tag.clone(), l.fun.clone(), r.tag.clone(), r.fun.clone()],
    )?;
    let (eq_tag, eq_fun) = (
        Formula::eq(l.tag.clone(), r.tag.clone()),
        Formula::eq(l.fun.clone(), r.fun.clone()),
    );
    Some((
        syl(&both, &and_left(eq_tag.clone(), eq_fun.clone()))?,
        syl(&both, &and_right(eq_tag, eq_fun))?,
    ))
}

/// `⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. (ctor_i(y⃗,r⃗) = ctor_i(y⃗′,r⃗′) → ⋀ eqs)`.
///
/// The inner `None` is a nullary constructor, where there is nothing to state.
pub(super) fn ctor_injective(
    env: &mut Env,
    mach: &Machine,
    frame: &Frame<'_>,
    i: usize,
) -> Option<Option<Thm>> {
    let s = &mach.wt.sums;
    let (k, m) = (frame.telescopes[i].betas.len(), frame.recargs[i].m);
    if k + m == 0 {
        return Some(None)
    }
    let (l, r) = (side(env, mach, i, k, m)?, side(env, mach, i, k, m)?);
    let h = Formula::eq(l.term.clone(), r.term.clone());
    let (tags_eq, funs_eq) = split(s, &l, &r)?;

    let mut eqs: Vec<Thm> = Vec::with_capacity(k + m);

    // ── the non-recursive arguments, down the tuple's `π₂` spine ────────────
    if k > 0 {
        let mut cur = syl(
            &tags_eq,
            &inst_all(mach.syms.inj_inj(i)?, &[l.tuple.clone(), r.tuple.clone()])?,
        )?;
        for j in 0..k {
            let (rest_l, rest_r) = (
                Telescope::tuple_of(s, &l.ys[j + 1..]),
                Telescope::tuple_of(s, &r.ys[j + 1..]),
            );
            let pair = inst_all(
                &s.ap.pair_inj,
                &[l.ys[j].clone(), rest_l.clone(), r.ys[j].clone(), rest_r.clone()],
            )?;
            let both = syl(&cur, &pair)?;
            let (e_head, e_rest) = (
                Formula::eq(l.ys[j].clone(), r.ys[j].clone()),
                Formula::eq(rest_l, rest_r),
            );
            eqs.push(syl(&both, &and_left(e_head.clone(), e_rest.clone()))?);
            cur = syl(&both, &and_right(e_head, e_rest))?;
        }
    }

    // ── the recursive arguments, by applying both functions at `inj_j •` ────
    for j in 0..m {
        let pt = mach.syms.inj(j, s.point())?;
        let lhs = s.ap.apply(l.fun.clone(), pt.clone());
        let hole = env.fresh_var();
        let congr = mpd_const(
            &Thm::eq_leibniz(
                l.fun.clone(),
                r.fun.clone(),
                hole,
                Formula::eq(lhs.clone(), s.ap.apply(Term::var(hole), pt.clone())),
            ),
            &Thm::eq_refl(lhs.clone()),
        )?;
        let step = syl(&funs_eq, &congr)?;
        let to_l = eq_symm(env, &inst_all(&frame.recargs[i].app[j], &l.rs)?)?;
        let to_r = inst_all(&frame.recargs[i].app[j], &r.rs)?;
        let head = hyp_eq_trans(env, &a1i(&to_l, h.clone()), &step)?;
        let chain = hyp_eq_trans(env, &head, &a1i(&to_r, h.clone()))?;
        debug_assert_eq!(
            *chain.concl(),
            Formula::imp(h.clone(), Formula::eq(l.rs[j].clone(), r.rs[j].clone())),
            "inductive::distinct: a recursive argument's equation has the wrong shape"
        );
        eqs.push(chain);
    }

    let mut out = eqs.pop()?;
    while let Some(e) = eqs.pop() {
        out = hyp_and(&e, &out)?;
    }
    let mut quant = l.args.clone();
    quant.extend(l.recs.iter().copied());
    quant.extend(r.args.iter().copied());
    quant.extend(r.recs.iter().copied());
    Some(Some(gen_all(&quant, &out)))
}

/// `⊢ ∀y⃗ ∀r⃗ ∀y⃗′ ∀r⃗′. ¬(ctor_i(y⃗,r⃗) = ctor_j(y⃗′,r⃗′))`, for `i ≠ j`.
pub(super) fn ctors_distinct(
    env: &mut Env,
    mach: &Machine,
    ind: &Inductive,
    i: usize,
    j: usize,
) -> Option<Thm> {
    let n = ind.ctors.len();
    if i == j || i >= n || j >= n {
        return None
    }
    let s = &mach.wt.sums;
    let l = side(env, mach, i, ind.telescopes[i].betas.len(), ind.recargs[i].m)?;
    let r = side(env, mach, j, ind.telescopes[j].betas.len(), ind.recargs[j].m)?;
    let (tags_eq, _) = split(s, &l, &r)?;
    let refuted = {
        let d = mach.syms.inj_distinct(env, s, i, j)?;
        inst_all(&d, &[l.tuple.clone(), r.tuple.clone()])?
    };
    let out = syl(&tags_eq, &refuted)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::not(Formula::eq(l.term.clone(), r.term.clone())),
        "inductive::distinct: distinctness has the wrong shape"
    );
    let mut quant = l.args.clone();
    quant.extend(l.recs.iter().copied());
    quant.extend(r.args.iter().copied());
    quant.extend(r.recs.iter().copied());
    Some(gen_all(&quant, &out))
}
