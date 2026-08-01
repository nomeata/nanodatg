//! **Enumerations**: inductive types whose constructors take no arguments at
//! all, as W-types with empty fibres.
//!
//! This is the degenerate corner of `INDUCTIVES.md`'s translation, and it is
//! the one that reaches `Bool`. For a non-indexed, non-parameterised,
//! non-recursive inductive with `n` constructors, each of arity `0`, the recipe
//!
//! ```text
//! A := the n-element tag set        B := λ_. 0        T := W_{x∈A} B(x)
//! ```
//!
//! degenerates: every fibre `B(a)` is empty, so the only function out of it is
//! `∅`, and every element of the W-type is `⟨tag, ∅⟩`. No recursion happens
//! anywhere, which is why the whole development below is `sup_mem` fired once.
//!
//! The constant-empty family is literally the set `∅`, because
//! [`crate::wtype::app_of_empty`] gives `app(∅,a) = ∅` for **every** `a` — the
//! same trick [`crate::wrec_unit`] uses. No `rec₊` is needed to build `B`.
//!
//! # The bound is the tag set itself
//!
//! `W(A,B,u)` needs a `u` with `closed(A,B,u)`, and
//! [`crate::bound::least_universe_closed`] discharges that at `u := U(c)` given
//! `A ∈ U(c)` and `∀a ∈ A. B(a) ∈ U(c)`. Rather than hunt for a `c`, take
//! **`c := A`**: then `A ∈ U(A)` is [`crate::universe::mem_least_universe`],
//! free of charge, and `∅ ∈ U(A)` follows from `∅ ⊆ A` by the subset clause.
//! So
//!
//! ```text
//! enum(A) := W(A, ∅, U(A))
//! ```
//!
//! carries **no** hypothesis at all. That choice mattered beyond convenience:
//! `1 + 1 ∈ U(c)` for an unrelated `c` is a universe-closure statement that
//! [`crate::universe`] recorded as open when this was written (binary unions
//! and products of members of a universe), so seeding the universe with the tag
//! set is what routed around it. Both are now proved —
//! [`crate::universe::least_universe_bin_union`] and
//! [`crate::funspace::product_in_universe`] — so the detour is no longer
//! forced; it is kept because it costs nothing and keeps `enum(A)` free of any
//! hypothesis whatever.
//!
//! # Interface
//!
//! Writing `enum(A)` for `W(A, ∅, U(A))` and `⟨a,∅⟩` for the Kuratowski pair:
//!
//! ```text
//! ⊢ ∀A. ∅ ∈ U(A)                                       [empty_in_least_universe]
//! ⊢ ∀A. closed(A, ∅, U(A))                             [enum_closed]
//! ⊢ ∀A ∀a. (a ∈ A → ⟨a,∅⟩ ∈ enum(A))                   [enum_mem]
//! ⊢ ∀a ∀a′. (¬(a = a′) → ¬(⟨a,∅⟩ = ⟨a′,∅⟩))            [enum_inj]
//! ```
//!
//! and, at the two-constructor instance that interprets Lean's `Bool`
//! ([`Enum2`], built by [`enum2`]):
//!
//! ```text
//! ⊢ inl(•) ∈ 1 + 1                          ⊢ inr(•) ∈ 1 + 1
//! ⊢ ⟨inl(•),∅⟩ ∈ enum(1 + 1)                 [Enum2::fst]
//! ⊢ ⟨inr(•),∅⟩ ∈ enum(1 + 1)                 [Enum2::snd]
//! ⊢ ¬(⟨inl(•),∅⟩ = ⟨inr(•),∅⟩)               [Enum2::distinct]
//! ```
//!
//! [`enum1`] is the same at `A := 1`, for a one-constructor enumeration, and
//! [`enum0`] names `enum(0)` for a zero-constructor one — which gets no
//! membership theorem, correctly, since it has no elements.
//!
//! # Non-vacuity
//!
//! Everything above would be true of an *empty* `enum(A)` if `enum_mem`'s
//! antecedent were never satisfiable, so the antecedent is discharged, twice,
//! at concrete tags: [`Enum2::fst`] and [`Enum2::snd`] have no hypothesis left.
//! And two membership theorems about one set say nothing about its *size* if
//! the two elements might coincide — a one-element `Bool` would validate both —
//! so [`Enum2::distinct`] is derived as well, from
//! [`crate::sums::sum_disjoint`] through the pair's injectivity. `tests/enums.rs`
//! pins all three to their exact formulas and checks the two terms differ.

use kernel::{Env, Formula, Term, Thm};

use crate::bound::Bound;
use crate::wtype::Wtype;
use crate::{
    a1i, and_intro, contrapos, eq_symm, ex_falso, gen_all, inst_all, syl,
};

/// `⊢ ∀A. ∅ ∈ U(A)`.
///
/// `∅ ⊆ A` holds because nothing is a member of `∅`, and the subset clause of
/// the universe axiom — transferred to `U(·)` by
/// [`crate::universe::least_universe_closed_sub`] — puts a subset of a member
/// back in. The member is `A` itself, by [`crate::universe::mem_least_universe`].
pub fn empty_in_least_universe(env: &mut Env, wt: &Wtype, bnd: &Bound) -> Option<Thm> {
    let s = &wt.sums;
    let av = env.fresh_var();
    let ta = Term::var(av);
    let z = wt.empty();

    let mem_lu = crate::universe::mem_least_universe(env, bnd.lu, &bnd.lu_ax)?;
    let a_in_u = inst_all(&mem_lu, std::slice::from_ref(&ta))?;

    // `∅ ⊆ A`: `∀z. (z ∈ ∅ → z ∈ A)`, from `⊢ ∀z. ¬(z ∈ ∅)`.
    let zv = env.fresh_var();
    let tz = Term::var(zv);
    let sub = Thm::gen(
        zv,
        &syl(
            &inst_all(&s.ap.empty_ax, std::slice::from_ref(&tz))?,
            &ex_falso(Formula::mem(tz, ta.clone())),
        )?,
    );
    let c2 = crate::universe::least_universe_closed_sub(env, bnd.lu, &bnd.lu_ax)?;
    let all_sub = Thm::mp(&inst_all(&c2, &[ta.clone(), ta.clone()])?, &a_in_u)?;
    let out = Thm::mp(&inst_all(&all_sub, std::slice::from_ref(&z))?, &sub)?;
    Some(Thm::gen(av, &out))
}

/// The antecedent every unconditional W-type rule carries, proved at
/// `c := A`, `B := ∅`: `⊢ A ∈ U(A) ∧ ∀a. (a ∈ A → app(∅,a) ∈ U(A))`, stated at
/// the term `a`.
fn typing_at(env: &mut Env, wt: &Wtype, bnd: &Bound, empty_u: &Thm, ta: &Term) -> Option<Thm> {
    let s = &wt.sums;
    let u = Term::apply(bnd.lu, vec![ta.clone()]);
    let z = wt.empty();

    let mem_lu = crate::universe::mem_least_universe(env, bnd.lu, &bnd.lu_ax)?;
    let a_in_u = inst_all(&mem_lu, std::slice::from_ref(ta))?;
    let e_in_u = inst_all(empty_u, std::slice::from_ref(ta))?;

    // Every fibre is `∅`, and `∅ ∈ U(A)`.
    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let app_e = inst_all(&wt.app_empty, std::slice::from_ref(&tb))?;
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        z.clone(),
        wt.fibre(z.clone(), tb.clone()),
        hole,
        Formula::mem(Term::var(hole), u.clone()),
    );
    let fibre_in_u = Thm::mp(&Thm::mp(&carry, &eq_symm(env, &app_e)?)?, &e_in_u)?;
    let fam = Thm::gen(bv, &a1i(&fibre_in_u, Formula::mem(tb, ta.clone())));
    debug_assert_eq!(
        *fam.concl(),
        crate::bound::fibres_in(env, s, ta, &z, &u),
        "enums: the family condition is not the one the W-type rules state"
    );
    Some(and_intro(&a_in_u, &fam))
}

/// `⊢ ∀A. closed(A, ∅, U(A))` — the W-type's bound hypothesis, discharged
/// outright for the constant-empty family over its own universe.
pub fn enum_closed(env: &mut Env, wt: &Wtype, bnd: &Bound, empty_u: &Thm) -> Option<Thm> {
    let av = env.fresh_var();
    let ta = Term::var(av);
    let z = wt.empty();
    let ante = typing_at(env, wt, bnd, empty_u, &ta)?;
    let out = Thm::mp(
        &inst_all(&bnd.least_universe_closed, &[ta.clone(), ta.clone(), z.clone()])?,
        &ante,
    )?;
    debug_assert_eq!(
        *out.concl(),
        crate::wtype::closed(env, &wt.sums, &ta, &z, &Term::apply(bnd.lu, vec![ta.clone()])),
        "enums: closed has the wrong shape"
    );
    Some(Thm::gen(av, &out))
}

/// **The typing rule for a nullary constructor.**
/// `⊢ ∀A ∀a. (a ∈ A → ⟨a,∅⟩ ∈ W(A, ∅, U(A)))`
///
/// [`crate::bound::sup_mem_at`] at `c := A`, `B := ∅`, `f := ∅`. The only
/// function out of the empty fibre is `∅` ([`crate::wtype::empty_is_a_function`]),
/// so the constructor takes no argument beyond its tag, which is the whole
/// content of "this inductive's constructors have no fields".
pub fn enum_mem(env: &mut Env, wt: &Wtype, bnd: &Bound, empty_u: &Thm) -> Option<Thm> {
    let s = &wt.sums;
    let av = env.fresh_var();
    let ta = Term::var(av);
    let u = Term::apply(bnd.lu, vec![ta.clone()]);
    let z = wt.empty();
    let w_t = wt.of(ta.clone(), z.clone(), u.clone());

    let ante = typing_at(env, wt, bnd, empty_u, &ta)?;
    // `⊢ ∀a. (a ∈ A → ∀f. (f ∈ fs(app(∅,a), W) → ⟨a,f⟩ ∈ W))`
    let rule = Thm::mp(
        &inst_all(&bnd.sup_mem, &[ta.clone(), ta.clone(), z.clone()])?,
        &ante,
    )?;

    let bv = env.fresh_var();
    let tb = Term::var(bv);
    let at_b = inst_all(&rule, std::slice::from_ref(&tb))?;

    // `⊢ ∅ ∈ fs(app(∅,a), W)`, by rewriting the fibre to `∅`.
    let empty_fun = inst_all(&wt.empty_fun, std::slice::from_ref(&w_t))?;
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        z.clone(),
        wt.fibre(z.clone(), tb.clone()),
        hole,
        Formula::mem(z.clone(), s.fs.of(Term::var(hole), w_t.clone())),
    );
    let app_e = inst_all(&wt.app_empty, std::slice::from_ref(&tb))?;
    let empty_in_fs = Thm::mp(&Thm::mp(&carry, &eq_symm(env, &app_e)?)?, &empty_fun)?;

    // Under the antecedent `a ∈ A`: instantiate the inner `∀f` at `∅` and
    // discharge its premise.
    let (prem, inner) = at_b.concl().as_imp()?;
    let inst = Thm::ax_inst(inner.clone(), z.clone())?;
    let at_empty = syl(&at_b, &inst)?;
    let have = a1i(&empty_in_fs, prem.clone());
    let out = crate::hyp_mp(&at_empty, &have)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(prem, Formula::mem(wt.sup(tb.clone(), z), w_t)),
        "enums: enum_mem has the wrong shape"
    );
    Some(gen_all(&[av, bv], &out))
}

/// `⊢ ∀a ∀a′. (¬(a = a′) → ¬(⟨a,∅⟩ = ⟨a′,∅⟩))` — distinct tags give distinct
/// elements. This is [`crate::wtype::Wtype::sup_inj`] (the Kuratowski pair's
/// injectivity) contraposed, and it is what stops a two-constructor
/// enumeration from being provably a singleton.
pub fn enum_inj(env: &mut Env, wt: &Wtype) -> Option<Thm> {
    let z = wt.empty();
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let inj = inst_all(&wt.sup_inj, &[tx.clone(), z.clone(), ty.clone(), z.clone()])?;
    // `⟨x,∅⟩ = ⟨y,∅⟩ → (x = y ∧ ∅ = ∅)`, so in particular `→ x = y`.
    let (_, conj) = inj.concl().as_imp()?;
    let left = crate::and_left(Formula::eq(tx.clone(), ty.clone()), Formula::eq(z.clone(), z.clone()));
    debug_assert_eq!(
        conj,
        Formula::and(Formula::eq(tx.clone(), ty.clone()), Formula::eq(z.clone(), z.clone())),
        "enums: sup_inj does not conclude the expected conjunction"
    );
    let to_eq = syl(&inj, &left)?;
    Some(gen_all(&[xv, yv], &contrapos(&to_eq)?))
}

/// The two-constructor enumeration — Lean's `Bool`, and the shape this whole
/// file exists for.
pub struct Enum2 {
    /// `1 + 1`, the tag set.
    pub tags: Term,
    /// `enum(1+1) = W(1+1, ∅, U(1+1))`, the type itself.
    pub ty: Term,
    /// `⟨inl(•), ∅⟩` — the first constructor.
    pub fst_t: Term,
    /// `⟨inr(•), ∅⟩` — the second constructor.
    pub snd_t: Term,
    /// `⊢ ⟨inl(•),∅⟩ ∈ enum(1+1)`, unconditionally.
    pub fst: Thm,
    /// `⊢ ⟨inr(•),∅⟩ ∈ enum(1+1)`, unconditionally.
    pub snd: Thm,
    /// `⊢ ¬(⟨inl(•),∅⟩ = ⟨inr(•),∅⟩)` — the type really has two elements.
    pub distinct: Thm,
}

/// Build [`Enum2`].
pub fn enum2(wt: &Wtype, bnd: &Bound, mem: &Thm, inj: &Thm) -> Option<Enum2> {
    let s = &wt.sums;
    let (one, point) = (s.unit(), s.point());
    let tags = s.sum_of(one.clone(), one.clone());
    let u = Term::apply(bnd.lu, vec![tags.clone()]);
    let z = wt.empty();
    let ty = wt.of(tags.clone(), z.clone(), u);

    let l = s.inl(point.clone());
    let r = s.inr(point.clone());

    // `inl(•) ∈ 1+1` and `inr(•) ∈ 1+1`.
    let l_tag = Thm::mp(
        &inst_all(&s.inl_mem, &[one.clone(), one.clone(), point.clone()])?,
        &s.unit_mem,
    )?;
    let r_tag = Thm::mp(
        &inst_all(&s.inr_mem, &[one.clone(), one.clone(), point.clone()])?,
        &s.unit_mem,
    )?;

    let fst = Thm::mp(&inst_all(mem, &[tags.clone(), l.clone()])?, &l_tag)?;
    let snd = Thm::mp(&inst_all(mem, &[tags.clone(), r.clone()])?, &r_tag)?;

    // `¬(inl(•) = inr(•))`, hence the two elements differ.
    let disjoint = inst_all(&s.disjoint, &[point.clone(), point.clone()])?;
    let distinct = Thm::mp(&inst_all(inj, &[l.clone(), r.clone()])?, &disjoint)?;

    let (fst_t, snd_t) = (wt.sup(l, z.clone()), wt.sup(r, z));
    // The struct's *term* fields are labels for its theorems, and `mem`/`inj`
    // are caller-supplied: a membership about some `X ≠ enum(1+1)` with the
    // right antecedent composes here just as well, and the returned `ty`,
    // `fst_t` and `snd_t` would then name terms the theorems are not about.
    // Checked rather than asserted, for the same reason the guard exists.
    if !mem.hyps().is_empty()
        || !inj.hyps().is_empty()
        || *fst.concl() != Formula::mem(fst_t.clone(), ty.clone())
        || *snd.concl() != Formula::mem(snd_t.clone(), ty.clone())
        || *distinct.concl() != Formula::not(Formula::eq(fst_t.clone(), snd_t.clone()))
    {
        return None
    }
    Some(Enum2 { tags, ty, fst_t, snd_t, fst, snd, distinct })
}

/// The one-constructor enumeration: `A := 1`, sole element `⟨•,∅⟩`.
pub struct Enum1 {
    /// `1`, the tag set.
    pub tags: Term,
    /// `enum(1) = W(1, ∅, U(1))`.
    pub ty: Term,
    /// `⟨•, ∅⟩` — the sole constructor.
    pub only_t: Term,
    /// `⊢ ⟨•,∅⟩ ∈ enum(1)`, unconditionally.
    pub only: Thm,
}

/// Build [`Enum1`].
pub fn enum1(wt: &Wtype, bnd: &Bound, mem: &Thm) -> Option<Enum1> {
    let s = &wt.sums;
    let (one, point) = (s.unit(), s.point());
    let u = Term::apply(bnd.lu, vec![one.clone()]);
    let z = wt.empty();
    let ty = wt.of(one.clone(), z.clone(), u);
    let only = Thm::mp(&inst_all(mem, &[one.clone(), point.clone()])?, &s.unit_mem)?;
    let only_t = wt.sup(point, z);
    // As in [`enum2`]: the term fields label the theorem, and `mem` is the
    // caller's.
    if !mem.hyps().is_empty() || *only.concl() != Formula::mem(only_t.clone(), ty.clone()) {
        return None
    }
    Some(Enum1 { tags: one, ty, only_t, only })
}

/// The zero-constructor enumeration `enum(0) = W(0, ∅, U(0))`, as a term.
///
/// No membership theorem accompanies it, and that is the point: an empty type
/// has no constructors, so there is nothing to type.
pub fn enum0(wt: &Wtype, bnd: &Bound) -> Term {
    let z = wt.empty();
    let u = Term::apply(bnd.lu, vec![z.clone()]);
    wt.of(z.clone(), z, u)
}
