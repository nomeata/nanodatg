//! The dependent product `dprod(A) = Π(x:A). b(x)`, as one Separation on a
//! function space.
//!
//! # Interface
//!
//! For a unary fibre symbol `b`, writing `img(A) = { b(x) : x ∈ A }` for the
//! fibre image, `fs` for [`crate::funspace`]'s function space and
//!
//! ```text
//! L(f)  :=  f ∈ fs(A, ⋃img(A))  ∧  ∀x. (x ∈ A → app(f,x) ∈ b(x))
//! ```
//!
//! for the defining condition — its right conjunct being [`is_section`] — the
//! exports are
//!
//! ```text
//! ⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = b(x)))   [image_symbol]
//! ⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))                   [dprod_symbol, checked by dprod_members]
//! ⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))                  [dprod_subset_funspace]
//! ```
//!
//! [`DProd::new`] introduces both symbols and proves all of it in one call, and
//! is the only entry point a caller needs; the free functions are exposed for
//! the tests that check the pieces separately. **Nothing here is an axiom** —
//! `img` is one Replacement and `dprod` is one Separation.
//!
//! # What it denotes, and the default it no longer carries
//!
//! `⟦Π(x:A). B(x)⟧` is an opaque symbol in the checker, which is why `pi_cong`
//! gaps. What it should denote is the functions on `A` whose value at each `x`
//! lands in the fibre `b(x)`. The codomain has to be *some* set containing
//! every fibre, and `⋃{b(x) : x ∈ A}` is the cheapest one: a Replacement image
//! followed by a union, both total, so it costs no side condition.
//!
//! The dependent product really can be empty — take any `x ∈ A` with `b(x)`
//! empty — so [`crate::funcs::separation_nonempty`], which needs its result
//! inhabited, did not apply. The way out was the one
//! [`crate::funspace::funspace`] and [`crate::funcs::collection`] also took:
//! define the disjunctive condition
//!
//! ```text
//! f ∈ dprod(A)  ↔  L(f)  ∨  (¬∃g. L(g)  ∧  f ∈ fs(A, ⋃img(A)))
//! ```
//!
//! so that the symbol was total, with the intended condition recoverable only
//! under the antecedent `∃g. L(g)` — and, unlike the function space, there was
//! no canonical section available to discharge it, so `dprod_ax` was an
//! implication nobody could use.
//!
//! `∅` removes the whole construction. [`crate::funcs::separation_full`] carves
//! the set out whether or not anything is in it, so [`dprod_symbol`] defines
//! `L(f)` directly and [`dprod_members`] states it with no antecedent.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::Funspace;
use crate::{a1i, and_left, gen_all, iff_mp, inst_all, syl};

/// The Replacement image `img(A) = { b(x) : x ∈ A }`, with
/// `⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = b(x)))`.
///
/// Replacement at its cheapest, exactly as [`crate::funcs::lambda`]: the
/// relation is `w = b(x)`, so the `∃!` premise is
/// [`crate::exists_unique_eq`] and costs nothing. `b` must be unary.
pub fn image_symbol(env: &mut Env, b: FnSym) -> Option<(FnSym, Thm)> {
    if b.arity() != 1 {
        return None
    }
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(av), Term::var(x));
    let bx = Term::apply(b, vec![tx.clone()]);

    let (w, phi, exu) = crate::exists_unique_eq(env, &[], &bx);
    let repl = Thm::ax_replacement(env, x, w, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(x, &a1i(&exu, Formula::mem(tx.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
    crate::define_by_membership(env, &[av], &img, w, &cond)
}

/// The dependent product `dprod(A) = Π(x:A). b(x)`, for a unary fibre symbol
/// `b`, together with everything proved about it.
pub struct DProd {
    /// `img(A) = { b(x) : x ∈ A }`.
    pub img: FnSym,
    /// `⊢ ∀A ∀w. (w ∈ img(A) ↔ ∃x. (x ∈ A ∧ w = b(x)))`.
    pub img_ax: Thm,
    /// The symbol itself.
    pub dprod: FnSym,
    /// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))` — the defining axiom, which is now the
    /// intended condition and nothing else.
    pub dprod_def: Thm,
    /// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))`, where `L(f)` is
    /// `f ∈ fs(A,⋃img(A)) ∧ ∀x. (x ∈ A → app(f,x) ∈ b(x))` — the same
    /// statement, with [`dprod_members`] having rebuilt `L` independently and
    /// checked it against the defining axiom.
    pub dprod_ax: Thm,
    /// `⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))`.
    pub dprod_sub: Thm,
}

impl DProd {
    /// Introduce `img` and `dprod` and prove both lemmas about them.
    ///
    /// `fsp` must be the function space built over `ap.sets`, or the terms will
    /// not compose: every symbol here is a definitional extension, so a second
    /// `Sets` would give a second, unrelated pairing operation.
    pub fn new(env: &mut Env, ap: &Apply, fsp: &Funspace, b: FnSym) -> Option<DProd> {
        let (img, img_ax) = image_symbol(env, b)?;
        let (dprod, dprod_def) = dprod_symbol(env, ap, fsp, img, b)?;
        let dprod_ax = dprod_members(env, ap, fsp, img, b, dprod, &dprod_def)?;
        let dprod_sub = dprod_subset_funspace(env, ap, fsp, img, b, dprod, &dprod_def)?;
        Some(DProd { img, img_ax, dprod, dprod_def, dprod_ax, dprod_sub })
    }

    /// The term `dprod(A)`.
    pub fn of(&self, a: Term) -> Term { Term::apply(self.dprod, vec![a]) }
}

/// The base set `⋃ img(A)` — a superset of every fibre `b(x)` for `x ∈ A`.
pub(super) fn base_of(ap: &Apply, img: FnSym, a: &Term) -> Term {
    ap.sets.union_of(Term::apply(img, vec![a.clone()]))
}

/// `∀x. (x ∈ A → app(f,x) ∈ b(x))` — `f` is a section of the fibration.
pub fn is_section(env: &mut Env, ap: &Apply, b: FnSym, a: &Term, f: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(ap.apply(f.clone(), tx.clone()), Term::apply(b, vec![tx])),
        ),
    )
}

/// The membership condition defined: `L(f) := f ∈ fs(A,⋃img(A)) ∧ section(f)`,
/// together with the function space term it is carved out of.
fn dprod_cond(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    a: &Term,
    f: FreeVar,
) -> (Formula, Term) {
    let tf = Term::var(f);
    let fs_t = fsp.of(a.clone(), base_of(ap, img, a));
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    (Formula::and(mem_fs, is_section(env, ap, b, a, &tf)), fs_t)
}

/// Introduce `dprod(A) = Π(x:A). b(x)`, with
/// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))`.
///
/// One call to [`crate::funcs::separation_full`] and nothing else: the
/// condition it carves by, `f ∈ fs(A,⋃img(A)) ∧ section(f)`, *is* `L(f)` on the
/// nose, so there is not even a shape to convert. See the section comment for
/// the default disjunct this replaces.
pub fn dprod_symbol(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
) -> Option<(FnSym, Thm)> {
    if b.arity() != 1 || img.arity() != 1 {
        return None
    }
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, fs_t) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let psi = is_section(env, ap, b, &ta, &tf);
    debug_assert_eq!(l, Formula::and(mem_fs, psi.clone()), "dprod: condition shape drift");

    let existence = crate::funcs::separation_full(env, f, &psi, &fs_t, &ap.empty_ax)?;
    let sv = env.fresh_var();
    debug_assert_eq!(
        *existence.concl(),
        Formula::exists(
            sv,
            Formula::forall(f, Formula::iff(Formula::mem(tf, Term::var(sv)), l.clone()))
        ),
        "dprod: Separation has an unexpected shape"
    );

    crate::define_by_membership(env, &[av], &existence, f, &l)
}

/// `⊢ ∀A ∀f. (f ∈ dprod(A) ↔ L(f))` — the members of the dependent product are
/// the sections, **unconditionally**.
///
/// This used to be conditional on `∃g. L(g)`, that being the hypothesis under
/// which [`dprod_symbol`]'s default disjunct was dead — and, unlike the
/// function space, no canonical section was available to discharge it. There is
/// no default any more, so the statement is exactly the defining axiom, and
/// what this function adds is the *check*: it rebuilds `L(f)` from
/// [`is_section`] and the function space independently and refuses unless
/// `dp_def` characterises `dprod(A)` by precisely that.
pub fn dprod_members(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    dp: FnSym,
    dp_def: &Thm,
) -> Option<Thm> {
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, _) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let dp_t = Term::apply(dp, vec![ta]);
    let expected = Formula::forall(
        av,
        Formula::forall(f, Formula::iff(Formula::mem(tf, dp_t), l)),
    );
    if *dp_def.concl() != expected {
        return None
    }
    Some(dp_def.clone())
}

/// `⊢ ∀A. dprod(A) ⊆ fs(A, ⋃img(A))`.
///
/// A member of `dprod(A)` satisfies `L`, whose left conjunct is membership in
/// the function space. (This was already unconditional when `dprod` carried a
/// default disjunct — the default was chosen to be the function space itself
/// precisely so that it would be. Now there is only one case.)
pub fn dprod_subset_funspace(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    dp: FnSym,
    dp_def: &Thm,
) -> Option<Thm> {
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, fs_t) = dprod_cond(env, ap, fsp, img, b, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let psi = is_section(env, ap, b, &ta, &tf);

    let l_mem = and_left(mem_fs.clone(), psi);
    debug_assert_eq!(*l_mem.concl(), Formula::imp(l.clone(), mem_fs), "dprod_subset: shape drift");

    let dp_at_f = inst_all(dp_def, &[ta.clone(), tf.clone()])?;
    let dp_t = Term::apply(dp, vec![ta.clone()]);
    debug_assert_eq!(
        *dp_at_f.concl(),
        Formula::iff(Formula::mem(tf, dp_t.clone()), l),
        "dprod's defining axiom has an unexpected shape"
    );
    let out = Thm::gen(f, &syl(&iff_mp(&dp_at_f)?, &l_mem)?);
    debug_assert_eq!(
        *out.concl(),
        kernel::thm::subset(env, dp_t, fs_t),
        "dprod_subset_funspace: unexpected shape"
    );
    Some(gen_all(&[av], &out))
}
