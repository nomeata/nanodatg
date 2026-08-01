//! The dependent product `dprod(q⃗,A) = Π(x:A). b(q⃗,x)` over a fibre family
//! carrying a **parameter prefix**, as one Separation on a function space.
//!
//! # Interface
//!
//! For a fibre symbol `b` of arity `k+1`, writing `img(q⃗,A) = { b(q⃗,x) : x ∈ A }`
//! for the fibre image, `fs` for [`crate::funspace`]'s function space and
//!
//! ```text
//! L(f)  :=  f ∈ fs(A, ⋃img(q⃗,A))  ∧  ∀x. (x ∈ A → app(f,x) ∈ b(q⃗,x))
//! ```
//!
//! for the defining condition — its right conjunct being [`section_n`] — the
//! exports are
//!
//! ```text
//! ⊢ ∀q⃗ ∀A ∀w. (w ∈ img(q⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(q⃗,x)))   [image_symbol_n]
//! ⊢ ∀q⃗ ∀A ∀f. (f ∈ dprod(q⃗,A) ↔ L(f))    [dprod_symbol_n, checked by dprod_members_n]
//! ⊢ ∀q⃗ ∀A. dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))               [dprod_subset_funspace_n]
//! ```
//!
//! [`DProdN::new`] introduces both symbols and proves all of it in one call, and
//! is the only entry point a caller needs; the free functions are exposed for
//! the tests that check the pieces separately. **Nothing here is an axiom** —
//! `img` is one Replacement and `dprod` is one Separation.
//!
//! # Why the prefix, and why a second copy of [`super::dprod`]
//!
//! `⟦Π(x:A). B x⟧`'s fibre is a symbol chosen by the *shape of the body*, and a
//! body that mentions the ambient context — a `Π` under a `λ`, under a `let`, in
//! a declaration with parameters — decomposes into a skeleton with holes plus
//! the terms filling them. The fibre symbol then has arity `k+1`, one argument
//! per hole and one for the binder. `checker`'s skeleton machinery produces
//! `k > 0` for all but a handful of sites (`tg.rs`: a dependent `Π` whose body
//! mentions only its own binder arises **11 times** on `init-prelude`), so the
//! unary [`super::dprod`] is the rare case and this is the common one.
//!
//! A symbol's arity is fixed, and there is no way inside the object language to
//! specialise an arity-`k+1` symbol to an arity-`1` one, so [`super::dprod`]
//! cannot be *instantiated* at a prefixed fibre — it has to be re-run with the
//! prefix threaded through the argument lists. Nothing else changes: no step of
//! the argument ever takes the fibre term apart. **At `k = 0` this is
//! [`super::dprod`] on the nose** — same symbols, same statements — and
//! `derived/tests/dprod_n.rs` pins that so the two cannot drift.
//!
//! These are the same constructions `checker`'s private `image_symbol_n`,
//! `section_n` and `dprod_symbol_n` perform; they are stated here so that the
//! `Π` typing rule that consumes them ([`super::dprod_universe_n`]) can be
//! derived, tested and *used* on the library side rather than only inside the
//! checker.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::funcs::Apply;
use crate::funspace::Funspace;
use crate::{and_left, gen_all, iff_mp, inst_all, syl};

/// `f(q⃗, arg)`.
pub(super) fn sym_at(f: FnSym, prefix: &[Term], arg: Term) -> Term {
    let mut v = prefix.to_vec();
    v.push(arg);
    Term::apply(f, v)
}

/// The instantiation list `q⃗, a, b`.
pub(super) fn inst_at(prefix: &[Term], a: &Term, b: &Term) -> Vec<Term> {
    let mut v = prefix.to_vec();
    v.push(a.clone());
    v.push(b.clone());
    v
}

/// The Replacement image `img(q⃗,A) = { b(q⃗,x) : x ∈ A }`, with
/// `⊢ ∀q⃗ ∀A ∀w. (w ∈ img(q⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(q⃗,x)))`.
///
/// Replacement at its cheapest, exactly as [`super::image_symbol`]: the relation
/// is `w = b(q⃗,x)`, so the `∃!` premise is [`crate::exists_unique_eq`] and costs
/// nothing. `b` must have arity at least 1.
pub fn image_symbol_n(env: &mut Env, b: FnSym) -> Option<(FnSym, Thm)> {
    let k = (b.arity() as usize).checked_sub(1)?;
    let qs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, x) = (env.fresh_var(), env.fresh_var());
    let (ta, tx) = (Term::var(av), Term::var(x));
    let bx = sym_at(b, &qts, tx.clone());

    let (w, phi, exu) = crate::exists_unique_eq(env, &[], &bx);
    let repl = Thm::ax_replacement(env, x, w, phi.clone())?;
    let repl_a = inst_all(&repl, std::slice::from_ref(&ta))?;
    let premise = Thm::gen(x, &crate::a1i(&exu, Formula::mem(tx.clone(), ta.clone())));
    let img = Thm::mp(&repl_a, &premise)?;

    let cond = Formula::exists(x, Formula::and(Formula::mem(tx, ta), phi));
    let mut params = qs;
    params.push(av);
    crate::define_by_membership(env, &params, &img, w, &cond)
}

/// `∀x. (x ∈ A → app(f,x) ∈ b(q⃗,x))` — `f` is a section of the fibration.
pub fn section_n(env: &mut Env, ap: &Apply, b: FnSym, prefix: &[Term], a: &Term, f: &Term) -> Formula {
    let x = env.fresh_var();
    let tx = Term::var(x);
    Formula::forall(
        x,
        Formula::imp(
            Formula::mem(tx.clone(), a.clone()),
            Formula::mem(ap.apply(f.clone(), tx.clone()), sym_at(b, prefix, tx)),
        ),
    )
}

/// The base set `⋃ img(q⃗,A)` — a superset of every fibre `b(q⃗,x)` for `x ∈ A`.
pub(super) fn base_of_n(ap: &Apply, img: FnSym, prefix: &[Term], a: &Term) -> Term {
    ap.sets.union_of(sym_at(img, prefix, a.clone()))
}

/// The apparatus one prefixed dependent product is built over: the ordered
/// pair and `app`, the function space, and the two symbols `img`/`b` that the
/// defining condition mentions.
///
/// Grouped rather than passed loose because they are not independent — `fsp`
/// must be the function space over `ap.sets` and `img` the Replacement image of
/// `b`, or the terms do not compose — and because every function below wants
/// exactly this four.
struct Parts<'a> {
    ap: &'a Apply,
    fsp: &'a Funspace,
    img: FnSym,
    b: FnSym,
}

impl Parts<'_> {
    /// The prefix length `k`, or `None` if the symbols' arities disagree.
    fn arity(&self) -> Option<usize> {
        let k = (self.b.arity() as usize).checked_sub(1)?;
        (self.img.arity() as usize == k + 1).then_some(k)
    }
}

/// The membership condition defined: `L(f) := f ∈ fs(A,⋃img(q⃗,A)) ∧ section(f)`,
/// together with the function space term it is carved out of.
fn dprod_cond_n(
    env: &mut Env,
    p: &Parts<'_>,
    prefix: &[Term],
    a: &Term,
    f: FreeVar,
) -> (Formula, Term) {
    let tf = Term::var(f);
    let fs_t = p.fsp.of(a.clone(), base_of_n(p.ap, p.img, prefix, a));
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    (Formula::and(mem_fs, section_n(env, p.ap, p.b, prefix, a, &tf)), fs_t)
}

/// Introduce `dprod(q⃗,A) = Π(x:A). b(q⃗,x)`, with
/// `⊢ ∀q⃗ ∀A ∀f. (f ∈ dprod(q⃗,A) ↔ L(f))`.
///
/// One call to [`crate::funcs::separation_full`] and nothing else, exactly as in
/// [`super::dprod_symbol`]: the condition it carves by *is* `L(f)` on the nose.
/// Separation is total, so there is no inhabitation antecedent and no default
/// disjunct — see [`super::dprod`]'s header for the construction that removed.
pub fn dprod_symbol_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
) -> Option<(FnSym, Thm)> {
    let parts = Parts { ap, fsp, img, b };
    let k = parts.arity()?;
    let qs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, fs_t) = dprod_cond_n(env, &parts, &qts, &ta, f);
    let psi = section_n(env, ap, b, &qts, &ta, &tf);
    debug_assert_eq!(
        l,
        Formula::and(Formula::mem(tf.clone(), fs_t.clone()), psi.clone()),
        "dprod_n: condition shape drift"
    );

    let existence = crate::funcs::separation_full(env, f, &psi, &fs_t, &ap.empty_ax)?;
    let sv = env.fresh_var();
    debug_assert_eq!(
        *existence.concl(),
        Formula::exists(
            sv,
            Formula::forall(f, Formula::iff(Formula::mem(tf, Term::var(sv)), l.clone()))
        ),
        "dprod_n: Separation has an unexpected shape"
    );

    let mut params = qs;
    params.push(av);
    crate::define_by_membership(env, &params, &existence, f, &l)
}

/// `⊢ ∀q⃗ ∀A ∀f. (f ∈ dprod(q⃗,A) ↔ L(f))` — the members of the dependent product
/// are the sections, **unconditionally**.
///
/// What this adds over the defining axiom is the *check*: `L(f)` is rebuilt from
/// [`section_n`] and the function space independently and `dp_def` is refused
/// unless it characterises `dprod(q⃗,A)` by precisely that. That is the same
/// discipline `checker`'s `lam_in_dprod_n` applies to the stack it is handed,
/// and it is what makes the symbols-plus-axioms input of
/// [`super::dprod_universe_n`] safe.
pub fn dprod_members_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    dp: FnSym,
    dp_def: &Thm,
) -> Option<Thm> {
    let parts = Parts { ap, fsp, img, b };
    let k = parts.arity()?;
    if dp.arity() as usize != k + 1 {
        return None
    }
    let qs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, _) = dprod_cond_n(env, &parts, &qts, &ta, f);
    let dp_t = sym_at(dp, &qts, ta);
    let body = Formula::forall(f, Formula::iff(Formula::mem(tf, dp_t), l));
    let mut all = qs;
    all.push(av);
    if *dp_def.concl() != quantify(&all, &body) {
        return None
    }
    Some(dp_def.clone())
}

/// `∀q⃗ ∀A. φ`, the prefix generalisation as a *formula*.
fn quantify(xs: &[FreeVar], phi: &Formula) -> Formula {
    xs.iter().rev().fold(phi.clone(), |acc, x| Formula::forall(*x, acc))
}

/// `⊢ ∀q⃗ ∀A. dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))`.
///
/// A member of `dprod(q⃗,A)` satisfies `L`, whose left conjunct is membership in
/// the function space. Unconditional, and the ingredient
/// [`super::dprod_universe_n::dprod_in_universe_of_n`] needs in order to carry
/// the dependent product into a universe by `C₂` alone.
pub fn dprod_subset_funspace_n(
    env: &mut Env,
    ap: &Apply,
    fsp: &Funspace,
    img: FnSym,
    b: FnSym,
    dp: FnSym,
    dp_def: &Thm,
) -> Option<Thm> {
    let parts = Parts { ap, fsp, img, b };
    let k = parts.arity()?;
    if dp.arity() as usize != k + 1 {
        return None
    }
    let qs: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
    let qts: Vec<Term> = qs.iter().map(|q| Term::var(*q)).collect();
    let (av, f) = (env.fresh_var(), env.fresh_var());
    let (ta, tf) = (Term::var(av), Term::var(f));

    let (l, fs_t) = dprod_cond_n(env, &parts, &qts, &ta, f);
    let mem_fs = Formula::mem(tf.clone(), fs_t.clone());
    let psi = section_n(env, ap, b, &qts, &ta, &tf);

    let l_mem = and_left(mem_fs.clone(), psi);
    debug_assert_eq!(*l_mem.concl(), Formula::imp(l.clone(), mem_fs), "dprod_subset_n: shape drift");

    let dp_at_f = inst_all(dp_def, &inst_at(&qts, &ta, &tf))?;
    let dp_t = sym_at(dp, &qts, ta.clone());
    if *dp_at_f.concl() != Formula::iff(Formula::mem(tf, dp_t.clone()), l) {
        return None
    }
    let out = Thm::gen(f, &syl(&iff_mp(&dp_at_f)?, &l_mem)?);
    if *out.concl() != kernel::thm::subset(env, dp_t, fs_t) {
        return None
    }
    let mut all = qs;
    all.push(av);
    Some(gen_all(&all, &out))
}

/// The dependent product `dprod(q⃗,A) = Π(x:A). b(q⃗,x)` for a fibre symbol `b`
/// of arity `k+1`, together with everything proved about it.
///
/// The n-ary [`super::DProd`], with which it agrees field for field at `k = 0`.
pub struct DProdN {
    /// The length of the parameter prefix, i.e. `b.arity() - 1`.
    pub k: usize,
    /// The fibre family symbol handed in.
    pub b: FnSym,
    /// `img(q⃗,A) = { b(q⃗,x) : x ∈ A }`.
    pub img: FnSym,
    /// `⊢ ∀q⃗ ∀A ∀w. (w ∈ img(q⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(q⃗,x)))`.
    pub img_ax: Thm,
    /// The symbol itself.
    pub dprod: FnSym,
    /// `⊢ ∀q⃗ ∀A ∀f. (f ∈ dprod(q⃗,A) ↔ L(f))` — the defining axiom.
    pub dprod_def: Thm,
    /// The same statement, with [`dprod_members_n`] having rebuilt `L`
    /// independently and checked it against the defining axiom.
    pub dprod_ax: Thm,
    /// `⊢ ∀q⃗ ∀A. dprod(q⃗,A) ⊆ fs(A, ⋃img(q⃗,A))`.
    pub dprod_sub: Thm,
}

impl DProdN {
    /// Introduce `img` and `dprod` and prove every lemma about them.
    ///
    /// `fsp` must be the function space built over `ap.sets`, or the terms will
    /// not compose: every symbol here is a definitional extension, so a second
    /// `Sets` would give a second, unrelated pairing operation.
    pub fn new(env: &mut Env, ap: &Apply, fsp: &Funspace, b: FnSym) -> Option<DProdN> {
        let k = (b.arity() as usize).checked_sub(1)?;
        let (img, img_ax) = image_symbol_n(env, b)?;
        let (dprod, dprod_def) = dprod_symbol_n(env, ap, fsp, img, b)?;
        let dprod_ax = dprod_members_n(env, ap, fsp, img, b, dprod, &dprod_def)?;
        let dprod_sub = dprod_subset_funspace_n(env, ap, fsp, img, b, dprod, &dprod_def)?;
        Some(DProdN { k, b, img, img_ax, dprod, dprod_def, dprod_ax, dprod_sub })
    }

    /// The term `dprod(q⃗,A)`.
    pub fn of(&self, prefix: &[Term], a: Term) -> Term { sym_at(self.dprod, prefix, a) }

    /// The term `img(q⃗,A)`.
    pub fn img_of(&self, prefix: &[Term], a: Term) -> Term { sym_at(self.img, prefix, a) }
}
