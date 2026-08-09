//! The **skeleton decomposition**: splitting a term into the part that mentions
//! a distinguished variable and the maximal subterms that do not.
//!
//! # Interface
//!
//! ```text
//! skeleton(x_canon, hole_var, t, v, holes) -> Term
//! ```
//!
//! [`skeleton`] rewrites `t` into a **skeleton**: every occurrence of `v` is
//! replaced by the canonical binder slot `x_canon`, and every maximal subterm
//! *not* mentioning `v` is pushed onto `holes` and replaced by a canonical hole
//! variable, `hole_var(i)` for the `i`-th.
//!
//! It is **total**: the applicative structure it walks is read straight off the
//! term with [`Term::as_app`], so there is no term it cannot take apart, and
//! the result can be walked again to rebuild an instance of the skeleton.
//!
//! `hole_var` is a callback rather than an [`kernel::Env`] because the hole
//! variables are *canonical*: two calls for the same index must return the same
//! variable, across every term the caller ever decomposes, or two occurrences
//! of one body shape would produce two unequal skeletons.
//!
//! **Nothing here is a theorem and nothing here is trusted.** A skeleton is a
//! *term*, and a wrong one yields a reassembly that fails to match, never a bad
//! proof.
//!
//! # Why this exists
//!
//! A binder's body is an open term. Interpreting `λ y:A. b` as a function graph
//! wants the body as a *function symbol* `t`, and the obvious `t(v) := ⟦b⟧` is
//! wrong: a nested binder's body mentions the enclosing binders' variables too,
//! and a defined symbol may not contain free variables that are not among its
//! parameters — it would not be a conservative extension.
//!
//! The fix is to abstract more. `⟦b⟧` splits into the skeleton `C` and the list
//! `s⃗` of its maximal `v`-free subterms, which become extra parameters, so the
//! symbol is `t(s⃗, x)` and the graph `lam_C(s⃗, ⟦A⟧)`. That is exactly why
//! [`crate::funcs::lambda_n`], [`crate::funcs::beta_conditional_n`],
//! [`crate::ext::lam_ext_n`] and the rest of the `_n` family exist: they are
//! the unary constructions with a parameter prefix threaded through.
//!
//! The decomposition is canonical *and* stable under substitution —
//! substituting into an `sᵢ` keeps it `v`-free and leaves `C` alone — which is
//! the property beta reduction needs: the interpretation of `b[a]` really is
//! the interpretation of `b` with the abstracted positions filled in, so the
//! two sides of the beta equation line up syntactically instead of merely
//! morally.
//!
//! # The `Parts` table this replaced, and what it cost
//!
//! Until `Term::as_app` existed the kernel exposed no way to read a term's
//! applicative structure, so this module carried a `record` function and a
//! `Parts = HashMap<Term, (FnSym, Vec<Term>)>` side table: **every term the
//! caller intends to decompose later must be built through it**, and
//! `skeleton` answered `None` for anything else.
//!
//! Three things were wrong with that, all of them measured rather than argued
//! (`PRELUDE-COST.md` §3.2, §3.3):
//!
//! * **It stored what the term already held.** The value `(f, args)` is
//!   precisely the contents of the `TermData::App` node the key points at, in a
//!   second `Vec` — 246 bytes of marginal cost per entry for a copy.
//! * **It was 54 % of the live heap** of an `init-prelude` run and held 80 % of
//!   the process's live kernel `Term` nodes, growing at 0.6 entries per
//!   conversion forever, with no eviction and no scope.
//! * **Its misses were silent and wrong.** A term the *kernel* built — a
//!   substitution instance, or either endpoint of a `derived::congr` — never
//!   passed through `record`, so it was indistinguishable from a term with no
//!   structure. `mini`'s `conv::app_cong` header records six conversions lost
//!   to exactly that asymmetry, and clearing the table between declarations
//!   turned 0 gaps into 213.
//!
//! Reading the structure back out of the term is not merely cheaper than
//! remembering it; it is the operation the callers wanted all along, and it
//! cannot miss.

use kernel::{FreeVar, Term};

/// Split `t` into the part that mentions `v` and the maximal `v`-free
/// subterms, which are pushed onto `holes` and replaced by canonical hole
/// variables. `v` itself becomes the canonical bound-variable slot `x_canon`.
///
/// **Total.** The three cases are exhaustive: a term not mentioning `v` is a
/// hole, `v` itself is the slot, and anything else mentions `v` and is
/// therefore an application — a `Free` other than `v` and a `Bound` do not
/// mention `v`, so [`Term::as_app`] cannot answer `None` here.
pub fn skeleton(
    x_canon: FreeVar,
    hole_var: &mut dyn FnMut(usize) -> FreeVar,
    t: &Term,
    v: FreeVar,
    holes: &mut Vec<Term>,
) -> Term {
    if !t.occurs_free(v) {
        let h = hole_var(holes.len());
        holes.push(t.clone());
        return Term::var(h)
    }
    if *t == Term::var(v) {
        return Term::var(x_canon)
    }
    let Some((f, args)) = t.as_app() else {
        // Unreachable: see the totality note above. `Term::var(v)` is the only
        // non-application mentioning `v`, and it was handled.
        return t.clone()
    };
    let mut out = Vec::with_capacity(args.len());
    for a in args {
        out.push(skeleton(x_canon, hole_var, a, v, holes));
    }
    Term::apply(f, out)
}
