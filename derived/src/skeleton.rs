//! The **skeleton decomposition**: splitting a term into the part that mentions
//! a distinguished variable and the maximal subterms that do not.
//!
//! # Interface
//!
//! ```text
//! type Parts = HashMap<Term, (FnSym, Vec<Term>)>
//!
//! record(parts, f, args)                     -> Term    // Term::apply, remembered
//! skeleton(parts, x_canon, hole_var, t, v, holes) -> Option<Term>
//! ```
//!
//! [`record`] builds `f(args)` and remembers its applicative structure in
//! `parts`; every term the caller intends to decompose later must be built
//! through it.
//!
//! [`skeleton`] rewrites `t` into a **skeleton**: every occurrence of `v` is
//! replaced by the canonical binder slot `x_canon`, and every maximal subterm
//! *not* mentioning `v` is pushed onto `holes` and replaced by a canonical hole
//! variable, `hole_var(i)` for the `i`-th. The result is `None` if some subterm
//! that mentions `v` was never passed through [`record`] — the caller has
//! leaked a variable, and that should surface as a failure rather than be
//! papered over. Nodes built on the way are themselves recorded, so the
//! skeleton can be walked again to rebuild an instance of it.
//!
//! `hole_var` is a callback rather than an [`kernel::Env`] because the hole
//! variables are *canonical*: two calls for the same index must return the same
//! variable, across every term the caller ever decomposes, or two occurrences
//! of one body shape would produce two unequal skeletons.
//!
//! **Nothing here is a theorem and nothing here is trusted.** [`Parts`] is a
//! *hint* — the kernel does not expose [`Term`]'s constructors for reading, so
//! the applicative structure has to be recorded on the way in — and a wrong
//! hint yields a skeleton whose reassembly fails to match, never a bad proof.
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

use std::collections::HashMap;

use kernel::{FnSym, FreeVar, Term};

/// The applicative structure of the terms a caller has built.
///
/// The kernel does not expose [`Term`]'s constructors for reading, so a term
/// that will have to be taken apart later has to be *recorded* when it is
/// built. See [`record`].
pub type Parts = HashMap<Term, (FnSym, Vec<Term>)>;

/// `f(args)`, with its applicative structure remembered in `parts`.
///
/// The first recording of a term wins: the same term built twice has the same
/// structure, so a later insertion could only be redundant.
pub fn record(parts: &mut Parts, f: FnSym, args: Vec<Term>) -> Term {
    let t = Term::apply(f, args.clone());
    parts.entry(t.clone()).or_insert((f, args));
    t
}

/// Split `t` into the part that mentions `v` and the maximal `v`-free
/// subterms, which are pushed onto `holes` and replaced by canonical hole
/// variables. `v` itself becomes the canonical bound-variable slot `x_canon`.
///
/// Returns `None` if a term mentioning `v` was not built by [`record`], which
/// would mean the caller had leaked a variable — a bug, and one that should
/// surface as a failure rather than be papered over.
pub fn skeleton(
    parts: &mut Parts,
    x_canon: FreeVar,
    hole_var: &mut dyn FnMut(usize) -> FreeVar,
    t: &Term,
    v: FreeVar,
    holes: &mut Vec<Term>,
) -> Option<Term> {
    if !t.occurs_free(v) {
        let h = hole_var(holes.len());
        holes.push(t.clone());
        return Some(Term::var(h))
    }
    if *t == Term::var(v) {
        return Some(Term::var(x_canon))
    }
    let (f, args) = parts.get(t)?.clone();
    let mut out = Vec::with_capacity(args.len());
    for a in &args {
        out.push(skeleton(parts, x_canon, hole_var, a, v, holes)?);
    }
    // Through `record`, so that the skeleton's own structure is recorded too: a
    // caller walks it to rebuild an instance of the skeleton at a binder, and
    // the kernel does not expose a term for reading.
    Some(record(parts, f, out))
}
