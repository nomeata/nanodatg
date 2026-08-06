//! **Term substitution without a symbol** — `derived::subst_term`.
//!
//! `kernel::Term` exposes no `subst`, so a term with a hole used to be spelled
//! `define_abbrev` over the hole variables and `inst_all` at the fillings. That
//! spelling is a conservative-extension obligation, a permanent signature
//! entry, and a *precondition* — the abstraction prefix must cover every free
//! variable of the body, chosen at build time with no retrofit. `subst_term`
//! has none of those and computes the same term.
//!
//! Every test here therefore has the same shape: **compute both ways and
//! compare**, rather than compare against a hand-written expected term. A
//! hand-written expectation would test my reading of the substitution and not
//! its agreement with the thing it replaces, and agreement is the claim.
//! [`substitution_is_simultaneous_and_not_a_fold`] and
//! [`a_free_variable_outside_the_prefix_is_the_whole_point`] are the two that
//! also pin a *difference*, and they say which.

use derived::{define_abbrev, inst_all, subst_term};
use kernel::{Env, FnSym, FreeVar, Term};

/// The old spelling: name the hole, then fill it. Returns `None` exactly where
/// `define_abbrev` refuses — which is the behaviour under test in
/// [`a_free_variable_outside_the_prefix_is_the_whole_point`].
fn via_abbrev(env: &mut Env, xs: &[FreeVar], body: &Term, args: &[Term]) -> Option<Term> {
    let (_, ax) = define_abbrev(env, xs, body)?;
    let inst = inst_all(&ax, args)?;
    Some(inst.concl().as_eq()?.1)
}

/// `subst_term` on the same data, with the prefix and the arguments zipped.
fn via_subst(xs: &[FreeVar], body: &Term, args: &[Term]) -> Term {
    let subs: Vec<(FreeVar, Term)> =
        xs.iter().copied().zip(args.iter().cloned()).collect();
    subst_term(body, &subs)
}

/// A scratch signature: a binary `g`, a unary `h`, a constant `c`.
fn sig(env: &mut Env) -> (FnSym, FnSym, Term) {
    let g = env.declare(2);
    let h = env.declare(1);
    let c = env.declare(0);
    (g, h, Term::apply(c, vec![]))
}

/// **The drop-in claim**, at the shape the `mini/` call sites have: a body over
/// two parameters, instantiated at two closed terms.
#[test]
fn it_agrees_with_define_abbrev_then_inst_all() {
    let mut env = Env::new();
    let (g, h, c) = sig(&mut env);
    let (x, y) = (env.fresh_var(), env.fresh_var());

    // `g(h(x), g(y, x))` — `x` twice, at two different depths, because a
    // substitution that handled only the shallow occurrence would pass on a
    // body that mentioned each variable once.
    let body = Term::apply(
        g,
        vec![
            Term::apply(h, vec![Term::var(x)]),
            Term::apply(g, vec![Term::var(y), Term::var(x)]),
        ],
    );
    let args = vec![c.clone(), Term::apply(h, vec![c])];

    let want = via_abbrev(&mut env, &[x, y], &body, &args).expect("the prefix covers the body");
    assert_eq!(via_subst(&[x, y], &body, &args), want);
}

/// **Substitution is simultaneous**, which is what makes it a drop-in and not
/// merely a convenience.
///
/// Substituting `x := y` and `y := c` at once gives `g(y, c)`: the `y`
/// introduced by the first replacement is *not* then replaced by the second,
/// because every variable is closed before any argument is opened. A fold of
/// one-variable substitutions gives `g(c, c)` instead, and would silently
/// disagree with every `define_abbrev` site it replaced.
///
/// The `assert_ne` is the half that makes this test say something: without it,
/// a `subst_term` that folded would still pass the equality if the fold and the
/// simultaneous answer happened to coincide here.
#[test]
fn substitution_is_simultaneous_and_not_a_fold() {
    let mut env = Env::new();
    let (g, _h, c) = sig(&mut env);
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let body = Term::apply(g, vec![Term::var(x), Term::var(y)]);
    let args = vec![Term::var(y), c.clone()];

    let want = via_abbrev(&mut env, &[x, y], &body, &args).expect("the prefix covers the body");
    assert_eq!(via_subst(&[x, y], &body, &args), want, "the two spellings must agree");
    assert_eq!(want, Term::apply(g, vec![Term::var(y), c.clone()]), "simultaneous, so `g(y, c)`");
    assert_ne!(
        want,
        Term::apply(g, vec![c.clone(), c]),
        "`g(c, c)` is what a fold of one-variable substitutions produces, and it is wrong"
    );
}

/// **A free variable outside the prefix**, which `define_abbrev` refuses and
/// `subst_term` does not care about.
///
/// This is the failure mode the abstraction prefix exists to create. Here it is
/// the loud one — `define_abbrev` returns `None` and the caller decides what to
/// do. The dangerous one is silent: a prefix that is wrong but still *covers*
/// the body yields a well-formed symbol and a true defining equation about the
/// wrong abstraction, and nothing anywhere refuses. `subst_term` has no prefix
/// and so has neither.
#[test]
fn a_free_variable_outside_the_prefix_is_the_whole_point() {
    let mut env = Env::new();
    let (g, _h, c) = sig(&mut env);
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let body = Term::apply(g, vec![Term::var(x), Term::var(y)]);

    assert!(
        via_abbrev(&mut env, &[x], &body, std::slice::from_ref(&c)).is_none(),
        "`define_abbrev` must refuse a body whose free variables are not among `xs`"
    );
    assert_eq!(
        subst_term(&body, &[(x, c.clone())]),
        Term::apply(g, vec![c, Term::var(y)]),
        "`y` stays free, and that is a term and not a claim"
    );
}

/// **The two degenerate prefixes**, because a fold over an empty list and a
/// variable that does not occur are the two ways to get the identity and both
/// have been written wrong before.
#[test]
fn the_empty_substitution_and_the_absent_variable_are_both_the_identity() {
    let mut env = Env::new();
    let (_g, h, c) = sig(&mut env);
    let z = env.fresh_var();
    let body = Term::apply(h, vec![c.clone()]);

    assert_eq!(subst_term(&body, &[]), body, "no variables, no change");
    assert_eq!(subst_term(&body, &[(z, c)]), body, "`z` does not occur, so no change");
}

/// **A variable substituted for itself is the identity**, and the point is that
/// it is the identity *through the close/open pair* rather than by a shortcut:
/// `subst_term` has no early exit, so this exercises the full round trip and
/// would catch an off-by-one in the depth accounting that a distinct
/// replacement could mask.
#[test]
fn substituting_a_variable_for_itself_round_trips() {
    let mut env = Env::new();
    let (g, h, _c) = sig(&mut env);
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let body = Term::apply(
        g,
        vec![Term::var(x), Term::apply(h, vec![Term::apply(g, vec![Term::var(y), Term::var(x)])])],
    );
    assert_eq!(subst_term(&body, &[(x, Term::var(x)), (y, Term::var(y))]), body);
}

/// **Nothing about the result is asserted that reflexivity did not already
/// give.** The theorem `subst_term` builds is `⊢ t[s⃗/x⃗] = t[s⃗/x⃗]`, so the
/// result can always be fed straight back to [`kernel::Thm::eq_refl`] — this
/// records that the helper's output is an ordinary term and carries no
/// provenance a caller could mistake for evidence.
#[test]
fn the_result_is_an_inert_term() {
    let mut env = Env::new();
    let (g, _h, c) = sig(&mut env);
    let x = env.fresh_var();
    let body = Term::apply(g, vec![Term::var(x), Term::var(x)]);
    let out = subst_term(&body, &[(x, c)]);
    let refl = kernel::Thm::eq_refl(out.clone());
    assert!(refl.hyps().is_empty());
    assert_eq!(refl.concl().as_eq().expect("an equation"), (out.clone(), out));
}
