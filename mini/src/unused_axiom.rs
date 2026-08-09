//! **A non-standard axiom nothing in the file refers to is ignored**, and the
//! file stays in scope.
//!
//! # Interface
//!
//! ```text
//! unused_axiom::classify(&[Declaration]) -> Classified { used, unused }
//! unused_axiom::referenced(&[Declaration]) -> HashSet<Name>
//! ```
//!
//! [`crate::run::check_file_with`] is the one caller. It declines the file on
//! `used.first()` — exactly the decline it has always issued — and drops
//! `unused` from the declarations the interpretation pass walks, recording them
//! in [`crate::ledger::Ledger::ignored_axioms`].
//!
//! # Why an unused one may be ignored, and why that is a narrowing
//!
//! `mini::convert::is_standard_axiom` draws the line this narrows: Lean's own
//! three axioms are validated by the set-theoretic model and are therefore
//! `derived/` obligations, while a **user-declared** axiom's inhabitation is
//! not derivable in principle. Mini takes such a file out of scope because a
//! run that stops at the first missing derivation would stop there for ever.
//!
//! The owner's decision, and it is the whole of the design principle:
//!
//! > **We cannot generate evidence for it, and nothing depends on it, so there
//! > is nothing to be evidence *for*.**
//!
//! The obligation an axiom creates is `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` at a
//! `(declaration, σ)` pair, and every *consequence* of that obligation reaches
//! the ledger through a **reference** to `c` — a constant occurrence in some
//! other declaration's type or value. An axiom no declaration refers to is
//! therefore a pure signature extension that no theorem in the file rests on:
//! dropping the pair drops nothing else, and the evidence mini does produce for
//! the rest of the file is unchanged, statement for statement.
//!
//! So this is a narrowing of the original rule and not a reversal. The rule was
//! *"a file whose theorems may rest on an underivable inhabitation is out of
//! scope"*; the rule is now *"a file whose theorems **do** rest on one is out of
//! scope"*. A **used** non-standard axiom declines exactly as before, with the
//! same reason string and the same exit 2. Nothing that was in scope leaves it,
//! and nothing that enters it brings an obligation with it.
//!
//! The ignored declaration is **not silent**: it is counted and named on the
//! verdict line and in the ledger row, so a reader can see that the file
//! contains something no evidence exists for. `MINI-HANDOFF` §64's lesson —
//! *a declined declaration with no scheduled pair is invisible* — is what that
//! is for.
//!
//! # What counts as a reference
//!
//! [`referenced`] collects, over **every declaration in the file**:
//!
//! | declaration | expressions walked |
//! |---|---|
//! | [`Declaration::Axiom`] | its type — an axiom's statement may name another axiom |
//! | [`Declaration::Def`] | its type **and** its value (`def`, `theorem`, `opaque` alike) |
//! | [`Declaration::Inductive`] | the type former's type, and **every constructor's** type |
//! | [`Declaration::Mutual`] | the same, for every member of the block |
//! | [`Declaration::Quot`] | nothing — see below |
//!
//! and within an expression it collects
//!
//! * every `Expr::Const`'s name, and
//! * every `Expr::Proj`'s `ind` name.
//!
//! The second is not reachable for an *axiom* — a projection's head is always an
//! inductive — but it is a genuine constant reference, and `crate::expr::has_const`
//! deliberately does **not** descend into it, so a walk written by analogy with
//! that function would have a hole in it. Collecting it costs nothing and means
//! the answer here does not depend on an argument about what `ind` can be.
//!
//! **Levels carry no constant**, so a `Expr::Const`'s level arguments are not
//! walked; `Expr::Sort`'s level likewise.
//!
//! ## The three populations that are *not* walked, and why none can hide one
//!
//! * **`Declaration::Quot`.** Its four constants' types are built by
//!   `crate::kernel`, not read from the file, and they mention `Quot`, `Eq` and
//!   nothing else. No file-declared name can occur in them.
//! * **Recursors.** Mini *generates* every recursor it checks, from the
//!   inductive's own `(ty, ctors)` — `crate::convert`'s header: `parseRecInfo`
//!   is a stub, and the export's recursors are dropped. So a recursor's type
//!   and every rule right-hand side are functions of expressions this walk
//!   already covers, and a constant occurring **only** in the export's recursor
//!   is referenced by nothing mini checks, interprets or takes evidence from.
//! * **`crate::mutual_aux::expand`'s output and `crate::nested_splice`'s
//!   tables.** Both are computed from the declarations in this list, after this
//!   walk; the model an `--nested` run reads is spliced into the export by
//!   `crate::modelgen` *before* parsing, so it is in the list too.
//!
//! ## One pass, not a fixed point
//!
//! An axiom is used if **any** declaration in the file refers to it, including
//! a declaration nothing else refers to, and including another non-standard
//! axiom that is itself unused. Iterating — dropping the unused ones and asking
//! again — would classify more axioms as unused and is deliberately not done:
//! one pass is the conservative side of the only question that matters, and the
//! unsound direction is calling a used axiom unused.
//!
//! A declaration's own expressions are walked like any other's, so an axiom
//! whose type named itself would be *used*. That cannot arise in a well-founded
//! export; excluding self would be the same answer with an extra case.

use std::collections::HashSet;

use crate::env::Declaration;
use crate::expr::{Expr, Name, E};

/// The file's non-standard axioms, in file order, split by [`referenced`].
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Classified {
    /// Something in the file refers to these. The file is out of scope, and
    /// `used[0]` is the name the decline reports.
    pub used: Vec<Name>,
    /// Nothing in the file refers to these. Ignored: not translated, no pair
    /// scheduled, and not a reason to decline.
    pub unused: Vec<Name>,
}

/// Every constant name any declaration in the file refers to.
///
/// The walk is iterative and memoised on `E`, which is a pointer into the
/// hash-consed arena, so it costs one visit per *distinct* node over the whole
/// file rather than one per occurrence.
pub fn referenced(decls: &[Declaration]) -> HashSet<Name> {
    let mut out: HashSet<Name> = HashSet::new();
    let mut seen: HashSet<E> = HashSet::new();
    let mut stack: Vec<E> = Vec::new();
    for d in decls {
        match d {
            Declaration::Axiom { ty, .. } => stack.push(*ty),
            Declaration::Def { ty, value, .. } => stack.extend([*ty, *value]),
            // The kernel builds this one's constants; nothing is read from the
            // file. See the header.
            Declaration::Quot => {}
            Declaration::Inductive { ty, ctors, .. } => {
                stack.push(*ty);
                stack.extend(ctors.iter().map(|(_, c)| *c));
            }
            Declaration::Mutual { types, .. } => {
                for t in types {
                    stack.push(t.ty);
                    stack.extend(t.ctors.iter().map(|(_, c)| *c));
                }
            }
        }
    }
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue
        }
        match e.view() {
            Expr::Const(n, _) => {
                out.insert(n);
            }
            Expr::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            Expr::Lam { ty, body } | Expr::Forall { ty, body } => {
                stack.push(ty);
                stack.push(body);
            }
            Expr::Let { ty, val, body } => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            // **`ind` is collected**, unlike in `crate::expr::has_const`.
            Expr::Proj { ind, s, .. } => {
                out.insert(ind);
                stack.push(s);
            }
            Expr::BVar(..) | Expr::Sort(..) | Expr::NatLit(..) | Expr::StrLit(..) => {}
        }
    }
    out
}

/// Split the file's non-standard axioms into the used and the unused.
///
/// `nonstandard` is the predicate `crate::convert::is_standard_axiom` negates,
/// applied to a [`Declaration::Axiom`]'s name. Passing it in rather than
/// calling it keeps this module free of the export format.
pub fn classify(decls: &[Declaration], nonstandard: impl Fn(&Name) -> bool) -> Classified {
    let refs = referenced(decls);
    let mut c = Classified::default();
    for d in decls {
        let Declaration::Axiom { name, .. } = d else { continue };
        if !nonstandard(name) {
            continue
        }
        if refs.contains(name) { c.used.push(*name) } else { c.unused.push(*name) }
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{DefKind, IndType};
    use crate::expr;
    use std::rc::Rc;

    fn ax(n: &str, ty: E) -> Declaration {
        Declaration::Axiom { name: Name::simple(n), lparams: Vec::new(), ty }
    }

    fn prop() -> E { expr::sort(expr::Level::zero()) }

    fn cst(n: &str) -> E { expr::konst(Name::simple(n), Rc::from([])) }

    /// **Every reference kind the header enumerates is one this walk sees**, and
    /// each is reachable through **exactly one** arm.
    ///
    /// One axiom per kind, and the assertion is on the whole `unused` set, so
    /// dropping any arm moves exactly one name into it and the failure names
    /// the arm. That one-to-one property is what a first draft of this test did
    /// not have: it put the def's reference in `lam(cst("inDefType"), …)`, whose
    /// binder type is the def's type again, so a walk that skipped
    /// `Declaration::Def`'s `ty` still found the constant in its `value` and
    /// the mutation survived. Every use below occurs in one place only, and the
    /// `let` is spelled out for the same reason — its three sub-expressions are
    /// three arms, and only the body is reachable another way.
    #[test]
    fn every_reference_kind_is_a_use() {
        let decls = vec![
            ax("inAxiomType", prop()),
            ax("inDefType", prop()),
            ax("inDefValue", prop()),
            ax("inIndType", prop()),
            ax("inCtorType", prop()),
            ax("inMutualType", prop()),
            ax("inMutualCtor", prop()),
            ax("inProjHead", prop()),
            ax("inLetType", prop()),
            ax("inLetValue", prop()),
            ax("inLetBody", prop()),
            ax("inAppFun", prop()),
            ax("inAppArg", prop()),
            ax("inLamBinder", prop()),
            ax("inLamBody", prop()),
            ax("nowhere", prop()),
            // an axiom's statement naming another axiom
            ax("user", expr::forall(cst("inAxiomType"), prop())),
            // The type's reference and the value's are **different** names, so
            // the two arms are independently observable.
            Declaration::Def {
                name: Name::simple("d"),
                lparams: Vec::new(),
                ty: cst("inDefType"),
                value: cst("inDefValue"),
                kind: DefKind::Def,
            },
            Declaration::Inductive {
                name: Name::simple("I"),
                lparams: Vec::new(),
                num_params: 0,
                ty: expr::forall(cst("inIndType"), prop()),
                ctors: vec![(Name::simple("I.mk"), expr::forall(cst("inCtorType"), cst("I")))],
            },
            Declaration::Mutual {
                lparams: Vec::new(),
                num_params: 0,
                types: vec![IndType {
                    name: Name::simple("M"),
                    ty: expr::forall(cst("inMutualType"), prop()),
                    ctors: vec![(
                        Name::simple("M.mk"),
                        expr::forall(cst("inMutualCtor"), cst("M")),
                    )],
                }],
            },
            Declaration::Def {
                name: Name::simple("p"),
                lparams: Vec::new(),
                ty: prop(),
                value: expr::proj(Name::simple("inProjHead"), 0, expr::bvar(0)),
                kind: DefKind::Def,
            },
            // The expression arms, one name each: `let`'s three,
            // `app`'s two, `lam`'s two. (`forall`'s two are the same arm as
            // `lam`'s, and `I`/`M` above already run through it.)
            Declaration::Def {
                name: Name::simple("e"),
                lparams: Vec::new(),
                ty: prop(),
                value: expr::let_(
                    cst("inLetType"),
                    cst("inLetValue"),
                    expr::app(
                        cst("inLetBody"),
                        expr::app(
                            expr::app(cst("inAppFun"), cst("inAppArg")),
                            expr::lam(cst("inLamBinder"), cst("inLamBody")),
                        ),
                    ),
                ),
                kind: DefKind::Def,
            },
        ];
        let c = classify(&decls, |_| true);
        let unused: Vec<String> = c.unused.iter().map(|n| n.to_string()).collect();
        // `nowhere` by design, and `user` because nothing refers to *it* — an
        // axiom that names another is a use of the other and not of itself,
        // which is the "one pass, not a fixed point" reading in the header.
        // Every other name here must be in `used`, and dropping any arm of the
        // walk moves exactly one of them into this list.
        assert_eq!(
            unused,
            vec!["nowhere".to_string(), "user".to_string()],
            "used: {:?}",
            c.used
        );
    }

    /// `Quot` carries no expression and must not panic the walk.
    #[test]
    fn quot_contributes_nothing_and_is_not_an_axiom() {
        let decls = vec![Declaration::Quot, ax("lonely", prop())];
        let c = classify(&decls, |_| true);
        assert!(c.used.is_empty());
        assert_eq!(c.unused.len(), 1);
    }

    /// The predicate is what decides membership: a standard axiom is in
    /// neither list, used or not.
    #[test]
    fn a_standard_axiom_is_in_neither_list() {
        let decls = vec![ax("propext", prop()), ax("mine", prop())];
        let c = classify(&decls, |n| n.to_string() != "propext");
        assert!(c.used.is_empty());
        assert_eq!(c.unused.iter().map(|n| n.to_string()).collect::<Vec<_>>(), vec!["mine"]);
    }

    /// **One pass, not a fixed point.** `b` is referred to only by `a`, which
    /// is itself unused; `b` is nevertheless *used*.
    #[test]
    fn an_unused_axiom_still_uses_what_it_names() {
        let decls = vec![ax("b", prop()), ax("a", expr::forall(cst("b"), prop()))];
        let c = classify(&decls, |_| true);
        assert_eq!(c.used.iter().map(|n| n.to_string()).collect::<Vec<_>>(), vec!["b"]);
        assert_eq!(c.unused.iter().map(|n| n.to_string()).collect::<Vec<_>>(), vec!["a"]);
    }

    /// File order, both lists, and three axioms rather than two — the ordering
    /// the decline reads off `used[0]` is not pinned by a pair.
    #[test]
    fn both_lists_are_in_file_order() {
        let decls = vec![
            ax("one", prop()),
            ax("two", prop()),
            ax("three", prop()),
            Declaration::Def {
                name: Name::simple("d"),
                lparams: Vec::new(),
                ty: prop(),
                value: expr::app(cst("three"), cst("one")),
                kind: DefKind::Def,
            },
        ];
        let c = classify(&decls, |_| true);
        assert_eq!(
            c.used.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
            vec!["one", "three"]
        );
        assert_eq!(c.unused.iter().map(|n| n.to_string()).collect::<Vec<_>>(), vec!["two"]);
    }
}
