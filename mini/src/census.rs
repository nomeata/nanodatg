//! A **clause census**: how often each §6.2 interpretation clause occurs in the
//! expressions mini must interpret, per export file.
//!
//! # Interface
//!
//! ```text
//! Census::of(&[Declaration]) -> Census      // counts, by clause
//! ```
//!
//! # Why this exists rather than a guess
//!
//! Threading evidence is done one operation at a time, and which operation to
//! do next should be decided by which clause the corpus actually spends its
//! nodes on, not by which is easiest. MINI-DESIGN.md §12 orders the work
//! `infer_type`-first; this says what fraction of the work that leaves
//! blocked behind the `λ`/`Π` clauses, which are the ones needing the n-ary
//! prefix-threaded lemma family and the skeleton decomposition.
//!
//! The census walks the *converted* declarations — types and values both, and
//! the constructor types inside an inductive — at their own symbolic levels.
//! Counting at ground σ instead would multiply every count by the size of the
//! schedule without changing a single ratio, since grounding substitutes levels
//! and never changes an expression's shape.
//!
//! `Π` is split three ways because the three take entirely different
//! derivations, and the split is decidable from the declaration alone only for
//! the first: a `Π` whose *codomain* is syntactically `Sort 0` is the `Prop`
//! clause (`cond`, a conditional singleton); one whose body does not mention
//! the binder is a plain function space (`fs`); the rest need the dependent
//! product (`dprod`). The counts below therefore under-report `PiProp`, since a
//! codomain that only *reduces* to `Sort 0` is counted as dependent — which is
//! the conservative direction for sizing the work.

use crate::env::Declaration;
use crate::expr::{has_bvar, Expr, Level, E};
use std::collections::BTreeMap;

/// One §6.2 clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Clause {
    BVar,
    Sort,
    Const,
    App,
    Lam,
    /// `Π` with a syntactically `Sort 0` codomain — the conditional-singleton
    /// clause.
    PiProp,
    /// `Π` whose body does not mention the binder — a plain function space.
    PiArrow,
    /// `Π` whose body mentions the binder — a dependent product.
    PiDep,
    Let,
    Proj,
    NatLit,
    StrLit,
}

impl Clause {
    pub fn name(self) -> &'static str {
        match self {
            Clause::BVar => "bvar",
            Clause::Sort => "sort",
            Clause::Const => "const",
            Clause::App => "app",
            Clause::Lam => "lam",
            Clause::PiProp => "pi-prop",
            Clause::PiArrow => "pi-arrow",
            Clause::PiDep => "pi-dep",
            Clause::Let => "let",
            Clause::Proj => "proj",
            Clause::NatLit => "natLit",
            Clause::StrLit => "strLit",
        }
    }

    /// Whether mini can interpret this clause today. Kept beside the clause so
    /// that the two cannot drift: adding a clause to [`crate::interp`] means
    /// moving one line here, and the census immediately re-sizes the rest.
    pub fn interpreted(self) -> bool {
        matches!(self, Clause::Sort | Clause::BVar | Clause::App | Clause::Const | Clause::Let)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Census {
    pub counts: BTreeMap<Clause, u64>,
}

impl Census {
    pub fn of(decls: &[Declaration]) -> Census {
        let mut c = Census::default();
        for d in decls {
            match d {
                Declaration::Axiom { ty, .. } => c.walk(ty),
                Declaration::Def { ty, value, .. } => {
                    c.walk(ty);
                    c.walk(value);
                }
                // `Quot`'s four types are built by the kernel, not converted;
                // they are counted when the kernel adds them, not here.
                Declaration::Quot => {}
                Declaration::Inductive { ty, ctors, .. } => {
                    c.walk(ty);
                    for (_, ct) in ctors {
                        c.walk(ct);
                    }
                }
            }
        }
        c
    }

    pub fn total(&self) -> u64 { self.counts.values().sum() }

    /// Nodes mini can interpret today, and nodes it cannot.
    pub fn split(&self) -> (u64, u64) {
        let done: u64 = self.counts.iter().filter(|(k, _)| k.interpreted()).map(|(_, v)| v).sum();
        (done, self.total() - done)
    }

    pub fn merge(&mut self, other: &Census) {
        for (k, v) in &other.counts {
            *self.counts.entry(*k).or_insert(0) += v;
        }
    }

    fn bump(&mut self, k: Clause) { *self.counts.entry(k).or_insert(0) += 1; }

    fn walk(&mut self, e: &E) {
        match &**e {
            Expr::BVar(_) => self.bump(Clause::BVar),
            Expr::Sort(_) => self.bump(Clause::Sort),
            Expr::Const(..) => self.bump(Clause::Const),
            Expr::App(f, a) => {
                self.bump(Clause::App);
                self.walk(f);
                self.walk(a);
            }
            Expr::Lam { ty, body } => {
                self.bump(Clause::Lam);
                self.walk(ty);
                self.walk(body);
            }
            Expr::Forall { ty, body } => {
                let k = if matches!(&**body, Expr::Sort(Level::Zero)) {
                    Clause::PiProp
                } else if has_bvar(body, 0) {
                    Clause::PiDep
                } else {
                    Clause::PiArrow
                };
                self.bump(k);
                self.walk(ty);
                self.walk(body);
            }
            Expr::Let { ty, val, body } => {
                self.bump(Clause::Let);
                self.walk(ty);
                self.walk(val);
                self.walk(body);
            }
            Expr::Proj { s, .. } => {
                self.bump(Clause::Proj);
                self.walk(s);
            }
            Expr::NatLit(_) => self.bump(Clause::NatLit),
            Expr::StrLit(_) => self.bump(Clause::StrLit),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{app, bvar, forall, lam, sort};

    #[test]
    fn the_three_pi_clauses_are_distinguished() {
        let prop = sort(Level::Zero);
        let ty1 = sort(Level::Zero.succ());
        // `Π (_ : Type 0). Prop` — the Prop clause.
        let mut c = Census::default();
        c.walk(&forall(ty1.clone(), prop.clone()));
        assert_eq!(c.counts.get(&Clause::PiProp), Some(&1));
        // `Π (_ : Prop). Type 0` — a plain arrow.
        let mut c = Census::default();
        c.walk(&forall(prop.clone(), ty1.clone()));
        assert_eq!(c.counts.get(&Clause::PiArrow), Some(&1));
        // `Π (x : Type 0). x` — dependent.
        let mut c = Census::default();
        c.walk(&forall(ty1, bvar(0)));
        assert_eq!(c.counts.get(&Clause::PiDep), Some(&1));
    }

    #[test]
    fn split_tracks_what_interp_can_do() {
        let mut c = Census::default();
        // `λ (_ : Prop). (f a)` — one uninterpretable node, three interpretable.
        c.walk(&lam(sort(Level::Zero), app(bvar(0), bvar(0))));
        let (done, todo) = c.split();
        assert_eq!(todo, 1, "the lam is the only clause interp cannot do yet");
        assert_eq!(done, 4);
    }
}
