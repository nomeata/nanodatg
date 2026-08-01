//! **The gap ledger**: what mini can and cannot interpret, per
//! `(declaration, σ)` on the real corpus, attributed by cause.
//!
//! # Interface
//!
//! ```text
//! Ledger::run(&[Declaration], &schedule) -> Ledger
//! ```
//!
//! # What this measures, and what it does not
//!
//! It runs the §6.2 dispatch over every declaration at every ground
//! instantiation the pre-pass scheduled, and records for each whether `⟦ty⟧`
//! and `⟦val⟧` were produced — and when they were not, the **first clause that
//! blocked**, not merely that something did. `mini/src/census.rs` counts
//! *nodes*; this counts *declarations*, which is the granularity that matters,
//! because one un-interpreted node at a declaration's root blocks all of it.
//!
//! It does **not** yet measure evidence completeness. `Typing.ev` for an
//! application needs `assert_def_eq` to return a `Conv`, and that signature
//! change is not made; until it is, a typing column would report the absence
//! of one function and nothing about the library. The residue below is
//! therefore the *interpretation's* residue, which is a real and separable
//! axis — MINI-DESIGN.md §0's two axes, with the second one honestly not yet
//! measured.
//!
//! # Nothing here searches
//!
//! Worth stating in those words, because it is the claim task #29 is built on.
//! Every constant's interpretation is read from the store by
//! `(name, ground levels)`; every `bvar`'s is read from the scope stack by
//! index; every clause is decided by `body_clause`/`term_clause`, which is
//! `is_prop`, which is inference. **No function in this path looks for a fact
//! it was not handed or cannot compute forward.** There is no fallback, no
//! retry, and no goal-directed matching anywhere in it.

use std::collections::BTreeMap;

use crate::env::{Declaration, DefKind, Environment};
use crate::ev::Gap;
use crate::expr::Name;
use crate::ground;
use crate::interp::{ConstInterp, Interp};
use crate::kernel::{Checker, Typing};

/// The interpretation and, when it is absent, the named reason.
fn split(t: crate::kernel::R<Typing>) -> (Option<kernel::Term>, Option<Gap>) {
    match t {
        Ok(t) => {
            let g = if t.tm.is_none() { t.ev.gap().cloned().or(Some(Gap::Classifier)) } else { None };
            (t.tm, g)
        }
        // Inference failed outright, which on an accepted file it should not.
        Err(_) => (None, None),
    }
}

/// One row per reason, so the residue is readable by cause.
#[derive(Debug, Default, Clone)]
pub struct Ledger {
    /// `(declaration, σ)` pairs attempted.
    pub pairs: usize,
    /// Pairs whose **type** interpreted.
    pub types_ok: usize,
    /// Pairs with a value (`def`/`theorem`/`opaque`) whose value interpreted.
    pub values_ok: usize,
    /// Pairs with a value at all.
    pub values_attempted: usize,
    /// Why an interpretation stopped, by first blocking cause.
    pub blocked: BTreeMap<String, usize>,
    /// Declarations whose *every* scheduled instantiation interpreted.
    pub fully_interpreted: usize,
    pub declarations: usize,
}

impl Ledger {
    fn note(&mut self, g: Option<&Gap>) {
        let k = match g {
            Some(Gap::StructProj(n)) => format!("proj({n})"),
            Some(Gap::NoInterpretation(n, _)) => format!("no-interp({n})"),
            Some(Gap::StrLit) => "strLit".to_string(),
            Some(Gap::SymbolicLevel) => "symbolic-level".to_string(),
            Some(Gap::Skeleton) => "skeleton".to_string(),
            Some(Gap::Classifier) => "classifier".to_string(),
            Some(Gap::DefEqUnthreaded) => "defeq-unthreaded".to_string(),
            Some(Gap::PiTypingUnthreaded) => "pi-typing-unthreaded".to_string(),
            Some(Gap::LamTypingUnthreaded) => "lam-typing-unthreaded".to_string(),
            Some(other) => format!("{other:?}"),
            None => "inference-error".to_string(),
        };
        *self.blocked.entry(k).or_insert(0) += 1;
    }

    /// Run the interpretation over the whole file.
    ///
    /// Declarations in file order, σ inner — mini-lean's order for the first
    /// and MINI-DESIGN.md §3's for the second. A constant is minted **before**
    /// its type is interpreted, because a recursive declaration's own type may
    /// mention it, and a later declaration certainly will.
    pub fn run(
        env: &Environment,
        decls: &[Declaration],
        schedule: &std::collections::HashMap<Name, Vec<Vec<u32>>>,
        ip: &mut Interp,
    ) -> Ledger {
        let mut led = Ledger::default();
        for d in decls {
            let (name, lparams, ty, val) = match d {
                Declaration::Axiom { name, lparams, ty } => (name, lparams, ty, None),
                Declaration::Def { name, lparams, ty, value, .. } => {
                    (name, lparams, ty, Some(value))
                }
                // `Quot`'s four constants are built by the kernel and have no
                // converted expressions here; the inductive path is §9 zone B
                // and is not wired, so both are counted as declarations with
                // no interpretable content rather than silently skipped.
                Declaration::Quot | Declaration::Inductive { .. } => {
                    led.declarations += 1;
                    continue
                }
            };
            led.declarations += 1;
            let sigmas: &[Vec<u32>] = schedule.get(name).map(|v| v.as_slice()).unwrap_or(&[]);
            let sigmas: Vec<Vec<u32>> =
                if sigmas.is_empty() { vec![vec![0; lparams.len()]] } else { sigmas.to_vec() };
            let mut all_ok = true;
            for sigma in &sigmas {
                led.pairs += 1;
                let ty_g = ground::subst_ground(ty, lparams, sigma);
                let val_g = val.map(|v| ground::subst_ground(v, lparams, sigma));

                let mut c = Checker::threaded(env, ip);
                // `⟦ty⟧` is `infer_type(ty).tm`: one traversal, both results,
                // and the reason for a missing one is the `Typing`'s own `ev`.
                let (ty_tm, ty_blocked) = split(c.infer_type(&ty_g));
                let (val_tm, val_blocked) = match &val_g {
                    Some(v) => split(c.infer_type(v)),
                    None => (None, None),
                };
                drop(c);

                if ty_tm.is_some() {
                    led.types_ok += 1;
                } else {
                    all_ok = false;
                    led.note(ty_blocked.as_ref());
                }
                if val_g.is_some() {
                    led.values_attempted += 1;
                    if val_tm.is_some() {
                        led.values_ok += 1;
                    } else {
                        all_ok = false;
                        led.note(val_blocked.as_ref());
                    }
                }

                // Mint `⟦c.{σ}⟧`. A transparent definition whose value
                // interpreted gets an **abbreviation**, whose defining axiom is
                // also delta reduction's certificate; everything else gets an
                // opaque symbol, which is a signature extension and asserts
                // nothing about inhabitation — hence the `Gap` on its typing.
                let key = (name.clone(), sigma.clone());
                if ip.get_const(&key).is_some() {
                    continue
                }
                let transparent = matches!(
                    d,
                    Declaration::Def { kind: DefKind::Def | DefKind::Theorem, .. }
                );
                let entry = match (transparent, val_tm) {
                    (true, Some(v)) => match ip.abbrev(&v) {
                        Some((t, ax)) => ConstInterp {
                            term: t,
                            typing: Err(Gap::Axiom(name.clone())),
                            defeq: crate::ev::Sealed::new(ax).ok(),
                        },
                        None => ConstInterp {
                            term: ip.opaque(),
                            typing: Err(Gap::Axiom(name.clone())),
                            defeq: None,
                        },
                    },
                    _ => ConstInterp {
                        term: ip.opaque(),
                        typing: Err(Gap::Axiom(name.clone())),
                        defeq: None,
                    },
                };
                ip.put_const(key, entry);
            }
            if all_ok {
                led.fully_interpreted += 1;
            }
        }
        led
    }

    /// The row format the corpus tables scrape.
    pub fn row(&self) -> String {
        let mut s = format!(
            "ledger\tdeclars={}\tpairs={}\ttypesOk={}\tvaluesOk={}/{}\tfullyInterpreted={}",
            self.declarations,
            self.pairs,
            self.types_ok,
            self.values_ok,
            self.values_attempted,
            self.fully_interpreted
        );
        for (k, v) in &self.blocked {
            s.push_str(&format!("\t{k}={v}"));
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{forall, konst, sort, Level};

    /// A file mini can interpret **completely**: an axiom and a definition
    /// over sorts and arrows only. Every pair must interpret, and the blocked
    /// map must be empty — a ledger that reported "all fine" on an empty run
    /// would prove nothing, so the counts are checked too.
    #[test]
    fn an_inductive_free_file_interprets_completely() {
        let mut env = Environment::empty();
        let prop = sort(Level::Zero);
        let a = Name::simple("A");
        crate::kernel::add(
            &mut env,
            &Declaration::Axiom { name: a.clone(), lparams: vec![], ty: prop.clone() },
        )
        .unwrap();
        let id_ty = forall(konst(a.clone(), Vec::new().into()), konst(a.clone(), Vec::new().into()));
        let id = Declaration::Def {
            name: Name::simple("id"),
            lparams: vec![],
            ty: id_ty,
            value: crate::expr::lam(konst(a.clone(), Vec::new().into()), crate::expr::bvar(0)),
            kind: DefKind::Def,
        };
        crate::kernel::add(&mut env, &id).unwrap();

        let decls = vec![
            Declaration::Axiom { name: a, lparams: vec![], ty: prop },
            id,
        ];
        let mut ip = Interp::new();
        let led = Ledger::run(&env, &decls, &Default::default(), &mut ip);
        assert_eq!(led.pairs, 2);
        assert_eq!(led.types_ok, 2, "both types must interpret");
        assert_eq!(led.values_ok, 1);
        assert_eq!(led.values_attempted, 1);
        assert!(led.blocked.is_empty(), "unexpected gaps: {:?}", led.blocked);
        assert_eq!(led.fully_interpreted, 2);
    }

    /// A clause mini cannot interpret blocks, and the ledger says **which**
    /// one rather than only that something did. The reason comes from the
    /// `Typing`'s own `ev`, so attribution cannot drift from the gap.
    #[test]
    fn an_uninterpretable_clause_is_attributed_by_name() {
        let env = Environment::empty();
        let d = Declaration::Axiom {
            name: Name::simple("p"),
            lparams: vec![],
            ty: std::rc::Rc::new(crate::expr::Expr::NatLit(3)),
        };
        let mut ip = Interp::new();
        let led = Ledger::run(&env, &[d], &Default::default(), &mut ip);
        assert_eq!(led.types_ok, 0);
        assert_eq!(led.blocked.get("no-interp(Nat)"), Some(&1), "got {:?}", led.blocked);
    }
}
