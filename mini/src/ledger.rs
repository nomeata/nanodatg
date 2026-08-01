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
//! It measures **both** of MINI-DESIGN.md §0's axes, kept apart:
//!
//! * *interpretation* — was `⟦ty⟧` / `⟦val⟧` produced at all;
//! * *evidence* — was `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` produced, and when not, **what
//!   kind of work** it is waiting on ([`Cause`]).
//!
//! The second axis is the one nanoda cannot produce today, because its ledger
//! mixes threading debt with library debt. Here they are separate columns, and
//! §0.4's rule is what keeps them separate: a gap's reason propagates from the
//! sub-result that caused it, never from the failing clause's own label. A
//! previous run filed 104 pairs as `pi-typing-unthreaded` when the cause was an
//! uninterpreted inductive several levels down; that is *scope*, not
//! *threading*, and the two must not trade places.
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
    // ── the evidence axis ────────────────────────────────────────────────
    /// Pairs whose type's own typing `⊢ ⟦ty[σ]⟧ ∈ ⟦Sort l⟧` was derived.
    pub type_ev_ok: usize,
    /// Pairs whose constant typing `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` was derived.
    pub const_ev_ok: usize,
    /// Why a constant typing was missing, by propagated reason.
    pub missing: BTreeMap<String, usize>,
    /// The same, rolled up to the axis it belongs to.
    pub by_cause: BTreeMap<&'static str, usize>,
    /// `Sealed::new` refusals at the store funnel. **Zero on a correctly
    /// threaded run**, by I2: at top level no scopes are open. A nonzero
    /// count is a threading bug surfaced where it should surface, and it is
    /// mini's analogue of nanoda's escaped-assumption ledger.
    pub unsealed: usize,
    /// The §0.3 conversion census, summed over the file.
    pub convs: crate::interp::ConvStats,
}

impl Ledger {
    fn key(g: Option<&Gap>) -> String {
        match g {
            Some(Gap::StructProj(n)) => format!("proj({n})"),
            Some(Gap::NoInterpretation(n, _)) => format!("no-interp({n})"),
            Some(Gap::Axiom(n)) => format!("axiom({n})"),
            Some(Gap::Iota(n)) => format!("iota({n})"),
            Some(Gap::UnitLike(n)) => format!("unit-like({n})"),
            Some(Gap::StructEta(n)) => format!("struct-eta({n})"),
            Some(Gap::StrLit) => "strLit".to_string(),
            Some(Gap::SymbolicLevel) => "symbolic-level".to_string(),
            Some(Gap::Skeleton) => "skeleton".to_string(),
            Some(Gap::Classifier) => "classifier".to_string(),
            Some(Gap::NoEndpoint) => "no-endpoint".to_string(),
            Some(Gap::NotDecomposable) => "not-decomposable".to_string(),
            Some(Gap::BinderCongruence) => "binder-congruence".to_string(),
            Some(Gap::ConvCompose(w)) => format!("conv-compose({w})"),
            Some(Gap::EndpointDrift) => "endpoint-drift".to_string(),
            Some(Gap::FunEta) => "fun-eta".to_string(),
            Some(Gap::SortTowerHeight) => "sort-tower-height".to_string(),
            Some(other) => format!("{other:?}"),
            None => "inference-error".to_string(),
        }
    }

    fn note(&mut self, g: Option<&Gap>) { *self.blocked.entry(Self::key(g)).or_insert(0) += 1; }

    /// Record a missing constant typing, **by the axis it is waiting on**.
    fn note_missing(&mut self, g: Option<&Gap>) {
        *self.missing.entry(Self::key(g)).or_insert(0) += 1;
        let c = match g.map(Gap::cause) {
            Some(crate::ev::Cause::Scope) => "interpretation-scope",
            Some(crate::ev::Cause::Library) => "library-gap",
            Some(crate::ev::Cause::Threading) => "threading-incompleteness",
            Some(crate::ev::Cause::Assumption) => "model-assumption",
            Some(crate::ev::Cause::Bug) => "mini-bug",
            None => "inference-error",
        };
        *self.by_cause.entry(c).or_insert(0) += 1;
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
                let ty_t = c.infer_type(&ty_g);
                let ty_ev = ty_t.as_ref().ok().map(|t| t.ev.clone());
                let (ty_tm, ty_blocked) = split(ty_t);
                // **The `def`/`theorem` pipeline of §8.** The value's own
                // typing is transported along the conversion the acceptance
                // gate produces, and then along the constant's defining
                // equation: `⊢ ⟦val⟧ ∈ ⟦valTy⟧` ↦ `⊢ ⟦val⟧ ∈ ⟦ty⟧` ↦
                // `⊢ ⟦c⟧ ∈ ⟦ty⟧`. Nothing is re-derived and nothing is
                // discarded; the `Conv` this consumes is the reason
                // `assert_def_eq` returns one.
                let mut val_mem: Option<crate::ev::Ev> = None;
                let (val_tm, val_blocked) = match &val_g {
                    Some(v) => {
                        let tv = c.infer_type(v);
                        if let (Ok(tv), Some(want)) = (&tv, ty_tm.clone()) {
                            val_mem = Some(c.retarget_to(tv, &ty_g, want));
                        }
                        split(tv)
                    }
                    None => (None, None),
                };
                drop(c);

                if ty_tm.is_some() {
                    led.types_ok += 1;
                } else {
                    all_ok = false;
                    led.note(ty_blocked.as_ref());
                }
                if ty_ev.as_ref().is_some_and(|e| e.is_proved()) {
                    led.type_ev_ok += 1;
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
                // An axiom's inhabitation is a model assumption; everything
                // else that has no interpreted value is blocked by whatever
                // stopped the value.
                // §0.4 again, and this one bit: `Gap::Axiom` is a *model
                // assumption* and belongs only to a declaration that really is
                // an axiom. Using it as the fallback filed 57 theorems as
                // assumptions — the sharpest possible version of the mistake
                // the rule exists to prevent, since "not derivable in
                // principle" and "not derived yet" are not even on the same
                // axis. When a definition's typing is missing, the reason is
                // whatever stopped its value, or failing that its type.
                let no_val = match d {
                    Declaration::Axiom { .. } => Gap::Axiom(name.clone()),
                    _ => val_blocked
                        .clone()
                        .or_else(|| ty_blocked.clone())
                        .unwrap_or(Gap::Classifier),
                };
                let entry = match val_tm {
                    // The value interpreted, so `⟦c.{σ}⟧` is an
                    // **abbreviation** for it — a conservative definitional
                    // extension whose axiom is also delta reduction's
                    // certificate. `opaque` gets the abbreviation and hence the
                    // typing, but not the equation: opacity is a *checker*
                    // policy, not a fact about the model.
                    Some(v) => match ip.abbrev(&v) {
                        Some((t, ax)) => {
                            // `⊢ ⟦c⟧ ∈ ⟦ty⟧`, from `⊢ ⟦val⟧ ∈ ⟦ty⟧` carried
                            // back along `⊢ ⟦c⟧ = ⟦val⟧`.
                            let typing = match val_mem.clone() {
                                Some(crate::ev::Ev::Proved(m)) => {
                                    match ip.retarget_subject(&m, &ax) {
                                        Some(t) => match crate::ev::Sealed::new(t) {
                                            Ok(s) => Ok(s),
                                            Err(_) => {
                                                led.unsealed += 1;
                                                Err(Gap::Skeleton)
                                            }
                                        },
                                        None => Err(Gap::ConvCompose("store-retarget")),
                                    }
                                }
                                Some(crate::ev::Ev::Gap(g)) => Err(g),
                                None => Err(no_val.clone()),
                            };
                            ConstInterp {
                                term: t,
                                typing,
                                defeq: if transparent {
                                    crate::ev::Sealed::new(ax).ok()
                                } else {
                                    None
                                },
                            }
                        }
                        None => ConstInterp {
                            term: ip.opaque(),
                            typing: Err(Gap::Skeleton),
                            defeq: None,
                        },
                    },
                    // A fresh opaque symbol is a pure signature extension: it
                    // is conservative on its own, but that it *denotes an
                    // inhabitant* of anything is exactly what is not derivable.
                    None => ConstInterp {
                        term: ip.opaque(),
                        typing: Err(no_val.clone()),
                        defeq: None,
                    },
                };
                match &entry.typing {
                    Ok(_) => led.const_ev_ok += 1,
                    Err(g) => led.note_missing(Some(g)),
                }
                ip.put_const(key, entry);
            }
            if all_ok {
                led.fully_interpreted += 1;
            }
        }
        led.convs = ip.convs;
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

    /// The evidence axis, as its own row: what was derived, and what the rest
    /// is waiting on.
    pub fn evidence_row(&self) -> String {
        let mut s = format!(
            "evidence\tpairs={}\ttypeEv={}\tconstEv={}\tunsealed={}",
            self.pairs, self.type_ev_ok, self.const_ev_ok, self.unsealed
        );
        for (k, v) in &self.by_cause {
            s.push_str(&format!("\t{k}={v}"));
        }
        for (k, v) in &self.missing {
            s.push_str(&format!("\twaiting:{k}={v}"));
        }
        s
    }

    /// The §0.3 conversion census: how many conversions are hypothesis-free.
    pub fn conv_row(&self) -> String {
        format!(
            "convs\tproved={}\tsealed={}\tgapped={}\tmoved={}\tmovedSealed={}",
            self.convs.proved,
            self.convs.sealed,
            self.convs.gapped,
            self.convs.moved,
            self.convs.moved_sealed
        )
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
