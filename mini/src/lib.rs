//! **mini** — a Rust port of
//! [`lean-mini-kernel`](https://github.com/nomeata/lean-mini-kernel), to be
//! made evidence-passing.
//!
//! Mini exists so that the evidence-threading design is built where there are
//! no caches, no hash-consing and no arena to confound it: a `ReaderT LEnv
//! (Except String)` and nothing else, owned de Bruijn expressions with explicit
//! `shift`/`substs`, a local context that is literally a telescope, whnf as a
//! stack machine with full eager delta, and recursors *generated* from
//! inductive declarations rather than parsed. See `MINI-DESIGN.md`.
//!
//! Status: **step (b)** — the port, unproven. `kernel`/`derived` are declared
//! as dependencies for step (c) and not yet used.
//!
//! Layout, one module per `MINI-DESIGN.md` §1 entry that exists yet:
//!
//! * [`expr`] — `Name`, `Level`, `Expr`, `shift`, `substs`, `subst_level`.
//! * [`env`] — `Declaration`, `ConstantInfo`, `Environment`.
//! * [`kernel`] — the port of `Kernel.lean`'s mutual block and
//!   `Environment.add`.
//! * [`convert`] — export file → mini declarations, and the level pre-pass.
//! * [`blocker`] — abort at the first missing derivation, and say what and
//!   where; the hard stop that replaces reading the ledger's columns.
//! * [`census`] — which §6.2 clauses the corpus actually spends its nodes on.
//! * [`class_s`] — §5.3's subsingleton carrier, for a non-indexed declaration.
//! * [`ctor_ix`] — an indexed family's constructors, §5.2's (M) at a λ-nest.
//! * [`conv`] — `Γ ⊢ ⟦e⟧ = ⟦e'⟧` and the certificate legs of a reduction.
//! * [`direct`] — the declarations whose denotation is named, not translated.
//! * [`dump`] — every stored theorem, sorted, with its absences named.
//! * [`ground`] — the mini side of the pre-pass: levels at a ground σ.
//! * [`ev`] — `Ev`/`Gap`/`Sealed`: evidence, named absences, and the
//!   persistence funnel.
//! * [`scope`] — binder open/close; the only module that names `Thm::assume`.
//! * [`interp`] — `⟦·⟧` against `mini::Expr`, and the per-`(name, σ)` store.
//! * [`ledger`] — what `⟦·⟧` reaches on the corpus, attributed by cause.
//! * [`mutual_aux`] — a `mutual … end` block as one aux inductive, its members
//!   as ordinary definitions over it, and its rules as `rfl` theorems.
//! * [`recursor`] — `⟦T.rec⟧`, and what each declaration's eliminator waits on.
//! * [`rec_prop`] — the class-(S) eliminator, §5.3's subsingleton rule at
//!   `ni = 0`.
//! * [`run`] — the per-file verdict.

/// **Mint a [`Gap`](crate::ev::Gap) into an `Err`, recording the exact source
/// line** — the `?`-census, as a macro rather than a `#[track_caller]` function.
///
/// `Ev::missing` covers the gaps that become evidence; this covers the ones
/// that become an `Err` and are turned into evidence by whichever caller
/// happened to be above. Without it the trail names the forwarding site, which
/// is how `Nat.add` came to be reported as giving up in `app_evidence`.
///
/// A macro because these routes mint through a per-function `miss` closure and
/// `#[track_caller]` would name the closure body; `file!()`/`line!()` expand at
/// the *use* site, so `ok_or_else(|| gap!(…))` reads the line that chose it.
#[macro_export]
macro_rules! gap {
    ($g:expr) => {{
        let g = $g;
        $crate::blocker::record_line(&g, file!(), line!());
        g
    }};
}

pub mod acc;
pub mod axiom;
pub mod blocker;
pub mod census;
pub mod class_p_ix;
pub mod class_s;
pub mod class_s_ix;
pub mod conv;
pub mod convert;
pub mod ctor_ix;
pub mod direct;
pub mod dump;
pub mod env;
pub mod ev;
pub mod expr;
pub mod fun_eta;
pub mod ground;
pub mod interp;
pub mod iota_dep;
pub mod iota_ix_dep;
pub mod kernel;
pub mod ledger;
pub mod minor_ix;
pub mod mutual_aux;
pub mod nested;
pub mod nested_ev;
pub mod proj_data;
pub mod proj_prop;
pub mod quot;
pub mod quot_classes;
pub mod quot_iota;
pub mod rec_acc;
pub mod rec_acc_ap;
pub mod rec_acc_ih;
pub mod rec_acc_iota;
pub mod rec_acc_value;
pub mod rec_dep;
pub mod rec_ix_dep;
pub mod rec_ix_prop;
pub mod rec_prop;
pub mod rec_s_ix;
pub mod rec_trunc;
pub mod rec_trunc_ix;
pub mod recursor;
pub mod run;
pub mod scope;
pub mod unit_like;
pub mod zoneb;
