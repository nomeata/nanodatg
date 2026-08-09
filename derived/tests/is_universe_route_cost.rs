//! Kernel-call cost of the two routes to each `U(c)` closure fact, and the
//! fixtures pinning that the routes prove the same statement.
//!
//! # The question this file answers
//!
//! `⊢ ∀x. is_universe(U(x))` is a theorem
//! (`derived::universe::least_universe_is_universe`), so three derivations that
//! transfer a closure property through the intersection — a fact holding in
//! *every* universe holds in `U(c)`, since `U(c) ⊆ u` for each universe
//! `u ∋ c` — could instead instantiate the general `is_universe(u)`-conditioned
//! statement at `u := U(c)` and discharge the antecedent. Shorter to *say* is
//! not cheaper to *run*: the theorem's `C₄` conjunct rides on
//! Cantor–Schröder–Bernstein, and this file measures what each route costs so
//! the choice is a number and not a taste.
//!
//! # How to read a number off
//!
//! As in `hyp_merge_cost.rs`: every `cell_*` test is an *entry point for a
//! coverage run*, not an assertion about cost. Build with
//! `-C instrument-coverage`, run one cell per process with its own
//! `LLVM_PROFILE_FILE`, and sum the execution counts of the
//! `kernel::thm::Thm::*` functions out of `llvm-cov export`. Differences
//! between cells are the cost of the step that distinguishes them:
//!
//! * `cell_s1_transfer − cell_base` — site 1, `bound::least_universe_closed`,
//!   the transfer route.
//! * `cell_s1_inst − cell_thm` — site 1 by instantiating
//!   `bound::universe_closed` at `U(c)`, **given** the theorem.
//! * `cell_thm − cell_base` — what the theorem itself costs
//!   (`csb::Csb::with_apply` + `least_universe_is_universe`), which the
//!   instantiation route must pay wherever the pipeline has not already.
//!
//! Likewise `s2` (`bound::least_universe_funspace_mem` versus
//! `bound::funspace_mem_universe` at `U(c)`) over the same base, and `s3`
//! (`funspace::pow_closed` / `funspace::sub_closed` versus
//! `universe::universe_power_closed` / `universe::universe_sub_mem` at `U(c)`)
//! over `cell_clauses_base`.
//!
//! The `ident_*` tests are the correctness half and run under plain
//! `cargo test`: each builds both routes and pins the conclusions equal as
//! `Formula`s — the kernel is locally nameless, so this is alpha-insensitive
//! identity, not a prose claim. The one deliberate exception is
//! [`ident_site3_sub_curried_not_identical`]: the clause-level
//! `sub_closed` is *curried* (`big ∈ u → (small ⊆ big → small ∈ u)`) while
//! `universe_sub_mem` instantiates to the uncurried form, and every consumer
//! chains the curried one — so for that site the instantiation route does not
//! even produce the statement the consumers use.

use kernel::{Env, FnSym, Formula, Term, Thm};

use derived::bound;
use derived::csb::Csb;
use derived::funspace as fsp;
use derived::rules::{hyp_and, inst_all};
use derived::sums::Sums;
use derived::universe as uni;
use derived::wtype::Wtype;
use derived::{a1i, imp_refl, gen_all};

/// The pieces every cell needs: a `Sums`/`Wtype` and the universe operator over
/// the same `Sets`, exactly as `tests/bound.rs` builds them.
struct Fix {
    wt: Wtype,
    lu: FnSym,
    lu_ax: Thm,
    pairing: Thm,
}

impl Fix {
    fn sums(&self) -> &Sums {
        &self.wt.sums
    }
}

fn fixture(env: &mut Env) -> Fix {
    let sums = Sums::new(env).expect("sums");
    let wt = Wtype::over(env, sums).expect("wtype");
    let sums = &wt.sums;
    let (lu, lu_ax) = uni::least_universe(env).expect("U(x)");
    let pairing = uni::universe_pairing(
        env,
        sums.ap.sets.up,
        &sums.ap.sets.up_ax,
        sums.ap.empty,
        &sums.ap.empty_ax,
        sums.pow,
        &sums.pow_ax,
    )
    .expect("universe_pairing");
    Fix { wt, lu, lu_ax, pairing }
}

/// The `bound` chain up to step 4 — everything both routes at sites 1 and 2
/// consume: `universe_closed` and `funspace_mem_universe` at an arbitrary `u`.
struct Chain4 {
    universe_closed: Thm,
    funspace_mem: Thm,
}

fn chain4(env: &mut Env, f: &Fix) -> Chain4 {
    let pair = bound::universe_opair(env, f.sums().ap.sets.up, &f.pairing).expect("opair");
    let mem_mem = uni::universe_mem_mem(env).expect("C₁ applied");
    let pairs = bound::funspace_pairs(env, f.sums()).expect("funspace_pairs");
    let sub = bound::funspace_subset_universe(env, f.sums(), &pairs, &mem_mem, &pair)
        .expect("subset");
    let funspace_mem =
        bound::funspace_mem_universe(env, f.sums(), &f.sums().ap.empty_ax, &pairs, &sub)
            .expect("member");
    let universe_closed =
        bound::universe_closed(env, f.sums(), &mem_mem, &pair, &funspace_mem)
            .expect("universe_closed");
    Chain4 { universe_closed, funspace_mem }
}

/// `⊢ ∀x. is_universe(U(x))`, over the fixture's own symbols.
fn the_theorem(env: &mut Env, f: &Fix) -> Thm {
    let csb = Csb::with_apply(env, &f.sums().ap).expect("csb");
    uni::least_universe_is_universe(
        env,
        &csb,
        f.lu,
        &f.lu_ax,
        f.sums().pow,
        &f.sums().pow_ax,
    )
    .expect("least_universe_is_universe")
}

/// From `⊢ (is_universe(t) ∧ P) → Q` and `⊢ is_universe(t)` (the theorem
/// instantiated), derive `⊢ P → Q`. The discharge every instantiation route
/// pays: `P → (is_universe(t) ∧ P)` from `a1i` + `imp_refl` + `hyp_and`, then
/// one syllogism.
fn discharge(imp: &Thm, univ: &Thm, p: Formula) -> Thm {
    let p_univ = a1i(univ, p.clone());
    let p_pair = hyp_and(&p_univ, &imp_refl(p)).expect("P → (is_universe ∧ P)");
    derived::rules::syl(&p_pair, imp).expect("discharge syllogism")
}

// ── Site 1: `least_universe_closed` ────────────────────────────────────────

/// The transfer route: `bound::least_universe_closed` as shipped.
fn s1_transfer(env: &mut Env, f: &Fix, c: &Chain4) -> Thm {
    bound::least_universe_closed(
        env,
        f.sums(),
        f.lu,
        &f.lu_ax,
        &f.wt.fs_mono,
        &c.universe_closed,
    )
    .expect("least_universe_closed")
}

/// The instantiation route: `bound::universe_closed` at `u := U(c)`, its
/// `is_universe` antecedent discharged by the theorem.
fn s1_inst(env: &mut Env, f: &Fix, c: &Chain4, thm: &Thm) -> Thm {
    let (cv, av, bv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, ta, tb) = (Term::var(cv), Term::var(av), Term::var(bv));
    let w = Term::apply(f.lu, vec![tc.clone()]);
    let fam = bound::fibres_in(env, f.sums(), &ta, &tb, &w);
    let p = Formula::and(Formula::mem(ta.clone(), w.clone()), fam);
    let at = inst_all(&c.universe_closed, &[w, ta, tb]).expect("universe_closed at U(c)");
    let univ = inst_all(thm, std::slice::from_ref(&tc)).expect("is_universe(U(c))");
    gen_all(&[cv, av, bv], &discharge(&at, &univ, p))
}

// ── Site 2: `least_universe_funspace_mem` ──────────────────────────────────

fn s2_transfer(env: &mut Env, f: &Fix, c: &Chain4) -> Thm {
    bound::least_universe_funspace_mem(
        env,
        f.sums(),
        f.lu,
        &f.lu_ax,
        &f.wt.fs_mono,
        &c.funspace_mem,
    )
    .expect("least_universe_funspace_mem")
}

fn s2_inst(env: &mut Env, f: &Fix, c: &Chain4, thm: &Thm) -> Thm {
    let (cv, xv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tc, tx, tf) = (Term::var(cv), Term::var(xv), Term::var(fv));
    let w = Term::apply(f.lu, vec![tc.clone()]);
    let p = Formula::and(
        Formula::mem(tx.clone(), w.clone()),
        Formula::mem(tf.clone(), f.sums().fs.of(tx.clone(), w.clone())),
    );
    let at = inst_all(&c.funspace_mem, &[w, tx, tf]).expect("funspace_mem at U(c)");
    let univ = inst_all(thm, std::slice::from_ref(&tc)).expect("is_universe(U(c))");
    gen_all(&[cv, xv, fv], &discharge(&at, &univ, p))
}

// ── Site 3: `funspace::pow_closed` / `sub_closed` at `U(c)` ────────────────

/// What the site-3 consumers hold: `C₂(U(·))` and `C₃(U(·))` as `∀c` theorems,
/// exactly the `Space` fields `c2`/`c3`.
struct Clauses {
    c2: Thm,
    c3: Thm,
}

fn clauses(env: &mut Env, f: &Fix) -> Clauses {
    let c2 = uni::least_universe_closed_sub(env, f.lu, &f.lu_ax).expect("C₂(U(x))");
    let c3 = uni::least_universe_closed_pow(env, f.lu, &f.lu_ax, f.sums().pow, &f.sums().pow_ax)
        .expect("C₃(U(x))");
    Clauses { c2, c3 }
}

/// The clause route: `pow_closed` from `C₂`/`C₃` instantiated at `c`, as
/// `funspace_in_universe_of`, `pi_rule` and `tower::rungs` all run it.
fn s3_pow_transfer(env: &mut Env, f: &Fix, cl: &Clauses, tc: &Term) -> Thm {
    let w = Term::apply(f.lu, vec![tc.clone()]);
    let c2 = inst_all(&cl.c2, std::slice::from_ref(tc)).expect("C₂ at c");
    let c3 = inst_all(&cl.c3, std::slice::from_ref(tc)).expect("C₃ at c");
    fsp::pow_closed(env, f.sums().pow, &f.sums().pow_ax, &w, &c2, &c3).expect("pow_closed")
}

/// The instantiation route: `universe_power_closed` at `u := U(c)`, discharged.
/// `universe_power_closed` itself must be derived first — no consumer holds it.
fn s3_pow_inst(env: &mut Env, f: &Fix, thm: &Thm, tc: &Term) -> Thm {
    let upc = uni::universe_power_closed(env, f.sums().pow, &f.sums().pow_ax)
        .expect("universe_power_closed");
    let w = Term::apply(f.lu, vec![tc.clone()]);
    let yv = env.fresh_var();
    let ty = Term::var(yv);
    let at = inst_all(&upc, &[w.clone(), ty.clone()]).expect("upc at U(c), y");
    let univ = inst_all(thm, std::slice::from_ref(tc)).expect("is_universe(U(c))");
    let p = Formula::mem(ty, w);
    Thm::gen(yv, &discharge(&at, &univ, p))
}

// ── Coverage cells. Nothing is asserted about cost: build one route, stop. ──

#[test]
fn cell_base() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let _ = chain4(&mut env, &f);
}

#[test]
fn cell_s1_transfer() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain4(&mut env, &f);
    let _ = s1_transfer(&mut env, &f, &c);
}

#[test]
fn cell_s2_transfer() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain4(&mut env, &f);
    let _ = s2_transfer(&mut env, &f, &c);
}

#[test]
fn cell_thm() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let _ = chain4(&mut env, &f);
    let _ = the_theorem(&mut env, &f);
}

#[test]
fn cell_s1_inst() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain4(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let _ = s1_inst(&mut env, &f, &c, &thm);
}

#[test]
fn cell_s2_inst() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain4(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let _ = s2_inst(&mut env, &f, &c, &thm);
}

#[test]
fn cell_clauses_base() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let _ = clauses(&mut env, &f);
}

#[test]
fn cell_s3_pow_transfer() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let cl = clauses(&mut env, &f);
    let tc = Term::apply(env.declare(0), vec![]);
    let _ = s3_pow_transfer(&mut env, &f, &cl, &tc);
}

#[test]
fn cell_s3_thm() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let _ = clauses(&mut env, &f);
    let _ = the_theorem(&mut env, &f);
}

#[test]
fn cell_s3_pow_inst() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let _ = clauses(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let tc = Term::apply(env.declare(0), vec![]);
    let _ = s3_pow_inst(&mut env, &f, &thm, &tc);
}

#[test]
fn cell_s3_sub_transfer() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let cl = clauses(&mut env, &f);
    let tc = Term::apply(env.declare(0), vec![]);
    let big = Term::apply(env.declare(0), vec![]);
    let small = Term::apply(env.declare(0), vec![]);
    let c2 = inst_all(&cl.c2, std::slice::from_ref(&tc)).expect("C₂ at c");
    let _ = fsp::sub_closed(&c2, &big, &small).expect("sub_closed");
}

#[test]
fn cell_s3_sub_inst() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let _ = clauses(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let tc = Term::apply(env.declare(0), vec![]);
    let big = Term::apply(env.declare(0), vec![]);
    let small = Term::apply(env.declare(0), vec![]);
    let usm = uni::universe_sub_mem(&mut env).expect("universe_sub_mem");
    let w = Term::apply(f.lu, vec![tc.clone()]);
    let at = inst_all(&usm, &[w.clone(), big.clone(), small.clone()]).expect("usm at U(c)");
    let univ = inst_all(&thm, std::slice::from_ref(&tc)).expect("is_universe(U(c))");
    let sub = kernel::thm::subset(&mut env, small.clone(), big.clone());
    let p = Formula::and(Formula::mem(big, w), sub);
    let _ = discharge(&at, &univ, p);
}

// ── Identity fixtures: the two routes prove the same formula. ──────────────

/// Site 1: `bound::universe_closed` at `u := U(c)`, antecedent discharged, is
/// *the same statement* as `bound::least_universe_closed` — as a `Formula`,
/// which under the locally-nameless kernel is alpha-insensitive identity.
#[test]
fn ident_site1_closed() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain4(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let transfer = s1_transfer(&mut env, &f, &c);
    let inst = s1_inst(&mut env, &f, &c, &thm);
    assert_eq!(
        transfer.concl(),
        inst.concl(),
        "the two routes to least_universe_closed prove different statements"
    );
}

/// Site 2: the same, for `least_universe_funspace_mem` against
/// `bound::funspace_mem_universe` at `U(c)`.
#[test]
fn ident_site2_funspace_mem() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let c = chain4(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let transfer = s2_transfer(&mut env, &f, &c);
    let inst = s2_inst(&mut env, &f, &c, &thm);
    assert_eq!(
        transfer.concl(),
        inst.concl(),
        "the two routes to least_universe_funspace_mem prove different statements"
    );
}

/// Site 3, power: `funspace::pow_closed` at `U(c)` against
/// `universe_power_closed` instantiated and discharged.
#[test]
fn ident_site3_pow() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let cl = clauses(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let tc = Term::apply(env.declare(0), vec![]);
    let transfer = s3_pow_transfer(&mut env, &f, &cl, &tc);
    let inst = s3_pow_inst(&mut env, &f, &thm, &tc);
    assert_eq!(
        transfer.concl(),
        inst.concl(),
        "the two routes to pow_closed at U(c) prove different statements"
    );
}

/// Site 3, subset: the statements are **not** identical, and this pins how
/// they differ. `sub_closed` is curried — `big ∈ u → (small ⊆ big →
/// small ∈ u)` — which is the shape every consumer chains with `syl`;
/// `universe_sub_mem` at `U(c)` discharges to the *uncurried*
/// `(big ∈ u ∧ small ⊆ big) → small ∈ u`. Converting costs further kernel
/// calls on top of the instantiation, so for this site the clause route is
/// both cheaper and the only one producing the consumed shape directly.
#[test]
fn ident_site3_sub_curried_not_identical() {
    let mut env = Env::new();
    let f = fixture(&mut env);
    let cl = clauses(&mut env, &f);
    let thm = the_theorem(&mut env, &f);
    let tc = Term::apply(env.declare(0), vec![]);
    let big = Term::apply(env.declare(0), vec![]);
    let small = Term::apply(env.declare(0), vec![]);
    let w = Term::apply(f.lu, vec![tc.clone()]);

    let c2 = inst_all(&cl.c2, std::slice::from_ref(&tc)).expect("C₂ at c");
    let transfer = fsp::sub_closed(&c2, &big, &small).expect("sub_closed");

    let usm = uni::universe_sub_mem(&mut env).expect("universe_sub_mem");
    let at = inst_all(&usm, &[w.clone(), big.clone(), small.clone()]).expect("usm at U(c)");
    let univ = inst_all(&thm, std::slice::from_ref(&tc)).expect("is_universe(U(c))");
    let sub = kernel::thm::subset(&mut env, small.clone(), big.clone());
    let p = Formula::and(Formula::mem(big.clone(), w.clone()), sub.clone());
    let inst = discharge(&at, &univ, p.clone());

    let mem_big = Formula::mem(big, w.clone());
    let mem_small = Formula::mem(small, w);
    assert_eq!(
        *transfer.concl(),
        Formula::imp(mem_big, Formula::imp(sub, mem_small.clone())),
        "sub_closed's curried shape drifted"
    );
    assert_eq!(
        *inst.concl(),
        Formula::imp(p, mem_small),
        "the discharged universe_sub_mem shape drifted"
    );
    assert_ne!(
        transfer.concl(),
        inst.concl(),
        "the two shapes were expected to differ; if they now agree, \
         re-measure and reconsider the route choice for sub_closed"
    );
}
