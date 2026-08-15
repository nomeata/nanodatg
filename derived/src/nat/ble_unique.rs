//! **The `ble` bridge**: any operation satisfying the three clauses *is* `ble`,
//! decoded.
//!
//! # Interface
//!
//! ```text
//! ⊢ ∀g ∀t ∀f. ( (∀y. (y ∈ ω → app(app(g,0), y) = t))
//!             → ((∀x. (x ∈ ω → app(app(g, succ x), 0) = f))
//!             → ((∀x. (x ∈ ω → ∀y. (y ∈ ω →
//!                    app(app(g, succ x), succ y) = app(app(g,x), y))))
//!             → ∀x. (x ∈ ω → ∀y. (y ∈ ω →
//!                    app(app(g,x), y) = bleb(t,f,x,y))))))
//! ```
//!
//! [`ble_uniqueness`], and [`ble_transfer`] fires it. It is
//! [`unique`](crate::nat::unique)'s bridge one variable wider, and it exists
//! for the same reason: a checker meets `≤` as a **set** — the interpretation
//! of whatever declaration its input called `Nat.ble`, compiled through
//! whatever `brecOn`/`below`/`match` nest its author used — and must not trust
//! a name. What it would take to use it is the three clauses for that set,
//! derived by δ and ι, and this instantiated at them.
//!
//! **No checker can do that today** — but *why* is not what this header said
//! for two revisions, and the wrong reason set the wrong scope. It is **not**
//! that deriving the clauses needs δ and ι run *under a universal quantifier*
//! through the `brecOn` nest. A Lean proof of a clause is converted into the
//! set-level equation by `checker/src/mini/eq_cash.rs`, which never
//! reduces the operation at all: it reads the proof's **typing**, moves the
//! subject to `•` by proof irrelevance, β-descends `⟦Eq.{v}⟧`'s stored nest and
//! applies `derived::prop::cond_elim`. `mini` already certifies `natBleZ`,
//! `natBleSZ` and `natBleSS` from `Nat.ble`'s own `brecOn` nest at ground σ —
//! that certification *is* the schematic work, done by ordinary typing
//! inference. What is actually missing is upstream and downstream of it: the
//! three clauses are **not in `init-prelude`** (Lean core proves none of them
//! under any name, §3), so they must be synthesised; and `tg.rs` still cannot
//! call `eq_cash`, though **no longer for the reason this line used to give**.
//! There is no `mini` crate any more: `eq_cash` is `checker/src/mini/eq_cash.rs`,
//! `checker/src/lib.rs` declares `pub mod mini`, `checker/src/mini.rs` declares
//! `pub mod eq_cash`, and `cash` is `pub` — so `crate::mini::eq_cash::cash`
//! *resolves* from `tg.rs`, which already reaches into `crate::mini::` for
//! `NatClause`, `Translated`/`DepRec`/`DepElim` and `proj_data::build`. The
//! blocker moved rather than closed: `cash` demands a live
//! `mini::kernel::Checker`, built from a `mini::env::Environment` and a
//! `&mut mini::interp::Interp`, and `TgBackend` holds neither at any site
//! (`Environment` does not occur in `tg.rs` at all; every `Interp` mention is a
//! comment). Everything mini publishes to tg arrives as finished data through
//! the shared const store, not as a checker one can resume.
//! `MEASUREMENTS.md`, *"The Lean-`Eq`-to-set-equation bridge already exists, and
//! it is not in the checker"*, is the measurement. The obvious way round — the
//! corpus holds only 51 distinct
//! `Nat.ble` instances, every operand ≤ 12, so derive 51 concrete facts instead
//! — was censused before it was built and refuted (`MEASUREMENTS.md`, "The
//! concrete route to link 3 is refuted inside the rule"): with the accelerator
//! withheld all 51 *reduce* concretely, and **not one certifies**. Two steps of
//! the unfolding are outright admissions — a `PProd` projection, and ι at a
//! `Nat.rec` whose major is a nat literal, which is the very origin the
//! workaround was meant to escape — and 25 424 β contractions are conditional
//! on domain premises nothing discharges.
//!
//! So this bridge is waiting on a **synthesised declaration and a live mini
//! checker handle inside `TgBackend`**, not on wiring, not on a schematic ι,
//! and no longer on a crate boundary. Three documents once said "wiring",
//! including an earlier version of this header; the revision after that said
//! "schematic ι", and that was wrong too; the revision after *that* said "crate
//! boundary", which was true when the crates were separate and is now stale.
//!
//! **And granting both of those would still not be enough** — measured
//! 2026-08-15 (`MEASUREMENTS.md`, *"The `Nat.ble` tranche, refuted at its own
//! gate"*). [`BleClauses`]'s three fields are `&Thm`, and [`ble_transfer`]
//! reaches its conclusion by `mp` on them, so **whatever hypotheses the clauses
//! carry, the numeral equation carries**. On the one input that contains them,
//! `checker --features tg` certifies `natBleZ` / `natBleSZ` / `natBleSS` only
//! *conditionally* — 16 / 23 / 24 undischarged raw-beta atoms each, the
//! `⟦arg⟧ ∈ ⟦binder domain⟧` obligations of `Nat.ble`'s own `brecOn` nest — so
//! the transfer would return a conditional equation and the checker's gap would
//! move to the escape ledger rather than close. `mini` certifies the same three
//! unconditionally; `mini` is not the program that owns the ledger, and that
//! distinction is the whole of link 2.
//!
//! # Why `t` and `f` are quantified, and not `succ 0` and `0`
//!
//! Because the imported operation is `Bool`-valued and `ble` is not. The three
//! clauses a checker can derive read `app(app(g,0),y) = ⟦Bool.true⟧`, and
//! nothing in `derived/` may know what that is — so the two values are
//! parameters here exactly as they are in [`crate::nat::Boolean`], and the
//! conclusion lands on `bleb`, which is `boolify ∘ ble`. Stating the bridge
//! against `ble` directly would oblige the caller to prove its operation
//! `ω`-valued, which it is not.
//!
//! # This link is worth nothing on its own, and neither are the other two
//!
//! `MEASUREMENTS.md`'s "Origin 2 is not the bignum bridge" prices the tranche
//! at **2 959 gaps** — the largest single origin in the `init-prelude` ledger —
//! and `NAT-BRIDGE-FEASIBILITY.md` §4.6 is the chain. Three links:
//!
//! 1. `⊢ bleb(t,f,num a,num b) = t` at literal operands — [`crate::nat::Boolean`]
//!    and [`Eval::ble_bool`](crate::nat::Eval::ble_bool), 70 inferences at four
//!    bits.
//! 2. **this file** — the transfer from the imported set to `bleb`.
//! 3. `reduce_rec` recording the major premise's own whnf as a step the backend
//!    sees, in `checker/`, so that `derive_iota_core` stops reading an
//!    unreduced major off `args[major]`.
//!
//! Closing any two of the three moves the ledger by zero. That is stated here
//! rather than left implied because link 1's predecessor —
//! [`crate::nat::Compare`], complete and certified since task #94 — sat unused
//! for want of exactly this sentence.
//!
//! **Link 3 landed and the list above still understates it.** `reduce_rec` does
//! return the major's own trace (`checker/src/tc.rs`), gated on
//! `reduct::fully_ruled` — and on this population the gate can never open,
//! because the major's reduction is either one `Admit::NatRed` (accelerator on)
//! or a β/δ/ι/projection chain (accelerator off), and `fully_ruled` admits
//! neither ι nor projection for measured reasons. The missing piece is not the
//! plumbing; it is this file's three premises, which nothing supplies.
//!
//! # The proof
//!
//! Induction on `x` with `∀y` **inside** the motive, so the hypothesis is
//! available at `y'` in the step; the step then splits on `y` by an inner
//! induction whose own hypothesis is ignored, which is how a case analysis on
//! `0`/`succ` is spelled with the tools this module has. Four cases, one
//! existing lemma each:
//!
//! | case | left | right |
//! |---|---|---|
//! | `x = 0` | clause 1 | [`Compare::ble_zero_l`] then [`Boolean::boolify_one`] |
//! | `x = succ x'`, `y = 0` | clause 2 | `sub(succ x',0) = succ x'` then `iszero(succ x') = 0`, then [`Boolean::boolify_zero`] |
//! | `x = succ x'`, `y = succ y'` | clause 3, then the hypothesis at `y'` | [`Sub::sub_succ_succ`] under `ble_ax` |
//!
//! Every one of them is an equation between terms of `ω` lifted through
//! `boolify`; nothing here is a disjunction, a negation or a case split on a
//! formula, which is [`compare`](crate::nat::compare)'s discipline kept one
//! level up.
//!
//! # What it does not assume
//!
//! **No typing hypothesis on `g`**, for [`unique`](crate::nat::unique)'s
//! reason: the statement reads `g` only through `app`, so `app(app(g,x),y)` is
//! a term whatever `g` is, and requiring `g ∈ fs(ω, fs(ω, B))` would be an
//! antecedent nothing reads and a caller would have to discharge first. **And
//! none on `t` and `f`** — they are never compared, only produced, so the
//! bridge holds at `t = f` as much as at `t ≠ f`. That is what makes the
//! non-vacuity witness in `derived/tests/nat.rs` cheap, and it is also why that
//! witness is not on its own evidence that the bridge distinguishes anything:
//! the test pairs it with a run at two distinct values.
//!
//! Both clause premises are stated **only on `ω`**. `g` may do anything it
//! likes off the carrier and the conclusion is silent there, which is the most
//! a checker could honestly claim about a set it did not build.

use kernel::{Env, Formula, FreeVar, Term, Thm};

use crate::discharge::{assuming, discharge};
use crate::err::DResult;
use crate::prim::{self, Shape};
use crate::rules::{congr_arg, inst_all};

use super::apparatus::Nat;
use super::boolean::Boolean;
use super::compare::Compare;
use super::glue::{congr1, gen_all, induct, induct_step, Chain};
use super::sub::Sub;

/// The four formulas the bridge is stated in, at a caller-supplied `g`, `t`
/// and `f`.
pub struct BleSpec {
    /// `∀y. (y ∈ ω → app(app(g,0), y) = t)`.
    pub zero_l: Formula,
    /// `∀x. (x ∈ ω → app(app(g, succ x), 0) = f)`.
    pub succ_zero: Formula,
    /// `∀x. (x ∈ ω → ∀y. (y ∈ ω → app(app(g,succ x), succ y) = app(app(g,x), y)))`.
    pub succ_succ: Formula,
    /// `∀x. (x ∈ ω → ∀y. (y ∈ ω → app(app(g,x), y) = bleb(t,f,x,y)))`.
    pub agrees: Formula,
}

impl BleSpec {
    /// Build the four formulas, using `xv`/`yv` as the bound variables — the
    /// same ones the derivation quantifies, so that a caller pinning the shape
    /// rebuilds exactly what [`ble_uniqueness`] produces.
    pub fn at(
        nat: &Nat,
        bl: &Boolean,
        g: &Term,
        t: &Term,
        f: &Term,
        xv: FreeVar,
        yv: FreeVar,
    ) -> BleSpec {
        let (tx, ty) = (Term::var(xv), Term::var(yv));
        let at = |a: Term, b: Term| nat.apply(nat.apply(g.clone(), a), b);
        let (x_om, y_om) = (nat.in_omega(tx.clone()), nat.in_omega(ty.clone()));
        let (zero, sx) = (nat.zero(), nat.succ_of(tx.clone()));
        let sy = nat.succ_of(ty.clone());

        let over_y = |body: Formula| Formula::forall(yv, Formula::imp(y_om.clone(), body));
        let over_x = |body: Formula| Formula::forall(xv, Formula::imp(x_om.clone(), body));

        BleSpec {
            zero_l: over_y(Formula::eq(at(zero.clone(), ty.clone()), t.clone())),
            succ_zero: over_x(Formula::eq(at(sx.clone(), zero), f.clone())),
            succ_succ: over_x(over_y(Formula::eq(at(sx, sy), at(tx.clone(), ty.clone())))),
            agrees: over_x(over_y(Formula::eq(
                at(tx.clone(), ty.clone()),
                bl.bleb_of(t.clone(), f.clone(), tx, ty),
            ))),
        }
    }
}

/// `⊢ ∀g ∀t ∀f. (clause₁ → (clause₂ → (clause₃ → agrees)))` — **the `ble`
/// bridge**.
pub fn ble_uniqueness(
    env: &mut Env,
    nat: &Nat,
    sb: &Sub,
    cmp: &Compare,
    bl: &Boolean,
) -> DResult<Thm> {
    let (gv, tv, fv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (tg, tt, tf) = (Term::var(gv), Term::var(tv), Term::var(fv));
    let (xv, yv) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(xv), Term::var(yv));
    let spec = BleSpec::at(nat, bl, &tg, &tt, &tf, xv, yv);

    let (h1, h2, h3) = (
        assuming(spec.zero_l.clone()),
        assuming(spec.succ_zero.clone()),
        assuming(spec.succ_succ.clone()),
    );

    let zero = nat.zero();
    let iszero = sb.iszero;
    let at = |a: Term, b: Term| nat.apply(nat.apply(tg.clone(), a), b);
    let bleb_at = |a: Term, b: Term| bl.bleb_of(tt.clone(), tf.clone(), a, b);

    // `⊢ bleb(t,f,a,b) = boolify(t,f,v)` from `⊢ ble(a,b) = v`: unfold the
    // composite, then rewrite the third argument of `boolify` under it. This is
    // the whole of the right-hand side in all four cases, and the only thing
    // that differs between them is which `v` the case has proved.
    let rhs = |env: &mut Env, a: &Term, b: &Term, ble_eq: &Thm| -> DResult<Thm> {
        let unfold = inst_all(&bl.bleb_ax, &[tt.clone(), tf.clone(), a.clone(), b.clone()])?;
        let args = [tt.clone(), tf.clone(), cmp.ble_of(a.clone(), b.clone())];
        let inner = congr_arg(env, bl.boolify, &args, 2, ble_eq)?;
        Chain::from(unfold).then(inner).done(env)
    };

    // The motive: `∀y ∈ ω` **inside**, so that the hypothesis is usable at the
    // `y'` of the successor case rather than only at the `y` it was stated for.
    let y_om = nat.in_omega(ty.clone());
    let phi = Formula::forall(
        yv,
        Formula::imp(
            y_om.clone(),
            Formula::eq(at(tx.clone(), ty.clone()), bleb_at(tx.clone(), ty.clone())),
        ),
    );

    // ── x = 0: `g(0,y) = t` against `ble(0,y) = succ 0` ──────────────────────
    let base = {
        let h_y = assuming(y_om.clone());
        let lhs = prim::mp(&inst_all(&h1, std::slice::from_ref(&ty))?, &h_y)?;
        let ble0 = prim::mp(&inst_all(&cmp.ble_zero_l, std::slice::from_ref(&ty))?, &h_y)?;
        let one_at = inst_all(&bl.boolify_one, &[tt.clone(), tf.clone()])?;
        let r = Chain::from(rhs(env, &zero, &ty, &ble0)?).then(one_at).done(env)?;
        let body = Chain::from(lhs).then_rev(r).done(env)?;
        prim::gen(yv, &discharge(&y_om, &body))?
    };

    // ── x = succ x' ──────────────────────────────────────────────────────────
    let step = induct_step(nat.core(), xv, &phi, |x_om, ih| {
        let sx = nat.succ_of(tx.clone());
        let psi = Formula::eq(at(sx.clone(), ty.clone()), bleb_at(sx.clone(), ty.clone()));

        // y = 0: `g(succ x, 0) = f` against `ble(succ x, 0) = 0`, which is
        // `sub(succ x, 0) = succ x` followed by `iszero(succ x) = 0`.
        let inner_base = {
            let lhs = prim::mp(&inst_all(&h2, std::slice::from_ref(&tx))?, x_om)?;
            let ble_s0 = {
                let unfold = inst_all(&cmp.ble_ax, &[sx.clone(), zero.clone()])?;
                let sz = inst_all(&sb.sub_zero, std::slice::from_ref(&sx))?;
                let izs = prim::mp(&inst_all(&sb.iszero_succ, std::slice::from_ref(&tx))?, x_om)?;
                Chain::from(unfold).then(congr1(env, iszero, &sz)?).then(izs).done(env)?
            };
            let zero_at = inst_all(&bl.boolify_zero, &[tt.clone(), tf.clone()])?;
            let r = Chain::from(rhs(env, &sx, &zero, &ble_s0)?).then(zero_at).done(env)?;
            Chain::from(lhs).then_rev(r).done(env)?
        };

        // y = succ y': clause 3, then the OUTER hypothesis at y'. The inner
        // hypothesis is deliberately unused — this induction is a case analysis.
        let inner_step = induct_step(nat.core(), yv, &psi, |y_om_thm, _unused| {
            let sy = nat.succ_of(ty.clone());
            let c3_x = prim::mp(&inst_all(&h3, std::slice::from_ref(&tx))?, x_om)?;
            let c3 = prim::mp(&inst_all(&c3_x, std::slice::from_ref(&ty))?, y_om_thm)?;
            let ih_y = prim::mp(&inst_all(ih, std::slice::from_ref(&ty))?, y_om_thm)?;
            let ble_ss = {
                let unfold = inst_all(&cmp.ble_ax, &[sx.clone(), sy.clone()])?;
                let ss = prim::mp(
                    &prim::mp(&inst_all(&sb.sub_succ_succ, &[tx.clone(), ty.clone()])?, x_om)?,
                    y_om_thm,
                )?;
                let back = inst_all(&cmp.ble_ax, &[tx.clone(), ty.clone()])?;
                Chain::from(unfold).then(congr1(env, iszero, &ss)?).then_rev(back).done(env)?
            };
            let fold = inst_all(&bl.bleb_ax, &[tt.clone(), tf.clone(), tx.clone(), ty.clone()])?;
            let r = Chain::from(rhs(env, &sx, &sy, &ble_ss)?).then_rev(fold).done(env)?;
            Chain::from(c3).then(ih_y).then_rev(r).done(env)
        })?;

        induct(env, nat.core(), yv, &psi, &inner_base, &inner_step)
    })?;

    let all_x = induct(env, nat.core(), xv, &phi, &base, &step)?;
    debug_assert_eq!(
        *all_x.concl(),
        spec.agrees,
        "ble_uniqueness: the conclusion has the wrong shape"
    );
    let discharged =
        discharge(&spec.zero_l, &discharge(&spec.succ_zero, &discharge(&spec.succ_succ, &all_x)));
    gen_all(&[gv, tv, fv], &discharged)
}

/// **The caller's side of the bridge**: its own operation, the two values it
/// decodes to, and the three clauses it derived from its own definition.
///
/// One datum rather than six arguments, for [`crate::nat::Decode`]'s reason —
/// they are never held apart, and a nine-argument [`ble_transfer`] was over
/// clippy's limit and harder to read besides.
pub struct BleClauses<'a> {
    /// The imported operation, read only through `app`.
    pub g: &'a Term,
    /// What it returns when `≤` holds.
    pub t: &'a Term,
    /// What it returns when `≤` does not hold.
    pub f: &'a Term,
    /// `⊢ ∀y. (y ∈ ω → app(app(g,0), y) = t)`.
    pub zero_l: &'a Thm,
    /// `⊢ ∀x. (x ∈ ω → app(app(g, succ x), 0) = f)`.
    pub succ_zero: &'a Thm,
    /// `⊢ ∀x ∀y ∈ ω. app(app(g,succ x), succ y) = app(app(g,x), y)`.
    pub succ_succ: &'a Thm,
}

/// The bridge fired at one operation: from the three clauses and two
/// memberships, `⊢ app(app(g,a), b) = bleb(t,f,a,b)`.
///
/// One instantiation at three terms, three `mp`s for the clauses, then two
/// instantiations and two `mp`s for the arguments and their memberships —
/// **independent of how large `a` and `b` are**, which is the property the
/// whole bridge exists for. Composed with
/// [`Eval::ble_bool`](crate::nat::Eval::ble_bool) it is the certificate the
/// checker's `Admit::NatRed` stands in for today.
pub fn ble_transfer(
    bridge: &Thm,
    c: &BleClauses<'_>,
    a_mem: &Thm,
    b_mem: &Thm,
) -> DResult<Thm> {
    let (a, _) = a_mem.concl().mem_parts()?;
    let (b, _) = b_mem.concl().mem_parts()?;
    let at_g = inst_all(bridge, &[c.g.clone(), c.t.clone(), c.f.clone()])?;
    let agrees =
        prim::mp(&prim::mp(&prim::mp(&at_g, c.zero_l)?, c.succ_zero)?, c.succ_succ)?;
    let at_a = prim::mp(&inst_all(&agrees, std::slice::from_ref(&a))?, a_mem)?;
    prim::mp(&inst_all(&at_a, std::slice::from_ref(&b))?, b_mem)
}
