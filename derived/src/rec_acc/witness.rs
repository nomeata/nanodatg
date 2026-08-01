//! **Non-vacuity**: the recursor fires, closed and unconditional, at a concrete
//! instance.
//!
//! # Interface
//!
//! At `A := 1`, `R := ∅`, `T := 1`, `e := ∅` — writing `F` for
//! `accrec(1,∅,1,∅)` and `P` for `pack(1,∅,1,∅)`:
//!
//! ```text
//! ⊢ ∀x ∀i. app(app(app(∅,x),•),i) = ∅                        [empty_step]
//! ⊢ step_typed(1,∅,1,∅)                                    [unit_step_typed]
//! ⊢ • ∈ acc(1,∅)                                            [unit_accessible]
//! ⊢ ∃w. ⟨•,w⟩ ∈ F                                             [unit_in_domain]
//! ⊢ F ∈ fs(acc(1,∅), 1)                                       [unit_funspace]
//! ⊢ app(F,•) = ∅                                                  [unit_iota]
//! ⊢ app(app(P,•),•) = ∅                                      [unit_pack_iota]
//! ```
//!
//! **Every one of these has no antecedent at all.**
//!
//! # Why this is the whole point
//!
//! [`super::total`]'s three theorems all carry `step_typed`, and `e` is an
//! arbitrary set, so they could in principle be statements about an antecedent
//! no four sets satisfy — and [`super::is_attempt`]'s theorems would all still
//! hold with `accrec = ∅`, since `indom(∅,x)` is never satisfied. Both hazards
//! are closed here at once: `step_typed` is *discharged*, and the first return
//! of [`unit_facts`] exhibits a pair of the recursor.
//!
//! The instance is the cheapest one that works, and it works for a reason that
//! does not generalise — which is exactly the discipline
//! [`crate::wrec_unit`] follows for `W`. `e := ∅` has empty domain, so
//! [`crate::wtype::app_of_empty`] computes the step to `∅` at *every* argument,
//! and `step_typed` becomes `∅ ∈ 1`. `R := ∅` makes every point of `A`
//! `R`-minimal, so `acc(1,∅) = 1` by [`crate::acc::acc_empty_relation`].
//!
//! # What it does *not* show, and where that is shown instead
//!
//! This instance has no edges, so the induction hypothesis is nowhere applied
//! and the recursion never actually recurses. The fact that it *would* — that
//! the recursive value is visibly inside the ι equation rather than hidden in an
//! opaque set — is [`super::ih::ih_app`], which is general and unconditional:
//!
//! ```text
//! ⊢ ∀g ∀A ∀R ∀x ∀y. ((y ∈ A ∧ ⟨y,x⟩ ∈ R) →
//!       app(app(ih(g,A,R,x), y), •) = app(g,y))
//! ```
//!
//! At `g := accrec` that reads: applying ι's third argument to a predecessor and
//! to the proof that it *is* one gives back `app(accrec,y)`. The two together —
//! a closed firing here, and a general beta rule there — are what stand between
//! "derived" and "derived about nothing".

use kernel::{Env, FnSym, Formula, Term, Thm};

use crate::{a1i, gen_all, inst_all};

use super::base::Base;
use super::extend::step_typed;
use super::package::pack_of;

/// `⊢ ∀x ∀i. app(app(app(∅,x),•),i) = ∅` — the empty step computes to `∅`
/// everywhere.
///
/// Three uses of [`crate::wtype::app_of_empty`], chained by congruence: `∅` has
/// no pairs, so `app(∅,·)` is `∅` at every argument, and the three curried
/// applications collapse one after another.
///
/// Every theorem in this file is advertised **closed and unconditional** — that
/// is the entire point of the file — so each entry refuses a `Base` carrying a
/// hypothetical theorem. The equation is pinned in release, against a rebuilt
/// `step_at(∅,x,i) = ∅`.
pub fn empty_step(env: &mut Env, b: &Base) -> Option<Thm> {
    if !b.all_unconditional() {
        return None
    }
    let aoe = crate::wtype::app_of_empty(env, &b.s)?;
    let (xv, iv) = (env.fresh_var(), env.fresh_var());
    let (tx, ti) = (Term::var(xv), Term::var(iv));
    let z = Term::apply(b.s.ap.empty, vec![]);
    let pt = b.s.point();

    // `app(∅,x) = ∅`, then `app(app(∅,x),•) = app(∅,•) = ∅`, then once more.
    let step = |env: &mut Env, inner: &Thm, arg: &Term| -> Option<Thm> {
        let (lhs, _) = inner.concl().as_eq()?;
        let hole = env.fresh_var();
        let ap = b.s.ap.app;
        let cong = Thm::eq_leibniz(
            lhs.clone(),
            z.clone(),
            hole,
            Formula::eq(
                Term::apply(ap, vec![lhs.clone(), arg.clone()]),
                Term::apply(ap, vec![Term::var(hole), arg.clone()]),
            ),
        );
        let moved = Thm::mp(
            &Thm::mp(&cong, inner)?,
            &Thm::eq_refl(Term::apply(ap, vec![lhs, arg.clone()])),
        )?;
        crate::eq_trans(env, &moved, &inst_all(&aoe, std::slice::from_ref(arg))?)
    };

    let s1 = inst_all(&aoe, std::slice::from_ref(&tx))?;
    let s2 = step(env, &s1, &pt)?;
    let s3 = step(env, &s2, &ti)?;
    if *s3.concl() != Formula::eq(b.step_at(&z, &tx, &ti), z) {
        return None
    }
    Some(gen_all(&[xv, iv], &s3))
}

/// `⊢ step_typed(1,∅,1,∅)` — the typing side condition, **discharged**.
///
/// The step is `∅` at every argument by [`empty_step`], and `∅ ∈ 1` is
/// [`crate::sums::Sums::unit_mem`]. So the hypothesis every theorem in
/// [`super::total`] carries is satisfiable, and the instance below shows what it
/// buys.
///
/// `empty_step` must be [`empty_step`], unconditional: this theorem's whole job
/// is to *discharge* a hypothesis, and one carrying a `Γ` of its own would
/// discharge nothing. The formula is pinned in release against a rebuilt
/// `step_typed(1,∅,1,∅)`.
pub fn unit_step_typed(env: &mut Env, b: &Base, empty_step: &Thm) -> Option<Thm> {
    if !b.all_unconditional() || !empty_step.hyps().is_empty() {
        return None
    }
    let one = b.s.unit();
    let z = Term::apply(b.s.ap.empty, vec![]);
    let (xv, iv) = (env.fresh_var(), env.fresh_var());
    let (tx, ti) = (Term::var(xv), Term::var(iv));

    let es = inst_all(empty_step, &[tx.clone(), ti.clone()])?;
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        z.clone(),
        b.step_at(&z, &tx, &ti),
        hole,
        Formula::mem(Term::var(hole), one.clone()),
    );
    let sym = crate::eq_symm(env, &es)?;
    let mem = Thm::mp(&Thm::mp(&carry, &sym)?, &b.s.unit_mem)?;

    let bound = super::ih::ih_bound(&b.s, &one, &one);
    let inner = Thm::gen(iv, &a1i(&mem, Formula::mem(ti, bound)));
    let out = Thm::gen(
        xv,
        &a1i(&inner, Formula::mem(tx, b.acc_of(&one, &z))),
    );
    if *out.concl() != step_typed(env, b, &one, &z, &one, &z) {
        return None
    }
    Some(out)
}

/// `⊢ • ∈ acc(1,∅)` — the point is accessible, because `∅` has no edges.
///
/// [`crate::acc::acc_empty_relation`] at `A := 1`, carried across by Leibniz.
///
/// The whole content is `b.ac.empty_relation`, which is `pub` and until now was
/// read here with a **conclusion-only** pin: a `Thm::assume(∀A. acc(A,∅) = A)`
/// passed straight through [`super::Base::over`] (whose loop covered four of the
/// seven `Acc` fields) and out of here as `{…} ⊢ • ∈ acc(1,∅)`, from where
/// [`unit_facts`] threaded the `Γ` into all four closed witnesses. Two guards
/// close it: [`crate::acc::Acc::all_unconditional`] at the `Base` boundary, and
/// [`crate::establishes`] here, so the pin at this call site now says both
/// halves out loud.
pub fn unit_accessible(env: &mut Env, b: &Base) -> Option<Thm> {
    if !b.all_unconditional() {
        return None
    }
    let one = b.s.unit();
    let z = Term::apply(b.s.ap.empty, vec![]);
    let eq = inst_all(&b.ac.empty_relation, std::slice::from_ref(&one))?;
    if !crate::establishes(&eq, &Formula::eq(b.acc_of(&one, &z), one.clone())) {
        return None
    }
    let hole = env.fresh_var();
    let carry = Thm::eq_leibniz(
        one.clone(),
        b.acc_of(&one, &z),
        hole,
        Formula::mem(b.s.point(), Term::var(hole)),
    );
    Thm::mp(&Thm::mp(&carry, &crate::eq_symm(env, &eq)?)?, &b.s.unit_mem)
}

/// What [`unit_facts`] needs: the four general theorems it instantiates, and the
/// three closed facts about this instance that discharge their hypotheses.
///
/// A view rather than seven loose arguments, so that a caller cannot pair one
/// development's `iota` with another's `step_typed` and get a true theorem about
/// the wrong recursor.
pub struct UnitInputs<'a> {
    /// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀z. (z ∈ acc(A,R) → indom(accrec,z)))`.
    pub totality: &'a Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. (ST → accrec ∈ fs(acc(A,R),T))`.
    pub funspace: &'a Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) → app(accrec,x) = step))`.
    pub iota: &'a Thm,
    /// The same at the thesis's packaging; see [`super::package::pack_iota`].
    pub pack_iota: &'a Thm,
    /// `⊢ step_typed(1,∅,1,∅)` — [`unit_step_typed`].
    pub step_typed: &'a Thm,
    /// `⊢ • ∈ acc(1,∅)` — [`unit_accessible`].
    pub accessible: &'a Thm,
    /// `⊢ ∀x ∀i. app(app(app(∅,x),•),i) = ∅` — [`empty_step`].
    pub empty_step: &'a Thm,
}

impl UnitInputs<'_> {
    /// The hypothesis half of the house rule for all seven fields.
    ///
    /// Every field is documented `⊢ …`, and the four theorems [`unit_facts`]
    /// returns are the ones [`crate::rec_acc`]'s header calls "**closed and
    /// unconditional**" and "every one of these has no antecedent at all". That
    /// sentence is a statement about the *sequent*, and [`Thm::mp`] unions `Γ`s
    /// silently, so one hypothetical input falsifies all four at once — which is
    /// exactly what a `Γ`-carrying `accessible` used to do. Conclusions are not
    /// rechecked here; each is pinned where it is spent, and the four results
    /// are pinned in release below.
    pub fn all_unconditional(&self) -> bool {
        crate::all_unconditional(&[
            self.totality,
            self.funspace,
            self.iota,
            self.pack_iota,
            self.step_typed,
            self.accessible,
            self.empty_step,
        ])
    }
}

/// The three closed consequences: the recursor is defined at `•`, is a function
/// on `acc(1,∅)`, and computes there.
///
/// Returned together because they share the same two inputs and are meaningless
/// apart: totality without a computed value says nothing about the recursion,
/// and a computed value without totality could be `app(∅,•)`.
///
/// # What is checked, and why all four are now pinned in release
///
/// `inp` must carry no hypothetical theorem
/// ([`UnitInputs::all_unconditional`]), and each of the four results is compared
/// with a rebuilt formula before being returned. Returns 3 and 4 already were;
/// returns 1 and 2 were not, in **either** profile, and both are pure
/// consequent-relabelling risks: `in_dom` is whatever
/// `inp.totality`'s inner consequent happens to be, and `fsp` is whatever
/// `inp.funspace` concludes after `ST` is discharged — a `UnitInputs.funspace`
/// of shape `ST → anything` handed back "anything" under the label
/// `F ∈ fs(acc(1,∅),1)`. These four theorems *are* the module's non-vacuity
/// claim, so the pins are the claim, and a `debug_assert` would have left the
/// release measurement path (`scripts/arena.sh`, `stepcount`,
/// `cargo build --release`) checking nothing.
pub fn unit_facts(
    env: &mut Env,
    b: &Base,
    rec: FnSym,
    inp: &UnitInputs,
) -> Option<(Thm, Thm, Thm, Thm)> {
    if !b.all_unconditional() || !inp.all_unconditional() {
        return None
    }
    let (totality, funspace, iota, pack_iota) =
        (inp.totality, inp.funspace, inp.iota, inp.pack_iota);
    let (st, accessible, empty_step) = (inp.step_typed, inp.accessible, inp.empty_step);
    let one = b.s.unit();
    let z = Term::apply(b.s.ap.empty, vec![]);
    let pt = b.s.point();
    let ps = vec![one.clone(), z.clone(), one.clone(), z.clone()];
    let rec_t = Term::apply(rec, ps.clone());

    // `indom(accrec(1,∅,1,∅), •)`.
    let tot = Thm::mp(&inst_all(totality, &ps)?, st)?;
    let in_dom = Thm::mp(
        &Thm::mp(&Thm::ax_inst(tot.concl().clone(), pt.clone())?, &tot)?,
        accessible,
    )?;
    if *in_dom.concl() != b.indom(env, &rec_t, &pt) {
        return None
    }

    // `accrec ∈ fs(acc(1,∅), 1)`.
    let fsp = Thm::mp(&inst_all(funspace, &ps)?, st)?;
    if *fsp.concl()
        != Formula::mem(rec_t.clone(), b.s.fs.of(b.acc_of(&one, &z), one.clone()))
    {
        return None
    }

    // `app(accrec,•) = ∅`, from ι and the computed step.
    let io = Thm::mp(&inst_all(iota, &ps)?, st)?;
    let io_x = Thm::mp(&Thm::ax_inst(io.concl().clone(), pt.clone())?, &io)?;
    let fired = Thm::mp(&io_x, accessible)?;
    let es = inst_all(empty_step, &[pt.clone(), b.ih_at(&rec_t, &one, &z, &pt)])?;
    let computed = crate::eq_trans(env, &fired, &es)?;
    if *computed.concl() != Formula::eq(b.app(&rec_t, &pt), z.clone()) {
        return None
    }

    // The same at the thesis's packaging.
    let pio = Thm::mp(&inst_all(pack_iota, &ps)?, st)?;
    let pio_x = Thm::mp(&Thm::ax_inst(pio.concl().clone(), pt.clone())?, &pio)?;
    let pfired = Thm::mp(&pio_x, accessible)?;
    let pcomputed = crate::eq_trans(env, &pfired, &es)?;
    let pack = pack_of(b, rec, &one, &z, &one, &z);
    if *pcomputed.concl() != Formula::eq(b.app(&b.app(&pack, &pt), &pt), z) {
        return None
    }

    Some((in_dom, fsp, computed, pcomputed))
}
