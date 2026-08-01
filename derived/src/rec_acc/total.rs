//! **Totality**, and the unguarded ι rule.
//!
//! # Interface
//!
//! Writing `ST` for [`super::extend::step_typed`]:
//!
//! ```text
//! ⊢ ∀A ∀R ∀T ∀e. (ST → ∀z. (z ∈ acc(A,R) → indom(accrec,z)))        [totality]
//! ⊢ ∀A ∀R ∀T ∀e. (ST → accrec(A,R,T,e) ∈ fs(acc(A,R), T))      [rec_funspace]
//! ⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) →
//!       app(accrec,x) = app(app(app(e,x),•), ih(accrec,A,R,x))))        [iota]
//! ```
//!
//! **`ST` is the only hypothesis, and it is the only one anywhere in
//! [`crate::rec_acc`].** Everything up to and including
//! [`super::is_attempt::iota_on_domain`] is unconditional; this file is where
//! the price of totality is paid, and the price is exactly the one
//! `INDUCTIVES.md` records for `wrec`: the step must be typed into `T`, because
//! `e` is an arbitrary set and nothing else forces its values anywhere.
//!
//! There is **no** analogue of `wrec`'s second hypothesis `closed(A,B,u)`. `W`
//! carries it through every theorem because `W(A,B,u)` is not a subset of
//! anything already named; `acc(A,R) ⊆ A` by construction, so no bound is a
//! parameter and none has to be discharged.
//!
//! # The argument
//!
//! [`crate::acc::acc_rect`] at `φ(z) := indom(accrec,z)`, with the induction
//! step supplied by [`super::extend`]: at a point `x ∈ A` all of whose
//! `R`-predecessors are already in `accrec`'s domain, the one-point extension
//! `G := accrec ∪ {⟨x,V⟩}` is an attempt, so `G ⊆ accrec` — the recursor being
//! the union of *all* attempts — and `x` is in `accrec`'s domain after all.
//!
//! The step needs `x ∈ acc(A,R)`, and gets it from
//! [`crate::acc::acc_intro`] — which is unconditional here and is the single
//! fact that makes this module cheaper than [`crate::wrec_total`].

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::acc::{acc_rect, ind_step, Params};
use crate::funspace::is_total;
use crate::{
    a1i, and_right, exists_mono, gen_all, hyp_and, hyp_mp, iff_mp, iff_mpr, imp_refl, inst_all,
    syl, uncurry,
};

use super::attempt::indom_intro;
use super::base::Base;
use super::extend::{
    ext_bound, ext_is_attempt, ext_rec_cond, ext_value_typed, hypothesis, rec_value_typed,
    step_typed, Ext,
};
use super::is_attempt::UnionFacts;
use super::shared::{gen_under, hyp_inst};

/// Everything [`totality`] needs that is not already in [`Base`].
pub struct Machinery<'a> {
    /// The set of attempts.
    pub att: FnSym,
    /// Its characteristic theorem.
    pub att_ax: &'a Thm,
    /// The recursor symbol.
    pub rec: FnSym,
    /// The union-layer theorems.
    pub facts: &'a UnionFacts<'a>,
    /// `⊢ ∀A ∀R ∀T ∀e ∀x. (indom(accrec,x) → app(accrec,x) = …)`.
    pub iota_dom: &'a Thm,
    /// `⊢ ∀A ∀R ∀T ∀e. rec_cond(A,R,e,accrec)`.
    pub rec_rc: &'a Thm,
    /// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))`.
    pub bin: &'a Thm,
}

/// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀z. (z ∈ acc(A,R) → indom(accrec,z)))` — **the recursor
/// is defined everywhere on `acc(A,R)`**.
///
/// See the module header for the argument.
pub fn totality(env: &mut Env, b: &Base, m: &Machinery) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt, te) = (ps[0].clone(), ps[1].clone(), ps[2].clone(), ps[3].clone());
    let acc_t = b.acc_of(&ta, &tr);
    let rec_t = Term::apply(m.rec, ps.clone());

    let (zv, xv) = (env.fresh_var(), env.fresh_var());
    let (tz, tx) = (Term::var(zv), Term::var(xv));
    let phi = b.indom(env, &rec_t, &tz);
    let st = step_typed(env, b, &ta, &tr, &tt, &te);

    // ── The induction step, at the fresh point `x` ──────────────────────────
    let e = Ext {
        b,
        att: m.att,
        att_ax: m.att_ax,
        rec: m.rec,
        facts: m.facts,
        iota_dom: m.iota_dom,
        bin: m.bin,
        ps: ps.clone(),
        x: tx.clone(),
    };
    let k = hypothesis(env, &e, &tx);

    let vanp = e.value_at_new_point(env)?;
    let sv_g = e.ext_single_valued(env, &vanp)?;
    let rvt = rec_value_typed(env, &e)?;
    let k_vt = ext_value_typed(env, &e, &tx, &rvt)?;
    let k_bound = ext_bound(env, &e, &tx, &k_vt)?;
    let k_rc = ext_rec_cond(env, &e, &tx, &sv_g, m.rec_rc)?;
    let k_att = ext_is_attempt(env, &e, &tx, &k_bound, &sv_g, &k_rc)?;

    // `⟨x,V⟩ ∈ G`, so `x` is in `G`'s domain, so it is in `accrec`'s.
    let q_in_g = Thm::mp(&e.new_point_in_ext(&e.q())?, &Thm::eq_refl(e.q()))?;
    let ind_g = Thm::mp(&indom_intro(env, b, &e.g(), &tx, &e.value())?, &q_in_g)?;
    let bridge = {
        let mut a = ps.clone();
        a.push(e.g());
        inst_all(m.facts.indom, &a)?
    };
    let k_bridge = hyp_inst(&syl(&k_att, &bridge)?, std::slice::from_ref(&tx))?;
    let k_goal = hyp_mp(&k_bridge, &a1i(&ind_g, k.clone()))?;
    if *k_goal.concl() != Formula::imp(k, b.indom(env, &rec_t, &tx)) {
        return None
    }

    // ── Reassemble the minor premise and fire `acc_rect` ────────────────────
    let curried = uncurry(&uncurry(&k_goal)?)?; // ST → (x ∈ A → (IH → …))
    let minor = gen_under(xv, &curried)?;
    let want = Formula::imp(
        st.clone(),
        ind_step(env, &b.ac, &acc_t, &ta, &tr, zv, &phi),
    );
    if *minor.concl() != want {
        return None
    }

    let rect = acc_rect(env, &b.ac, &vars, Params { a: vars[0], r: vars[1] }, zv, &phi)?;
    let out = syl(&minor, &rect)?;
    debug_assert_eq!(
        *out.concl(),
        Formula::imp(
            st,
            Formula::forall(zv, Formula::imp(Formula::mem(tz, acc_t), phi))
        ),
        "totality: unexpected shape"
    );
    Some(gen_all(&vars, &out))
}

/// `⊢ ∀A ∀R ∀T ∀e. (ST → ∀x. (x ∈ acc(A,R) → app(accrec,x) = …))` — **the ι
/// rule, unguarded**.
///
/// [`super::is_attempt::iota_on_domain`] with its guard discharged by
/// [`totality`], and nothing else.
pub fn iota(
    env: &mut Env,
    b: &Base,
    rec: FnSym,
    total: &Thm,
    iota_dom: &Thm,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt, te) = (ps[0].clone(), ps[1].clone(), ps[2].clone(), ps[3].clone());
    let rec_t = Term::apply(rec, ps.clone());
    let st = step_typed(env, b, &ta, &tr, &tt, &te);

    let xv = env.fresh_var();
    let tx = Term::var(xv);
    let tot = inst_all(total, &ps)?;
    let tot_x = hyp_inst(&tot, std::slice::from_ref(&tx))?;
    let dom = inst_all(iota_dom, &ps)?;
    let dom_x = Thm::mp(&Thm::ax_inst(dom.concl().clone(), tx.clone())?, &dom)?;

    let body = crate::funcs::hyp_syl(&tot_x, &a1i(&dom_x, st.clone()))?;
    let out = gen_under(xv, &body)?;
    let eqn = Formula::eq(
        b.app(&rec_t, &tx),
        b.step_at(&te, &tx, &b.ih_at(&rec_t, &ta, &tr, &tx)),
    );
    if *out.concl()
        != Formula::imp(
            st,
            Formula::forall(
                xv,
                Formula::imp(Formula::mem(tx, b.acc_of(&ta, &tr)), eqn),
            ),
        )
    {
        return None
    }
    Some(gen_all(&vars, &out))
}

/// `⊢ ∀A ∀R ∀T ∀e. (ST → accrec(A,R,T,e) ∈ fs(acc(A,R), T))` — **the recursor is
/// a function from the accessible part to the target**.
///
/// Its three clauses are [`super::union::rec_subset_prod`], [`totality`]
/// sharpened to name a value in `T`, and [`super::union::rec_single_valued`].
pub fn rec_funspace(
    env: &mut Env,
    b: &Base,
    rec: FnSym,
    facts: &UnionFacts,
    total: &Thm,
) -> Option<Thm> {
    let vars: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let ps: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
    let (ta, tr, tt, te) = (ps[0].clone(), ps[1].clone(), ps[2].clone(), ps[3].clone());
    let acc_t = b.acc_of(&ta, &tr);
    let rec_t = Term::apply(rec, ps.clone());
    let st = step_typed(env, b, &ta, &tr, &tt, &te);

    // Totality, sharpened: the witness lies in `T`.
    let (xv, wv) = (env.fresh_var(), env.fresh_var());
    let (tx, tw) = (Term::var(xv), Term::var(wv));
    let pair = b.s.ap.sets.pair(tx.clone(), tw.clone());
    let mem_pair = Formula::mem(pair.clone(), rec_t.clone());

    let sub = inst_all(facts.subset_prod, &ps)?;
    let sub_at = Thm::mp(&Thm::ax_inst(sub.concl().clone(), pair.clone())?, &sub)?;
    let pip = inst_all(
        &b.s.pair_in_prod,
        &[acc_t.clone(), tt.clone(), tx.clone(), tw.clone()],
    )?;
    let to_wt = syl(
        &syl(&sub_at, &iff_mp(&pip)?)?,
        &and_right(
            Formula::mem(tx.clone(), acc_t.clone()),
            Formula::mem(tw.clone(), tt.clone()),
        ),
    )?;
    let body = hyp_and(&to_wt, &imp_refl(mem_pair.clone()))?;
    let mono = exists_mono(wv, &Thm::gen(wv, &body))?;

    let tot = inst_all(total, &ps)?;
    let tot_x = hyp_inst(&tot, std::slice::from_ref(&tx))?;
    let st_total_body = crate::funcs::hyp_syl(&tot_x, &a1i(&mono, st.clone()))?;
    let st_total = gen_under(xv, &st_total_body)?;
    if *st_total.concl()
        != Formula::imp(st.clone(), is_total(env, &b.s.ap.sets, &acc_t, &tt, &rec_t))
    {
        return None
    }

    let sv = inst_all(facts.single_valued, &ps)?;
    let cond = hyp_and(&st_total, &a1i(&sv, st.clone()))?;
    let sub_all = a1i(&inst_all(facts.subset_prod, &ps)?, st.clone());
    let isfun = hyp_and(&sub_all, &cond)?;
    let want = crate::funspace::is_function(env, &b.s.ap.sets, &b.s.prod, &acc_t, &tt, &rec_t);
    if *isfun.concl() != Formula::imp(st.clone(), want) {
        return None
    }

    let fs_at = inst_all(&b.s.fs.fs_ax, &[acc_t.clone(), tt.clone(), rec_t.clone()])?;
    let out = syl(&isfun, &iff_mpr(&fs_at)?)?;
    if *out.concl()
        != Formula::imp(st, Formula::mem(rec_t, b.s.fs.of(acc_t, tt)))
    {
        return None
    }
    Some(gen_all(&vars, &out))
}
