//! The terms, and the hypothesis bundle everything is derived under.
//!
//! # Interface
//!
//! [`ext_of`] builds the extended graph `G := g ∪ {⟨⟨a,f⟩, v⟩}` and
//! [`hypothesis`] the conjunction every theorem in [`crate::wrec_extend`]
//! carries. `Cx` bundles the symbols, terms and variable names the sibling
//! files all need, so that each of them builds *the same* formula rather than a
//! look-alike.
//!
//! # Why the context is a struct with closures
//!
//! The recursion condition has to be established at the new point `⟨a,f⟩` and at
//! every old point of `g`, and the two are the *same* formula at two
//! substitution instances. Nothing in this crate substitutes into a term from
//! outside the kernel, so the only way to be certain the two instances match on
//! the nose is to build both from one closure taking the constructor and the
//! family — which is what `Cx` carries. Getting this wrong would not produce a
//! wrong theorem, but it would produce one that refuses to compose.

use kernel::{Env, Formula, Term, Thm};
use crate::funspace::bin_union;
use crate::separation::{or_intro_left, or_intro_right};
use crate::sums::Sums;
use crate::wrec::{indom, step_at};
use crate::wrec_total::{step_typed, Recursor};
use crate::wtype::Wtype;
use crate::{and_left, and_right, iff_mpr, inst_all, syl};

use super::shared::{iff_trans, or_right_cong, split_and};

/// The value the extension puts at `⟨a,f⟩`:
/// `V := app(e, ⟨a, ⟨f, comp(wrec(A,B,u,T,e), f, B(a))⟩⟩)`.
pub fn new_value(s: &Sums, r: &Recursor, ps: &[Term], a: &Term, f: &Term) -> Term {
    let rec_t = r.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);
    let fibre = s.ap.apply(ps[1].clone(), a.clone());
    step_at(&s.ap, r.comp, &ps[4], &rec_t, a, f, &fibre)
}

/// The one-point extension `G := wrec(A,B,u,T,e) ∪ {⟨⟨a,f⟩, V⟩}`.
pub fn ext_of(s: &Sums, r: &Recursor, ps: &[Term], a: &Term, f: &Term) -> Term {
    let rec_t = r.of(&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);
    let v = new_value(s, r, ps, a, f);
    let q = s.ap.sets.pair(s.ap.sets.pair(a.clone(), f.clone()), v);
    bin_union(&s.ap.sets, rec_t, crate::singleton(s.ap.sets.up, q))
}

/// The induction step's hypothesis, as one formula:
///
/// ```text
/// K := (((closed(A,B,u) ∧ step_typed(A,B,u,T,e)) ∧ a ∈ A) ∧ f ∈ fs(B(a),W))
///          ∧ ∀b. (b ∈ B(a) → indom(wrec, app(f,b)))
/// ```
///
/// Left-nested, and built in one place, because every lemma below has to
/// rebuild it and they must agree on the nose.
pub fn hypothesis(
    env: &mut Env,
    wt: &Wtype,
    r: &Recursor,
    ps: &[Term],
    a: &Term,
    f: &Term,
) -> Formula {
    let s = &wt.sums;
    let (ta, tb, tu, tt, te) = (&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);
    let w_t = wt.of(ta.clone(), tb.clone(), tu.clone());
    let rec_t = r.of(ta, tb, tu, tt, te);
    let fibre = s.ap.apply(tb.clone(), a.clone());

    let cl = crate::wtype::closed(env, s, ta, tb, tu);
    let st = step_typed(env, s, wt, ta, tb, tu, tt, te);
    let ma = Formula::mem(a.clone(), ta.clone());
    let mf = Formula::mem(f.clone(), s.fs.of(fibre.clone(), w_t));

    let bv = env.fresh_var();
    let tbv = Term::var(bv);
    let ih = Formula::forall(
        bv,
        Formula::imp(
            Formula::mem(tbv.clone(), fibre),
            indom(env, &s.ap, &rec_t, &s.ap.apply(f.clone(), tbv)),
        ),
    );
    Formula::and(
        Formula::and(Formula::and(Formula::and(cl, st), ma), mf),
        ih,
    )
}

/// Every term and every projection out of `K`, assembled once.
pub(super) struct Cx {
    /// The five parameters `A`, `B`, `u`, `T`, `e`.
    pub(super) ps: Vec<Term>,
    /// The constructor `a` the induction step is at.
    pub(super) a: Term,
    /// The subterm family `f` the induction step is at.
    pub(super) f: Term,
    /// `W(A,B,u)`.
    pub(super) w_t: Term,
    /// `wrec(A,B,u,T,e)`.
    pub(super) rec_t: Term,
    /// `B(a)`.
    pub(super) fibre: Term,
    /// `⟨a,f⟩`.
    pub(super) w0: Term,
    /// `V`.
    pub(super) v: Term,
    /// `⟨⟨a,f⟩, V⟩`.
    pub(super) q: Term,
    /// `G`.
    pub(super) g: Term,
    /// `K`.
    pub(super) k: Formula,
    /// `⊢ K → closed(A,B,u)`.
    pub(super) cl: Thm,
    /// `⊢ K → step_typed(A,B,u,T,e)`.
    pub(super) st: Thm,
    /// `⊢ K → a ∈ A`.
    pub(super) ma: Thm,
    /// `⊢ K → f ∈ fs(B(a),W)`.
    pub(super) mf: Thm,
    /// `⊢ K → ∀b. (b ∈ B(a) → indom(wrec, app(f,b)))`.
    pub(super) ih: Thm,
    /// `⊢ ∀u ∀v ∀z. (z ∈ u ∪ v ↔ (z ∈ u ∨ z ∈ v))`.
    pub(super) bin: Thm,
}

impl Cx {
    pub(super) fn new(
        env: &mut Env,
        wt: &Wtype,
        r: &Recursor,
        ps: &[Term],
        a: &Term,
        f: &Term,
    ) -> Option<Cx> {
        let s = &wt.sums;
        let (ta, tb, tu, tt, te) = (&ps[0], &ps[1], &ps[2], &ps[3], &ps[4]);
        let k = hypothesis(env, wt, r, ps, a, f);
        let (k4, ih_f) = split_and(&k)?;
        let (k3, mf_f) = split_and(&k4)?;
        let (k2, ma_f) = split_and(&k3)?;
        let (cl_f, st_f) = split_and(&k2)?;

        let p4 = and_left(k4.clone(), ih_f.clone());
        let ih = and_right(k4, ih_f);
        let p3 = syl(&p4, &and_left(k3.clone(), mf_f.clone()))?;
        let mf = syl(&p4, &and_right(k3, mf_f))?;
        let p2 = syl(&p3, &and_left(k2.clone(), ma_f.clone()))?;
        let ma = syl(&p3, &and_right(k2, ma_f))?;
        let cl = syl(&p2, &and_left(cl_f.clone(), st_f.clone()))?;
        let st = syl(&p2, &and_right(cl_f, st_f))?;

        Some(Cx {
            ps: ps.to_vec(),
            a: a.clone(),
            f: f.clone(),
            w_t: wt.of(ta.clone(), tb.clone(), tu.clone()),
            rec_t: r.of(ta, tb, tu, tt, te),
            fibre: s.ap.apply(tb.clone(), a.clone()),
            w0: s.ap.sets.pair(a.clone(), f.clone()),
            v: new_value(s, r, ps, a, f),
            q: s.ap.sets.pair(
                s.ap.sets.pair(a.clone(), f.clone()),
                new_value(s, r, ps, a, f),
            ),
            g: ext_of(s, r, ps, a, f),
            k,
            cl,
            st,
            ma,
            mf,
            ih,
            bin: crate::sums::mem_bin_union_iff(env, &s.ap.sets)?,
        })
    }

    /// `⊢ p ∈ G ↔ (p ∈ wrec ∨ p = ⟨⟨a,f⟩,V⟩)` — the extension's membership
    /// condition, with the singleton already read off.
    pub(super) fn mem(&self, s: &Sums, p: &Term) -> Option<Thm> {
        let sing = crate::singleton(s.ap.sets.up, self.q.clone());
        let bu = inst_all(&self.bin, &[self.rec_t.clone(), sing, p.clone()])?;
        let ms = inst_all(&s.ap.mem_sing, &[self.q.clone(), p.clone()])?;
        iff_trans(&bu, &or_right_cong(&ms, &Formula::mem(p.clone(), self.rec_t.clone()))?)
    }

    /// `⊢ p ∈ wrec → p ∈ G`.
    pub(super) fn embed(&self, s: &Sums, p: &Term) -> Option<Thm> {
        let m = self.mem(s, p)?;
        syl(
            &or_intro_left(
                Formula::mem(p.clone(), self.rec_t.clone()),
                Formula::eq(p.clone(), self.q.clone()),
            ),
            &iff_mpr(&m)?,
        )
    }

    /// `⊢ ⟨⟨a,f⟩,V⟩ ∈ G` — the new pair really is there.
    pub(super) fn new_pair(&self, s: &Sums) -> Option<Thm> {
        let m = self.mem(s, &self.q)?;
        Thm::mp(
            &syl(
                &or_intro_right(
                    Formula::mem(self.q.clone(), self.rec_t.clone()),
                    Formula::eq(self.q.clone(), self.q.clone()),
                ),
                &iff_mpr(&m)?,
            )?,
            &Thm::eq_refl(self.q.clone()),
        )
    }
}
