//! `Bool.rec` as the W-recursor, and its two computation rules.
//!
//! Each test rebuilds the formula it expects from the kernel's own constructors,
//! so a theorem with the right name and the wrong shape fails here.
//!
//! **Non-vacuity.** The two exports are equations, and three things are checked
//! about them beyond their shape: that each side is a *different term* (so
//! neither is reflexivity in disguise); that the recursor on the left is
//! literally the term [`derived::wbool_rec::BoolRec::of`] builds, i.e. a real
//! `wrec` application; and that the *same* recursor returns `fls` at one
//! constructor and `tru` at the other, which no degenerate step could do.

use kernel::{Env, Formula, Term};

use derived::bound::Bound;
use derived::twopoint::TwoPoint;
use derived::wbool_rec::BoolRec;
use derived::wrec_total::Recursor;
use derived::wtype::Wtype;

struct Fix {
    wt: Wtype,
    bnd: Bound,
    br: BoolRec,
}

/// The two `∀`-bound variables the exports are stated at, rebuilt so the test
/// can name the terms the theorem talks about.
fn expected(env: &mut Env, f: &Fix, r: &Recursor, second: bool) -> (Formula, Term, Term) {
    let (fv, tv) = (env.fresh_var(), env.fresh_var());
    let (fls, tru) = (Term::var(fv), Term::var(tv));
    let rec_t = BoolRec::of(&f.wt, &f.bnd, r, &fls, &tru);
    let s = &f.wt.sums;
    let tag = if second { s.inr(s.point()) } else { s.inl(s.point()) };
    let ctor = f.wt.sup(tag, f.wt.empty());
    let lhs = s.ap.apply(rec_t, ctor);
    let minor = if second { tru } else { fls };
    let body = Formula::eq(lhs.clone(), minor.clone());
    (Formula::forall(fv, Formula::forall(tv, body)), lhs, minor)
}

/// Rebuilding the recursor needs the *same* `Recursor` the fixture used, so the
/// whole chain is built once and the symbols handed back.
fn fixture_with_recursor(env: &mut Env) -> (Fix, Recursor) {
    let wt = Wtype::new(env).expect("W-type");
    let bnd = Bound::new(env, &wt).expect("bound");
    let r = Recursor::new(env, &wt).expect("recursor");
    let ext = derived::wrec_extend::extension(env, &wt, &r).expect("extension");
    let total = derived::wrec_total::totality(env, &wt, &r, &ext).expect("totality");
    let iota = derived::wrec_total::iota(env, &wt, &r, &total).expect("iota");
    let empty_u = derived::enums::empty_in_least_universe(env, &wt, &bnd).expect("∅ ∈ U(A)");
    let closed = derived::enums::enum_closed(env, &wt, &bnd, &empty_u).expect("closed");
    let tp = TwoPoint::over(env, &wt.sums.ap).expect("two-point");
    let br = BoolRec::over(env, &wt, &bnd, &r, &closed, &iota, &tp).expect("Bool.rec");
    let r2 = Recursor {
        comp: r.comp,
        comp_ax: r.comp_ax.clone(),
        ext: r.ext.clone(),
        att: r.att,
        att_ax: r.att_ax.clone(),
        rec: r.rec,
        members: r.members.clone(),
        sv: r.sv.clone(),
        subset: r.subset.clone(),
        value: r.value.clone(),
        mono: r.mono.clone(),
        subset_prod: r.subset_prod.clone(),
        rec_cond: r.rec_cond.clone(),
        comp_typed: r.comp_typed.clone(),
    };
    (Fix { wt, bnd, br }, r2)
}

#[test]
fn the_recursor_computes_at_bool_false() {
    let mut env = Env::new();
    let (f, r) = fixture_with_recursor(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.br.iota_false.concl()));
    let (want, lhs, minor) = expected(&mut env, &f, &r, false);
    assert_eq!(*f.br.iota_false.concl(), want);
    assert_ne!(lhs, minor, "the equation is reflexivity in disguise");
}

#[test]
fn the_recursor_computes_at_bool_true() {
    let mut env = Env::new();
    let (f, r) = fixture_with_recursor(&mut env);
    assert!(kernel::thm::debug_locally_closed(f.br.iota_true.concl()));
    let (want, lhs, minor) = expected(&mut env, &f, &r, true);
    assert_eq!(*f.br.iota_true.concl(), want);
    assert_ne!(lhs, minor, "the equation is reflexivity in disguise");
}

/// The two constructors are what [`derived::enums::Enum2`] says they are, and
/// the two rules are about **one** recursor: the same `brec(fls,tru)` returns
/// `fls` at `⟨inl •,∅⟩` and `tru` at `⟨inr •,∅⟩`.
#[test]
fn one_recursor_two_values() {
    let mut env = Env::new();
    let (f, r) = fixture_with_recursor(&mut env);
    let empty_u = derived::enums::empty_in_least_universe(&mut env, &f.wt, &f.bnd).expect("∅ ∈ U");
    let mem = derived::enums::enum_mem(&mut env, &f.wt, &f.bnd, &empty_u).expect("enum_mem");
    let inj = derived::enums::enum_inj(&mut env, &f.wt).expect("enum_inj");
    let e2 = derived::enums::enum2(&f.wt, &f.bnd, &mem, &inj).expect("Bool");

    let (fv, tv) = (env.fresh_var(), env.fresh_var());
    let (fls, tru) = (Term::var(fv), Term::var(tv));
    let rec_t = BoolRec::of(&f.wt, &f.bnd, &r, &fls, &tru);
    let ap = &f.wt.sums.ap;

    let at_false = derived::inst_all(&f.br.iota_false, &[fls.clone(), tru.clone()]).expect("inst");
    let at_true = derived::inst_all(&f.br.iota_true, &[fls.clone(), tru.clone()]).expect("inst");
    assert_eq!(
        *at_false.concl(),
        Formula::eq(ap.apply(rec_t.clone(), e2.fst_t.clone()), fls),
        "the false rule is not stated at ⟦Bool.false⟧"
    );
    assert_eq!(
        *at_true.concl(),
        Formula::eq(ap.apply(rec_t, e2.snd_t.clone()), tru),
        "the true rule is not stated at ⟦Bool.true⟧"
    );
    assert_ne!(e2.fst_t, e2.snd_t, "the two constructors are the same term");
}
