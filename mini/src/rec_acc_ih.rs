//! **`derived`'s induction hypothesis is a section of Lean's** —
//! `ih(accrec,A,R̄,x) ∈ ⟦∀ y (hy : r y x), C y (h y hy)⟧`.
//!
//! # Interface
//!
//! ```text
//! rec_acc_ih::ih_in_minor_domain(ip, cx, x, x_in_a, ih, iset, scopes) -> Option<Thm>
//! ```
//!
//! Called from [`crate::rec_acc_value`]'s refinement induction and from nowhere
//! else. `MINI-HANDOFF.md` §25 item 3 names this as the cost of piece 2 and
//! sizes it as *three* separate facts; measured, that is the right count and
//! this file is one per section below.
//!
//! # The two spellings, and why nothing relates them for free
//!
//! `derived`'s `ih` is a set of **rows**,
//!
//! ```text
//! ih(g,A,R,x) = { ⟨y, cval(ep(R,y,x), app(g,y))⟩ : y ∈ A }
//! ```
//!
//! and Lean's `∀ y (hy : r y x), C y (h y hy)` interprets to a `dprod` of
//! `dprod`s. They are the same function and they are built by different
//! constructions, so the membership is proved and not read off: `dprod`'s own
//! defining condition wants a function-space membership **and** a section
//! condition, and the function-space membership wants a subset, a totality and
//! a single-valuedness.
//!
//! | fact | route |
//! |---|---|
//! | each row is a section of its own fibre | `dprod_const_fibre_n`, then `cval_bound`/`cval_single_valued` |
//! | the whole is a section over `A` | `ih_ax` and `app_of_graph`, then `dprod_def` |
//! | `ep(R̄,y,x) = ⟦r y x⟧` | [`RecAccApparatus::edge_value`](crate::rec_acc_ap::RecAccApparatus::edge_value) |
//!
//! # The inner fibre is constant, and that is what keeps this finite
//!
//! `⟦∀ (hy : r y x), C y (h y hy)⟧` is a `dprod` whose fibre does **not**
//! mention the proof binder — `h y hy : Acc α r y` is a `Prop`, so it denotes
//! `•` and the body is `app(app(C̄,y),•)` at every argument. So
//! [`derived::ext::dprod_const_fibre_n`] applies and the inner product *is* a
//! function space `fs(⟦r y x⟧, app(app(C̄,y),•))`, with no `⋃img` anywhere. The
//! constancy is **checked**, against the fibre symbol's own defining equation,
//! rather than assumed from the shape of Lean's type.
//!
//! The outer product has no such luck: its fibre mentions `y` twice, through
//! `r y x` and through `C y`. That one is done the long way, and `⋃img(h⃗,A)` is
//! named exactly once, in [`ih_in_minor_domain`]'s own opening.
//!
//! # Where the induction hypothesis is spent, and where A4 is not
//!
//! The row at `y` is `cval(ep(R̄,y,x), app(accrec,y))`, and its typing needs
//! `app(accrec,y) ∈ app(app(C̄,y),•)` — which is **`φ(y)`**, the induction
//! hypothesis's right conjunct. That is the whole reason the refinement has to
//! be an induction rather than a direct typing: nothing outside an `acc_rect`
//! holds that fact at a predecessor.
//!
//! It is needed only under `h ∈ ep(R̄,y,x)`, because `cval`'s two lemmas are
//! guarded by **inhabitation of the condition** rather than by the proposition
//! ([`derived::rec_acc::cval`]). At a `y` that is not a predecessor the
//! conditional value is empty and the fibre is `dprod(∅,·) = {∅}`, and no case
//! analysis on the proposition is performed here or in the library.

use kernel::{Formula, Term, Thm};

use derived::rec_acc::{cval_of, ep_of, ih_of, row_of};

use crate::interp::{Interp, PiShape};
use crate::rec_acc_value::Cx;
use crate::scope::Scopes;

/// `Γ ⊢ ih(accrec,A,R̄,x) ∈ ⟦∀ y (hy : r y x), C y (h y hy)⟧`.
///
/// `ih` is the induction hypothesis of the *refinement*, `iset` the domain of
/// Lean's minor premise's third `Π`, and `sc` the caller's own [`Scopes`] —
/// threaded rather than replaced, because everything here carries the `x`
/// binder's hypothesis and the assumed induction hypothesis as well as its own
/// two, and the LIFO order of the four is what makes `gen_checked` succeed at
/// each close.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ih_in_minor_domain(
    ip: &mut Interp,
    cx: &Cx<'_>,
    x: &Term,
    x_in_a: &Thm,
    ih: &Thm,
    iset: &Term,
    sc: &mut Scopes,
) -> Option<Thm> {
    let prelude = ip.prelude.clone();
    let sums = prelude.tower.sums.clone();
    let base = cx.ra.ra.base.clone();
    let up = sums.ap.sets.up;
    let ih_tm = ih_of(base.ih, cx.accrec.clone(), cx.a.clone(), cx.graph.clone(), x.clone());

    let PiShape::Dep { site: si, dom: da } = ip.as_pi(iset)? else { return None };
    if da != cx.a {
        return None
    }
    // The one place `⋃img` is named. Everything below is stated over it.
    let outer_base = sums.ap.sets.union_of(si.dp.img_of(&si.holes, cx.a.clone()));
    let sv = derived::inst_all(
        &base.ih_single_valued,
        &[cx.accrec.clone(), cx.a.clone(), cx.graph.clone(), x.clone()],
    )?;

    // ── everything at one predecessor `y ∈ A` ───────────────────────────────
    let tok_y = sc.open(&mut ip.env, cx.a.clone());
    let (yv, y, y_in_a) = {
        let s = sc.get(0)?;
        (s.var(), s.term(), s.assumption().clone())
    };
    let v = ip.app(cx.accrec.clone(), y.clone());
    let ep_t = ep_of(base.ep, cx.graph.clone(), y.clone(), x.clone());
    let sing_v = derived::singleton(up, v.clone());
    let row_v = cval_of(&sums, ep_t.clone(), v.clone());
    let row = row_of(&sums, base.ep, &cx.accrec, &cx.graph, x, &y);

    // `⟨y, row_v⟩ ∈ ih`, and hence `app(ih,y) = row_v`.
    let row_in = {
        let y2 = ip.env.fresh_var();
        let body = Formula::and(
            Formula::mem(Term::var(y2), cx.a.clone()),
            Formula::eq(row.clone(), row_of(&sums, base.ep, &cx.accrec, &cx.graph, x, &Term::var(y2))),
        );
        let witness = derived::and_intro(&y_in_a, &Thm::eq_refl(row.clone()));
        let ex = derived::exists_intro(y2, body, y.clone(), &witness)?;
        let ax = derived::inst_all(
            &base.ih_ax,
            &[cx.accrec.clone(), cx.a.clone(), cx.graph.clone(), x.clone(), row.clone()],
        )?;
        Thm::mp(&derived::iff_mpr(&ax)?, &ex)?
    };
    let app_eq = Thm::mp(
        &derived::inst_all(&base.app_of_graph, &[ih_tm.clone(), y.clone(), row_v.clone()])?,
        &derived::and_intro(&sv, &row_in),
    )?;

    // ── the row lands in Lean's own fibre at `y` ────────────────────────────
    let inner = ip.rebuild(&si.skel, &si.holes, &y);
    let row_in_inner = row_in_fibre(
        ip,
        cx,
        &Row { y: &y, y_in_a: &y_in_a, x, x_in_a, v: &v, ep_t: &ep_t, sing_v: &sing_v, row_v: &row_v },
        ih,
        &inner,
        sc,
    )?;
    let row_sym = ip.to_fibre_set(&si, yv, &row_in_inner)?;

    // ── …hence in `⋃img(h⃗,A)`, which is what the function space is into ────
    let b_at_y = ip.fibre_at(&si, y.clone());
    let img_t = si.dp.img_of(&si.holes, cx.a.clone());
    let row_in_base = {
        let w = ip.env.fresh_var();
        let at_w = ip.fibre_at(&si, Term::var(w));
        let body = Formula::and(
            Formula::mem(Term::var(w), cx.a.clone()),
            Formula::eq(b_at_y.clone(), at_w),
        );
        let ex = derived::exists_intro(
            w,
            body,
            y.clone(),
            &derived::and_intro(&y_in_a, &Thm::eq_refl(b_at_y.clone())),
        )?;
        let mut args = si.holes.clone();
        args.push(cx.a.clone());
        args.push(b_at_y.clone());
        let in_img = Thm::mp(&derived::iff_mpr(&derived::inst_all(&si.dp.img_ax, &args)?)?, &ex)?;

        let s = ip.env.fresh_var();
        let body = Formula::and(
            Formula::mem(Term::var(s), img_t.clone()),
            Formula::mem(row_v.clone(), Term::var(s)),
        );
        let ex = derived::exists_intro(
            s,
            body,
            b_at_y.clone(),
            &derived::and_intro(&in_img, &row_sym),
        )?;
        let ax = derived::inst_all(&sums.ap.sets.un_ax, &[img_t.clone(), row_v.clone()])?;
        Thm::mp(&derived::iff_mpr(&ax)?, &ex)?
    };

    // The three bodies the three conjuncts of `dprod`'s condition want, all at
    // this one `y` and discharged from one scope.
    let sec_body = ip.retarget_subject(&row_sym, &app_eq)?;
    let tot_body = {
        let u = ip.env.fresh_var();
        let body = Formula::and(
            Formula::mem(Term::var(u), outer_base.clone()),
            Formula::mem(sums.ap.sets.pair(y.clone(), Term::var(u)), ih_tm.clone()),
        );
        derived::exists_intro(u, body, row_v.clone(), &derived::and_intro(&row_in_base, &row_in))?
    };
    let prod_body = {
        let ax = derived::inst_all(
            &sums.pair_in_prod,
            &[cx.a.clone(), outer_base.clone(), y.clone(), row_v.clone()],
        )?;
        Thm::mp(&derived::iff_mpr(&ax)?, &derived::and_intro(&y_in_a, &row_in_base))?
    };

    let closed = sc.close(tok_y);
    let section = closed.discharge(&sec_body).ok()?;
    let total = closed.discharge(&tot_body).ok()?;
    let rows_in_prod = closed.discharge(&prod_body).ok()?;

    // ── `ih ⊆ prod(A, ⋃img)`, by elimination on `ih`'s own membership ───────
    let subset = subset_of_prod(ip, cx, x, &ih_tm, &outer_base, &rows_in_prod)?;

    // ── `ih ∈ fs(A, ⋃img)`, then `ih ∈ dprod(h⃗,A)` ─────────────────────────
    let is_fun = derived::and_intro(&subset, &derived::and_intro(&total, &sv));
    let in_fs = Thm::mp(
        &derived::iff_mpr(&derived::inst_all(
            &prelude.fs.fs_ax,
            &[cx.a.clone(), outer_base, ih_tm.clone()],
        )?)?,
        &is_fun,
    )?;
    let mut args = si.holes.clone();
    args.push(cx.a.clone());
    args.push(ih_tm.clone());
    let def = derived::inst_all(&si.dp.dprod_def, &args)?;
    let out = Thm::mp(&derived::iff_mpr(&def)?, &derived::and_intro(&in_fs, &section))?;
    (*out.concl() == Formula::mem(ih_tm, iset.clone())).then_some(out)
}

/// One row of the induction hypothesis, and the terms it is written with.
struct Row<'a> {
    y: &'a Term,
    y_in_a: &'a Thm,
    x: &'a Term,
    x_in_a: &'a Thm,
    /// `app(accrec,y)` — the recursive value.
    v: &'a Term,
    /// `ep(R̄,y,x)` — the edge proposition, `derived`'s spelling.
    ep_t: &'a Term,
    /// `{v}`.
    sing_v: &'a Term,
    /// `cval(ep(R̄,y,x), v)`.
    row_v: &'a Term,
}

/// `Γ ⊢ cval(ep(R̄,y,x), app(accrec,y)) ∈ ⟦∀ (hy : r y x), C y (h y hy)⟧`.
///
/// Three moves. The edge proposition is identified with Lean's own truth value
/// `⟦r y x⟧` — the only statement in the project that wants **both** graph
/// bridges, and it is `derived`'s, so mini only instantiates it. The fibre is
/// constant, so the inner `dprod` is a function space. And the constant
/// function `c × {v}` is in `fs(c,V)` as soon as `v ∈ V` holds *under `c`'s own
/// inhabitation*, which is exactly where the induction hypothesis is spent.
fn row_in_fibre(
    ip: &mut Interp,
    cx: &Cx<'_>,
    row: &Row<'_>,
    ih: &Thm,
    inner: &Term,
    sc: &mut Scopes,
) -> Option<Thm> {
    let prelude = ip.prelude.clone();
    let sums = prelude.tower.sums.clone();
    let base = cx.ra.ra.base.clone();
    let point = ip.point();

    let PiShape::Dep { site: sj, dom: rel } = ip.as_pi(inner)? else { return None };
    // `⟦r y x⟧ ∈ ⟦Prop⟧`, and the check inside `rel_typing` is what identifies
    // `app(app(⟦r⟧,y),x)` with the domain the interpretation named.
    let rel_u0 = crate::rec_acc::rel_typing(
        ip, &cx.r, &cx.r_mem, row.y, row.y_in_a, row.x, row.x_in_a, &rel,
    )?;
    let edge_eq = Thm::mp(
        &derived::inst_all(
            &cx.ra.edge_value,
            &[cx.a.clone(), cx.r.clone(), row.y.clone(), row.x.clone()],
        )?,
        &derived::and_intro(row.y_in_a, &derived::and_intro(row.x_in_a, &rel_u0)),
    )?;

    // ── the inner product is a function space ───────────────────────────────
    let c_at_y = ip.app(cx.cm.clone(), row.y.clone());
    let fibre = ip.app(c_at_y, point);
    let zv = ip.env.fresh_var();
    let mut bargs = sj.holes.clone();
    bargs.push(Term::var(zv));
    let b_at_z = derived::inst_all(&sj.b_ax, &bargs)?;
    if b_at_z.concl().as_eq()?.1 != fibre {
        return None
    }
    let const_h = crate::rec_dep::gen_all_checked(
        &[zv],
        &derived::a1i(&b_at_z, Formula::mem(Term::var(zv), rel.clone())),
    )?;
    let cfib = derived::ext::dprod_const_fibre_n(
        &mut ip.env,
        &prelude.ap,
        &prelude.fs,
        sj.b,
        sj.dp.img,
        &sj.dp.img_ax,
        sj.dp.dprod,
        &sj.dp.dprod_def,
        &prelude.fs_app_mem,
        &prelude.fs_retarget,
    )?;
    let mut cargs = sj.holes.clone();
    cargs.push(rel.clone());
    cargs.push(fibre.clone());
    let dp_eq = Thm::mp(&derived::inst_all(&cfib, &cargs)?, &const_h)?;

    // ── the constant function is in it ──────────────────────────────────────
    let cval_rel = cval_of(&sums, rel.clone(), row.v.clone());
    let tok_w = sc.open(&mut ip.env, rel.clone());
    let (w, w_in_rel) = {
        let s = sc.get(0)?;
        (s.term(), s.assumption().clone())
    };
    // `w` is a proof of `r y x`, so it is `•` — which is what puts the pair
    // into the graph and so lets the induction hypothesis fire.
    let w_pt = ip.point_of_proof(&rel_u0, &w_in_rel)?;
    let pt_eq_w = derived::eq_symm(&mut ip.env, &w_pt)?;
    let pt_in_rel = ip.retarget_subject(&w_in_rel, &pt_eq_w)?;
    let pair = Thm::mp(
        &derived::inst_all(
            &cx.ac.pair_in_graph,
            &[cx.a.clone(), cx.r.clone(), row.y.clone(), row.x.clone()],
        )?,
        &derived::and_intro(row.y_in_a, &derived::and_intro(row.x_in_a, &pt_in_rel)),
    )?;
    let at_y = derived::inst_all(ih, std::slice::from_ref(row.y))?;
    let conj = Thm::mp(&Thm::mp(&at_y, row.y_in_a)?, &pair)?;
    let v_in_fibre = derived::and_elim_right(&conj)?;
    if *v_in_fibre.concl() != Formula::mem(row.v.clone(), fibre.clone()) {
        return None
    }

    let guard_body = derived::and_intro(&w_in_rel, &v_in_fibre);
    let tot_body = {
        let v_in_sing = Thm::mp(
            &derived::iff_mpr(&derived::inst_all(
                &sums.ap.mem_sing,
                &[row.v.clone(), row.v.clone()],
            )?)?,
            &Thm::eq_refl(row.v.clone()),
        )?;
        let pair_wv = Thm::mp(
            &derived::iff_mpr(&derived::inst_all(
                &sums.pair_in_prod,
                &[rel.clone(), row.sing_v.clone(), w.clone(), row.v.clone()],
            )?)?,
            &derived::and_intro(&w_in_rel, &v_in_sing),
        )?;
        let u = ip.env.fresh_var();
        let body = Formula::and(
            Formula::mem(Term::var(u), fibre.clone()),
            Formula::mem(sums.ap.sets.pair(w.clone(), Term::var(u)), cval_rel.clone()),
        );
        derived::exists_intro(u, body, row.v.clone(), &derived::and_intro(&v_in_fibre, &pair_wv))?
    };
    let closed = sc.close(tok_w);
    let guard = closed.discharge(&guard_body).ok()?;
    let total = closed.discharge(&tot_body).ok()?;

    let sub = Thm::mp(
        &derived::inst_all(
            &base.cval_bound,
            &[rel.clone(), row.v.clone(), rel.clone(), fibre.clone()],
        )?,
        &guard,
    )?;
    let single = derived::inst_all(&base.cval_single_valued, &[rel.clone(), row.v.clone()])?;
    let is_fun = derived::and_intro(&sub, &derived::and_intro(&total, &single));
    let in_fs = Thm::mp(
        &derived::iff_mpr(&derived::inst_all(
            &prelude.fs.fs_ax,
            &[rel.clone(), fibre, cval_rel.clone()],
        )?)?,
        &is_fun,
    )?;
    let back = derived::eq_symm(&mut ip.env, &dp_eq)?;
    let in_dprod = ip.retarget_set(&in_fs, &back)?;
    if in_dprod.concl().as_mem()?.1 != *inner {
        return None
    }
    // `cval(ep(R̄,y,x), v) = cval(⟦r y x⟧, v)` — the edge equation, applied in
    // the product's first argument.
    let cval_eq = derived::congr_arg(
        &mut ip.env,
        sums.prod.prod,
        &[row.ep_t.clone(), row.sing_v.clone()],
        0,
        &edge_eq,
    )?;
    if cval_eq.concl().as_eq()?.0 != *row.row_v {
        return None
    }
    ip.retarget_subject(&in_dprod, &cval_eq)
}

/// `Γ ⊢ ∀p. (p ∈ ih → p ∈ prod(A, ⋃img))`.
///
/// `ih`'s own membership condition is `∃y. (y ∈ A ∧ p = row(y))`, so this is one
/// existential elimination over the per-row fact the caller already discharged.
/// The `∃`'s body is rebuilt at a fresh variable rather than read off the
/// theorem — `Formula::forall` abstracts, so the two are equal exactly when the
/// row term is the one `derived` states its axiom with, and the `syl` below is
/// what says so.
fn subset_of_prod(
    ip: &mut Interp,
    cx: &Cx<'_>,
    x: &Term,
    ih_tm: &Term,
    outer_base: &Term,
    rows_in_prod: &Thm,
) -> Option<Thm> {
    let sums = ip.prelude.tower.sums.clone();
    let base = cx.ra.ra.base.clone();
    let (pv, yv, hole) = (ip.env.fresh_var(), ip.env.fresh_var(), ip.env.fresh_var());
    let (p, y) = (Term::var(pv), Term::var(yv));
    let row_y = row_of(&sums, base.ep, &cx.accrec, &cx.graph, x, &y);
    let prod_t = sums.prod.of(cx.a.clone(), outer_base.clone());
    let in_prod = Formula::mem(p.clone(), prod_t.clone());

    let mem_ya = Formula::mem(y.clone(), cx.a.clone());
    let eq_p = Formula::eq(p.clone(), row_y.clone());
    let body = Formula::and(mem_ya.clone(), eq_p.clone());

    let at_y = derived::inst_all(rows_in_prod, std::slice::from_ref(&y))?;
    let row_in_prod = derived::syl(&derived::and_left(mem_ya, eq_p.clone()), &at_y)?;
    let to_eq = derived::syl(
        &derived::and_right(Formula::mem(y.clone(), cx.a.clone()), eq_p),
        &derived::eq_symm_imp(&mut ip.env, p.clone(), row_y.clone()),
    )?;
    let leib =
        Thm::eq_leibniz(row_y, p.clone(), hole, Formula::mem(Term::var(hole), prod_t));
    let step = derived::hyp_mp(
        &derived::hyp_mp(&derived::a1i(&leib, body), &to_eq)?,
        &row_in_prod,
    )?;
    let all_y = crate::rec_dep::gen_all_checked(&[yv], &step)?;
    let from_ex = derived::exists_elim_imp(yv, &all_y, &in_prod)?;

    let ax = derived::inst_all(
        &base.ih_ax,
        &[cx.accrec.clone(), cx.a.clone(), cx.graph.clone(), x.clone(), p.clone()],
    )?;
    let out = derived::syl(&derived::iff_mp(&ax)?, &from_ex)?;
    let want = kernel::thm::subset(&mut ip.env, ih_tm.clone(), sums.prod.of(cx.a.clone(), outer_base.clone()));
    let all_p = crate::rec_dep::gen_all_checked(&[pv], &out)?;
    (*all_p.concl() == want).then_some(all_p)
}
