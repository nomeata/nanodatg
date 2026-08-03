//! **A function on `Sum_n(A⃗)`, restricted to one summand** — the branch
//! `f|ⱼ = { ⟨z, app(f, Injⱼ(z))⟩ : z ∈ Aⱼ }`.
//!
//! # The consumer, and the obligation it discharges
//!
//! `#37`'s general fibre is `Sum_m(A⃗)` with `Aⱼ = Σ(z::γⱼ)`
//! ([`crate::inductive::carrier::fibre_values`]), so a constructor's recursive
//! arguments arrive **packed into one function** on that sum
//! ([`crate::recarg::RecArg::general`]). Lean's recursor does not see the pack:
//! its minor premise for a function-typed field takes *the field's own
//! function*, on `Aⱼ`, and one induction hypothesis per field, also on `Aⱼ`.
//! The packed step of [`crate::inductive::step`] is defined at an **arbitrary**
//! `f ∈ fs(Sum_m(A⃗), W)` — that is what `step_typed` quantifies over — so the
//! field cannot be recovered by naming the variable a constructor was applied
//! to. It has to be projected out of `f`, and that projection is this file.
//!
//! At `γⱼ = ∅` nothing here is reached: `Aⱼ` is `1`, the field is the single
//! value `app(f, Injⱼ(•))`, and the plain spelling stands. **The two spellings
//! are chosen per recursive argument, off `CtorSpec::rec_doms`**, exactly as
//! [`crate::recarg`]'s two entry points are chosen per constructor.
//!
//! # What it is, and why it costs almost nothing
//!
//! `Injⱼ` is a **unary function symbol** ([`super::ISumSyms::inj_sym`]), so
//! `x ↦ app(f, Injⱼ(x))` is an abbreviation `Bⱼ(f,x)` of arity 2 and the
//! restriction is the lambda graph [`crate::funcs::lambda_n`] builds over it.
//! Both facts a consumer needs then come off the existing lambda apparatus
//! rather than from a fresh Replacement argument:
//!
//! | fact | from |
//! |---|---|
//! | `app(f|ⱼ, z) = Bⱼ(f,z)` for `z ∈ Aⱼ` | [`crate::funcs::beta_conditional_n`] |
//! | `f|ⱼ ∈ fs(Aⱼ, C)` when the body lands in `C` | [`crate::ext::lam_in_funspace_n`] |
//!
//! and the abbreviation is unfolded once, here, so that **no exported
//! statement mentions `Bⱼ`**. That is the whole construction: one
//! [`crate::define_abbrev`] and one [`crate::funcs::lambda_n`] per depth `j`,
//! and no new axiom.
//!
//! The alternative — a Replacement symbol of its own, with `Injⱼ` inlined in
//! the body — would have had to re-derive `beta_conditional_n`'s and
//! `lam_in_funspace_n`'s arguments at a second shape. They are ~250 lines
//! between them and neither is about injections.
//!
//! # Interface
//!
//! [`Branch::new`] mints the symbols for one depth `j` and derives
//!
//! ```text
//! ⊢ ∀f ∀A ∀z. (z ∈ A → app(restrⱼ(f,A), z) = app(f, Injⱼ(z)))          [Branch::app]
//! ```
//!
//! with [`Branch::of`] the term `restrⱼ(f,A)`. **The domain is a parameter**,
//! not read off `f` — there is no domain operator in this crate, and every
//! consumer has `Aⱼ` to hand — which is [`crate::wrec::comp_of`]'s choice for
//! the same reason and keeps the operation total.
//!
//! [`branch_in_funspace`] is the typing rule **at the shape its consumers
//! hold**:
//!
//! ```text
//! ⊢ ∀A₀ … ∀A_{n-1} ∀S ∀f. (f ∈ fs(Sum_n(A⃗), S) → restrⱼ(f, Aⱼ) ∈ fs(Aⱼ, S))
//! ```
//!
//! Not the pointwise `(∀z ∈ Aⱼ. app(f,Injⱼ z) ∈ S) → …` that
//! [`crate::ext::lam_in_funspace_n`] hands back: all four consumers —
//! [`crate::inductive::typed`], [`crate::inductive::iota`],
//! [`crate::inductive::rect`] and the dependent recursor — hold a *function
//! space membership on the whole fibre* and nothing weaker, because that is
//! what `step_typed` gives them. Handing back the pointwise form would make
//! each of them discharge the same two lines.
//!
//! # Non-vacuity
//!
//! [`branch_in_funspace`] alone is satisfied by `f|ⱼ := ∅` on an empty `Aⱼ`.
//! [`Branch::app`] rules that out: it says the restriction *computes*, at
//! every point of `Aⱼ`, to the value `f` takes at that point's injection. The
//! two together are what makes `f|ⱼ = gⱼ` provable by
//! [`crate::ext::funspace_ext`] when `f` is a
//! [`RecArg::general`](crate::recarg::RecArg::general) dispatcher, which is the
//! ι rule's use.

use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};

use crate::ext::lam_in_funspace_n;
use crate::funcs::{beta_conditional_n, lambda_n};
use crate::sums::Sums;
use crate::wrec::hyp_eq_trans;
use crate::{
    a1i, and_left, and_right, define_abbrev, eq_symm, gen_all, hyp_and, hyp_mp, inst_all, syl,
    uncurry,
};

/// The restriction operator at one injection depth: the body abbreviation, the
/// lambda graph, and the two facts about them stated without the abbreviation.
///
/// One per depth `j` and **independent of the arity** — `Injⱼ(a)` mentions
/// neither `n` nor any summand ([`super::symbols`]'s cache table), so the same
/// symbol restricts a function on `Sum_3(A⃗)` and one on `Sum_7(A⃗)`. Only
/// [`branch_in_funspace`] is keyed by the pair.
pub struct Branch {
    /// The injection depth this restricts along.
    pub depth: usize,
    /// `Bⱼ(f,x) = app(f, Injⱼ(x))`, arity 2 — the lambda's body. Exposed only
    /// because [`Branch::graph_ax`] and [`Branch::lam_in_funspace`] are stated
    /// over it; nothing else should need it.
    pub body: FnSym,
    /// `⊢ ∀f ∀x. Bⱼ(f,x) = app(f, Injⱼ(x))`.
    pub body_ax: Thm,
    /// `restrⱼ(f, A) = { ⟨x, Bⱼ(f,x)⟩ : x ∈ A }`, arity 2.
    pub graph: FnSym,
    /// `⊢ ∀f ∀A ∀y. (y ∈ restrⱼ(f,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, Bⱼ(f,x)⟩))`.
    pub graph_ax: Thm,
    /// `⊢ ∀f ∀A ∀z. (z ∈ A → app(restrⱼ(f,A), z) = app(f, Injⱼ(z)))` — the
    /// abbreviation already unfolded.
    pub app: Thm,
    /// `⊢ ∀f ∀A ∀C. ((∀x. (x ∈ A → Bⱼ(f,x) ∈ C)) → restrⱼ(f,A) ∈ fs(A,C))` —
    /// the raw lambda typing rule, over the body symbol.
    /// [`branch_in_funspace`] is what consumers want.
    pub lam_in_funspace: Thm,
}

impl Branch {
    /// Mint the two symbols for depth `j` and derive [`Branch::app`].
    ///
    /// `inj` must be [`super::ISumSyms::inj_sym`] at `depth`; it is checked to
    /// be unary, which is the only property of it this construction uses —
    /// everything else about the injections stays in [`super::symbols`].
    pub fn new(env: &mut Env, s: &Sums, inj: FnSym, depth: usize) -> Option<Branch> {
        if inj.arity() != 1 {
            return None
        }
        let ap = &s.ap;
        let (fv, xv) = (env.fresh_var(), env.fresh_var());
        let (tf, tx) = (Term::var(fv), Term::var(xv));
        let value = ap.apply(tf, Term::apply(inj, vec![tx]));
        let (body, body_ax) = define_abbrev(env, &[fv, xv], &value)?;
        let (graph, graph_ax) = lambda_n(env, ap, body)?;
        let beta = beta_conditional_n(env, ap, body, graph, &graph_ax)?;
        let lam_in_funspace = lam_in_funspace_n(env, ap, &s.prod, &s.fs, body, graph, &graph_ax)?;

        // ── unfold `Bⱼ` out of the computation rule ─────────────────────────
        let (gv, av, zv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        let (tg, ta, tz) = (Term::var(gv), Term::var(av), Term::var(zv));
        let at = inst_all(&beta, &[tg.clone(), ta.clone(), tz.clone()])?;
        let unfold = inst_all(&body_ax, &[tg.clone(), tz.clone()])?;
        let mem_z = Formula::mem(tz.clone(), ta.clone());
        let out = hyp_eq_trans(env, &at, &a1i(&unfold, mem_z.clone()))?;
        let want = Formula::imp(
            mem_z,
            Formula::eq(
                ap.apply(Term::apply(graph, vec![tg.clone(), ta]), tz.clone()),
                ap.apply(tg, Term::apply(inj, vec![tz])),
            ),
        );
        if *out.concl() != want {
            return None
        }
        Some(Branch {
            depth,
            body,
            body_ax,
            graph,
            graph_ax,
            app: gen_all(&[gv, av, zv], &out),
            lam_in_funspace,
        })
    }

    /// The term `restrⱼ(f, A)`.
    pub fn of(&self, f: Term, a: Term) -> Term { Term::apply(self.graph, vec![f, a]) }
}

/// `⊢ ∀A ∀B ∀f ∀x. ((f ∈ fs(A,B) ∧ x ∈ A) → app(f,x) ∈ B)` — the statement
/// [`branch_in_funspace`] requires of the `app_mem` it is handed.
///
/// Rebuilt rather than assumed: `app_mem` arrives as a bare `&Thm` and is
/// `mp`-ed against below, so a theorem with the wrong conclusion — or with a
/// sequent hypothesis — would ride into a result this file's header states
/// `⊢ …`. This is [`crate::ext::funspace_app_mem`]'s conclusion.
fn app_mem_stmt(env: &mut Env, s: &Sums) -> Formula {
    let vs: Vec<FreeVar> = (0..4).map(|_| env.fresh_var()).collect();
    let (ta, tb, tf, tx) =
        (Term::var(vs[0]), Term::var(vs[1]), Term::var(vs[2]), Term::var(vs[3]));
    let body = Formula::imp(
        Formula::and(
            Formula::mem(tf.clone(), s.fs.of(ta.clone(), tb.clone())),
            Formula::mem(tx.clone(), ta),
        ),
        Formula::mem(s.ap.apply(tf, tx), tb),
    );
    vs.into_iter().rev().fold(body, |acc, v| Formula::forall(v, acc))
}

/// `⊢ ∀A₀ … ∀A_{n-1} ∀S ∀f. (f ∈ fs(Sum_n(A⃗), S) → restrⱼ(f, Aⱼ) ∈ fs(Aⱼ, S))`
/// — **the restriction of a function on the sum is a function on the summand**.
///
/// `branch` must be [`Branch::new`] at `j` over `syms`' own `Injⱼ`, and
/// `app_mem` [`crate::ext::funspace_app_mem`] over the same [`Sums`]; both are
/// checked. `None` when `j ≥ n`, when [`super::ISumSyms::ensure`] has not
/// reached arity `n`, or when either check fails.
///
/// Two steps and no case analysis: `Injⱼ(x) ∈ Sum_n(A⃗)` for `x ∈ Aⱼ`
/// ([`super::ISumSyms::inj_mem`]) puts `app(f, Injⱼ(x))` in `S`, which is the
/// body condition [`crate::ext::lam_in_funspace_n`] asks for.
pub fn branch_in_funspace(
    env: &mut Env,
    s: &Sums,
    syms: &super::ISumSyms,
    branch: &Branch,
    app_mem: &Thm,
    n: usize,
    j: usize,
) -> Option<Thm> {
    if j >= n || branch.depth != j || !syms.is_over(s) {
        return None
    }
    let want = app_mem_stmt(env, s);
    if !crate::establishes(app_mem, &want) {
        return None
    }
    let ap = &s.ap;
    let avs: Vec<FreeVar> = (0..n).map(|_| env.fresh_var()).collect();
    let as_: Vec<Term> = avs.iter().map(|v| Term::var(*v)).collect();
    let (sv, fv, xv) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (ts, tf, tx) = (Term::var(sv), Term::var(fv), Term::var(xv));

    let sum = syms.sum(&as_)?;
    let h = Formula::mem(tf.clone(), s.fs.of(sum.clone(), ts.clone()));
    let mem_x = Formula::mem(tx.clone(), as_[j].clone());
    let k = Formula::and(h.clone(), mem_x.clone());
    let k_h = and_left(h.clone(), mem_x.clone());
    let k_x = and_right(h.clone(), mem_x.clone());

    // `x ∈ Aⱼ → Injⱼ(x) ∈ Sum_n(A⃗)`, then `app(f, Injⱼ(x)) ∈ S`.
    let inj_x = syms.inj(j, tx.clone())?;
    let mut inj_args = as_.clone();
    inj_args.push(tx.clone());
    let k_inj = syl(&k_x, &inst_all(syms.inj_mem(n, j)?, &inj_args)?)?;
    let am = inst_all(app_mem, &[sum, ts.clone(), tf.clone(), inj_x.clone()])?;
    let k_val = hyp_mp(&a1i(&am, k.clone()), &hyp_and(&k_h, &k_inj)?)?;

    // …which is `Bⱼ(f,x) ∈ S`, the body condition.
    let bx = inst_all(&branch.body_ax, &[tf.clone(), tx.clone()])?;
    let body_x = Term::apply(branch.body, vec![tf.clone(), tx.clone()]);
    let hole = env.fresh_var();
    let leib = Thm::eq_leibniz(
        ap.apply(tf.clone(), inj_x),
        body_x.clone(),
        hole,
        Formula::mem(Term::var(hole), ts.clone()),
    );
    let k_body = hyp_mp(&a1i(&Thm::mp(&leib, &eq_symm(env, &bx)?)?, k.clone()), &k_val)?;

    // Generalise over `x` under `h`, and feed the lambda's own typing rule.
    let inner = Formula::imp(mem_x, Formula::mem(body_x, ts.clone()));
    let h_all = Thm::mp(
        &Thm::ax_dist(xv, h.clone(), inner)?,
        &Thm::gen(xv, &uncurry(&k_body)?),
    )?;
    let rule = inst_all(&branch.lam_in_funspace, &[tf.clone(), as_[j].clone(), ts.clone()])?;
    let out = syl(&h_all, &rule)?;

    let want = Formula::imp(
        h,
        Formula::mem(
            branch.of(tf, as_[j].clone()),
            s.fs.of(as_[j].clone(), ts),
        ),
    );
    if *out.concl() != want {
        return None
    }
    let mut quant = avs;
    quant.push(sv);
    quant.push(fv);
    Some(gen_all(&quant, &out))
}
