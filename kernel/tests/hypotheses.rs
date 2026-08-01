//! The hypothesis-carrying judgement: `assume`, `implies_intr`, and the side
//! conditions the other rules acquired because of them.
//!
//! # Why this shape of test
//!
//! Every assertion here pins an **exact** hypothesis set and an **exact**
//! conclusion, and the negatives are the point. A rule that fails to fire is a
//! rejection; a rule that fires when it should not is `⊢ ⊥`. Three negatives are
//! load-bearing and each was mutation-verified — the check was deleted, the test
//! was watched to fail, the check was restored:
//!
//! * [`gen_refuses_a_variable_free_in_a_hypothesis`] — delete the `occurs_free`
//!   scan in `gen_checked` and it fails.
//! * [`define_refuses_a_hypothetical_witness`] — delete the `hyps.is_empty()`
//!   guard in `define` and it fails.
//! * [`hypothesis_sets_ignore_insertion_order`] — stop `mk_union` interleaving
//!   and it fails. (It pinned `mk_hyps`'s `sort_unstable` until `Thm::mp`
//!   started merging two sorted sets instead of re-sorting their
//!   concatenation.)
//! * [`mp_merges_hypothesis_sets_exactly_as_a_sort_would`] — the differential
//!   test for that merge, against the `chain`/`sort`/`dedup` it replaced, over
//!   all 4096 pairs of subsets of six atoms.
//!
//! The file also builds `⊢ ∀x. ∃!y. (y = x)` from the primitives *using* the new
//! rules, which is both the positive control for the `define` negative and a
//! demonstration that `assume`/`implies_intr` shorten real derivations: the same
//! witness in `derived/tests/define.rs` needs `imp_refl`, `and_intro` and
//! `exists_intro` from a crate of derived combinators, and here each is three
//! lines of `assume`, `mp`, `implies_intr`.

use kernel::thm::{define, exists_unique};
use kernel::{Env, Formula, FreeVar, Term, Thm};

// ─────────────────────────────────────────────────────────────────────────────
// Small helpers, built from the primitives only — this crate has no
// dev-dependency on `derived`, deliberately.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ φ → φ`.
fn imp_refl(phi: &Formula) -> Thm { Thm::implies_intr(phi, &Thm::assume(phi.clone())) }

/// `⊢ φ` and `⊢ ψ` give `⊢ φ ∧ ψ`, where `φ ∧ ψ` is `¬(φ → ¬ψ)`.
///
/// Assume the antecedent `φ → ¬ψ`, apply it to `φ` and then to `ψ` to reach `⊥`,
/// and discharge. Hypotheses make this the three-step argument it reads as.
fn and_intro(a: &Thm, b: &Thm) -> Thm {
    let h = Formula::imp(a.concl().clone(), Formula::not(b.concl().clone()));
    let not_psi = Thm::mp(&Thm::assume(h.clone()), a).expect("mp: h applied to a");
    let bot = Thm::mp(&not_psi, b).expect("mp: ¬ψ applied to b");
    Thm::implies_intr(&h, &bot)
}

/// `⊢ body[t/y]` gives `⊢ ∃y. body`, where `∃y. body` is `¬∀y. ¬body`.
fn exists_intro(y: FreeVar, body: &Formula, t: &Term, thm: &Thm) -> Thm {
    let all_not = Formula::forall(y, Formula::not(body.clone()));
    let inst = Thm::ax_inst(all_not.clone(), t.clone()).expect("ax_inst on a ∀");
    let not_body = Thm::mp(&inst, &Thm::assume(all_not.clone())).expect("mp: instantiation");
    let bot = Thm::mp(&not_body, thm).expect("mp: ¬body[t/y] applied to body[t/y]");
    Thm::implies_intr(&all_not, &bot)
}

/// `⊢ ψ` and any `φ` give `{φ} ⊢ ψ` — the same theorem, now carrying a
/// hypothesis it does not need.
///
/// This is how the negative tests below manufacture a premise whose *conclusion*
/// is exactly right and whose hypothesis set is not empty, so that the thing
/// under test is the hypothesis set and nothing else.
fn burden(thm: &Thm, phi: &Formula) -> Thm {
    let k = Thm::ax_k(thm.concl().clone(), phi.clone()); // ⊢ ψ → (φ → ψ)
    let imp = Thm::mp(&k, thm).expect("mp: ax_k applied to the theorem");
    Thm::mp(&imp, &Thm::assume(phi.clone())).expect("mp: φ → ψ applied to the assumption")
}

/// `⊢ ∀x. ∃!y. (y = x)`, built from the primitives. The positive control for
/// [`define_refuses_a_hypothetical_witness`].
fn identity_witness(env: &mut Env, x: FreeVar, y: FreeVar) -> Thm {
    let (tx, ty) = (Term::var(x), Term::var(y));
    let phi = Formula::eq(ty.clone(), tx.clone());

    // The `∃`'s body: `φ ∧ ∀y'. (φ[y'/y] → y' = y)`, rebuilt here rather than
    // taken from the kernel, so a change to `exists_unique`'s shape shows up.
    let y3 = env.fresh_var();
    let uniq_clause =
        Formula::forall(y3, Formula::imp(phi.subst(y, &Term::var(y3)), Formula::eq(Term::var(y3), ty)));
    let body = Formula::and(phi, uniq_clause);

    // Prove the body at `y := x`: `x = x` and `∀y'. (y' = x → y' = x)`.
    let y2 = env.fresh_var();
    let uniq = Thm::gen(y2, &imp_refl(&Formula::eq(Term::var(y2), tx.clone())));
    let at_x = and_intro(&Thm::eq_refl(tx.clone()), &uniq);
    assert_eq!(at_x.concl(), &body.subst(y, &tx), "hand-built witness is not the ∃ body at x");

    Thm::gen(x, &exists_intro(y, &body, &tx, &at_x))
}

// ─────────────────────────────────────────────────────────────────────────────
// Backward compatibility: the hypothesis-free fragment must be untouched.
// ─────────────────────────────────────────────────────────────────────────────

/// Every axiom and every rule applied to hypothesis-free premises must produce a
/// theorem with an **empty** hypothesis set.
///
/// This is the whole backward-compatibility claim in one test: `derived/`'s
/// ~38 000 lines and `checker/`'s backend never call `assume`, so every theorem
/// they build lands here, and unioning empty sets is the identity.
#[test]
fn the_hypothesis_free_fragment_stays_hypothesis_free() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (tx, ty) = (Term::var(x), Term::var(y));
    let (p, q) = (Formula::mem(tx.clone(), ty.clone()), Formula::eq(tx.clone(), ty.clone()));

    let axioms = [
        Thm::ax_k(p.clone(), q.clone()),
        Thm::ax_s(p.clone(), q.clone(), p.clone()),
        Thm::ax_contra(p.clone(), q.clone()),
        Thm::ax_inst(Formula::forall(x, p.clone()), ty.clone()).expect("ax_inst"),
        Thm::ax_dist(x, Formula::mem(ty.clone(), ty.clone()), p.clone()).expect("ax_dist"),
        Thm::eq_refl(tx.clone()),
        Thm::eq_leibniz(tx.clone(), ty.clone(), x, p.clone()),
        Thm::ax_extensionality(&mut env),
        Thm::ax_pairing(&mut env),
        Thm::ax_union(&mut env),
        Thm::ax_power(&mut env),
        Thm::ax_regularity(&mut env),
        Thm::ax_tarski(&mut env),
        Thm::ax_choice(&mut env),
    ];
    for (i, t) in axioms.iter().enumerate() {
        assert!(t.hyps().is_empty(), "axiom {i} came back with hypotheses");
    }

    // And the rules, on hypothesis-free premises.
    let refl = Thm::eq_refl(tx.clone());
    let eq_xx = Formula::eq(tx.clone(), tx.clone());
    // ⊢ (x=x) → (p → (x=x)), applied to ⊢ x=x.
    let k = Thm::ax_k(eq_xx.clone(), p.clone());
    let applied = Thm::mp(&k, &refl).expect("mp on ax_k and reflexivity");
    assert_eq!(applied.concl(), &Formula::imp(p, eq_xx), "mp changed the conclusion");
    assert!(applied.hyps().is_empty(), "mp invented a hypothesis");
    assert!(Thm::gen(x, &refl).hyps().is_empty(), "gen invented a hypothesis");
    assert!(Thm::gen_checked(x, &refl).expect("gen_checked on a closed theorem").hyps().is_empty());

    // `gen` on a hypothesis-free theorem is still unconditional: the variable
    // being generalised may occur anywhere in the conclusion.
    assert_eq!(Thm::gen(x, &refl).concl(), &Formula::forall(x, Formula::eq(tx.clone(), tx)));
}

// ─────────────────────────────────────────────────────────────────────────────
// `assume` and `implies_intr`.
// ─────────────────────────────────────────────────────────────────────────────

/// `assume(φ)` is exactly `{φ} ⊢ φ` — one hypothesis, and the conclusion is the
/// hypothesis itself.
#[test]
fn assume_asserts_only_what_it_assumes() {
    let mut env = Env::new();
    let x = env.fresh_var();
    let phi = Formula::mem(Term::var(x), Term::var(x));

    let a = Thm::assume(phi.clone());
    assert_eq!(a.concl(), &phi, "assume changed the formula");
    assert_eq!(a.hyps(), std::slice::from_ref(&phi), "assume did not record exactly its assumption");

    // And it is *not* the same theorem as the hypothesis-free one, which is the
    // property that stops a hypothesis being laundered away by `==`.
    assert_ne!(a, Thm::implies_intr(&phi, &a), "a discharged theorem compared equal to the undischarged one");
}

/// Discharge: `Γ ∪ {h} ⊢ φ` becomes `Γ ⊢ h → φ`. The hypothesis leaves the set
/// and reappears as an antecedent — nothing is dropped.
#[test]
fn implies_intr_moves_a_hypothesis_into_the_formula() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (h1, h2) = (Formula::mem(Term::var(x), Term::var(y)), Formula::eq(Term::var(x), Term::var(y)));

    // {h1, h2} ⊢ h1, by weakening `assume(h1)` with `h2`.
    let both = burden(&Thm::assume(h1.clone()), &h2);
    assert_eq!(both.concl(), &h1);
    assert_eq!(both.hyps().len(), 2, "expected exactly two hypotheses");

    let discharged = Thm::implies_intr(&h2, &both);
    assert_eq!(discharged.concl(), &Formula::imp(h2.clone(), h1.clone()), "wrong discharged conclusion");
    assert_eq!(discharged.hyps(), std::slice::from_ref(&h1), "discharge removed the wrong hypothesis");

    // Discharging the last one closes the theorem entirely: `⊢ h1 → (h2 → h1)`.
    let closed = Thm::implies_intr(&h1, &discharged);
    assert_eq!(
        closed.concl(),
        &Formula::imp(h1.clone(), Formula::imp(h2, h1)),
        "wrong nesting after two discharges"
    );
    assert!(closed.hyps().is_empty(), "discharging everything left a hypothesis behind");
}

/// Discharging a hypothesis that is not there **weakens** rather than failing.
///
/// This is Isabelle's behaviour and it is sound — `Γ ⊢ φ` gives `Γ ⊢ h → φ` for
/// any `h` at all. It is pinned because it is a deliberate choice, not an
/// oversight: a caller who needs to know whether the hypothesis was present must
/// look at [`Thm::hyps`] before calling.
#[test]
fn implies_intr_of_an_absent_hypothesis_is_weakening() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::mem(Term::var(x), Term::var(y));
    let absent = Formula::eq(Term::var(y), Term::var(y));

    let a = Thm::assume(phi.clone());
    let out = Thm::implies_intr(&absent, &a);
    assert_eq!(out.concl(), &Formula::imp(absent, phi.clone()), "weakening changed the consequent");
    assert_eq!(out.hyps(), &[phi], "weakening disturbed the hypothesis set");
}

// ─────────────────────────────────────────────────────────────────────────────
// The hypothesis set is a *set*.
// ─────────────────────────────────────────────────────────────────────────────

/// Two theorems assembled from the same assumptions in **opposite orders** must
/// have identical hypothesis sets, and must compare `==`.
///
/// Mutation-verified. It used to be verified against `mk_hyps`'s
/// `sort_unstable`; since `Thm::mp` merges instead of re-sorting, the ordering
/// this test pins is `mk_union`'s, and it fails if the merge stops interleaving
/// (`if g[i] <= d[j]` → `if true`) — every hypothesis here arrives through `mp`.
/// That failure is not unsoundness but silent incompleteness — the two theorems
/// stop composing, and every later rule returns `None` a long way from the
/// cause.
#[test]
fn hypothesis_sets_ignore_insertion_order() {
    let mut env = Env::new();
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let (a, b, c) = (
        Formula::mem(Term::var(x), Term::var(y)),
        Formula::eq(Term::var(y), Term::var(z)),
        Formula::mem(Term::var(z), Term::var(z)),
    );

    let goal = Formula::eq(Term::var(x), Term::var(x));
    let base = Thm::eq_refl(Term::var(x));

    // Same three assumptions, three different orders of arrival.
    let one = burden(&burden(&burden(&base, &a), &b), &c);
    let two = burden(&burden(&burden(&base, &c), &a), &b);
    let three = burden(&burden(&burden(&base, &b), &c), &a);

    assert_eq!(one.concl(), &goal);
    assert_eq!(one.hyps().len(), 3, "expected three hypotheses");
    assert_eq!(one.hyps(), two.hyps(), "hypothesis order leaked through");
    assert_eq!(one.hyps(), three.hyps(), "hypothesis order leaked through");
    assert_eq!(one, two, "theorems with the same assumptions did not compare equal");
    assert_eq!(one, three, "theorems with the same assumptions did not compare equal");

    // The order is a function of the formulas alone, so a *fresh* environment
    // reproduces nothing about the sort — but the same formulas must still sort
    // the same way relative to each other in a second, independent assembly.
    let again = burden(&burden(&burden(&base, &b), &a), &c);
    assert_eq!(one.hyps(), again.hyps(), "canonical order is not reproducible");
}

/// The same assumption reaching a theorem twice must be recorded once, and
/// discharging it must remove **every** copy.
#[test]
fn hypothesis_sets_deduplicate() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let h = Formula::mem(Term::var(x), Term::var(y));
    let other = Formula::eq(Term::var(y), Term::var(y));

    // `mp` merges two premises that both assume `h`.
    let assumed = Thm::assume(h.clone()); // {h} ⊢ h
    let k = burden(&Thm::ax_k(h.clone(), other.clone()), &h); // {h} ⊢ h → (other → h)
    let merged = Thm::mp(&k, &assumed).expect("mp on two premises assuming h");
    assert_eq!(merged.hyps(), std::slice::from_ref(&h), "the shared hypothesis was recorded twice");

    let discharged = Thm::implies_intr(&h, &merged);
    assert!(discharged.hyps().is_empty(), "discharge left a duplicate copy behind");
}

/// `mp` takes the **union**: neither premise's assumptions may be lost.
#[test]
fn mp_unions_the_hypothesis_sets() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let (g, d) = (Formula::mem(Term::var(x), Term::var(y)), Formula::mem(Term::var(y), Term::var(x)));
    let phi = Formula::eq(Term::var(x), Term::var(x));

    // Γ = {g} ⊢ φ → φ, and Δ = {d} ⊢ φ.
    let left = burden(&imp_refl(&phi), &g);
    let right = burden(&Thm::eq_refl(Term::var(x)), &d);
    let out = Thm::mp(&left, &right).expect("mp on φ → φ and φ");

    assert_eq!(out.concl(), &phi, "mp changed the conclusion");
    assert_eq!(out.hyps().len(), 2, "mp lost a hypothesis");
    assert!(out.hyps().contains(&g) && out.hyps().contains(&d), "mp lost a hypothesis");
}

// ─────────────────────────────────────────────────────────────────────────────
// `gen`'s side condition — the soundness hole this change would otherwise open.
// ─────────────────────────────────────────────────────────────────────────────

/// **The classic natural-deduction side condition.** From `{x ∈ y} ⊢ x ∈ y` one
/// must not conclude `{x ∈ y} ⊢ ∀x. x ∈ y`.
///
/// Mutation-verified: deleting the `occurs_free` scan in `gen_checked` makes
/// this test fail. Without the check the kernel proves that everything is a
/// member of `y` from the assumption that one thing is, and `⊥` follows by
/// instantiating at a non-member.
#[test]
fn gen_refuses_a_variable_free_in_a_hypothesis() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::mem(Term::var(x), Term::var(y));
    let assumed = Thm::assume(phi.clone());

    assert!(Thm::gen_checked(x, &assumed).is_none(), "gen generalised a variable free in a hypothesis");

    // The panicking wrapper must not be a way around the same check.
    let a = assumed.clone();
    assert!(std::panic::catch_unwind(move || Thm::gen(x, &a)).is_err(), "gen's wrapper skipped the side condition");

    // `y` is free in the hypothesis too, so it is refused for the same reason.
    assert!(Thm::gen_checked(y, &assumed).is_none(), "gen generalised a second variable free in a hypothesis");

    // Discharging first makes it legitimate, and *that* is the intended route:
    // `⊢ ∀x. (x ∈ y → x ∈ y)` is true, `{x ∈ y} ⊢ ∀x. x ∈ y` is not.
    let discharged = Thm::implies_intr(&phi, &assumed);
    let generalised = Thm::gen_checked(x, &discharged).expect("gen refused a discharged theorem");
    assert_eq!(generalised.concl(), &Formula::forall(x, Formula::imp(phi.clone(), phi)));
    assert!(generalised.hyps().is_empty());
}

/// A variable free in the *conclusion* but in no hypothesis is fine — that is
/// the case the rule exists for, and refusing it would make the kernel useless.
#[test]
fn gen_allows_a_variable_absent_from_the_hypotheses() {
    let mut env = Env::new();
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let h = Formula::mem(Term::var(y), Term::var(z));
    let concl = Formula::eq(Term::var(x), Term::var(x));

    let t = burden(&Thm::eq_refl(Term::var(x)), &h); // {y ∈ z} ⊢ x = x
    let g = Thm::gen_checked(x, &t).expect("gen refused a variable that is free in no hypothesis");
    assert_eq!(g.concl(), &Formula::forall(x, concl), "wrong quantified conclusion");
    assert_eq!(g.hyps(), &[h], "gen disturbed the hypothesis set");

    // But the hypothesis's own variables are still refused.
    assert!(Thm::gen_checked(y, &t).is_none(), "gen generalised over a hypothesis variable");
    assert!(Thm::gen_checked(z, &t).is_none(), "gen generalised over a hypothesis variable");
}

/// The side condition must look at **every** hypothesis, not just the first.
///
/// A scan that stops early — or that checks only one operand of a merge — would
/// pass the test above and fail here. This is the shape of mistake the
/// above-kernel layer hit: checking a side condition against one premise's set
/// rather than against the merged one.
#[test]
fn gen_scans_the_whole_hypothesis_set() {
    let mut env = Env::new();
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let harmless = Formula::eq(Term::var(z), Term::var(z));
    let dangerous = Formula::mem(Term::var(x), Term::var(y));

    let t = burden(&burden(&Thm::eq_refl(Term::var(x)), &harmless), &dangerous);
    assert_eq!(t.hyps().len(), 2);
    assert!(Thm::gen_checked(x, &t).is_none(), "gen missed a hypothesis mentioning x");

    // Order of arrival must not matter, since the set is canonicalised: the
    // dangerous hypothesis may sort either side of the harmless one.
    let swapped = burden(&burden(&Thm::eq_refl(Term::var(x)), &dangerous), &harmless);
    assert_eq!(t.hyps(), swapped.hyps());
    assert!(Thm::gen_checked(x, &swapped).is_none(), "gen missed a hypothesis mentioning x");
}

/// The other route to an illegitimate generalisation is still shut: `ax_dist`'s
/// own `x ∉ FV(φ)` is a **separate** condition and is unaffected by this change.
///
/// Together with `gen`'s condition this closes the attack: `{x ∈ y} ⊢ x ∈ y`
/// cannot become `∀x. x ∈ y` by generalising, and cannot become it by
/// discharging to `⊢ (x ∈ y) → (x ∈ y)` and pushing the quantifier inside
/// either.
#[test]
fn the_two_variable_conditions_are_independent() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::mem(Term::var(x), Term::var(y));

    // `ax_dist` at the discharged theorem's antecedent: x IS free in φ.
    assert!(Thm::ax_dist(x, phi.clone(), phi.clone()).is_none(), "ax_dist ignored its own side condition");

    // And `ax_dist` still fires where it is legitimate, with no hypotheses.
    let w = env.fresh_var();
    let free_of_x = Formula::mem(Term::var(w), Term::var(y));
    let d = Thm::ax_dist(x, free_of_x, phi).expect("ax_dist rejected a valid instance");
    assert!(d.hyps().is_empty(), "an axiom came back with hypotheses");
}

// ─────────────────────────────────────────────────────────────────────────────
// `define` must not mint a symbol from a hypothetical witness.
// ─────────────────────────────────────────────────────────────────────────────

/// A witness proved under an assumption must be **rejected**, and the identical
/// witness without the assumption must be **accepted**.
///
/// The pair is the test: the only difference between the two calls is the
/// witness's hypothesis set, so nothing else can explain the rejection.
///
/// Mutation-verified: deleting the `hyps.is_empty()` guard in `define` makes the
/// rejection half fail. Structurally this is the recorded SECOND SOUNDNESS BUG —
/// something proved under a side condition becoming an unconditional symbol.
#[test]
fn define_refuses_a_hypothetical_witness() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::eq(Term::var(y), Term::var(x));

    let good = identity_witness(&mut env, x, y);
    assert!(good.hyps().is_empty(), "the control witness is not hypothesis-free");
    assert_eq!(
        good.concl(),
        &Formula::forall(x, exists_unique(&mut env, y, &phi)),
        "the control witness does not prove the required ∃!"
    );

    // The same conclusion, now carrying an irrelevant assumption.
    let junk = Formula::mem(Term::var(x), Term::var(x));
    let hypothetical = burden(&good, &junk);
    assert_eq!(hypothetical.concl(), good.concl(), "burdening changed the conclusion");
    assert_eq!(hypothetical.hyps(), &[junk], "burdening did not add exactly one hypothesis");

    assert!(
        define(&mut env, &[x], y, phi.clone(), &hypothetical).is_none(),
        "define minted a symbol from a witness proved under an assumption"
    );

    // The control: hypothesis-free, same everything else, must succeed.
    let (f, axiom) = define(&mut env, &[x], y, phi, &good).expect("define rejected a valid witness");
    let expected = Formula::forall(x, Formula::eq(Term::apply(f, vec![Term::var(x)]), Term::var(x)));
    assert_eq!(axiom.concl(), &expected, "unexpected defining axiom");
    assert!(axiom.hyps().is_empty(), "a defining axiom came back with hypotheses");
}

/// Discharging the assumption first is the sanctioned route, and it works —
/// provided the caller actually proves the `∃!` outright.
///
/// This pins that the rejection above is not a dead end: `define` refuses the
/// hypothetical witness, and the caller's remedy is `implies_intr` plus a proof
/// of the antecedent, not a way around the check.
#[test]
fn define_accepts_a_witness_whose_assumption_was_discharged() {
    let mut env = Env::new();
    let (x, y) = (env.fresh_var(), env.fresh_var());
    let phi = Formula::eq(Term::var(y), Term::var(x));

    let junk = Formula::mem(Term::var(x), Term::var(x));
    let good = identity_witness(&mut env, x, y);
    let hypothetical = burden(&good, &junk);

    // `⊢ junk → ∀x. ∃!y. y = x`. Still not what `define` wants — its conclusion
    // is now an implication, not the `∃!` statement — so it is refused too.
    let discharged = Thm::implies_intr(&junk, &hypothetical);
    assert!(discharged.hyps().is_empty());
    assert!(
        define(&mut env, &[x], y, phi.clone(), &discharged).is_none(),
        "define accepted an implication in place of the required ∃!"
    );

    // Recovering the real thing means proving `junk` — which is not provable —
    // or, as here, using the unburdened witness.
    assert!(define(&mut env, &[x], y, phi, &good).is_some(), "define rejected the unburdened witness");
}

// ─────────────────────────────────────────────────────────────────────────────
// The canonical order itself.
// ─────────────────────────────────────────────────────────────────────────────

/// The order on formulas must be **total, deterministic and consistent with
/// `==`** — the three properties `sort_unstable` + `dedup` rely on.
///
/// Consistency with `==` is the one worth pinning: `dedup` removes only
/// *adjacent* equal elements, so if `cmp` could return `Equal` for distinct
/// formulas the set would silently lose a hypothesis, and if it could return
/// non-`Equal` for equal ones the set would silently keep a duplicate.
#[test]
fn the_formula_order_is_total_and_agrees_with_equality() {
    let mut env = Env::new();
    let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
    let fs = [
        Formula::false_(),
        Formula::mem(Term::var(x), Term::var(y)),
        Formula::mem(Term::var(y), Term::var(x)),
        Formula::eq(Term::var(x), Term::var(y)),
        Formula::forall(z, Formula::mem(Term::var(z), Term::var(x))),
        Formula::imp(Formula::mem(Term::var(x), Term::var(y)), Formula::false_()),
    ];

    for a in &fs {
        for b in &fs {
            assert_eq!(
                a.cmp(b) == core::cmp::Ordering::Equal,
                a == b,
                "the order disagrees with equality, which breaks dedup"
            );
            assert_eq!(a.cmp(b), b.cmp(a).reverse(), "the order is not antisymmetric");
            for c in &fs {
                if a <= b && b <= c {
                    assert!(a <= c, "the order is not transitive");
                }
            }
        }
    }

    // Two independently built copies of the same formula compare equal and sort
    // identically — this is what makes the order a function of syntax alone.
    let again = Formula::forall(z, Formula::mem(Term::var(z), Term::var(x)));
    assert_eq!(again.cmp(&fs[4]), core::cmp::Ordering::Equal, "a rebuilt formula did not compare equal");
}

/// `mp`'s union is a **merge of two sorted lists**, not a re-sort of their
/// concatenation (`PERF-REVIEW.md` F4). It must agree with the re-sort it
/// replaced on every input, so this is a differential test against exactly the
/// old implementation — `chain`, `sort`, `dedup` — over **all 4096 pairs of
/// subsets** of six distinct atoms.
///
/// Six atoms rather than two because the ways a merge goes wrong are ways of
/// interleaving: a run in one list while the other waits, a tie in the middle
/// rather than at an end, one list exhausting first, and either list empty.
/// Enumerating the subsets covers all of those without guessing which matters —
/// and the canonical order here is `Formula`'s hash order, so the atoms sit in
/// an order nothing in the test controls, which is the point.
///
/// The second assertion is the soundness half stated separately, because it is
/// a different property from agreeing with the old code: **no hypothesis may be
/// dropped.** A theorem missing a hypothesis is stronger than its premises
/// justify. Losing the *order* is only incompleteness; losing an element is not.
#[test]
fn mp_merges_hypothesis_sets_exactly_as_a_sort_would() {
    let mut env = Env::new();
    let vars: Vec<Term> = (0..6).map(|_| Term::var(env.fresh_var())).collect();
    let atoms: Vec<Formula> = (0..6).map(|i| Formula::mem(vars[i].clone(), vars[(i + 1) % 6].clone())).collect();
    let phi = Formula::eq(vars[0].clone(), vars[0].clone());

    let mut cases = 0;
    for gm in 0u32..64 {
        for dm in 0u32..64 {
            let pick = |m: u32| -> Vec<Formula> { (0..6).filter(|i| m >> i & 1 == 1).map(|i| atoms[i].clone()).collect() };
            let (g, d) = (pick(gm), pick(dm));
            // Γ ⊢ φ → φ and Δ ⊢ φ, with Γ and Δ arriving in index order — which
            // is *not* the canonical order, so `mp` is really merging.
            let left = g.iter().fold(imp_refl(&phi), |t, h| burden(&t, h));
            let right = d.iter().fold(Thm::eq_refl(vars[0].clone()), |t, h| burden(&t, h));
            let out = Thm::mp(&left, &right).expect("mp on φ → φ and φ");

            let mut want: Vec<Formula> = left.hyps().iter().chain(right.hyps()).cloned().collect();
            want.sort();
            want.dedup();
            assert_eq!(out.concl(), &phi, "mp changed the conclusion");
            assert_eq!(out.hyps(), want.as_slice(), "merge disagreed with sort+dedup at {gm:#08b}/{dm:#08b}");
            for h in g.iter().chain(&d) {
                assert!(out.hyps().contains(h), "mp dropped a hypothesis at {gm:#08b}/{dm:#08b}");
            }
            cases += 1;
        }
    }
    assert_eq!(cases, 64 * 64);
}

/// The merged set is **canonical**: sorted and duplicate-free, which is what
/// makes `Thm`'s `hyps` a set and what every later `==` on two theorems relies
/// on. A merge that emitted a correct multiset in the wrong order would pass
/// the "nothing dropped" half of the test above and still break composition.
#[test]
fn mp_leaves_the_hypothesis_set_canonical() {
    let mut env = Env::new();
    let vars: Vec<Term> = (0..5).map(|_| Term::var(env.fresh_var())).collect();
    let atoms: Vec<Formula> = (0..5).map(|i| Formula::mem(vars[i].clone(), vars[(i + 2) % 5].clone())).collect();
    let phi = Formula::eq(vars[0].clone(), vars[0].clone());

    for gm in 0u32..32 {
        for dm in 0u32..32 {
            let pick = |m: u32| -> Vec<Formula> { (0..5).filter(|i| m >> i & 1 == 1).map(|i| atoms[i].clone()).collect() };
            let left = pick(gm).iter().fold(imp_refl(&phi), |t, h| burden(&t, h));
            let right = pick(dm).iter().fold(Thm::eq_refl(vars[0].clone()), |t, h| burden(&t, h));
            let hyps = Thm::mp(&left, &right).expect("mp on φ → φ and φ").hyps().to_vec();
            assert!(hyps.windows(2).all(|w| w[0] < w[1]), "merged set is not strictly ascending: {hyps:?}");
        }
    }
}
