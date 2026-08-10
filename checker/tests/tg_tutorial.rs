//! End-to-end tests for the Tarski–Grothendieck backend.
//!
//! These assert something stronger than "the checker accepted the file": they
//! assert that for the listed tutorial exports, **every** definitional-equality
//! step was discharged by a real kernel derivation, with no gaps. That is the
//! property the whole project exists to establish, so it is worth a test that
//! fails the moment a step silently starts being taken on trust.
//!
//! Only meaningful with `--features tg`; otherwise the backend is
//! `NullCertifier` and there is nothing to check.

#![cfg(feature = "tg")]

use std::path::{Path, PathBuf};
use std::process::Command;

// SKIP is not PASS: 20 of the tests below return early when `vendor/arena-tests`
// is absent, and cargo reports every one of them `ok`. See ci/skip-guard.rs.
#[path = "../../ci/skip-guard.rs"]
mod skip_guard;

fn corpus() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("vendor/arena-tests") }

/// A temp path no other test can collide with.
///
/// The config paths here used to be keyed on the process id alone, which is
/// the *same* for every test in the binary — and `cargo test` runs them in
/// parallel. Two tests writing their config to one path is a race that shows
/// up as an unrelated assertion failing, and it did, the moment the general
/// path's tests added four more concurrent report runs. Keyed on a per-call
/// counter as well, it cannot.
fn tmp_cfg(tag: &str, export: &Path) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    std::env::temp_dir().join(format!(
        "nanodatg-{tag}-{}-{}-{}.json",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed),
        export.file_stem().unwrap_or_default().to_string_lossy(),
    ))
}

/// Run one export and return (accepted, derived_count, gap_count).
fn check(export: &Path) -> (bool, u64, u64) {
    let cfg_path = tmp_cfg("tg", export);
    let cfg = format!(
        r#"{{"export_file_path": {},
             "unpermitted_axiom_hard_error": false,
             "unsafe_permit_all_axioms": true,
             "nat_extension": true,
             "string_extension": true,
             "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn checker");
    let _ = std::fs::remove_file(&cfg_path);

    let text = String::from_utf8_lossy(&out.stderr);
    let grab = |label: &str| -> u64 {
        text.lines()
            .find(|l| l.trim_start().starts_with(label))
            .and_then(|l| l.split_whitespace().last())
            .and_then(|n| n.parse().ok())
            .unwrap_or(u64::MAX)
    };
    (out.status.success(), grab("derived (real kernel Thm)"), grab("TOTAL gaps"))
}

/// Tutorial exports the TG kernel can currently discharge completely.
///
/// This is the **inductive-free fragment**: exports 001–032, everything before
/// `033_empty` introduces the first `inductive`. Every one of them is derived
/// with no gaps, and — since a conditional certificate reaching the checker is
/// itself counted as a gap — with no undischarged assumptions either.
///
/// They exercise `Sort`, `Pi`/arrow types, dependent types, constants, `let`,
/// the level algebra and weak-head normalisation of foralls, plus beta.
///
/// `006` and `007` both reduce `(λ x y : Type. x) Prop (Prop → Prop)` in a
/// single two-argument contraction. The first argument is a sort, so its domain
/// premise is `x ∈ U(x)`; the second is an arrow, and needs
/// `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧`. A non-dependent `Pi` is interpreted as the
/// constant-fibre dependent product — `mini`'s clause, one symbol per corpus —
/// and the membership is `derived::funspace`'s `⊢ ∀a. fs(a,a) ∈ U(a)` carried
/// across `TgBackend::dprod_fs_eq`, the one seam between the interpretation's
/// `dprod` and the library's `fs` vocabulary.
///
/// `027`–`029` are the Church-numeral encodings, and they are the ones that
/// need Lean's **lambda typing rule**: their beta arguments are lambdas and
/// applications of defined constants, so the domain premise is discharged by
/// `lam_in_funspace_n`/`lam_in_dprod_n` and by reducing an obligation to the
/// typing of the locals it mentions. See `tg`'s module docs.
const FULLY_DERIVED: &[&str] = &[
    "001_basicDef",
    "003_arrowType",
    "004_dependentType",
    "005_constType",
    "006_betaReduction",
    "007_betaReduction2",
    "008_forallSortWhnf",
    "012_levelComp1",
    "013_levelComp2",
    "014_levelComp3",
    "015_levelParams",
    "017_levelComp4",
    "018_levelComp5",
    "019_imax1",
    "020_imax2",
    "021_levelMaxComm",
    "022_levelMaxAssoc",
    "023_levelMaxIdem",
    "024_levelMaxAbsorb",
    "025_inferVar",
    "026_defEqLambda",
    "027_peano1",
    // `028_peano2` and `029_peano3` spent one milestone in [`GAP_BUDGET`],
    // because the interpretation stopped guessing at a universe parameter and
    // their `Π`s are exactly the case it stopped guessing about. They are back,
    // and the reason is the **level-instantiation pre-pass**
    // (`checker/src/instantiations.rs`): the declarations are now checked at a
    // ground instantiation, `imax u (imax …)` simplifies to a numeral, and one
    // clause of §6.2 applies instead of neither. Both are 0 gaps *and* 0
    // escapes again, which is the acceptance test for that whole design.
    "028_peano2",
    "029_peano3",
    "030_letType",
    "031_letTypeDep",
    "032_letRed",
];

/// Exports that still contain a gap, with the reason. Listing them explicitly
/// means a *newly* incomplete file shows up as a failure rather than going
/// unnoticed — and that closing a gap shows up too, as an unexpected pass.
///
/// `073_boolRecEqns` used to head this list — it is where a recursor first
/// meets a constructor — and has moved to [`RECURSOR_DERIVED`]. `N.rec` is now
/// wired too, and `075_nRecReduction` is down to four gaps, none of them iota:
/// what is left there is `pi_cong`'s extensionality route and one escaping
/// certificate. `List.rec` has no curried interpretation yet.
const HAS_GAPS: &[&str] = &["075_nRecReduction", "076_listRecReduction"];

/// The gap budget for the files that still have gaps — a **ratchet**, not a
/// target. Each number is what the file measures today; the test fails if a
/// change makes it worse, so a regression in the interpretation shows up as a
/// failure rather than as a number nobody re-read.
///
/// `073_boolRecEqns` was at 24 before `Bool` was interpreted as a W-type, of
/// which 12 were typing obligations about `Bool.true`/`Bool.false` escaping to
/// the boundary undischarged; those 12 are gone, and 2 of the remaining 12 are
/// the ι rule itself. See `INDUCTIVES.md`.
///
/// `075_nRecReduction` was at 74 before `N` was interpreted, and is at 72
/// after. That small a move is itself the measurement: unlike `073`, this
/// file's gaps are dominated by `N.rec` — an opaque constant — and by the
/// motive lambdas around it, not by constructor memberships escaping. Six of
/// the 72 are the ι rule.
///
/// `073` and `116` moved again when **iota** stopped being an admission and
/// became a rule with a derivation behind it (`Certifier::iota`): `073` from 12
/// to 10 and `116` from 23 to 18. On `073` the two iota gaps closed and two of
/// the ten cascade gaps followed, but two *escapes* appeared in their place —
/// the certificate is conditional on the typings of `motive`, `falseVal` and
/// `trueVal`, which are context locals, so `Bool.rec`'s arguments are not
/// closed even though its major premise is. On `116` the same certificate comes
/// out unconditional and five gaps closed with no new escape. `075` and `076`
/// did not move at all: their recursors are `N.rec` and `List.rec`, which have
/// no curried interpretation here.
///
/// `076_listRecReduction` was at 87 before `List` was interpreted and is at 87
/// after — **no movement at all**, and the number is here so that the negative
/// is a checked claim rather than a remembered one. The interpretation is real:
/// 21 of the file's 24 obligations about an opaque head are now settled by the
/// `CtorApp` rule, where before they were pure assumptions. They settle
/// *conditionally*, and that is the whole story: `076` states its theorem under
/// `∀ α (xs : List α)`, so **every** term in it mentions a context local and no
/// typing obligation in the file can be discharged unconditionally, whatever
/// `List` is interpreted as. `073` improved because `Bool.true` is closed. The
/// remaining 87 split as 21 escaped assumptions and 66 the ι rule and its
/// cascade — so the recursor, not the interpretation, is what is left here.
///
/// `075_nRecReduction` moved **54 → 4** when `N.rec` was wired: all six ι gaps
/// closed, and with them their whole cascade. Two other things had to be fixed
/// to get there, and both were older than `N.rec`. `derive_beta` counted its
/// contractions on the *substituted* head rather than on the syntactic lambda
/// nesting, so where the checker stopped after three the backend took a fourth
/// and proved a different equation — caught by its own guard, three times, and
/// reported as a gap. And a reduct memoised by an uncertified `whnf` call left a
/// later certified call with nothing to recall. That second fix also moved
/// `101_proofIrrelevanceWhnf` 10 → 6, `113` 5 → 1 and `114` 6 → 2.
///
/// The reduct memo now carries the **reduction** rather than only the reduct
/// (`checker/src/reduct.rs`), so a hit hands back the evidence whatever kind of
/// call first populated the entry, and no reduction is re-run for its
/// certificate. `Admit::Whnf` is gone corpus-wide, `101` moved 6 → 5 and `114`
/// 2 → 1, and nothing else in the corpus moved by a gap or an escape.
///
/// The four that are left are not the recursor: two are `pi_cong`'s
/// extensionality route ("the body certificate is not the fibres' pointwise
/// equation"), one is a congruence above them, and one is the single escaping
/// certificate — conditional on `⟦motive⟧ ∈ ⟦N → Sort 1⟧`, a **closed** lambda
/// whose typing wants `fs(N,N) ∈ U(⟦Sort 0⟧)` and so can be discharged at no
/// binder. That escape is what `INDUCTIVES.md` predicted; the prediction that
/// most of the cascade would merely *become* escapes did not hold.
///
/// `076_listRecReduction` moved **63 → 32** when `List.rec` was wired: all five
/// ι gaps closed and 26 of the cascade with them, and nothing else in the corpus
/// moved by a gap. It did **not** reach the `073` outcome the handover predicted,
/// and the reason is measured rather than argued: its 15 escapes were there
/// before the recursor existed and are 16 after, so they are not the recursor's
/// and closing 31 gaps beneath them did not move them. The 32 split as 16
/// escapes, 3 primary gaps (two `eq_cache`, one `pi_cong` extensionality) and 13
/// cascade over those three. Its escaping certificates carry `⟦α⟧ ∈ ⟦Type 0⟧`,
/// `⟦xs⟧ ∈ ⟦List α⟧` and `⟦h⟧ ∈ ⟦α⟧` — every one of them dischargeable at a
/// binder in principle — together with the motive lambda's typing, which wants
/// `⟦List α⟧ ∈ ⟦Sort 1⟧` and is the `Sort`-encoding obstruction already on
/// record. See `INDUCTIVES.md`.
/// **Hoisting a binder-dependent assumption** moved five of these files and
/// nothing else in the corpus. `guard_and_generalise_at` used to refuse
/// whenever a certificate carried an assumption mentioning the very binder
/// being generalised — `ax_dist` will not move a `∀` past a free occurrence,
/// rightly — and that refusal was, measured, the *only* reason `pi_cong`'s
/// extensionality route and its constant-fibre bridge ever failed: 216 of 216
/// failures on `init-prelude`. Restating such an assumption as
/// `∀w. (w ∈ A → φ(w))` before the generalisation removes the obstruction.
///
/// Both gap categories go to **zero** corpus-wide (`init-prelude`: 214 pointwise
/// + 465 constant-fibre → 0, with the cascade `pi congruence over an admitted
/// body premise` 1293 → 743, total 10219 → 9650). The tutorial total goes
/// 263 → 210. The cost is escapes: the hoisted assumption is owed by nobody yet,
/// so it survives to the boundary — 49 → 68 over the corpus, 804 → 1484 on
/// `init-prelude`. That trade is why the numbers below move by so much less than
/// the primary gaps do.
///
/// `077_RBTree.id_spec` is the file this shows up in: 101 → 53. It is not in
/// this list, so nothing pins it; the note is the record.
///
/// **The consumer for the hoisted shape now exists and moves none of these.**
/// `TgBackend::discharge_families` re-opens a guarded assumption at its own
/// variable, types the subject under the binder's guard and peels it; it fires
/// **zero** times corpus-wide. Every number in this file is unchanged,
/// deliberately.
///
/// The reason given here used to be that the typing call is the one
/// `domain_obligation`'s raw fallback already failed "under a superset of those
/// assumptions". The conclusion holds and the reason does not: on
/// `init-prelude` the peel's assumption set is not a superset in **446 of the
/// 677** calls it makes, and handing `has_type` the union of both sets still
/// derives **0 of 677**. The assumption set is not what stops it — the subject
/// has no typing rule. `TgBackend::discharge_families` carries the split.
///
/// What the escapes are was then probed directly, which settles a question this
/// comment has got wrong twice. `076_listRecReduction`'s seventeen are: 13 a
/// single context local's typing `⟦w⟧ ∈ ⟦A⟧` and nothing else, 2 three such, 2
/// the motive lambdas' typings (one of those also carrying a guarded family
/// about `List.rec`). **Fifteen of the seventeen assume only context locals** —
/// so the sentence below claiming they are "dischargeable at a binder in
/// principle" is wrong: the binders that would discharge them are the ones
/// `infer` opened *above* the `def_eq` query, and no congruence rule inside the
/// query ever sees them. That is the fourth hypothesis about these escapes and
/// the first one that was measured instead of inferred; see `MEASUREMENTS.md`.
///
/// **`028_peano2` and `029_peano3` joined this list, and then left it again.**
/// They are the Church numerals: `two.{u} : Π (α : Sort u). (α → α) → α → α`.
/// That `Π`'s sort is `imax u (imax (imax u u) (imax u u))`, which does not
/// simplify, so at `u` the declaration's own parameter it is `Prop` on the
/// instantiation `u := 0` and a function space on every other. §6.2 gives those
/// two *different sets*, so the interpretation applied **neither** clause and
/// built an axiom-free symbol instead — see `Clause::Undet` and
/// `TyGap::PiUndet`. That was a correction, not a regression: the previous zero
/// came from reading the type as a function space unconditionally, which is
/// right only for `u ≠ 0`.
///
/// The **level-instantiation pre-pass** removed the dilemma rather than
/// resolving it: nothing in `028` uses `two` at a level at all, so it is
/// checked at the default instantiation, where `u` is a numeral, the `imax`
/// simplifies, and the sort is decided. Both files are back in
/// [`FULLY_DERIVED`], at 0 gaps and 0 escapes. `081_PSigma.snd` (3 → 0) and
/// `074_prodRecEqns` (16 → 14 gaps, 2 → 4 escapes) moved with them and are not
/// pinned here.
const GAP_BUDGET: &[(&str, u64)] = &[
    ("075_nRecReduction", 3),
    ("076_listRecReduction", 31),
    ("116_rtreeRecReduction", 10),
    // `101_proofIrrelevanceWhnf` was here at 5 and is now at zero — see
    // [`PROOF_IRRELEVANCE_DERIVED`], which pins the stronger claim.
    // **Two, not one, and the two are the same gap counted twice.** These
    // declarations are demanded by nothing, so they are checked once per entry
    // of `instantiations::DEFAULT_LEVELS`, which is now `[0, 1]` rather than a
    // single arbitrary level — see the constant's own documentation. Each pass
    // reports the file's one gap, so the file reports two. Nothing about the
    // interpretation moved here; the *amount of checking* did.
    ("113_reduceCtorParamRefl.mk", 2),
    ("114_reduceCtorParamRefl2.mk", 2),
    // **The projection typing rule's residue, and the reason it is a residue.**
    // `081` was at 8 gaps at `DEFAULT_LEVELS = [0]` and 0 at `[1]`, and that
    // disagreement was the whole of the interpretation's `[0]`/`[1]` gap. At
    // `u = v = 0` the redex `(λ α β s. s.0) α β s` is a proof, so §6.2's `Prop`
    // clause makes it `•`, while its reduct `s.0` is a proof that is neither a
    // `λ` nor an application and so interprets to `proj(0, ⟦s⟧)`.
    // `point_of_proof` bridges the two from `⟦s.0⟧ ∈ ⟦α⟧`, which is what
    // `TgBackend::has_type_proj` now supplies — seven of the eight gaps, the
    // beta step and its congruence cascade, close.
    //
    // What is left is **one** gap and it is the escape row: `proj` is an
    // axiom-free symbol, so `proj(0, ⟦s⟧) ∈ ⟦α⟧` is carried as an antecedent
    // rather than derived, hoisted at each of the three binders and owed by
    // nobody at the boundary. It is not a missing rule — it is the missing
    // *interpretation of `PSigma`*, one level down, and no typing rule over an
    // uninterpreted structure can close it. Pinned here so the trade stays
    // visible: 8 gaps / 0 escapes became 1 / 1.
    ("081_PSigma.snd", 1),
    // **Two files whose numbers went up when `admit` stopped guessing, and both
    // were always this high.** `Certifier::admit`'s implementation used to try
    // `proof_eq` first and pass the step off as derived whenever both sides
    // interpreted to `•`. `125_quotIndReduction` reported *zero* gaps that way
    // and is really at two: `Quot.ind`'s computation rule is an `Admit::Quot`
    // step with no backend rule behind it, and the quotient is not interpreted.
    // `124_quotLiftReduction` was 9 and is 10. Pinned so that the correction
    // stays made — an entry here is the only thing that would notice a rescue
    // being reintroduced.
    ("124_quotLiftReduction", 10),
    ("125_quotIndReduction", 2),
];

/// Exports outside the inductive-free fragment that are nevertheless derived
/// completely — no gaps, and no undischarged assumption either.
///
/// `073_boolRecEqns` is the whole list, and it is the project's second headline
/// result after the fragment: **a file where a recursor meets a constructor,
/// derived end to end**. It proves `Bool.rec fls tru Bool.false = fls` and its
/// `true` twin by `rfl`, so every step is iota and its cascade.
///
/// It is kept apart from [`FULLY_DERIVED`] deliberately: that constant *is* the
/// inductive-free fragment, exports 001–032, and its count — 27 — is quoted as
/// a result. Adding a 28th entry to it would quietly change what that number
/// means.
const RECURSOR_DERIVED: &[&str] = &["073_boolRecEqns"];

/// Exports whose **proof irrelevance** steps are derived end to end.
///
/// `101_proofIrrelevanceWhnf` was at 5 gaps and is at zero, and the way it got
/// there is the point of the pin: nothing new was proved. `is_proof` already
/// established `⟦e⟧ ∈ ⟦α⟧` and `⟦α⟧ ∈ U₀` on both sides and threw both away,
/// the step was admitted, and the admission's rescue path then went looking for
/// exactly those two facts with `has_type`. The facts are handed to
/// `Certifier::proof_irrel` instead. One gap closed, and the four congruences
/// stacked above it closed with it — which is why a file with one proof
/// irrelevance in it moved by five.
///
/// Pinned with the escape count as well as the gap count, for the reason
/// [`RECURSOR_DERIVED`] gives: "no gaps" is only worth asserting if no
/// assumption walked out of the back door instead.
const PROOF_IRRELEVANCE_DERIVED: &[&str] = &["101_proofIrrelevanceWhnf"];

/// Proof irrelevance, derived rather than admitted.
#[test]
fn proof_irrelevance_files_are_fully_derived() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    for name in PROOF_IRRELEVANCE_DERIVED {
        let f = dir.join(format!("{name}.ndjson"));
        assert!(f.exists(), "missing corpus file {}", f.display());
        let (accepted, derived, gaps) = check(&f);
        assert!(accepted, "{name}: checker rejected a good file");
        assert_eq!(gaps, 0, "{name}: expected a complete derivation, found {gaps} gap(s)");
        assert!(derived > 0, "{name}: reported no derivation steps at all");
        assert_eq!(escaped_count(&f), 0, "{name}: a certificate reached the boundary still assuming something");
    }
}

/// `073_boolRecEqns`, derived end to end — iota included.
///
/// Asserted separately from the fragment, and with the **escape count** checked
/// as well as the gap count: an iota certificate for `Bool.rec` is conditional
/// on the typings of `motive`, `falseVal` and `trueVal`, which are context
/// locals, so "no gaps" here specifically means those conditions were
/// discharged at their binders rather than carried to the boundary.
#[test]
fn the_bool_recursor_file_is_fully_derived() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    for name in RECURSOR_DERIVED {
        let f = dir.join(format!("{name}.ndjson"));
        assert!(f.exists(), "missing corpus file {}", f.display());
        let (accepted, derived, gaps) = check(&f);
        assert!(accepted, "{name}: checker rejected a good file");
        assert_eq!(gaps, 0, "{name}: expected a complete derivation, found {gaps} gap(s)");
        assert!(derived > 0, "{name}: reported no derivation steps at all");
        assert_eq!(escaped_count(&f), 0, "{name}: a certificate reached the boundary still assuming something");
    }
}

#[test]
fn tutorial_files_are_fully_derived() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    for name in FULLY_DERIVED {
        let f = dir.join(format!("{name}.ndjson"));
        assert!(f.exists(), "missing corpus file {}", f.display());
        let (accepted, derived, gaps) = check(&f);
        assert!(accepted, "{name}: checker rejected a good file");
        assert_eq!(gaps, 0, "{name}: expected a complete derivation, found {gaps} gap(s)");
        assert!(derived > 0, "{name}: reported no derivation steps at all — is the backend wired up?");
    }
}

/// The non-dependent `Π` interprets as the **constant-fibre dependent
/// product** — `mini`'s clause, `dprod₀(B,A)` for `A → B` — not as a separate
/// function-space clause (task #125's alignment; SCOPING.md §10 is the
/// decision).
///
/// Pinned through the typing report's clause census. Before the alignment an
/// arrow-typed application or lambda was typed by the `fs` rules and the two
/// rows below were nonzero on these files, so this test was red. After it,
/// every obligation an *interpreted* `Π` serves goes through the
/// dependent-product rules; the `fs` rows are reserved for targets a `derived`
/// theorem states over the function space, and no tutorial export produces
/// one. The gap counts are pinned elsewhere ([`FULLY_DERIVED`],
/// [`GAP_BUDGET`], [`RECURSOR_DERIVED`]); this asserts the *route*, because
/// the point of the alignment is that the two engines name one head symbol
/// and agree by reflexivity rather than by bridge theorem.
///
/// The seam still pays, in both directions, and both are asserted: `006`'s
/// `⟦Prop → Prop⟧ ∈ ⟦Sort 1⟧` is `fs(a,a) ∈ U(a)` carried across
/// `TgBackend::dprod_fs_eq` to the `dprod` term (the `FsDiag` row), and
/// `075`'s `⟦N.succ⟧ ∈ ⟦N → N⟧` is `derived`'s `succ ∈ fs(N,N)` re-registered
/// at the `dprod` spelling (a `Ctor` row hit at the new target). Dropping
/// either seam consumer regresses the file's gap count, which its budget
/// catches; the row assertions here catch the *silent* failure mode, where a
/// rescue path masks the loss.
#[test]
fn arrows_are_typed_by_the_dependent_product_rules() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    for name in ["006_betaReduction", "027_peano1", "073_boolRecEqns", "075_nRecReduction"] {
        let f = dir.join(format!("{name}.ndjson"));
        assert!(f.exists(), "missing corpus file {}", f.display());
        assert_eq!(
            report_row(&f, "by App: a function's values lie in its codomain"),
            None,
            "{name}: an interpreted arrow was typed by the fs application rule"
        );
        assert_eq!(
            report_row(&f, "by Lam: a graph is a function into any codomain it lands in"),
            None,
            "{name}: an interpreted arrow was typed by the fs lambda rule"
        );
    }
    let f = dir.join("006_betaReduction.ndjson");
    assert_eq!(
        report_row(&f, "by fs(a,a) ∈ U(a)"),
        Some(1),
        "006: the arrow's universe membership stopped crossing the fs seam"
    );
    let f = dir.join("075_nRecReduction.ndjson");
    assert!(
        report_row(&f, "by Ctor: a constructor lies in its inductive type").is_some_and(|n| n > 0),
        "075: no constructor membership fired — N.succ's dprod-spelled claim is not being found"
    );
}

/// Beta is a *derivation*, not an admit.
///
/// The fixture reduces `(λ x y : Type. x) Prop Prop`, a two-argument contraction
/// under a `constType` that has to be delta-unfolded first. Every argument is a
/// sort, so both domain premises are instances of `x ∈ U(x)` and the whole file
/// comes out with no gaps at all. Asserting *zero* gaps rather than "the beta
/// gap is gone" is what makes this a test of the derivation rather than of the
/// wording of a report.
#[test]
fn beta_over_a_sort_argument_is_fully_derived() {
    let f = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/good/beta-sort-argument.ndjson");
    let (accepted, derived, gaps) = check(&f);
    assert!(accepted, "beta fixture: checker rejected a good file");
    assert!(derived > 0, "beta fixture: no steps derived at all");
    assert_eq!(gaps, 0, "beta fixture: beta is supposed to be derived, found {gaps} gap(s)");
}

#[test]
fn files_with_known_gaps_are_still_accepted() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    for name in HAS_GAPS {
        let f = dir.join(format!("{name}.ndjson"));
        let (accepted, derived, gaps) = check(&f);
        assert!(accepted, "{name}: checker rejected a good file");
        // The point of these is that the gap is *reported*, not hidden.
        assert!(gaps > 0, "{name}: expected a reported gap; if this now derives fully, move it to FULLY_DERIVED");
        assert!(derived > 0, "{name}: no steps derived at all");
    }
}

/// The gap counts of the partially derived files, held to their measured
/// values.
///
/// This is the test that makes "the interpretation is worth more than the ι
/// rule" a claim the build checks rather than a note in a report: the two files
/// below are the only tutorial exports whose counts moved when `Bool` gained a
/// real interpretation, and both moved because typing obligations about
/// constructors stopped escaping — not because any reduction rule changed.
#[test]
fn partially_derived_files_stay_within_their_budget() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    for (name, budget) in GAP_BUDGET {
        let f = dir.join(format!("{name}.ndjson"));
        let (accepted, _, gaps) = check(&f);
        assert!(accepted, "{name}: checker rejected a good file");
        assert!(
            gaps <= *budget,
            "{name}: {gaps} gaps, budget {budget} — the interpretation regressed"
        );
        if gaps < *budget {
            panic!("{name}: {gaps} gaps, budget {budget} — an improvement; lower the budget");
        }
    }
}

/// The backend must not change what the checker accepts or rejects — it only
/// adds evidence. An ill-typed file must still be rejected with TG active.
#[test]
fn tg_backend_still_rejects_bad_files() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/bad");
    for entry in std::fs::read_dir(&dir).expect("fixtures/bad").flatten() {
        let p = entry.path();
        if p.extension().is_some_and(|e| e == "ndjson") {
            let (accepted, _, _) = check(&p);
            assert!(!accepted, "{}: accepted an ill-typed file with the TG backend", p.display());
        }
    }
}

/// Zeta reduction where the `let`'s expansion contains a **free variable**.
///
/// `let` is interpreted as an explicit definition of its expansion, so zeta is
/// the defining equation. When the expansion mentions Lean locals — i.e. kernel
/// free variables — those must become *parameters* of the defined symbol, since
/// `kernel::thm::define` refuses a body with a free variable it does not
/// abstract (that side condition was added after an unsoundness was found
/// without it).
///
/// Nothing in the arena corpus exercises this: zeta fires exactly once there,
/// in `032_letRed`, whose expansion is closed. This fixture is
/// `∀ x : Type, (let y := x; y) → x` proved by `λ x p. p`, which forces
/// `(let y := x; y) ≡ x` through definitional equality with the expansion being
/// the local `x`. Verified to genuinely reach zeta by temporarily forcing that
/// rule to admit and observing the gap appear.
///
/// The file still reports `pi congruence` gaps, which are unrelated; the
/// assertion is specifically that **no zeta gap** arises.
#[test]
fn zeta_with_a_free_variable_expansion() {
    let f = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/good/let-free-variable.ndjson");
    let (accepted, derived, _gaps) = check(&f);
    assert!(accepted, "checker rejected a well-typed file");
    assert!(derived > 0, "no steps derived at all");
    assert!(
        !gap_reasons(&f).iter().any(|r| r.contains("zeta")),
        "zeta gapped on a let whose expansion is a free variable: {:?}",
        gap_reasons(&f)
    );
}

/// A certificate that reaches a boundary still resting on an assumption is a
/// step taken on trust, and must be **reported as a gap** rather than passed off
/// as a derivation.
///
/// Carrying the beta typing obligation `⟦a⟧ ∈ ⟦A⟧` as a genuine antecedent is
/// what turns most of those obligations into complete conditional derivations;
/// the ones that are never discharged are the residue, and the whole design is
/// only honest if the residue is visible. So this asserts the ledger balances:
/// the number of escaped certificates the report prints is exactly the count of
/// the escape gap row, and that row is in the total.
///
/// `028_peano2` and `029_peano3` are the two files this machinery was measured
/// on — 32 gaps down to 8 and 59 down to 9 — and between them they cover both
/// cases: `028` discharges every one of its conditional derivations, `029`
/// leaves one over.
#[test]
fn escaped_assumptions_are_reported_as_gaps() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    for name in ["028_peano2", "029_peano3", "075_nRecReduction"] {
        let f = dir.join(format!("{name}.ndjson"));
        assert!(f.exists(), "missing corpus file {}", f.display());
        let (_, _, total) = check(&f);
        let escaped = escaped_count(&f);
        let rows = gap_reasons(&f);
        let row = rows.iter().find(|r| r.contains("undischarged assumption"));
        match escaped {
            0 => assert!(row.is_none(), "{name}: no certificate escaped, yet a gap claims one did: {row:?}"),
            n => {
                let row = row.unwrap_or_else(|| panic!("{name}: {n} certificate(s) escaped and no gap says so: {rows:?}"));
                let counted: u64 = row.split_whitespace().last().and_then(|t| t.parse().ok()).unwrap_or(u64::MAX);
                assert_eq!(counted, n, "{name}: escape ledger and gap row disagree");
                assert!(total >= n, "{name}: {n} escapes are not included in the {total} reported gaps");
            }
        }
    }
}

/// The backend's whole report for one export, as text.
fn report(export: &Path) -> String {
    let cfg_path = tmp_cfg("rep", export);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true,
             "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// Sum the counts of every report row whose text starts with `label`.
fn rows_totalling(text: &str, label: &str) -> u64 {
    text.lines()
        .map(str::trim_start)
        .filter(|l| l.starts_with(label))
        .filter_map(|l| l.split_whitespace().last().and_then(|t| t.parse::<u64>().ok()))
        .sum()
}

/// **`⟦·⟧` is a function, across §6.2's two clauses and the case where neither
/// applies.**
///
/// Carneiro interprets `∀` (a `Π` into `Prop`) as the conditional singleton
/// `[∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]` and `Π` (into a `Type`) as a dependent product, and
/// `TgBackend::interp_pi` now implements both. Which clause a `Π` falls under is
/// decided by a *syntactic* approximation of the body's sort, because the
/// backend may not call `infer` — so the standing risk is that the
/// approximation answers differently for two definitionally equal types, and
/// then the interpretation is not a function of the Lean term. Two things pin
/// that here, over all 91 tutorial exports:
///
/// * **The clauses never meet.** `derive_pi_cong` reports a distinct gap when
///   it is handed one term from each clause, which can only happen if two
///   `def_eq`-related `Π`s were classified differently. It must stay at zero.
///   Weakening the classifier to `syn_type` alone — which gives up on a `λ` and
///   a `let`, so a `Π` whose body is a redex is classified `Type` while its
///   contractum is classified `Prop` — makes this fire 30 times. Dropping
///   either exit of `interp_pi` makes it fire 4 times.
///
///   Zero over the tutorials, and **two** over `init-prelude`, which is the
///   honest state of the approximation rather than a clean result: one is a
///   four-argument application whose head's type does not reach a `Sort` by
///   delta alone, the other a redex whose contractum the classifier still
///   declines. Neither costs a gap — the total is unchanged either way — but
///   neither is a term the interpretation can claim to be a function on.
/// * **Both of `interp_pi`'s exits take the branch.** A `Π` whose body has no
///   loose de Bruijn index leaves by the syntactic fast path and one whose body
///   does leaves by the exact `occurs_free` test; if either forgot to consult
///   the classifier, the `Π`s reaching it would still be function spaces or
///   dependent products, and their `ty_pi_prop` obligation — which is
///   discharged only for a registered conditional singleton — would go back to
///   having no evidence. So the derived count is asserted to dominate.
///
/// # `λ` and application, the other two splits
///
/// §6.2 splits **three** constructors, not one: alongside `∀`/`Π` it sends a
/// proof `λ` and a proof application to `•` and everything else to a graph and
/// a set-application. `TgBackend::term_clause` decides those two, by the same
/// approximation one level down (`sort(e) = lvl(type of e)`), so it carries the
/// same risk and is pinned the same way — two more gap rows that must stay at
/// zero, and two population counts that must not collapse.
///
/// The population counts are what catch a *branch* quietly reverting rather
/// than a classification disagreeing. Deleting the `Prop` branch of
/// `interp_lambda` or of `interp_app` makes `⟦·⟧` a function again — wrongly,
/// by the `Type` clause everywhere — and no disagreement row fires; the count
/// going to zero is what fires. Both were checked by deletion (`λ` 88 → 0,
/// application 962 → 0), as was the `Prop` lambda's typing rule in `ty_lam`
/// (`λ` 88 → 68, `by ty_lam` 104 → 87).
///
/// **And the disagreement rows are not, on this corpus, what catches a
/// disagreement** — which is worth writing down rather than assuming. Deleting
/// `term_clause`'s redex case, so that `(λn m. …) lit1 lit1` is undetermined
/// while the constant it delta-reduces from is a proof, is a real
/// classification disagreement and both rows stay at **zero**: `delta` and
/// `beta` meet the two terms before any congruence does, and report it as their
/// own gap (222 → 282 over the corpus, and the inductive-free fragment off
/// 27/27). The rows are still asserted, because the case they name — two
/// `def_eq` lambdas or applications reaching a congruence from opposite clauses
/// — is the one nothing else would report at all.
#[test]
fn the_two_clauses_of_the_interpretation_never_disagree() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let mut files: Vec<PathBuf> =
        std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok().map(|e| e.path())).collect();
    files.retain(|p| p.extension().is_some_and(|x| x == "ndjson"));
    files.sort();
    assert!(!files.is_empty(), "no tutorial exports found");

    let (mut derived, mut missing, mut undet, mut by_param) = (0u64, 0u64, 0u64, 0u64);
    let (mut lam_point, mut app_point, mut lam_typed) = (0u64, 0u64, 0u64);
    for f in &files {
        let text = report(f);
        let name = f.file_stem().unwrap().to_string_lossy().into_owned();
        for row in [
            "gap: pi congruence: one ∀ and one Π",
            "gap: pi congruence: one Π of undetermined sort",
            // The same discipline for the other two splits of §6.2.
            "gap: lam congruence: one proof λ and one Λ",
            "gap: congruence: one proof application and one",
        ] {
            let mixed = rows_totalling(&text, row);
            assert_eq!(mixed, 0, "{name}: {mixed} term(s) classified one way and compared against another");
        }
        derived += rows_totalling(&text, "by ty_pi_prop");
        missing += rows_totalling(&text, "no evidence: ty_pi_prop");
        undet += rows_totalling(&text, "no evidence: ty_pi_undet");
        by_param += rows_totalling(&text, "a universe parameter:");
        lam_point += rows_totalling(&text, "λ interpreted as •");
        app_point += rows_totalling(&text, "application interpreted as •");
        lam_typed += rows_totalling(&text, "by ty_lam");
    }
    // **The two term-level clauses are taken, and by this many terms.** Held as
    // ratchets so that deleting either branch — which no disagreement row would
    // notice, since the `Type` clause is a function too — fails the build.
    // Measured at `DEFAULT_LEVELS = [0, 1]`.
    //
    // These are **event** counts — one per `interp` traversal that took the
    // clause — not term counts. 962 → 353 applications when the
    // interpretation's binder opens moved to expression-derived de Bruijn
    // levels: an α-identical opened body is now one `ExprPtr`, so its
    // subterms interpret once and hit the memo thereafter, and every memo hit
    // is a traversal that no longer happens. The clause is exercised exactly
    // as before — the per-file disagreement rows above stay at zero, and the
    // prelude's gap/derivation ledger is unchanged row for row — there are
    // simply fewer traversals to count.
    assert!(lam_point >= 88, "only {lam_point} λs took §6.2's Prop clause, expected at least 88");
    assert!(app_point >= 300, "only {app_point} applications took §6.2's Prop clause, expected at least 300");
    // The `Prop` lambda's own typing rule, `cond_intro`, reached through
    // inference: 17 of these 104 are it, and they are all of it — no `has_type`
    // obligation in this corpus is about a proof `λ`. Deleting the rule takes
    // this to 87.
    assert!(lam_typed >= 104, "inference typed only {lam_typed} λs, expected at least 104");
    // Measured: 149 derived against 1 with no evidence. Held as a ratchet so
    // that an exit of `interp_pi` quietly reverting to the `Π` clause fails the
    // build rather than showing up as a number nobody re-read.
    assert!(derived >= 149, "the Prop clause discharged only {derived} of its typing obligations");
    assert!(missing <= 1, "{missing} Prop-valued ∀s had no membership fact, expected at most 1");
    // **The third case has collapsed, and this is the ratchet that keeps it
    // collapsed.** It used to be the large one — 336 of the corpus's 660 `Π`
    // typing sites fell under neither clause, and 1830 of the 1831 expressions
    // that put them there were a universe parameter rather than a limit of the
    // syntactic walk. The whole point of the level-instantiation pre-pass
    // (`checker/src/instantiations.rs`) is that a universe parameter is *not* a
    // permanent obstruction: check the declaration at a ground instantiation
    // and the level is a numeral. Measured after: **36** undetermined typing
    // sites, down from 336.
    //
    // The bound is therefore an upper one now, and reverting the pre-pass fails
    // the build rather than being reported as a number nobody re-read.
    assert!(undet <= 36, "{undet} Π typing sites reported as undetermined, expected at most 36");
    // What is left of the undetermined *expression* population — 1394, from
    // 1830 — is dominated by the passes that take no σ, which is every pass
    // that checks an inductive block: `check_declar_all` does not give those an
    // instantiation, deliberately, because an inductive's check runs over a
    // mutual block and mints a fresh eliminator universe of its own.
    // Up from 1394, and **not** because the interpretation got worse: this counts
    // *classification queries* that hit a universe parameter with no σ in force,
    // and `term_clause` asks the classifier about every `λ` and every
    // application as well as every `Π`. The passes it is dominated by are still
    // the ones that check an inductive block, which take no σ deliberately.
    // 4953 → 4962 when `T`-policy 2 started building a general recursor nest on
    // `042`/`068`/`075`/`077`: a nest walks the recursor's own type and
    // interprets every binder, and those four recursors are checked in passes
    // that take no σ. Nine more *queries*, no change to any answer — the four
    // files' gap and escape counts are unmoved and their reports differ only in
    // the general path's own ledger rows.
    //
    // …and **back to 4953** when the `is_recursive` window closed: those nine
    // queries were the nine binders of the four nests above, and those four
    // nests were themselves the window rather than the policy (see
    // [`no_tutorial_export_builds_a_general_recursor_nest`]). The `np > 0` type
    // former adds one query of its own, which is why the number is 4953 and not
    // 4952. No answer moved either way — the 91-row gap/escape/derived table is
    // byte-identical across the whole change.
    assert!(by_param <= 4953, "{by_param} undetermined-by-parameter expressions, expected at most 4953");
}

/// **Every instantiation the backend interprets was predicted by the pre-pass.**
///
/// `checker/src/instantiations.rs` decides, before any checking starts, which
/// `(declaration, universe levels)` pairs the run needs, by a worklist fixpoint
/// over the export file's `Const` nodes. That is a *syntactic* prediction, and
/// the checker creates two kinds of instantiation no expression in the file
/// mentions: literal expansion mints `List.nil.{0} Char` and friends, and
/// `inductive.rs` mints temporary declarations for nested inductives.
///
/// The first is handled by a fixed seed list, which is a claim about coverage —
/// and a claim about coverage that is only believed is the kind that quietly
/// stops being true. So the backend counts what it actually interprets against
/// the schedule and reports the misses as their own row, and this asserts the
/// row is zero over the whole tutorial corpus. A non-zero count is not a
/// cosmetic failure: it means a declaration was interpreted at an instantiation
/// nothing scheduled it at, so no store entry can exist for it.
#[test]
fn the_pre_pass_predicts_every_instantiation_the_backend_interprets() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let mut files: Vec<PathBuf> =
        std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok().map(|e| e.path())).collect();
    files.retain(|p| p.extension().is_some_and(|x| x == "ndjson"));
    files.sort();
    assert!(!files.is_empty(), "no tutorial exports found");

    let (mut predicted, mut unpredicted) = (0u64, 0u64);
    for f in &files {
        let text = report(f);
        let name = f.file_stem().unwrap().to_string_lossy().into_owned();
        let miss = rows_totalling(&text, "…at an instantiation the pre-pass did NOT predict");
        assert_eq!(miss, 0, "{name}: {miss} constant instantiation(s) the pre-pass did not schedule");
        unpredicted += miss;
        predicted += rows_totalling(&text, "constants interpreted at a scheduled instantiation");
    }
    // A zero miss row proves nothing if nothing was audited.
    assert!(predicted > 0, "the audit never ran: no constant instantiation was checked against the schedule");
    assert_eq!(unpredicted, 0);
}

/// How many certificates the run finished with an undischarged assumption.
fn escaped_count(export: &Path) -> u64 {
    let cfg_path = tmp_cfg("esc", export);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true,
             "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    let text = String::from_utf8_lossy(&out.stderr);
    // "… , N accounted for by a rule, M escaped (max K assumptions)"
    let Some(line) = text.lines().find(|l| l.trim_start().starts_with("conditional derivations:")) else {
        return 0
    };
    let toks: Vec<&str> = line.split_whitespace().collect();
    toks.iter()
        .position(|t| *t == "escaped")
        .and_then(|i| i.checked_sub(1))
        .and_then(|i| toks[i].parse().ok())
        .expect("the report line names an escape count")
}

/// One report row, by its label. `None` when the row is absent.
fn report_row(export: &Path, label: &str) -> Option<u64> {
    let cfg_path = tmp_cfg("row", export);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true,
             "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    let text = String::from_utf8_lossy(&out.stderr);
    text.lines()
        .find(|l| l.trim_start().starts_with(label))
        .and_then(|l| l.split_whitespace().last())
        .and_then(|n| n.parse().ok())
}

/// **A declaration with parameters reaches the general path, and its
/// constructors get typing rules.**
///
/// This is the whole observable of lifting `Decline::Params`: `Prod` has one
/// parameter — two, in fact — so before the Lean-facing type-former nest
/// existed the general path declined it at declaration scope and *nothing*
/// downstream was attempted. `074_prodRecEqns` is the tutorial that applies
/// `Prod.mk`, so it is where the change shows up as typing obligations
/// discharged rather than carried.
///
/// Asserted as "some translated declarations and some `CtorApp` discharges",
/// not as an exact count: the numbers move whenever the interpretation does,
/// and a ratchet on them would fail for reasons that have nothing to do with
/// parameters. Zero on either row means the parameter path is gone, which is
/// the regression worth catching. The file's *gap* count is pinned separately
/// in [`GAP_BUDGET`], and it did not move when this landed.
#[test]
fn a_parameterised_declaration_reaches_the_general_path() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let f = dir.join("074_prodRecEqns.ndjson");
    assert!(f.exists(), "missing corpus file {}", f.display());
    let translated = report_row(&f, "declarations translated").expect("the ledger row exists");
    assert!(translated > 0, "no declaration reached the general path — is `Decline::Params` back?");
    let ctor_app =
        report_row(&f, "by CtorApp: an applied constructor").expect("the clause row exists");
    assert!(
        ctor_app > 0,
        "no applied constructor was typed by its rule — the parameterised `CtorRule` is not firing"
    );
}

/// **The threat-model anchor is tied to a term the backend actually produces.**
///
/// `README.md` makes the whole guarantee conditional on `⟦False⟧` being
/// genuinely refutable in the target, and `derived::anchor::falsity` proves
/// `⊢ ∀x. ¬(x ∈ ∅)` and `⊢ ⟦False⟧ = ∅`. Until `⟦Sort 0⟧` became `U₀` those were
/// statements about a term the interpretation never built: a `Prop`-valued
/// inductive with no value got an opaque nullary symbol carrying no axioms, and
/// `⟦False⟧ := {∅}` was an equally consistent reading of it.
///
/// The fixture is `inductive False : Prop` with its recursor and one definition
/// naming it — the smallest export that makes the backend interpret `False` at
/// all. What is asserted is that the run *reports* the anchor: `false_const`
/// records it only after instantiating it and checking the body is literally
/// about the symbol it just introduced for `False`, so a report line is a
/// checked theorem and not a label.
///
/// Asserting a positive count rather than an exact one: the count is per
/// declaration-backend, which is an implementation detail, whereas "this run
/// derived it" is the property.
#[test]
fn the_false_anchor_is_tied_to_the_backends_own_term() {
    let f = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/good/false-prop.ndjson");
    let (accepted, derived, gaps) = check(&f);
    assert!(accepted, "False fixture: checker rejected a good file");
    assert!(derived > 0, "False fixture: no steps derived at all");
    assert_eq!(gaps, 0, "False fixture: {gaps} gap(s)");
    let anchors = report_lines(&f)
        .into_iter()
        .find(|l| l.contains("⟦False⟧ anchored"))
        .and_then(|l| l.split_whitespace().last().and_then(|n| n.parse::<u64>().ok()));
    assert!(
        anchors.is_some_and(|n| n > 0),
        "⟦False⟧ was interpreted but ⊢ ∀x. ¬(x ∈ ⟦False⟧) was not derived at that term"
    );
}

/// Every line of the coverage report for one export.
fn report_lines(export: &Path) -> Vec<String> {
    let cfg_path = tmp_cfg("lines", export);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true,
             "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    String::from_utf8_lossy(&out.stderr).lines().map(|l| l.trim().to_string()).collect()
}

/// The gap reasons reported for one export.
fn gap_reasons(export: &Path) -> Vec<String> {
    let cfg_path = tmp_cfg("gaps", export);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true,
             "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin")).arg(&cfg_path).output().expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    String::from_utf8_lossy(&out.stderr)
        .lines()
        .filter(|l| l.trim_start().starts_with("gap:"))
        .map(|l| l.trim().to_string())
        .collect()
}

/// **The projection typing rule is reached, on both of its two paths.**
///
/// A projection had no typing rule at all: `infer`'s `Proj` case called
/// `ty_gap` directly, and `has_type`'s structural match had no `Expr::Proj`
/// arm. There are therefore two paths to pin, because they are two different
/// mechanisms and either could quietly stop firing without the other noticing:
///
/// * **inference-driven** — `Certifier::ty_proj`, composed from the premises
///   `infer` already has. Counted as `by ty_proj`, and its absence as
///   `no evidence: ty_proj`, so the two together are a fixed population and
///   asserting the first is high *and* the second is zero pins the rule rather
///   than the corpus.
/// * **searched** — `TgBackend::has_type_proj`, the clause `has_type` reaches
///   when a definitional-equality derivation needs `⟦s.i⟧ ∈ ⟦F⟧` with no
///   inference in progress to ask. This is the one `point_of_proof` needs, and
///   it is counted separately as its own `HtClause`.
///
/// Verified to fire by deletion, which is this file's standing practice:
/// removing the `Expr::Proj` arm from `has_type_uncached` takes the searched
/// row 5 → 0 and `081_PSigma.snd` back to 8 gaps; reverting `infer`'s `Proj`
/// case to `ty_gap` takes `by ty_proj` 27 → 0 and `no evidence: ty_proj` 0 → 27.
///
/// # The claim guard
///
/// `TgBackend::typing` checks the theorem concludes the membership being
/// claimed. `ty_not_the_claim` is that check failing, and it is a bug report
/// rather than a missing rule, so it is asserted at zero: a rule that starts
/// concluding something other than what it advertises fails the build. Verified
/// by breaking it — making `ty_proj` state its antecedent about the *structure*
/// instead of the projection takes `ty_not_the_claim` 0 → 27 and `by ty_proj`
/// 27 → 0, and this test fails.
///
/// # One discipline here has no witness on this corpus, and that is measured
///
/// Both projection clauses refuse to assume at whatever target they were handed
/// and instead recompute the field type from the structure's constructor
/// telescope (`syn_type_proj`), assuming only at that — the rule
/// `has_type_local` follows, and the reason it exists is that a target merely
/// *definitionally* equal to Lean's own judgement would make the antecedent
/// stronger than the judgement.
///
/// **Deleting that discipline moves nothing.** Restating `has_type_proj`'s
/// antecedent at the demanded target leaves every number in this file
/// unchanged: the corpus's gaps and escapes (215 and 78 when this was measured,
/// 210 and 78 since proof irrelevance stopped being admitted), the searched row
/// at 5, the inference row at 27. On this corpus every projection obligation is demanded at exactly the
/// interpreted field type, so the two spellings coincide and no test can tell
/// them apart. The guard stays — it is the right statement to assume, and the
/// corpus not exercising it is a fact about the corpus — but it is recorded
/// here as unwitnessed rather than left to look pinned.
#[test]
fn the_projection_typing_rule_fires() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let mut files: Vec<PathBuf> =
        std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok().map(|e| e.path())).collect();
    files.retain(|p| p.extension().is_some_and(|x| x == "ndjson"));
    files.sort();
    assert!(!files.is_empty(), "no tutorial exports found");

    let (mut inferred, mut no_evidence, mut searched, mut not_claim) = (0u64, 0u64, 0u64, 0u64);
    for f in &files {
        let text = report(f);
        inferred += rows_totalling(&text, "by ty_proj");
        no_evidence += rows_totalling(&text, "no evidence: ty_proj");
        searched += rows_totalling(&text, "by Proj: the field's own typing");
        not_claim += rows_totalling(&text, "no evidence: ty_not_the_claim");
    }
    assert!(inferred >= 27, "inference typed only {inferred} projections, expected at least 27");
    assert_eq!(no_evidence, 0, "{no_evidence} projection typings had no evidence; the rule declined");
    assert!(searched >= 5, "has_type reached the projection clause only {searched} times, expected at least 5");
    assert_eq!(not_claim, 0, "{not_claim} typing rule(s) concluded something other than the claim");
}

/// **A constructor's membership rule is keyed by the universe levels it is
/// stated at, not only by its name.**
///
/// `TgBackend::ctor_rules` holds, per interpreted constructor, the conditional
/// theorem `⊢ ∀α. (α ∈ S → app(⟦nil⟧,α) ∈ app(⟦List⟧,α))` that
/// `has_type_ctor_app` instantiates. Every term in that statement — `S`, which
/// is `⟦Sort ℓ⟧`, and the three abbreviation symbols `ind_abbrev` mints per
/// `(name, levels)` — depends on the instantiation it was built at. The map was
/// keyed by the Lean name alone and populated on the first instantiation the
/// backend met, so a second one read back a rule about the wrong universe.
///
/// # This needed a fixture, because the corpus does not reach it
///
/// A backend is per declaration, so the two instantiations have to occur in
/// **one** declaration. Probed directly — a counter on the reuse itself — the
/// condition fires **zero** times across all 91 tutorial exports,
/// `init-prelude` and `undecidability`. So the bug was real and unwitnessed,
/// and asserting it needed a case built for it rather than found.
///
/// `list-two-levels.ndjson` is `076_listRecReduction`'s `List` block plus
///
/// ```text
/// def k : List.{0} Prop → List.{1} (Sort 1) → Sort 1 := fun x y => Prop
/// def twoLevelLists : k (List.nil.{0} Prop) (List.nil.{1} (Sort 1)) := ∀ p : Prop, p
/// ```
///
/// The second declaration's type must be delta-unfolded and then contracted
/// twice, and each contraction's domain premise is a `List.nil` membership at
/// its own level — so one declaration asks the rule for two instantiations, in
/// order.
///
/// Measured, name-keyed against `(name, levels)`-keyed: **1 gap, 1 escaped
/// certificate, 1 obligation answered by `CtorApp` and 1 falling through to the
/// raw fallback** becomes **0 gaps, 0 escapes, 2 answered by `CtorApp`**. The
/// second contraction's premise `⟦Sort 1⟧ ∈ ⟦Sort 1⟧` — the first
/// instantiation's `S`, at the second's argument — is not derivable, which is
/// why the failure mode is a spurious gap and never a wrong theorem: even had
/// it been discharged, the conclusion names the first instantiation's symbols
/// and `has_type_a`'s guard rejects it.
///
/// Verified to fire by reverting the key to the Lean name alone, which restores
/// exactly the numbers above and fails this test.
#[test]
fn a_constructor_rule_is_keyed_by_its_universe_levels() {
    let f = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/good/list-two-levels.ndjson");
    let (accepted, derived, gaps) = check(&f);
    assert!(accepted, "list-two-levels: checker rejected a well-typed file");
    assert!(derived > 0, "list-two-levels: no steps derived at all");
    assert_eq!(gaps, 0, "list-two-levels: {gaps} gap(s); the constructor rule was read at the wrong levels");
    assert_eq!(escaped_count(&f), 0, "list-two-levels: a certificate reached the boundary still assuming something");
    // Both `List.nil` obligations must be answered by the rule. A zero-gap file
    // in which the clause simply never fired would pass the assertions above
    // and prove nothing.
    let by_rule = rows_totalling(&report(&f), "by CtorApp:");
    assert_eq!(by_rule, 2, "list-two-levels: {by_rule} obligations answered by the constructor rule, expected 2");
}

// ─────────────────────────────────────────────────────────────────────────────
// The general inductive path (`derived::inductive`), wired after the three
// hand-written shape recognisers. See `WIRING-DESIGN.md` §§3–5, and the
// module docs on `TgBackend::gen_scope` / `walk_spec` / `gen_const`.
// ─────────────────────────────────────────────────────────────────────────────

/// The general path's report rows for one export, as `(label, count)`.
fn gen_rows(export: &Path) -> Vec<(String, u64)> {
    let text = report(export);
    let mut out = Vec::new();
    let mut inside = false;
    for l in text.lines() {
        let t = l.trim_end();
        if t.trim_start().starts_with("the general inductive path") {
            inside = true;
            continue
        }
        if inside {
            // The section ends at the next un-indented-to-four heading.
            if !t.starts_with("    ") {
                break
            }
            let t = t.trim();
            if let Some((label, n)) = t.rsplit_once(char::is_whitespace) {
                if let Ok(n) = n.parse::<u64>() {
                    out.push((label.trim().to_string(), n));
                }
            }
        }
    }
    out
}

/// One row of the general path's ledger, or 0 when the row is absent.
fn gen_row(export: &Path, label: &str) -> u64 {
    gen_rows(export).into_iter().find(|(l, _)| l == label).map(|(_, n)| n).unwrap_or(0)
}

const GEN_TRANSLATED: &str = "declarations translated";
const GEN_CTORS: &str = "constructors given a term and a typing rule";
const GEN_GUARD: &str = "cached specs declined: βⱼ bodies not canonical";
const GEN_INDICES: &str = "…declined: indices";
const GEN_FUNREC: &str = "…declined: function-typed recursive argument";
const GEN_SORT: &str = "…declined: sort-ambiguous or Prop (class S/P)";

fn tutorial(name: &str) -> PathBuf { corpus().join("good/tutorial").join(format!("{name}.ndjson")) }

/// **The general path runs at all** — otherwise every decline assertion below
/// is a statement about a code path nothing reaches.
///
/// The shapes it covers that no recogniser could: `enum_arity` refuses more
/// than two constructors and every constructor with a field; `nat_shape` and
/// `list_shape` match one declaration each, checked field by field. The
/// tutorials' witness is `035_twoBool`/`061_twoBoolRec`, which declare a
/// **two-field single-constructor structure** alongside the enumeration —
/// `Σy₀:β₀. Σy₁:β₁(y₀). 1` over a one-summand tag set, which is outside all
/// three recognisers and inside `DeclSpec`.
///
/// Verified to fire by making `TgBackend::ind_const` return `None` instead of
/// consulting `gen_const`: both rows go to zero.
#[test]
fn the_general_inductive_path_translates_shapes_no_recogniser_covers() {
    if skip_guard::absent(&corpus().join("good/tutorial")) {
        return
    }
    let mut translated = 0u64;
    let mut ctors = 0u64;
    for name in ["035_twoBool", "061_twoBoolRec", "042_rbTreeDef", "077_RBTree.id_spec"] {
        let f = tutorial(name);
        if !f.is_file() {
            continue
        }
        translated += gen_row(&f, GEN_TRANSLATED);
        ctors += gen_row(&f, GEN_CTORS);
    }
    assert!(translated > 0, "the general path translated nothing; every decline row below proves nothing");
    assert!(ctors > 0, "the general path gave no constructor a term and a typing rule");
}

/// **An indexed family is declined, positively and by name of the reason.**
///
/// Indices are *unrepresentable* in `derived::inductive::DeclSpec` — `good`/`G`
/// is the third output of the thesis's `spec` judgment and undoing the erasure
/// of indices needs the equality type first — so there is **no derived-side
/// backstop**. `TgBackend::gen_scope`'s `num_indices == 0` line is the whole of
/// the scope enforcement, and `RBTree` (`numIndices: 2`, over `Color` and `N`)
/// is what walks into it.
///
/// The three `RBTree` files must therefore be untouched by the general path:
/// their gap and escape counts are pinned in [`GAP_BUDGET`], and movement there
/// would mean a scope leak. This test adds what that cannot say — that the
/// decline *happened*, with the matching reason, rather than the declaration
/// never being reached.
///
/// Verified to fire by deleting the `num_indices` check: the row drops to zero
/// and `042`/`077` move.
#[test]
fn an_indexed_family_is_declined_as_indexed() {
    if skip_guard::absent(&corpus().join("good/tutorial")) {
        return
    }
    for name in ["042_rbTreeDef", "068_rbTreeRef", "077_RBTree.id_spec"] {
        let f = tutorial(name);
        if !f.is_file() {
            continue
        }
        let n = gen_row(&f, GEN_INDICES);
        assert!(n > 0, "{name}: the general path never declined an indexed family");
    }
}

/// **A function-typed recursive argument is declined, positively.**
///
/// `CtorSpec::recs` is a `usize` — the assumption that a recursive argument
/// contributes the fibre summand `1` rather than a genuine telescope. A field
/// whose type is a `Π` into the inductive (`116`'s
/// `RTree.node : (Bool → RTree) → RTree`, and `Acc.intro`) breaks that, and it
/// has to be refused **before** the field type is interpreted: interpreting a
/// self-mentioning type would recurse into the declaration being built.
///
/// Verified to fire by deleting the codomain test in `walk_spec`: the row drops
/// to zero and the decline becomes `SelfMention` instead.
#[test]
fn a_function_typed_recursive_argument_is_declined() {
    let f = tutorial("116_rtreeRecReduction");
    if skip_guard::absent(&f) {
        return
    }
    let n = gen_row(&f, GEN_FUNREC);
    assert!(n > 0, "116: `RTree.node`'s `Bool → RTree` field was not declined as function-typed");
    // And the file itself does not move: the decline is the whole of the
    // path's involvement with it.
    let (accepted, _, gaps) = check(&f);
    assert!(accepted, "116: checker rejected a well-typed file");
    assert_eq!(gaps, 10, "116: the general path moved a file it is supposed to decline");
    assert_eq!(escaped_count(&f), 2, "116: escape count moved");
}

/// **The eliminator branch is decided from the declaration's own level.**
///
/// `LEVEL-POLYMORPHIC-INDUCTIVES.md` §2–3: which of Lean's three eliminator
/// classes a declaration is in is fixed **per declaration**, never by the sort
/// it happens to be instantiated at. `TgBackend::provably_nonzero` is that
/// test, and a declaration it cannot show nonzero is declined outright rather
/// than translated at the instantiations that make it a `Type` — because a
/// per-instantiation branch is the design error that note closes.
///
/// `073_boolRecEqns` declares `Eq` and `False`-shaped propositions alongside
/// `Bool`, so the row is nonzero there while the file stays fully derived.
///
/// Verified to fire by making `provably_nonzero` return `true` unconditionally:
/// the row drops to zero.
#[test]
fn a_sort_ambiguous_declaration_is_declined() {
    let f = tutorial("073_boolRecEqns");
    if skip_guard::absent(&f) {
        return
    }
    let n = gen_row(&f, GEN_SORT);
    assert!(n > 0, "073: no declaration was declined on its own resultant level");
    let (_, derived, gaps) = check(&f);
    assert_eq!(gaps, 0, "073: the file the recogniser order exists to protect moved");
    assert!(derived > 0);
}

/// **A cached translation is a hint, never a trusted package.**
///
/// A `GenInd` is cached per *thread* — an `Inductive::build` per obligation
/// would be absurd — while a `TgBackend` is built and dropped per
/// *declaration*. So every term reachable from a cached translation, the `βⱼ`
/// field-type bodies above all, has to be stated over per-thread-stable
/// symbols. Moving `ind_syms` from the backend to `Shared` is what makes them
/// so (`WIRING-DESIGN.md` §3.4), and this row is the check: on a cache hit the
/// declaration is **re-walked under the recorded variables** and the freshly
/// interpreted bodies are compared against the stored ones. A nonzero count
/// means the interpretation is not canonical across declarations after all,
/// and the cached carrier is being rebuilt rather than reused.
///
/// Asserted at zero *and* alongside a nonzero translation count, because a row
/// that is zero because nothing was ever cached says nothing.
///
/// Verified to fire by reverting `ind_abbrev` to a per-backend store (skipping
/// the `Shared::ind_syms` consult): `035_twoBool` alone reports 2 cached
/// translations that did not survive re-interpretation instead of 0.
#[test]
fn a_cached_general_translation_is_re_derived_before_it_is_used() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let mut files: Vec<PathBuf> =
        std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok().map(|e| e.path())).collect();
    files.retain(|p| p.extension().is_some_and(|x| x == "ndjson"));
    files.sort();
    let (mut misses, mut translated) = (0u64, 0u64);
    for f in &files {
        let rows = gen_rows(f);
        let get = |label: &str| rows.iter().find(|(l, _)| l == label).map(|(_, n)| *n).unwrap_or(0);
        let m = get(GEN_GUARD);
        assert_eq!(
            m,
            0,
            "{}: {m} cached translation(s) did not survive re-interpretation",
            f.file_stem().unwrap().to_string_lossy()
        );
        misses += m;
        translated += get(GEN_TRANSLATED);
    }
    assert!(translated > 0, "nothing was ever translated, so the guard row proves nothing");
    assert_eq!(misses, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// The general ι rule (`RECURSOR-DESIGN.md` §3.4/§5.2, `WIRING-DESIGN.md` §6.4).
//
// **No tutorial export reaches it.** The shapes it computes for are the ones
// with a nullary constructor *and* a constructor with fields, and every
// two-constructor tutorial enumeration is claimed by `enum_rec_shape` first —
// `WIRING-DESIGN.md` §12.9, confirmed again here: the `ι sites the general rule
// computed` row is zero on all 91. So the assertions that the deliverable
// works have to be made on `init-prelude`, which is where the corpus's masked
// shapes live (`Lean.Name.str : Name → String → Name`, mask `Rec, Plain`).
// ─────────────────────────────────────────────────────────────────────────────

const GEN_NESTS: &str = "recursors given a general nest";
const GEN_FIRED: &str = "ι sites the general rule computed";
const GEN_TPOLICY: &str = "…declined (recursor): T-policy 2/3, HYP not dischargeable";
/// The four rows that say a per-thread store was consulted and **not** used.
/// Every one of them is zero on `init-prelude`, and that is the statement that
/// the interpretation is a function of `(name, ground levels)` on this corpus.
const GEN_SPEC_DECLINED: &str = "cached specs declined: βⱼ bodies not canonical";
const GEN_REC_REBUILT: &str = "cached recursors declined: not over this carrier";
const NEST_DECLINED: &str = "shared nests declined: not over this walk/translation";
const CTOR_NEST_DECLINED: &str = "shared constructor nests declined: not over this translation";
/// The two rows the four above are read *through*: a store that stops hitting
/// declines silently, but the symbol it then mints is counted here.
const IND_REMINT: &str = "shared inductive symbols declined: body not canonical";
const CONST_REMINT: &str = "shared symbols declined: body not canonical";

/// **`T`-policy 2 builds a nest**, which policy 1 alone could not.
///
/// Policy 1 — every constructor nullary, `T := fin(s⃗)` — was the whole of what
/// rung 3 wired, and it reaches no declaration with a field. Policy 2 takes `T`
/// to be the motive's value at the first nullary constructor, **as the nest
/// walked it**, which is what a declaration like `Lean.Name` needs. The
/// tutorials cannot show the ι rule firing, but they can show the nest being
/// built where it previously declined, and that the files it appears in do not
/// move — which is the other half of the claim.
///
/// **The nests those four files used to build were a bug, and this is the
/// assertion that keeps them from coming back.**
///
/// This test used to read the opposite way: it asserted that `042`, `068`,
/// `075` and `077` each built one general recursor nest, as the evidence that
/// `T`-policy 2 was reachable. They did — and every one of them was for a
/// declaration the **hand-written stack owns**. While an inductive is being
/// checked, the checker installs a temporary `InductiveData` with
/// `is_recursive: false` (`inductive.rs:115`), so `nat_shape`/`list_shape`
/// refuse their own declarations for the duration and the general path picks
/// them up — a second carrier and a re-minted `⟦N⟧`/`⟦List⟧` for the length of
/// the check, which is `Dt::IndDrift` and the recorded failure that cost 54 ι
/// sites. `TgBackend::recognised_ind` closes the window, and with it closed
/// **no tutorial export builds a general recursor nest at all**.
///
/// The claim those four files were standing in for — that policy 2 is
/// reachable — is asserted where it is true, on `init-prelude`, by
/// [`the_general_iota_rule_computes_on_the_prelude`]: **five** nests and 92 ι
/// sites. (The nest count read 77, then 75, while a nest was rebuilt once per
/// declaration that reached it; `Shared::gen_ctor_nests` made the five distinct
/// nests the whole of it. The ι sites, which are what the reach claim is really
/// about, did not move.)
///
/// Verified to fire by making `recognised_ind` ask `list_shape`/`nat_shape` for
/// their `is_recursive` clause again: the four files' nest rows come back.
#[test]
fn no_tutorial_export_builds_a_general_recursor_nest() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let mut files: Vec<PathBuf> =
        std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok().map(|e| e.path())).collect();
    files.retain(|p| p.extension().is_some_and(|x| x == "ndjson"));
    files.sort();
    for f in &files {
        let n = gen_row(f, GEN_NESTS);
        assert_eq!(
            n, 0,
            "{}: {n} general recursor nest(s) — a recogniser-owned declaration leaked into the \
             general path, most likely through the `is_recursive` window",
            f.file_stem().unwrap().to_string_lossy()
        );
    }
}

/// **The deliverable: the general ι rule computes, at masked and multi-field
/// constructors — and policy 3 still declines.**
///
/// Both halves are asserted here, off **one** run of the checker, because that
/// run is expensive: `init-prelude` is the only corpus export that reaches the
/// general ι rule at all (see
/// [`no_tutorial_export_reaches_the_general_iota_rule`]), and a debug-profile
/// pass over it costs about four minutes. Everything below is read out of a
/// single report rather than by asking three times.
///
/// # What fires
///
/// 80 sites, over three declarations, all of them shapes no recogniser reaches:
///
/// | declaration | constructors | fields |
/// |---|---|---|
/// | `Lean.Name` | `anonymous`, `str`, `num` | mask `Rec, Plain` |
/// | `Lean.SourceInfo` | `original`, `synthetic`, `none` | four and three plain |
/// | `Lean.Macro.Exception` | `unsupportedSyntax`, `error` | two plain |
///
/// `Lean.Name.str` is the target `WIRING-DESIGN.md` §8 names, and it is the
/// interesting one twice over: its mask is interleaved, so an unpermuted
/// premise list would fail the positional check at every site, and it has a
/// live recursive call, so the reduct's `⟦Name.rec C s⃗ n⟧` has to be recovered
/// from the rule's `app(grec, n)`.
///
/// # What must still decline
///
/// A declaration with **no** nullary constructor has no canonical closed point
/// for the motive, so no single target makes `HYP` both true and derivable
/// (`RECURSOR-DESIGN.md` §5.2 option 3). `Lean.ParserDescr` is the corpus's
/// instance, and its 169 ι sites stay counted gaps. That row must stay
/// **nonzero**: a zero would mean the gate had been widened past what the
/// design admits — and measurably buys nothing, since widening it builds 150
/// more `GenRecursor`s and closes no gap.
///
/// The three counts are a **ratchet**: `≥` on the sites, `≤` on the two costs,
/// so an improvement passes and a regression fails.
///
/// Verified to fire by making `fire_general` refuse a non-empty `fields` — rung
/// 3's behaviour: the site count drops to 26 (the nullary constructors alone)
/// and gaps rise to 15923. And by deleting `gen_rec_bottom`'s `T`-policy gate:
/// the decline row goes to zero.
#[test]
fn the_general_iota_rule_computes_on_the_prelude() {
    let f = corpus().join("good/init-prelude.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    let text = report(&f);
    let row = |label: &str| -> u64 {
        let mut inside = false;
        for l in text.lines() {
            if l.trim_start().starts_with("the general inductive path") {
                inside = true;
                continue
            }
            if inside {
                if !l.starts_with("    ") {
                    break
                }
                if let Some((k, n)) = l.trim().rsplit_once(char::is_whitespace) {
                    if k.trim() == label {
                        return n.parse().unwrap_or(u64::MAX)
                    }
                }
            }
        }
        0
    };
    let fired = row(GEN_FIRED);
    assert!(
        fired >= 80,
        "the general ι rule computed at {fired} sites, expected at least 80 — \
         `Lean.Name`/`SourceInfo`/`Macro.Exception` between them have that many"
    );
    // **Where `T`-policy 2's reachability is asserted.** It used to be four
    // tutorial files, and those turned out to be the `is_recursive` window
    // rather than the policy — see
    // [`no_tutorial_export_builds_a_general_recursor_nest`]. `init-prelude` is
    // where it is real.
    //
    // **This row counts nests *built*, and that stopped being the same as nests
    // *reached*.** It read 75 while the `βⱼ` guard was missing: five distinct
    // nests, each rebuilt roughly once per declaration that reached it, with the
    // 70 rebuilds counted beside it by [`GEN_REC_REBUILT`]. With
    // `Shared::gen_ctor_nests` closing the canonicity cascade the two rows read
    // 5 and 0 — the same five nests, each built once. So the reach ratchet is
    // `≥ 5`, and the rebuild row is pinned at zero next to it: a store that
    // silently stopped hitting would push this row back up and fail *there*,
    // which is what keeps `5` from being a loosening.
    let nests = row(GEN_NESTS);
    assert!(nests >= 5, "only {nests} general recursor nests, expected at least 5");
    let declined = row(GEN_TPOLICY);
    assert!(
        declined > 0,
        "no recursor declined on the `T`-policy; policy 3 is not being enforced"
    );
    // **The canonicity invariant this whole store discipline exists for**: one
    // interpretation per `(name, ground levels)` for the run, so that a theorem
    // derived while checking one declaration is about the terms the next one
    // builds. Each of the four rows is a *different* store declining, and each
    // was nonzero at some point in this file's history; the last to close was
    // the `βⱼ` one, at 5630, which the other three were downstream of.
    // A missing row would read zero and pass, so the row's presence is asserted
    // first: this must fail when the ledger changes, not go quiet.
    for label in [GEN_SPEC_DECLINED, GEN_REC_REBUILT, NEST_DECLINED, CTOR_NEST_DECLINED] {
        assert!(
            text.lines().any(|l| l.trim_start().starts_with(label)),
            "the report no longer has a `{label}` row"
        );
        assert_eq!(
            rows_totalling(&text, label),
            0,
            "`{label}` is nonzero: the interpretation is not canonical across declarations"
        );
    }
    // **The four rows above are the stores declining; these two are what it
    // costs.** A store can also stop hitting without declining — by never being
    // consulted — and then every one of the four stays zero while a symbol is
    // re-minted anyway. So the re-mint counters are pinned beside them, and
    // their presence is asserted first for the same reason as above: a row that
    // vanished from the ledger reads zero and would pass.
    for label in [IND_REMINT, CONST_REMINT] {
        assert!(
            text.lines().any(|l| l.trim_start().starts_with(label)),
            "the report no longer has a `{label}` row"
        );
    }
    // `⟦T.rec⟧` was the last one open. All 85 inductive re-mints on this corpus
    // were general recursor nest heads (`Lean.Name.rec` 50, `Lean.SourceInfo.rec`
    // 22, `Option.rec` 7, `Lean.Macro.Exception.rec` 6), because
    // `Shared::rec_nests` refused to store a `RecBottom::General`; sharing it
    // takes the row to **0**, and it is an equality, not a ratchet — one
    // re-minted inductive symbol is one constant with two denotations.
    //
    // Verified to fire by restoring the exclusion (`if !matches!(nest.bottom,
    // RecBottom::General(..))` at the store site): this reads 85 again and fails
    // here, with `CONST_REMINT` back at 173.
    assert_eq!(
        rows_totalling(&text, IND_REMINT),
        0,
        "`{IND_REMINT}` is nonzero: an inductive or recursor has two denotations in one run"
    );
    // **The constant row is a ratchet at 15, and the 15 are two named causes
    // neither of which is a store.** `String.utf8EncodeChar` 6 and
    // `List.utf8Encode` 6 (its value mentions the first) drift because
    // `TgBackend::interp`'s `Expr::Let` arm is the one `define_abbrev` site with
    // no per-thread store at all — nine let-mints on this corpus, and two of
    // them are the pair that drifts. `outParam` 3 drifts with the *same* head
    // symbol and a different argument: it is interpreted at an instantiation
    // still mentioning a universe parameter, and the two backends build
    // `imax`/`max` level terms of different shapes for it. Both are levers of
    // their own; neither is a nest.
    let const_remint = rows_totalling(&text, CONST_REMINT);
    assert!(
        const_remint <= 15,
        "`{CONST_REMINT}` is {const_remint}, ratchet 15 — a store stopped hitting"
    );
    // **Threading stage 0's measurable: proof irrelevance does not search.**
    //
    // `is_proof` establishes `⟦e⟧ ∈ ⟦α⟧` and `⟦α⟧ ∈ U₀`; those are exactly the
    // two premises `derive_point_of_proof` used to look for with `has_type_a`,
    // one rule later, having watched them be thrown away. They are handed to
    // `Certifier::proof_irrel` now, and this row is what says so. It is an
    // **equality, not a ratchet**: a single search here is a threading leak,
    // and a leak that is allowed to be "no worse than before" is one nobody
    // finds.
    //
    // The row's presence is asserted first, for the reason the store rows above
    // give: a row that vanished from the ledger reads zero and would pass. The
    // other two search rows are deliberately *not* pinned — they are asked by
    // `point_the_subject` and by the `admit` fall-through, which stages 1-2
    // starve, and pinning them now would pin the scaffolding.
    const POP_IRREL: &str = "…asked by proof irrelevance";
    assert!(
        text.lines().any(|l| l.trim_start().starts_with(POP_IRREL)),
        "the report no longer has a `{POP_IRREL}` row"
    );
    assert_eq!(
        rows_totalling(&text, POP_IRREL),
        0,
        "proof irrelevance searched for a premise inference had already established"
    );
    let gaps = rows_totalling(&text, "TOTAL gaps");
    // 15572 → 15492 when the type former's `np > 0` nest landed: twelve more ι
    // sites and 1164 more `CtorApp` typing discharges. 15492 → 15423 when
    // projection congruence and proof irrelevance became rules fed by the
    // evidence inference already had (threading stage 0): 16 `def_eq_proj`
    // admissions and their cascade.
    //
    // **15423 → 15455, and the rise is the result.** `TgBackend::admit` used to
    // try `proof_eq` before reporting a gap, and rescue the step whenever both
    // sides happened to interpret to `•`. Measured, that was 20 steps a run,
    // every one of them `Admit::ProjRed` — a projection reduction with no
    // certificate, recorded as derived because the two sides were proofs. The
    // attempt is gone, those 20 gaps are visible, 48 more appear in the
    // congruence cascade above them, and 36 escapes go away with the
    // conditional certificates the rescue used to manufacture. A ratchet that
    // was moved *upward* has to say why, and this is why: the gaps were always
    // there.
    //
    // **15455 → 15423, and it is the same 20 steps, now derived under the
    // reduction's own name.** `Certifier::proj_red` exists, `whnf` records
    // `Rule::ProjRed` rather than an admission, and the checker infers both
    // endpoints and hands the rule Carneiro's Theorem 6.7 premises. See
    // [`projection_reduction_is_a_rule_fed_by_inference`] for what closes and
    // by which route.
    //
    // **15423 → 15542, and the rise is one row: the boundary-escape count.**
    // `infer_app` now certifies the `ensure_pi` reduction of the head's type
    // and converts the head's typing along it (`THREADING-CENSUS.md` §1.2's
    // silently dropped leg; stage 2's first slice). A leg with a beta step
    // carries that step's domain obligation as an antecedent, and the leg is
    // handed to `ty_conv` *borrowed* — deliberately unconsumed, see
    // `Certifier::ty_conv`'s doc — so every conditional leg is counted at the
    // boundary: +119 in `gap: undischarged assumption … survived to the
    // boundary`, and nowhere else (every other gap row is flat or falls;
    // `ty_app` holes fall 481 → 418). Before this, the same reductions
    // happened *uncertified* — the obligations existed and were invisible.
    // Bought: +252 derived kernel theorems, +111 conversions carried, and 7
    // declaration typings stored (19 → 26) whose antecedent-free derivations
    // the composed leg completed. Stage 1's binder context is what discharges
    // these antecedents; a further rise with no such purchase still fails
    // here.
    assert!(gaps > 0 && gaps <= 15542, "init-prelude: {gaps} gaps, ratchet 15542 — the general ι path regressed");
    let esc: u64 = text
        .lines()
        .find(|l| l.trim_start().starts_with("conditional derivations:"))
        .and_then(|l| {
            let toks: Vec<&str> = l.split_whitespace().collect();
            let i = toks.iter().position(|t| *t == "escaped")?;
            toks[i - 1].parse().ok()
        })
        .expect("the report line names an escape count");
    // **The escape ratchet moves the wrong way, and it is bought.** 2145 → 2153
    // when the `np > 0` nest landed: this is the recorded `076` pattern at
    // prelude scale — closing a gap beneath a conditional certificate lets the
    // certificate escape — and the trade is 80 gaps for 8 escapes. Loosened
    // deliberately rather than silently: a *further* rise with no gap movement
    // is still a regression and still fails here.
    // 2153 → 2138 with threading stage 0, in the *right* direction and for a
    // reason worth recording: `Certifier::eta` and `Certifier::proj_cong` now
    // **take** the certificates their call sites used to drop, and a
    // conditional certificate a rule takes is accounted for rather than
    // escaping. 2138 → 2102 when `admit` stopped guessing — see the gap ratchet
    // above; a rescue that fired produced a conditional certificate, and every
    // one of those had to escape.
    // 2102 → 2138 when projection reduction became a rule: the derivations the
    // rescue used to manufacture are back, built from threaded premises instead
    // of searched ones, and they are conditional for the same reason they always
    // were — `⟦α⟧ ∈ U₀` for these α rests on the ambient locals' typings. Bought
    // by 32 gaps, and it is the *same* trade as the one recorded above, run
    // backwards.
    // 2138 → 2257 with the `ensure_pi` leg composed into the head typing —
    // the same +119 as the gap ratchet above, one row, one mechanism: a
    // conditional reduction certificate now exists where the reduction used
    // to run uncertified, and `ty_conv` borrows rather than consumes it. See
    // the gap ratchet's paragraph for what it buys and why the over-report is
    // the safe direction; stage 1 is what brings both counters down.
    assert!(esc <= 2257, "init-prelude: {esc} escapes, ratchet 2257 — the general ι path regressed");
}

/// **How much of the prelude is actually translated** — the declaration-typing
/// ledger, read as a completeness measure rather than as a cache hit rate.
///
/// `Shared::declar_typings` is not a cache. The claim this project exists to
/// establish is that a Lean declaration `c : T` becomes a target-theory theorem
/// `⊢ ⟦c⟧ ∈ ⟦T⟧`, and that store is where such a theorem lives. A declaration
/// with no entry is a declaration that has **not been translated** — so the
/// headline number for `init-prelude` is not its 15423 definitional-equality
/// gaps, which count steps inside checking, but this: of **2891**
/// (declaration, σ) pairs with a value, **19** carry a proof of their own
/// typing. `mini`'s counterpart is 121 of 223.
///
/// # The three ways a pair fails to be translated, and why they are separated
///
/// The rows used to be `Seen`, `FromInfer`, `Conditional` and an unnamed
/// arithmetic residue, and the residue was two different things:
///
/// * **`Gap` — 2674.** Inference produced no certificate at all, because the
///   declaration's own check gapped. A genuine absence, and cascade: it is
///   interpretation scope, not threading debt.
/// * **`Conditional` — 198.** Inference *established* the typing and it was
///   thrown away, because the derivation stood under antecedents. A certificate
///   that was computed and discarded is threading debt by definition, and this
///   is the row that says how much of it there is.
/// * **`NoKey` — 0.** A temporary declaration, whose name is interned in a
///   per-declaration arena; nothing can key it and nothing is owed.
///
/// The identity `Seen = NoKey + Gap + Conditional + FromInfer` is asserted, not
/// assumed: an unaccounted residue is exactly what let these two be conflated.
///
/// # And the size of the lever
///
/// `MissCond` — **1161** of the 31256 use-site misses are against a typing that
/// was derived and discarded. That is what storing conditional typings could
/// answer, at best, and `TgBackend::store_declar_typing`'s doc records what was
/// measured about whether it would help: the antecedents are hoisted guarded
/// families, `discharge_families` closes none of them, and storing one would
/// move a `ty_const` gap into the escape ledger rather than close it.
///
/// # And what those antecedents are, which is why the lever does not move
///
/// The three rows beneath `Conditional` are the census of the antecedents
/// themselves rather than of the declarations carrying them, and they are what
/// settles whether discharging the family is reachable from here:
///
/// * **`CondHyp` — 200.** Every one is a hoisted guarded family, so
///   `CondHyp = CondNest + CondMem` is asserted below. An antecedent of a
///   fourth kind must add a row rather than disappear into a residue; that is
///   the same discipline the `Seen` identity above enforces, and for the same
///   reason.
/// * **`CondNest` — 170.** A family whose body is itself a family.
///   `peel_family` declines these, so recursing into the nesting is missing
///   plumbing — and unwrapping them by hand to the innermost membership, under
///   every guard collected on the way, derives 0 of 170.
/// * **`CondMem` — 30.** The shape `peel_family` attempts. Every one is about a
///   structure projection `⟦s.i⟧`, whose typing `has_type_proj` can only
///   acquire and never derive.
///
/// So both plumbing gaps on this path — no peel for typing certificates, no
/// recursion into nested families — are worth exactly zero, and neither
/// `Conditional`, `MissCond` nor `Stored` can move until `⟦s.i⟧` has a typing.
/// The ratchets below are one-directional for the same reason they always were;
/// what is new is that a *rise* in `CondMem` is the signal worth watching, since
/// it is the row a stronger `has_type` would show up in first.
#[test]
fn the_declaration_typing_ledger_accounts_for_every_declaration() {
    let f = corpus().join("good/init-prelude.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    let text = report(&f);
    let row = |label: &str| -> u64 {
        assert!(
            text.lines().map(str::trim_start).any(|l| l.starts_with(label)),
            "the report no longer has a `{label}` row — a vanished row reads zero and would pass"
        );
        rows_totalling(&text, label)
    };

    let seen = row("declarations with a value");
    let nokey = row("…of a temporary declaration, which no store can key");
    let gap = row("…whose typing inference could not justify at all");
    let cond = row("…derived only under antecedents");
    let from_infer = row("…carried out of inference, not searched for");
    let refused = row("…derived, but the store's own checks refused it");
    let stored = row("…stored as ⟦c⟧ ∈ ⟦T⟧");
    let hit = row("uses answered from the store");
    let miss = row("uses with no entry (or at other levels)");
    let miss_cond = row("…of them against a typing that was derived and discarded");
    let cond_hyp = row("…the antecedents they carry, each a hoisted guarded family");
    let cond_nest = row("…of them a family of families, which peeling declines");
    let cond_mem = row("…of them a membership ⟦a⟧ ∈ ⟦A⟧, which peeling would attempt");

    // **Every pair is accounted for.** This is the assertion the split exists
    // for: while the residue was arithmetic, `Gap` and `Conditional` were one
    // number, and they call for opposite work.
    assert_eq!(
        seen,
        nokey + gap + cond + from_infer,
        "the declaration-typing ledger does not account for all {seen} pairs: \
         {nokey} no-key + {gap} gap + {cond} conditional + {from_infer} from-infer"
    );
    assert_eq!(from_infer, stored + refused, "a pair carried out of inference is either stored or refused");

    // Ratchets, in the direction that says progress. `stored` and `hit` may only
    // rise; `cond`, `gap` and `miss_cond` may only fall.
    // 19 → 26 stored (and 2674 → 2667 never-derived) when `infer_app` began
    // composing the `ensure_pi` leg into the head's typing: seven value
    // typings that used to run out of evidence at the unreduced head type now
    // complete antecedent-free and pass `Sealed`.
    assert!(stored >= 26, "only {stored} declaration typings stored, was 26");
    assert!(hit >= 1308, "only {hit} uses answered from the store, was 1308");
    assert!(cond <= 198, "{cond} typings derived and discarded, was 198");
    assert!(gap <= 2667, "{gap} typings with no certificate at all, was 2667");
    // 1161 → 1165 with the same change, and 1165 → 1214 when the
    // interpretation's binder opens moved to keyed de Bruijn levels. `cond`
    // itself is unchanged at 198 both times: no typing was newly discarded —
    // the store's *ask* traffic shifted, and more of the (unchanged) misses
    // land on keys whose typing was derived under antecedents. A rise here
    // with `cond` flat is attribution churn, not new discarding; a rise
    // *with* `cond` is the regression this pin is for.
    assert!(miss_cond <= 1214, "{miss_cond} misses against a discarded typing, was 1214");
    // Sanity: the store is consulted, and it mostly misses. Stated so that a
    // change that stops consulting it fails here rather than reading as a win.
    assert!(miss > hit, "the declaration-typing store stopped being the minority answer — {hit} hits, {miss} misses");
    assert!(miss_cond <= cond * 64, "misses attributed to discarded typings ({miss_cond}) outrun {cond} discards implausibly");

    // **The antecedents are accounted for too.** Every one is a hoisted guarded
    // family, and every family is either a nesting or a membership; an
    // antecedent of some other shape is a new fact about this path and must be
    // given its own row rather than be absorbed.
    assert_eq!(
        cond_hyp,
        cond_nest + cond_mem,
        "the {cond_hyp} antecedents of the {cond} conditional typings are not accounted for: \
         {cond_nest} nested + {cond_mem} membership"
    );
    // Each conditional typing carries at least one antecedent — that is what
    // makes it conditional — and, measured, at most two: 196 carry one and two
    // carry two.
    assert!(cond_hyp >= cond, "{cond} conditional typings carry only {cond_hyp} antecedents between them");
    assert!(cond_hyp <= cond * 2, "{cond} conditional typings carry {cond_hyp} antecedents, more than two each");
    // Ratchets, in the direction that says progress: fewer antecedents owed,
    // and fewer of them in the shape nothing can even attempt. `cond_mem` is
    // deliberately *not* ratcheted — it may rise, and a rise is the first thing
    // a stronger `has_type` would show here — but it is read above so that the
    // identity covers it.
    assert!(cond_hyp <= 200, "{cond_hyp} antecedents owed by conditional typings, was 200");
    assert!(cond_nest <= 170, "{cond_nest} of them families of families, was 170");
}

/// **Projection reduction is a rule, and inference feeds it** — and the two
/// numbers that say so are not the same number.
///
/// `whnf` used to record a projection contraction as `Rule::Admitted`, so the
/// only thing that ever saw the step was `Certifier::admit`. While `admit` had
/// an optimistic fall-through it rediscovered, by itself, that both endpoints
/// were proofs, and passed 20 steps a run off as derived under the label of the
/// funnel rather than of the reduction. The fall-through is gone;
/// `Certifier::proj_red` is where those steps are answered now.
///
/// # What is pinned, and why each row
///
/// * `gap: proj_reduce` at **630** — a ratchet on the rule's own decline, which
///   is where a projection reduction the backend cannot justify now reports.
///   630 is the honest residue: no interpretation of structures exists, so the
///   constructor's computation rule is out of reach (`INDUCTIVES.md`), and what
///   closes is only the population where both endpoints are proofs.
/// * The `…threaded, asked by projection reduction` row must **exist and be
///   nonzero**. A row that vanished from the ledger reads zero and a `≤`
///   assertion would pass; a zero here means the rule is declining before it
///   reaches the derivation, which is exactly the state this test was written
///   against — the first implementation scored zero on it and looked, from the
///   gap total alone, indistinguishable from no change at all.
/// * The three **search** rows must not move. This is the load-bearing claim:
///   the 20 did not close because a searching caller disappeared, they closed
///   because a new asker was handed premises. `…asked by the admit fall-through`
///   is zero and stays zero (the fall-through is deleted), `…asked by a proof
///   λ's body clause` and `…asked by a reduction rule's proof shortcut` are the
///   two remaining searchers and neither is touched by this stage. If a later
///   change closes projection reductions by *searching* again, the middle row
///   moves and this test says so.
///
/// # The thing that made this work, recorded because it is not obvious
///
/// The checker's `is_proof` says **no** at every one of the 650 sites. Inference
/// runs at the declaration's own universe parameters, so the type `motive t`
/// with `motive : Π t. Sort u` is not a proposition — `u` is a parameter. The
/// backend's `term_clause` says **yes**, because it reads levels through
/// `TcCtx::under_sigma` and the instantiation in force sends `u` to `0`. Both
/// are right; they are answering different questions, and `TypeChecker::PropAt`
/// is where that is now written down. Handing over a witness built at the
/// parameters closes **nothing**; handing over one built under σ closes the 20.
#[test]
fn projection_reduction_is_a_rule_fed_by_inference() {
    let f = corpus().join("good/init-prelude.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    let text = report(&f);

    const THREADED: &str = "…threaded, asked by projection reduction";
    const SHORTCUT: &str = "…asked by a reduction rule's proof shortcut";
    const LAM_CLAUSE: &str = "…asked by a proof λ's body clause";
    const FALLTHROUGH: &str = "…asked by the admit fall-through";
    for label in [THREADED, SHORTCUT, LAM_CLAUSE, FALLTHROUGH] {
        assert!(
            text.lines().map(str::trim_start).any(|l| l.starts_with(label)),
            "the report no longer has a `{label}` row — a vanished row reads zero and would pass"
        );
    }

    let proj_red = rows_totalling(&text, "gap: proj_reduce");
    assert!(
        proj_red > 0 && proj_red <= 630,
        "init-prelude: {proj_red} proj_reduce gaps, ratchet 630 — projection reduction regressed"
    );

    let threaded = rows_totalling(&text, THREADED);
    assert!(
        threaded >= 11,
        "only {threaded} projection reductions reached the threaded derivation, expected at least 11 — \
         the rule is declining before it gets there"
    );

    // The search population is untouched: 34, 41 and 0 at the measurement.
    assert_eq!(rows_totalling(&text, FALLTHROUGH), 0, "the admit fall-through is deleted and must stay deleted");
    assert!(
        rows_totalling(&text, SHORTCUT) <= 34,
        "the `beta`/`zeta`/`delta`/`iota` proof shortcut is searching more than it did — \
         projection reduction is supposed to be fed, not to search"
    );
    assert!(
        rows_totalling(&text, LAM_CLAUSE) <= 41,
        "`point_the_subject` is searching more than it did"
    );
}

/// **No tutorial export reaches the general ι rule**, and the row says so.
///
/// Recorded as an assertion rather than as a remark because it is the reason
/// the test above has to run `init-prelude`: if a tutorial ever *does* reach
/// it, that is the moment to move the acceptance evidence somewhere cheaper,
/// and this is what will say so.
#[test]
fn no_tutorial_export_reaches_the_general_iota_rule() {
    let dir = corpus().join("good/tutorial");
    if skip_guard::absent(&dir) {
        return
    }
    let mut files: Vec<PathBuf> =
        std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok().map(|e| e.path())).collect();
    files.retain(|p| p.extension().is_some_and(|x| x == "ndjson"));
    files.sort();
    for f in &files {
        let n = gen_row(f, GEN_FIRED);
        assert_eq!(
            n, 0,
            "{}: {n} general ι site(s) — the tutorials now exercise the rule, \
             so `the_general_iota_rule_computes_on_the_prelude` can be made cheaper",
            f.file_stem().unwrap().to_string_lossy()
        );
    }
}

/// **The declaration-boundary quantifier stores, answers, and keys by level
/// expression** — `LEVELPOLY.md` §5.3 step 5, on its own fixture.
///
/// `test_resources/LevelPoly/export` is five universe-polymorphic
/// definitions — the atoms this pin needs, because two pass under each of the
/// bugs it is written against:
///
/// * `myty.{u} : Sort (u+2) := Sort (u+1)` — its value typing is the sort rule
///   at a *variable* level, conditional on exactly `u ∈ ω`, so the boundary
///   must quantify it: `⊢ ∀u. u ∈ ω → ⟦myty⟧(u) ∈ srt(succ (succ u))`.
/// * `myty2.{u} : Sort (u+2) := myty.{u}` — a use **at the same parameter
///   name**, whose key matches the stored entry: the quantified store answers
///   it, conditionally, and the answer is itself quantified at *its* boundary.
/// * `myothr.{v} : Sort (v+2) := myty.{v}` — a use **at a different parameter
///   name**, whose key does not match. It must *miss* the quantified store —
///   the entry is per level expression, not per constant — so its own value
///   typing stays a counted gap and it is *not* quantified at its boundary;
///   pinning both counts exactly is what makes a key that stopped
///   discriminating fail here.
/// * `mypair.{u,v} : Sort (max u v + 2) := Sort (max u v + 1)` and
///   `mypair2.{u,v} := mypair.{u,v}` — the **two-parameter** pair, without
///   which the quantifier *prefix order* is unobservable: with one variable,
///   generalising forward and in reverse coincide, and the first version of
///   this test stayed green under exactly that mutation. With two, a wrong
///   prefix re-opens with the antecedents swapped, the guard refuses, and the
///   hit count drops.
///
/// Both runs are under `NANODATG_NO_SCHEDULE=1`, the deletion's staging
/// switch: under the σ-schedule a definition is only ever interpreted at
/// ground levels, so the boundary the quantifier guards is unreachable — the
/// pre-deletion prelude measures exactly 0 on both rows, and this fixture is
/// the reason that 0 is "not yet reachable" rather than "cannot fire". The
/// flag-off run is the wedge's standing bit-identity promise: both rows zero
/// even in the staged state.
///
/// Mutations run against this test (each made the cell red, then was
/// reverted): generalising in forward order instead of reverse leaves the
/// quantifier prefix inverted on `mypair`, `gen_checked` and the re-open
/// guard between them refuse it, and the store row reads 3; generalising the
/// *untransported* theorem — about `⟦val⟧` instead of `⟦c⟧` — is refused at
/// the consult guard, the conditional answers never happen, and the store
/// row reads 2.
#[test]
fn the_declaration_boundary_quantifier_stores_and_answers() {
    let export = Path::new(env!("CARGO_MANIFEST_DIR")).join("test_resources/LevelPoly/export");
    let run = |flag: &str| -> String {
        let cfg_path = tmp_cfg(&format!("lp{flag}"), &export);
        let cfg = format!(
            r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true, "print_success_message": false}}"#,
            serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
        );
        std::fs::write(&cfg_path, cfg).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin"))
            .arg(&cfg_path)
            .env("NANODATG_LEVELPOLY", flag)
            .env("NANODATG_NO_SCHEDULE", "1")
            .output()
            .expect("spawn");
        let _ = std::fs::remove_file(&cfg_path);
        assert!(out.status.success(), "the LevelPoly fixture must be accepted (flag={flag})");
        String::from_utf8_lossy(&out.stderr).into_owned()
    };

    const STORED: &str = "…quantified at the boundary and stored";
    const HIT: &str = "uses answered from the quantified store, conditionally";

    let on = run("1");
    // `myty` and `mypair` quantify their own sort-rule typings at the
    // boundary; `myty2` and `mypair2` quantify the store's conditional
    // answers in turn. `myothr` misses the store, so its value typing has no
    // evidence and nothing to quantify — exactly 4, not 5.
    assert_eq!(
        rows_totalling(&on, STORED),
        4,
        "the boundary quantifier stored {} declarations, expected exactly 4 \
         (myty, myty2, mypair, mypair2; myothr's different-name key must miss):\n{on}",
        rows_totalling(&on, STORED)
    );
    // …and exactly two uses — `myty2`'s and `mypair2`'s, at the matching
    // parameter names — are answered from the store. `myothr`'s must miss:
    // its key is a different level expression.
    assert_eq!(
        rows_totalling(&on, HIT),
        2,
        "the quantified store answered {} uses, expected exactly 2 \
         (a per-name key stopped discriminating, or a same-name use missed):\n{on}",
        rows_totalling(&on, HIT)
    );

    let off = run("0");
    assert_eq!(rows_totalling(&off, STORED), 0, "flag off must be bit-identical: nothing stored");
    assert_eq!(rows_totalling(&off, HIT), 0, "flag off must be bit-identical: nothing answered");
}

/// **The ω-prefix lets a polymorphic inductive's nest build at its own
/// parameters** — `LEVELPOLY.md` §5.4 blocker 2, first slice.
///
/// `037_prodType` is `Prod.{u,v} : Type u → Type v → Type (max u v)` — the
/// corpus's own two-parameter polymorphic inductive, and two parameters
/// matter: a one-parameter pin passes under a prefix that mishandles order
/// (the same two-atoms lesson as `mypair` above). In the staged state its
/// parameter domains interpret to `srt(u)`/`srt(v)` at *variable* levels, so
/// before the prefix landed `gen_ty_nest`'s `define_abbrev(xs = params)`
/// refused the whole nest (`…declined: the parameter nest refused`, 60 on
/// `init-prelude`), the constructor got no rule, and the declaration did not
/// translate. With the ω-variables threaded as leading arguments of every
/// body symbol and graph, the nest builds and the file is fully derived.
///
/// Mutation run against this test (red, then reverted): returning an empty
/// prefix from `omega_prefix` reproduces the refusal — translated reads 0,
/// constructor rules read 0, and the gap total is nonzero.
#[test]
fn the_omega_prefix_builds_the_polymorphic_nest_in_the_staged_state() {
    let f = corpus().join("good/tutorial/037_prodType.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    let cfg_path = tmp_cfg("omga", &f);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true, "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&f.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin"))
        .arg(&cfg_path)
        .env("NANODATG_LEVELPOLY", "1")
        .env("NANODATG_NO_SCHEDULE", "1")
        .output()
        .expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    assert!(out.status.success(), "037_prodType must be accepted in the staged state");
    let text = String::from_utf8_lossy(&out.stderr).into_owned();
    assert_eq!(
        rows_totalling(&text, "…declined: the parameter nest refused"),
        0,
        "the ω-prefix stopped covering Prod's parameter domains:\n{text}"
    );
    assert_eq!(
        rows_totalling(&text, "declarations translated"),
        1,
        "Prod did not translate at its own parameters:\n{text}"
    );
    assert_eq!(
        rows_totalling(&text, "constructors given a term and a typing rule"),
        2,
        "Prod.mk's rule population moved:\n{text}"
    );
    assert_eq!(
        rows_totalling(&text, "TOTAL gaps"),
        0,
        "037_prodType stopped being fully derived in the staged state:\n{text}"
    );
}

/// `057_typeWithTypeFieldPoly` is a polymorphic inductive **with a
/// `Type u`-valued field** — the exact shape `LEVELPOLY.md` §5.4 blocker 2b
/// names: the field's interpretation mentions the ω-variable `û`, and before
/// route (ii) landed, `walk_spec`'s `define_abbrev(xs = params ++ plains)`
/// refused the `βⱼ` body (`…declined: field type at a variable level`, 76 on
/// `init-prelude`), so the declaration did not translate. With the
/// declaration's level variables riding as leading machine parameters
/// (`np' = nw + np`) the abbreviation is total and the file is fully derived
/// in the staged state.
///
/// One field is enough for *this* pin because the ordering hazard has its own
/// discipline (`gi.omega` is declaration-ordered and single-sourced); the
/// two-parameter ordering itself is pinned by `037_prodType` above, whose
/// carrier takes `w_u, w_v` in declaration order.
///
/// Mutation run against this test (red, then reverted): making
/// `omega_of_levels` return the empty list restores the refusal — the
/// `…declined: field type at a variable level` row comes back and the
/// declaration count drops to zero.
#[test]
fn route_ii_translates_a_type_valued_field_in_the_staged_state() {
    let f = corpus().join("good/tutorial/057_typeWithTypeFieldPoly.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    let cfg_path = tmp_cfg("lvar", &f);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true, "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&f.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin"))
        .arg(&cfg_path)
        .env("NANODATG_LEVELPOLY", "1")
        .env("NANODATG_NO_SCHEDULE", "1")
        .output()
        .expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    assert!(out.status.success(), "057 must be accepted in the staged state");
    let text = String::from_utf8_lossy(&out.stderr).into_owned();
    assert_eq!(
        rows_totalling(&text, "…declined: field type at a variable level (βⱼ awaits the ω-prefix)"),
        0,
        "a Type-valued field declined again — route (ii)'s prefix stopped covering it:\n{text}"
    );
    assert_eq!(
        rows_totalling(&text, "declarations translated"),
        1,
        "the declaration with the Type-valued field did not translate:\n{text}"
    );
    assert_eq!(
        rows_totalling(&text, "constructors given a term and a typing rule"),
        2,
        "the constructor rule population moved:\n{text}"
    );
    assert_eq!(
        rows_totalling(&text, "TOTAL gaps"),
        0,
        "057 stopped being fully derived in the staged state:\n{text}"
    );
}

/// **The Undet `Π` is wired: `ite0` interpretation and `pi_imax_dep` typing**
/// — `LEVELPOLY.md` §5.4 blocker 1, on its own fixture.
///
/// `test_resources/UndetPi/export` is three universe-polymorphic definitions
/// and one axiom, each `Π` falling under **neither** clause of §6.2 at the
/// declaration's own parameters (`Clause::Undet` for a parameter, all three —
/// the `Π types under neither clause … a universe parameter` row is pinned at
/// 3 so the fixture cannot silently drift onto a decided clause):
///
/// * `piu.{u} : Sort (imax (u+1) u) := ∀ (α : Sort u), α` — the minimal
///   atom: guard `û` read through a `Local`'s binder type, zero skeleton
///   holes, and the rule's `û`/`v̂` arms *distinct* (`succ û` against `û`),
///   so an instantiation that swapped them fails the typing guard rather
///   than passing by coincidence.
/// * `pdep.{u,v} : Sort (imax (u+1) v) := ∀ (α : Sort u), ax0.{v}` — the
///   guard read through a `Const`'s declared type, **two** level parameters
///   (the `u ∈ ω` hypothesis list has two members whose positions the
///   conjunction projections must find), and one skeleton hole.
/// * `pnest.{u,v} := fun (α : Sort u) => ∀ (x : α), ax0.{v}` — the wired
///   `Π` under a binder: its `A ∈ srt(û)` premise is the *enclosing
///   lambda's own guard*, so the λ boundary discharges it — the uniform
///   typing invariant showing through — and the certificate that leaves the
///   declaration is conditional on level memberships and the fibres
///   conjunct only.
///
/// Flag **on**, staged: all three typing sites are answered by the wired rule
/// (`by ty_pi_undet` = 3) and the no-evidence row is absent. Flag **off**,
/// staged — the wedge's bit-identity promise doubling as this fixture's red
/// state: the same three sites are `no evidence: ty_pi_undet` and the wired
/// row is zero.
#[test]
fn the_undet_pi_is_wired_in_the_staged_state() {
    let export = Path::new(env!("CARGO_MANIFEST_DIR")).join("test_resources/UndetPi/export");
    let run = |flag: &str| -> String {
        let cfg_path = tmp_cfg(&format!("upi{flag}"), &export);
        let cfg = format!(
            r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true, "print_success_message": false}}"#,
            serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
        );
        std::fs::write(&cfg_path, cfg).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_nanoda_bin"))
            .arg(&cfg_path)
            .env("NANODATG_LEVELPOLY", flag)
            .env("NANODATG_NO_SCHEDULE", "1")
            .output()
            .expect("spawn");
        let _ = std::fs::remove_file(&cfg_path);
        assert!(out.status.success(), "the UndetPi fixture must be accepted (flag={flag})");
        String::from_utf8_lossy(&out.stderr).into_owned()
    };

    const WIRED: &str = "by ty_pi_undet";
    const MISSED: &str = "no evidence: ty_pi_undet";
    const UNDET_PARAM: &str = "a universe parameter: neither clause";

    let on = run("1");
    assert_eq!(
        rows_totalling(&on, UNDET_PARAM),
        3,
        "the fixture's Πs stopped being Undet — the atoms have drifted onto a decided clause:\n{on}"
    );
    assert_eq!(
        rows_totalling(&on, WIRED),
        3,
        "the wired Undet rule answered {} sites, expected all 3:\n{on}",
        rows_totalling(&on, WIRED)
    );
    assert_eq!(rows_totalling(&on, MISSED), 0, "a wired site still reports no evidence:\n{on}");

    let off = run("0");
    assert_eq!(rows_totalling(&off, WIRED), 0, "flag off must be bit-identical: nothing wired");
    assert_eq!(
        rows_totalling(&off, MISSED),
        3,
        "the red state moved — the fixture no longer exercises the gap the wiring closes:\n{off}"
    );
}

/// **The wired Undet-`Π` clause's outcome rows are a partition** — the
/// instrument `LEVELPOLY.md` §5.4 blocker 1's remaining population is measured
/// with, pinned against a counter that knows nothing about it.
///
/// The decomposition is only worth anything if the rows *add up*: a reason
/// counted twice, a `?` that returns without noting one, or a slot collision
/// in [`PiPoly::slot`] would each shift the shares while leaving every row
/// individually plausible, and the whole point of the instrument is to choose
/// the next edit by share. So the typing rows are summed and checked against
/// `by ty_pi_undet` + `no evidence: ty_pi_undet`, which come from
/// `certify.rs`'s gap ledger — a counter incremented on a different code path,
/// for a different purpose, that cannot be kept in step by accident.
///
/// **`118_accRecReduction`, deliberately**: staged, it populates **three**
/// outcome rows at once — the rule firing (2), the `Π` that was never wired
/// (9) and the level bridge refusing (1). Three atoms is this project's floor
/// for pinning a split, and a file with one populated row would pass the sum
/// check under a mutation that dropped either of the other two. The
/// individual rows are pinned too, so a *reason* silently moving from one row
/// to another — the failure a sum alone cannot see — is caught as well.
///
/// It also pins the bridge's own arms at the same site: `∅ ⊆ x` once,
/// `succ(∅) ⊆ b` twice, and seven sub-levels whose images already coincide.
/// Those are the three `≤` arms the corpus leans on hardest, and a bridge that
/// stopped taking one of them while still closing this file's two sites would
/// otherwise be invisible here.
///
/// Mutations run against this test (each made the cell red, then was
/// reverted): dropping `note_pipoly` from the `TBridge` exit takes the sum to
/// 11 against a ledger reading 12; giving `TNoLeftArm` and `TBridge` the same
/// slot leaves the sum right and moves the two rows to 0/1; and — the one that
/// tests the *mathematics* rather than the bookkeeping — instantiating
/// `imax_absorb` at `(v̂, û)` instead of `(û, v̂)` takes the fired row to 0,
/// because the absorbed side is the `imax`'s **right** arm and nothing else.
/// The last is the argument-order bug this branch has already hit once, in a
/// place where the two arms coincided and no test could see it.
#[test]
fn the_undet_pi_outcome_rows_partition_the_obligations() {
    let f = corpus().join("good/tutorial/118_accRecReduction.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    let text = staged_poly_report(&f, "1");

    let rows: [(&str, u64); 8] = [
        ("typing: pi_imax_dep fired", 2),
        ("…missed: the Π was not wired", 9),
        ("…missed: the obligation's type is not a Sort", 0),
        ("…missed: the guard walk spelled no domain sort level", 0),
        ("…missed: the level bridge refused", 1),
        ("…missed: the per-skeleton rule chain refused", 0),
        ("…missed: the ω-membership recursion disagreed", 0),
        ("…missed: a structural step did not match its shape", 0),
    ];
    let mut sum = 0;
    for (label, want) in rows {
        let got = rows_totalling(&text, label);
        assert_eq!(got, want, "the row {label:?} reads {got}, expected {want}:\n{text}");
        sum += got;
    }
    let ledger =
        rows_totalling(&text, "by ty_pi_undet") + rows_totalling(&text, "no evidence: ty_pi_undet");
    assert_eq!(
        sum, ledger,
        "the outcome rows sum to {sum} but the gap ledger counted {ledger} PiUndet obligations \
         — the decomposition is not a partition:\n{text}"
    );
    // Non-vacuity: a run where the clause never engaged would satisfy `0 == 0`.
    assert!(sum >= 3, "the fixture stopped exercising the clause at all:\n{text}");

    for (label, want) in [
        ("level bridge — bridge: two sub-levels whose ω-images already coincide", 7),
        ("level bridge — ≤: ∅ ⊆ x", 1),
        ("level bridge — ≤: succ(∅) ⊆ b, under b ≠ ∅", 2),
    ] {
        let got = rows_totalling(&text, label);
        assert_eq!(got, want, "the bridge arm {label:?} reads {got}, expected {want}:\n{text}");
    }
}

/// **Flag off, the instrument is silent and every obligation is unanswered** —
/// the wedge's standing bit-identity promise, at the report block and the
/// clause this tranche added.
#[test]
fn the_undet_pi_decomposition_is_absent_with_the_flag_off() {
    let f = corpus().join("good/tutorial/118_accRecReduction.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    let text = staged_poly_report(&f, "0");
    assert!(
        !text.contains("the wired Undet-Π clause"),
        "the decomposition block printed with the flag off:\n{text}"
    );
    assert_eq!(
        rows_totalling(&text, "no evidence: ty_pi_undet"),
        12,
        "flag off must be bit-identical: all 12 PiUndet obligations stay unanswered:\n{text}"
    );
    assert_eq!(rows_totalling(&text, "by ty_pi_undet"), 0, "flag off wired something:\n{text}");
}

/// Every row of the ι-site partition, in report order. Kept here rather than
/// derived from the report so that *adding* a `RecMiss` variant without adding
/// it here is caught by the sum check below: an unlisted row that fires makes
/// the listed rows fall short of the gap ledger.
const REC_MISS_ROWS: [&str; 20] = [
    "…the head names no recursor",
    "…bottom: indices / several motives / K-like / mutual",
    "…bottom: a hand-written recogniser owns it",
    "…bottom: the recursor's level list is not ind+motive",
    "…bottom: the declaration has no general translation",
    "…bottom: minor/rule/param counts disagree",
    "…bottom: T-policy 3, no nullary constructor",
    "…bottom: the Lean-facing type former refused",
    "…bottom: the derived layer refused the recursor",
    "…bottom: W-machinery unavailable",
    "…bottom: a hand-written stack was unavailable",
    "…the recursor type is not a Π to the major premise",
    "…fewer than four recursor arguments",
    "…fewer than np+4 arguments (the two-minor floor)",
    "…the general bottom's np+n+2 arity is not met",
    "…the T-policy term is not in the walk's domains",
    "…rec_of refused at these parameters",
    "…a domain mentions an unnamed ω-variable",
    "…an abbreviation or beta lemma refused",
    "…the head abbreviation refused",
];

/// **The ι-site partition, and its level-independence** — `LEVELPOLY.md` §5.4
/// blocker 2c.
///
/// `iota: this recursor has no curried interpretation` is one number (399 on
/// the staged `init-prelude`), and the commissioning brief hoped blocker 1's
/// `srt` machinery would move it. This test is the instrument that decided
/// otherwise, at fixture scale, and it makes two claims.
///
/// **It is a partition.** [`RecMiss`] has one variant per `rec_nest` refusal
/// site and `note_rec_miss` is called from exactly one place — the ι site that
/// asked — so the rows must sum to the gap row, which `certify.rs`'s ledger
/// counts on an entirely unrelated code path. Three files carry three
/// *different* reasons, which is what makes a mis-attribution visible: a
/// mutation that merges two reasons into one slot keeps every sum right and is
/// caught only by the per-file labels disagreeing.
///
/// **It does not depend on the level machinery.** The same rows are asserted in
/// all four states — flag on and off, scheduled and staged. That is the
/// measurement behind blocker 2c's re-attribution: not one of the 399 sites is
/// refused for a reason a level has any part in, so no amount of `srt` wiring
/// can move this row. A run whose rows differed between the flag states would
/// mean the opposite, and would be a real finding rather than a broken test.
///
/// Mutations run against this test (each red, then reverted): dropping the
/// `note_rec_miss` call at the ι exit takes every sum to 0 against ledgers
/// reading 1/3/1/1/1; and returning `RecMiss::BottomTPolicy` from the
/// `BottomShape` gate keeps all five sums right while moving `077`'s three
/// sites onto the T-policy row — the mis-attribution a sum alone cannot see,
/// and the reason this test needs three distinct reasons rather than one.
#[test]
fn the_rec_nest_outcome_rows_partition_the_no_curried_row() {
    // (file, the one reason that file carries, how many sites)
    let cases: [(&str, &str, u64); 5] = [
        ("074_prodRecEqns", "…bottom: T-policy 3, no nullary constructor", 1),
        ("077_RBTree.id_spec", "…bottom: indices / several motives / K-like / mutual", 3),
        ("094_ruleK", "…bottom: indices / several motives / K-like / mutual", 1),
        ("116_rtreeRecReduction", "…bottom: the declaration has no general translation", 1),
        ("118_accRecReduction", "…bottom: indices / several motives / K-like / mutual", 1),
    ];
    let mut seen: Vec<&str> = vec![];
    for (stem, reason, want) in cases {
        let f = corpus().join(format!("good/tutorial/{stem}.ndjson"));
        if skip_guard::absent(&f) {
            return
        }
        seen.push(reason);
        for (flag, scheduled) in [("1", false), ("0", false), ("1", true), ("0", true)] {
            let state = if scheduled { "scheduled" } else { "staged" };
            let text = poly_report(&f, flag, scheduled);
            let ledger = rows_totalling(&text, "gap: iota: this recursor has no curried");
            let mut sum = 0;
            for row in REC_MISS_ROWS {
                let got = rows_totalling(&text, row);
                let expect = if row == reason { want } else { 0 };
                assert_eq!(
                    got, expect,
                    "{stem} ({state}, flag={flag}): the row {row:?} reads {got}, \
                     expected {expect}:\n{text}"
                );
                sum += got;
            }
            assert_eq!(
                sum, ledger,
                "{stem} ({state}, flag={flag}): the reason rows sum to {sum} but the gap ledger \
                 counted {ledger} sites with no curried nest — not a partition:\n{text}"
            );
            // Non-vacuity: a run that asked for no ι step at all satisfies 0 == 0.
            assert!(
                sum >= 1,
                "{stem} ({state}, flag={flag}) stopped exercising the recursor path:\n{text}"
            );
        }
    }
    seen.sort_unstable();
    seen.dedup();
    assert!(
        seen.len() >= 3,
        "the fixture set collapsed to {} distinct reasons; a mis-attribution mutation is only \
         observable at two or more, and the third is what pins which row moved",
        seen.len()
    );
}

/// **Blocker 3, isolated in one file, with the schedule as its own control** —
/// `LEVELPOLY.md` §5.4 blocker 3.
///
/// `015_levelParams` stores two declaration typings in both states. Under the
/// schedule one use is answered from the store; with the schedule deleted the
/// *same* use is not, and the reason row says why: the declaration **is**
/// stored, at other levels. That is the whole of blocker 3 — a use inside `g`
/// spells `f`'s levels with `g`'s parameter variables, so the key
/// `(f, ⟦levels⟧)` misses an entry stored at `f`'s own — reduced to a single
/// site whose two ends differ by nothing but the schedule.
///
/// It is also the size check. `Dt::MissOtherLevels` is the *only* part of the
/// store-miss population any level construction can reach; on the staged
/// prelude it is 483 of 17124 misses, so blocker 3 closed completely takes
/// `uses answered from the store` to at most 117 + 483 = 600 against a ratchet
/// of 1308. The rest is declarations whose typing was never derived at any
/// levels, which is not a level problem. This test pins the mechanism; §5.4
/// carries the number.
///
/// And it pins **which** half. All 483 are at *ground* levels — a use spelled
/// `f.{0}`, not one spelled at another declaration's parameter variables. The
/// stored `∀u⃗` instantiated at `∅` concludes about `srt(∅)` while the use's
/// obligation, under the ground special case, is about a tower rung: provably
/// equal, not identical. There is therefore no variable-to-variable population
/// that could be closed by instantiation alone, ahead of unifying
/// `interp_sort`. That measurement is what makes blocker 3 part of the
/// switchover rather than a precondition of it.
///
/// `118_accRecReduction` is the discriminating negative — 19 store misses,
/// none of them cross-level — without which a counter wired to fire on every
/// miss would pass.
///
/// Mutation run against this test (red, then reverted): returning `true`
/// unconditionally from `stored_at_other_levels`, which takes 118's row 0 → 19.
///
/// **One mutation was tried and did *not* redden**, and the code changed rather
/// than the claim: `stored_at_other_levels` first carried a `levels != key.1`
/// conjunct, and dropping it left every assertion here green. It is
/// unreachable — the function is only called once a lookup at that exact key
/// has missed — so it was removed. A guard no mutation can redden reads as a
/// check and is not one.
#[test]
fn the_store_miss_that_a_level_construction_could_reach_is_counted_apart() {
    let lp = corpus().join("good/tutorial/015_levelParams.ndjson");
    let acc = corpus().join("good/tutorial/118_accRecReduction.ndjson");
    if skip_guard::absent(&lp) || skip_guard::absent(&acc) {
        return
    }
    const STORED: &str = "…stored as ⟦c⟧ ∈ ⟦T⟧";
    const HIT: &str = "uses answered from the store";
    const MISS: &str = "uses with no entry";
    const XLEVEL: &str = "…of them against a declaration stored at other levels";
    const GROUND: &str = "…of those, at ground levels";

    // The control: the schedule answers the use.
    let sched = poly_report(&lp, "1", true);
    assert_eq!(rows_totalling(&sched, STORED), 2, "scheduled:\n{sched}");
    assert_eq!(rows_totalling(&sched, HIT), 1, "the schedule must answer the use:\n{sched}");
    assert_eq!(rows_totalling(&sched, MISS), 0, "scheduled:\n{sched}");
    assert_eq!(
        rows_totalling(&sched, XLEVEL),
        0,
        "under the schedule every level is ground, so no key can miss on levels alone:\n{sched}"
    );

    // The deletion: the same two entries, the same one use, now unanswered —
    // and attributed to the boundary rather than to an absent entry.
    let staged = poly_report(&lp, "1", false);
    assert_eq!(rows_totalling(&staged, STORED), 2, "staged:\n{staged}");
    assert_eq!(
        rows_totalling(&staged, HIT),
        0,
        "the use is expected to go unanswered without the schedule — if this now reads 1, \
         blocker 3's cross-level consumption has been built and §5.4 needs re-taking:\n{staged}"
    );
    assert_eq!(rows_totalling(&staged, MISS), 1, "staged:\n{staged}");
    assert_eq!(
        rows_totalling(&staged, XLEVEL),
        1,
        "the miss must be attributed to the σ boundary, not to an absent entry:\n{staged}"
    );
    // And it is the *ground* half — the one that needs the vocabulary unified
    // rather than merely the stored `∀u⃗` instantiated. On the staged prelude
    // this row is 483 of 483: there is no variable-to-variable population to
    // close ahead of the switchover, which is why blocker 3 is part of it and
    // not a precondition of it (§5.5).
    assert_eq!(
        rows_totalling(&staged, GROUND),
        1,
        "if this drops below the cross-level row, a use at another declaration's parameter \
         variables has appeared and blocker 3 has a separately closable half after all — \
         which would be a finding, and §5.5 clause 1 would need re-taking:\n{staged}"
    );

    // The discriminating negative: misses that are *not* the boundary's.
    let other = poly_report(&acc, "1", false);
    assert_eq!(rows_totalling(&other, MISS), 19, "staged:\n{other}");
    assert_eq!(
        rows_totalling(&other, XLEVEL),
        0,
        "these 19 are against declarations stored at no levels at all; a counter that fired \
         on every miss would be indistinguishable from one that fires on the right ones:\n{other}"
    );
}

/// **The switchover's staging switch does what §5.5 clause 1 says, and nothing
/// with the flag off** — `NANODATG_UNIFY_SORT=1`.
///
/// Two claims, because the switch is worth nothing if either fails.
///
/// **It is inert flag-off.** Both call sites sit inside `levelpoly_enabled()`,
/// so the standing bit-identity promise survives a switch that would otherwise
/// change every `⟦Sort ℓ⟧` in the program. Asserted as report identity, not as
/// a gap count: a count can coincide.
///
/// **It really unifies the vocabulary.** With it on, the rung-shaped typing
/// rules stop firing — `IndTy` (an inductive type lies in its universe) goes
/// to zero, and so do `x ∈ U(x)` and `U₀ ∈ U₁`. Those three are the ones whose
/// conclusions are literally about tower rungs, so a switch that had somehow
/// left the ground path in place would keep them alive. On the staged prelude
/// the same three read 888 / 51 / 17 and go to 0 / 0 / 0; here they are
/// smaller but the direction is the same, and the *fixture* is what stops the
/// prelude numbers in §5.4 from being the only evidence.
///
/// Mutation run against this test (red, then reverted): making
/// `unify_sort_enabled` return `false` unconditionally, which restores the
/// rung rules and fails the second half while leaving the first half green —
/// which is exactly the asymmetry the two halves exist to separate.
#[test]
fn the_switchover_staging_switch_unifies_the_sort_vocabulary() {
    let f = corpus().join("good/tutorial/015_levelParams.ndjson");
    if skip_guard::absent(&f) {
        return
    }
    // Flag off: the switch cannot be reached, so the report is unmoved.
    let off = poly_report(&f, "0", true);
    let off_unified = poly_report_unified(&f, "0", true);
    assert_eq!(
        off, off_unified,
        "the switchover switch changed a flag-off run; the bit-identity promise is broken"
    );

    // Flag on, staged: the rung-shaped rules go dark, which is what "one
    // vocabulary" means operationally.
    let staged = poly_report(&f, "1", false);
    let unified = poly_report_unified(&f, "1", false);
    let rung = [
        "by IndTy: an inductive type lies in its universe",
        "by x ∈ U(x)",
        "by U₀ ∈ U₁",
    ];
    let before: u64 = rung.iter().map(|r| rows_totalling(&staged, r)).sum();
    let after: u64 = rung.iter().map(|r| rows_totalling(&unified, r)).sum();
    assert!(
        before > 0,
        "the fixture stopped firing any rung-shaped rule, so it can no longer witness the \
         vocabulary switch at all:\n{staged}"
    );
    assert_eq!(
        after, 0,
        "the rung-shaped rules still fired with the vocabulary unified ({before} → {after}); \
         `⟦Sort 0⟧` is still a tower rung somewhere:\n{unified}"
    );
    // Acceptance is what the switchover may not move, in either state.
    // `poly_report*` asserts exit 0 already; this pins that both ran.
    assert!(unified.contains("Tarski-Grothendieck kernel"), "no report:\n{unified}");
}

/// One run of `export` with the switchover's staging switch on.
fn poly_report_unified(export: &Path, flag: &str, scheduled: bool) -> String {
    poly_report_env(export, flag, scheduled, true)
}

/// One staged run of `export`, at the given `NANODATG_LEVELPOLY` setting,
/// returning the report.
fn staged_poly_report(export: &Path, flag: &str) -> String {
    poly_report(export, flag, false)
}

/// One run of `export` at the given flag setting, scheduled or staged.
fn poly_report(export: &Path, flag: &str, scheduled: bool) -> String {
    poly_report_env(export, flag, scheduled, false)
}

/// One run of `export`, with the switchover's staging switch optionally set.
fn poly_report_env(export: &Path, flag: &str, scheduled: bool, unify: bool) -> String {
    let cfg_path = tmp_cfg(&format!("upipart{flag}"), export);
    let cfg = format!(
        r#"{{"export_file_path": {}, "unpermitted_axiom_hard_error": false, "unsafe_permit_all_axioms": true,
             "nat_extension": true, "string_extension": true, "print_success_message": false}}"#,
        serde_json::to_string(&export.to_string_lossy().to_string()).unwrap()
    );
    std::fs::write(&cfg_path, cfg).unwrap();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_nanoda_bin"));
    cmd.arg(&cfg_path).env("NANODATG_LEVELPOLY", flag);
    if !scheduled {
        cmd.env("NANODATG_NO_SCHEDULE", "1");
    }
    if unify {
        cmd.env("NANODATG_UNIFY_SORT", "1");
    }
    let out = cmd.output().expect("spawn");
    let _ = std::fs::remove_file(&cfg_path);
    assert!(
        out.status.success(),
        "the fixture must be accepted (flag={flag}, scheduled={scheduled})"
    );
    String::from_utf8_lossy(&out.stderr).into_owned()
}
