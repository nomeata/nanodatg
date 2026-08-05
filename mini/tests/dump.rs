//! `mini --dump-theorems` — the stored context, and the two properties that
//! make it worth reading.
//!
//! The corpus lives in `vendor/arena-tests`, which is gitignored, so each test
//! skips rather than fails when it is absent — the idiom `tutorial.rs` uses.
//!
//! # What is asserted, and why these and not "the dump is non-empty"
//!
//! * **Determinism**, in two *processes*. Every store behind the dump is a
//!   `HashMap`, and Rust seeds `RandomState` per process, so two runs in one
//!   process share a seed and would pass while the feature was broken. Two
//!   subprocesses is the only test that actually pins the sorting.
//! * **Honest absence**, in both directions: a declaration that **declined**
//!   prints its reason, and a pair the run never reached prints as *not
//!   reached* rather than being silently missing. MINI-DESIGN.md §0.5 — *read a
//!   zero row twice* — is the reason the second one is a test and not a nicety.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_root() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf() }

fn export(name: &str) -> Option<PathBuf> {
    let p = repo_root().join("vendor/arena-tests/good/tutorial").join(name);
    p.exists().then_some(p)
}

/// A checked-in fixture, which is **not** gitignored and therefore never skips.
fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

/// `mini <flags> <export>`, returning stdout. The exit status is not asserted:
/// `--block` exits 3 by design, and this suite is about what was printed.
fn run(path: &Path, flags: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_mini"))
        .args(flags)
        .arg(path)
        .output()
        .expect("spawn mini");
    String::from_utf8_lossy(&out.stdout).to_string()
}

/// **Two processes, byte-identical.**
///
/// `042_rbTreeDef` is the fixture because it is the one that fills the most
/// stores: two non-indexed carriers, an indexed family at two σ, and the
/// constructor tables of all three. A dump that iterated any of them in
/// `HashMap` order would differ here and nowhere else.
#[test]
fn the_dump_is_byte_identical_across_two_processes() {
    let Some(p) = export("042_rbTreeDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let a = run(&p, &["--dump-theorems"]);
    let b = run(&p, &["--dump-theorems"]);
    assert!(a.contains("indexed RBTree"), "the fixture must reach zone B:\n{a}");
    if a != b {
        let first = a
            .lines()
            .zip(b.lines())
            .enumerate()
            .find(|(_, (x, y))| x != y)
            .map(|(i, (x, y))| format!("line {i}:\n  run 1: {x}\n  run 2: {y}"))
            .unwrap_or_else(|| "the runs differ in length".to_string());
        panic!("the dump is not deterministic across processes — {first}");
    }
}

/// The same for a **filtered** dump, which takes a different path through the
/// collection and could sort correctly in one and not the other.
#[test]
fn a_filtered_dump_is_deterministic_too() {
    let Some(p) = export("042_rbTreeDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let a = run(&p, &["--dump-only=RBTree"]);
    let b = run(&p, &["--dump-only=RBTree"]);
    assert_eq!(a, b, "a filtered dump must be deterministic too");
    assert!(a.contains("indexed RBTree"), "the filter must keep its subject:\n{a}");
    assert!(!a.contains("inductive Color"), "the filter must drop everything else:\n{a}");
}

/// **A declined declaration is shown, with its reason.**
///
/// The reason is matched as the ledger's own key, not as prose: `blocker` and
/// `ledger` already agree on that vocabulary and the dump is the third
/// instrument using it.
///
/// *(Rewritten in place. The prior revision ran on `117_accRecType`, where
/// `Acc` declined `fun-typed-rec-arg(Acc)` at **both** of its instantiations,
/// and it pinned a second property with that: that a decline is reported per σ
/// rather than once per name. `Acc` now takes [`mini::direct`]'s clause and
/// declines at neither σ, and the per-σ half has **no corpus witness left** —
/// `RTree` is the only declaration that still declines and it has no universe
/// parameters, so its decline is one row by construction. That half is
/// therefore not asserted here rather than asserted vacuously; restoring it
/// wants a fixture with a level-parametric declining declaration, and this
/// paragraph is the record that it is owed.)*
///
/// *(The reason literal was `fun-typed-rec-arg(RTree)` until
/// `mini/src/zoneb.rs`'s spec walk learned `CtorSpec::rec_doms`. `RTree` still
/// declines and still declines once — what changed is **which** step refuses
/// it: the spec is now built and so is the carrier, and the decline is
/// `derived::cumul`'s universe placement, which reads a constructor's fibre
/// value and is stated at `finord(mᵢ)` alone. The row will move again, to the
/// recursor, the day that placement widens.)*
///
/// *(**It moved, and not to the recursor.** The placement widened
/// (`derived` `3e334d4`) and `zoneb::fibre_facts` now supplies its two
/// per-summand facts, so `RTree`'s carrier is placed in `U₁` and the decline is
/// the **constructor**: `ctor(RTree: function-typed recursive field)`. The nest
/// scope holds `g ∈ dprod(b,⟦Bool⟧)` and `Ctor::mem` wants
/// `g ∈ fs(Σ(z::γ), ind(p⃗))` — `MINI-HANDOFF.md` §29 item 3's six steps. The
/// sentence above predicted the recursor and skipped the constructor, which is
/// the ordinary way a "next step" prediction goes wrong: it names the piece it
/// can see rather than the next one.)*
///
/// *(**The witness moved off the corpus entirely, and that is the finding this
/// revision records.** `RTree`'s constructor landed, so the declaration
/// *translates* — carrier, type former, both constructors and their typings —
/// and what is left is its **eliminator**, which is a per-pair `waiting:` row
/// and not a whole declaration. Measured rather than assumed:
/// `--dump-theorems` over all 91 tutorial exports finds **zero** whole
/// declarations without a translation other than the two below. Every other
/// declaration the tutorial corpus contains now translates.
///
/// So the property has no corpus witness at all, which is one step past the
/// per-σ half the paragraph above already records as owed. It is moved to
/// `tests/fixtures/squash_at_nonzero_sigma.ndjson` rather than weakened or
/// deleted — a checked-in fixture, so this test no longer skips when the
/// gitignored corpus is absent, and its row **carries a σ** (`Squash σ=[1]`),
/// which `RTree`'s never did. The per-σ half still wants a declaration
/// declining at *two* σ and is still owed.)*
#[test]
fn an_untranslated_declaration_is_shown_with_its_reason() {
    let out = run(&fixture("squash_at_nonzero_sigma.ndjson"), &["--dump-theorems"]);
    let rows: Vec<&str> = out
        .lines()
        .skip_while(|l| !l.contains("── untranslated"))
        .filter(|l| l.contains("not translated:"))
        .collect();
    assert_eq!(rows.len(), 1, "Squash has no translation, and that must be a row:\n{out}");
    assert!(
        rows[0].contains("ind-spec(Squash: class (P) above Prop)"),
        "the reason must be the ledger's key: {}",
        rows[0]
    );
    assert!(rows[0].contains("Squash"), "the row must name its subject: {}", rows[0]);
    assert!(rows[0].contains("σ=[1]"), "the row must name which σ it was: {}", rows[0]);
    assert!(
        rows[0].contains("declaration not translated:"),
        "the row must say which of the three tables it came from: {}",
        rows[0]
    );
}

/// **Exactly three things in the tutorial corpus have no translation**, and
/// they are pinned by name and by reason so that a fourth cannot appear
/// quietly.
///
/// The other side of the test above. An entry here is something mini
/// *knowingly did not build* — strictly worse than a pair that stops at an
/// obligation, and, until the census below was widened, invisible to every
/// counter the verdict watched.
///
/// # This test asserted an empty population, and the zero was a measurement
/// artefact
///
/// *Rewritten in place, and the sentence it replaces is worth quoting because
/// it was the confident one:* "**Measured** rather than assumed:
/// `--dump-theorems` over all 91 tutorial exports finds **zero** `declined:`
/// rows. Every declaration the tutorial corpus contains now translates."
///
/// The measurement was real and the conclusion did not follow. Zone B was
/// called **only from a constant occurrence that missed the store**, so a
/// declaration nothing used at a ground level was never asked whether it is
/// translatable — it produced no row because nothing looked, not because it
/// translates. `ledger::fill_declaration` now fills from the schedule at the
/// moment the declaration is reached, so the population is a function of the
/// *file*, and three declarations that were never reached turned out to
/// decline: `reduceCtorParam`, `reduceCtorParamRefl` and
/// `reduceCtorParamRefl2`, all three as `ind-spec(…: nested occurrence)`.
///
/// # The nested occurrence was not one, and the reason was wrong at all three
///
/// Those exports write a constructor's recursive field not as `T α` but as
/// `constType (T α) (T α)`, an application of a definition that *reduces* to
/// it. `zoneb`'s spec walk tested the shape syntactically, deliberately ahead
/// of any interpretation — `Checker::infer_type` on a self-mentioning type
/// reaches `const_evidence` → `miss_reason` → `zoneb::ensure` on the very
/// declaration being built, which is an unbounded recursion — and so it read an
/// ordinary recursive argument as a nesting.
///
/// `zoneb::rec_field` now reads the spine through the **acceptance-only**
/// `Checker::whnf`, which is handed no `⟦e⟧` and therefore interprets nothing,
/// peeling and reducing alternately exactly as zone A's own `check_ctor_param`
/// and `build_rec_type` do. `052` translates completely as a result. The other
/// two do not, and what stopped them was hidden behind the wrong reason rather
/// than caused by lifting it:
///
/// | export | declaration | reason |
/// | --- | --- | --- |
/// | `113_reduceCtorParamRefl.mk` | `reduceCtorParamRefl` | `ctor(…: recursive field codomain)` |
/// | `114_reduceCtorParamRefl2.mk` | `reduceCtorParamRefl2` | same |
///
/// Both fields reduce to `α → T α`, a **function-typed** recursive argument
/// whose domain is the declaration's own parameter, so the constructor's fibre
/// value is `Sum₁(Σ(z::γ(p⃗)))` — a term mentioning `p⃗`.
///
/// # The `derived/` generalisation landed, and the reason moved rather than went
///
/// *The row above read `ind-spec(…: carrier)` for one round, and the paragraph
/// under it said `derived`'s `Fibre::new` abbreviates each fibre value over
/// one fresh variable, so a value mentioning `p⃗` is refused. That was right,
/// it was located by instrumenting every `?` in `Inductive::build`, and it is
/// now fixed:* `Fibre::new` takes the declaration's **parameter telescope** and
/// mints `coᵢ(p⃗,y) = vᵢ` through `funcs::lambda_n`,
/// `funcs::beta_conditional_n` and `ext::lam_in_funspace_n`. Re-run, the same
/// census finds **no** `?` in `Inductive::build` returning `None` on any of the
/// 91 exports: the carrier builds for both.
///
/// # The placement closed too, and the reason moved a second time
///
/// *The row above read `ind-fibre-value(…)` for two rounds.* The paragraph
/// under it said `zoneb::fibre_facts` composes what
/// `cumul::DeclUniverse::over_at_general` is owed per fibre summand, that `γ`
/// here is the *parameter* `α` whose typing is conditional, and that the
/// placement demanded it outright — first because `bnd` at a parameter is
/// refutable, then, after `bnd` went, because `isum::isum_in_universe` refused
/// a conditional input structurally. Both are history:
/// `isum::isum_in_universe_under` carries the antecedent through the fold, and
/// `spec_of` discharges the `γ` typing through the parameter scopes so that
/// what arrives is `⊢ H → ⟦γ⟧ ∈ Uₙ` with nothing on the left.
/// `mini/tests/fixtures/parameter_domain_branching.lean` is the fixture that
/// closed it, at `constEv = 8`.
///
/// **These two did not close with it, and they stopped somewhere new.** The
/// carrier *is* placed now; what refuses them is one construction further
/// along again, in `zoneb::constructor`: the recursive field's Lean codomain is
/// `constType (T α) (T α)`, whose interpretation is an application term, while
/// the constructor's own spine is `⟦T⟧(p⃗)`. The two are definitionally equal —
/// that is what makes the field recursive at all, and `rec_field` classifies it
/// by its reduct — but `⟦·⟧` is a function of the *term*, so the membership
/// arrives about one and is owed about the other, and the bridge is a
/// conversion nobody composes yet. **That is a δ/β step and not a placement
/// obligation**, which is why this row's reason is now `ctor(…)` and not
/// `ind-…`: the whole of the parameter-domain question is answered and what is
/// left is the `constType` obfuscation these two exports share with `052`.
/// SCOPING.md §4 is the calibration entry for exactly this class of gap.
///
/// `RTree.node`'s `γ` is `Bool`, closed, and its codomain is written out, which
/// is why the corpus's other function-typed witness never met either.
///
/// # The census watched two of the three tables, and the third had an occupant
///
/// *Rewritten in place a second time.* The section this test scrapes listed
/// `IndApparatus::untranslated` and `ctor_untranslated` and **not**
/// `rec_untranslated`, so an eliminator that was attempted once at the
/// declaration and could not be built produced no row here. `052`'s
/// `reduceCtorParam.rec` is exactly that, and it is the entry that matters
/// most of the three: `052` is pending work in `derived/` — the case the brief
/// for this change asked whether the silence also covered. It did. *(This
/// sentence used to add that `113`/`114` "refuse correctly and permanently".
/// They did not: the reason they refused has now moved twice and the
/// declaration is placed. Nothing on this list is permanent.)* The section now
/// enumerates
/// all three tables, which is the same population
/// `mini::ledger::Untranslated` counts, so this test and the verdict line's
/// `untranslated:` column cannot drift apart.
///
/// Read the three twice, per MINI-DESIGN.md §0.5: this is *these three and no
/// others*, measured over all 91 exports, and not *nothing was dumped*. The
/// `--dump-theorems` output is non-empty at every one of them, which the
/// header-line check below is for.
#[test]
fn tutorial_untranslated_records_are_exactly_these_three() {
    let dir = repo_root().join("vendor/arena-tests/good/tutorial");
    let Ok(entries) = std::fs::read_dir(&dir) else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let mut files: Vec<PathBuf> = entries
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "ndjson"))
        .collect();
    files.sort();
    assert_eq!(files.len(), 91, "the tutorial corpus is 91 exports");
    let mut rows: Vec<String> = Vec::new();
    let mut dumped = 0usize;
    for f in &files {
        let out = run(f, &["--dump-theorems"]);
        // **Two exports produce no dump at all**, and that is an *arena
        // decline* — a verdict about the file, exit 2 — rather than anything
        // this section is about: `031_letTypeDep` and `032_letRed` declare a
        // non-standard axiom, so mini refuses the file before any store
        // exists. `tutorial.rs`'s `DECLINED_NONSTANDARD_AXIOM` names both; they
        // are counted here rather than skipped by name, so that a *third*
        // export losing its dump fails this test instead of passing quietly.
        if !out.contains("── untranslated") {
            assert!(
                out.contains("non-standard axiom"),
                "an export produced no dump for a new reason: {}\n{out}",
                f.display()
            );
            continue
        }
        dumped += 1;
        for l in out.lines().filter(|l| l.contains("not translated:")) {
            rows.push(format!("{}: {}", f.file_name().unwrap().to_string_lossy(), l.trim()));
        }
    }
    assert_eq!(dumped, 89, "the population that has a store at all changed");
    let expected = vec![
        "052_reduceCtorParam.mk.ndjson: reduceCtorParam.rec σ=[1]  (eliminator not translated: \
         recursor(reduceCtorParam: dependent recursor: a minor premise does not transport))"
            .to_string(),
        "113_reduceCtorParamRefl.mk.ndjson: reduceCtorParamRefl σ=[]  (declaration not \
         translated: ctor(reduceCtorParamRefl: recursive field codomain))"
            .to_string(),
        "114_reduceCtorParamRefl2.mk.ndjson: reduceCtorParamRefl2 σ=[]  (declaration not \
         translated: ctor(reduceCtorParamRefl2: recursive field codomain))"
            .to_string(),
    ];
    assert_eq!(
        rows, expected,
        "the untranslated population changed — a fourth entry, or one of these three closing. \
         `tutorial.rs`'s `UNTRANSLATED_ON_THE_CORPUS` is the same fact at column granularity \
         and must move with it"
    );
}

/// **"Never reached" is not spelled like "succeeded".**
///
/// Armed, the run stops at the first blocker, so a later scheduled pair has no
/// entry in the store at all. That pair must still appear, and must say that
/// nothing was attempted for it — the distinction §0.5 says costs planning
/// mistakes when a ledger cannot make it. Asserted alongside a pair that *was*
/// stored, because a dump in which every row said "not reached" would pass a
/// one-sided check.
///
/// *(The two-sidedness used to be a header count, `2 pairs / 1 stored`. That
/// counts **every** stored constant, not the scheduled pairs — `Acc` and
/// `Acc.intro` are stored here too since the direct clause landed — so it was
/// measuring the wrong population and would move again for any reason at all.
/// It is now asserted where it belongs: the first pair's own interpretation
/// line.)*
///
/// *(**The export moved, at `a9c49d8`'s predecessor**, and the prior revision
/// read `117_accRecType.ndjson` with `⟦accRecType.{0,0}⟧` as the stored side.
/// `5658439` landed `Acc.rec` at `u₁ = 0`, so `117`'s first pair stopped
/// blocking and its second pair became **reached** — it now carries a stored
/// `⟦c.{σ}⟧` and a named `waiting on …`, which is a different row and the right
/// one. There was no "not reached" left in that file to assert, so the test was
/// red from `5658439` until here; the property is unchanged and only its
/// witness moved. `115_rTreeRec.ndjson` is the witness now: `u_1 := 0` blocks on
/// `fun-typed-rec-arg(RTree)` and `u_1 := 1` is never attempted. **It will flip
/// the day `RTree` builds**, and the successor should move it again rather than
/// weaken it — the property this asserts is about the dump, not about `RTree`,
/// and any export that stops at its first of two pairs will do.)*
///
/// *(The reason `u_1 := 0` blocked on moved three times — through
/// `ind-fibre-value(RTree)`, `ctor(RTree: …)` and `recursor(RTree: …)` — without
/// this test needing a line changed, because it never named it. That is "the
/// property is about the dump" demonstrated rather than asserted.)*
///
/// *(**The prediction came true and the witness moved again**, as that
/// paragraph asked. `115_rTreeRec`'s `u_1 := 0` pair now interprets — the
/// minor premise's crossing at a function-typed recursive slot is built for the
/// proof clause — so `115` has no unreached pair left. The witness is
/// `116_rtreeRecReduction.ndjson`, whose **first** scheduled pair is stored and
/// whose other **two** are never attempted, which is the same property with
/// more of it: two unreached rows instead of one, and a stored pair whose own
/// typing is a named absence rather than a theorem. Moved, not weakened: every
/// assertion below is the one it was, and the row count went up.)*
///
/// *(**And then the witness ran out, which is a finding and not a licence to
/// weaken this.** `116`'s remaining three pairs are all *reached* now — the
/// `u₁ ≥ 1` eliminator landed, so `RTree.left` has a value and the scheduler
/// no longer stops before `rfl` and `rtreeRecReduction`. Measured over **both**
/// corpora, `good/tutorial` and `bad/tutorial`, 92 exports: `not reached`
/// appears **zero** times. So the `count == 2` arm is not merely unsatisfied
/// here, it has no witness anywhere, and asserting it at any file would pin
/// nothing — `SCOPING.md`'s "a negative fixture must reach the check it names".)*
///
/// *(**And in the same increment the other arm ran out too.** The replacement
/// asserted `waiting on iota(RTree.rec)` as the surviving witness for "a
/// reached pair with no typing names what it waits on", and `iota_dep` closed
/// that pair before the sentence was a day old. Measured again over both
/// corpora: **no** dump contains `not reached` or `waiting on`, and the only
/// parenthesised absence left anywhere is
/// `(none expected — not a transparent definition)`, which
/// [`every_absence_carries_a_reason`] covers.
///
/// What is left to assert here is the property that does not need an absence
/// to have a witness: **every scheduled pair gets a row**, whether or not the
/// store has anything for it — three rows in a file with three pairs — and
/// none of them is an unexplained hole. Both absence arms are pinned as the
/// absences they now are, so a successor who reintroduces either sees this go
/// red and can restore the stronger form rather than discovering the gap. This
/// is the second time in two increments that a witness here was closed by the
/// work rather than moved by it; a third should be read as "this file's
/// negative properties belong on a synthetic export", not as a fourth
/// rewrite.)*
#[test]
fn an_unreached_pair_is_named_as_unreached_not_omitted() {
    let Some(p) = export("116_rtreeRecReduction.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--block", "--dump-theorems"]);
    assert!(
        out.contains("⟦RTree.left.{}⟧"),
        "the first pair must be stored, or the check below is one-sided:\n{out}"
    );
    assert_eq!(
        out.matches("not reached").count(),
        0,
        "an unreached pair is back; restore this test's stronger form:\n{out}"
    );
    assert!(
        !out.contains("waiting on"),
        "a reached pair lost its typing; restore this test's stronger form:\n{out}"
    );
    // …and the positive half, which is what makes the two zeros above readable:
    // every scheduled pair carries a theorem rather than a hole.
    let scheduled = out
        .split_once("── constants")
        .and_then(|(_, r)| r.split_once("── also stored"))
        .map(|(l, _)| l.to_string())
        .unwrap_or_default();
    assert_eq!(
        scheduled.matches("typing   ⊢").count(),
        3,
        "a scheduled pair lost its typing row:\n{out}"
    );
    // Every scheduled pair is listed, whether or not it is in the store.
    for d in ["RTree.left   σ =", "rfl   σ =", "rtreeRecReduction   σ ="] {
        assert!(
            out.lines().any(|l| l.trim_start().starts_with(d)),
            "every scheduled pair gets a row, and {d:?} has none:\n{out}"
        );
    }
}

/// **No absence is unexplained.**
///
/// Every `(…)` the dump prints in place of a theorem must carry a reason. An
/// empty or bare parenthetical would be the §0.5 defect reintroduced as a
/// formatting bug, which is exactly how it would come back.
#[test]
fn every_absence_carries_a_reason() {
    let Some(p) = export("117_accRecType.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    for l in out.lines() {
        let t = l.trim();
        assert!(!t.ends_with("()"), "an unexplained absence:\n  {l}");
        if let Some(i) = t.find("  (") {
            let reason = &t[i + 3..];
            assert!(
                reason.len() > 12,
                "an absence must say why, not just that it is absent:\n  {l}"
            );
        }
    }
}

/// The dump must not **create** what it reports.
///
/// `Interp::ind_apparatus` builds the apparatus on demand; a dump that reached
/// for it would turn "no declaration reached zone B" into a page of theorems
/// about an apparatus this file never asked for. `001_basicDef` has no
/// inductive at all, so the section must say the apparatus was never built.
#[test]
fn the_dump_does_not_build_the_apparatus_it_reports() {
    let Some(p) = export("001_basicDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    assert!(
        out.contains("not built — no declaration in this file reached zone B"),
        "an apparatus that was never built must be reported as absent, not constructed:\n{out}"
    );
}

/// The statements printed are the **stored** ones.
///
/// `001_basicDef` is `def basicDef : Type := Prop`, so its two theorems are
/// exactly `⊢ ⟦basicDef⟧ ∈ ⟦Sort 1⟧` and `⊢ ⟦basicDef⟧ = ⟦Sort 0⟧`. Pinned
/// because it is the smallest case where a *wrong* dump — one that printed the
/// type it believed rather than the conclusion it holds — would still look
/// plausible.
#[test]
fn a_constants_typing_and_defining_equation_are_the_real_ones() {
    let Some(p) = export("001_basicDef.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems"]);
    assert!(out.contains("typing   ⊢ ⟦basicDef.{}⟧ ∈ ⟦Sort 1⟧"), "{out}");
    assert!(out.contains("defeq    ⊢ ⟦basicDef.{}⟧ = ⟦Sort 0⟧"), "{out}");
}

/// **A store that acquires a theorem must stop being printed as an absence.**
///
/// Two rows, one defect, and it is the one this module's header calls property
/// 2 read backwards. A dump that cannot see a store costs a reader a search; a
/// dump that **denies** one costs them a construction, because "not stored"
/// beside a `derived/` module path reads as a library gap.
///
/// * `value-motive ι` said *"not stored — `IndexedDepRecursor` has no `iota`
///   field"*, and that stopped being true at `211c46e`, when `derived` built it
///   beside `typing`. The absence outlived its cause by one landing.
/// * `rec abbrev` is the other direction and the ordinary one: the eliminator
///   nest bottom's defining axiom had no reader at all until
///   `mini/src/iota_dep.rs`, and a `define_abbrev` whose equation is not stored
///   is a symbol no consumer can get inside.
///
/// `077` is the fixture because it has both: an indexed family whose ι rules
/// are built, and a value-motive eliminator whose bottom is named. Asserted as
/// the *presence of a theorem line* rather than the absence of a string, so a
/// future rename of the reason does not quietly satisfy it.
#[test]
fn a_store_that_gained_a_theorem_is_no_longer_printed_as_absent() {
    let Some(p) = export("077_RBTree.id_spec.ndjson") else {
        eprintln!("SKIP: gitignored corpus absent");
        return
    };
    let out = run(&p, &["--dump-theorems", "--dump-only=RBTree"]);
    let thm = |label: &str| {
        out.lines()
            .filter(|l| l.contains(label))
            .any(|l| l.contains('⊢'))
    };
    for i in 0..3 {
        assert!(
            thm(&format!("value-motive ι {i}")),
            "IndexedDepRecursor::iota[{i}] is built and must be printed as a theorem:\n{out}"
        );
    }
    assert!(
        !out.contains("has no `iota` field") && !out.contains("neither built nor tested"),
        "the dump is still denying a store that exists:\n{out}"
    );
    assert!(
        thm("rec abbrev RBTree.rec"),
        "the value-motive eliminator's nest bottom must have its defining axiom stored:\n{out}"
    );
    assert!(
        out.lines().any(|l| l.contains("rec target RBTree.rec") && l.contains("Sort")),
        "…and the set `T` was instantiated at, which is the rung and not u₁:\n{out}"
    );
}
