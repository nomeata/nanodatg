//! The Tarski–Grothendieck proof backend: real [`kernel::Thm`] certificates.
//!
//! # What this does and does not claim
//!
//! Every Lean expression is interpreted as a term of the kernel's first-order
//! language, and every definitional-equality certificate is a genuine kernel
//! theorem `⟦a⟧ = ⟦b⟧` — derived from the equality axioms by real inference
//! rules, not asserted.
//!
//! Most of the interpretation is still **pure signature extension**: fresh
//! symbols with *no* axioms (the dependent `pi`, `let`, `proj`, `bvar`, the
//! level formers, …). That is unconditionally conservative, so nothing here
//! enlarges the trusted base or risks consistency. Four parts of the
//! interpretation are now *definitional extensions* instead, which is what
//! makes them mean something:
//!
//! * **`Sort`**. `⟦Sort 0⟧` is a fixed constant and `⟦Sort (u+1)⟧ := U(⟦Sort u⟧)`,
//!   where `U` is the least-Grothendieck-universe operator of
//!   [`derived::universe`]. `⊢ ∀x. x ∈ U(x)` then gives
//!   `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` outright — the one typing fact this backend has.
//!   Levels that are not literal successors keep an opaque `sort` symbol.
//! * **`App`**. `⟦f a⟧ := app(⟦f⟧, ⟦a⟧)`, with `app` the set-theoretic
//!   application of [`derived::funcs`] — **unless the application is a
//!   proof**, in which case it is `•`; see the proof split below.
//! * **`Lam`**. `⟦λx:A. b⟧` is the *function graph* `{⟨x, t(x)⟩ : x ∈ ⟦A⟧}` of
//!   [`derived::funcs::lambda`] — again unless the lambda is a proof, in which
//!   case it is `•`. See "Lambdas" below for how the body is turned into a
//!   function symbol, and why the version used here is `lambda_n`.
//! * **`Pi`**. `⟦Π x:A. B⟧ := dprod_C(s⃗, ⟦A⟧)`, the **dependent product** over
//!   the fibre `x ↦ ⟦B⟧` — at *every* codomain, `mini`'s clause (SCOPING.md
//!   §10). A body that does not mention the binder is the degenerate shape,
//!   not a separate clause: its skeleton is the bare hole variable, so every
//!   arrow `A → B` shares one constant-fibre symbol, `dprod₀(⟦B⟧, ⟦A⟧)`, and
//!   two spellings of one arrow agree by reflexivity. The library's function
//!   space `fs` remains `derived`'s statement vocabulary, met at
//!   [`TgBackend::dprod_fs_eq`]. The fibre is built by the same skeleton
//!   decomposition the lambdas use (see "Lambdas" below), so the binder is
//!   opened at a local and the constant fibre is recognised *exactly* — "the
//!   interpreted body does not mention this binder's variable" — rather than
//!   conservatively from the loose-bvar count. With every binder in a `Π` tower
//!   opened, an interpreted term contains no `bvar` symbols at all.
//!
//! # The proof split
//!
//! §6.2 gives **two clauses each** for three constructors, not one:
//!
//! ```text
//! ⟦∀x : α. β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]      ⟦Πx : α. β⟧ = ∏_{x∈⟦α⟧} ⟦β⟧
//! ⟦λx : α. e⟧ = •                          ⟦Λx : α. e⟧ = (x ∈ ⟦α⟧ ↦ ⟦e⟧)
//! ⟦e₁ e₂⟧     = •                          ⟦e₁ · e₂⟧   = ⟦e₁⟧(⟦e₂⟧)
//! ```
//!
//! The left column is taken when the term is a **proof** and the right when it
//! is not. `•` is the proof object: a proposition denotes a subset of `{•}`, so
//! proof irrelevance is not an axiom here but the shape of the model.
//! [`TgBackend::term_clause`] is the decision — the same classifier
//! [`TgBackend::body_clause`] runs for `Π`, one level down, because
//! `sort(e) = lvl(type of e)`.
//!
//! Two consequences worth naming. The `Prop` lambda has its own **typing rule**,
//! [`derived::prop::cond_intro`] rather than [`lam_in_funspace_n`]: a graph is
//! never a member of a conditional singleton, so before the split a proof
//! lambda's obligation was not merely unproved but unprovable as stated. And a
//! proof that is *neither* a `λ` nor an application — a variable above all —
//! interprets to itself; that it equals `•` is Theorem 6.7, and
//! [`TgBackend::point_of_proof`] derives it from the context's own assumptions
//! rather than baking it into `⟦·⟧`.
//!
//! With those in place [`derived::funcs::beta_conditional`] applies, and
//! [`Certifier::beta`] is a real derivation rather than an admit — modulo one
//! premise it cannot always discharge, discussed under "What beta still costs".
//!
//! # Lambdas: how the body becomes a function symbol
//!
//! `lambda` wants the body as a *unary* function symbol `t`, but a Lean lambda
//! body is an open expression. Instantiating the binder at a fresh local and
//! interpreting gives a term `bt` containing one distinguished free variable
//! `v`; the obvious move is then `t(v) := bt`. That is wrong as it stands,
//! because a nested lambda's body mentions the *enclosing* binders too, and a
//! defined symbol may not contain free variables that are not among its
//! parameters (it would not be a conservative extension).
//!
//! The fix is to abstract more: `bt` is split into a **skeleton** — the part
//! that actually mentions `v` — and the list of **maximal `v`-free subterms**,
//! which become extra parameters. So
//!
//! ```text
//! ⟦λ y:A. b⟧  :=  lam_C(s₁, …, s_k, ⟦A⟧)
//! ```
//!
//! where `C` is the skeleton, `lam_C` is the graph symbol built once per
//! skeleton, and `s⃗` are the abstracted subterms. This decomposition is
//! canonical *and* stable under substitution — substituting into an `s_i`
//! keeps it `v`-free and leaves `C` alone — which is exactly the property beta
//! needs: `⟦b[a]⟧` really is `⟦b⟧` with the abstracted positions filled in, so
//! the two sides of the beta equation line up syntactically instead of merely
//! morally. Without it, `⟦(λx.λy.x) P⟧` and `⟦λy.P⟧` would be built from
//! unrelated symbols and no chain of steps could connect them.
//!
//! A skeleton's graph is derived **once for the whole run**, not once per
//! declaration: the signature every backend builds terms in is shared per
//! thread (see [`Shared`]), so two occurrences of one body shape in two
//! declarations are the same *term* and hit the same cache. That is what makes
//! the construction affordable for every lambda, with no cut-off on how many
//! subterms a body may abstract.
//!
//! The extra parameters are why `lambda_n`, `beta_conditional_n` and
//! `lam_ext_n` exist: the derived originals take a unary body symbol, and `t`
//! here has arity `k + 1`. They are the derived derivations with the prefix
//! threaded through, and coincide with them at `k = 0`. `lam_ext_n` threads
//! *two* prefixes, of independent lengths, since the two lambdas it relates
//! have unrelated skeletons.
//!
//! # What beta still costs
//!
//! `beta_conditional` is *conditional*: a set-theoretic function has a set
//! domain, so `app(lam(A), a) = t(a)` needs `a ∈ A`. Discharging that is a
//! **typing** obligation — `⟦a⟧ ∈ ⟦A⟧` whenever Lean says `a : A` — and it is
//! Lean's typing judgement, so it is discharged by a family of clauses, one per
//! typing rule: [`TgBackend::has_type_a`].
//!
//! Two of them are facts about the *operators* the interpretation is built from
//! (`domain_premise`):
//!
//! * `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧`, from `⊢ ∀x. x ∈ U(x)` — which is not restricted
//!   to sorts, and settles any obligation whose target is `U(⟦a⟧)`;
//! * `⟦A → A⟧ ∈ ⟦Sort (u+1)⟧` when `⟦A⟧` is `⟦Sort u⟧`, from
//!   [`derived::funspace`]'s `⊢ ∀a. fs(a,a) ∈ U(a)`, carried across
//!   [`TgBackend::dprod_fs_eq`] to the constant-fibre `dprod` the arrow
//!   interprets to.
//!
//! The restriction to the diagonal `fs(a,a)` is not a shortcut either: the
//! two-argument form `⊢ ∀a ∀b ∀c. ((a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c))` exists,
//! but its antecedent needs closure of `U(x)` under binary unions, which is
//! unproved.
//!
//! The rest are structural. A constant transfers the obligation to its *value*
//! along the defining equation; an application is the characteristic property of
//! its function's type — the dependent product's `∀x ∈ A. app(f,x) ∈ b(x)`
//! conjunct with the fibre unfolded, or `fs`'s `app(f,x) ∈ b` where a library
//! theorem states the target over the function space. A **lambda** is
//! [`lam_in_funspace_n`] when its stated type is an `fs` and [`lam_in_dprod_n`]
//! when it is a dependent product — the prefix-threaded ports of
//! [`derived::ext::lam_in_funspace`] and [`derived::ext::lam_in_dprod`], which
//! exist only for a *unary* body and fibre symbol while every lambda and `Π`
//! here carries the hole prefix its skeleton decomposition gives it. Their
//! premise is a typing judgement *under the binder*, so `has_type` carries
//! assumptions of the shape `w ∈ D` and discharges the binder's own by the very
//! move the lambda *congruence* rule already used
//! ([`TgBackend::guard_and_generalise_at`]). A local is that assumption — and
//! where no binder supplies it, [`TgBackend::has_type_local`] *acquires* it, the
//! new antecedent travelling back out to the caller rather than being invented.
//! A **projection** has no theorem to find at all — `⟦s.i⟧` is `proj(i, ⟦s⟧)`
//! over an axiom-free symbol, and the content that is missing is the
//! interpretation of the *structure* — so [`TgBackend::has_type_proj`] carries
//! its field typing the same way rather than deriving it, and the ledger says
//! so. A `Π` is still out of reach, needing `dprod_in_universe`'s n-ary port.
//!
//! ## The same rules, driven by inference instead of searched for
//!
//! `has_type` is a *search*: it is handed a term and a target and recurses down
//! the term looking for a rule that fits. It has to be, because the obligations
//! it serves arise inside a definitional-equality derivation, where there is no
//! inference in progress to ask.
//!
//! The obligation at a *declaration* is not like that. `check_declar` infers
//! `val`'s type, and the whole point of instrumenting inference is that the
//! recursion which computes the type can carry the derivation that the term
//! inhabits it. So [`Certifier`]'s typing methods — `ty_sort`, `ty_const`,
//! `ty_local`, `ty_conv`, `ty_app`, `ty_lam`, `ty_proj`, `ty_let` — are the same
//! rules with the search removed: each is handed the premises inference has already
//! computed, does no recursion of its own, and either composes them or reports a
//! named gap. The conversion premise of the application rule is exactly the
//! certificate `assert_def_eq` used to confirm and discard.
//!
//! Measured: the search cost 36% of `init-prelude`'s runtime and found nothing
//! the composed derivations do not find. It is gone; see `MEASUREMENTS.md`.
//!
//! A `Π` type is very often written as a defined *name* rather than spelled out,
//! so two delta steps are part of the judgement: [`TgBackend::expose_pi`]
//! unfolds a constant at the head of a function's type until the `Π` appears,
//! and `has_type` unfolds the *target* along its defining equation when no other
//! clause matches. Both are pure delta — no `whnf`, no definitional equality —
//! so neither can re-enter the checker, and the membership is carried back
//! across the defining equation rather than restated.
//!
//! **What is left is dominated by shapes no typing rule can reach** (see
//! [`ht_report`]). Over the tutorial corpus, of 552 obligations: 278 are about a
//! *local* at the top level, where nothing is assumed and nothing is derivable;
//! 164 are about an opaque constant or an application of one, which is an
//! inductive type, constructor or recursor and has no axioms at all. On
//! `init-prelude`, of 17537: 5186 local, 3959 opaque. So the typing rules cannot
//! close this category on their own — the interpretation of *inductives* is what
//! the opaque half needs, and it is out of scope for the inductive-free
//! fragment.
//!
//! Where the obligation is not discharged outright it is **reduced, and only
//! failing that carried**. Reduced: `⟦a⟧ ∈ ⟦A⟧` usually follows from the typing
//! of the *locals* `a` mentions, and those are exactly the assumptions a `λ`
//! binder introduces — so the certificate becomes
//! `⊢ (⟦w₁⟧ ∈ ⟦A₁⟧ ∧ …) → ⟦redex⟧ = ⟦reduct⟧` and every conjunct is discharged
//! when the checker climbs back out of the binders. Carried: the certificate is
//! `⊢ (⟦a⟧ ∈ ⟦A⟧) → ⟦redex⟧ = ⟦reduct⟧` — a complete derivation of a weaker
//! statement, not an assertion — and every rule below merges its premises'
//! assumptions and lifts its reasoning through the conjunction.
//!
//! The difference between the two matters at the binder. A raw `⟦a⟧ ∈ ⟦A⟧`
//! mentions the binder's variable *inside a compound term*, so `ax_dist` refuses
//! to generalise past it — correctly, since the assumption is not uniform in the
//! variable — and the whole congruence fails. The reduced form is the guard
//! being introduced there, so it is peeled off instead. That is what took
//! `028_peano2` and `029_peano3` from 8 and 9 gaps to zero: their last remaining
//! gap was one blocked generalisation each.
//!
//! Carrying, rather than admitting, is what stopped the obligation poisoning
//! whole subtrees: a beta step that could not discharge it used to become an
//! admit, and every `trans`, `symm` and congruence above it "over an admitted
//! premise". Measured over the tutorial corpus, that change took 726 gaps to
//! 586 and removed the 206 `beta: argument not shown to lie in the binder's
//! domain` gaps entirely; on `good/init-prelude.ndjson`, 23812 to 18025.
//!
//! The typing rules above then take the tutorial corpus from 545 gaps to 528
//! and from 65 files at zero gaps to 67 — the two added are `028_peano2` and
//! `029_peano3`, which completes the **inductive-free fragment** (tutorial
//! exports 001–032, before `033_empty` introduces the first `inductive`: all 27
//! of them now report zero gaps and zero escapes). On `init-prelude`, 15953 to
//! 15937, with 1451 of 17537 obligations discharged rather than 486 — a small
//! movement for the reason the ledger gives, that 8919 of its obligations are
//! about a local at the top level or about an opaque constant, and no typing
//! rule can reach either.
//!
//! # Honesty
//!
//! **Every rule that concludes something about two specific terms is handed
//! those terms and checks its result against them.** [`Certifier::beta`],
//! [`Certifier::delta`], [`Certifier::zeta`], [`Certifier::lam_cong`],
//! [`Certifier::pi_cong`], [`Certifier::app_cong`], [`Certifier::trans`] and
//! [`Certifier::symm`] — the rules that build a chain rather than read one off —
//! check before returning [`TgCert::Proved`] that the theorem they hold is
//! literally `⟦a⟧ = ⟦b⟧` for the `a`, `b` the checker claimed equal; `refl`,
//! `sort` and `const_eq` compare the two interpretations directly.
//!
//! The check goes through [`CondEq::proves`], so a *conditional* premise is
//! matched on the same equation as an unconditional one rather than being
//! exempted from the comparison.
//!
//! A *conditional* certificate is held in its own variant and never passes for
//! an unconditional one — [`TgCert::thm`] answers `None` for it — and the
//! assumptions it advertises are checked, on construction, to be literally the
//! antecedent of the theorem it carries ([`CondEq::new`]). And a conditional
//! certificate that reaches the checker as an *answer* is not a proof of what
//! the checker claimed, so it is counted and reported as a gap; see the escape
//! ledger next to [`escaped`]. Over the tutorial corpus 133 certificates finish
//! that way, and 2622 on `init-prelude`; those numbers are in the totals above,
//! not excluded from them.
//!
//! [`TgBackend::has_type_a`] has the same single exit guard it always had: the
//! theorem it hands back must literally conclude `⟦e⟧ ∈ ty` for the `e` and `ty`
//! it was asked about. Under a binder the statement is
//! `⊢ conj(assumptions) → ⟦e⟧ ∈ ty` and the guard compares against *that*, with
//! the assumptions checked to be literally the antecedent, and to extend the
//! list the clause was asked for — so a clause cannot
//! quietly drop one. Assumptions are introduced in exactly two places (a `λ`
//! binder, for its own variable; a beta step, for the locals of its argument)
//! and discharged in exactly one, which checks that what is left over is
//! precisely what it was handed. The entry point asks with none, so what
//! `beta_step` receives is an unconditional theorem.
//!
//! `app_cong`, `trans` and `symm` used to be the exception — handed
//! sub-*certificates* only, so unable to see what they were supposed to be
//! proving — and are not any more. How much they were waving through is now a
//! measured quantity rather than a guess: the number of calls whose derivation
//! **fails** the comparison, reported on its own line by [`global_report`].
//!
//! | rule | tutorial corpus (91 files) | `init-prelude` |
//! | --- | ---: | ---: |
//! | `app_cong` | 9 (in 7 files) | 2 |
//! | `trans` | 0 | 0 |
//! | `symm` | 0 | 0 |
//!
//! It is a separate line and not a gap row, because a failed guard does not
//! always mean a gap: when the two sides interpret to the *same* term,
//! reflexivity proves the claim outright and there is nothing left to report.
//! That is what happens to both `init-prelude` mismatches, which is why the
//! total there goes **down** by one — a `trans` that used to compose over an
//! admitted premise now composes over a real reflexivity. The nine tutorial
//! mismatches are genuine gaps and are reported as such, taking the corpus from
//! 535 to 545: nine `congruence: derived equation does not match the claim`,
//! plus a cascade of nine into `pi congruence over an admitted body premise`
//! (156 → 165) and one into `congruence over an admitted premise` (36 → 37),
//! less nine that were being reported as `pi congruence: the body certificate is
//! not the fibres' pointwise equation` (12 → 3). The count rose because the
//! mis-stated claim is now named where it is made instead of upstream of it. All
//! nine fall in files that already had gaps; the 65 files at zero gaps are the
//! same 65.
//!
//! That `trans` and `symm` never miss, and that `app_cong` misses twice in
//! 79,516 derivations on `init-prelude`, is worth stating plainly, because it
//! contradicts what this module used to say (see the `Π` section below): the
//! certificates arriving at a binder are about the terms the checker claimed, so
//! `app_cong` was not the reason `pi_cong` could not use them.
//!
//! [`Certifier::pi_cong`] is handed both terms and checks, and has two routes
//! to a derivation — congruence and Extensionality. What each buys is stated
//! plainly next.
//!
//! # What `Π` congruence still costs
//!
//! Every `Type`-clause `Π` interprets as a `dprod_C` whose head symbol depends
//! on the *shape* of the fibre — the constant fibre (a body that ignores its
//! binder) being the degenerate shape at the bare-hole skeleton, one symbol
//! corpus-wide. So `pi_cong` is in the same two positions `lam_cong` is, and
//! takes the same two routes:
//!
//! * both sides the same `dprod_C` — congruence over its arguments;
//! * two *different* `dprod`s — dependent-product Extensionality
//!   ([`dprod_ext_n`]), whose pointwise premise is read off the body certificate
//!   by the same [`TgBackend::pointwise_premise`] the lambda rule uses. Two
//!   spellings of one arrow whose `dep` classification disagrees (the
//!   β-unstable case) land here, the constant fibre against the dependent one.
//!
//! There is no constant-fibre *bridge* in the conversion path any more: with
//! one clause there are no two interpretation spellings to bridge, and
//! [`dprod_const_fibre_n`] survives as [`TgBackend::dprod_fs_eq`] — the seam to
//! theorems `derived` states over `fs` — rather than as a conversion rule. The
//! history below predates that removal; its measurements are records, and the
//! bridge rows it names are gone with the clause.
//!
//! Measured on `good/init-prelude.ndjson`, against the previous encoding (a
//! dependent `Π` as an opaque `pi` symbol over the raw de Bruijn body):
//!
//! | gap | before | after |
//! | --- | ---: | ---: |
//! | `pi congruence` (all reasons) | 4538 | 4480 |
//! | … dependent/non-dependent interpret differently | 1196 | **0** |
//! | … cascade: the body premise was itself admitted | 2427 | 2868 |
//! | … the body certificate does not make the fibre constant | — | 621 |
//! | … the body certificate is not the fibres' pointwise equation | — | 283 |
//! | **TOTAL gaps** | 16009 | **15954** |
//!
//! and over the tutorial corpus 538 → 535, with 65 of 91 files at zero gaps
//! rather than 64.
//!
//! **The encoding mismatch is gone as a category, and what replaces it is
//! mostly not `pi_cong`'s to fix.** Of the 621 bridge failures, ~500 are cases
//! where the certificate handed down is *reflexive*.
//!
//! This was previously read as `app_cong` being unable to see what it was
//! supposed to be proving, and so handing up a certificate that need not be
//! about the binder's bodies at all. Guarding `app_cong` settles that question,
//! and the reading was wrong: with the guard in place `app_cong`'s derivation
//! misses its claim **twice** over the whole of `init-prelude`, and all 621
//! bridge failures and 283 pointwise failures remain, unchanged to the unit. The
//! reflexive certificates really are about the two bodies — the bodies are the
//! same term, which is why the certificate is reflexive — and what they fail to
//! establish is the thing the bridge actually needs, that the *fibre* is
//! constant in the binder. That is a property of the fibre's construction, not
//! of the certificate's provenance, and it is `pi_cong`'s to fix after all.
//!
//! The guard did move the tutorial numbers, but in the opposite direction from
//! the one that hypothesis predicts: `pi congruence: the body certificate is not
//! the fibres' pointwise equation` drops from 12 to 3 there, because nine claims
//! that used to arrive at `pi_cong` already bent are now stopped, and named, at
//! the `app_cong` that bent them.
//!
//! The largest remaining category by far is still the cascade: a beta step below
//! whose typing obligation is undischargeable, which no congruence rule can
//! repair.
//!
//! ## Both categories are now zero, and the reading above was wrong again
//!
//! The two rows the previous paragraphs are about — the bridge's
//! "does not make the fibre constant" and Extensionality's "is not the fibres'
//! pointwise equation" — are **gone**, and the reason has nothing to do with the
//! fibre's construction or with what the certificates are about. It was measured
//! by probing every failure of [`TgBackend::pointwise_premise`] on
//! `init-prelude`: in **216 of 216** the two fibre unfoldings already matched the
//! certificate exactly, and what refused was
//! [`TgBackend::guard_and_generalise_at`], because the certificate carried an
//! assumption mentioning the very binder variable being generalised — always a
//! membership `t(w) ∈ s`, a beta typing obligation about a binder-dependent
//! argument. `Thm::ax_dist` will not move a `∀` past a free occurrence, which is
//! correct; the mistake was stating the assumption at a variable about to leave
//! scope. Hoisting it to `∀w. (w ∈ A → φ(w))` is the whole fix.
//!
//! | gap | before | after |
//! | --- | ---: | ---: |
//! | … the body certificate does not make the fibre constant | 465 | **0** |
//! | … the body certificate is not the fibres' pointwise equation | 214 | **0** |
//! | … cascade: the body premise was itself admitted | 1293 | 743 |
//! | escaped assumptions | 804 | 1484 |
//! | **TOTAL gaps** | 10219 | **9650** |
//!
//! The escape row is the cost and it is not incidental: nothing yet discharges a
//! hoisted assumption, so it survives to the boundary and is reported. Primary
//! gaps fell by 1249; 680 of that came back as escapes. The hoisted shape is
//! chosen so that a discharge is *reachable* — it is literally what
//! [`TgBackend::has_type_lam`] proves — which the un-hoisted `φ(w)` was not.
//!
//! So the standing lesson repeats a third time: each of the three readings of
//! this gap category (an `app_cong` handing up an unrelated certificate; a
//! property of the fibre's construction) was refuted by instrumenting the thing
//! rather than reasoning about it.
//!
//! ## …and a fourth time: the consumer for the hoisted shape proves nothing
//!
//! The next lever recorded above was the obvious one: the hoisted assumption is
//! a **guarded family** `∀x. (x ∈ A → ⟦a(x)⟧ ∈ ⟦A(x)⟧)`, the shape
//! [`TgBackend::has_type_lam`] proves, so a *consumer* — a rule that re-opens
//! the family at its own variable, types the subject under the binder's own
//! guard, and peels the assumption — should convert those escapes into
//! discharges. That consumer now exists ([`TgBackend::discharge_families`],
//! hooked at [`TgBackend::cert`], the one funnel every conditional certificate
//! passes through), and it is **measured to fire zero times**, corpus-wide.
//!
//! Not zero because the peel is unreachable — it reaches the typing call in
//! every case — but because the typing call fails. Instrumented on
//! `init-prelude`, of 1378 guarded families offered:
//!
//! | | count |
//! | --- | ---: |
//! | offered | 1378 |
//! | the binder is free in no other assumption | 1378 |
//! | …the obligation is a membership (rest are *nested* families) | 825 |
//! | …its subject has a Lean node | 825 |
//! | …**`has_type` derived it under the guard** | **0** |
//!
//! And the reason is structural rather than incidental. A hoisted assumption is
//! a beta obligation that reached [`TgBackend::domain_obligation`]'s **raw
//! fallback**, which fires only after `has_type` has already failed both with no
//! assumptions *and* under [`TgBackend::local_premises`] — the typings of every
//! local the argument mentions, a superset of the single guard the consumer can
//! offer. Retrying under the guard is therefore the same failing call, weakened.
//!
//! What the families are about, probed by head symbol on `init-prelude` and on
//! the tutorial corpus, is the same list either way: **constructors of
//! inductives this backend does not interpret** — `Decidable.isTrue/isFalse`,
//! `Option.some`, `Or.inl/inr`, `Lean.Name.str/num`, `Lean.Syntax.node`,
//! `Prod.mk`, `RBTree.red/black/leaf`, `RTree.leaf/node`, `Acc.intro`,
//! `Eq.refl` — together with applications of `N.rec`/`List.rec`, whose curried
//! nests have no typing theorem. None of those has a membership fact to derive
//! *from*; see [`TgBackend::ind_mems`] and [`CtorRule`] for the two that do.
//!
//! The consumer is kept, and the ladder above is printed on every run, for two
//! reasons: the zero is then a re-measured fact rather than a remembered one,
//! and the moment a constructor gains a membership theorem this is the rule that
//! spends it. It costs nothing measurable (`init-prelude` 11.59–11.68 s and
//! 169.0–169.7 MB before, 11.59–11.61 s and 169.5–169.7 MB after, three runs
//! each) and changes no number anywhere in the corpus.
//!
//! ## What the escapes actually are
//!
//! Since the guarded family turned out to be a wrapper rather than a cause, the
//! whole escape population was probed instead — every certificate that reached a
//! boundary still conditional, classified by what it assumes, with the family
//! wrappers unwrapped. Corpus-wide (68 escaping certificates, 119 assumption
//! atoms) and on `init-prelude` (1484 certificates, 2089 atoms):
//!
//! | the escaping certificate assumes | tutorial | `init-prelude` |
//! | --- | ---: | ---: |
//! | only context locals' own typings `⟦w⟧ ∈ ⟦A⟧` | 26 | 413 |
//! | those plus a lambda's typing | 2 | 29 |
//! | at least one constructor/recursor obligation | 40 | 1042 |
//!
//! | assumption atom | tutorial | `init-prelude` |
//! | --- | ---: | ---: |
//! | a context local's own typing | 64 | 713 |
//! | a lambda's typing (the `Sort`-encoding obstruction) | 15 | 193 |
//! | everything else — constructors, recursors, opaque heads | 40 | 1183 |
//!
//! 19 of the tutorial's 68 and 721 of `init-prelude`'s 2089 atoms are wrapped in
//! at least one guarded family, nested up to **six** deep on `077` — the same
//! obligation re-hoisted at each successive binder. Unwrapping it, which the
//! consumer does correctly, exposes an obligation nothing can discharge.
//!
//! The first row of the second table is the interesting one and it is **not** a
//! missing rule. `⟦w⟧ ∈ ⟦A⟧` for a context local is exactly what Carneiro's
//! Theorem 6.7 quantifies over: `Γ ⊢ e ≡ e'` is interpreted as *for all
//! `γ ∈ ⟦Γ⟧`, `⟦Γ ⊢ e⟧γ = ⟦Γ ⊢ e'⟧γ`*, so a certificate conditional on precisely
//! the ambient context's typings is the judgement's own statement rather than a
//! step taken on trust — the bare equation the ledger compares it against is
//! *stronger* than what the thesis proves, and false in general off `⟦Γ⟧`. What
//! stands in the way of counting those differently is that the backend cannot
//! today tell an *ambient* local (introduced by the checker's `infer`, above the
//! `def_eq` query) from one the query opened itself, and only the first kind is
//! entitled to this reading. That distinction is the next lever on this row, and
//! it is a decision about what a top-level claim means, not a derivation.
//!
//! Two things this changed elsewhere, both consequences of opening the binder:
//!
//! * `def_eq_binder_aux` now instantiates `Π` frames at the locals introduced
//!   above them, exactly as it already did for `λ` frames. It deliberately did
//!   not, *because* `⟦Π⟧` was built over the raw body; that reason has gone.
//!   Without the change the bridge and the Extensionality route are unreachable
//!   below the outermost binder (measured: 16097 gaps rather than 15954).
//! * The **de Bruijn shift** category — 756 gaps where the claim had two
//!   different `bvar` symbols for one binder — has gone with the `bvar`s.

use crate::util::{ExprPtr, LevelPtr, LevelsPtr, NamePtr, TcCtx};
use crate::env::Declar;
use crate::expr::Expr;
use crate::level::Level;
use derived::funcs::Apply;
use derived::inductive::{CtorSpec, DeclSpec, Slot};
use crate::certify::Certifier;
use crate::sealed::Sealed;
use kernel::{Env, FnSym, Formula, FreeVar, Term, Thm};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::rc::Rc;

/// A certificate: a real kernel theorem, a real kernel theorem that still rests
/// on assumptions, or a named gap.
///
/// Making the gap a *variant* rather than a silent success is the point. A
/// backend that could only return `Thm` would have to either refuse (breaking
/// the checker) or forge (defeating the exercise); this way an unproved step is
/// recorded, propagates through the combinators, and can be reported.
///
/// [`TgCert::Conditional`] is a *separate variant* rather than a `hyps` field on
/// `Proved`, and that is deliberate. `Proved` means "this equation is derived,
/// full stop"; every existing consumer of [`TgCert::thm`] keeps exactly that
/// reading, and a rule that has not been taught about assumptions cannot
/// silently treat a conditional derivation as an unconditional one — the
/// compiler makes it say what it does with the new variant. The cardinal rule
/// ("never return `Proved` for a theorem not matched against the claim") is
/// therefore still checkable by reading the `Proved` sites alone.
#[derive(Debug)]
pub enum TgCert {
    /// A genuine derivation of `⟦a⟧ = ⟦b⟧`.
    Proved(Thm),
    /// A genuine derivation of `⊢ (h₁ ∧ … ∧ hₙ) → ⟦a⟧ = ⟦b⟧`, `n ≥ 1`.
    ///
    /// The theorem is complete — nothing here is asserted — but the *claim* the
    /// checker made is the bare equation, so until every `hᵢ` is discharged this
    /// is a step taken on trust. See [`escape_report`]: a conditional
    /// certificate that is never handed back to a rule is counted and reported
    /// as a gap.
    Conditional {
        /// Literally `⊢ conj(hyps) → ⟦a⟧ = ⟦b⟧`; checked on construction.
        thm: Thm,
        /// The assumption atoms, in the order the left-nested conjunction
        /// `conj(R ++ [h]) = conj(R) ∧ h` puts them.
        hyps: Vec<Formula>,
    },
    /// A step that was taken on trust, tagged with why.
    Admitted(&'static str),
}

/// Cloning a conditional certificate creates a *second* obligation, and the
/// escape ledger counts copies, not derivations: a copy that is stored in one of
/// the checker's caches and a copy that is handed back as an answer are both
/// certificates that have to be accounted for. So the `Clone` impl is written
/// out rather than derived, in order to bump the counter.
impl Clone for TgCert {
    fn clone(&self) -> Self {
        match self {
            TgCert::Proved(t) => TgCert::Proved(t.clone()),
            TgCert::Conditional { thm, hyps } => {
                note_conditional();
                CONDITIONAL_COPIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                TgCert::Conditional { thm: thm.clone(), hyps: hyps.clone() }
            }
            TgCert::Admitted(r) => TgCert::Admitted(r),
        }
    }
}

impl TgCert {
    /// The underlying theorem, if this step was actually proved **outright**.
    ///
    /// A conditional derivation deliberately answers `None` here: its theorem is
    /// not the equation, it is an implication, and a caller that has not been
    /// taught to discharge the antecedent must not be handed it.
    pub fn thm(&self) -> Option<&Thm> {
        match self {
            TgCert::Proved(t) => Some(t),
            TgCert::Conditional { .. } | TgCert::Admitted(_) => None,
        }
    }
    /// Whether this certificate is a complete, unconditional derivation.
    ///
    /// **Not sufficient for caching.** `kernel::Thm` is a sequent, so a
    /// `Proved(Γ ⊢ a = b)` with `Γ` non-empty answers `true` here and is still
    /// valid only where `Γ` holds; the cache predicate is
    /// [`crate::certify::is_unconditional`], which asks the theorem as well as
    /// the variant. This one keeps its meaning — "the rule concluded the
    /// equation itself, not an implication and not an admission" — because that
    /// is what its other callers are asking.
    pub fn is_proved(&self) -> bool { matches!(self, TgCert::Proved(_)) }

    /// The kernel hypotheses the certificate's theorem stands under, for
    /// whichever variant carries a theorem; empty for an admission.
    ///
    /// Distinct from [`TgCert::Conditional`]'s `hyps`, which are antecedents
    /// *inside* the formula and therefore travel with it. These are the sequent's
    /// `Γ`, which does not travel with the formula and so must not be carried
    /// into a store keyed on anything that omits it. See
    /// [`crate::certify::hypothesis_free`].
    pub fn hyps(&self) -> &[Formula] {
        match self {
            TgCert::Proved(t) => t.hyps(),
            TgCert::Conditional { thm, .. } => thm.hyps(),
            TgCert::Admitted(_) => &[],
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Conditional equations.
//
// The one obligation this backend cannot generally discharge is a *typing*
// one: `beta_conditional_n` needs `⟦a⟧ ∈ ⟦A⟧` for the binder's domain, and
// `domain_premise` knows only two instances of it. Rather than admit the step,
// the premise is recorded as a genuine antecedent and carried: every rule below
// merges its premises' assumption sets and lifts its equality reasoning through
// the conjunction, and at a λ binder the assumption about that binder's own
// variable is discharged into `lam_ext_n`'s pointwise premise.
//
// Nothing here is trusted. A `CondEq` is checked on construction to be exactly
// `⊢ conj(hyps) → (a = b)`, so a rule that mangles the assumption list produces
// `None` — hence a reported gap — rather than a certificate that claims more
// than it proves.
// ─────────────────────────────────────────────────────────────────────────────

/// A derivation of an equation together with the assumptions it rests on:
/// `thm` is literally `⊢ (h₁ ∧ … ∧ hₙ) → a = b`, or `⊢ a = b` when `hyps` is
/// empty.
///
/// The conjunction is **left-nested**, so `conj(R ++ [h]) = conj(R) ∧ h` and
/// [`derived::uncurry`] peels the last assumption off — which is what the
/// discharge at a binder needs.
#[derive(Debug, Clone)]
struct CondEq {
    thm: Thm,
    hyps: Vec<Formula>,
}

impl CondEq {
    /// Check `thm` really is `⊢ conj(hyps) → (a = b)` and package the two.
    ///
    /// This is the only constructor, so no `CondEq` anywhere can misdescribe its
    /// own assumptions.
    fn new(thm: Thm, hyps: Vec<Formula>) -> Option<CondEq> {
        match conj_of(&hyps) {
            None => {
                thm.concl().as_eq()?;
            }
            Some(h) => {
                let (ante, concl) = thm.concl().as_imp()?;
                if ante != h {
                    return None
                }
                concl.as_eq()?;
            }
        }
        Some(CondEq { thm, hyps })
    }

    /// An unconditional derivation.
    fn plain(thm: Thm) -> Option<CondEq> { CondEq::new(thm, Vec::new()) }

    /// `⊢ t = t`.
    fn refl(t: Term) -> CondEq { CondEq { thm: Thm::eq_refl(t), hyps: Vec::new() } }

    /// The equation derived, under the assumptions.
    fn as_eq(&self) -> Option<(Term, Term)> { u_as_eq(&self.thm, conj_of(&self.hyps).as_ref()) }

    /// Whether this derivation is of the equation `l = r`.
    fn proves(&self, l: &Term, r: &Term) -> bool { self.as_eq() == Some((l.clone(), r.clone())) }
}

/// `h₁ ∧ … ∧ hₙ`, left-nested; `None` for the empty list.
fn conj_of(hyps: &[Formula]) -> Option<Formula> {
    let mut it = hyps.iter();
    let first = it.next()?.clone();
    Some(it.fold(first, |acc, h| Formula::and(acc, h.clone())))
}

/// `⊢ conj(hyps) → hyps[i]`, by peeling conjuncts off the left-nested form.
fn conj_proj(hyps: &[Formula], i: usize) -> Option<Thm> {
    let n = hyps.len();
    if i >= n {
        return None
    }
    // `cur : ⊢ conj(hyps) → conj(hyps[..k])`, starting at `k = n` with
    // reflexivity and shedding one conjunct at a time.
    let mut cur = derived::imp_refl(conj_of(hyps)?);
    let mut k = n;
    while k > i + 1 {
        let (prefix, last) = (conj_of(&hyps[..k - 1])?, hyps[k - 1].clone());
        cur = derived::syl(&cur, &derived::and_left(prefix, last))?;
        k -= 1;
    }
    if i == 0 {
        // `conj(hyps[..1])` *is* `hyps[0]`.
        return Some(cur)
    }
    derived::syl(&cur, &derived::and_right(conj_of(&hyps[..i])?, hyps[i].clone()))
}

/// Re-state `⊢ conj(from) → φ` as `⊢ conj(to) → φ`, where every assumption of
/// `from` also occurs in `to`.
///
/// This is what lets two derivations with different assumption sets be combined:
/// both are re-stated under the merged set first. It is also how assumptions get
/// *reordered*, which the discharge at a binder needs — the one being discharged
/// has to be last.
fn reassume(thm: &Thm, from: &[Formula], to: &[Formula]) -> Option<Thm> {
    if from == to {
        return Some(thm.clone())
    }
    let Some(h) = conj_of(to) else {
        // Nothing to assume: only an already-unconditional theorem qualifies.
        return from.is_empty().then(|| thm.clone())
    };
    if from.is_empty() {
        return Some(derived::a1i(thm, h))
    }
    // `⊢ conj(to) → conj(from)`, built conjunct by conjunct in `from`'s order,
    // which reproduces `from`'s own left-nesting.
    let mut acc: Option<Thm> = None;
    for f in from {
        let p = conj_proj(to, to.iter().position(|g| g == f)?)?;
        acc = Some(match acc {
            None => p,
            Some(a) => derived::hyp_and(&a, &p)?,
        });
    }
    derived::syl(&acc?, thm)
}

/// The inductive `name` belongs to: itself, or the one it is a constructor of.
fn ind_of<'t>(decls: &crate::env::Env<'_, 't>, name: NamePtr<'t>) -> Option<NamePtr<'t>> {
    match decls.get_declar(&name)? {
        Declar::Inductive(_) => Some(name),
        Declar::Constructor(c) => Some(c.inductive_name),
        _ => None,
    }
}

/// `⊢ H → φ` restated under a longer, **right**-nested `H` whose prefix is the
/// list the theorem already assumes — the move a constructor rule needs to
/// carry the type former's bridge (`H_p → app-spine(⟦T⟧,p⃗) = ind(p⃗)`) under its
/// own premises, which are the parameters followed by the fields.
///
/// Two things are deliberate and both are load-bearing.
///
/// *Right-nested.* [`reassume`] is the same move for the checker's own
/// assumption lists, which [`conj_of`] nests to the **left**; a derived rule's
/// antecedent is `derived::conj_of`'s right-nested bundle. The two are the same
/// formula for two atoms and different from three on, and a `βⱼ`-carrying
/// constructor of a one-parameter declaration has exactly three
/// (`p ∈ ⟦Sort u⟧`, `h ∈ ⟦α⟧`, `t ∈ ⟦T α⟧`), so this is the first arity at
/// which the difference is visible at all.
///
/// *Prefix, not subset.* A premise list that merely *contains* the parameters
/// is refused. Nothing would be unsound about searching for them, but a rule
/// whose premises are not in Lean's own argument order is one
/// [`TgBackend::has_type_ctor_app`] rejects positionally anyway, so a
/// permutation here would only turn a loud refusal into a diffuse gap.
fn under_prefix(thm: &Thm, prefix: &[Formula], prems: &[Formula]) -> Option<Thm> {
    let np = prefix.len();
    if prems.len() < np || prems[..np] != *prefix {
        return None
    }
    if prems.len() == np {
        return Some(thm.clone())
    }
    match np {
        // Nothing assumed: weakening is the whole of it.
        0 => Some(derived::a1i(thm, derived::conj_of(prems)?)),
        _ => derived::syl(&derived::conj_sub(prems, 0, np)?, thm),
    }
}

/// `hyps` without the entry at `i` — the binder guard a lambda rule appended
/// there before typing its body.
///
/// Used to say precisely what [`TgBackend::guard_and_generalise_at`] must have
/// left over: the outer assumptions, plus whatever the body acquired *after*
/// the guard, and nothing else. `None` if there is no such position, which is
/// how a body that somehow lost the guard declines rather than passing.
fn drop_guard(hyps: &[Formula], i: usize) -> Option<Vec<Formula>> {
    (i < hyps.len()).then(|| {
        let mut out = hyps.to_vec();
        out.remove(i);
        out
    })
}

/// The union of two assumption lists, `a`'s order first.
fn merge_hyps(a: &[Formula], b: &[Formula]) -> Vec<Formula> {
    let mut out = a.to_vec();
    for h in b {
        if !out.contains(h) {
            out.push(h.clone());
        }
    }
    out
}

// The `u_*` family: the equality toolkit of `derived`, repeated "under an
// assumption". `h = None` is the unconditional case and each function then
// coincides with its `derived` original; `h = Some(H)` works inside `⊢ H → …`,
// where `a1i` weakens and `hyp_mp` is modus ponens. Writing them this way means
// every rule below has exactly one code path, so the conditional case cannot
// drift from the unconditional one.

/// Remove assumption `i` from a conditional derivation, **by discharging it**.
///
/// `c` is `⊢ conj(hyps) → C` and `fam` is `⊢ conj(rest) → hyps[i]`, where `rest`
/// is `hyps` without that entry; the result is `⊢ conj(rest) → C`. That is
/// modus ponens, once the assumption in question has been moved to the end of
/// the conjunction so that [`derived::uncurry`] can expose it.
///
/// The assumption is *proved*, not forgotten. Nothing here can drop one
/// silently: [`reassume`] refuses unless every assumption of `hyps` is present
/// in the target list, [`derived::hyp_mp`] refuses unless `fam` proves exactly
/// the antecedent being removed, and [`CondEq::new`] re-checks the theorem
/// against the assumption list it is advertised under.
fn peel_off(c: &CondEq, i: usize, fam: &Thm) -> Option<CondEq> {
    let family = c.hyps.get(i)?.clone();
    let rest: Vec<Formula> =
        c.hyps.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, f)| f.clone()).collect();
    // `⊢ conj(rest ++ [family]) → C`: the same assumptions, with the one being
    // discharged last.
    let mut ordered = rest.clone();
    ordered.push(family);
    let restated = reassume(&c.thm, &c.hyps, &ordered)?;
    let out = match conj_of(&rest) {
        // Nothing else is assumed, so `restated` is `⊢ family → C` and `fam` is
        // `⊢ family`.
        None => Thm::mp(&restated, fam)?,
        Some(_) => derived::hyp_mp(&derived::uncurry(&restated)?, fam)?,
    };
    CondEq::new(out, rest)
}

/// `⊢ φ` ↦ `⊢ H → φ`.
fn u_a1i(thm: &Thm, h: Option<&Formula>) -> Thm {
    match h {
        None => thm.clone(),
        Some(h) => derived::a1i(thm, h.clone()),
    }
}

/// From `⊢ H → (φ → ψ)` and `⊢ H → φ` infer `⊢ H → ψ`.
fn u_mp(imp: &Thm, arg: &Thm, h: Option<&Formula>) -> Option<Thm> {
    match h {
        None => Thm::mp(imp, arg),
        Some(_) => derived::hyp_mp(imp, arg),
    }
}

/// What `⊢ H → φ` concludes — and `None` unless the antecedent is literally
/// `H`, so a theorem assuming something else cannot be mistaken for one
/// assuming this.
fn u_concl(thm: &Thm, h: Option<&Formula>) -> Option<Formula> {
    match h {
        None => Some(thm.concl().clone()),
        Some(h) => {
            let (ante, concl) = thm.concl().as_imp()?;
            (ante == *h).then_some(concl)
        }
    }
}

/// `φ ∧ ψ` taken apart. `Formula::and(a,b)` is `¬(a → ¬b)`, so this unfolds
/// that encoding; a formula that is not of that shape yields `None`.
fn as_and(f: &Formula) -> Option<(Formula, Formula)> {
    let false_ = Formula::false_();
    let (inner, r1) = f.as_imp()?;
    (r1 == false_).then_some(())?;
    let (a, nb) = inner.as_imp()?;
    let (b, r2) = nb.as_imp()?;
    (r2 == false_).then_some(())?;
    Some((a, b))
}

/// From `⊢ H → (φ ∧ ψ)` infer `⊢ H → ψ`. `derived::and_elim_right`, threaded.
fn u_and_elim_right(thm: &Thm, h: Option<&Formula>) -> Option<Thm> {
    match h {
        None => derived::and_elim_right(thm),
        Some(_) => {
            let (a, b) = as_and(&u_concl(thm, h)?)?;
            derived::syl(thm, &derived::and_right(a, b))
        }
    }
}

/// From `⊢ H → φ` and `⊢ H → ψ` infer `⊢ H → (φ ∧ ψ)`, threaded.
fn u_and_intro(a: &Thm, b: &Thm, h: Option<&Formula>) -> Option<Thm> {
    match h {
        None => Some(derived::and_intro(a, b)),
        Some(_) => derived::hyp_and(a, b),
    }
}

/// From `⊢ H → φ` and `⊢ φ → ψ` infer `⊢ H → ψ`, threaded. At `H = None` the
/// first is simply `⊢ φ` and this is modus ponens.
fn u_syl(ab: &Thm, bc: &Thm, h: Option<&Formula>) -> Option<Thm> {
    match h {
        None => Thm::mp(bc, ab),
        Some(_) => derived::syl(ab, bc),
    }
}

/// From `⊢ H → ∀x. φ` infer `⊢ H → φ[t/x]`. [`derived::inst_all`] at one
/// argument, threaded.
fn u_inst1(thm: &Thm, t: &Term, h: Option<&Formula>) -> Option<Thm> {
    match h {
        None => derived::inst_all(thm, std::slice::from_ref(t)),
        Some(_) => derived::syl(thm, &Thm::ax_inst(u_concl(thm, h)?, t.clone())?),
    }
}

/// The equation `⊢ H → (a = b)` concludes — and `None` unless the antecedent is
/// literally `H`, so a theorem assuming something else cannot be mistaken for
/// one assuming this.
fn u_as_eq(thm: &Thm, h: Option<&Formula>) -> Option<(Term, Term)> {
    match h {
        None => thm.concl().as_eq(),
        Some(h) => {
            let (ante, concl) = thm.concl().as_imp()?;
            (ante == *h).then_some(())?;
            concl.as_eq()
        }
    }
}

/// Transitivity under an assumption. `derived::eq_trans`, threaded.
fn u_eq_trans(env: &mut Env, ab: &Thm, bc: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b1) = u_as_eq(ab, h)?;
    let (b2, c) = u_as_eq(bc, h)?;
    if b1 != b2 {
        return None
    }
    let x = env.fresh_var();
    // ⊢ b = c → (a = b → a = c)
    let leib = Thm::eq_leibniz(b1, c, x, Formula::eq(a, Term::var(x)));
    let step = u_mp(&u_a1i(&leib, h), bc, h)?;
    u_mp(&step, ab, h)
}

/// Symmetry under an assumption. `derived::eq_symm`, threaded.
fn u_eq_symm(env: &mut Env, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b) = u_as_eq(ab, h)?;
    let x = env.fresh_var();
    // ⊢ a = b → (a = a → b = a)
    let leib = Thm::eq_leibniz(a.clone(), b, x, Formula::eq(Term::var(x), a.clone()));
    let step = u_mp(&u_a1i(&leib, h), ab, h)?;
    u_mp(&step, &u_a1i(&Thm::eq_refl(a), h), h)
}

/// Congruence in one argument, under an assumption. `derived::congr_arg`.
fn u_congr_arg(env: &mut Env, f: FnSym, args: &[Term], idx: usize, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
    let (a, b) = u_as_eq(ab, h)?;
    if args.get(idx) != Some(&a) {
        return None
    }
    let lhs = Term::apply(f, args.to_vec());
    let x = env.fresh_var();
    let mut hole = args.to_vec();
    hole[idx] = Term::var(x);
    let leib = Thm::eq_leibniz(a, b, x, Formula::eq(lhs.clone(), Term::apply(f, hole)));
    let step = u_mp(&u_a1i(&leib, h), ab, h)?;
    u_mp(&step, &u_a1i(&Thm::eq_refl(lhs), h), h)
}

/// From `⊢ H → φ(x⃗)` infer `⊢ H → ∀x⃗. φ(x⃗)`, outermost variable first.
///
/// The one shape the `u_*` family cannot reach: they all conclude `⊢ H → φ`
/// with the quantifier outside, and a pointwise `HYP` conjunct needs it
/// **inside** the implication so that the assumptions the derivation escapes
/// with stay outside. [`Thm::ax_dist`]'s side condition — `H` does not mention
/// the variable — is exactly the soundness condition, and it is checked there
/// rather than assumed here; `None` if any part of it fails.
fn gen_under(thm: &Thm, h: &Formula, xs: &[FreeVar]) -> Option<Thm> {
    let mut cur = thm.clone();
    for x in xs.iter().rev() {
        let (ante, body) = cur.concl().as_imp()?;
        if ante != *h {
            return None
        }
        let dist = Thm::ax_dist(*x, h.clone(), body)?;
        cur = Thm::mp(&dist, &Thm::gen_checked(*x, &cur)?)?;
    }
    Some(cur)
}

/// Congruence in every argument, under an assumption. `derived::congr`.
fn u_congr(env: &mut Env, f: FnSym, eqs: &[Thm], h: Option<&Formula>) -> Option<Thm> {
    let mut args: Vec<Term> = Vec::with_capacity(eqs.len());
    for e in eqs {
        args.push(u_as_eq(e, h)?.0);
    }
    if args.len() != f.arity() as usize {
        return None
    }
    let mut acc = u_a1i(&Thm::eq_refl(Term::apply(f, args.clone())), h);
    for (i, e) in eqs.iter().enumerate() {
        let step = u_congr_arg(env, f, &args, i, e, h)?;
        args[i] = u_as_eq(e, h)?.1;
        acc = u_eq_trans(env, &acc, &step, h)?;
    }
    Some(acc)
}

// ─────────────────────────────────────────────────────────────────────────────
// There is no cut-off on the assumption count.
//
// There used to be one — `MAX_HYPS = 12` — on the size of the set a
// [`TgCert::Conditional`] carries, guarding against the quadratic in
// [`TgBackend::ceq_trans`]: every combination re-states both premises under the
// merged set, at one projection per assumption. It was described as never hit
// at the shipped settings. It was hit, and the coverage report said so on every
// run: the `max N assumptions` figure read exactly 12, the cap, because that is
// where the cap put it.
//
// The measured distribution, over `good/**` minus `perf/` (99 files, the
// tutorials and `init-prelude` included) with the cap lifted — 94659 merged
// sets:
//
// | size | sets | cum. |
// |-----:|-----:|-----:|
// | 0    | 29220 |  30.9% |
// | 1    | 39944 |  73.1% |
// | 2–4  | 20896 |  95.1% |
// | 5–8  |  3078 |  98.4% |
// | 9–12 |   887 |  99.3% |
// | 13–16|   565 |  99.9% |
// | 17–22|    69 | 100.0% |
//
// Unlike the hole distribution, this one *stops*: nothing anywhere in the
// corpus merges more than 22 assumptions, and a cap of 32 is already
// indistinguishable from no cap at all. So the sweep is a plain trade of
// coverage against ~6% of the run, with no tail to worry about:
//
// | cut-off | prelude gaps | prelude runtime | prelude RSS | tutorial gaps | tutorial files at 0 | fragment |
// |--------:|-------------:|----------------:|------------:|--------------:|--------------------:|---------:|
// | 0       | 23801        | 4.3 s           | 90 MB       | 736           | 64                  | 25/27    |
// | 2       | 20086        | 6.5 s           | 100 MB      | 696           | 64                  | 25/27    |
// | 4       | 16870        | 7.3 s           | 110 MB      | 585           | 65                  | 25/27    |
// | 8       | 15993        | 8.2 s           | 127 MB      | 531           | 67                  | 27/27    |
// | 12      | 15937        | 9.0 s           | 132 MB      | 528           | 67                  | 27/27    |
// | 16      | 15832        | 9.5 s           | 134 MB      | 527           | 67                  | 27/27    |
// | 32      | 15782        | 9.5 s           | 133 MB      | 527           | 67                  | 27/27    |
// | none    | 15782        | 9.5 s           | 133 MB      | 527           | 67                  | 27/27    |
//
// So the cap was buying 6% of the run for 155 `init-prelude` gaps and one
// tutorial gap, and it is gone. What is left in its place is the
// `max N assumptions` figure in the coverage report, which now reads the real
// maximum (22) rather than the cap, so that the day this does start to matter
// is a number on the report rather than an audit.
//
// **What removing it exposes, honestly.** The set is not bounded by anything in
// the checker any more; it is bounded by the input, at roughly the number of
// locals in scope at a beta redex ([`TgBackend::local_premises`] contributes one
// per free local, and each `λ` binder one more). The re-statement cost is
// quadratic in that, so a development with far deeper binder nesting than
// `init-prelude`'s 22 would pay for it. That is a growth law to measure against
// mathlib, not a reason to pick a number now: the number that was picked cost
// coverage on a corpus that never came close to needing it.
// ─────────────────────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────────────────────
// The shared prelude.
//
// The ambient signature — the universe tower, `app`, the function space and the
// facts about them no single construction owns — is `derived::prelude`. It is
// built once per thread and replayed, and `fast_forward` advances a fresh `Env`
// past the ids it used; see that module's header for why replaying is sound.
// ─────────────────────────────────────────────────────────────────────────────

use derived::prelude::{fast_forward, prelude, Prelude};

// ─────────────────────────────────────────────────────────────────────────────
// The n-ary middle layer, now in `derived/`.
//
// `derived::funcs::lambda`/`beta_conditional`, `derived::ext`'s `lam_cong`,
// `pi_cong`, `const_fibre` and `lam_typing`, and `derived::prop::cond` all take
// a *unary* body or fibre symbol. The skeleton decomposition described in the
// module docs produces symbols with `k` extra parameters, so each of those
// constructions has an **n-ary port** that threads the prefix through the
// argument lists and coincides with the original at `k = 0`.
//
// None of them mentions an `Expr`, a `NamePtr` or a `TcCtx` — they are stated
// entirely in kernel `Term`s and `Thm`s — so by `README.md`'s boundary rule
// they belong in `derived/`, and that is where they now are:
//
//   derived::ext::lam_ext_n            derived::ext::image_ext_n
//   derived::ext::dprod_ext_n          derived::prop::cond_ext_n
//   derived::ext::image_symbol_n       derived::ext::dprod_symbol_n
//   derived::ext::section_n            derived::ext::dprod_const_fibre_n
//   derived::ext::lam_pair_val_n       derived::ext::lam_single_valued_n
//   derived::ext::lam_in_funspace_n    derived::ext::lam_in_dprod_n
//
// together with `derived::funcs::lambda_n`/`beta_conditional_n`, which moved
// earlier for `derived::wlist_fun`'s sake. Each carries its own interface
// header stating exactly what it proves; nothing below needs to know how.
//
// Nothing there is trusted either: like everything outside `kernel/`, they can
// only reach a `Thm` through the kernel's primitive rules, so a mistake yields
// a `None` — hence a reported gap — rather than a false theorem.
// ─────────────────────────────────────────────────────────────────────────────

use derived::ext::{
    dprod_const_fibre_n, dprod_ext_n, dprod_symbol_n, image_symbol_n, lam_ext_n, lam_in_dprod_n,
    lam_in_funspace_n,
};
use derived::funcs::{beta_conditional_n, lambda_n};
use derived::prop::cond_ext_n;

// ─────────────────────────────────────────────────────────────────────────────
// The two application-typing rules.
//
// Both are the *characteristic property* of the interpretation of a `Π` type,
// applied — which is the whole content of Lean's application typing rule once
// `Π` means what it means here. They are free functions rather than methods so
// that they can also be tested against hand-built inhabitants; see
// `app_in_codomain_types_the_identity` and `app_in_fibre_types_a_section`.
//
// Both are threaded through the `u_*` family, so that they work equally under a
// binder's assumption `w ∈ D` (`h = Some(H)`) and outside one (`h = None`);
// see [`TgBackend::has_type_h`].
//
// Neither can produce a false claim: a `Thm` is only obtainable from the
// kernel's rules, and every caller re-checks the conclusion against the
// membership it is supposed to be.
// ─────────────────────────────────────────────────────────────────────────────

/// `⊢ H → app(f,x) ∈ cod` from `⊢ H → f ∈ fs(dom,cod)` and `⊢ H → x ∈ dom`.
///
/// `fs_app_mem` must be [`Prelude::fs_app_mem`],
/// `⊢ ∀a ∀b ∀f ∀x. ((f ∈ fs(a,b) ∧ x ∈ a) → app(f,x) ∈ b)`.
#[allow(clippy::too_many_arguments)]
fn app_in_codomain(
    fs_app_mem: &Thm,
    dom: &Term,
    cod: &Term,
    f: &Term,
    x: &Term,
    h_f: &Thm,
    h_x: &Thm,
    h: Option<&Formula>,
) -> Option<Thm> {
    let inst = derived::inst_all(fs_app_mem, &[dom.clone(), cod.clone(), f.clone(), x.clone()])?;
    let both = match h {
        None => derived::and_intro(h_f, h_x),
        Some(_) => derived::hyp_and(h_f, h_x)?,
    };
    u_mp(&u_a1i(&inst, h), &both, h)
}

/// `⊢ H → app(f,x) ∈ b(h⃗,x)`, unfolded, from `⊢ H → f ∈ dprod(h⃗,dom)` and
/// `⊢ H → x ∈ dom`.
///
/// `dprod_def` is [`Fibre::dprod_def`] — `f ∈ dprod(h⃗,A)` iff `f` lies in a
/// function space *and* `∀x. (x ∈ A → app(f,x) ∈ b(h⃗,x))` — and it is the
/// second conjunct that does the work. `b_def` is [`Fibre::b_def`], which turns
/// `b(h⃗,x)` into the fibre skeleton with `x` in the binder slot; that is what
/// makes the result line up syntactically with `⟦B[x]⟧`, by exactly the argument
/// [`TgBackend::beta_step`] makes for the body.
#[allow(clippy::too_many_arguments)]
fn app_in_fibre(
    env: &mut Env,
    app: FnSym,
    dprod_def: &Thm,
    b_def: &Thm,
    holes: &[Term],
    dom: &Term,
    f: &Term,
    x: &Term,
    h_f: &Thm,
    h_x: &Thm,
    h: Option<&Formula>,
) -> Option<Thm> {
    let mut inst = holes.to_vec();
    inst.push(dom.clone());
    inst.push(f.clone());
    let at_f = derived::inst_all(dprod_def, &inst)?;
    let members = u_mp(&u_a1i(&derived::iff_mp(&at_f)?, h), h_f, h)?;
    let section = u_and_elim_right(&members, h)?;
    let at_x = u_inst1(&section, x, h)?;
    let in_fibre = u_mp(&at_x, h_x, h)?;

    let mut binst = holes.to_vec();
    binst.push(x.clone());
    let unfold = derived::inst_all(b_def, &binst)?;
    let (fibre_t, body_t) = unfold.concl().as_eq()?;
    let app_t = Term::apply(app, vec![f.clone(), x.clone()]);
    let w = env.fresh_var();
    let leib = Thm::eq_leibniz(fibre_t, body_t.clone(), w, Formula::mem(app_t.clone(), Term::var(w)));
    let out = u_mp(&u_a1i(&Thm::mp(&leib, &unfold)?, h), &in_fibre, h)?;
    // The statement the caller relies on; a release build must not skip it.
    let want = Formula::mem(app_t, body_t);
    (u_concl(&out, h)? == want).then_some(out)
}

/// The function symbols the interpretation uses that carry *no* axioms.
///
/// All are introduced by signature extension; that is sound but limiting, and
/// it is why the rules over them (`zeta`, …) stay in the equational fragment.
/// `sort`, `lam`, `app` and the dependent product are *not* here: those are real
/// definitional extensions, held in [`Prelude`], [`Shared::lam_infos`] and
/// [`Shared::pi_infos`].
#[derive(Clone, Copy)]
struct Syms {
    /// Sorts whose level is not a literal successor tower.
    sort: FnSym,
    /// The fallback for a `Π` whose fibre decomposition broke down — which is
    /// unreachable in principle, and a reported gap rather than a wrong answer
    /// if it ever is not. Every other `Π` is an `fs` or a `dprod`.
    pi: FnSym,
    let_: FnSym,
    proj: FnSym,
    /// Lean's de Bruijn indices. A Lean expression is already de Bruijn and
    /// hash-consed, so alpha-equivalent Lean terms are pointer-equal and map to
    /// syntactically equal kernel terms; a per-index symbol therefore suffices
    /// and no binding structure need be reproduced on the kernel side.
    bvar: FnSym,
    /// Universe levels.
    lzero: FnSym,
    lsucc: FnSym,
    lmax: FnSym,
    limax: FnSym,
    /// Index encodings for `bvar`, `proj` and level/name parameters.
    idx: FnSym,
}

/// Everything known about one lambda *skeleton*. Shared by every lambda whose
/// body has that shape.
struct LamInfo {
    /// The head symbol of the interpretation, `lam_C(h⃗, A)`.
    lam: FnSym,
    /// The graph machinery, when it was built; `None` for the inert encoding,
    /// in which case `lam` is an opaque symbol and beta over this lambda
    /// reports a gap. Every skeleton gets a graph now — there is no hole-count
    /// cut-off — so the `None` case is the construction refusing, which it does
    /// not do on any corpus measured.
    graph: Option<Graph>,
}

/// Everything known about one dependent-`Π` *fibre skeleton*. Shared by every
/// `Π` whose body has that shape.
struct PiInfo {
    /// The head symbol of the interpretation, `dprod_C(h⃗, A)`.
    dprod: FnSym,
    /// The dependent-product machinery, when it was built; `None` for the inert
    /// encoding, in which case `dprod` is an opaque symbol and the `Π` bridge
    /// over it reports a gap.
    fibre: Option<Fibre>,
}

/// Everything known about one `Prop`-valued `∀` *body skeleton*. Shared by
/// every `∀` whose body has that shape.
///
/// Carneiro's §6.2 gives `∀` and `Π` **two** clauses, and this is the first:
///
/// ```text
/// ⟦∀x : α. β⟧ = {•} ∩ ⋂_{x ∈ ⟦α⟧} ⟦β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]   — β a Prop
/// ```
///
/// A *subset of `{•}`*, not a dependent function space. It is exactly a
/// [`derived::prop::conditional_singleton`] over the formula
/// `∀x. (x ∈ A → • ∈ skeleton)`, with the skeleton's holes and the domain as
/// the symbol's parameters — the same decomposition [`PiInfo`] uses, so a `∀`
/// and a `Π` over the same body shape share their hole numbering.
struct PropInfo {
    /// The head symbol of the interpretation, `chi_C(h⃗, A) = [∀x ∈ A. • ∈ C]`.
    chi: FnSym,
    /// `⊢ ∀h⃗ ∀A ∀z. (z ∈ chi(h⃗,A) ↔ (z ∈ 1 ∧ ∀x. (x ∈ A → • ∈ b(h⃗,x))))` — the
    /// characteristic theorem, or `None` for the inert encoding, in which case
    /// `chi` is an opaque symbol and everything over it reports a gap.
    chi_ax: Option<Thm>,
    /// The **fibre** `b(h⃗,x) := skeleton` and `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    ///
    /// The `∀` clause needs the body abstracted into a symbol for the same
    /// reason the `Π` clause does ([`Fibre`]): the pointwise premise two `∀`s
    /// are related by — `∀x. (x ∈ A → b(h⃗,x) = b'(q⃗,x))` — has to be a
    /// statement *about symbols*, or it could not be `∀`-quantified over the
    /// domain. Sharing the shape also lets [`TgBackend::pointwise_premise`]
    /// serve both clauses unchanged.
    fibre: Option<(FnSym, Thm)>,
    /// The formula `∀x. (x ∈ A → • ∈ C)` the singleton is conditional on,
    /// stated at the canonical hole and domain variables. Carried because
    /// [`derived::tower::Tower::cond_in_u0`] is a *construction taking a
    /// formula* — it cannot be `∀`-quantified — so the caller has to hand the
    /// very formula back.
    phi: Formula,
    /// The parameter variables, holes first and the domain last: the order
    /// `chi`'s arguments are supplied in.
    params: Vec<FreeVar>,
}

/// The definitional-extension half of a dependent-`Π` skeleton.
struct Fibre {
    /// The fibre function `b(h⃗, x)`.
    b: FnSym,
    /// `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    b_def: Thm,
    /// The Replacement image `img(h⃗, A) = { b(h⃗,x) : x ∈ A }`.
    img: FnSym,
    /// `⊢ ∀h⃗ ∀A ∀w. (w ∈ img(h⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(h⃗,x)))`.
    img_ax: Thm,
    /// `⊢ ∀h⃗ ∀A ∀f. (f ∈ dprod(h⃗,A) ↔ (f ∈ fs(A,⋃img(h⃗,A)) ∧ section(f)))`.
    dprod_def: Thm,
}

/// The definitional-extension half of a lambda skeleton.
struct Graph {
    /// The body function `t(h⃗, x)`.
    t: FnSym,
    /// `⊢ ∀h⃗ ∀x. t(h⃗,x) = skeleton`.
    t_def: Thm,
    /// `⊢ ∀h⃗ ∀A ∀y. (y ∈ lam(h⃗,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(h⃗,x)⟩))`.
    lam_ax: Thm,
}

// ─────────────────────────────────────────────────────────────────────────────
// There is no cut-off on the hole count.
//
// There used to be one — `MAX_HOLES = 8` — because a skeleton's graph cost
// ~130µs to derive and `good/init-prelude.ndjson` reached some 32k distinct
// skeletons, so building them all added ~13s to the run. Sharing the signature
// across the thread's backends (see [`Shared`]) collapsed those 32388 skeletons
// to 2651 — the same shapes, now recognised as the same — and the graph
// construction with them, from 2.3s to 0.66s.
//
// So the cap is gone, and with it the entire `beta: the lambda's graph … was
// not built` category: 1228 gaps on `init-prelude` and 24 over the tutorials
// before, zero now. Measured on `good/init-prelude.ndjson`, with the tutorial
// totals beside it — all with the shared signature, so the first row is *not*
// the old baseline, which was 5.4s for the same 18025 gaps:
//
// | cut-off | prelude gaps | prelude runtime | not built | tutorial gaps |
// |--------:|-------------:|----------------:|----------:|--------------:|
// | 8       | 18025        | 2.7 s           | 1228      | 586           |
// | 16      | 16830        | 3.2 s           | 493       | 567           |
// | 32      | 16301        | 4.0 s           | 205       | 542           |
// | 64      | 16199        | 5.1 s           | 108       | 538           |
// | 128     | 16061        | 6.8 s           | 26        | 538           |
// | none    | 16009        | 8.8 s           | 0         | 538           |
//
// The hole distribution says no finite value could ever have been principled.
// Over `init-prelude`'s 2651 skeletons: 1% need no hole at all, 34% need 1–4,
// 22% need 5–8, 21% need 9–16, 14% need 17–32, 6% need 33–64, and 3% need more
// than 64 — a tail that thins but does not stop, reaching past 128. Every cap
// is a bet on the corpus.
//
// What removing it costs — 8.8s against 2.7s — is *not* graph construction, and
// that is the reason it is no longer guarded. A beta step instantiates a lemma
// whose formula grows with the hole count, one quantifier at a time, so a redex
// over a `k`-hole lambda costs O(k²) inside the kernel's `open`/`close`; a perf
// profile of the uncapped run puts ~40% of its samples in `Term::new`,
// `Term::open` and the allocator beneath them, and `beta_step` accounts for 3.8s
// of the 8.8s against 0.7s for every graph in the run. That is the derivation
// the checker exists to produce, not a mitigation for producing it slowly.
// ─────────────────────────────────────────────────────────────────────────────

/// Where one particular lambda *occurrence* sits: which skeleton it uses, and
/// with what arguments.
struct LamSite<'t> {
    /// Key into [`Shared::lam_infos`].
    key: Term,
    /// The abstracted `v`-free subterms, in traversal order.
    holes: Vec<Term>,
    /// `⟦binder_type⟧`.
    dom: Term,
    /// The body, with the binder opened at the local below. Recorded because
    /// [`TgBackend::has_type_lam`] has to type the body *under* the binder, and
    /// `interp` is memoised — so the opening cannot be repeated later.
    body: ExprPtr<'t>,
    /// The kernel free variable that local interprets to: the binder's own
    /// variable, and the one [`TgBackend::guard_and_generalise_at`] abstracts.
    var: FreeVar,
}

/// Where one particular **proof `λ`** occurrence sits — §6.2's `Prop` clause
/// for `λ`, whose interpretation is `•`.
///
/// There is no skeleton, no graph and no head symbol: `•` is a closed term with
/// no arguments, so nothing about the lambda survives in its interpretation.
/// What is recorded is what the *typing* rule needs — the binder's domain, the
/// opened body and the binder's own kernel variable — which is exactly
/// [`LamSite`] minus the graph machinery.
struct PropLamSite<'t> {
    /// `⟦binder_type⟧`.
    dom: Term,
    /// The body, with the binder opened at a fresh local. `interp` is memoised,
    /// so the opening cannot be repeated later.
    body: ExprPtr<'t>,
    /// The kernel free variable that local interprets to — the one
    /// [`TgBackend::guard_and_generalise_at`] abstracts.
    var: FreeVar,
}

/// Where one particular dependent-`Π` *occurrence* sits.
struct PiSite {
    /// Key into [`Shared::pi_infos`].
    key: Term,
    /// The abstracted `v`-free subterms, in traversal order.
    holes: Vec<Term>,
    /// `⟦binder_type⟧`.
    dom: Term,
}

/// Which clause of Carneiro's §6.2 a `Π` falls under, as far as the backend
/// can tell without calling `infer`.
///
/// ```text
/// ⟦∀x : α. β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]   — β a Prop      Clause::Prop
/// ⟦Π x : α. β⟧ = ∏_{x ∈ ⟦α⟧} ⟦β⟧      — β a Type      Clause::Type
/// ```
///
/// The third variant is the point. `Π A B : Sort (imax u v)` with `v` a
/// universe *parameter* does not simplify — it is `0` when the parameter is
/// instantiated at `0` and `max(u,v)` otherwise — so at a level-polymorphic
/// declaration's own parameters the `Π` is **neither**: the two clauses name
/// two different sets and nothing decides between them. Taking either branch is
/// taking the wrong one on some instantiation, so [`TgBackend::interp_pi`]
/// takes neither and the `Π` gets an axiom-free symbol over which every rule
/// reports [`crate::certify::TyGap::PiUndet`].
///
/// [`Clause::Undet`] also absorbs "this approximation could not follow the
/// term", which is a different kind of not-knowing; [`Undet`] counts the two
/// apart so the first — the one no per-declaration interpretation can ever fix
/// — is visible on its own.
///
/// **And it is fixed, by not interpreting per declaration.** The
/// level-instantiation pre-pass ([`crate::instantiations`]) schedules each
/// declaration at ground universe levels, and at a ground level the `imax`
/// simplifies and one of the first two variants applies. `Undet` for a
/// parameter survives only where no σ is in force — inductive blocks, and a
/// recursor's own eliminator universe — and `TyGap::PiUndet` drops from 2366 to
/// 12 typing sites on `init-prelude`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Clause {
    Prop,
    Type,
    Undet,
}

/// Where one particular `Prop`-valued `∀` *occurrence* sits. The [`PiSite`] of
/// the other clause.
struct PropSite {
    /// Key into [`Shared::prop_infos`].
    key: Term,
    /// The abstracted `v`-free subterms, in traversal order.
    holes: Vec<Term>,
    /// `⟦binder_type⟧`.
    dom: Term,
}

// ─────────────────────────────────────────────────────────────────────────────
// The shared signature.
//
// A `TgBackend` is built per declaration, but the *signature* it builds terms
// in has no reason to be per declaration. A lambda skeleton is a property of
// the body's shape, and the same shapes recur in declaration after
// declaration — but when every backend has its own `Env`, the symbols standing
// for `app`, `proj`, the bound-variable slot and the enclosing lambdas are
// different symbols each time, so two occurrences of one shape produce two
// *different* skeleton terms and the graph is derived twice. Measured on
// `good/init-prelude.ndjson`: 32388 distinct skeleton terms for 1566 distinct
// shapes, a factor of 20 of pure repetition.
//
// Sharing one `Env` across the thread's backends makes those terms literally
// equal, so a shape's graph is derived once for the whole run: 32388 skeletons
// become 2651, and the graph construction drops from 2.3s to 0.66s. Coverage is
// unchanged to the gap — the derivations are the same derivations, and nothing
// about what one declaration can prove depends on another.
//
// Only the *signature* and what is keyed on it moves. `parts`, `consts`,
// `exprs`, `locals` and the rest stay per declaration: they are keyed by Lean
// nodes whose identity is per declaration (`locals` by the level-and-type key
// [`LocalKey`], kept per declaration to match the checker's own `TcCache`
// lifetime), and they are not what makes
// skeletons differ — everything in a body that does not mention the binder is
// abstracted into a hole, so a skeleton contains only `app`/`proj`/`Π`
// structure, the canonical variables, and the graph symbols of nested lambdas.
//
// Sharing is sound for the same reason the [`Prelude`] replay is: an `Env` is
// only a pair of counters, so one shared `Env` issues *fewer* colliding names
// than several independent ones, never more.
//
// It does mean those counters now run for the whole check rather than being
// reset per declaration. `init-prelude` ends at 38692 symbols and 616356
// variables for 2059 declarations — about 19 symbols and 300 variables each —
// against a `u32` each. The kernel's counters are `checked_add`, so exhausting
// one is a panic rather than an aliased variable, and at 300 per declaration
// that is ~1.4 × 10⁷ declarations away: two orders of magnitude past mathlib.
// The remedy, if it is ever needed, is to drop `SHARED` and start a fresh one:
// nothing outside it depends on it persisting, and the only cost of recycling
// is re-deriving the graphs.
//
// ── How this grows ───────────────────────────────────────────────────────────
//
// Measured on prefixes of `good/init-prelude.ndjson`, cut at declaration
// boundaries (every prefix still checks clean). `live` is the heap after
// `malloc_trim`, i.e. what the caches actually hold, as against `peak`, which
// includes each declaration's transient work:
//
// | decls | time  | peak RSS | live heap | lam_infos | pi_infos | lam_betas | lam_exts | vars   |
// |------:|------:|---------:|----------:|----------:|---------:|----------:|---------:|-------:|
// | 142   | 0.19s | 10 MB    | 10 MB     | 177       | 210      | 96        | 71       | 27739  |
// | 523   | 1.74s | 43 MB    | 39 MB     | 1113      | 692      | 443       | 184      | 185404 |
// | 957   | 3.41s | 77 MB    | 56 MB     | 1658      | 1157     | 729       | 211      | 336336 |
// | 1067  | 7.56s | 133 MB   | 61 MB     | 1727      | 1237     | 795       | 216      | 400462 |
// | 1525  | 8.66s | 133 MB   | 79 MB     | 2392      | 1545     | 1062      | 217      | 524741 |
// | 2059  | 9.45s | 134 MB   | 91 MB     | 2671      | 1829     | 1155      | 217      | 616356 |
//
// **The live heap is linear in the number of distinct skeletons, not in
// declarations.** Regressing `live` on `lam_infos` over those points gives
// ~33 KB per skeleton with a ~4 MB intercept, and it fits every row. Skeletons
// in turn grow *sub*-linearly in declarations — 2.4 per declaration at 362,
// 1.3 at 2059, with a marginal rate of 0.9 — because sharing keeps finding the
// same shapes. `lam_exts` saturates outright, at 217 from declaration 1348 on:
// the set of skeleton *pairs* ever compared converges. So nothing here is
// superlinear, and the caches are not the thing to watch first.
//
// **Peak RSS is not a function of the declaration count at all.** It is set by
// the single most expensive declaration: `Lean.ParserDescr.noConfusion`, at
// index 959, costs 4.0 s of the 9.4 s run (42%) and takes the peak from 77 MB
// to 133 MB by itself. The cost distribution is that heavy-tailed throughout —
// the top 10 declarations are 58% of the run, the top 100 are 79%, and the
// remaining 1959 are 21%. Any per-declaration average over this corpus is a
// statement about one `noConfusion`.
//
// **What that says about evicting: do not.** An earlier version of this note
// recommended that eviction, "when it is written", be a high-water-mark LRU over
// `lam_infos`. **That recommendation is withdrawn, and it should not be
// written.** It is recorded here rather than deleted so that a future reader who
// remembers it knows it was reversed on purpose.
//
// The reversal is a project decision, not a measurement. This crate
// *instruments* an existing checker; it does not restructure it. Eviction is a
// change to how nanoda works — it makes what the checker can hand back depend on
// how much memory it has used, which is exactly the property a
// certificate-carrying checker must not acquire — and paying memory to keep a
// certificate beside every memoised result is the intended trade, not a cost to
// be engineered away. Measuring the memory is worth doing; it is information,
// and never a reason to start evicting.
//
// The numbers above stand as measurement. At this scale the caches are 91 MB of
// a 134 MB peak that one declaration would demand anyway, so eviction could not
// lower the peak even if it were wanted. Carrying certificates in the reduct
// memo and on the equality cache's edges (`checker/src/reduct.rs`,
// `checker/src/union_find.rs`) added 0.3% to peak RSS on `init-prelude` —
// 168.1–169.0 MB before, 169.0–169.1 MB after — which is the scale of the thing
// eviction was being proposed against.
// ─────────────────────────────────────────────────────────────────────────────

// ─────────────────────────────────────────────────────────────────────────────
// Inductive types.
//
// The first, smallest rung of `INDUCTIVES.md`'s ladder: an inductive whose
// constructors take **no arguments at all** is a W-type with empty fibres, and
// its constructors are the terms `⟨tag, ∅⟩`. `Bool` is exactly that. See
// [`derived::enums`] for the construction; what lives here is the recognition
// (which Lean declarations are of that shape) and the plumbing.
//
// Everything below is *derivation*, not axiom: `Bool.false ∈ Bool` is a real
// theorem about a real set, and the two elements are provably distinct, so the
// interpretation is neither empty nor collapsed.
//
// Built lazily and once per thread: a development with no enumeration in it
// pays nothing, and one with fifty pays once.
// ─────────────────────────────────────────────────────────────────────────────

/// A **conditional** membership rule for an applied constructor.
///
/// `Bool.true` and `N.zero` are *terms*: their typing is one unconditional
/// theorem, and [`TgBackend::ind_mems`] holds it keyed by the pair of terms. A
/// constructor of a **parameterised** inductive is not — `List.nil` is applied
/// to `α` before it is a list at all, and `List.cons` to `α`, a head and a tail
/// — so its typing is a rule with one premise per argument:
///
/// ```text
/// ⊢ ∀x₁…xₙ. ((⟦x₁⟧ ∈ D₁ ∧ (… ∧ ⟦xₙ⟧ ∈ Dₙ)) → app(…app(⟦c⟧,x₁)…,xₙ) ∈ T)
/// ```
///
/// where each `Dᵢ` may mention the earlier `xⱼ`. [`TgBackend::has_type_ctor_app`]
/// instantiates it at the interpreted arguments and discharges each premise by
/// recursion — which is how `α ∈ ⟦Type u⟧` gets found among the binder's own
/// assumptions rather than being invented.
///
/// Nothing here is trusted: the rule is a real `Thm`, the premises are real
/// derivations, and `has_type_h`'s guard still checks the conclusion is the
/// membership being claimed.
#[derive(Clone)]
struct CtorRule {
    /// The rule itself, universally quantified over [`Self::vars`].
    thm: Thm,
    /// The variables it is quantified over, one per Lean argument, in order.
    vars: Vec<FreeVar>,
    /// The premises `⟦xᵢ⟧ ∈ Dᵢ`, at those variables and in the same order.
    prems: Vec<Formula>,
}

/// The W-type machinery, and the inductive types built from it.
struct Inductives {
    /// `enum(0) = W(0, ∅, U(0))` — the empty type.
    e0: Term,
    /// `enum(1)`, and `⊢ ⟨•,∅⟩ ∈ enum(1)`.
    e1: derived::enums::Enum1,
    /// `enum(1+1)`, its two elements, and their memberships — Lean's `Bool`.
    e2: derived::enums::Enum2,
    /// `N = W(1+1, rec₊(λ_.0, λ_.1), U(1+1))`, its two constructors and their
    /// memberships — Lean's `inductive N | zero | succ (n : N)`. The first
    /// *recursive* inductive, and the first whose fibres are not empty.
    nat: derived::wnat::Nat,
    /// `List`, `List.nil` and `List.cons` as **set functions** — Lean's
    /// `inductive List (α : Type u)`, the first **parameterised** inductive.
    ///
    /// The W-type itself is [`derived::wlist`], whose `lt` is a *unary* symbol
    /// because the type is a family; what is kept here is the layer that turns
    /// the three into sets, since an interpretation that reads `List α` as
    /// `app(⟦List⟧,⟦α⟧)` can use nothing else. `cons` is curried; see
    /// [`derived::wlist_fun`].
    list_fun: derived::wlist_fun::ListFun,
    /// `lt(α) = W(1+α, fam(α), U(1+α))` and its two constructors, as *terms* —
    /// what [`derived::wlist_rec`]'s ι rules are stated at. `list_fun` above is
    /// the layer that turns those terms into set functions; the recursor speaks
    /// of the terms.
    list: derived::wlist::WList,
    /// `rec₊`, the case function the fibre family is built from. Held because
    /// [`derived::wlist::WList::fam_of`] needs it to *name* the family, and the
    /// recursor's arguments have to be the very terms `list` was built over.
    cases: derived::sums::Cases,
    /// The W-type and its bound, kept so that the **recursor** development can
    /// be built lazily on top of them. It is not built here: `Recursor::new`
    /// plus totality is the largest derivation in `derived`, and most files
    /// that declare an inductive never reduce one.
    wt: derived::wtype::Wtype,
    bnd: derived::bound::Bound,
    /// The one-point graph `{⟨a,b⟩}`, over the *same* [`derived::wtype::Wtype`]
    /// as everything else. `N` was built over it, and [`derived::wnat_rec`]
    /// insists on being handed that very one — a second copy would mint new
    /// symbols and none of `N`'s theorems would compose with the recursor's.
    pf: derived::point_fun::PointFun,
    /// `⊢ ∀A. closed(A, ∅, U(A))` — the W-type bound hypothesis for an
    /// enumeration, the one thing [`derived::wbool_rec`] needs that
    /// [`derived::enums`] already derived.
    enum_closed: Thm,
}

/// The W-recursor itself, independently of which inductive is being eliminated.
///
/// `Recursor::new`, the one-point extension, structural induction for totality,
/// and totality's two consequences — the unguarded ι rule and `wrec ∈ fs(W,T)`.
/// This is the expensive half of `derived`, and **none of it mentions the tag
/// set**: `Bool.rec` and `N.rec` differ only in the packed step underneath, so
/// they share this prefix rather than build it twice. Sharing is not merely a
/// saving: a second `Recursor::new` would mint fresh symbols, and no theorem
/// stated over one copy composes with a theorem stated over the other.
struct RecCore {
    /// `wrec(A,B,u,T,e)`, with its defining property.
    r: derived::wrec_total::Recursor,
    /// `⊢ ∀A∀B∀u∀T∀e. ((closed ∧ step_typed) → ∀a∀f. (… → app(wrec,⟨a,f⟩) = …))`.
    iota: Thm,
    /// `⊢ ∀A∀B∀u∀T∀e. ((closed ∧ step_typed) → wrec ∈ fs(W,T))`.
    funspace: Thm,
}

/// The **recursor** for a two-constructor enumeration, as a set.
///
/// `⟦Bool.rec⟧` is a *curried nest* of lambda graphs (see [`RecNest`]); this is
/// what sits at the bottom of it — [`derived::wbool_rec`]'s W-recursor together
/// with the two computation rules that make iota fire.
struct BoolRecursor {
    /// `⊢ ∀fls ∀tru. app(brec(fls,tru), ⟨inj •, ∅⟩) = minor`, indexed by
    /// constructor.
    iota: [Thm; 2],
    /// The `wrec` symbol, and the three arguments that do not vary.
    rec_sym: FnSym,
    tags: Term,
    zero: Term,
    universe: Term,
    /// Unordered pairing, for the target `{fls,tru}` and the step.
    up: FnSym,
    /// The step's two arguments `⟨inj •, ⟨∅,∅⟩⟩`.
    keys: [Term; 2],
    /// The two constructor terms `⟨inj •, ∅⟩`, as [`derived::enums`] builds
    /// them — what the iota equations are stated at.
    ctors: [Term; 2],
}

impl BoolRecursor {
    /// `brec(fls,tru) = wrec(1+1, ∅, U(1+1), {fls,tru}, e(fls,tru))`.
    fn brec(&self, ap: &Apply, fls: &Term, tru: &Term) -> Term {
        let target = Term::apply(self.up, vec![fls.clone(), tru.clone()]);
        let step = Term::apply(
            self.up,
            vec![
                ap.sets.pair(self.keys[0].clone(), fls.clone()),
                ap.sets.pair(self.keys[1].clone(), tru.clone()),
            ],
        );
        Term::apply(
            self.rec_sym,
            vec![self.tags.clone(), self.zero.clone(), self.universe.clone(), target, step],
        )
    }
}

/// The **recursor** for the unary recursive shape — Lean's `N.rec`.
///
/// The `Bool` analogue of this ([`BoolRecursor`]) is a graph on two points,
/// because with empty fibres the W-recursor's step sees exactly two arguments.
/// `N`'s `succ` fibre is `1`, so the step has to compute
/// `app(app(s, app(f,•)), app(r,•))` — the recursive call is *live* — and the
/// packed step is [`derived::wnat_rec`]'s two-layer Replacement instead. What
/// is kept here is the whole development plus the pieces `nrec` is built from,
/// so that the term the nest's bottom names and the term the ι rules are stated
/// at are the same term.
struct NatRecursor {
    /// The packed step and both ι rules; see [`derived::wnat_rec::NatRec`].
    nr: derived::wnat_rec::NatRec,
    /// The shared W-recursor. Held, not rebuilt: `nr`'s theorems are stated
    /// over *this* `Recursor`.
    core: Rc<RecCore>,
    /// The W-type, its bound and `N` itself, for the same reason.
    inds: Rc<Inductives>,
}

impl NatRecursor {
    /// `nrec(z,s,T) = wrec(1+1, B, U(1+1), T, e(z,s,T))`.
    fn nrec(&self, z: &Term, s: &Term, t: &Term) -> Term {
        self.nr.of(&self.inds.wt, &self.inds.bnd, &self.inds.nat, &self.core.r, z, s, t)
    }
}

/// The **recursor** for the parameterised recursive shape — Lean's `List.rec`.
///
/// [`NatRecursor`] again with two differences, both of which are what
/// [`derived::wlist_rec`] exists to absorb: the tag set is `1 + α` for a free
/// parameter `α`, so every term here takes it as an argument; and `List.cons`
/// carries a **field** as well as a recursive argument, so the packed step's
/// value has three components rather than two.
struct ListRecursor {
    /// The packed step and both ι rules; see [`derived::wlist_rec::ListRec`].
    lr: derived::wlist_rec::ListRec,
    /// The shared W-recursor. Held, not rebuilt: `lr`'s theorems are stated over
    /// *this* `Recursor`.
    core: Rc<RecCore>,
    /// The W-type, its bound, `lt` and `rec₊`, for the same reason.
    inds: Rc<Inductives>,
}

impl ListRecursor {
    /// `lrec(α,z,s,T) = wrec(1+α, fam(α), U(1+α), T, e(α,z,s,T))`.
    fn lrec(&self, alpha: &Term, z: &Term, s: &Term, t: &Term) -> Term {
        self.lr.of(
            &self.inds.wt,
            &self.inds.bnd,
            &self.inds.list,
            &self.inds.cases,
            &self.core.r,
            alpha,
            z,
            s,
            t,
        )
    }
}

impl Inductives {
    /// The whole development, over the prelude's own pairing, power set,
    /// product, function space and universe operator — so that `⟦Bool⟧` is a
    /// set built from the same operators every other rule speaks of.
    /// Over a **caller-supplied** `Wtype` and `Bound` — the [`EnvCore`]'s, so
    /// that the enumerations, `N` and `List` here are welded to the same `W`
    /// as the general path's [`derived::inductive::Machine`], on whichever
    /// engine built it first. This used to mint its own `Sums` (over the
    /// prelude's operators) and its own `Wtype`/`Bound`; the core builds the
    /// pair over the prelude *tower's* own `Sums` instead, which is the
    /// object `mini` was already using — one `sum`, one `W`, for both.
    fn build(
        env: &mut Env,
        _pre: &Prelude,
        wt: derived::wtype::Wtype,
        bnd: derived::bound::Bound,
    ) -> Option<Inductives> {
        let empty_u = derived::enums::empty_in_least_universe(env, &wt, &bnd)?;
        let mem = derived::enums::enum_mem(env, &wt, &bnd, &empty_u)?;
        let inj = derived::enums::enum_inj(env, &wt)?;
        let e0 = derived::enums::enum0(&wt, &bnd);
        let e1 = derived::enums::enum1(&wt, &bnd, &mem)?;
        let e2 = derived::enums::enum2(&wt, &bnd, &mem, &inj)?;
        // `N` needs two things the enumerations do not: the case function
        // `rec₊`, to compute the fibre family, and the one-point graph
        // `{⟨•,n⟩}`, which is `succ`'s recursive argument. Both are built over
        // the *same* `Sums` as the W-type, so every theorem composes.
        let cases = derived::sums::Cases::new(env, &wt.sums)?;
        let pf = derived::point_fun::PointFun::over(env, &wt.sums, &wt.app_pair)?;
        let nat = derived::wnat::Nat::over(env, &wt, &bnd, &cases, &pf, &empty_u)?;
        // `List` reuses all of that and adds one thing: the fibre family's
        // right branch is a constant function on an *arbitrary* `α`, which is a
        // lambda graph rather than a one-point graph.
        let list = derived::wlist::WList::over(env, &wt, &bnd, &cases, &pf, &empty_u)?;
        let list_fun = derived::wlist_fun::ListFun::over(env, &wt, &list)?;
        let enum_closed = derived::enums::enum_closed(env, &wt, &bnd, &empty_u)?;
        Some(Inductives { e0, e1, e2, nat, list_fun, list, cases, wt, bnd, pf, enum_closed })
    }

    /// The type term for an enumeration with `n` constructors.
    fn ty(&self, n: usize) -> Option<Term> {
        match n {
            0 => Some(self.e0.clone()),
            1 => Some(self.e1.ty.clone()),
            2 => Some(self.e2.ty.clone()),
            _ => None,
        }
    }

    /// The `i`th constructor of an `n`-constructor enumeration, with the
    /// theorem that it lies in the type.
    fn ctor(&self, n: usize, i: usize) -> Option<(Term, Thm)> {
        match (n, i) {
            (1, 0) => Some((self.e1.only_t.clone(), self.e1.only.clone())),
            (2, 0) => Some((self.e2.fst_t.clone(), self.e2.fst.clone())),
            (2, 1) => Some((self.e2.snd_t.clone(), self.e2.snd.clone())),
            _ => None,
        }
    }
}

/// A literal's **value** — the key its interpretation is shared under.
///
/// The *value*, not the arena pointer: a literal reaches the backend both from
/// the export file's own arena and from a `TcCtx` one (the nat extension
/// computes literals while reducing), and the two must denote the same term or
/// the interpretation is not a function of the expression.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Lit {
    Nat(num_bigint::BigUint),
    Str(String),
}

// ─────────────────────────────────────────────────────────────────────────────
// The shared semantic core (ENV-UNIFY.md §3.3, tracks B1/B2).
//
// Everything that must be **one object per run** for two engines' certificates
// to compose, behind one cheaply-cloneable handle: the kernel `Env` (one
// brand, one counter pair — `Env` is deliberately not `Clone`, because two
// copies would re-issue the same ids for different purposes), the canonical
// skeleton variables (`x_canon` and the hole series, which appear inside
// every skeleton key and so decide whether two engines' keys are equal
// *terms*), and the W-type apparatus (`Wtype`, `Bound`, `Machine` — every
// `Machine::over` mints a fresh `rec₊`, `⋂` and `MachineId`, so a second
// build is a second family of symbols no theorem relates to the first's).
//
// `mini`'s `Interp::over` and this file's [`install_shared_core`] both take
// one of these; `Interp::new` and the [`shared`] fallback mint a private one,
// which reproduces the old two-`Env` behaviour exactly. The `Rc`s make the
// handle `!Send`, and that is the concurrency decision, not an accident: the
// evidence axis of a mixed run is single-threaded, and a thread that wants
// its own apparatus gets its own core (today's per-thread `SHARED`
// behaviour, unchanged).
// ─────────────────────────────────────────────────────────────────────────────

/// The one-per-run semantic objects both engines must share for their
/// certificates to compose, as a cloneable same-thread handle. See the header
/// above for what belongs here and why.
#[derive(Clone)]
pub struct EnvCore {
    /// The kernel signature and variable source — the brand.
    env: Rc<std::cell::RefCell<Env>>,
    /// The canonical binder slot every skeleton abstracts over.
    pub x_canon: FreeVar,
    /// The canonical hole-variable series, grown on demand by either engine.
    /// Shared because a skeleton key contains `hole_var(i)` literally: two
    /// series would make the same shape two different key terms.
    hole_vars: Rc<std::cell::RefCell<Vec<FreeVar>>>,
    /// The W-type and its bound, over the **prelude tower's own `Sums`**,
    /// built once on first demand. The outer `Option` is "attempted", the
    /// inner "succeeded" — a failed build is not retried.
    wtb: Rc<std::cell::RefCell<Option<Option<(derived::wtype::Wtype, derived::bound::Bound)>>>>,
    /// The one [`derived::inductive::Machine`], over that same `Wtype` and
    /// `Bound`, built once on first demand. Same `Option` convention.
    machine: Rc<
        std::cell::RefCell<
            Option<Option<Rc<std::cell::RefCell<derived::inductive::Machine>>>>,
        >,
    >,
}

impl EnvCore {
    /// A fresh core: one `Env::new()`, fast-forwarded past this thread's
    /// prelude, with the canonical binder slot minted. This is exactly the
    /// preamble `Interp::new` and the old `shared()` each ran privately; a
    /// caller that hands the *same* core to both engines is what makes their
    /// symbols one signature.
    pub fn fresh() -> EnvCore {
        let pre = prelude();
        let mut env = Env::new();
        fast_forward(&mut env, &pre);
        let x_canon = env.fresh_var();
        EnvCore {
            env: Rc::new(std::cell::RefCell::new(env)),
            x_canon,
            hole_vars: Rc::new(std::cell::RefCell::new(Vec::new())),
            wtb: Rc::new(std::cell::RefCell::new(None)),
            machine: Rc::new(std::cell::RefCell::new(None)),
        }
    }

    /// The kernel `Env`, for the duration of one statement. Every use must be
    /// short-lived: holding this across a call that itself reaches the core
    /// panics on the re-entrant borrow.
    pub fn env_mut(&self) -> std::cell::RefMut<'_, Env> { self.env.borrow_mut() }

    /// Mint a fresh variable from the shared `Env`.
    pub fn fresh_var(&self) -> FreeVar { self.env.borrow_mut().fresh_var() }

    /// The `i`-th canonical hole variable, minting on demand. The series is
    /// one series across every client of this core, whichever engine asks
    /// first.
    pub fn hole_var(&self, i: usize) -> FreeVar {
        let mut hs = self.hole_vars.borrow_mut();
        while hs.len() <= i {
            let v = self.env.borrow_mut().fresh_var();
            hs.push(v);
        }
        hs[i]
    }

    /// The `i`-th hole variable **if it has been minted**, without minting.
    /// For the read-only "is this skeleton a bare hole" checks.
    pub fn hole(&self, i: usize) -> Option<FreeVar> { self.hole_vars.borrow().get(i).copied() }

    /// Whether two handles are the same core — one `Env`, one brand.
    pub fn same_core(&self, other: &EnvCore) -> bool { Rc::ptr_eq(&self.env, &other.env) }

    /// The shared `Wtype` and `Bound`, over the prelude tower's own `Sums`,
    /// built on first demand. Clones share the underlying symbols, so a clone
    /// *is* the shared apparatus.
    pub fn wtype_bound(
        &self,
        pre: &Prelude,
    ) -> Option<(derived::wtype::Wtype, derived::bound::Bound)> {
        if let Some(r) = self.wtb.borrow().as_ref() {
            return r.clone()
        }
        let built = {
            let mut env = self.env.borrow_mut();
            derived::wtype::Wtype::over(&mut env, pre.tower.sums.clone()).and_then(|wt| {
                let bnd =
                    derived::bound::Bound::over(&mut env, &wt, pre.u_sym, pre.lu_ax.clone())?;
                Some((wt, bnd))
            })
        };
        *self.wtb.borrow_mut() = Some(built.clone());
        built
    }

    /// The one shared [`derived::inductive::Machine`], over
    /// [`EnvCore::wtype_bound`]'s `Wtype` and `Bound`, built on first demand.
    /// Both engines' inductive translations must be welded to this one — the
    /// `MachineId` guards on `Inductive::is_over` are what enforce it.
    pub fn machine(
        &self,
        pre: &Prelude,
    ) -> Option<Rc<std::cell::RefCell<derived::inductive::Machine>>> {
        if let Some(r) = self.machine.borrow().as_ref() {
            return r.clone()
        }
        let built = self.wtype_bound(pre).and_then(|(wt, bnd)| {
            let mut env = self.env.borrow_mut();
            derived::inductive::Machine::over(&mut env, wt, bnd)
        });
        let m = built.map(|m| Rc::new(std::cell::RefCell::new(m)));
        *self.machine.borrow_mut() = Some(m.clone());
        m
    }
}

/// The per-thread signature, and the derivations keyed on it.
///
/// # Every `Thm` here is a [`Sealed`], and that is a rule rather than a habit
///
/// These stores hand a theorem back in a *later declaration* than the one that
/// derived it, under a key made of interpreted terms and names. A key like that
/// does not mention `Γ`, so a hypothesis-carrying entry would be re-asserted
/// silently at the point of use, and the kernel could not object — the theorem
/// handed back is perfectly good, and the error would be entirely in what the
/// checker concluded from it. [`crate::sealed::Sealed`]'s only constructor
/// checks `hyps().is_empty()`, so a new store cannot be added without its author
/// saying what happens to a hypothetical theorem, and the cheap answer
/// ([`Sealed::seal`], which declines it) is the one that fails closed.
///
/// Nothing in this crate builds a hypothetical `Thm` today, so no seal here ever
/// fails and none of this moves a measured number. It replaces an argument about
/// today's callers with one about the code.
struct Shared {
    /// The kernel signature, variable source and canonical skeleton
    /// variables, shared by every backend on this thread so that equal
    /// skeletons are equal *terms* — and, when a caller installed the core
    /// ([`install_shared_core`]), shared with `mini`'s `Interp` too, so that
    /// the *two engines'* skeletons are equal terms. The canonical variables
    /// are reused across skeletons: they are abstracted away by
    /// `define_abbrev` immediately and never escape.
    core: EnvCore,
    /// The axiom-free interpretation symbols; copied into each backend.
    syms: Syms,
    /// Head symbol (and, when built, graph machinery) per distinct skeleton.
    lam_infos: HashMap<Term, Rc<LamInfo>>,
    /// The same entries, found by the `lam` symbol instead of the skeleton.
    /// A typing obligation's *target* arrives as a term with no Lean node
    /// attached, so a target of the shape `app(lam_C(h⃗,A), x)` needs the graph
    /// machinery behind its head symbol before it can be beta-reduced; this is
    /// that lookup. The exact analogue of [`Shared::pi_by_dprod`].
    lam_by_lam: HashMap<FnSym, (Term, Rc<LamInfo>)>,
    /// Beta theorems, derived lazily: most lambdas are never a redex head.
    lam_betas: HashMap<Term, Option<Sealed>>,
    /// Graph-extensionality theorems, keyed by the *pair* of skeletons being
    /// related. Derived lazily and shared: `lam_ext_n` is a full Extensionality
    /// derivation, and a development compares the same two body shapes over and
    /// over (once per occurrence, and again per `def_eq` call).
    lam_exts: HashMap<(Term, Term), Option<Sealed>>,
    /// Dependent-product extensionality theorems, keyed the same way.
    pi_exts: HashMap<(Term, Term), Option<Sealed>>,
    /// Head symbol (and, when built, fibre machinery) per distinct dependent-`Π`
    /// body skeleton.
    pi_infos: HashMap<Term, Rc<PiInfo>>,
    /// The same entries, found by the `dprod` symbol instead of the skeleton.
    /// A typing obligation arrives as a *term* `dprod_C(q⃗,A)` with no Lean `Π`
    /// attached, so the lambda rule needs the fibre machinery behind its head
    /// symbol; this is that lookup.
    pi_by_dprod: HashMap<FnSym, (Term, Rc<PiInfo>)>,
    /// `⊢ ∀B ∀A. dprod(B,A) = fs(A,B)` at the **constant-fibre skeleton** — the
    /// interpreted arrow spelled as the library's function space. `⟦Π⟧` is a
    /// `dprod` at every codomain, so nothing this backend interprets is ever an
    /// `fs`; `derived` nevertheless states real obligations over `fs` —
    /// `succ_in_funspace`, the ι rules' minor-premise chains — and this theorem
    /// is the one place the two vocabularies meet. Derived on first use from
    /// [`dprod_const_fibre_n`], whose constant-fibre hypothesis is the fibre's
    /// own defining equation weakened and generalised. The outer `Option` is
    /// "has it been attempted", the inner one "did it succeed".
    dprod_fs: Option<Option<Sealed>>,
    /// Head symbol (and characteristic theorem) per distinct **`Prop`-valued
    /// `∀`** body skeleton — the other clause of §6.2. The exact analogue of
    /// [`Shared::pi_infos`].
    prop_infos: HashMap<Term, Rc<PropInfo>>,
    /// The same entries, found by the `chi` symbol instead of the skeleton.
    /// The analogue of [`Shared::pi_by_dprod`]: a term arrives with no Lean
    /// node attached and the rules have to recognise it as a `∀`.
    prop_by_chi: HashMap<FnSym, (Term, Rc<PropInfo>)>,
    /// One axiom-free symbol per body skeleton of a `Π` that falls under
    /// **neither** clause of §6.2. Kept apart from [`Shared::pi_infos`] and
    /// [`Shared::prop_infos`] on purpose; see [`TgBackend::interp_pi_undet`].
    undet_syms: HashMap<Term, FnSym>,
    /// `∀`-extensionality theorems, keyed by the *pair* of body skeletons being
    /// related, exactly as [`Shared::pi_exts`] is.
    prop_exts: HashMap<(Term, Term), Option<Thm>>,
    /// `⊢ ∀h⃗ ∀A. chi(h⃗,A) ∈ U₀` per skeleton, derived **lazily**: it is
    /// [`derived::tower::Tower::cond_in_u0`], which runs excluded middle over
    /// `φ` and two `cond_true`/`cond_false` derivations, and only a skeleton
    /// whose `ty_pi_prop` obligation is actually asked needs it.
    prop_u0s: HashMap<Term, Option<Sealed>>,
    /// `⊢ ∀h⃗ ∀A. (φ(h⃗,A) → • ∈ chi(h⃗,A))` per `∀` skeleton — the **typing rule
    /// of a proof `λ`**, [`derived::prop::cond_intro`] generalised over the
    /// skeleton's parameters. Derived lazily for [`Shared::prop_u0s`]'s reason:
    /// only a skeleton some proof lambda is actually checked against needs it.
    prop_intros: HashMap<Term, Option<Sealed>>,
    /// `lam_in_funspace_n` per lambda skeleton, derived lazily and shared.
    lam_fss: HashMap<Term, Option<Sealed>>,
    /// `lam_in_dprod_n`, keyed by the *pair* of skeletons it relates — the
    /// lambda's and the dependent product's, which are independent.
    lam_dprods: HashMap<(Term, Term), Option<Sealed>>,
    /// The W-type machinery, derived on first use — most developments never
    /// declare an enumeration, and the derivation is not free. The outer
    /// `Option` is "has it been attempted", the inner one "did it succeed".
    inds: Option<Option<Rc<Inductives>>>,
    /// `⊢ T ∈ U(ω)` for each interpreted inductive **type** `T` that provably
    /// lies in `⟦Type 0⟧`, keyed by the W-type term itself: `⟦N⟧`'s
    /// `W(1+1,B,U(1+1))` from [`derived::cumul::NatMem::over`], and the three
    /// enumerations' `W(A,∅,U(A))` from [`derived::cumul::enum_in_u1`].
    ///
    /// Kept here rather than on the backend because every entry is stated at
    /// *closed* terms over the per-thread signature, so one derivation serves
    /// every declaration; the per-declaration part is only the Leibniz step onto
    /// that declaration's abbreviation, which is three kernel rules. The chain
    /// underneath — `bounded`, `tower_closed`, `Inside`, `WMem` — is the single
    /// most expensive thing in `derived` after the recursor, and a development
    /// that never asks `⟦T⟧ : Type 0` must not pay for it.
    ind_ty_u1: Option<Rc<Vec<(Term, Sealed)>>>,
    /// The W-recursor and its two consequences, derived on first use —
    /// separately from [`Shared::inds`], because it is the most expensive
    /// derivation in `derived` and only a file that actually *reduces* a
    /// recursor needs it. Shared by every inductive's recursor.
    rec_core: Option<Option<Rc<RecCore>>>,
    /// The recursor for a two-constructor enumeration, on top of that.
    bool_rec: Option<Option<Rc<BoolRecursor>>>,
    /// The recursor for the unary recursive shape, on top of the same.
    nat_rec: Option<Option<Rc<NatRecursor>>>,
    /// The recursor for the **parameterised** shape — `List.rec` — on the same
    /// [`RecCore`] again.
    list_rec: Option<Option<Rc<ListRecursor>>>,
    // **The general path's apparatus** — one [`derived::inductive::Machine`] —
    // used to be a field here, per thread, built on [`Inductives`]'s own
    // `Wtype` and `Bound`. It now lives one level down, in [`EnvCore`], over
    // the *core's* `Wtype` and `Bound` — the same objects [`Inductives`] is
    // built over — so that when the core is shared with `mini`, the two
    // engines' carriers, [`RecCore`] and the whole signature share one `W`,
    // one function space, one pairing and one universe operator. That sharing
    // is the single coordination point `RECURSOR-DESIGN.md` §7.4 warned
    // about, and it is still satisfied without touching `derived/`: the
    // `RefCell` around the `Machine` is there because `Inductive::build`
    // needs `&mut Machine` (the telescope and `Σ`-symbol caches grow) at the
    // same time as `&mut Env`, and the two live behind *different* cells so
    // neither borrow is re-entrant on the other.
    /// Translated declarations, keyed `(NamePtr::raw, interpreted levels)` —
    /// the [`Shared::const_syms`] convention. `None` memoises a **decline**, so
    /// a declaration that the walk refuses once does not re-run the walk per
    /// obligation (the `has_types`/`points` precedent).
    gen_inds: HashMap<(u32, Vec<Term>), Option<Rc<GenInd>>>,
    /// The general recursors, built lazily on first ι demand — the [`RecCore`]
    /// precedent, and for the same reason: most declarations that mention a
    /// recursor never reduce one.
    gen_recs: HashMap<(u32, Vec<Term>), Option<Rc<GenRec>>>,

    // ── Constants, canonicalised per thread ──────────────────────────────────
    //
    // A `TgBackend` is built and dropped per declaration, so anything it mints
    // for itself is a *different symbol* in the next declaration's backend. That
    // is harmless as long as no theorem outlives the backend that built it — and
    // [`Shared::declar_typings`] is exactly a theorem that does. For a stored
    // `⊢ ⟦c⟧ ∈ ⟦T⟧` to be usable where `c` is *used*, `⟦c⟧` and `⟦T⟧` have to be
    // the same terms there as here, so the symbols the interpretation rests on
    // move here, keyed by what the Lean side actually names.
    //
    // The keys are `(NamePtr::raw, levels)` and the entries are only made for
    // names living in the **export file's** own arena, whose index is stable for
    // the whole run; a name interned in a per-declaration arena gets a
    // per-backend symbol as before, and simply never matches the store.
    /// Symbols for constants with no value — axioms, constructors, recursors.
    /// Keyed by the name and its universe arity; the levels are the symbol's
    /// arguments, as before.
    opaque_syms: HashMap<(u32, u32), FnSym>,
    /// `(⟦c.{us}⟧, ⊢ ⟦c.{us}⟧ = ⟦value⟧)` for constants introduced as explicit
    /// definitions. Keyed by the name **and** the levels, exactly as
    /// [`TgBackend::ind_abbrev`] is, so the interpretation stays injective on
    /// constants: two distinct names never share a symbol however equal their
    /// values are.
    const_syms: HashMap<(u32, Vec<Term>), (Term, Sealed)>,
    /// One opaque nullary symbol per universe **parameter name**.
    ///
    /// Sharing these across declarations is what makes `⟦f.{u}⟧` at `f`'s own
    /// parameter the same term as `⟦f.{u}⟧` inside some later `g.{u}`. It is
    /// sound for the reason every other choice in the interpretation is: nothing
    /// derives that two universe parameters are *distinct*, so mapping the `u`
    /// of two declarations to one constant loses information and adds none.
    param_syms: HashMap<u32, Term>,
    /// One kernel **free variable** per universe parameter name — the
    /// ω-vocabulary's reading of a parameter (`LEVELPOLY.md` §1.1), beside the
    /// opaque symbol [`Shared::param_syms`] keeps for the *syntactic*
    /// vocabulary.
    ///
    /// A variable and not a symbol, because the declaration-boundary
    /// quantifier (§5.3 step 5) must `Thm::gen` over it: a theorem
    /// `⊢ u ∈ ω → φ(u)` at a free variable `u` generalises to `⊢ ∀u. …`,
    /// while at a declared constant it is stuck at that constant forever.
    /// Shared across declarations for the reason `param_syms` is — nothing
    /// derives two parameters distinct, and `⟦f.{u}⟧` inside a later `g.{u}`
    /// must be about the same `u`.
    param_vars: HashMap<u32, FreeVar>,
    /// One nullary symbol per de Bruijn index. See [`TgBackend::idx_term`].
    idx_syms: HashMap<u64, FnSym>,
    /// One opaque nullary symbol per **literal value**.
    ///
    /// Per backend, `42` was a fresh symbol in every declaration, so any
    /// definition or constructor field type mentioning a literal interpreted to
    /// a different term each time. That is a *primitive* failure of canonicity
    /// — unlike an inductive carrier or a recursor nest there was no store
    /// behind it at all — and it seeds the rest: `UInt8`'s field is `Fin (2^8)`,
    /// so a fresh `8` re-mints `⟦UInt8⟧`, and every constant above it follows.
    ///
    /// Sharing them is sound for the reason [`Shared::param_syms`] is: the
    /// symbols carry no axioms, so identifying two occurrences of one value
    /// loses information and adds none. Distinct values still get distinct
    /// symbols, which is what the interpretation needs to stay injective.
    lit_syms: HashMap<Lit, FnSym>,
    /// **The abbreviation symbols of interpreted inductives**, their
    /// constructors and their recursors — [`TgBackend::ind_abbrev`]'s store,
    /// per thread rather than per backend, keyed `(NamePtr::raw, levels)` like
    /// [`Shared::const_syms`] and for the same reason.
    ///
    /// It was per-backend as long as everything it fed was rebuilt per backend
    /// too, which was harmless. The **general inductive path** breaks that: a
    /// [`GenInd`] is cached per thread, and every term reachable from it — the
    /// `βⱼ` bodies above all — is stated over whatever `⟦Bool⟧`, `⟦N⟧`, … it
    /// mentioned when it was built. A per-backend symbol there would make a
    /// cached package a set of true theorems about symbols the *next*
    /// declaration's backend never produces, which is the mislabelling this
    /// project has paid for before.
    ///
    /// Entries are made only for export-file names ([`TgBackend::name_key`]),
    /// and nothing is *trusted* from here: a hit is returned only when its
    /// defining equation is about the body this backend just interpreted,
    /// exactly as [`TgBackend::const_abbrev`] guards. A mismatch mints a fresh
    /// per-backend symbol — today's behaviour — and is counted as
    /// [`Dt::IndDrift`].
    ind_syms: HashMap<(u32, Vec<Term>), (FnSym, Sealed)>,
    /// **The recursor nests**, per thread rather than per backend — keyed
    /// `(NamePtr::raw, levels)` like [`Shared::const_syms`].
    ///
    /// `⟦T.rec.{us}⟧` is the head of a curried nest of lambda graphs, and every
    /// symbol in that nest is a fresh `define_abbrev`. Built per backend, the
    /// head is therefore a *different symbol in every declaration*, and so is
    /// the interpretation of every constant whose value mentions the recursor —
    /// which on `init-prelude` is the whole `Nat` arithmetic family. Measured
    /// before this store existed: `Nat.below`, `Nat.brecOn`, `Nat.add`,
    /// `Nat.mul`, `Nat.pow` and fourteen more each acquired **about a thousand**
    /// distinct interpretations, roughly one per declaration checked, and each
    /// re-mint declined the shared symbol for every constant above it.
    ///
    /// **Every bottom is stored, including [`RecBottom::General`].** It was not
    /// always: a general nest carries a [`GenTyNest`], and while that was built
    /// per backend the ι rule's `app-spine(⟦T⟧,p⃗) = ind(p⃗)` was an equation
    /// about *this* backend's symbols, so a shared nest would have handed
    /// [`TgBackend::fire_general`] somebody else's `⟦T⟧`. [`Shared::gen_ty_nests`]
    /// made the type former per thread at `42a0dee`, and
    /// [`TgBackend::adopt_ty_nest`] hands a later backend the *same* `Rc` it
    /// stored, so [`same_bottom`] can ask `Rc::ptr_eq` of it exactly as it asks
    /// it of the three hand-written singletons. The exception lapsed; it was
    /// not weakened.
    ///
    /// Measured on `init-prelude` while the exception stood: all **85**
    /// remaining [`Dt::IndDrift`] events were general nest heads —
    /// `Lean.Name.rec` 50, `Lean.SourceInfo.rec` 22, `Option.rec` 7,
    /// `Lean.Macro.Exception.rec` 6 — and the **173** [`Dt::Drift`] events were
    /// the constants sitting on them (`Lean.Name.casesOn` 26,
    /// `Lean.SourceInfo.casesOn` 23, the two `ctorIdx`s 38, `below` 19,
    /// `brecOn` 14). Sharing the general nest takes both rows to zero.
    ///
    /// Nothing is trusted from here: see [`TgBackend::reuse_rec_nest`], which
    /// re-derives this backend's domains, replays the nest's applicative
    /// structure and checks the stored defining equation against it before the
    /// entry is used.
    rec_nests: HashMap<(u32, Vec<Term>), Rc<SharedNest>>,
    /// **The Lean-facing type former**, per thread — and with it `⟦T⟧` itself
    /// for every declaration the general path translates.
    ///
    /// [`GenTyNest`] is built entirely out of its [`GenInd`]: the variables are
    /// `gi.param_vars`, the domains `gi.param_doms`, the innermost body
    /// `gi.ind.ty_of(p⃗)`. Everything else in it is a fresh `define_abbrev` and
    /// a `lambda_n` over those, so **two backends holding the same `GenInd`
    /// would build the same nest up to the identity of symbols that carry no
    /// information**. Built per backend, they did not: `⟦T⟧` was a different
    /// symbol in every declaration, which is 15840 of the 25705 inductive
    /// re-mints measured on `init-prelude` and the seed for most of the rest —
    /// a constructor field type mentioning `⟦T⟧` interprets differently, so the
    /// `βⱼ` guard on the *next* declaration misses, so its carrier is rebuilt
    /// too.
    ///
    /// The stored `GenInd` is kept beside the nest and the guard is
    /// `Rc::ptr_eq` against it — the same test [`Shared::gen_recs`] uses, and
    /// exact rather than approximate: same `Rc`, same variables, same domains,
    /// same bottom, so the cached nest's theorems are about precisely the terms
    /// this backend would have built. A different `Rc` means [`TgBackend::gen_ind`]
    /// rebuilt the translation, and then the nest above it is stale and is
    /// rebuilt with it.
    gen_ty_nests: HashMap<(u32, Vec<Term>), (Rc<GenInd>, Rc<GenTyNest>)>,
    /// **The constructors' nests**, per thread — and with them `⟦cᵢ⟧` itself.
    ///
    /// The last of the four minting sites that had no store, and the one the
    /// other three were downstream of. A constructor's nest is built entirely
    /// out of its [`GenInd`], its [`GenTyNest`] and the walk's domains: the
    /// bottom is `gi.ind.ctor_term(mach, i, y⃗, r⃗)` at `gi.field_vars[i]`, the
    /// levels are `tn.vars ++ field_vars` over `tn.doms ++ field domains`, and
    /// everything else in it is a `define_abbrev` and a `lambda_n` over those.
    /// So **two backends holding the same translation, the same type former and
    /// the same domains build the same nest up to the identity of symbols that
    /// carry no information** — which is precisely the guard:
    /// `Rc::ptr_eq` on both, and a pointwise comparison of the variables and
    /// domains. Nothing is trusted from here: see
    /// [`TgBackend::adopt_ctor_nest`], which rebuilds `⟦cᵢ⟧` and its spine
    /// through this backend's [`TgBackend::mk`] and checks the stored rule and
    /// bridge against them before either is registered.
    ///
    /// Measured on `init-prelude`: this store is what takes
    /// `cached specs declined: βⱼ bodies not canonical` — the last remaining
    /// canonicity lever — to zero, and the constant and inductive re-mint rows
    /// with it. See [`SharedCtorNest`] for the chain from `⟦LT.mk⟧` to `Fin`.
    gen_ctor_nests: HashMap<(u32, Vec<Term>), Rc<SharedCtorNest>>,
    /// **The store**: `⊢ ⟦c.{us}⟧ ∈ ⟦T⟧` for every declaration whose typing
    /// could be derived when the declaration was checked, keyed by the constant
    /// and the universe levels it is stated at.
    ///
    /// Unconditional by construction — [`TgBackend::store_declar_typing`] drops
    /// a derivation that left antecedents rather than storing it — and matched
    /// against the caller's claim at the point of use by
    /// [`TgBackend::has_type_a`]'s single-exit guard, like every other clause.
    declar_typings: HashMap<(u32, Vec<Term>), Sealed>,
    /// The **quantified** declaration typings — `LEVELPOLY.md` §5.3 step 5.
    ///
    /// A value typing whose every antecedent is `uᵢ ∈ ω` over an ω-vocabulary
    /// parameter variable ([`Shared::param_vars`]) is not discarded: the
    /// antecedents are the *level hypotheses* of a level-polymorphic
    /// declaration, and the declaration boundary closes them by `Thm::gen`
    /// into `⊢ ∀u⃗. ⋀(uᵢ∈ω) → ⟦c⟧ ∈ ⟦T⟧`. Stored beside the entry the vars
    /// (outermost quantifier first, the order `inst_all` wants) and the
    /// antecedent list at the generic point, so a use can re-open the
    /// implication and hand the `uᵢ ∈ ω` assumptions to the caller's own
    /// antecedent channel (§5.2). `Sealed`, like every store here: the
    /// quantified theorem itself carries no sequent hypotheses.
    declar_typings_poly: HashMap<(u32, Vec<Term>), (Vec<FreeVar>, Vec<Formula>, Sealed)>,
    /// Keys whose declaration typing was **derived and then discarded** because
    /// the derivation stood under antecedents ([`Dt::Conditional`]).
    ///
    /// Instrumentation, and it draws no conclusion: it exists so that a use that
    /// misses the store can say *which* absence it missed. A declaration whose
    /// own check gapped and a declaration whose translation was computed and
    /// thrown away are the same `Dt::Miss` today, and they call for completely
    /// different work.
    declined_cond: std::collections::HashSet<(u32, Vec<Term>)>,
    /// `⊢ ∀x. ¬(x ∈ ⟦False⟧)` — **the threat-model anchor**, at the very symbol
    /// [`TgBackend::false_const`] hands the rest of the backend for `False`.
    ///
    /// Kept rather than dropped because it is the one theorem in the run that no
    /// rule consumes: the guarantee in `README.md` is a statement *about* the
    /// interpretation, not a step in it. Holding it here is what lets
    /// [`global_report`] say whether this run has it.
    false_anchor: Option<Sealed>,
    /// The level-quantification apparatus (`LEVELPOLY.md`), built over the
    /// prelude's tower when `NANODATG_LEVELPOLY=1` and `None` otherwise.
    ///
    /// **Prototype seam of the `explore/level-poly-target` branch.** When
    /// present, a `Sort ℓ` whose canonical level still mentions a parameter is
    /// interpreted as `srt(ℓ̂)` — a term with *facts* — instead of the opaque
    /// `sort(⟦ℓ⟧)` symbol, and [`TgBackend::ty_sort`] discharges
    /// `⟦Sort ℓ⟧ ∈ ⟦Sort (ℓ+1)⟧` at a variable `ℓ` as a conditional
    /// certificate under the `u ∈ ω` assumptions. Off by default; with the
    /// flag unset nothing here changes behaviour.
    lp: Option<Rc<derived::levels::apparatus::LevelPoly>>,
}

/// Whether the level-quantification prototype is enabled for this process.
fn levelpoly_enabled() -> bool {
    static F: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *F.get_or_init(|| std::env::var_os("NANODATG_LEVELPOLY").is_some_and(|v| v != "0"))
}

thread_local! {
    static SHARED: std::cell::RefCell<Option<Rc<std::cell::RefCell<Shared>>>> =
        const { std::cell::RefCell::new(None) };
}

/// Install a caller-supplied [`EnvCore`] as the seed of this thread's
/// [`Shared`] — the production route to one signature across both engines:
/// hand the same core to `mini`'s `Interp::over` and to this. Must run before
/// the thread's first `TgBackend` is built; panics if the thread already has
/// a `Shared`, because replacing one mid-run would strand every symbol the
/// old one minted.
pub fn install_shared_core(core: EnvCore) {
    SHARED.with(|slot| {
        assert!(
            slot.borrow().is_none(),
            "install_shared_core: this thread already has a Shared; installing the core must \
             happen before the first TgBackend"
        );
        *slot.borrow_mut() = Some(new_shared(core));
    })
}

/// The thread's shared signature, created on first use — over a private fresh
/// [`EnvCore`] unless [`install_shared_core`] ran first.
fn shared(_pre: &Prelude) -> Rc<std::cell::RefCell<Shared>> {
    SHARED.with(|slot| {
        if let Some(s) = slot.borrow().as_ref() {
            return s.clone()
        }
        let sh = new_shared(EnvCore::fresh());
        *slot.borrow_mut() = Some(sh.clone());
        sh
    })
}

/// A [`Shared`] over `core`, with the ten structure symbols minted from it.
fn new_shared(core: EnvCore) -> Rc<std::cell::RefCell<Shared>> {
    {
        let syms = {
            let mut env = core.env_mut();
            Syms {
                sort: env.declare(1),
                pi: env.declare(2),
                let_: env.declare(3),
                proj: env.declare(2),
                bvar: env.declare(1),
                lzero: env.declare(0),
                lsucc: env.declare(1),
                lmax: env.declare(2),
                limax: env.declare(2),
                idx: env.declare(1),
            }
        };
        // The prototype apparatus is built once per core, before anything
        // else numbers symbols off its `Env`; its cost is measured in
        // `LEVELPOLY.md` §4 and is paid only under the flag. The tower it is
        // built over is the thread prelude's — the same one `fast_forward`
        // replayed into this core's `Env`, so the symbols line up whichever
        // caller minted the core.
        let lp = if levelpoly_enabled() {
            let pre = prelude();
            let mut env = core.env_mut();
            derived::levels::apparatus::level_poly(&mut env, &pre.tower).map(Rc::new)
        } else {
            None
        };
        let sh = Rc::new(std::cell::RefCell::new(Shared {
            core,
            syms,
            lam_infos: HashMap::new(),
            lam_by_lam: HashMap::new(),
            lam_betas: HashMap::new(),
            lam_exts: HashMap::new(),
            pi_exts: HashMap::new(),
            pi_infos: HashMap::new(),
            pi_by_dprod: HashMap::new(),
            dprod_fs: None,
            prop_infos: HashMap::new(),
            prop_by_chi: HashMap::new(),
            undet_syms: HashMap::new(),
            prop_exts: HashMap::new(),
            prop_u0s: HashMap::new(),
            prop_intros: HashMap::new(),
            lam_fss: HashMap::new(),
            lam_dprods: HashMap::new(),
            inds: None,
            ind_ty_u1: None,
            rec_core: None,
            bool_rec: None,
            nat_rec: None,
            list_rec: None,
            gen_inds: HashMap::new(),
            gen_recs: HashMap::new(),
            opaque_syms: HashMap::new(),
            const_syms: HashMap::new(),
            param_syms: HashMap::new(),
            param_vars: HashMap::new(),
            idx_syms: HashMap::new(),
            lit_syms: HashMap::new(),
            ind_syms: HashMap::new(),
            rec_nests: HashMap::new(),
            gen_ty_nests: HashMap::new(),
            gen_ctor_nests: HashMap::new(),
            declar_typings: HashMap::new(),
            declar_typings_poly: HashMap::new(),
            declined_cond: std::collections::HashSet::new(),
            false_anchor: None,
            lp,
        }));
        sh
    }
}

/// The Tarski–Grothendieck backend.
pub struct TgBackend<'x, 't: 'x, 'p: 't> {
    /// The signature, and everything keyed on it, shared per thread.
    shared: Rc<std::cell::RefCell<Shared>>,
    /// The [`Shared`]'s own [`EnvCore`], cloned out so the `Env` and the
    /// canonical variables are reachable without borrowing `Shared` — the
    /// two live behind different cells, so neither borrow is re-entrant on
    /// the other.
    core: EnvCore,
    /// The application machinery and the universe operator, shared per thread.
    pre: Rc<Prelude>,
    /// The checker's declaration environment, used to resolve a constant to its
    /// value so that `⟦c⟧` can be an *explicit definition* rather than an opaque
    /// symbol. This is what makes delta reduction justifiable at all.
    decls: &'x crate::env::Env<'x, 't>,
    /// Defining equations `⊢ ⟦c⟧ = ⟦value⟧`, keyed by the constant's expression
    /// node. Delta certificates are built from these by congruence.
    const_defs: HashMap<ExprPtr<'t>, Thm>,
    /// The same equations keyed by the *term* `⟦c⟧` instead of the Lean node.
    /// A typing obligation's target arrives as a term, and a Lean type is very
    /// often a defined constant (`PN`, `Nat`, …) rather than the `Π` it stands
    /// for; this is how [`TgBackend::has_type_h`] unfolds it.
    abbrev_defs: HashMap<Term, Thm>,
    /// Defining equations `⊢ ⟦let …⟧ = ⟦body[val/x]⟧`, keyed by the `Let` node.
    /// Zeta reduction is exactly this equation.
    let_defs: HashMap<ExprPtr<'t>, Thm>,
    syms: Syms,
    /// Interpretation cache. Without it, interpreting nested expressions would
    /// be quadratic; with it, each hash-consed Lean node is translated once.
    exprs: HashMap<ExprPtr<'t>, Term>,
    /// The same map read backwards: one Lean node per term this backend
    /// interpreted, first occurrence winning.
    ///
    /// A typing obligation's *target* arrives as a term, and beta-reducing a
    /// target `app(f, x)` needs `x ∈ dom` — a typing judgement about a term with
    /// no Lean node in hand. This is how [`TgBackend::target_mem`] gets one back,
    /// so that the whole `has_type` recursion applies to it rather than only the
    /// term-level facts. It is a *hint*: the node is checked to interpret to the
    /// term before it is used, and the derivation is checked against the claim
    /// by [`TgBackend::has_type_a`]'s guard either way.
    exprs_rev: HashMap<Term, ExprPtr<'t>>,
    levels: HashMap<LevelPtr<'t>, Term>,
    /// One representative per level-equivalence class, so that levels the
    /// checker considers equal interpret to identical terms.
    level_reps: Vec<LevelPtr<'t>>,
    /// Memoised class lookup.
    level_canon: HashMap<LevelPtr<'t>, LevelPtr<'t>>,
    /// Per-name and per-index constants, allocated on demand.
    consts: HashMap<NamePtr<'t>, FnSym>,
    /// Lean local ids to kernel free variables. Allocated through `Env` rather
    /// than derived from the Lean id: the derived rules mint fresh variables for
    /// Leibniz holes, and a collision between such a hole and a Lean local would
    /// substitute at the wrong occurrences — a genuine soundness bug, not just a
    /// wrong answer.
    ///
    /// **The key is [`LocalKey`]: a de Bruijn-level local is identified by its
    /// level *and* its interpreted declared type; a `mk_unique` local by its id
    /// alone.** Level and type identify the variable — two locals agreeing in
    /// both have no attribute left to differ in — and the level alone does not:
    /// [`TcCtx::replace_dbj_level`] retires a level when its binder closes, so
    /// one level is reused across a declaration by binders with unrelated
    /// types. Under a level-only key those all mapped to a single kernel
    /// variable, and a memoised theorem mentioning that variable (its typing
    /// hypothesis `v ∈ ⟦A⟧` above all) would be a statement about *some earlier
    /// binder's* type at every later reuse. With the type in the key, a hit
    /// returns a variable whose every memoised statement was made at exactly
    /// this level and this type, so the statement is the one the caller is
    /// asking about — that identity, not hope, is what makes the memoised
    /// theorems valid.
    ///
    /// Why the *interpreted* type and not the Lean node: every memoised theorem
    /// is a kernel statement, so kernel-term identity of the type is exactly
    /// the grain at which two locals' statements coincide. Two Lean spellings
    /// with one interpretation generate literally identical statements and may
    /// share a variable; splitting them would only lose hits. The converse
    /// direction is safe because the interpretation memo (`exprs`) makes
    /// `⟦·⟧` a function, and `Env`'s counters never reissue a symbol, so equal
    /// terms cannot stand for different types. A type that itself mentions
    /// locals makes the key recursive — `⟦A⟧` contains the *variables* of the
    /// outer locals — which is deliberate: level `n` at type `P x` shares
    /// exactly when `x` resolved to the same variable first, and that is
    /// precisely when the typing hypotheses agree verbatim.
    ///
    /// This map lives and dies with the backend, i.e. per declaration — the
    /// same lifetime as the checker's `TcCache` (`infer`/`whnf`/`eq`), which is
    /// the set of caches the (level, type) discipline exists to serve.
    locals: HashMap<LocalKey, kernel::FreeVar>,
    params: HashMap<NamePtr<'t>, Term>,
    /// The ω-vocabulary's free variable per parameter name — the per-backend
    /// memo over [`Shared::param_vars`], with a per-backend variable for a
    /// name interned in this declaration's arena (such names cannot outlive
    /// the declaration, so neither need their variable).
    param_omegas: HashMap<NamePtr<'t>, FreeVar>,
    idxs: HashMap<u64, Term>,

    /// The applicative structure of every term this backend built.
    ///
    /// **Redundant, and retained only because retiring it moves this backend's
    /// frontier counters.** `kernel::Term::as_app` reads the same `(f, args)`
    /// straight off the term, which is what `derived::skeleton` and `mini`'s
    /// `Interp::parts_of` now do; a side table is a second copy of the
    /// argument vector the term already holds, keyed by the term. On `mini`
    /// the identical table measured **54 % of the live heap** of an
    /// `init-prelude` run and 96 % of the peak RSS of a closure run
    /// (`PRELUDE-COST.md` §3.2), and its misses were the silent kind: a term
    /// the kernel itself built read back as structureless. See
    /// [`skeleton_recorded`] for what the switch here would cost.
    parts: HashMap<Term, (FnSym, Vec<Term>)>,
    /// Where each lambda occurrence sits.
    lam_sites: HashMap<ExprPtr<'t>, LamSite<'t>>,
    /// Where each dependent-`Π` occurrence sits.
    pi_sites: HashMap<ExprPtr<'t>, PiSite>,
    /// Where each `Prop`-valued `∀` occurrence sits.
    prop_sites: HashMap<ExprPtr<'t>, PropSite>,
    /// Where each `Π` that falls under neither clause of §6.2 sits.
    undet_sites: HashMap<ExprPtr<'t>, PropSite>,
    /// Where each **proof `λ`** sits — §6.2's other lambda clause, whose
    /// interpretation is `•` and so carries no graph. See [`PropLamSite`].
    prop_lam_sites: HashMap<ExprPtr<'t>, PropLamSite<'t>>,
    /// **Which clause of §6.2 an expression's type puts it under** — and
    /// whether it is decided at all. See [`Clause`] and
    /// [`TgBackend::body_clause`].
    ///
    /// Memoised, and that is not an optimisation. The interpretation has to be
    /// a *function*, so the same expression must not be classified two ways on
    /// two paths.
    props: HashMap<ExprPtr<'t>, Clause>,
    /// **Which clause of §6.2 an expression's *own* sort puts it under** —
    /// whether it is a proof. [`TgBackend::props`] one level down; see
    /// [`TgBackend::term_clause`], and memoised for the same reason.
    terms: HashMap<ExprPtr<'t>, Clause>,
    /// Memoised delta-unfolding of a type down to its `Sort`.
    exposed_sorts: HashMap<ExprPtr<'t>, Option<LevelPtr<'t>>>,
    /// Memoised [`TgBackend::open_level`]: one more than the maximum de Bruijn
    /// *level* embedded in the expression (0 for an expression with no level
    /// locals). A function of the node, so the binder-open level the
    /// interpretation chooses is too — which is what makes `⟦·⟧` independent
    /// of the ambient counter at interpretation time.
    open_levels: HashMap<ExprPtr<'t>, u16>,
    /// A copy of the shared canonical bound-variable slot, so that the common
    /// read-only use needs no borrow.
    x_canon: FreeVar,

    /// Typing derivations `⊢ conj(assms') → ⟦e⟧ ∈ ty`, memoised on the triple.
    /// `None` is cached too: most of what this is asked is not derivable, and
    /// re-deriving that answer is the cost that matters. The assumptions are
    /// part of the key because they are part of the statement.
    ///
    /// The stored `Vec<Formula>` is `assms'`: the key's assumptions, followed by
    /// whatever the derivation had to *acquire* — see [`TgBackend::has_type_h`].
    has_types: HashMap<(ExprPtr<'t>, Term, Vec<Formula>), Option<(Thm, HtClause, Vec<Formula>)>>,
    /// The constant instantiations currently being unfolded, innermost last.
    ///
    /// This is what makes [`TgBackend::has_type_const`]'s step into a
    /// constant's value **terminate by construction**, and it replaced a depth
    /// bound. `Self::ht_active` cannot do the job: it keys on the whole triple
    /// `(e, ty, assms)`, and a delta chain runs through *distinct* constants,
    /// with `subst_expr_levels` minting a fresh, unequal key at each step. Keyed
    /// on `(name, levels)` — the instantiation, not the expression — a repeat is
    /// exactly a cycle in the delta graph, and cutting it loses nothing that
    /// could have terminated.
    const_active: Vec<(NamePtr<'t>, LevelsPtr<'t>)>,
    /// The `(e, ty, assms)` triples currently being worked on, so that a
    /// definition that somehow refers to itself returns `None` instead of
    /// looping.
    ht_active: Vec<(ExprPtr<'t>, Term, Vec<Formula>)>,
    /// `⊢ H → ⟦e⟧ = •` per **proof** expression, memoised — see
    /// [`TgBackend::point_of_proof`]. The value is an `Option` so a failure is
    /// memoised too: the two `has_type` calls behind it are not free, and a
    /// proof whose typing is out of reach stays out of reach.
    ///
    /// Stored as the `(theorem, assumptions)` pair rather than as a [`CondEq`]:
    /// cloning a `CondEq` is a *copy* the escape ledger charges for, and a memo
    /// is not a second obligation.
    points: HashMap<ExprPtr<'t>, Option<(Thm, Vec<Formula>)>>,
    /// Memoised syntactic type synthesis.
    syn_types: HashMap<ExprPtr<'t>, Option<ExprPtr<'t>>>,
    /// Memoised delta-unfolding of a type down to its `Π`.
    exposed: HashMap<ExprPtr<'t>, Option<ExprPtr<'t>>>,
    /// Memoised "could this shape ever be typed" test.
    typeables: HashMap<ExprPtr<'t>, bool>,
    /// `⊢ elem ∈ type` for every constructor of an interpreted inductive, keyed
    /// by the pair of terms it is about. This is what lets `has_type` discharge
    /// an obligation whose argument is a constructor — the commonest one there
    /// is, once a development has any inductive in it.
    ind_mems: HashMap<(Term, Term), Thm>,
    /// `⊢ ⟦T⟧ ∈ ⟦Sort u⟧` for an interpreted inductive **type** — as opposed to
    /// its constructors, which are [`TgBackend::ind_mems`]. Kept apart for two
    /// reasons: the theorem underneath is not a constructor membership but
    /// [`derived::cumul`]'s cumulative-hierarchy argument, which is expensive
    /// enough to be built only when something asks; and the clause that serves
    /// it is counted separately ([`HtClause::IndTy`]), so "the theorem is
    /// registered but nothing consults it" is a readable outcome rather than a
    /// number hidden inside `Ctor`'s.
    ///
    /// The value is an `Option` so a *failed* lookup is memoised too: the miss
    /// is the common case and re-deciding it per obligation is not free.
    ind_ty_mems: HashMap<(Term, Term), Option<Thm>>,
    /// The abbreviation symbol standing for each interpreted inductive or
    /// constructor, with its defining equation, keyed by the Lean name **and the
    /// universe levels it is used at**. Keeping the interpretation *injective on
    /// constants*: see [`TgBackend::ind_abbrev`].
    ind_syms: HashMap<(NamePtr<'t>, Vec<Term>), (Term, Thm)>,
    /// The conditional membership rule for each interpreted constructor that is
    /// **applied** rather than being a term in its own right — `List.nil` and
    /// `List.cons`, whose Lean types are `Π`s. See [`CtorRule`].
    ///
    /// Keyed by the Lean name **and the universe levels it is used at**, exactly
    /// as [`TgBackend::ind_syms`] is, and for a reason that is not defensive.
    /// The stored theorem mentions `S = ⟦Sort ℓ⟧` at *those* levels, and the
    /// abbreviation symbols `⟦List⟧`, `⟦List.nil⟧` and `⟦List.cons⟧` that
    /// `ind_abbrev` mints per `(name, levels)`. A name-only key meant the rule
    /// built at the first instantiation encountered was handed back at every
    /// later one, and it is a statement about the wrong universe there — its
    /// premise `α ∈ S` cannot be discharged and, if it somehow were, the
    /// conclusion is about the other instantiation's symbols and
    /// `has_type_a`'s guard rejects it. Either way a derivation that was
    /// available is reported as a gap.
    ///
    /// Nothing in the arena corpus reaches this: no declaration in the
    /// tutorials, `init-prelude` or `undecidability` interprets a
    /// `List`-shaped inductive at two instantiations within one backend, which
    /// is per declaration. `tests/fixtures/good/list-two-levels.ndjson` is the
    /// case built to reach it, and it measures the difference — see
    /// `a_constructor_rule_is_keyed_by_its_universe_levels`.
    ctor_rules: HashMap<(NamePtr<'t>, Vec<Term>), CtorRule>,
    /// What the general path's ι rule needs about a **constructor with fields**,
    /// keyed exactly as [`TgBackend::ctor_rules`]. See [`GenCtorBridge`].
    gen_ctor_bridges: HashMap<(NamePtr<'t>, Vec<Term>), Rc<GenCtorBridge>>,
    /// **One `⟦c⟧` per constructor per backend** — see [`TgBackend::gen_const`]
    /// for why re-minting one is not merely wasteful.
    gen_consts: HashMap<(NamePtr<'t>, Vec<Term>), Option<Term>>,
    /// **One type-former nest per declaration per backend**, keyed as
    /// [`TgBackend::gen_consts`] is. See [`GenTyNest`], and
    /// [`TgBackend::gen_const`] for why a second nest for one declaration is a
    /// bug rather than an inefficiency.
    gen_ty_nests: HashMap<(NamePtr<'t>, Vec<Term>), Rc<GenTyNest>>,
    /// **One carrier per declaration per backend**, ahead of the per-thread
    /// [`Shared::gen_inds`].
    ///
    /// The per-thread cache guards every hit by re-walking the declaration and
    /// re-interpreting its field types, and falls back to a rebuild when they
    /// have drifted (`WIRING-DESIGN.md` §3.4). That is right *across* backends
    /// and wrong *within* one: the re-walk opens each binder at a fresh local,
    /// so `interp` recomputes rather than recalling, and on `init-prelude` it
    /// recomputes differently often enough that `Lean.Name`'s carrier was built
    /// **507** times for the 97 backends that wanted its recursor. Two carriers
    /// in one backend means two `⟦Lean.Name.str⟧` symbols, and then `⟦cᵢ f⃗⟧`,
    /// the constructor rule and the ι rule are about different sets — 54 ι
    /// sites' worth of gaps, and the interpretation not a function on that
    /// constant.
    ///
    /// This memo is the fix and it is only a memo: nothing is trusted from it
    /// that was not already checked when it was built, and it is dropped with
    /// the backend, so the cross-backend guard is untouched.
    gen_inds: HashMap<(NamePtr<'t>, Vec<Term>), Option<Rc<GenInd>>>,
    /// The curried nest interpreting each recursor this backend understands,
    /// keyed like [`TgBackend::ind_syms`] by the name and the universe levels.
    rec_nests: HashMap<(NamePtr<'t>, Vec<Term>), Rc<RecNest>>,
    /// What [`TgBackend::guard_and_generalise_at`] hoisted, keyed by the
    /// **closure** it produced: `∀w. (w ∈ A → φ(w))` ↦ `(w, ⟦A⟧, φ(w))`.
    ///
    /// A closure is an opaque `Formula` once it is built — the kernel exposes no
    /// destructor for `∀` — and the discharge in [`TgBackend::peel_family`] needs
    /// the binder's variable back, because `φ(w)`'s subject is a term some Lean
    /// node interprets to and re-opening it at a *fresh* variable would name a
    /// term no node ever produced.
    ///
    /// It is a **hint and nothing more**. Everything read out of it is checked:
    /// the typing derivation is `has_type`'s, re-generalised through
    /// `guard_and_generalise_at`, and the result is compared against the very
    /// assumption being peeled before it is used. A wrong or stale entry
    /// therefore yields `None`, never a discharge of something else.
    hoisted: HashMap<Formula, (FreeVar, Term, Formula)>,
    /// The inductive declarations [`TgBackend::gen_ind`] is currently walking,
    /// innermost last — the [`TgBackend::const_active`] pattern.
    ///
    /// A field type mentioning the declaration itself is refused outright
    /// ([`Decline::SelfMention`]), so this should be unreachable; it costs
    /// three lines and makes "should be" not matter.
    spec_active: Vec<NamePtr<'t>>,
    /// Whether the last [`TgBackend::gen_ind_build`] declined only because the
    /// declaration's constructors were not in the environment yet — the one
    /// [`Decline`] that must not be memoised.
    spec_unavailable: bool,

    _marker: PhantomData<&'p ()>,
}

/// The curried interpretation of a **recursor**: one lambda graph per Lean
/// argument, with `derived`'s W-recursor at the bottom.
///
/// `INDUCTIVES.md`'s "wiring" correction names this the *currying layer*, and
/// says why it cannot be avoided. Lean applies a recursor one argument at a
/// time, so the checker reads `Bool.rec C f t b` as
/// `app(app(app(app(⟦Bool.rec⟧,⟦C⟧),⟦f⟧),⟦t⟧),⟦b⟧)` — four set-applications,
/// chosen before the head is even known — whereas
/// [`derived::wrec`] supplies one application at a Kuratowski pair. The
/// bridge is a nest of [`derived::funcs::lambda_n`] graphs, one per Lean
/// argument, each carrying the earlier ones as parameters:
///
/// ```text
/// ⟦Bool.rec.{u}⟧ := lam₁(D₁)      t₁(C)     := lam₂(C, D₂(C))
///                                 t₂(C,F)   := lam₃(F, D₃(C))
///                                 t₃(F,T)   := lam₄(F, T, ⟦Bool⟧)
///                                 t₄(F,T,b) := app(brec(F,T), b)
/// ```
///
/// The domains `D₁ = ⟦Bool → Sort u⟧`, `D₂(C) = ⟦C Bool.false⟧` and
/// `D₃(C) = ⟦C Bool.true⟧` are read off the recursor's **own type**, with
/// each binder opened at a local exactly as [`TgBackend::interp_lambda`]
/// opens one. That is not a convenience: the reduct of an iota step is the
/// matching minor premise's lambda re-applied to the same arguments, so its
/// beta steps carry the very same domain premises, and the two sides of the
/// equation can only share their assumptions if the two nests share their
/// domains. They are the same terms because both go through
/// [`TgBackend::interp`] on the same Lean types.
struct RecNest {
    /// `⟦T.rec.{us}⟧`, the abbreviation symbol.
    head: Term,
    /// `⊢ ⟦T.rec.{us}⟧ = lam₁(D₁)`.
    head_def: Thm,
    /// The graph symbols, outermost first.
    lams: Vec<FnSym>,
    /// `⊢ ∀p⃗ ∀A ∀a. (a ∈ A → app(lam(p⃗,A),a) = t(p⃗,a))`, one per level.
    betas: Vec<Thm>,
    /// `⊢ ∀p⃗ ∀x. t(p⃗,x) = body`, one per level.
    t_defs: Vec<Thm>,
    /// Which earlier Lean arguments each level's graph carries as
    /// parameters — `[[], [0], [0,1], [0,1,2]]` at depth four.
    ///
    /// Every level carries *all* the arguments above it, rather than only the
    /// ones its own body happens to mention. `Bool`'s bottom
    /// `app(brec(F,T), b)` ignores the motive, so the tighter `[[], [0], [1],
    /// [1,2]]` would do for it; `N`'s does not, because the target `T` it
    /// recurses into **is** the motive's value at `N.zero`. Carrying the whole
    /// prefix is what makes the nest independent of its bottom, which is what
    /// `List.rec` — a parameter, a motive, two minors and a major — will want
    /// at depth five.
    prefixes: Vec<Vec<usize>>,
    /// What sits underneath: which W-recursor the innermost body applies, and
    /// hence which ι rules [`TgBackend::derive_iota`] fires.
    bottom: RecBottom,
}

/// The **outermost** term of a nest: `lam₀(D₀)`.
///
/// A nest is not a nested *term*. Level `k`'s body is abstracted into the
/// symbol `tₖ` by `define_abbrev`, so the chain from one level to the next
/// lives in the `t_defs`, and the term the head abbreviates is only the
/// outermost graph. That is what `head_def` states, and therefore all
/// `head_def` can be asked about; the levels underneath are pinned by the walk
/// agreeing on the variables and domains they are built from, which is
/// [`nest_agrees`]'s first two clauses rather than this one.
///
/// The arity spine is still walked in full, because the deeper graph symbols
/// *are* used — by the ι rule, out of the adopted nest — and because
/// `Term::apply` panics on an arity mismatch rather than returning, so a
/// disagreement has to be caught before any term is built.
///
/// `None` if the shapes do not line up.
fn nest_replay(lams: &[FnSym], doms: &[Term]) -> Option<Term> {
    let depth = doms.len();
    if lams.len() != depth || depth == 0 {
        return None
    }
    for (k, l) in lams.iter().enumerate() {
        if l.arity() as usize != k + 1 {
            return None
        }
    }
    Some(Term::apply(lams[0], vec![doms[0].clone()]))
}

/// **The claim-check on a stored nest**: is this nest the one *this* walk would
/// have built?
///
/// Four things are asked, and no one of them implies the rest.
///
/// * The **variables** agree. The nest's theorems are stated over them, so a
///   walk that opened the recursor's binders elsewhere cannot use them.
/// * The **domains** agree. Every level is `lamₖ(x⃗, Dₖ)`, so one differing
///   domain makes every level a different term.
/// * The **arities** line up, which is what makes the levels replayable at all.
/// * `head_def` is about **this** `head` and concludes it equal to the
///   outermost graph. Without this clause a true equation about somebody else's
///   abbreviation of the same body would be accepted, which is the
///   mislabelling the store exists to avoid.
#[allow(clippy::too_many_arguments)]
fn nest_agrees(
    stored_vars: &[FreeVar],
    stored_doms: &[Term],
    head: &Term,
    head_def: &Thm,
    lams: &[FnSym],
    vars: &[FreeVar],
    doms: &[Term],
) -> bool {
    if stored_vars != vars || stored_doms != doms {
        return false
    }
    match nest_replay(lams, doms) {
        Some(outer) => *head_def.concl() == Formula::eq(head.clone(), outer),
        None => false,
    }
}

/// **The claim-check on a stored constructor nest**, and the spine it is about.
///
/// [`nest_agrees`]'s counterpart for [`Shared::gen_ctor_nests`], and asking more
/// because more is stored: not one defining equation but the two theorems every
/// consumer of the nest reads — [`CtorRule`]'s membership and
/// [`GenCtorBridge`]'s spine equation, each already instantiated at the stored
/// variables by the caller.
///
/// The two conclusions between them pin everything the adopting backend must
/// agree about:
///
/// * `ct`, `vars` and their **order**, through the spine both formulas mention;
/// * `doms` and *their* order, through the antecedent's atoms;
/// * `ty_spine`, the type former's own spine, which the rule concludes
///   membership in — a nest adopted at another declaration's `⟦T p⃗⟧` would type
///   its constructor into the wrong set;
/// * `bottom`, the carrier's `ctorᵢ(y⃗,r⃗)`, which the bridge equates the spine
///   to and which the general ι rule rewrites along.
///
/// The spine is built through `mk` rather than [`Term::apply`], so that the
/// adopting backend's `parts` records **every prefix** of it: a term the rules
/// cannot take apart is a term they cannot use, and the prefixes are what
/// `has_type_ctor_app` walks down. It is returned rather than recomputed by the
/// caller for the same reason [`nest_replay`] is separate from the assertion
/// about it — the term the check ran on must be the term that gets used.
#[allow(clippy::too_many_arguments)]
fn ctor_nest_agrees(
    mk: &mut impl FnMut(FnSym, Vec<Term>) -> Term,
    app: FnSym,
    ct: &Term,
    vars: &[FreeVar],
    doms: &[Term],
    ty_spine: &Term,
    bottom: &Term,
    rule: &Formula,
    bridge: &Formula,
) -> Option<Term> {
    if vars.len() != doms.len() {
        return None
    }
    let mut spine = ct.clone();
    for v in vars {
        spine = mk(app, vec![spine, Term::var(*v)]);
    }
    let prems: Vec<Formula> =
        vars.iter().zip(doms).map(|(v, d)| Formula::mem(Term::var(*v), d.clone())).collect();
    // A constructor reaching the nest has at least one level — the fieldless,
    // parameterless case is `gen_const_uncached`'s own arm, with an
    // *unconditional* membership — so the absent antecedent of an empty nest is
    // a decline rather than a vacuous match.
    let h = derived::conj_of(&prems)?;
    if *rule != Formula::imp(h.clone(), Formula::mem(spine.clone(), ty_spine.clone())) {
        return None
    }
    if *bridge != Formula::imp(h, Formula::eq(spine.clone(), bottom.clone())) {
        return None
    }
    Some(spine)
}

/// Whether two nests sit on **the same** W-recursor derivation.
///
/// Pointer equality, not structural, in all four arms — and it is exact rather
/// than approximate, because everything a bottom contributes to a nest is a
/// function of the `Rc`s compared here together with the walk's variables and
/// domains, which [`nest_agrees`] compares pointwise beside it.
///
/// * The three **hand-written** recursors are per-thread singletons
///   ([`Shared::nat_rec`] and friends), so two backends either hold the same
///   `Rc` or one of them is looking at a rebuild.
/// * A **general** bottom carries two: the [`GenRec`] — per thread behind
///   [`Shared::gen_recs`], and itself guarded on the [`GenInd`] it was built
///   over — and the [`GenTyNest`], per thread behind [`Shared::gen_ty_nests`]
///   since `42a0dee`. Both must match, and for different reasons. The `GenRec`
///   is what [`TgBackend::rec_nest`] applies at the nest's bottom, so a
///   different one is a different *term*; the `GenTyNest` is not mentioned by
///   the nest's term at all, but it is what [`TgBackend::fire_general`] reads
///   `app-spine(⟦T⟧,p⃗) = ind(p⃗)` out of, and a nest handed back with somebody
///   else's `⟦T⟧` in its bottom would fire the ι rule at a symbol this backend
///   has neither registered in `parts` nor given a defining equation.
fn same_bottom(a: &RecBottom, b: &RecBottom) -> bool {
    match (a, b) {
        (RecBottom::Enum(x), RecBottom::Enum(y)) => Rc::ptr_eq(x, y),
        (RecBottom::Nat(x), RecBottom::Nat(y)) => Rc::ptr_eq(x, y),
        (RecBottom::List(x), RecBottom::List(y)) => Rc::ptr_eq(x, y),
        (RecBottom::General(gx, tx), RecBottom::General(gy, ty)) => {
            pair_ptr_eq((gx, tx), (gy, ty))
        }
        _ => false,
    }
}

/// [`same_bottom`]'s general arm: **both** halves, **by identity**.
///
/// Factored out because it cannot otherwise be tested. Building a
/// [`RecBottom::General`] means building a [`derived::inductive::Machine`] and a
/// whole `GenRecursor`, so a unit test cannot reach the arm — and the mutation
/// that matters is invisible to the corpus, where the two halves never
/// disagree: dropping either `ptr_eq` accepts a nest over another backend's
/// carrier or another backend's `⟦T⟧` and moves no verdict, gap or escape.
/// Generic, so the test can supply the witnesses at a type it can allocate
/// twice over — and **without a `PartialEq` bound**, deliberately, so that
/// `==` cannot be written here in place of `Rc::ptr_eq`: value equality would
/// accept a rebuilt derivation that says the same thing about other symbols,
/// which is the whole failure this test is against.
fn pair_ptr_eq<A, B>(x: (&Rc<A>, &Rc<B>), y: (&Rc<A>, &Rc<B>)) -> bool {
    Rc::ptr_eq(x.0, y.0) && Rc::ptr_eq(x.1, y.1)
}

/// A [`RecNest`] in [`Shared::rec_nests`], with the two things a later backend
/// has to agree about before it may use it.
///
/// The nest's theorems are stated over `vars` and its terms mention `doms`, so
/// a backend reusing it must open the recursor's binders at *these* variables
/// — the discipline [`TgBackend::walk_spec`] already follows for a cached
/// [`GenInd`] — and must interpret the domains to the same terms. Both are
/// checked; neither is assumed.
struct SharedNest {
    nest: Rc<RecNest>,
    /// The head's symbol, so that a reusing backend can rebuild `⟦T.rec⟧` with
    /// [`TgBackend::mk`] and thereby register its shape in its own `parts`.
    head_sym: FnSym,
    /// The kernel variables the recursor's binders were opened at.
    vars: Vec<FreeVar>,
    /// The interpreted domains, one per level.
    doms: Vec<Term>,
}

/// The W-recursor at the bottom of a [`RecNest`], and with it the ι rules that
/// make the nest compute.
///
/// The *nest* is the same construction for every inductive — one lambda graph
/// per Lean argument, domains walked off the recursor's own type. What differs
/// is only the innermost body and the computation rules it is joined to, so
/// that is what this is: the plug, not a second nest.
/// # What `List.rec` needed, and what it cost — measured, 2026-07-31
///
/// The nest itself: **nothing**, as predicted. Its depth is `major_idx + 1`,
/// which is five for `List.rec.{u₁,u} α C nil cons t`, and every level already
/// carried the whole prefix above it. What the parameter cost, beyond the third
/// variant of this enum:
///
/// * **the minors and the target move along by `num_params`.** [`Self::rec_nest`]
///   reads them at `vars[np+1]`/`vars[np+2]` and `doms[np+1]`, which is
///   `doms[2]` — the motive at `List.nil α`, not at a closed constructor.
/// * **the constructor's parameters are dropped before its fields.**
///   [`TgBackend::derive_iota_core`] used to *reject* a constructor with
///   parameters; it now takes `ctor_args[num_params..]`, mirroring
///   `reduce_rec`'s `num_extra_params_to_major`, which for a non-nested
///   inductive is exactly `num_params`. The two are held together by requiring
///   the argument count to be `num_params + num_fields` on the nose, and by the
///   guard at the end of [`TgBackend::derive_iota`], which compares the derived
///   equation against the reduct `reduce_rec` really produced.
/// * **the type is a redex.** `⟦List α⟧` is `app(⟦List.{u}⟧, ⟦α⟧)`, so the
///   bridge to `derived::wlist`'s `lt(α)` is not a defining equation but a beta
///   step, conditional on `⟦α⟧ ∈ ⟦Type u⟧` — the recursor's own level-0 domain
///   obligation. [`TgBackend::mem_along_c`] is [`TgBackend::mem_along`] with
///   that premise carried rather than discharged.
/// * **the constructors are applied to `α`**, so ι needs the *equations*
///   `app(Nil(S),α) = ⟨inl •,∅⟩` and `app(app(app(C(S),α),h),t) = ⟨inr h,{⟨•,t⟩}⟩`
///   where `derived::wlist_fun` previously exported only the memberships. It
///   exports both now.
///
/// `076_listRecReduction` went **63 gaps / 15 escapes → 32 / 16**, all five ι
/// gaps closed. It did **not** reach the `073` outcome this note used to
/// predict, and the prediction was wrong for a reason worth keeping: `076`'s
/// arguments *are* context locals, but its escapes are not about them. It had 15
/// escaping certificates before any ι certificate existed and has 16 after, so
/// they are not the recursor's — closing 31 gaps beneath them moved them by one.
/// What is left is 16 escapes, three primary gaps (two `eq_cache`, one
/// `pi congruence: the body certificate is not the fibres' pointwise equation`)
/// and 13 cascade over those three, which is `075`'s residue at `076`'s binder
/// depth.
#[derive(Clone)]
enum RecBottom {
    /// A two-constructor enumeration: `app(brec(F,T), b)`.
    Enum(Rc<BoolRecursor>),
    /// The unary recursive shape: `app(nrec(z,s,T), b)` with `T` the motive's
    /// value at the nullary constructor — i.e. the nest's own level-2 domain.
    Nat(Rc<NatRecursor>),
    /// The parameterised recursive shape: `app(lrec(α,z,s,T), b)`, the nest one
    /// level deeper. `α` is the recursor's *first* argument, so the two minor
    /// premises sit at `vars[2]`/`vars[3]` and `T` is `doms[2]` — the motive at
    /// `List.nil α` rather than at a closed constructor.
    List(Rc<ListRecursor>),
    /// **The general path**: `derived::inductive`'s carrier and
    /// [`derived::inductive::GenRecursor`], at whatever arity the declaration
    /// has. The three arms above are the hand-written stacks and stay ahead of
    /// this one in [`TgBackend::rec_bottom`] — see the seam note in
    /// `WIRING-DESIGN.md` §8: the two build *different sets* (seed `U(A)` vs
    /// `U({A,T})`, fibres `0`/`1` vs `finord(m)`) with no bridging theorem, so
    /// nothing may mix them for one inductive.
    /// The [`GenTyNest`] beside it is the Lean-facing type former of the very
    /// declaration being eliminated. It is carried here rather than inside
    /// [`GenRec`] because it is keyed by the *declaration's* instantiation
    /// while `GenRec` is reached through the *recursor's*, whose level list
    /// carries the motive's in front. Both are per thread —
    /// [`Shared::gen_recs`] and [`Shared::gen_ty_nests`] — and
    /// [`same_bottom`] asks `Rc::ptr_eq` of each, which is what lets a general
    /// nest be shared at all: the ι rule still needs
    /// `app-spine(⟦T⟧,p⃗) = ind(p⃗)` at symbols *this* backend has registered,
    /// and the pointer test is what says the adopted nest is over them.
    General(Rc<GenRec>, Rc<GenTyNest>),
}

/// **A general inductive declaration, translated** — the spec the derived layer
/// was handed, the interpreted field-type bodies its `βⱼ` symbols stand for,
/// and the carrier with every theorem about it.
///
/// Cached per thread (`Shared::gen_inds`), which is what forces
/// `WIRING-DESIGN.md` §3.4's symbol discipline: an `Inductive::build` per
/// obligation would be absurd, so every term reachable from here — the `βⱼ`
/// bodies above all — must be stated over per-thread-stable symbols, and
/// [`Shared::ind_syms`] is the move that makes them so.
///
/// Nothing is *trusted* from a hit. [`TgBackend::gen_ind`] re-walks the
/// declaration under the recorded variables and compares the freshly
/// interpreted field-type bodies against [`GenInd::beta_bodies`]; a mismatch
/// declines the cache rather than the declaration, and is counted. A stale
/// entry therefore costs a rebuild, never a theorem about the wrong terms.
struct GenInd {
    /// The `np` parameter variables the declaration's own binders were opened
    /// at. Every `βⱼ` body is stated over these.
    param_vars: Vec<FreeVar>,
    /// The interpretations of the `np` parameter binder types, in order — the
    /// domains of the Lean-facing type former's nest. `param_doms[i]` may
    /// mention `param_vars[..i]`.
    ///
    /// Part of the cache guard, on exactly the same grounds as
    /// [`GenInd::beta_bodies`]: a parameter's domain is an interpretation like
    /// any other, so a symbol that did not survive the backend change makes the
    /// stored nest a statement about somebody else's set.
    param_doms: Vec<Term>,
    /// Per constructor, in Lean **declared** order: which fields are plain and
    /// which recursive. Part of the guard — a mask that changed under a
    /// re-walk means the walk is reading a different declaration.
    orders: Vec<Vec<Slot>>,
    /// Per constructor, the kernel variable each field's binder was opened at,
    /// in declared order. A recursive field's variable is recorded and appears
    /// in **no** abstraction list, which is what makes a later field's
    /// dependence on it an automatic decline (`kernel::thm::define` refuses a
    /// body with free variables outside `xs`).
    field_vars: Vec<Vec<FreeVar>>,
    /// Per constructor, the interpretation of each **plain** field's Lean type,
    /// in plain order — the bodies `define_abbrev` abstracted into `βⱼ`.
    beta_bodies: Vec<Vec<Term>>,
    /// The `βⱼ` symbols themselves with their defining equations, in the same
    /// order. Stored because a re-walk must speak of *these* symbols: the
    /// cached `Ctor::mem` mentions them, and a freshly minted symbol with an
    /// identical body is still a different symbol.
    betas: Vec<Vec<(FnSym, Thm)>>,
    /// The translated declaration, theorems included — the standing memo rule.
    ind: Rc<derived::inductive::Inductive>,
}

/// **What the general ι rule needs about a constructor with fields**, produced
/// as a by-product of building its nest ([`TgBackend::gen_ctor_nest`]) and kept
/// so that the two are never derived twice.
///
/// [`derived::inductive::GenRecursor`]'s (S4) is stated at
/// `ctorᵢ(y⃗,t⃗)` under `Hᵢ^ctor` — the carrier's own spelling of both. A use
/// site has neither: it has the Lean spine `⟦cᵢ f₀ … f_{nf−1}⟧` and typing
/// obligations at the *nest's* domains (`⟦β⟧` for a plain field, `⟦T⟧` for a
/// recursive one). These two theorems are the bridge, and they are exactly the
/// two the nest builder already had in hand:
///
/// ```text
/// spine: ⊢ ∀x⃗. (H_declared(x⃗) → app-spine(⟦cᵢ⟧, x⃗) = ctorᵢ(x⃗ split by the mask))
/// mem:   ⊢ ∀x⃗. (H_declared(x⃗) → Hᵢ^ctor(x⃗ split by the mask))
/// ```
///
/// with `H_declared` the fields' memberships **in Lean declared order** at the
/// nest's domains. Instantiating both at one argument list and discharging
/// `H_declared` once serves the constructor bridge (§6.4 step 2) and the ι
/// rule's own `Hᵢ^ctor` (step 3) from a single set of obligations, which is
/// what keeps the two sides of the equation resting on the same assumptions.
struct GenCtorBridge {
    spine: Thm,
    /// `None` exactly when the constructor has **no fields**: `Ctor::mem` then
    /// carries no `Hᵢ^ctor` at all (the `Ctx(None)` discipline), and the ι rule
    /// asks for none either. A `Some` here at a field-free constructor, or a
    /// `None` at one with fields, would put the two out of step, so the arity is
    /// what decides which is expected — never the option itself.
    mem: Option<Thm>,
    /// How many of [`GenCtorBridge::vars`] are the declaration's **parameters**.
    /// They come first, ahead of the fields, because that is the order Lean's
    /// spine has.
    np: usize,
    /// The variables both theorems are generalised over: `np` parameters, then
    /// the fields in declared order.
    vars: Vec<FreeVar>,
    /// The mask over the **fields**, so a caller can split an argument list the
    /// same way.
    order: Vec<Slot>,
}

/// **A constructor's nest**, kept per thread rather than per backend — the
/// [`SharedNest`] of [`TgBackend::gen_ctor_nest`].
///
/// `⟦cᵢ⟧` is the head of a nest of `np + nf` lambda graphs, and every symbol in
/// it is a fresh [`derived::define_abbrev`]. Built per backend, `⟦LT.mk⟧` was a
/// different symbol in every declaration, and that is the **root** of the
/// remaining canonicity failure on `init-prelude`: the first drift in the run
/// is `⟦LT.mk⟧`, which re-mints `⟦instLTNat⟧` (its value is `LT.mk Nat.lt`),
/// which changes the `βⱼ` body of `Fin.mk`'s second field (`val < n`), which
/// misses [`TgBackend::gen_ind`]'s guard, which rebuilds `Fin`'s translation and
/// with it every symbol above it. See [`Shared::gen_ctor_nests`].
///
/// The whole package is stored, not merely the term: the nest's symbols are
/// what [`CtorRule`] and [`GenCtorBridge`] are stated over, so a backend that
/// adopted the term and rebuilt the rules would be back where it started.
struct SharedCtorNest {
    /// The translation the nest was built over, for the `Rc::ptr_eq` guard.
    gi: Rc<GenInd>,
    /// The type former's nest, likewise.
    tn: Rc<GenTyNest>,
    /// The head's symbol, so that a reusing backend can rebuild `⟦cᵢ⟧` with
    /// [`TgBackend::mk`] and thereby register its shape in its own `parts` —
    /// [`TgBackend::adopt_ty_nest`]'s reason, at the constructor.
    ct_sym: FnSym,
    ct: Term,
    ct_ax: Thm,
    /// The kernel variables the nest's levels were opened at: the declaration's
    /// parameters, then the constructor's fields in declared order.
    vars: Vec<FreeVar>,
    /// The interpreted domains, one per level — a parameter's binder type, a
    /// plain field's Lean type, a recursive field's the spine `⟦T p⃗⟧`.
    doms: Vec<Term>,
    rule: CtorRule,
    bridge: Rc<GenCtorBridge>,
}

/// **The Lean-facing type former**, and the bridge from the spine Lean writes
/// to the carrier's `ind(p⃗)` — `WIRING-DESIGN.md` §5, at general `np`.
///
/// `derived::inductive` states everything at `ind(p⃗)`, a term whose head is a
/// `FnSym` of arity `np`. Lean writes `T α β` as a curried application, so
/// `⟦T⟧` has to be a **set**: a nest of `np` lambda graphs, exactly
/// [`TgBackend::gen_ctor_nest`]'s construction with `ind(p⃗)` at the bottom
/// instead of `ctorᵢ(y⃗,r⃗)`. `List` has had this shape by hand since
/// [`TgBackend::list_const`] (`ListFun::l_of` and its `l_beta`); this is that,
/// generally.
///
/// The bridge is conditional, and the condition is not decoration: the level-`k`
/// beta equation holds only when the argument is in the domain, so
/// `app-spine(⟦T⟧, p⃗) = ind(p⃗)` is available exactly under the parameters' own
/// typings. Every consumer therefore carries `H_p` and discharges it from the
/// obligations it already has — the constructor rule from its own premises, the
/// ι rule from `nest_chain`'s.
///
/// **`np = 0` is the same structure with an empty nest**: `spine` is `head`,
/// `prems` is empty and `spine_eq` *is* the defining equation `⊢ ⟦T⟧ = ind()`,
/// so the parameterless path is byte-identical to what it was before this
/// existed. That is deliberate — the zero-gap files must not be re-derived
/// through a vacuous nest.
struct GenTyNest {
    /// `⟦T⟧` — the abbreviation a Lean `Const` interprets to.
    head: Term,
    /// `⊢ ⟦T⟧ = <the outermost graph, or `ind()` when `np = 0`>`.
    head_ax: Thm,
    /// `head`'s symbol, so that a backend adopting this nest from
    /// [`Shared::gen_ty_nests`] can rebuild `⟦T⟧` through [`TgBackend::mk`] and
    /// so register its shape in its own `parts`. `None` only if the head was
    /// not built by `mk`, which declines the sharing.
    head_sym: Option<FnSym>,
    /// The `np` parameter variables the nest was built at — [`GenInd`]'s own,
    /// so that `ind(p⃗)` here is the term its theorems mention.
    vars: Vec<FreeVar>,
    /// The parameter domains in order; `doms[i]` may mention `vars[..i]`.
    doms: Vec<Term>,
    /// `pᵢ ∈ doms[i]`, in order — `H_p`'s atoms, **right**-nested by
    /// `derived::conj_of` when bundled, like every other derived antecedent.
    prems: Vec<Formula>,
    /// `app-spine(⟦T⟧, p⃗)` at [`GenTyNest::vars`]; `head` itself when `np = 0`.
    spine: Term,
    /// `⊢ (H_p →) app-spine(⟦T⟧, p⃗) = ind(p⃗)`, at [`GenTyNest::vars`].
    spine_eq: Thm,
    /// The same, `∀`-closed over [`GenTyNest::vars`], for use at other terms.
    spine_eq_all: Thm,
}

/// The general recursor of one declaration, with the carrier it eliminates and
/// the shared W-recursor its theorems are stated over.
struct GenRec {
    gi: Rc<GenInd>,
    gr: Rc<derived::inductive::GenRecursor>,
    core: Rc<RecCore>,
}

/// **Why the general inductive path declined a declaration.**
///
/// Every one of these leaves the constant opaque, exactly as before the path
/// existed, and an opaque constant produces counted gaps. The cardinal
/// property of the whole boundary is that **there is no code path from a
/// decline to a `Thm`** — so this enum is a taxonomy of *what was not
/// attempted*, never of what was attempted and got the wrong answer.
///
/// The first four are read straight off `InductiveData`. They are not
/// defensive boilerplate: [`Decline::Indices`] is the whole of the scope
/// enforcement for indexed families, because indices are *unrepresentable* in
/// [`derived::inductive::DeclSpec`] and there is therefore no derived-side
/// backstop. `RBTree` (`042`/`068`/`077`, `numIndices: 2`) declines here.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Decline {
    /// An indexed family. `DeclSpec` has no field for indices and adding one
    /// would be a different construction — it needs the equality type first.
    Indices,
    /// A `mutual … end` block.
    Mutual,
    /// A nested inductive: a recursive occurrence under another type former,
    /// whose fibre summand is a genuine telescope rather than `finord(m)`.
    Nested,
    /// No constructors — Lean's `Empty`.
    /// [`derived::inductive::GenRecursor::build`] declines it too.
    NoCtors,
    /// The declaration's **own** resultant level is not provably nonzero, so
    /// Lean's eliminator trichotomy does not put it in class (T). Building a
    /// W-type for a possibly-`Prop` inductive even at a `Type` instantiation
    /// would make the branch per-instantiation, which is the design error
    /// `LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.3 closes.
    SortAmbiguous,
    /// The declaration has parameters. The *spec* is general in `np`; what is
    /// not yet wired is the **Lean-facing** layer for `np > 0` — the type
    /// former becomes a nest of `np` lambda graphs and every constructor's
    /// premises acquire the parameter spine. Recorded rather than attempted:
    /// see the report at the end of this file.
    Params,
    /// A recursive argument that is **function-typed** — a `Π` whose ultimate
    /// codomain is the inductive (`116_rtreeRecReduction`'s
    /// `RTree.node : Bool → RTree`, `Acc.intro`). `CtorSpec::recs` is a
    /// `usize`, which is exactly the assumption that this does not happen.
    FunRecArg,
    /// A field type that mentions the declaration itself in a position that is
    /// not a plain recursive argument. Interpreting it would recurse into the
    /// declaration being built.
    SelfMention,
    /// A later field's type depends on an **earlier recursive** field. `βⱼ` has
    /// arity `np + j` — parameters plus the earlier *non-recursive* arguments —
    /// so nothing else is available to substitute. The decline is automatic
    /// (the recursive field's variable is in no abstraction list and
    /// `define_abbrev` refuses); this counts it distinctly rather than letting
    /// it fall into a generic failure.
    RecFieldDep,
    /// A field's type mentions an ω-vocabulary **level variable**, and the
    /// `βⱼ` abbreviation cannot name it: `βᵢ` has arity `np + i` by the
    /// [`derived::inductive::DeclSpec`] well-formedness contract, so
    /// `define_abbrev`'s free-variable guard refuses the body. This is
    /// `LEVELPOLY.md` §5.4 blocker 2b — the machine-contract extension — and
    /// counting it under [`Decline::RecFieldDep`] mislabelled 76 staged rows
    /// until it got its own reason.
    LevelVar,
    /// The walk did not find the shape it expected: a missing binder, a
    /// codomain that is not the declaration at its own parameters, a
    /// constructor index out of range, a level arity mismatch.
    Shape,
    /// The builder re-entered itself on the same declaration.
    Reentrant,
    /// The shared W-type machinery or the [`derived::inductive::Machine`] over
    /// it could not be built.
    Machinery,
    /// [`derived::inductive::Inductive::build`] declined the spec — the
    /// derived layer's own half of the positive scope check.
    Build,
    /// **A constructor of the declaration is not in the environment yet.**
    ///
    /// Not a scope decline: while the checker is checking `T.mk` itself, the
    /// environment is limited to the declarations *before* it, so `T` resolves
    /// and `T.mk` does not. The three hand-written recognisers have exactly the
    /// same exposure (`enum_arity` fails its `get_constructor` there too) and
    /// have always simply left the constant opaque for that one declaration.
    ///
    /// It is counted separately, and — unlike every other variant — it is
    /// **not memoised**: the same declaration is perfectly translatable at the
    /// next one, and caching this answer would make a transient
    /// environment-visibility miss permanent for the whole thread.
    Unavailable,
    /// The `T`-policy has no target to offer at this declaration — or, today,
    /// the one it offers is policy 2, whose `HYP` is genuinely conditional and
    /// is not yet dischargeable. See [`TgBackend::gen_rec_bottom`].
    TPolicy,
}

const N_DECLINE: usize = 16;

impl Decline {
    const fn name(self) -> &'static str {
        match self {
            Decline::Indices => "…declined: indices",
            Decline::Mutual => "…declined: mutual block",
            Decline::Nested => "…declined: nested inductive",
            Decline::NoCtors => "…declined: no constructors",
            Decline::SortAmbiguous => "…declined: sort-ambiguous or Prop (class S/P)",
            Decline::Params => "…declined: the parameter nest refused",
            Decline::FunRecArg => "…declined: function-typed recursive argument",
            Decline::SelfMention => "…declined: field type mentions the declaration",
            Decline::RecFieldDep => "…declined: field type depends on a recursive field",
            Decline::LevelVar => "…declined: field type at a variable level (βⱼ awaits the ω-prefix)",
            Decline::Shape => "…declined: arity/shape mismatch",
            Decline::Reentrant => "…declined: re-entrant",
            Decline::Machinery => "…declined: W-type machinery unavailable",
            Decline::Build => "…declined: the derived layer refused the spec",
            Decline::Unavailable => "…declined: constructors not yet in the environment",
            Decline::TPolicy => "…declined (recursor): T-policy 2/3, HYP not dischargeable",
        }
    }
    const ALL: [Decline; N_DECLINE] = [
        Decline::Indices,
        Decline::Mutual,
        Decline::Nested,
        Decline::NoCtors,
        Decline::SortAmbiguous,
        Decline::Params,
        Decline::FunRecArg,
        Decline::SelfMention,
        Decline::RecFieldDep,
        Decline::LevelVar,
        Decline::Shape,
        Decline::Reentrant,
        Decline::Machinery,
        Decline::Build,
        Decline::Unavailable,
        Decline::TPolicy,
    ];
}

/// What [`TgBackend::walk_spec`] read off one declaration.
///
/// Not stored: it is the *input* to `Inductive::build` and to the Lean-facing
/// layer, and what survives is [`GenInd`].
struct SpecWalk {
    /// The kernel variables the `np` parameter binders were opened at.
    param_vars: Vec<FreeVar>,
    /// The interpretations of the parameter binder types — the domains of the
    /// Lean-facing type former's nest.
    param_doms: Vec<Term>,
    /// One per constructor, indexed by `ctor_idx`.
    ctors: Vec<CtorWalk>,
}

/// One constructor, as the walk read it.
struct CtorWalk {
    /// The field mask in Lean **declared** order.
    order: Vec<Slot>,
    /// The kernel variable each field binder was opened at, declared order.
    field_vars: Vec<FreeVar>,
    /// Each field's *domain*, declared order.
    field_doms: Vec<FieldDom>,
    /// The interpreted plain-field types, in plain order.
    beta_bodies: Vec<Term>,
    /// How many fields are recursive.
    recs: usize,
}

/// A constructor field's domain: either the interpretation of its Lean type
/// together with the `βⱼ` symbol abbreviating it, or the declaration itself.
enum FieldDom {
    /// A non-recursive field: `(⟦its type⟧, βⱼ, ⊢ ∀x⃗. βⱼ(x⃗) = ⟦its type⟧)`.
    Plain(Term, FnSym, Thm),
    /// A recursive field, whose type is the declaration at its own parameters.
    Rec,
}

static DECLINES: [std::sync::atomic::AtomicU64; N_DECLINE] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_DECLINE];
/// Distinct `(declaration, levels)` pairs the general path translated.
static GEN_BUILT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Cache hits whose recorded `βⱼ` bodies did not survive re-interpretation.
static GEN_GUARD_MISS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Constructor terms and typing rules the general path registered.
static GEN_CTORS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Recursor nests bottoming out in [`RecBottom::General`].
static GEN_RECS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Cached general recursors whose carrier is not the one this backend rebuilt.
static GEN_REC_GUARD_MISS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// ι sites the general rule computed — the deliverable, counted.
static GEN_IOTAS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);



fn note_decline(d: Decline) { DECLINES[d as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// What the general inductive path did, or the empty string if it was never
/// consulted.
fn gen_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let built = GEN_BUILT.load(Relaxed);
    let declined: u64 = DECLINES.iter().map(|c| c.load(Relaxed)).sum();
    if built == 0 && declined == 0 {
        return String::new()
    }
    let width = Decline::ALL.iter().map(|d| d.name().len()).max().unwrap_or(24) + 6;
    let mut s = String::from("  the general inductive path (derived::inductive):\n");
    let row = |s: &mut String, label: &str, n: u64| {
        s.push_str(&format!("    {:<width$}  {n:>10}\n", label));
    };
    row(&mut s, "declarations translated", built);
    row(&mut s, "constructors given a term and a typing rule", GEN_CTORS.load(Relaxed));
    row(&mut s, "recursors given a general nest", GEN_RECS.load(Relaxed));
    row(&mut s, "cached specs declined: βⱼ bodies not canonical", GEN_GUARD_MISS.load(Relaxed));
    row(
        &mut s,
        "cached recursors declined: not over this carrier",
        GEN_REC_GUARD_MISS.load(Relaxed),
    );
    row(&mut s, "ι sites the general rule computed", GEN_IOTAS.load(Relaxed));
    for d in Decline::ALL {
        let n = DECLINES[d as usize].load(Relaxed);
        if n > 0 {
            row(&mut s, d.name(), n);
        }
    }
    s
}

impl<'x, 't: 'x, 'p: 't> TgBackend<'x, 't, 'p> {
    /// A backend for one declaration, over the thread's shared signature.
    pub fn new(decls: &'x crate::env::Env<'x, 't>) -> Self {
        let pre = prelude();
        let shared = shared(&pre);
        let (syms, core) = {
            let sh = shared.borrow();
            (sh.syms, sh.core.clone())
        };
        let x_canon = core.x_canon;
        TgBackend {
            shared,
            core,
            pre,
            decls,
            const_defs: HashMap::new(),
            abbrev_defs: HashMap::new(),
            let_defs: HashMap::new(),
            syms,
            exprs: HashMap::new(),
            exprs_rev: HashMap::new(),
            levels: HashMap::new(),
            level_reps: Vec::new(),
            level_canon: HashMap::new(),
            consts: HashMap::new(),
            locals: HashMap::new(),
            params: HashMap::new(),
            param_omegas: HashMap::new(),
            idxs: HashMap::new(),
            parts: HashMap::new(),
            lam_sites: HashMap::new(),
            pi_sites: HashMap::new(),
            prop_sites: HashMap::new(),
            undet_sites: HashMap::new(),
            prop_lam_sites: HashMap::new(),
            props: HashMap::new(),
            terms: HashMap::new(),
            exposed_sorts: HashMap::new(),
            open_levels: HashMap::new(),
            x_canon,
            has_types: HashMap::new(),
            const_active: Vec::new(),
            ht_active: Vec::new(),
            points: HashMap::new(),
            syn_types: HashMap::new(),
            exposed: HashMap::new(),
            typeables: HashMap::new(),
            ind_mems: HashMap::new(),
            ind_ty_mems: HashMap::new(),
            ind_syms: HashMap::new(),
            ctor_rules: HashMap::new(),
            gen_ctor_bridges: HashMap::new(),
            gen_consts: HashMap::new(),
            gen_ty_nests: HashMap::new(),
            gen_inds: HashMap::new(),
            rec_nests: HashMap::new(),
            hoisted: HashMap::new(),
            spec_active: Vec::new(),
            spec_unavailable: false,
            _marker: PhantomData,
        }
    }

    /// The shared signature, for the duration of one statement.
    ///
    /// Every use is deliberately short-lived: holding this across a call that
    /// itself reaches the shared state would panic on the re-entrant borrow.
    fn env_mut(&self) -> std::cell::RefMut<'_, Env> { self.core.env_mut() }

    /// Build `f(args)` and remember its shape, so that [`Self::skeleton`] can
    /// take it apart again later.
    fn mk(&mut self, f: FnSym, args: Vec<Term>) -> Term { record(&mut self.parts, f, args) }

    /// Accept `eq` as a proof that `redex` and `reduct` are equal, but only
    /// after checking it really is that equation. Every rule that concludes
    /// something about two specific terms goes through this.
    fn check_against(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        eq: Thm,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
        what: &'static str,
    ) -> TgCert {
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        // `derived::establishes`, not a bare `concl()` comparison: a theorem
        // establishes its conclusion only where its `Γ` holds, and a certificate
        // handed back from here is read as an answer with no context attached.
        if derived::establishes(&eq, &kernel::Formula::eq(lhs, rhs)) {
            self.proved(eq)
        } else if what == "zeta" {
            self.note_admit("zeta: derived equation does not match the reduction")
        } else {
            self.note_admit("derived equation does not match the reduction")
        }
    }

    /// Wrap a derived theorem, tallying it for the coverage report.
    fn proved(&mut self, t: Thm) -> TgCert {
        note_proved();
        TgCert::Proved(t)
    }

    /// Wrap a derivation together with whatever it still assumes.
    ///
    /// The single place a [`TgCert::Conditional`] is built. `CondEq`'s
    /// constructor has already checked that the theorem is literally
    /// `⊢ conj(hyps) → (a = b)`, so the assumptions recorded here are the
    /// theorem's real antecedents and not a label attached to it.
    ///
    /// It is also where a **guarded family** of typing obligations is discharged
    /// ([`Self::discharge_families`]): being the one funnel, it is the one place
    /// that sees every conditional derivation this backend hands back, whichever
    /// rule built it, and a certificate that leaves here unconditional is one the
    /// escape ledger never has to count.
    fn cert(&mut self, ctx: &mut TcCtx<'t, 'p>, c: CondEq) -> TgCert {
        let c = if c.hyps.is_empty() { c } else { self.discharge_families(ctx, c) };
        if c.hyps.is_empty() {
            return self.proved(c.thm)
        }
        note_proved();
        note_conditional();
        MAX_ASSUMED.fetch_max(c.hyps.len() as u64, std::sync::atomic::Ordering::Relaxed);
        TgCert::Conditional { thm: c.thm, hyps: c.hyps }
    }

    /// Take a certificate handed to a rule, as a conditional equation.
    ///
    /// Every [`Certifier`] method that receives certificates calls this on each
    /// of them, whatever it then does with them — that is what keeps the escape
    /// ledger exact (see [`escape_report`]): a conditional certificate is
    /// accounted for the moment a rule takes it, so the ones left over are
    /// exactly the copies the checker consumed as an *answer*.
    fn consume(&mut self, c: &TgCert) -> Option<CondEq> {
        match c {
            TgCert::Proved(t) => CondEq::plain(t.clone()),
            TgCert::Conditional { thm, hyps } => {
                note_consumed();
                CondEq::new(thm.clone(), hyps.clone())
            }
            TgCert::Admitted(_) => None,
        }
    }

    /// Transitivity, merging the two derivations' assumptions.
    fn ceq_trans(&mut self, ab: &CondEq, bc: &CondEq) -> Option<CondEq> {
        let hyps = merge_hyps(&ab.hyps, &bc.hyps);
        let h = conj_of(&hyps);
        let x = reassume(&ab.thm, &ab.hyps, &hyps)?;
        let y = reassume(&bc.thm, &bc.hyps, &hyps)?;
        CondEq::new(u_eq_trans(&mut self.env_mut(), &x, &y, h.as_ref())?, hyps)
    }

    /// Symmetry, keeping the assumptions.
    fn ceq_symm(&mut self, ab: &CondEq) -> Option<CondEq> {
        let h = conj_of(&ab.hyps);
        CondEq::new(u_eq_symm(&mut self.env_mut(), &ab.thm, h.as_ref())?, ab.hyps.clone())
    }

    /// Congruence over `f`, merging every argument's assumptions.
    fn ceq_congr(&mut self, f: FnSym, cs: &[CondEq]) -> Option<CondEq> {
        let mut hyps: Vec<Formula> = Vec::new();
        for c in cs {
            hyps = merge_hyps(&hyps, &c.hyps);
        }
        let h = conj_of(&hyps);
        let mut lifted = Vec::with_capacity(cs.len());
        for c in cs {
            lifted.push(reassume(&c.thm, &c.hyps, &hyps)?);
        }
        CondEq::new(u_congr(&mut self.env_mut(), f, &lifted, h.as_ref())?, hyps)
    }

    /// `⊢ H → ⟦e⟧ = •` — **§6.2's soundness clause for proofs, derived rather
    /// than assumed.**
    ///
    /// Carneiro's Theorem 6.7: if `Γ ⊢ e : α` and `lvl(Γ ⊢ α) = 0` then
    /// `⟦Γ ⊢ e⟧γ = •`. For a `λ` and for an application the interpretation *is*
    /// `•` by construction — that is [`Self::term_clause`]'s two splits — and
    /// this is the residue. A proof that is neither, a **variable** above all,
    /// interprets to itself: §6.2 sends `x` to `πᵢ(γ)`, and it is `•` only
    /// because `γ` ranges over `⟦Γ⟧`. This kernel has no `γ`; what stands in for
    /// it is the ambient assumptions, so the equation is *conditional* on them,
    /// and that is exactly what comes back.
    ///
    /// Two premises, both of them things the backend already knows how to get:
    ///
    /// * `⟦e⟧ ∈ ⟦α⟧` — for a context local, the local's own typing, acquired as
    ///   an antecedent by [`Self::has_type_local`];
    /// * `⟦α⟧ ∈ U₀` — for a `∀`, [`Self::prop_in_u0`]; for a local of type
    ///   `Prop`, again the local's own typing.
    ///
    /// [`derived::tower::Tower::u0_subsingleton`] — `∀p ∀x. ((p ∈ U₀ ∧ x ∈ p) →
    /// x = •)`, itself proved from `U₀ = {0,1}` and `unit_eta` with no axiom —
    /// closes it. Nothing is assumed: the instantiated conclusion is compared
    /// against `⟦e⟧ = •` before it is handed back, and whatever the two premises
    /// rest on rides out with the result, so an equation that really does depend
    /// on the context says so and the escape ledger counts it.
    fn point_of_proof(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, from: Pop) -> Option<CondEq> {
        let te = self.interp(ctx, e);
        let point = self.pre.point();
        // The two split clauses: nothing to derive.
        if te == point {
            note_pop(Pop::Split);
            return Some(CondEq::refl(point))
        }
        let hit = self.points.get(&e).cloned();
        let out = match hit {
            Some(r) => {
                note_pop(Pop::Memo);
                r
            }
            None => {
                let r = self.derive_point_of_proof(ctx, e, &te, from);
                self.remember_point(e, &r);
                r
            }
        };
        let (thm, hyps) = out?;
        CondEq::new(thm, hyps)
    }

    /// [`Self::point_of_proof`] with the two premises **handed in**.
    ///
    /// This is the same derivation as [`Self::derive_point_of_proof`] and the
    /// same guard; what is different is where `⟦e⟧ ∈ ⟦α⟧` and `⟦α⟧ ∈ U₀` come
    /// from. The searching version reconstructs both — the first by
    /// [`Self::syn_type`]'s delta-only re-walk and two `has_type_a` queries —
    /// after the checker has just established them and dropped them. Here they
    /// arrive.
    ///
    /// The fast paths above the derivation are kept because they are cheaper
    /// than it, not because the premises might be missing: a proof that took one
    /// of §6.2's split clauses interprets to `•` outright, and a defined
    /// constant standing for a proof is settled by its own defining equation.
    ///
    /// `from` names the rule that asked, as it does on [`Self::point_of_proof`],
    /// and for the same reason: this entry point has acquired more than one
    /// caller, and "the threaded route was taken N times" is not a useful number
    /// unless it can be split by who took it.
    fn point_of_proof_from(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        mem: &TgTyping,
        prop: &TgTyping,
        from: Pop,
    ) -> Option<CondEq> {
        let te = self.interp(ctx, e);
        let point = self.pre.point();
        if te == point {
            note_pop(Pop::Split);
            return Some(CondEq::refl(point))
        }
        // A memoised **success** is as good as a fresh derivation and cheaper.
        // A memoised *failure* is not: it records that the search route came up
        // empty, and the whole point of this entry point is that it does not
        // depend on that route succeeding. Falling through on `None` is what
        // keeps a threaded derivation from being lost to a negative cache
        // written by a weaker path.
        if let Some(Some((thm, hyps))) = self.points.get(&e).cloned() {
            note_pop(Pop::Memo);
            return CondEq::new(thm, hyps)
        }
        if let Some(t) = self.unfolds_to(&te, &point) {
            note_pop(Pop::Unfold);
            let out = Some((t, Vec::new()));
            self.remember_point(e, &out);
            let (thm, hyps) = out?;
            return CondEq::new(thm, hyps)
        }
        note_pop(Pop::Threaded);
        note_pop(from);
        let tty = self.interp(ctx, ty);
        // Which premise is missing is the whole diagnostic value of this path:
        // a hole here is a place *inference* could not justify its own result,
        // and it says which later stage owes the fix.
        let (mem, prop) = (Self::ty_parts(mem), Self::ty_parts(prop));
        if mem.is_none() {
            note_pop(Pop::NoMem);
        }
        if prop.is_none() {
            note_pop(Pop::NoProp);
        }
        let out = match (mem, prop) {
            (Some((me, hs_e)), Some((mp, hs_p))) => {
                let r = self.point_from_premises(&te, &tty, (&me, &hs_e), (&mp, &hs_p));
                if r.is_none() {
                    note_pop(Pop::Refused);
                }
                r
            }
            _ => None,
        };
        note_pop(if out.is_some() { Pop::Derived } else { Pop::Failed });
        self.remember_point(e, &out);
        let (thm, hyps) = out?;
        CondEq::new(thm, hyps)
    }

    /// Give the side whose `⟦α⟧ ∈ U₀` is a hole the other side's, across the
    /// equation the checker has just proved between the two propositions.
    ///
    /// Both propositions are definitionally equal — that is the side condition
    /// proof irrelevance rests on — so their interpretations are equal and a
    /// membership about one is a membership about the other. This is the only
    /// work `ty_eq` is put to, and it is real work: the two `∈ U₀` witnesses
    /// come from inference at *different* expressions, and one being derivable
    /// says nothing about the other.
    ///
    /// The identity when both sides have evidence, when neither has, or when
    /// the equation is not about these two types.
    fn share_prop(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a_ty: ExprPtr<'t>,
        b_ty: ExprPtr<'t>,
        a_prop: TgTyping,
        b_prop: TgTyping,
        ty_eq: Option<&CondEq>,
    ) -> (TgTyping, TgTyping) {
        if a_prop.is_gap() == b_prop.is_gap() {
            return (a_prop, b_prop)
        }
        let Some(ty_eq) = ty_eq else { return (a_prop, b_prop) };
        let (ta, tb) = (self.interp(ctx, a_ty), self.interp(ctx, b_ty));
        let u0 = self.pre.u0();
        if a_prop.is_gap() {
            // `⟦b_ty⟧ ∈ U₀` is what exists; the equation runs the other way.
            let Some(back) = self.ceq_symm(ty_eq) else { return (a_prop, b_prop) };
            match self.carry_mem(&b_prop, &tb, &ta, &u0, &back) {
                Some(filled) => {
                    note_pop(Pop::Shared);
                    (filled, b_prop)
                }
                None => (a_prop, b_prop),
            }
        } else {
            match self.carry_mem(&a_prop, &ta, &tb, &u0, ty_eq) {
                Some(filled) => {
                    note_pop(Pop::Shared);
                    (a_prop, filled)
                }
                None => (a_prop, b_prop),
            }
        }
    }

    /// `⊢ H → to ∈ set` from `⊢ H' → from ∈ set` and `⊢ H'' → from = to`, by
    /// Leibniz on the subject. `None` if the equation is not about `from` and
    /// `to`, or the premise is a hole.
    fn carry_mem(
        &mut self,
        mem: &TgTyping,
        from: &Term,
        to: &Term,
        set: &Term,
        eq: &CondEq,
    ) -> Option<TgTyping> {
        let (thm, hs) = Self::ty_parts(mem)?;
        eq.proves(from, to).then_some(())?;
        let hyps = merge_hyps(&hs, &eq.hyps);
        let h = conj_of(&hyps);
        let lifted = reassume(&thm, &hs, &hyps)?;
        let e = reassume(&eq.thm, &eq.hyps, &hyps)?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(from.clone(), to.clone(), w, Formula::mem(Term::var(w), set.clone()));
        let step = u_mp(&u_a1i(&leib, h.as_ref()), &e, h.as_ref())?;
        let out = u_mp(&step, &lifted, h.as_ref())?;
        // `typing` answers a *gap* when what was built is not the membership
        // claimed. Handing that back would swap one hole for another and report
        // a rule as having fired, so it is `None` here — the guard's verdict,
        // not a certificate shaped like one.
        let out = self.typing(crate::certify::TyGap::Conv, to, set, out, hyps);
        (!out.is_gap()).then_some(out)
    }

    /// File a `⟦e⟧ = •` result in the memo.
    ///
    /// **Never a theorem that stands under kernel hypotheses.** The memo is
    /// keyed on the `ExprPtr` alone and lives for a whole declaration, so a
    /// `Γ ⊢ ⟦e⟧ = •` filed here would be handed to a later caller under a
    /// context that need not satisfy `Γ` — the same hazard
    /// [`crate::certify::hypothesis_free`] describes for the reduct memos, at
    /// the store that had no guard. A *conditional* result is still filed: its
    /// assumptions are antecedents inside the formula, so they travel with it.
    ///
    /// Today no derivation in this backend acquires a kernel hypothesis, so the
    /// guard never fires; it is here so that it fails closed when one does.
    fn remember_point(&mut self, e: ExprPtr<'t>, r: &Option<(Thm, Vec<Formula>)>) {
        if r.as_ref().is_some_and(|(t, _)| !t.hyps().is_empty()) {
            return
        }
        self.points.insert(e, r.clone());
    }

    /// [`Self::point_of_proof`] without the memo or the `•` fast path.
    fn derive_point_of_proof(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        te: &Term,
        from: Pop,
    ) -> Option<(Thm, Vec<Formula>)> {
        // A **defined constant** standing for a proof. §6.2 sends a constant to
        // its value's interpretation and the value, being a proof, to `•`; this
        // module inserts an abbreviation symbol in between so that the
        // interpretation stays injective on constants, and the abbreviation's
        // own defining equation is the whole derivation. Unconditional, and
        // cheaper than the typing route below.
        let point = self.pre.point();
        if let Some(t) = self.unfolds_to(te, &point) {
            note_pop(Pop::Unfold);
            return Some((t, Vec::new()))
        }
        note_pop(Pop::Searched);
        note_pop(from);
        let ty = self.syn_type(ctx, e)?;
        let tty = self.interp(ctx, ty);
        let u0 = self.pre.u0();
        let (mem_e, hs_e) = self.has_type_a(ctx, e, &tty, &[], 0)?;
        let (mem_p, hs_p) = self.has_type_a(ctx, ty, &u0, &[], 0)?;
        let out = self.point_from_premises(te, &tty, (&mem_e, &hs_e), (&mem_p, &hs_p));
        note_pop(if out.is_some() { Pop::Derived } else { Pop::Failed });
        out
    }

    /// `⊢ H → ⟦e⟧ = •` from the two premises `⟦e⟧ ∈ ⟦α⟧` and `⟦α⟧ ∈ U₀`,
    /// however they were obtained.
    ///
    /// This is the whole of the derivation; everything above it is the question
    /// of where the two premises come from. Factored out because there are two
    /// answers to that — the checker hands them over
    /// ([`Certifier::proof_irrel`]), or they are searched for — and only the
    /// first is the design's.
    fn point_from_premises(
        &mut self,
        te: &Term,
        tty: &Term,
        (mem_e, hs_e): (&Thm, &[Formula]),
        (mem_p, hs_p): (&Thm, &[Formula]),
    ) -> Option<(Thm, Vec<Formula>)> {
        let point = self.pre.point();
        let hyps = merge_hyps(hs_e, hs_p);
        let h = conj_of(&hyps);
        let me = reassume(mem_e, hs_e, &hyps)?;
        let mp = reassume(mem_p, hs_p, &hyps)?;
        // The premise is `(α ∈ U₀ ∧ e ∈ α)`, in that order.
        let both = u_and_intro(&mp, &me, h.as_ref())?;
        let lem = self.pre.tower.u0_subsingleton.clone();
        let inst = derived::inst_all(&lem, &[tty.clone(), te.clone()])?;
        let out = u_mp(&u_a1i(&inst, h.as_ref()), &both, h.as_ref())?;
        // The guard: only this equation, about this term, counts.
        (u_concl(&out, h.as_ref())? == Formula::eq(te.clone(), point)).then_some(())?;
        Some((out, hyps))
    }

    /// `⊢ H → ⟦a⟧ = ⟦b⟧`, **because both sides are proofs**.
    ///
    /// Proof irrelevance falling out of the model rather than being assumed: a
    /// proposition denotes a subset of `{•}` and so has no two distinct
    /// inhabitants. Where both sides took a split clause the two interpretations
    /// are literally `•` and the equation is reflexivity, with no assumption at
    /// all; otherwise it is [`Self::point_of_proof`] on each side, chained.
    ///
    /// Guarded: the derivation is compared against `⟦a⟧ = ⟦b⟧` before it is
    /// returned, so the caller cannot be handed a theorem about other terms.
    fn proof_eq(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, from: Pop) -> Option<CondEq> {
        (self.term_clause(ctx, a) == Clause::Prop).then_some(())?;
        (self.term_clause(ctx, b) == Clause::Prop).then_some(())?;
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            return Some(CondEq::refl(ta))
        }
        let ca = self.point_of_proof(ctx, a, from)?;
        let cb = self.point_of_proof(ctx, b, from)?;
        let cb = self.ceq_symm(&cb)?;
        let out = self.ceq_trans(&ca, &cb)?;
        out.proves(&ta, &tb).then_some(out)
    }

    fn note_admit(&mut self, reason: &'static str) -> TgCert {
        // Tallied straight into the run totals rather than buffered and merged
        // on `Drop`: a `Drop` impl on the backend would make `TypeChecker`'s
        // borrow of its context live to the end of scope, which breaks callers
        // that legitimately reuse the context afterwards.
        merge_one(reason);
        TgCert::Admitted(reason)
    }

    /// A 0-ary "numeral" term standing for an index. These are opaque tags, not
    /// the primitive `ℕ` of milestone 4.
    fn idx_term(&mut self, i: u64) -> Term {
        if let Some(t) = self.idxs.get(&i) {
            return t.clone()
        }
        // Encoded as `idx` applied to itself i times over a base would be
        // linear in i; instead each distinct index gets its own nullary symbol,
        // which keeps interpretation O(1) per node.
        //
        // The symbol is shared across the thread rather than minted per
        // backend. A de Bruijn index carries nothing but its identity, and a
        // per-backend symbol made `⟦#0⟧` — and hence the interpretation of
        // *every value with a binder in it* — differ between one declaration's
        // backend and the next. That was measured: it was why 557 of the
        // constants with values could not use the shared symbol for their
        // definition, and so why a typing stored while checking one declaration
        // was about terms no later declaration ever built.
        let existing = self.shared.borrow().idx_syms.get(&i).copied();
        let s = match existing {
            Some(s) => s,
            None => {
                let s = self.env_mut().declare(0);
                self.shared.borrow_mut().idx_syms.insert(i, s);
                s
            }
        };
        let inner = self.mk(s, vec![]);
        let t = self.mk(self.syms.idx, vec![inner]);
        self.idxs.insert(i, t.clone());
        t
    }

    /// Interpret a universe level.
    ///
    /// The level is *simplified first*. The checker decides level equality with
    /// its own algebra (`eq_antisymm`), under which e.g. `imax 1 1` and `1` are
    /// equal; interpreting them naively would give syntactically different terms
    /// and turn a settled equality into an unprovable one. Normalising to the
    /// checker's canonical form keeps the two views in step, so equal levels map
    /// to identical terms and reflexivity discharges them.
    /// The canonical representative of `l`'s level-equivalence class.
    ///
    /// `simplify` is not a normal form: it settles neither commutativity,
    /// associativity, idempotence nor absorption of `max`, so `max u v` and
    /// `max v u` remain syntactically different while the checker rightly calls
    /// them equal. Rather than reimplement level algebra — `CLAUDE.md` puts
    /// levels in the translator, not the kernel — reuse the checker's own
    /// decision procedure and keep one representative per class.
    ///
    /// The scan is linear in the number of distinct classes, which is bounded by
    /// the development's universe vocabulary (tens, in practice) rather than its
    /// size.
    fn canon_level(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> LevelPtr<'t> {
        // Under σ: this backend interprets one *instantiation* of a
        // declaration, and at a ground one every level here is a numeral.
        // See `TcCtx::under_sigma` and `crate::instantiations`.
        let l = ctx.under_sigma(l);
        if let Some(r) = self.level_canon.get(&l) {
            return *r
        }
        for rep in self.level_reps.clone() {
            if ctx.eq_antisymm(l, rep) {
                self.level_canon.insert(l, rep);
                return rep
            }
        }
        self.level_reps.push(l);
        self.level_canon.insert(l, l);
        l
    }

    /// Interpret a level structurally.
    ///
    /// Deliberately does **not** canonicalise: canonicalising here and then
    /// decomposing the representative can hand a sub-level back the whole level
    /// (absorption maps `succ u` to `max u (succ u)`, whose own sub-level is
    /// `succ u`), and the recursion never terminates. Canonicalisation happens
    /// once, at the dispatch point in [`Self::interp_sort`], where the shape
    /// choice actually matters.
    fn interp_level(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> Term {
        // Under σ, which is also what makes the `Param` arm below rare: at a
        // ground instantiation the declaration's own parameters are gone, so
        // the only parameters reaching it are the ones no σ names — the
        // eliminator universe an inductive's recursor introduces, and every
        // level while an inductive block is being checked.
        let l = ctx.under_sigma(l);
        if let Some(t) = self.levels.get(&l) {
            return t.clone()
        }
        let t = match ctx.read_level(l) {
            Level::Zero => self.mk(self.syms.lzero, vec![]),
            Level::Succ(a, _) => {
                let a = self.interp_level(ctx, a);
                self.mk(self.syms.lsucc, vec![a])
            }
            Level::Max(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                self.mk(self.syms.lmax, vec![a, b])
            }
            Level::IMax(a, b, _) => {
                let (a, b) = (self.interp_level(ctx, a), self.interp_level(ctx, b));
                self.mk(self.syms.limax, vec![a, b])
            }
            Level::Param(n, _) => {
                if let Some(t) = self.params.get(&n) {
                    t.clone()
                } else {
                    // One symbol per parameter *name*, shared across
                    // declarations: see `Shared::param_syms`.
                    let shared = self.name_key(n).and_then(|k| self.shared.borrow().param_syms.get(&k).cloned());
                    let t = match shared {
                        Some(t) => t,
                        None => {
                            let s = self.env_mut().declare(0);
                            let t = self.mk(s, vec![]);
                            if let Some(k) = self.name_key(n) {
                                self.shared.borrow_mut().param_syms.insert(k, t.clone());
                            }
                            t
                        }
                    };
                    self.params.insert(n, t.clone());
                    t
                }
            }
        };
        self.levels.insert(l, t.clone());
        t
    }

    /// `⟦Sort l⟧`, climbing [`derived::tower`]'s universe tower.
    ///
    /// ```text
    /// ⟦Sort 0⟧     := U₀ = {0,1}       — Prop, the truth values
    /// ⟦Sort 1⟧     := U₁ = U(ω)
    /// ⟦Sort (l+1)⟧ := U(⟦Sort l⟧)      for l ≥ 1
    /// ```
    ///
    /// Levels that are neither zero nor a successor (`max`, `imax`, a parameter)
    /// fall back to the opaque `sort` symbol: nothing is known about where they
    /// sit, which is honest, and the encoding stays injective on simplified
    /// levels so the `sort` rule is unaffected.
    ///
    /// # Level 0 is a term with properties, not a nullary symbol
    ///
    /// `⟦Sort 0⟧` used to be `self.syms.sort0`, an opaque constant with no
    /// axioms — under which `⟦Prop⟧ := ∅` is a consistent extension and
    /// `derived::anchor::falsity`'s theorems about `{0,1}` said nothing about
    /// anything the backend produced. It is now the tower's `U₀`, so
    /// `⊢ [φ] ∈ ⟦Prop⟧`, `⊢ ⟦False⟧ ∈ ⟦Prop⟧` and proof irrelevance are all
    /// facts about the interpretation.
    ///
    /// # Why level 1 is seeded at `ω` and not at `U₀`
    ///
    /// `U₀ = {0,1}` is hereditarily finite, and `V_ω` satisfies every clause of
    /// `derived::universe::is_universe`, so `U(U₀) ⊆ V_ω` — and every member of
    /// `V_ω` is finite. A tower seeded at `U₀` would make `⟦Type 0⟧` a set with
    /// **no infinite member at all**, while `⟦N⟧` is infinite; the seed is
    /// therefore `ω`, which is the thesis's own two-clause definition (§6.2
    /// fixes `U₀ = {∅,{•}}` separately and never defines `U_{n+1}` from `Uₙ`).
    /// See [`derived::tower`] for the countermodel in full.
    ///
    /// The price is that `⟦Sort 0⟧ ∈ ⟦Sort 1⟧` stops being an instance of
    /// `⊢ ∀x. x ∈ U(x)`; [`Prelude::u0_in_u1`] is the theorem that replaces it,
    /// and [`Self::domain_premise`] is where it is used.
    fn interp_sort(&mut self, ctx: &mut TcCtx<'t, 'p>, level: LevelPtr<'t>) -> Term {
        // Dispatch on the *canonical representative* of the level, not on its
        // raw shape. Otherwise `Sort (max u u)` takes the opaque branch while
        // the equal `Sort u` takes the universe-tower branch, and two equal
        // levels yield different terms — which is what made idempotence and
        // absorption unprovable.
        let l = self.canon_level(ctx, level);
        // `explore/level-poly-target`: a level the σ-schedule cannot ground is
        // interpreted as `srt(ℓ̂)` — a term with facts — when the apparatus is
        // enabled. Dispatching on the canonical representative keeps `⟦·⟧` a
        // function exactly as the ground path does, and a ground level never
        // takes this branch, so the two vocabularies cannot collide.
        if levelpoly_enabled() && !self.level_ground(ctx, l) {
            if let Some(t) = self.interp_sort_poly(ctx, l) {
                return t
            }
        }
        match ctx.read_level(l) {
            Level::Zero => self.pre.u0(),
            Level::Succ(a, _) => {
                let below = self.interp_sort(ctx, a);
                // `Succ(Zero)`, i.e. `Type 0`, is `U(ω)` — not `U(U₀)`. Tested
                // on the *interpretation* of the sub-level rather than on its
                // syntax, so that a level equal to `0` by any route lands here
                // too and `⟦·⟧` stays a function.
                let below = if below == self.pre.u0() { self.pre.tower.omega() } else { below };
                self.mk(self.pre.u_sym, vec![below])
            }
            _ => {
                let lt = self.interp_level(ctx, l);
                self.mk(self.syms.sort, vec![lt])
            }
        }
    }

    fn interp_levels(&mut self, ctx: &mut TcCtx<'t, 'p>, ls: LevelsPtr<'t>) -> Vec<Term> {
        ctx.read_levels(ls).iter().copied().collect::<Vec<_>>().into_iter().map(|l| self.interp_level(ctx, l)).collect()
    }

    // ── The level-quantification prototype (`LEVELPOLY.md`) ──────────────────
    //
    // Everything below is inert unless `NANODATG_LEVELPOLY=1`: the flag gates
    // both entry points ([`Self::interp_sort`]'s early return and
    // [`Self::ty_sort`]'s branch), and with it unset the apparatus is never
    // built and no path reaches these functions.

    /// The thread's [`derived::levels::apparatus::LevelPoly`], when enabled.
    fn lp(&self) -> Option<Rc<derived::levels::apparatus::LevelPoly>> {
        self.shared.borrow().lp.clone()
    }

    /// Whether `l` is ground — no level parameter reaches it. (σ has already
    /// been applied by the caller; what is left symbolic stays symbolic.)
    fn level_ground(&self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> bool {
        match ctx.read_level(l) {
            Level::Zero => true,
            Level::Succ(a, _) => self.level_ground(ctx, a),
            Level::Max(a, b, _) | Level::IMax(a, b, _) => {
                self.level_ground(ctx, a) && self.level_ground(ctx, b)
            }
            Level::Param(..) => false,
        }
    }

    /// The ω-vocabulary's **free variable** for the parameter name `n` —
    /// shared per thread through [`Shared::param_vars`] when the name is the
    /// export file's, per backend otherwise (an arena name cannot outlive its
    /// declaration).
    ///
    /// A variable, where [`Self::interp_level`]'s Param arm mints an opaque
    /// *symbol*: the symbol gives the syntactic vocabulary its injectivity,
    /// the variable is what the declaration-boundary quantifier can
    /// `Thm::gen` over. `⟦Sort u⟧ = srt(u)` at the variable `u` is therefore
    /// implicitly universal exactly the way the checker means it.
    fn param_omega_var(&mut self, n: NamePtr<'t>) -> FreeVar {
        if let Some(v) = self.param_omegas.get(&n) {
            return *v
        }
        let shared = self.name_key(n).and_then(|k| self.shared.borrow().param_vars.get(&k).copied());
        let v = match shared {
            Some(v) => v,
            None => {
                let v = self.env_mut().fresh_var();
                if let Some(k) = self.name_key(n) {
                    self.shared.borrow_mut().param_vars.insert(k, v);
                }
                v
            }
        };
        self.param_omegas.insert(n, v);
        v
    }

    /// Whether `v` is one of the ω-vocabulary's parameter variables — i.e. a
    /// variable [`Self::param_omega_var`] has handed out on this thread or in
    /// this backend. What the declaration boundary may quantify over.
    fn is_param_omega_var(&self, v: FreeVar) -> bool {
        self.param_omegas.values().any(|w| *w == v)
            || self.shared.borrow().param_vars.values().any(|w| *w == v)
    }

    /// The `u ∈ ω` assumptions a level's interpretation needs, one per distinct
    /// parameter, in traversal order.
    fn collect_level_params(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>, omega: &Term, out: &mut Vec<Formula>) {
        match ctx.read_level(l) {
            Level::Zero => {}
            Level::Succ(a, _) => self.collect_level_params(ctx, a, omega, out),
            Level::Max(a, b, _) | Level::IMax(a, b, _) => {
                self.collect_level_params(ctx, a, omega, out);
                self.collect_level_params(ctx, b, omega, out);
            }
            Level::Param(n, _) => {
                let t = Term::var(self.param_omega_var(n));
                let f = Formula::mem(t, omega.clone());
                if !out.contains(&f) {
                    out.push(f);
                }
            }
        }
    }

    /// Interpret a level into the **ω-vocabulary** — `∅`, `succ`, `∪`,
    /// `ite0(·,∅,·∪·)` — together with the evidence that the result is a
    /// natural number: `(ℓ̂, assms, ⊢ ⋀assms → ℓ̂ ∈ ω)` (the theorem is
    /// unconditional when `assms` is empty). `LEVELPOLY.md` §1.1.
    ///
    /// This is deliberately **not** [`Self::interp_level`]: that map reifies
    /// level *syntax* into axiom-free symbols (`lzero`, `lmax`, …) for the
    /// injectivity the sort rule needs; this one interprets levels as the
    /// natural numbers they denote, which is what `srt(·)` consumes. A
    /// parameter here is the shared per-name **free variable**
    /// ([`Self::param_omega_var`]) — so an `assms` entry is a hypothesis about
    /// a variable the declaration boundary can `gen` over, where the
    /// syntactic vocabulary's per-name symbol stays a constant forever.
    fn omega_level(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> Option<(Term, Vec<Formula>, Thm)> {
        let lp = self.lp()?;
        let omega = lp.omega();
        let mut assms = Vec::new();
        self.collect_level_params(ctx, l, &omega, &mut assms);
        let h = conj_of(&assms);
        let (t, thm) = self.omega_level_rec(ctx, l, &lp, &assms, h.as_ref())?;
        debug_assert_eq!(
            u_concl(&thm, h.as_ref()),
            Some(Formula::mem(t.clone(), omega)),
            "omega_level: the evidence is not about the term"
        );
        Some((t, assms, thm))
    }

    /// The recursive half of [`Self::omega_level`]: `(ℓ̂, ⊢ [H →] ℓ̂ ∈ ω)`
    /// under the *fixed* antecedent `h = conj(assms)`.
    fn omega_level_rec(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        l: LevelPtr<'t>,
        lp: &derived::levels::apparatus::LevelPoly,
        assms: &[Formula],
        h: Option<&Formula>,
    ) -> Option<(Term, Thm)> {
        // `⊢ a → b` and `⊢ [H →] a` give `⊢ [H →] b`.
        let lift = |cl: &Thm, prem: &Thm| -> Option<Thm> {
            match h {
                None => Thm::mp(cl, prem),
                Some(_) => derived::syl(prem, cl),
            }
        };
        match ctx.read_level(l) {
            Level::Zero => {
                let t = lp.zero();
                Some((t, u_a1i(&lp.r.peano.core.zero_mem, h)))
            }
            Level::Succ(a, _) => {
                let (ta, pa) = self.omega_level_rec(ctx, a, lp, assms, h)?;
                let cl = derived::inst_all(&lp.r.peano.core.succ_closed, std::slice::from_ref(&ta))?;
                let thm = lift(&cl, &pa)?;
                Some((lp.succ_of(ta), thm))
            }
            Level::Max(a, b, _) => {
                let (ta, pa) = self.omega_level_rec(ctx, a, lp, assms, h)?;
                let (tb, pb) = self.omega_level_rec(ctx, b, lp, assms, h)?;
                let both = match h {
                    None => derived::and_intro(&pa, &pb),
                    Some(_) => derived::hyp_and(&pa, &pb)?,
                };
                let cl = derived::inst_all(&lp.ord.max_in_omega, &[ta.clone(), tb.clone()])?;
                let thm = lift(&cl, &both)?;
                Some((lp.max(ta, tb), thm))
            }
            Level::IMax(a, b, _) => {
                let (ta, pa) = self.omega_level_rec(ctx, a, lp, assms, h)?;
                let (tb, pb) = self.omega_level_rec(ctx, b, lp, assms, h)?;
                let both = match h {
                    None => derived::and_intro(&pa, &pb),
                    Some(_) => derived::hyp_and(&pa, &pb)?,
                };
                let cl = derived::inst_all(&lp.imax_in_omega, &[ta.clone(), tb.clone()])?;
                let thm = lift(&cl, &both)?;
                Some((lp.imax(ta, tb), thm))
            }
            Level::Param(n, _) => {
                let t = Term::var(self.param_omega_var(n));
                let f = Formula::mem(t.clone(), lp.omega());
                let i = assms.iter().position(|a| *a == f)?;
                Some((t, conj_proj(assms, i)?))
            }
        }
    }

    /// `⟦Sort ℓ⟧ := srt(ℓ̂)` at a level the σ-schedule cannot ground — the
    /// quantified replacement for the opaque `sort(⟦ℓ⟧)` arm. Only the term;
    /// the evidence is rebuilt by the consumer ([`Self::ty_sort_poly`]), which
    /// is where it is checked against the obligation.
    fn interp_sort_poly(&mut self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> Option<Term> {
        let lp = self.lp()?;
        let omega = lp.omega();
        let mut assms = Vec::new();
        self.collect_level_params(ctx, l, &omega, &mut assms);
        let h = conj_of(&assms);
        let (t, _) = self.omega_level_rec(ctx, l, &lp, &assms, h.as_ref())?;
        Some(lp.srt_at(t))
    }

    /// The quantified branch of the sort-typing rule, `None` when it does not
    /// apply (flag off, ground level, or an obligation whose interpreted shape
    /// is not literally `srt(ℓ̂) ∈ srt(succ ℓ̂)`).
    fn ty_sort_poly(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, te: &Term, tt: &Term) -> Option<TgTyping> {
        let lp = self.lp()?;
        let Expr::Sort { level, .. } = ctx.read_expr(e) else { return None };
        let l = self.canon_level(ctx, level);
        if self.level_ground(ctx, l) {
            return None
        }
        let (lhat, assms, hthm) = self.omega_level(ctx, l)?;
        // The obligation must be about exactly the terms the rule proves
        // things about — the same guard every rule here ends on.
        if *te != lp.srt_at(lhat.clone()) || *tt != lp.srt_at(lp.succ_of(lhat.clone())) {
            return None
        }
        let sis = derived::inst_all(&lp.s.sort_in_sort, std::slice::from_ref(&lhat))?;
        let h = conj_of(&assms);
        let thm = match h {
            None => Thm::mp(&sis, &hthm)?,
            Some(_) => derived::syl(&hthm, &sis)?,
        };
        Some(self.typing(crate::certify::TyGap::Sort, te, tt, thm, assms))
    }

    /// The per-thread key for a Lean name, or `None` for a name interned in a
    /// per-declaration arena, whose index means nothing outside it.
    ///
    /// Everything keyed on this — the shared constant symbols and the typing
    /// store — is *shared across declarations*, so the key has to be stable
    /// across declarations. An export-file name's index is: the export file is
    /// parsed once and its arena never changes. A `TcCtx` name's index is
    /// reused by the next declaration for something else, and would alias.
    ///
    /// Delegated to [`crate::instantiations::name_key`] rather than spelled out
    /// twice: the pre-pass's schedule is keyed on exactly this, and the audit
    /// that checks the backend against the schedule is worthless if the two
    /// keys can drift.
    fn name_key(&self, n: NamePtr<'t>) -> Option<u32> { crate::instantiations::name_key(n) }

    /// The per-thread key for one *instantiation* of a constant: the name, and
    /// the universe levels it is used at, interpreted.
    ///
    /// The levels are part of the key because they are part of the denotation.
    /// `⟦f.{0}⟧` and `⟦f.{u}⟧` are definitions of two different bodies — the
    /// value is level-substituted before it is interpreted — so they are two
    /// symbols and, in the store, two entries.
    fn const_key(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<(u32, Vec<Term>)> {
        let k = self.name_key(name)?;
        Some((k, self.interp_levels(ctx, levels)))
    }

    /// **Check one interpreted constant instantiation against the schedule.**
    ///
    /// Instrumentation only: it draws no conclusion and changes no term. Its
    /// whole job is to make "the pre-pass predicted every instantiation the
    /// backend needed" a *measured* claim rather than an argued one. See the
    /// audit ledger next to [`inst_report`].
    fn audit_instantiation(&mut self, ctx: &mut TcCtx<'t, 'p>, name: NamePtr<'t>, levels: LevelsPtr<'t>) {
        let Some(k) = self.name_key(name) else { return note_inst(InstAudit::Temporary) };
        let ls = ctx.read_levels(levels);
        let mut inst = Vec::with_capacity(ls.len());
        for l in ls.iter().copied() {
            let l = ctx.under_sigma(l);
            // A ground simplified level is `succ^n(zero)` and nothing else, so
            // this both extracts the numeral and decides groundness.
            let (base, n) = ctx.level_succs(l);
            if !matches!(ctx.read_level(base), Level::Zero) {
                return note_inst(InstAudit::NonGround)
            }
            match u32::try_from(n) {
                Ok(n) => inst.push(n),
                Err(_) => return note_inst(InstAudit::NonGround),
            }
        }
        match crate::instantiations::was_predicted(k, &inst) {
            Some(true) => note_inst(InstAudit::Predicted),
            Some(false) => note_inst(InstAudit::Unpredicted),
            // No schedule was published, so there is nothing to audit against.
            None => {}
        }
    }

    /// `⟦c.{levels}⟧` and its defining equation, for a constant with a value.
    ///
    /// The symbol is allocated **once per thread** per `(name, levels)` pair,
    /// not once per declaration, so that the term denoting a constant is the
    /// same wherever the constant is mentioned. That is what makes a theorem
    /// about `⟦c⟧` derived while checking `c` mean anything while checking
    /// something else.
    ///
    /// Keying on the pair rather than on the *body* is deliberate, and is
    /// [`Self::ind_abbrev`]'s argument: two distinct constants with equal values
    /// must keep distinct denotations, or `⊢ ⟦a⟧ = ⟦b⟧` would stop being
    /// evidence about `a` and `b`.
    ///
    /// A cached entry is returned only if its defining equation is about the
    /// body this backend just interpreted. If the two have drifted, the
    /// interpretation is not canonical after all, and this hands back a fresh
    /// per-backend symbol — which reproduces the old behaviour exactly, and is
    /// counted, so that "the store never hits" cannot be mistaken for "nothing
    /// is derivable".
    fn const_abbrev(&mut self, key: Option<(u32, Vec<Term>)>, body: &Term) -> Option<(Term, Thm)> {
        if let Some(k) = key.as_ref() {
            if let Some((t, ax)) = self.shared.borrow().const_syms.get(k) {
                if *ax.concl() == Formula::eq(t.clone(), body.clone()) {
                    return Some((t.clone(), ax.thm().clone()))
                }
                note_dt(Dt::Drift);
            }
        }
        // A body mentioning the ω-vocabulary's parameter variables gets a
        // symbol of that arity — `LEVELPOLY.md` §1.6's `f̂(u⃗)` — whose defining
        // axiom `⊢ ∀u⃗. f̂(u⃗) = body(u⃗)` is instantiated back at the variables
        // so the equation handed out is at the generic point, exactly the
        // shape the nullary case hands out. Any other free variable in a body
        // is a leak, and refusing it (below, via `define_abbrev`'s own guard)
        // is what the opaque fallback at the call site is for.
        let mut fvs = Vec::new();
        body.free_vars(&mut fvs);
        fvs.sort();
        fvs.dedup();
        fvs.retain(|v| self.is_param_omega_var(*v));
        let (sym, all) = derived::define_abbrev(&mut self.env_mut(), &fvs, body)?;
        let args: Vec<Term> = fvs.iter().map(|v| Term::var(*v)).collect();
        let ax = if fvs.is_empty() { all } else { derived::inst_all(&all, &args)? };
        let t = self.mk(sym, args);
        // The house rule: pin the conclusion *and* read `hyps()`. The seal below
        // asks the same question again, by type, at the store.
        if !derived::establishes(&ax, &Formula::eq(t.clone(), body.clone())) {
            return None
        }
        if let Some(k) = key {
            if let Ok(sealed) = Sealed::new(ax.clone()) {
                self.shared.borrow_mut().const_syms.entry(k).or_insert((t.clone(), sealed));
            }
        }
        Some((t, ax))
    }

    /// The `i`-th canonical hole variable, allocating on demand — from the
    /// [`EnvCore`], so the series is one series across both engines.
    fn hole_var(&mut self, i: usize) -> FreeVar { self.core.hole_var(i) }

    /// The graph machinery for a skeleton, if that skeleton has been seen.
    fn lam_info(&self, key: &Term) -> Option<Rc<LamInfo>> { self.shared.borrow().lam_infos.get(key).cloned() }

    /// Split `t` into the part that mentions `v` and the maximal `v`-free
    /// subterms, which are pushed onto `holes` and replaced by canonical hole
    /// variables. `v` itself becomes the canonical bound-variable slot.
    ///
    /// Returns `None` if a term mentioning `v` was not built by [`Self::mk`],
    /// which would mean the interpretation had leaked a variable — a bug, and
    /// one that should surface as a gap rather than be papered over.
    ///
    /// **This backend decomposes through [`Self::parts`] and `mini` no longer
    /// does**, and the difference is deliberate rather than an oversight.
    /// `derived::skeleton::skeleton` reads structure off the term with
    /// `Term::as_app` and is therefore total; pointing this wrapper at it moves
    /// five of `checker/tests/tg_tutorial.rs`'s counter assertions — the
    /// projection clause is reached 3 times instead of 5, because a
    /// decomposition that used to fail now succeeds and an earlier rule fires
    /// instead. Those counters are tg's own frontier record and re-baselining
    /// them is a change to make on purpose, not a side effect of a memory fix
    /// in another crate. So [`skeleton_recorded`] keeps the old behaviour here,
    /// and `TgBackend::parts` keeps its reason to exist.
    fn skeleton(&mut self, t: &Term, v: FreeVar, holes: &mut Vec<Term>) -> Option<Term> {
        let core = self.core.clone();
        let mut hole_var = |i: usize| -> FreeVar { core.hole_var(i) };
        skeleton_recorded(&mut self.parts, self.x_canon, &mut hole_var, t, v, holes)
    }

    /// Rebuild `t` with `subst` applied, registering every node built on the
    /// way, so that the result can be taken apart again by [`Self::parts`].
    ///
    /// This is how a *fibre at a binder* becomes a term the typing rules can
    /// read: `b(q⃗,v)` unfolds, inside the kernel, to the skeleton with `q⃗` and
    /// `v` plugged in, and that term has never passed through [`Self::mk`]. The
    /// result is compared against the kernel's own instantiation by the caller,
    /// so a divergence here is a `None`, not a wrong answer.
    ///
    /// A leaf the backend did not build cannot be substituted into; it is
    /// returned unchanged, and only if it mentions none of the variables being
    /// substituted.
    fn reify(&mut self, t: &Term, subst: &[(FreeVar, Term)]) -> Option<Term> {
        if let Some((_, s)) = subst.iter().find(|(v, _)| *t == Term::var(*v)) {
            return Some(s.clone())
        }
        if let Some((f, args)) = self.parts.get(t).cloned() {
            let mut out = Vec::with_capacity(args.len());
            for a in &args {
                out.push(self.reify(a, subst)?);
            }
            return Some(self.mk(f, out))
        }
        subst.iter().all(|(v, _)| !t.occurs_free(*v)).then(|| t.clone())
    }

    /// The definitional extension behind one skeleton: the body symbol
    /// `t(h⃗,x) := skeleton` and its graph `lam(h⃗,A) = {⟨x,t(h⃗,x)⟩ : x ∈ A}`.
    ///
    /// Derived once per skeleton and then shared by every occurrence of that
    /// shape, in every declaration this thread checks.
    fn build_graph(&mut self, sk: &Term, holes: usize) -> Option<(FnSym, Graph)> {
        let mut ps: Vec<FreeVar> = Vec::with_capacity(holes + 1);
        for i in 0..holes {
            ps.push(self.hole_var(i));
        }
        ps.push(self.x_canon);
        let (t, t_def) = derived::define_abbrev(&mut self.env_mut(), &ps, sk)?;
        let (lam, lam_ax) = lambda_n(&mut self.env_mut(), &self.pre.clone().ap, t)?;
        Some((lam, Graph { t, t_def, lam_ax }))
    }

    /// One more than the largest de Bruijn **level** occurring in `e` — the
    /// first level at which the interpretation may open a binder of `e`
    /// without colliding with anything `e` already mentions.
    ///
    /// A function of the node, memoised, and that is the load-bearing
    /// property: the level (and so, with the interpreted domain, the
    /// [`LocalKey`] and the kernel variable) an interpretation binder opens at
    /// must not depend on *when* the interpretation is asked. On a closed
    /// telescope this numbering coincides with the checker's own (0, 1, 2, …),
    /// so checker-embedded locals and interpretation opens of one telescope
    /// agree on their variables.
    fn open_level(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> u16 {
        if let Some(l) = self.open_levels.get(&e) {
            return *l
        }
        let l = match ctx.read_expr(e) {
            Expr::Local { id, binder_type, .. } => {
                let own = match id {
                    crate::expr::FVarId::DbjLevel(n) => n.saturating_add(1),
                    crate::expr::FVarId::Unique(_) => 0,
                };
                own.max(self.open_level(ctx, binder_type))
            }
            Expr::App { fun, arg, .. } => {
                let f = self.open_level(ctx, fun);
                f.max(self.open_level(ctx, arg))
            }
            Expr::Lambda { binder_type, body, .. } | Expr::Pi { binder_type, body, .. } => {
                let t = self.open_level(ctx, binder_type);
                t.max(self.open_level(ctx, body))
            }
            Expr::Let { binder_type, val, body, .. } => {
                let t = self.open_level(ctx, binder_type);
                let v = self.open_level(ctx, val);
                t.max(v).max(self.open_level(ctx, body))
            }
            Expr::Proj { structure, .. } => self.open_level(ctx, structure),
            Expr::Sort { .. }
            | Expr::Const { .. }
            | Expr::Var { .. }
            | Expr::NatLit { .. }
            | Expr::StringLit { .. } => 0,
        };
        self.open_levels.insert(e, l);
        l
    }

    /// Interpret `λ binder:dom. body`.
    ///
    /// **Two clauses**, exactly as [`Self::interp_pi`] has two, and decided by
    /// the same classifier one level down:
    ///
    /// ```text
    /// ⟦λx : α. e⟧ = •                       — e a proof
    /// ⟦Λx : α. e⟧ = (x ∈ ⟦α⟧ ↦ ⟦e⟧)         — e a term of a Type
    /// ```
    ///
    /// The `Prop` clause is **proof irrelevance**: a proposition denotes a
    /// subset of `{•}`, so every one of its inhabitants *is* `•` and there is
    /// nothing else a proof could be sent to. Building a function graph for one
    /// was not merely wasteful — the graph's typing rule
    /// [`lam_in_funspace_n`]/[`lam_in_dprod_n`] states membership in a function
    /// space, while the obligation the checker asks about a proof `λ` is
    /// membership in a *conditional singleton*, so nothing could ever discharge
    /// it. See [`Self::term_clause`] for the classification, and
    /// [`Self::has_type_lam_prop`] for the rule that replaces the graph's.
    ///
    /// Neither the domain nor the body is interpreted on the `Prop` path beyond
    /// what the typing rule needs: `•` mentions neither, and §6.2 does not
    /// descend into a proof.
    ///
    /// Returns `None` only if the decomposition itself broke down, which would
    /// be a bug in this module; the caller then falls back to an opaque symbol
    /// so that a bug degrades into a reported gap rather than a wrong answer.
    fn interp_lambda(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        binder_name: NamePtr<'t>,
        binder_style: crate::expr::BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> Option<Term> {
        let dom = self.interp(ctx, binder_type);

        // Open the binder at a de Bruijn level that is a **function of the
        // expression** — one more than the largest level `e` embeds
        // ([`Self::open_level`]) — so the binder's kernel variable is keyed by
        // `(level, ⟦binder_type⟧)` ([`LocalKey::Level`]) and an identical
        // binder shape reuses the same variable, and with it every memoised
        // statement about the opened body (the interpretation memo's entries
        // for the body's subterms above all). A `mk_unique` local here minted
        // a fresh variable per occurrence, which made those entries
        // unreachable by construction: the opened body's `ExprPtr` could
        // never recur.
        //
        // *Not* the ambient `dbj_level_counter`, deliberately. The checker
        // asks for interpretations at many depths, and a counter-relative
        // open makes `⟦·⟧` depend on when it is first asked: the same `Π`
        // shape interpreted once mid-inference (checker binders open,
        // embedded checker locals in the expression) and once at the
        // declaration boundary got different skeletons, which turned
        // `073_boolRecEqns` fully-derived into one `pi congruence` gap. An
        // expression-derived level is depth-independent, collides with
        // nothing `e` mentions (it is above every embedded level), lines up
        // with the checker's own numbering on a closed telescope — and needs
        // no open/close discipline at all, so there is no early-exit hazard
        // and the checker's counter is never touched.
        let level = self.open_level(ctx, e);
        let local = ctx.remake_dbj_level(binder_name, binder_style, binder_type, level);
        self.interp_lambda_at(ctx, e, level, local, dom, body)
    }

    /// The body of [`Self::interp_lambda`], at its opened binder.
    fn interp_lambda_at(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        level: u16,
        local: ExprPtr<'t>,
        dom: Term,
        body: ExprPtr<'t>,
    ) -> Option<Term> {
        // The variable, obtained **exactly the way the body's occurrences
        // will obtain it** — through the interpretation itself (the `Local`
        // arm, expression memo included). Computing the `(level, ⟦type⟧)` key
        // here and minting on a miss is not equivalent: the same `Local` node
        // can already carry a memoised interpretation from an earlier walk
        // whose key no longer matches (the key contains the *interpreted*
        // type, which may mention other keyed variables), and the body would
        // then resolve through the memo while the open minted a second
        // variable — one binder split across two variables, a skeleton that
        // misses its own binder, and a completeness regression the claim
        // checks turn into gaps. Measured on `073_boolRecEqns` before this
        // was routed through `interp`: one new gap and a Prop-clause count
        // collapse. Consistency with the body, not the key itself, is the
        // load-bearing property.
        let key = LocalKey::Level(level, dom.clone());
        let pre_existing = self.exprs.contains_key(&local) || self.locals.contains_key(&key);
        note_binder_var(pre_existing);
        let tlocal = self.interp(ctx, local);
        let mut lfvs = Vec::new();
        tlocal.free_vars(&mut lfvs);
        let v = match lfvs.as_slice() {
            [v] if tlocal == Term::var(*v) => *v,
            _ => return None,
        };
        let body_open = ctx.inst(body, &[local]);

        // Which clause. Asked at the *opened* body and stamped on `e`, exactly
        // as `interp_pi` asks `body_clause` and stamps its answer: the two are
        // the same question — `sort(λx:α. e) = imax (lvl α) (sort e)` is `0`
        // exactly when `sort(e)` is — so the memo on `e` and the memo on the
        // body agree by construction.
        let clause = self.term_clause(ctx, body_open);
        self.terms.insert(e, clause);
        if clause == Clause::Prop {
            note_split(Split::LamProp);
            self.prop_lam_sites.insert(e, PropLamSite { dom, body: body_open, var: v });
            return Some(self.pre.point())
        }

        let bt = self.interp(ctx, body_open);

        let mut holes = Vec::new();
        let sk = self.skeleton(&bt, v, &mut holes)?;

        let info = match self.lam_info(&sk) {
            Some(i) => i,
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let info = match self.build_graph(&sk, holes.len()) {
                    Some((lam, g)) => Rc::new(LamInfo { lam, graph: Some(g) }),
                    // Inert: the right *shape*, so that the interpretation stays
                    // compositional, but with no defining axioms and hence no
                    // beta. The construction is closed for every skeleton this
                    // module builds, so this is unreachable in practice — and a
                    // reported gap rather than a wrong answer if it ever is not.
                    None => Rc::new(LamInfo { lam: self.env_mut().declare(arity), graph: None }),
                };
                let mut sh = self.shared.borrow_mut();
                sh.lam_infos.insert(sk.clone(), info.clone());
                sh.lam_by_lam.insert(info.lam, (sk.clone(), info.clone()));
                info
            }
        };

        let mut args = holes.clone();
        args.push(dom.clone());
        let term = self.mk(info.lam, args);
        self.lam_sites.insert(e, LamSite { key: sk, holes, dom, body: body_open, var: v });
        Some(term)
    }

    /// Interpret `e₁ e₂`.
    ///
    /// **Two clauses**, the third of §6.2's three splits:
    ///
    /// ```text
    /// ⟦e₁ e₂⟧   = •              — the application is a proof
    /// ⟦e₁ · e₂⟧ = ⟦e₁⟧(⟦e₂⟧)     — it is not
    /// ```
    ///
    /// The thesis states the condition on the *function*, `sort(Γ ⊢ e₁) = 0`;
    /// asking it of the application itself is the same question, since
    /// `e₁ : Πx:α. β` gives `lvl(Πx:α. β) = imax (lvl α) (lvl β)`, which is `0`
    /// exactly when `lvl β` — the sort of the application — is. Asking it here
    /// keeps one classifier for all three splits.
    ///
    /// On the `Prop` path the parts are **not** interpreted. `•` mentions
    /// neither of them, and a proof's interior is not something any rule can
    /// state a theorem about once the proof itself has collapsed to a point.
    fn interp_app(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        fun: ExprPtr<'t>,
        arg: ExprPtr<'t>,
    ) -> Term {
        if self.term_clause(ctx, e) == Clause::Prop {
            note_split(Split::AppProp);
            return self.pre.point()
        }
        let (f, a) = (self.interp(ctx, fun), self.interp(ctx, arg));
        self.mk(self.pre.ap.app, vec![f, a])
    }

    /// The fibre machinery for a `Π` skeleton, if that skeleton has been seen.
    fn pi_info(&self, key: &Term) -> Option<Rc<PiInfo>> { self.shared.borrow().pi_infos.get(key).cloned() }

    /// The definitional extension behind one `Π` skeleton: the fibre symbol
    /// `b(h⃗,x) := skeleton`, its Replacement image, and the dependent product
    /// `dprod(h⃗,A) = Π(x:A). b(h⃗,x)`.
    ///
    /// Derived once per skeleton and shared by every occurrence of that shape.
    fn build_fibre(&mut self, sk: &Term, holes: usize) -> Option<(FnSym, Fibre)> {
        let mut ps: Vec<FreeVar> = Vec::with_capacity(holes + 1);
        for i in 0..holes {
            ps.push(self.hole_var(i));
        }
        ps.push(self.x_canon);
        let (b, b_def) = derived::define_abbrev(&mut self.env_mut(), &ps, sk)?;
        let (img, img_ax) = image_symbol_n(&mut self.env_mut(), b)?;
        let pre = self.pre.clone();
        let (dprod, dprod_def) = dprod_symbol_n(&mut self.env_mut(), &pre.ap, &pre.fs, img, b)?;
        Some((dprod, Fibre { b, b_def, img, img_ax, dprod_def }))
    }

    /// The conditional-singleton machinery for a `∀` skeleton, if that skeleton
    /// has been seen.
    fn prop_info(&self, key: &Term) -> Option<Rc<PropInfo>> {
        self.shared.borrow().prop_infos.get(key).cloned()
    }

    /// `⊢ ⟦∀x:α. β⟧ ∈ ⟦Prop⟧`, i.e. `⊢ [φ] ∈ U₀`.
    ///
    /// Every proposition's denotation is a truth value — the `Prop` clause
    /// builds a **subset of `{•}`**, and `{0,1}` is where those live. The
    /// theorem is [`derived::tower::Tower::cond_in_u0`], derived once per body
    /// skeleton and generalised over the skeleton's parameters, so a second `∀`
    /// of the same shape is an instantiation.
    ///
    /// Everything is checked rather than assumed: the target must be `U₀` on
    /// the nose, the subject's head symbol must be a *registered* conditional
    /// singleton, and the instantiated conclusion is compared against the very
    /// membership claimed. Nothing here can return a theorem about some other
    /// set.
    fn prop_in_u0(&mut self, te: &Term, tt: &Term) -> Option<Thm> {
        if *tt != self.pre.u0() {
            return None
        }
        let (chi, args) = self.parts.get(te)?.clone();
        let (key, info) = self.shared.borrow().prop_by_chi.get(&chi).cloned()?;
        if args.len() != info.params.len() {
            return None
        }
        // Cloned out of the cell before anything else runs: deriving the
        // theorem needs `env_mut`, which borrows the same cell.
        let hit = self.shared.borrow().prop_u0s.get(&key).cloned();
        let general = match hit {
            Some(t) => t.map(Sealed::into_thm),
            None => {
                let chi_ax = info.chi_ax.clone();
                let ps: Vec<Term> = info.params.iter().map(|v| Term::var(*v)).collect();
                let c = Term::apply(chi, ps.clone());
                let pre = self.pre.clone();
                let built = chi_ax.as_ref().and_then(|ax| {
                    let at = derived::inst_all(ax, &ps)?;
                    let thm = pre.tower.cond_in_u0(&mut self.env_mut(), &info.phi, &c, &at)?;
                    (*thm.concl() == Formula::mem(c.clone(), pre.u0())).then_some(())?;
                    Some(derived::gen_all(&info.params, &thm))
                });
                self.shared.borrow_mut().prop_u0s.insert(key, Sealed::seal(built.clone()));
                built
            }
        };
        let inst = derived::inst_all(&general?, &args)?;
        // The guard: a theorem is only handed back if it is *this* membership.
        (*inst.concl() == Formula::mem(te.clone(), tt.clone())).then_some(inst)
    }

    /// `⊢ ∀h⃗ ∀A. (φ(h⃗,A) → • ∈ chi(h⃗,A))` — **the typing rule of a proof `λ`**.
    ///
    /// [`derived::prop::cond_intro`], `⊢ φ → • ∈ [φ]`, generalised over one `∀`
    /// skeleton's parameters, derived once and shared. Given `∀x ∈ ⟦α⟧. • ∈ ⟦β⟧`
    /// — which is what typing the lambda's body under the binder's guard
    /// establishes — it concludes `• ∈ [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]`, i.e. `⟦λ⟧ ∈ ⟦∀⟧`.
    ///
    /// Everything is checked rather than assumed: `cond_intro` is handed the
    /// skeleton's own `φ` and characteristic theorem, and its conclusion is
    /// compared against the implication it is supposed to be before it is
    /// generalised. A skeleton with no characteristic theorem — the inert
    /// encoding — yields `None`, and the caller reports a gap.
    fn prop_intro_thm(&mut self, key: &Term) -> Option<Thm> {
        if let Some(t) = self.shared.borrow().prop_intros.get(key) {
            return t.as_ref().map(|s| s.thm().clone())
        }
        let built = (|| {
            let info = self.prop_info(key)?;
            let chi_ax = info.chi_ax.clone()?;
            let ps: Vec<Term> = info.params.iter().map(|v| Term::var(*v)).collect();
            let c = Term::apply(info.chi, ps.clone());
            let at = derived::inst_all(&chi_ax, &ps)?;
            let pre = self.pre.clone();
            let thm = derived::prop::cond_intro(&pre.tower.sums, &info.phi, &c, &at)?;
            // The guard: this is only the rule if it says what the rule says.
            let want = Formula::imp(info.phi.clone(), Formula::mem(pre.point(), c));
            (*thm.concl() == want).then_some(())?;
            Some(derived::gen_all(&info.params, &thm))
        })();
        self.shared.borrow_mut().prop_intros.insert(key.clone(), Sealed::seal(built.clone()));
        built
    }

    /// The definitional extension behind one **`Prop`-valued `∀`** skeleton:
    /// the conditional singleton `chi(h⃗,A) = [∀x ∈ A. • ∈ C(h⃗,x)]`.
    ///
    /// One `define_abbrev` for the fibre and one
    /// [`derived::prop::conditional_singleton`] — a single Separation on the
    /// unit set — over it. The parameters are the skeleton's holes followed by
    /// the domain, which is `hole_var(holes)`: [`Self::skeleton`] only ever
    /// uses `hole_var(0..holes)`, so that slot is free by construction, and
    /// using it keeps the whole construction inside the canonical variables
    /// rather than minting a fresh one per skeleton.
    ///
    /// Derived once per skeleton and shared by every occurrence of that shape.
    fn build_cond(
        &mut self,
        sk: &Term,
        holes: usize,
    ) -> (Formula, Vec<FreeVar>, Option<(FnSym, Thm)>, Option<(FnSym, Thm)>) {
        let mut ps: Vec<FreeVar> = Vec::with_capacity(holes + 1);
        for i in 0..holes {
            ps.push(self.hole_var(i));
        }
        let x = self.x_canon;
        // `b(h⃗,x) := skeleton`, the same abstraction [`Self::build_fibre`]
        // makes, so that the body is a *symbol* the pointwise premise can speak
        // of.
        ps.push(x);
        let fibre = derived::define_abbrev(&mut self.env_mut(), &ps, sk);
        ps.pop();
        let a = self.hole_var(holes);
        let mut params = ps;
        params.push(a);
        let point = self.pre.tower.sums.point();
        let Some((b, _)) = fibre.as_ref() else {
            // Without a fibre symbol there is no formula to be conditional on.
            return (Formula::false_(), params, None, None)
        };
        let mut bargs: Vec<Term> = params[..holes].iter().map(|v| Term::var(*v)).collect();
        bargs.push(Term::var(x));
        // `∀x. (x ∈ A → • ∈ b(h⃗,x))` — §6.2's `[∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]` without
        // the brackets, which is exactly what the conditional singleton adds.
        let phi = Formula::forall(
            x,
            Formula::imp(
                Formula::mem(Term::var(x), Term::var(a)),
                Formula::mem(point, Term::apply(*b, bargs)),
            ),
        );
        let pre = self.pre.clone();
        let built =
            derived::prop::conditional_singleton(&mut self.env_mut(), &pre.tower.sums, &params, &phi);
        (phi, params, built, fibre)
    }

    /// `⟦∀x : α. β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]` — **§6.2's `Prop` clause**.
    ///
    /// `bt` is `⟦β⟧` and `v` the binder's kernel variable, or `None` when the
    /// binder provably does not occur. The two are *not* separate cases: a body
    /// that does not mention the binder decomposes into the degenerate skeleton
    /// `h₀` with `holes = [⟦β⟧]`, which is what [`Self::skeleton`] itself
    /// returns for a `v`-free term. Routing every exit of [`Self::interp_pi`]
    /// through this one function is what keeps `⟦·⟧` a function: were the
    /// syntactic non-dependence test to emit one symbol and the exact test
    /// another, two equal Lean terms would interpret to unequal set terms.
    fn interp_pi_prop(&mut self, e: ExprPtr<'t>, dom: Term, bt: Term, v: Option<FreeVar>) -> Option<Term> {
        let mut holes = Vec::new();
        let sk = match v {
            Some(v) if bt.occurs_free(v) => self.skeleton(&bt, v, &mut holes)?,
            // The degenerate skeleton, spelled out rather than obtained from
            // `skeleton` at a variable that does not occur: the two agree, and
            // this way the fast path needs no variable at all.
            _ => {
                let h = self.hole_var(0);
                holes.push(bt);
                Term::var(h)
            }
        };

        let info = match self.prop_info(&sk) {
            Some(i) => i,
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let (phi, params, built, fibre) = self.build_cond(&sk, holes.len());
                let info = match built {
                    Some((chi, chi_ax)) => Rc::new(PropInfo { chi, chi_ax: Some(chi_ax), fibre, phi, params }),
                    // Inert, exactly as [`PiInfo`]'s fallback is: the right
                    // *shape*, so the interpretation stays compositional, but no
                    // characteristic theorem and hence no membership fact. A
                    // reported gap rather than a wrong answer.
                    None => Rc::new(PropInfo {
                        chi: self.env_mut().declare(arity),
                        chi_ax: None,
                        fibre: None,
                        phi,
                        params,
                    }),
                };
                let mut sh = self.shared.borrow_mut();
                sh.prop_infos.insert(sk.clone(), info.clone());
                sh.prop_by_chi.insert(info.chi, (sk.clone(), info.clone()));
                info
            }
        };

        let mut args = holes.clone();
        args.push(dom.clone());
        let term = self.mk(info.chi, args);
        self.prop_sites.insert(e, PropSite { key: sk, holes, dom });
        Some(term)
    }

    /// `⟦Π x : α. β⟧` when **neither clause of §6.2 applies** — see
    /// [`Clause::Undet`] and [`crate::certify::TyGap::PiUndet`].
    ///
    /// An axiom-free symbol per body skeleton, applied to the skeleton's holes
    /// and the domain: the same shape both real clauses build, and *nothing
    /// else*. There is no defining equation, so no membership fact and no
    /// bridge can be derived over it and every rule that meets one reports a
    /// gap — which is the intended outcome. The alternative, picking a clause,
    /// would be interpreting the `Π` as a set it is not on half its
    /// instantiations.
    ///
    /// The symbols live in their own table rather than sharing
    /// [`Shared::pi_infos`]. They must: a skeleton can appear both under a
    /// decided `Π` and under an undecided one, and were they to share, whichever
    /// came first would hand the other its answer — a real dependent product to
    /// a `Π` that is not one, or an inert symbol to one that is.
    ///
    /// The binder handling is [`Self::interp_pi_prop`]'s, exactly: both of
    /// [`Self::interp_pi`]'s exits come here, and a body that does not mention
    /// the binder takes the degenerate skeleton either way, so `⟦·⟧` stays a
    /// function across the two exits here too.
    fn interp_pi_undet(&mut self, e: ExprPtr<'t>, dom: Term, bt: Term, v: Option<FreeVar>) -> Option<Term> {
        let mut holes = Vec::new();
        let sk = match v {
            Some(v) if bt.occurs_free(v) => self.skeleton(&bt, v, &mut holes)?,
            _ => {
                let h = self.hole_var(0);
                holes.push(bt);
                Term::var(h)
            }
        };
        let hit = self.shared.borrow().undet_syms.get(&sk).copied();
        let sym = match hit {
            Some(s) => s,
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let s = self.env_mut().declare(arity);
                self.shared.borrow_mut().undet_syms.insert(sk.clone(), s);
                s
            }
        };
        let mut args = holes.clone();
        args.push(dom.clone());
        let term = self.mk(sym, args);
        self.undet_sites.insert(e, PropSite { key: sk, holes, dom });
        Some(term)
    }

    /// Interpret `Π binder:dom. body`.
    ///
    /// **Two clauses, and a third case where neither applies.** Carneiro's §6.2
    /// interprets `∀` and `Π` differently, and which one applies is decided by
    /// the *body's sort*:
    ///
    /// ```text
    /// ⟦∀x : α. β⟧ = {•} ∩ ⋂_{x ∈ ⟦α⟧} ⟦β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]   — β a Prop
    /// ⟦Π x : α. β⟧ = ∏_{x ∈ ⟦α⟧} ⟦β⟧                                — β a Type
    /// ```
    ///
    /// The first is a **subset of `{•}`**; this used to build the second for
    /// every `Expr::Pi` unconditionally, which made a `Prop`-valued `∀`
    /// something it is not — and made its typing obligation `⟦∀…⟧ ∈ U₀` not
    /// merely unproved but unprovable as stated, since a `dprod` is no subset
    /// of `{•}`. [`Self::body_clause`] is the decision and
    /// [`Self::interp_pi_prop`] the first clause.
    ///
    /// The third case is [`Clause::Undet`]: `Sort (imax u v)` with `v` a
    /// universe parameter does not simplify, and the `Π` is a subset of `{•}`
    /// on the instantiations where `v := 0` and a function space on the others.
    /// Both clauses are then *wrong*, so neither is applied and
    /// [`Self::interp_pi_undet`] builds an axiom-free symbol of the right
    /// shape instead. That is a gap by construction, and the right one: no
    /// reading of a level-polymorphic declaration can settle it.
    ///
    /// For the second clause: every `Π` is the **dependent product**
    /// `dprod_C(h⃗, A)` over the fibre `b_C(h⃗, ·)`, built by exactly the
    /// skeleton decomposition the lambda machinery uses — see [`build_fibre`].
    /// A body that does not mention the binder is not a separate clause: its
    /// skeleton is the bare hole variable, so every arrow `A → B` shares one
    /// constant-fibre symbol — `dprod₀(B, A)`, `mini`'s own spelling — and two
    /// non-dependent `Π`s agree by reflexivity where the retired `fs` clause
    /// needed a bridge theorem. `derived::funspace`'s `fs` stays the library's
    /// statement vocabulary; [`Self::dprod_fs_eq`] is the one crossing.
    ///
    /// [`build_fibre`]: Self::build_fibre
    ///
    /// # Why the binder is opened
    ///
    /// This used to interpret the body in its *raw* de Bruijn form, with the
    /// binder's occurrences left as the opaque `bvar` symbol. That is enough
    /// for an opaque `pi(A,B)`, and not enough for a dependent product: the
    /// fibre `b(h⃗,x)` has to be a function *of* the binder, so the binder has
    /// to be a variable the definition can abstract. So the binder is opened,
    /// at a keyed de Bruijn level, exactly as in [`Self::interp_lambda`].
    ///
    /// Two things fall out of that, both good. Non-dependence is now decided
    /// **exactly** — "the interpreted body does not mention this binder's
    /// variable" — rather than conservatively from the loose-bvar count, so a
    /// body that mentions an *enclosing* binder but not this one is now the
    /// arrow it really is. And with every binder in the tower opened, an
    /// interpreted term contains no `bvar` symbols at all, which is what makes
    /// the certificates the checker hands down (stated at *its* locals) line up
    /// with the terms the claim is about.
    ///
    /// Returns `None` only if the decomposition itself broke down; the caller
    /// then falls back to the opaque `pi` symbol, so a bug degrades into a
    /// reported gap rather than a wrong answer.
    fn interp_pi(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        binder_name: NamePtr<'t>,
        binder_style: crate::expr::BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> Option<Term> {
        let dom = self.interp(ctx, binder_type);

        // A body with no loose de Bruijn index cannot mention the binder, and
        // instantiating it would be the identity — so skip the local entirely.
        //
        // This exit takes the `Prop` clause too. Missing it would be the exact
        // way to make `⟦·⟧` non-functional: `∀x:A. β` with a `β` that happens
        // not to mention `x` reaches *this* return, and the same `∀` written so
        // that `β` mentions an enclosing binder reaches the next one.
        if ctx.num_loose_bvars(body) == 0 {
            let b = self.interp(ctx, body);
            let clause = self.body_clause(ctx, body);
            self.props.insert(e, clause);
            return match clause {
                Clause::Prop => self.interp_pi_prop(e, dom, b, None),
                Clause::Undet => self.interp_pi_undet(e, dom, b, None),
                // The constant fibre: the body is hole 0 entire and the
                // skeleton is the bare hole variable — one table entry
                // corpus-wide, shared with every arrow whatever its codomain.
                Clause::Type => {
                    let h = self.hole_var(0);
                    self.finish_pi_site(e, Term::var(h), vec![b], dom)
                }
            }
        }

        // An expression-derived de Bruijn-level open, for
        // [`Self::interp_lambda`]'s reasons — reuse by `(level, ⟦type⟧)` key,
        // depth-independence, no counter and no close.
        let level = self.open_level(ctx, e);
        let local = ctx.remake_dbj_level(binder_name, binder_style, binder_type, level);
        self.interp_pi_at(ctx, e, level, local, dom, body)
    }

    /// The body of [`Self::interp_pi`], at its opened binder.
    fn interp_pi_at(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        level: u16,
        local: ExprPtr<'t>,
        dom: Term,
        body: ExprPtr<'t>,
    ) -> Option<Term> {
        // See `interp_lambda_open`: the variable comes from `interp` so it is
        // the one the body's occurrences resolve to, memo included.
        let key = LocalKey::Level(level, dom.clone());
        let pre_existing = self.exprs.contains_key(&local) || self.locals.contains_key(&key);
        note_binder_var(pre_existing);
        let tlocal = self.interp(ctx, local);
        let mut lfvs = Vec::new();
        tlocal.free_vars(&mut lfvs);
        let v = match lfvs.as_slice() {
            [v] if tlocal == Term::var(*v) => *v,
            _ => return None,
        };
        let body_open = ctx.inst(body, &[local]);
        let bt = self.interp(ctx, body_open);
        // Asked once, here, and stamped on `e`: the decision has to be a
        // function of the expression, and it is consulted again by the
        // *enclosing* `Π` — `imax u v = 0` exactly when `v = 0`, so a `Π` into
        // a `Prop`-valued `Π` is itself `Prop`-valued.
        let clause = self.body_clause(ctx, body_open);
        self.props.insert(e, clause);
        match clause {
            Clause::Prop => return self.interp_pi_prop(e, dom, bt, Some(v)),
            Clause::Undet => return self.interp_pi_undet(e, dom, bt, Some(v)),
            Clause::Type => {}
        }

        // A body whose interpretation does not mention the binder's variable is
        // a *constant* fibre. It is not a separate clause: `skeleton` sends the
        // whole body to hole 0 and the key is the bare hole variable, so every
        // arrow shares one skeleton — and one `dprod` symbol — corpus-wide.
        let mut holes = Vec::new();
        let sk = self.skeleton(&bt, v, &mut holes)?;
        self.finish_pi_site(e, sk, holes, dom)
    }

    /// The tail of [`Self::interp_pi`]'s `Type` clause: register (or share) the
    /// fibre skeleton's machinery and record where this occurrence sits.
    fn finish_pi_site(&mut self, e: ExprPtr<'t>, sk: Term, holes: Vec<Term>, dom: Term) -> Option<Term> {
        let info = match self.pi_info(&sk) {
            Some(i) => i,
            None => {
                let arity = u32::try_from(holes.len() + 1).ok()?;
                let info = match self.build_fibre(&sk, holes.len()) {
                    Some((dprod, fb)) => Rc::new(PiInfo { dprod, fibre: Some(fb) }),
                    // Inert: the right *shape*, so that the interpretation stays
                    // compositional, but with no defining axioms and hence no
                    // typing. A reported gap rather than a wrong answer.
                    None => Rc::new(PiInfo { dprod: self.env_mut().declare(arity), fibre: None }),
                };
                let mut sh = self.shared.borrow_mut();
                sh.pi_infos.insert(sk.clone(), info.clone());
                sh.pi_by_dprod.insert(info.dprod, (sk.clone(), info.clone()));
                info
            }
        };

        let mut args = holes.clone();
        args.push(dom.clone());
        let term = self.mk(info.dprod, args);
        self.pi_sites.insert(e, PiSite { key: sk, holes, dom });
        Some(term)
    }

    /// The W-type machinery, derived on first demand and shared per thread.
    ///
    /// `None` — a failure to build it — degrades into the opaque interpretation
    /// that was there before, i.e. into reported gaps, never into a claim.
    fn inductives(&mut self) -> Option<Rc<Inductives>> {
        if let Some(r) = self.shared.borrow().inds.clone() {
            return r
        }
        let pre = self.pre.clone();
        // The `Wtype` and `Bound` come from the core — the same pair the
        // [`derived::inductive::Machine`] is built over, on either engine —
        // and the borrow is released before `Inductives::build` takes the
        // `Env`.
        let wtb = self.core.wtype_bound(&pre);
        let built = wtb.and_then(|(wt, bnd)| {
            let mut env = self.env_mut();
            Inductives::build(&mut env, &pre, wt, bnd)
        });
        let r = built.map(Rc::new);
        self.shared.borrow_mut().inds = Some(r.clone());
        r
    }

    /// **`⊢ T ∈ ⟦Type 0⟧` for every interpreted inductive type that has one** —
    /// [`derived::cumul`]'s deliverable, at the very W-types this backend
    /// interprets Lean's inductives as and at the very `U₁`
    /// [`Self::interp_sort`] sends `Type 0` to. Built at most once per thread;
    /// see [`Shared::ind_ty_u1`].
    ///
    /// Four entries: `N` ([`derived::cumul::NatMem`]) and the three
    /// enumerations `enum(0)`, `enum(1)`, `enum(1+1)`
    /// ([`derived::cumul::enum_in_u1`]) — Lean's `Empty`, `Unit` and `Bool`.
    /// They share one chain, and `Bool`'s tag-set obligation `(1+1) ∈ U₁` is
    /// literally `N`'s, taken off the same derivation rather than repeated.
    ///
    /// # Why this needs `Chain::over` and not `Chain::new`
    ///
    /// `derived::cumul::Chain::new` mints its own tower — its own `ω`, `U(·)`,
    /// `Sums` and `W` — and a theorem about *those* symbols is not a theorem
    /// about anything this backend produces. What makes the wiring possible is
    /// that the chain's mathematics never inspects where its signature came
    /// from, so `Chain::over` takes the prelude's [`derived::tower::Tower`] and
    /// the [`Inductives`]' own `Wtype` and `Bound` and derives the same six
    /// lemmas over them. `derived::cumul::NatMem::over` is then the witness
    /// argument at a **caller-supplied** `N`, which matters because
    /// `derived::sums::Cases::new` mints a fresh `rec₊`: a second `Nat` would
    /// have a different fibre family, hence a different `W`, hence a theorem
    /// about a set no rule here speaks of.
    ///
    /// # The guard
    ///
    /// Two checks per entry, both here rather than trusted from `derived`: the
    /// theorem rests on **nothing** (`hyps().is_empty()`), and it says exactly
    /// `body ∈ ⟦Type 0⟧` at the two terms this backend would use. A derivation
    /// that concluded anything else — about the bound `U(1+1)`, say, where the
    /// statement is refutable — is dropped from the table, not adapted.
    fn ind_ty_u1(&mut self) -> Rc<Vec<(Term, Sealed)>> {
        if let Some(t) = self.shared.borrow().ind_ty_u1.clone() {
            return t
        }
        let pre = self.pre.clone();
        let u1 = pre.u1();
        let mut table: Vec<(Term, Sealed)> = Vec::new();
        if let Some(inds) = self.inductives() {
            let mut env = self.env_mut();
            if let Some(chain) = derived::cumul::Chain::over(&mut env, &pre.tower, &inds.wt, &inds.bnd) {
                // **The guard, applied to every entry alike.** A derivation is
                // recorded only if it rests on nothing and its conclusion is
                // literally `body ∈ U₁` for the body it is filed under. Nothing
                // is filed by head symbol, and nothing is adapted to fit.
                let mut add = |body: &Term, t: Option<Thm>| {
                    if let Some(t) = t {
                        if derived::establishes(&t, &Formula::mem(body.clone(), u1.clone())) {
                            if let Ok(sealed) = Sealed::new(t) {
                                table.push((body.clone(), sealed));
                            }
                        }
                    }
                };
                let s = &inds.wt.sums;
                let nat = derived::cumul::NatMem::over(&mut env, &chain, &inds.nat);
                // `(1+1) ∈ U₁` is proved on the way to `N ∈ U₁` and is exactly
                // what `Bool`'s tag set needs, so it is taken from there rather
                // than derived twice.
                let tags2 = nat.as_ref().map(|m| m.tags_in_u1.clone());
                add(&inds.nat.ty, nat.map(|m| m.nat_in_u1));

                let zero_u1 = derived::cumul::zero_in_u1(&chain);
                add(
                    &inds.e0,
                    derived::cumul::enum_in_u1(&mut env, &chain, &s.zero(), &zero_u1),
                );
                if let Some(one_u1) = derived::cumul::unit_in_u1(&chain) {
                    add(
                        &inds.e1.ty,
                        derived::cumul::enum_in_u1(&mut env, &chain, &inds.e1.tags, &one_u1),
                    );
                }
                if let Some(t2) = tags2 {
                    add(
                        &inds.e2.ty,
                        derived::cumul::enum_in_u1(&mut env, &chain, &inds.e2.tags, &t2),
                    );
                }
            }
        }
        let r = Rc::new(table);
        self.shared.borrow_mut().ind_ty_u1 = Some(r.clone());
        r
    }

    /// `⊢ te ∈ ty` when `te` is an interpreted inductive **type** and `ty` the
    /// universe it provably lives in — at present `⟦N⟧`, `⟦Bool⟧`, `⟦Unit⟧` and
    /// `⟦Empty⟧`, each at `⟦Type 0⟧`.
    ///
    /// The lookup is ordered cheapest-first, because the overwhelmingly common
    /// answer is "no": the target must be `U₁` on the nose, the subject must be
    /// an abbreviation this backend introduced, and its body must be one of the
    /// four W-types the `Inductives` built. Only then is the chain built — which
    /// is why the body is compared against terms already in hand rather than
    /// against the table, whose construction is the expensive step.
    ///
    /// # What is guarded, and why it is not the head symbol
    ///
    /// `⟦N⟧` is a fresh nullary symbol per declaration, so the shared theorem is
    /// about the *body* `W(1+1,B,U(1+1))` and has to be carried onto the
    /// abbreviation by Leibniz along its own defining equation. The guard is
    /// therefore on the **conclusion**: what is returned is registered only if
    /// it literally says `te ∈ ty` for the pair asked about. Recognising the
    /// head symbol would not do — that is the shape of bug this codebase has
    /// found five of.
    fn ind_ty_mem(&mut self, te: &Term, ty: &Term) -> Option<Thm> {
        if let Some(t) = self.ind_ty_mems.get(&(te.clone(), ty.clone())) {
            return t.clone()
        }
        let out = self.ind_ty_mem_uncached(te, ty);
        self.ind_ty_mems.insert((te.clone(), ty.clone()), out.clone());
        out
    }

    fn ind_ty_mem_uncached(&mut self, te: &Term, ty: &Term) -> Option<Thm> {
        if *ty != self.pre.u1() {
            return None
        }
        // `⊢ te = body`, the abbreviation's own defining equation.
        let def = self.abbrev_defs.get(te).cloned()?;
        let (_, body) = def.concl().as_eq()?;
        // Whether that body is an interpreted inductive type is decided against
        // the `Inductives` **if they exist**, and by comparing *terms*: building
        // them here would make an unrelated obligation pay for a development
        // that has no inductive in it at all, and building the chain before
        // knowing the body is one of the four would make every abbreviation
        // asked at `⟦Type 0⟧` pay for the cumulative hierarchy.
        let inds = self.shared.borrow().inds.clone().flatten()?;
        if ![&inds.nat.ty, &inds.e0, &inds.e1.ty, &inds.e2.ty].contains(&&body) {
            return None
        }
        note_ind_ty(false);
        let base = self.ind_ty_u1().iter().find(|(b, _)| *b == body).map(|(_, t)| t.thm().clone())?;

        let back = derived::eq_symm(&mut self.env_mut(), &def)?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(body, te.clone(), w, Formula::mem(Term::var(w), ty.clone()));
        let out = Thm::mp(&Thm::mp(&leib, &back)?, &base)?;
        if *out.concl() != Formula::mem(te.clone(), ty.clone()) {
            return None
        }
        note_ind_ty(true);
        Some(out)
    }

    /// The W-recursor and its two consequences, derived on first use and shared
    /// for the rest of the run.
    ///
    /// This is the expensive half of `derived`: `Recursor::new`, the one-point
    /// extension, structural induction for totality, and totality's two
    /// consequences. A file that declares an inductive but never reduces its
    /// recursor pays none of it; a file that reduces two different recursors
    /// pays for it once, and — more to the point — the two developments are
    /// then stated over the *same* symbols and compose.
    fn rec_core(&mut self) -> Option<Rc<RecCore>> {
        if let Some(r) = self.shared.borrow().rec_core.clone() {
            return r
        }
        let inds = self.inductives();
        let built = inds.and_then(|inds| {
            let mut env = self.env_mut();
            let wt = &inds.wt;
            let r = derived::wrec_total::Recursor::new(&mut env, wt)?;
            let ext = derived::wrec_extend::extension(&mut env, wt, &r)?;
            let total = derived::wrec_total::totality(&mut env, wt, &r, &ext)?;
            let iota = derived::wrec_total::iota(&mut env, wt, &r, &total)?;
            let funspace = derived::wrec_total::wrec_funspace(&mut env, wt, &r, &total)?;
            Some(RecCore { r, iota, funspace })
        });
        let r = built.map(Rc::new);
        self.shared.borrow_mut().rec_core = Some(r.clone());
        r
    }

    /// The recursor development for a two-constructor enumeration, on top of
    /// [`Self::rec_core`].
    ///
    /// What is added here is only the packed step: with empty fibres the
    /// W-recursor's step sees exactly two arguments, so it is a graph on two
    /// points ([`derived::twopoint`]).
    fn bool_recursor(&mut self) -> Option<Rc<BoolRecursor>> {
        if let Some(r) = self.shared.borrow().bool_rec.clone() {
            return r
        }
        let inds = self.inductives();
        let core = self.rec_core();
        let built = inds.zip(core).and_then(|(inds, core)| {
            let mut env = self.env_mut();
            let (wt, bnd) = (&inds.wt, &inds.bnd);
            let r = &core.r;
            let tp = derived::twopoint::TwoPoint::over(&mut env, &wt.sums.ap)?;
            let br = derived::wbool_rec::BoolRec::over(
                &mut env,
                wt,
                bnd,
                r,
                &inds.enum_closed,
                &core.iota,
                &tp,
            )?;
            let tags = derived::wbool_rec::BoolRec::tags(wt);
            Some(BoolRecursor {
                iota: [br.iota_false, br.iota_true],
                rec_sym: r.rec,
                universe: Term::apply(bnd.lu, vec![tags.clone()]),
                tags,
                zero: wt.empty(),
                up: wt.sums.ap.sets.up,
                keys: [
                    derived::wbool_rec::BoolRec::key(wt, false),
                    derived::wbool_rec::BoolRec::key(wt, true),
                ],
                ctors: [inds.e2.fst_t.clone(), inds.e2.snd_t.clone()],
            })
        });
        let r = built.map(Rc::new);
        self.shared.borrow_mut().bool_rec = Some(r.clone());
        r
    }

    /// The recursor development for the unary recursive shape, on top of the
    /// same [`Self::rec_core`].
    ///
    /// What is added here is the packed step of [`derived::wnat_rec`] — two
    /// layers of Replacement over the projections of [`derived::proj`] — and
    /// with it both ι rules, the `succ` one carrying a live recursive call.
    fn nat_recursor(&mut self) -> Option<Rc<NatRecursor>> {
        if let Some(r) = self.shared.borrow().nat_rec.clone() {
            return r
        }
        let inds = self.inductives();
        let core = self.rec_core();
        let built = inds.zip(core).and_then(|(inds, core)| {
            let nr = {
                let mut env = self.env_mut();
                let pj = derived::proj::Proj::new(&mut env, &inds.wt.sums.ap, &inds.pf)?;
                derived::wnat_rec::NatRec::over(
                    &mut env,
                    &inds.wt,
                    &inds.bnd,
                    &inds.nat,
                    &core.r,
                    &inds.pf,
                    &pj,
                    &core.iota,
                    &core.funspace,
                )?
            };
            Some(NatRecursor { nr, core, inds })
        });
        let r = built.map(Rc::new);
        self.shared.borrow_mut().nat_rec = Some(r.clone());
        r
    }

    /// The recursor development for the parameterised recursive shape, on top of
    /// the same [`Self::rec_core`] again.
    ///
    /// What is added here is [`derived::wlist_rec`]'s packed step: one
    /// Replacement over `prod(α, P(α,T))`, whose value takes the constructor's
    /// **field** as well as its recursive argument.
    fn list_recursor(&mut self) -> Option<Rc<ListRecursor>> {
        if let Some(r) = self.shared.borrow().list_rec.clone() {
            return r
        }
        let inds = self.inductives();
        let core = self.rec_core();
        let built = inds.zip(core).and_then(|(inds, core)| {
            let lr = {
                let mut env = self.env_mut();
                let pj = derived::proj::Proj::new(&mut env, &inds.wt.sums.ap, &inds.pf)?;
                derived::wlist_rec::ListRec::over(
                    &mut env,
                    &inds.wt,
                    &inds.bnd,
                    &inds.list,
                    &inds.cases,
                    &core.r,
                    &inds.pf,
                    &pj,
                    &core.iota,
                    &core.funspace,
                )?
            };
            Some(ListRecursor { lr, core, inds })
        });
        let r = built.map(Rc::new);
        self.shared.borrow_mut().list_rec = Some(r.clone());
        r
    }

    /// The number of constructors, when `name` is an inductive of the one shape
    /// this backend interprets: an **enumeration**.
    ///
    /// That means non-mutual, non-nested, non-recursive, no parameters, no
    /// indices, no universe parameters, not a `Prop`, and every constructor
    /// nullary — which is `Bool`, `Empty`, and nothing else in the tutorial
    /// corpus. Each condition is one the [`derived::enums`] construction
    /// genuinely needs:
    ///
    /// * *nullary constructors* is what makes every fibre `B(a)` empty, and
    ///   hence the W-type's elements `⟨tag,∅⟩` with no recursive part;
    /// * *no parameters or indices* is what makes the type a closed term rather
    ///   than a family, so `INDUCTIVES.md`'s `good` predicate is vacuous;
    /// * *no universe parameters* keeps the interpretation injective on
    ///   constants: `PUnit.{0}` and `PUnit.{1}` are different Lean types and
    ///   must not become one term;
    /// * *not a `Prop`* because the thesis interprets a `Prop` as a subset of
    ///   `{•}` ([`derived::prop`]), not as a W-type, and proof irrelevance
    ///   depends on that.
    fn enum_arity(&self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>) -> Option<usize> {
        let decls = self.decls;
        let ind = decls.get_inductive(name)?;
        if ind.num_params != 0 || ind.num_indices != 0 || ind.is_recursive || ind.is_nested {
            return None
        }
        if ind.all_ind_names.len() != 1 || !ctx.read_levels(ind.info.uparams).is_empty() {
            return None
        }
        // `Sort 0` is `Prop`, which is interpreted as a subsingleton elsewhere.
        let Expr::Sort { level, .. } = ctx.read_expr(ind.info.ty) else { return None };
        let level = ctx.simplify(level);
        if matches!(ctx.read_level(level), Level::Zero) {
            return None
        }
        let n = ind.all_ctor_names.len();
        if n > 2 {
            return None
        }
        // Every constructor nullary, and the indices exactly `0..n`.
        let mut seen = vec![false; n];
        for cn in ind.all_ctor_names.iter() {
            let c = decls.get_constructor(cn)?;
            if c.num_params != 0 || c.num_fields != 0 {
                return None
            }
            *seen.get_mut(c.ctor_idx as usize)? = true;
        }
        seen.iter().all(|b| *b).then_some(n)
    }

    /// `Some(())` when `name` is the **empty `Prop`-inductive**, i.e. `False`.
    ///
    /// [`Self::enum_arity`] declines every `Prop`, and rightly: a `Prop` is a
    /// subsingleton, not a W-type over a tag set, and `enum(0)`'s W-type
    /// `W(∅,∅,U(∅))` is `∅` only by a derivation the enumeration development
    /// does not run for `Prop`s. But the *empty* `Prop`-inductive has a
    /// denotation the thesis states outright — §6.2's `⟦Γ ⊢ ⊥⟧γ = ∅` — and
    /// [`derived::anchor::falsity`] proves everything about it. So it gets its
    /// own arm.
    ///
    /// Every condition is read off `InductiveData`, not off the name: a name
    /// test would make the threat-model anchor a statement about spelling.
    /// Sort 0, no parameters, no indices, no universe parameters, non-mutual,
    /// and **no constructors at all**.
    fn false_shape(&self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>) -> Option<()> {
        let ind = self.decls.get_inductive(name)?;
        if ind.num_params != 0 || ind.num_indices != 0 || ind.is_recursive || ind.is_nested {
            return None
        }
        if ind.all_ind_names.len() != 1 || !ctx.read_levels(ind.info.uparams).is_empty() {
            return None
        }
        if !ind.all_ctor_names.is_empty() {
            return None
        }
        let Expr::Sort { level, .. } = ctx.read_expr(ind.info.ty) else { return None };
        let level = ctx.simplify(level);
        matches!(ctx.read_level(level), Level::Zero).then_some(())
    }

    /// `true` when `e` is the constant `name` at no universe levels.
    ///
    /// Used to check a constructor's *field* type is the inductive itself,
    /// which is what "recursive, with exactly one recursive argument" means as
    /// a statement about the declaration rather than about its name.
    fn is_ind_const(&self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, name: &NamePtr<'t>) -> bool {
        match ctx.read_expr(e) {
            Expr::Const { name: n, levels, .. } => n == *name && ctx.read_levels(levels).is_empty(),
            _ => false,
        }
    }

    /// `Some(())` when `name` is an inductive of the second shape this backend
    /// interprets: **one nullary constructor and one taking a single argument
    /// of the type itself**, which is Lean's
    /// `inductive N | zero | succ (n : N)`.
    ///
    /// Every condition is one [`derived::wnat`] genuinely needs, and every one
    /// is read off `InductiveData`/`ConstructorData` rather than off the name:
    ///
    /// * *no parameters or indices* — the type is a closed term, not a family,
    ///   so `INDUCTIVES.md`'s `good` predicate is vacuous;
    /// * *no universe parameters* — keeps the interpretation injective on
    ///   constants, as for the enumerations;
    /// * *not a `Prop`* — a `Prop` is a subsingleton ([`derived::prop`]), not a
    ///   W-type;
    /// * *exactly two constructors, of arity 0 and 1*, the second's field being
    ///   the inductive itself — that is what makes the fibre family
    ///   `B(inl •) = 0`, `B(inr •) = 1` and nothing else. A second field, or a
    ///   field of another type, would need a `Σ` in the tag set.
    ///
    /// `zero`'s type is checked to be `N` and `succ`'s to be `N → N`, so a
    /// declaration that merely *counts* right cannot slip through.
    fn nat_shape(&self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>) -> Option<()> {
        self.nat_shape_flagged(ctx, name, true)
    }

    /// [`Self::nat_shape`], optionally without the `is_recursive` clause. See
    /// [`Self::recognised_ind`] for why anyone would want that.
    fn nat_shape_flagged(
        &self,
        ctx: &mut TcCtx<'t, 'p>,
        name: &NamePtr<'t>,
        require_rec: bool,
    ) -> Option<()> {
        let decls = self.decls;
        let ind = decls.get_inductive(name)?;
        if ind.num_params != 0 || ind.num_indices != 0 || (require_rec && !ind.is_recursive) || ind.is_nested {
            return None
        }
        if ind.all_ind_names.len() != 1 || !ctx.read_levels(ind.info.uparams).is_empty() {
            return None
        }
        let Expr::Sort { level, .. } = ctx.read_expr(ind.info.ty) else { return None };
        let level = ctx.simplify(level);
        if matches!(ctx.read_level(level), Level::Zero) {
            return None
        }
        if ind.all_ctor_names.len() != 2 {
            return None
        }
        let mut seen = [false; 2];
        for cn in ind.all_ctor_names.iter() {
            let c = decls.get_constructor(cn)?;
            if c.num_params != 0 {
                return None
            }
            match (c.ctor_idx, c.num_fields) {
                (0, 0) => {
                    // `zero : N`
                    if !self.is_ind_const(ctx, c.info.ty, name) {
                        return None
                    }
                    seen[0] = true;
                }
                (1, 1) => {
                    // `succ : N → N`
                    let Expr::Pi { binder_type, body, .. } = ctx.read_expr(c.info.ty) else {
                        return None
                    };
                    if !self.is_ind_const(ctx, binder_type, name)
                        || !self.is_ind_const(ctx, body, name)
                    {
                        return None
                    }
                    seen[1] = true;
                }
                _ => return None,
            }
        }
        seen.iter().all(|b| *b).then_some(())
    }

    /// `Some(())` when `name` is an inductive of the third shape this backend
    /// interprets: **one type parameter, one nullary constructor, and one taking
    /// a head of the parameter type and a tail of the inductive** — Lean's
    /// `inductive List (α : Type u) | nil | cons (h : α) (t : List α)`.
    ///
    /// Every condition is one [`derived::wlist`] genuinely needs, and every one
    /// is read off `InductiveData`/`ConstructorData` rather than off the name:
    ///
    /// * *exactly one parameter and no indices* — a parameter stays a free
    ///   variable of the whole construction, whereas an index would need
    ///   `INDUCTIVES.md`'s `good` predicate and hence the equality type;
    /// * *exactly one universe parameter*, and the type is `Sort ℓ → Sort ℓ` for
    ///   the **same** `ℓ`, not `Prop` — a `Prop` is a subsingleton, not a W-type;
    /// * *two constructors, of arity 0 and 2*, the second's fields being the
    ///   parameter and the inductive applied to it. That is what makes the fibre
    ///   family `B(inl •) = 0`, `B(inr h) = 1` and nothing else.
    ///
    /// The constructor types are checked in full — `nil : ∀α, List α` and
    /// `cons : ∀α, α → List α → List α`, with the de Bruijn indices verified —
    /// so a declaration that merely *counts* right cannot slip through.
    fn list_shape(&self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>) -> Option<()> {
        self.list_shape_flagged(ctx, name, true)
    }

    /// [`Self::list_shape`], optionally without the `is_recursive` clause. See
    /// [`Self::recognised_ind`] for why anyone would want that.
    fn list_shape_flagged(
        &self,
        ctx: &mut TcCtx<'t, 'p>,
        name: &NamePtr<'t>,
        require_rec: bool,
    ) -> Option<()> {
        let decls = self.decls;
        let ind = decls.get_inductive(name)?;
        if ind.num_params != 1 || ind.num_indices != 0 || (require_rec && !ind.is_recursive) || ind.is_nested {
            return None
        }
        if ind.all_ind_names.len() != 1 || ctx.read_levels(ind.info.uparams).len() != 1 {
            return None
        }
        let Expr::Pi { binder_type, body, .. } = ctx.read_expr(ind.info.ty) else { return None };
        let Expr::Sort { level: dom_l, .. } = ctx.read_expr(binder_type) else { return None };
        let Expr::Sort { level: cod_l, .. } = ctx.read_expr(body) else { return None };
        let dom_l = ctx.simplify(dom_l);
        if matches!(ctx.read_level(dom_l), Level::Zero) {
            return None
        }
        if ctx.simplify(cod_l) != dom_l {
            return None
        }
        if ind.all_ctor_names.len() != 2 {
            return None
        }
        let uparams = ind.info.uparams;
        let mut seen = [false; 2];
        for cn in ind.all_ctor_names.iter() {
            let c = decls.get_constructor(cn)?;
            if c.num_params != 1 {
                return None
            }
            // Every constructor's type opens with the parameter binder.
            let Expr::Pi { binder_type: pt, body: rest, .. } = ctx.read_expr(c.info.ty) else {
                return None
            };
            let Expr::Sort { level: pl, .. } = ctx.read_expr(pt) else { return None };
            if ctx.simplify(pl) != dom_l {
                return None
            }
            match (c.ctor_idx, c.num_fields) {
                // `nil : ∀ (α : Sort ℓ), List α`
                (0, 0) => {
                    if !self.is_ind_at(ctx, rest, name, uparams, 0) {
                        return None
                    }
                    seen[0] = true;
                }
                // `cons : ∀ (α : Sort ℓ), α → List α → List α`
                (1, 2) => {
                    let Expr::Pi { binder_type: hd, body: r2, .. } = ctx.read_expr(rest) else {
                        return None
                    };
                    if !matches!(ctx.read_expr(hd), Expr::Var { dbj_idx, .. } if dbj_idx == 0) {
                        return None
                    }
                    let Expr::Pi { binder_type: tl, body: r3, .. } = ctx.read_expr(r2) else {
                        return None
                    };
                    if !self.is_ind_at(ctx, tl, name, uparams, 1)
                        || !self.is_ind_at(ctx, r3, name, uparams, 2)
                    {
                        return None
                    }
                    seen[1] = true;
                }
                _ => return None,
            }
        }
        seen.iter().all(|b| *b).then_some(())
    }

    /// `true` when `e` is the constant `name` at levels `levels`, applied to the
    /// de Bruijn variable `idx`. Checking the index is what distinguishes
    /// `List α` from `List β` inside a nested binder.
    fn is_ind_at(
        &self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        name: &NamePtr<'t>,
        levels: LevelsPtr<'t>,
        idx: u16,
    ) -> bool {
        let Expr::App { fun, arg, .. } = ctx.read_expr(e) else { return false };
        if !matches!(ctx.read_expr(arg), Expr::Var { dbj_idx, .. } if dbj_idx == idx) {
            return false
        }
        match ctx.read_expr(fun) {
            Expr::Const { name: n, levels: ls, .. } =>
                n == *name && *ctx.read_levels(ls) == *ctx.read_levels(levels),
            _ => false,
        }
    }

        /// A fresh nullary symbol abbreviating `body`, its defining equation
    /// registered so the rest of the backend can unfold it, memoised on the
    /// Lean *name*.
    ///
    /// **Why an abbreviation, rather than the W-type term itself.** Two Lean
    /// inductives of the same shape — `Bool` and `TwoBool`, which
    /// `035_twoBool` and `061_twoBoolRec` declare side by side — have the same
    /// W-type, so interpreting each as that term outright would give two
    /// distinct Lean constants **one** denotation. Nothing false follows (every
    /// certificate is still checked against the claim, and the checker only
    /// ever asks `const_eq` about one constant at a time), but the
    /// interpretation would stop being injective on constants, which is a
    /// property worth keeping: it is what makes "`⊢ ⟦a⟧ = ⟦b⟧`" evidence about
    /// `a` and `b` rather than about their shapes. One `define_abbrev` per name
    /// restores it, for nothing — the symbol is fresh, so distinct names get
    /// distinct symbols, and the defining equation carries every theorem across.
    ///
    /// The key is the name **together with the universe levels**. For `Bool` and
    /// `N` that list is always empty; `List` is universe-polymorphic, and its
    /// denotation genuinely varies with the level, because `⟦List.{u}⟧` is a
    /// graph over `⟦Type u⟧`. Keying on the pair keeps one symbol per
    /// (constant, instantiation), which is what injectivity asks for.
    fn ind_abbrev(&mut self, name: NamePtr<'t>, levels: &[Term], body: &Term) -> Option<(Term, Thm)> {
        let key = (name, levels.to_vec());
        if let Some((t, ax)) = self.ind_syms.get(&key) {
            // The memo is checked against what is being asked for, not merely
            // recalled. A stored equation about a *different* body would be
            // handed to the Leibniz transports below and simply fail there, so
            // this is not a soundness fix — it is what turns a silent
            // re-derivation into a counted one.
            if *ax.concl() == Formula::eq(t.clone(), body.clone()) {
                return Some((t.clone(), ax.clone()))
            }
            note_dt(Dt::IndDrift);
        }
        // The per-thread store, on the [`Shared::const_syms`] pattern: same
        // key discipline (export-file names only), same guard, same fallback.
        let shared_key = self.name_key(name).map(|k| (k, levels.to_vec()));
        let from_shared = shared_key.as_ref().and_then(|k| {
            let (sym, ax) = self.shared.borrow().ind_syms.get(k).cloned()?;
            let ax = ax.into_thm();
            // The symbol came from another backend, so *this* backend has never
            // seen its applicative shape; `mk` is what re-registers it. Its
            // arguments are the body's ω-vocabulary parameter variables, in
            // the same sorted order the mint below chose them — deterministic
            // in the body, so both backends reconstruct the same application.
            let mut fvs = Vec::new();
            body.free_vars(&mut fvs);
            fvs.sort();
            fvs.dedup();
            fvs.retain(|v| self.is_param_omega_var(*v));
            let t = self.mk(sym, fvs.iter().map(|v| Term::var(*v)).collect());
            if *ax.concl() == Formula::eq(t.clone(), body.clone()) {
                Some((t, ax))
            } else {
                note_dt(Dt::IndDrift);
                None
            }
        });
        let (t, ax) = match from_shared {
            Some(hit) => hit,
            None => {
                // The §1.6 arity, exactly as [`Self::const_abbrev`]: a carrier
                // whose body mentions ω-vocabulary parameter variables is a
                // symbol applied to them, with the defining axiom quantified
                // and handed back at the generic point.
                let mut fvs = Vec::new();
                body.free_vars(&mut fvs);
                fvs.sort();
                fvs.dedup();
                fvs.retain(|v| self.is_param_omega_var(*v));
                let (sym, all) = derived::define_abbrev(&mut self.env_mut(), &fvs, body)?;
                let args: Vec<Term> = fvs.iter().map(|v| Term::var(*v)).collect();
                let ax = if fvs.is_empty() { all } else { derived::inst_all(&all, &args)? };
                let t = self.mk(sym, args);
                // `⊢ sym = body`, which is what `abbrev_defs` is read for —
                // under no hypotheses, which is what the store requires.
                if !derived::establishes(&ax, &Formula::eq(t.clone(), body.clone())) {
                    return None
                }
                if let Some(k) = shared_key {
                    if let Ok(sealed) = Sealed::new(ax.clone()) {
                        self.shared.borrow_mut().ind_syms.entry(k).or_insert((sym, sealed));
                    }
                }
                (t, ax)
            }
        };
        self.abbrev_defs.insert(t.clone(), ax.clone());
        self.ind_syms.insert(key, (t.clone(), ax.clone()));
        Some((t, ax))
    }

    /// `⟦False⟧ := ∅`, with **the threat-model anchor derived at that term**.
    ///
    /// # Why this arm exists at all
    ///
    /// `README.md` states the whole guarantee as: if a development translates
    /// and the kernel accepts every step, the development proves no
    /// contradiction — *as long as the translation of `False` is genuinely
    /// refutable in the target*. [`derived::anchor::falsity`] proves
    /// `⊢ ∀x. ¬(x ∈ ∅)` and `⊢ ⟦False⟧ = ∅`, and until now those were statements
    /// about the term the backend *should* produce: what it actually produced
    /// was an opaque nullary symbol with no axioms whatever, about which `∅` and
    /// `{∅}` are equally consistent. This arm is what ties the two together, and
    /// the tie is checked here rather than asserted:
    ///
    /// * `⊢ ⟦False⟧ = ∅` is [`Self::ind_abbrev`]'s own defining equation, so the
    ///   left-hand side is literally the symbol every other rule will speak of;
    /// * `⊢ ∀x. ¬(x ∈ ⟦False⟧)` is [`derived::anchor::uninhabited_along`] of
    ///   that equation with `⊢ ∀x. ¬(x ∈ ∅)`, and its conclusion is checked
    ///   against `⟦False⟧` before it is recorded;
    /// * `⊢ ⟦False⟧ ∈ ⟦Prop⟧` — which is `⊢ ∅ ∈ {0,1}` carried across the same
    ///   equation — is registered in [`Self::ind_mems`], so a typing obligation
    ///   `False : Prop` is discharged rather than assumed. This is only
    ///   available because `⟦Sort 0⟧` is now `U₀` and not an opaque symbol; see
    ///   [`Self::interp_sort`].
    ///
    /// The anchor itself is *used* by nothing: it is not a lemma the derivation
    /// needs, it is the statement the guarantee rests on. It is therefore
    /// counted in [`global_report`], so that "the anchor was derived at the
    /// backend's own term" is an observable of every run rather than a claim in
    /// a comment.
    fn false_const(&mut self, name: NamePtr<'t>) -> Option<Term> {
        let pre = self.pre.clone();
        let sums = &pre.tower.sums;
        let body = derived::anchor::false_set(sums);
        let u0 = pre.u0();
        let in_prop = derived::anchor::false_in_prop(sums)?;
        let uninhabited = derived::anchor::false_uninhabited(&mut self.env_mut(), sums)?;

        let (ct, ax) = self.ind_abbrev(name, &[], &body)?;

        // `⊢ ∀x. ¬(x ∈ ⟦False⟧)`, one Leibniz step from `⊢ ∀x. ¬(x ∈ ∅)`.
        //
        // Checked by *instantiating* rather than by comparing the quantified
        // formula: the bound variable is whichever one `uninhabited_along`
        // generalised over, and what has to be true is that the body is about
        // `⟦False⟧`.
        let anchor = derived::anchor::uninhabited_along(&mut self.env_mut(), &ax, &uninhabited)?;
        let w = self.env_mut().fresh_var();
        let at_w = derived::inst_all(&anchor, &[Term::var(w)])?;
        if *at_w.concl() != Formula::not(Formula::mem(Term::var(w), ct.clone())) {
            // A theorem that is not about `⟦False⟧` anchors nothing.
            return None
        }
        note_anchor();
        self.shared.borrow_mut().false_anchor = Sealed::new(anchor).ok();

        // `⊢ ⟦False⟧ ∈ ⟦Prop⟧`, the same equation run backwards under `_ ∈ U₀`.
        let back = derived::eq_symm(&mut self.env_mut(), &ax)?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(body, ct.clone(), w, Formula::mem(Term::var(w), u0.clone()));
        let mem = Thm::mp(&Thm::mp(&leib, &back)?, &in_prop)?;
        if *mem.concl() == Formula::mem(ct.clone(), u0.clone()) {
            self.ind_mems.insert((ct.clone(), u0), mem);
        }
        Some(ct)
    }

    /// `Some(idx)` when `name` is the recursor of an interpreted two-constructor
    /// enumeration, applied the way iota needs it: motive, two minor premises,
    /// and a major premise that is the `idx`th constructor.
    ///
    /// Every condition is read off `RecursorData` rather than off the name, and
    /// each is one [`derived::wbool_rec`] genuinely needs: no parameters and no
    /// indices (the type is a closed term, not a family), one motive and two
    /// minors (the packed step is a graph on exactly two points), and not `is_k`
    /// (subsingleton elimination is a different construction, `INDUCTIVES.md`
    /// §5.3, and is out of scope).
    fn enum_rec_shape(&self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>) -> Option<()> {
        let decls = self.decls;
        let Declar::Recursor(r) = decls.get_declar(name)? else { return None };
        if r.num_params != 0 || r.num_indices != 0 || r.num_motives != 1 || r.num_minors != 2 {
            return None
        }
        if r.is_k || r.all_inductives.len() != 1 || r.rec_rules.len() != 2 {
            return None
        }
        // Exactly one universe parameter, the motive's — the enumeration itself
        // has none (`enum_arity` refuses one), so this is `Bool.rec.{u}`.
        if ctx.read_levels(r.info.uparams).len() != 1 {
            return None
        }
        (self.enum_arity(ctx, &r.all_inductives[0]) == Some(2)).then_some(())
    }

    /// `Some(())` when `name` is the recursor of the interpreted **unary
    /// recursive** shape — `N.rec`.
    ///
    /// The conditions are [`Self::enum_rec_shape`]'s, over [`Self::nat_shape`]
    /// instead: no parameters and no indices, one motive, two minor premises,
    /// two recursor rules, not `is_k`, and exactly one universe parameter (the
    /// motive's — `N` itself has none). What differs is only what the recursor
    /// eliminates, and hence which packed step sits under the nest.
    fn nat_rec_shape(&self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>) -> Option<()> {
        let decls = self.decls;
        let Declar::Recursor(r) = decls.get_declar(name)? else { return None };
        if r.num_params != 0 || r.num_indices != 0 || r.num_motives != 1 || r.num_minors != 2 {
            return None
        }
        if r.is_k || r.all_inductives.len() != 1 || r.rec_rules.len() != 2 {
            return None
        }
        if ctx.read_levels(r.info.uparams).len() != 1 {
            return None
        }
        self.nat_shape(ctx, &r.all_inductives[0])
    }

    /// `Some(())` when `name` is the recursor of the interpreted
    /// **parameterised** shape — `List.rec`.
    ///
    /// [`Self::nat_rec_shape`]'s conditions with the two the parameter forces:
    /// `num_params = 1` rather than `0`, and **two** universe parameters rather
    /// than one — the motive's and the type's, since `List` is itself
    /// universe-polymorphic where `Bool` and `N` are not.
    fn list_rec_shape(&self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>) -> Option<()> {
        let decls = self.decls;
        let Declar::Recursor(r) = decls.get_declar(name)? else { return None };
        if r.num_params != 1 || r.num_indices != 0 || r.num_motives != 1 || r.num_minors != 2 {
            return None
        }
        if r.is_k || r.all_inductives.len() != 1 || r.rec_rules.len() != 2 {
            return None
        }
        if ctx.read_levels(r.info.uparams).len() != 2 {
            return None
        }
        self.list_shape(ctx, &r.all_inductives[0])
    }

    /// Which W-recursor `name`'s nest bottoms out in, if this backend has one.
    ///
    /// **The three hand-written recognisers come first**, which is the step-one
    /// invariant: `Bool.rec`/`N.rec`/`List.rec` reach the stacks they have
    /// always reached, byte for byte. The general arm is what is new, and it is
    /// only consulted when all three decline.
    fn rec_bottom(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: &NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<RecBottom> {
        if self.enum_rec_shape(ctx, name).is_some() {
            return Some(RecBottom::Enum(self.bool_recursor()?))
        }
        if self.nat_rec_shape(ctx, name).is_some() {
            return Some(RecBottom::Nat(self.nat_recursor()?))
        }
        if self.list_rec_shape(ctx, name).is_some() {
            return Some(RecBottom::List(self.list_recursor()?))
        }
        self.gen_rec_bottom(ctx, name, levels).map(|(g, tn)| RecBottom::General(g, tn))
    }

    /// **The general recursor** for `name`, if the declaration it eliminates is
    /// one [`Self::gen_ind`] translated and the `T`-policy has a target to
    /// offer — `WIRING-DESIGN.md` §6.1.
    ///
    /// # What is wired, and what is not
    ///
    /// `T`-policy **1 and 2** ([`Self::t_policy`]), at any number of parameters
    /// and any universe instantiation. Policy 3 — no nullary constructor at all,
    /// so no canonical closed point for the motive — declines here and is
    /// counted as [`Decline::TPolicy`]; widening the gate to admit it was
    /// measured and closes zero gaps, because `t_policy` then refuses inside
    /// `rec_nest` instead.
    ///
    /// The `np > 0` case rests on the Lean-facing type former
    /// ([`GenTyNest`]), which is returned alongside: the ι rule needs
    /// `app-spine(⟦T⟧,p⃗) = ind(p⃗)` and that equation is per backend.
    fn gen_rec_bottom(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: &NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<(Rc<GenRec>, Rc<GenTyNest>)> {
        let Some(Declar::Recursor(r)) = self.decls.get_declar(name) else { return None };
        if r.num_indices != 0 || r.num_motives != 1 || r.is_k || r.all_inductives.len() != 1 {
            return None
        }
        let ind_name = r.all_inductives[0];
        // Same seam as [`Self::ind_const`]'s: a declaration one of the
        // hand-written recognisers owns is never eliminated by the general
        // recursor, even when its own `*_rec_shape` refused this use. The two
        // stacks build different sets and there is no bridging theorem.
        if self.recognised_ind(ctx, &ind_name) {
            return None
        }
        let ind = self.decls.get_inductive(&ind_name)?;
        // **The eliminator-class consistency check, and the level split.** A
        // class-(T) recursor carries exactly one more universe parameter than
        // the declaration — the motive's, large elimination by Lean's reason 1
        // — and it is the **first**: `RBTree.rec` is `[u_1, u]` against
        // `RBTree`'s `[u]`, and `List.rec` likewise **[decoded**, the exports'
        // own `levelParams`**]**. So the declaration's own instantiation is the
        // *tail* of the recursor's, and a recursor whose parameter count does
        // not fit that shape declines rather than guesses.
        let ind_lp = ctx.read_levels(ind.info.uparams).len();
        let rec_lp = ctx.read_levels(r.info.uparams).len();
        let given = ctx.read_levels(levels);
        if rec_lp != ind_lp + 1 || given.len() != rec_lp {
            return None
        }
        let ind_levels = ctx.alloc_levels_slice(&given[1..]);
        let gi = self.gen_ind(ctx, ind_name, ind_levels)?;
        let n = gi.ind.spec.ctors.len();
        if r.num_minors as usize != n
            || r.rec_rules.len() != n
            || r.num_params as usize != gi.param_vars.len()
        {
            note_decline(Decline::Shape);
            return None
        }
        // `T`-policy 1 or 2 — [`Self::t_policy`] decides which. Policy 3, a
        // declaration with no nullary constructor at all, has no canonical
        // closed point for the motive and declines here (`Lean.ParserDescr` is
        // the corpus's biggest instance).
        if !gi.ind.spec.ctors.iter().any(|c| c.args.is_empty() && c.recs == 0) {
            note_decline(Decline::TPolicy);
            return None
        }
        // A hit is only usable if it is over **this** backend's carrier.
        //
        // `gen_inds`' guard re-walks the declaration on every hit and falls back
        // to a per-backend build when the `βⱼ` bodies did not survive — which on
        // `init-prelude` is essentially always (`MEASUREMENTS.md`: 3783 of 3803).
        // The recursor cached beside it is then a package of theorems about the
        // *previous* carrier's symbols: its ι rules mention `ind()` and `W` from
        // a build this backend no longer has, so every equation they state is
        // about terms `doms`/`abbrev_defs` never produce. `Rc::ptr_eq` is the
        // whole test, because `gen_ind` hands back the very `Rc` it stored when
        // — and only when — its own guard agreed.
        //
        // Rebuilding is the correct answer, not a missed optimisation, and it is
        // counted so the price stays visible.
        let ind_lv = self.interp_levels(ctx, ind_levels);
        // The Lean-facing type former of the declaration being eliminated —
        // per backend, and refused rather than guessed if it does not build.
        let Some(tn) = self.gen_ty_nest(&gi, ind_name, &ind_lv) else {
            note_decline(Decline::Params);
            return None
        };
        let key = (self.name_key(ind_name)?, ind_lv);
        let hit = self.shared.borrow().gen_recs.get(&key).cloned();
        if let Some(g) = hit {
            match &g {
                Some(g) if !Rc::ptr_eq(&g.gi, &gi) => {
                    GEN_REC_GUARD_MISS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                // A memoised decline, or a package over this very carrier.
                _ => return g.map(|g| (g, tn)),
            }
        }
        let core = self.rec_core()?;
        let mach = self.machine()?;
        let built = {
            let m = mach.borrow();
            let mut env = self.env_mut();
            derived::inductive::GenRecursor::build(
                &mut env,
                &m,
                &gi.ind,
                &core.r,
                &core.iota,
                &core.funspace,
            )
        };
        let out = built.map(|gr| Rc::new(GenRec { gi, gr: Rc::new(gr), core }));
        if out.is_some() {
            GEN_RECS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        } else {
            note_decline(Decline::Build);
        }
        // Never replace a recursor with a decline — `gen_ind_inner`'s rule, and
        // reachable here for the same reason now that a guard miss rebuilds: a
        // failed *rebuild* says this backend cannot use the package, not that
        // the package the previous backend built is wrong for it.
        {
            let mut sh = self.shared.borrow_mut();
            if out.is_some() || !matches!(sh.gen_recs.get(&key), Some(Some(_))) {
                sh.gen_recs.insert(key, out.clone());
            }
        }
        out.map(|g| (g, tn))
    }

    /// Build (or recall) the curried nest interpreting `T.rec.{us}`. See
    /// [`RecNest`].
    ///
    /// Returns `None` — leaving the recursor an opaque constant, exactly as
    /// before — if any part of the construction refuses. Nothing here is
    /// trusted: every symbol is a `define_abbrev`, every theorem a real `Thm`,
    /// and the iota rule below still checks its result against the claim.
    fn rec_nest(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<Rc<RecNest>> {
        let key = (name, self.interp_levels(ctx, levels));
        if let Some(n) = self.rec_nests.get(&key) {
            return Some(n.clone())
        }
        // The per-thread entry, if the name is the export file's. Read as a
        // **hint**: what it supplies to the walk below is the variables to open
        // the binders at, and nothing else is taken on its word.
        let shared_key = self.name_key(name).map(|k| (k, key.1.clone()));
        let cached =
            shared_key.as_ref().and_then(|k| self.shared.borrow().rec_nests.get(k).cloned());
        let bottom = self.rec_bottom(ctx, &name, levels)?;

        // ── The domains, from the recursor's own type ───────────────────────
        //
        // One level per Lean argument up to and including the major premise.
        // Each binder is opened at a local with a kernel variable reserved for
        // it first, so that the interpretation of the *next* domain puts that
        // variable exactly where the binder was.
        //
        // These stay `mk_unique` opens — deliberately, where `interp_lambda`
        // and `interp_pi` moved to keyed de Bruijn levels: the variable here
        // must be able to match a nest **stored by another declaration's
        // backend** (next comment), which is an identity a per-declaration
        // `(level, type)` key cannot transport. On a reuse walk the variable
        // comes from the **stored** nest rather than from `fresh_var`, because
        // the stored theorems are stated over those variables; nothing else is
        // taken from the store until `reuse_rec_nest` has checked the walk
        // against it. This is `walk_spec`'s reuse discipline, at a recursor
        // instead of a constructor.
        let Declar::Recursor(r) = self.decls.get_declar(&name)? else { return None };
        let (uparams, ty) = (r.info.uparams, r.info.ty);
        let depth = r.major_idx() + 1;
        let mut cur = ctx.subst_expr_levels(ty, uparams, levels);
        let mut doms: Vec<Term> = Vec::with_capacity(depth);
        let mut vars: Vec<FreeVar> = Vec::with_capacity(depth);
        for i in 0..depth {
            let Expr::Pi { binder_name, binder_style, binder_type, body, .. } = ctx.read_expr(cur)
            else {
                return None
            };
            doms.push(self.interp(ctx, binder_type));
            let local = ctx.mk_unique(binder_name, binder_style, binder_type);
            let lkey = unique_key(ctx, local)?;
            let v = match cached.as_ref().and_then(|c| c.vars.get(i)) {
                Some(v) => *v,
                None => self.env_mut().fresh_var(),
            };
            self.locals.insert(lkey, v);
            vars.push(v);
            cur = ctx.inst(body, &[local]);
        }
        if vars.len() < 4 {
            return None
        }

        // The stored nest, if it survives being checked against this walk.
        if let Some(c) = cached {
            if let Some(n) = self.reuse_rec_nest(&c, &vars, &doms, &bottom) {
                self.rec_nests.insert(key, n.clone());
                return Some(n)
            }
            note_dt(Dt::NestDrift);
        }

        // ── The bottom: the W-recursor, applied to the major premise ────────
        //
        // This is the only part that knows which inductive is being eliminated.
        // Everything above it is the same construction whatever sits here, and
        // that is deliberate: `List.rec`'s nest is this one at depth five.
        let ap = self.pre.ap.clone();
        let (major, minor_z, minor_s) =
            (Term::var(vars[depth - 1]), Term::var(vars[1]), Term::var(vars[2]));
        // With a parameter the minors move along by one, and so does the target.
        let np = match self.decls.get_declar(&name) {
            Some(Declar::Recursor(r)) => r.num_params as usize,
            _ => return None,
        };
        if depth < np + 4 {
            return None
        }
        let bottom_body = match &bottom {
            // `t_last(C,F,T,b) := app(brec(F,T), b)` — the motive is carried but
            // unused, the two minor premises being the whole of the step.
            RecBottom::Enum(br) => ap.apply(br.brec(&ap, &minor_z, &minor_s), major),
            // `t_last(C,z,s,b) := app(nrec(z,s,T), b)` with `T := D₂(C)`, the
            // motive's value at the nullary constructor. That is the level-2
            // domain the walk above has *already computed*, and using it rather
            // than rebuilding the term is what lets the two sides of an ι
            // equation share their assumptions.
            RecBottom::Nat(nr) => ap.apply(nr.nrec(&minor_z, &minor_s, &doms[1]), major),
            // `t_last(α,C,z,s,b) := app(lrec(α,z,s,T), b)` with `T := D₂(C)`, the
            // motive's value at `List.nil α`. The parameter is the level-0
            // argument and the minors are one further along; `T` is again the
            // domain the walk above has *already computed*, for the same reason.
            RecBottom::List(lr) => ap.apply(
                lr.lrec(
                    &Term::var(vars[0]),
                    &Term::var(vars[np + 1]),
                    &Term::var(vars[np + 2]),
                    &doms[np + 1],
                ),
                major,
            ),
            // `t_last(p⃗,C,s⃗,b) := app(grec(p⃗,s⃗,T), b)`. The minors sit at
            // `vars[np+1 .. np+1+n]` and `T` is the `T`-policy of §6.3, read
            // off the domains **as the walk computed them** — never rebuilt,
            // which is the twice-recorded `075` lesson.
            RecBottom::General(g, _) => {
                let n = g.gi.ind.spec.ctors.len();
                if depth != np + n + 2 {
                    return None
                }
                let ps: Vec<Term> = vars[..np].iter().map(|v| Term::var(*v)).collect();
                let minors: Vec<Term> =
                    vars[np + 1..np + 1 + n].iter().map(|v| Term::var(*v)).collect();
                let t_policy = self.t_policy(&g.gi, &doms, &minors, np)?;
                let mach = self.machine()?;
                let rec_term = {
                    let m = mach.borrow();
                    g.gr.rec_of(&m, &g.gi.ind, &g.core.r, &ps, &minors, &t_policy)?
                };
                ap.apply(rec_term, major)
            }
        };

        // ── The nest, innermost first ───────────────────────────────────────
        //
        // Level `k` is the graph `lamₖ(x₀…x_{k-1}, Dₖ)` whose body symbol is
        // `tₖ(x₀…x_{k-1}, xₖ)`: every argument above it is a parameter, and its
        // body is the next level's graph — or, at the bottom, `bottom_body`.
        let mut lams: Vec<FnSym> = vec![];
        let mut betas: Vec<Thm> = vec![];
        let mut t_defs: Vec<Thm> = vec![];
        let prefixes: Vec<Vec<usize>> = (0..depth).map(|k| (0..k).collect()).collect();

        let mut inner: Option<Term> = None;
        for k in (0..depth).rev() {
            let body = match inner {
                None => bottom_body.clone(),
                Some(t) => t,
            };
            let xs: Vec<FreeVar> = vars[..=k].to_vec();
            let (tk, tk_def) = derived::define_abbrev(&mut self.env_mut(), &xs, &body)?;
            let (lamk, lamk_ax) = lambda_n(&mut self.env_mut(), &ap, tk)?;
            let betak = beta_conditional_n(&mut self.env_mut(), &ap, tk, lamk, &lamk_ax)?;
            lams.push(lamk);
            betas.push(betak);
            t_defs.push(tk_def);
            let mut args: Vec<Term> = vars[..k].iter().map(|v| Term::var(*v)).collect();
            args.push(doms[k].clone());
            inner = Some(Term::apply(lamk, args));
        }
        lams.reverse();
        betas.reverse();
        t_defs.reverse();

        let (head, head_def) = self.ind_abbrev(name, &key.1, &inner?)?;
        let head_sym = self.parts.get(&head).map(|(f, _)| *f);
        let nest = Rc::new(RecNest { head, head_def, lams, betas, t_defs, prefixes, bottom });
        // Publish, so that the next declaration mentioning this recursor gets
        // the same `⟦T.rec⟧` instead of minting one — **whatever the bottom**.
        // A `General` bottom used to be excluded here because it carries a
        // [`GenTyNest`]; that stopped being per backend at `42a0dee`. See
        // [`Shared::rec_nests`].
        if let (Some(k), Some(head_sym)) = (shared_key, head_sym) {
            let entry = Rc::new(SharedNest {
                nest: nest.clone(),
                head_sym,
                vars: vars.clone(),
                doms: doms.clone(),
            });
            self.shared.borrow_mut().rec_nests.entry(k).or_insert(entry);
        }
        self.rec_nests.insert(key, nest.clone());
        Some(nest)
    }

    /// **Check a stored [`RecNest`] against this backend's walk**, and hand it
    /// back only if it survives.
    ///
    /// Everything asked is cheap — no `define_abbrev`, no `lambda_n`, no
    /// `beta_conditional_n`, which is the entire point: the expensive half of
    /// [`Self::rec_nest`] is what a hit avoids.
    ///
    /// 1. **The bottom is the same one** — [`same_bottom`]. The nest's ι rules
    ///    are the bottom's, so a nest over a different W-recursor computes
    ///    different equations. `Rc::ptr_eq` is the whole test, because every
    ///    part of a bottom is per thread: two backends either get the same `Rc`
    ///    or the derivation has been rebuilt and the nest above it is stale.
    ///    This backend's bottom is the one [`Self::rec_bottom`] has *already*
    ///    built above, which for a general one is what re-established `⟦T⟧`'s
    ///    applicative shape and defining equation here — so the comparison is
    ///    against a bottom this backend can use, not merely against a stored
    ///    one.
    /// 2. **The head is this symbol**, rebuilt through [`Self::mk`] rather than
    ///    cloned so that its applicative shape is registered in *this* backend's
    ///    `parts` — without which the term would be an atom the decomposition
    ///    cannot open.
    /// 3. **The walk agrees and the equation is about it** — [`nest_agrees`].
    ///
    /// Where the pinning comes from is worth being exact about, because the two
    /// halves of clause 3 cover different levels of the nest. A nest is not a
    /// nested *term*: level `k`'s body is abstracted into `tₖ` by
    /// `define_abbrev`, so `head_def` states only `⟦T.rec⟧ = lam₀(D₀)` and can
    /// pin only level 0. Levels below it are pinned by the **pointwise**
    /// comparison of the stored variables and domains against this walk's,
    /// which is why that comparison is not redundant with the equation check
    /// and why the test for it swaps levels 1 and 2 rather than 0 and 1.
    ///
    fn reuse_rec_nest(
        &mut self,
        c: &SharedNest,
        vars: &[FreeVar],
        doms: &[Term],
        bottom: &RecBottom,
    ) -> Option<Rc<RecNest>> {
        if !same_bottom(&c.nest.bottom, bottom) {
            return None
        }
        // As in [`Self::adopt_ty_nest`]: a head over ω-vocabulary parameter
        // variables is an application, and its arguments are read off the
        // stored head rather than assumed nullary.
        let args = match c.nest.head.as_app() {
            Some((_, args)) => args.to_vec(),
            None => vec![],
        };
        let head = self.mk(c.head_sym, args);
        if head != c.nest.head {
            return None
        }
        if !nest_agrees(&c.vars, &c.doms, &head, &c.nest.head_def, &c.nest.lams, vars, doms) {
            return None
        }
        // The unfolding chain reads this map, and it is per backend.
        self.abbrev_defs.insert(head, c.nest.head_def.clone());
        Some(c.nest.clone())
    }

    /// `true` when this backend gives `name` a real denotation with a typing
    /// theorem behind it — an interpreted inductive, or one of its constructors.
    ///
    /// Purely a *shape* test: it builds nothing and derives nothing, so it is
    /// safe to call from [`Self::typeable_shape`], which runs before any
    /// interpretation has happened. Answering `true` only lets a typing rule be
    /// attempted; whether the attempt succeeds is still decided by
    /// [`Self::has_type_h`]'s guard.
    fn interpreted_shape(&mut self, ctx: &mut TcCtx<'t, 'p>, name: &NamePtr<'t>, levels: LevelsPtr<'t>) -> bool {
        let decls = self.decls;
        let ind = match decls.get_declar(name) {
            Some(Declar::Inductive(_)) => *name,
            Some(Declar::Constructor(c)) => c.inductive_name,
            _ => return false,
        };
        // `List` is universe-polymorphic, so it is the one shape that admits a
        // non-empty level list — exactly one, matching its single `uparam`.
        if self.list_shape(ctx, &ind).is_some() {
            return ctx.read_levels(levels).len() == 1
        }
        if ctx.read_levels(levels).is_empty()
            && (self.enum_arity(ctx, &ind).is_some() || self.nat_shape(ctx, &ind).is_some())
        {
            return true
        }
        // …and the **general path**, which is why an application of one of its
        // constructors reaches the typing rules at all — the `N.succ` lesson
        // from the log, at general arity.
        //
        // Only the declaration-level scope is asked, not the field walk: this
        // runs before any interpretation has happened and must build nothing.
        // Answering `true` only lets a rule be *attempted*; whether the attempt
        // succeeds is still decided by `has_type_h`'s guard.
        if self.gen_scope(ctx, &ind, levels).is_err() {
            return false
        }
        // …unless the walk has already declined this declaration. Reading the
        // memo builds nothing and costs one lookup, and it keeps the gate from
        // sending obligations about a declaration the path is known to refuse
        // — `116`'s `RTree`, whose function-typed recursive argument only the
        // *field* walk can see.
        let lv = self.interp_levels(ctx, levels);
        match self.name_key(ind) {
            Some(k) => !matches!(self.shared.borrow().gen_inds.get(&(k, lv)), Some(None)),
            None => true,
        }
    }

    /// `⟦c⟧` when `c` is an interpreted inductive or one of its constructors.
    ///
    /// Two shapes are recognised: an **enumeration** ([`Self::enum_arity`]) and
    /// the **unary recursive** shape ([`Self::nat_shape`]), which is `N`.
    ///
    /// A constructor's **membership theorem** is registered on the way past, so
    /// that [`Self::has_type_h`] can discharge `⟦Bool.true⟧ ∈ ⟦Bool⟧` — or
    /// `⟦N.succ⟧ ∈ ⟦N → N⟧` — outright rather than carrying it as an
    /// assumption. It is transported along the defining equations
    /// [`Self::ind_abbrev`] introduced, and checked to conclude the membership
    /// being claimed before it is registered.
    ///
    /// **`N.succ` is a function, not a term-former.** Lean applies it, so its
    /// denotation has to be a *set*: the graph `{⟨n, succ n⟩ : n ∈ N}`, whose
    /// typing statement is `∈ fs(N,N)` rather than `∈ N`. That is the one place
    /// this differs from the nullary case, and it is what lets the application
    /// rule discharge `⟦N.succ n⟧ ∈ ⟦N⟧` from `⟦n⟧ ∈ ⟦N⟧`.
    fn ind_const(&mut self, ctx: &mut TcCtx<'t, 'p>, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Option<Term> {
        // **Order matters, and it is the step-one invariant.** The three
        // hand-written recognisers run first, so `Bool`/`N`/`List`/`False` and
        // everything fed by them are byte-identical to before the general path
        // existed. The two stacks build *different sets* — seed `U(A)` vs
        // `U({A,T})`, fibres `0`/`1` vs `finord(m)`, `1+α` vs `Sum_2(1,α+0)` —
        // with no bridging theorem, so nothing may mix them for one inductive
        // (`WIRING-DESIGN.md` §8). Cutting over is step two, and it is blocked
        // on `derived::cumul` accepting `finord(m)` fibres.
        if let Some(t) = self.ind_const_recognised(ctx, name, levels) {
            return Some(t)
        }
        // **A declaration a recogniser owns never reaches the general path** —
        // not even when the recogniser refused this particular *use*.
        //
        // `ind_const_recognised` returns `None` both for "not my shape" and for
        // "my shape, but I could not serve this instantiation", and the two must
        // not be conflated: falling through on the second builds a *second*
        // carrier for the same inductive, over the other stack's incompatible
        // sets. Nothing unsound follows — every theorem is guarded — but
        // `ind_abbrev` then sees a changed body for `⟦List⟧` and re-mints it, so
        // `interp` stops being a function on that constant, which is the recorded
        // failure that cost 54 ι sites. Measured: before this guard,
        // `076_listRecReduction` built a general `List` carrier and a general
        // `List.rec` nest beside the hand-written ones and reported one
        // `shared inductive symbols declined: body not canonical`.
        if self.recognised_ind(ctx, &ind_of(self.decls, name)?) {
            return None
        }
        self.gen_const(ctx, name, levels)
    }

    /// Whether one of the hand-written recognisers **owns** this declaration.
    ///
    /// A shape test only: it decides whose stack the declaration belongs to,
    /// not whether that stack can serve a given use. See [`Self::ind_const`] for
    /// why the distinction is load-bearing.
    /// **`is_recursive` is not consulted**, and that is the point. While an
    /// inductive is being *checked*, the checker installs a temporary
    /// `InductiveData` with `is_recursive: false` and only asserts the export's
    /// real value afterwards (`inductive.rs:115`, `inductive.rs:30`). During
    /// that window `list_shape` and `nat_shape` refuse **their own**
    /// declarations, so a gate built out of them would hand `List` to the
    /// general path for the length of `List`'s own declaration check and back
    /// again after it — two bodies for one `(name, levels)` key, which is
    /// `Dt::IndDrift` and a re-minted `⟦List⟧`. Measured on
    /// `076_listRecReduction`: one drift, and one general carrier and nest for a
    /// declaration the hand-written stack owns.
    ///
    /// Dropping the clause loses nothing: in both shapes the recursion is
    /// already implied by the field checks that follow — `nat_shape` requires
    /// `succ`'s field to be the declaration and `list_shape` requires `cons`'s
    /// tail to be — so the flag was a restatement, not a test. The two callers
    /// that must keep asking for it are the recognisers themselves, which is
    /// why this is a second entry point rather than a change to theirs.
    fn recognised_ind(&self, ctx: &mut TcCtx<'t, 'p>, ind: &NamePtr<'t>) -> bool {
        self.list_shape_flagged(ctx, ind, false).is_some()
            || self.false_shape(ctx, ind).is_some()
            || self.enum_arity(ctx, ind).is_some()
            || self.nat_shape_flagged(ctx, ind, false).is_some()
    }

    /// The three hand-written shape recognisers, unchanged.
    fn ind_const_recognised(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<Term> {
        let decls = self.decls;
        // `List` first: it is the only shape with universe parameters, and the
        // guard below rejects those.
        let ind_of = match decls.get_declar(&name)? {
            Declar::Inductive(_) => Some(name),
            Declar::Constructor(c) => Some(c.inductive_name),
            _ => None,
        };
        if let Some(i) = ind_of {
            if self.list_shape(ctx, &i).is_some() {
                return self.list_const(ctx, name, levels)
            }
        }
        if !ctx.read_levels(levels).is_empty() {
            return None
        }
        match decls.get_declar(&name)? {
            Declar::Inductive(_) => {
                // `False` first: it is the one `Prop` here, and `enum_arity`
                // declines every `Prop`, so the two recognisers cannot overlap.
                if self.false_shape(ctx, &name).is_some() {
                    return self.false_const(name)
                }
                let body = match self.enum_arity(ctx, &name) {
                    Some(n) => self.inductives()?.ty(n)?,
                    None => {
                        self.nat_shape(ctx, &name)?;
                        self.inductives()?.nat.ty.clone()
                    }
                };
                Some(self.ind_abbrev(name, &[], &body)?.0)
            }
            Declar::Constructor(c) => {
                let (ind_name, idx) = (c.inductive_name, c.ctor_idx as usize);
                // `arrow` says whether the constructor's *type* is the inductive
                // itself or an arrow into it — i.e. whether it takes an
                // argument. It is what the two Leibniz steps below rewrite
                // under, so it is computed once and used three times.
                let (ty_body, ctor_body, thm, arrow) = match self.enum_arity(ctx, &ind_name) {
                    Some(n) => {
                        let inds = self.inductives()?;
                        let (t, (cb, thm)) = (inds.ty(n)?, inds.ctor(n, idx)?);
                        (t, cb, thm, false)
                    }
                    None => {
                        self.nat_shape(ctx, &ind_name)?;
                        let inds = self.inductives()?;
                        let t = inds.nat.ty.clone();
                        match idx {
                            0 => (t, inds.nat.zero_t.clone(), inds.nat.zero.clone(), false),
                            1 => (
                                t,
                                inds.nat.succ_fun.clone(),
                                inds.nat.succ_in_funspace.clone(),
                                true,
                            ),
                            _ => return None,
                        }
                    }
                };
                let fs = self.pre.fs_sym();
                let target = |t: &Term| -> Term {
                    if arrow { Term::apply(fs, vec![t.clone(), t.clone()]) } else { t.clone() }
                };
                if *thm.concl() != Formula::mem(ctor_body.clone(), target(&ty_body)) {
                    return None
                }
                let (ty, ty_ax) = self.ind_abbrev(ind_name, &[], &ty_body)?;
                let (ct, ct_ax) = self.ind_abbrev(name, &[], &ctor_body)?;

                // `⊢ ⟦c⟧ ∈ target(W(…))`, then `⊢ ⟦c⟧ ∈ target(⟦T⟧)`; two
                // Leibniz steps along the defining equations, each run
                // backwards. The second rewrites *every* occurrence of the
                // W-type in the target, which is both of them for an arrow.
                let back_c = derived::eq_symm(&mut self.env_mut(), &ct_ax)?;
                let w = self.env_mut().fresh_var();
                let leib =
                    Thm::eq_leibniz(ctor_body, ct.clone(), w, Formula::mem(Term::var(w), target(&ty_body)));
                let at_ct = Thm::mp(&Thm::mp(&leib, &back_c)?, &thm)?;

                let back_t = derived::eq_symm(&mut self.env_mut(), &ty_ax)?;
                let w = self.env_mut().fresh_var();
                let leib = Thm::eq_leibniz(
                    ty_body,
                    ty.clone(),
                    w,
                    Formula::mem(ct.clone(), target(&Term::var(w))),
                );
                let out = Thm::mp(&Thm::mp(&leib, &back_t)?, &at_ct)?;

                // The guard: a theorem that does not literally say
                // `⟦c⟧ ∈ ⟦its type⟧` is not registered, whatever it proves.
                let claim = target(&ty);
                if *out.concl() != Formula::mem(ct.clone(), claim.clone()) {
                    return None
                }
                // An arrow-typed constructor's obligation arrives at the term
                // `⟦T → T⟧` interprets to — the constant-fibre `dprod` — while
                // `derived` states the membership over `fs`. Register the claim
                // at both spellings; `mem_at_dprod` is the one Leibniz step
                // between them.
                if arrow {
                    if let Some((dp, at_dp)) = self.mem_at_dprod(&ct, &ty, &ty, &out) {
                        self.ind_mems.insert((ct.clone(), dp), at_dp);
                    }
                }
                self.ind_mems.insert((ct.clone(), claim), out);
                Some(ct)
            }
            _ => None,
        }
    }

    /// `⟦c⟧` for `List`, `List.nil` and `List.cons` at one level instance, with
    /// the two **constructor rules** registered on the way past.
    ///
    /// This is the `Bool`/`N` pattern with two differences, both forced by the
    /// parameter.
    ///
    /// *The denotation depends on the universe level.* `⟦List.{u}⟧` is the graph
    /// `{⟨α, lt(α)⟩ : α ∈ ⟦Type u⟧}`, so the domain — and hence the set — varies
    /// with `u`. The abbreviation symbol is therefore keyed on the pair
    /// (name, levels), which keeps the interpretation injective on constants
    /// without pretending the level is irrelevant.
    ///
    /// *The typing is a rule, not a theorem.* `List.nil` is not a list until it
    /// is applied to `α`, so what is registered is a [`CtorRule`] whose premises
    /// are discharged at the point of use — see [`Self::has_type_ctor_app`]. The
    /// premise `⟦α⟧ ∈ ⟦Type u⟧` is the one `INDUCTIVES.md` worried nothing could
    /// discharge; it is discharged as **the binder's own assumption**, because
    /// `α` always arrives as a bound variable of that type.
    ///
    /// `derived::wlist_fun` states both rules over `app(L(S),α)` rather than
    /// over `lt(α)`, precisely so that the terms here are the ones `⟦List α⟧`
    /// interprets to and the two Leibniz transports below are the only bridging
    /// needed.
    fn list_const(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<Term> {
        let decls = self.decls;
        let ind_name = match decls.get_declar(&name)? {
            Declar::Inductive(_) => name,
            Declar::Constructor(c) => c.inductive_name,
            _ => return None,
        };
        self.list_shape(ctx, &ind_name)?;
        let ind = decls.get_inductive(&ind_name)?;
        if ctx.read_levels(levels).len() != ctx.read_levels(ind.info.uparams).len() {
            return None
        }
        let lv = self.interp_levels(ctx, levels);

        // `S := ⟦Sort ℓ⟧` at *these* levels — literally the term a binder
        // `(α : Type u)` will assume membership in, since it is the
        // interpretation of the same expression.
        let ty = ctx.subst_expr_levels(ind.info.ty, ind.info.uparams, levels);
        let Expr::Pi { binder_type, .. } = ctx.read_expr(ty) else { return None };
        let s_term = self.interp(ctx, binder_type);

        let (mut nil_name, mut cons_name) = (None, None);
        for cn in ind.all_ctor_names.iter() {
            let c = decls.get_constructor(cn)?;
            match c.ctor_idx {
                0 => nil_name = Some(*cn),
                1 => cons_name = Some(*cn),
                _ => return None,
            }
        }
        let (nil_name, cons_name) = (nil_name?, cons_name?);

        let inds = self.inductives()?;
        let lf_l = inds.list_fun.l_of(s_term.clone());
        let lf_nil = inds.list_fun.nil_of(s_term.clone());
        let lf_cons = inds.list_fun.cons_of(s_term.clone());
        let nil_rule = inds.list_fun.nil_rule.clone();
        let cons_rule = inds.list_fun.cons_rule.clone();
        drop(inds);

        let (l_t, l_ax) = self.ind_abbrev(ind_name, &lv, &lf_l)?;
        let (nil_t, nil_ax) = self.ind_abbrev(nil_name, &lv, &lf_nil)?;
        let (cons_t, cons_ax) = self.ind_abbrev(cons_name, &lv, &lf_cons)?;

        if !self.ctor_rules.contains_key(&(nil_name, lv.clone())) {
            let app = self.pre.ap.app;
            let back = |b: &mut Self, ax: &Thm| derived::eq_symm(&mut b.env_mut(), ax);

            // ── `nil`: one premise, `α ∈ S` ──────────────────────────────────
            let av = self.env_mut().fresh_var();
            let ta = Term::var(av);
            let a_in_s = Formula::mem(ta.clone(), s_term.clone());
            let raw = derived::inst_all(&nil_rule, &[s_term.clone(), ta.clone()])?;
            let app_lb = self.mk(app, vec![lf_l.clone(), ta.clone()]);
            let app_nb = self.mk(app, vec![lf_nil.clone(), ta.clone()]);
            if *raw.concl()
                != Formula::imp(a_in_s.clone(), Formula::mem(app_nb, app_lb.clone()))
            {
                return None
            }
            // `⟦List.nil⟧` for the graph, then `⟦List⟧` for the type.
            let w = self.env_mut().fresh_var();
            let hole_app = self.mk(app, vec![Term::var(w), ta.clone()]);
            let leib = Thm::eq_leibniz(
                lf_nil.clone(),
                nil_t.clone(),
                w,
                Formula::imp(a_in_s.clone(), Formula::mem(hole_app, app_lb.clone())),
            );
            let step = Thm::mp(&Thm::mp(&leib, &back(self, &nil_ax)?)?, &raw)?;

            let app_nil_t = self.mk(app, vec![nil_t.clone(), ta.clone()]);
            let w2 = self.env_mut().fresh_var();
            let hole_app2 = self.mk(app, vec![Term::var(w2), ta.clone()]);
            let leib2 = Thm::eq_leibniz(
                lf_l.clone(),
                l_t.clone(),
                w2,
                Formula::imp(a_in_s.clone(), Formula::mem(app_nil_t.clone(), hole_app2)),
            );
            let out_nil = Thm::mp(&Thm::mp(&leib2, &back(self, &l_ax)?)?, &step)?;
            let app_l_t = self.mk(app, vec![l_t.clone(), ta.clone()]);
            if *out_nil.concl()
                != Formula::imp(a_in_s.clone(), Formula::mem(app_nil_t, app_l_t))
            {
                return None
            }
            let rule_nil = CtorRule {
                thm: Thm::gen_checked(av, &out_nil)?,
                vars: vec![av],
                prems: vec![a_in_s],
            };

            // ── `cons`: three premises, the last mentioning the first ────────
            let bv = self.env_mut().fresh_var();
            let hv = self.env_mut().fresh_var();
            let tv = self.env_mut().fresh_var();
            let (tb, th, tt) = (Term::var(bv), Term::var(hv), Term::var(tv));
            let b_in_s = Formula::mem(tb.clone(), s_term.clone());
            let h_in_b = Formula::mem(th.clone(), tb.clone());
            let raw = derived::inst_all(
                &cons_rule,
                &[s_term.clone(), tb.clone(), th.clone(), tt.clone()],
            )?;
            let app_lb = self.mk(app, vec![lf_l.clone(), tb.clone()]);
            let prem_raw = Formula::and(
                b_in_s.clone(),
                Formula::and(h_in_b.clone(), Formula::mem(tt.clone(), app_lb.clone())),
            );
            let spine = |b: &mut Self, head: Term| {
                let one = b.mk(app, vec![head, tb.clone()]);
                let two = b.mk(app, vec![one, th.clone()]);
                b.mk(app, vec![two, tt.clone()])
            };
            let spine_lb = spine(self, lf_cons.clone());
            if *raw.concl() != Formula::imp(prem_raw.clone(), Formula::mem(spine_lb, app_lb.clone()))
            {
                return None
            }
            let w3 = self.env_mut().fresh_var();
            let spine_w = spine(self, Term::var(w3));
            let leib3 = Thm::eq_leibniz(
                lf_cons.clone(),
                cons_t.clone(),
                w3,
                Formula::imp(prem_raw, Formula::mem(spine_w, app_lb)),
            );
            let step = Thm::mp(&Thm::mp(&leib3, &back(self, &cons_ax)?)?, &raw)?;

            // The type occurs twice — in the tail's premise and in the target —
            // so one Leibniz with a hole in both places rewrites them together.
            let spine_c = spine(self, cons_t.clone());
            let w4 = self.env_mut().fresh_var();
            let hole_lb = self.mk(app, vec![Term::var(w4), tb.clone()]);
            let leib4 = Thm::eq_leibniz(
                lf_l.clone(),
                l_t.clone(),
                w4,
                Formula::imp(
                    Formula::and(
                        b_in_s.clone(),
                        Formula::and(h_in_b.clone(), Formula::mem(tt.clone(), hole_lb.clone())),
                    ),
                    Formula::mem(spine_c.clone(), hole_lb),
                ),
            );
            let out_cons = Thm::mp(&Thm::mp(&leib4, &back(self, &l_ax)?)?, &step)?;
            let app_l_b = self.mk(app, vec![l_t.clone(), tb.clone()]);
            let t_in_l = Formula::mem(tt.clone(), app_l_b);
            if *out_cons.concl()
                != Formula::imp(
                    Formula::and(b_in_s.clone(), Formula::and(h_in_b.clone(), t_in_l.clone())),
                    Formula::mem(spine_c, {
                        let f = self.mk(app, vec![l_t.clone(), tb.clone()]);
                        f
                    }),
                )
            {
                return None
            }
            let rule_cons = CtorRule {
                thm: derived::gen_all(&[bv, hv, tv], &out_cons),
                vars: vec![bv, hv, tv],
                prems: vec![b_in_s, h_in_b, t_in_l],
            };

            self.ctor_rules.insert((nil_name, lv.clone()), rule_nil);
            self.ctor_rules.insert((cons_name, lv.clone()), rule_cons);
        }

        if name == ind_name {
            Some(l_t)
        } else if name == nil_name {
            Some(nil_t)
        } else if name == cons_name {
            Some(cons_t)
        } else {
            None
        }
    }

    // ── The general inductive path ──────────────────────────────────────────
    //
    // Everything from here to `interp` is `WIRING-DESIGN.md` §§3–5: the
    // `FnSym` boundary, the eliminator branch, and the Lean-facing layer that
    // turns `derived::inductive`'s `ind(p⃗)` / `ctor_i(y⃗,r⃗)` into the curried
    // applications Lean writes.

    /// **Is `l` provably nonzero, read off the level expression itself?**
    ///
    /// `LEVEL-POLYMORPHIC-INDUCTIVES.md` §2–3 and thesis §2.6.2: the
    /// translation branch is fixed **per declaration** by Lean's eliminator
    /// trichotomy, never by the instantiated sort. So this is asked of the
    /// declaration's *own* resultant level — before any σ — and a declaration
    /// whose answer is `false` is declined outright rather than translated at
    /// the instantiations that happen to make it a `Type`.
    ///
    /// This is sharper than the three recognisers' `matches!(…, Level::Zero)`
    /// after `simplify`. On a monomorphic declaration the two agree, because
    /// there are no parameters to be ambiguous about; on a polymorphic one they
    /// do not, and `list_shape`'s test **would** admit a `Sort ℓ → Sort ℓ`
    /// list — the recorded hazard. The old recognisers keep their own tests
    /// until they are deleted; the general path closes the hazard for every
    /// shape it serves.
    fn provably_nonzero(&self, ctx: &mut TcCtx<'t, 'p>, l: LevelPtr<'t>) -> bool {
        match ctx.read_level(l) {
            Level::Succ(..) => true,
            Level::Max(a, b, _) => self.provably_nonzero(ctx, a) || self.provably_nonzero(ctx, b),
            // `imax a b` is `0` exactly when `b` is, so only the right side
            // can witness nonzeroness.
            Level::IMax(_, b, _) => self.provably_nonzero(ctx, b),
            Level::Zero | Level::Param(..) => false,
        }
    }

    /// `true` when `e` mentions any of `names` as a constant, anywhere.
    ///
    /// Used to refuse a *plain* field whose type mentions the declaration being
    /// translated. Interpreting such a type would re-enter [`Self::ind_const`]
    /// on the declaration under construction, and the interpretation would
    /// stop being a function on that constant — one occurrence an abbreviation,
    /// another an opaque symbol. Refusing is the honest answer.
    fn mentions_const(&self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, names: &[NamePtr<'t>]) -> bool {
        let mut stack = vec![e];
        let mut seen: Vec<ExprPtr<'t>> = Vec::new();
        while let Some(e) = stack.pop() {
            if seen.contains(&e) {
                continue
            }
            seen.push(e);
            match ctx.read_expr(e) {
                Expr::Const { name, .. } =>
                    if names.contains(&name) {
                        return true
                    },
                Expr::App { fun, arg, .. } => {
                    stack.push(fun);
                    stack.push(arg);
                }
                Expr::Pi { binder_type, body, .. } | Expr::Lambda { binder_type, body, .. } => {
                    stack.push(binder_type);
                    stack.push(body);
                }
                Expr::Let { binder_type, val, body, .. } => {
                    stack.push(binder_type);
                    stack.push(val);
                    stack.push(body);
                }
                Expr::Proj { structure, .. } => stack.push(structure),
                Expr::Local { binder_type, .. } => stack.push(binder_type),
                _ => {}
            }
        }
        false
    }

    /// Whether `e` is the declaration `name` at exactly `levels`, applied to
    /// the `np` parameter locals in order — [`Self::is_ind_at`]'s check
    /// generalised to a spine. `np = 0` is the bare constant.
    fn is_ind_spine(
        &self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        name: &NamePtr<'t>,
        levels: LevelsPtr<'t>,
        params: &[ExprPtr<'t>],
    ) -> bool {
        let (head, args) = ctx.unfold_apps(e);
        if args.len() != params.len() {
            return false
        }
        if !args.iter().zip(params.iter()).all(|(a, p)| a == p) {
            return false
        }
        match ctx.read_expr(head) {
            Expr::Const { name: n, levels: ls, .. } =>
                n == *name && *ctx.read_levels(ls) == *ctx.read_levels(levels),
            _ => false,
        }
    }

    /// **The declaration-level scope of the general path** — everything
    /// decidable from `InductiveData` alone, before a single binder is opened.
    ///
    /// All checks are **positive**: this verifies the covered shape rather than
    /// enumerating exclusions, which is `spec.rs`'s contract.
    ///
    /// `num_indices == 0` is not defensive boilerplate — indices are
    /// *unrepresentable* in [`DeclSpec`], so there is no derived-side backstop
    /// and this line is the whole of the scope enforcement for indexed
    /// families. `RBTree` (`numIndices: 2`) declines here and nowhere else.
    ///
    /// **The index check comes after the eliminator branch, deliberately.**
    /// `INDEXED-DESIGN.md` §2.1 decides the translation of an indexed family by
    /// the same trichotomy as a non-indexed one, and the two branches want
    /// different constructions: class (T) takes §5.2's `good` subset, classes
    /// (S)/(P) take `acc` or truncation. Testing the sort first makes the
    /// `indices` row of the report **the class-(T) census** — the declarations
    /// §5.2 would serve — rather than a mixture of those with every indexed
    /// `Prop`, which on the preludes is most of them (`Eq`, `Acc`, `HEq`, `Or`'s
    /// friends). Getting that ordering the other way round is not a bug, but it
    /// makes the number uninformative, and the number is the point of counting.
    ///
    /// Cheap enough to be a gate for [`Self::interpreted_shape`]: it reads
    /// fields and walks a level expression, and builds nothing.
    fn gen_scope(
        &self,
        ctx: &mut TcCtx<'t, 'p>,
        ind_name: &NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Result<(), Decline> {
        let ind = self.decls.get_inductive(ind_name).ok_or(Decline::Shape)?;
        if ind.all_ind_names.len() != 1 {
            return Err(Decline::Mutual)
        }
        if ind.is_nested {
            return Err(Decline::Nested)
        }
        if ind.all_ctor_names.is_empty() {
            return Err(Decline::NoCtors)
        }
        if ctx.read_levels(levels).len() != ctx.read_levels(ind.info.uparams).len() {
            return Err(Decline::Shape)
        }
        // **The eliminator branch**, on the declaration's *own* level
        // expression — never the σ-instantiated numeral. See
        // [`Self::provably_nonzero`].
        let mut cur = ind.info.ty;
        for _ in 0..(ind.num_params + ind.num_indices) {
            let Expr::Pi { body, .. } = ctx.read_expr(cur) else { return Err(Decline::Shape) };
            // The binder is not opened: a `Sort` cannot mention it, and opening
            // would mint locals this predicate has no business minting.
            cur = body;
        }
        let Expr::Sort { level, .. } = ctx.read_expr(cur) else { return Err(Decline::Shape) };
        if !self.provably_nonzero(ctx, level) {
            return Err(Decline::SortAmbiguous)
        }
        if ind.num_indices != 0 {
            return Err(Decline::Indices)
        }
        // `np > 0` is wired: the type former is a nest of `np` lambda graphs
        // ([`Self::gen_ty_nest`]), every constructor's nest and rule carries the
        // parameter spine in front of its fields, and the recursor's bottom
        // takes `p⃗` from `vars[..np]`. [`Decline::Params`] survives as the exit
        // for a declaration whose *type former nest* refuses to build — which is
        // a decline about this declaration, not about parameters in general.
        Ok(())
    }

    /// **The spec walk** — `WIRING-DESIGN.md` §3.2, steps 2–4.
    ///
    /// Walks the declaration's own type and then each constructor's, at ground
    /// levels, with every binder opened at a `ctx.mk_unique` local whose kernel
    /// variable is reserved *first* — the `rec_nest` discipline, so that the
    /// interpretation of a later type puts that variable exactly where the
    /// binder was.
    ///
    /// `reuse` supplies the kernel variables instead of minting them, which is
    /// what makes a cached [`GenInd`]'s guard meaningful: re-walking under the
    /// *same* variables reproduces the same `βⱼ` bodies exactly when the
    /// interpretation is canonical, and produces different ones exactly when it
    /// is not.
    ///
    /// Returns the walk, or the reason it declined. Nothing here derives
    /// anything: the walk builds terms and reserves variables, and every exit
    /// is `Err`.
    #[allow(clippy::type_complexity)]
    fn walk_spec(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        ind_name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
        reuse: Option<&GenInd>,
    ) -> Result<SpecWalk, Decline> {
        let decls = self.decls;
        self.gen_scope(ctx, &ind_name, levels)?;
        let ind = decls.get_inductive(&ind_name).ok_or(Decline::Shape)?;
        let np = ind.num_params as usize;

        // ── 2. The declaration's own type, at these levels ──────────────────
        let ty = ctx.subst_expr_levels(ind.info.ty, ind.info.uparams, levels);
        let mut param_vars: Vec<FreeVar> = Vec::with_capacity(np);
        let mut param_doms: Vec<Term> = Vec::with_capacity(np);
        let mut param_locals: Vec<ExprPtr<'t>> = Vec::with_capacity(np);
        let mut cur = ty;
        for i in 0..np {
            let Expr::Pi { binder_name, binder_style, binder_type, body, .. } = ctx.read_expr(cur)
            else {
                return Err(Decline::Shape)
            };
            param_doms.push(self.interp(ctx, binder_type));
            let local = ctx.mk_unique(binder_name, binder_style, binder_type);
            let lkey = unique_key(ctx, local).ok_or(Decline::Shape)?;
            let v = match reuse {
                Some(g) => *g.param_vars.get(i).ok_or(Decline::Shape)?,
                None => self.env_mut().fresh_var(),
            };
            self.locals.insert(lkey, v);
            param_vars.push(v);
            param_locals.push(local);
            cur = ctx.inst(body, &[local]);
        }
        if !matches!(ctx.read_expr(cur), Expr::Sort { .. }) {
            return Err(Decline::Shape)
        }

        // ── 3. Each constructor's type, at the *same* locals ────────────────
        let n = ind.all_ctor_names.len();
        let mut ctors: Vec<Option<CtorWalk>> = (0..n).map(|_| None).collect();
        for cn in ind.all_ctor_names.iter() {
            let c = decls.get_constructor(cn).ok_or(Decline::Unavailable)?;
            let i = c.ctor_idx as usize;
            if i >= n || ctors[i].is_some() {
                return Err(Decline::Shape)
            }
            if c.num_params as usize != np {
                return Err(Decline::Shape)
            }
            let cty = ctx.subst_expr_levels(c.info.ty, c.info.uparams, levels);
            // The first `np` binders are the declaration's parameters. Lean
            // guarantees they are the same expressions; verify, and open them
            // at the *same* locals, so every constructor's `βⱼ` bodies and
            // hypotheses are stated at one set of variables.
            let mut cur = cty;
            for local in param_locals.iter() {
                let Expr::Pi { body, .. } = ctx.read_expr(cur) else { return Err(Decline::Shape) };
                cur = ctx.inst(body, &[*local]);
            }

            let nf = c.num_fields as usize;
            let mut order: Vec<Slot> = Vec::with_capacity(nf);
            let mut field_vars: Vec<FreeVar> = Vec::with_capacity(nf);
            let mut field_doms: Vec<FieldDom> = Vec::with_capacity(nf);
            let mut beta_bodies: Vec<Term> = Vec::new();
            let mut plain_vars: Vec<FreeVar> = Vec::new();
            let mut recs = 0usize;
            for f in 0..nf {
                let Expr::Pi { binder_name, binder_style, binder_type, body, .. } = ctx.read_expr(cur)
                else {
                    return Err(Decline::Shape)
                };
                let is_rec = self.is_ind_spine(ctx, binder_type, &ind_name, levels, &param_locals);
                let slot = if is_rec {
                    Slot::Rec
                } else {
                    // **Before** any `interp`: a `Π` whose ultimate codomain is
                    // the declaration is a function-typed recursive argument,
                    // and interpreting it would recurse into the declaration
                    // being built. `CtorSpec::recs` cannot express it.
                    let mut cod = binder_type;
                    while let Expr::Pi { body, .. } = ctx.read_expr(cod) {
                        cod = body;
                    }
                    if self.mentions_const(ctx, cod, &ind.all_ind_names) {
                        return Err(Decline::FunRecArg)
                    }
                    if self.mentions_const(ctx, binder_type, &ind.all_ind_names) {
                        return Err(Decline::SelfMention)
                    }
                    Slot::Plain
                };
                let v = match reuse {
                    Some(g) => *g
                        .field_vars
                        .get(i)
                        .and_then(|vs| vs.get(f))
                        .ok_or(Decline::Shape)?,
                    None => self.env_mut().fresh_var(),
                };
                match slot {
                    Slot::Rec => {
                        recs += 1;
                        field_doms.push(FieldDom::Rec);
                    }
                    Slot::Plain => {
                        // The variable is reserved *before* the type is
                        // interpreted, exactly as `rec_nest` does, so that a
                        // later field's type puts it where the binder was.
                        let body_t = self.interp(ctx, binder_type);
                        // `βⱼ` of arity `np + j`: the parameters, then the
                        // earlier **plain** fields. A recursive field's
                        // variable is deliberately absent, which is what makes
                        // a dependence on it a decline rather than a wrong
                        // arity.
                        let mut xs = param_vars.clone();
                        xs.extend(plain_vars.iter().copied());
                        if field_vars
                            .iter()
                            .zip(order.iter())
                            .any(|(fv, s)| *s == Slot::Rec && body_t.occurs_free(*fv))
                        {
                            return Err(Decline::RecFieldDep)
                        }
                        // **On a reuse walk the symbol comes from the stored
                        // translation, never from a fresh `define_abbrev`.**
                        // The `Ctor::mem` this walk's results are matched
                        // against mentions the *stored* `βⱼ`; a freshly minted
                        // one is a different symbol, the antecedents would not
                        // line up, and the constructor rule would silently
                        // fail to be registered. (It could not go the other
                        // way — `gen_ctor_nest` compares before it uses — but
                        // a rule that is never built is a diffuse gap, which
                        // is exactly the failure mode this whole boundary is
                        // arranged to avoid.)
                        let (sym, beta_ax) = match reuse {
                            Some(g) => g
                                .betas
                                .get(i)
                                .and_then(|bs| bs.get(beta_bodies.len()))
                                .cloned()
                                .ok_or(Decline::Shape)?,
                            // The explicit recursive-field check above has
                            // already fired, so a refusal here is the
                            // free-variable guard: a level variable the
                            // `np + i` arity contract cannot name.
                            None => derived::define_abbrev(&mut self.env_mut(), &xs, &body_t)
                                .ok_or(Decline::LevelVar)?,
                        };
                        field_doms.push(FieldDom::Plain(body_t.clone(), sym, beta_ax));
                        beta_bodies.push(body_t);
                        plain_vars.push(v);
                    }
                }
                order.push(slot);
                field_vars.push(v);
                let local = ctx.mk_unique(binder_name, binder_style, binder_type);
                let lkey = unique_key(ctx, local).ok_or(Decline::Shape)?;
                self.locals.insert(lkey, v);
                cur = ctx.inst(body, &[local]);
            }
            // ── 4. The codomain is the declaration at its own parameters ────
            if !self.is_ind_spine(ctx, cur, &ind_name, levels, &param_locals) {
                return Err(Decline::Shape)
            }
            ctors[i] = Some(CtorWalk {
                order,
                field_vars,
                field_doms,
                beta_bodies,
                recs,
            });
        }
        let ctors: Vec<CtorWalk> = ctors.into_iter().collect::<Option<_>>().ok_or(Decline::Shape)?;
        Ok(SpecWalk { param_vars, param_doms, ctors })
    }

    /// The thread's [`derived::inductive::Machine`], built on first use over
    /// [`Inductives`]'s `Wtype` and `Bound`.
    fn machine(&mut self) -> Option<Rc<std::cell::RefCell<derived::inductive::Machine>>> {
        self.core.machine(&self.pre)
    }

    /// **The translated declaration** for `ind_name` at `levels`, from the
    /// per-thread cache or freshly built. `None` is a counted decline.
    fn gen_ind(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        ind_name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<Rc<GenInd>> {
        if self.spec_active.contains(&ind_name) {
            note_decline(Decline::Reentrant);
            return None
        }
        // The per-backend memo. See [`TgBackend::gen_inds`]: within one backend
        // a declaration must have **one** carrier, or the terms this backend
        // hands the derived theorems are about two different sets.
        let local = (ind_name, self.interp_levels(ctx, levels));
        if let Some(hit) = self.gen_inds.get(&local) {
            return hit.clone()
        }
        self.spec_active.push(ind_name);
        let out = self.gen_ind_inner(ctx, ind_name, levels);
        self.spec_active.pop();
        // A transient decline — the constructors are not yet in the environment
        // — must not be memoised here either: the same backend may reach this
        // declaration again once they are. `Decline::Unavailable`.
        if out.is_some() || !self.spec_unavailable {
            self.gen_inds.insert(local, out.clone());
        }
        out
    }

    fn gen_ind_inner(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        ind_name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<Rc<GenInd>> {
        let lv = self.interp_levels(ctx, levels);
        let key = self.name_key(ind_name).map(|k| (k, lv.clone()));

        // A hit is a **hint**: the recorded `βⱼ` bodies are re-derived under
        // the recorded variables and compared. This is the `hoisted`
        // discipline — nothing is trusted from the cache, and a stale entry
        // costs a rebuild rather than a theorem about the wrong terms.
        if let Some(k) = key.as_ref() {
            let hit = self.shared.borrow().gen_inds.get(k).cloned();
            match hit {
                // A memoised decline: do not re-run the walk per obligation.
                Some(None) => return None,
                Some(Some(gi)) => {
                    match self.walk_spec(ctx, ind_name, levels, Some(&gi)) {
                        Ok(w) => {
                            let agrees = w.ctors.len() == gi.orders.len()
                                && w.param_doms == gi.param_doms
                                && w.ctors.iter().enumerate().all(|(i, c)| {
                                    c.order == gi.orders[i] && c.beta_bodies == gi.beta_bodies[i]
                                });
                            if agrees {
                                return Some(gi)
                            }
                            // The interpretation is not canonical across
                            // backends after all. Counted, so that "the cache
                            // never hits" can be told apart from "the cache
                            // never agrees" — the distinction the `const_syms`
                            // drift row exists to make.
                            GEN_GUARD_MISS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        }
                        // The walk declined outright; the rebuild below counts
                        // the reason. Not a guard miss: nothing disagreed.
                        Err(_) => {}
                    }
                }
                None => {}
            }
        }

        let built = self.gen_ind_build(ctx, ind_name, levels);
        if let Some(k) = key {
            let mut sh = self.shared.borrow_mut();
            match (&built, sh.gen_inds.get(&k)) {
                // A **transient** miss is never memoised: see
                // [`Decline::Unavailable`].
                (None, _) if self.spec_unavailable => {}
                // Never replace a translation with a decline. A guard miss
                // means *this* backend must not use the stored package; it does
                // not mean the package is wrong for the backend that built it,
                // and the guard runs again next time either way.
                (None, Some(Some(_))) => {}
                _ => {
                    sh.gen_inds.insert(k, built.clone());
                }
            }
        }
        built
    }

    fn gen_ind_build(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        ind_name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<Rc<GenInd>> {
        self.spec_unavailable = false;
        let walk = match self.walk_spec(ctx, ind_name, levels, None) {
            Ok(w) => w,
            Err(d) => {
                self.spec_unavailable = d == Decline::Unavailable;
                note_decline(d);
                return None
            }
        };
        let np = walk.param_vars.len();
        let mut cspecs = Vec::with_capacity(walk.ctors.len());
        for c in walk.ctors.iter() {
            let args: Vec<FnSym> = c
                .field_doms
                .iter()
                .filter_map(|d| match d {
                    FieldDom::Plain(_, sym, _) => Some(*sym),
                    FieldDom::Rec => None,
                })
                .collect();
            cspecs.push(CtorSpec::with_order(args, c.recs, c.order.clone())?);
        }
        let spec = DeclSpec::new(np, cspecs);
        // Belt and braces: the derived layer re-checks this and declines
        // otherwise, but a wrong `βⱼ` arity here would derive true theorems
        // about the wrong declaration, so it is worth its own exit.
        if !spec.well_formed() {
            note_decline(Decline::Build);
            return None
        }
        let mach = match self.machine() {
            Some(m) => m,
            None => {
                note_decline(Decline::Machinery);
                return None
            }
        };
        let ind = {
            // Two `RefCell`s, not two borrows of one: `self.env_mut()` borrows
            // `Shared`, `mach.borrow_mut()` borrows the machine's own cell, and
            // `Inductive::build` reaches neither back.
            let mut m = mach.borrow_mut();
            let mut env = self.env_mut();
            derived::inductive::Inductive::build(&mut env, &mut m, &spec)
        };
        let Some(ind) = ind else {
            note_decline(Decline::Build);
            return None
        };
        GEN_BUILT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Some(Rc::new(GenInd {
            param_vars: walk.param_vars,
            param_doms: walk.param_doms,
            orders: walk.ctors.iter().map(|c| c.order.clone()).collect(),
            field_vars: walk.ctors.iter().map(|c| c.field_vars.clone()).collect(),
            beta_bodies: walk.ctors.iter().map(|c| c.beta_bodies.clone()).collect(),
            betas: walk
                .ctors
                .iter()
                .map(|c| {
                    c.field_doms
                        .iter()
                        .filter_map(|d| match d {
                            FieldDom::Plain(_, sym, ax) => Some((*sym, ax.clone())),
                            FieldDom::Rec => None,
                        })
                        .collect()
                })
                .collect(),
            ind: Rc::new(ind),
        }))
    }

    /// **`⟦c⟧` on the general path**, for an inductive or one of its
    /// constructors — `WIRING-DESIGN.md` §5.
    ///
    /// `derived::inductive` speaks in `ind(p⃗)` and `ctor_i(y⃗,r⃗)` at variables;
    /// Lean speaks in curried applications. This is the bridge, and for a
    /// **parameterless** declaration it is short: the type former is the bare
    /// abbreviation of `ind()`; a nullary constructor is the bare abbreviation
    /// of `ctor_i()` with `Ctor::mem` — a *closed* theorem, because
    /// `inductive/shared.rs`'s `Ctx(None)` discipline drops the hypothesis
    /// entirely when there is nothing to assume — transported onto it; and a
    /// constructor with fields is [`Self::gen_ctor_nest`].
    ///
    /// Every theorem registered here is checked against the membership being
    /// claimed before it is stored, exactly as [`Self::ind_const`]'s
    /// enumeration arm does.
    fn gen_const(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
    ) -> Option<Term> {
        let decls = self.decls;
        let (ind_name, ctor) = match decls.get_declar(&name)? {
            Declar::Inductive(_) => (name, None),
            Declar::Constructor(c) =>
                (c.inductive_name, Some((c.ctor_idx as usize, c.num_fields as usize))),
            _ => return None,
        };
        // **One nest per constructor per backend.** `gen_ctor_nest` mints a
        // fresh graph symbol per level, so building it twice gives two
        // `⟦cᵢ⟧`s with the same meaning and different names — and then
        // `ind_abbrev` sees a changed body, re-mints, and the second overwrites
        // the first's [`GenCtorBridge`] and [`CtorRule`] while `interp`'s own
        // cache still hands out the first. That is not hypothetical: it cost 54
        // of `init-prelude`'s `Lean.Name`/`SourceInfo` ι sites, which is how it
        // was found. `interp` memoises by `ExprPtr` and the same constant
        // reaches here under several, so the memo has to be by name and levels.
        let lv = self.interp_levels(ctx, levels);
        if let Some(hit) = self.gen_consts.get(&(name, lv.clone())) {
            return hit.clone()
        }
        let out = self.gen_const_uncached(ctx, name, levels, ind_name, ctor, &lv);
        self.gen_consts.insert((name, lv), out.clone());
        out
    }

    /// **The type former's nest** — [`GenTyNest`], built once per declaration
    /// per backend.
    ///
    /// `np` levels of lambda graph over the parameter domains the spec walk
    /// interpreted, with `ind(p⃗)` at the bottom, and the conditional beta chain
    /// that takes the Lean spine to it. At `np = 0` the loop does not run, the
    /// body *is* `ind()` and [`Self::nest_spine_eq`] hands back the defining
    /// equation unchanged — so the parameterless path is exactly what it was.
    ///
    /// Everything is checked against what it must say before it is stored: the
    /// bottom against `ind(p⃗)` at [`GenInd::param_vars`], and the chain against
    /// `H_p → spine = ind(p⃗)`. A refusal is [`Decline::Params`], raised by the
    /// caller — the constant stays opaque, as it did when `np > 0` declined
    /// outright.
    fn gen_ty_nest(
        &mut self,
        gi: &Rc<GenInd>,
        ind_name: NamePtr<'t>,
        lv: &[Term],
    ) -> Option<Rc<GenTyNest>> {
        let key = (ind_name, lv.to_vec());
        if let Some(n) = self.gen_ty_nests.get(&key) {
            return Some(n.clone())
        }
        // The per-thread entry, usable exactly when it was built over **this**
        // translation. See [`Shared::gen_ty_nests`].
        let shared_key = self.name_key(ind_name).map(|k| (k, lv.to_vec()));
        let cached = shared_key
            .as_ref()
            .and_then(|k| self.shared.borrow().gen_ty_nests.get(k).cloned());
        if let Some((cgi, tn)) = cached {
            if Rc::ptr_eq(&cgi, gi) {
                if let Some(tn) = self.adopt_ty_nest(&tn) {
                    self.gen_ty_nests.insert(key, tn.clone());
                    return Some(tn)
                }
            }
            note_dt(Dt::NestDrift);
        }
        let ap = self.pre.ap.clone();
        let vars = gi.param_vars.clone();
        let doms = gi.param_doms.clone();
        if doms.len() != vars.len() {
            return None
        }
        let np = vars.len();
        let bottom = gi.ind.ty_of(vars.iter().map(|v| Term::var(*v)).collect());
        // The ω-prefix (see [`Self::omega_prefix`]): level variables the
        // domains or the carrier mention, threaded as leading arguments of
        // every body symbol and graph in the nest so `define_abbrev`'s
        // free-variable guard is satisfied by naming them rather than by
        // declining the nest.
        let omega = self.omega_prefix(doms.iter().chain(std::iter::once(&bottom)));
        let wts: Vec<Term> = omega.iter().map(|v| Term::var(*v)).collect();

        // ── The nest, innermost first — [`Self::gen_ctor_nest`]'s loop ──────
        let mut betas: Vec<Thm> = Vec::with_capacity(np);
        let mut t_defs: Vec<Thm> = Vec::with_capacity(np);
        let mut inner: Option<Term> = None;
        for k in (0..np).rev() {
            let body = inner.unwrap_or_else(|| bottom.clone());
            let mut xs: Vec<FreeVar> = omega.clone();
            xs.extend_from_slice(&vars[..=k]);
            let (tk, tk_def) = derived::define_abbrev(&mut self.env_mut(), &xs, &body)?;
            let (lamk, lamk_ax) = lambda_n(&mut self.env_mut(), &ap, tk)?;
            let betak = beta_conditional_n(&mut self.env_mut(), &ap, tk, lamk, &lamk_ax)?;
            betas.push(betak);
            t_defs.push(tk_def);
            let mut args: Vec<Term> = wts.clone();
            args.extend(vars[..k].iter().map(|v| Term::var(*v)));
            args.push(doms[k].clone());
            inner = Some(Term::apply(lamk, args));
        }
        betas.reverse();
        t_defs.reverse();
        let body = inner.unwrap_or_else(|| bottom.clone());
        let (head, head_ax) = self.ind_abbrev(ind_name, lv, &body)?;

        let prems: Vec<Formula> =
            (0..np).map(|i| Formula::mem(Term::var(vars[i]), doms[i].clone())).collect();
        let (spine, spine_eq) =
            self.nest_spine_eq(&head, &head_ax, &betas, &t_defs, &omega, &vars, &doms, &prems)?;
        // The guard: the chain must land on `ind(p⃗)` under exactly `H_p`, or it
        // is not the bridge the constructor rules and the ι rule will use.
        let claim = Formula::eq(spine.clone(), bottom);
        let want = match derived::conj_of(&prems) {
            None => claim,
            Some(h) => Formula::imp(h, claim),
        };
        if *spine_eq.concl() != want {
            return None
        }
        let head_sym = self.parts.get(&head).map(|(f, _)| *f);
        let out = Rc::new(GenTyNest {
            head,
            head_ax,
            head_sym,
            spine_eq_all: derived::gen_all(&vars, &spine_eq),
            vars,
            doms,
            prems,
            spine,
            spine_eq,
        });
        if let (Some(k), Some(_)) = (shared_key, out.head_sym) {
            self.shared
                .borrow_mut()
                .gen_ty_nests
                .entry(k)
                .or_insert((gi.clone(), out.clone()));
        }
        self.gen_ty_nests.insert(key, out.clone());
        Some(out)
    }

    /// Take a [`GenTyNest`] built by another backend into this one.
    ///
    /// The nest's *terms* are already right — the `Rc::ptr_eq` on the
    /// [`GenInd`] at the call site is what establishes that — but two things
    /// about `⟦T⟧` are per backend and have to be re-established here, or the
    /// nest is a set of true theorems this backend cannot use:
    ///
    /// * its **applicative shape**, which [`Self::skeleton`] and every rule
    ///   that opens a term read out of `parts`, and which is recorded by
    ///   [`Self::mk`] rather than by the symbol existing;
    /// * its **defining equation** in `abbrev_defs`, which is how the
    ///   unfolding chain gets from `⟦T⟧` to the graph underneath it.
    ///
    /// Rebuilding the head with `mk` and checking it against the stored one is
    /// what turns "the same symbol" into a checked claim rather than an
    /// assumption; a mismatch declines the entry and the nest is rebuilt.
    fn adopt_ty_nest(&mut self, tn: &Rc<GenTyNest>) -> Option<Rc<GenTyNest>> {
        // The head's arguments are read off the stored head itself: a carrier
        // over ω-vocabulary parameter variables is a symbol *applied to them*
        // (`LEVELPOLY.md` §1.6), and rebuilding it nullary would be an arity
        // error, not a decline.
        let args = match tn.head.as_app() {
            Some((_, args)) => args.to_vec(),
            None => vec![],
        };
        let head = self.mk(tn.head_sym?, args);
        if head != tn.head {
            return None
        }
        if tn.head_ax.concl().as_eq()?.0 != head {
            return None
        }
        self.abbrev_defs.insert(head, tn.head_ax.clone());
        Some(tn.clone())
    }

    #[allow(clippy::type_complexity)]
    fn gen_const_uncached(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: NamePtr<'t>,
        levels: LevelsPtr<'t>,
        ind_name: NamePtr<'t>,
        ctor: Option<(usize, usize)>,
        lv: &[Term],
    ) -> Option<Term> {
        let gi = self.gen_ind(ctx, ind_name, levels)?;
        let lv = lv.to_vec();
        let mach = self.machine()?;
        let np = gi.param_vars.len();

        // ── The type former ─────────────────────────────────────────────────
        let Some(tn) = self.gen_ty_nest(&gi, ind_name, &lv) else {
            note_decline(Decline::Params);
            return None
        };
        let (ty_t, ty_ax) = (tn.head.clone(), tn.head_ax.clone());
        let Some((i, nf)) = ctor else { return Some(ty_t) };
        if i >= gi.ind.ctors.len() || nf != gi.orders[i].len() {
            return None
        }

        if np == 0 && nf == 0 {
            let ty_body = gi.ind.ty_of(Vec::new());
            // ── A nullary constructor: a term, and a closed membership ──────
            let ctor_body = {
                let m = mach.borrow();
                gi.ind.ctor_term(&m, i, &[], &[])?
            };
            let (ct, ct_ax) = self.ind_abbrev(name, &lv, &ctor_body)?;
            // `Ctor::mem` is `⊢ ctor_i() ∈ ind()` outright — no `∀`, no
            // antecedent — for a parameterless nullary constructor. Checked,
            // not assumed: a theorem of any other shape is not used.
            let raw = gi.ind.ctors[i].mem.clone();
            if *raw.concl() != Formula::mem(ctor_body.clone(), ty_body.clone()) {
                return None
            }
            // Two Leibniz steps along the defining equations, each run
            // backwards: first the constructor's, then the type's.
            let back_c = derived::eq_symm(&mut self.env_mut(), &ct_ax)?;
            let w = self.env_mut().fresh_var();
            let leib = Thm::eq_leibniz(
                ctor_body,
                ct.clone(),
                w,
                Formula::mem(Term::var(w), ty_body.clone()),
            );
            let at_ct = Thm::mp(&Thm::mp(&leib, &back_c)?, &raw)?;

            let back_t = derived::eq_symm(&mut self.env_mut(), &ty_ax)?;
            let w = self.env_mut().fresh_var();
            let leib =
                Thm::eq_leibniz(ty_body, ty_t.clone(), w, Formula::mem(ct.clone(), Term::var(w)));
            let out = Thm::mp(&Thm::mp(&leib, &back_t)?, &at_ct)?;
            // The guard: a theorem that does not literally say `⟦c⟧ ∈ ⟦T⟧` is
            // not registered, whatever it proves.
            if *out.concl() != Formula::mem(ct.clone(), ty_t.clone()) {
                return None
            }
            self.ind_mems.insert((ct.clone(), ty_t), out);
            GEN_CTORS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return Some(ct)
        }

        // The walk is re-run under the *recorded* variables, which is what
        // makes its `βⱼ` bodies the very terms `gi`'s theorems mention.
        let walk = self.walk_spec(ctx, ind_name, levels, Some(&gi)).ok()?;
        self.gen_ctor_nest(&gi, &tn, &mach, name, &walk, &lv, i)
    }

    /// **A constructor with fields**: the curried nest, and the [`CtorRule`]
    /// its applications are typed by.
    ///
    /// Two things make this more than [`Self::gen_const`]'s nullary case.
    ///
    /// *The term is a nest.* Lean applies `List.cons α h t` one argument at a
    /// time, so `⟦List.cons⟧` has to be a **set**: a nest of `np + k + m`
    /// lambda graphs, [`RecNest`]'s construction with `ctor_i(y⃗,r⃗)` at the
    /// bottom, split out of the variable list by the order mask. The
    /// **parameters are ordinary levels of it** — they precede the fields, as
    /// they do in the Lean spine — even though `ctor_i(y⃗,r⃗)` itself mentions
    /// none of them: `p⃗` occurs in a constructor's *type*, never in its value.
    ///
    /// *The premises must be in Lean argument order.* [`CtorRule`]'s `prems`
    /// are positional against the spine — [`Self::has_type_ctor_app`] rejects a
    /// premise whose subject is not the argument at that position — while
    /// `Ctor::mem`'s hypothesis is plains-then-recs and mentions no parameter
    /// at all. So `⊢ H_declared → H_mem` is built atom by atom out of
    /// `H_declared`, which **drops** the parameter atoms, **reorders** the
    /// field ones, and carries the two coordinate changes the boundary needs: a
    /// plain field's type is stated at its interpretation `⟦β⟧` rather than at
    /// the symbol `βⱼ(p⃗,y⃗)` abbreviating it, and a recursive field's at the
    /// Lean spine `⟦T p⃗⟧` rather than at `ind(p⃗)`. Both are what a *use site*
    /// states, which is the whole point of the rule.
    ///
    /// The parameter atoms are not dropped from the *rule*, only from `H_mem`:
    /// they are what discharges the type former's own conditional bridge
    /// ([`GenTyNest`]), which is how a recursive field's `⟦T p⃗⟧` reaches
    /// `ind(p⃗)` at all.
    ///
    /// An unpermuted rule would fail the positional check at every interleaved
    /// constructor: a gap, not an unsoundness, but 100% of the sites at every
    /// masked prelude shape — `Lean.Name.str` alone is `Rec, Plain`.
    #[allow(clippy::too_many_arguments)]
    fn gen_ctor_nest(
        &mut self,
        gi: &Rc<GenInd>,
        tn: &Rc<GenTyNest>,
        mach: &Rc<std::cell::RefCell<derived::inductive::Machine>>,
        name: NamePtr<'t>,
        walk: &SpecWalk,
        lv: &[Term],
        i: usize,
    ) -> Option<Term> {
        let ap = self.pre.ap.clone();
        let cw = walk.ctors.get(i)?;
        if cw.order != gi.orders[i] || cw.field_vars != gi.field_vars[i] {
            return None
        }
        if walk.param_vars != tn.vars || walk.param_doms != tn.doms {
            return None
        }
        let order = &cw.order;
        let nf = order.len();
        let np = tn.vars.len();
        // **The nest runs over the parameters too.** Lean writes
        // `List.cons α h t` as a four-deep spine, so `⟦List.cons⟧` is a nest of
        // `np + nf` lambda graphs; the parameters are ordinary levels of it, and
        // the constructor's own fields sit underneath.
        let mut vars: Vec<FreeVar> = tn.vars.clone();
        vars.extend(cw.field_vars.iter().copied());

        // The domains the nest is built over: a parameter's is the
        // interpretation of its binder type, a plain field's the interpretation
        // of its Lean type, and a recursive field's the **spine**
        // `app-spine(⟦T⟧, p⃗)` — what a use site's obligation `t ∈ ⟦T p⃗⟧` is
        // literally stated at.
        let mut doms: Vec<Term> = tn.doms.clone();
        doms.extend(cw.field_doms.iter().map(|d| match d {
            FieldDom::Plain(t, _, _) => t.clone(),
            FieldDom::Rec => tn.spine.clone(),
        }));

        // ── The bottom: `ctor_i(y⃗, r⃗)`, split out by the mask ──────────────
        //
        // The parameters do **not** appear in it: §5.2's constructor term is a
        // tag and a function, and `p⃗` occurs only in its *type*
        // (`derived/src/inductive/ctor.rs`'s header).
        let (mut ys, mut rs) = (Vec::new(), Vec::new());
        for (f, slot) in order.iter().enumerate() {
            match slot {
                Slot::Plain => ys.push(Term::var(cw.field_vars[f])),
                Slot::Rec => rs.push(Term::var(cw.field_vars[f])),
            }
        }
        let ps: Vec<Term> = tn.vars.iter().map(|v| Term::var(*v)).collect();
        let ty_body = gi.ind.ty_of(ps.clone());
        let bottom = {
            let m = mach.borrow();
            gi.ind.ctor_term(&m, i, &ys, &rs)?
        };

        // ── The nest another backend already built, if it is this one ───────
        //
        // Everything below is a `define_abbrev` and a `lambda_n` over the four
        // things now in hand — `gi`, `tn`, `vars` and `doms` — so an entry that
        // agrees on all four is the very nest this backend would build, up to
        // symbol identity. See [`Shared::gen_ctor_nests`].
        let shared_key = self.name_key(name).map(|k| (k, lv.to_vec()));
        let cached = shared_key
            .as_ref()
            .and_then(|k| self.shared.borrow().gen_ctor_nests.get(k).cloned());
        if let Some(sc) = cached {
            if Rc::ptr_eq(&sc.gi, gi) && Rc::ptr_eq(&sc.tn, tn) && sc.vars == vars && sc.doms == doms
            {
                if let Some(ct) = self.adopt_ctor_nest(&sc, name, lv, tn, &bottom) {
                    GEN_CTORS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    return Some(ct)
                }
            }
            note_dt(Dt::CtorNestDrift);
        }

        // ── The nest, innermost first — `rec_nest`'s loop with a new bottom ─
        //
        // With the ω-prefix of [`Self::omega_prefix`], as in
        // [`Self::gen_ty_nest`]: a field or parameter domain at a variable
        // level would otherwise make `define_abbrev` refuse the whole
        // constructor.
        let omega = self.omega_prefix(doms.iter().chain(std::iter::once(&bottom)));
        let wts: Vec<Term> = omega.iter().map(|v| Term::var(*v)).collect();
        let depth = np + nf;
        let mut betas: Vec<Thm> = Vec::with_capacity(depth);
        let mut t_defs: Vec<Thm> = Vec::with_capacity(depth);
        let mut inner: Option<Term> = None;
        for k in (0..depth).rev() {
            let body = inner.unwrap_or_else(|| bottom.clone());
            let mut xs: Vec<FreeVar> = omega.clone();
            xs.extend_from_slice(&vars[..=k]);
            let (tk, tk_def) = derived::define_abbrev(&mut self.env_mut(), &xs, &body)?;
            let (lamk, lamk_ax) = lambda_n(&mut self.env_mut(), &ap, tk)?;
            let betak = beta_conditional_n(&mut self.env_mut(), &ap, tk, lamk, &lamk_ax)?;
            betas.push(betak);
            t_defs.push(tk_def);
            let mut args: Vec<Term> = wts.clone();
            args.extend(vars[..k].iter().map(|v| Term::var(*v)));
            args.push(doms[k].clone());
            inner = Some(Term::apply(lamk, args));
        }
        betas.reverse();
        t_defs.reverse();
        let (ct, ct_ax) = self.ind_abbrev(name, lv, &inner?)?;

        // ── The premises, in Lean declared order: parameters, then fields ───
        let prems: Vec<Formula> =
            (0..depth).map(|f| Formula::mem(Term::var(vars[f]), doms[f].clone())).collect();
        let h = derived::conj_of(&prems);
        let hr = h.as_ref();
        // `⊢ H → app-spine(⟦T⟧,p⃗) = ind(p⃗)`, the type former's own bridge
        // restated under this rule's premises.
        let ty_eq = under_prefix(&tn.spine_eq, &tn.prems, &prems)?;

        // ── `⊢ H → spine = ctor_i(y⃗,r⃗)` ───────────────────────────────────
        let (spine, spine_eq) =
            self.nest_spine_eq(&ct, &ct_ax, &betas, &t_defs, &omega, &vars, &doms, &prems)?;

        // ── `⊢ H → H_mem`, atom by atom, in the order `Ctor::mem` states ────
        //
        // The plain atoms first, then the recursive ones — `ctor_atoms`' order
        // — each carried from `H`'s own atom by one Leibniz step.
        let mut mem_parts: Vec<Thm> = Vec::with_capacity(nf);
        let mut mem_atoms: Vec<Formula> = Vec::with_capacity(nf);
        let mut plain_seen = 0usize;
        for pass_rec in [false, true] {
            for (f, slot) in order.iter().enumerate() {
                if matches!(slot, Slot::Rec) != pass_rec {
                    continue
                }
                let at_h = derived::conj_proj(&prems, np + f)?;
                let carried = match slot {
                    // `⟦β⟧ ↦ βⱼ(p⃗, y₀…y_{j-1})`, backwards along `βⱼ`'s own
                    // defining equation.
                    Slot::Plain => {
                        let FieldDom::Plain(_, _, beta_ax) = &cw.field_doms[f] else { return None };
                        let mut at: Vec<Term> = ps.clone();
                        at.extend(ys[..plain_seen].iter().cloned());
                        let inst = derived::inst_all(beta_ax, &at)?;
                        let back = derived::eq_symm(&mut self.env_mut(), &inst)?;
                        plain_seen += 1;
                        self.u_mem_along(&at_h, &back, hr)?
                    }
                    // `app-spine(⟦T⟧,p⃗) ↦ ind(p⃗)`, forwards along the type's —
                    // conditional, because the beta chain is.
                    Slot::Rec => self.uu_mem_along(&at_h, &ty_eq, hr)?,
                };
                mem_atoms.push(u_concl(&carried, hr)?);
                mem_parts.push(carried);
            }
        }

        // ── `Ctor::mem` at these variables, and the claim it must make ──────
        //
        // `⊢ ∀p⃗ ∀y⃗ ∀r⃗. (H_mem → ctor_i(y⃗,r⃗) ∈ ind(p⃗))`, and **without** the
        // `H_mem →` when the constructor has no fields at all — the `Ctx(None)`
        // discipline. Both shapes are checked rather than assumed.
        let mut inst_at: Vec<Term> = ps.clone();
        inst_at.extend(ys.iter().cloned());
        inst_at.extend(rs.iter().cloned());
        let mem = derived::inst_all(&gi.ind.ctors[i].mem, &inst_at)?;
        let at_ind_concl = Formula::mem(bottom.clone(), ty_body.clone());
        let (at_ind, hmem) = match derived::conj_of(&mem_atoms) {
            None => {
                if *mem.concl() != at_ind_concl {
                    return None
                }
                (u_a1i(&mem, hr), None)
            }
            Some(mem_hyp) => {
                if *mem.concl() != Formula::imp(mem_hyp, at_ind_concl) {
                    return None
                }
                let mut acc = mem_parts.pop()?;
                while let Some(p) = mem_parts.pop() {
                    acc = match hr {
                        None => derived::and_intro(&p, &acc),
                        Some(_) => derived::hyp_and(&p, &acc)?,
                    };
                }
                (u_syl(&acc, &mem, hr)?, Some(acc))
            }
        };
        // `⊢ H → ctor_i(y⃗,r⃗) ∈ app-spine(⟦T⟧,p⃗)`.
        let back_t = self.u_eq_symm(&ty_eq, hr)?;
        let at_ty = self.uu_mem_along(&at_ind, &back_t, hr)?;

        // ── `⊢ H → spine ∈ app-spine(⟦T⟧,p⃗)` ───────────────────────────────
        let back = self.u_eq_symm(&spine_eq, hr)?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(
            bottom,
            spine.clone(),
            w,
            Formula::mem(Term::var(w), tn.spine.clone()),
        );
        let out = u_mp(&u_syl(&back, &leib, hr)?, &at_ty, hr)?;

        // The guard: the rule must say exactly what `has_type_ctor_app` will
        // instantiate it as — the premises in declared order, the subject the
        // Lean spine, the target the Lean spine of the type former.
        let claim = Formula::mem(spine, tn.spine.clone());
        if *out.concl() != Formula::imp(h?, claim) {
            return None
        }
        let rule = CtorRule { thm: derived::gen_all(&vars, &out), vars: vars.clone(), prems };
        self.ctor_rules.insert((name, lv.to_vec()), rule.clone());
        // The two theorems the general ι rule needs about this constructor, kept
        // rather than re-derived: `hmem` is `⊢ H → Hᵢ^ctor` — absent exactly
        // when the constructor has no fields, the `Ctx(None)` discipline — and
        // `spine_eq` is `⊢ H → spine = ctorᵢ(y⃗,r⃗)`. See [`GenCtorBridge`].
        let bridge = Rc::new(GenCtorBridge {
            spine: derived::gen_all(&vars, &spine_eq),
            mem: hmem.map(|m| derived::gen_all(&vars, &m)),
            np,
            vars: vars.clone(),
            order: order.clone(),
        });
        self.gen_ctor_bridges.insert((name, lv.to_vec()), bridge.clone());
        // The per-thread entry. `ct_sym` is what lets the next backend rebuild
        // `⟦cᵢ⟧` through its own [`Self::mk`]; without it the entry could not be
        // adopted, so it is what makes one.
        if let (Some(k), Some(ct_sym)) = (shared_key, self.parts.get(&ct).map(|(f, _)| *f)) {
            self.shared.borrow_mut().gen_ctor_nests.entry(k).or_insert_with(|| {
                Rc::new(SharedCtorNest {
                    gi: gi.clone(),
                    tn: tn.clone(),
                    ct_sym,
                    ct: ct.clone(),
                    ct_ax,
                    vars,
                    doms,
                    rule,
                    bridge,
                })
            });
        }
        GEN_CTORS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Some(ct)
    }

    /// Take a constructor's nest, built by another backend, into this one.
    ///
    /// [`Self::adopt_ty_nest`] at the constructor, and with more to re-establish
    /// because more is stored. The nest's *terms* are already right — the
    /// `Rc::ptr_eq` on the [`GenInd`] and the [`GenTyNest`] at the call site,
    /// together with the pointwise comparison of the variables and domains, is
    /// what establishes that. What is per backend is:
    ///
    /// * `⟦cᵢ⟧`'s **applicative shape** and that of the spine over it, which
    ///   [`Self::skeleton`] and every rule that opens a term reads out of
    ///   `parts`, and which [`Self::mk`] records rather than the symbol
    ///   existing;
    /// * its **defining equation** in `abbrev_defs`, the first link of the
    ///   unfolding chain, and its entry in `ind_syms`, so a second use of the
    ///   constant in this backend gets the same term;
    /// * the [`CtorRule`] and [`GenCtorBridge`] maps, which
    ///   [`Self::has_type_ctor_app`] and the general ι rule read.
    ///
    /// Nothing is trusted. The head is rebuilt and compared, and both stored
    /// theorems are **instantiated at this backend's variables and checked
    /// against the very claims they are used as** — [`ctor_nest_agrees`], which
    /// says what that pins. The bridge's `mem` is not re-checked here: it is
    /// built out of `gi.betas` and `gi.ind`, both fixed by the `Rc::ptr_eq`, and
    /// the ι rule checks at the point of use that it shares the `spine`
    /// theorem's antecedent (`iota: the constructor's two bridges do not share
    /// an antecedent`).
    fn adopt_ctor_nest(
        &mut self,
        sc: &Rc<SharedCtorNest>,
        name: NamePtr<'t>,
        lv: &[Term],
        tn: &GenTyNest,
        bottom: &Term,
    ) -> Option<Term> {
        let app = self.pre.ap.app;
        // As in [`Self::adopt_ty_nest`]: a constructor over ω-vocabulary
        // parameter variables is a symbol applied to them; the arguments are
        // read off the stored term rather than assumed nullary.
        let ct_args = match sc.ct.as_app() {
            Some((_, args)) => args.to_vec(),
            None => vec![],
        };
        let ct = self.mk(sc.ct_sym, ct_args);
        if ct != sc.ct || sc.ct_ax.concl().as_eq()?.0 != ct {
            return None
        }
        let args: Vec<Term> = sc.vars.iter().map(|v| Term::var(*v)).collect();
        let rule = derived::inst_all(&sc.rule.thm, &args)?;
        let bridge = derived::inst_all(&sc.bridge.spine, &args)?;
        {
            let parts = &mut self.parts;
            let mut mk = |f: FnSym, xs: Vec<Term>| record(parts, f, xs);
            ctor_nest_agrees(
                &mut mk,
                app,
                &ct,
                &sc.vars,
                &sc.doms,
                &tn.spine,
                bottom,
                rule.concl(),
                bridge.concl(),
            )?;
        }
        self.abbrev_defs.insert(ct.clone(), sc.ct_ax.clone());
        self.ind_syms.insert((name, lv.to_vec()), (ct.clone(), sc.ct_ax.clone()));
        self.ctor_rules.insert((name, lv.to_vec()), sc.rule.clone());
        self.gen_ctor_bridges.insert((name, lv.to_vec()), sc.bridge.clone());
        Some(ct)
    }

    /// `⊢ H → app(…app(⟦c⟧, x₀)…, x_{nf-1}) = body`, and the spine itself.
    ///
    /// [`Self::nest_chain`] without the `CondEq` wrapper and with the domain
    /// premises being `H`'s own atoms rather than derived obligations: at level
    /// `k` the premise is literally `prems[k]`, because the nest's domain at
    /// level `k` *is* the field's stated type.
    #[allow(clippy::too_many_arguments)]
    /// The ω-vocabulary parameter variables free in `terms`, sorted and
    /// deduplicated — the abstraction prefix a nest's body symbols carry
    /// (`LEVELPOLY.md` §5.4 blocker 2). A `Type u` parameter's domain
    /// interprets to `srt(u)` at the *variable* `u`, so a nest body mentions
    /// `u` free, and `define_abbrev`'s free-variable guard rightly refuses it
    /// unless the prefix names it. Sorting makes the prefix a function of the
    /// terms, so every backend building over the same terms builds the same
    /// symbol arities — the canonicity the shared nest stores require.
    fn omega_prefix<'a>(&self, terms: impl Iterator<Item = &'a Term>) -> Vec<FreeVar> {
        let mut fvs = Vec::new();
        for t in terms {
            t.free_vars(&mut fvs);
        }
        fvs.sort();
        fvs.dedup();
        fvs.retain(|v| self.is_param_omega_var(*v));
        fvs
    }

    /// `nest_spine_eq`'s betas and body definitions are `∀`-closed over the
    /// ω-prefix **and then** the graph parameters (`define_abbrev` and
    /// `beta_conditional_n` quantify every argument position), so the
    /// instantiation lists here lead with the ω terms. The membership
    /// premises `H_p` stay about the Lean parameters alone: an ω variable is
    /// a *level*, and its `u ∈ ω` fact is the quantified store's business
    /// (§5.3 step 5), not a spine premise.
    #[allow(clippy::too_many_arguments)]
    fn nest_spine_eq(
        &mut self,
        ct: &Term,
        ct_ax: &Thm,
        betas: &[Thm],
        t_defs: &[Thm],
        omega: &[FreeVar],
        vars: &[FreeVar],
        doms: &[Term],
        prems: &[Formula],
    ) -> Option<(Term, Thm)> {
        let app = self.pre.ap.app;
        let wts: Vec<Term> = omega.iter().map(|v| Term::var(*v)).collect();
        let h = derived::conj_of(prems);
        let hr = h.as_ref();
        let mut acc = u_a1i(ct_ax, hr);
        let mut spine = ct.clone();
        for k in 0..vars.len() {
            let x = Term::var(vars[k]);
            acc = self.u_app_cong(&acc, &x, hr)?;
            let mut inst: Vec<Term> = wts.clone();
            inst.extend(vars[..k].iter().map(|v| Term::var(*v)));
            inst.push(doms[k].clone());
            inst.push(x.clone());
            let cond = derived::inst_all(&betas[k], &inst)?;
            let prem = derived::conj_proj(prems, k)?;
            let beta = u_mp(&u_a1i(&cond, hr), &prem, hr)?;
            acc = self.u_eq_trans(&acc, &beta, hr)?;
            let mut inst_t: Vec<Term> = wts.clone();
            inst_t.extend(vars[..=k].iter().map(|v| Term::var(*v)));
            let td = derived::inst_all(&t_defs[k], &inst_t)?;
            acc = self.u_eq_trans(&acc, &u_a1i(&td, hr), hr)?;
            spine = self.mk(app, vec![spine, x]);
        }
        Some((spine, acc))
    }

    /// From `⊢ H → (a = b)` infer `⊢ H → (app(a,x) = app(b,x))`.
    fn u_app_cong(&mut self, ab: &Thm, x: &Term, h: Option<&Formula>) -> Option<Thm> {
        let (a, b) = u_concl(ab, h)?.as_eq()?;
        let app = self.pre.ap.app;
        let lhs = self.mk(app, vec![a.clone(), x.clone()]);
        let w = self.env_mut().fresh_var();
        let hole = self.mk(app, vec![Term::var(w), x.clone()]);
        let leib = Thm::eq_leibniz(a, b, w, Formula::eq(lhs.clone(), hole));
        u_mp(&u_syl(ab, &leib, h)?, &u_a1i(&Thm::eq_refl(lhs), h), h)
    }

    /// From `⊢ H → a = b` and `⊢ H → b = c` infer `⊢ H → a = c`.
    fn u_eq_trans(&mut self, ab: &Thm, bc: &Thm, h: Option<&Formula>) -> Option<Thm> {
        let (a, b) = u_concl(ab, h)?.as_eq()?;
        let (b2, c) = u_concl(bc, h)?.as_eq()?;
        if b != b2 {
            return None
        }
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(b, c, w, Formula::eq(a, Term::var(w)));
        u_mp(&u_syl(bc, &leib, h)?, ab, h)
    }

    /// From `⊢ H → a = b` infer `⊢ H → b = a`.
    fn u_eq_symm(&mut self, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
        let (a, b) = u_concl(ab, h)?.as_eq()?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(a.clone(), b, w, Formula::eq(Term::var(w), a.clone()));
        u_mp(&u_syl(ab, &leib, h)?, &u_a1i(&Thm::eq_refl(a), h), h)
    }

    /// From `⊢ H → x ∈ a` and `⊢ a = b` infer `⊢ H → x ∈ b`.
    fn u_mem_along(&mut self, xa: &Thm, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
        let (x, a) = u_concl(xa, h)?.as_mem()?;
        let (a2, b) = ab.concl().as_eq()?;
        if a != a2 {
            return None
        }
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(a, b, w, Formula::mem(x, Term::var(w)));
        u_syl(xa, &Thm::mp(&leib, ab)?, h)
    }

    /// [`Self::u_mem_along`] with the **equation** conditional as well: from
    /// `⊢ H → x ∈ a` and `⊢ H → a = b` infer `⊢ H → x ∈ b`.
    ///
    /// The type former's bridge is of that shape whenever `np > 0` — the beta
    /// chain holds under the parameters' own typings — so a recursive field's
    /// transport from the Lean spine to `ind(p⃗)` cannot use the unconditional
    /// form. At `np = 0` the two coincide.
    fn uu_mem_along(&mut self, xa: &Thm, ab: &Thm, h: Option<&Formula>) -> Option<Thm> {
        let (x, a) = u_concl(xa, h)?.as_mem()?;
        let (a2, b) = u_concl(ab, h)?.as_eq()?;
        if a != a2 {
            return None
        }
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(a, b, w, Formula::mem(x, Term::var(w)));
        u_mp(&u_syl(ab, &leib, h)?, xa, h)
    }

    /// **The `T`-policy** — which target the general W-recursor is instantiated
    /// at, `WIRING-DESIGN.md` §6.3, adopted unchanged from
    /// `RECURSOR-DESIGN.md` §5.2.
    ///
    /// The W-recursor needs a *set* `T` containing every value the elimination
    /// produces. Lean's motive is a function, so the checker has to pick one,
    /// and the choice is fixed at nest-build time because the nest's bottom
    /// mentions it.
    ///
    /// 1. Every constructor nullary → `T := fin(s⃗)`, the finite set of the
    ///    minor premises themselves. `HYP`-free, and what keeps a `Bool`-shaped
    ///    elimination at zero gaps.
    /// 2. Otherwise, if some constructor `i₀` is nullary → `T := D_{np+1+i₀}`,
    ///    the motive's value at that constructor, **as the nest walked it**.
    ///    Rebuilding the term instead would make the two sides of an ι equation
    ///    carry different assumptions — the twice-recorded `075` lesson.
    /// 3. Otherwise → decline the nest. No corpus witness needs a fallback.
    fn t_policy(&mut self, gi: &GenInd, doms: &[Term], minors: &[Term], np: usize) -> Option<Term> {
        let ctors = &gi.ind.spec.ctors;
        let nullary = |c: &CtorSpec| c.args.is_empty() && c.recs == 0;
        if ctors.iter().all(nullary) {
            let mach = self.machine()?;
            let s = mach.borrow().wt.sums.clone();
            // `fin(s⃗)` — the finite set *of* the minor premises, which are the
            // nest's own variables, not anything in `doms`.
            return Some(derived::finset::FinSet::of(&s, minors))
        }
        let i0 = ctors.iter().position(nullary)?;
        doms.get(np + 1 + i0).cloned()
    }

    /// Interpret a Lean expression as a kernel term.
    pub fn interp(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Term {
        if let Some(t) = self.exprs.get(&e) {
            return t.clone()
        }
        let t = match ctx.read_expr(e) {
            Expr::Sort { level, .. } => self.interp_sort(ctx, level),
            Expr::Var { dbj_idx, .. } => {
                let i = self.idx_term(dbj_idx as u64);
                self.mk(self.syms.bvar, vec![i])
            }
            Expr::Const { name, levels, .. } => {
                // Every constant this backend interprets is checked against the
                // schedule the pre-pass computed. See `inst_report`.
                self.audit_instantiation(ctx, name, levels);
                // A constant with a value becomes an **explicit definition**
                // `⟦c⟧ := ⟦value⟧`, monomorphised at these levels. That is
                // conservative for free (`∃!y. y = t` holds for any term), and
                // it is what makes delta reduction justifiable: without a
                // defining equation there is nothing relating the constant to
                // what it unfolds to.
                //
                // Constants without values — axioms, constructors, recursors —
                // stay opaque, which is correct: they do not delta-reduce.
                let decls = self.decls;
                let value = decls.get_declar_val(&name).and_then(|(uparams, val)| {
                    (ctx.read_levels(levels).len() == ctx.read_levels(uparams).len())
                        .then(|| ctx.subst_expr_levels(val, uparams, levels))
                });
                if let Some(val_subst) = value {
                    let body = self.interp(ctx, val_subst);
                    let key = self.const_key(ctx, name, levels);
                    // A definition body with free variables outside the parameter list
                    // cannot be introduced soundly; fall back to an opaque symbol.
                    let Some((t, axiom)) = self.const_abbrev(key, &body) else {
                        let s = self.env_mut().declare(0);
                        return Term::apply(s, vec![])
                    };
                    self.const_defs.insert(e, axiom.clone());
                    self.abbrev_defs.insert(t.clone(), axiom);
                    t
                } else if let Some(t) = self.ind_const(ctx, name, levels) {
                    // An inductive with nullary constructors, and its
                    // constructors: real sets, with real membership theorems.
                    // See [`Inductives`].
                    t
                } else if let Some(n) = self.rec_nest(ctx, name, levels) {
                    // A recursor this backend can compute: the curried nest of
                    // lambda graphs with `derived`'s W-recursor at the bottom.
                    // See [`RecNest`]. Still a `define_abbrev` symbol, so the
                    // interpretation stays injective on constants; what is new
                    // is that it has a *defining equation*, which is what makes
                    // iota reachable at all.
                    n.head.clone()
                } else {
                    let args = self.interp_levels(ctx, levels);
                    let arity = u32::try_from(args.len()).expect("universe parameter count overflow");
                    // Shared per thread when the name is the export file's, so
                    // that an opaque constant occurring in a stored typing is
                    // the same symbol wherever it is used. Per-backend
                    // otherwise, exactly as before.
                    let sym = match self.name_key(name) {
                        Some(nk) => {
                            let hit = self.shared.borrow().opaque_syms.get(&(nk, arity)).copied();
                            match hit {
                                Some(s) => s,
                                None => {
                                    let s = self.env_mut().declare(arity);
                                    self.shared.borrow_mut().opaque_syms.insert((nk, arity), s);
                                    s
                                }
                            }
                        }
                        None => match self.consts.get(&name) {
                            Some(s) if s.arity() == arity => *s,
                            _ => {
                                let s = self.env_mut().declare(arity);
                                self.consts.insert(name, s);
                                s
                            }
                        },
                    };
                    self.mk(sym, args)
                }
            }
            Expr::App { fun, arg, .. } => self.interp_app(ctx, e, fun, arg),
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                match self.interp_lambda(ctx, e, binder_name, binder_style, binder_type, body) {
                    Some(t) => t,
                    None => {
                        // Unreachable in principle; see `interp_lambda`. One
                        // opaque symbol per occurrence, which says nothing about
                        // the lambda but is cheap, closed, and makes beta over
                        // it report a gap instead of misbehaving.
                        let d = self.interp(ctx, binder_type);
                        let s = self.env_mut().declare(1);
                        self.mk(s, vec![d])
                    }
                }
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                // Every `Type`-clause `Π x:A. B` is the **dependent product**
                // `dprod_C(h⃗,A)` of [`dprod_symbol_n`], the arrow being the
                // constant-fibre case at the bare-hole skeleton — one symbol
                // corpus-wide, agreeing with `mini`'s clause by reflexivity.
                // `dprod_const_fibre_n` relates it to the library's `fs` where
                // a `derived` theorem is stated over the function space. See
                // [`Self::interp_pi`].
                match self.interp_pi(ctx, e, binder_name, binder_style, binder_type, body) {
                    Some(t) => t,
                    None => {
                        // Unreachable in principle; see `interp_pi`. The opaque
                        // symbol says nothing about the `Π` but is cheap and
                        // closed, and makes the bridge over it report a gap
                        // instead of misbehaving.
                        let (d, b) = (self.interp(ctx, binder_type), self.interp(ctx, body));
                        self.mk(self.syms.pi, vec![d, b])
                    }
                }
            }
            Expr::Let { val, body, .. } => {
                // A `let` denotes its expansion, so introduce it as an
                // **explicit definition** of that expansion — exactly as a
                // constant is introduced as a definition of its value. Zeta is
                // then the defining equation, a real theorem, rather than the
                // interpretation quietly doing the substitution itself (which
                // would leave the kernel certifying nothing about the step).
                //
                // The expansion may mention Lean locals, i.e. kernel free
                // variables, so those become parameters of the symbol; `define`
                // refuses a body with a free variable it does not abstract.
                let expanded = ctx.inst(body, &[val]);
                let t = self.interp(ctx, expanded);
                let mut fvs = Vec::new();
                t.free_vars(&mut fvs);
                let defined = derived::define_abbrev(&mut self.env_mut(), &fvs, &t);
                match defined {
                    Some((sym, axiom)) => {
                        let args: Vec<Term> = fvs.iter().map(|v| Term::var(*v)).collect();
                        // Specialise `⊢ ∀fvs. sym(fvs) = t` down to this instance.
                        if let Some(inst) = derived::inst_all(&axiom, &args) {
                            self.let_defs.insert(e, inst);
                        }
                        self.mk(sym, args)
                    }
                    None => {
                        let s = self.env_mut().declare(0);
                        self.mk(s, vec![])
                    }
                }
            }
            Expr::Local { id, binder_type, .. } => {
                // Lean locals become kernel *free* variables. This is what makes
                // the eventual certificate a closed statement: generalising over
                // them is `lam_cong`/`pi_cong`'s job, and free variables are
                // exactly what the kernel's `gen` rule can abstract.
                //
                // A de Bruijn-level local is keyed by its level **and its
                // interpreted declared type** — levels are reused across a
                // declaration's telescopes, and level + type is what identifies
                // the variable (see [`LocalKey`]). Interpreting the type here
                // terminates because it is a strict subterm, and it is the same
                // memoised `⟦A⟧` the typing hypothesis `v ∈ ⟦A⟧` is stated at,
                // so the key and the hypotheses about the variable can never
                // disagree. A unique-id local is keyed by its id alone.
                let key = match id {
                    crate::expr::FVarId::DbjLevel(n) => {
                        let ty = self.interp(ctx, binder_type);
                        LocalKey::Level(n, ty)
                    }
                    crate::expr::FVarId::Unique(n) => LocalKey::Unique(n),
                };
                let v = match self.locals.get(&key) {
                    Some(v) => *v,
                    None => {
                        let v = self.env_mut().fresh_var();
                        self.locals.insert(key, v);
                        v
                    }
                };
                Term::var(v)
            }
            Expr::Proj { idx, structure, .. } => {
                let i = self.idx_term(idx as u64);
                let s = self.interp(ctx, structure);
                self.mk(self.syms.proj, vec![i, s])
            }
            // Literals get one opaque nullary symbol each, **per thread and per
            // value** — see [`Shared::lit_syms`]. Milestone 4 replaces these
            // with the kernel's primitive `ℕ` and its native bignum rule
            // schemas.
            Expr::NatLit { .. } | Expr::StringLit { .. } => {
                let lit = match ctx.read_expr(e) {
                    Expr::NatLit { ptr, .. } => ctx.read_bignum(ptr).cloned().map(Lit::Nat),
                    Expr::StringLit { ptr, .. } => Some(Lit::Str(ctx.read_string(ptr).to_string())),
                    _ => None,
                };
                let sym = match lit {
                    Some(l) => {
                        let hit = self.shared.borrow().lit_syms.get(&l).copied();
                        match hit {
                            Some(s) => s,
                            // Not `entry`: the borrow above has to end before
                            // `declare` takes the same cell mutably.
                            None => {
                                let s = self.env_mut().declare(0);
                                self.shared.borrow_mut().lit_syms.insert(l, s);
                                s
                            }
                        }
                    }
                    // A literal whose value cannot be read is left per
                    // occurrence, exactly as before.
                    None => self.env_mut().declare(0),
                };
                self.mk(sym, vec![])
            }
        };
        self.exprs.insert(e, t.clone());
        self.exprs_rev.entry(t.clone()).or_insert(e);
        t
    }

    /// `⊢ ⟦a⟧ ∈ dom`, the typing premise `beta_conditional_n` is conditional on,
    /// or `None` when this interpretation does not know that membership.
    ///
    /// Three facts are available, all genuine theorems about the operators the
    /// interpretation is built from:
    ///
    /// * `⊢ ∀x. x ∈ U(x)` — a sort sits in the next universe up, since
    ///   `⟦Sort (u+1)⟧` *is* `U(⟦Sort u⟧)` for `u ≥ 1`;
    /// * `⊢ U₀ ∈ U₁` — the one level where that fails, because the tower is
    ///   seeded at `ω` rather than at `U₀`. See [`Self::interp_sort`];
    /// * `⊢ ∀a. fs(a,a) ∈ U(a)` — the function space `t → t` sits in the least
    ///   universe over `t`. A non-dependent `Pi` interprets as the
    ///   constant-fibre `dprod`, so the fact is carried across
    ///   [`Self::dprod_fs_eq`] to conclude `⟦t → t⟧ ∈ ⟦Sort (u+1)⟧` at the
    ///   term the interpretation builds.
    ///
    /// Whichever applies, the result is checked to be literally `⟦a⟧ ∈ dom`
    /// before it is returned, so a mistake here yields a gap and not a theorem
    /// about the wrong terms.
    fn domain_premise(&mut self, ta: &Term, dom: &Term) -> Option<Thm> {
        let want = Formula::mem(ta.clone(), dom.clone());
        let out = if *ta == self.pre.u0() && *dom == self.pre.u1() {
            // `⟦Prop⟧ ∈ ⟦Type 0⟧`, which is `U₀ ∈ U(ω)` and so *not* an instance
            // of `x ∈ U(x)`.
            self.pre.u0_in_u1.clone()
        } else if *dom == Term::apply(self.pre.u_sym, vec![ta.clone()]) {
            let mem_u = self.pre.mem_u.clone();
            derived::inst_all(&mem_u, std::slice::from_ref(ta))?
        } else {
            // `⟦a⟧` has to be a *diagonal* arrow `⟦t → t⟧`: the two-argument
            // form `(a ∪ b) ∈ U(c) → fs(a,b) ∈ U(c)` carries an antecedent
            // about binary unions that is not dischargeable here. The arrow
            // interprets as `dprod(t,t)` at the constant-fibre skeleton; the
            // library facts are stated over `fs`, so the membership is derived
            // there and carried across [`Self::dprod_fs_eq`] — one Leibniz
            // step, exactly the seam `mini`'s `dprod_is_fs` is.
            let (f, args) = self.parts.get(ta)?.clone();
            if args.len() != 2 || args[0] != args[1] {
                return None
            }
            let h = self.hole_var(0);
            let const_dprod =
                self.shared.borrow().pi_infos.get(&Term::var(h)).map(|i| i.dprod);
            if Some(f) != const_dprod {
                return None
            }
            let t = args[0].clone();
            // `⟦Prop → Prop⟧ ∈ ⟦Type 0⟧` is the one diagonal whose target is not
            // `U(t)`, since `⟦Type 0⟧` is `U(ω)` and not `U(U₀)`.
            let at_fs = if t == self.pre.u0() && *dom == self.pre.u1() {
                self.pre.fs_u0_in_u1.clone()
            } else {
                if *dom != Term::apply(self.pre.u_sym, vec![t.clone()]) {
                    return None
                }
                let fs_in_u = self.pre.fs_in_u.clone();
                derived::inst_all(&fs_in_u, std::slice::from_ref(&t))?
            };
            let fs_t = Term::apply(self.pre.fs_sym(), vec![t.clone(), t.clone()]);
            (*at_fs.concl() == Formula::mem(fs_t, dom.clone())).then_some(())?;
            let eq = self.dprod_fs_eq()?;
            let inst = derived::inst_all(&eq, &[t.clone(), t])?;
            let (dp, fs_at) = inst.concl().as_eq()?;
            (dp == *ta).then_some(())?;
            let back = derived::eq_symm(&mut self.env_mut(), &inst)?;
            let w = self.env_mut().fresh_var();
            let leib = Thm::eq_leibniz(fs_at, dp, w, Formula::mem(Term::var(w), dom.clone()));
            Thm::mp(&Thm::mp(&leib, &back)?, &at_fs)?
        };
        (*out.concl() == want).then_some(out)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The type-directed interpretation.
    //
    // `domain_premise` above knows two facts about the *operators* the
    // interpretation is built from, and nothing about Lean's typing judgement.
    // `has_type` is the judgement: `⊢ ⟦e⟧ ∈ ⟦A⟧` derived by recursion on the
    // structure of `e`, one clause per Lean typing rule. Every clause ends at
    // the same guard — the theorem handed back must literally conclude
    // `Formula::mem(⟦e⟧, ty)` — so a clause that builds the wrong thing yields
    // `None`, i.e. a carried assumption and a reported gap, never a claim.
    //
    // `None` means "not proved". It never means "assume it": the assumption
    // path is `beta_step`'s, and it is visible in the escape ledger.
    //
    // What each clause needs:
    //
    // * `Sort u` — `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧` *is* `x ∈ U(x)`, so it is already
    //   settled by `domain_premise`'s first branch, which is not restricted to
    //   sorts. There is no separate clause and nothing to add.
    // * `Const c` — `⟦c⟧` is introduced as a *definition* of `⟦value⟧`, so the
    //   membership transfers along the defining equation and the obligation
    //   becomes the value's own. Constants with no value (axioms, inductive
    //   types, constructors, recursors) are opaque symbols with no axioms
    //   whatever, so nothing about where they live is derivable — honestly
    //   `None`.
    // * `App f a` — the characteristic property of the interpretation of `f`'s
    //   type: the `∀x ∈ A. app(f,x) ∈ b(x)` conjunct of `dprod_def`, after
    //   which `b(h⃗,⟦a⟧)` is unfolded to the fibre skeleton — the same
    //   unfolding `beta_step` does, which is why the result lines up with
    //   `⟦B[a]⟧` syntactically. For a target a `derived` theorem states over
    //   `fs(A,B)` it is `Prelude::fs_app_mem` instead.
    // * `Local w` — the binder assumption in force, if there is one; failing
    //   that, [`TgBackend::has_type_local`] *acquires* the context's own typing
    //   `⟦w⟧ ∈ ⟦A⟧` of it as a new antecedent, which the caller then either
    //   discharges at the binder or carries into the certificate. It is `None`
    //   only when the obligation is stated at a type that is not `⟦A⟧` and does
    //   not unfold to it.
    // * `Lam` — [`lam_in_funspace_n`] when the target is a function space and
    //   [`lam_in_dprod_n`] when it is a dependent product. Both consume a
    //   *pointwise* premise `∀x. (x ∈ A → t(h⃗,x) ∈ …)`, which is itself a
    //   typing obligation under the binder; see below.
    // * `Pi` — needs `dprod_in_universe`, whose n-ary port does not exist.
    //   `None`, and counted, so the cost of its absence is a measured number
    //   rather than a guess (see [`ht_report`]).
    // * `Let`, `Proj`, literals — `None`.
    //
    // # Resting on a binder's assumption
    //
    // The lambda rule's premise is a typing judgement *under the binder*: to
    // show `⟦λx:A. b⟧ ∈ ⟦Π x:A. B⟧` one has to show `⟦b⟧ ∈ ⟦B⟧` for a variable
    // `x` known only to lie in `A`. So the recursion carries a list of
    // assumptions, all of the shape `w ∈ D`, and derives
    //
    //     ⊢ conj(assumptions) → ⟦e⟧ ∈ ty
    //
    // rather than the bare membership. This is the same discipline [`CondEq`]
    // uses for equations, run over memberships, with the same `u_*` family
    // threading it — so the conditional path cannot drift from the
    // unconditional one, and `assumptions = []` is literally the old code.
    //
    // **Nothing conditional escapes unaccounted for.** An assumption enters the
    // recursion in exactly two places. The lambda rule introduces its *own*
    // binder's guard and discharges it again by
    // [`TgBackend::guard_and_generalise_at`] — the same move the lambda
    // *congruence* rule uses — checking that what is left over is precisely what
    // it started from. [`TgBackend::has_type_local`] acquires the ambient typing
    // of a context local, and that one is *not* discharged here: it is appended
    // to the list every clause threads and handed back out through
    // [`TgBackend::has_type_a`], whose guard checks the returned list still
    // begins with the one it was asked for. `beta_step` puts whatever comes back
    // into the [`CondEq`]'s hypotheses, so it is counted by the escape ledger
    // and reported as a gap unless a binder discharges it later.
    //
    // [`TgBackend::has_type_h`] is the entry point for callers that cannot carry
    // a new antecedent: it declines rather than acquiring.
    // ─────────────────────────────────────────────────────────────────────────

    // ── Termination ──────────────────────────────────────────────────────────
    //
    // There used to be a constant here, `MAX_TYPE_DEPTH = 16`, and a depth
    // parameter tested against it on the way into `has_type_a`, in
    // `target_head_step` and in `typeable_shape`, with `unfolds_to` and
    // `expose_pi` using it as a loop count. It was a **termination** bound: the
    // recursion followed the delta graph, which the checker never verifies is
    // acyclic, and the cycle guard `Self::ht_active` could not substitute for it
    // because it keys on the exact triple `(e, ty, assms)` and a delta chain
    // runs through *distinct* constants — with `subst_expr_levels` minting a
    // fresh, unequal key at every step.
    //
    // A magic number is the wrong mechanism, and it is gone. What replaced it,
    // edge by edge:
    //
    // * **The delta edge** — [`Self::has_type_const`] stepping into a
    //   constant's value — is guarded by [`Self::const_active`], the
    //   instantiations currently being unfolded. A repeat of `(name, levels)` is
    //   exactly a cycle in the delta graph, so cutting it loses nothing that
    //   could have terminated, and the walk is bounded by the size of the
    //   declaration environment. That is what `ht_active` could not do: it keys
    //   on the whole triple, and every step of a delta chain is a fresh triple.
    //
    //   The store was *meant* to remove this edge outright, and it cannot. A
    //   stored typing is a single theorem, `⟦c⟧ ∈ ⟦T_c⟧` at the declared type
    //   and at the declaration's own universe parameters; an obligation about
    //   `c` arrives at whatever target the surrounding derivation produced, and
    //   at whatever levels the use site instantiates. Making the lookup the only
    //   clause cost `028_peano2` its last derivation — 25 uses of this rule
    //   became 5, all twenty losses being *the same constants at other universe
    //   instantiations* — and took the inductive-free fragment off 27/27. So the
    //   store is a shortcut in front of the derivation, not a replacement for
    //   it, and termination is the visited set's job.
    // * **`unfolds_to`** walks `Self::abbrev_defs`, a finite map, and stops on a
    //   term it has already visited. Every iteration consumes a distinct key, so
    //   the loop runs at most `abbrev_defs.len()` times. (It is in fact
    //   monotone: a defining equation's right-hand side is built out of symbols
    //   declared strictly before its left-hand side, so the chain descends the
    //   signature. The visited set does not rely on that.)
    // * **`expose_pi`** walks the *Lean* declaration environment and stops on a
    //   name it has already unfolded, so it runs at most once per declaration.
    // * **`typeable_shape`** likewise carries the names it has unfolded; its
    //   other edge descends into an application's function, which is structural.
    // * **`target_head_step`** recurses only into the *head* of an application
    //   whose shape [`Self::parts`] recorded, i.e. into a strict subterm, and
    //   otherwise unfolds one abbreviation without recursing. Structural.
    //
    // What is left in `has_type_a` itself: `App` into `fun`/`arg` and `Lambda`
    // into its body are structural descent on the Lean expression; the type
    // delta clause replaces the target by an `abbrev_defs` value, which as above
    // descends the signature; and the target-beta clause replaces the target by
    // a reduct.
    //
    // **The target-beta edge is the one with no syntactic descent to point at**,
    // and it is worth being explicit that its termination argument is weaker
    // than the others'. `Self::ht_active` cuts a chain that returns to a target
    // it is already working on, which rules out cycles; what it does not rule
    // out is an infinite chain of *distinct* targets. There is a measure that
    // works — each step either contracts a redex whose graph symbol was declared
    // after its body, or unfolds an abbreviation whose right-hand side is built
    // from earlier symbols, so the multiset of symbols descends — but it is not
    // airtight in the presence of duplication (a body may use its binder twice),
    // so it is offered as a reason to expect termination rather than a proof of
    // it. Measured: no divergence anywhere in `good/**`, and the deepest
    // recursion a derivation succeeds at is 9 without the declaration-typing
    // store and 17 with it, against the 16 the old bound allowed.
    //
    // `global_report` still prints that depth, because a recursion with nothing
    // testing against it is worth being able to watch; nothing tests against
    // it.

    /// `⊢ ⟦e⟧ ∈ ty`, unconditionally, or `None` when this interpretation cannot
    /// derive it.
    ///
    /// The entry point: no assumptions, so the result is a bare theorem about
    /// the membership claimed. Everything inside may rest on binder assumptions;
    /// nothing here does.
    /// `⊢ conj(assms) → (⟦e⟧ ∈ ty)` — the derivation, *provided* it needed no
    /// assumption beyond the ones it was handed.
    ///
    /// Every caller that cannot itself carry a new antecedent goes through here.
    fn has_type_h(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<Thm> {
        let (thm, used) = self.has_type_a(ctx, e, ty, assms, depth)?;
        (used == assms).then_some(thm)
    }

    /// `⊢ conj(assms') → (⟦e⟧ ∈ ty)`, together with `assms'`.
    ///
    /// `assms'` is `assms` followed by whatever the derivation had to **acquire**
    /// — and the only thing it may acquire is the ambient typing `⟦w⟧ ∈ ⟦A⟧` of a
    /// context local `w : A` (see [`Self::has_type_local`]). The invariant
    /// `assms'.starts_with(assms)` is checked in the guard below, so a clause
    /// cannot quietly weaken what it was asked for into something else.
    ///
    /// Memoised on `(e, ty, assms)`. The memo caches negative results too,
    /// including ones the depth bound or the cycle guard caused; that can only
    /// lose completeness — a `Some` is checked against its claim on every path
    /// out, so nothing false can be cached.
    fn has_type_a(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, Vec<Formula>)> {
        let key = (e, ty.clone(), assms.to_vec());
        let out = match self.has_types.get(&key) {
            Some(r) => r.clone(),
            None => {
                if self.ht_active.contains(&key) {
                    return None
                }
                self.ht_active.push(key.clone());
                let out = self.has_type_uncached(ctx, e, ty, assms, depth);
                self.ht_active.pop();

                // The guard. A theorem that does not literally conclude the
                // membership being claimed — under literally the assumptions
                // being advertised — is not a proof of it, whatever it proves.
                // Every clause passes through here, once.
                let want = Formula::mem(self.interp(ctx, e), ty.clone());
                let out = out.filter(|(t, _, used)| {
                    if !used.starts_with(assms) {
                        return false
                    }
                    let full = match conj_of(used) {
                        None => want.clone(),
                        Some(h) => Formula::imp(h, want.clone()),
                    };
                    // `establishes`, i.e. `hyps().is_empty()` as well as the
                    // conclusion. The assumptions this clause advertises are
                    // *antecedents of the formula*; a kernel `Γ` would be an
                    // extra, unadvertised one, and `self.has_types` is keyed on
                    // `(expr, type, assumptions)` and would replay it silently.
                    derived::establishes(t, &full)
                });
                // How deep the recursion actually goes when it works. Nothing
                // is tested against this; it is reported because a recursion
                // with no bound on it is worth being able to look at.
                if out.is_some() {
                    note_type_depth(depth);
                }
                self.has_types.insert(key, out.clone());
                out
            }
        };
        // Counted per *use*, memo replays included, so the split says which
        // typing rule is carrying the work rather than which was derived first.
        let (thm, clause, used) = out?;
        note_ht(clause);
        Some((thm, used))
    }

    /// [`Self::has_type_a`] without the memo, the guard or the cycle check;
    /// reports which clause answered, and the assumption list the answer is
    /// stated under.
    fn has_type_uncached(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        let te = self.interp(ctx, e);
        let hyp = conj_of(assms);

        // An assumption in force *is* a derivation of what it says. This is the
        // clause a `Local` takes under its own binder — and the only reason the
        // lambda rule below can ever discharge its pointwise premise.
        if let Some(t) = self.assumed(&te, ty, assms) {
            return Some((t, HtClause::Assumed, assms.to_vec()))
        }

        // The two facts about the operators themselves — `x ∈ U(x)`, which is
        // what makes `Sort` work, and `fs(a,a) ∈ U(a)`. Both are term-level and
        // cheap, so they are tried before anything is taken apart.
        if let Some(t) = self.domain_premise(&te, ty) {
            let by = if te == self.pre.u0() && *ty == self.pre.u1() {
                HtClause::U0MemU1
            } else if *ty == Term::apply(self.pre.u_sym, vec![te.clone()]) {
                HtClause::MemU
            } else {
                HtClause::FsDiag
            };
            return Some((u_a1i(&t, hyp.as_ref()), by, assms.to_vec()))
        }
        // A constructor of an interpreted inductive. The whole content is that
        // `⟦Bool.true⟧` really is an element of the set `⟦Bool⟧` — one theorem,
        // derived once in [`derived::enums`], with no reduction and no `Π`
        // anywhere. This is the clause that pays for interpreting the inductive
        // at all, since a constructor is the commonest argument there is.
        if let Some(t) = self.ind_mems.get(&(te.clone(), ty.clone())).cloned() {
            return Some((u_a1i(&t, hyp.as_ref()), HtClause::Ctor, assms.to_vec()))
        }
        // The same, one level up: the inductive *type* in the sort it lives in.
        // `⟦T⟧ ∈ ⟦Sort u⟧` is what the lambda and `Π` rules keep wanting, and
        // until `derived::cumul` there was no inductive for which it was
        // provable at all — `W(A,B,U(A)) ∈ U(A)` is refutable, so the
        // membership has to be in a universe containing `ω`.
        if let Some(t) = self.ind_ty_mem(&te, ty) {
            return Some((u_a1i(&t, hyp.as_ref()), HtClause::IndTy, assms.to_vec()))
        }
        // The same, for a constructor that has to be *applied* before it is an
        // element of anything — `List.nil α`, `List.cons α h t`. Tried before
        // the structural clauses because it is cheaper and more specific than
        // the general application rule, which would need `⟦List.cons⟧`'s
        // dependent product and hence `⟦List α⟧ ∈ ⟦Sort u⟧`.
        if let Some(r) = self.has_type_ctor_app(ctx, e, assms, depth) {
            return Some(r)
        }

        let structural = match ctx.read_expr(e) {
            Expr::Const { .. } => self.has_type_const(ctx, e, ty, assms, depth),
            Expr::App { fun, arg, .. } => self.has_type_app(ctx, fun, arg, assms, depth),
            Expr::Lambda { .. } => self.has_type_lam(ctx, e, ty, assms, depth),
            Expr::Local { binder_type, .. } => self.has_type_local(ctx, &te, binder_type, ty, assms),
            Expr::Proj { .. } => self.has_type_proj(ctx, e, &te, ty, assms),
            _ => None,
        };
        if structural.is_some() {
            return structural
        }

        // Last: the *target* may be a defined constant standing for the `Π` (or
        // the arrow) the rules above match on — `PN`, `Nat`, and most Lean types
        // are. Unfold it along its defining equation and try again there; the
        // membership is carried back by Leibniz, so what comes out is still
        // about `ty`.
        if let Some(def) = self.abbrev_defs.get(ty).cloned() {
            if let Some(r) = (|| {
                let (_, ty2) = def.concl().as_eq()?;
                let (inner, used) = self.has_type_a(ctx, e, &ty2, assms, depth + 1)?;
                let hyp = conj_of(&used);
                let back = derived::eq_symm(&mut self.env_mut(), &def)?;
                let w = self.env_mut().fresh_var();
                let leib = Thm::eq_leibniz(ty2, ty.clone(), w, Formula::mem(te.clone(), Term::var(w)));
                let step = Thm::mp(&leib, &back)?;
                let out = u_mp(&u_a1i(&step, hyp.as_ref()), &inner, hyp.as_ref())?;
                Some((out, HtClause::TypeDelta, used))
            })() {
                return Some(r)
            }
        }
        // And last of all: the target may *beta-reduce*. The type-level analogue
        // of the clause above — see [`Self::has_type_target_beta`].
        self.has_type_target_beta(ctx, e, ty, assms, depth)
    }

    /// `⟦e⟧ ∈ ty` where the target `ty` **beta-reduces**: the type-level
    /// analogue of [`HtClause::TypeDelta`].
    ///
    /// A Lean type like a motive `C xs` interprets to a set-*application*
    /// `app(⟦C⟧, ⟦xs⟧)`, and when `⟦C⟧` is a lambda graph that application has a
    /// value the rest of `has_type` can match on — but only after it is
    /// contracted. So: reduce the target one head step, settle the obligation
    /// against the reduct, and carry the membership back along the equation by
    /// Leibniz, exactly as the delta clause does.
    ///
    /// # Beta's own premise is not assumed
    ///
    /// `app(lam(A), x) = t(x)` holds only for `x ∈ A` — see
    /// [`derived::funcs::beta_conditional`]. That premise is settled by
    /// [`Self::target_mem`], which either derives it or *acquires* it as an
    /// antecedent in the same way [`Self::has_type_local`] does; either way it
    /// comes back in the returned assumption list, where the caller discharges
    /// it at a binder or the escape ledger counts it. There is no path here that
    /// takes it on trust.
    fn has_type_target_beta(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        let (eq0, ty2, used0) = self.target_head_step(ctx, ty, assms, depth)?;
        let Some((inner, used)) = self.has_type_a(ctx, e, &ty2, &used0, depth + 1) else {
            note_tb(TbMiss::Reduct);
            return None
        };
        let hyp = conj_of(&used);
        // `⊢ H → ty = ty2`, restated under whatever the recursion acquired.
        let eq = reassume(&eq0, &used0, &used)?;
        let back = u_eq_symm(&mut self.env_mut(), &eq, hyp.as_ref())?;
        let te = self.interp(ctx, e);
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(ty2, ty.clone(), w, Formula::mem(te, Term::var(w)));
        let step = u_mp(&u_a1i(&leib, hyp.as_ref()), &back, hyp.as_ref())?;
        let out = u_mp(&step, &inner, hyp.as_ref())?;
        Some((out, HtClause::TargetBeta, used))
    }

    /// One head reduction of a *type*: `⊢ conj(used) → ty = ty'`, with `ty'`.
    ///
    /// Three cases, in the order a weak-head normalisation would take them:
    ///
    /// * `app(lam_C(h⃗,A), x)` contracts to the body skeleton at `x`, on the
    ///   premise `x ∈ A`;
    /// * `app(f, x)` where `f` is itself an application reduces its *head*
    ///   first — this is the curried case, `⟦C α xs⟧`, and it is the common one;
    /// * `app(c, x)` for a defined constant `c` unfolds `c`.
    ///
    /// The congruence in the last two is [`u_congr_arg`] at the function slot,
    /// so the equation stays about the term it started from.
    fn target_head_step(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, Term, Vec<Formula>)> {
        let app = self.pre.ap.app;
        let (f, args) = self.parts.get(ty).cloned()?;
        if f != app || args.len() != 2 {
            return None
        }
        let (head, x) = (args[0].clone(), args[1].clone());
        let (hsym, hargs) = self.parts.get(&head).cloned()?;

        // ── The head is a lambda graph: beta ─────────────────────────────────
        let lam = self.shared.borrow().lam_by_lam.get(&hsym).cloned();
        if let Some((key, info)) = lam {
            let (holes, dom) = hargs.split_last().map(|(d, h)| (h.to_vec(), d.clone()))?;
            let t_def = info.graph.as_ref()?.t_def.clone();
            note_tb(TbMiss::Reached);
            // Beta's domain premise, derived or acquired — never assumed.
            let Some((mem, used)) = self.target_mem(ctx, &x, &dom, assms, depth) else {
                note_tb(TbMiss::Domain);
                return None
            };
            let beta = self.beta_thm(&key)?;
            let mut inst = holes.clone();
            inst.push(dom);
            inst.push(x.clone());
            let cond = derived::inst_all(&beta, &inst)?;
            let hyp = conj_of(&used);
            let eq0 = u_mp(&u_a1i(&cond, hyp.as_ref()), &mem, hyp.as_ref())?;
            // `t(h⃗,x)` unfolded to the body skeleton with `x` plugged in.
            let mut tinst = holes;
            tinst.push(x);
            let unfold = derived::inst_all(&t_def, &tinst)?;
            let eq = u_eq_trans(&mut self.env_mut(), &eq0, &u_a1i(&unfold, hyp.as_ref()), hyp.as_ref())?;
            // The equation has to be about `ty` itself, not about whatever the
            // instantiation happened to produce.
            let (l, r) = u_as_eq(&eq, hyp.as_ref())?;
            if l != *ty {
                return None
            }
            return Some((eq, r, used))
        }

        // ── The head reduces first: a curried application, or a definition ───
        let (heq, head2, used) = if hsym == app && hargs.len() == 2 {
            self.target_head_step(ctx, &head, assms, depth + 1)?
        } else {
            let def = self.abbrev_defs.get(&head).cloned()?;
            let (_, v) = def.concl().as_eq()?;
            (u_a1i(&def, conj_of(assms).as_ref()), v, assms.to_vec())
        };
        let hyp = conj_of(&used);
        let eq = u_congr_arg(&mut self.env_mut(), app, &[head, x.clone()], 0, &heq, hyp.as_ref())?;
        // Register the reduct's shape so that the next step can take it apart.
        let ty2 = self.mk(app, vec![head2, x]);
        let (l, r) = u_as_eq(&eq, hyp.as_ref())?;
        if l != *ty || r != ty2 {
            return None
        }
        Some((eq, ty2, used))
    }

    /// `⊢ conj(used) → x ∈ dom` for a term `x` that arrived without a Lean node
    /// — beta's own domain premise, at a *target*.
    ///
    /// The three term-level facts first, since they are cheap and closed; then
    /// the Lean node `x` was interpreted from, if this backend interpreted one,
    /// at which point the obligation is an ordinary one and the whole `has_type`
    /// recursion applies to it — including [`Self::has_type_local`], which is
    /// what settles the common case of a motive applied to a context local.
    ///
    /// The node is only a *hint*: it is checked to interpret to `x` before it is
    /// used, and [`Self::has_type_a`]'s guard checks the resulting theorem
    /// against the claim regardless.
    fn target_mem(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        x: &Term,
        dom: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, Vec<Formula>)> {
        let hyp = conj_of(assms);
        if let Some(t) = self.assumed(x, dom, assms) {
            return Some((t, assms.to_vec()))
        }
        if let Some(t) = self.domain_premise(x, dom) {
            return Some((u_a1i(&t, hyp.as_ref()), assms.to_vec()))
        }
        if let Some(t) = self.ind_mems.get(&(x.clone(), dom.clone())).cloned() {
            return Some((u_a1i(&t, hyp.as_ref()), assms.to_vec()))
        }
        if let Some(t) = self.ind_ty_mem(x, dom) {
            return Some((u_a1i(&t, hyp.as_ref()), assms.to_vec()))
        }
        let e = *self.exprs_rev.get(x)?;
        if self.interp(ctx, e) != *x {
            return None
        }
        self.has_type_a(ctx, e, dom, assms, depth + 1)
    }

    /// `⊢ conj(assms) → (te ∈ ty)` when one of the assumptions says so.
    ///
    /// The assumption's target and `ty` need not be the same *term*: a binder's
    /// domain is `⟦A⟧` for whatever `A` Lean wrote, and the obligation that
    /// arrives later may be stated at the `Π` that `A` is a defined name for.
    /// The two are bridged by the defining equations themselves — a chain of
    /// real theorems — so the result still concludes `te ∈ ty`.
    fn assumed(&mut self, te: &Term, ty: &Term, assms: &[Formula]) -> Option<Thm> {
        for (i, f) in assms.iter().enumerate() {
            let Some((s, d)) = f.as_mem() else { continue };
            if s != *te {
                continue
            }
            let p = conj_proj(assms, i)?;
            if d == *ty {
                return Some(p)
            }
            let Some(eq) = self.unfolds_to(&d, ty) else { continue };
            let w = self.env_mut().fresh_var();
            let leib = Thm::eq_leibniz(d, ty.clone(), w, Formula::mem(te.clone(), Term::var(w)));
            let step = Thm::mp(&leib, &eq)?;
            let h = conj_of(assms);
            return u_mp(&u_a1i(&step, h.as_ref()), &p, h.as_ref())
        }
        None
    }

    /// A **context local**, by acquiring its own declared typing as a new
    /// antecedent: `⊢ (conj(assms) ∧ ⟦w⟧ ∈ ⟦A⟧) → ⟦w⟧ ∈ ty` for `w : A`.
    ///
    /// # Why this is a derivation and not an admission
    ///
    /// Carneiro reads `Γ ⊢ e : B` as *for every `γ ∈ ⟦Γ⟧`, `⟦e⟧γ ∈ ⟦B⟧γ`*, so
    /// for a local `w : A` in `Γ` the fact `⟦w⟧ ∈ ⟦A⟧` is part of the ambient
    /// assumption rather than something to be proved. This module carries that
    /// assumption as an *antecedent inside the formula*, discharged when the
    /// binder that introduced the local closes, by `gen` + `ax_dist`.
    ///
    /// It is **not** that the kernel has no context — this comment used to say
    /// so, and `kernel/src/thm.rs` says the opposite in bold: a `Thm` is a
    /// sequent `Γ ⊢ φ` with a real `hyps()`. The antecedent form is a *choice*
    /// this module makes, because a formula-level antecedent travels with the
    /// formula and so survives the `ExprPtr`-keyed caches, while a sequent
    /// hypothesis does not. See `THREADING-CENSUS.md` §2, stage 1, where that
    /// trade is the open design decision. That is precisely what
    /// [`Self::guard_and_generalise_at`] does for the pointwise premise of the
    /// lambda rules, and it is the same discipline
    /// [`Self::local_premises`] applies at a beta redex — the difference is only
    /// that here the recursion asks for the assumption at the point where it is
    /// needed, instead of the caller guessing the whole set in advance.
    ///
    /// Three things keep it honest. The antecedent is `⟦w⟧ ∈ ⟦A⟧` for the
    /// local's *own declared type*, read off the `Expr::Local` the checker
    /// introduced — never the type the obligation happens to be stated at. The
    /// bridge from `⟦A⟧` to `ty` is [`Self::assumed`]'s, i.e. a chain of real
    /// defining equations, so a `ty` merely *definitionally* equal to `⟦A⟧`
    /// yields `None` and a counted gap. And the acquired assumption is returned
    /// to the caller, which either discharges it or carries it into the
    /// certificate, where the escape ledger counts it.
    fn has_type_local(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        te: &Term,
        binder_type: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        let a = self.interp(ctx, binder_type);
        let f = Formula::mem(te.clone(), a);
        // `assumed` has already been tried at `assms`, so if the typing is
        // already in force this clause has nothing to add — and must not add a
        // duplicate conjunct, which would break the discharge at the binder.
        if assms.contains(&f) {
            return None
        }
        let mut used = assms.to_vec();
        used.push(f);
        let t = self.assumed(te, ty, &used)?;
        Some((t, HtClause::Local, used))
    }

    /// A **structure projection**, by acquiring its own field typing as a new
    /// antecedent: `⊢ (conj(assms) ∧ ⟦s.i⟧ ∈ ⟦F⟧) → ⟦s.i⟧ ∈ ty`, where `F` is
    /// the `i`-th field type of the structure's constructor telescope.
    ///
    /// # Why this is carried and not derived
    ///
    /// `⟦s.i⟧` is `proj(i, ⟦s⟧)`, and `proj` is one of the [`Syms`] — an
    /// **axiom-free** symbol introduced by signature extension. Nothing at all
    /// is provable about it, so `proj(i, ⟦s⟧) ∈ ⟦F⟧` is not a theorem this
    /// interpretation has and no rule can make it one: the missing content is
    /// the interpretation of the *structure*, which would have to make `⟦S⟧` a
    /// set of tuples and `proj` its component map. That is the same obstruction
    /// [`HtMiss::ConstOpaque`] measures for uninterpreted inductives, one level
    /// down.
    ///
    /// So the module's standing discipline applies — "where the obligation is
    /// not discharged outright it is reduced, and only failing that **carried**"
    /// — and this is the carrying clause. What comes back is a complete
    /// derivation of a weaker statement, not an assertion: the membership is an
    /// antecedent, it travels out in the returned assumption list, and the
    /// escape ledger reports it if no binder discharges it. Nothing here is
    /// admitted and nothing is assumed silently.
    ///
    /// Two things keep it honest, both copied from [`Self::has_type_local`].
    /// The antecedent is stated at the projection's **own field type**, read off
    /// the constructor telescope by [`Self::syn_type_proj`] — never at the
    /// target the obligation happens to be stated at, so a target that is only
    /// *definitionally* the field type yields `None` and a counted gap rather
    /// than a stronger assumption than Lean's own judgement. And where
    /// `syn_type_proj` cannot reach the telescope (it is delta-only) this
    /// declines outright, so nothing is assumed about a projection whose field
    /// type this module cannot see.
    fn has_type_proj(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        te: &Term,
        ty: &Term,
        assms: &[Formula],
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        let Expr::Proj { idx, structure, .. } = ctx.read_expr(e) else { return None };
        let field = self.syn_type_proj(ctx, idx, structure)?;
        let a = self.interp(ctx, field);
        let f = Formula::mem(te.clone(), a);
        // Already in force: `assumed` has had its chance at `assms`, and a
        // duplicate conjunct would break the discharge at the binder.
        if assms.contains(&f) {
            return None
        }
        let mut used = assms.to_vec();
        used.push(f);
        let t = self.assumed(te, ty, &used)?;
        Some((t, HtClause::Proj, used))
    }

    /// `⊢ a = b`, when `a` unfolds to `b` along the abbreviation equations
    /// [`Self::interp`] introduced for defined constants. `None` if it does not.
    ///
    /// Terminates because every iteration consumes a distinct key of
    /// [`Self::abbrev_defs`], a finite map: the chain is followed only while the
    /// current term *is* such a key, and a term already visited stops it. (It
    /// cannot in fact revisit one — a defining equation's right-hand side is
    /// built from symbols declared before its left-hand side — but the visited
    /// set is what the argument rests on, not that.)
    fn unfolds_to(&mut self, a: &Term, b: &Term) -> Option<Thm> {
        let mut acc = Thm::eq_refl(a.clone());
        let mut cur = a.clone();
        let mut seen: std::collections::HashSet<Term> = std::collections::HashSet::new();
        loop {
            if cur == *b {
                return Some(acc)
            }
            if !seen.insert(cur.clone()) {
                return None
            }
            let step = self.abbrev_defs.get(&cur).cloned()?;
            let (_, next) = step.concl().as_eq()?;
            acc = derived::eq_trans(&mut self.env_mut(), &acc, &step)?;
            cur = next;
        }
    }

    /// The declaration `c.{us} : ty := val` has just been checked. Form
    /// `⊢ ⟦c.{us}⟧ ∈ ⟦ty⟧` and store it, so that a later use of `c` is a lookup
    /// rather than a walk down the delta graph.
    ///
    /// A constant's typing **has** to be stored: it is the only way to use the
    /// fact that `f : T` when `f` is later applied. It is not optional and there
    /// is no switch for it — there was one briefly, and turning it off looked
    /// like a 36% saving on `init-prelude` (11.79 s against 16.03 s) at no cost
    /// in gaps or escapes. That reading was wrong. The 36% was never the cost of
    /// *storing*; it was the cost of searching for a typing from scratch, at
    /// 1645 declarations, 1633 of which failed — a search that existed only
    /// because `infer` returned a type without the derivation justifying it.
    ///
    /// Two halves, both available here and nowhere else:
    ///
    /// * `⊢ ⟦val⟧ ∈ ⟦ty⟧` — the typing, now *handed in* by `check_declar` as
    ///   the composition of inference's own derivation with the conversion
    ///   along `⟦T'⟧ = ⟦T⟧`, rather than searched for;
    /// * `⊢ ⟦c⟧ = ⟦val⟧` — the defining equation, which is what
    ///   [`derived::define_abbrev`] hands back when the constant is introduced
    ///   as an explicit definition of its value.
    ///
    /// The second is *not* obtained by interpreting a `Const` node for `c`: the
    /// environment under which a declaration is checked stops at that
    /// declaration (`EnvLimit::ByName`), so `c` has no value as far as this
    /// backend can see, and `interp` would give it an opaque symbol. It is
    /// obtained by asking for the abbreviation of `⟦val⟧` directly — which is
    /// the same symbol a later backend gets, because
    /// [`Self::abbrev_of`] memoises the definitional extension on its body.
    ///
    /// **Nothing conditional is stored** ([`Dt::Conditional`]), and the reason
    /// is *not* the one a reader of [`crate::sealed`] would guess. Two different
    /// things are spelled `hyps` here: `TgTyping::Derived { hyps }` is a list of
    /// **formula-level antecedents** on a theorem `⊢ conj(hyps) → ⟦val⟧ ∈ ⟦ty⟧`,
    /// while [`Sealed`] tests `Thm::hyps()`, the **kernel sequent**. Measured on
    /// `init-prelude`: all 198 conditional declaration typings have an *empty*
    /// kernel sequent, so `Sealed::new` would accept every one of them. The
    /// persistence discipline is not what forbids this.
    ///
    /// What forbids it is what the antecedents *are*. Measured over the same
    /// 198: every one is a **hoisted guarded family**, `∀x. (x ∈ ⟦A⟧ → …)`, and
    /// 196 of them carry exactly one (the other two carry two). They are already
    /// generalised past the binder that produced them, so no binder is left to
    /// discharge them, and none is closed — the `discharge_families` ledger
    /// reads 1186 offered and **0 discharged**, corpus-wide. Storing such an
    /// entry would not close a gap; it would move 1161 `ty_const` store misses
    /// into the escape ledger, one undischargeable family per use, and both rows
    /// count as gaps. The lever that would make it pay is discharging the
    /// family, not widening the store.
    ///
    /// # And discharging the family is out of reach here, which was measured
    ///
    /// Two pieces of plumbing are visibly absent, and both are worth nothing.
    /// [`Self::discharge_families`] takes a [`CondEq`] and guards on `as_eq`, so
    /// a *typing* certificate is never offered to it at all; and
    /// [`Self::peel_family`] declines a family whose body is itself a family.
    /// Building either would be a small change. Neither closes anything:
    ///
    /// * The 198 carry **200 antecedents**, and the ledger beneath
    ///   [`Dt::Conditional`] counts them — **170** are families of families
    ///   ([`Dt::CondNest`]) and **30** are plain memberships ([`Dt::CondMem`]).
    /// * All 30 memberships are about a **structure projection** `⟦s.i⟧`, whose
    ///   typing [`Self::has_type_proj`] can only ever *acquire* as a new
    ///   antecedent, never derive — the interpretation of the structure is what
    ///   is missing, which is the same obstruction `INDUCTIVES.md` records.
    /// * Unwrapping the 170 nestings to their innermost membership and asking
    ///   `has_type` under **every** guard collected on the way — and under the
    ///   subject's own local-premise closure on top of that — derives **0 of
    ///   170**, at every depth from 2 to 7. They too are all projections.
    ///
    /// So the antecedents of the 198 are entirely inside interpretation scope.
    /// No amount of threading reaches them, and neither [`Dt::Conditional`],
    /// [`Dt::MissCond`] nor [`Dt::Stored`] can move until `⟦s.i⟧` has a typing.
    ///
    /// This is still threading debt and is counted as such: 198 certificates
    /// were computed and thrown away. [`Dt::MissCond`] is how many uses would
    /// benefit if that changed.
    /// The parameter variable of a **level hypothesis** `u ∈ ω`, when `f` is
    /// exactly that: a membership whose subject is one of the ω-vocabulary's
    /// parameter variables and whose set is the apparatus's own `ω`. Anything
    /// else — a hoisted family, a membership at another set, a variable this
    /// backend never handed out — is `None`, and the caller treats the
    /// hypothesis as the binder-owed obligation it then is.
    fn omega_hyp_var(&self, f: &Formula) -> Option<FreeVar> {
        let lp = self.lp()?;
        let (t, om) = f.as_mem()?;
        if om != lp.omega() {
            return None
        }
        let mut fvs = Vec::new();
        t.free_vars(&mut fvs);
        let [v] = fvs[..] else { return None };
        if t != Term::var(v) {
            return None
        }
        self.is_param_omega_var(v).then_some(v)
    }

    /// **The declaration-boundary quantifier** — `LEVELPOLY.md` §5.3 step 5.
    ///
    /// Takes a value typing `⊢ ⋀(uᵢ∈ω) → ⟦val⟧ ∈ ⟦T⟧` whose every antecedent
    /// is a level hypothesis ([`Self::omega_hyp_var`]), transports it across
    /// the defining equation `⟦c⟧ = ⟦val⟧` **under the same antecedent**, and
    /// closes the level hypotheses by `Thm::gen` — they are hypotheses about
    /// the declaration's own parameters, and the declaration boundary is the
    /// binder that owns them:
    ///
    /// ```text
    /// ⊢ ∀u⃗. ⋀(uᵢ∈ω) → ⟦c⟧(u⃗) ∈ ⟦T⟧(u⃗)
    /// ```
    ///
    /// Stored with the variables (outermost first) and the antecedents at the
    /// generic point, so [`Self::has_type_const`] can re-open the implication
    /// and hand the `uᵢ ∈ ω` assumptions to its caller's antecedent channel.
    /// `false` on any other hypothesis shape or any refused step, and the
    /// caller's discard-and-count path runs unchanged.
    fn store_poly_typing(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        key: &(u32, Vec<Term>),
        tyt: &Term,
        val: ExprPtr<'t>,
        thm: &Thm,
        hyps: &[Formula],
    ) -> bool {
        if hyps.is_empty() || !thm.hyps().is_empty() {
            return false
        }
        let mut vars: Vec<FreeVar> = Vec::with_capacity(hyps.len());
        for f in hyps {
            match self.omega_hyp_var(f) {
                Some(v) if !vars.contains(&v) => vars.push(v),
                _ => return false,
            }
        }
        let Some(h) = conj_of(hyps) else { return false };
        // The theorem must be about this declaration's value and declared
        // type — the same refusal the unconditional path makes, one
        // antecedent deeper.
        let vt = self.interp(ctx, val);
        if u_concl(thm, Some(&h)) != Some(Formula::mem(vt.clone(), tyt.clone())) {
            return false
        }
        let Some((ct, def)) = self.const_abbrev(Some(key.clone()), &vt) else { return false };
        let Some(back) = derived::eq_symm(&mut self.env_mut(), &def) else { return false };
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(vt.clone(), ct.clone(), w, Formula::mem(Term::var(w), tyt.clone()));
        let Some(step) = Thm::mp(&leib, &back) else { return false };
        let Some(out) = derived::syl(thm, &step) else { return false };
        if !derived::establishes(&out, &Formula::imp(h, Formula::mem(ct, tyt.clone()))) {
            return false
        }
        let mut all = out;
        for v in vars.iter().rev() {
            all = match Thm::gen_checked(*v, &all) {
                Some(t) => t,
                None => return false,
            };
        }
        let Ok(sealed) = Sealed::new(all) else { return false };
        self.shared
            .borrow_mut()
            .declar_typings_poly
            .entry(key.clone())
            .or_insert((vars, hyps.to_vec(), sealed));
        true
    }

    fn store_declar_typing(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: NamePtr<'t>,
        uparams: LevelsPtr<'t>,
        ty: ExprPtr<'t>,
        val: ExprPtr<'t>,
        typing: TgTyping,
    ) {
        note_dt(Dt::Seen);
        // The store is per (name, levels) and the name has to outlive this
        // declaration's arena; nothing else can be stored, so nothing else is
        // attempted.
        let Some(key) = self.const_key(ctx, name, uparams) else { return note_dt(Dt::NoKey) };
        let tyt = self.interp(ctx, ty);

        // What inference established, if it established anything. This is the
        // whole point of threading a certificate through `infer`: the fact was
        // computed on the way down and is simply read off here.
        let thm = match &typing {
            TgTyping::Derived { thm, hyps } if hyps.is_empty() => {
                note_dt(Dt::FromInfer);
                Some(thm.clone())
            }
            TgTyping::Derived { thm, hyps } => {
                // §5.3 step 5, the declaration boundary. A derivation whose
                // every antecedent is `uᵢ ∈ ω` over a parameter variable is
                // not owed to any binder — those are the declaration's *level
                // hypotheses*, and the boundary is exactly where they close:
                // `gen` over the variables turns the implication into the
                // quantified typing `⊢ ∀u⃗. ⋀(uᵢ∈ω) → ⟦c⟧ ∈ ⟦T⟧`.
                if self.store_poly_typing(ctx, &key, &tyt, val, thm, hyps) {
                    note_dt(Dt::Conditional);
                    note_dt(Dt::PolyStored);
                    return
                }
                // A conditional typing is not stored, for the reason above —
                // and the key is remembered, so that a use that then misses can
                // be told apart from a use whose declaration was never proved.
                note_dt(Dt::Conditional);
                // The census of what is being thrown away. Structural only: it
                // reads `Self::hoisted` and the formula's own shape, derives
                // nothing and asks `has_type` nothing, so the ledger cannot
                // perturb the run it is measuring.
                for f in hyps {
                    note_dt(Dt::CondHyp);
                    if self.omega_hyp_var(f).is_some() {
                        note_dt(Dt::CondOmega);
                        continue
                    }
                    match self.hoisted.get(f).map(|(_, _, phi)| phi.as_mem().is_some()) {
                        Some(true) => note_dt(Dt::CondMem),
                        Some(false) => note_dt(Dt::CondNest),
                        None => {}
                    }
                }
                self.shared.borrow_mut().declined_cond.insert(key.clone());
                None
            }
            TgTyping::Gap(_) => {
                note_dt(Dt::Gap);
                None
            }
        };
        let Some(thm) = thm else { return };
        // The handed-in theorem must be about this declaration's value and
        // declared type; a certificate is never taken on its label.
        let vt = self.interp(ctx, val);
        if *thm.concl() != Formula::mem(vt, tyt.clone()) {
            return note_dt(Dt::Refused)
        }
        note_dt(Dt::Derived);

        // `⊢ ⟦c⟧ = ⟦val⟧`, the defining equation, at this declaration's own
        // parameters. It is *not* fetched by interpreting a `Const` node for
        // `c`: the environment stops at `c`, so `interp` would make it opaque.
        let body = self.interp(ctx, val);
        let Some((ct, def)) = self.const_abbrev(Some(key.clone()), &body) else { return note_dt(Dt::Refused) };

        // `⟦val⟧ ∈ ⟦T⟧` carried across the equation, backwards, by Leibniz.
        let Some(back) = derived::eq_symm(&mut self.env_mut(), &def) else { return note_dt(Dt::Refused) };
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(body, ct.clone(), w, Formula::mem(Term::var(w), tyt.clone()));
        let Some(step) = Thm::mp(&leib, &back) else { return note_dt(Dt::Refused) };
        let Some(out) = Thm::mp(&step, &thm) else { return note_dt(Dt::Refused) };
        // The theorem must conclude the membership it is being stored as. This
        // is the same discipline every rule in this file follows; a stored
        // theorem is checked here *and* against the caller's claim at the point
        // of use.
        if !derived::establishes(&out, &Formula::mem(ct, tyt)) {
            return note_dt(Dt::Refused)
        }
        if !ctx.read_levels(uparams).is_empty() {
            note_dt(Dt::Poly);
        }
        note_dt(Dt::Stored);
        let Ok(out) = Sealed::new(out) else { return note_dt(Dt::Refused) };
        self.shared.borrow_mut().declar_typings.entry(key).or_insert(out);
    }

    /// `⟦c⟧ ∈ ty` — **a lookup**, in the store
    /// [`Self::store_declar_typing`] filled when `c` was checked.
    ///
    /// # What this used to be, and why it is not that any more
    ///
    /// It used to step from the constant to its *value* and recurse, carrying
    /// the membership back along the defining equation. That worked, and it was
    /// the reason `MAX_TYPE_DEPTH` existed: the step follows the delta graph,
    /// which the checker never verifies is acyclic, and it manufactures a fresh
    /// recursion key at every step (`subst_expr_levels` at the use site's
    /// levels), so the cycle guard could not see a chain of distinct constants
    /// either. Nothing else in the recursion is like that — the other edges are
    /// structural, or shrink the target type.
    ///
    /// A constant's typing does not depend on where it is used, so re-deriving
    /// it per use was redundant as well as unbounded. It is now derived once,
    /// where `check_declar` establishes it, and this is the read.
    ///
    /// # The lookup is not a licence
    ///
    /// The stored theorem is about `⟦c.{us}⟧` and the declaration's *declared*
    /// type. It is handed back only after [`Self::has_type_a`]'s single-exit
    /// guard has checked that its conclusion is literally the formula the caller
    /// asked about — a target merely *definitionally* equal to the declared type
    /// is a different formula, and yields `None` and a counted gap.
    ///
    /// # Levels
    ///
    /// The key includes the interpreted level arguments, and a use at other
    /// levels simply misses. See [`Self::store_declar_typing`].
    fn has_type_const(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        let Expr::Const { name, levels, .. } = ctx.read_expr(e) else { return None };
        // Interpreting the constant is what registers its defining equation and
        // fixes which symbol `⟦c⟧` is — and so what a stored theorem has to be
        // about.
        let te = self.interp(ctx, e);

        // ── The store ────────────────────────────────────────────────────────
        //
        // A hit is used only when it concludes *literally* the membership being
        // claimed. The stored theorem is at the declaration's declared type; an
        // obligation at any other target is a different formula, and handing the
        // theorem back for it would be returning a theorem not matched against
        // the claim. So it falls through to the derivation instead.
        if let Some(key) = self.const_key(ctx, name, levels) {
            let hit = self.shared.borrow().declar_typings.get(&key).cloned();
            match hit {
                Some(t) if *t.concl() == Formula::mem(te.clone(), ty.clone()) => {
                    note_dt(Dt::Hit);
                    return Some((
                        u_a1i(t.thm(), conj_of(assms).as_ref()),
                        HtClause::Const,
                        assms.to_vec(),
                    ))
                }
                Some(_) => note_dt(Dt::Wrong),
                None => {
                    // The quantified store (§5.3 step 5). Instantiating the
                    // `∀u⃗` at the variables themselves re-opens exactly the
                    // implication that was generalised, so the guard below is
                    // against the very membership being claimed; the `uᵢ ∈ ω`
                    // antecedents join the caller's own assumption set, which
                    // is the §5.2 channel and is counted by the conditional-
                    // typing ledger like any other antecedent the caller
                    // carries.
                    let phit = self.shared.borrow().declar_typings_poly.get(&key).cloned();
                    if let Some((vars, whyps, sealed)) = phit {
                        let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
                        if let Some(opened) = derived::inst_all(sealed.thm(), &args) {
                            let want = Formula::mem(te.clone(), ty.clone());
                            let h = conj_of(&whyps);
                            if u_concl(&opened, h.as_ref()) == Some(want) {
                                let merged = merge_hyps(assms, &whyps);
                                if let Some(re) = reassume(&opened, &whyps, &merged) {
                                    note_dt(Dt::PolyHit);
                                    return Some((re, HtClause::Const, merged))
                                }
                            }
                        }
                    }
                    note_dt(Dt::Miss);
                    if self.shared.borrow().declined_cond.contains(&key) {
                        note_dt(Dt::MissCond);
                    }
                }
            }
        }

        // ── The derivation ───────────────────────────────────────────────────
        let def = self.const_defs.get(&e).cloned()?;
        let (c_t, val_t) = def.concl().as_eq()?;
        let decls = self.decls;
        let (uparams, val) = decls.get_declar_val(&name)?;
        if ctx.read_levels(levels).len() != ctx.read_levels(uparams).len() {
            return None
        }
        // The visited set. A delta chain that comes back to a constant it is
        // already unfolding cannot terminate, and this is what stops it; see the
        // termination note above.
        let step_key = (name, levels);
        if self.const_active.contains(&step_key) {
            return None
        }
        let val = ctx.subst_expr_levels(val, uparams, levels);
        self.const_active.push(step_key);
        let inner = self.has_type_a(ctx, val, ty, assms, depth + 1);
        self.const_active.pop();
        let (h, used) = inner?;

        // ⊢ ⟦value⟧ = ⟦c⟧, then Leibniz at the hole `x ∈ ty`.
        let back = derived::eq_symm(&mut self.env_mut(), &def)?;
        let x = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(val_t, c_t, x, Formula::mem(Term::var(x), ty.clone()));
        let step = Thm::mp(&leib, &back)?;
        let hyp = conj_of(&used);
        let out = u_mp(&u_a1i(&step, hyp.as_ref()), &h, hyp.as_ref())?;
        Some((out, HtClause::Const, used))
    }

    /// `app(…app(⟦c⟧,a₁)…,aₙ) ∈ T` for a **constructor of a parameterised
    /// inductive**, by instantiating its [`CtorRule`] and discharging the
    /// premises by recursion.
    ///
    /// The unconditional counterpart is [`TgBackend::ind_mems`], which serves
    /// `Bool.true` and `N.zero`. That table cannot serve `List.nil`, because
    /// `List.nil` is not a list — `List.nil α` is, and `α` is a *variable*, so
    /// there is no pair of terms to key on and no theorem without a hypothesis.
    ///
    /// Every premise is settled by [`Self::has_type_h`], so nothing is invented:
    /// `⟦α⟧ ∈ ⟦Type u⟧` is found among the binder's own assumptions, `⟦h⟧ ∈ ⟦α⟧`
    /// likewise, and `⟦t⟧ ∈ ⟦List α⟧` recursively — which is what makes a nested
    /// `cons` work. If any premise cannot be settled the whole clause declines
    /// and the obligation is counted as a gap.
    ///
    /// The spine length must match exactly. A *partial* application —
    /// `List.cons α h` on its own — is not covered: its typing statement is
    /// `∈ fs(⟦List α⟧, ⟦List α⟧)`, which needs the middle graph's function-space
    /// theorem rather than the beta equations, and is not derived.
    fn has_type_ctor_app(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        if !matches!(ctx.read_expr(e), Expr::App { .. }) {
            return None
        }
        let (head, args) = ctx.unfold_apps(e);
        let Expr::Const { name, levels, .. } = ctx.read_expr(head) else { return None };
        // Interpreting the head is what registers the rule, so this comes first
        // and doubles as the "is this one of ours" test.
        self.ind_const(ctx, name, levels)?;
        // Keyed by the instantiation as well as the name: the rule speaks of
        // `⟦Sort ℓ⟧` and of the abbreviation symbols minted for *these* levels,
        // so a use at other levels must miss rather than read the wrong one.
        let lv = self.interp_levels(ctx, levels);
        let rule = self.ctor_rules.get(&(name, lv)).cloned()?;
        if args.len() != rule.vars.len() {
            return None
        }
        let ts: Vec<Term> = args.iter().map(|a| self.interp(ctx, *a)).collect();
        let inst = derived::inst_all(&rule.thm, &ts)?;

        let mut proofs: Vec<(Thm, Vec<Formula>)> = Vec::with_capacity(ts.len());
        let mut used = assms.to_vec();
        for (i, prem) in rule.prems.iter().enumerate() {
            let mut f = prem.clone();
            for (v, t) in rule.vars.iter().zip(ts.iter()) {
                f = f.subst(*v, t);
            }
            let (subj, dom) = f.as_mem()?;
            // The premise must be about the argument it is supposed to be about.
            if subj != ts[i] {
                return None
            }
            // Each premise may acquire further assumptions of its own; `used`
            // grows monotonically and every earlier proof is re-stated under the
            // final list before the conjunction is built.
            let (p, grown) = self.has_type_a(ctx, args[i], &dom, &used, depth + 1)?;
            proofs.push((p, grown.clone()));
            used = grown;
        }

        let hyp = conj_of(&used);
        let mut proofs: Vec<Thm> =
            proofs.iter().map(|(p, from)| reassume(p, from, &used)).collect::<Option<_>>()?;
        let mut acc = proofs.pop()?;
        while let Some(p) = proofs.pop() {
            acc = match hyp.as_ref() {
                None => derived::and_intro(&p, &acc),
                Some(_) => derived::hyp_and(&p, &acc)?,
            };
        }
        let out = u_mp(&u_a1i(&inst, hyp.as_ref()), &acc, hyp.as_ref())?;
        Some((out, HtClause::CtorApp, used))
    }

    /// `app(⟦f⟧,⟦a⟧) ∈ ty` from `⟦f⟧ ∈ ⟦Π A B⟧` and `⟦a⟧ ∈ ⟦A⟧`.
    ///
    /// The `Π` is read off `f`'s *syntactic* type ([`Self::syn_type`]): no
    /// reduction and no definitional equality, so this cannot call back into the
    /// checker while the checker is inside the backend.
    ///
    /// The target `ty` is not an input: what this derives is whatever the
    /// characteristic property yields, and [`Self::has_type_h`]'s guard decides
    /// whether that is the membership being claimed.
    fn has_type_app(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        fun: ExprPtr<'t>,
        arg: ExprPtr<'t>,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        // Interpreting a `Π` builds a fibre — a Replacement derivation — so the
        // shape check that says the head could conceivably be typed at all comes
        // first, and the type is interpreted only if it passes.
        if !self.typeable_shape(ctx, fun, &mut Vec::new()) {
            return None
        }
        let fty0 = self.syn_type(ctx, fun)?;
        let fty = self.expose_pi(ctx, fty0)?;
        let Expr::Pi { binder_type, .. } = ctx.read_expr(fty) else { return None };

        let fty_t = self.interp(ctx, fty);
        let dom_t = self.interp(ctx, binder_type);
        let (tf, ta) = (self.interp(ctx, fun), self.interp(ctx, arg));
        let (hf, used_f) = self.has_type_pi(ctx, fun, fty0, &fty_t, assms, depth)?;
        let (ha, used) = self.has_type_a(ctx, arg, &dom_t, &used_f, depth + 1)?;
        let hf = reassume(&hf, &used_f, &used)?;
        let hyp = conj_of(&used);

        // A function-space target: `⟦Π⟧` is always a `dprod` now, but a typing
        // stated by a `derived` theorem — the ι rules' minor-premise chains —
        // may still name `fs`, and a function's values lie in its codomain.
        if let Some((f, args)) = self.parts.get(&fty_t).cloned() {
            if f == self.pre.fs_sym() && args.len() == 2 && args[0] == dom_t {
                let lem = self.pre.fs_app_mem.clone();
                let out = app_in_codomain(&lem, &dom_t, &args[1], &tf, &ta, &hf, &ha, hyp.as_ref())?;
                return Some((out, HtClause::AppFs, used))
            }
        }

        // Dependent: the `∀x ∈ A. app(f,x) ∈ b(x)` conjunct of the dependent
        // product's defining axiom, then the fibre symbol unfolded.
        let site = self.pi_sites.get(&fty)?;
        let (skel, holes, pdom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        if pdom != dom_t {
            return None
        }
        let info = self.pi_info(&skel)?;
        let fb = info.fibre.as_ref()?;
        let (dprod_def, b_def) = (fb.dprod_def.clone(), fb.b_def.clone());
        let app = self.pre.ap.app;
        let out = app_in_fibre(
            &mut self.env_mut(),
            app,
            &dprod_def,
            &b_def,
            &holes,
            &pdom,
            &tf,
            &ta,
            &hf,
            &ha,
            hyp.as_ref(),
        )?;
        Some((out, HtClause::AppDProd, used))
    }

    /// `⊢ H → ⟦f⟧ ∈ fty_t`, where `fty_t` interprets the `Π` that
    /// [`Self::expose_pi`] found inside `f`'s syntactic type `fty0`.
    ///
    /// The *un*-exposed type is tried first, because it is what everything else
    /// speaks of: a binder's assumption is `⟦w⟧ ∈ ⟦A⟧` for the `A` Lean wrote,
    /// and a constant's own typing is stated at its declared type. The two are
    /// bridged by the defining equation, so the result is still about `fty_t`.
    fn has_type_pi(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        fun: ExprPtr<'t>,
        fty0: ExprPtr<'t>,
        fty_t: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, Vec<Formula>)> {
        let ft0 = self.interp(ctx, fty0);
        if ft0 != *fty_t {
            if let (Some(eq), Some((h, used))) =
                (self.unfolds_to(&ft0, fty_t), self.has_type_a(ctx, fun, &ft0, assms, depth + 1))
            {
                let tf = self.interp(ctx, fun);
                let w = self.env_mut().fresh_var();
                let leib = Thm::eq_leibniz(ft0, fty_t.clone(), w, Formula::mem(tf, Term::var(w)));
                let step = Thm::mp(&leib, &eq)?;
                let hyp = conj_of(&used);
                return Some((u_mp(&u_a1i(&step, hyp.as_ref()), &h, hyp.as_ref())?, used))
            }
        }
        self.has_type_a(ctx, fun, fty_t, assms, depth + 1)
    }

    /// The fibre of a **`Prop`-valued `∀`** at a binder's variable: the set a
    /// proof `λ`'s body has to inhabit.
    ///
    /// `ty` must be `chi_C(q⃗, dom)` for a *registered* conditional singleton
    /// over exactly this lambda's domain — checked, since the term arrives with
    /// no Lean node attached — and the fibre is rebuilt from the skeleton and
    /// compared against what the fibre symbol unfolds to, exactly as the
    /// dependent-product route does. Returns the skeleton key, the target's
    /// arguments, `⊢ b(q⃗,v) = fibre`, and both sides of it.
    #[allow(clippy::type_complexity)]
    fn prop_fibre_at(
        &mut self,
        ty: &Term,
        dom: &Term,
        v: FreeVar,
    ) -> Option<(Term, Vec<Term>, Thm, Term, Term)> {
        let (chi, targs) = self.parts.get(ty).cloned()?;
        let (pkey, pinfo) = self.shared.borrow().prop_by_chi.get(&chi).cloned()?;
        if targs.len() != pinfo.params.len() || targs.last() != Some(dom) {
            return None
        }
        let qholes: Vec<Term> = targs[..targs.len() - 1].to_vec();
        let b_def = pinfo.fibre.as_ref()?.1.clone();
        let mut binst = qholes.clone();
        binst.push(Term::var(v));
        let unfold_b = derived::inst_all(&b_def, &binst)?;
        let (b_at_v, fibre) = unfold_b.concl().as_eq()?;
        // The fibre at the binder is a term the *kernel* built, so its shape is
        // not on record. Rebuild it from the skeleton and check the two agree.
        let mut sub: Vec<(FreeVar, Term)> = Vec::with_capacity(qholes.len() + 1);
        for (i, q) in qholes.iter().enumerate() {
            sub.push((self.hole_var(i), q.clone()));
        }
        sub.push((self.x_canon, Term::var(v)));
        if self.reify(&pkey, &sub)? != fibre {
            return None
        }
        Some((pkey, targs, unfold_b, b_at_v, fibre))
    }

    /// `⊢ conj(rest) → • ∈ chi_C(q⃗,A)` from `⊢ conj(inner) → • ∈ fibre`, the
    /// body's typing under the binder's guard.
    ///
    /// The **`Prop` clause's lambda rule**. Where [`lam_in_funspace_n`] and
    /// [`lam_in_dprod_n`] take a pointwise premise about a graph's values, this
    /// takes the same premise about `•` and feeds it to
    /// [`Self::prop_intro_thm`]. The three steps:
    ///
    /// 1. the body's typing is checked to be about `•` — a proof `λ`'s body is
    ///    itself a proof, and `cond_intro`'s premise speaks of no other subject;
    /// 2. its target is re-aimed from the fibre *term* at the fibre *symbol*,
    ///    by Leibniz over `b(q⃗,v) = fibre`, so that the premise is a statement
    ///    about symbols and can be `∀`-quantified;
    /// 3. the binder's guard is discharged and the variable generalised by the
    ///    same [`Self::guard_and_generalise_at`] every other binder rule uses,
    ///    producing literally the `φ` the singleton is conditional on.
    #[allow(clippy::too_many_arguments)]
    fn prop_lam_close(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        at_v: &Thm,
        inner: &[Formula],
        body: ExprPtr<'t>,
        v: FreeVar,
        dom: &Term,
        pkey: &Term,
        targs: &[Term],
        unfold_b: &Thm,
        b_at_v: &Term,
        fibre: &Term,
    ) -> Option<(Thm, Vec<Formula>, Vec<Formula>)> {
        let point = self.pre.point();
        // Step 1. Nothing here is entitled to *assume* the body interpreted to
        // `•`; the classification says it is a proof, and this is where that is
        // read back off the derivation.
        //
        // A proof's interpretation is `•` on the nose only when it took one of
        // §6.2's two split clauses. `λ α s z. z` at `u := 0` is the standing
        // counterexample: the body is a **variable**, which §6.2 sends to
        // itself, and it is `•` only because the context says so. That is
        // exactly what [`Self::point_of_proof`] derives, and the assumption it
        // needs is the binder's own guard — already in force here — so the
        // rewrite costs nothing that was not already owed.
        let (at_v, inner) = self.point_the_subject(ctx, at_v, inner, body, fibre)?;
        let (at_v, inner) = (&at_v, inner.as_slice());
        let h = conj_of(inner);
        // Step 2.
        let fwd = derived::eq_symm(&mut self.env_mut(), unfold_b)?;
        let (l, r) = fwd.concl().as_eq()?;
        ((l, r) == (fibre.clone(), b_at_v.clone())).then_some(())?;
        let w = self.env_mut().fresh_var();
        let leib =
            Thm::eq_leibniz(fibre.clone(), b_at_v.clone(), w, Formula::mem(point.clone(), Term::var(w)));
        let step = Thm::mp(&leib, &fwd)?;
        let at_v = u_mp(&u_a1i(&step, h.as_ref()), at_v, h.as_ref())?;
        // Step 3.
        let concl = Formula::mem(point, b_at_v.clone());
        let (pointwise, rest) = self.guard_and_generalise_at(&at_v, inner, &concl, v, dom)?;
        let hyp = conj_of(&rest);
        let lem = self.prop_intro_thm(pkey)?;
        let inst = derived::inst_all(&lem, targs)?;
        let out = u_mp(&u_a1i(&inst, hyp.as_ref()), &pointwise, hyp.as_ref())?;
        Some((out, rest, inner.to_vec()))
    }

    /// Re-aim `⊢ conj(inner) → (⟦body⟧ ∈ fibre)` at `• ∈ fibre`.
    ///
    /// The identity when `⟦body⟧` already *is* `•`, which is the case whenever
    /// the body took one of §6.2's split clauses. Otherwise
    /// [`Self::point_of_proof`] supplies `⊢ H → ⟦body⟧ = •` and Leibniz carries
    /// the membership across; whatever `H` adds is merged into the assumption
    /// list and handed back, so the caller's accounting stays exact.
    ///
    /// The merge appends, so the binder's guard keeps its index and
    /// [`drop_guard`] still finds it.
    fn point_the_subject(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        at_v: &Thm,
        inner: &[Formula],
        body: ExprPtr<'t>,
        fibre: &Term,
    ) -> Option<(Thm, Vec<Formula>)> {
        let point = self.pre.point();
        let h = conj_of(inner);
        let concl = u_concl(at_v, h.as_ref())?;
        let (sub, at) = concl.as_mem()?;
        if at != *fibre {
            return None
        }
        if sub == point {
            return Some((at_v.clone(), inner.to_vec()))
        }
        let pe = self.point_of_proof(ctx, body, Pop::SearchLam)?;
        (pe.as_eq()? == (sub.clone(), point.clone())).then_some(())?;
        let hyps = merge_hyps(inner, &pe.hyps);
        let hh = conj_of(&hyps);
        let lifted = reassume(at_v, inner, &hyps)?;
        let eq = reassume(&pe.thm, &pe.hyps, &hyps)?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(sub, point, w, Formula::mem(Term::var(w), fibre.clone()));
        let step = u_mp(&u_a1i(&leib, hh.as_ref()), &eq, hh.as_ref())?;
        Some((u_mp(&step, &lifted, hh.as_ref())?, hyps))
    }

    /// `⟦λx:A. p⟧ ∈ ty` for a **proof** `λ` — §6.2's other lambda clause.
    ///
    /// `⟦λ⟧` is `•` and `ty` has to be the conditional singleton `⟦∀x:A. β⟧`;
    /// the body is typed under the binder's guard and the result closed by
    /// [`Self::prop_lam_close`]. [`Self::has_type_lam`]'s structure, with the
    /// graph machinery removed — there is no skeleton and no beta to line up,
    /// because `•` has no arguments.
    fn has_type_lam_prop(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        let site = self.prop_lam_sites.get(&e)?;
        let (dom, body, v) = (site.dom.clone(), site.body, site.var);
        let (pkey, targs, unfold_b, b_at_v, fibre) = self.prop_fibre_at(ty, &dom, v)?;

        // The guard the body is typed under, appended last so that
        // `guard_and_generalise_at` can peel it off again.
        let mut inner = assms.to_vec();
        inner.push(Formula::mem(Term::var(v), dom.clone()));
        let (at_v, inner) = self.has_type_a(ctx, body, &fibre, &inner, depth + 1)?;
        let (out, rest, inner) = self.prop_lam_close(
            ctx, &at_v, &inner, body, v, &dom, &pkey, &targs, &unfold_b, &b_at_v, &fibre,
        )?;
        // What is left after the discharge must be exactly what went in, plus
        // whatever the body acquired for an *enclosing* local.
        let want = drop_guard(&inner, assms.len())?;
        if rest != want {
            return None
        }
        Some((out, HtClause::LamProp, rest))
    }

    /// `⟦λx:A. b⟧ ∈ ty` — **Lean's lambda typing rule**, by
    /// [`lam_in_funspace_n`] when `ty` is a function space over `⟦A⟧` and by
    /// [`lam_in_dprod_n`] when it is a dependent product over `⟦A⟧`.
    ///
    /// Both lemmas consume the same premise, `∀x. (x ∈ ⟦A⟧ → t(h⃗,x) ∈ …)`, and
    /// that premise is where the recursion goes under the binder: the body is
    /// typed with `⟦x⟧ ∈ ⟦A⟧` added to the assumptions, and the assumption is
    /// then *discharged* into the guard of the `∀` by
    /// [`Self::guard_and_generalise_at`] — the same move
    /// [`Self::pointwise_premise`] makes for the lambda congruence rule, whose
    /// premise has exactly this shape.
    ///
    /// The two body symbols line up by the argument [`Self::beta_step`] makes:
    /// `t(h⃗,x)` unfolds to the skeleton with `x` in the binder slot, which is
    /// literally the interpretation of the opened body — checked here, not
    /// assumed.
    ///
    /// What is left after the discharge is checked to be exactly the assumptions
    /// that went in — the outer ones, plus any the body *acquired* for a local
    /// of the enclosing context, which are handed back to the caller — with the
    /// binder's own assumption gone and nothing else.
    fn has_type_lam(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: &Term,
        assms: &[Formula],
        depth: u32,
    ) -> Option<(Thm, HtClause, Vec<Formula>)> {
        // Interpreting the lambda is what registers its graph symbol and site —
        // or, under §6.2's other clause, records that it has neither.
        let _ = self.interp(ctx, e);
        if self.prop_lam_sites.contains_key(&e) {
            return self.has_type_lam_prop(ctx, e, ty, assms, depth)
        }
        let site = self.lam_sites.get(&e)?;
        let (key, holes, dom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        let (body, v) = (site.body, site.var);

        // The cheap discriminator, first. Both rules below need the target to be
        // a function space or a dependent product **over this lambda's own
        // domain**; anything else declines. It used to be tested at the bottom,
        // after the graph machinery had been derived and the body interpreted,
        // and by far the commonest outcome for a typing obligation about a
        // lambda is that it declines here. The conditions are re-tested where
        // they are used, so this is a cost guard and nothing else.
        let (head, targs) = self.parts.get(ty).cloned()?;
        let fs_shape = head == self.pre.fs_sym() && targs.len() == 2 && targs[0] == dom;
        if !fs_shape
            && !(targs.last() == Some(&dom) && self.shared.borrow().pi_by_dprod.contains_key(&head))
        {
            return None
        }

        let info = self.lam_info(&key)?;
        let t_def = info.graph.as_ref()?.t_def.clone();

        // `t(h⃗,v)` unfolds to the interpretation of the body opened at `v`.
        let mut tinst = holes.clone();
        tinst.push(Term::var(v));
        let unfold_t = derived::inst_all(&t_def, &tinst)?;
        let (t_at_v, bt) = unfold_t.concl().as_eq()?;
        if bt != self.interp(ctx, body) {
            return None
        }

        // The guard the body is typed under, appended last so that
        // `guard_and_generalise_at` can peel it off again.
        let mut inner = assms.to_vec();
        inner.push(Formula::mem(Term::var(v), dom.clone()));

        // ── Non-dependent: a fixed codomain ──────────────────────────────────
        if fs_shape {
            let cod = targs[1].clone();
            let (at_v, inner) = self.has_type_a(ctx, body, &cod, &inner, depth + 1)?;
            let at_v = self.retarget_mem(&at_v, &inner, &unfold_t, &cod, None)?;
            let concl = Formula::mem(t_at_v, cod.clone());
            let (pointwise, rest) = self.guard_and_generalise_at(&at_v, &inner, &concl, v, &dom)?;
            let want = drop_guard(&inner, assms.len())?;
            if rest != want {
                return None
            }
            let hyp = conj_of(&rest);
            let lem = self.lam_fs_thm(&key)?;
            let mut args = holes;
            args.push(dom);
            args.push(cod);
            let inst = derived::inst_all(&lem, &args)?;
            let out = u_mp(&u_a1i(&inst, hyp.as_ref()), &pointwise, hyp.as_ref())?;
            return Some((out, HtClause::LamFs, rest))
        }

        // ── Dependent: the fibre at the binder ───────────────────────────────
        let (pkey, pinfo) = self.shared.borrow().pi_by_dprod.get(&head).cloned()?;
        if targs.last() != Some(&dom) {
            return None
        }
        let qholes: Vec<Term> = targs[..targs.len() - 1].to_vec();
        let b_def = pinfo.fibre.as_ref()?.b_def.clone();
        let mut binst = qholes.clone();
        binst.push(Term::var(v));
        let unfold_b = derived::inst_all(&b_def, &binst)?;
        let (b_at_v, fibre) = unfold_b.concl().as_eq()?;
        // The fibre at the binder is a term the *kernel* built, so its shape is
        // not on record and the recursion could not take it apart. Rebuild it
        // from the skeleton and check the two agree.
        let mut sub: Vec<(FreeVar, Term)> = Vec::with_capacity(qholes.len() + 1);
        for (i, q) in qholes.iter().enumerate() {
            sub.push((self.hole_var(i), q.clone()));
        }
        sub.push((self.x_canon, Term::var(v)));
        if self.reify(&pkey, &sub)? != fibre {
            return None
        }

        let (at_v, inner) = self.has_type_a(ctx, body, &fibre, &inner, depth + 1)?;
        let at_v = self.retarget_mem(&at_v, &inner, &unfold_t, &fibre, Some(&unfold_b))?;
        let concl = Formula::mem(t_at_v, b_at_v);
        let (pointwise, rest) = self.guard_and_generalise_at(&at_v, &inner, &concl, v, &dom)?;
        let want = drop_guard(&inner, assms.len())?;
        if rest != want {
            return None
        }
        let hyp = conj_of(&rest);
        let lem = self.lam_dprod_thm(&key, &pkey)?;
        let mut args = holes;
        args.extend(qholes);
        args.push(dom);
        let inst = derived::inst_all(&lem, &args)?;
        let out = u_mp(&u_a1i(&inst, hyp.as_ref()), &pointwise, hyp.as_ref())?;
        Some((out, HtClause::LamDProd, rest))
    }

    /// Re-aim `⊢ conj(hyps) → (⟦body⟧ ∈ c)` at the two *symbols* the typing
    /// lemmas speak of: `⊢ conj(hyps) → (t(h⃗,v) ∈ b(q⃗,v))`.
    ///
    /// `t_def` is `⊢ t(h⃗,v) = ⟦body⟧` and `b_def`, when the target is a fibre
    /// rather than a fixed codomain, is `⊢ b(q⃗,v) = c`. Both rewrites are
    /// Leibniz over the defining equation, so a definition that does not in fact
    /// unfold to the term in hand makes the `mp` fail rather than the claim slip.
    fn retarget_mem(
        &mut self,
        thm: &Thm,
        hyps: &[Formula],
        t_def: &Thm,
        c: &Term,
        b_def: Option<&Thm>,
    ) -> Option<Thm> {
        let h = conj_of(hyps);
        // The subject: `⟦body⟧` back to `t(h⃗,v)`.
        let back = derived::eq_symm(&mut self.env_mut(), t_def)?;
        let (bt, t_at_v) = back.concl().as_eq()?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(bt, t_at_v.clone(), w, Formula::mem(Term::var(w), c.clone()));
        let step = Thm::mp(&leib, &back)?;
        let out = u_mp(&u_a1i(&step, h.as_ref()), thm, h.as_ref())?;
        let Some(b_def) = b_def else { return Some(out) };
        // The target: `c` back to `b(q⃗,v)`.
        let fwd = derived::eq_symm(&mut self.env_mut(), b_def)?;
        let (fibre, b_at_v) = fwd.concl().as_eq()?;
        if fibre != *c {
            return None
        }
        let w2 = self.env_mut().fresh_var();
        let leib2 = Thm::eq_leibniz(fibre, b_at_v, w2, Formula::mem(t_at_v, Term::var(w2)));
        let step2 = Thm::mp(&leib2, &fwd)?;
        u_mp(&u_a1i(&step2, h.as_ref()), &out, h.as_ref())
    }

    /// [`lam_in_funspace_n`] for one lambda skeleton, derived on first use and
    /// shared thereafter.
    fn lam_fs_thm(&mut self, key: &Term) -> Option<Thm> {
        if let Some(t) = self.shared.borrow().lam_fss.get(key) {
            return t.as_ref().map(|s| s.thm().clone())
        }
        let info = self.lam_info(key)?;
        let thm = match info.graph.as_ref() {
            Some(g) => {
                let (t, lam, lam_ax) = (g.t, info.lam, g.lam_ax.clone());
                let pre = self.pre.clone();
                lam_in_funspace_n(&mut self.env_mut(), &pre.ap, &pre.prod, &pre.fs, t, lam, &lam_ax)
            }
            None => None,
        };
        self.shared.borrow_mut().lam_fss.insert(key.clone(), Sealed::seal(thm.clone()));
        thm
    }

    /// [`lam_in_dprod_n`] for one (lambda skeleton, `Π` skeleton) pair, derived
    /// on first use and shared thereafter.
    fn lam_dprod_thm(&mut self, lkey: &Term, pkey: &Term) -> Option<Thm> {
        let k = (lkey.clone(), pkey.clone());
        if let Some(t) = self.shared.borrow().lam_dprods.get(&k) {
            return t.as_ref().map(|s| s.thm().clone())
        }
        let thm = self.derive_lam_in_dprod(lkey, pkey);
        self.shared.borrow_mut().lam_dprods.insert(k, Sealed::seal(thm.clone()));
        thm
    }

    /// [`Self::lam_dprod_thm`] without the cache.
    fn derive_lam_in_dprod(&mut self, lkey: &Term, pkey: &Term) -> Option<Thm> {
        let li = self.lam_info(lkey)?;
        let pi = self.pi_info(pkey)?;
        let (t, lam) = (li.graph.as_ref()?.t, li.lam);
        let fb = pi.fibre.as_ref()?;
        let (b, img, img_ax, dprod_def) = (fb.b, fb.img, fb.img_ax.clone(), fb.dprod_def.clone());
        let dprod = pi.dprod;
        let beta = self.beta_thm(lkey)?;
        let lam_fs = self.lam_fs_thm(lkey)?;
        let pre = self.pre.clone();
        lam_in_dprod_n(
            &mut self.env_mut(),
            &pre.ap,
            &pre.fs,
            (t, lam, &beta, &lam_fs),
            (b, img, &img_ax, dprod, &dprod_def),
        )
    }

    /// Lean's type for `e`, read off the declaration environment and the
    /// binders — no `whnf`, no `infer`, no definitional equality.
    ///
    /// This is deliberately *not* the checker's `infer`. `infer` lives on
    /// `TypeChecker`, which owns this backend and is in the middle of a call
    /// into it, and it decides definitional equalities on the way — so calling
    /// it here would be re-entrant. Every case below is a projection out of data
    /// already to hand, and anything else is `None`.
    fn syn_type(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let Some(r) = self.syn_types.get(&e) {
            return *r
        }
        let out = match ctx.read_expr(e) {
            Expr::Local { binder_type, .. } => Some(binder_type),
            Expr::Sort { level, .. } => {
                let l = ctx.succ(level);
                Some(ctx.mk_sort(l))
            }
            Expr::Const { name, levels, .. } => {
                let decls = self.decls;
                let info = *decls.get_declar(&name)?.info();
                (ctx.read_levels(levels).len() == ctx.read_levels(info.uparams).len()).then_some(())?;
                Some(ctx.subst_expr_levels(info.ty, info.uparams, levels))
            }
            Expr::App { fun, arg, .. } => {
                let fty = self.syn_type(ctx, fun)?;
                // A `Π` in the head position is what is usable, and [`Self::expose_pi`]
                // is how far this will go to find one: defined constants get
                // unfolded, nothing else happens.
                let fty = self.expose_pi(ctx, fty)?;
                match ctx.read_expr(fty) {
                    Expr::Pi { body, .. } => Some(ctx.inst(body, &[arg])),
                    _ => None,
                }
            }
            Expr::Proj { idx, structure, .. } => self.syn_type_proj(ctx, idx, structure),
            _ => None,
        };
        self.syn_types.insert(e, out);
        out
    }

    /// The field type of a structure projection — [`Self::syn_type`]'s `Proj`
    /// case, and a **delta-only** transcription of `TypeChecker::infer_proj`.
    ///
    /// A projection's type is the `idx`-th binder of the structure's single
    /// constructor, with the parameters instantiated at the structure type's own
    /// arguments and the earlier fields at projections of the same subject. The
    /// checker's version reaches each `Π` by `whnf`; this one may not call back
    /// into the checker, so it reaches them by [`Self::expose_pi`] — delta only
    /// — and declines wherever that is not enough.
    ///
    /// Without it a projection has no type this module can see, and a proof that
    /// is written as a projection is classified `Undet` while the constant it
    /// delta-reduces from is classified `Prop` — one term interpreted two ways.
    fn syn_type_proj(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        idx: usize,
        structure: ExprPtr<'t>,
    ) -> Option<ExprPtr<'t>> {
        let sty = self.syn_type(ctx, structure)?;
        let (_, sname, slevels, sargs) = ctx.unfold_const_apps(sty)?;
        let decls = self.decls;
        let ind = decls.get_structure(&sname, true)?;
        let (num_params, ind_name) = (ind.num_params as usize, ind.info.name);
        let ctor_name = *ind.all_ctor_names.first()?;
        let ctor = decls.get_constructor(&ctor_name)?;
        (ctx.read_levels(slevels).len() == ctx.read_levels(ctor.info.uparams).len()).then_some(())?;
        (sargs.len() >= num_params).then_some(())?;
        let mut cur = ctx.subst_declar_info_levels(ctor.info, slevels);
        // The parameter telescope, at the structure type's own arguments.
        for a in sargs.iter().take(num_params) {
            let p = self.expose_pi(ctx, cur)?;
            let Expr::Pi { body, .. } = ctx.read_expr(p) else { return None };
            cur = ctx.inst(body, &[*a]);
        }
        // The earlier fields, at projections of the same subject — a later
        // field's type may mention an earlier one.
        for i in 0..idx {
            let p = self.expose_pi(ctx, cur)?;
            let Expr::Pi { body, .. } = ctx.read_expr(p) else { return None };
            cur = if ctx.num_loose_bvars(body) == 0 {
                body
            } else {
                let arg = ctx.mk_proj(ind_name, i, structure);
                ctx.inst(body, &[arg])
            };
        }
        let p = self.expose_pi(ctx, cur)?;
        match ctx.read_expr(p) {
            Expr::Pi { binder_type, .. } => Some(binder_type),
            _ => None,
        }
    }

    /// Unfold defined constants at the head of `ty` until a `Π` appears.
    ///
    /// **Delta only.** No beta, no iota, no `whnf`, no definitional equality —
    /// so, like [`Self::syn_type`], this cannot call back into the checker while
    /// the checker is inside the backend. It is nevertheless what makes the
    /// application rule reach anything at all in practice: a Lean function type
    /// is very often written as a defined name (`PN`, `Nat → Nat`, …) and the
    /// `Π` is one unfolding away.
    ///
    /// Terminates because it unfolds each declaration name at most once: the
    /// environment is finite, so the walk stops after at most one step per
    /// declaration. It stops sooner in every real case — a value only mentions
    /// declarations admitted before it — but that is a property of the driver,
    /// and this loop does not depend on it.
    fn expose_pi(&mut self, ctx: &mut TcCtx<'t, 'p>, ty: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let Some(r) = self.exposed.get(&ty) {
            return *r
        }
        let decls = self.decls;
        let mut cur = ty;
        let mut out = None;
        let mut seen: std::collections::HashSet<NamePtr<'t>> = std::collections::HashSet::new();
        loop {
            match ctx.read_expr(cur) {
                Expr::Pi { .. } => {
                    out = Some(cur);
                    break
                }
                Expr::Const { name, levels, .. } => {
                    if !seen.insert(name) {
                        break
                    }
                    let Some((uparams, val)) = decls.get_declar_val(&name) else { break };
                    if ctx.read_levels(levels).len() != ctx.read_levels(uparams).len() {
                        break
                    }
                    cur = ctx.subst_expr_levels(val, uparams, levels);
                }
                _ => break,
            }
        }
        self.exposed.insert(ty, out);
        out
    }

    /// Unfold defined constants at the head of `ty` until a `Sort` appears, and
    /// hand back its level. The [`Self::expose_pi`] of the other shape, and
    /// delta-only for the same reason: it runs while the checker is inside the
    /// backend, so it may not call back into `infer` or `whnf`.
    ///
    /// Terminates for [`Self::expose_pi`]'s reason — each declaration name is
    /// unfolded at most once.
    fn expose_sort(&mut self, ctx: &mut TcCtx<'t, 'p>, ty: ExprPtr<'t>) -> Option<LevelPtr<'t>> {
        if let Some(r) = self.exposed_sorts.get(&ty) {
            return *r
        }
        let decls = self.decls;
        let mut cur = ty;
        let mut out = None;
        let mut seen: std::collections::HashSet<NamePtr<'t>> = std::collections::HashSet::new();
        loop {
            match ctx.read_expr(cur) {
                Expr::Sort { level, .. } => {
                    out = Some(level);
                    break
                }
                Expr::Const { name, levels, .. } => {
                    if !seen.insert(name) {
                        break
                    }
                    let Some((uparams, val)) = decls.get_declar_val(&name) else { break };
                    if ctx.read_levels(levels).len() != ctx.read_levels(uparams).len() {
                        break
                    }
                    cur = ctx.subst_expr_levels(val, uparams, levels);
                }
                _ => break,
            }
        }
        self.exposed_sorts.insert(ty, out);
        out
    }

    /// **Which clause of §6.2 a `Π` with this body falls under.**
    ///
    /// Three answers, not two: `b`'s Lean type is `Sort 0` ([`Clause::Prop`]),
    /// is a `Sort` that is definitely not `0` ([`Clause::Type`]), or is not
    /// decided at all ([`Clause::Undet`]) — either because the level is
    /// `imax u v` at a universe *parameter*, or because this approximation
    /// could not follow the term. The two reasons are counted apart; see
    /// [`Clause`].
    ///
    /// # Why this is a syntactic approximation and not `infer`
    ///
    /// The decision needs the body's sort, `infer` lives on `TypeChecker`,
    /// which owns this backend and is in the middle of a call into it, and the
    /// backend may not call back — the same constraint [`Self::syn_type`] and
    /// [`Self::has_type_app`] are written under. The two candidate routes were
    /// this one and having `infer_pi` stamp its own `imax` verdict into a
    /// context-level side table. The side table loses: `interp` runs on a `Π`
    /// long before inference reaches it — interpreting any declared type that
    /// *contains* the `Π` is enough — so the entry would be read before it was
    /// written and the wrong clause would be locked in. `infer_pi` also
    /// computes one verdict for a whole telescope, where this needs one per
    /// node.
    ///
    /// # Why it is memoised
    ///
    /// Not for speed. `⟦·⟧` must be a **function**: if one expression were
    /// classified `Prop` on one path and `Type` on another, two equal Lean
    /// terms would interpret to unequal set terms and every congruence rule
    /// over them would fail. The answer therefore depends on the expression and
    /// on the declaration environment and on nothing else, and the memo pins
    /// that.
    ///
    /// # Why it looks at heads and arities and never at arguments
    ///
    /// A Lean *level* cannot depend on a term, so `B[a/x]` is a `Sort 0`
    /// exactly when `B` is. Every case below therefore reads the head's
    /// declared type, drops as many `Π` binders as the spine has arguments,
    /// and looks at what is left — never instantiating, and so never caring
    /// that the residue still carries loose de Bruijn indices. That is what
    /// makes the answer agree on definitionally equal types, which
    /// [`Self::syn_type`] alone did not: `syn_type` gives up on a `λ` and on a
    /// `let`, and a `Π` whose body is a redex would then be classified `Type`
    /// while its contractum was classified `Prop`, leaving `derive_pi_cong`
    /// with one term from each clause and nothing to relate them.
    ///
    /// A nested `Π` is answered from [`TgBackend::props`], which
    /// [`Self::interp_pi`] has already stamped: `interp` descends into the body
    /// before the enclosing `Π` asks, so the entry is there. It is recomputed
    /// on a miss rather than defaulted, and the recomputation agrees, because
    /// `imax u v = 0` exactly when `v = 0` however the body is written.
    fn body_clause(&mut self, ctx: &mut TcCtx<'t, 'p>, b: ExprPtr<'t>) -> Clause {
        if let Some(v) = self.props.get(&b) {
            return *v
        }
        let out = match ctx.read_expr(b) {
            // `Sort u : Sort (u+1)`, a successor, which is never `Sort 0`
            // whatever the parameters are.
            Expr::Sort { .. } => Clause::Type,
            // `Π A B : Sort (imax u v)`, and `imax u v = 0` exactly when
            // `v = 0` — so the body decides, all three ways. The body is not
            // opened: nothing below reads a term.
            Expr::Pi { body, .. } => self.body_clause(ctx, body),
            // A `λ`'s type is a `Π`, and a `Π` is not a `Sort`.
            Expr::Lambda { .. } => Clause::Type,
            // A `let` denotes its expansion, and has its type.
            Expr::Let { val, body, .. } => {
                let expansion = ctx.inst(body, &[val]);
                self.body_clause(ctx, expansion)
            }
            Expr::Local { binder_type, .. } => self.clause_after(ctx, binder_type, 0),
            Expr::Const { name, levels, .. } => match self.declared_ty(ctx, name, levels) {
                Some(t) => self.clause_after(ctx, t, 0),
                None => undet_unknown(),
            },
            Expr::App { .. } => {
                let (h, args) = ctx.unfold_apps(b);
                match ctx.read_expr(h) {
                    Expr::Local { binder_type, .. } => self.clause_after(ctx, binder_type, args.len()),
                    Expr::Const { name, levels, .. } => match self.declared_ty(ctx, name, levels) {
                        Some(t) => self.clause_after(ctx, t, args.len()),
                        None => undet_unknown(),
                    },
                    // A redex at the head. Contract it and ask again; the
                    // contractum has the same type, so the two agree — which is
                    // the whole point of asking.
                    Expr::Lambda { body, .. } => {
                        let red = ctx.inst(body, &args[..1]);
                        let red = ctx.foldl_apps(red, args[1..].iter().copied());
                        self.body_clause(ctx, red)
                    }
                    _ => undet_unknown(),
                }
            }
            // A literal's type is `Nat` or `String`, both `Type 0`. A loose de
            // Bruijn index and a projection have types this walk cannot reach.
            Expr::NatLit { .. } | Expr::StringLit { .. } => Clause::Type,
            Expr::Var { .. } | Expr::Proj { .. } => undet_unknown(),
        };
        self.props.insert(b, out);
        out
    }

    /// A constant's declared type at these universe levels.
    fn declared_ty(&mut self, ctx: &mut TcCtx<'t, 'p>, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> Option<ExprPtr<'t>> {
        let decls = self.decls;
        let info = *decls.get_declar(&name)?.info();
        (ctx.read_levels(levels).len() == ctx.read_levels(info.uparams).len()).then_some(())?;
        Some(ctx.subst_expr_levels(info.ty, info.uparams, levels))
    }

    /// Which clause what is left of the type `ty` after `k` arguments have been
    /// applied falls under.
    ///
    /// The binders are *dropped*, not instantiated: a level cannot mention a
    /// term, so the residue's level is the same either way, and dropping them
    /// keeps this usable on a body that still has loose indices in it.
    fn clause_after(&mut self, ctx: &mut TcCtx<'t, 'p>, ty: ExprPtr<'t>, k: usize) -> Clause {
        let mut cur = ty;
        for _ in 0..k {
            let Some(p) = self.expose_pi(ctx, cur) else { return undet_unknown() };
            let Expr::Pi { body, .. } = ctx.read_expr(p) else { return undet_unknown() };
            cur = body;
        }
        match self.expose_sort(ctx, cur) {
            // Dispatch on the level *under the ambient instantiation*, exactly
            // as `TypeChecker::infer_pi` does when it chooses between
            // `TyGap::Pi`, `TyGap::PiProp` and `TyGap::PiUndet`: the three must
            // agree, or a `Π` would be interpreted by one clause and its typing
            // obligation stated for another.
            Some(l) => {
                let s = ctx.under_sigma(l);
                match ctx.read_level(s) {
                    Level::Zero => Clause::Prop,
                    Level::Succ(..) => Clause::Type,
                    // A parameter, or a `max`/`imax` that did not simplify
                    // because a parameter is in the way — which, with a ground
                    // σ in force, means a parameter *no σ names*: the
                    // eliminator universe of a recursor, or anything at all
                    // while an inductive block is being checked. `0` on some
                    // instantiation and not on others; see [`Clause::Undet`].
                    _ => {
                        note_undet(Undet::Param);
                        return Clause::Undet
                    }
                }
            }
            None => undet_unknown(),
        }
    }

    /// **Which clause of §6.2 a `λ` or an application falls under** — the
    /// thesis's `sort(Γ ⊢ e)`, approximated the same way [`Self::body_clause`]
    /// approximates its `lvl(Γ ⊢ α)`.
    ///
    /// §6.2 splits three constructors, not one. Alongside
    ///
    /// ```text
    /// ⟦∀x : α. β⟧ = [∀x ∈ ⟦α⟧. • ∈ ⟦β⟧]      ⟦Πx : α. β⟧ = ∏_{x∈⟦α⟧} ⟦β⟧
    /// ```
    ///
    /// the thesis has
    ///
    /// ```text
    /// ⟦λx : α. e⟧ = •                          ⟦Λx : α. e⟧ = (x ∈ ⟦α⟧ ↦ ⟦e⟧)
    /// ⟦e₁ e₂⟧     = •                          ⟦e₁ · e₂⟧   = ⟦e₁⟧(⟦e₂⟧)
    /// ```
    ///
    /// and the left column is taken exactly when the term is a **proof**, i.e.
    /// when the type of its type is `Sort 0`. That is one level below what
    /// [`Self::body_clause`] answers, and the relation is exactly
    ///
    /// ```text
    /// sort(e) = lvl(type of e)
    /// ```
    ///
    /// so this is not a second classifier: every case below either settles the
    /// question from the level algebra alone or hands the term's *type* to
    /// `body_clause`. Two classifiers that could disagree is precisely what
    /// would make `⟦·⟧` fail to be a function, so there is only one.
    ///
    /// # Why `Undet` keeps the `Type` clause here, and not for `Π`
    ///
    /// [`Self::interp_pi_undet`] builds an axiom-free symbol when neither
    /// clause applies, because *both* real clauses assert something false about
    /// an undecided `Π` — a dependent product is not a subset of `{•}` and vice
    /// versa. A `λ` is different: the `Type` clause builds a function *graph*,
    /// a fresh symbol that identifies nothing, whereas the `Prop` clause
    /// collapses the term to `•` and so identifies it with every other proof.
    /// Guessing `Type` on an undecided term therefore costs gaps; guessing
    /// `Prop` would be an over-identification, which is the one direction that
    /// could make the checker accept something it should not. So `Undet` takes
    /// the `Type` clause, and the mixed-clause gap rows `lam congruence: one
    /// proof λ and one Λ` and `congruence: one proof application and one` are
    /// what say whether that ever costs anything.
    ///
    /// Memoised for [`Self::body_clause`]'s reason and no other: the answer must
    /// depend on the expression and the declaration environment and on nothing
    /// else.
    fn term_clause(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Clause {
        if let Some(v) = self.terms.get(&e) {
            return *v
        }
        let out = match ctx.read_expr(e) {
            // A **type** is never a proof. `Sort u : Sort (u+1)` and
            // `Π A B : Sort (imax u v)`, and a `Sort` is a proof only if some
            // `Sort k` is itself of type `Sort 0` — but `Sort k : Sort (k+1)`,
            // and no `k+1` is `0`.
            Expr::Sort { .. } | Expr::Pi { .. } => Clause::Type,
            // `sort(λx:α. e) = lvl(Πx:α. τ) = imax (lvl α) (sort e)`, and
            // `imax u v = 0` exactly when `v = 0` — so the body decides, all
            // three ways, exactly as it does for `Π` in `body_clause`.
            //
            // The binder is opened rather than left loose: a bare de Bruijn
            // index has no type this walk can read, and every `λ` whose body is
            // the binder would answer `Undet`.
            //
            // Opened at an expression-derived de Bruijn level
            // ([`Self::open_level`]), not a `mk_unique` local: this walk needs
            // no kernel variable at all, only a `Local` node whose type it can
            // read — and a level-local makes `opened` a *stable* `ExprPtr`, so
            // the memo above answers for every identical `λ` instead of
            // exactly once, and `opened` is the same node `interp_lambda`
            // builds, so the two walks share it.
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let level = self.open_level(ctx, e);
                let local = ctx.remake_dbj_level(binder_name, binder_style, binder_type, level);
                let opened = ctx.inst(body, &[local]);
                self.term_clause(ctx, opened)
            }
            // A `let` denotes its expansion, and is a proof exactly when the
            // expansion is.
            Expr::Let { val, body, .. } => {
                let expansion = ctx.inst(body, &[val]);
                self.term_clause(ctx, expansion)
            }
            // A literal's type is `Nat` or `String`, both `Type 0`, so neither
            // is a proof. `syn_type` declines on them, so they are named here
            // rather than defaulting to `Undet`.
            Expr::NatLit { .. } | Expr::StringLit { .. } => Clause::Type,
            // A **redex**. [`Self::syn_type`] gives up on a `λ` in head
            // position, and a whole reduction sequence is redexes: without this
            // case `(λn m. …) lit1 lit1` is undetermined while the constant it
            // unfolded from is a proof, the two interpret to different terms,
            // and the delta step relating them has nothing to prove. Contract
            // and ask again — the contractum has the same type, so the two
            // answers agree, which is the whole point of asking. This is
            // `body_clause`'s redex case, one level down.
            Expr::App { .. } => {
                let (h, args) = ctx.unfold_apps(e);
                match ctx.read_expr(h) {
                    Expr::Lambda { body, .. } if !args.is_empty() => {
                        let red = ctx.inst(body, &args[..1]);
                        let red = ctx.foldl_apps(red, args[1..].iter().copied());
                        self.term_clause(ctx, red)
                    }
                    _ => match self.syn_type(ctx, e) {
                        Some(t) => self.body_clause(ctx, t),
                        None => undet_unknown(),
                    },
                }
            }
            // A **projection out of a proof is a proof.** `syn_type` cannot
            // reach a projection's type — that needs the structure's
            // constructor telescope and a `whnf` this may not run — but the one
            // direction that matters needs no type at all: Lean requires every
            // field of a `Prop`-valued structure to be a `Prop`, and
            // `TypeChecker::infer_proj` rejects the alternative outright. So a
            // projection whose *subject* is a proof is a proof.
            //
            // The converse is false — a `Type`-valued structure may have `Prop`
            // fields — so that direction stays undetermined, and takes the
            // `Type` clause with everything else undecided.
            //
            // Without this, `PSigma.fst α β s` is a proof at `u := 0` while the
            // projection it delta-reduces to is undetermined, the two interpret
            // to different terms, and `081_PSigma.snd` loses eight derivations
            // to a disagreement that is only the walk's.
            Expr::Proj { structure, .. } => match self.syn_type(ctx, e) {
                Some(t) => self.body_clause(ctx, t),
                // A **projection out of a proof is a proof**, whatever the field
                // telescope says: Lean requires every field of a `Prop`-valued
                // structure to be a `Prop`, and `TypeChecker::infer_proj`
                // rejects the alternative outright. The converse is false — a
                // `Type`-valued structure may have `Prop` fields, which is
                // exactly `PSigma.fst` — so the field's own type is what
                // `syn_type_proj` is for, and this is only the fallback.
                None => match self.term_clause(ctx, structure) {
                    Clause::Prop => Clause::Prop,
                    _ => undet_unknown(),
                },
            },
            // Everything else — `Const`, `Local`, a loose index — by the
            // identity `sort(e) = lvl(type of e)`: read the type off the
            // environment and ask the *same* classifier the `Π` split asks.
            _ => match self.syn_type(ctx, e) {
                Some(t) => self.body_clause(ctx, t),
                None => undet_unknown(),
            },
        };
        self.terms.insert(e, out);
        out
    }

    /// Classify an argument whose typing obligation `has_type` could not
    /// discharge, so that the remaining work is a table rather than a guess.
    fn ht_shape(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> HtMiss {
        let head = |b: &mut Self, ctx: &mut TcCtx<'t, 'p>, h: ExprPtr<'t>| match ctx.read_expr(h) {
            Expr::Const { name, .. } => {
                if b.decls.get_declar_val(&name).is_some() {
                    HtMiss::AppDefHead
                } else {
                    HtMiss::AppOpaqueHead
                }
            }
            Expr::Lambda { .. } => HtMiss::AppLamHead,
            Expr::Local { .. } => HtMiss::AppLocalHead,
            _ => HtMiss::AppOther,
        };
        match ctx.read_expr(e) {
            Expr::Local { .. } => HtMiss::Local,
            Expr::Lambda { .. } => HtMiss::Lam,
            Expr::Pi { .. } => HtMiss::Pi,
            Expr::Const { name, .. } =>
                if self.decls.get_declar_val(&name).is_some() {
                    HtMiss::ConstDef
                } else {
                    HtMiss::ConstOpaque
                },
            Expr::App { .. } => {
                let (h, _) = ctx.unfold_apps(e);
                head(self, ctx, h)
            }
            _ => HtMiss::Other,
        }
    }

    /// Classify the *target type* of an obligation `has_type` could not
    /// discharge. The cross-cut of [`Self::ht_shape`]: that one says what the
    /// obligation is *about*, this one says what it is *stated at*, and the two
    /// point at different missing rules.
    fn ht_target(&mut self, ty: &Term) -> HtTarget {
        if let Some((f, args)) = self.parts.get(ty).cloned() {
            if f == self.pre.ap.app && args.len() == 2 {
                let head = args[0].clone();
                let Some((hsym, hargs)) = self.parts.get(&head).cloned() else {
                    return HtTarget::AppVarHead
                };
                if self.shared.borrow().lam_by_lam.contains_key(&hsym) {
                    return HtTarget::AppLamHead
                }
                let curried = hsym == self.pre.ap.app && hargs.len() == 2;
                // Walk down the application spine to its innermost head: that is
                // what decides whether the target could ever reduce.
                let mut cur = head.clone();
                loop {
                    match self.parts.get(&cur).cloned() {
                        Some((s, a)) if s == self.pre.ap.app && a.len() == 2 => cur = a[0].clone(),
                        _ => break,
                    }
                }
                let kind = match self.parts.get(&cur).cloned() {
                    None => 3usize,
                    Some((s, _)) =>
                        if self.shared.borrow().lam_by_lam.contains_key(&s) {
                            0
                        } else if self.abbrev_defs.contains_key(&cur) {
                            1
                        } else {
                            2
                        },
                };
                return match (curried, kind) {
                    (false, 0) => HtTarget::AppLamHead,
                    (false, 1) => HtTarget::AppAbbrevHead,
                    (false, 3) => HtTarget::AppVarHead,
                    (false, _) => HtTarget::AppOpaqueHead,
                    (true, 0) => HtTarget::SpineLam,
                    (true, 1) => HtTarget::SpineAbbrev,
                    (true, 3) => HtTarget::SpineVar,
                    (true, _) => HtTarget::SpineOpaque,
                }
            }
        }
        if self.abbrev_defs.contains_key(ty) {
            return HtTarget::Abbrev
        }
        HtTarget::Other
    }

    /// Whether `e` is of a shape [`Self::has_type_a`] could conceivably discharge.
    ///
    /// A cost guard, not a soundness one: `has_type` would answer `None` for all
    /// of these anyway, but only after interpreting a type, and interpreting a
    /// `Π` builds a fibre. The shapes that are never typeable — a local, an
    /// opaque constant — are much the commonest arguments, so checking first is
    /// what keeps this off the hot path.
    ///
    /// A **lambda** is typeable since [`Self::has_type_lam`] exists. That is not
    /// a detail: a defined constant whose value is a lambda — which is what
    /// nearly every Lean function is — is unreachable without it, and so is
    /// every application of one.
    ///
    /// Terminates for [`Self::expose_pi`]'s reason: `unfolded` carries the
    /// declaration names already stepped through on this path, so each is
    /// unfolded at most once and the walk is bounded by the size of the
    /// environment. Cutting on a repeat is not an approximation — a constant
    /// whose value cycles back to it has no shape to reach, so `false` is the
    /// answer whichever point of the cycle the walk entered at, and memoising it
    /// is sound. The other edge, into an application's function, is structural.
    fn typeable_shape(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        unfolded: &mut Vec<NamePtr<'t>>,
    ) -> bool {
        if let Some(b) = self.typeables.get(&e) {
            return *b
        }
        let out = match ctx.read_expr(e) {
            // A local is typeable under its own binder, by the assumption in
            // force; a lambda by `has_type_lam`.
            Expr::Sort { .. } | Expr::Lambda { .. } | Expr::Local { .. } => true,
            Expr::Const { name, levels, .. } => {
                let decls = self.decls;
                match decls.get_declar_val(&name) {
                    Some((uparams, val)) if ctx.read_levels(levels).len() == ctx.read_levels(uparams).len() => {
                        if unfolded.contains(&name) {
                            false
                        } else {
                            let val = ctx.subst_expr_levels(val, uparams, levels);
                            unfolded.push(name);
                            let r = self.typeable_shape(ctx, val, unfolded);
                            unfolded.pop();
                            r
                        }
                    }
                    // An opaque constant is not typeable — *unless* it is one of
                    // the constructors this backend interprets, whose typing is
                    // a real theorem rather than an axiom. `N.succ` is one, and
                    // without this its applications never reach the function
                    // space rule at all.
                    _ => self.interpreted_shape(ctx, &name, levels),
                }
            }
            Expr::App { fun, .. } => self.typeable_shape(ctx, fun, unfolded),
            _ => false,
        };
        self.typeables.insert(e, out);
        out
    }

    /// `⟦w⟧ ∈ ⟦A⟧` for every local `w : A` free in `e`, in traversal order.
    ///
    /// These are the typing facts a beta step is *allowed* to lean on, and the
    /// reason is structural rather than opportunistic: a local's typing is
    /// exactly what a `λ` binder's own pointwise premise supplies, so an
    /// obligation reduced to them is an obligation that will be discharged when
    /// the checker climbs back out of the binders — by
    /// [`Self::guard_and_generalise_at`], with the kernel checking the side
    /// condition each time.
    ///
    /// The alternative — assuming `⟦a⟧ ∈ ⟦A⟧` outright — is strictly worse than
    /// this even when both end up carried, because the raw assumption mentions
    /// the binder's variable *inside a compound term* and so blocks the
    /// generalisation at that binder, whereas `⟦w⟧ ∈ ⟦A⟧` is precisely the
    /// guard being introduced there.
    fn local_premises(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Vec<Formula> {
        let mut locals = Vec::new();
        let mut seen = Vec::new();
        self.collect_locals(ctx, e, &mut locals, &mut seen);
        locals
            .into_iter()
            .filter_map(|l| {
                let Expr::Local { binder_type, .. } = ctx.read_expr(l) else { return None };
                let (w, a) = (self.interp(ctx, l), self.interp(ctx, binder_type));
                Some(Formula::mem(w, a))
            })
            .collect()
    }

    /// The `Local` nodes of `e`, without repetition.
    fn collect_locals(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        out: &mut Vec<ExprPtr<'t>>,
        seen: &mut Vec<ExprPtr<'t>>,
    ) {
        if seen.contains(&e) {
            return
        }
        seen.push(e);
        let mut go = |b: &mut Self, ctx: &mut TcCtx<'t, 'p>, x: ExprPtr<'t>| b.collect_locals(ctx, x, out, seen);
        match ctx.read_expr(e) {
            Expr::Local { .. } =>
                if !out.contains(&e) {
                    out.push(e)
                },
            Expr::App { fun, arg, .. } => {
                go(self, ctx, fun);
                go(self, ctx, arg);
            }
            Expr::Lambda { binder_type, body, .. } | Expr::Pi { binder_type, body, .. } => {
                go(self, ctx, binder_type);
                go(self, ctx, body);
            }
            Expr::Let { binder_type, val, body, .. } => {
                go(self, ctx, binder_type);
                go(self, ctx, val);
                go(self, ctx, body);
            }
            Expr::Proj { structure, .. } => go(self, ctx, structure),
            _ => {}
        }
    }

    /// The beta theorem for one lambda skeleton, derived on first use.
    fn beta_thm(&mut self, key: &Term) -> Option<Thm> {
        if let Some(t) = self.shared.borrow().lam_betas.get(key) {
            return t.as_ref().map(|s| s.thm().clone())
        }
        let info = self.lam_info(key)?;
        let g = info.graph.as_ref()?;
        let (t, lam, lam_ax) = (g.t, info.lam, g.lam_ax.clone());
        let ap = self.pre.clone();
        let thm = beta_conditional_n(&mut self.env_mut(), &ap.ap, t, lam, &lam_ax);
        self.shared.borrow_mut().lam_betas.insert(key.clone(), Sealed::seal(thm.clone()));
        thm
    }

    /// The typing obligation a beta contraction rests on: `⊢ … → ⟦a⟧ ∈ dom`,
    /// together with the assumptions it is stated under.
    ///
    /// The obligation is Lean's typing judgement, and `has_type` is that
    /// judgement — one clause per typing rule. When no clause applies the step
    /// is **not** admitted: the premise is kept as a genuine assumption and the
    /// certificate says so, `⊢ (⟦a⟧ ∈ dom) → …`. It then has to be discharged
    /// before the certificate reaches a boundary, or it is reported as a gap
    /// (see `escape_report`).
    ///
    /// `has_type_a` may *acquire* the ambient typing of a context local on the
    /// way — see [`Self::has_type_local`] — so what comes back is the derivation
    /// together with the assumption list it is stated under. An empty list is
    /// the unconditional case, and only that counts as discharged in the ledger.
    ///
    /// Shared by [`Self::beta_step`] and by the iota rule, whose curried nest
    /// pays exactly the same obligation once per Lean argument.
    fn domain_obligation(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        arg: ExprPtr<'t>,
        ta: &Term,
        dom: &Term,
    ) -> (Option<Thm>, Vec<Formula>) {
        let mut hyps = Vec::new();
        let mut mem_inst = match self.has_type_a(ctx, arg, dom, &[], 0) {
            Some((t, used)) => {
                hyps = used;
                Some(t)
            }
            None => None,
        };
        note_ht_call(mem_inst.is_some() && hyps.is_empty());
        // Failing an outright derivation, *reduce* the obligation instead of
        // assuming it: the argument's typing usually follows from the typing of
        // the locals it mentions, and those are exactly the assumptions a `λ`
        // binder discharges. See [`Self::local_premises`].
        if mem_inst.is_none() || !hyps.is_empty() {
            note_ht_miss(self.ht_shape(ctx, arg));
            let t = self.ht_target(dom);
            note_ht_target(t);
        }
        if mem_inst.is_none() {
            let prem = self.local_premises(ctx, arg);
            if !prem.is_empty() {
                if let Some(t) = self.has_type_h(ctx, arg, dom, &prem, 0) {
                    mem_inst = Some(t);
                    hyps = prem;
                }
            }
            if mem_inst.is_none() {
                // The raw fallback: nothing about the argument was derived, so
                // the membership itself becomes the assumption. Counted
                // separately, and cross-cut by target shape, because this is the
                // set the next rule has to attack.
                note_ht_raw(self.ht_shape(ctx, arg));
                let t = self.ht_target(dom);
                note_ht_raw_target(t);
                hyps = vec![Formula::mem(ta.clone(), dom.clone())];
            }
        }
        (mem_inst, hyps)
    }

    /// One beta contraction: `⊢ app(⟦λ⟧, ⟦a⟧) = ⟦body[a]⟧`, possibly under the
    /// assumption `⟦a⟧ ∈ dom` when the typing obligation cannot be discharged.
    fn beta_step(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        lam_expr: ExprPtr<'t>,
        body: ExprPtr<'t>,
        arg: ExprPtr<'t>,
    ) -> Result<(CondEq, ExprPtr<'t>), &'static str> {
        // Interpreting the lambda is what registers its graph symbol.
        let _ = self.interp(ctx, lam_expr);
        let Some(site) = self.lam_sites.get(&lam_expr) else {
            return Err("beta: the lambda has no function-graph interpretation")
        };
        let (key, holes, dom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        let ta = self.interp(ctx, arg);

        // The domain premise is settled *first*: it is a term comparison plus
        // one instantiation, while the beta lemma below is a derivation, and
        // most redexes fail here.
        //
        // The obligation is Lean's typing judgement, and `has_type` is that
        // judgement — one clause per typing rule, over the two facts
        // `domain_premise` knows about the operators themselves. When no clause
        // applies the step is **not** admitted: the premise is kept as a genuine assumption and
        // the certificate says so, `⊢ (⟦a⟧ ∈ dom) → …`. It then has to be
        // discharged before the certificate reaches a boundary, or it is
        // reported as a gap (see `escape_report`).
        //
        // `has_type_a` may *acquire* the ambient typing of a context local on the
        // way — see [`Self::has_type_local`] — so what comes back is the
        // derivation together with the assumption list it is stated under. An
        // empty list is the unconditional case, and only that counts as
        // discharged in the ledger.
        let (mem_inst, hyps) = self.domain_obligation(ctx, arg, &ta, &dom);
        let Some(beta) = self.beta_thm(&key) else {
            return Err("beta: the lambda's graph, and so its beta lemma, was not built")
        };

        // ⊢ ⟦a⟧ ∈ dom → app(lam(h⃗,dom), ⟦a⟧) = t(h⃗, ⟦a⟧)
        let mut inst = holes.clone();
        inst.push(dom.clone());
        inst.push(ta.clone());
        let Some(conditional) = derived::inst_all(&beta, &inst) else {
            return Err("beta: instantiating the beta lemma failed")
        };

        // With the membership in hand the premise comes off — outright, or under
        // whatever the reduction above left. Without it the implication *is* the
        // certificate, its antecedent being the single assumption recorded above.
        let hyp = conj_of(&hyps);
        let eq_t = match &mem_inst {
            Some(m) => {
                let Some(t) = u_mp(&u_a1i(&conditional, hyp.as_ref()), m, hyp.as_ref()) else {
                    return Err("beta: discharging the domain premise failed")
                };
                t
            }
            None => conditional,
        };
        let Some(eq_t) = CondEq::new(eq_t, hyps) else {
            return Err("beta: the beta lemma does not have the assumed shape")
        };

        // Unfold `t(h⃗, ⟦a⟧)` to the skeleton with the argument plugged in, and
        // check that is literally the interpretation of the contracted body.
        let info = self.lam_info(&key).expect("skeleton registered");
        let Some(g) = info.graph.as_ref() else {
            return Err("beta: the lambda's graph was not built")
        };
        let mut inst_t = holes;
        inst_t.push(ta);
        let Some(unfold) = derived::inst_all(&g.t_def, &inst_t) else {
            return Err("beta: instantiating the body definition failed")
        };
        let Some(unfold) = CondEq::plain(unfold) else {
            return Err("beta: the body definition is not an equation")
        };
        let Some(step) = self.ceq_trans(&eq_t, &unfold) else {
            return Err("beta: chaining the body definition failed")
        };

        let next = ctx.inst(body, &[arg]);
        let tnext = self.interp(ctx, next);
        let Some((_, rhs)) = step.as_eq() else {
            return Err("beta: the derived step is not an equation")
        };
        if rhs != tnext {
            return Err("beta: the contracted body does not match its interpretation")
        }
        Ok((step, next))
    }

    /// The whole (possibly multi-argument) beta contraction the checker asked
    /// for, as `⊢ ⟦redex⟧ = ⟦reduct⟧` — or, where a contraction's typing
    /// obligation could not be discharged, under the assumptions it needed.
    fn derive_beta(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
    ) -> Result<CondEq, &'static str> {
        let (fun, args) = ctx.unfold_apps(redex);
        if args.is_empty() {
            return Err("beta: the redex is not an application")
        }
        // How many contractions the checker actually made. It peels the
        // **syntactic** leading lambdas of the head, one per argument, and
        // re-applies whatever is left — so counting them here on the same
        // uninstantiated nesting is what makes the two agree. Counting instead
        // on the *substituted* body over-reduces: in `075` the zero rule
        // `(λ motive zero succ. zero) C z s m` puts `fun m => m` in the head
        // position after three contractions, and the checker stops there while
        // a fourth contraction would silently prove a different equation. It
        // would be caught by the guard below — it was, three times — but as a
        // gap rather than as the derivation that was available.
        let mut n_steps = 0usize;
        let mut b = fun;
        while n_steps < args.len() {
            let Expr::Lambda { body, .. } = ctx.read_expr(b) else { break };
            n_steps += 1;
            b = body;
        }

        let mut cur = fun;
        let mut acc = CondEq::refl(self.interp(ctx, fun));
        let app = self.pre.ap.app;

        for (k, arg) in args.into_iter().enumerate() {
            let ta = self.interp(ctx, arg);
            let Some(lifted) = self.ceq_congr(app, &[acc.clone(), CondEq::refl(ta)]) else {
                return Err("beta: congruence over the spine refused")
            };
            acc = lifted;
            if k < n_steps {
                let Expr::Lambda { body, .. } = ctx.read_expr(cur) else {
                    return Err("beta: the head is not the lambda nest it was counted as")
                };
                let (step, next) = self.beta_step(ctx, cur, body, arg)?;
                let Some(chained) = self.ceq_trans(&acc, &step) else {
                    return Err("beta: chaining a contraction failed")
                };
                acc = chained;
                cur = next;
            }
        }

        // Guard. The derivation is worth nothing unless it is a derivation of
        // the equation the checker actually claimed.
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if !acc.proves(&lhs, &rhs) {
            return Err("beta: derived equation does not match the reduction")
        }
        Ok(acc)
    }

    /// The beta contractions of a spine, as far as they go: `⊢ ⟦e⟧ = ⟦e′⟧`
    /// with `e′` the head-normal form the checker itself would compute.
    ///
    /// [`Self::derive_beta`] with the reduct *discovered* rather than supplied.
    /// The iota rule needs it because the reduct it is handed is the minor
    /// premise's lambda re-applied to the recursor's arguments, and what that
    /// contracts to is precisely what the left-hand side has to be matched
    /// against.
    fn beta_spine(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
    ) -> Result<(CondEq, ExprPtr<'t>), &'static str> {
        let (fun, args) = ctx.unfold_apps(e);
        let mut cur = fun;
        let mut acc = CondEq::refl(self.interp(ctx, fun));
        let app = self.pre.ap.app;
        for arg in args {
            let ta = self.interp(ctx, arg);
            let Some(lifted) = self.ceq_congr(app, &[acc.clone(), CondEq::refl(ta)]) else {
                return Err("iota: congruence over the reduct's spine refused")
            };
            acc = lifted;
            if let Expr::Lambda { body, .. } = ctx.read_expr(cur) {
                let (step, next) = self.beta_step(ctx, cur, body, arg)?;
                let Some(chained) = self.ceq_trans(&acc, &step) else {
                    return Err("iota: chaining a contraction of the reduct failed")
                };
                acc = chained;
                cur = next;
            } else {
                return Err("iota: the reduct's spine is not a redex all the way down")
            }
        }
        Ok((acc, cur))
    }

    /// `⊢ conj(hyps) → ⟦a⟧ ∈ dom`, with the assumptions it rests on.
    ///
    /// [`Self::domain_obligation`] in the one shape every caller here wants: a
    /// real implication whether or not the typing was discharged. When it was
    /// not, the membership *is* the assumption and the implication is
    /// reflexivity — which is exactly as strong as the derivation, and no
    /// stronger.
    fn mem_obligation(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        arg: ExprPtr<'t>,
        ta: &Term,
        dom: &Term,
    ) -> Option<(Thm, Vec<Formula>)> {
        let (mem, hyps) = self.domain_obligation(ctx, arg, ta, dom);
        match mem {
            Some(t) => Some((t, hyps)),
            None => Some((derived::imp_refl(conj_of(&hyps)?), hyps)),
        }
    }

    /// Move a derived membership along a defining equation.
    ///
    /// The interpretation names an inductive by an **abbreviation** — `⟦N⟧`,
    /// with `⊢ ⟦N⟧ = W(1+1,B,U(1+1))` — while `derived`'s theorems are stated at
    /// the W-type itself. `has_type` answers at the abbreviation, because that
    /// is what a Lean type interprets to; the ι rules want the other. One
    /// Leibniz step bridges them, and the *assumptions* stay stated at the
    /// abbreviation, which is what lets a λ binder discharge them later.
    fn mem_along(
        &mut self,
        thm: &Thm,
        hyps: &[Formula],
        eq: &Thm,
        phi: impl Fn(Term) -> Formula,
    ) -> Option<Thm> {
        let (a, b) = eq.concl().as_eq()?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(a, b, w, phi(Term::var(w)));
        let imp = Thm::mp(&leib, eq)?;
        match conj_of(hyps) {
            None => Thm::mp(&imp, thm),
            Some(_) => derived::syl(thm, &imp),
        }
    }

    /// Contract the curried nest at one argument list: `⊢ ⟦T.rec a⃗⟧ = body`,
    /// where `body` is the nest's bottom — the W-recursor applied to the last
    /// argument.
    ///
    /// `args` runs from the first recursor argument up to and including the
    /// major premise, and `doms` are the matching domains **walked off the
    /// recursor's own type at those very arguments**. Returns the chain
    /// together with each level's typing obligation, because the ι rules need
    /// two of them again as their own hypotheses and asking twice would both
    /// double-count the ledger and risk asking at a different term.
    #[allow(clippy::type_complexity)]
    fn nest_chain(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        nest: &RecNest,
        args: &[ExprPtr<'t>],
        ta: &[Term],
        doms: &[Term],
    ) -> Result<(CondEq, Vec<(Thm, Vec<Formula>)>), &'static str> {
        let app = self.pre.ap.app;
        let Some(mut acc) = CondEq::plain(nest.head_def.clone()) else {
            return Err("iota: the recursor's defining equation is not an equation")
        };
        let mut obligations = Vec::with_capacity(args.len());
        for k in 0..args.len() {
            let Some(lifted) = self.ceq_congr(app, &[acc.clone(), CondEq::refl(ta[k].clone())])
            else {
                return Err("iota: congruence over the recursor's spine refused")
            };
            acc = lifted;

            let Some((mem_inst, hyps)) = self.mem_obligation(ctx, args[k], &ta[k], &doms[k]) else {
                return Err("iota: a domain obligation has no assumption to rest on")
            };
            let mut inst: Vec<Term> = nest.prefixes[k].iter().map(|i| ta[*i].clone()).collect();
            inst.push(doms[k].clone());
            inst.push(ta[k].clone());
            let Some(conditional) = derived::inst_all(&nest.betas[k], &inst) else {
                return Err("iota: instantiating the nest's beta lemma failed")
            };
            let hyp = conj_of(&hyps);
            let Some(eq_t) = u_mp(&u_a1i(&conditional, hyp.as_ref()), &mem_inst, hyp.as_ref())
            else {
                return Err("iota: discharging a domain premise failed")
            };
            let Some(eq_t) = CondEq::new(eq_t, hyps.clone()) else {
                return Err("iota: the nest's beta lemma does not have the assumed shape")
            };
            obligations.push((mem_inst, hyps));

            let mut inst_t: Vec<Term> = nest.prefixes[k].iter().map(|i| ta[*i].clone()).collect();
            inst_t.push(ta[k].clone());
            let Some(unfold) = derived::inst_all(&nest.t_defs[k], &inst_t) else {
                return Err("iota: instantiating the nest's body definition failed")
            };
            let Some(unfold) = CondEq::plain(unfold) else {
                return Err("iota: the nest's body definition is not an equation")
            };
            let Some(step) = self.ceq_trans(&eq_t, &unfold) else {
                return Err("iota: chaining the nest's body definition failed")
            };
            let Some(chained) = self.ceq_trans(&acc, &step) else {
                return Err("iota: chaining a contraction of the nest failed")
            };
            acc = chained;
        }
        Ok((acc, obligations))
    }

    /// **The iota rule**: `⊢ ⟦T.rec … cᵢ …⟧ = ⟦reduct⟧`.
    ///
    /// Both sides are reduced to the *same* term and joined:
    ///
    /// * the left by unfolding `⟦T.rec⟧` to its curried nest ([`RecNest`]),
    ///   contracting one graph per recursor argument, and firing the W-recursor
    ///   equation the nest's bottom supplies at the constructor;
    /// * the right by contracting the redex `reduce_rec` produced, which is the
    ///   matching `RecRule::val` re-applied to the same arguments.
    ///
    /// The two sides therefore carry **the same** domain premises — the nest's
    /// domains are read off the recursor's own type and the reduct's off the
    /// same Lean binder types — so merging them adds nothing, and any premise
    /// that cannot be discharged is carried once rather than twice.
    ///
    /// # Trailing arguments
    ///
    /// A recursor may be applied to **more** than its own arguments: `075`'s
    /// motive is a function type, so `N.rec C z s t m` has one argument past the
    /// major premise. Those are not part of the ι step at all — `reduce_rec`
    /// re-applies them unchanged to the reduct — so the equation is derived at
    /// the *core*, the recursor applied to exactly its own arguments, and lifted
    /// over the rest by congruence. That is also why the guard at the end
    /// compares against the full redex and reduct rather than the core.
    fn derive_iota(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
    ) -> Result<CondEq, &'static str> {
        let (fun, args) = ctx.unfold_apps(redex);
        let Expr::Const { name, levels, .. } = ctx.read_expr(fun) else {
            return Err("iota: the redex head is not a constant")
        };
        let Some(Declar::Recursor(r)) = self.decls.get_declar(&name) else {
            return Err("iota: the head is not a recursor")
        };
        let depth = r.major_idx() + 1;
        if args.len() < depth {
            return Err("iota: the recursor is not applied to its major premise")
        }
        let Some(nest) = self.rec_nest(ctx, name, levels) else {
            return Err("iota: this recursor has no curried interpretation")
        };

        // ── Split off the trailing arguments, on both sides ──────────────────
        let trailing = args.len() - depth;
        let core_args: Vec<ExprPtr<'t>> = args[..depth].to_vec();
        let core_redex = ctx.foldl_apps(fun, core_args.iter().copied());
        let (rfun, rargs) = ctx.unfold_apps(reduct);
        if rargs.len() < trailing {
            return Err("iota: the reduct has fewer arguments than the redex")
        }
        let keep = rargs.len() - trailing;
        if rargs[keep..] != args[depth..] {
            return Err("iota: the reduct's trailing arguments are not the redex's")
        }
        let core_reduct = ctx.foldl_apps(rfun, rargs[..keep].iter().copied());

        let mut out = self.derive_iota_core(ctx, &nest, fun, &core_args, core_redex, core_reduct)?;

        // ── Back over the trailing arguments, congruence on both sides ───────
        let app = self.pre.ap.app;
        for a in &args[depth..] {
            let ta = self.interp(ctx, *a);
            let Some(lifted) = self.ceq_congr(app, &[out.clone(), CondEq::refl(ta)]) else {
                return Err("iota: congruence over a trailing argument refused")
            };
            out = lifted;
        }

        // The guard. The derivation is worth nothing unless it is a derivation
        // of the equation the checker actually claimed.
        let (l, rr) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if !out.proves(&l, &rr) {
            return Err("iota: derived equation does not match the reduction")
        }
        Ok(out)
    }

    /// The ι equation at the recursor applied to exactly its own arguments.
    fn derive_iota_core(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        nest: &RecNest,
        fun: ExprPtr<'t>,
        args: &[ExprPtr<'t>],
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
    ) -> Result<CondEq, &'static str> {
        let major = args.len() - 1;

        // Which constructor is the major premise, and what its fields are. Read
        // off `ConstructorData`, never off the name — and the major premise may
        // be **applied**: `N.succ n` is a constructor with a field, and
        // `List.cons α h t` is one with a parameter in front of two.
        //
        // The parameters are dropped here, and that has to mirror `reduce_rec`
        // exactly: it skips `num_extra_params_to_major` of the constructor's
        // arguments before re-applying the rule, which for a non-nested
        // inductive is its `num_params`. Requiring the argument count to be
        // *exactly* `num_params + num_fields` is what makes the two agree; a
        // mismatch would in any case be caught by the guard below, which
        // compares the derived equation against the reduct `reduce_rec` really
        // produced.
        let (cfun, ctor_args) = ctx.unfold_apps(args[major]);
        let Expr::Const { name: cname, .. } = ctx.read_expr(cfun) else {
            return Err("iota: the major premise is not a constructor")
        };
        let Some(Declar::Constructor(c)) = self.decls.get_declar(&cname) else {
            return Err("iota: the major premise is not a constructor")
        };
        let idx = c.ctor_idx as usize;
        let cnp = c.num_params as usize;
        // How many constructors the bottom computes for. The three hand-written
        // arms are two-constructor shapes and keep the bound they were written
        // at; the general one knows its own `n`, which is `WIRING-DESIGN.md`
        // §6.2's `idx >= n`. Getting this wrong costs a gap, not a wrong claim:
        // `derive_iota`'s guard compares the derived equation against the
        // reduction either way.
        let n_ctors = match &nest.bottom {
            RecBottom::General(g, _) => g.gi.ind.spec.ctors.len(),
            _ => 2,
        };
        if idx >= n_ctors || ctor_args.len() != cnp + c.num_fields as usize {
            return Err("iota: the constructor is not one this backend computes")
        }
        let fields: Vec<ExprPtr<'t>> = ctor_args[cnp..].to_vec();
        // The parameters the major premise's constructor was applied to. The
        // general path needs them: `⟦cᵢ p⃗ f⃗⟧` is a spine over both, and the
        // bridge to `ctorᵢ(y⃗,r⃗)` is instantiated at the whole list.
        let cparams: Vec<ExprPtr<'t>> = ctor_args[..cnp].to_vec();

        // The domains **at the actual arguments**, walked off the recursor's
        // type exactly as the nest's were walked off it at locals.
        let Expr::Const { name, levels, .. } = ctx.read_expr(fun) else {
            return Err("iota: the redex head is not a constant")
        };
        let Some(Declar::Recursor(r)) = self.decls.get_declar(&name) else {
            return Err("iota: the head is not a recursor")
        };
        let (uparams, ty) = (r.info.uparams, r.info.ty);
        let mut cur = ctx.subst_expr_levels(ty, uparams, levels);
        let mut doms: Vec<Term> = Vec::with_capacity(args.len());
        for a in args {
            let Expr::Pi { binder_type, body, .. } = ctx.read_expr(cur) else {
                return Err("iota: the recursor's type is not the telescope its data claims")
            };
            doms.push(self.interp(ctx, binder_type));
            cur = ctx.inst(body, &[*a]);
        }
        let ta: Vec<Term> = args.iter().map(|a| self.interp(ctx, *a)).collect();

        // ── The left-hand side: unfold, contract, then fire ──────────────────
        let (chain, obligations) = self.nest_chain(ctx, nest, args, &ta, &doms)?;
        let fired = match nest.bottom.clone() {
            RecBottom::Enum(br) => self.fire_enum(&br, &ta, idx)?,
            RecBottom::Nat(nr) => self
                .fire_nat(ctx, &nr, nest, cfun, args, &ta, &doms, &obligations, idx, &fields)?,
            RecBottom::List(lr) => self
                .fire_list(ctx, &lr, nest, cfun, args, &ta, &doms, &obligations, idx, &fields)?,
            RecBottom::General(gr, tn) => self.fire_general(
                ctx, &gr, &tn, nest, cfun, args, &ta, &doms, &obligations, idx, &cparams,
                &fields,
            )?,
        };
        let Some(lhs_chain) = self.ceq_trans(&chain, &fired) else {
            return Err("iota: chaining the computation rule failed")
        };

        // ── The right-hand side: the reduct contracts to the same term ───────
        let (rhs_chain, rhs_final) = self.beta_spine(ctx, reduct)?;
        let final_t = self.interp(ctx, rhs_final);
        let Some((_, fired_rhs)) = lhs_chain.as_eq() else {
            return Err("iota: the left-hand chain is not an equation")
        };
        if final_t != fired_rhs {
            return Err("iota: the reduct does not contract to what the recursor computes")
        }
        let Some(back) = self.ceq_symm(&rhs_chain) else {
            return Err("iota: reversing the reduct's contraction failed")
        };
        let Some(out) = self.ceq_trans(&lhs_chain, &back) else {
            return Err("iota: joining the two sides failed")
        };
        let (l, rr) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if !out.proves(&l, &rr) {
            return Err("iota: the core equation does not match the reduction")
        }
        Ok(out)
    }

    /// The ι rule for a two-constructor enumeration:
    /// `⊢ app(brec(f,t), ⟨inj •,∅⟩) = minor`, unconditional in both minor
    /// premises. `derived::wbool_rec` does the work; this is the matching.
    fn fire_enum(
        &mut self,
        br: &BoolRecursor,
        ta: &[Term],
        idx: usize,
    ) -> Result<CondEq, &'static str> {
        let app = self.pre.ap.app;
        // The constructor is an abbreviation; the recursor's equation is stated
        // at the W-type element it abbreviates, so one Leibniz step joins them.
        let Some(ctor_def) = self.abbrev_defs.get(&ta[3]).cloned() else {
            return Err("iota: the constructor has no defining equation")
        };
        let Some(ctor_def) = CondEq::plain(ctor_def) else {
            return Err("iota: the constructor's defining equation is not an equation")
        };
        let brec = br.brec(&self.pre.ap.clone(), &ta[1], &ta[2]);
        let Some(at_ctor) = self.ceq_congr(app, &[CondEq::refl(brec.clone()), ctor_def]) else {
            return Err("iota: congruence at the constructor refused")
        };

        let Some(fired) = derived::inst_all(&br.iota[idx], &[ta[1].clone(), ta[2].clone()]) else {
            return Err("iota: instantiating the W-recursor's computation rule failed")
        };
        let want =
            Formula::eq(self.pre.ap.apply(brec, br.ctors[idx].clone()), ta[1 + idx].clone());
        if *fired.concl() != want {
            return Err("iota: the W-recursor's computation rule is not about this instance")
        }
        let Some(fired) = CondEq::plain(fired) else {
            return Err("iota: the computation rule is not an equation")
        };
        match self.ceq_trans(&at_ctor, &fired) {
            Some(t) => Ok(t),
            None => Err("iota: the nest does not reduce to the W-recursor at the constructor"),
        }
    }

    /// The ι rules for the unary recursive shape — `N.rec`.
    ///
    /// [`derived::wnat_rec`] supplies both, and neither is unconditional:
    ///
    /// ```text
    /// HYP := z ∈ N-target ∧ s ∈ fs(N, fs(T,T))
    /// ⊢ ∀z∀s∀T.    (HYP → app(nrec(z,s,T), ⟨inl •,∅⟩) = z)
    /// ⊢ ∀z∀s∀T∀n. ((HYP ∧ n ∈ N) → app(nrec(z,s,T), ⟨inr •,{⟨•,n⟩}⟩)
    ///                                 = app(app(s,n), app(nrec(z,s,T), n)))
    /// ```
    ///
    /// `HYP` is Lean's own typing of the two minor premises and nothing more, so
    /// it is supplied here rather than assumed: `⟦z⟧ ∈ T` **is** the level-2
    /// domain obligation the nest already paid for, and `⟦s⟧ ∈ fs(N,fs(T,T))` is
    /// the level-3 one asked at the beta-reduced kernel term rather than at the
    /// dependent product `∀n, C n → C (succ n)`, which `has_type` cannot match.
    ///
    /// `T` is `doms[1]` — the motive's value at `N.zero` **as the nest computed
    /// it**, not a term rebuilt here. Rebuilding it would give two terms that
    /// are equal only after a beta step, and then the two sides of the equation
    /// would not share their assumptions and the certificate would not compose.
    ///
    /// The `succ` rule's right-hand side mentions `nrec` **again** — the live
    /// recursive call, which no `Bool` equation could exercise. The reduct
    /// spells that call as `⟦N.rec C z s n⟧`, the curried nest at the field, so
    /// the last step here contracts that nest once more and rewrites the call
    /// into the shape the reduct uses.
    #[allow(clippy::too_many_arguments)]
    fn fire_nat(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        nr: &NatRecursor,
        nest: &RecNest,
        cfun: ExprPtr<'t>,
        args: &[ExprPtr<'t>],
        ta: &[Term],
        doms: &[Term],
        obligations: &[(Thm, Vec<Formula>)],
        idx: usize,
        fields: &[ExprPtr<'t>],
    ) -> Result<CondEq, &'static str> {
        let ap = self.pre.ap.clone();
        let app = ap.app;
        let major = args.len() - 1;
        let inds = nr.inds.clone();
        let nat_ty = inds.nat.ty.clone();
        let (z, s, t_target) = (ta[1].clone(), ta[2].clone(), doms[1].clone());
        let nrec = nr.nrec(&z, &s, &t_target);

        // `⊢ ⟦N⟧ = W(1+1,B,U(1+1))`. The major premise's domain *is* `⟦N⟧`, so
        // the equation is looked up rather than reconstructed, and checked.
        let Some(n_ax) = self.abbrev_defs.get(&doms[major]).cloned() else {
            return Err("iota: the inductive has no defining equation")
        };
        if n_ax.concl().as_eq() != Some((doms[major].clone(), nat_ty.clone())) {
            return Err("iota: the major premise's domain is not this inductive")
        }

        // ── `HYP`, from the recursor's own domain obligations ────────────────
        let (hz, hz_hyps) = obligations[1].clone();
        let fs = self.pre.fs_sym();
        let inner = Term::apply(fs, vec![t_target.clone(), t_target.clone()]);
        let shown = Term::apply(fs, vec![doms[major].clone(), inner.clone()]);
        let Some((hs, hs_hyps)) = self.mem_obligation(ctx, args[2], &s, &shown) else {
            return Err("iota: the succ minor premise has no typing to rest on")
        };
        let (s_c, inner_c) = (s.clone(), inner.clone());
        let Some(hs) = self.mem_along(&hs, &hs_hyps, &n_ax, |w| {
            Formula::mem(s_c.clone(), Term::apply(fs, vec![w, inner_c.clone()]))
        }) else {
            return Err("iota: transporting the succ minor's typing failed")
        };

        let mut hyps = merge_hyps(&hz_hyps, &hs_hyps);
        let premise = derived::wnat_rec::premise(&inds.wt.sums, &inds.nat, &z, &s, &t_target);

        // ── The constructor, and with it which rule fires ────────────────────
        let (ctor_eq, rule, extra) = match idx {
            0 => {
                // `⟦N.zero⟧ = ⟨inl •,∅⟩`, one Leibniz step.
                let Some(def) = self.abbrev_defs.get(&ta[major]).cloned() else {
                    return Err("iota: the constructor has no defining equation")
                };
                let Some(def) = CondEq::plain(def) else {
                    return Err("iota: the constructor's defining equation is not an equation")
                };
                let Some(rule) = derived::inst_all(
                    &nr.nr.iota_zero,
                    &[z.clone(), s.clone(), t_target.clone()],
                ) else {
                    return Err("iota: instantiating the zero computation rule failed")
                };
                (def, rule, None)
            }
            _ => {
                // `⟦N.succ n⟧ = ⟨inr •,{⟨•,⟦n⟧}⟩⟩`: unfold the constructor's
                // graph, beta-reduce it at `⟦n⟧`, unfold the abbreviation the
                // result is stated at.
                if fields.len() != 1 {
                    return Err("iota: the successor constructor has the wrong arity")
                }
                let tn = self.interp(ctx, fields[0]);
                let Some((hn, hn_hyps)) = self.mem_obligation(ctx, fields[0], &tn, &doms[major])
                else {
                    return Err("iota: the constructor's field has no typing to rest on")
                };
                let tn_c = tn.clone();
                let Some(hn_t) = self.mem_along(&hn, &hn_hyps, &n_ax, |w| {
                    Formula::mem(tn_c.clone(), w)
                }) else {
                    return Err("iota: transporting the field's typing failed")
                };

                let succ_t = self.interp(ctx, cfun);
                let Some(succ_ax) = self.abbrev_defs.get(&succ_t).cloned() else {
                    return Err("iota: the constructor has no defining equation")
                };
                let Some(succ_ax) = CondEq::plain(succ_ax) else {
                    return Err("iota: the constructor's defining equation is not an equation")
                };
                let Some(step1) = self.ceq_congr(app, &[succ_ax, CondEq::refl(tn.clone())]) else {
                    return Err("iota: congruence at the constructor's field refused")
                };
                let Some(sb) = derived::inst_all(&inds.nat.succ_beta, &[tn.clone()]) else {
                    return Err("iota: instantiating the constructor's beta rule failed")
                };
                let hn_h = conj_of(&hn_hyps);
                let Some(step2) = u_mp(&u_a1i(&sb, hn_h.as_ref()), &hn_t, hn_h.as_ref()) else {
                    return Err("iota: discharging the field's typing failed")
                };
                let Some(step2) = CondEq::new(step2, hn_hyps.clone()) else {
                    return Err("iota: the constructor's beta rule does not have the assumed shape")
                };
                let Some(sc) = derived::inst_all(&inds.nat.sc_ax, &[tn.clone()]) else {
                    return Err("iota: instantiating the successor abbreviation failed")
                };
                let Some(sc) = CondEq::plain(sc) else {
                    return Err("iota: the successor abbreviation is not an equation")
                };
                let Some(a) = self.ceq_trans(&step1, &step2) else {
                    return Err("iota: chaining the constructor's beta rule failed")
                };
                let Some(def) = self.ceq_trans(&a, &sc) else {
                    return Err("iota: chaining the successor abbreviation failed")
                };
                let Some(rule) = derived::inst_all(
                    &nr.nr.iota_succ,
                    &[z.clone(), s.clone(), t_target.clone(), tn.clone()],
                ) else {
                    return Err("iota: instantiating the succ computation rule failed")
                };
                hyps = merge_hyps(&hyps, &hn_hyps);
                (def, rule, Some((tn, hn_t, hn_hyps)))
            }
        };

        // ── `⊢ conj(hyps) → HYP`, and with it the rule's own antecedent ──────
        let h = conj_of(&hyps);
        let (Some(hz), Some(hs)) =
            (reassume(&hz, &hz_hyps, &hyps), reassume(&hs, &hs_hyps, &hyps))
        else {
            return Err("iota: restating the minor premises' typings failed")
        };
        let Some(mut ante) = u_and_intro(&hz, &hs, h.as_ref()) else {
            return Err("iota: assembling the recursor's hypothesis failed")
        };
        let mut want = premise;
        if let Some((_, hn_t, hn_hyps)) = &extra {
            let Some(hn_t) = reassume(hn_t, hn_hyps, &hyps) else {
                return Err("iota: restating the field's typing failed")
            };
            let Some(both) = u_and_intro(&ante, &hn_t, h.as_ref()) else {
                return Err("iota: assembling the successor's hypothesis failed")
            };
            let tn = extra.as_ref().map(|(t, _, _)| t.clone()).unwrap();
            ante = both;
            want = Formula::and(want, Formula::mem(tn, nat_ty));
        }
        if u_concl(&ante, h.as_ref()) != Some(want) {
            return Err("iota: the assembled hypothesis is not the one the rule asks for")
        }
        let Some(fired) = u_syl(&ante, &rule, h.as_ref()) else {
            return Err("iota: discharging the computation rule's hypothesis failed")
        };
        let Some(fired) = CondEq::new(fired, hyps) else {
            return Err("iota: the computation rule does not have the assumed shape")
        };

        // ── `app(nrec, ⟦cᵢ …⟧) = app(nrec, ⟨…⟩)`, then the rule ──────────────
        let Some(at_ctor) = self.ceq_congr(app, &[CondEq::refl(nrec.clone()), ctor_eq]) else {
            return Err("iota: congruence at the constructor refused")
        };
        let Some(mut acc) = self.ceq_trans(&at_ctor, &fired) else {
            return Err("iota: the nest does not reduce to the W-recursor at the constructor")
        };

        // ── The live recursive call, spelled the way the reduct spells it ────
        if let Some((tn, _, _)) = extra {
            let mut rec_args: Vec<ExprPtr<'t>> = args[..major].to_vec();
            rec_args.push(fields[0]);
            let mut rec_ta: Vec<Term> = ta[..major].to_vec();
            rec_ta.push(tn.clone());
            let (call, _) = self.nest_chain(ctx, nest, &rec_args, &rec_ta, doms)?;
            let Some(back) = self.ceq_symm(&call) else {
                return Err("iota: reversing the recursive call's contraction failed")
            };
            let head = ap.apply(s.clone(), tn);
            let Some(fixup) = self.ceq_congr(app, &[CondEq::refl(head), back]) else {
                return Err("iota: congruence at the recursive call refused")
            };
            let Some(t) = self.ceq_trans(&acc, &fixup) else {
                return Err("iota: rewriting the recursive call failed")
            };
            acc = t;
        }
        Ok(acc)
    }

    /// Move a derived membership along a **conditional** defining equation.
    ///
    /// [`Self::mem_along`] with the equation itself resting on assumptions,
    /// which is what the parameter forces: `⟦List α⟧` is `app(⟦List.{u}⟧, ⟦α⟧)`
    /// and so is a *redex*, whose contraction to `lt(α)` holds only for an `α`
    /// in the graph's domain. That premise is `⟦α⟧ ∈ ⟦Type u⟧`, the binder's own
    /// assumption, so it is carried rather than discharged — and the two lists
    /// are merged, so the result says exactly what it rests on.
    fn mem_along_c(
        &mut self,
        thm: &Thm,
        hyps: &[Formula],
        eq: &Thm,
        eq_hyps: &[Formula],
        phi: impl Fn(Term) -> Formula,
    ) -> Option<(Thm, Vec<Formula>)> {
        let out_hyps = merge_hyps(hyps, eq_hyps);
        let h = conj_of(&out_hyps);
        let eq_m = reassume(eq, eq_hyps, &out_hyps)?;
        let thm_m = reassume(thm, hyps, &out_hyps)?;
        let (a, b) = u_as_eq(&eq_m, h.as_ref())?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(a, b, w, phi(Term::var(w)));
        let step = u_syl(&eq_m, &leib, h.as_ref())?;
        Some((u_mp(&step, &thm_m, h.as_ref())?, out_hyps))
    }

    /// **The general ι rule** — `WIRING-DESIGN.md` §6.4, at `T`-policy 1 **and
    /// 2**.
    ///
    /// [`derived::inductive::GenRecursor`] supplies (S4) per constructor:
    ///
    /// ```text
    /// ⊢ ∀p⃗ ∀s⃗ ∀T ∀y⃗ ∀t⃗. ((HYP ∧ Hᵢ^ctor) →
    ///      app(grec(p⃗,s⃗,T), ctorᵢ(y⃗,t⃗))
    ///        = sᵢ ⟪y⃗,t⃗ in declared order⟫ app(grec,t₀) … )
    /// ```
    ///
    /// Six things have to be produced at the use site.
    ///
    /// *The parameters.* `p⃗` is `ta[..np]`, and the same `p⃗` has to be the one
    /// the **major premise's constructor** was applied to — checked, because
    /// `Hᵢ^ctor` is stated at the constructor's instantiation while the rule
    /// asks for it at the recursor's, and a mismatch would be two true theorems
    /// about different sets. The raw carrier is `carrier_at` at `p⃗`, not
    /// `ind.wty`, which is stated over the *declaration's* parameter variables
    /// and cannot be substituted — the kernel has no term-level substitution.
    /// Same reason a plain field's domain comes from `βⱼ`'s instantiated
    /// defining equation rather than from [`GenInd::beta_bodies`].
    ///
    /// *The target.* `T` is [`Self::t_policy`] at the domains **this call**
    /// walked off the recursor's type, never a term rebuilt here. The nest's
    /// bottom was built from the same policy at the nest's own locals, and the
    /// join at the end is what checks the two agree: a mismatch is a gap.
    ///
    /// *The constructor.* `⟦cᵢ f₀ … ⟧` is a Lean spine, not the carrier's
    /// `ctorᵢ(y⃗,t⃗)`. [`GenCtorBridge`] holds the two theorems that relate them
    /// — the spine equation and `Hᵢ^ctor` — both under one antecedent, the
    /// fields' memberships at the nest's own domains, so that discharging it
    /// once serves both and the two sides of the equation rest on the same
    /// assumptions. A **field-free constructor of a parameterless
    /// declaration** has neither: its interpretation *is* an abbreviation of
    /// the carrier's term and its `Hᵢ^ctor` is absent (the `Ctx(None)`
    /// discipline), which is the whole of the policy-1 case. At `np > 0` even a
    /// field-free constructor is a nest — `List.nil α` is a spine — so it has a
    /// bridge, whose `mem` half is `None` exactly when `Hᵢ^ctor` is.
    ///
    /// *`HYP`, pointwise.* [`derived::inductive::premise`] quantifies a minor's
    /// field slots over `βⱼ(y⃗)` and its recursive slots over the **raw** `W`,
    /// which is what makes it match `step_typed`'s junk quantification. A use
    /// site has only the minor's curried `fs`-membership at the beta-reduced
    /// Lean type, so [`Self::gen_minor_typed`] bridges the two.
    ///
    /// *The live recursive calls.* The rule's right-hand side spells them
    /// `app(grec, tⱼ)` and the reduct spells them `⟦T.rec C s⃗ tⱼ⟧`, so the nest
    /// is contracted once more per recursive field and the call rewritten —
    /// [`Self::fire_nat`]'s last step, looped over `mᵢ`.
    ///
    /// Everything is checked against the claim before it is used: the rule's
    /// antecedent against the `HYP` assembled here, its conclusion against the
    /// equation being fired, and the constructor's bridge against the term the
    /// nest's bottom applies.
    #[allow(clippy::too_many_arguments)]
    fn fire_general(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        gr: &GenRec,
        tn: &GenTyNest,
        nest: &RecNest,
        cfun: ExprPtr<'t>,
        args: &[ExprPtr<'t>],
        ta: &[Term],
        doms: &[Term],
        obligations: &[(Thm, Vec<Formula>)],
        idx: usize,
        cparams: &[ExprPtr<'t>],
        fields: &[ExprPtr<'t>],
    ) -> Result<CondEq, &'static str> {
        let ap = self.pre.ap.clone();
        let app = ap.app;
        let major = args.len() - 1;
        let ind = gr.gi.ind.clone();
        let n = ind.spec.ctors.len();
        let np = gr.gi.param_vars.len();
        if idx >= n {
            return Err("iota: the constructor is not one this backend computes")
        }
        // Layout: `np` parameters, the motive, `n` minors, the major premise.
        if ta.len() != np + n + 2 || doms.len() != np + n + 2 || obligations.len() != np + n + 2 {
            return Err("iota: the general recursor is not applied to its own arguments")
        }
        let ps: Vec<Term> = ta[..np].to_vec();
        let minors: Vec<Term> = ta[np + 1..np + 1 + n].to_vec();
        let mach = match self.machine() {
            Some(m) => m,
            None => return Err("iota: the general apparatus is unavailable"),
        };
        let sums = mach.borrow().wt.sums.clone();
        let nullary = |c: &CtorSpec| c.args.is_empty() && c.recs == 0;
        let fin_target = ind.spec.ctors.iter().all(nullary);

        let Some(t) = self.t_policy(&gr.gi, doms, &minors, np) else {
            return Err("iota: the target policy has no target to offer here")
        };
        let grec = {
            let m = mach.borrow();
            match gr.gr.rec_of(&m, &ind, &gr.core.r, &ps, &minors, &t) {
                Some(g) => g,
                None => return Err("iota: the general recursor term could not be built"),
            }
        };
        // `W(A(p⃗),B(p⃗),U)` at *these* parameters. The kernel has no term-level
        // substitution, so this is rebuilt by `carrier_at` rather than taken
        // from `ind.wty` — and checked below against what `ind.ty_ax` says.
        let w_at = {
            let m = mach.borrow();
            match derived::inductive::carrier_at(&m, &ind, &ps) {
                Some((_, _, _, w)) => w,
                None => return Err("iota: the carrier at these parameters could not be built"),
            }
        };

        // ── `⊢ ⟦T⟧ = W` and back: the carrier under two names ────────────────
        //
        // `HYP` types a recursive slot at the raw `W`; every Lean-facing
        // obligation is at the Lean spine `app-spine(⟦T⟧, p⃗)`. At `np = 0` the
        // spine is the abbreviation and the bridge is its defining equation; at
        // `np > 0` it is [`GenTyNest`]'s beta chain, conditional on the
        // parameters' own typings — which are exactly the obligations
        // `nest_chain` has already paid at levels `0 ‥ np`, so they are taken
        // from there rather than asked again.
        let ty_t = doms[major].clone();
        let ind_body = ind.ty_of(ps.clone());
        let (ty_ax, ty_hyps) = self.gen_ty_bridge(tn, &ps, ta, doms, obligations, &ty_t, &ind_body)?;
        let Some(w_ax) = derived::inst_all(&ind.ty_ax, &ps) else {
            return Err("iota: instantiating the carrier's defining equation failed")
        };
        if w_ax.concl().as_eq() != Some((ind_body.clone(), w_at.clone())) {
            return Err("iota: the carrier's defining equation is not about this W-type")
        }
        let th = conj_of(&ty_hyps);
        let Some(ty_w) = self.u_eq_trans(&ty_ax, &u_a1i(&w_ax, th.as_ref()), th.as_ref()) else {
            return Err("iota: chaining the carrier's two defining equations failed")
        };
        if u_concl(&ty_w, th.as_ref()) != Some(Formula::eq(ty_t.clone(), w_at.clone())) {
            return Err("iota: the carrier's defining equation is not about this W-type")
        }
        let Some(w_ty) = self.u_eq_symm(&ty_w, th.as_ref()) else {
            return Err("iota: reversing the carrier's defining equation failed")
        };
        let w_ty = (w_ty, ty_hyps);

        // ── `HYP`: one pointwise `minor_typedᵢ` per constructor ──────────────
        let mut hyp_parts: Vec<(Thm, Vec<Formula>)> = Vec::with_capacity(n);
        for i in 0..n {
            hyp_parts.push(self.gen_minor_typed(
                ctx,
                &gr.gi,
                args,
                doms,
                obligations,
                &ps,
                &w_at,
                &minors,
                &t,
                &ty_t,
                &w_ty,
                fin_target,
                i,
            )?);
        }
        let want_hyp = {
            let mut env = self.env_mut();
            match derived::inductive::premise::hyp_of(
                &mut env,
                &sums,
                &ind.spec.ctors,
                &ps,
                &w_at,
                &minors,
                &t,
            ) {
                Some(h) => h,
                None => return Err("iota: the general recursor has no minor premises"),
            }
        };

        // ── The constructor: its spine equation, and its own typings ─────────
        let order = ind.spec.ctors[idx].order.clone();
        let (m_rec, k_plain) = (ind.spec.ctors[idx].recs, ind.spec.ctors[idx].args.len());
        if fields.len() != k_plain + m_rec {
            return Err("iota: the constructor is not applied to its own fields")
        }
        let mut ctor_hyps: Vec<Formula> = Vec::new();
        let (ctor_eq, ctor_h, ys_c, ts_c) = if np == 0 && fields.is_empty() {
            // Nullary at a parameterless declaration: `⟦cᵢ⟧` abbreviates the
            // carrier's term outright, and the rule carries no `Hᵢ^ctor` at all.
            let ctor_term = {
                let m = mach.borrow();
                match ind.ctor_term(&m, idx, &[], &[]) {
                    Some(c) => c,
                    None => return Err("iota: the constructor term could not be built"),
                }
            };
            let Some(def) = self.abbrev_defs.get(&ta[major]).cloned() else {
                return Err("iota: the constructor has no defining equation")
            };
            if def.concl().as_eq() != Some((ta[major].clone(), ctor_term)) {
                return Err("iota: the major premise is not this constructor")
            }
            let Some(def) = CondEq::plain(def) else {
                return Err("iota: the constructor's defining equation is not an equation")
            };
            (def, None, Vec::new(), Vec::new())
        } else {
            let Expr::Const { name: cname, levels: clevels, .. } = ctx.read_expr(cfun) else {
                return Err("iota: the major premise is not a constructor")
            };
            // The bridge is a by-product of building the constructor's nest, so
            // the constant has to have been interpreted at least once. `interp`
            // is cached, and `ta[major]` has already forced it; this is the line
            // that says so rather than relying on it.
            let _ = self.interp(ctx, cfun);
            let clv = self.interp_levels(ctx, clevels);
            let Some(br) = self.gen_ctor_bridges.get(&(cname, clv)).cloned() else {
                return Err("iota: the constructor has no bridge to the carrier's term")
            };
            // `mem` is present exactly when the constructor has fields — the
            // `Ctx(None)` discipline on both sides — and the bridge's own
            // parameter count must be this declaration's.
            if br.vars.len() != np + fields.len()
                || br.order != order
                || br.np != np
                || br.mem.is_some() != !fields.is_empty()
            {
                return Err("iota: the constructor's bridge is about another constructor")
            }
            if cparams.len() != np {
                return Err("iota: the major premise is not applied to the declaration's parameters")
            }
            // The spine is `⟦cᵢ p⃗ f⃗⟧`, parameters first, so the bridge is
            // instantiated at both — and the parameters must be the *recursor's*,
            // or `Hᵢ^ctor` would be stated about a different instantiation than
            // the ι rule asks for.
            let mut tf: Vec<Term> = cparams.iter().map(|p| self.interp(ctx, *p)).collect();
            if tf != ps {
                return Err("iota: the constructor's parameters are not the recursor's")
            }
            tf.extend(fields.iter().map(|f| self.interp(ctx, *f)).collect::<Vec<_>>());
            let cargs: Vec<ExprPtr<'t>> =
                cparams.iter().chain(fields.iter()).copied().collect();
            let Some(spine_inst) = derived::inst_all(&br.spine, &tf) else {
                return Err("iota: instantiating the constructor's bridge failed")
            };
            let mem_inst = match &br.mem {
                None => None,
                Some(m) => match derived::inst_all(m, &tf) {
                    Some(m) => Some(m),
                    None => return Err("iota: instantiating the constructor's bridge failed"),
                },
            };
            let Some((ante, spine_eq)) = spine_inst.concl().as_imp() else {
                return Err("iota: the constructor's bridge is not conditional")
            };
            if let Some(mi) = &mem_inst {
                match mi.concl().as_imp() {
                    Some((ante2, _)) if ante2 == ante => {}
                    _ => {
                        return Err(
                            "iota: the constructor's two bridges do not share an antecedent",
                        )
                    }
                }
            }
            if spine_eq.as_eq().map(|(l, _)| l) != Some(ta[major].clone()) {
                return Err("iota: the constructor's bridge is not about this spine")
            }

            // Discharge the shared antecedent, atom by atom, from the arguments'
            // own typing obligations — read off the instantiated formula rather
            // than rebuilt, so a dependent field's type is whatever the bridge
            // says it is.
            let mut atoms: Vec<Formula> = Vec::with_capacity(cargs.len());
            let mut cur = ante.clone();
            for _ in 1..cargs.len() {
                let Some((a, rest)) = as_and(&cur) else {
                    return Err("iota: the constructor's antecedent is not a conjunction")
                };
                atoms.push(a);
                cur = rest;
            }
            atoms.push(cur);
            let mut parts: Vec<(Thm, Vec<Formula>)> = Vec::with_capacity(cargs.len());
            for (f, atom) in atoms.iter().enumerate() {
                let Some((subj, dom)) = atom.as_mem() else {
                    return Err("iota: the constructor's antecedent is not a membership")
                };
                if subj != tf[f] {
                    return Err("iota: the constructor's antecedent is about another field")
                }
                let Some(o) = self.mem_obligation(ctx, cargs[f], &tf[f], &dom) else {
                    return Err("iota: a constructor field has no typing to rest on")
                };
                ctor_hyps = merge_hyps(&ctor_hyps, &o.1);
                parts.push(o);
            }
            let ch = conj_of(&ctor_hyps);
            let mut restated: Vec<Thm> = Vec::with_capacity(parts.len());
            for (thm, hs) in &parts {
                let Some(r) = reassume(thm, hs, &ctor_hyps) else {
                    return Err("iota: restating a constructor field's typing failed")
                };
                restated.push(r);
            }
            let mut acc = restated.pop().expect("a nest with a level has an argument");
            while let Some(p) = restated.pop() {
                let Some(both) = u_and_intro(&p, &acc, ch.as_ref()) else {
                    return Err("iota: assembling the constructor's premises failed")
                };
                acc = both;
            }
            if u_concl(&acc, ch.as_ref()) != Some(ante) {
                return Err("iota: the constructor's assembled premise is not the one it asks for")
            }
            let Some(eq) = u_syl(&acc, &spine_inst, ch.as_ref()) else {
                return Err("iota: discharging the constructor's bridge failed")
            };
            let hc = match &mem_inst {
                None => None,
                Some(mi) => match u_syl(&acc, mi, ch.as_ref()) {
                    Some(h) => Some(h),
                    None => return Err("iota: discharging the constructor's bridge failed"),
                },
            };
            let Some(eq) = CondEq::new(eq, ctor_hyps.clone()) else {
                return Err("iota: the constructor's bridge does not have the assumed shape")
            };
            let (mut ys, mut ts) = (Vec::new(), Vec::new());
            for (f, slot) in order.iter().enumerate() {
                match slot {
                    Slot::Plain => ys.push(tf[np + f].clone()),
                    Slot::Rec => ts.push(tf[np + f].clone()),
                }
            }
            (eq, hc, ys, ts)
        };

        // ── (S4) at these terms, and the claim it must make ──────────────────
        let mut at: Vec<Term> = ps.clone();
        at.extend(minors.iter().cloned());
        at.push(t.clone());
        at.extend(ys_c.iter().cloned());
        at.extend(ts_c.iter().cloned());
        let Some(rule) = derived::inst_all(&gr.gr.iota[idx], &at) else {
            return Err("iota: instantiating the general computation rule failed")
        };
        let ctor_term = {
            let m = mach.borrow();
            match ind.ctor_term(&m, idx, &ys_c, &ts_c) {
                Some(c) => c,
                None => return Err("iota: the constructor term could not be built"),
            }
        };
        let ihs: Vec<Term> = ts_c.iter().map(|x| ap.apply(grec.clone(), x.clone())).collect();
        let rhs = derived::inductive::applied_minor(
            &ap,
            &order,
            &minors[idx],
            &ys_c,
            &ts_c,
            &ihs,
        );
        let full_hyp = match &ctor_h {
            None => want_hyp.clone(),
            Some(hc) => {
                let Some(hcf) = u_concl(hc, conj_of(&ctor_hyps).as_ref()) else {
                    return Err("iota: the constructor's typings have no conclusion")
                };
                Formula::and(want_hyp.clone(), hcf)
            }
        };
        let want = Formula::imp(
            full_hyp.clone(),
            Formula::eq(ap.apply(grec.clone(), ctor_term), rhs),
        );
        if *rule.concl() != want {
            return Err("iota: the general computation rule is not about this instance")
        }

        // ── The antecedent, from everything above, on one hypothesis list ────
        let mut hyps: Vec<Formula> = Vec::new();
        for (_, hs) in &hyp_parts {
            hyps = merge_hyps(&hyps, hs);
        }
        hyps = merge_hyps(&hyps, &ctor_hyps);
        let h = conj_of(&hyps);
        let mut restated: Vec<Thm> = Vec::with_capacity(n);
        for (thm, hs) in &hyp_parts {
            let Some(r) = reassume(thm, hs, &hyps) else {
                return Err("iota: restating a minor premise's typing failed")
            };
            restated.push(r);
        }
        let mut ante = restated.pop().expect("n >= 1");
        while let Some(p) = restated.pop() {
            let Some(both) = u_and_intro(&p, &ante, h.as_ref()) else {
                return Err("iota: assembling the recursor's hypothesis failed")
            };
            ante = both;
        }
        if let Some(hc) = &ctor_h {
            let Some(hc) = reassume(hc, &ctor_hyps, &hyps) else {
                return Err("iota: restating the constructor's typings failed")
            };
            let Some(both) = u_and_intro(&ante, &hc, h.as_ref()) else {
                return Err("iota: assembling the constructor's hypothesis failed")
            };
            ante = both;
        }
        if u_concl(&ante, h.as_ref()) != Some(full_hyp) {
            return Err("iota: the assembled hypothesis is not the one the rule asks for")
        }
        let Some(fired) = u_syl(&ante, &rule, h.as_ref()) else {
            return Err("iota: discharging the general computation rule's hypothesis failed")
        };
        let Some(fired) = CondEq::new(fired, hyps) else {
            return Err("iota: the general computation rule does not have the assumed shape")
        };

        // ── `app(grec, ⟦cᵢ f⃗⟧) = app(grec, ctorᵢ(y⃗,t⃗))`, then the rule ──────
        let Some(at_ctor) = self.ceq_congr(app, &[CondEq::refl(grec.clone()), ctor_eq]) else {
            return Err("iota: congruence at the constructor refused")
        };
        let Some(mut acc) = self.ceq_trans(&at_ctor, &fired) else {
            return Err("iota: the nest does not reduce to the W-recursor at the constructor")
        };

        // ── The live recursive calls, spelled the way the reduct spells them ─
        if m_rec > 0 {
            let base =
                derived::inductive::applied_minor(&ap, &order, &minors[idx], &ys_c, &ts_c, &[]);
            let mut cur = CondEq::refl(base);
            let mut ri = 0usize;
            for (f, slot) in order.iter().enumerate() {
                if matches!(slot, Slot::Plain) {
                    continue
                }
                let mut rec_args: Vec<ExprPtr<'t>> = args[..major].to_vec();
                rec_args.push(fields[f]);
                let mut rec_ta: Vec<Term> = ta[..major].to_vec();
                rec_ta.push(ts_c[ri].clone());
                let (call, _) = self.nest_chain(ctx, nest, &rec_args, &rec_ta, doms)?;
                let Some(back) = self.ceq_symm(&call) else {
                    return Err("iota: reversing a recursive call's contraction failed")
                };
                let Some(next) = self.ceq_congr(app, &[cur, back]) else {
                    return Err("iota: congruence at a recursive call refused")
                };
                cur = next;
                ri += 1;
            }
            let Some(joined) = self.ceq_trans(&acc, &cur) else {
                return Err("iota: rewriting the recursive calls failed")
            };
            acc = joined;
        }
        GEN_IOTAS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(acc)
    }

    /// `⊢ H → (⟦T p⃗⟧ = ind(p⃗))` at the ι site's own parameters, with `H` the
    /// assumptions the parameters' typings rested on.
    ///
    /// At `np = 0` this is the type former's defining equation and `H` is empty
    /// — the parameterless path, unchanged. At `np > 0` it is [`GenTyNest`]'s
    /// beta chain, whose antecedent is the parameters' memberships; those are
    /// discharged from `obligations[0 ‥ np]`, the typings [`Self::nest_chain`]
    /// has already paid for at the nest's own levels. Asking again would both
    /// double-count the ledger and risk asking at a different term.
    ///
    /// Every atom of the antecedent is checked to be the membership this call's
    /// own domain walk produced: a parameter whose domain is not the one the
    /// type former was built over is a decline, because the equation would then
    /// be about a different set.
    #[allow(clippy::too_many_arguments)]
    fn gen_ty_bridge(
        &mut self,
        tn: &GenTyNest,
        ps: &[Term],
        ta: &[Term],
        doms: &[Term],
        obligations: &[(Thm, Vec<Formula>)],
        ty_t: &Term,
        ind_body: &Term,
    ) -> Result<(Thm, Vec<Formula>), &'static str> {
        let np = ps.len();
        if tn.vars.len() != np {
            return Err("iota: the type former is not the one this recursor eliminates")
        }
        let Some(inst) = derived::inst_all(&tn.spine_eq_all, ps) else {
            return Err("iota: instantiating the type former's bridge failed")
        };
        let want = Formula::eq(ty_t.clone(), ind_body.clone());
        if np == 0 {
            if *inst.concl() != want {
                return Err("iota: the major premise's domain is not this inductive")
            }
            return Ok((inst, Vec::new()))
        }
        let Some((ante, concl)) = inst.concl().as_imp() else {
            return Err("iota: the type former's bridge is not conditional")
        };
        if concl != want {
            return Err("iota: the major premise's domain is not this inductive")
        }
        // The antecedent is `derived::conj_of`'s **right**-nested bundle, so it
        // is peeled from the left, one atom at a time.
        let mut atoms: Vec<Formula> = Vec::with_capacity(np);
        let mut cur = ante.clone();
        for _ in 1..np {
            let Some((a, rest)) = as_and(&cur) else {
                return Err("iota: the type former's antecedent is not a conjunction")
            };
            atoms.push(a);
            cur = rest;
        }
        atoms.push(cur);
        let mut hyps: Vec<Formula> = Vec::new();
        let mut parts: Vec<(Thm, Vec<Formula>)> = Vec::with_capacity(np);
        for (k, atom) in atoms.iter().enumerate() {
            if *atom != Formula::mem(ta[k].clone(), doms[k].clone()) {
                return Err("iota: a parameter's domain is not the type former's")
            }
            hyps = merge_hyps(&hyps, &obligations[k].1);
            parts.push(obligations[k].clone());
        }
        let h = conj_of(&hyps);
        let mut restated: Vec<Thm> = Vec::with_capacity(np);
        for (thm, hs) in &parts {
            let Some(r) = reassume(thm, hs, &hyps) else {
                return Err("iota: restating a parameter's typing failed")
            };
            restated.push(r);
        }
        let mut acc = restated.pop().expect("np >= 1");
        while let Some(p) = restated.pop() {
            let Some(both) = u_and_intro(&p, &acc, h.as_ref()) else {
                return Err("iota: assembling the parameters' typings failed")
            };
            acc = both;
        }
        if u_concl(&acc, h.as_ref()) != Some(ante) {
            return Err("iota: the assembled parameter typings are not the ones asked for")
        }
        let Some(eq) = u_mp(&u_a1i(&inst, h.as_ref()), &acc, h.as_ref()) else {
            return Err("iota: discharging the type former's bridge failed")
        };
        Ok((eq, hyps))
    }

    /// `⊢ H → minor_typedᵢ` — one conjunct of the general recursor's `HYP`,
    /// **pointwise**, from the minor premise's own typing.
    ///
    /// [`derived::inductive::premise`] states
    ///
    /// ```text
    /// ∀y⃗ ∀t⃗ ∀v⃗. ((⋀ⱼ yⱼ ∈ βⱼ(y₀…y_{j−1}) ∧ ⋀ⱼ tⱼ ∈ W ∧ ⋀ⱼ vⱼ ∈ T)
    ///                → sᵢ ⟪mask over y⃗,t⃗⟫ v⃗ ∈ T)
    /// ```
    ///
    /// and a use site has the *curried* `fs`-membership at the beta-reduced
    /// Lean type — the same term [`Self::fire_nat`] asks for. Three moves close
    /// the distance, and each is guarded:
    ///
    /// * **the coordinates.** `βⱼ(y⃗)` is unfolded to the interpretation `⟦β⟧`
    ///   the nest's domain is stated at, and the raw `W` to the abbreviation
    ///   `⟦T⟧`, one Leibniz step each.
    /// * **`k + 2m` function applications.** The curried form implies the
    ///   pointwise one by that many instances of `funspace_app_mem`
    ///   ([`app_in_codomain`]), folded left over the mask order and then the
    ///   induction hypotheses — the order [`derived::inductive::applied_minor`]
    ///   applies them in, which is the one spelling the step value, `HYP` and
    ///   the ι rules all share.
    /// * **the quantifiers.** The derivation runs under `H_out ∧ H_pw` and is
    ///   curried apart at the end, so the escaping assumptions stay outside the
    ///   `∀` where they belong (`Thm::ax_dist`, whose side condition is exactly
    ///   "the assumption does not mention the bound variable").
    ///
    /// # What declines, and why it must
    ///
    /// A **dependent** plain field — `βⱼ`'s body mentioning an earlier field —
    /// has no iterated-`fs` type at all, so there is no curried form to start
    /// from. That is a counted gap with its own reason, not a silent decline:
    /// it is `RECURSOR-DESIGN.md` §5.1's dependent-motive escape arriving one
    /// level down, on the constructor's telescope rather than on the motive.
    /// The motive's own dependence surfaces differently — as a minor whose Lean
    /// type does not beta-reduce to the `fs` chain asked for here, so the
    /// obligation escapes rather than being discharged.
    ///
    /// A **nullary** constructor needs none of this: `minor_typedᵢ` is the bare
    /// `sᵢ ∈ T`. Under policy 1 that is `FinSet::mem`, free; under policy 2 at
    /// the constructor the target was read off, it is the obligation the nest
    /// has *already* paid, which is why it is taken from `obligations` rather
    /// than asked again.
    #[allow(clippy::too_many_arguments)]
    fn gen_minor_typed(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        gi: &GenInd,
        args: &[ExprPtr<'t>],
        doms: &[Term],
        obligations: &[(Thm, Vec<Formula>)],
        ps: &[Term],
        w_at: &Term,
        minors: &[Term],
        t: &Term,
        ty_t: &Term,
        w_ty: &(Thm, Vec<Formula>),
        fin_target: bool,
        i: usize,
    ) -> Result<(Thm, Vec<Formula>), &'static str> {
        let ap = self.pre.ap.clone();
        let ind = gi.ind.clone();
        let ctor = ind.spec.ctors[i].clone();
        let (k, m) = (ctor.args.len(), ctor.recs);
        let np = ps.len();
        let order = ctor.order.clone();
        let su = minors[i].clone();
        let Some(mach) = self.machine() else {
            return Err("iota: the general apparatus is unavailable")
        };
        let sums = mach.borrow().wt.sums.clone();

        // The statement to produce, in the derived layer's own spelling. Built
        // first; everything below is checked against it.
        let want = {
            let mut env = self.env_mut();
            derived::inductive::premise::minor_typed_at(
                &mut env, &sums, &ctor, ps, w_at, &su, t, &ind.rec_slot_domains(i),
            )
        };

        if k == 0 && m == 0 {
            let (thm, hyps) = if fin_target {
                let Some(mem) = mach.borrow().fin.mem(&sums, minors, i) else {
                    return Err("iota: a minor premise is not in the target it defines")
                };
                (mem, Vec::new())
            } else if doms[np + 1 + i] == *t {
                obligations[np + 1 + i].clone()
            } else {
                match self.mem_obligation(ctx, args[np + 1 + i], &su, t) {
                    Some(o) => o,
                    None => return Err("iota: a minor premise has no typing to rest on"),
                }
            };
            if u_concl(&thm, conj_of(&hyps).as_ref()) != Some(want) {
                return Err("iota: a nullary minor's typing is not the one HYP asks for")
            }
            return Ok((thm, hyps))
        }

        // ── The pointwise variables ──────────────────────────────────────────
        //
        // Minted before the chain, because at `np > 0` a plain field's domain is
        // read off `βⱼ`'s defining equation **instantiated at these very
        // variables**, and the equation's arguments are `p⃗` then `y₀…y_{j−1}`.
        let (yv, tv, vv) = {
            let mut env = self.env_mut();
            let yv: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
            let tv: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
            let vv: Vec<FreeVar> = (0..m).map(|_| env.fresh_var()).collect();
            (yv, tv, vv)
        };
        let ys: Vec<Term> = yv.iter().map(|v| Term::var(*v)).collect();
        let ts: Vec<Term> = tv.iter().map(|v| Term::var(*v)).collect();
        let vs: Vec<Term> = vv.iter().map(|v| Term::var(*v)).collect();

        // ── The curried shape the minor's Lean type beta-reduces to ──────────
        //
        // One domain per field in mask order, then one `T` per recursive field,
        // then `T`. A plain field contributes the interpretation of its Lean
        // type **at these parameters**; a recursive one the Lean spine
        // `⟦T p⃗⟧`, which is what the nest's own domain says and therefore what a
        // use site can produce.
        //
        // The parameters are why the body is taken from `βⱼ`'s instantiated
        // defining equation rather than from [`GenInd::beta_bodies`]: the stored
        // body is stated over the walk's *parameter variables*, and the kernel
        // has no term-level substitution, so at `np > 0` the two are different
        // terms and the one a use site can produce is the instantiated one. At
        // `np = 0` they coincide.
        let fs = self.pre.fs_sym();
        let mut chain: Vec<Term> = Vec::with_capacity(k + 2 * m);
        let mut beta_insts: Vec<Thm> = Vec::with_capacity(k);
        let mut plain_seen = 0usize;
        for slot in &order {
            match slot {
                Slot::Plain => {
                    let Some((bsym, bax)) = gi.betas[i].get(plain_seen) else {
                        return Err("iota: a plain field has no defining equation")
                    };
                    if *bsym != ctor.args[plain_seen] {
                        return Err("iota: a plain field's symbol is not the spec's")
                    }
                    let mut bat: Vec<Term> = ps.to_vec();
                    bat.extend(ys[..plain_seen].iter().cloned());
                    let Some(inst) = derived::inst_all(bax, &bat) else {
                        return Err("iota: instantiating a field type's definition failed")
                    };
                    let Some((lhs, body)) = inst.concl().as_eq() else {
                        return Err("iota: a field type's definition is not an equation")
                    };
                    if lhs != Term::apply(ctor.args[plain_seen], bat) {
                        return Err("iota: a field type's definition is not about this domain")
                    }
                    // A **dependent** field — its type mentioning an earlier one
                    // — has no iterated-`fs` type at all, so there is no curried
                    // form to start from. Counted, with its own reason.
                    if yv.iter().any(|v| body.occurs_free(*v)) {
                        return Err("iota: HYP undischargeable — dependent constructor field")
                    }
                    chain.push(body);
                    beta_insts.push(inst);
                    plain_seen += 1;
                }
                Slot::Rec => chain.push(ty_t.clone()),
            }
        }
        for _ in 0..m {
            chain.push(t.clone());
        }
        // `cods[j]` is what remains after `j` applications; `cods[0]` is the
        // membership asked of the minor.
        let mut cods: Vec<Term> = vec![t.clone(); chain.len() + 1];
        for j in (0..chain.len()).rev() {
            cods[j] = Term::apply(fs, vec![chain[j].clone(), cods[j + 1].clone()]);
        }
        let shown = cods[0].clone();
        let Some((hs, raw_hyps)) = self.mem_obligation(ctx, args[np + 1 + i], &su, &shown) else {
            return Err("iota: a minor premise has no typing to rest on")
        };
        // **The carrier bridge's own assumptions join the minor's.** At `np > 0`
        // the equation `⟦T p⃗⟧ = W` holds under the parameters' typings, which
        // may themselves rest on context locals; those have to travel with this
        // conjunct, or the `∀`-closure below would quantify over a variable an
        // undischarged assumption mentions. At `np = 0` the list is empty and
        // `out_hyps` is exactly what it was.
        //
        // Only when the constructor **has** a recursive field: the bridge is
        // used nowhere else, and dragging its assumptions in unconditionally
        // would let them escape from constructors that never needed them.
        let out_hyps = if m > 0 { merge_hyps(&raw_hyps, &w_ty.1) } else { raw_hyps.clone() };
        let Some(hs) = reassume(&hs, &raw_hyps, &out_hyps) else {
            return Err("iota: restating the minor premise's typing failed")
        };
        let w_ty_out = match m {
            0 => None,
            _ => match reassume(&w_ty.0, &w_ty.1, &out_hyps) {
                Some(w) => Some(w),
                None => return Err("iota: restating the carrier's defining equation failed"),
            },
        };
        // `mem_obligation` hands back a **vacuous** `⊢ H → H` when it could not
        // type the argument, so the conclusion has to be read rather than
        // assumed. Everything downstream would refuse it anyway — `hyp_and`
        // would build the wrong conjunction and `funspace_app_mem`'s antecedent
        // would not match — but the reason matters: this is where a **genuinely
        // dependent motive** lands. Its minor's Lean type does not beta-reduce
        // to an iterated `fs` at all, so no `has_type` rule can produce this
        // membership, and `RECURSOR-DESIGN.md` §7.3 asks for the escape to be
        // counted under its own name rather than as a nondescript failure.
        if u_concl(&hs, conj_of(&out_hyps).as_ref())
            != Some(Formula::mem(su.clone(), shown.clone()))
        {
            return Err("iota: HYP undischargeable — dependent motive")
        }

        // ── The pointwise antecedent ─────────────────────────────────────────
        let mut pw: Vec<Formula> = (0..k)
            .map(|j| {
                let mut a = ps.to_vec();
                a.extend(ys[..j].iter().cloned());
                Formula::mem(ys[j].clone(), Term::apply(ctor.args[j], a))
            })
            .collect();
        pw.extend(ts.iter().map(|x| Formula::mem(x.clone(), w_at.clone())));
        pw.extend(vs.iter().map(|x| Formula::mem(x.clone(), t.clone())));
        // **`derived::conj_of`, not this file's.** The two nest the opposite
        // way — the checker's assumption lists are left-nested, `derived`'s
        // hypothesis bundles right-nested — and `minor_typed` is stated with the
        // latter, so a left-nested `h_pw` would be a different formula from the
        // third atom on. `Lean.Name.str` has exactly three
        // (`y ∈ β`, `t ∈ W`, `v ∈ T`), so this is the first shape at which the
        // difference is visible at all.
        let Some(h_pw) = derived::conj_of(&pw) else {
            return Err("iota: a non-nullary minor has an empty pointwise antecedent")
        };
        // The escaping assumptions stay in the checker's own convention: they
        // are handed to `reassume` and the `u_*` family, which read them
        // left-nested.
        let h_out = conj_of(&out_hyps);
        let h_all = match &h_out {
            Some(o) => Formula::and(o.clone(), h_pw.clone()),
            None => h_pw.clone(),
        };
        let ha = Some(&h_all);

        // Everything below is stated under `h_all`; the two projections out of
        // it are the only places the two halves are distinguished.
        let left = |o: &Formula| derived::and_left(o.clone(), h_pw.clone());
        let Some(mut acc_thm) = (match &h_out {
            Some(o) => derived::syl(&left(o), &hs),
            None => Some(u_a1i(&hs, ha)),
        }) else {
            return Err("iota: restating the minor premise's typing failed")
        };
        // The carrier bridge, under `h_all` — conditional at `np > 0`, and one
        // weakening away from unconditional at `np = 0`.
        let w_ty_all = match &w_ty_out {
            None => None,
            Some(w) => match &h_out {
                Some(o) => derived::syl(&left(o), w),
                None => Some(u_a1i(w, ha)),
            },
        };
        if m > 0 && w_ty_all.is_none() {
            return Err("iota: restating the carrier's defining equation failed")
        }
        let mut atom_thms: Vec<Thm> = Vec::with_capacity(pw.len());
        for j in 0..pw.len() {
            let Some(p) = derived::conj_proj(&pw, j) else {
                return Err("iota: projecting the pointwise antecedent failed")
            };
            let carried = match &h_out {
                Some(o) => derived::syl(&derived::and_right(o.clone(), h_pw.clone()), &p),
                None => Some(p),
            };
            match carried {
                Some(c) => atom_thms.push(c),
                None => return Err("iota: carrying a pointwise assumption failed"),
            }
        }

        // ── The arguments, in application order, each typed at its domain ────
        let mut arg_terms: Vec<Term> = Vec::with_capacity(k + 2 * m);
        let mut arg_thms: Vec<Thm> = Vec::with_capacity(k + 2 * m);
        let (mut pi, mut ri) = (0usize, 0usize);
        for slot in &order {
            match slot {
                Slot::Plain => {
                    // `yⱼ ∈ βⱼ(p⃗, y₀…y_{j−1})` ↦ `yⱼ ∈ ⟦β⟧`, along `βⱼ`'s own
                    // defining equation at *these* terms — the very equation the
                    // chain above was built from, so the guard is that its
                    // right-hand side is still that domain.
                    let Some(inst) = beta_insts.get(pi) else {
                        return Err("iota: a plain field has no defining equation")
                    };
                    if inst.concl().as_eq().map(|(_, r)| r)
                        != Some(chain[arg_terms.len()].clone())
                    {
                        return Err("iota: a field type's definition is not about this domain")
                    }
                    let Some(c) = self.u_mem_along(&atom_thms[pi], inst, ha) else {
                        return Err("iota: unfolding a field type failed")
                    };
                    arg_terms.push(ys[pi].clone());
                    arg_thms.push(c);
                    pi += 1;
                }
                Slot::Rec => {
                    let Some(wa) = w_ty_all.clone() else {
                        return Err("iota: transporting a recursive slot's typing failed")
                    };
                    let Some(c) = self.uu_mem_along(&atom_thms[k + ri], &wa, ha) else {
                        return Err("iota: transporting a recursive slot's typing failed")
                    };
                    arg_terms.push(ts[ri].clone());
                    arg_thms.push(c);
                    ri += 1;
                }
            }
        }
        for j in 0..m {
            arg_terms.push(vs[j].clone());
            arg_thms.push(atom_thms[k + m + j].clone());
        }

        // ── `k + 2m` applications ────────────────────────────────────────────
        let fs_app_mem = self.pre.fs_app_mem.clone();
        let mut acc_term = su.clone();
        for (j, (x, x_thm)) in arg_terms.iter().zip(&arg_thms).enumerate() {
            let Some(next) = app_in_codomain(
                &fs_app_mem,
                &chain[j],
                &cods[j + 1],
                &acc_term,
                x,
                &acc_thm,
                x_thm,
                ha,
            ) else {
                return Err("iota: applying the minor premise to one argument failed")
            };
            acc_term = ap.apply(acc_term.clone(), x.clone());
            acc_thm = next;
        }
        let applied = derived::inductive::applied_minor(&ap, &order, &su, &ys, &ts, &vs);
        if acc_term != applied {
            return Err("iota: the applied minor is not the one the rule spells")
        }
        if u_concl(&acc_thm, ha) != Some(Formula::mem(applied, t.clone())) {
            return Err("iota: applying the minor premise did not land in the target")
        }

        // ── Curry the escaping assumptions back out, then quantify ───────────
        let mut quant = yv;
        quant.extend(tv);
        quant.extend(vv);
        let closed = match &h_out {
            None => derived::gen_all(&quant, &acc_thm),
            Some(o) => {
                let Some(u) = derived::uncurry(&acc_thm) else {
                    return Err("iota: separating the minor's assumptions failed")
                };
                match gen_under(&u, o, &quant) {
                    Some(c) => c,
                    None => return Err("iota: quantifying the pointwise typing failed"),
                }
            }
        };
        let claim = match &h_out {
            None => want,
            Some(o) => Formula::imp(o.clone(), want),
        };
        if *closed.concl() != claim {
            return Err("iota: the pointwise minor typing is not the one HYP asks for")
        }
        Ok((closed, out_hyps))
    }

    #[allow(clippy::too_many_arguments)]
    /// The ι rules for the parameterised recursive shape — `List.rec`.
    ///
    /// [`derived::wlist_rec`] supplies both, with
    /// `HYP := z ∈ T ∧ s ∈ fs(α, fs(lt(α), fs(T,T)))`:
    ///
    /// ```text
    /// ⊢ ∀α∀z∀s∀T.     (HYP → app(lrec(α,z,s,T), ⟨inl •,∅⟩) = z)
    /// ⊢ ∀α∀z∀s∀T∀h∀t. ((HYP ∧ (h ∈ α ∧ t ∈ lt(α))) →
    ///        app(lrec(α,z,s,T), ⟨inr h,{⟨•,t⟩}⟩)
    ///             = app(app(app(s,h),t), app(lrec(α,z,s,T), t)))
    /// ```
    ///
    /// Three things differ from [`Self::fire_nat`], and all three are the
    /// parameter.
    ///
    /// *`T` is `doms[2]`* — the motive at `List.nil α` rather than at a closed
    /// constructor — and, as there, it is the domain the nest already computed
    /// rather than a term rebuilt here, so that the two sides of the equation
    /// share their assumptions.
    ///
    /// *The type is a redex.* `⟦List α⟧` is `app(⟦List.{u}⟧, ⟦α⟧)`, so the
    /// bridge to `lt(α)` is not a defining equation but
    /// [`derived::wlist_fun::ListFun::l_beta`] under `⟦α⟧ ∈ ⟦Type u⟧` — the
    /// recursor's own level-0 domain obligation, handed back by
    /// [`Self::nest_chain`] rather than asked again. [`Self::mem_along_c`] is
    /// [`Self::mem_along`] with that premise carried.
    ///
    /// *The constructors are applied to `α`.* `⟦List.nil α⟧` is
    /// `app(⟦List.nil.{u}⟧, ⟦α⟧)` and `⟦List.cons α h t⟧` a three-deep spine, so
    /// the equations that take them to the W-type elements the ι rules are
    /// stated at are [`derived::wlist_fun::ListFun::nil_beta`] and `cons_beta`,
    /// transported across the abbreviations exactly as `list_const` transports
    /// the memberships.
    ///
    /// The cons rule's right-hand side mentions `lrec` **again**, at the tail;
    /// the reduct spells that call as `⟦List.rec α C z s t⟧`, so the last step
    /// contracts the nest once more and rewrites the call into that shape.
    fn fire_list(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        lr: &ListRecursor,
        nest: &RecNest,
        cfun: ExprPtr<'t>,
        args: &[ExprPtr<'t>],
        ta: &[Term],
        doms: &[Term],
        obligations: &[(Thm, Vec<Formula>)],
        idx: usize,
        fields: &[ExprPtr<'t>],
    ) -> Result<CondEq, &'static str> {
        let ap = self.pre.ap.clone();
        let app = ap.app;
        let major = args.len() - 1;
        if major != 4 || obligations.len() != 5 {
            return Err("iota: the list recursor is not applied to its five arguments")
        }
        let inds = lr.inds.clone();
        let (alpha, z, s) = (ta[0].clone(), ta[2].clone(), ta[3].clone());
        let (s_term, t_target) = (doms[0].clone(), doms[2].clone());
        let lrec = lr.lrec(&alpha, &z, &s, &t_target);
        let lt = inds.list.ty_of(alpha.clone());
        let list_ty = doms[major].clone();

        // ── `⊢ ⟦α⟧ ∈ ⟦Type u⟧ → ⟦List α⟧ = lt(α)` ────────────────────────────
        //
        // The type former is a *graph*, so this is a beta step and not a
        // defining equation. `⟦List.{u}⟧` is looked up at the constructor's own
        // universe levels and the result checked against the domain the nest
        // walked off the recursor's type, so a level mismatch declines rather
        // than proving something about another instance.
        let Expr::Const { levels: clevels, .. } = ctx.read_expr(cfun) else {
            return Err("iota: the major premise is not a constructor")
        };
        let Some(Declar::Constructor(c)) = self.decls.get_declar(&{
            let Expr::Const { name, .. } = ctx.read_expr(cfun) else {
                return Err("iota: the major premise is not a constructor")
            };
            name
        }) else {
            return Err("iota: the major premise is not a constructor")
        };
        let ind_name = c.inductive_name;
        let Some(l_t) = self.ind_const(ctx, ind_name, clevels) else {
            return Err("iota: the inductive has no interpretation")
        };
        let Some(l_ax) = self.abbrev_defs.get(&l_t).cloned() else {
            return Err("iota: the inductive has no defining equation")
        };
        if self.mk(app, vec![l_t.clone(), alpha.clone()]) != list_ty {
            return Err("iota: the major premise's domain is not this inductive at this parameter")
        }
        let (lf_l, l_beta, nil_beta, cons_beta) = {
            let lf = &inds.list_fun;
            (
                lf.l_of(s_term.clone()),
                lf.l_beta.clone(),
                lf.nil_beta.clone(),
                lf.cons_beta.clone(),
            )
        };
        let a_in_s = Formula::mem(alpha.clone(), s_term.clone());
        let lt_eq_raw = {
            let Some(raw) = derived::inst_all(&l_beta, &[s_term.clone(), alpha.clone()]) else {
                return Err("iota: instantiating the type former's beta rule failed")
            };
            let Some(back) = derived::eq_symm(&mut self.env_mut(), &l_ax) else {
                return Err("iota: reversing the inductive's defining equation failed")
            };
            let w = self.env_mut().fresh_var();
            let hole_app = self.mk(app, vec![Term::var(w), alpha.clone()]);
            let leib = Thm::eq_leibniz(
                lf_l.clone(),
                l_t.clone(),
                w,
                Formula::imp(a_in_s.clone(), Formula::eq(hole_app, lt.clone())),
            );
            let Some(out) = Thm::mp(&leib, &back).and_then(|i| Thm::mp(&i, &raw)) else {
                return Err("iota: transporting the type former's beta rule failed")
            };
            if *out.concl()
                != Formula::imp(a_in_s.clone(), Formula::eq(list_ty.clone(), lt.clone()))
            {
                return Err("iota: the type former's beta rule is not about this instance")
            }
            out
        };
        let (ha, ha_hyps) = obligations[0].clone();
        let h_a = conj_of(&ha_hyps);
        let Some(lt_eq) = u_syl(&ha, &lt_eq_raw, h_a.as_ref()) else {
            return Err("iota: discharging the parameter's typing failed")
        };

        // ── `HYP`, from the recursor's own domain obligations ────────────────
        let (hz, hz_hyps) = obligations[2].clone();
        let fs = self.pre.fs_sym();
        let inner = Term::apply(fs, vec![t_target.clone(), t_target.clone()]);
        let mid = Term::apply(fs, vec![list_ty.clone(), inner.clone()]);
        let shown = Term::apply(fs, vec![alpha.clone(), mid.clone()]);
        let Some((hs, hs_raw_hyps)) = self.mem_obligation(ctx, args[3], &s, &shown) else {
            return Err("iota: the cons minor premise has no typing to rest on")
        };
        let (s_c, alpha_c, inner_c) = (s.clone(), alpha.clone(), inner.clone());
        let Some((hs, hs_hyps)) =
            self.mem_along_c(&hs, &hs_raw_hyps, &lt_eq, &ha_hyps, move |w| {
                Formula::mem(
                    s_c.clone(),
                    Term::apply(
                        fs,
                        vec![
                            alpha_c.clone(),
                            Term::apply(fs, vec![w, inner_c.clone()]),
                        ],
                    ),
                )
            })
        else {
            return Err("iota: transporting the cons minor's typing failed")
        };

        let mut hyps = merge_hyps(&hz_hyps, &hs_hyps);
        let premise =
            derived::wlist_rec::premise(&inds.wt.sums, &inds.list, &alpha, &z, &s, &t_target);

        // ── The constructor, and with it which rule fires ────────────────────
        let ctor_t = self.interp(ctx, cfun);
        let Some(ctor_ax) = self.abbrev_defs.get(&ctor_t).cloned() else {
            return Err("iota: the constructor has no defining equation")
        };
        let (ctor_eq, rule, extra) = match idx {
            0 => {
                // `⟦List.nil α⟧ = ⟨inl •,∅⟩`: unfold the graph, beta-reduce at
                // `⟦α⟧`, and the value is the W-type element itself.
                if !fields.is_empty() {
                    return Err("iota: the nil constructor has the wrong arity")
                }
                let lf_nil = inds.list_fun.nil_of(s_term.clone());
                let elem = derived::wlist::WList::nil_term(&inds.wt);
                let Some(raw) = derived::inst_all(&nil_beta, &[s_term.clone(), alpha.clone()])
                else {
                    return Err("iota: instantiating the nil beta rule failed")
                };
                let Some(back) = derived::eq_symm(&mut self.env_mut(), &ctor_ax) else {
                    return Err("iota: reversing the constructor's defining equation failed")
                };
                let w = self.env_mut().fresh_var();
                let hole_app = self.mk(app, vec![Term::var(w), alpha.clone()]);
                let leib = Thm::eq_leibniz(
                    lf_nil,
                    ctor_t.clone(),
                    w,
                    Formula::imp(a_in_s.clone(), Formula::eq(hole_app, elem.clone())),
                );
                let Some(out) = Thm::mp(&leib, &back).and_then(|i| Thm::mp(&i, &raw)) else {
                    return Err("iota: transporting the nil beta rule failed")
                };
                if *out.concl()
                    != Formula::imp(a_in_s.clone(), Formula::eq(ta[major].clone(), elem))
                {
                    return Err("iota: the nil beta rule is not about this instance")
                }
                let Some(def) = u_syl(&ha, &out, h_a.as_ref())
                    .and_then(|t| CondEq::new(t, ha_hyps.clone()))
                else {
                    return Err("iota: the nil constructor's equation has the wrong shape")
                };
                let Some(rule) = derived::inst_all(
                    &lr.lr.iota_nil,
                    &[alpha.clone(), z.clone(), s.clone(), t_target.clone()],
                ) else {
                    return Err("iota: instantiating the nil computation rule failed")
                };
                (def, rule, None)
            }
            _ => {
                // `⟦List.cons α h t⟧ = ⟨inr h,{⟨•,t⟩}⟩`, the three-deep spine.
                if fields.len() != 2 {
                    return Err("iota: the cons constructor has the wrong arity")
                }
                let th = self.interp(ctx, fields[0]);
                let tl = self.interp(ctx, fields[1]);
                let Some((hh, hh_hyps)) = self.mem_obligation(ctx, fields[0], &th, &alpha) else {
                    return Err("iota: the head has no typing to rest on")
                };
                let Some((hl_raw, hl_raw_hyps)) =
                    self.mem_obligation(ctx, fields[1], &tl, &list_ty)
                else {
                    return Err("iota: the tail has no typing to rest on")
                };
                let tl_c = tl.clone();
                let Some((hl, hl_hyps)) =
                    self.mem_along_c(&hl_raw, &hl_raw_hyps, &lt_eq, &ha_hyps, move |w| {
                        Formula::mem(tl_c.clone(), w)
                    })
                else {
                    return Err("iota: transporting the tail's typing failed")
                };

                let lf_cons = inds.list_fun.cons_of(s_term.clone());
                let elem = derived::wlist::WList::cons_term(&inds.wt, th.clone(), tl.clone());
                let Some(raw) = derived::inst_all(
                    &cons_beta,
                    &[s_term.clone(), alpha.clone(), th.clone(), tl.clone()],
                ) else {
                    return Err("iota: instantiating the cons beta rule failed")
                };
                // Two transports: the constructor's graph, then the type's,
                // the latter occurring only in the tail's premise.
                let spine = |b: &mut Self, head: Term| {
                    let one = b.mk(app, vec![head, alpha.clone()]);
                    let two = b.mk(app, vec![one, th.clone()]);
                    b.mk(app, vec![two, tl.clone()])
                };
                let prem_of = |b: &mut Self, ty_head: Term| {
                    let app_l = b.mk(app, vec![ty_head, alpha.clone()]);
                    Formula::and(
                        a_in_s.clone(),
                        Formula::and(
                            Formula::mem(th.clone(), alpha.clone()),
                            Formula::mem(tl.clone(), app_l),
                        ),
                    )
                };
                let prem_raw = prem_of(self, lf_l.clone());
                let Some(back_c) = derived::eq_symm(&mut self.env_mut(), &ctor_ax) else {
                    return Err("iota: reversing the constructor's defining equation failed")
                };
                let w = self.env_mut().fresh_var();
                let spine_w = spine(self, Term::var(w));
                let leib = Thm::eq_leibniz(
                    lf_cons,
                    ctor_t.clone(),
                    w,
                    Formula::imp(prem_raw, Formula::eq(spine_w, elem.clone())),
                );
                let Some(step) = Thm::mp(&leib, &back_c).and_then(|i| Thm::mp(&i, &raw)) else {
                    return Err("iota: transporting the cons beta rule failed")
                };
                let Some(back_l) = derived::eq_symm(&mut self.env_mut(), &l_ax) else {
                    return Err("iota: reversing the inductive's defining equation failed")
                };
                let w2 = self.env_mut().fresh_var();
                let spine_c = spine(self, ctor_t.clone());
                let prem_w = prem_of(self, Term::var(w2));
                let leib2 = Thm::eq_leibniz(
                    lf_l.clone(),
                    l_t.clone(),
                    w2,
                    Formula::imp(prem_w, Formula::eq(spine_c.clone(), elem.clone())),
                );
                let Some(out) = Thm::mp(&leib2, &back_l).and_then(|i| Thm::mp(&i, &step)) else {
                    return Err("iota: transporting the cons beta rule's premise failed")
                };
                let prem = prem_of(self, l_t.clone());
                if *out.concl()
                    != Formula::imp(prem.clone(), Formula::eq(ta[major].clone(), elem))
                {
                    return Err("iota: the cons beta rule is not about this instance")
                }

                // Its three premises, from the three obligations already paid.
                let eq_hyps = merge_hyps(&merge_hyps(&ha_hyps, &hh_hyps), &hl_raw_hyps);
                let eh = conj_of(&eq_hyps);
                let (Some(ea), Some(eh_h), Some(et)) = (
                    reassume(&ha, &ha_hyps, &eq_hyps),
                    reassume(&hh, &hh_hyps, &eq_hyps),
                    reassume(&hl_raw, &hl_raw_hyps, &eq_hyps),
                ) else {
                    return Err("iota: restating the constructor's premises failed")
                };
                let Some(ante) = u_and_intro(&eh_h, &et, eh.as_ref())
                    .and_then(|r| u_and_intro(&ea, &r, eh.as_ref()))
                else {
                    return Err("iota: assembling the constructor's premises failed")
                };
                if u_concl(&ante, eh.as_ref()) != Some(prem) {
                    return Err("iota: the constructor's assembled premise is not the one it asks for")
                }
                let Some(def) = u_syl(&ante, &out, eh.as_ref())
                    .and_then(|t| CondEq::new(t, eq_hyps))
                else {
                    return Err("iota: the cons constructor's equation has the wrong shape")
                };

                let Some(rule) = derived::inst_all(
                    &lr.lr.iota_cons,
                    &[
                        alpha.clone(),
                        z.clone(),
                        s.clone(),
                        t_target.clone(),
                        th.clone(),
                        tl.clone(),
                    ],
                ) else {
                    return Err("iota: instantiating the cons computation rule failed")
                };
                hyps = merge_hyps(&merge_hyps(&hyps, &hh_hyps), &hl_hyps);
                (def, rule, Some((th, tl, hh, hh_hyps, hl, hl_hyps)))
            }
        };

        // ── `⊢ conj(hyps) → HYP`, and with it the rule's own antecedent ──────
        let h = conj_of(&hyps);
        let (Some(hz), Some(hs)) =
            (reassume(&hz, &hz_hyps, &hyps), reassume(&hs, &hs_hyps, &hyps))
        else {
            return Err("iota: restating the minor premises' typings failed")
        };
        let Some(mut ante) = u_and_intro(&hz, &hs, h.as_ref()) else {
            return Err("iota: assembling the recursor's hypothesis failed")
        };
        let mut want = premise;
        if let Some((th, tl, hh, hh_hyps, hl, hl_hyps)) = &extra {
            let (Some(hh), Some(hl)) =
                (reassume(hh, hh_hyps, &hyps), reassume(hl, hl_hyps, &hyps))
            else {
                return Err("iota: restating the constructor's field typings failed")
            };
            let Some(both) = u_and_intro(&hh, &hl, h.as_ref())
                .and_then(|r| u_and_intro(&ante, &r, h.as_ref()))
            else {
                return Err("iota: assembling the cons hypothesis failed")
            };
            ante = both;
            want = Formula::and(
                want,
                Formula::and(
                    Formula::mem(th.clone(), alpha.clone()),
                    Formula::mem(tl.clone(), lt.clone()),
                ),
            );
        }
        if u_concl(&ante, h.as_ref()) != Some(want) {
            return Err("iota: the assembled hypothesis is not the one the rule asks for")
        }
        let Some(fired) = u_syl(&ante, &rule, h.as_ref()) else {
            return Err("iota: discharging the computation rule's hypothesis failed")
        };
        let Some(fired) = CondEq::new(fired, hyps) else {
            return Err("iota: the computation rule does not have the assumed shape")
        };

        // ── `app(lrec, ⟦cᵢ α …⟧) = app(lrec, ⟨…⟩)`, then the rule ────────────
        let Some(at_ctor) = self.ceq_congr(app, &[CondEq::refl(lrec.clone()), ctor_eq]) else {
            return Err("iota: congruence at the constructor refused")
        };
        let Some(mut acc) = self.ceq_trans(&at_ctor, &fired) else {
            return Err("iota: the nest does not reduce to the W-recursor at the constructor")
        };

        // ── The live recursive call, spelled the way the reduct spells it ────
        if let Some((th, tl, _, _, _, _)) = extra {
            let mut rec_args: Vec<ExprPtr<'t>> = args[..major].to_vec();
            rec_args.push(fields[1]);
            let mut rec_ta: Vec<Term> = ta[..major].to_vec();
            rec_ta.push(tl.clone());
            let (call, _) = self.nest_chain(ctx, nest, &rec_args, &rec_ta, doms)?;
            let Some(back) = self.ceq_symm(&call) else {
                return Err("iota: reversing the recursive call's contraction failed")
            };
            let head = ap.apply(ap.apply(s.clone(), th), tl);
            let Some(fixup) = self.ceq_congr(app, &[CondEq::refl(head), back]) else {
                return Err("iota: congruence at the recursive call refused")
            };
            let Some(t) = self.ceq_trans(&acc, &fixup) else {
                return Err("iota: rewriting the recursive call failed")
            };
            acc = t;
        }
        Ok(acc)
    }

    /// Graph extensionality relating the two lambda *skeletons*, derived on
    /// first use and shared thereafter.
    fn lam_ext_thm(&mut self, ka: &Term, kb: &Term) -> Option<Thm> {
        let key = (ka.clone(), kb.clone());
        if let Some(t) = self.shared.borrow().lam_exts.get(&key) {
            return t.as_ref().map(|s| s.thm().clone())
        }
        let ia = self.lam_info(ka)?;
        let ib = self.lam_info(kb)?;
        let thm = match (ia.graph.as_ref(), ib.graph.as_ref()) {
            (Some(ga), Some(gb)) => {
                let ap = self.pre.clone();
                lam_ext_n(&mut self.env_mut(), &ap.ap, ga.t, ia.lam, &ga.lam_ax, gb.t, ib.lam, &gb.lam_ax)
            }
            _ => None,
        };
        self.shared.borrow_mut().lam_exts.insert(key, Sealed::seal(thm.clone()));
        thm
    }

    /// The pointwise premise of [`lam_ext_n`], read off the body certificate.
    ///
    /// The certificate says `⊢ ⟦b⟧ = ⟦b'⟧` with both bodies opened at the
    /// checker's local for this binder — a kernel *free* variable `w`. What the
    /// extensionality lemma wants is `⊢ ∀x. (x ∈ A → t(h⃗,x) = t'(h⃗',x))`.
    ///
    /// The bridge is the two body-symbol definitions: `t(h⃗,w)` unfolds to the
    /// skeleton with `w` in the binder slot, which is exactly the certificate's
    /// left-hand side — *if* `w` is the right variable, which is checked by
    /// comparing the unfolded terms rather than assumed. `w` itself is not
    /// handed to this rule, so it is searched for among the free variables of
    /// the certificate; a body that ignores its binder pins nothing, and then a
    /// fresh variable does (the resulting `∀` is vacuous, which is correct).
    ///
    /// Weakening to the guarded form is `a1i`, and the generalisation is the
    /// kernel's `gen_checked`.
    ///
    /// # `gen`'s side condition, and why the fallible primitive is used here
    ///
    /// Since `Thm` became a sequent `Γ ⊢ φ`, `gen` **has** the classic side
    /// condition `w ∉ FV(Γ)`. [`kernel::Thm::gen_checked`] is the primitive and
    /// reports a violation as `None`; `Thm::gen` is the wrapper that **panics**
    /// on it, and this crate does not call it — `ci/check-boundary.sh` R6′
    /// forbids the token outright, so a rule that one day starts from an
    /// assumption inherits a counted gap rather than an abort.
    ///
    /// This file called the panicking wrapper until task #30, on the argument
    /// that every call was reachable only with `Γ = ∅` because no rule here
    /// builds a hypothetical `Thm`. The argument was true (and remains true
    /// today: [`crate::scope`] has no caller in this crate yet, so no `Γ` is
    /// ever non-empty here) but it was unreachability by an externally pinned
    /// invariant rather than by anything local, and the pin was a *ban* on
    /// hypotheses outside the kernel — which is not a soundness rule and is not
    /// what the sequent judgement is for. Answering the hazard at the site
    /// costs one `?`.
    ///
    /// An earlier version of this comment said `gen` "needs no side condition,
    /// since a `Thm` carries no hypotheses". That was the pre-sequent argument
    /// and it is retired; it is recorded here only so the sentence is not
    /// reconstructed from memory.
    ///
    /// Separately from `Γ`, `w` must be absent from `h⃗`, `h⃗'` and `A`, or the
    /// `∀` would capture them; the candidates are filtered on exactly that, and
    /// a slip there could only make the `mp` below fail, never produce a false
    /// claim.
    ///
    /// # Discharging an assumption
    ///
    /// This is also the one place where a carried assumption goes away. If the
    /// body certificate is conditional and one of its assumptions is literally
    /// `w ∈ A` — the guard of the very `∀` being built — then that assumption is
    /// *not* weakened in, it is **used**: re-stated last, peeled off with
    /// [`derived::uncurry`], generalised, and pushed back through the ∀ with
    /// `Thm::ax_dist`. The kernel checks `ax_dist`'s side condition (`w` not
    /// free in the remaining assumptions), so a mistake is a rejection.
    ///
    /// Returns the premise together with the assumptions that survive it.
    fn pointwise_premise(
        &mut self,
        t_def_a: &Thm,
        t_def_b: &Thm,
        holes_a: &[Term],
        holes_b: &[Term],
        dom_a: &Term,
        body: &CondEq,
    ) -> Option<(Thm, Vec<Formula>)> {
        let (u1, u2) = body.as_eq()?;

        // Variables `w` may be: those the two body interpretations mention, but
        // not any that the parameters or the domain do.
        let mut excluded: Vec<FreeVar> = Vec::new();
        for h in holes_a.iter().chain(holes_b.iter()) {
            h.free_vars(&mut excluded);
        }
        dom_a.free_vars(&mut excluded);
        let mut seen: Vec<FreeVar> = Vec::new();
        u1.free_vars(&mut seen);
        u2.free_vars(&mut seen);
        let mut cands: Vec<FreeVar> = Vec::new();
        for v in seen {
            if !excluded.contains(&v) && !cands.contains(&v) {
                cands.push(v);
            }
        }
        // A body that does not mention its binder leaves `w` free; any variable
        // not already in play will do, and a fresh one certainly is not.
        cands.push(self.env_mut().fresh_var());

        for w in cands {
            let tw = Term::var(w);
            let inst = |holes: &[Term]| {
                let mut v = holes.to_vec();
                v.push(tw.clone());
                v
            };
            let Some(ea) = derived::inst_all(t_def_a, &inst(holes_a)) else { continue };
            let Some(eb) = derived::inst_all(t_def_b, &inst(holes_b)) else { continue };
            // `t(h⃗,w) = ⟦b⟧` and `t'(h⃗',w) = ⟦b'⟧` — the halves that make the
            // certificate applicable at all.
            match (ea.concl().as_eq(), eb.concl().as_eq()) {
                (Some((_, ra)), Some((_, rb))) if ra == u1 && rb == u2 => {}
                _ => continue,
            }
            let Some(eb_symm) = derived::eq_symm(&mut self.env_mut(), &eb) else { continue };
            let (Some(ea), Some(eb_symm)) = (CondEq::plain(ea), CondEq::plain(eb_symm)) else { continue };
            let Some(half) = self.ceq_trans(&ea, body) else { continue };
            let Some(at_w) = self.ceq_trans(&half, &eb_symm) else { continue };
            let Some(out) = self.guard_and_generalise(&at_w, w, dom_a) else { continue };
            return Some(out)
        }
        None
    }

    /// Turn `⊢ conj(hyps) → (l = r)`, stated at the free variable `w`, into
    /// `⊢ conj(rest) → ∀x. (x ∈ A → l[x] = r[x])`.
    ///
    /// The guarded, generalised form is what both extensionality lemmas want as
    /// a premise: [`lam_ext_n`]'s pointwise equation and
    /// [`dprod_const_fibre_n`]'s constant-fibre condition are the same shape.
    ///
    /// Weakening to the guarded form is `a1i`, and the generalisation is the
    /// kernel's `gen_checked`, whose side condition `w ∉ FV(Γ)` is discussed on
    /// [`Self::pointwise_premise`]: `Γ` is empty at every call in this file
    /// today, and a future one where it is not reports a gap.
    ///
    /// Separately from `Γ`, `w` must be absent from `A` and from anything the
    /// two sides are supposed to be uniform in; the callers filter their
    /// candidates on exactly that, and a slip there could only make the `mp` in
    /// the caller fail, never produce a false claim.
    ///
    /// # Discharging an assumption
    ///
    /// This is the one place where a carried assumption goes away. If the
    /// certificate is conditional and one of its assumptions is literally
    /// `w ∈ A` — the guard of the very `∀` being built — then that assumption is
    /// *not* weakened in, it is **used**: re-stated last, peeled off with
    /// [`derived::uncurry`], generalised, and pushed back through the ∀ with
    /// `Thm::ax_dist`. The kernel checks `ax_dist`'s side condition (`w` not
    /// free in the remaining assumptions), so a mistake is a rejection.
    ///
    /// # Assumptions that mention the binder
    ///
    /// Any *other* assumption mentioning `w` is **hoisted** to its own guarded
    /// universal closure `∀w. (w ∈ A → φ(w))` before the generalisation; see
    /// [`Self::guard_and_generalise_at`].
    ///
    /// Returns the premise together with the assumptions that survive it.
    fn guard_and_generalise(&mut self, at_w: &CondEq, w: FreeVar, dom: &Term) -> Option<(Thm, Vec<Formula>)> {
        let (l, r) = at_w.as_eq()?;
        self.guard_and_generalise_at(&at_w.thm, &at_w.hyps, &Formula::eq(l, r), w, dom)
    }

    /// [`Self::guard_and_generalise`] over an arbitrary conclusion.
    ///
    /// The equation form is what lambda and `Π` *congruence* want; the
    /// membership form `t(h⃗,w) ∈ b(q⃗,w)` is what the lambda *typing* rule wants
    /// ([`Self::has_type_lam`]). Nothing in the argument looks at the
    /// conclusion, so the two share one implementation and one discharge.
    ///
    /// `thm` is checked to be literally `⊢ conj(hyps) → concl` first, so a
    /// caller that mis-describes what it holds gets `None`.
    ///
    /// # Why an assumption mentioning `w` is hoisted rather than refused
    ///
    /// The premise being built is `w`-free — `w` is *bound* in it — so an
    /// assumption `φ(w)` cannot come along as it stands, and `ax_dist` refuses.
    /// Measured, that refusal was the **only** reason `pi_cong`'s extensionality
    /// route and its constant-fibre bridge ever failed: every one of the 216
    /// failures on `init-prelude` reached this point with the two fibre
    /// unfoldings already matching the certificate, and was stopped by a leftover
    /// assumption — always a membership `t(w) ∈ s` — that mentions the binder.
    /// Those are beta typing obligations about arguments that depend on the
    /// binder, and there is nothing wrong with them; what is wrong is stating
    /// them at a variable that is about to go out of scope.
    ///
    /// So they are re-stated at every point of the domain at once:
    /// `∀w. (w ∈ A → φ(w))`, which is `w`-free, and which — instantiated at this
    /// `w`, under this guard — gives `φ(w)` back. That is a *weakening* of the
    /// assumption set: strictly more is assumed than is used, and the assumption
    /// stays in the returned list, so it is still owed. It is also the shape a
    /// discharge can reach, being exactly what the lambda typing rule
    /// ([`Self::has_type_lam`]) produces, whereas `φ(w)` is not.
    fn guard_and_generalise_at(
        &mut self,
        thm: &Thm,
        hyps: &[Formula],
        concl: &Formula,
        w: FreeVar,
        dom: &Term,
    ) -> Option<(Thm, Vec<Formula>)> {
        (u_concl(thm, conj_of(hyps).as_ref())? == *concl).then_some(())?;
        let guard = Formula::mem(Term::var(w), dom.clone());

        // Sort the assumptions by their relation to the binder's variable.
        //
        //   * the guard itself is *discharged* into the implication being built,
        //     not assumed twice;
        //   * an assumption free of `w` survives unchanged;
        //   * any other assumption mentions `w`, and cannot survive as it
        //     stands: the premise being built is `w`-free, so `ax_dist` would —
        //     rightly — refuse. It is **hoisted** to its own guarded universal
        //     closure `∀w. (w ∈ A → φ(w))`, which is `w`-free and, at this one
        //     `w` and under this one guard, gives back `φ(w)`.
        //
        // Hoisting is a *weakening of the assumption set*: what is assumed is
        // strictly more than what is used. It is also the shape a discharge can
        // reach — it is exactly what the lambda typing rule produces — whereas
        // `φ(w)` mentions a variable that has gone out of scope.
        enum Src {
            /// The guard, discharged into the implication.
            Guard,
            /// A surviving assumption, at this index of `rest`.
            Plain(usize),
            /// Hoisted; `rest[i]` is its guarded universal closure.
            Hoist(usize),
        }
        let mut rest: Vec<Formula> = Vec::new();
        let mut srcs: Vec<Src> = Vec::with_capacity(hyps.len());
        for f in hyps {
            if *f == guard {
                srcs.push(Src::Guard);
                continue
            }
            let (keep, hoisted) = if f.occurs_free(w) {
                let closure = Formula::forall(w, Formula::imp(guard.clone(), f.clone()));
                // Remember what went in, so that `peel_family` can try to
                // discharge the closure later at the same variable. The record
                // is a hint; see the field's own documentation.
                self.hoisted.entry(closure.clone()).or_insert((w, dom.clone(), f.clone()));
                (closure, true)
            } else {
                (f.clone(), false)
            };
            let i = match rest.iter().position(|g| *g == keep) {
                Some(i) => i,
                None => {
                    rest.push(keep);
                    rest.len() - 1
                }
            };
            srcs.push(if hoisted { Src::Hoist(i) } else { Src::Plain(i) });
        }

        // `K := conj(rest) ∧ (w ∈ A)`, the antecedent everything is rebuilt
        // under. The guard is last so that `uncurry` peels it off again.
        let mut k_parts = rest.clone();
        k_parts.push(guard.clone());
        let g_at = k_parts.len() - 1;
        let k = conj_of(&k_parts)?;

        // `⊢ K → conj(hyps)`, one assumption at a time, so that `thm` applies.
        let mut acc: Option<Thm> = None;
        for src in &srcs {
            let p = match src {
                Src::Guard => conj_proj(&k_parts, g_at)?,
                Src::Plain(i) => conj_proj(&k_parts, *i)?,
                Src::Hoist(i) => {
                    let closure = conj_proj(&k_parts, *i)?;
                    // `⊢ (∀w. (w ∈ A → φ)) → (w ∈ A → φ)`, then the guard.
                    let inst = Thm::ax_inst(rest[*i].clone(), Term::var(w))?;
                    let under_guard = derived::syl(&closure, &inst)?;
                    derived::hyp_mp(&under_guard, &conj_proj(&k_parts, g_at)?)?
                }
            };
            acc = Some(match acc {
                None => p,
                Some(a) => derived::hyp_and(&a, &p)?,
            });
        }
        let under_k = match acc {
            Some(a) => derived::syl(&a, thm)?,
            // No assumptions at all: `thm` is already `⊢ concl`.
            None => derived::a1i(thm, k),
        };

        // `⊢ conj(rest) → (w ∈ A → concl)`; with no `rest`, `conj([guard])` *is*
        // the guard and the theorem is already in that form.
        let guarded = if rest.is_empty() { under_k } else { derived::uncurry(&under_k)? };

        let all = Thm::gen_checked(w, &guarded)?;
        if rest.is_empty() {
            return Some((all, rest))
        }
        // `⊢ ∀w. (conj(rest) → (w ∈ A → …))` becomes
        // `⊢ conj(rest) → ∀w. (w ∈ A → …)`. The kernel refuses if `w` is free in
        // `conj(rest)`, which is exactly the condition under which the move
        // would be wrong.
        let rc = conj_of(&rest)?;
        let dist = Thm::ax_dist(w, rc, Formula::imp(guard, concl.clone()))?;
        let out = Thm::mp(&dist, &all)?;
        Some((out, rest))
    }

    /// Discharge every assumption of a certificate that is a **guarded family**
    /// of typing obligations, `∀x. (x ∈ A → ⟦a(x)⟧ ∈ ⟦A(x)⟧)`.
    ///
    /// This is the consumer for the shape [`Self::guard_and_generalise_at`]
    /// hoists. Hoisting a binder-dependent assumption is what lets `pi_cong`'s
    /// extensionality route and its constant-fibre bridge get past `ax_dist`, but
    /// it leaves the obligation *owed*: it rides up with the certificate and, if
    /// nothing proves it, the escape ledger counts it at the boundary.
    ///
    /// The shape was chosen so that a proof is reachable. It is exactly what
    /// [`Self::has_type_lam`] establishes about a lambda's body, and the way to
    /// establish it is the same: type the subject **under the binder's own
    /// guard** and generalise. So each candidate assumption is re-opened at the
    /// variable it was closed over, the subject's Lean node is recovered, and
    /// `has_type` is asked for `⟦a⟧ ∈ ⟦A⟧` with `w ∈ ⟦A⟧` in force. What comes
    /// back goes through the *same* `guard_and_generalise_at`, so the formula
    /// proved is built by the same code that built the assumption, and the two
    /// are compared before anything is peeled.
    ///
    /// # Nothing is dropped
    ///
    /// A peel replaces `⊢ conj(rest ++ [family]) → C` by `⊢ conj(rest) → C`, and
    /// it does so by `mp` against a derivation of `family` from `conj(rest)`.
    /// The assumption is therefore *discharged*, not forgotten: the ledger keeps
    /// balancing, because the certificate that comes out asserts strictly less
    /// than the one that went in.
    ///
    /// # It fires zero times, and the reason is not the assumption set
    ///
    /// `init-prelude` offers **1186** families; 1144 have a binder free of the
    /// other assumptions, **677** of those are plain memberships with a Lean
    /// node — and `has_type` derives **0** of the 677. The comment this replaces
    /// said the typing call was the one `domain_obligation`'s raw fallback had
    /// already failed "under a superset of these assumptions". That conclusion
    /// was right and the mechanism was wrong: in **446 of the 677** the peel's
    /// `rest ++ [guard]` does not even *contain* the subject's local premises,
    /// so it is the weaker set, not the stronger one. Handing `has_type` the
    /// union of both — every guard plus `local_premises` of the subject — was
    /// measured, and derives **0 of 677** as well. Nothing about the assumption
    /// set is what stops this.
    ///
    /// What stops it is that the subject has no typing rule, and the split says
    /// so. Of the 677:
    ///
    /// * **221** are not applications at all — 187 lambdas whose target is a
    ///   motive application rather than a function space or a dependent product,
    ///   19 projections and literals, 13 locals, 2 `Π`s;
    /// * **186** are applications of a constant this backend does not interpret
    ///   as an inductive: `Lean.Syntax.node`, `Nat.rec`, `List.rec`, `Eq.refl`;
    /// * **29** are applications of a local or of a lambda, and **3** have a
    ///   constructor rule but not at these universe levels;
    /// * **238** have a constructor rule at these levels, of the right arity,
    ///   and fail on one of its **premises**. Not one of the 677 gets all its
    ///   premises: the `prems-ok` count is zero.
    ///
    /// The 238 are the only ones with anything but interpretation scope in them.
    /// **144** of them fail on a premise about a bare context local whose own
    /// typing `⟦w⟧ ∈ ⟦A⟧` is already in force — the rule states that premise at
    /// a domain which is neither `⟦A⟧` nor reachable from it by
    /// [`Self::unfolds_to`], and which [`Self::target_head_step`] cannot reduce
    /// either, because its application spine bottoms out at a *variable*. That
    /// is a real missing bridge and the one sub-population here that is not
    /// interpretation scope. It is also not the lever this rule was reached
    /// through: none of the 144 is an antecedent of a conditional declaration
    /// typing (see [`Self::store_declar_typing`]), so closing it would move this
    /// ledger off zero and leave [`Dt::Conditional`], [`Dt::MissCond`] and the
    /// declaration-typing hit rate exactly where they are.
    ///
    /// The other 467 of the 1144 are nested — a family whose body is a family —
    /// and [`Self::peel_family`] declines them. Unwrapping them to the innermost
    /// membership and asking under every guard collected on the way derives 0 of
    /// those too, so recursing into the nesting is plumbing that buys nothing.
    fn discharge_families(&mut self, ctx: &mut TcCtx<'t, 'p>, c: CondEq) -> CondEq {
        // The equation the caller has already matched against its claim. Nothing
        // below can change it — `reassume`, `uncurry`, `hyp_mp` and `mp` all
        // preserve the consequent — but the guard is here rather than argued,
        // because `cert`'s callers check `proves` *before* this runs and a peel
        // that moved the equation would slip past them.
        let Some(claim) = c.as_eq() else { return c };
        let mut cur = c;
        // One peel can only shorten the list, so this terminates; the loop is
        // there because peeling one assumption may make another's `w` free of
        // the rest and so newly peelable.
        'outer: loop {
            for i in 0..cur.hyps.len() {
                let Some(next) = self.peel_family(ctx, &cur, i) else { continue };
                if next.as_eq() != Some(claim.clone()) {
                    continue
                }
                cur = next;
                continue 'outer
            }
            return cur
        }
    }

    /// One peel: [`Self::discharge_families`] at assumption `i`, or `None` if
    /// that assumption is not a guarded family this can prove.
    fn peel_family(&mut self, ctx: &mut TcCtx<'t, 'p>, c: &CondEq, i: usize) -> Option<CondEq> {
        let family = c.hyps.get(i)?.clone();
        let (w, dom, phi) = self.hoisted.get(&family).cloned()?;
        note_peel(PeelStop::Family);
        // The other assumptions, in order. `w` must not be free in any of them:
        // the generalisation below would otherwise capture, and `ax_dist` would
        // refuse — as it should.
        let rest: Vec<Formula> =
            c.hyps.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, f)| f.clone()).collect();
        if rest.iter().any(|f| f.occurs_free(w)) {
            return None
        }
        note_peel(PeelStop::Free);

        // The obligation, and the Lean node its subject came from. The node is a
        // *hint*: `has_type_a`'s guard checks the derivation against the claim
        // regardless, and it is checked to interpret to the subject here.
        let Some((subj, target)) = phi.as_mem() else {
            note_peel(PeelStop::Nested);
            return None
        };
        note_peel(PeelStop::Mem);
        let e = *self.exprs_rev.get(&subj)?;
        if self.interp(ctx, e) != subj {
            return None
        }
        note_peel(PeelStop::Node);

        // Type the subject under the binder's own guard, appended last so that
        // `guard_and_generalise_at` peels it back off.
        let mut inner = rest.clone();
        inner.push(Formula::mem(Term::var(w), dom.clone()));
        let Some(proof) = self.has_type_h(ctx, e, &target, &inner, 0) else {
            let sh = self.ht_shape(ctx, e);
            PEEL_SHAPE[sh as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let tg = self.ht_target(&target);
            PEEL_TARGET[tg as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return None
        };
        note_peel(PeelStop::Typed);

        // Re-close it: `⊢ conj(rest) → ∀w. (w ∈ ⟦A⟧ → φ(w))`. Built by the same
        // routine that built the assumption, and then *compared* against it, so
        // a mis-recorded hint cannot discharge the wrong thing.
        let (fam, left) = self.guard_and_generalise_at(&proof, &inner, &phi, w, &dom)?;
        if left != rest {
            return None
        }
        let h = conj_of(&rest);
        if u_concl(&fam, h.as_ref())? != family {
            return None
        }
        note_peel(PeelStop::Closed);

        let out = peel_off(c, i, &fam)?;
        note_peel(PeelStop::Peeled);
        Some(out)
    }

    /// Dependent-product extensionality relating the two fibre *skeletons*,
    /// derived on first use and shared thereafter.
    fn pi_ext_thm(&mut self, ka: &Term, kb: &Term) -> Option<Thm> {
        let key = (ka.clone(), kb.clone());
        if let Some(t) = self.shared.borrow().pi_exts.get(&key) {
            return t.as_ref().map(|s| s.thm().clone())
        }
        let ia = self.pi_info(ka)?;
        let ib = self.pi_info(kb)?;
        let thm = match (ia.fibre.as_ref(), ib.fibre.as_ref()) {
            (Some(fa), Some(fb)) => {
                let pre = self.pre.clone();
                dprod_ext_n(
                    &mut self.env_mut(),
                    &pre.ap,
                    &pre.fs,
                    (fa.b, fa.img, &fa.img_ax, ia.dprod, &fa.dprod_def),
                    (fb.b, fb.img, &fb.img_ax, ib.dprod, &fb.dprod_def),
                )
            }
            _ => None,
        };
        self.shared.borrow_mut().pi_exts.insert(key, Sealed::seal(thm.clone()));
        thm
    }

    /// `∀`-extensionality relating the two body *skeletons*, derived on first
    /// use and shared thereafter — [`Self::pi_ext_thm`] for the other clause.
    fn prop_ext_thm(&mut self, ka: &Term, kb: &Term) -> Option<Thm> {
        let key = (ka.clone(), kb.clone());
        if let Some(t) = self.shared.borrow().prop_exts.get(&key) {
            return t.clone()
        }
        let ia = self.prop_info(ka)?;
        let ib = self.prop_info(kb)?;
        let thm = match (ia.fibre.as_ref(), ia.chi_ax.as_ref(), ib.fibre.as_ref(), ib.chi_ax.as_ref()) {
            (Some((ba, _)), Some(axa), Some((bb, _)), Some(axb)) => {
                let pre = self.pre.clone();
                cond_ext_n(
                    &mut self.env_mut(),
                    &pre.tower.sums,
                    (*ba, ia.chi, axa),
                    (*bb, ib.chi, axb),
                )
            }
            _ => None,
        };
        self.shared.borrow_mut().prop_exts.insert(key, thm.clone());
        thm
    }

    /// `⊢ chi_C(h⃗,A) = chi_C'(q⃗,A')` — two `Prop`-valued `∀`s whose bodies have
    /// different shapes, related by [`cond_ext_n`].
    ///
    /// The mirror of [`Self::derive_pi_dprod_ext`], premise for premise: the
    /// domain equation is read off the domain certificate and the pointwise
    /// equation off the body certificate by the very same
    /// [`Self::pointwise_premise`], the conditional singleton's fibre playing
    /// the part the dependent product's fibre plays there.
    fn derive_prop_ext(
        &mut self,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        let (Some(sa), Some(sb)) = (self.prop_sites.get(&a), self.prop_sites.get(&b)) else {
            return Err("pi congruence: a ∀ has no conditional-singleton interpretation")
        };
        let (key_a, holes_a, dom_a) = (sa.key.clone(), sa.holes.clone(), sa.dom.clone());
        let (key_b, holes_b, dom_b) = (sb.key.clone(), sb.holes.clone(), sb.dom.clone());
        let (Some(info_a), Some(info_b)) = (self.prop_info(&key_a), self.prop_info(&key_b)) else {
            return Err("pi congruence: the ∀'s body skeleton was not registered")
        };
        let (Some((_, b_def_a)), Some((_, b_def_b))) = (info_a.fibre.as_ref(), info_b.fibre.as_ref())
        else {
            return Err("pi congruence: the ∀'s fibre was not built")
        };
        let (b_def_a, b_def_b) = (b_def_a.clone(), b_def_b.clone());

        let dom_thm = match dom {
            Some(d) if d.proves(&dom_a, &dom_b) => d.clone(),
            _ if dom_a == dom_b => CondEq::refl(dom_a.clone()),
            _ => return Err(pi_dom_gap(dom)),
        };
        let Some(body_thm) = body else { return Err("pi congruence over an admitted body premise") };
        let Some((pointwise, rest)) =
            self.pointwise_premise(&b_def_a, &b_def_b, &holes_a, &holes_b, &dom_a, body_thm)
        else {
            return Err("pi congruence: the body certificate is not the ∀ bodies' pointwise equation")
        };

        let Some(ext) = self.prop_ext_thm(&key_a, &key_b) else {
            return Err("pi congruence: ∀-extensionality could not be derived")
        };
        let mut args = holes_a;
        args.extend(holes_b);
        args.push(dom_a);
        args.push(dom_b);
        let Some(inst) = derived::inst_all(&ext, &args) else {
            return Err("pi congruence: instantiating ∀-extensionality failed")
        };

        // Both premises under the union of their assumptions; `pointwise` is not
        // an equation, so `Self::discharge` does not apply and the two `mp`s are
        // done by hand, exactly as in `derive_pi_dprod_ext`.
        let hyps = merge_hyps(&dom_thm.hyps, &rest);
        let h = conj_of(&hyps);
        let lemma = u_a1i(&inst, h.as_ref());
        let Some(dom_lifted) = reassume(&dom_thm.thm, &dom_thm.hyps, &hyps) else {
            return Err("pi congruence: re-stating the domain premise failed")
        };
        let Some(after_dom) = u_mp(&lemma, &dom_lifted, h.as_ref()) else {
            return Err("pi congruence: discharging the domain premise failed")
        };
        let Some(pw_lifted) = reassume(&pointwise, &rest, &hyps) else {
            return Err("pi congruence: re-stating the pointwise premise failed")
        };
        let Some(out) = u_mp(&after_dom, &pw_lifted, h.as_ref()) else {
            return Err("pi congruence: discharging the pointwise premise failed")
        };
        CondEq::new(out, hyps).ok_or("pi congruence: the result is not the assumed equation")
    }

    /// `⊢ ∀B ∀A. dprod(B,A) = fs(A,B)` at the constant-fibre skeleton — the
    /// interpreted arrow spelled as the library's function space. Derived once
    /// per thread and shared; see [`Shared::dprod_fs`].
    ///
    /// This is [`dprod_const_fibre_n`] with its constant-fibre hypothesis
    /// discharged outright: at the bare-hole skeleton the fibre's defining
    /// equation is `⊢ ∀B ∀x. b(B,x) = B` — a projection — so
    /// `∀x. (x ∈ A → b(B,x) = B)` is that axiom weakened by `a1i` and
    /// generalised, and the equation holds unconditionally, the empty domain
    /// included. The conclusion is compared against the statement above before
    /// it is generalised, so a mistake yields `None` and a reported gap, never
    /// a theorem about other terms.
    fn dprod_fs_eq(&mut self) -> Option<Thm> {
        if let Some(r) = self.shared.borrow().dprod_fs.clone() {
            return r.map(Sealed::into_thm)
        }
        let built = (|| {
            let h = self.hole_var(0);
            let sk = Term::var(h);
            // The constant-fibre skeleton's machinery — one table entry
            // corpus-wide, shared with `interp_pi`'s own registration.
            let info = match self.pi_info(&sk) {
                Some(i) => i,
                None => {
                    let info = match self.build_fibre(&sk, 1) {
                        Some((dprod, fb)) => Rc::new(PiInfo { dprod, fibre: Some(fb) }),
                        None => return None,
                    };
                    let mut sh = self.shared.borrow_mut();
                    sh.pi_infos.insert(sk.clone(), info.clone());
                    sh.pi_by_dprod.insert(info.dprod, (sk.clone(), info.clone()));
                    info
                }
            };
            let fb = info.fibre.as_ref()?;
            let pre = self.pre.clone();
            let bridge = dprod_const_fibre_n(
                &mut self.env_mut(),
                &pre.ap,
                &pre.fs,
                fb.b,
                fb.img,
                &fb.img_ax,
                info.dprod,
                &fb.dprod_def,
                &pre.fs_app_mem,
                &pre.fs_retarget,
            )?;
            let (vb, va, vx) = {
                let mut env = self.env_mut();
                (env.fresh_var(), env.fresh_var(), env.fresh_var())
            };
            let (tb, ta, tx) = (Term::var(vb), Term::var(va), Term::var(vx));
            // `∀x. (x ∈ A → b(B,x) = B)`, from the fibre's own defining
            // equation — checked to *be* the projection before it is used.
            let at_x = derived::inst_all(&fb.b_def, &[tb.clone(), tx.clone()])?;
            let want_ax =
                Formula::eq(Term::apply(fb.b, vec![tb.clone(), tx.clone()]), tb.clone());
            (*at_x.concl() == want_ax).then_some(())?;
            let guarded = derived::a1i(&at_x, Formula::mem(tx.clone(), ta.clone()));
            let family = derived::gen_all(&[vx], &guarded);
            let inst = derived::inst_all(&bridge, &[tb.clone(), ta.clone(), tb.clone()])?;
            let out = Thm::mp(&inst, &family)?;
            let want = Formula::eq(
                Term::apply(info.dprod, vec![tb.clone(), ta.clone()]),
                Term::apply(pre.fs_sym(), vec![ta, tb]),
            );
            (*out.concl() == want).then_some(())?;
            Some(derived::gen_all(&[vb, va], &out))
        })();
        self.shared.borrow_mut().dprod_fs = Some(Sealed::seal(built.clone()));
        built
    }

    /// From `⊢ subj ∈ fs(a,b)` — a library theorem stated over the function
    /// space — conclude `⊢ subj ∈ dprod(b,a)` at the constant-fibre skeleton,
    /// the term `⟦a → b⟧` now interprets to. One Leibniz step along
    /// [`Self::dprod_fs_eq`], run backwards; the claim is compared before it is
    /// returned.
    fn mem_at_dprod(&mut self, subj: &Term, a: &Term, b: &Term, mem_fs: &Thm) -> Option<(Term, Thm)> {
        let eq = self.dprod_fs_eq()?;
        let inst = derived::inst_all(&eq, &[b.clone(), a.clone()])?;
        let (dp, fs_t) = inst.concl().as_eq()?;
        (*mem_fs.concl() == Formula::mem(subj.clone(), fs_t.clone())).then_some(())?;
        let back = derived::eq_symm(&mut self.env_mut(), &inst)?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(fs_t, dp.clone(), w, Formula::mem(subj.clone(), Term::var(w)));
        let out = Thm::mp(&Thm::mp(&leib, &back)?, mem_fs)?;
        // Rebuilt through `mk` so the term's structure is on record for the
        // rules that will take the claim apart later.
        let (f, args) = dp.as_app()?;
        let dp = self.mk(f, args.to_vec());
        (*out.concl() == Formula::mem(subj.clone(), dp.clone())).then_some((dp, out))
    }

    /// [`retarget`] against this backend's record of term structure.
    fn retarget(&self, cert: &CondEq, want_l: &Term, want_r: &Term) -> Option<CondEq> {
        retarget_cond(&self.parts, cert, want_l, want_r)
    }

    /// One premise of `Π` congruence, as `⊢ l = r` under its assumptions.
    ///
    /// Three ways to get there, in order: the certificate already *is* that
    /// equation; it becomes that equation after [`Self::retarget`]; or the two
    /// sides interpret identically and reflexivity proves it outright. The last
    /// is the only one that survives an admitted certificate, and it is a
    /// complete proof rather than a shortcut.
    fn pi_premise(&mut self, c: Option<&CondEq>, l: &Term, r: &Term) -> Option<CondEq> {
        if let Some(t) = c {
            if t.proves(l, r) {
                return Some(t.clone())
            }
            if let Some(rt) = self.retarget(t, l, r) {
                return Some(rt)
            }
        }
        (l == r).then(|| CondEq::refl(l.clone()))
    }

    /// `⊢ ⟦Π x:A. b⟧ = ⟦Π x:A'. b'⟧`.
    ///
    /// Every `Type`-clause `Π` — dependent or not — interprets by a `dprod`
    /// whose head symbol is a property of the fibre's *shape*, the constant
    /// fibre being the degenerate shape at the bare-hole skeleton. So there are
    /// two cases: the same `dprod` — congruence over its arguments, the fibre's
    /// abstracted subterms followed by the domain — and two *different*
    /// `dprod`s, related by dependent-product Extensionality
    /// ([`Self::derive_pi_dprod_ext`]). Two spellings of one arrow that used to
    /// land in different clauses (`fs` against `dprod`, `dep = has_bvar` being
    /// β-unstable) now land in the second case, where `dprod_ext_n` relates
    /// them; there is no bridge theorem because there are no longer two
    /// interpretation spellings to bridge.
    ///
    /// Ahead of both: two **`Prop`-valued `∀`s**, §6.2's other clause. Over the
    /// same body skeleton that is plain congruence on the shared
    /// conditional-singleton symbol, whose arguments are laid out exactly as a
    /// dependent product's — the skeleton's holes, then the domain — so
    /// [`Self::derive_pi_argwise`] serves both; over differently shaped bodies
    /// the symbols are unrelated and what settles it is
    /// [`Self::derive_prop_ext`], the same split for the same reason.
    fn derive_pi_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        if !matches!((ctx.read_expr(a), ctx.read_expr(b)), (Expr::Pi { .. }, Expr::Pi { .. })) {
            return Err("pi congruence: not applied to two Π types")
        }
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        // Read the two premises' targets straight off the *claim* rather than
        // re-interpreting the two sub-expressions. Those agree today, but this
        // way the premises are by construction about the terms the conclusion
        // will be compared against, so the rule cannot drift from its guard.
        let (Some((fa, aargs)), Some((fb, bargs))) = (self.parts.get(&ta).cloned(), self.parts.get(&tb).cloned())
        else {
            return Err("pi congruence: a Π has no applicative interpretation")
        };
        // A `Π` under neither clause. Its symbol has no axioms, so the only
        // thing available is plain congruence over it, and only when both sides
        // are the same shape. Everything else about such a term is a gap by
        // construction — see [`Clause::Undet`].
        let (ua, ub) = (self.undet_sites.contains_key(&a), self.undet_sites.contains_key(&b));
        if ua || ub {
            // Exactly one side undetermined is a **classification
            // disagreement**: the two `Π`s are `def_eq`, so their sorts are
            // too, and one of the two answers is this approximation's fault
            // rather than the level algebra's. Named apart from the honest case
            // so that it can be held at zero.
            if ua != ub {
                return Err("pi congruence: one Π of undetermined sort and one decided")
            }
            if fa != fb {
                return Err("pi congruence: two Πs of undetermined sort over differently shaped bodies")
            }
            return self.derive_pi_argwise(fa, &aargs, &bargs, dom, body)
        }
        // Two `Prop`-valued `∀`s. `⟦∀x:A. β⟧` is `chi_C(h⃗,A)` and the arguments
        // are the body skeleton's holes followed by the domain, so this is the
        // dependent product's argument-wise congruence at a different symbol.
        if self.prop_sites.contains_key(&a) && self.prop_sites.contains_key(&b) {
            if fa == fb {
                if let Ok(t) = self.derive_pi_argwise(fa, &aargs, &bargs, dom, body) {
                    return Ok(t)
                }
            }
            return self.derive_prop_ext(a, b, dom, body)
        }
        // One of each clause. Nothing relates a subset of `{•}` to a function
        // space, and nothing should: the two sides are interpreted by different
        // clauses because the syntactic sort approximation split them, and a
        // rule that bridged them would be relating terms the model does not.
        if self.prop_sites.contains_key(&a) != self.prop_sites.contains_key(&b) {
            return Err("pi congruence: one ∀ and one Π — the two clauses of §6.2")
        }
        // Two dependent products: congruence over the shared head symbol when
        // the two bodies have the same shape, and Extensionality otherwise —
        // exactly the split `lam_cong` makes, and for the same reason.
        if self.pi_sites.contains_key(&a) && self.pi_sites.contains_key(&b) {
            if fa == fb {
                if let Ok(t) = self.derive_pi_argwise(fa, &aargs, &bargs, dom, body) {
                    return Ok(t)
                }
            }
            return self.derive_pi_dprod_ext(a, b, dom, body)
        }
        // Neither side registered a dependent-product site, so at least one
        // interpretation fell back to the opaque `pi` symbol — a bug degraded
        // into a gap, per `interp_pi`. Plain congruence over the shared symbol
        // is all the signature supports.
        if fa != fb {
            return Err("pi congruence: a Π has no dependent-product interpretation")
        }
        if fa == self.syms.pi {
            // Binary, domain then the raw body.
            if aargs.len() != 2 || bargs.len() != 2 {
                return Err("pi congruence: a Π interprets to an unexpected arity")
            }
            let (ia, ja) = (aargs[0].clone(), aargs[1].clone());
            let (ib, jb) = (bargs[0].clone(), bargs[1].clone());
            let dom_thm = self.pi_premise(dom, &ia, &ib).ok_or(pi_dom_gap(dom))?;
            let body_thm = self.pi_premise(body, &ja, &jb).ok_or(pi_body_gap(body))?;
            return self.ceq_congr(fa, &[dom_thm, body_thm]).ok_or("pi congruence: congruence rule refused")
        }
        Err("pi congruence: a Π interprets to an unexpected head symbol")
    }

    /// Congruence over a dependent product's arguments — the abstracted,
    /// binder-free subterms of the body followed by the binder's domain.
    ///
    /// The cheap route when the two `Π` types differ only in those positions: no
    /// Extensionality derivation is needed, and on this corpus the arguments are
    /// usually literally equal, so most positions are reflexivity.
    fn derive_pi_argwise(
        &mut self,
        f: FnSym,
        aargs: &[Term],
        bargs: &[Term],
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        if aargs.len() != bargs.len() || aargs.is_empty() {
            return Err("pi congruence: a Π interprets to an unexpected arity")
        }
        let last = aargs.len() - 1;
        let mut prems = Vec::with_capacity(aargs.len());
        for i in 0..aargs.len() {
            let c = if i == last { dom } else { body };
            let Some(p) = self.pi_premise(c, &aargs[i], &bargs[i]) else {
                return Err(if i == last { pi_dom_gap(dom) } else { pi_body_gap(body) })
            };
            prems.push(p);
        }
        self.ceq_congr(f, &prems).ok_or("pi congruence: congruence rule refused")
    }

    /// `⊢ dprod_C(h⃗,A) = dprod_C'(h⃗',A')`, by dependent-product extensionality.
    ///
    /// The mirror of [`Self::derive_lam_cong`], and for the same reason: the
    /// head symbol of `⟦Π⟧` depends on the *shape* of the fibre, so two `Π`
    /// types with differently-shaped bodies are built by unrelated symbols and
    /// no amount of `congr_arg` relates them. What does is that the two products
    /// have the same members — [`dprod_ext_n`] — whose pointwise premise is read
    /// off the body certificate by the very same [`Self::pointwise_premise`] the
    /// lambda rule uses, the fibre's defining equation playing the part of the
    /// graph body's.
    fn derive_pi_dprod_ext(
        &mut self,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        let (Some(sa), Some(sb)) = (self.pi_sites.get(&a), self.pi_sites.get(&b)) else {
            return Err("pi congruence: a Π has no dependent-product interpretation")
        };
        let (key_a, holes_a, dom_a) = (sa.key.clone(), sa.holes.clone(), sa.dom.clone());
        let (key_b, holes_b, dom_b) = (sb.key.clone(), sb.holes.clone(), sb.dom.clone());
        let (Some(info_a), Some(info_b)) = (self.pi_info(&key_a), self.pi_info(&key_b)) else {
            return Err("pi congruence: the Π's fibre skeleton was not registered")
        };
        let (Some(fa), Some(fb)) = (info_a.fibre.as_ref(), info_b.fibre.as_ref()) else {
            return Err("pi congruence: the Π's fibre was not built")
        };
        let (b_def_a, b_def_b) = (fa.b_def.clone(), fb.b_def.clone());

        let dom_thm = match dom {
            Some(d) if d.proves(&dom_a, &dom_b) => d.clone(),
            _ if dom_a == dom_b => CondEq::refl(dom_a.clone()),
            _ => return Err(pi_dom_gap(dom)),
        };
        let Some(body_thm) = body else { return Err("pi congruence over an admitted body premise") };
        let Some((pointwise, rest)) =
            self.pointwise_premise(&b_def_a, &b_def_b, &holes_a, &holes_b, &dom_a, body_thm)
        else {
            return Err("pi congruence: the body certificate is not the fibres' pointwise equation")
        };

        let Some(ext) = self.pi_ext_thm(&key_a, &key_b) else {
            return Err("pi congruence: dependent-product extensionality could not be derived")
        };
        let mut args = holes_a;
        args.extend(holes_b);
        args.push(dom_a);
        args.push(dom_b);
        let Some(inst) = derived::inst_all(&ext, &args) else {
            return Err("pi congruence: instantiating dependent-product extensionality failed")
        };

        // Both premises under the union of their assumptions; `pointwise` is not
        // an equation, so `Self::discharge` does not apply and the two `mp`s are
        // done by hand, exactly as in `derive_lam_cong`.
        let hyps = merge_hyps(&dom_thm.hyps, &rest);
        let h = conj_of(&hyps);
        let lemma = u_a1i(&inst, h.as_ref());
        let Some(dom_lifted) = reassume(&dom_thm.thm, &dom_thm.hyps, &hyps) else {
            return Err("pi congruence: re-stating the domain premise failed")
        };
        let Some(after_dom) = u_mp(&lemma, &dom_lifted, h.as_ref()) else {
            return Err("pi congruence: discharging the domain premise failed")
        };
        let Some(pw_lifted) = reassume(&pointwise, &rest, &hyps) else {
            return Err("pi congruence: re-stating the pointwise premise failed")
        };
        let Some(out) = u_mp(&after_dom, &pw_lifted, h.as_ref()) else {
            return Err("pi congruence: discharging the pointwise premise failed")
        };
        CondEq::new(out, hyps).ok_or("pi congruence: the result is not the assumed equation")
    }

    /// `⊢ ⟦λx:A. b⟧ = ⟦λx:A'. b'⟧`, by graph extensionality.
    fn derive_lam_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        dom: Option<&CondEq>,
        body: Option<&CondEq>,
    ) -> Result<CondEq, &'static str> {
        // Interpreting the two lambdas is what registers their graph symbols —
        // or records that they are proofs and have none.
        let _ = self.interp(ctx, a);
        let _ = self.interp(ctx, b);
        // §6.2's two clauses for `λ`. Two proof lambdas are both `•`, so the
        // equation is reflexivity and there is no premise to want. Exactly one
        // is a **classification disagreement**: the two lambdas are `def_eq`, so
        // their sorts are too, and one of the two answers is
        // [`Self::term_clause`]'s fault. Named apart so it can be held at zero.
        let (pa, pb) = (self.prop_lam_sites.contains_key(&a), self.prop_lam_sites.contains_key(&b));
        if pa != pb {
            return Err("lam congruence: one proof λ and one Λ — the two clauses of §6.2")
        }
        if pa {
            return Ok(CondEq::refl(self.pre.point()))
        }
        let (Some(sa), Some(sb)) = (self.lam_sites.get(&a), self.lam_sites.get(&b)) else {
            return Err("lam congruence: a lambda has no function-graph interpretation")
        };
        let (key_a, holes_a, dom_a) = (sa.key.clone(), sa.holes.clone(), sa.dom.clone());
        let (key_b, holes_b, dom_b) = (sb.key.clone(), sb.holes.clone(), sb.dom.clone());

        let Some(info_a) = self.lam_info(&key_a) else {
            return Err("lam congruence: the lambda's skeleton was not registered")
        };
        let Some(info_b) = self.lam_info(&key_b) else {
            return Err("lam congruence: the lambda's skeleton was not registered")
        };
        let (Some(ga), Some(gb)) = (info_a.graph.as_ref(), info_b.graph.as_ref()) else {
            return Err("lam congruence: the lambda's graph was not built")
        };
        let (t_def_a, t_def_b) = (ga.t_def.clone(), gb.t_def.clone());

        // The domain premise. The certificate the checker handed down is the
        // right one when it proves the two binder types equal; when the types
        // interpret identically, reflexivity does the job instead — which is
        // the only way a gapped domain certificate can still be rescued.
        let dom_thm = match dom {
            Some(d) if d.proves(&dom_a, &dom_b) => d.clone(),
            _ if dom_a == dom_b => CondEq::refl(dom_a.clone()),
            _ => return Err("lam congruence: the domain certificate does not match the binder types"),
        };

        let Some(body_thm) = body else {
            return Err("lam congruence over an admitted premise")
        };
        let Some((pointwise, rest)) =
            self.pointwise_premise(&t_def_a, &t_def_b, &holes_a, &holes_b, &dom_a, body_thm)
        else {
            return Err("lam congruence: the body certificate is not the graphs' pointwise equation")
        };
        // `pointwise` is `⊢ conj(rest) → ∀x. …`, whose consequent is not an
        // equation — so it cannot be a `CondEq`, and `Self::discharge` (which
        // returns one) does not apply. The two premises are discharged by hand
        // below with the same `reassume`/`u_mp` moves.

        let Some(ext) = self.lam_ext_thm(&key_a, &key_b) else {
            return Err("lam congruence: graph extensionality could not be derived")
        };
        let mut args = holes_a;
        args.extend(holes_b);
        args.push(dom_a);
        args.push(dom_b);
        let Some(inst) = derived::inst_all(&ext, &args) else {
            return Err("lam congruence: instantiating graph extensionality failed")
        };

        // Both premises are discharged under the union of their assumptions:
        // the domain equation's, and whatever the pointwise premise could not
        // shed at the binder.
        let hyps = merge_hyps(&dom_thm.hyps, &rest);
        let h = conj_of(&hyps);
        let lemma = u_a1i(&inst, h.as_ref());
        let Some(dom_lifted) = reassume(&dom_thm.thm, &dom_thm.hyps, &hyps) else {
            return Err("lam congruence: re-stating the domain premise failed")
        };
        let Some(after_dom) = u_mp(&lemma, &dom_lifted, h.as_ref()) else {
            return Err("lam congruence: discharging the domain premise failed")
        };
        let Some(pw_lifted) = reassume(&pointwise, &rest, &hyps) else {
            return Err("lam congruence: re-stating the pointwise premise failed")
        };
        // This is the step that would fail if the generalisation above had
        // captured a parameter: the premise would not be the lemma's.
        let Some(out) = u_mp(&after_dom, &pw_lifted, h.as_ref()) else {
            return Err("lam congruence: discharging the pointwise premise failed")
        };
        CondEq::new(out, hyps).ok_or("lam congruence: the result is not the assumed equation")
    }
}

/// Why a `Π` congruence could not use its domain premise: the certificate below
/// was itself a gap, or it was about the wrong terms. Naming the two apart is
/// what makes the coverage report say which is missing.
fn pi_dom_gap(c: Option<&CondEq>) -> &'static str {
    if c.is_none() {
        "pi congruence over an admitted domain premise"
    } else {
        "pi congruence: the domain certificate is not about the binder types"
    }
}

/// [`pi_dom_gap`] for the body premise.
fn pi_body_gap(c: Option<&CondEq>) -> &'static str {
    if c.is_none() {
        "pi congruence over an admitted body premise"
    } else {
        "pi congruence: the body certificate is not about the binder bodies"
    }
}

/// The applicative structure of the terms a match may take apart: the shape
/// [`TgBackend::parts`] records on the way in.
type Parts = HashMap<Term, (FnSym, Vec<Term>)>;

/// `f(args)`, with its applicative structure remembered in `parts`.
///
/// The first recording of a term wins: the same term built twice has the same
/// structure, so a later insertion could only be redundant.
fn record(parts: &mut Parts, f: FnSym, args: Vec<Term>) -> Term {
    let t = Term::apply(f, args.clone());
    parts.entry(t.clone()).or_insert((f, args));
    t
}

/// The skeleton decomposition **through a recording table** — `derived`'s, as
/// it stood before `Term::as_app` existed, kept here because this backend's
/// frontier counters are calibrated to it.
///
/// `None` when a subterm mentioning `v` was not passed through [`record`]. That
/// is not a property of the term; it is a property of who built it, and
/// `derived::skeleton`'s header says what believing otherwise cost. Retiring
/// this in favour of the total decomposition is a one-line change plus a
/// re-baseline of five assertions in `checker/tests/tg_tutorial.rs`, and it
/// would let [`TgBackend::parts`] — the same table `PRELUDE-COST.md` §3.2
/// measured at 54 % of `mini`'s live heap — go away here too.
fn skeleton_recorded(
    parts: &mut Parts,
    x_canon: FreeVar,
    hole_var: &mut dyn FnMut(usize) -> FreeVar,
    t: &Term,
    v: FreeVar,
    holes: &mut Vec<Term>,
) -> Option<Term> {
    if !t.occurs_free(v) {
        let h = hole_var(holes.len());
        holes.push(t.clone());
        return Some(Term::var(h))
    }
    if *t == Term::var(v) {
        return Some(Term::var(x_canon))
    }
    let (f, args) = parts.get(t)?.clone();
    let mut out = Vec::with_capacity(args.len());
    for a in &args {
        out.push(skeleton_recorded(parts, x_canon, hole_var, a, v, holes)?);
    }
    // Through `record`, so that the skeleton's own structure is recorded too.
    Some(record(parts, f, out))
}

/// Match `have` against `want`, reading off which free variables of `have` have
/// to become which subterms of `want`.
///
/// A pure syntactic first-order match, one-sided: only `have`'s free variables
/// are treated as holes, and a variable bound twice to different terms fails.
/// Interior nodes are compared through `parts`, so a term the backend did not
/// build stops the match rather than being taken apart by guesswork.
fn match_term(parts: &Parts, have: &Term, want: &Term, subst: &mut Vec<(FreeVar, Term)>) -> Option<()> {
    if have == want {
        return Some(())
    }
    if let Some((f, hargs)) = parts.get(have) {
        let (g, wargs) = parts.get(want)?;
        if f != g || hargs.len() != wargs.len() {
            return None
        }
        for (h, w) in hargs.iter().zip(wargs.iter()) {
            match_term(parts, h, w, subst)?;
        }
        return Some(())
    }
    // Not an application the backend built, so the only thing it can be and
    // still match is a free variable standing for a whole subterm.
    let mut fvs = Vec::new();
    have.free_vars(&mut fvs);
    if fvs.len() != 1 || *have != Term::var(fvs[0]) {
        return None
    }
    let v = fvs[0];
    match subst.iter().find(|(u, _)| *u == v) {
        Some((_, t)) => (t == want).then_some(()),
        None => {
            subst.push((v, want.clone()));
            Some(())
        }
    }
}

/// Re-aim a certificate from the *opened* form of a binder body at the raw
/// de Bruijn form that `⟦Π⟧` is built over.
///
/// The checker compares binder bodies after instantiating them at locals, so
/// the certificate it hands `pi_cong` is about `⟦B[l⃗]⟧`, with `l⃗` kernel free
/// variables — whereas `⟦Π x:A. B⟧` is `sym(⟦A⟧, ⟦B⟧)` over the *raw* body, in
/// which those positions are `bvar` symbols instead. The two are related by
/// exactly the rule a free variable admits: generalise it, then instantiate at
/// the term wanted in its place. Generalisation carries a side condition — the
/// local must not be free in the theorem's hypotheses — so this uses
/// [`kernel::Thm::gen_checked`] and lets a violation become a `None`, hence a
/// counted gap; see `TgBackend::pointwise_premise` for why the panicking
/// `Thm::gen` is not used anywhere in this crate. `ax_inst` is the kernel's own
/// instantiation, so the result is a genuine theorem about the wanted terms.
///
/// Which term goes in which variable's place is *read off* by matching the
/// certificate against the wanted equation rather than guessed, and the outcome
/// is compared against that equation before it is returned. So the worst a
/// mismatch can do — a shifted de Bruijn index under a nested `Π`, a body the
/// backend did not build, one local that would have to become two different
/// terms — is produce `None`, hence a reported gap.
///
/// A certificate that carries assumptions is re-aimed the same way, except that
/// generalising and re-instantiating rewrites the *assumptions* too — so they
/// are substituted alongside, and `CondEq::new` re-checks that the rewritten
/// list really is the rewritten theorem's antecedent.
fn retarget_cond(parts: &Parts, cert: &CondEq, want_l: &Term, want_r: &Term) -> Option<CondEq> {
    let (have_l, have_r) = cert.as_eq()?;
    let mut subst: Vec<(FreeVar, Term)> = Vec::new();
    match_term(parts, &have_l, want_l, &mut subst)?;
    match_term(parts, &have_r, want_r, &mut subst)?;
    if subst.is_empty() {
        // Nothing to re-aim, and the caller has already compared the
        // certificate verbatim; going on would only re-derive what it has.
        return None
    }
    let mut cur = cert.thm.clone();
    let mut hyps = cert.hyps.clone();
    for (v, t) in subst {
        cur = derived::inst_all(&Thm::gen_checked(v, &cur)?, std::slice::from_ref(&t))?;
        hyps = hyps.iter().map(|f| f.subst(v, &t)).collect();
    }
    // The guard. Nothing above is trusted to have produced the right equation,
    // and `CondEq::new` re-checks that the assumptions really are the theorem's
    // antecedent after the rewrite.
    let out = CondEq::new(cur, hyps)?;
    out.proves(want_l, want_r).then_some(out)
}

/// [`retarget_cond`] for a certificate that assumes nothing.
#[cfg(test)]
fn retarget(parts: &Parts, cert: &Thm, want_l: &Term, want_r: &Term) -> Option<Thm> {
    let c = CondEq::plain(cert.clone())?;
    Some(retarget_cond(parts, &c, want_l, want_r)?.thm)
}

/// The key of [`TgBackend::locals`] — which Lean local a kernel free variable
/// stands for. See the field's doc for the full argument; in brief:
///
/// * A **`Level`** local is a binder open — the checker's own telescopes, and
///   since 2026-08-09 the interpretation's too
///   ([`TgBackend::interp_lambda`]/[`TgBackend::interp_pi`] open at the
///   expression-derived level [`TgBackend::open_level`] computes). The
///   checker's levels are stack positions [`TcCtx::replace_dbj_level`] hands
///   back on close, so the level alone recurs at unrelated binders and the
///   interpreted declared type completes the identity: same level and type — the same variable, and nothing left
///   to differ in (which is what lets an identical binder shape reuse its
///   variable and every memoised statement about it); different type — a
///   different variable, so no memoised statement can cross.
/// * A **`Unique`** local's id is never reused within a `TcCtx`
///   (`util.rs`'s monotonic counter), so the id alone already identifies the
///   binder opening it stands for. Its type is deliberately *not* part of the
///   key: the recursive-field reservations ([`TgBackend::walk_spec`]) must
///   reserve a variable for a binder whose type is never interpreted at all,
///   and [`TgBackend::rec_nest`] reserves variables that must match a nest
///   *stored by another declaration's backend* — an identity no
///   `(level, type)` key can transport, which is why its positional
///   `cached.vars` hint plus the [`nest_agrees`] claim-check stays.
///
/// The two variants are distinct constructors, so the halves of the key space
/// cannot alias — the property the old `(1 << 32)` bit encoded.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum LocalKey {
    Level(u16, Term),
    Unique(u32),
}

/// The [`TgBackend::locals`] key for a **`mk_unique`** local. `None` on
/// anything else — in particular on a de Bruijn-level local, whose key needs
/// the interpreted type and is built where the interpretation is at hand.
fn unique_key<'t, 'p>(ctx: &TcCtx<'t, 'p>, e: ExprPtr<'t>) -> Option<LocalKey> {
    match ctx.read_expr(e) {
        Expr::Local { id: crate::expr::FVarId::Unique(n), .. } => Some(LocalKey::Unique(n)),
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The typing judgement, carried by inference.
//
// `has_type` is a *search*: given a term and a target, it recurses down the
// term looking for a rule that fits. That search exists because `infer` used to
// return a type and nothing else, so the fact `⟦e⟧ ∈ ⟦T⟧` — established by the
// very recursion that computed `T` — had to be rediscovered afterwards. On
// `init-prelude` that was 1645 searches, of which 1633 failed, for 36% of the
// runtime.
//
// The rules below are the same typing rules, driven the other way round: each
// is handed the premises inference has *already* computed and does no search
// and no recursion of its own. They share `has_type`'s machinery — the graph
// skeletons, the dependent product's characteristic property, the discharge at
// a binder — and its discipline: a rule checks its result against the judgement
// being claimed, and a mismatch is a counted gap, never a theorem.
//
// The two coexist deliberately. `has_type` still serves the obligations that
// arise *inside* a definitional-equality derivation (`beta`'s domain premise),
// where there is no inference in progress to ask.
// ─────────────────────────────────────────────────────────────────────────────

/// A typing certificate: `⊢ conj(hyps) → ⟦e⟧ ∈ ⟦ty⟧`, or a named gap.
///
/// Shaped like [`TgCert`] and for the same reasons — a gap is a *variant*, so
/// an unjustified typing propagates visibly instead of being forged or
/// refused — with one difference. There is no separate `Proved`/`Conditional`
/// split: a typing's assumptions are always memberships about the ambient
/// locals, they are discharged by exactly one rule ([`Certifier::ty_lam`]), and
/// the only place the difference matters is whether the declaration typing may
/// be stored. So `hyps.is_empty()` carries that distinction and nothing else
/// needs to branch on it.
#[derive(Debug, Clone)]
pub enum TgTyping {
    /// `⊢ conj(hyps) → ⟦e⟧ ∈ ⟦ty⟧`, checked on construction to be exactly that.
    Derived {
        /// The theorem, literally the implication (or the bare membership when
        /// `hyps` is empty).
        thm: Thm,
        /// The assumptions, in the order the left-nested conjunction puts them.
        hyps: Vec<Formula>,
    },
    /// No evidence, tagged with why. See [`crate::certify::TyGap`].
    Gap(&'static str),
}

impl TgTyping {
    /// No evidence at all. The inference rules use this to short-circuit: a rule
    /// whose premise is a hole concludes nothing, so the terms it would
    /// otherwise have to build are not built.
    pub fn is_gap(&self) -> bool { matches!(self, TgTyping::Gap(_)) }
}

impl<'x, 't: 'x, 'p: 't> TgBackend<'x, 't, 'p> {
    /// Every kernel free variable the backend has minted for a Lean local
    /// **occurring in `e`**, following each local into its own binder type.
    ///
    /// The transitive step is the whole point. `⟦w⟧` is an opaque variable that
    /// does not carry its type, so `FV(⟦e⟧)` misses the locals that appear only
    /// inside the *declared types* of `e`'s locals — and those are exactly the
    /// ones a `has_type_local` assumption `⟦w⟧ ∈ ⟦A⟧` can mention. The Lean
    /// `ExprPtr` that keys the memo does contain them (a `Local` node is hashed
    /// over its `binder_type`), so they are part of what the key distinguishes,
    /// and the memo's written premise is about the *expression*, not about its
    /// interpretation.
    fn locals_of(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        out: &mut Vec<FreeVar>,
        seen: &mut Vec<ExprPtr<'t>>,
    ) {
        if seen.contains(&e) {
            return
        }
        seen.push(e);
        match ctx.read_expr(e) {
            Expr::Local { binder_type, id, .. } => {
                // A level local's key contains its interpreted type. Read that
                // from the interpretation memo rather than interpreting here:
                // any local that *has* a variable had its declared type
                // interpreted when the variable was minted (the `Local` arm
                // does so for the key), so an `exprs` miss means there is no
                // variable to collect — and this walk stays a read, minting
                // nothing.
                let key = match id {
                    crate::expr::FVarId::Unique(n) => Some(LocalKey::Unique(n)),
                    crate::expr::FVarId::DbjLevel(n) =>
                        self.exprs.get(&binder_type).map(|ty| LocalKey::Level(n, ty.clone())),
                };
                if let Some(k) = key {
                    if let Some(v) = self.locals.get(&k) {
                        out.push(*v);
                    }
                }
                self.locals_of(ctx, binder_type, out, seen);
            }
            Expr::App { fun, arg, .. } => {
                self.locals_of(ctx, fun, out, seen);
                self.locals_of(ctx, arg, out, seen);
            }
            Expr::Lambda { binder_type, body, .. } | Expr::Pi { binder_type, body, .. } => {
                self.locals_of(ctx, binder_type, out, seen);
                self.locals_of(ctx, body, out, seen);
            }
            Expr::Let { binder_type, val, body, .. } => {
                self.locals_of(ctx, binder_type, out, seen);
                self.locals_of(ctx, val, out, seen);
                self.locals_of(ctx, body, out, seen);
            }
            Expr::Proj { structure, .. } => self.locals_of(ctx, structure, out, seen),
            _ => {}
        }
    }

    /// Record a gap and return it.
    fn ty_miss(&mut self, g: crate::certify::TyGap) -> TgTyping {
        note_ty_gap(g);
        TgTyping::Gap(g.name())
    }

    /// Package a derivation as a typing certificate — **after checking it
    /// concludes the membership being claimed**.
    ///
    /// This is the single exit from every rule below, and it is the same guard
    /// [`Self::has_type_a`] has: a derivation that came out about some other
    /// pair of terms is a gap, not a certificate. Five soundness bugs on this
    /// project were caught by guards of exactly this shape.
    fn typing(
        &mut self,
        by: crate::certify::TyGap,
        te: &Term,
        ty: &Term,
        thm: Thm,
        hyps: Vec<Formula>,
    ) -> TgTyping {
        let want = Formula::mem(te.clone(), ty.clone());
        match u_concl(&thm, conj_of(&hyps).as_ref()) {
            Some(c) if c == want => {
                note_ty_out(by, hyps.is_empty());
                TgTyping::Derived { thm, hyps }
            }
            _ => self.ty_miss(crate::certify::TyGap::Claim),
        }
    }

    /// The two halves of a typing premise, or `None` if it is a hole.
    fn ty_parts(t: &TgTyping) -> Option<(Thm, Vec<Formula>)> {
        match t {
            TgTyping::Derived { thm, hyps } => Some((thm.clone(), hyps.clone())),
            TgTyping::Gap(_) => None,
        }
    }

    /// `⊢ conj(hyps) → ⟦e⟧ ∈ tgt` from a derivation stated at `src`, when `src`
    /// unfolds to `tgt` along the interpretation's own defining equations.
    ///
    /// This is [`Self::has_type_pi`]'s bridge, factored out: inference reads a
    /// function's type off the syntax, and the `Π` it eliminates may be reached
    /// only after unfolding a defined name. Nothing merely *definitionally*
    /// equal will do — [`Self::unfolds_to`] is a chain of real equations.
    fn ty_bridge(&mut self, te: &Term, src: &Term, tgt: &Term, thm: &Thm, hyps: &[Formula]) -> Option<Thm> {
        if src == tgt {
            return Some(thm.clone())
        }
        let eq = self.unfolds_to(src, tgt)?;
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(src.clone(), tgt.clone(), w, Formula::mem(te.clone(), Term::var(w)));
        let step = Thm::mp(&leib, &eq)?;
        let h = conj_of(hyps);
        u_mp(&u_a1i(&step, h.as_ref()), thm, h.as_ref())
    }

    /// The body of the application rule, once both premises are in hand:
    /// `app(f,a) ∈ B` from `f ∈ ⟦Π A B⟧` and `a ∈ ⟦A⟧`.
    ///
    /// The two cases are [`Self::has_type_app`]'s, and for the same reasons: a
    /// target a `derived` theorem stated over `fs`, whose values lie in its
    /// codomain; an interpreted `Π`, always the dependent product, whose
    /// characteristic property *is* `∀x ∈ A. app(f,x) ∈ b(x)`.
    #[allow(clippy::too_many_arguments)]
    fn ty_app_from(
        &mut self,
        fty: ExprPtr<'t>,
        fty_t: &Term,
        dom_t: &Term,
        tf: &Term,
        ta: &Term,
        hf: &Thm,
        ha: &Thm,
        used: &[Formula],
    ) -> Option<Thm> {
        let hyp = conj_of(used);
        if let Some((f, args)) = self.parts.get(fty_t).cloned() {
            if f == self.pre.fs_sym() && args.len() == 2 && args[0] == *dom_t {
                let lem = self.pre.fs_app_mem.clone();
                return app_in_codomain(&lem, dom_t, &args[1], tf, ta, hf, ha, hyp.as_ref())
            }
        }
        let site = self.pi_sites.get(&fty)?;
        let (skel, holes, pdom) = (site.key.clone(), site.holes.clone(), site.dom.clone());
        if pdom != *dom_t {
            return None
        }
        let info = self.pi_info(&skel)?;
        let fb = info.fibre.as_ref()?;
        let (dprod_def, b_def) = (fb.dprod_def.clone(), fb.b_def.clone());
        let app = self.pre.ap.app;
        app_in_fibre(
            &mut self.env_mut(),
            app,
            &dprod_def,
            &b_def,
            &holes,
            &pdom,
            tf,
            ta,
            hf,
            ha,
            hyp.as_ref(),
        )
    }
}

impl<'x, 't: 'x, 'p: 't> Certifier<'t, 'p> for TgBackend<'x, 't, 'p> {
    type Cert = TgCert;
    type Typing = TgTyping;

    fn ty_gap(
        &mut self,
        _ctx: &mut TcCtx<'t, 'p>,
        _e: ExprPtr<'t>,
        _ty: ExprPtr<'t>,
        reason: &'static str,
    ) -> TgTyping {
        note_ty_gap_named(reason);
        TgTyping::Gap(reason)
    }

    /// Are the typing's hypotheses and conclusion confined to the free variables
    /// of `⟦e⟧` and `⟦ty⟧`?
    ///
    /// The premise the two inference memos are keyed on. See
    /// [`Certifier::typing_is_confined`] for why it is asked and why the answer
    /// is only consumed by a `debug_assert`.
    ///
    /// A `Gap` carries nothing, so it is confined vacuously and — importantly —
    /// without interpreting anything: the check must not be the reason a
    /// definitional extension gets built. A `Derived` typing has already had
    /// both `⟦e⟧` and `⟦ty⟧` built by the rule that produced it, so the two
    /// `interp` calls below are memo hits.
    fn typing_is_confined(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        t: &TgTyping,
    ) -> bool {
        let TgTyping::Derived { thm, hyps } = t else { return true };
        if hyps.is_empty() && thm.hyps().is_empty() {
            return true
        }
        let mut allowed: Vec<FreeVar> = Vec::new();
        self.locals_of(ctx, e, &mut allowed, &mut Vec::new());
        self.locals_of(ctx, ty, &mut allowed, &mut Vec::new());
        let mut seen: Vec<FreeVar> = Vec::new();
        for h in hyps.iter().chain(thm.hyps()) {
            h.free_vars(&mut seen);
        }
        // A parameter's ω-variable is confined by *name*, not by context: the
        // same `u` in the same declaration reaches the same variable wherever
        // the memoised expression recurs, so an assumption `u ∈ ω` recalls
        // correctly under any context — the property the locals check asserts
        // occurrence-by-occurrence, held here by construction instead.
        seen.iter().all(|v| allowed.contains(v) || self.is_param_omega_var(*v))
    }

    /// `⟦Π A B⟧ ∈ ⟦Sort (imax u v)⟧`, as far as the *term-level* facts reach.
    ///
    /// Deliberately **not** the `has_type` search. Interpreting a `Π` builds a
    /// fibre — a Replacement derivation — per skeleton, and there are 5801 of
    /// these sites on `init-prelude`; running the full recursion at each is the
    /// same shape of mistake as the typing search `store_declar_typing` used to
    /// do, which cost 36% of the run for 12 hits. So this asks
    /// [`Self::domain_premise`], which is closed, term-level and non-recursive,
    /// and reports an honest gap otherwise.
    fn ty_pi(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        which: crate::certify::TyGap,
    ) -> TgTyping {
        let (te, tt) = (self.interp(ctx, e), self.interp(ctx, ty));
        // The `Prop` clause is not a harder instance of the `Type` one, and it
        // is not `domain_premise`'s business: `⟦∀…⟧` is a conditional singleton
        // and `⟦Prop⟧` is `U₀`, so the obligation is exactly
        // `⊢ [φ] ∈ U₀` — [`derived::tower::Tower::cond_in_u0`], at this
        // skeleton. It falls out where the term was built, which is why it is
        // asked first and not left to the general search.
        if which == crate::certify::TyGap::PiProp {
            if let Some(t) = self.prop_in_u0(&te, &tt) {
                return self.typing(which, &te, &tt, t, Vec::new())
            }
        }
        match self.domain_premise(&te, &tt) {
            Some(t) => self.typing(which, &te, &tt, t, Vec::new()),
            None => self.ty_miss(which),
        }
    }

    /// `⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧`, which the interpretation makes
    /// `x ∈ U(x)` — [`Self::domain_premise`]'s first branch, at one instance.
    ///
    /// At a level the σ-schedule cannot ground, and with the
    /// `explore/level-poly-target` apparatus enabled, the obligation is
    /// `srt(ℓ̂) ∈ srt(succ ℓ̂)` instead — `Srt::sort_in_sort` at the variable
    /// index, a **conditional** certificate under the level's `u ∈ ω`
    /// assumptions (`LEVELPOLY.md` §1.3). The guard that the interpreted
    /// obligation really has that shape falls through to the ordinary miss
    /// when it fails, e.g. when canonicalisation reshaped `succ ℓ`.
    fn ty_sort(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: ExprPtr<'t>) -> TgTyping {
        let (te, tt) = (self.interp(ctx, e), self.interp(ctx, ty));
        if levelpoly_enabled() {
            if let Some(t) = self.ty_sort_poly(ctx, e, &te, &tt) {
                return t
            }
        }
        match self.domain_premise(&te, &tt) {
            Some(t) => self.typing(crate::certify::TyGap::Sort, &te, &tt, t, Vec::new()),
            None => self.ty_miss(crate::certify::TyGap::Sort),
        }
    }


    /// A constant's typing: **a lookup** in the store filled when the
    /// declaration was checked. Not a walk down the delta graph — a constant's
    /// typing does not depend on where it is used, so deriving it per use was
    /// redundant as well as unbounded (see [`Self::has_type_const`]).
    ///
    /// The stored theorem is about the *declared* type. Inference asks at
    /// exactly the declared type, so the two line up by construction — and the
    /// guard checks it rather than assuming it.
    fn ty_const(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: ExprPtr<'t>) -> TgTyping {
        let Expr::Const { name, levels, .. } = ctx.read_expr(e) else {
            return self.ty_miss(crate::certify::TyGap::Const)
        };
        // The store is consulted *before* anything is interpreted. Interpreting
        // a constant registers the whole definitional extension beneath its
        // value, and interpreting its declared type builds a Replacement
        // derivation for every `Π` in it; neither is worth doing for a constant
        // whose typing was never stored, which is most of them.
        let Some(key) = self.const_key(ctx, name, levels) else {
            return self.ty_miss(crate::certify::TyGap::Const)
        };
        let hit = self.shared.borrow().declar_typings.get(&key).cloned();
        let Some(t) = hit else {
            // The quantified store (§5.3 step 5): the `∀u⃗` entry, re-opened at
            // the generic point exactly as [`Self::has_type_const`] does, its
            // `uᵢ ∈ ω` antecedents riding the typing's own hypothesis channel
            // — inference then carries them like any binder-owed assumption,
            // and the declaration boundary of the *using* declaration is
            // where they close again.
            let phit = self.shared.borrow().declar_typings_poly.get(&key).cloned();
            if let Some((vars, whyps, sealed)) = phit {
                let args: Vec<Term> = vars.iter().map(|v| Term::var(*v)).collect();
                if let Some(opened) = derived::inst_all(sealed.thm(), &args) {
                    let te = self.interp(ctx, e);
                    let tt = self.interp(ctx, ty);
                    let h = conj_of(&whyps);
                    if u_concl(&opened, h.as_ref()) == Some(Formula::mem(te.clone(), tt.clone())) {
                        note_dt(Dt::PolyHit);
                        return self.typing(crate::certify::TyGap::Const, &te, &tt, opened, whyps)
                    }
                }
            }
            note_dt(Dt::Miss);
            if self.shared.borrow().declined_cond.contains(&key) {
                note_dt(Dt::MissCond);
            }
            return self.ty_miss(crate::certify::TyGap::Const)
        };
        note_dt(Dt::Hit);
        // Interpreting the constant is what fixes which symbol `⟦c⟧` is, and so
        // what a stored theorem has to be about.
        let te = self.interp(ctx, e);
        let tt = self.interp(ctx, ty);
        self.typing(crate::certify::TyGap::Const, &te, &tt, t.into_thm(), Vec::new())
    }

    /// A context local: its own declared typing, **acquired as an antecedent**.
    ///
    /// `Γ ⊢ w : A` for a local is carried as an **antecedent inside the
    /// formula** and discharged when the binder that introduced `w` closes.
    /// (Not because the kernel lacks a context — it has one, `Thm` is a
    /// sequent — but because an antecedent travels with the formula and a
    /// sequent hypothesis does not; see [`Self::has_type_local`].) That discharge is
    /// [`Certifier::ty_lam`]'s, and it is the same `gen` + `ax_dist` move
    /// [`Self::has_type_local`] relies on.
    fn ty_local(&mut self, ctx: &mut TcCtx<'t, 'p>, e: ExprPtr<'t>, ty: ExprPtr<'t>) -> TgTyping {
        let (te, tt) = (self.interp(ctx, e), self.interp(ctx, ty));
        let f = Formula::mem(te.clone(), tt.clone());
        let thm = derived::imp_refl(f.clone());
        self.typing(crate::certify::TyGap::Local, &te, &tt, thm, vec![f])
    }

    /// A **structure projection**: its own field typing, acquired as an
    /// antecedent. [`Self::has_type_proj`] driven by inference instead of
    /// searched for, and that method's doc comment is where the reason it is
    /// carried rather than derived is written down — `proj` is an axiom-free
    /// symbol, so there is no theorem here to find.
    ///
    /// # The claim is recomputed, not taken
    ///
    /// The checker reaches the field type by `whnf` and hands it in. This rule
    /// does not assume at whatever it was handed: it re-derives the field type
    /// from the structure's constructor telescope with
    /// [`Self::syn_type_proj`] and refuses unless the two interpret to the same
    /// term. So an antecedent is only ever acquired at Lean's own judgement for
    /// this projection, and an obligation stated at something merely
    /// definitionally equal to it is a counted gap.
    fn ty_proj(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        structure: ExprPtr<'t>,
    ) -> TgTyping {
        // `e` really is a projection, and out of the subject the caller named.
        let Expr::Proj { idx, structure: s, .. } = ctx.read_expr(e) else {
            return self.ty_miss(crate::certify::TyGap::Proj)
        };
        if s != structure {
            return self.ty_miss(crate::certify::TyGap::Proj)
        }
        let (te, tt) = (self.interp(ctx, e), self.interp(ctx, ty));
        // The field type, recomputed here. Declining when the delta-only walk
        // cannot reach the telescope is deliberate: nothing is assumed about a
        // projection whose field type this module cannot see for itself.
        let Some(field) = self.syn_type_proj(ctx, idx, structure) else {
            return self.ty_miss(crate::certify::TyGap::Proj)
        };
        let tf = self.interp(ctx, field);
        if tf != tt {
            return self.ty_miss(crate::certify::TyGap::Proj)
        }
        let f = Formula::mem(te.clone(), tt.clone());
        let thm = derived::imp_refl(f.clone());
        self.typing(crate::certify::TyGap::Proj, &te, &tt, thm, vec![f])
    }

    /// **Conversion.** From `⟦e⟧ ∈ ⟦from⟧` and a definitional-equality
    /// certificate relating `from` and `to`, conclude `⟦e⟧ ∈ ⟦to⟧` by Leibniz.
    ///
    /// This is where the certificate `assert_def_eq` used to confirm and throw
    /// away does its work. The equation may have been derived in either
    /// direction — the checker's application rule states it as
    /// `binder_type ≡ arg_type` and the rule needs `arg_type = binder_type` —
    /// so both are accepted and the wrong one is turned round with a real
    /// `eq_symm`. Anything that is not about these two types is a gap.
    fn ty_conv(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        from: ExprPtr<'t>,
        to: ExprPtr<'t>,
        typing: TgTyping,
        eq: &TgCert,
    ) -> TgTyping {
        // Decline before interpreting anything: a hole for a premise concludes
        // nothing, and interpreting the two types is not free.
        let Some((thm, hyps)) = Self::ty_parts(&typing) else {
            return self.ty_miss(crate::certify::TyGap::Premise)
        };
        let (tf, tt) = (self.interp(ctx, from), self.interp(ctx, to));
        let te = self.interp(ctx, e);
        // Nothing to do: the two types interpret to the same term.
        if tf == tt {
            return typing
        }
        // Read the equation without cloning the certificate: cloning a
        // conditional one is a second obligation, and this rule is not entitled
        // to create one.
        let (eq_thm, eq_hyps): (&Thm, &[Formula]) = match eq {
            TgCert::Proved(t) => (t, &[]),
            TgCert::Conditional { thm, hyps } => (thm, hyps.as_slice()),
            TgCert::Admitted(_) => return self.ty_miss(crate::certify::TyGap::Premise),
        };
        let hyps2 = merge_hyps(&hyps, eq_hyps);
        let h = conj_of(&hyps2);
        let Some(eq_lifted) = reassume(eq_thm, eq_hyps, &hyps2) else {
            return self.ty_miss(crate::certify::TyGap::Conv)
        };
        let Some((l, r)) = u_as_eq(&eq_lifted, h.as_ref()) else {
            return self.ty_miss(crate::certify::TyGap::Conv)
        };
        // Orient the equation at `⟦from⟧ = ⟦to⟧`, or refuse.
        let oriented = if (l.clone(), r.clone()) == (tf.clone(), tt.clone()) {
            Some(eq_lifted)
        } else if (l, r) == (tt.clone(), tf.clone()) {
            u_eq_symm(&mut self.env_mut(), &eq_lifted, h.as_ref())
        } else {
            None
        };
        let Some(oriented) = oriented else { return self.ty_miss(crate::certify::TyGap::Conv) };
        let Some(lifted) = reassume(&thm, &hyps, &hyps2) else {
            return self.ty_miss(crate::certify::TyGap::Conv)
        };
        let w = self.env_mut().fresh_var();
        let leib = Thm::eq_leibniz(tf, tt.clone(), w, Formula::mem(te.clone(), Term::var(w)));
        let out = (|| {
            let step = u_a1i(&leib, h.as_ref());
            let step = u_mp(&step, &oriented, h.as_ref())?;
            u_mp(&step, &lifted, h.as_ref())
        })();
        match out {
            Some(t) => self.typing(crate::certify::TyGap::Conv, &te, &tt, t, hyps2),
            None => self.ty_miss(crate::certify::TyGap::Conv),
        }
    }

    /// **Application.** The premises are inference's own: the function's typing
    /// at the `Π` it eliminates, and the argument's typing at that `Π`'s domain
    /// — the latter obtained by converting along the very equality the checker
    /// had to establish anyway.
    fn ty_app(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        app: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        fun: ExprPtr<'t>,
        fun_ty: ExprPtr<'t>,
        arg: ExprPtr<'t>,
        f: TgTyping,
        a: TgTyping,
    ) -> TgTyping {
        let (Some((hf, used_f)), Some((ha, used_a))) = (Self::ty_parts(&f), Self::ty_parts(&a)) else {
            return self.ty_miss(crate::certify::TyGap::Premise)
        };
        let Expr::Pi { binder_type, .. } = ctx.read_expr(fun_ty) else {

            return self.ty_miss(crate::certify::TyGap::App)
        };
        let fty_t = self.interp(ctx, fun_ty);
        let dom_t = self.interp(ctx, binder_type);
        let (tf, ta) = (self.interp(ctx, fun), self.interp(ctx, arg));
        let tapp = self.interp(ctx, app);
        let tty = self.interp(ctx, ty);

        // The function's typing may be stated at a defined name for the `Π`;
        // bridge it along the defining equations, or decline.
        let f_ty_stated = match u_concl(&hf, conj_of(&used_f).as_ref()).and_then(|c| c.as_mem().map(|(_, d)| d)) {
            Some(d) => d,
            None => return self.ty_miss(crate::certify::TyGap::App),
        };
        let Some(hf) = self.ty_bridge(&tf, &f_ty_stated, &fty_t, &hf, &used_f) else {
            return self.ty_miss(crate::certify::TyGap::App)
        };

        let used = merge_hyps(&used_f, &used_a);
        let (Some(hf), Some(ha)) = (reassume(&hf, &used_f, &used), reassume(&ha, &used_a, &used)) else {
            return self.ty_miss(crate::certify::TyGap::App)
        };
        match self.ty_app_from(fun_ty, &fty_t, &dom_t, &tf, &ta, &hf, &ha, &used) {
            Some(t) => self.typing(crate::certify::TyGap::App, &tapp, &tty, t, used),
            None => self.ty_miss(crate::certify::TyGap::App),
        }
    }

    /// **Lambda.** From the body's typing under the binder's hypothesis,
    /// conclude the lambda's — by [`lam_in_funspace_n`] when the target is a
    /// function space over the binder's domain and [`lam_in_dprod_n`] when it is
    /// a dependent product over it.
    ///
    /// This is [`Self::has_type_lam`] with the recursion removed. It opens the
    /// binder at the checker's *own* local rather than at the site's variable,
    /// because that is the variable the body's derivation already speaks of; the
    /// skeleton is re-instantiated at it and checked to unfold to the
    /// interpretation of the body, so nothing is assumed about the two agreeing.
    fn ty_lam(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        lam: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        local: ExprPtr<'t>,
        body: ExprPtr<'t>,
        b: TgTyping,
    ) -> TgTyping {
        let Some((at_v, inner)) = Self::ty_parts(&b) else {
            return self.ty_miss(crate::certify::TyGap::Premise)
        };
        // Interpreting the lambda registers its graph symbol and site.
        let tlam = self.interp(ctx, lam);
        let tty = self.interp(ctx, ty);
        // The kernel variable the checker's local interprets to. Read out of
        // the interpretation rather than assumed, and checked to be exactly a
        // variable: the discharge at the binder abstracts it, and abstracting
        // anything else would be abstracting the wrong thing.
        let tlocal = self.interp(ctx, local);
        let mut fvs = Vec::new();
        tlocal.free_vars(&mut fvs);
        let v = match fvs.as_slice() {
            [v] if tlocal == Term::var(*v) => *v,
            _ => return self.ty_miss(crate::certify::TyGap::Lam),
        };
        // §6.2's other lambda clause: a proof `λ` is `•` and has no graph, so
        // the premise closes by `cond_intro` rather than by the graph lemmas.
        if let Some(site) = self.prop_lam_sites.get(&lam) {
            let dom = site.dom.clone();
            let out = (|| {
                let (pkey, targs, unfold_b, b_at_v, fibre) = self.prop_fibre_at(&tty, &dom, v)?;
                self.prop_lam_close(
                    ctx, &at_v, &inner, body, v, &dom, &pkey, &targs, &unfold_b, &b_at_v, &fibre,
                )
            })();
            return match out {
                Some((t, rest, _)) => self.typing(crate::certify::TyGap::Lam, &tlam, &tty, t, rest),
                None => self.ty_miss(crate::certify::TyGap::Lam),
            }
        }
        let Some(site) = self.lam_sites.get(&lam) else { return self.ty_miss(crate::certify::TyGap::Lam) };
        let (key, holes, dom) = (site.key.clone(), site.holes.clone(), site.dom.clone());

        // The cheap discriminator first, as in `has_type_lam`: both rules need
        // the target to be a function space or a dependent product over *this*
        // lambda's domain, and by far the commonest outcome is that it is not.
        let Some((head, targs)) = self.parts.get(&tty).cloned() else {
            return self.ty_miss(crate::certify::TyGap::Lam)
        };
        let fs_shape = head == self.pre.fs_sym() && targs.len() == 2 && targs[0] == dom;
        if !fs_shape && !(targs.last() == Some(&dom) && self.shared.borrow().pi_by_dprod.contains_key(&head)) {
            return self.ty_miss(crate::certify::TyGap::Lam)
        }

        let Some(info) = self.lam_info(&key) else { return self.ty_miss(crate::certify::TyGap::Lam) };
        let Some(graph) = info.graph.as_ref() else { return self.ty_miss(crate::certify::TyGap::Lam) };
        let t_def = graph.t_def.clone();

        // `t(h⃗,v)` must unfold to the interpretation of the body opened at the
        // checker's own local. Checked, not assumed.
        let mut tinst = holes.clone();
        tinst.push(Term::var(v));
        let Some(unfold_t) = derived::inst_all(&t_def, &tinst) else {
            return self.ty_miss(crate::certify::TyGap::Lam)
        };
        let Some((t_at_v, bt)) = unfold_t.concl().as_eq() else {
            return self.ty_miss(crate::certify::TyGap::Lam)
        };
        if bt != self.interp(ctx, body) {
            return self.ty_miss(crate::certify::TyGap::Lam)
        }

        let out = if fs_shape {
            // ── Non-dependent: a fixed codomain ──────────────────────────────
            let cod = targs[1].clone();
            (|| {
                let at_v = self.retarget_mem(&at_v, &inner, &unfold_t, &cod, None)?;
                let concl = Formula::mem(t_at_v.clone(), cod.clone());
                let (pointwise, rest) = self.guard_and_generalise_at(&at_v, &inner, &concl, v, &dom)?;
                let hyp = conj_of(&rest);
                let lem = self.lam_fs_thm(&key)?;
                let mut args = holes.clone();
                args.push(dom.clone());
                args.push(cod);
                let inst = derived::inst_all(&lem, &args)?;
                Some((u_mp(&u_a1i(&inst, hyp.as_ref()), &pointwise, hyp.as_ref())?, rest))
            })()
        } else {
            // ── Dependent: the fibre at the binder ───────────────────────────
            (|| {
                let (pkey, pinfo) = self.shared.borrow().pi_by_dprod.get(&head).cloned()?;
                let qholes: Vec<Term> = targs[..targs.len() - 1].to_vec();
                let b_def = pinfo.fibre.as_ref()?.b_def.clone();
                let mut binst = qholes.clone();
                binst.push(Term::var(v));
                let unfold_b = derived::inst_all(&b_def, &binst)?;
                let (b_at_v, fibre) = unfold_b.concl().as_eq()?;
                // The fibre at the binder is a term the kernel built, so rebuild
                // it from the skeleton and check the two agree.
                let mut sub: Vec<(FreeVar, Term)> = Vec::with_capacity(qholes.len() + 1);
                for (i, q) in qholes.iter().enumerate() {
                    sub.push((self.hole_var(i), q.clone()));
                }
                sub.push((self.x_canon, Term::var(v)));
                if self.reify(&pkey, &sub)? != fibre {
                    return None
                }
                let at_v = self.retarget_mem(&at_v, &inner, &unfold_t, &fibre, Some(&unfold_b))?;
                let concl = Formula::mem(t_at_v.clone(), b_at_v);
                let (pointwise, rest) = self.guard_and_generalise_at(&at_v, &inner, &concl, v, &dom)?;
                let hyp = conj_of(&rest);
                let lem = self.lam_dprod_thm(&key, &pkey)?;
                let mut args = holes.clone();
                args.extend(qholes);
                args.push(dom.clone());
                let inst = derived::inst_all(&lem, &args)?;
                Some((u_mp(&u_a1i(&inst, hyp.as_ref()), &pointwise, hyp.as_ref())?, rest))
            })()
        };
        match out {
            Some((t, rest)) => self.typing(crate::certify::TyGap::Lam, &tlam, &tty, t, rest),
            None => self.ty_miss(crate::certify::TyGap::Lam),
        }
    }

    /// **Let.** A `let` is interpreted as an explicit definition of its
    /// expansion, so the expansion's typing carries across that defining
    /// equation by Leibniz — the same move [`Self::has_type_const`] makes for a
    /// constant, and for the same reason: the equation is a real theorem, not
    /// the interpretation quietly substituting.
    fn ty_let(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        e: ExprPtr<'t>,
        ty: ExprPtr<'t>,
        expansion: ExprPtr<'t>,
        b: TgTyping,
    ) -> TgTyping {
        let Some((thm, hyps)) = Self::ty_parts(&b) else {
            return self.ty_miss(crate::certify::TyGap::Premise)
        };
        let te = self.interp(ctx, e);
        let tt = self.interp(ctx, ty);
        let tx = self.interp(ctx, expansion);
        let Some(def) = self.let_defs.get(&e).cloned() else { return self.ty_miss(crate::certify::TyGap::Let) };
        // `⊢ ⟦let⟧ = ⟦expansion⟧`; turned round it re-aims the membership.
        let out = (|| {
            let (l, r) = def.concl().as_eq()?;
            if l != te || r != tx {
                return None
            }
            let back = derived::eq_symm(&mut self.env_mut(), &def)?;
            let w = self.env_mut().fresh_var();
            let leib = Thm::eq_leibniz(tx.clone(), te.clone(), w, Formula::mem(Term::var(w), tt.clone()));
            let step = Thm::mp(&leib, &back)?;
            let h = conj_of(&hyps);
            u_mp(&u_a1i(&step, h.as_ref()), &thm, h.as_ref())
        })();
        match out {
            Some(t) => self.typing(crate::certify::TyGap::Let, &te, &tt, t, hyps),
            None => self.ty_miss(crate::certify::TyGap::Let),
        }
    }

    fn refl(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>) -> TgCert {
        let t = self.interp(ctx, a);
        self.proved(Thm::eq_refl(t))
    }

    /// Symmetry, **guarded**.
    ///
    /// Turning an equation around is the least a rule can do, and it was still
    /// unchecked: the certificate handed in need not be about `b ≡ a` at all,
    /// and reversing whatever it *is* about produced a `Proved` for a claim the
    /// rule had never looked at. Now the reversed equation is matched against
    /// `⟦a⟧ = ⟦b⟧` — through [`CondEq::proves`], which reads the equation out
    /// from under the assumption list, so a conditional premise is checked on
    /// the same terms as an unconditional one — and anything else is a gap.
    fn symm(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, c: TgCert) -> TgCert {
        let cc = self.consume(&c);
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match cc {
            Some(t) => match self.ceq_symm(&t) {
                Some(t) if t.proves(&ta, &tb) => return self.cert(ctx, t),
                Some(_) => {
                    note_unmatched(Rule::Symm);
                    "symm: derived equation does not match the claim"
                }
                None => "symm refused",
            },
            None => "symm over an admitted premise",
        };
        // Both sides interpret identically: reflexivity proves the claim
        // outright, needing no premise. Same fallback, and same justification,
        // as in `lam_cong`/`pi_cong`.
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Transitivity, **guarded**.
    ///
    /// `ceq_trans` already refuses two premises that do not meet in the middle,
    /// but agreeing on a midpoint says nothing about the *endpoints*: two
    /// certificates about an unrelated pair compose perfectly well, and the
    /// composite was then returned as a proof of whatever the checker happened
    /// to be claiming. `a` and `b` are that claim, and the composite is matched
    /// against `⟦a⟧ = ⟦b⟧` before it counts.
    fn trans(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, ab: TgCert, bc: TgCert) -> TgCert {
        // Both are taken before either is inspected: a premise the rule cannot
        // use is still a premise the rule has *received*, and the escape ledger
        // counts receipt.
        let (x, y) = (self.consume(&ab), self.consume(&bc));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match (x, y) {
            (Some(x), Some(y)) => match self.ceq_trans(&x, &y) {
                Some(t) if t.proves(&ta, &tb) => return self.cert(ctx, t),
                Some(_) => {
                    note_unmatched(Rule::Trans);
                    "trans: derived equation does not match the claim"
                }
                None => "trans refused",
            },
            _ => "trans over an admitted premise",
        };
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Congruence for application, **guarded**.
    ///
    /// `⟦f x⟧` is `app(⟦f⟧, ⟦x⟧)`, so this is ordinary congruence over the
    /// interpretation's application symbol — and precisely because it is so
    /// ordinary it was the one place a wrong certificate could travel furthest.
    /// Handed only two sub-certificates, the rule could not tell whether they
    /// were about the function and argument of the application it was supposed
    /// to be proving something about; it built `app(l₁,l₂) = app(r₁,r₂)` from
    /// whatever it was given and returned that as a proof of the claim. A
    /// certificate assembled that way is about a term the checker never asked
    /// about, and it then arrived at a binder where `pi_cong` — which does check
    /// — could only report a gap several levels away from the rule that made it.
    ///
    /// Now `a` and `b` are the two applications, so the congruence is matched
    /// against `⟦a⟧ = ⟦b⟧` and a mismatch is named where it happens. That
    /// happens 9 times over the tutorial corpus (in 7 files) and twice on
    /// `init-prelude`, and the nine are the same nine `pi_cong` was previously
    /// reporting as `the body certificate is not the fibres' pointwise
    /// equation`, which drops from 12 to 3. It was *not* the cause of the 621
    /// bridge failures, as the module docs used to claim; those are unchanged.
    fn app_cong(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, f: TgCert, arg: TgCert) -> TgCert {
        let s = self.pre.ap.app;
        let (cf, cx) = (self.consume(&f), self.consume(&arg));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        // §6.2's two clauses for application, exactly as in `lam_cong`. Two
        // proof applications are both `•` and reflexivity is the whole
        // derivation — taken before congruence so that the guard ledger is not
        // charged for a rule that was never applicable. One of each is a
        // classification disagreement, and gets its own row.
        let (pa, pb) = (self.term_clause(ctx, a) == Clause::Prop, self.term_clause(ctx, b) == Clause::Prop);
        if pa != pb {
            return self.note_admit("congruence: one proof application and one — the two clauses of §6.2")
        }
        if pa && ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        let why: &'static str = match (cf, cx) {
            (Some(x), Some(y)) => match self.ceq_congr(s, &[x, y]) {
                Some(t) if t.proves(&ta, &tb) => return self.cert(ctx, t),
                Some(_) => {
                    note_unmatched(Rule::AppCong);
                    "congruence: derived equation does not match the claim"
                }
                None => "congruence rule refused",
            },
            // A gap anywhere below means the whole congruence is a gap; there is
            // nothing to prove congruence *from*.
            _ => "congruence over an admitted premise",
        };
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Congruence for `λ`, by **graph extensionality**, and guarded.
    ///
    /// `⟦λx:A. b⟧` is a function *graph* `lam_C(s⃗, ⟦A⟧)` whose head symbol
    /// depends on the shape of the body, so this is not congruence over
    /// sub-terms: from `⊢ ⟦A⟧ = ⟦A'⟧` and `⊢ ⟦b⟧ = ⟦b'⟧` one has to conclude
    /// `⊢ lam_C(s⃗,⟦A⟧) = lam_C'(s⃗',⟦A'⟧)` for two *different* symbols. Two
    /// graphs are equal because they have the same members, which is
    /// Extensionality — [`derived::ext::lam_ext`], here in the
    /// parameter-threading form [`lam_ext_n`] the skeleton decomposition needs.
    ///
    /// Its second premise is *pointwise*, `∀x. (x ∈ A → t(x) = t'(x))`, whereas
    /// the certificate this rule is handed compares the bodies at one fixed
    /// local. [`Self::pointwise_premise`] closes that gap: the local is a kernel
    /// free variable, `Thm::gen_checked` abstracts it — under the side condition
    /// `x ∉ FV(Γ)`, whose failure is reported as a gap rather than raised — and
    /// the `x ∈ A` guard is pure weakening. What it
    /// must establish — and does, by unfolding both body definitions and
    /// comparing terms — is that the certificate really is about the graphs'
    /// body symbols at that variable.
    ///
    /// Whatever comes out is checked against `⟦a⟧ = ⟦b⟧` before it counts as a
    /// proof, so every way this can go wrong is a gap rather than a false
    /// theorem.
    ///
    /// # Binder chains
    ///
    /// A binder *chain* is folded up innermost-first, and this used to be where
    /// the rule stopped: `def_eq_binder_aux` handed each frame its lambda in
    /// **un-instantiated** form, so an inner frame's lambda still carried loose
    /// de Bruijn indices for the enclosing binders — interpreted as opaque
    /// `bvar` symbols — while the certificate beneath it was about bodies opened
    /// at real locals. `pointwise_premise` could then never match, and the outer
    /// frame was in turn handed an equation between those un-instantiated inner
    /// lambdas. On a chain of length two or more, nothing derivable here bridged
    /// that.
    ///
    /// `def_eq_binder_aux` now instantiates each `λ` frame at the locals
    /// introduced above it, so the frame's terms *are* the ones its premises
    /// talk about, and the derivation applies at every depth. (`Π` frames are
    /// deliberately left alone: `⟦Π⟧` is built over the raw de Bruijn body, so
    /// `pi_cong` wants the opposite form. See the comment there.)
    ///
    /// The degenerate case remains as a fallback: if the two lambdas interpret
    /// to the *same* graph, reflexivity proves the claim outright, with no
    /// premise needed. That is a complete proof, not a shortcut — and it is
    /// still what closes the chains the derivation cannot reach.
    fn lam_cong(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, dom: TgCert, body: TgCert) -> TgCert {
        let (cd, cb) = (self.consume(&dom), self.consume(&body));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match self.derive_lam_cong(ctx, a, b, cd.as_ref(), cb.as_ref()) {
            Ok(t) if t.proves(&ta, &tb) => return self.cert(ctx, t),
            Ok(_) => "lam congruence: derived equation does not match the claim",
            Err(reason) => reason,
        };
        // Both lambdas interpret to the same graph: reflexivity is the claim.
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// Congruence for `Π`, **guarded**.
    ///
    /// `⟦Π x:A. B⟧` is `fs(⟦A⟧,⟦B⟧)` when the body ignores the binder and the
    /// dependent product `dprod_C(s⃗,⟦A⟧)` when it does not, so the two sides of
    /// a claim can be built by unrelated symbols. [`Self::derive_pi_cong`] picks
    /// among the three routes — congruence, dependent-product Extensionality,
    /// and the constant-fibre bridge — and the module docs record what each one
    /// buys.
    ///
    /// Getting the premises into the form the claim needs is
    /// [`TgBackend::retarget`]'s job wherever the certificate is stated at a
    /// different local from the one the claim is about; the substitution is read
    /// off by matching rather than assumed.
    ///
    /// Everything is checked against `⟦a⟧ = ⟦b⟧` before it counts as a proof, so
    /// every way this can go wrong is a gap rather than a false theorem.
    ///
    /// The reflexivity fallback covers the case where both sides interpret
    /// identically — a complete proof of the claim, needing no premise at all,
    /// and on this corpus by far the commonest way a `Π` congruence is settled.
    fn pi_cong(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>, dom: TgCert, body: TgCert) -> TgCert {
        let (cd, cb) = (self.consume(&dom), self.consume(&body));
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        let why: &'static str = match self.derive_pi_cong(ctx, a, b, cd.as_ref(), cb.as_ref()) {
            Ok(t) if t.proves(&ta, &tb) => return self.cert(ctx, t),
            Ok(_) => "pi congruence: derived equation does not match the claim",
            Err(reason) => reason,
        };
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(why)
    }

    /// One iota contraction, derived rather than admitted where the recursor
    /// is one this backend interprets. See [`TgBackend::derive_iota`].
    fn iota(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> TgCert {
        if let Some(t) = self.proof_eq(ctx, redex, reduct, Pop::SearchRule) {
            return self.cert(ctx, t)
        }
        match self.derive_iota(ctx, redex, reduct) {
            Ok(c) => self.cert(ctx, c),
            Err(why) => self.note_admit(why),
        }
    }

    fn beta(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> TgCert {
        // §6.2's `Prop` clause: a proof application is `•`, and a contraction
        // does not change a term's type and so does not change its sort — the
        // contractum is `•` too and the step is reflexivity. There is no spine
        // to walk, no graph to unfold and no domain obligation to discharge.
        if let Some(t) = self.proof_eq(ctx, redex, reduct, Pop::SearchRule) {
            return self.cert(ctx, t)
        }
        match self.derive_beta(ctx, redex, reduct) {
            Ok(t) => self.cert(ctx, t),
            Err(reason) => self.note_admit(reason),
        }
    }

    /// Zeta: `let x := v; b ≡ b[v/x]`.
    ///
    /// Discharged by the `Let`'s defining equation, guarded against the claim in
    /// the same way as `delta` and `beta`.
    fn zeta(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> TgCert {
        if let Some(t) = self.proof_eq(ctx, redex, reduct, Pop::SearchRule) {
            return self.cert(ctx, t)
        }
        let Some(eq) = self.let_defs.get(&redex).cloned() else {
            let _ = self.interp(ctx, redex);
            match self.let_defs.get(&redex).cloned() {
                Some(eq) => return self.check_against(ctx, eq, redex, reduct, "zeta"),
                None => return self.note_admit("zeta: the let has no defining equation"),
            }
        };
        self.check_against(ctx, eq, redex, reduct, "zeta")
    }

    fn delta(&mut self, ctx: &mut TcCtx<'t, 'p>, redex: ExprPtr<'t>, reduct: ExprPtr<'t>) -> TgCert {
        // `redex` is `c a₁ … aₙ` and `reduct` is `value a₁ … aₙ`. Interpreting
        // the head constant registers its defining equation `⊢ ⟦c⟧ = ⟦value⟧`;
        // folding `app_cong` over the argument spine lifts that to the whole
        // application.
        if let Some(t) = self.proof_eq(ctx, redex, reduct, Pop::SearchRule) {
            return self.cert(ctx, t)
        }
        let (fun, args) = ctx.unfold_apps(redex);
        let _ = self.interp(ctx, fun);
        let Some(head) = self.const_defs.get(&fun).cloned() else {
            return self.note_admit("delta: head constant has no defining equation")
        };
        let mut acc = head;
        for a in args {
            let ta = self.interp(ctx, a);
            let refl = Thm::eq_refl(ta);
            let app = self.pre.ap.app;
            let stepped = derived::congr(&mut self.env_mut(), app, &[acc, refl]);
            match stepped {
                Some(t) => acc = t,
                None => return self.note_admit("delta: congruence over the spine refused"),
            }
        }
        // Guard: the derived equation must really be about the two terms the
        // checker claims are equal. If the interpretation and the reduction have
        // drifted apart, that is a bug — report it rather than pass it off.
        let (lhs, rhs) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        if *acc.concl() != kernel::Formula::eq(lhs, rhs) {
            return self.note_admit("delta: derived equation does not match the reduction")
        }
        self.proved(acc)
    }

    /// Eta. The half the checker settled arrives as `expanded`; the half that
    /// needs a function-extensionality lemma is what is still missing.
    ///
    /// `expanded` is *consumed* rather than ignored, which is not bookkeeping
    /// pedantry: a conditional certificate is accounted against the escape
    /// ledger the moment a rule takes it, so dropping this one silently would
    /// report an assumption as having escaped when in fact it was handed over.
    /// Once `λz. b z = b` is derivable, the composition happens here and both
    /// halves are already in hand.
    fn eta(
        &mut self,
        _ctx: &mut TcCtx<'t, 'p>,
        _a: ExprPtr<'t>,
        _b: ExprPtr<'t>,
        _expansion: ExprPtr<'t>,
        expanded: TgCert,
    ) -> TgCert {
        let _ = self.consume(&expanded);
        self.note_admit("eta (needs a function-extensionality lemma)")
    }

    fn sort(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>) -> TgCert {
        // The checker only calls this when the two levels are equal under its
        // own level algebra. When that makes the interpretations syntactically
        // identical, reflexivity settles it outright. When it does not — say
        // `max u v` versus `max v u` — proving it needs level axioms the
        // signature does not have, so it is recorded as a gap rather than waved
        // through.
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            self.proved(Thm::eq_refl(ta))
        } else {
            self.note_admit("sort equality modulo level algebra")
        }
    }

    fn const_eq(&mut self, ctx: &mut TcCtx<'t, 'p>, a: ExprPtr<'t>, b: ExprPtr<'t>) -> TgCert {
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            self.proved(Thm::eq_refl(ta))
        } else {
            self.note_admit("constant equality modulo level algebra")
        }
    }

    /// **Projection congruence**, and it needs no axiom about projections.
    ///
    /// `⟦s.i⟧` is `proj(i, ⟦s⟧)` over a signature symbol, so `s ≡ s'` lifts to
    /// `s.i ≡ s'.i` by congruence over that symbol with reflexivity in the index
    /// position. Everything is checked: `a` and `b` really are projections at
    /// one index, the premise really is about the two structures, and the result
    /// really is the claim.
    fn proj_cong(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        structures: TgCert,
    ) -> TgCert {
        let Some(sc) = self.consume(&structures) else {
            return self.note_admit(crate::certify::Admit::Proj.name())
        };
        let (Expr::Proj { idx: ia, structure: sa, .. }, Expr::Proj { idx: ib, structure: sb, .. }) =
            (ctx.read_expr(a), ctx.read_expr(b))
        else {
            return self.note_admit("def_eq_proj: not a pair of projections")
        };
        if ia != ib {
            return self.note_admit("def_eq_proj: two different field indices")
        }
        let (tsa, tsb) = (self.interp(ctx, sa), self.interp(ctx, sb));
        if !sc.proves(&tsa, &tsb) {
            return self.note_admit("def_eq_proj: the premise is not about the two structures")
        }
        let i = self.idx_term(ia as u64);
        let proj = self.syms.proj;
        let Some(out) = self.ceq_congr(proj, &[CondEq::refl(i), sc]) else {
            return self.note_admit("def_eq_proj: congruence refused")
        };
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if !out.proves(&ta, &tb) {
            return self.note_admit("def_eq_proj: derived equation does not match the claim")
        }
        self.cert(ctx, out)
    }

    /// **Two locals with one id**, decided by [`LocalKey`]'s own grain.
    ///
    /// A level-local's kernel variable is keyed by level **and** interpreted
    /// declared type, so the claim splits exactly along the key:
    ///
    /// * the two types interpret to the same term — one key, one variable,
    ///   and the equation is reflexivity, derived outright;
    /// * the types are merely definitionally equal — two keys, two variables,
    ///   and no rule of this backend relates two distinct free variables. The
    ///   step stays a gap, under the label the checker used to admit under.
    ///
    /// `ty_eq` is consumed either way — receipt is what the escape ledger
    /// counts — but the residue case cannot use it: `⊢ ⟦A⟧ = ⟦A'⟧` relates the
    /// *types*, and what the claim needs is an equation between the two
    /// *variables*, which only an interpretation choice (one variable per
    /// def-eq class of types) could supply. That choice is exactly what
    /// [`LocalKey`] rejects — a memo key must not depend on a definitional
    /// equality judgement — so the gap is genuine and stays counted.
    fn local_eq(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        ty_eq: TgCert,
    ) -> TgCert {
        // Taken before it is inspected, like every premise (see `consume`).
        let _receipt = self.consume(&ty_eq);
        let (Expr::Local { id: ia, .. }, Expr::Local { id: ib, .. }) =
            (ctx.read_expr(a), ctx.read_expr(b))
        else {
            return self.note_admit("def_eq_local: not a pair of locals")
        };
        if ia != ib {
            return self.note_admit("def_eq_local: two different ids")
        }
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        self.note_admit(crate::certify::Admit::Local.name())
    }

    /// **Proof irrelevance**, from the premises the checker handed over.
    ///
    /// Carneiro's Theorem 6.7 on each side — a proposition denotes a subset of
    /// `{•}`, so anything in it *is* `•` — and transitivity between them. What
    /// used to happen instead is the clearest double-work loop the threading
    /// census found: the checker established both memberships, dropped them,
    /// admitted the step, and the admission's rescue path then searched for
    /// exactly those two facts.
    ///
    /// `ty_eq` earns its place rather than riding along: `⟦α⟧ ∈ U₀` is the
    /// premise most likely to be a hole on one side and not the other — one
    /// proposition may be a `∀` whose conditional singleton is registered while
    /// the other is a constant — and the two propositions are definitionally
    /// equal, so Leibniz carries whichever one exists across to the side that
    /// lacks it.
    #[allow(clippy::too_many_arguments)]
    fn proof_irrel(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        a: ExprPtr<'t>,
        b: ExprPtr<'t>,
        a_ty: ExprPtr<'t>,
        b_ty: ExprPtr<'t>,
        a_mem: TgTyping,
        a_prop: TgTyping,
        b_mem: TgTyping,
        b_prop: TgTyping,
        ty_eq: &TgCert,
    ) -> TgCert {
        // Taken whatever happens next, so the escape ledger stays exact.
        let teq = self.consume(ty_eq);
        let (ta, tb) = (self.interp(ctx, a), self.interp(ctx, b));
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        let (a_prop, b_prop) = self.share_prop(ctx, a_ty, b_ty, a_prop, b_prop, teq.as_ref());
        let reason = crate::certify::Admit::ProofIrrel.name();
        let Some(ca) = self.point_of_proof_from(ctx, a, a_ty, &a_mem, &a_prop, Pop::ThreadIrrel) else {
            return self.note_admit(reason)
        };
        let Some(cb) = self.point_of_proof_from(ctx, b, b_ty, &b_mem, &b_prop, Pop::ThreadIrrel) else {
            return self.note_admit(reason)
        };
        let out = self
            .ceq_symm(&cb)
            .and_then(|cb| self.ceq_trans(&ca, &cb))
            .filter(|out| out.proves(&ta, &tb));
        match out {
            Some(out) => self.cert(ctx, out),
            None => self.note_admit(reason),
        }
    }

    /// **Projection reduction**, and the honest statement of what this backend
    /// can say about one.
    ///
    /// It cannot say the thing a reader expects. `(mk a₁ … aₙ).i ⟶ aⱼ` is the
    /// constructor's own computation rule, and this backend has no
    /// interpretation of structures, so it has no axiom about `mk`, none about
    /// `proj` beyond its being a function symbol, and therefore no derivation of
    /// the reduction *as a reduction*. That is `INDUCTIVES.md`'s scope, not
    /// threading debt, and it is what the `proj_reduce` gap has always meant.
    ///
    /// What it can say is the other thing, and the checker now hands over
    /// exactly what saying it needs. If both endpoints are proofs then each
    /// interprets to `•` — Carneiro's Theorem 6.7, [`Self::point_of_proof_from`]
    /// — and the two equations compose to the claim. No property of projections
    /// enters that argument at all; it is true of the endpoints of *any* step
    /// between two proofs, and it is the same derivation `beta`, `zeta`, `delta`
    /// and `iota` each run before reaching for their real rule.
    ///
    /// The difference from those four is where the premises come from, and it is
    /// the difference this whole stage is about. They call [`Self::proof_eq`],
    /// which reconstructs both premises — `syn_type`'s delta-only shadow walk for
    /// the type, then two `has_type_a` searches — because a backend may not
    /// re-enter the checker. Here the checker inferred both endpoints before
    /// asking, so the premises **arrive**, and the ledger separates the two
    /// routes (`…threaded, asked by projection reduction` against
    /// `…asked by a reduction rule's proof shortcut`).
    ///
    /// Every exit that is not a derivation is [`crate::certify::Admit::ProjRed`]
    /// — the reduction's own name. This method is the site that noticed *and*
    /// the site that is at fault, which is the property `admit`'s deleted
    /// fall-through did not have.
    fn proj_red(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        redex: ExprPtr<'t>,
        reduct: ExprPtr<'t>,
        redex_proof: Option<crate::tc::Proof<'t, TgTyping>>,
        reduct_proof: Option<crate::tc::Proof<'t, TgTyping>>,
    ) -> TgCert {
        let reason = crate::certify::Admit::ProjRed.name();
        let (ta, tb) = (self.interp(ctx, redex), self.interp(ctx, reduct));
        // Both sides took one of §6.2's split clauses, or the interpretation
        // happens to compute: reflexivity is the claim, with no premise at all.
        if ta == tb {
            return self.proved(Thm::eq_refl(ta))
        }
        let (Some(l), Some(r)) = (redex_proof, reduct_proof) else {
            return self.note_admit(reason)
        };
        let Some(ca) = self.point_of_proof_from(ctx, redex, l.ty, &l.mem, &l.prop, Pop::ThreadProjRed) else {
            return self.note_admit(reason)
        };
        let Some(cb) = self.point_of_proof_from(ctx, reduct, r.ty, &r.mem, &r.prop, Pop::ThreadProjRed) else {
            return self.note_admit(reason)
        };
        let out = self
            .ceq_symm(&cb)
            .and_then(|cb| self.ceq_trans(&ca, &cb))
            .filter(|out| out.proves(&ta, &tb));
        match out {
            Some(out) => self.cert(ctx, out),
            None => self.note_admit(reason),
        }
    }

    /// A step the *checker* took on trust. **A gap, and nothing else.**
    ///
    /// This used to try [`TgBackend::proof_eq`] first, and rescue the step when
    /// both sides happened to interpret to `•`. That was wrong, and the reason
    /// is worth stating in full because the rescue *worked* — it turned 20 real
    /// gaps a run into green ticks:
    ///
    /// > If the checker does not know why an equation should hold then
    /// > admitting is the right step. Optimistically finding a proof is not;
    /// > that is hiding a problem under the rug.
    ///
    /// `admit`'s contract is "I cannot justify this". A rule that *can* justify
    /// its conclusion says so by being a rule: [`Certifier::proof_irrel`] takes
    /// the two memberships and the two `∈ U₀` witnesses as parameters and
    /// derives from them, [`Certifier::iota`], `beta`, `zeta` and `delta` each
    /// derive their own claim, and every one of them reports its own gap under
    /// its own name when it cannot. What was left for the fallback was the
    /// *other* sites — `Whnf`, `Cache`, `UnitLike`, `EtaStruct`, `StringLit`,
    /// `NatEq`, `NatRed`, `Local`, `BoolTrue` — where the checker concluded by a
    /// rule it cannot justify and the terms merely happen to be proofs.
    ///
    /// There the rescue hid the defect twice over. It under-reported the site:
    /// `Admit::Whnf` is documented as a *bug report* that must stay at zero, and
    /// a silently rescued whnf step is a broken trace that never shows up. And
    /// it mislabelled the fix: when a projection reduction is rescued because
    /// both sides are proofs, the thing to do is give `reduce_proj` a
    /// certificate, not to record a green tick at the funnel that noticed. A
    /// fallback is, by construction, the label of the site that noticed rather
    /// than the label of what went wrong.
    ///
    /// **Measured on `init-prelude`: 20 steps, every one of them
    /// `Admit::ProjRed`** — so `gap: proj_reduce` rose 630 → 650 when the
    /// fall-through went, and the total rose with it. Those twenty are back at
    /// 630, and they are back the right way round: [`Certifier::proj_red`] is a
    /// rule, `whnf` records `Rule::ProjRed` rather than an admission, and the
    /// checker infers both endpoints and hands the rule its premises. What that
    /// took is recorded on `TypeChecker`'s `PropAt` — the rescue had been
    /// *right* about those steps for a reason the checker could not restate,
    /// because the backend reads universe levels under σ and inference does not.
    fn admit(&mut self, _ctx: &mut TcCtx<'t, 'p>, _a: ExprPtr<'t>, _b: ExprPtr<'t>, reason: &'static str) -> TgCert {
        self.note_admit(reason)
    }

    fn declar_checked(
        &mut self,
        ctx: &mut TcCtx<'t, 'p>,
        name: crate::util::NamePtr<'t>,
        uparams: crate::util::LevelsPtr<'t>,
        ty: ExprPtr<'t>,
        val: ExprPtr<'t>,
        typing: TgTyping,
    ) {
        self.store_declar_typing(ctx, name, uparams, ty, val, typing);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Reporting.
//
// A `TgBackend` is created per `TypeChecker`, i.e. per declaration, and dropped
// with it, so the per-run totals have to be accumulated somewhere shared. This
// is a report on the checker's own completeness, not part of any derivation.
// ─────────────────────────────────────────────────────────────────────────────

use std::sync::Mutex;

static TOTALS: Mutex<Option<Vec<(&'static str, u64)>>> = Mutex::new(None);
static PROVED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

// ── The guard ledger ─────────────────────────────────────────────────────────
//
// `app_cong`, `trans` and `symm` used to return whatever their premises composed
// to, without ever comparing it against the equation the checker claimed. They
// now do compare, and this counts how often that comparison *fails* — which is
// the number that says how much used to be waved through.
//
// It is deliberately not a gap row. A rule whose derivation misses the claim
// usually still reports a gap and is counted there, but not always: when both
// sides interpret to the same term, reflexivity proves the claim outright and
// there is nothing to report. So the totals below and the gap rows measure two
// different things, and folding them together would misstate both.

/// The three rules this ledger covers.
#[derive(Clone, Copy)]
enum Rule {
    AppCong,
    Trans,
    Symm,
}

static UNMATCHED: [std::sync::atomic::AtomicU64; 3] =
    [const { std::sync::atomic::AtomicU64::new(0) }; 3];

/// Record one derivation that did not match the claim it was built for.
fn note_unmatched(r: Rule) { UNMATCHED[r as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

// ── The escape ledger ────────────────────────────────────────────────────────
//
// A conditional certificate is a complete derivation of an *implication*, while
// the checker's claim is the bare equation. So carrying one is only honest for
// as long as it stays inside the derivation: the moment a copy is used as an
// answer, an assumption has been taken on trust, and it has to be reported.
//
// The backend cannot see where the checker stops recursing, so the accounting is
// done the other way round, by copies:
//
//   * every conditional certificate *created* — by a rule, or by `Clone`, since
//     a copy is a second certificate that must also be accounted for —
//     increments `CONDITIONAL`;
//   * every conditional certificate *handed back to a rule* increments
//     `CONSUMED`, because the rule has then either folded the assumption into
//     its own result (which is counted in turn), proved the claim without it, or
//     reported a gap instead.
//
// The difference is exactly the number of copies that no rule ever received —
// the ones the checker consumed as a verdict, plus any left in its caches. Those
// are the escapes, and they are reported as gaps. `TgBackend::consume` is the
// single funnel for the second counter, and every `Certifier` method that takes
// a certificate calls it on every argument, whatever it then does.
//
// The direction of the residual error matters and is stated plainly: a copy
// abandoned in a cache is counted as an escape although nothing was concluded
// from it, so this **over**-reports. It cannot under-report, because a copy that
// was never handed to a rule cannot have had its assumption discharged.

/// Conditional certificates brought into existence, copies included.
static CONDITIONAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// How many of those were copies. A copy the checker parked in a cache and never
/// used again is the one thing this ledger over-reports, so the number is kept
/// visible: it bounds the over-report.
static CONDITIONAL_COPIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Conditional certificates handed back to a rule, which accounts for them.
static CONSUMED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// The largest assumption set any one certificate carried.
static MAX_ASSUMED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The gap reported for a certificate that reached a boundary still assuming
/// something.
///
/// The row is named after [`TgBackend::beta_step`]'s assumption — the argument
/// membership `domain_premise` could not show — because that is where an
/// assumption first enters a *definitional-equality* derivation. It is not the
/// only place one is introduced: `TgBackend::has_type_local` acquires a context
/// local's own typing and `TgBackend::has_type_proj` a projection's own field
/// typing, both of which travel out in the assumption list and land here if no
/// binder discharges them. The row's *count* is the ledger's (`CONDITIONAL`
/// minus `CONSUMED`) and so covers all of them; only its wording is specific.

const ESCAPED: &str = "undischarged assumption ⟦arg⟧ ∈ ⟦binder domain⟧ survived to the boundary";

/// Record one conditional certificate coming into existence.
pub fn note_conditional() { CONDITIONAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record one conditional certificate being handed back to a rule.
fn note_consumed() { CONSUMED.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// How many certificates finished conditional. Zero is the only value that lets
/// a file be called fully derived.
pub fn escaped() -> u64 {
    use std::sync::atomic::Ordering::Relaxed;
    CONDITIONAL.load(Relaxed).saturating_sub(CONSUMED.load(Relaxed))
}

/// Record one fully-derived certificate.
pub fn note_proved() { PROVED.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// **The threat-model anchor**, derived at the backend's own `⟦False⟧`.
///
/// Incremented once per `False`-shaped inductive whose interpretation was
/// introduced together with a checked `⊢ ∀x. ¬(x ∈ ⟦False⟧)`. Reported rather
/// than merely held, because it is the one theorem of a run that nothing
/// consumes: `README.md`'s guarantee is conditional on it, so whether a given
/// run *has* it should be readable off that run.
static FALSE_ANCHORS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Record one `⟦False⟧` tied to `⊢ ∀x. ¬(x ∈ ⟦False⟧)`.
fn note_anchor() { FALSE_ANCHORS.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// **The inductive-type membership table**: obligations that matched
/// `⟦T⟧ ∈ ⟦Type 0⟧` for an interpreted inductive type `T`, and those of them
/// that came back with a theorem.
///
/// Counted separately from the clause tally because the two answer different
/// questions. `HtClause::IndTy` says how much work the rule carried; these say
/// whether the corpus *asks* at all. A registered theorem that nothing consults
/// is a real outcome and has to be readable as one — the first count staying at
/// zero is the finding, not a missing measurement.
static IND_TY_ASKED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static IND_TY_DERIVED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Record one consultation (`derived == false`) or one success.
fn note_ind_ty(derived: bool) {
    let c = if derived { &IND_TY_DERIVED } else { &IND_TY_ASKED };
    c.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// How many times this run derived the anchor. `0` means no development it saw
/// declared `False`, not that the anchor failed.
pub fn false_anchors() -> u64 { FALSE_ANCHORS.load(std::sync::atomic::Ordering::Relaxed) }

/// **Binder opens in the interpretation** — `interp_lambda`/`interp_pi` —
/// split by whether the `(level, ⟦type⟧)` key already had a kernel variable.
///
/// The reuse count is the payoff of opening these binders at de Bruijn levels
/// instead of `mk_unique` locals: a reused variable means the opened body's
/// interpretation-memo entries (and every memoised statement about them) are
/// reachable again, where a unique local made them dead on arrival. Reported
/// so the payoff is a number per run, not an assumption.
static BINDER_VARS_MINTED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static BINDER_VARS_REUSED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Record one interpretation binder open.
fn note_binder_var(reused: bool) {
    let c = if reused { &BINDER_VARS_REUSED } else { &BINDER_VARS_MINTED };
    c.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// Record one step taken on trust.
pub fn merge_one(reason: &'static str) {
    let mut g = TOTALS.lock().expect("tg totals poisoned");
    let v = g.get_or_insert_with(Vec::new);
    match v.iter_mut().find(|(r, _)| *r == reason) {
        Some((_, m)) => *m += 1,
        None => v.push((reason, 1)),
    }
}

// ── The typing ledger ────────────────────────────────────────────────────────
//
// `has_type` is a family of clauses, one per Lean typing rule, and the useful
// question about it is not "how often does it work" but *which rule carries the
// work* — and, for the obligations it cannot discharge, what shape of argument
// they are about. Both halves are counted, because the second is the list of
// what the interpretation still lacks, in the order it would pay to fix.

/// The clause that discharged a typing obligation.
#[derive(Clone, Copy)]
enum HtClause {
    /// `⊢ ∀x. x ∈ U(x)`, which is also the `Sort` rule at levels `≥ 1`.
    MemU,
    /// `⊢ U₀ ∈ U₁`, i.e. `⟦Prop⟧ ∈ ⟦Type 0⟧` — the one level of the tower where
    /// `x ∈ U(x)` does not apply, because `U₁` is `U(ω)`.
    U0MemU1,
    /// `⊢ ∀a. fs(a,a) ∈ U(a)`, carried across [`TgBackend::dprod_fs_eq`] to
    /// the constant-fibre `dprod` the diagonal arrow interprets to.
    FsDiag,
    /// Along a constant's defining equation, from its value's typing.
    Const,
    /// A function's values lie in its codomain (`fs`).
    AppFs,
    /// The dependent product's characteristic property.
    AppDProd,
    /// A binder's own assumption, in force under it.
    Assumed,
    /// A context local, by acquiring its declared typing as a new antecedent.
    Local,
    /// A structure projection, by acquiring its field typing as a new
    /// antecedent — `proj` carries no axioms, so there is nothing to derive.
    Proj,
    /// Along the *target* type's defining equation.
    TypeDelta,
    /// By **beta-reducing the target** type — the type-level analogue of
    /// `TypeDelta`, for a target that is a set-application of a lambda graph.
    TargetBeta,
    /// `lam_in_funspace_n`: the lambda's body lands in a fixed codomain.
    LamFs,
    /// `lam_in_dprod_n`: the lambda's body lands in the fibre, pointwise.
    LamDProd,
    /// `cond_intro`: a **proof** `λ` is `•`, and `•` inhabits the conditional
    /// singleton its `∀` denotes — §6.2's other lambda clause.
    LamProp,
    /// A nullary constructor of an interpreted inductive, by the membership
    /// theorem `derived::enums` derived for it.
    Ctor,
    /// A constructor of a *parameterised* inductive, applied: its conditional
    /// rule, with the premises discharged by recursion.
    CtorApp,
    /// An interpreted inductive **type** in the universe it provably lives in —
    /// `⟦N⟧ ∈ ⟦Type 0⟧` and `⟦Bool⟧ ∈ ⟦Type 0⟧`, by `derived::cumul`'s
    /// cumulative hierarchy. The
    /// counterpart of `Ctor` one level up: `Ctor` puts an *element* in the type,
    /// this puts the *type* in a sort.
    IndTy,
}

const N_HT_CLAUSES: usize = 17;

impl HtClause {
    const fn name(self) -> &'static str {
        match self {
            HtClause::MemU => "x ∈ U(x)  (Sort, and any U-shaped domain)",
            HtClause::U0MemU1 => "U₀ ∈ U₁  (⟦Prop⟧ ∈ ⟦Type 0⟧)",
            HtClause::FsDiag => "fs(a,a) ∈ U(a)",
            HtClause::Const => "Const: along the defining equation",
            HtClause::AppFs => "App: a function's values lie in its codomain",
            HtClause::AppDProd => "App: the dependent product's sections",
            HtClause::Assumed => "the binder's own assumption",
            HtClause::Local => "Local: the context's own typing of it, acquired as an antecedent",
            HtClause::Proj => "Proj: the field's own typing, acquired as an antecedent",
            HtClause::TypeDelta => "the target type unfolded along its definition",
            HtClause::TargetBeta => "the target type beta-reduced",
            HtClause::LamFs => "Lam: a graph is a function into any codomain it lands in",
            HtClause::LamDProd => "Lam: a graph is a section of its fibres",
            HtClause::LamProp => "Lam: a proof λ is •, and • inhabits its ∀",
            HtClause::Ctor => "Ctor: a constructor lies in its inductive type",
            HtClause::CtorApp => "CtorApp: an applied constructor, by its conditional rule",
            HtClause::IndTy => "IndTy: an inductive type lies in its universe (⟦T⟧ ∈ ⟦Type 0⟧)",
        }
    }
    const ALL: [HtClause; N_HT_CLAUSES] = [
        HtClause::MemU,
        HtClause::U0MemU1,
        HtClause::FsDiag,
        HtClause::Const,
        HtClause::AppFs,
        HtClause::AppDProd,
        HtClause::Assumed,
        HtClause::Local,
        HtClause::Proj,
        HtClause::TypeDelta,
        HtClause::TargetBeta,
        HtClause::LamFs,
        HtClause::LamDProd,
        HtClause::LamProp,
        HtClause::Ctor,
        HtClause::CtorApp,
        HtClause::IndTy,
    ];
}

/// The shape of an argument whose typing obligation could not be discharged.
///
/// # What the opaque-constant misses actually are — measured, 2026-07-31
///
/// `ConstOpaque` and `AppOpaqueHead` together are 3848 of `init-prelude`'s
/// misses, and it is worth knowing what is under them, because the obvious
/// guess is wrong. Counted by head constant, the top of the list is
///
/// | count | constant |
/// | ---: | --- |
/// | 519 | `Nat` |
/// | 453 | `Nat.succ` |
/// | 166 | `PULift` |
/// | 122 | `Nat.rec` |
/// | 113 | `Eq` |
/// | 99 | `List.cons` |
/// | 91 | `List.nil` |
/// | 81 | `PUnit` |
/// | 64 | `False` |
///
/// — **inductive types, their constructors and their recursors, without
/// exception**. Lean's three standard axioms account for **zero** of them:
/// `propext`, `Classical.choice` and `Quot.sound` head no typing obligation
/// anywhere in `init-prelude`. So giving those three hand-built typing proofs,
/// which is the obvious way to make an axiom less opaque, would move nothing
/// here; what these misses ask for is the interpretation of *more inductives*,
/// which is [`Inductives`]' business and the `Sort`-encoding obstruction's.
#[derive(Clone, Copy)]
enum HtMiss {
    Local,
    ConstOpaque,
    ConstDef,
    Lam,
    Pi,
    AppOpaqueHead,
    AppDefHead,
    AppLamHead,
    AppLocalHead,
    AppOther,
    Other,
}

const N_HT_MISSES: usize = 11;

impl HtMiss {
    const fn name(self) -> &'static str {
        match self {
            HtMiss::Local => "a local — carried as an assumption, by design",
            HtMiss::ConstOpaque => "an opaque constant — an axiom, or an uninterpreted inductive",
            HtMiss::ConstDef => "a defined constant whose value is not typeable",
            HtMiss::Lam => "a lambda whose typing rule did not apply",
            HtMiss::Pi => "a Π — needs dprod_in_universe",
            HtMiss::AppOpaqueHead => "an application of an opaque constant",
            HtMiss::AppDefHead => "an application of a defined constant",
            HtMiss::AppLamHead => "an application of a lambda",
            HtMiss::AppLocalHead => "an application of a local",
            HtMiss::AppOther => "an application of something else",
            HtMiss::Other => "a let, projection or literal",
        }
    }
    const ALL: [HtMiss; N_HT_MISSES] = [
        HtMiss::Local,
        HtMiss::ConstOpaque,
        HtMiss::ConstDef,
        HtMiss::Lam,
        HtMiss::Pi,
        HtMiss::AppOpaqueHead,
        HtMiss::AppDefHead,
        HtMiss::AppLamHead,
        HtMiss::AppLocalHead,
        HtMiss::AppOther,
        HtMiss::Other,
    ];
}

/// The shape of the *target type* an obligation was stated at. The cross-cut of
/// [`HtMiss`]: what the obligation is about, against what it is stated at.
#[derive(Clone, Copy)]
enum HtTarget {
    /// `app(lam_C(h⃗,A), x)` — a set-application whose head is a lambda graph,
    /// which is what [`TgBackend::has_type_target_beta`] reduces.
    AppLamHead,
    /// `app(app(…), x)` — a *curried* set-application, split by what sits at
    /// the bottom of the application spine.
    SpineLam,
    SpineAbbrev,
    SpineOpaque,
    SpineVar,
    /// `app(c, x)` for a defined constant `c` — unfold `c`, then reduce.
    AppAbbrevHead,
    /// `app(w, x)` for a free variable: a motive that is a context local.
    AppVarHead,
    /// `app(f, x)` for an opaque head.
    AppOpaqueHead,
    /// A defined constant, which [`HtClause::TypeDelta`] unfolds.
    Abbrev,
    Other,
}

const N_HT_TARGETS: usize = 10;

impl HtTarget {
    const fn name(self) -> &'static str {
        match self {
            HtTarget::AppLamHead => "app(lam(…), x) — a target that beta-reduces",
            HtTarget::SpineLam => "curried, spine head a lambda graph",
            HtTarget::SpineAbbrev => "curried, spine head a defined constant",
            HtTarget::SpineOpaque => "curried, spine head opaque",
            HtTarget::SpineVar => "curried, spine head a context local",
            HtTarget::AppAbbrevHead => "app(c, x) for a defined constant c",
            HtTarget::AppVarHead => "app(w, x) for a context local w",
            HtTarget::AppOpaqueHead => "app(f, x) for an opaque f",
            HtTarget::Abbrev => "a defined constant",
            HtTarget::Other => "something else",
        }
    }
    const ALL: [HtTarget; N_HT_TARGETS] = [
        HtTarget::AppLamHead,
        HtTarget::SpineLam,
        HtTarget::SpineAbbrev,
        HtTarget::SpineOpaque,
        HtTarget::SpineVar,
        HtTarget::AppAbbrevHead,
        HtTarget::AppVarHead,
        HtTarget::AppOpaqueHead,
        HtTarget::Abbrev,
        HtTarget::Other,
    ];
}

static HT_TARGETS: [std::sync::atomic::AtomicU64; N_HT_TARGETS] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_TARGETS];
static HT_RAW_TARGETS: [std::sync::atomic::AtomicU64; N_HT_TARGETS] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_TARGETS];
static HT_RAWS: [std::sync::atomic::AtomicU64; N_HT_MISSES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_MISSES];

/// Record the target shape of one obligation that was not settled.
fn note_ht_target(t: HtTarget) { HT_TARGETS[t as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record the subject shape of one obligation that reached the *raw* fallback.
fn note_ht_raw(m: HtMiss) { HT_RAWS[m as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Record the target shape of one obligation that reached the *raw* fallback.
fn note_ht_raw_target(t: HtTarget) { HT_RAW_TARGETS[t as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// Where [`TgBackend::has_type_target_beta`] stops, for the targets that *are*
/// a redex. Counted per *derivation*, not per use — unlike [`note_ht`], a memo
/// replay is not counted again — so these are attempts, not obligations.
///
/// The split is the point: "the target beta-reduces" and "the obligation is
/// then derivable" are two different claims, and only separating them says
/// which of the two is the binding constraint.
#[derive(Clone, Copy)]
enum TbMiss {
    /// A target of the shape `app(lam(…), x)` was reached.
    Reached,
    /// …but beta's own premise `x ∈ A` could not be settled.
    Domain,
    /// …the target reduced, but the obligation at the reduct is not derivable.
    Reduct,
}

const N_TB: usize = 3;

static TB: [std::sync::atomic::AtomicU64; N_TB] = [const { std::sync::atomic::AtomicU64::new(0) }; N_TB];

fn note_tb(m: TbMiss) { TB[m as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// How far [`TgBackend::peel_family`] got. Cumulative: each stage counts every
/// attempt that reached it, so the drop from one row to the next is what that
/// stage refused.
#[derive(Clone, Copy)]
enum PeelStop {
    /// The assumption is a guarded family this backend hoisted.
    Family,
    /// …and the binder's variable is free in none of the other assumptions.
    Free,
    /// …and the obligation is a membership, not another nested family.
    Mem,
    /// (or it is a *nested* family — a closure hoisted at a second binder.)
    Nested,
    /// …and the subject is a term some Lean node interprets to.
    Node,
    /// …and `has_type` typed that node under the binder's guard.
    Typed,
    /// …and re-closing it reproduced the assumption exactly.
    Closed,
    /// …and the assumption came off the certificate.
    Peeled,
}

const N_PEEL: usize = 8;

impl PeelStop {
    const ALL: [PeelStop; N_PEEL] =
        [
            PeelStop::Family,
            PeelStop::Free,
            PeelStop::Mem,
            PeelStop::Nested,
            PeelStop::Node,
            PeelStop::Typed,
            PeelStop::Closed,
            PeelStop::Peeled,
        ];

    const fn name(self) -> &'static str {
        match self {
            PeelStop::Family => "a hoisted guarded family",
            PeelStop::Free => "  …its binder is free in no other assumption",
            PeelStop::Mem => "  …it is a membership",
            PeelStop::Nested => "  (…or a nested family)",
            PeelStop::Node => "  …its subject has a Lean node",
            PeelStop::Typed => "  …has_type derived it under the guard",
            PeelStop::Closed => "  …re-closing reproduced the assumption",
            PeelStop::Peeled => "  …discharged",
        }
    }
}

static PEEL: [std::sync::atomic::AtomicU64; N_PEEL] = [const { std::sync::atomic::AtomicU64::new(0) }; N_PEEL];

fn note_peel(s: PeelStop) { PEEL[s as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// What the un-typeable guarded families are about, and what they are stated at.
static PEEL_SHAPE: [std::sync::atomic::AtomicU64; N_HT_MISSES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_MISSES];
static PEEL_TARGET: [std::sync::atomic::AtomicU64; N_HT_TARGETS] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_TARGETS];

static HT_CLAUSES: [std::sync::atomic::AtomicU64; N_HT_CLAUSES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_CLAUSES];
static HT_MISSES: [std::sync::atomic::AtomicU64; N_HT_MISSES] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_HT_MISSES];
/// Obligations asked of `has_type` by `beta_step`, and how many it settled.
static HT_ASKED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static HT_SETTLED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// The deepest recursion at which `has_type_h` actually derived something.
///
/// There is no bound to compare it against any more (see the termination note
/// on `TgBackend`), so this is pure observability: a recursion that terminates
/// by construction is still worth being able to watch.
static HT_DEPTH_USED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Record the depth of one *successful* typing derivation.
fn note_type_depth(d: u32) { HT_DEPTH_USED.fetch_max(d as u64, std::sync::atomic::Ordering::Relaxed); }

/// The declaration-typing ledger: how often `⟦c⟧ ∈ ⟦T⟧` could be formed at the
/// point the declaration was checked, and how often the store then answered a
/// use. See [`TgBackend::declar_checked`].
static DT: [std::sync::atomic::AtomicU64; N_DT] = [const { std::sync::atomic::AtomicU64::new(0) }; N_DT];

/// Outcomes recorded in the declaration-typing ledger.
#[derive(Clone, Copy)]
#[repr(usize)]
enum Dt {
    /// A `Definition`/`Theorem`/`Opaque` reached the hook.
    Seen,
    /// …and its value's typing was derived, with no antecedent left over.
    Derived,
    /// …and it is a **temporary declaration**, whose name is interned in a
    /// per-declaration arena and so cannot key a cross-declaration store. No
    /// translation is possible for it and none is owed.
    NoKey,
    /// …and **inference produced no certificate at all**. This is the genuine
    /// absence: the declaration's own check gapped, so there is nothing to
    /// record. Cascade, and interpretation scope.
    Gap,
    /// …and the derivation was unconditional but did not survive the store's
    /// own checks — it did not conclude `⟦val⟧ ∈ ⟦ty⟧`, or the abbreviation
    /// equation for `⟦c⟧` could not be formed, or the Leibniz step did not
    /// establish the membership being stored. Counted rather than returned
    /// silently so that [`Dt::Seen`] is fully accounted for by the rows beneath
    /// it: `Seen = NoKey + Gap + Conditional + FromInfer`, and
    /// `FromInfer = Stored + Refused`.
    Refused,
    /// …and that derivation came from **inference itself** rather than from a
    /// search: `infer` carried it, and `check_declar` composed it with the
    /// conversion to the declared type. This is the number that says how much of
    /// the typing store is paid for by threading rather than by looking.
    FromInfer,
    /// …and the derivation left antecedents, so nothing was stored (a stored
    /// conditional typing is a second copy of an obligation no binder reaches).
    Conditional,
    /// The **antecedents** those conditional typings carry, one per antecedent
    /// rather than one per declaration. The census beneath it is what says
    /// whether discharging them is reachable; see
    /// [`TgBackend::store_declar_typing`].
    ///
    /// Every antecedent is a hoisted guarded family, so
    /// `CondHyp = CondNest + CondMem` — asserted, not assumed. A third kind of
    /// antecedent would have to add its own row rather than vanish into the
    /// residue, which is the same discipline `Seen`'s identity enforces.
    CondHyp,
    /// …of them a **family of families**, `∀x. (x ∈ ⟦A⟧ → ∀y. (y ∈ ⟦B⟧ → …))`:
    /// hoisted at one binder and then hoisted again at an outer one.
    /// [`TgBackend::peel_family`] declines these outright — its `phi.as_mem()`
    /// yields `None` — so recursing into the nesting is missing plumbing, and
    /// measured to be worth nothing (see the store's own documentation).
    CondNest,
    /// …of them a plain membership `⟦a⟧ ∈ ⟦A⟧`, the shape
    /// [`TgBackend::peel_family`] would attempt.
    CondMem,
    /// …of them a **level-parameter membership** `u ∈ ω` over an ω-vocabulary
    /// parameter variable — the antecedent the declaration-boundary quantifier
    /// (`LEVELPOLY.md` §5.3 step 5) closes by `gen` rather than by discharge.
    /// Counted only when the typing was *not* quantified away (a mixed
    /// antecedent set, or the transport refused).
    CondOmega,
    /// …and `⟦c⟧ ∈ ⟦T⟧` was formed and stored.
    Stored,
    /// …and every antecedent was `u ∈ ω` over a parameter variable, so the
    /// typing was **quantified at the boundary** — `⊢ ∀u⃗. ⋀(uᵢ∈ω) → ⟦c⟧ ∈ ⟦T⟧`
    /// — and stored in the quantified store instead of being discarded.
    PolyStored,
    /// A store entry answered a use of the constant.
    Hit,
    /// A **quantified** entry answered a use of the constant — instantiated at
    /// the generic point and handed back conditionally, its `u ∈ ω`
    /// assumptions riding the caller's own antecedent channel (§5.2).
    PolyHit,
    /// A use found no entry: never stored, or stored at **other levels**.
    Miss,
    /// …and the entry is missing *because the typing was conditional* — the
    /// declaration was translated and the translation was thrown away
    /// ([`Dt::Conditional`]). Split out from [`Dt::Miss`] because the two say
    /// opposite things about what to do next: a miss against a `Gap` is a
    /// declaration nothing ever proved, and a miss against a `Conditional` is a
    /// proof that was computed and discarded. This row is the size of the lever
    /// "store conditional typings too" — it is how many uses such a store could
    /// answer, at best.
    MissCond,
    /// A use found an entry, but it concludes a membership at the declared type
    /// and the obligation is stated at something else. The entry is not used;
    /// the derivation runs instead.
    Wrong,
    /// The declaration is level-polymorphic, so its entry is only reusable at a
    /// use site whose level arguments interpret identically.
    Poly,
    /// A shared constant symbol was found whose defining equation is about a
    /// *different* body than the one this backend interpreted — i.e. the
    /// interpretation is not canonical across declarations after all. A fresh
    /// per-backend symbol is used instead, so behaviour is unchanged; the count
    /// is here so that a store that never hits can be told apart from an
    /// interpretation that never agrees.
    Drift,
    /// The same, for an **inductive/constructor/recursor** abbreviation
    /// ([`TgBackend::ind_abbrev`]). A recursor nest's head necessarily drifts —
    /// its body mentions that backend's own graph symbols — so a nonzero count
    /// is expected; what the row is for is the *inductive* and *constructor*
    /// symbols, which must be canonical if a cached general `Inductive` is to
    /// mean anything across declarations.
    IndDrift,
    /// The same, for a **recursor nest** ([`Shared::rec_nests`]): a stored nest
    /// was found but did not survive [`TgBackend::reuse_rec_nest`]'s checks, so
    /// the nest was rebuilt per backend — today's behaviour before the store
    /// existed. Counts [`Shared::gen_ty_nests`] the same way. Distinct from
    /// [`Dt::IndDrift`] because the two say different things: this one is about
    /// the nest's *own* variables, domains and bottom, not about the
    /// abbreviation the nest ends up under.
    NestDrift,
    /// The same, for a **constructor's nest** ([`Shared::gen_ctor_nests`]): a
    /// stored nest was found but was not over this backend's translation, type
    /// former, variables or domains, so it was rebuilt — the behaviour before
    /// the store existed. Kept apart from [`Dt::NestDrift`] because the two
    /// stores fail for different reasons and the whole value of these rows is
    /// telling one cause from another.
    CtorNestDrift,
}

const N_DT: usize = 23;

impl Dt {
    const fn name(self) -> &'static str {
        match self {
            Dt::Seen => "declarations with a value",
            Dt::Derived => "…whose value's typing was derived",
            Dt::NoKey => "…of a temporary declaration, which no store can key",
            Dt::Gap => "…whose typing inference could not justify at all (no certificate)",
            Dt::Refused => "…derived, but the store's own checks refused it",
            Dt::FromInfer => "…carried out of inference, not searched for",
            Dt::Conditional => "…derived only under antecedents",
            Dt::CondHyp => "…the antecedents they carry, each a hoisted guarded family",
            Dt::CondNest => "…of them a family of families, which peeling declines",
            Dt::CondMem => "…of them a membership ⟦a⟧ ∈ ⟦A⟧, which peeling would attempt",
            Dt::CondOmega => "…of them a level-parameter membership u ∈ ω (not quantified away)",
            Dt::Stored => "…stored as ⟦c⟧ ∈ ⟦T⟧",
            Dt::PolyStored => "…quantified at the boundary and stored as ⊢ ∀u⃗. ⋀(uᵢ∈ω) → ⟦c⟧ ∈ ⟦T⟧",
            Dt::Hit => "uses answered from the store",
            Dt::PolyHit => "uses answered from the quantified store, conditionally",
            Dt::Miss => "uses with no entry (or at other levels)",
            Dt::MissCond => "…of them against a typing that was derived and discarded",
            Dt::Wrong => "uses whose target is not the declared type",
            Dt::Poly => "stored entries that are level-polymorphic",
            Dt::Drift => "shared symbols declined: body not canonical",
            Dt::IndDrift => "shared inductive symbols declined: body not canonical",
            Dt::NestDrift => "shared nests declined: not over this walk/translation",
            Dt::CtorNestDrift => "shared constructor nests declined: not over this translation",
        }
    }
    const ALL: [Dt; N_DT] = [
        Dt::Seen,
        Dt::Derived,
        Dt::NoKey,
        Dt::Gap,
        Dt::Refused,
        Dt::FromInfer,
        Dt::Conditional,
        Dt::CondHyp,
        Dt::CondNest,
        Dt::CondMem,
        Dt::CondOmega,
        Dt::Stored,
        Dt::PolyStored,
        Dt::Hit,
        Dt::PolyHit,
        Dt::Miss,
        Dt::MissCond,
        Dt::Wrong,
        Dt::Poly,
        Dt::Drift,
        Dt::IndDrift,
        Dt::NestDrift,
        Dt::CtorNestDrift,
    ];
}

fn note_dt(d: Dt) { DT[d as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

// ── Why a `Π` fell under neither clause of §6.2 ──────────────────────────────
//
// `TyGap::PiUndet` counts the *typing sites*. This counts the **expressions**,
// split by which of the two very different reasons put them there, because the
// two point at different work: one is a real limit on any per-declaration
// interpretation, the other is a limit on this approximation.

/// The reason a body's clause was not decided.
#[derive(Clone, Copy)]
enum Undet {
    /// The level is a parameter, or a `max`/`imax` that will not simplify until
    /// one is instantiated. **Not decidable here at all**: the `Π` is `Prop` on
    /// some instantiations and a function space on others, so no reading of the
    /// declaration can settle it. Closing this means interpreting per
    /// level-instantiation, which [`crate::instantiations`] now does — so what
    /// is left in this row is the passes that take no σ.
    Param,
    /// This walk could not follow the term — a projection, a loose index, a
    /// head whose type does not reach a `Sort` by delta alone. Decidable in
    /// principle; `infer` knows the answer and the backend may not ask it.
    Unknown,
}

const N_UNDET: usize = 2;

impl Undet {
    const fn name(self) -> &'static str {
        match self {
            Undet::Param => "a universe parameter: neither clause, at any reading of the declaration",
            Undet::Unknown => "the syntactic sort walk gave up",
        }
    }
    const ALL: [Undet; N_UNDET] = [Undet::Param, Undet::Unknown];
}

static UNDET: [std::sync::atomic::AtomicU64; N_UNDET] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_UNDET];

fn note_undet(u: Undet) { UNDET[u as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// [`Clause::Undet`] because the walk gave up, counted.
fn undet_unknown() -> Clause {
    note_undet(Undet::Unknown);
    Clause::Undet
}

// ── The proof split ──────────────────────────────────────────────────────────
//
// §6.2 splits three constructors, and the `Prop` side of two of them collapses
// the term to `•`. How often that happens is worth a row of its own: it is the
// population the graph machinery no longer has to carry, and — since collapsing
// a term to `•` is the one direction of the classification that *identifies*
// things — it is also the population any doubt about `TgBackend::term_clause`
// would be about.

#[derive(Clone, Copy)]
enum Split {
    /// `⟦λx : α. e⟧ = •` — the lambda is a proof.
    LamProp,
    /// `⟦e₁ e₂⟧ = •` — the application is a proof.
    AppProp,
}

const N_SPLIT: usize = 2;

impl Split {
    const fn name(self) -> &'static str {
        match self {
            Split::LamProp => "λ interpreted as • (a proof)",
            Split::AppProp => "application interpreted as • (a proof)",
        }
    }
    const ALL: [Split; N_SPLIT] = [Split::LamProp, Split::AppProp];
}

static SPLIT: [std::sync::atomic::AtomicU64; N_SPLIT] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_SPLIT];

fn note_split(s: Split) { SPLIT[s as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// The proof-split ledger, or the empty string if nothing took the `Prop`
/// clause of `λ` or of application.
fn split_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    if !SPLIT.iter().any(|c| c.load(Relaxed) > 0) {
        return String::new()
    }
    let width = Split::ALL.iter().map(|s| s.name().len()).max().unwrap_or(20) + 6;
    let mut s = String::from("  §6.2's Prop clause for terms:\n");
    for k in Split::ALL {
        s.push_str(&format!("    {:<width$}  {:>10}\n", k.name(), SPLIT[k as usize].load(Relaxed)));
    }
    s
}

// ── The inference-typing ledger ──────────────────────────────────────────────
//
// `infer` now returns evidence, and this counts what that evidence is: how many
// nodes came back with a complete derivation, how many with one resting on the
// ambient locals, and — for the rest — which rule ran out and why.
//
// It is deliberately **not** folded into the gap total. A gap in that table is a
// definitional-equality conclusion the checker drew and could not justify; a
// node whose typing is unknown is not a conclusion the checker drew at all, and
// counting the two together would misstate both. The typings the checker *acts*
// on are the declaration typings, and those are in the `Dt` rows above.

/// Typings that came back complete, and those resting on the ambient locals.
static TY_DERIVED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static TY_CONDITIONAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static TY_GAPS: [std::sync::atomic::AtomicU64; crate::certify::N_TY_GAPS] =
    [const { std::sync::atomic::AtomicU64::new(0) }; crate::certify::N_TY_GAPS];
/// Which rule produced each typing that *did* come back — the counterpart of
/// the gap rows, and the thing that says where the work is being carried.
static TY_BY: [std::sync::atomic::AtomicU64; crate::certify::N_TY_GAPS] =
    [const { std::sync::atomic::AtomicU64::new(0) }; crate::certify::N_TY_GAPS];

fn note_ty_out(by: crate::certify::TyGap, unconditional: bool) {
    let c = if unconditional { &TY_DERIVED } else { &TY_CONDITIONAL };
    c.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    TY_BY[by as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

fn note_ty_gap(g: crate::certify::TyGap) {
    TY_GAPS[g as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

/// The same, for a reason that arrived as a string across the trait boundary.
/// Unrecognised reasons are impossible — every one comes from `TyGap::name` —
/// so an unmatched one is dropped rather than given a bucket it would misname.
fn note_ty_gap_named(reason: &'static str) {
    if let Some(g) = crate::certify::TyGap::ALL.iter().find(|g| g.name() == reason) {
        note_ty_gap(*g);
    }
}

/// The inference-typing ledger, or the empty string if inference never produced
/// a typing certificate.
fn ty_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let (d, c) = (TY_DERIVED.load(Relaxed), TY_CONDITIONAL.load(Relaxed));
    let total_gaps: u64 = TY_GAPS.iter().map(|g| g.load(Relaxed)).sum();
    if d + c + total_gaps == 0 {
        return String::new()
    }
    let width = crate::certify::TyGap::ALL.iter().map(|g| g.name().len()).max().unwrap_or(20) + 12;
    let mut s = format!(
        "  typings carried out of inference: {d} derived, {c} conditional on the ambient locals, {total_gaps} not shown\n"
    );
    for g in crate::certify::TyGap::ALL {
        let n = TY_BY[g as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("by {}", g.name())));
        }
    }
    for g in crate::certify::TyGap::ALL {
        let n = TY_GAPS[g as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("no evidence: {}", g.name())));
        }
    }
    // Why a `Π` fell under neither clause of §6.2, over *expressions* rather
    // than over typing sites. The first row is the one that matters beyond this
    // module: it bounds what any interpretation done once at a declaration's own
    // universe parameters can ever reach.
    if UNDET.iter().any(|u| u.load(Relaxed) > 0) {
        s.push_str("    Π types under neither clause of §6.2, by reason:\n");
        for u in Undet::ALL {
            let n = UNDET[u as usize].load(Relaxed);
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("  {}", u.name())));
        }
    }
    s
}

// ── The level-instantiation audit ────────────────────────────────────────────
//
// `crate::instantiations` predicts, before checking starts, every
// `(constant, level arguments)` pair the backend is going to interpret. The
// prediction is *syntactic*: it walks the export file's expression DAG for
// `Const` nodes. Two things the checker does are not in that DAG — literal
// expansion, which mints `List.nil.{0} Char` and friends, and the temporary
// declarations `inductive.rs` creates for nested inductives — and the pre-pass
// handles the first with a fixed seed list.
//
// A seed list is a claim, and a claim about coverage that is merely *believed*
// is the kind that quietly stops being true. So the backend counts what it
// actually interprets against the prediction, and the miss row is printed
// whether or not it is zero. A non-zero miss row means the pre-pass is
// incomplete: some declaration was interpreted at an instantiation nothing
// scheduled it at, so the store cannot have an entry for it and whatever the
// interpretation concluded there rests on a σ nobody checked the declaration
// under.

/// Where one interpreted constant instantiation stood relative to the schedule.
#[derive(Clone, Copy)]
enum InstAudit {
    /// The pre-pass predicted this exact `(name, levels)` pair.
    Predicted,
    /// **It did not.** This row must be zero.
    Unpredicted,
    /// The level arguments still mention a universe parameter after σ, so there
    /// is no ground pair to compare. This is every constant interpreted while
    /// an inductive block is checked (those passes take no σ), and every
    /// occurrence of a recursor's own eliminator universe.
    NonGround,
    /// The constant's name lives in a per-declaration arena — a temporary
    /// declaration minted for a nested inductive — so it has no identity the
    /// schedule could be keyed on.
    Temporary,
}

const N_INST: usize = 4;

impl InstAudit {
    const fn name(self) -> &'static str {
        match self {
            InstAudit::Predicted => "constants interpreted at a scheduled instantiation",
            InstAudit::Unpredicted => "…at an instantiation the pre-pass did NOT predict",
            InstAudit::NonGround => "…at levels still mentioning a parameter (no σ in force)",
            InstAudit::Temporary => "…of a temporary declaration, which has no stable name",
        }
    }
    const ALL: [InstAudit; N_INST] =
        [InstAudit::Predicted, InstAudit::Unpredicted, InstAudit::NonGround, InstAudit::Temporary];
}

static INST_AUDIT: [std::sync::atomic::AtomicU64; N_INST] =
    [const { std::sync::atomic::AtomicU64::new(0) }; N_INST];

fn note_inst(a: InstAudit) { INST_AUDIT[a as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// The schedule and the audit against it, or the empty string when no schedule
/// was published (the library's other entry points do not build one).
fn inst_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let Some(st) = crate::instantiations::published_stats() else { return String::new() };
    let width = InstAudit::ALL.iter().map(|a| a.name().len()).max().unwrap_or(24) + 4;
    let mut s = String::from("  level instantiations, scheduled ahead of checking:\n");
    let row = |s: &mut String, label: String, n: u64| {
        s.push_str(&format!("    {:<width$}  {n:>10}\n", label));
    };
    row(&mut s, format!("declarations ({} of them monomorphic)", st.monomorphic), st.declars as u64);
    row(&mut s, format!("demanded pairs, closed in {} rounds", st.demand_rounds), st.demand_pairs as u64);
    row(&mut s, "declarations nothing demands (checked at the default)".into(), st.defaulted as u64);
    row(&mut s, format!("(declaration, instantiation) pairs, {} rounds in all", st.rounds), st.pairs as u64);
    if st.extension_seeds > 0 {
        row(&mut s, "seeded for literal expansion, not present in the file".into(), st.extension_seeds as u64);
    }
    if st.nonground_edges > 0 {
        row(&mut s, "constant uses whose levels did not evaluate to numerals".into(), st.nonground_edges as u64);
    }
    for a in InstAudit::ALL {
        let n = INST_AUDIT[a as usize].load(Relaxed);
        // The miss row is printed at zero too: "the pre-pass predicted
        // everything" is the claim being made, and a claim that only shows up
        // when it fails is not a claim anyone reads.
        if n > 0 || matches!(a, InstAudit::Unpredicted) {
            row(&mut s, a.name().into(), n);
        }
    }
    s
}

/// Record one clause discharging an obligation. Counts *every* use, memo
/// replays and the recursive ones inside a larger derivation included, which is
/// what says which typing rule is carrying the work.
fn note_ht(c: HtClause) { HT_CLAUSES[c as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

// ── `⟦e⟧ = •`, by route ──────────────────────────────────────────────────────
//
// [`TgBackend::point_of_proof`] is the one place a *typing* fact is still
// looked for rather than handed over, so how it was answered is the measurable
// for threading the proof/proposition witnesses. The rows separate the routes
// that need nothing (`Split`, `Memo`, `Unfold`) from the two that need the two
// premises, and those two from each other: `Threaded` is the checker handing
// over what it already established, `Searched` is `has_type_a` going to look
// for it. `Searched` is split by *who asked*, because the three askers are
// starved by different stages.

/// How a `⟦e⟧ = •` equation was obtained, and — for the ones that had to look —
/// which rule asked.
#[derive(Clone, Copy)]
#[repr(usize)]
enum Pop {
    /// `⟦e⟧` is already `•`: the subject took one of §6.2's two split clauses.
    Split,
    /// Answered from the `points` memo.
    Memo,
    /// Along a defined constant's own abbreviation equation.
    Unfold,
    /// From premises the **checker handed in**. No search.
    Threaded,
    /// …asked by proof irrelevance (`Certifier::proof_irrel`).
    ThreadIrrel,
    /// …asked by projection reduction (`Certifier::proj_red`).
    ThreadProjRed,
    /// From premises found by `has_type_a`. The number this project is trying
    /// to drive to zero.
    Searched,
    /// …asked by proof irrelevance (`Certifier::proof_irrel`).
    SearchIrrel,
    /// …asked by a proof `λ`'s body clause (`point_the_subject`).
    SearchLam,
    /// …asked by the `admit` fall-through (`Certifier::admit`'s implementation).
    SearchAdmit,
    /// …asked by a *reduction rule*'s proof shortcut — `beta`, `zeta`, `delta`,
    /// `iota`. Kept apart from [`Pop::SearchAdmit`] because the two are
    /// different things: a rule concluding "both sides are proofs, so this step
    /// is reflexivity" is deriving its own claim, while the admit funnel doing
    /// it is guessing at a claim it was told cannot be justified.
    SearchRule,
    /// …and the `⟦e⟧ ∈ ⟦α⟧` premise was a hole. Inference could not justify
    /// its own result for this term; the fix is upstream of here.
    NoMem,
    /// …and the `⟦α⟧ ∈ U₀` premise was a hole, likewise.
    NoProp,
    /// …and both were in hand, and `u0_subsingleton` still refused.
    Refused,
    /// One side's `⟦α⟧ ∈ U₀` was a hole and the other side's was carried across
    /// the type equality to fill it (`share_prop`).
    ///
    /// **Zero on every corpus here**, and the row is printed for that reason:
    /// the derivation is real and nothing exercises it, which is a fact worth
    /// stating rather than a claim worth assuming. It fires when inference can
    /// justify one proposition's `∈ U₀` and not the other's, and the corpora
    /// have so far only ever produced both or neither.
    Shared,
    /// A premise route reached the derivation and it went through.
    Derived,
    /// A premise route reached the derivation and it did not.
    Failed,
}

const N_POP: usize = 17;

impl Pop {
    const fn name(self) -> &'static str {
        match self {
            Pop::Split => "already • — one of §6.2's split clauses",
            Pop::Memo => "answered from the memo",
            Pop::Unfold => "along a defined constant's own equation",
            Pop::Threaded => "from premises the checker handed in",
            Pop::ThreadIrrel => "…threaded, asked by proof irrelevance",
            Pop::ThreadProjRed => "…threaded, asked by projection reduction",
            Pop::Searched => "from premises searched for (has_type)",
            Pop::SearchIrrel => "…asked by proof irrelevance",
            Pop::SearchLam => "…asked by a proof λ's body clause",
            Pop::SearchAdmit => "…asked by the admit fall-through",
            Pop::SearchRule => "…asked by a reduction rule's proof shortcut",
            Pop::NoMem => "…threaded, and ⟦e⟧ ∈ ⟦α⟧ was a hole",
            Pop::NoProp => "…threaded, and ⟦α⟧ ∈ U₀ was a hole",
            Pop::Refused => "…threaded, both in hand, and it still refused",
            Pop::Shared => "…∈ U₀ carried from the other side of the type equality",
            Pop::Derived => "premises in hand, and u0_subsingleton closed it",
            Pop::Failed => "premises in hand, and it did not",
        }
    }
    const ALL: [Pop; N_POP] = [
        Pop::Split,
        Pop::Memo,
        Pop::Unfold,
        Pop::Threaded,
        Pop::ThreadIrrel,
        Pop::ThreadProjRed,
        Pop::Searched,
        Pop::SearchIrrel,
        Pop::SearchLam,
        Pop::SearchAdmit,
        Pop::SearchRule,
        Pop::NoMem,
        Pop::NoProp,
        Pop::Refused,
        Pop::Shared,
        Pop::Derived,
        Pop::Failed,
    ];
}

static POP: [std::sync::atomic::AtomicU64; N_POP] = [const { std::sync::atomic::AtomicU64::new(0) }; N_POP];

fn note_pop(p: Pop) { POP[p as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// The `⟦e⟧ = •` ledger, or the empty string if no proof was ever pointed.
fn pop_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let counts: Vec<u64> = Pop::ALL.iter().map(|p| POP[*p as usize].load(Relaxed)).collect();
    if counts.iter().all(|n| *n == 0) {
        return String::new()
    }
    let width = Pop::ALL.iter().map(|p| p.name().len()).max().unwrap_or(24) + 4;
    let mut s = String::from("  a proof's interpretation shown to be •, by route:\n");
    for (p, n) in Pop::ALL.iter().zip(&counts) {
        // Every row prints, zero included: "nothing searched" is the claim, and
        // a claim that only appears when it fails is not a claim anyone reads.
        s.push_str(&format!("    {:<width$}  {n:>12}\n", p.name()));
    }
    s
}

/// Record one top-level obligation and whether it was settled.
fn note_ht_call(ok: bool) {
    use std::sync::atomic::Ordering::Relaxed;
    HT_ASKED.fetch_add(1, Relaxed);
    if ok {
        HT_SETTLED.fetch_add(1, Relaxed);
    }
}

/// Record the shape of one obligation that was not settled.
fn note_ht_miss(m: HtMiss) { HT_MISSES[m as usize].fetch_add(1, std::sync::atomic::Ordering::Relaxed); }

/// The typing ledger, or the empty string if `has_type` was never asked.
fn ht_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let (asked, settled) = (HT_ASKED.load(Relaxed), HT_SETTLED.load(Relaxed));
    // The declaration-typing ledger prints whenever a declaration reached the
    // boundary, whether or not any `has_type` obligation was ever asked — a
    // run small enough to settle every obligation structurally still stores
    // (or quantifies) its declaration typings, and a section that vanishes
    // with the recursion reads as zero to every consumer of the report.
    if asked == 0 && DT[Dt::Seen as usize].load(Relaxed) == 0 {
        return String::new()
    }
    let width = HtClause::ALL
        .iter()
        .map(|c| c.name().len())
        .chain(HtMiss::ALL.iter().map(|m| m.name().len()))
        .max()
        .unwrap_or(24)
        + 6;
    let mut s = format!(
        "  typing obligations (⟦a⟧ ∈ ⟦A⟧): {asked} asked, {settled} discharged, {} carried as assumptions\n  \
         deepest derivation: {}\n",
        asked - settled,
        HT_DEPTH_USED.load(Relaxed),
    );
    for c in HtClause::ALL {
        let n = HT_CLAUSES[c as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("by {}", c.name())));
        }
    }
    for m in HtMiss::ALL {
        let n = HT_MISSES[m as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("not shown: {}", m.name())));
        }
    }
    for t in HtTarget::ALL {
        let n = HT_TARGETS[t as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("stated at: {}", t.name())));
        }
    }
    for m in HtMiss::ALL {
        let n = HT_RAWS[m as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("raw fallback, about: {}", m.name())));
        }
    }
    for t in HtTarget::ALL {
        let n = HT_RAW_TARGETS[t as usize].load(Relaxed);
        if n > 0 {
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("raw fallback, stated at: {}", t.name())));
        }
    }
    let peels = PEEL[PeelStop::Family as usize].load(Relaxed);
    if peels > 0 {
        s.push_str("    guarded families, and how far discharging them got:\n");
        for st in PeelStop::ALL {
            let n = PEEL[st as usize].load(Relaxed);
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("  {}", st.name())));
        }
    }
        for m in HtMiss::ALL {
            let n = PEEL_SHAPE[m as usize].load(Relaxed);
            if n > 0 {
                s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("  family about: {}", m.name())));
            }
        }
        for t in HtTarget::ALL {
            let n = PEEL_TARGET[t as usize].load(Relaxed);
            if n > 0 {
                s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("  family stated at: {}", t.name())));
            }
        }
    if DT[Dt::Seen as usize].load(Relaxed) > 0 {
        s.push_str("    constant typings, stored once at the declaration:\n");
        for d in Dt::ALL {
            let n = DT[d as usize].load(Relaxed);
            s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("  {}", d.name())));
        }
    }
    let reached = TB[TbMiss::Reached as usize].load(Relaxed);
    if reached > 0 {
        s.push_str(&format!(
            "    {:<width$}  {reached:>10}\n",
            "target beta: redexes reached, of which"
        ));
        for (l, m) in [("premise x ∈ A not settled", TbMiss::Domain), ("reduct still not typeable", TbMiss::Reduct)] {
            let n = TB[m as usize].load(Relaxed);
            if n > 0 {
                s.push_str(&format!("    {:<width$}  {n:>10}\n", format!("  …{l}")));
            }
        }
    }
    s
}

/// Render what the TG kernel actually derived over this run.
pub fn global_report() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let g = TOTALS.lock().expect("tg totals poisoned");
    let proved = PROVED.load(Relaxed);
    let mut rows: Vec<(&'static str, u64)> = g.clone().unwrap_or_default();
    // An escaped assumption is a gap in exactly the sense the rest of this table
    // measures: a conclusion the checker took that was not derived outright.
    // It is added here rather than tallied through `merge_one` because it is
    // only knowable once the whole run is over.
    let escapes = escaped();
    if escapes > 0 {
        rows.push((ESCAPED, escapes));
    }
    rows.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    let width = rows.iter().map(|(r, _)| r.len() + 5).chain([24]).max().unwrap_or(24);
    let mut s = String::from("Tarski-Grothendieck kernel: derivation coverage\n");
    s.push_str(&format!("  {:<width$}  {proved:>12}\n", "derived (real kernel Thm)"));
    let total: u64 = rows.iter().map(|(_, n)| *n).sum();
    for (r, n) in &rows {
        s.push_str(&format!("  {:<width$}  {n:>12}\n", format!("gap: {r}")));
    }
    s.push_str(&format!("  {:<width$}  {total:>12}\n", "TOTAL gaps"));
    let made = CONDITIONAL.load(Relaxed);
    if made > 0 {
        s.push_str(&format!(
            "  conditional derivations: {} made ({} of them copies), {} accounted for by a rule, {} escaped (max {} assumptions)\n",
            made,
            CONDITIONAL_COPIES.load(Relaxed),
            CONSUMED.load(Relaxed),
            escapes,
            MAX_ASSUMED.load(Relaxed),
        ));
    }
    let unmatched: Vec<(&str, u64)> = [("app_cong", Rule::AppCong), ("trans", Rule::Trans), ("symm", Rule::Symm)]
        .into_iter()
        .map(|(n, r)| (n, UNMATCHED[r as usize].load(Relaxed)))
        .collect();
    if unmatched.iter().any(|(_, n)| *n > 0) {
        s.push_str("  derivations that failed their guard (did not match the claim):");
        for (n, c) in &unmatched {
            s.push_str(&format!(" {n}={c}"));
        }
        s.push('\n');
    }
    let (ity_asked, ity_got) = (IND_TY_ASKED.load(Relaxed), IND_TY_DERIVED.load(Relaxed));
    if ity_asked > 0 {
        s.push_str(&format!(
            "  {:<width$}  {:>12}\n",
            "⟦T⟧ ∈ ⟦Type 0⟧: fresh (subject, target) pairs matched / derived",
            format!("{ity_asked} / {ity_got}"),
        ));
    }
    let anchors = FALSE_ANCHORS.load(Relaxed);
    if anchors > 0 {
        s.push_str(&format!(
            "  {:<width$}  {anchors:>12}\n",
            "⟦False⟧ anchored: ⊢ ∀x. ¬(x ∈ ⟦False⟧) at the interpretation's own term",
        ));
    }
    let (bv_minted, bv_reused) = (BINDER_VARS_MINTED.load(Relaxed), BINDER_VARS_REUSED.load(Relaxed));
    if bv_minted + bv_reused > 0 {
        s.push_str(&format!(
            "  {:<width$}  {:>12}\n",
            "interpretation binder opens: variables minted / reused at a (level, type) key",
            format!("{bv_minted} / {bv_reused}"),
        ));
    }
    s.push_str(&ht_report());
    s.push_str(&pop_report());
    s.push_str(&ty_report());
    s.push_str(&split_report());
    s.push_str(&gen_report());
    s.push_str(&inst_report());
    if total == 0 && proved > 0 {
        s.push_str("  >> every definitional-equality step was fully derived\n");
    }
    s
}

// Gated on the feature as well as on `test`: these exercise the TG backend, and
// several of them hand a `TgCert` to `certify::is_unconditional`, whose
// parameter is `Cert` — which is `()` in a build without `--features tg`. Left
// ungated the module broke `cargo test` and two `ci/check.sh` steps for the
// default build while passing under `--features tg`, which is the configuration
// everyone was running.
#[cfg(all(test, feature = "tg"))]
mod tests {
    use super::*;

    /// A fresh constant, usable to instantiate a quantifier at.
    fn constant(env: &mut Env) -> Term { Term::apply(env.declare(0), vec![]) }

    /// **A de Bruijn-level local is one kernel variable per (level, declared
    /// type) — the level alone does not identify it, and neither does the type
    /// alone.** This is [`LocalKey`]'s contract, pinned directly.
    ///
    /// An *invariant* fixture, not a regression: no corpus declaration is known
    /// to miscompile under the level-only key, because two same-level locals
    /// are never simultaneously in scope ([`TcCtx::replace_dbj_level`] retires
    /// a level before it is reused) and every certificate is checked against
    /// its claim. What the level-only key *did* do is interpret successive
    /// same-level binders of unrelated types as one variable, so a memo keyed
    /// by anything containing that variable could hold a statement made at one
    /// binder's type and hand it back at the other's. The caches this enables
    /// are keyed at exactly this grain, so the invariant is pinned here, at
    /// the map itself.
    ///
    /// **Three level-locals, deliberately** — `(3, A)`, `(3, B)`, `(4, A)`:
    /// with only two, a key that projects out either component still passes
    /// one of the assertions, so each projection needs its own witness to go
    /// red. Mutation-verified: rekeying `Level` on the level alone fails the
    /// `(3, A) ≠ (3, B)` assertion; rekeying on the type alone fails
    /// `(3, A) ≠ (4, A)`.
    ///
    /// The fourth atom pins the key-space split: `DbjLevel(0)` and `Unique(0)`
    /// agree numerically and in type, and must still be two variables — the
    /// separation the retired `(1 << 32)` bit used to encode, now structural
    /// in [`LocalKey`]'s constructors.
    ///
    /// [`a_reused_level_at_a_new_type_is_a_new_variable`] is the same contract
    /// exercised through the constructors the checker actually uses.
    #[test]
    fn a_level_local_is_identified_by_level_and_type() {
        crate::tests::util::test_export_file(None, |export| {
            export.with_ctx(|ctx| {
                let env = export.new_env(crate::env::EnvLimit::Empty);
                let mut be = TgBackend::new(&env);

                let x = ctx.str1("x");
                let y = ctx.str1("y");
                let zero = ctx.zero();
                let one = ctx.succ(zero);
                let ty_a = ctx.mk_sort(zero);
                let ty_b = ctx.mk_sort(one);
                let style = crate::expr::BinderStyle::Default;

                let l3a = ctx.remake_dbj_level(x, style, ty_a, 3);
                let l3a_renamed = ctx.remake_dbj_level(y, style, ty_a, 3);
                let l3b = ctx.remake_dbj_level(x, style, ty_b, 3);
                let l4a = ctx.remake_dbj_level(x, style, ty_a, 4);

                let t3a = be.interp(ctx, l3a);
                let t3a_renamed = be.interp(ctx, l3a_renamed);
                let t3b = be.interp(ctx, l3b);
                let t4a = be.interp(ctx, l4a);

                // Same level, same type: the same variable — the binder name is
                // not part of the variable's identity, and there is nothing
                // else left for two such locals to differ in.
                assert_eq!(
                    t3a, t3a_renamed,
                    "level 3 at type A must be one variable whatever the binder is called"
                );
                // Same level, different type: levels are reused across a
                // declaration's telescopes, so without the type in the key
                // these two would be one variable and a memoised statement
                // made at `A` would be handed back at `B`.
                assert_ne!(t3a, t3b, "level 3 at type B must not reuse level 3 at type A's variable");
                // Different level, same type: two locals of one telescope may
                // share a type and are still two variables.
                assert_ne!(t3a, t4a, "level 4 at type A must not reuse level 3 at type A's variable");

                // `Unique(0)` versus `DbjLevel(0)` at the same type: the two
                // halves of the id space must not alias.
                let l0a = ctx.remake_dbj_level(x, style, ty_a, 0);
                let u0 = ctx.mk_unique(x, style, ty_a);
                let (t0a, tu0) = (be.interp(ctx, l0a), be.interp(ctx, u0));
                assert_ne!(t0a, tu0, "a unique-id local must never alias a level local");

                // And the memo is a memo: a second interpretation of the same
                // local is the same variable, not a fresh one.
                assert_eq!(t3a, be.interp(ctx, l3a), "re-interpreting a local must hit its variable");
            })
        })
        .unwrap()
    }

    /// **The live route to a level collision, exercised end to end.**
    ///
    /// `mk_dbj_level` opens a binder at the context's counter and
    /// [`TcCtx::replace_dbj_level`] hands the level back on close — the
    /// counter is documented *non-monotonic* (`util.rs`), and
    /// `def_eq_binder_aux` gives back whole frames at once. So sequential
    /// sibling binders in one declaration share a level, at whatever types
    /// they declare, inside one backend. This is not a corner: probe-measured
    /// on this branch, a level was re-minted at a type already-seen levels did
    /// not have **5659 times over `good/init-prelude.ndjson`** and 354 times
    /// across 58 of the 91 tutorial exports. Under the level-only key every
    /// one of those was the *same* kernel variable as its differently-typed
    /// predecessor.
    ///
    /// Three openings, deliberately — `A`, then `B`, then `A` again: the
    /// middle one pins the split and the outer pair pins that the split is
    /// *by type*, not "fresh per opening", which a two-opening test cannot
    /// distinguish. Mutation-verified together with
    /// [`a_level_local_is_identified_by_level_and_type`]: the level-only key
    /// turns the middle assertion red.
    #[test]
    fn a_reused_level_at_a_new_type_is_a_new_variable() {
        crate::tests::util::test_export_file(None, |export| {
            export.with_ctx(|ctx| {
                let env = export.new_env(crate::env::EnvLimit::Empty);
                let mut be = TgBackend::new(&env);

                let x = ctx.str1("x");
                let zero = ctx.zero();
                let one = ctx.succ(zero);
                let (ty_a, ty_b) = (ctx.mk_sort(zero), ctx.mk_sort(one));
                let style = crate::expr::BinderStyle::Default;

                // Open `x : A`, interpret it, close the binder.
                let first = ctx.mk_dbj_level(x, style, ty_a);
                let t_first = be.interp(ctx, first);
                ctx.replace_dbj_level(first);

                // Open `x : B`. The premise of this whole test is that the
                // counter handed the level back; assert it, so that a future
                // monotonic counter turns this test into a loud question
                // rather than a silent vacuity.
                let second = ctx.mk_dbj_level(x, style, ty_b);
                match (ctx.read_expr(first), ctx.read_expr(second)) {
                    (Expr::Local { id: i1, .. }, Expr::Local { id: i2, .. }) => {
                        assert_eq!(i1, i2, "close must hand the level back — the live route's premise")
                    }
                    _ => panic!("mk_dbj_level did not build locals"),
                }
                let t_second = be.interp(ctx, second);
                assert_ne!(
                    t_first, t_second,
                    "a reused level at a new type must be a new variable"
                );

                // Reopen at `A`: same level, same type — the same variable
                // again, so the split above is by type and not per opening.
                ctx.replace_dbj_level(second);
                let third = ctx.mk_dbj_level(x, style, ty_a);
                assert_eq!(
                    t_first,
                    be.interp(ctx, third),
                    "the same level at the same type must be the same variable across reopenings"
                );
            })
        })
        .unwrap()
    }

    /// **The interpretation's own binder opens reuse kernel variables by
    /// `(level, type)`.**
    ///
    /// `interp_lambda` used to open every binder at a `mk_unique` local: a
    /// fresh kernel variable per occurrence, so two α-identical lambdas —
    /// distinct `ExprPtr`s that differ only in the binder's *name* — never
    /// shared a variable, and every interpretation-memo entry about the opened
    /// body was unreachable from the second occurrence by construction. Opened
    /// at the expression-derived de Bruijn level ([`TgBackend::open_level`])
    /// and keyed by `(level, ⟦domain⟧)`, they share.
    ///
    /// **Three lambdas, deliberately** — same shape twice (`l1`, `l2`, binder
    /// names apart) and the same shape at a different domain (`l3`): with only
    /// two, a key that drops the type still passes the sharing half, so the
    /// split needs its own witness — the same three-atom argument as
    /// [`a_level_local_is_identified_by_level_and_type`]. A fourth subject
    /// (`l4`) embeds a level-0 local of the same domain type in its body, and
    /// pins [`TgBackend::open_level`]'s collision clause: the binder must open
    /// *above* every level its body mentions, or it captures the embedded
    /// local's variable. The final assertions pin that no counter moves: the
    /// opens touch neither `dbj_level_counter` (there is nothing to close) nor
    /// `unique_counter` (nothing on this path mints a unique local).
    ///
    /// Mutation-verified: reverting the open to `mk_unique` fails the sharing
    /// assertion; making `open_level` return 0 unconditionally fails `l4`'s
    /// no-capture assertion.
    #[test]
    fn interpretation_binders_share_variables_by_level_and_type() {
        crate::tests::util::test_export_file(None, |export| {
            export.with_ctx(|ctx| {
                let env = export.new_env(crate::env::EnvLimit::Empty);
                let mut be = TgBackend::new(&env);

                let x = ctx.str1("x");
                let y = ctx.str1("y");
                let zero = ctx.zero();
                let one = ctx.succ(zero);
                let (ty_a, ty_b) = (ctx.mk_sort(zero), ctx.mk_sort(one));
                let style = crate::expr::BinderStyle::Default;
                let v0 = ctx.mk_var(0);

                // λ (x : Prop). x and λ (y : Prop). y — α-identical, two nodes.
                let l1 = ctx.mk_lambda(x, style, ty_a, v0);
                let l2 = ctx.mk_lambda(y, style, ty_a, v0);
                // λ (x : Type). x — the same shape at another domain.
                let l3 = ctx.mk_lambda(x, style, ty_b, v0);
                assert_ne!(l1, l2, "two nodes, or nothing is tested");

                let t1 = be.interp(ctx, l1);
                let t2 = be.interp(ctx, l2);
                let t3 = be.interp(ctx, l3);
                assert_eq!(t1, t2, "α-identical lambdas must interpret to one term");
                assert_ne!(t1, t3, "a different domain is a different function");

                let var_of = |be: &TgBackend<'_, '_, '_>, e| be.lam_sites.get(&e).map(|s| s.var);
                let (v1, v2, v3) = (var_of(&be, l1), var_of(&be, l2), var_of(&be, l3));
                assert!(v1.is_some() && v2.is_some() && v3.is_some(), "all three are Type-clause lambdas");
                assert_eq!(v1, v2, "one (level, type) key, one kernel variable — this is the reuse");
                assert_ne!(v1, v3, "a different domain type must keep its own variable");

                // A binder whose body embeds a level-0 local of the same
                // domain type: the open must land above it, not on it.
                let x0 = ctx.remake_dbj_level(x, style, ty_a, 0);
                let body4 = ctx.mk_app(v0, x0);
                let l4 = ctx.mk_lambda(y, style, ty_a, body4);
                let t_x0 = be.interp(ctx, x0);
                be.interp(ctx, l4);
                let v4 = var_of(&be, l4).expect("l4 is a Type-clause lambda");
                assert_ne!(
                    Term::var(v4),
                    t_x0,
                    "the binder captured the embedded level-0 local — open_level must sit above every embedded level"
                );

                // No counter moves: nothing to close, and nothing unique.
                assert_eq!(ctx.dbj_level_counter, 0, "an interpretation open must not touch the checker's counter");
                assert_eq!(ctx.unique_counter, 0, "the lambda path must not mint unique locals");
            })
        })
        .unwrap()
    }

    /// **`def_eq_local` is a rule, split along [`LocalKey`]'s own grain.**
    ///
    /// The census's `def_eq_local` row: two locals with one id used to admit
    /// (`Admit::Local`) after establishing — and discarding — that their
    /// declared types are def-eq. Under `LocalKey` the honest answer splits:
    ///
    /// * same level, types interpreting to the **same term** — one kernel
    ///   variable, so reflexivity is a complete derivation (`l1` / `l2`, which
    ///   differ only in binder name);
    /// * same level, types **merely definitionally equal** — two kernel
    ///   variables, no rule relates them, and the step must stay a counted gap
    ///   rather than become a forged reflexivity (`l1` / `l3`, whose type is
    ///   one beta step away).
    ///
    /// Both directions are load-bearing. Mutation-verified: reverting
    /// `local_eq` to a bare admit turns the first assertion red; making it
    /// return reflexivity without comparing interpretations turns the second
    /// red.
    #[test]
    fn def_eq_local_splits_along_the_local_key() {
        crate::tests::util::test_export_file(None, |export| {
            export.with_tc(crate::env::EnvLimit::Empty, |tc| {
                let x = tc.ctx.str1("x");
                let y = tc.ctx.str1("y");
                let zero = tc.ctx.zero();
                let one = tc.ctx.succ(zero);
                let ty_a = tc.ctx.mk_sort(zero);
                let sort1 = tc.ctx.mk_sort(one);
                let style = crate::expr::BinderStyle::Default;

                // Same level, same declared type, different binder *name* — two
                // distinct `ExprPtr`s (a `Local` hashes its name) that
                // interpret to one variable.
                let l1 = tc.ctx.remake_dbj_level(x, style, ty_a, 3);
                let l2 = tc.ctx.remake_dbj_level(y, style, ty_a, 3);
                assert_ne!(l1, l2, "the two locals must be two nodes, or nothing is tested");
                let r = tc.def_eq(l1, l2);
                let cert = r.expect("same id at one type must still be def-eq");
                assert!(
                    cert.is_proved(),
                    "one LocalKey means one variable: reflexivity, not an admit — got {cert:?}"
                );
                assert!(
                    crate::certify::is_unconditional(&cert),
                    "reflexivity of a variable rests on nothing"
                );

                // Same level, type one beta step away: `(λ z : Sort 1. z) A`
                // is def-eq to `A` but interprets to a different term, so this
                // is *two* variables and the rule must decline, not forge.
                let v0 = tc.ctx.mk_var(0);
                let id_lam = tc.ctx.mk_lambda(x, style, sort1, v0);
                let ty_b = tc.ctx.mk_app(id_lam, ty_a);
                let l3 = tc.ctx.remake_dbj_level(x, style, ty_b, 3);
                let r2 = tc.def_eq(l1, l3);
                let cert2 = r2.expect("the checker's verdict is unchanged: same id, def-eq types");
                assert!(
                    matches!(cert2, TgCert::Admitted(_)),
                    "two distinct variables have no equating rule — this must stay a counted gap, got {cert2:?}"
                );
            })
        })
        .unwrap()
    }

    /// **The `Bool.true` shortcut composes the legs it already holds.**
    ///
    /// `def_eq`'s shortcut — `y_n` is `Bool.true` and `whnf(x_n)` reduces to
    /// it — used to discard the entry legs *and* the recorded reduction and
    /// answer `Admit::BoolTrue`. Every leg was in hand: `x ≡ x_n` from the
    /// no-unfolding reduction, `x_n ≡ whnf(x_n)` from the trace memo, and
    /// `whnf(x_n)` *is* `y_n` by hash-consing. The census (§1.4) called the
    /// composition mechanical; this pins it.
    ///
    /// Two subjects, deliberately: `boolId` alone exercises the pure delta
    /// middle leg (`Proved`, resting on the defining equation and nothing
    /// else), and `(λ b : Bool. b) boolId` puts a beta leg on the entry
    /// reduction as well, so the `x_leg` composition — not just the middle —
    /// is load-bearing. Under the admitting shortcut both were
    /// `Admitted("bool_true")`.
    #[test]
    fn bool_true_shortcut_composes_its_legs() {
        crate::tests::util::test_export_file(
            Some(std::path::Path::new("test_resources/BoolTrue/config.json")),
            |export| {
                export.with_tc(crate::env::EnvLimit::PpUnlimited, |tc| {
                    let bool_true = tc.ctx.c_bool_true().expect("the export declares Bool.true");
                    let no_levels = tc.ctx.alloc_levels_slice(&[]);
                    let n_bool = tc.ctx.str1("Bool");
                    let c_bool = tc.ctx.mk_const(n_bool, no_levels);
                    let n_boolid = tc.ctx.str1("boolId");
                    let bool_id = tc.ctx.mk_const(n_boolid, no_levels);

                    // One delta step: the middle leg is the defining equation,
                    // a complete unconditional derivation.
                    let r = tc.def_eq(bool_id, bool_true);
                    let cert = r.expect("boolId unfolds to Bool.true");
                    assert!(
                        cert.is_proved() && crate::certify::is_unconditional(&cert),
                        "a delta step to Bool.true is fully derived, not admitted — got {cert:?}"
                    );

                    // A beta step on the entry leg as well: the composition has
                    // to thread `x ≡ x_n` through, not only the middle. The
                    // beta step's domain obligation may be carried as an
                    // antecedent, so `Conditional` is as green as `Proved`
                    // here; only an admission is the old, discarded answer.
                    let n_b = tc.ctx.str1("b");
                    let style = crate::expr::BinderStyle::Default;
                    let v0 = tc.ctx.mk_var(0);
                    let id_lam = tc.ctx.mk_lambda(n_b, style, c_bool, v0);
                    let x2 = tc.ctx.mk_app(id_lam, bool_id);
                    let r2 = tc.def_eq(x2, bool_true);
                    let cert2 = r2.expect("(λ b. b) boolId reduces to Bool.true");
                    assert!(
                        !matches!(cert2, TgCert::Admitted(_)),
                        "every leg exists — the composite must not be an admission, got {cert2:?}"
                    );
                })
            },
        )
        .unwrap()
    }

    /// **`infer_app` composes the `ensure_pi` reduction leg into the head's
    /// typing** — the census's silently dropped leg (§1.2, `infer_app` row).
    ///
    /// `f : (λ T : Sort 1. T) Arrow` applied to `p : Bool`: the head's type
    /// must be beta-reduced (then delta-unfolded) before the `Π` appears, so
    /// the head's typing — stated at the *unreduced* type — has to be
    /// converted along that reduction or the application rule's premise is
    /// about the wrong type. `ty_bridge`'s delta-only rescue cannot cross the
    /// beta step, which is what makes this fixture red before the leg is
    /// composed: the typing came out `Gap` (`ty_app`), and comes out `Derived`
    /// once `infer_app` converts via `ty_conv`.
    #[test]
    fn ensure_pi_leg_is_composed_into_the_head_typing() {
        crate::tests::util::test_export_file(
            Some(std::path::Path::new("test_resources/BoolTrue/config.json")),
            |export| {
                export.with_tc(crate::env::EnvLimit::PpUnlimited, |tc| {
                    let no_levels = tc.ctx.alloc_levels_slice(&[]);
                    let n_bool = tc.ctx.str1("Bool");
                    let c_bool = tc.ctx.mk_const(n_bool, no_levels);
                    let n_arrow = tc.ctx.str1("Arrow");
                    let c_arrow = tc.ctx.mk_const(n_arrow, no_levels);
                    let style = crate::expr::BinderStyle::Default;

                    // `(λ T : Sort 1. T) Arrow` — one beta step, then one
                    // delta step, away from `Π b : Bool. Bool`.
                    let n_t = tc.ctx.str1("T");
                    let zero = tc.ctx.zero();
                    let one = tc.ctx.succ(zero);
                    let sort1 = tc.ctx.mk_sort(one);
                    let v0 = tc.ctx.mk_var(0);
                    let id_lam = tc.ctx.mk_lambda(n_t, style, sort1, v0);
                    let f_ty = tc.ctx.mk_app(id_lam, c_arrow);

                    let n_f = tc.ctx.str1("f");
                    let n_p = tc.ctx.str1("p");
                    let f = tc.ctx.mk_dbj_level(n_f, style, f_ty);
                    let p = tc.ctx.mk_dbj_level(n_p, style, c_bool);
                    let app = tc.ctx.mk_app(f, p);

                    let r = tc.infer(app, crate::tc::InferFlag::Check);
                    assert_eq!(r.ty, c_bool, "the application lands in Bool");
                    assert!(
                        matches!(r.cert, TgTyping::Derived { .. }),
                        "the head typing must be converted along the ensure_pi leg and \
                         carried into the application rule — got {:?}",
                        r.cert
                    );
                })
            },
        )
        .unwrap()
    }

    /// **A stored nest must not be adopted at a different walk.**
    ///
    /// `Shared::rec_nests` and `Shared::gen_ty_nests` hand a nest built by one
    /// declaration's backend to another's. What makes that safe is
    /// [`nest_agrees`]. This pins each of its clauses separately, because each
    /// one catches a failure the others do not see.
    ///
    /// **Three levels, deliberately.** At depth two, swapping the domains and
    /// swapping the variables produce the same wrong walk, so a two-level test
    /// passes whether the guard compares the spines pointwise or only their
    /// ends, and whether it associates the nest left or right. At depth three
    /// the two are distinguishable and each assertion fails for its own reason.
    ///
    /// **Mutation-verified**, one clause at a time. Dropping the `stored_vars`
    /// comparison fails the variable assertion; dropping `stored_doms` fails
    /// the *deep* domain assertion; dropping the `head` half of the equation
    /// check fails the foreign-abbreviation assertion; and weakening
    /// `nest_replay` to ignore `doms[0]` fails the level-0 domain assertion.
    /// None of the four is caught by the corpus: a wrongly adopted nest still
    /// has to pass the ι rule's own claim check, so the damage shows up as a
    /// silently rebuilt derivation and a moved counter, not as a changed
    /// verdict.
    #[test]
    fn a_stored_nest_is_only_adopted_at_the_walk_it_was_built_over() {
        let mut env = Env::new();
        // Three levels: `lam0(D0)`, `lam1(x0, D1)`, `lam2(x0, x1, D2)`.
        let lams = [env.declare(1), env.declare(2), env.declare(3)];
        let vars: Vec<FreeVar> = (0..3).map(|_| env.fresh_var()).collect();
        let doms: Vec<Term> = (0..3).map(|_| constant(&mut env)).collect();

        // Spelled out rather than taken from `nest_replay`: a test that builds
        // its expectation with the function under test cannot see that function
        // read the wrong domain. (It did not: replacing `doms[0]` by
        // `doms[len-1]` passed until this line stopped calling `nest_replay`.)
        let outer = Term::apply(lams[0], vec![doms[0].clone()]);
        assert_eq!(nest_replay(&lams, &doms), Some(outer.clone()), "the outermost graph is `lam0(D0)`");
        // The stored equation, as `define_abbrev` would have left it.
        let (head_sym, head_def) =
            derived::define_abbrev(&mut env, &[], &outer).expect("abbreviate the nest");
        let head = Term::apply(head_sym, vec![]);

        assert!(
            nest_agrees(&vars, &doms, &head, &head_def, &lams, &vars, &doms),
            "the walk it was built over must be accepted"
        );

        // The same declaration at permuted *domains* — the case where the
        // field types interpret to the same three terms in a different order.
        //
        // The swap is of levels **1 and 2**, not of 0 and 1, and that is the
        // whole point of the assertion. `head_def` mentions `doms[0]` and
        // nothing else, so a swap touching level 0 is caught by the head
        // equation and says nothing about whether the domains are compared at
        // all. Only a swap below level 0 isolates the pointwise clause. (This
        // test passed a swap of 0 and 1 with the clause deleted, which is how
        // the distinction was found.)
        let deep_swap = vec![doms[0].clone(), doms[2].clone(), doms[1].clone()];
        assert!(
            !nest_agrees(&vars, &doms, &head, &head_def, &lams, &vars, &deep_swap),
            "a walk over different domains must be declined below level 0 too"
        );
        // …and level 0 as well, which the head equation is what catches.
        let top_swap = vec![doms[1].clone(), doms[0].clone(), doms[2].clone()];
        assert!(
            !nest_agrees(&vars, &doms, &head, &head_def, &lams, &vars, &top_swap),
            "a walk over different domains must be declined at level 0"
        );

        // The same domains at permuted *variables* — the case where the
        // adopting walk opened the binders at other kernel variables, which is
        // exactly what `reuse_rec_nest` exists to prevent. Note that the head
        // equation is unchanged and true here: only the spine differs.
        let swapped_vars = vec![vars[0], vars[2], vars[1]];
        assert!(
            !nest_agrees(&vars, &doms, &head, &head_def, &lams, &swapped_vars, &doms),
            "a walk over different variables must be declined"
        );

        // A different abbreviation of the very same body. The equation is true
        // and its right-hand side is right; only the head is somebody else's,
        // which is the mislabelling the whole store exists to avoid.
        let (other_sym, _) =
            derived::define_abbrev(&mut env, &[], &outer).expect("a second abbreviation");
        let other = Term::apply(other_sym, vec![]);
        assert_ne!(other, head, "two `define_abbrev` calls must mint two symbols");
        assert!(
            !nest_agrees(&vars, &doms, &other, &head_def, &lams, &vars, &doms),
            "an equation about another symbol must be declined"
        );
    }

    /// **A general nest's bottom is two derivations, and both are checked, by
    /// identity.**
    ///
    /// [`same_bottom`]'s first three arms compare one `Rc` because their
    /// bottoms *are* one; [`RecBottom::General`] carries a [`GenRec`] and a
    /// [`GenTyNest`], and dropping either comparison hands a later backend a
    /// nest over somebody else's carrier or somebody else's `⟦T⟧`. The corpus
    /// cannot see either mutation — on `init-prelude` the two halves never
    /// disagree, so `shared nests declined` stays 0 and every verdict, gap and
    /// escape is unchanged — which is why the discrimination is asserted here
    /// instead. See [`pair_ptr_eq`] for why the arm is factored out at all.
    ///
    /// The last assertion is the one that is not about `&&`: two `Rc`s holding
    /// **equal values at different addresses** must be declined. That is not a
    /// hypothetical shape — it is exactly what a rebuilt [`GenInd`] produces.
    ///
    /// Verified to fire three ways: deleting either conjunct fails the
    /// corresponding "one half differs" assertion, and replacing `&&` with `||`
    /// fails both. The fourth mutation — `==` for `Rc::ptr_eq` — turns out to be
    /// **impossible**: it needs a `PartialEq` bound, and neither [`GenRec`] nor
    /// [`GenTyNest`] has one, so the real instantiation stops compiling. That is
    /// a stronger guarantee than a test, and the equal-values assertion is what
    /// records the intent should either type ever acquire `PartialEq`.
    #[test]
    fn a_general_bottom_agrees_only_when_both_halves_are_the_same_derivation() {
        let (a1, b1) = (Rc::new(7u32), Rc::new("t".to_string()));
        let (a2, b2) = (Rc::new(7u32), Rc::new("t".to_string()));

        assert!(pair_ptr_eq((&a1, &b1), (&a1, &b1)), "the very same pair must be accepted");
        assert!(
            !pair_ptr_eq((&a1, &b1), (&a2, &b1)),
            "a different carrier must be declined even at the same type former"
        );
        assert!(
            !pair_ptr_eq((&a1, &b1), (&a1, &b2)),
            "a different type former must be declined even over the same carrier"
        );
        assert_eq!((*a1, &*b1), (*a2, &*b2), "the witnesses must be equal by value");
        assert!(
            !pair_ptr_eq((&a1, &b1), (&a2, &b2)),
            "a rebuilt derivation must be declined, however equal it looks"
        );
    }

    /// **A stored constructor nest must not be adopted at other terms.**
    ///
    /// [`Shared::gen_ctor_nests`] hands one declaration's backend the `⟦cᵢ⟧`,
    /// the [`CtorRule`] and the [`GenCtorBridge`] another built. What makes that
    /// safe is [`ctor_nest_agrees`], and this pins each of the things it decides
    /// separately, because no one of them implies the rest.
    ///
    /// **Three levels, deliberately.** At depth two a swap of the domains and a
    /// swap of the variables are the same wrong walk, and a left-nested spine
    /// and a right-nested one have the same *set* of nodes; at depth three each
    /// is distinguishable and each assertion fails for its own reason. The
    /// domain swap is of levels **1 and 2** for [`nest_agrees`]'s recorded
    /// reason: a swap touching level 0 is caught by more than one clause and so
    /// isolates none.
    ///
    /// **Mutation-verified**, five mutations and five failures. Dropping the
    /// `rule` comparison fails the association and wrong-head assertions;
    /// dropping the `bridge` comparison fails the carrier-term assertion;
    /// building the spine right-nested, and iterating the premises in reverse,
    /// each fail the *positive* assertion, which is why that one compares the
    /// spine it hands back rather than merely accepting. The fifth is the one
    /// that isolates the domains: comparing only the two formulas' consequents
    /// and ignoring their antecedent — the only place a domain occurs — keeps
    /// every other assertion passing and fails the deep-domain one. None of the
    /// five is caught by the corpus: an adopted nest still has to pass
    /// `has_type_a`'s and the ι rule's own claim checks, so the damage is a
    /// silently rebuilt derivation and a moved counter, not a changed verdict.
    #[test]
    fn a_stored_constructor_nest_is_only_adopted_at_the_terms_it_was_built_over() {
        let mut env = Env::new();
        let app = env.declare(2);
        let ct = constant(&mut env);
        let other_ct = constant(&mut env);
        let ty_spine = constant(&mut env);
        let bottom = constant(&mut env);
        let vars: Vec<FreeVar> = (0..3).map(|_| env.fresh_var()).collect();
        let doms: Vec<Term> = (0..3).map(|_| constant(&mut env)).collect();

        // The spine, spelled out rather than taken from the function under test:
        // a test that builds its expectation with that function cannot see it
        // nest the applications the other way.
        let spine_over = |head: &Term, vs: &[FreeVar]| {
            let mut s = head.clone();
            for v in vs {
                s = Term::apply(app, vec![s, Term::var(*v)]);
            }
            s
        };
        let spine = spine_over(&ct, &vars);
        let hyp = |vs: &[FreeVar], ds: &[Term]| {
            let prems: Vec<Formula> =
                vs.iter().zip(ds).map(|(v, d)| Formula::mem(Term::var(*v), d.clone())).collect();
            derived::conj_of(&prems).expect("three premises")
        };
        let h = hyp(&vars, &doms);
        let rule = Formula::imp(h.clone(), Formula::mem(spine.clone(), ty_spine.clone()));
        let bridge = Formula::imp(h, Formula::eq(spine.clone(), bottom.clone()));

        let agrees = |vs: &[FreeVar], ds: &[Term], ty: &Term, bot: &Term, r: &Formula, b: &Formula| {
            let mut mk = |f: FnSym, xs: Vec<Term>| Term::apply(f, xs);
            ctor_nest_agrees(&mut mk, app, &ct, vs, ds, ty, bot, r, b)
        };

        // The nest it was built over, and the spine it is about — which is the
        // term the caller goes on to use, so the identity is asserted, not just
        // the acceptance.
        assert_eq!(
            agrees(&vars, &doms, &ty_spine, &bottom, &rule, &bridge),
            Some(spine.clone()),
            "the terms it was built over must be accepted, and the spine handed back"
        );

        // Permuted **domains** — the same fields interpreting to the same three
        // terms in a different order. Below level 0, where only the pointwise
        // comparison of the antecedent's atoms can see it.
        let deep = vec![doms[0].clone(), doms[2].clone(), doms[1].clone()];
        assert!(
            agrees(&vars, &deep, &ty_spine, &bottom, &rule, &bridge).is_none(),
            "a nest over different domains must be declined below level 0 too"
        );
        let top = vec![doms[1].clone(), doms[0].clone(), doms[2].clone()];
        assert!(
            agrees(&vars, &top, &ty_spine, &bottom, &rule, &bridge).is_none(),
            "a nest over different domains must be declined at level 0"
        );

        // Permuted **variables** — the adopting walk opened the binders
        // elsewhere, so both the spine and the premises are about other terms.
        let swapped = vec![vars[0], vars[2], vars[1]];
        assert!(
            agrees(&swapped, &doms, &ty_spine, &bottom, &rule, &bridge).is_none(),
            "a nest over different variables must be declined"
        );

        // A **right-nested** spine. Lean's spine is `((c x₀) x₁) x₂` and the
        // rule is positional against it; a rule stated at `c (x₀ (x₁ x₂))`
        // mentions the same symbols and the same variables and is a statement
        // about a different term.
        let mut rassoc = Term::var(vars[2]);
        for v in vars[..2].iter().rev() {
            rassoc = Term::apply(app, vec![Term::var(*v), rassoc]);
        }
        let rassoc = Term::apply(app, vec![ct.clone(), rassoc]);
        assert_ne!(rassoc, spine, "the two associations must be different terms");
        let rule_rassoc =
            Formula::imp(hyp(&vars, &doms), Formula::mem(rassoc, ty_spine.clone()));
        assert!(
            agrees(&vars, &doms, &ty_spine, &bottom, &rule_rassoc, &bridge).is_none(),
            "a rule about the other association must be declined"
        );

        // The **type former's spine**: a rule concluding membership in another
        // declaration's `⟦T p⃗⟧` types this constructor into the wrong set.
        let elsewhere = constant(&mut env);
        assert!(
            agrees(&vars, &doms, &elsewhere, &bottom, &rule, &bridge).is_none(),
            "a rule about another type former must be declined"
        );

        // The **carrier's constructor term**, which the ι rule rewrites along.
        assert!(
            agrees(&vars, &doms, &ty_spine, &elsewhere, &rule, &bridge).is_none(),
            "a bridge about another constructor term must be declined"
        );

        // Both theorems true, and about somebody else's abbreviation of `⟦cᵢ⟧`.
        // The mislabelling the whole store exists to avoid.
        let others = spine_over(&other_ct, &vars);
        assert_ne!(others, spine, "two abbreviations must give two spines");
        let h = hyp(&vars, &doms);
        assert!(
            agrees(
                &vars,
                &doms,
                &ty_spine,
                &bottom,
                &Formula::imp(h.clone(), Formula::mem(others.clone(), ty_spine.clone())),
                &Formula::imp(h, Formula::eq(others, bottom.clone())),
            )
            .is_none(),
            "a nest about another head must be declined"
        );

    }

    /// **A nest whose arities do not match the spine is not replayable.**
    ///
    /// Level `k` carries every argument above it, so its graph symbol has arity
    /// `k + 1`. A stored nest disagreeing about that is not a nest for this
    /// walk, and `Term::apply` panics on an arity mismatch rather than
    /// returning — so the check has to happen before any term is built.
    ///
    /// **Mutation-verified**: dropping the arity loop in [`nest_replay`] turns
    /// the first assertion from a `None` into a panic, and dropping the depth
    /// check turns the second into one.
    #[test]
    fn a_nest_with_the_wrong_arities_is_declined_rather_than_built() {
        let mut env = Env::new();
        let doms: Vec<Term> = (0..3).map(|_| constant(&mut env)).collect();
        // Level 1 should have arity 2 and has arity 3.
        let wrong = [env.declare(1), env.declare(3), env.declare(3)];
        assert!(nest_replay(&wrong, &doms).is_none(), "a mis-arited nest must not replay");
        // …and a nest of the wrong depth likewise.
        let short = [env.declare(1), env.declare(2)];
        assert!(nest_replay(&short, &doms).is_none(), "a nest of the wrong depth must not replay");
    }

    /// **A literal's key must separate the two kinds.**
    ///
    /// [`Shared::lit_syms`] shares one symbol per literal *value*, so that `8`
    /// in `UInt8`'s `Fin (2^8)` is the same term in every declaration. The key
    /// carries the kind as well as the digits: the nat `10` and the string
    /// `"10"` are different literals and must not collide into one denotation,
    /// which would make `⊢ ⟦(10 : Nat)⟧ = ⟦"10"⟧` derivable by `refl`.
    ///
    /// **Mutation-verified**: keying on the rendered digits alone (making both
    /// arms `Lit::Str`) fails the second assertion.
    #[test]
    fn a_literal_key_separates_nats_from_strings() {
        use std::collections::HashMap;
        let ten = Lit::Nat(num_bigint::BigUint::from(10u32));
        let ten_again = Lit::Nat(num_bigint::BigUint::from(10u32));
        let ten_str = Lit::Str("10".to_string());
        let eleven = Lit::Nat(num_bigint::BigUint::from(11u32));

        let mut env = Env::new();
        let mut syms: HashMap<Lit, FnSym> = HashMap::new();
        for l in [ten.clone(), ten_again.clone(), ten_str.clone(), eleven.clone()] {
            let s = env.declare(0);
            syms.entry(l).or_insert(s);
        }
        assert_eq!(syms[&ten], syms[&ten_again], "one value must get one symbol");
        assert_ne!(syms[&ten], syms[&ten_str], "a nat and a string must not share a denotation");
        assert_ne!(syms[&ten], syms[&eleven], "distinct values must keep distinct denotations");
    }

    /// **A hypothetical certificate must not be cacheable.**
    ///
    /// The definitional-equality cache is keyed on the `Expr` pair and on
    /// nothing else. That was sound while a `kernel::Thm` was valid absolutely;
    /// with `Thm` a sequent `Γ ⊢ φ` it is not, because retrieving `Γ ⊢ a = b`
    /// under a key that does not mention `Γ` re-asserts `Γ` silently — and the
    /// kernel cannot object, since the theorem handed back is perfectly good.
    ///
    /// `crate::certify::is_unconditional` is the predicate that decides what may
    /// be stored, and it used to read `c.is_proved()`. This pins the fixed
    /// reading. **Mutation-verified**: restoring `c.is_proved()` makes the
    /// second assertion below fail, and nothing else in the test suite notices —
    /// which is exactly why the test is here rather than being left to the
    /// corpus, where no rule yet builds a hypothetical `Thm` at all.
    #[test]
    fn a_certificate_under_hypotheses_is_not_cacheable() {
        let mut env = Env::new();
        let (a, b) = (constant(&mut env), constant(&mut env));
        let h = Formula::mem(a.clone(), b.clone());
        let eq = Formula::eq(a.clone(), b.clone());

        // The honest case: a derivation resting on nothing. `eq_refl` is the
        // only hypothesis-free theorem needed to make the point.
        let outright = TgCert::Proved(Thm::eq_refl(a.clone()));
        assert!(outright.hyps().is_empty());
        assert!(crate::certify::is_unconditional(&outright), "an absolute derivation must still be cacheable");

        // The dangerous case: the *same variant*, a theorem that is perfectly
        // valid, and valid only under `h`. `is_proved()` cannot tell the two
        // apart; `is_unconditional` must.
        // `crate::scope::test_support` rather than `Thm::assume` directly: I1
        // says the introduction rule is named in exactly one file, and a test
        // that needs a hypothetical theorem is not an exception to that.
        use crate::scope::test_support::assume;
        let under_h = Thm::mp(&assume(Formula::imp(h.clone(), eq.clone())), &assume(h.clone()));
        let under_h = under_h.expect("modus ponens on two assumptions");
        assert_eq!(under_h.concl(), &eq, "the test theorem must conclude the equation");
        assert!(!under_h.hyps().is_empty(), "the test theorem must stand under hypotheses");
        let hypothetical = TgCert::Proved(under_h);
        assert!(hypothetical.is_proved(), "the variant is still `Proved` — that is the trap");
        assert!(
            !crate::certify::is_unconditional(&hypothetical),
            "a theorem valid only under Γ was accepted for a cache keyed without Γ"
        );
        assert!(
            !crate::certify::hypothesis_free(&hypothetical),
            "the reduct memo's guard must reject it too"
        );
    }

    /// **A guard is discharged on literal formula equality, and on nothing
    /// else.**
    ///
    /// [`TgBackend::guard_and_generalise_at`] is where a binder gives back the
    /// assumption it introduced. The whole honesty of the conditional path rests
    /// on it recognising *its own* guard and no other formula: an assumption that
    /// merely happens to be equivalent to the guard — the same membership stated
    /// at a defined name for the domain, say — must **not** be treated as
    /// discharged, because the binder does not in fact prove it. It is hoisted to
    /// `∀w. (w ∈ A → φ(w))`, stays in the returned list, and is therefore still
    /// owed and counted by the escape ledger.
    ///
    /// That was an implementation detail — one `==` in a loop — and the failure
    /// analysis of the whole conditional machinery rests on it, so it is pinned
    /// here. Mutation-verified: relaxing the test to compare only the *subject*
    /// of the membership makes the second half of this test fail.
    #[test]
    fn a_binder_discharges_only_its_own_guard_verbatim() {
        let declars = crate::env::DeclarMap::default();
        let notation = crate::env::NotationMap::default();
        let decls = crate::env::Env::new(&declars, &notation, crate::env::EnvLimit::Empty);
        let mut be = TgBackend::new(&decls);

        let (dom, other, w) = {
            let mut env = be.env_mut();
            (constant(&mut env), constant(&mut env), env.fresh_var())
        };
        let guard = Formula::mem(Term::var(w), dom.clone());
        let concl = Formula::eq(Term::var(w), Term::var(w));

        // ── The guard itself: discharged, and nothing is left over. ──────────
        let hyps = vec![guard.clone()];
        let thm = derived::a1i(&Thm::eq_refl(Term::var(w)), conj_of(&hyps).unwrap());
        let (premise, rest) =
            be.guard_and_generalise_at(&thm, &hyps, &concl, w, &dom).expect("the guard is dischargeable");
        assert!(rest.is_empty(), "the binder's own guard should have been discharged, not left owed");
        assert_eq!(
            premise.concl(),
            &Formula::forall(w, Formula::imp(guard.clone(), concl.clone())),
            "the premise must be the guarded universal closure"
        );

        // ── A *different* membership about the same variable: not discharged. ─
        //
        // `w ∈ other` is the same shape and about the same subject. It is not
        // the guard, so it must survive — hoisted, since it mentions `w`.
        let stale = Formula::mem(Term::var(w), other.clone());
        let hyps = vec![guard.clone(), stale.clone()];
        let thm = derived::a1i(&Thm::eq_refl(Term::var(w)), conj_of(&hyps).unwrap());
        let (_, rest) = be
            .guard_and_generalise_at(&thm, &hyps, &concl, w, &dom)
            .expect("the guard is still dischargeable");
        assert_eq!(
            rest,
            vec![Formula::forall(w, Formula::imp(guard, stale))],
            "an assumption that is not literally the guard must be hoisted and stay owed"
        );
    }

    /// A **conditional** certificate carries its assumptions inside the formula,
    /// so it is hypothesis-free at the kernel level and the reduct memo may hold
    /// it — while the equality cache still may not, for the separate accounting
    /// reason `is_unconditional` documents.
    ///
    /// The two predicates are deliberately different, and this is what says so.
    #[test]
    fn a_conditional_certificate_is_hypothesis_free_but_not_unconditional() {
        let mut env = Env::new();
        let (a, b) = (constant(&mut env), constant(&mut env));
        let h = Formula::mem(a.clone(), b.clone());
        // `⊢ h → (a = a)`: `implies_intr` weakens a hypothesis-free theorem, so
        // the result is a closed implication — which is exactly the shape a
        // `Conditional` certificate has.
        let thm = derived::a1i(&Thm::eq_refl(a.clone()), h.clone());
        assert!(thm.hyps().is_empty(), "a discharged assumption leaves no Γ behind");
        let c = TgCert::Conditional { thm, hyps: vec![h] };
        assert!(crate::certify::hypothesis_free(&c), "its assumptions are antecedents, not a Γ");
        assert!(!crate::certify::is_unconditional(&c), "but it is still not an outright derivation");
    }

    /// [`lam_ext_n`] pinned to its *exact* conclusion, at a prefix on one side
    /// only — the asymmetric case, which is what `lam_cong` normally meets and
    /// which `derived::ext::lam_ext` cannot express.
    ///
    /// The shape has to be pinned rather than merely checked for provability:
    /// `lam_cong` matches its result against the claim syntactically, so a
    /// lemma that is only *equivalent* to the intended one is useless.
    #[test]
    fn lam_ext_n_has_the_stated_shape() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2); // t(p, x)
        let t2 = env.declare(1); // t'(x)
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");

        let thm = lam_ext_n(&mut env, &ap, t, lam, &lam_ax, t2, lam2, &lam2_ax).expect("lam_ext_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_a2) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_a2.clone()]).expect("instantiate");

        let x = env.fresh_var();
        let tx = Term::var(x);
        let pointwise = Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), big_a.clone()),
                Formula::eq(Term::apply(t, vec![p.clone(), tx.clone()]), Term::apply(t2, vec![tx])),
            ),
        );
        let expected = Formula::imp(
            Formula::eq(big_a.clone(), big_a2.clone()),
            Formula::imp(
                pointwise,
                Formula::eq(Term::apply(lam, vec![p, big_a]), Term::apply(lam2, vec![big_a2])),
            ),
        );
        assert_eq!(*inst.concl(), expected, "lam_ext_n has the wrong shape");
    }

    /// A graph symbol whose arity does not match its body symbol's is refused,
    /// rather than yielding a theorem about a malformed term.
    #[test]
    fn lam_ext_n_rejects_mismatched_arities() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2);
        let t2 = env.declare(1);
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");

        let wrong = env.declare(3);
        assert!(lam_ext_n(&mut env, &ap, t, wrong, &lam_ax, t2, lam2, &lam2_ax).is_none());
        assert!(lam_ext_n(&mut env, &ap, t, lam, &lam_ax, t2, wrong, &lam2_ax).is_none());
        // A nullary body symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(lam_ext_n(&mut env, &ap, nullary, lam, &lam_ax, t2, lam2, &lam2_ax).is_none());
    }

    /// A `parts` map for the terms built here, mirroring [`TgBackend::mk`].
    fn mk_in(parts: &mut Parts, f: FnSym, args: Vec<Term>) -> Term {
        let t = Term::apply(f, args.clone());
        parts.insert(t.clone(), (f, args));
        t
    }

    /// [`retarget`] does what `pi_cong` needs: a certificate stated at a local
    /// becomes one stated at the bound-variable encoding, with *exactly* the
    /// wanted conclusion.
    #[test]
    fn retarget_reaims_a_certificate_at_the_de_bruijn_form() {
        let mut env = Env::new();
        let mut parts = Parts::new();
        let (f, bvar) = (env.declare(1), env.declare(1));
        // `bvar(idx₀)`, the interpretation of a loose de Bruijn index, and a
        // second constant to stand for a different one.
        let b0 = mk_in(&mut parts, bvar, vec![constant(&mut env)]);
        let b1 = mk_in(&mut parts, bvar, vec![constant(&mut env)]);

        // A genuinely non-reflexive certificate stated at a local: `⊢ d(v) = f(v)`.
        let v = env.fresh_var();
        let fv = mk_in(&mut parts, f, vec![Term::var(v)]);
        let (d, d_def) = derived::define_abbrev(&mut env, &[v], &fv).expect("define");
        let dv = mk_in(&mut parts, d, vec![Term::var(v)]);
        let cert = derived::inst_all(&d_def, &[Term::var(v)]).expect("instantiate");
        assert_eq!(*cert.concl(), Formula::eq(dv, fv), "the certificate is stated at the local");

        // Re-aimed at the raw form the claim uses, and *exactly* that.
        let (db, fb) = (mk_in(&mut parts, d, vec![b0.clone()]), mk_in(&mut parts, f, vec![b0.clone()]));
        let out = retarget(&parts, &cert, &db, &fb).expect("retarget should re-aim");
        assert_eq!(*out.concl(), Formula::eq(db.clone(), fb));

        // One local cannot become two different terms: the certificate says
        // nothing about `d(bvar₀) = f(bvar₁)` and must not be bent into it.
        let fb1 = mk_in(&mut parts, f, vec![b1.clone()]);
        assert!(retarget(&parts, &cert, &db, &fb1).is_none(), "inconsistent binding must be refused");

        // A head symbol the certificate does not have is refused outright.
        let db1 = mk_in(&mut parts, d, vec![b1]);
        assert!(retarget(&parts, &cert, &db1, &db).is_none(), "mismatched head symbol must be refused");

        // A term the backend never built cannot be taken apart.
        let stranger = Term::apply(f, vec![b0]);
        let mut bare = Parts::new();
        bare.insert(stranger.clone(), (f, vec![]));
        assert!(retarget(&bare, &cert, &stranger, &stranger).is_none(), "unknown structure must be refused");
    }

    /// The prelude's stack, rebuilt: `app`, the Cartesian product and the
    /// function space over *one* `Sets`, which is what the `Π` lemmas need.
    fn pi_stack(env: &mut Env) -> (Apply, derived::funspace::Product, derived::funspace::Funspace) {
        let ap = Apply::new(env).expect("Apply::new");
        let (pow, pow_ax) = derived::power(env);
        let prod = derived::funspace::product(env, &ap.sets).expect("product");
        let fs = derived::funspace::Funspace::new(env, &ap.sets, pow, &pow_ax, &prod, &ap.empty_ax)
            .expect("Funspace::new");
        (ap, prod, fs)
    }

    /// A conditional singleton `chi(p⃗,A) = [∀x ∈ A. • ∈ b(p⃗,x)]` over a body
    /// symbol of arity `k+1`, as [`TgBackend::build_cond`] builds it.
    fn cond_over(env: &mut Env, sums: &derived::sums::Sums, b: FnSym) -> (FnSym, Thm, Formula, Vec<FreeVar>) {
        let k = b.arity() as usize - 1;
        let mut params: Vec<FreeVar> = (0..k).map(|_| env.fresh_var()).collect();
        let x = env.fresh_var();
        let a = env.fresh_var();
        let mut bargs: Vec<Term> = params.iter().map(|v| Term::var(*v)).collect();
        bargs.push(Term::var(x));
        let phi = Formula::forall(
            x,
            Formula::imp(
                Formula::mem(Term::var(x), Term::var(a)),
                Formula::mem(sums.point(), Term::apply(b, bargs)),
            ),
        );
        params.push(a);
        let (chi, ax) =
            derived::prop::conditional_singleton(env, sums, &params, &phi).expect("conditional_singleton");
        (chi, ax, phi, params)
    }

    /// [`cond_ext_n`] pinned to its *exact* conclusion, at a genuine parameter
    /// prefix on each side — §6.2's `∀` clause needing what [`dprod_ext_n`]
    /// gives its `Π` clause.
    ///
    /// The shape has to be pinned rather than merely checked for provability:
    /// `derive_prop_ext` instantiates the result and discharges two premises it
    /// built itself, so a lemma that is only *equivalent* to the intended one is
    /// useless.
    #[test]
    fn cond_ext_n_has_the_stated_shape() {
        let mut env = Env::new();
        let sums = derived::sums::Sums::new(&mut env).expect("Sums::new");
        let (b, b2) = (env.declare(2), env.declare(2)); // b(p,x), b'(q,x)
        let (chi, chi_ax, _, _) = cond_over(&mut env, &sums, b);
        let (chi2, chi2_ax, _, _) = cond_over(&mut env, &sums, b2);

        let thm = cond_ext_n(&mut env, &sums, (b, chi, &chi_ax), (b2, chi2, &chi2_ax)).expect("cond_ext_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, q, big_a, big_a2) =
            (constant(&mut env), constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), q.clone(), big_a.clone(), big_a2.clone()])
            .expect("instantiate");
        let x = env.fresh_var();
        let (bx, b2x) = (
            Term::apply(b, vec![p.clone(), Term::var(x)]),
            Term::apply(b2, vec![q.clone(), Term::var(x)]),
        );
        let expected = Formula::imp(
            Formula::eq(big_a.clone(), big_a2.clone()),
            Formula::imp(
                Formula::forall(
                    x,
                    Formula::imp(Formula::mem(Term::var(x), big_a.clone()), Formula::eq(bx, b2x)),
                ),
                Formula::eq(
                    Term::apply(chi, vec![p, big_a]),
                    Term::apply(chi2, vec![q, big_a2]),
                ),
            ),
        );
        assert_eq!(*inst.concl(), expected, "cond_ext_n has the wrong shape");

        // Non-vacuity: the two sides of the equation are built by different
        // symbols, so the lemma is not equating a term with itself.
        let (_, rest) = inst.concl().as_imp().expect("an implication");
        let (_, concl) = rest.as_imp().expect("a second implication");
        let (l, r) = concl.as_eq().expect("an equation");
        assert_ne!(l, r, "the lemma would equate a term with itself");
    }

    /// The characteristic theorems are *checked*, not assumed: a conditional
    /// singleton the axiom was not built for is refused, rather than yielding a
    /// theorem about the wrong sets.
    ///
    /// This is the guard that matters here. `cond_ext_n` reads `φ` off nothing —
    /// it *rebuilds* the formula it expects from `b` and the domain variable and
    /// compares — so handing it another singleton's axiom must fail rather than
    /// silently prove `chi = chi'` for symbols that are not conditional on
    /// anything related.
    #[test]
    fn cond_ext_n_rejects_a_mismatch() {
        let mut env = Env::new();
        let sums = derived::sums::Sums::new(&mut env).expect("Sums::new");
        let (b, b2) = (env.declare(2), env.declare(2));
        let (chi, chi_ax, _, _) = cond_over(&mut env, &sums, b);
        let (chi2, chi2_ax, _, _) = cond_over(&mut env, &sums, b2);

        assert!(
            cond_ext_n(&mut env, &sums, (b, chi, &chi_ax), (b2, chi2, &chi2_ax)).is_some(),
            "the matched pair goes through"
        );
        // The other singleton's axiom, its symbol, and the other body: refused.
        assert!(
            cond_ext_n(&mut env, &sums, (b, chi, &chi2_ax), (b2, chi2, &chi2_ax)).is_none(),
            "an axiom for another conditional singleton"
        );
        assert!(
            cond_ext_n(&mut env, &sums, (b, chi2, &chi_ax), (b2, chi2, &chi2_ax)).is_none(),
            "a foreign singleton symbol"
        );
        assert!(
            cond_ext_n(&mut env, &sums, (b2, chi, &chi_ax), (b2, chi2, &chi2_ax)).is_none(),
            "a foreign body symbol"
        );
        // A nullary body symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(
            cond_ext_n(&mut env, &sums, (nullary, chi, &chi_ax), (b2, chi2, &chi2_ax)).is_none(),
            "a body with no binder slot"
        );
    }

    /// `id(a)`, together with `⊢ id(a) ∈ fs(a,a)` — the one concrete function
    /// this development builds, and so the only genuine inhabitant of a function
    /// space a test of the application-typing rules can use.
    fn identity_in_funspace(
        env: &mut Env,
        ap: &Apply,
        prod: &derived::funspace::Product,
        fs: &derived::funspace::Funspace,
        a: &Term,
    ) -> (Term, Thm) {
        use derived::funspace::{identity_graph, identity_is_function};
        let (id, id_ax) = identity_graph(env, &ap.sets).expect("identity_graph");
        let id_fun =
            identity_is_function(env, &ap.sets, prod, id, &id_ax, &ap.pair_inj).expect("identity_is_function");
        let is_fun = derived::inst_all(&id_fun, std::slice::from_ref(a)).expect("isfun at a");
        let id_a = Term::apply(id, vec![a.clone()]);
        let members =
            derived::inst_all(&fs.fs_ax, &[a.clone(), a.clone(), id_a.clone()]).expect("fs_ax at a, a, id(a)");
        let thm = Thm::mp(&derived::iff_mpr(&members).expect("iff_mpr"), &is_fun).expect("mp");
        assert_eq!(*thm.concl(), Formula::mem(id_a.clone(), fs.of(a.clone(), a.clone())));
        (id_a, thm)
    }

    /// [`app_in_codomain`] against a genuine inhabitant: the identity function
    /// on `{c}`, applied to `c`, lands back in `{c}`.
    ///
    /// The corpus cannot reach this clause — every Lean function value is a
    /// lambda or an opaque constant, and neither has a typing lemma yet — so
    /// this is what says the rule composes at all.
    #[test]
    fn app_in_codomain_types_the_identity() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem =
            derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("funspace_app_mem");

        let c = constant(&mut env);
        let a0 = derived::singleton(ap.sets.up, c.clone());
        let (mem_c, _) = derived::upair_members(&ap.sets.up_ax, &c, &c).expect("upair_members");
        let (id_a, id_in_fs) = identity_in_funspace(&mut env, &ap, &prod, &fs, &a0);

        let out =
            app_in_codomain(&app_mem, &a0, &a0, &id_a, &c, &id_in_fs, &mem_c, None).expect("app_in_codomain");
        assert_eq!(
            *out.concl(),
            Formula::mem(ap.apply(id_a, c), a0),
            "app_in_codomain did not type the application"
        );
    }

    /// [`app_in_fibre`] against a genuine inhabitant.
    ///
    /// A dependent product needs a *section* to be inhabited, and the only
    /// function available is the identity — so the fibre is taken constant,
    /// `b(p,x) := p`, which by [`dprod_const_fibre_n`] makes the product a
    /// function space and the identity a member of it. The fibre symbol is
    /// still a fibre: the route goes through `dprod_def`'s section conjunct and
    /// unfolds `b(A,c)`, which is the step that has to line up with `⟦B[a]⟧`.
    #[test]
    fn app_in_fibre_types_a_section() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem =
            derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("funspace_app_mem");
        let retarget =
            derived::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair).expect("funspace_retarget");

        // `b(p,x) := p`, a one-parameter fibre that ignores the binder.
        let (p, x) = (env.fresh_var(), env.fresh_var());
        let (b, b_def) = derived::define_abbrev(&mut env, &[p, x], &Term::var(p)).expect("define_abbrev");
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let bridge =
            dprod_const_fibre_n(&mut env, &ap, &fs, b, img, &img_ax, dprod, &dprod_def, &app_mem, &retarget)
                .expect("dprod_const_fibre_n");

        let c = constant(&mut env);
        let a0 = derived::singleton(ap.sets.up, c.clone());
        let (mem_c, _) = derived::upair_members(&ap.sets.up_ax, &c, &c).expect("upair_members");

        // `∀x. (x ∈ A → b(A,x) = A)`, the bridge's premise, straight from `b`'s
        // definition; then `⊢ dprod(A,A) = fs(A,A)`.
        let w = env.fresh_var();
        let at_w = derived::inst_all(&b_def, &[a0.clone(), Term::var(w)]).expect("b_def at A, w");
        let cond = Thm::gen_checked(w, &derived::a1i(&at_w, Formula::mem(Term::var(w), a0.clone())))
            .expect("gen: w is free in no hypothesis of a hypothesis-free theorem");
        let inst = derived::inst_all(&bridge, &[a0.clone(), a0.clone(), a0.clone()]).expect("bridge at A");
        let eq = Thm::mp(&inst, &cond).expect("the constant-fibre premise");

        // The identity, moved across that equation into the dependent product.
        let (id_a, id_in_fs) = identity_in_funspace(&mut env, &ap, &prod, &fs, &a0);
        let back = derived::eq_symm(&mut env, &eq).expect("eq_symm");
        let dp = Term::apply(dprod, vec![a0.clone(), a0.clone()]);
        let v = env.fresh_var();
        let leib = Thm::eq_leibniz(
            fs.of(a0.clone(), a0.clone()),
            dp.clone(),
            v,
            Formula::mem(id_a.clone(), Term::var(v)),
        );
        let id_in_dp = Thm::mp(&Thm::mp(&leib, &back).expect("mp"), &id_in_fs).expect("mp");
        assert_eq!(*id_in_dp.concl(), Formula::mem(id_a.clone(), dp));

        let out = app_in_fibre(
            &mut env,
            ap.app,
            &dprod_def,
            &b_def,
            std::slice::from_ref(&a0),
            &a0,
            &id_a,
            &c,
            &id_in_dp,
            &mem_c,
            None,
        )
        .expect("app_in_fibre");
        assert_eq!(
            *out.concl(),
            Formula::mem(ap.apply(id_a, c), a0),
            "app_in_fibre did not type the application at the unfolded fibre"
        );
    }

    /// The dependent product over a fibre symbol with a `k`-parameter prefix.
    fn dprod_over(
        env: &mut Env,
        ap: &Apply,
        fs: &derived::funspace::Funspace,
        b: FnSym,
    ) -> (FnSym, Thm, FnSym, Thm) {
        let (img, img_ax) = image_symbol_n(env, b).expect("image_symbol_n");
        let (dprod, dprod_def) = dprod_symbol_n(env, ap, fs, img, b).expect("dprod_symbol_n");
        (img, img_ax, dprod, dprod_def)
    }

    /// [`dprod_const_fibre_n`] pinned to its *exact* conclusion, at a genuine
    /// parameter prefix — the case the unary `derived::ext::dprod_const_fibre`
    /// cannot express, and the only one the checker ever meets.
    ///
    /// The shape has to be pinned rather than merely checked for provability:
    /// `pi_cong` matches its result against the claim syntactically, so a lemma
    /// that is only *equivalent* to the intended one is useless.
    #[test]
    fn dprod_const_fibre_n_has_the_stated_shape() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let b = env.declare(2); // b(p, x)
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem = derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("app_mem");
        let retarget = derived::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair).expect("retarget");

        let thm = dprod_const_fibre_n(&mut env, &ap, &fs, b, img, &img_ax, dprod, &dprod_def, &app_mem, &retarget)
            .expect("dprod_const_fibre_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_b) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_b.clone()]).expect("instantiate");
        let x = env.fresh_var();
        let expected = Formula::imp(
            Formula::forall(
                x,
                Formula::imp(
                    Formula::mem(Term::var(x), big_a.clone()),
                    Formula::eq(Term::apply(b, vec![p.clone(), Term::var(x)]), big_b.clone()),
                ),
            ),
            Formula::eq(Term::apply(dprod, vec![p, big_a.clone()]), fs.of(big_a, big_b)),
        );
        assert_eq!(*inst.concl(), expected, "dprod_const_fibre_n has the wrong shape");

        // Non-vacuity twice over: the two sides of the equation are built by
        // different symbols, and the hypothesis is not the conclusion.
        let (ante, concl) = inst.concl().as_imp().expect("an implication");
        let (l, r) = concl.as_eq().expect("an equation");
        assert_ne!(l, r, "the lemma would equate a term with itself");
        assert_ne!(ante, concl);
    }

    /// The stack is *checked*, not assumed: a fibre, image or product the
    /// dependent product was not built over is refused, rather than yielding a
    /// theorem about the wrong sets.
    #[test]
    fn dprod_const_fibre_n_rejects_a_mismatch() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let (b, b2) = (env.declare(2), env.declare(2));
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let (img2, img2_ax, dprod2, dprod2_def) = dprod_over(&mut env, &ap, &fs, b2);
        let app_pair = derived::ext::app_of_pair(&mut env, &ap).expect("app_of_pair");
        let app_mem = derived::ext::funspace_app_mem(&mut env, &ap, &prod, &fs, &app_pair).expect("app_mem");
        let rt = derived::ext::funspace_retarget(&mut env, &ap, &prod, &fs, &app_pair).expect("retarget");

        let ok = |e: &mut Env, b, i, ia: &Thm, d, dd: &Thm| dprod_const_fibre_n(e, &ap, &fs, b, i, ia, d, dd, &app_mem, &rt);
        assert!(ok(&mut env, b, img, &img_ax, dprod, &dprod_def).is_some(), "the matched stack goes through");
        // The other fibre's product, image or defining axiom: each refused.
        assert!(ok(&mut env, b, img, &img_ax, dprod2, &dprod2_def).is_none(), "a foreign dependent product");
        assert!(ok(&mut env, b, img2, &img2_ax, dprod, &dprod_def).is_none(), "a foreign fibre image");
        assert!(ok(&mut env, b2, img, &img_ax, dprod, &dprod_def).is_none(), "a foreign fibre");
        assert!(ok(&mut env, b, img2, &img_ax, dprod, &dprod_def).is_none(), "an image axiom for another image");
        // A nullary fibre symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(ok(&mut env, nullary, img, &img_ax, dprod, &dprod_def).is_none(), "a fibre with no binder slot");
    }

    /// A lambda graph over a `k`-parameter body symbol.
    fn lam_over(env: &mut Env, ap: &Apply, t: FnSym) -> (FnSym, Thm) {
        lambda_n(env, ap, t).expect("lambda_n")
    }

    /// [`lam_in_funspace_n`] pinned to its *exact* conclusion, at a genuine
    /// parameter prefix — the case `derived::ext::lam_in_funspace` cannot
    /// express, and the only one the checker ever meets.
    ///
    /// The shape has to be pinned rather than merely checked for provability:
    /// `has_type_lam` discharges the premise by `mp` against a premise it built
    /// itself, so a lemma that is only *equivalent* to the intended one is
    /// useless.
    #[test]
    fn lam_in_funspace_n_has_the_stated_shape() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let t = env.declare(2); // t(p, x)
        let (lam, lam_ax) = lam_over(&mut env, &ap, t);

        let thm = lam_in_funspace_n(&mut env, &ap, &prod, &fs, t, lam, &lam_ax).expect("lam_in_funspace_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_c) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_c.clone()]).expect("instantiate");
        let x = env.fresh_var();
        let expected = Formula::imp(
            Formula::forall(
                x,
                Formula::imp(
                    Formula::mem(Term::var(x), big_a.clone()),
                    Formula::mem(Term::apply(t, vec![p.clone(), Term::var(x)]), big_c.clone()),
                ),
            ),
            Formula::mem(Term::apply(lam, vec![p, big_a.clone()]), fs.of(big_a, big_c)),
        );
        assert_eq!(*inst.concl(), expected, "lam_in_funspace_n has the wrong shape");
        // Non-vacuity: the hypothesis is not the conclusion.
        let (ante, concl) = inst.concl().as_imp().expect("an implication");
        assert_ne!(ante, concl);
    }

    /// The graph axiom is *checked*, not assumed: a graph built over another
    /// body symbol is refused rather than described as this one's.
    #[test]
    fn lam_in_funspace_n_rejects_a_foreign_axiom() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let (t, t2) = (env.declare(2), env.declare(2));
        let (lam, lam_ax) = lam_over(&mut env, &ap, t);
        let (lam2, lam2_ax) = lam_over(&mut env, &ap, t2);

        assert!(lam_in_funspace_n(&mut env, &ap, &prod, &fs, t, lam, &lam_ax).is_some(), "the matched pair");
        assert!(lam_in_funspace_n(&mut env, &ap, &prod, &fs, t, lam, &lam2_ax).is_none(), "a foreign axiom");
        assert!(lam_in_funspace_n(&mut env, &ap, &prod, &fs, t, lam2, &lam2_ax).is_none(), "a foreign graph");
        // A nullary body symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(lam_in_funspace_n(&mut env, &ap, &prod, &fs, nullary, lam, &lam_ax).is_none(), "no binder slot");
    }

    /// [`lam_in_dprod_n`] pinned to its *exact* conclusion, with the lambda's
    /// prefix and the fibre's prefix of **different lengths** — the whole point
    /// of the n-ary port, since the two skeletons are unrelated.
    #[test]
    fn lam_in_dprod_n_has_the_stated_shape() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let t = env.declare(3); // t(p₁, p₂, x)
        let b = env.declare(2); // b(q, x)
        let (lam, lam_ax) = lam_over(&mut env, &ap, t);
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let beta = beta_conditional_n(&mut env, &ap, t, lam, &lam_ax).expect("beta_conditional_n");
        let lam_fs = lam_in_funspace_n(&mut env, &ap, &prod, &fs, t, lam, &lam_ax).expect("lam_in_funspace_n");

        let thm = lam_in_dprod_n(&mut env, &ap, &fs, (t, lam, &beta, &lam_fs), (b, img, &img_ax, dprod, &dprod_def))
            .expect("lam_in_dprod_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p1, p2, q, big_a) =
            (constant(&mut env), constant(&mut env), constant(&mut env), constant(&mut env));
        let inst =
            derived::inst_all(&thm, &[p1.clone(), p2.clone(), q.clone(), big_a.clone()]).expect("instantiate");
        let x = env.fresh_var();
        let expected = Formula::imp(
            Formula::forall(
                x,
                Formula::imp(
                    Formula::mem(Term::var(x), big_a.clone()),
                    Formula::mem(
                        Term::apply(t, vec![p1.clone(), p2.clone(), Term::var(x)]),
                        Term::apply(b, vec![q.clone(), Term::var(x)]),
                    ),
                ),
            ),
            Formula::mem(Term::apply(lam, vec![p1, p2, big_a.clone()]), Term::apply(dprod, vec![q, big_a])),
        );
        assert_eq!(*inst.concl(), expected, "lam_in_dprod_n has the wrong shape");
        let (ante, concl) = inst.concl().as_imp().expect("an implication");
        assert_ne!(ante, concl);
    }

    /// Every part of the stack is checked: a beta lemma, a function-space lemma,
    /// a fibre, an image or a dependent product belonging to something else is
    /// refused rather than silently described.
    #[test]
    fn lam_in_dprod_n_rejects_a_mismatch() {
        let mut env = Env::new();
        let (ap, prod, fs) = pi_stack(&mut env);
        let (t, t2) = (env.declare(2), env.declare(2));
        let (b, b2) = (env.declare(2), env.declare(2));
        let (lam, lam_ax) = lam_over(&mut env, &ap, t);
        let (lam2, lam2_ax) = lam_over(&mut env, &ap, t2);
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let (img2, img2_ax, dprod2, dprod2_def) = dprod_over(&mut env, &ap, &fs, b2);
        let beta = beta_conditional_n(&mut env, &ap, t, lam, &lam_ax).expect("beta");
        let beta2 = beta_conditional_n(&mut env, &ap, t2, lam2, &lam2_ax).expect("beta2");
        let lam_fs = lam_in_funspace_n(&mut env, &ap, &prod, &fs, t, lam, &lam_ax).expect("lam_fs");
        let lam_fs2 = lam_in_funspace_n(&mut env, &ap, &prod, &fs, t2, lam2, &lam2_ax).expect("lam_fs2");

        let go = |e: &mut Env, l: (FnSym, FnSym, &Thm, &Thm), f: (FnSym, FnSym, &Thm, FnSym, &Thm)| {
            lam_in_dprod_n(e, &ap, &fs, l, f)
        };
        let fib = (b, img, &img_ax, dprod, &dprod_def);
        assert!(go(&mut env, (t, lam, &beta, &lam_fs), fib).is_some(), "the matched stack goes through");
        assert!(go(&mut env, (t, lam, &beta2, &lam_fs), fib).is_none(), "a foreign beta lemma");
        assert!(go(&mut env, (t, lam, &beta, &lam_fs2), fib).is_none(), "a foreign function-space lemma");
        assert!(
            go(&mut env, (t, lam, &beta, &lam_fs), (b, img, &img_ax, dprod2, &dprod2_def)).is_none(),
            "a foreign dependent product"
        );
        assert!(
            go(&mut env, (t, lam, &beta, &lam_fs), (b, img2, &img2_ax, dprod, &dprod_def)).is_none(),
            "a foreign fibre image"
        );
        assert!(
            go(&mut env, (t, lam, &beta, &lam_fs), (b2, img, &img_ax, dprod, &dprod_def)).is_none(),
            "a foreign fibre"
        );
        // A nullary body or fibre symbol has no binder slot at all.
        let nullary = env.declare(0);
        assert!(go(&mut env, (nullary, lam, &beta, &lam_fs), fib).is_none(), "a body with no binder slot");
        assert!(
            go(&mut env, (t, lam, &beta, &lam_fs), (nullary, img, &img_ax, dprod, &dprod_def)).is_none(),
            "a fibre with no binder slot"
        );
    }

    /// [`dprod_ext_n`] pinned to its *exact* conclusion, at a prefix on one side
    /// only — the asymmetric case, which is what `pi_cong` normally meets and
    /// which `derived::ext::dprod_ext` cannot express.
    #[test]
    fn dprod_ext_n_has_the_stated_shape() {
        let mut env = Env::new();
        let (ap, _prod, fs) = pi_stack(&mut env);
        let (b, b2) = (env.declare(2), env.declare(1)); // b(p,x) and b'(x)
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let (img2, img2_ax, dprod2, dprod2_def) = dprod_over(&mut env, &ap, &fs, b2);

        let thm = dprod_ext_n(
            &mut env,
            &ap,
            &fs,
            (b, img, &img_ax, dprod, &dprod_def),
            (b2, img2, &img2_ax, dprod2, &dprod2_def),
        )
        .expect("dprod_ext_n");
        assert!(kernel::thm::debug_locally_closed(thm.concl()), "dangling bound variable");

        let (p, big_a, big_a2) = (constant(&mut env), constant(&mut env), constant(&mut env));
        let inst = derived::inst_all(&thm, &[p.clone(), big_a.clone(), big_a2.clone()]).expect("instantiate");
        let x = env.fresh_var();
        let tx = Term::var(x);
        let pointwise = Formula::forall(
            x,
            Formula::imp(
                Formula::mem(tx.clone(), big_a.clone()),
                Formula::eq(Term::apply(b, vec![p.clone(), tx.clone()]), Term::apply(b2, vec![tx])),
            ),
        );
        let expected = Formula::imp(
            Formula::eq(big_a.clone(), big_a2.clone()),
            Formula::imp(
                pointwise,
                Formula::eq(Term::apply(dprod, vec![p, big_a]), Term::apply(dprod2, vec![big_a2])),
            ),
        );
        assert_eq!(*inst.concl(), expected, "dprod_ext_n has the wrong shape");
    }

    /// A defining axiom that is not the one [`dprod_symbol_n`] produces for the
    /// symbol at hand is rejected: the derivation would otherwise be sound but
    /// about the wrong sets, and silently so.
    #[test]
    fn dprod_ext_n_rejects_a_foreign_axiom() {
        let mut env = Env::new();
        let (ap, _prod, fs) = pi_stack(&mut env);
        let (b, b2) = (env.declare(2), env.declare(1));
        let (img, img_ax, dprod, dprod_def) = dprod_over(&mut env, &ap, &fs, b);
        let (img2, img2_ax, dprod2, dprod2_def) = dprod_over(&mut env, &ap, &fs, b2);

        // The two products swapped over: right shape, wrong symbols.
        assert!(dprod_ext_n(
            &mut env,
            &ap,
            &fs,
            (b, img, &img_ax, dprod2, &dprod2_def),
            (b2, img2, &img2_ax, dprod, &dprod_def),
        )
        .is_none());
        // An arity that does not match the fibre's.
        let wrong = env.declare(3);
        assert!(dprod_ext_n(
            &mut env,
            &ap,
            &fs,
            (b, wrong, &img_ax, dprod, &dprod_def),
            (b2, img2, &img2_ax, dprod2, &dprod2_def),
        )
        .is_none());
    }

    /// A membership atom over fresh constants, to stand for an assumption.
    fn atom(env: &mut Env) -> Formula { Formula::mem(constant(env), constant(env)) }

    /// [`gen_under`] moves a `∀` **inside** an implication, and refuses to when
    /// that would be unsound.
    ///
    /// The pointwise `HYP` conjunct is `∀y⃗ ∀t⃗ ∀v⃗. (… → …)` while the escaping
    /// assumptions of the minor's typing must stay *outside* the quantifier —
    /// they are about the use site's context locals, not about the bound
    /// variables. `Thm::ax_dist`'s side condition is what separates the two
    /// cases, and getting it wrong is not a gap but a wrong theorem: it would
    /// generalise a variable the assumption still constrains.
    ///
    /// Both directions are asserted. Breaking the check — dropping
    /// `ax_dist`'s `occurs_free` test — makes the second half return `Some`.
    #[test]
    fn gen_under_quantifies_only_what_its_assumption_does_not_mention() {
        let mut env = Env::new();
        let a = constant(&mut env);
        let pair = env.declare(2);
        let (x, y, z) = (env.fresh_var(), env.fresh_var(), env.fresh_var());
        // `h` mentions `y` and neither `x` nor `z`.
        let h = Formula::mem(Term::var(y), a);
        // `⊢ h → (x = x)`, hypothesis-free: a real theorem weakened, which is
        // the shape every `u_*` combinator hands back.
        let phi = Formula::eq(Term::var(x), Term::var(x));
        let thm = derived::a1i(&Thm::eq_refl(Term::var(x)), h.clone());
        assert!(thm.hyps().is_empty(), "the assumption is an antecedent, not a Γ");
        assert_eq!(*thm.concl(), Formula::imp(h.clone(), phi.clone()));

        let out = gen_under(&thm, &h, &[x]).expect("`x` is not mentioned by the assumption");
        assert_eq!(
            *out.concl(),
            Formula::imp(h.clone(), Formula::forall(x, phi)),
            "the quantifier must land inside the implication, not outside it"
        );

        // …and `y` is not generalisable while `h` constrains it. `gen_all`
        // would happily produce `∀y. (h(y) → φ)`, which is a *different* and
        // weaker statement; what must not be produced is `h(y) → ∀y. φ`.
        assert!(
            gen_under(&thm, &h, &[y]).is_none(),
            "a variable the assumption mentions must not be quantified under it"
        );

        // Outermost first, matching `derived::gen_all` and `premise::minor_typed`.
        let t = Term::apply(pair, vec![Term::var(x), Term::var(z)]);
        let psi = Formula::eq(t.clone(), t.clone());
        let two = derived::a1i(&Thm::eq_refl(t), h.clone());
        let out = gen_under(&two, &h, &[x, z]).expect("neither is mentioned by the assumption");
        assert_eq!(
            *out.concl(),
            Formula::imp(h, Formula::forall(x, Formula::forall(z, psi))),
            "`xs[0]` is the outermost quantifier"
        );
    }

    /// The left-nested conjunction is the one the discharge relies on:
    /// `conj(R ++ [h])` has to be `conj(R) ∧ h`, or `uncurry` peels the wrong
    /// assumption off and the binder discharges something it was not given.
    #[test]
    fn conj_is_left_nested_and_projects() {
        let mut env = Env::new();
        let hs: Vec<Formula> = (0..4).map(|_| atom(&mut env)).collect();
        let whole = conj_of(&hs).expect("non-empty");
        assert_eq!(whole, Formula::and(conj_of(&hs[..3]).expect("non-empty"), hs[3].clone()));
        assert_eq!(conj_of(&hs[..1]), Some(hs[0].clone()), "a single assumption is itself");
        assert_eq!(conj_of(&[]), None);

        for (i, h) in hs.iter().enumerate() {
            let p = conj_proj(&hs, i).expect("projection");
            assert_eq!(*p.concl(), Formula::imp(whole.clone(), h.clone()), "projection {i}");
        }
        assert!(conj_proj(&hs, 4).is_none(), "out of range");
    }

    /// **[`under_prefix`] nests to the right, and the difference is visible at
    /// three atoms.**
    ///
    /// The type former's bridge `H_p → app-spine(⟦T⟧,p⃗) = ind(p⃗)` is a
    /// `derived`-shaped theorem: its antecedent is `derived::conj_of`'s
    /// **right**-nested bundle, and so is the constructor rule's premise list it
    /// has to be restated under. This file's own [`conj_of`] nests to the left.
    /// The two agree for one and two atoms and diverge from three, which is
    /// exactly the arity a one-parameter constructor with two fields has — so a
    /// left-nested restatement here would pass every small test and fail on
    /// `List.cons`.
    ///
    /// Asserted as an equality against the right-nested formula built
    /// independently, not against whatever the function returns.
    #[test]
    fn the_type_former_bridge_is_restated_right_nested() {
        let mut env = Env::new();
        // **Three** in the prefix, not two: with two, the left- and
        // right-nested bundles of the prefix are the same formula and a
        // left-nesting bug passes. Verified by breaking it.
        let prefix: Vec<Formula> = (0..3).map(|_| atom(&mut env)).collect();
        let extra: Vec<Formula> = (0..2).map(|_| atom(&mut env)).collect();
        let mut prems = prefix.clone();
        prems.extend(extra.iter().cloned());

        let c = constant(&mut env);
        let eq = Formula::eq(c.clone(), c.clone());
        // `⊢ conj_r(prefix) → c = c`, the bridge's shape.
        let bridge =
            derived::a1i(&Thm::eq_refl(c.clone()), derived::conj_of(&prefix).expect("three atoms"));

        let out = under_prefix(&bridge, &prefix, &prems).expect("prefix restatement");
        assert_eq!(
            *out.concl(),
            Formula::imp(derived::conj_of(&prems).expect("five atoms"), eq.clone()),
            "the restated antecedent is not the right-nested premise list"
        );
        // The left-nested bundle of the same four atoms is a *different*
        // formula, which is the whole hazard.
        assert_ne!(
            derived::conj_of(&prems),
            conj_of(&prems),
            "four atoms must distinguish the two nestings"
        );

        // Nothing to add: the theorem comes back unchanged.
        assert_eq!(
            under_prefix(&bridge, &prefix, &prefix).map(|t| t.concl().clone()),
            Some(bridge.concl().clone())
        );
        // No parameters: weakening, and the target list is still right-nested.
        let closed = Thm::eq_refl(c);
        let w = under_prefix(&closed, &[], &prems).expect("weakening");
        assert_eq!(
            *w.concl(),
            Formula::imp(derived::conj_of(&prems).expect("five atoms"), eq)
        );

        // **A prefix that is not one is refused**, rather than searched for.
        let mut shuffled = extra.clone();
        shuffled.extend(prefix.iter().cloned());
        assert!(
            under_prefix(&bridge, &prefix, &shuffled).is_none(),
            "the parameters must come first, or the rule is not in Lean's argument order"
        );
        assert!(under_prefix(&bridge, &prefix, &prefix[..1]).is_none(), "shorter than the prefix");
    }

    /// `reassume` really re-states a derivation, and only under a *superset*:
    /// re-stating under assumptions that do not include the ones actually used
    /// would be exactly the way to lose an obligation silently.
    #[test]
    fn reassume_restates_and_reorders() {
        let mut env = Env::new();
        let (h1, h2, h3) = (atom(&mut env), atom(&mut env), atom(&mut env));
        let c = constant(&mut env);
        let eq = Formula::eq(c.clone(), c.clone());

        // ⊢ (h1 ∧ h2) → c = c
        let from = vec![h1.clone(), h2.clone()];
        let base = derived::a1i(&Thm::eq_refl(c.clone()), conj_of(&from).expect("non-empty"));

        // Reordered and extended.
        let to = vec![h3.clone(), h2.clone(), h1.clone()];
        let out = reassume(&base, &from, &to).expect("re-statement");
        assert_eq!(*out.concl(), Formula::imp(conj_of(&to).expect("non-empty"), eq.clone()));

        // Dropping an assumption that is genuinely used is refused.
        assert!(reassume(&base, &from, &[h1.clone()]).is_none(), "must not shed an assumption");
        assert!(reassume(&base, &from, &[]).is_none(), "must not shed every assumption");
        // An unconditional theorem may of course be weakened.
        let plain = Thm::eq_refl(c);
        let weak = reassume(&plain, &[], std::slice::from_ref(&h1)).expect("weakening");
        assert_eq!(*weak.concl(), Formula::imp(h1, eq));
    }

    /// `CondEq` refuses to describe a theorem it does not have: an assumption
    /// list that is not the theorem's antecedent is rejected outright, which is
    /// what stops a rule from advertising a discharged obligation it never
    /// discharged.
    #[test]
    fn cond_eq_checks_its_own_assumptions() {
        let mut env = Env::new();
        let (h1, h2) = (atom(&mut env), atom(&mut env));
        let c = constant(&mut env);
        let refl = Thm::eq_refl(c.clone());

        assert!(CondEq::new(refl.clone(), vec![]).is_some(), "a bare equation assumes nothing");
        assert!(CondEq::new(refl.clone(), vec![h1.clone()]).is_none(), "an equation is not an implication");

        let under_h1 = derived::a1i(&refl, h1.clone());
        assert!(CondEq::new(under_h1.clone(), vec![h1.clone()]).is_some());
        assert!(CondEq::new(under_h1.clone(), vec![h2.clone()]).is_none(), "the wrong assumption");
        assert!(CondEq::new(under_h1.clone(), vec![]).is_none(), "assumption cannot be dropped");
        assert!(CondEq::new(under_h1, vec![h1, h2]).is_none(), "assumption cannot be invented");

        // The conclusion has to be an equation, whatever the antecedent is.
        let not_eq = derived::imp_refl(Formula::false_());
        assert!(CondEq::new(not_eq, vec![Formula::false_()]).is_none());
    }

    /// [`peel_off`] removes the assumption it was given a proof of, keeps the
    /// rest, and refuses a proof of anything else.
    ///
    /// This is the algebra behind [`TgBackend::peel_family`], and the property
    /// that matters is the second half: an assumption may only leave a
    /// certificate against a derivation of *that* assumption. A rule that could
    /// drop one is the one unrecoverable error in this accounting, so it is
    /// tested rather than argued.
    #[test]
    fn peeling_discharges_the_assumption_it_names() {
        let mut env = Env::new();
        let (h1, h2) = (atom(&mut env), atom(&mut env));
        let c = constant(&mut env);
        let refl = Thm::eq_refl(c.clone());
        // A *provable* assumption, so that there is something real to discharge
        // it with: `h1 → h1` is `derived::imp_refl`.
        let taut = Formula::imp(h1.clone(), h1.clone());
        let eq = Formula::eq(c.clone(), c.clone());

        // ── The assumption comes off, and the others survive in order ────────
        let hyps = vec![h1.clone(), taut.clone(), h2.clone()];
        let whole = conj_of(&hyps).expect("non-empty");
        let cert = CondEq::new(derived::a1i(&refl, whole), hyps).expect("conditional");
        let rest = vec![h1.clone(), h2.clone()];
        let rest_h = conj_of(&rest).expect("non-empty");
        let fam = derived::a1i(&derived::imp_refl(h1.clone()), rest_h.clone());
        let out = peel_off(&cert, 1, &fam).expect("peel");
        assert_eq!(out.hyps, rest, "the other assumptions survive, in order");
        assert_eq!(*out.thm.concl(), Formula::imp(rest_h.clone(), eq.clone()));

        // ── A proof of something else discharges nothing ─────────────────────
        let bogus = derived::a1i(&derived::imp_refl(h2.clone()), rest_h);
        assert!(peel_off(&cert, 1, &bogus).is_none(), "a proof of the wrong assumption must not peel");
        // …nor does one stated under the wrong assumption set.
        let misstated = derived::a1i(&derived::imp_refl(h1.clone()), h1.clone());
        assert!(peel_off(&cert, 1, &misstated).is_none(), "a proof under the wrong hypotheses must not peel");
        assert!(peel_off(&cert, 3, &bogus).is_none(), "out of range");

        // ── The last assumption leaves an unconditional certificate ──────────
        let one = CondEq::new(derived::a1i(&refl, taut.clone()), vec![taut]).expect("conditional");
        let out = peel_off(&one, 0, &derived::imp_refl(h1)).expect("peel");
        assert!(out.hyps.is_empty(), "nothing is left assumed");
        assert_eq!(*out.thm.concl(), eq, "and the equation is proved outright");
    }

    /// Transitivity across two derivations with different assumptions produces
    /// the union, as a real antecedent.
    #[test]
    fn conditional_transitivity_merges_assumptions() {
        let mut env = Env::new();
        let (h1, h2) = (atom(&mut env), atom(&mut env));
        let b = constant(&mut env);
        // ⊢ h1 → d = b and ⊢ h2 → b = b, from a genuine equation and reflexivity.
        let (d, d_def) = derived::define_abbrev(&mut env, &[], &b).expect("define");
        let ab = derived::inst_all(&d_def, &[]).expect("instantiate"); // ⊢ d = b
        let da = Term::apply(d, vec![]);

        let c1 = CondEq::new(derived::a1i(&ab, h1.clone()), vec![h1.clone()]).expect("conditional");
        let c2 = CondEq::new(derived::a1i(&Thm::eq_refl(b.clone()), h2.clone()), vec![h2.clone()]).expect("cond");

        let hyps = merge_hyps(&c1.hyps, &c2.hyps);
        let h = conj_of(&hyps).expect("non-empty");
        let x = reassume(&c1.thm, &c1.hyps, &hyps).expect("restate");
        let y = reassume(&c2.thm, &c2.hyps, &hyps).expect("restate");
        let out = u_eq_trans(&mut env, &x, &y, Some(&h)).expect("transitivity");
        assert_eq!(*out.concl(), Formula::imp(Formula::and(h1, h2), Formula::eq(da, b)));
    }

    /// A characteristic axiom that is not the one `lambda_n` produces for the
    /// symbol at hand is rejected: the derivation would otherwise be sound but
    /// about the wrong sets, and silently so.
    #[test]
    fn lam_ext_n_rejects_a_foreign_axiom() {
        let mut env = Env::new();
        let ap = Apply::new(&mut env).expect("Apply::new");
        let t = env.declare(2);
        let t2 = env.declare(1);
        let (lam, lam_ax) = lambda_n(&mut env, &ap, t).expect("lambda_n");
        let (lam2, lam2_ax) = lambda_n(&mut env, &ap, t2).expect("lambda_n");
        // The two axioms swapped over: right shape, wrong symbols.
        assert!(lam_ext_n(&mut env, &ap, t, lam, &lam2_ax, t2, lam2, &lam_ax).is_none());
    }
}
