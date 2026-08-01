# Open questions for Joachim

Decisions I deliberately did not take autonomously, with enough context to
decide from cold. Newest first. Nothing here is blocking — work continued
around all of it.

*Nothing is currently open. §1 below has been answered and is kept for the
record.*

---

## Answered, kept for the record

- **The definitional-equality cache, once hypotheses are in the kernel**
  (raised by task #16; **resolved 2026-07-31/08-01**, checker side).

  As raised: `thm.rs` had argued that context-free theorems are what make the
  cache globally sound — a cached equality is valid absolutely, hence reusable
  anywhere. With hypotheses that fails, because `Γ ⊢ a = b` is usable only where
  `Γ` holds, so the checker had to either key the cache on the hypothesis set or
  cache only hypothesis-free theorems. Ignoring it would have been unsoundness,
  not slowness.

  **Option 1 was taken.** `certify::is_unconditional` is
  `c.thm().is_some_and(|t| t.hyps().is_empty())` and gates the equality-cache
  write in `tc.rs`; the reduct memo is gated by the weaker
  `certify::hypothesis_free` at its single write site; `Shared::declar_typings`
  was already right; and `infer_cache_*` deliberately admits *conditional*
  typings, with the reasoning at its insertion point. `kernel/README.md` records
  the decision, and the obligation section it points at is
  `kernel/src/thm.rs`'s "THE `hyps()` OBLIGATION".

- **Infinity: assert or derive?** (2026-07-31) **Derive it** — "it's a
  self-contained library task". So it stays out of the TCB; the axiom count
  remains eight.
- **Primitive-sort `ℕ`?** (2026-07-31) **No special handling for `Nat` until the
  very end.** "We will do it, but not before we run out of other things to do."
  So milestone 4 is deprioritised, and the single-sorted soundness narrative
  stands untouched for now. The choice between a primitive sort and
  numerals-as-defined-constants-plus-bignum-rule-schemas is deferred with it —
  worth revisiting *before* any milestone-4 code is written, since the first
  option is a `term.rs` rewrite rather than an addition.

- **Retire `ax_power`/`ax_union`/`ax_pairing` and `C₂`?** No — they are standard
  ZFC axioms and `C₂` is part of standard Tarski Axiom A. Similarity to the
  literature beats minimising the count.
- **How is choice supplied?** Set-level ZFC choice, guarded at non-empty members
  (Jech §1, Kunen I.12.1). Not global choice, which the thesis explicitly avoids.
- **A `the`/ε operator, or a Skolemising `define_choice`?** No. ε would make
  `Term` and `Formula` mutually recursive, dragging in the capture-avoidance
  machinery. `define_choice` at arity ≥ 1 would be *unsound* here, because
  `ax_replacement` accepts arbitrary formulas and Skolem symbols are not
  eliminable. A 0-ary Henkin constant would be sound but is not needed — the
  universe tower is `define`-able via Extensionality, and choice costs nothing
  measurable today.
- **Hypotheses in the kernel?** Yes, Isabelle-style, on the criterion that each
  kernel operation performed by the checker must be constant cost.
- **Context-relative certificates?** No. Keep hypothesis sets; the criterion is
  that the certificate at the *end of a definition* must be closed.
