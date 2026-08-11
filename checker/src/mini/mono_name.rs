//! **`monomorph`'s root prefix, inverted** — the one place in `mini` that
//! knows the naming scheme of `MONOMORPH.md` §1.1.
//!
//! # Interface
//!
//! ```text
//! mono_name::strip(&Name) -> Name
//! ```
//!
//! Total: a name that does not carry the prefix comes back unchanged, so a
//! caller never has to ask first.
//!
//! # The scheme, and why inverting it is a one-liner
//!
//! `monomorph` erases universe polymorphism by emitting one copy of a
//! declaration per ground instantiation `σ`, and names the copy by prepending
//!
//! ```text
//! _at ++ ⟨|σ|⟩ ++ ⟨σ₀⟩ ++ … ++ ⟨σ_{|σ|-1}⟩
//! ```
//!
//! at the **root** — `_at` a `Name.str` component, every `⟨·⟩` a `Name.num`.
//! `PUnit.{u}` at `[1]` is `_at.1.1.PUnit`, `Pair.{u,v}` at `[1,0]` is
//! `_at.2.1.0.Pair`, and `PTree._model.rec_0` at `[0]` is
//! `_at.1.0.PTree._model.rec_0`. A monomorphic declaration keeps its name
//! exactly, and `σ` empty is the identity.
//!
//! The prefix is at the root and **does not depend on the shape of the name it
//! is prepended to**; that is the property `MONOMORPH.md` §1.1 argues for at
//! length, and it is what makes this function possible. The length component
//! `⟨|σ|⟩` is there so the marker's extent is known without looking at what
//! follows it: read `_at`, read `k`, take the next `k` components, and
//! everything after that is the input's own name, whatever shape it has —
//! including a name whose own root component is numeric. Without the length,
//! `_at.0` prepended to `1.Foo` and `_at.0.1` prepended to `Foo` would be the
//! same name and the scheme would not be invertible.
//!
//! # Who is allowed to call this, and who must not
//!
//! **Only a clause table keyed on a name.** `mini` decides almost everything
//! structurally, and where it does not — [`crate::mini::direct::clause_for`]'s three
//! rows, which name a `derived/` construction that no general walk can reach —
//! the key is a name the pass is entitled to rewrite. Those sites ask about the
//! declaration the copy *is a copy of*, and this is how they ask.
//!
//! **One caller, and the reason is the built-in list and not luck.** `mini`'s
//! other name-keyed tables are [`crate::mini::quot::prim_for`]
//! (`Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`), [`crate::mini::axiom::clause_for`]
//! (`Quot.sound`) and [`crate::mini::convert::is_standard_axiom`] (`propext`,
//! `Classical.choice`, `Quot.sound`), and every one of those names is in
//! `monomorph`'s carried seed (`MONOMORPH.md` §3) — the quotient recognised
//! *structurally*, by the export's own record kind, and the three axioms by
//! name. They cannot acquire a prefix, so they do not need to see through one.
//! `Eq` and `Nat`, [`crate::mini::direct`]'s other two rows, are carried for the same
//! reason; `Acc` is not, and that asymmetry is what made the table the one
//! caller.
//!
//! It is **not** a general "real name of" and must not be used to decide
//! anything two copies of one declaration disagree about. `⟦T.{0}⟧` and
//! `⟦T.{1}⟧` are unrelated symbols (`LEVEL-POLYMORPHIC-INDUCTIVES.md` §3.1),
//! and after monomorphization they are unrelated *declarations*; a site that
//! stripped the prefix to look one of them up in a store keyed on the other
//! would be reading the wrong copy. Nothing here recovers `σ`, deliberately:
//! the callers do not want it, and a function that returned it would invite
//! exactly that use.
//!
//! # Why the fix is here and not in `monomorph`
//!
//! Making the pass skip `Acc` — carrying it as a built-in the way `Eq` and
//! `Nat` are carried (`MONOMORPH.md` §3) — would also close the gap, and is
//! the wrong trade. The built-in list exists for constants a *kernel* mints by
//! name and so cannot be told about a copy; `Acc` is not one of those, and
//! putting it there would make `monomorph`'s output depend on which
//! declarations one particular consumer happens to have a closed form for.
//! Every consumer that grew such a table would want its own entry. The prefix
//! is shape-free precisely so the consumer side can be the side that adapts.

use crate::mini::expr::{Name, NameView};

/// The `Name.str` component that opens the prefix.
const MARKER: &str = "_at";

/// `mono(d, σ) ↦ d`, and the identity on everything else.
///
/// Recognises the prefix only in full: `_at`, a length `k`, and then `k`
/// further `Name.num` components. A name that starts `_at` and does not
/// continue that way is somebody else's `_at` and comes back untouched.
pub fn strip(n: &Name) -> Name {
    // The prefix is at the *root*, so the components have to be collected
    // outermost-last before it can be read. `comps` is the name written left
    // to right: `_at.1.1.PUnit` gives `[_at, 1, 1, PUnit]`.
    let mut comps: Vec<NameView> = Vec::new();
    let mut cur = *n;
    loop {
        match cur.view() {
            NameView::Anon => break,
            v @ NameView::Str(pre, _) | v @ NameView::Num(pre, _) => {
                comps.push(v);
                cur = pre;
            }
        }
    }
    comps.reverse();
    // `_at`, then the length.
    let Some(NameView::Str(_, marker)) = comps.first() else { return *n };
    if &**marker != MARKER {
        return *n
    }
    let Some(NameView::Num(_, k)) = comps.get(1) else { return *n };
    let k = *k as usize;
    // `k` numerals must follow, and something must follow *them*: the prefix
    // is prepended to a name, never emitted alone.
    if comps.len() <= 2 + k {
        return *n
    }
    if !comps[2..2 + k].iter().all(|c| matches!(c, NameView::Num(..))) {
        return *n
    }
    // Rebuild the tail onto the anonymous root, one component at a time.
    let mut out = Name::anon();
    for c in &comps[2 + k..] {
        out = match c {
            NameView::Str(_, s) => Name::str(&out, s),
            NameView::Num(_, i) => Name::num(&out, *i),
            NameView::Anon => return *n,
        };
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `_at.1.0.Acc ↦ Acc`, the case that closes `117`/`118`.
    #[test]
    fn one_level_prefix_comes_off() {
        let at = Name::num(&Name::num(&Name::simple("_at"), 1), 0);
        let renamed = Name::str(&at, "Acc");
        assert_eq!(strip(&renamed), Name::simple("Acc"), "{renamed} should strip to Acc");
    }

    /// **Three numerals, not two.** A σ of length 2 passes under an inverter
    /// that read the components in the wrong order, and one of length 1 passes
    /// under an inverter that ignored the length entirely; `[0,1,2]` fails both.
    /// The second half is the length doing its job: the *same three numerals*
    /// under a declared length of 2 are a different name, and only two of them
    /// belong to the prefix.
    #[test]
    fn three_numerals_pin_the_extent() {
        let mut at = Name::num(&Name::simple("_at"), 3);
        for i in [0u64, 1, 2] {
            at = Name::num(&at, i);
        }
        let renamed = Name::str(&at, "Trip");
        assert_eq!(strip(&renamed), Name::simple("Trip"), "{renamed}");

        let mut bad = Name::num(&Name::simple("_at"), 2);
        for i in [0u64, 1, 2] {
            bad = Name::num(&bad, i);
        }
        let bad = Name::str(&bad, "Trip");
        assert_eq!(
            strip(&bad),
            Name::str(&Name::num(&Name::anon(), 2), "Trip"),
            "a declared length of 2 consumes two numerals and leaves the third: {bad}"
        );
    }

    /// The tail keeps **all** of its own shape, including numeric components —
    /// which is the whole reason the length is in the scheme. Three tail
    /// components, because two cannot tell `Foo.7.bar` from `Foo.bar.7`.
    #[test]
    fn a_numeric_tail_survives_intact() {
        let tail = Name::str(&Name::num(&Name::simple("Foo"), 7), "bar");
        let at = Name::num(&Name::num(&Name::simple("_at"), 1), 0);
        let renamed = Name::str(&Name::num(&Name::str(&at, "Foo"), 7), "bar");
        assert_eq!(strip(&renamed), tail, "{renamed}");
    }

    /// An unprefixed name is the identity — including a name that merely
    /// *starts* `_at`, and the bare prefix with nothing after it.
    #[test]
    fn everything_else_is_untouched() {
        for n in [
            Name::simple("Acc"),
            Name::str(&Name::simple("Nat"), "succ"),
            // `_at` with no length after it.
            Name::str(&Name::simple("_at"), "Acc"),
            // The prefix alone, with no name to have been prepended to.
            Name::num(&Name::num(&Name::simple("_at"), 1), 0),
            // A declaration whose own root is `_at` followed by a *string*.
            Name::str(&Name::str(&Name::simple("_at"), "one"), "Acc"),
        ] {
            assert_eq!(strip(&n), n, "{n} is not a monomorph copy");
        }
    }

    /// `modelgen`'s names compose with the prefix and come back whole — the
    /// property `MONOMORPH.md` §1.1 calls "free of any dependence on the shape
    /// of the name being renamed". Three tail components again.
    #[test]
    fn a_model_name_composes() {
        let inner = Name::str(&Name::str(&Name::simple("PTree"), "_model"), "rec_0");
        let at = Name::num(&Name::num(&Name::simple("_at"), 1), 0);
        let renamed = Name::str(&Name::str(&Name::str(&at, "PTree"), "_model"), "rec_0");
        assert_eq!(strip(&renamed), inner, "{renamed}");
    }
}
