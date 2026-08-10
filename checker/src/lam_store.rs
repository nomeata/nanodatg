//! **The one lambda mint**, shared by both engines over one
//! [`crate::tg::EnvCore`].
//!
//! # Why this is a store and not two caches
//!
//! `⟦λ x:A. b⟧ = lam_C(h⃗, ⟦A⟧)`: the body is skeletonised at the binder, the
//! *shape* `C` gets a symbol, and the occurrence's `v`-free subterms ride along
//! as arguments. The shape is what is keyed; the holes are per occurrence and
//! are therefore never stored.
//!
//! Both engines used to do that privately — `mini`'s `lams`/`lam_by_sym` and
//! the tg backend's `Shared::lam_infos`/`lam_by_lam` — over one shared
//! [`crate::tg::EnvCore`]. Sharing the core already made the two *keys* one
//! term (the canonical binder slot `x_canon` and the `hole_var` series come
//! from the core), so the same body shape hashed identically on both sides and
//! then minted **two** `lam` symbols, one per table.
//!
//! That is the forbidden state this repository names *identity, not
//! memoisation*: two uses of one lambda must name one carrier, or their
//! definitional equality needs a theorem where reflexivity should do. Two
//! symbols for one shape are not merely wasteful — `⊢ lam₁(h⃗,A) = lam₂(h⃗,A)`
//! is provable but nothing proves it, so a mini-derived typing about `lam₁`
//! meets a checker obligation about `lam₂` and is refused at the statement
//! guard: a counted gap where reflexivity was the whole proof.
//!
//! So the table moves onto the core, beside [`crate::const_store::ConstStore`]
//! and for the same reason: `mini` holds an [`crate::tg::EnvCore`] but no
//! `Shared`, so the core is the only place both engines reach.
//!
//! # The argument-order contract
//!
//! `t(h⃗, x)` — **holes first, the binder last**. Every `_n` construction in
//! `derived` assumes it, both engines encoded it separately and identically,
//! and [`LamStore::site`] is now the single place it is written down.
//! `mini/tests/route_tg.rs::one_lam_mint_argument_order` mutates it.
//!
//! # What each engine keeps
//!
//! The *key* is still computed per engine: `mini` calls `derived::skeleton`
//! (total), the tg backend calls its `skeleton_recorded` (through the `parts`
//! table, and `None` where a node was not recorded). The two agree node for
//! node wherever the second succeeds — same three cases, same traversal, same
//! hole numbering — so they are two decision procedures for one key, not two
//! keys. Unifying *those* is `tg.rs`'s own priced follow-on (`skeleton_recorded`
//! header) and is not this module's business.
//!
//! Likewise the derivations *over* a site — beta, extensionality,
//! `lam_in_funspace_n` — stay in the engine that wants them: they are keyed on
//! the skeleton and so, now, on one symbol series.

use std::collections::HashMap;
use std::rc::Rc;

use derived::prelude::Prelude;
use kernel::{Env, FnSym, FreeVar, Term, Thm};

/// The graph machinery for one skeleton, when it was built.
#[derive(Clone, Debug)]
pub struct Graph {
    /// The body function `t(h⃗, x)`, of arity `k+1`.
    pub t: FnSym,
    /// `⊢ ∀h⃗ ∀x. t(h⃗,x) = skeleton`.
    pub t_def: Thm,
    /// `⊢ ∀h⃗ ∀A ∀y. (y ∈ lam(h⃗,A) ↔ ∃x. (x ∈ A ∧ y = ⟨x, t(h⃗,x)⟩))` —
    /// `derived::funcs::lambda_n`'s characteristic theorem.
    pub lam_ax: Thm,
}

/// Everything known about one lambda **body shape**. Shared by every lambda
/// whose body has that shape, and now by both engines.
#[derive(Clone, Debug)]
pub struct LamSite {
    /// The graph symbol of the interpretation, `lam(h⃗, A)`, of arity `k+1`.
    pub lam: FnSym,
    /// The hole count of the occurrence that first built the symbols — the
    /// symbol's arity, less the binder.
    pub k: usize,
    /// The graph machinery, or `None` for the **inert** encoding: the right
    /// shape, so the interpretation stays compositional, with no defining
    /// axioms and hence no beta. The construction is closed for every skeleton
    /// either engine builds, so this is unreachable in practice — a reported
    /// gap rather than a wrong answer if it ever is not.
    pub graph: Option<Graph>,
}

/// Which engine first minted a site. **A measurement, never a licence**: no
/// decision in either engine reads it, and [`LamStore::site`] hands the same
/// site to both callers whatever it says. It exists so that
/// [`LamStore::report`] can say how many second mints the shared table
/// actually prevented, which is the only number that distinguishes this merge
/// from a rename.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Minter {
    Mini,
    Checker,
}

/// What one entry records beyond the site itself.
struct Provenance {
    site: Rc<LamSite>,
    /// Who minted it. See [`Minter`]: a measurement, never a licence.
    minted_by: Minter,
    /// Which engines have *asked* for this shape, `[mini, checker]`.
    ///
    /// This is the measurement the merge would otherwise have destroyed. Before
    /// it, `mini::Interp::skeleton_keys` and `tg::skeleton_keys` returned two
    /// key sets and `route_tg.rs::skeleton_key_divergence_sweep` compared them:
    /// the intersection counted shapes both dispatches keyed identically, the
    /// residues counted genuine divergence. With one table both calls return
    /// one vector, so the intersection is trivially everything and the
    /// comparison says nothing. This flag pair is the same three numbers,
    /// recovered from the asking side rather than the storing side — and it is
    /// strictly better, because it survives the cascade: a shape that only
    /// coincides *because* a nested `lam` symbol is now shared is counted here
    /// and could not be counted there.
    asked_by: [bool; 2],
}

/// The shared table: one entry per body shape, found by shape or by symbol.
#[derive(Default)]
pub struct LamStore {
    by_skel: HashMap<Term, Provenance>,
    by_lam: HashMap<FnSym, (Term, Rc<LamSite>)>,
    /// Sites minted, per minting engine.
    mints: [u64; 2],
    /// Lookups answered from an entry the **other** engine minted — the second
    /// mints this table prevented, and the whole point of it.
    cross_hits: [u64; 2],
    /// Lookups answered from an entry the same engine minted.
    own_hits: [u64; 2],
    /// Sites whose graph construction refused, minted inert.
    inert: u64,
    /// Mints that failed outright — `define_abbrev` or the arity conversion.
    /// Nothing is stored for these, so the next caller retries.
    failed: u64,
}

fn ix(m: Minter) -> usize {
    match m {
        Minter::Mini => 0,
        Minter::Checker => 1,
    }
}

impl LamStore {
    /// The site for body shape `skel` with `k` holes, minting it if this is the
    /// first time **either** engine has asked.
    ///
    /// `inert_on_refusal` is the one behavioural difference the two engines had
    /// and it is preserved as a parameter rather than legislated away: the tg
    /// backend answers a refused graph construction with an opaque symbol of
    /// the right arity (so its interpretation stays total and the gap is
    /// reported downstream at beta), `mini` answers `None` (so its caller gaps
    /// at the λ itself). A stored inert entry is visible to both — `graph:
    /// None` — and `mini` declines it exactly as it declines its own refusal.
    ///
    /// `env` is taken as a closure over the core rather than a borrow, because
    /// `define_abbrev` and `lambda_n` each want the kernel `Env` mutably and
    /// the caller must not be holding it.
    pub fn site(
        &mut self,
        who: Minter,
        pre: &Prelude,
        env: &mut Env,
        hole_vars: &[FreeVar],
        x_canon: FreeVar,
        skel: &Term,
        k: usize,
        inert_on_refusal: bool,
    ) -> Option<Rc<LamSite>> {
        if let Some(p) = self.by_skel.get_mut(skel) {
            let cross = p.minted_by != who;
            p.asked_by[ix(who)] = true;
            let site = p.site.clone();
            if cross {
                self.cross_hits[ix(who)] += 1;
            } else {
                self.own_hits[ix(who)] += 1;
            }
            if site.graph.is_none() && !inert_on_refusal {
                return None
            }
            return Some(site)
        }
        debug_assert_eq!(hole_vars.len(), k, "the caller supplies exactly the k hole variables");
        // `t(h⃗, x) = skeleton`, with the holes **first** and the binder
        // **last** — the argument order every `_n` construction assumes.
        let mut xs: Vec<FreeVar> = hole_vars.to_vec();
        xs.push(x_canon);
        let built = derived::define_abbrev(env, &xs, skel)
            .and_then(|(t, t_def)| {
                derived::funcs::lambda_n(env, &pre.ap, t)
                    .map(|(lam, lam_ax)| (lam, Graph { t, t_def, lam_ax }))
            });
        let site = match built {
            Some((lam, g)) => LamSite { lam, k, graph: Some(g) },
            None => {
                if !inert_on_refusal {
                    self.failed += 1;
                    return None
                }
                let Ok(arity) = u32::try_from(k + 1) else {
                    self.failed += 1;
                    return None
                };
                self.inert += 1;
                LamSite { lam: env.declare(arity), k, graph: None }
            }
        };
        let site = Rc::new(site);
        self.mints[ix(who)] += 1;
        let mut asked_by = [false; 2];
        asked_by[ix(who)] = true;
        self.by_skel
            .insert(skel.clone(), Provenance { site: site.clone(), minted_by: who, asked_by });
        self.by_lam.insert(site.lam, (skel.clone(), site.clone()));
        Some(site)
    }

    /// The site behind a `lam` symbol, and the shape it was keyed on.
    ///
    /// The read-back direction: a term of the shape `lam(h⃗,A)` arrives with no
    /// Lean node attached — a beta redex head, or a typing obligation's target
    /// — and the symbol is what names its machinery. `mini`'s `as_lam` and the
    /// tg backend's `lam_by_lam` reads are both this.
    pub fn by_lam(&self, f: FnSym) -> Option<(&Term, &Rc<LamSite>)> {
        self.by_lam.get(&f).map(|(sk, s)| (sk, s))
    }

    /// Is `f` a `lam` symbol of some site?
    pub fn is_lam(&self, f: FnSym) -> bool { self.by_lam.contains_key(&f) }

    /// The site for a shape, without minting.
    pub fn get(&self, skel: &Term) -> Option<&Rc<LamSite>> {
        self.by_skel.get(skel).map(|p| &p.site)
    }

    /// Every shape keyed — the skeleton-key measurement's lambda column.
    pub fn keys(&self) -> Vec<Term> { self.by_skel.keys().cloned().collect() }

    /// Shapes **both** dispatches asked for, and the one-sided residues:
    /// `(both, mini only, checker only)`. The successor of
    /// `route_tg.rs::skeleton_key_divergence_sweep`'s lam column; see
    /// [`Provenance::asked_by`].
    pub fn asked(&self) -> (usize, usize, usize) {
        let (mut both, mut m, mut c) = (0, 0, 0);
        for p in self.by_skel.values() {
            match p.asked_by {
                [true, true] => both += 1,
                [true, false] => m += 1,
                [false, true] => c += 1,
                [false, false] => unreachable!("an entry is created by an ask"),
            }
        }
        (both, m, c)
    }

    pub fn len(&self) -> usize { self.by_skel.len() }

    pub fn is_empty(&self) -> bool { self.by_skel.is_empty() }

    /// The one-mint measurement, one `k=v` tab-separated row like the crossing
    /// ledger's, so the same scrapers read it.
    ///
    /// `crossHits*` is the number that says the merge did something: a lookup
    /// the *other* engine's mint answered is a `lam` symbol that, before this
    /// table, would have been minted twice. `askedByBoth` is the same fact at
    /// shape granularity, and the two residues are the genuine divergence —
    /// shapes one dispatch produces walking a file the other also walked.
    pub fn report(&self) -> String {
        let (both, monly, conly) = self.asked();
        format!(
            "lammint\tsites={}\tmintedByMini={}\tmintedByChecker={}\t\
             crossHitsMini={}\tcrossHitsChecker={}\townHitsMini={}\townHitsChecker={}\t\
             askedByBoth={both}\taskedByMiniOnly={monly}\taskedByCheckerOnly={conly}\t\
             inert={}\tfailed={}",
            self.by_skel.len(),
            self.mints[0],
            self.mints[1],
            self.cross_hits[0],
            self.cross_hits[1],
            self.own_hits[0],
            self.own_hits[1],
            self.inert,
            self.failed,
        )
    }

    /// `(mints, cross-hits)` summed over both engines — for a test that wants
    /// the two numbers without parsing [`LamStore::report`].
    pub fn totals(&self) -> (u64, u64) {
        (self.mints[0] + self.mints[1], self.cross_hits[0] + self.cross_hits[1])
    }
}
