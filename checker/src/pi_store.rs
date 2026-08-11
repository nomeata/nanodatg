//! **The one dependent-product mint**, shared by both engines over one
//! [`crate::tg::EnvCore`].
//!
//! The sibling of [`crate::lam_store`], for `Π`. Read that module first: the
//! argument, the `Minter` measurement and the `inert_on_refusal` contract are
//! all the same and are not restated here. What follows is only what `Π`
//! does differently.
//!
//! # Why Π was the better target, and λ the one that was done first
//!
//! `⟦Π x:A. B⟧ = dprod_C(h⃗, ⟦A⟧)`: the *fibre* `B` is skeletonised at the
//! binder, the shape `C` gets a symbol, holes ride along. Both engines did that
//! privately — `mini`'s `fibres`/`fibre_by_sym`, the tg backend's
//! `Shared::pi_infos`/`pi_by_dprod` — over one shared core, so the same shape
//! hashed identically on both sides and minted **two** `dprod` symbols.
//!
//! `ENV-UNIFY.md` §B5 measured both halves before either was built, and the
//! two are not alike:
//!
//! | site | common / one-sided | nominal-blind |
//! |------|--------------------|---------------|
//! | lam  | 49 / 919+554       | 140 / 673+440 |
//! | Π    | 159 / 467+467      | **621 / 3+3** |
//!
//! λ's one-sided residue is **structural**: on `034_boolType` the two engines
//! mint nine λ shapes with *zero* shared, because `mini` generates the
//! recursor itself and skeletonises its own nest's bodies while the checker
//! walks the export's `Expr::Lambda` nodes — not even at the same arity. No
//! change to lambda handling merges those.
//!
//! **Π has no such divergence.** Blanking the `FnSym` ids collapses the
//! one-sided counts from 467+467 to 3+3, and the counts are equal file by file
//! across all 89 exports. That population is *the same skeleton wearing two
//! symbols*, and it is erased by construction by one mint path.
//!
//! # The one real difference from `LamStore`: two engines want two depths
//!
//! A `lam` site is one construction and either engine gets all of it. A `Π`
//! site is not. The checker's old `build_fibre` stopped after
//! `image_symbol_n` + `dprod_symbol_n`; `mini` went on through the rest of
//! [`derived::ext::DProdN`] and then four more universe lemmas, because it
//! needs `dprod(h⃗,A) ∈ U(c)` and the checker never asks.
//!
//! Merging by always building the deeper one would make the checker pay
//! `dprod_members_n`, `dprod_subset_funspace_n` and the whole universe layer at
//! every fibre it interprets, on a corpus where it minted 621 of them. So the
//! site is **tiered**: [`Fibre`] is what the symbol *is* and both engines get
//! it; [`Full`] is what `mini` proves *about* it and is built on the first ask
//! that wants it, upgrading the stored entry in place. A checker-minted site
//! that `mini` later reaches is upgraded, not re-minted — the symbol is
//! already one, which is the whole point.
//!
//! That is the same principle `LamStore`'s header states as "derivations over a
//! site stay in the engine that wants them"; `Π` is where it has teeth.
//!
//! # What is *not* merged here
//!
//! The `∀` half — the checker's `prop_infos`/`prop_by_chi` and `mini`'s
//! `conds`/`cond_by_sym`, ~545 more duplicate mints — is a second table on this
//! same pattern and is deliberately not in this one. It has a hazard `Π` does
//! not: the checker's `build_cond` takes the domain parameter at the
//! *canonical* slot `hole_var(k)`, while `mini`'s `cond_site` takes a
//! `fresh_var()`. The keys still agree (the key is the fibre skeleton, which
//! mentions neither), but `phi` and `params` do not, so merging the two needs
//! `mini` moved onto the canonical slot first — a behavioural change to a
//! derivation, not a table move. Doing it inside this tranche would have made
//! one commit that both merges a table and alters a proof.
//!
//! And `Shared::undet_syms` stays a third, checker-only table, for the reason
//! its own doc gives: one skeleton can sit under both a decided and an
//! undecided `Π`, and sharing would hand one the other's answer.

use std::collections::HashMap;
use std::rc::Rc;

use derived::prelude::Prelude;
use kernel::{Env, FnSym, FreeVar, Term, Thm};

pub use crate::lam_store::Minter;

/// What the `dprod` symbol **is**: the definitional extension, and nothing
/// proved on top of it. Both engines get this.
///
/// Named to match the tg backend's own `Fibre`, whose five fields these are,
/// so that `info.fibre.as_ref()` keeps reading at every one of its call sites.
#[derive(Clone, Debug)]
pub struct Fibre {
    /// The fibre function `b(h⃗, x)`, of arity `k+1`.
    pub b: FnSym,
    /// `⊢ ∀h⃗ ∀x. b(h⃗,x) = skeleton`.
    pub b_def: Thm,
    /// `img(h⃗, A) = { b(h⃗,x) : x ∈ A }`.
    pub img: FnSym,
    /// `⊢ ∀h⃗ ∀A ∀w. (w ∈ img(h⃗,A) ↔ ∃x. (x ∈ A ∧ w = b(h⃗,x)))`.
    pub img_ax: Thm,
    /// `⊢ ∀h⃗ ∀A ∀f. (f ∈ dprod(h⃗,A) ↔ (f ∈ fs(A,⋃img(h⃗,A)) ∧ section(f)))`.
    pub dprod_def: Thm,
}

/// What `mini` proves *about* the symbol, built on the first ask that wants it.
///
/// Kept apart from [`Fibre`] so that the checker — which needs none of it — does
/// not pay for it at every fibre. See the module header.
#[derive(Clone)]
pub struct Full {
    /// The complete [`derived::ext::DProdN`], i.e. [`Fibre`] plus `dprod_ax` and
    /// `dprod_sub`. Assembled from the fields already minted, never by
    /// `DProdN::new` — that would mint a *second* `img` and `dprod`, which is
    /// precisely the duplication this module exists to remove.
    pub dp: Rc<derived::ext::DProdN>,
    /// `⊢ ∀h⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres) → img(h⃗,A) ∈ U(c))`.
    pub replacement: Thm,
    /// `⊢ ∀h⃗ ∀c ∀A. ((A ∈ U(c) ∧ fibres) → dprod(h⃗,A) ∈ U(c))`.
    pub rule: Thm,
}

/// Everything known about one **fibre skeleton**, shared by every `Π` whose
/// fibre has that shape and now by both engines.
///
/// Holes are *not* here: they are per occurrence, and both engines attach them
/// at the use site (the checker on its `PiSite`, `mini` by cloning a view).
/// That is [`crate::lam_store::LamSite`]'s convention and is kept.
#[derive(Clone)]
pub struct PiSite {
    /// The head symbol of the interpretation, `dprod(h⃗, A)`, of arity `k+1`.
    pub dprod: FnSym,
    /// The hole count of the occurrence that first built the symbols.
    pub k: usize,
    /// The definitional extension, or `None` for the **inert** encoding: the
    /// right shape and arity, so the interpretation stays compositional and
    /// total, with no defining axioms and hence no `Π` bridge. The checker
    /// wants this (it reports the gap downstream); `mini` declines it.
    pub fibre: Option<Fibre>,
    /// The universe layer, present once some caller has asked for it.
    pub full: Option<Rc<Full>>,
}

struct Provenance {
    site: Rc<PiSite>,
    minted_by: Minter,
    asked_by: [bool; 2],
}

/// The shared table: one entry per fibre shape, found by shape or by symbol.
#[derive(Default)]
pub struct PiStore {
    by_skel: HashMap<Term, Provenance>,
    by_dprod: HashMap<FnSym, (Term, Rc<PiSite>)>,
    mints: [u64; 2],
    /// Lookups answered from an entry the **other** engine minted — the second
    /// mints this table prevented, and the whole point of it.
    cross_hits: [u64; 2],
    own_hits: [u64; 2],
    /// Sites whose [`Full`] layer was built onto an entry that already existed.
    /// The tiering's own measurement: a positive count is a `dprod` symbol that
    /// was minted once and proved about later, which is exactly what the two
    /// old tables could not do.
    upgrades: u64,
    /// Upgrades that *failed*, leaving the entry at [`Fibre`]. The caller gets
    /// `None` and gaps; nothing is stored as full that is not full.
    upgrade_failed: u64,
    inert: u64,
    failed: u64,
}

fn ix(m: Minter) -> usize {
    match m {
        Minter::Mini => 0,
        Minter::Checker => 1,
    }
}

/// The universe layer over an already-minted [`Fibre`]. Free function so that
/// the mint path and the upgrade path run literally the same code.
fn build_full(env: &mut Env, pre: &Prelude, k: usize, dprod: FnSym, core: &Fibre) -> Option<Full> {
    // `DProdN`'s remaining two lemmas, over the symbols already minted.
    // **Not** `DProdN::new`: that would mint a second `img` and a second
    // `dprod`, which is the duplication this module exists to remove.
    let dprod_ax = derived::ext::dprod_members_n(
        env,
        &pre.ap,
        &pre.fs,
        core.img,
        core.b,
        dprod,
        &core.dprod_def,
    )?;
    let dprod_sub = derived::ext::dprod_subset_funspace_n(
        env,
        &pre.ap,
        &pre.fs,
        core.img,
        core.b,
        dprod,
        &core.dprod_def,
    )?;
    let dp = derived::ext::DProdN {
        k,
        b: core.b,
        img: core.img,
        img_ax: core.img_ax.clone(),
        dprod,
        dprod_def: core.dprod_def.clone(),
        dprod_ax,
        dprod_sub,
    };
    let ur = derived::universe::universe_replacement_n(
        env,
        &pre.tower.space.empty_ax,
        dp.img,
        &dp.img_ax,
        dp.b,
    )?;
    let replacement = derived::universe::least_universe_replacement_n(
        env,
        pre.tower.space.lu,
        &pre.tower.space.lu_ax,
        dp.img,
        dp.b,
        &ur,
    )?;
    let rule = {
        let fibre = dp.fibre(&replacement);
        let u = derived::ext::UniverseParts {
            lu: pre.tower.space.lu,
            c2: &pre.tower.space.c2,
            fs_in_u: &pre.tower.funspace_of,
            union: &pre.tower.union,
            bin_union: &pre.tower.bin_union,
        };
        let general = derived::ext::dprod_in_universe_of_n(env, &pre.ap, &pre.fs, &fibre, &u)?;
        derived::ext::dprod_in_universe_pair_n(env, &pre.ap, &fibre, &u, &general)?
    };
    Some(Full { dp: Rc::new(dp), replacement, rule })
}

impl PiStore {
    /// The site for fibre shape `skel` with `k` holes, minting it if this is
    /// the first time **either** engine has asked, and upgrading it to [`Full`]
    /// if this ask wants that and an earlier one did not.
    ///
    /// `inert_on_refusal` and the `Minter` measurement are
    /// [`crate::lam_store::LamStore::site`]'s and mean the same here.
    /// `want_full` is this table's own: see the module header on tiering.
    #[allow(clippy::too_many_arguments)]
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
        want_full: bool,
    ) -> Option<Rc<PiSite>> {
        if let Some(p) = self.by_skel.get_mut(skel) {
            let cross = p.minted_by != who;
            p.asked_by[ix(who)] = true;
            let site = p.site.clone();
            if cross {
                self.cross_hits[ix(who)] += 1;
            } else {
                self.own_hits[ix(who)] += 1;
            }
            let Some(core) = site.fibre.as_ref() else {
                // Inert: `mini` declines it exactly as it declines its own
                // refusal, the checker takes the opaque symbol.
                return if inert_on_refusal { Some(site) } else { None }
            };
            if !want_full || site.full.is_some() {
                return Some(site)
            }
            // **The upgrade.** The symbol stays; only the proofs about it are
            // added. This is the path a checker-minted site takes when `mini`
            // reaches the same shape.
            let Some(full) = build_full(env, pre, site.k, site.dprod, core) else {
                self.upgrade_failed += 1;
                return None
            };
            self.upgrades += 1;
            let upgraded = Rc::new(PiSite { full: Some(Rc::new(full)), ..(*site).clone() });
            self.by_skel
                .get_mut(skel)
                .expect("the entry was just read")
                .site = upgraded.clone();
            self.by_dprod.insert(upgraded.dprod, (skel.clone(), upgraded.clone()));
            return Some(upgraded)
        }
        debug_assert_eq!(hole_vars.len(), k, "the caller supplies exactly the k hole variables");
        // `b(h⃗, x) = skeleton`, holes **first** and the binder **last** — the
        // same argument order `LamStore::site` fixes for `t`, and every `_n`
        // construction in `derived` assumes it.
        let mut xs: Vec<FreeVar> = hole_vars.to_vec();
        xs.push(x_canon);
        let built = derived::define_abbrev(env, &xs, skel).and_then(|(b, b_def)| {
            let (img, img_ax) = derived::ext::image_symbol_n(env, b)?;
            let (dprod, dprod_def) = derived::ext::dprod_symbol_n(env, &pre.ap, &pre.fs, img, b)?;
            Some((dprod, Fibre { b, b_def, img, img_ax, dprod_def }))
        });
        let site = match built {
            Some((dprod, core)) => {
                let full = if want_full {
                    match build_full(env, pre, k, dprod, &core) {
                        Some(f) => Some(Rc::new(f)),
                        None => {
                            // The caller that wanted the universe layer gets
                            // nothing, and nothing is stored: a later ask
                            // retries, exactly as a failed mint does.
                            self.failed += 1;
                            return None
                        }
                    }
                } else {
                    None
                };
                PiSite { dprod, k, fibre: Some(core), full }
            }
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
                PiSite { dprod: env.declare(arity), k, fibre: None, full: None }
            }
        };
        let site = Rc::new(site);
        self.mints[ix(who)] += 1;
        let mut asked_by = [false; 2];
        asked_by[ix(who)] = true;
        self.by_skel
            .insert(skel.clone(), Provenance { site: site.clone(), minted_by: who, asked_by });
        self.by_dprod.insert(site.dprod, (skel.clone(), site.clone()));
        Some(site)
    }

    /// The site behind a `dprod` symbol, and the shape it was keyed on — the
    /// read-back direction, `mini`'s `fibre_by_sym` and the tg backend's
    /// `pi_by_dprod`.
    pub fn by_dprod(&self, f: FnSym) -> Option<(&Term, &Rc<PiSite>)> {
        self.by_dprod.get(&f).map(|(sk, s)| (sk, s))
    }

    /// The site for a shape, without minting.
    pub fn get(&self, skel: &Term) -> Option<&Rc<PiSite>> {
        self.by_skel.get(skel).map(|p| &p.site)
    }

    /// Every shape keyed — the skeleton-key measurement's `Π` column.
    pub fn keys(&self) -> Vec<Term> { self.by_skel.keys().cloned().collect() }

    /// Shapes **both** dispatches asked for, and the one-sided residues:
    /// `(both, mini only, checker only)`. See
    /// [`crate::lam_store::LamStore::asked`], which this mirrors.
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

    /// The one-mint measurement, in the crossing ledger's `k=v` tab-separated
    /// row shape so the same scrapers read it.
    pub fn report(&self) -> String {
        let (both, monly, conly) = self.asked();
        format!(
            "pimint\tsites={}\tmintedByMini={}\tmintedByChecker={}\t\
             crossHitsMini={}\tcrossHitsChecker={}\townHitsMini={}\townHitsChecker={}\t\
             askedByBoth={both}\taskedByMiniOnly={monly}\taskedByCheckerOnly={conly}\t\
             upgrades={}\tupgradeFailed={}\tinert={}\tfailed={}",
            self.by_skel.len(),
            self.mints[0],
            self.mints[1],
            self.cross_hits[0],
            self.cross_hits[1],
            self.own_hits[0],
            self.own_hits[1],
            self.upgrades,
            self.upgrade_failed,
            self.inert,
            self.failed,
        )
    }

    /// `(mints, cross-hits, upgrades)` summed over both engines — for a test
    /// that wants the numbers without parsing [`PiStore::report`].
    pub fn totals(&self) -> (u64, u64, u64) {
        (self.mints[0] + self.mints[1], self.cross_hits[0] + self.cross_hits[1], self.upgrades)
    }
}
