//! Extensionality for Replacement images, the dependent product, and Lean's λ
//! and Π typing rules.
//!
//! This module is a **hub**: every construction lives in its own file with its
//! own interface header, and everything is re-exported here, so the paths
//! `crate::ext::…` all still resolve and no caller has to know which file a
//! theorem came from. Read the header of the one file you need — none of them
//! requires any of the others' derivations.
//!
//! | file | what it exports |
//! |---|---|
//! | [`lam_cong`] | `img(A) = img'(A')` and `lam(A) = lam'(A')` from equal domains and pointwise equal bodies — the checker's `lam_cong` |
//! | [`dprod`] | the symbol `dprod(A) = Π(x:A). b(x)`, its defining axiom, and `dprod(A) ⊆ fs(A, ⋃img(A))` |
//! | [`pi_cong`] | `dprod(A) = dprod'(A')` from equal domains and pointwise equal fibres — the checker's `pi_cong` |
//! | [`funspace_cong`] | `fs(a,b) = fs(a',b')` from `a = a'` and `b = b'`, in quantified-implication form |
//! | [`app`] | `app(f,x) = y` from `⟨x,y⟩ ∈ f`, and `app(f,x) ∈ b` for `f ∈ fs(a,b)` |
//! | [`fun_ext`] | `f = g` for two members of `fs(a,b)` that agree pointwise — **function extensionality** |
//! | [`eta`] | `f = graph(f,A)` for `f ∈ fs(A,B)` — a function **is** the graph of its own application |
//! | [`retarget`] | `f ∈ fs(a,b)` becomes `f ∈ fs(a,c)` whenever the values lie in `c` |
//! | [`const_fibre`] | `dprod(A) = fs(A,B)` when every fibre is `B` |
//! | [`lam_typing`] | `lam(A) ∈ fs(A,C)` and `lam(A) ∈ dprod(A)` — **Lean's λ rule** |
//! | [`dprod_universe`] | `dprod(A) ∈ U(c)`, conditionally and then unconditionally — **Lean's Π rule** |
//! | [`dprod_n`] | the symbols `img(q⃗,A)`, `dprod(q⃗,A)` and their lemmas, for a fibre carrying a parameter prefix |
//! | [`dprod_universe_n`] | `dprod(q⃗,A) ∈ U(c)` from `A ∈ U(c)` and the fibres — **Lean's Π rule, n-ary** |
//! | [`lam_cong_n`] | [`lam_cong`] with a parameter prefix on each side |
//! | [`pi_cong_n`] | [`pi_cong`] with a parameter prefix on each side |
//! | [`const_fibre_n`] | [`const_fibre`] with a parameter prefix on the fibre |
//! | [`lam_typing_n`] | [`lam_typing`] with a prefix on the lambda and an independent one on the fibre |
//!
//! The four `…_n` files at the bottom are the **n-ary ports** of the four above
//! them, and coincide with them at prefix length zero. They exist because a
//! binder's body is an open expression: it decomposes into a skeleton plus its
//! maximal binder-free subterms ([`crate::skeleton`]), so the symbol built from
//! it carries one parameter per hole in addition to the binder, and a symbol's
//! arity is fixed. See [`dprod_n`]'s header for the argument in full.
//!
//! `shared` holds the private combinators more than one of them needs; it
//! exports no theorem and is not re-exported.
//!
//! # Why extensionality is the theme
//!
//! `⟦λx:A. b⟧` is interpreted as the *graph* `{ ⟨x, t(x)⟩ : x ∈ A }`
//! ([`crate::funcs::lambda`]) and `⟦Π(x:A). B x⟧` as a `dprod`, so both are
//! sets whose head symbol is chosen by the *shape of the body*. Two
//! interpretations of provably-equal types are therefore built by two unrelated
//! symbols, and congruence over sub-terms relates nothing at all. What relates
//! them is Extensionality — same members, same set — and that is what
//! [`lam_cong`], [`pi_cong`] and [`const_fibre`] each do for one pair of
//! interpretations. [`funspace_cong`] is the one case where ordinary congruence
//! does suffice and only the *form* has to be assembled.
//!
//! The last two files are not about extensionality: they are the membership
//! facts Lean's λ and Π rules interpret to, and they live here because they are
//! about `dprod` and nothing else has it.

pub mod app;
pub mod const_fibre;
pub mod const_fibre_n;
pub mod dprod;
pub mod dprod_n;
pub mod dprod_pi;
pub mod dprod_universe;
pub mod dprod_universe_n;
pub mod eta;
pub mod fun_ext;
pub mod funspace_cong;
pub mod lam_cong;
pub mod lam_cong_n;
pub mod lam_typing;
pub mod lam_typing_n;
pub mod pi_cong;
pub mod pi_cong_n;
pub mod retarget;
mod shared;

pub use app::{app_of_pair, funspace_app_mem};
pub use const_fibre::dprod_const_fibre;
pub use const_fibre_n::dprod_const_fibre_n;
pub use dprod::{
    dprod_members, dprod_subset_funspace, dprod_symbol, image_symbol, is_section, DProd,
};
pub use dprod_n::{
    dprod_members_n, dprod_subset_funspace_n, dprod_symbol_n, image_symbol_n, section_n, DProdN,
};
pub use dprod_pi::dprod_in_universe_pair;
pub use dprod_universe::{dprod_in_universe, dprod_in_universe_of};
pub use dprod_universe_n::{
    dprod_in_universe_of_n, dprod_in_universe_pair_n, Fibre, UniverseParts,
};
pub use eta::{funspace_eta, Eta};
pub use fun_ext::{funspace_ext, pointwise};
pub use funspace_cong::fs_cong;
pub use lam_cong::{image_ext, lam_ext, lam_ext_same_domain};
pub use lam_cong_n::{image_ext_n, lam_ext_n};
pub use lam_typing::{body_in, body_in_fibre, lam_in_dprod, lam_in_funspace};
pub use lam_typing_n::{
    body_in_n, lam_in_dprod_n, lam_in_funspace_n, lam_pair_val_n, lam_single_valued_n,
};
pub use pi_cong::{dprod_ext, dprod_ext_same_domain};
pub use pi_cong_n::dprod_ext_n;
pub use retarget::{funspace_retarget, values_in};
