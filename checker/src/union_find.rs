//! A union find data structure for caching definitional equalities, which also
//! remembers **why** each equality was added.
//!
//! # Interface
//!
//! * [`UnionFind::union`] — merge two classes, recording the certificate that
//!   justified the merge on the new edge.
//! * [`UnionFind::check_uf_eq`] — the decision procedure, unchanged from
//!   upstream nanoda: are these two known equal?
//! * [`UnionFind::explain`] — the certificates along the path connecting two
//!   members of one class, each with the direction the path traverses it in.
//! * [`Hop`] — one edge of such a path.
//!
//! # Two structures, not one
//!
//! The *decision* is made by the ordinary union-find below — same node map,
//! same ranks, same path compression, same answers as upstream — and nothing in
//! this file changes what it decides. The *explanation* is a second, separate
//! forest: one edge per successful `union`, labelled with the certificate for
//! that union, and never compressed.
//!
//! They are kept apart because path compression destroys explanations: it
//! reparents a node onto a root it has no single edge to. Keeping the proof
//! forest uncompressed costs a longer walk on `explain`, which is paid once per
//! pair (the caller memoises the composed certificate); keeping the decision
//! compressed is what preserves the checker's performance and its verdicts.
//!
//! # Why edges record the pair their certificate is about
//!
//! Adding the edge `a — b` requires `a` to be a root of the proof forest, so
//! the path from `a` to its root is **reversed** first (the standard proof-
//! forest insertion). Reversing an edge does not reverse the certificate on it:
//! the certificate still concludes about the pair it was built for.
//!
//! So an edge stores that pair outright, rather than a flag saying which way it
//! currently reads. A flag has to be flipped on every reversal, and a flipped
//! flag is a silent lie: a one-hop explain path composes no rule, so the
//! certificate would go back to the caller as a proof of `a ≡ b` when it proves
//! `b ≡ a`, with nothing in between to check it. With the pair recorded,
//! [`UnionFind::hop`] *derives* the orientation by comparing the pair against
//! the direction the path walks, and a link whose certificate is about neither
//! direction yields no hop at all — the caller admits instead of claiming.

use crate::util::{new_fx_index_map, FxIndexMap};
use std::hash::Hash;

#[derive(Debug)]
pub(crate) struct UnionFind<A, C>
where
    A: PartialEq + Eq + Hash, {
    node_map: FxIndexMap<A, UFNode>,
    /// The proof forest, indexed in lockstep with `node_map`. `None` marks a
    /// root.
    proof: Vec<Option<ProofEdge<C>>>,
}

// Because we have `IndexMap`, we can get away with `UFNode` only containing parent and rank.
#[derive(Debug, Clone)]
struct UFNode {
    parent: usize,
    rank: usize,
}

/// The proof-forest edge out of a node: who its proof-parent is, the
/// certificate for the union that created the edge, and which way round that
/// certificate reads.
#[derive(Debug)]
struct ProofEdge<C> {
    parent: usize,
    /// `None` when the union that created this edge was justified by something
    /// the cache does not keep (see `certify::is_unconditional`). The edge still
    /// exists — the *decision* must not change — but a path through it cannot
    /// be explained.
    cert: Option<C>,
    /// The ordered pair `cert` concludes about, as node indices. Fixed when the
    /// edge is created and never touched again, reversals included.
    claim: (usize, usize),
}

/// One edge of an explain path, oriented the way the path walks it.
///
/// `cert` justifies `from ≡ to` when `reversed` is `false`, and `to ≡ from`
/// when it is `true`.
///
/// An edge whose union carried no certificate has no hop: [`UnionFind::explain`]
/// gives up on the whole path rather than skipping a link in it.
pub(crate) struct Hop<A, C> {
    pub(crate) from: A,
    pub(crate) to: A,
    pub(crate) cert: C,
    pub(crate) reversed: bool,
}

impl<A, C> UnionFind<A, C>
where
    A: PartialEq + Eq + Hash + Copy,
{
    pub(crate) fn new() -> Self { UnionFind { node_map: new_fx_index_map(), proof: Vec::new() } }

    pub(crate) fn clear(&mut self) {
        self.node_map.clear();
        self.proof.clear();
    }

    /// If `e` is in the UF data structure already, return
    /// the index it's located at.
    ///
    /// If `e` was not already in the UF data structure,
    /// insert it with a new UFNode and return the index at which
    /// it's located.
    fn get_or_push(&mut self, e: A) -> usize {
        if let Some(idx) = self.node_map.get_index_of(&e) {
            idx
        } else {
            let this_idx = self.node_map.len();
            let new_node = UFNode { parent: this_idx, rank: 0 };
            let (idx, was_new) = self.node_map.insert_full(e, new_node);
            debug_assert_eq!(this_idx, idx);
            debug_assert!(was_new.is_none());
            self.proof.push(None);
            debug_assert_eq!(self.proof.len(), self.node_map.len());
            idx
        }
    }

    /// For an element (a : A) that occupies index `idx`, find and return the root
    /// element of its UF/equivalence class, while also setting this element's parent
    /// to be the root parent (path compression).
    fn find_parent_idx(&mut self, idx: usize) -> usize {
        // Recursively get the parent's parent's parent, etc. until we find the root,
        // which is the element for which `parent_idx == idx`
        let parent_idx = self.node_map.get_index(idx).map(|(_, node)| node.parent).unwrap();
        if parent_idx == idx {
            idx
        } else {
            // compression
            // recurse to find the parent's parent's parent, etc. until we reach the root.
            let root = self.find_parent_idx(parent_idx);
            // Set this element's parent to the now-known root element
            // for this union class.
            match self.node_map.get_index_mut(idx) {
                None => panic!(),
                // Now that we know what the root is, do path compression by setting
                // this element's parent to the root.
                Some((_, ufnode)) => {
                    ufnode.parent = root;
                }
            }
            root
        }
    }

    /// For two root elements that were not previously members of the same equivalence class,
    /// merge them into the same equivalence class by marking either `x_root.parent = y_root`
    /// or vice-versa, while managing `rank` for efficiency.
    fn link_roots(&mut self, x_root: usize, y_root: usize) {
        // This is only called after `find_parent_idx`, so `x` and `y` are the indices
        // of the root elements of their respective equivalence classes. If `x_root` and `y_root`
        // are the same, we don't need to do anything since (1) they're the same already, and (2)
        // `find_parent_idx` performs path compression.
        if x_root != y_root {
            // At this point we know that `x_root` and `y_root` were not yet marked as equivalent/
            // members of the same equivalence class.
            let x_root_rank = self.node_map.get_index(x_root).map(|(_, node)| node.rank).unwrap();
            let y_root_rank = self.node_map.get_index(y_root).map(|(_, node)| node.rank).unwrap();
            if y_root_rank < x_root_rank {
                // if x_root and y_root were not previously marked as equivalent, and y_root has
                // a lower rank, union the equivalence classes by setting y_root's parent to x_root.
                match self.node_map.get_index_mut(y_root) {
                    None => panic!(),
                    Some((_, ufnode)) => {
                        ufnode.parent = x_root;
                    }
                }
            } else {
                // if x_root and y_root were not previously marked as equivalent, and x_root has
                // a lower or equal rank, union the equivalence classes by setting x_root's parent to y_root.
                match self.node_map.get_index_mut(x_root) {
                    None => panic!(),
                    Some((_, ufnode)) => {
                        ufnode.parent = y_root;
                    }
                }
            }
            // If they happen to have the same rank, increment y_root's rank by one.
            if x_root_rank == y_root_rank {
                match self.node_map.get_index_mut(y_root) {
                    None => panic!(),
                    Some((_, ufnode)) => {
                        ufnode.rank += 1;
                    }
                }
            }
        }
    }

    /// Reverse every proof edge on the path from `idx` to its proof-forest root,
    /// leaving `idx` a root.
    ///
    /// This is the one operation that makes a proof forest insertable at an
    /// arbitrary node. Each edge keeps its certificate and flips its
    /// `reversed` flag, because the certificate still concludes about the same
    /// ordered pair — only the direction the path walks it changes.
    fn make_proof_root(&mut self, idx: usize) {
        let mut prev: Option<ProofEdge<C>> = None;
        let mut cur = idx;
        loop {
            let edge = self.proof[cur].take();
            self.proof[cur] = prev;
            match edge {
                None => return,
                Some(ProofEdge { parent, cert, claim }) => {
                    prev = Some(ProofEdge { parent: cur, cert, claim });
                    cur = parent;
                }
            }
        }
    }

    /// update the union-find structure so that `a` and `b` are members of the same
    /// equivalence class, and perform path compression.
    ///
    /// `cert` is the justification for `a ≡ b`, and is recorded on the edge this
    /// creates. When `a` and `b` are *already* in one class the structure gains
    /// nothing and the certificate is dropped: adding a second edge between two
    /// connected nodes would put a cycle in the proof forest.
    pub(crate) fn union(&mut self, a: A, b: A, cert: Option<C>) {
        let (ai, bi) = (self.get_or_push(a), self.get_or_push(b));
        let (a_root, b_root) = (self.find_parent_idx(ai), self.find_parent_idx(bi));
        if a_root == b_root {
            return
        }
        self.make_proof_root(ai);
        self.proof[ai] = Some(ProofEdge { parent: bi, cert, claim: (ai, bi) });
        self.link_roots(a_root, b_root);
    }

    /// Check whether e1 and e2 are known to be equal.
    pub(crate) fn check_uf_eq(&mut self, e1: A, e2: A) -> bool {
        let (e1, e2) = (self.get_or_push(e1), self.get_or_push(e2));
        self.find_parent_idx(e1) == self.find_parent_idx(e2)
    }

    /// The proof-forest path from `idx` up to its root, as node indices.
    fn proof_path(&self, mut idx: usize) -> Vec<usize> {
        let mut out = vec![idx];
        while let Some(e) = &self.proof[idx] {
            idx = e.parent;
            out.push(idx);
        }
        out
    }

    /// The certificates connecting `e1` to `e2`, in order, or `None` if they are
    /// not connected in the proof forest.
    ///
    /// The path goes up from `e1` to the two nodes' lowest common ancestor and
    /// back down to `e2`; the descending half is walked in reverse, so its hops
    /// come back with `reversed` flipped. Certificates are cloned, because the
    /// same edge can serve any number of later explanations — which is the point
    /// of storing them.
    pub(crate) fn explain(&mut self, e1: A, e2: A) -> Option<Vec<Hop<A, C>>>
    where
        C: Clone,
    {
        let (i1, i2) = (self.get_or_push(e1), self.get_or_push(e2));
        let p1 = self.proof_path(i1);
        let p2 = self.proof_path(i2);
        // The lowest common ancestor: the first node of `p1` that also lies on
        // `p2`. Both paths end at the same root when the two are connected.
        let pos2: std::collections::HashMap<usize, usize> =
            p2.iter().enumerate().map(|(k, n)| (*n, k)).collect();
        let (cut1, cut2) = p1.iter().enumerate().find_map(|(k, n)| pos2.get(n).map(|k2| (k, *k2)))?;

        let mut hops = Vec::with_capacity(cut1 + cut2);
        for &n in &p1[..cut1] {
            hops.push(self.hop(n, false)?);
        }
        for &n in p2[..cut2].iter().rev() {
            hops.push(self.hop(n, true)?);
        }
        Some(hops)
    }

    /// The hop out of `n`, walked forwards (`n ⟶ parent`) or backwards
    /// (`parent ⟶ n`).
    fn hop(&self, n: usize, backwards: bool) -> Option<Hop<A, C>>
    where
        C: Clone,
    {
        let edge = self.proof[n].as_ref().expect("a node below the lowest common ancestor has a parent");
        let cert = edge.cert.clone()?;
        let (i, j) = if backwards { (edge.parent, n) } else { (n, edge.parent) };
        // Derived, not remembered: the certificate is about `edge.claim`, and
        // this says whether that is the direction the path takes. A certificate
        // about neither direction is not this edge's, and yields no hop.
        let reversed = match edge.claim {
            c if c == (i, j) => false,
            c if c == (j, i) => true,
            _ => return None,
        };
        let (from, to) = (*self.node_map.get_index(i).unwrap().0, *self.node_map.get_index(j).unwrap().0);
        Some(Hop { from, to, cert, reversed })
    }
}
