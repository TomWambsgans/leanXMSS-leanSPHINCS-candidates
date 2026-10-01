//! FORS: `k = 24` Merkle trees of `2^a = 1024` secret leaves; the digest opens one leaf per tree.

use crate::*;

pub const FORS_LEAVES: usize = 1 << A;

/// What a signature carries for FORS: the opened secret and the Merkle path of each tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForsOpening {
    pub secrets: [Digest; K],
    pub paths: [[Digest; A]; K],
}

pub fn fors_secret_tweak(idx: u64, kappa: usize, j: usize) -> Tweak {
    tweak(TWEAK_FTS_PRF, kappa, idx as u32, 0, j as u32)
}

/// `s_{idx,kappa,j} = Th(P, tw_ftsprf(idx, kappa, j), S)`.
pub fn fors_secret(pp: &PublicParam, master: &MasterSecret, idx: u64, kappa: usize, j: usize) -> Digest {
    th(pp, &fors_secret_tweak(idx, kappa, j), master)
}

pub fn fors_leaf_tweak(idx: u64, kappa: usize, j: usize) -> Tweak {
    tweak(TWEAK_FTS_LEAF, kappa, idx as u32, 0, j as u32)
}

pub fn fors_leaf(pp: &PublicParam, idx: u64, kappa: usize, j: usize, secret: &Digest) -> Digest {
    th(pp, &fors_leaf_tweak(idx, kappa, j), secret)
}

fn fors_node(pp: &PublicParam, idx: u64, kappa: usize, level: usize, j: usize, left: &Digest, right: &Digest) -> Digest {
    th_digests(pp, &tweak(TWEAK_FTS_NODE, kappa, idx as u32, level as u32, j as u32), &[*left, *right])
}

/// The FORS public key: `Th` over the `k` roots.
pub fn fors_key_of_roots(pp: &PublicParam, idx: u64, roots: &[Digest; K]) -> Digest {
    th_digests(pp, &tweak(TWEAK_FTS_ROOTS, 0, idx as u32, 0, 0), roots)
}

/// A FORS instance whose leaves are known: every tree level, kept for the openings.
pub struct ForsForest {
    /// `levels[kappa][level][j]`, level 0 being the leaves.
    levels: Vec<Vec<Vec<Digest>>>,
    pub key: Digest,
}

impl ForsForest {
    /// Builds the forest of instance `idx` from its `k * 2^a` leaves, tree by tree.
    pub fn from_leaves(pp: &PublicParam, idx: u64, leaves: &[Digest]) -> Self {
        assert_eq!(leaves.len(), K * FORS_LEAVES);
        let levels: Vec<Vec<Vec<Digest>>> = (0..K)
            .map(|kappa| {
                let mut tree = vec![leaves[kappa * FORS_LEAVES..(kappa + 1) * FORS_LEAVES].to_vec()];
                for level in 1..=A {
                    let below = &tree[level - 1];
                    let up = (0..below.len() / 2)
                        .map(|j| fors_node(pp, idx, kappa, level, j, &below[2 * j], &below[2 * j + 1]))
                        .collect();
                    tree.push(up);
                }
                tree
            })
            .collect();
        let roots = std::array::from_fn(|kappa| levels[kappa][A][0]);
        Self { key: fors_key_of_roots(pp, idx, &roots), levels }
    }

    pub fn leaf(&self, kappa: usize, j: usize) -> Digest {
        self.levels[kappa][0][j]
    }

    /// The Merkle path of leaf `u[kappa]` in every tree.
    pub fn paths(&self, u: &[u32; K]) -> [[Digest; A]; K] {
        std::array::from_fn(|kappa| {
            std::array::from_fn(|level| self.levels[kappa][level][(u[kappa] as usize >> level) ^ 1])
        })
    }
}

/// The FORS leaves of instance `idx` from the master secret, tree after tree.
pub fn fors_leaves(pp: &PublicParam, master: &MasterSecret, idx: u64) -> Vec<Digest> {
    (0..K * FORS_LEAVES)
        .map(|t| {
            let (kappa, j) = (t / FORS_LEAVES, t % FORS_LEAVES);
            fors_leaf(pp, idx, kappa, j, &fors_secret(pp, master, idx, kappa, j))
        })
        .collect()
}

/// `Fts.recover`: the FORS key an opening reaches.
pub fn fors_recover(pp: &PublicParam, idx: u64, u: &[u32; K], opening: &ForsOpening) -> Digest {
    let roots = std::array::from_fn(|kappa| {
        let opened = u[kappa] as usize;
        let leaf = fors_leaf(pp, idx, kappa, opened, &opening.secrets[kappa]);
        (0..A).fold(leaf, |node, level| {
            let sibling = &opening.paths[kappa][level];
            let (left, right) = if (opened >> level) & 1 == 0 { (node, *sibling) } else { (*sibling, node) };
            fors_node(pp, idx, kappa, level + 1, opened >> (level + 1), &left, &right)
        })
    });
    fors_key_of_roots(pp, idx, &roots)
}
