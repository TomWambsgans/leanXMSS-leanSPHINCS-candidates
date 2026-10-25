// CREDIT: adapted from leanVM's SPHINCS crate (https://github.com/leanEthereum/leanVM, crates/sphincs),
// MIT OR Apache-2.0, see licenses/leanVM-LICENSE-MIT and licenses/leanVM-LICENSE-APACHE.
// Re-parameterized to the leanSphincs candidate (leanSPHINCS.tex): a two-level WOTS forest as the
// few-time signature, WOTS+C with w = 4, 64 chains and target sum 123, and three toggles: the
// height (22, 24, 26 or 28), the shape (one pruned tree, or a hypertree whose key builds the top
// layer only) and the hash (Keccak-256, BLAKE2s or SHA-256).

//! The leanSphincs candidate.
//!
//! `Th(P, tw, M)` is the hash of `P | tw | M` truncated to `n = 16` bytes, with a 16-byte address
//! `tw`; each hash has its own layout ([`hash`]). Every hash call goes through [`hash`], which also
//! counts compressions (thread-local) so tests can check the note's costs.

mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod forest;
pub use forest::*;
mod scheme;
pub use scheme::*;

/// `n`: hash value and Merkle node length, in bytes.
pub const N: usize = 16;
pub type Digest = [u8; N];

pub const PUBLIC_PARAM_LEN: usize = 16;
pub type PublicParam = [u8; PUBLIC_PARAM_LEN];

/// The master secret of a (non-threshold) key.
pub const MASTER_SECRET_LEN: usize = 32;
pub type MasterSecret = [u8; MASTER_SECRET_LEN];

pub const RANDOMIZER_LEN: usize = 16;
pub type Randomizer = [u8; RANDOMIZER_LEN];

pub const MESSAGE_LEN: usize = 32;
pub type Message = [u8; MESSAGE_LEN];

pub const COUNTER_LEN: usize = 4;

/// Bits per WOTS chunk: chains of `2^W = 4` positions, i.e. 3 hash steps.
pub const W: usize = 2;
pub const CHAIN_LEN: usize = 1 << W;
/// Number of WOTS chains.
pub const V: usize = 64;
/// WOTS+C target sum of the signed positions.
pub const TARGET_SUM: usize = 123;

/// The tree heights `h`, one per lifetime: about `2^(h + 4)` signatures.
pub const HEIGHTS: [usize; 4] = [22, 24, 26, 28];
/// The tallest height: the digest's index field and the address fields are sized for it.
pub const MAX_H: usize = 28;

/// The layer heights of a layered key of height `h`, top layer first: three layers, a top layer of at
/// most 12 and two equal bottom layers of at least 6.
pub fn layered_heights(h: usize) -> &'static [usize] {
    match h {
        22 => &[10, 6, 6],
        24 => &[12, 6, 6],
        26 => &[12, 7, 7],
        28 => &[12, 8, 8],
        _ => panic!("no layered split for h = {h}"),
    }
}

/// The few-time signature, a two-level WOTS forest: `COORDS` independent coordinates, each a top
/// tree of height `TOP_HEIGHT` over super-children, each of those over `SUBS` sub-trees of height
/// `SUB_HEIGHT`, whose children are WOTS keys of `CHILD_CHAINS` chains of `CHAIN_TOP` steps, signed
/// at a codeword of digit sum `CODEWORD_SUM`.
pub const COORDS: usize = 8;
pub const TOP_HEIGHT: usize = 4;
pub const SUBS: usize = 2;
pub const SUB_HEIGHT: usize = 3;
pub const CHILD_CHAINS: usize = 6;
pub const CHAIN_TOP: usize = 4;
pub const CODEWORD_SUM: usize = 5;

/// Digest bits of one coordinate: the super-child, then a child and a codeword index per sub-tree.
pub const COORD_BITS: usize = TOP_HEIGHT + SUBS * (SUB_HEIGHT + 8);

pub const MAX_ENCODING_ATTEMPTS: u64 = 1 << 32;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
/// Bytes of the forest opening.
pub const FOREST_SIZE: usize = COORDS * VALUES_PER_COORD * N;
/// Bytes a tree layer adds besides its path: the WOTS+C counter and the 64 chain values.
pub const LAYER_SIZE: usize = COUNTER_LEN + V * N;

/// The shape of a key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// One tree of height `h`; the key builds a kept subtree of `2^b` leaves (`b = h` is the full
    /// key) and the signer grinds its randomizer into it.
    Pruned { b: usize },
    /// A hypertree split by [`layered_heights`]; the key builds the top layer only, the signer
    /// the lower trees on the way, and no randomizer is ground.
    Layered,
}

/// One of the configurations: a hash, a height and a shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Config {
    pub hash: HashFn,
    pub h: usize,
    pub shape: Shape,
}

impl Config {
    pub fn new(hash: HashFn, h: usize, shape: Shape) -> Self {
        assert!(HEIGHTS.contains(&h), "h = {h}");
        if let Shape::Pruned { b } = shape {
            assert!(b <= h);
        }
        Self { hash, h, shape }
    }

    /// The layer heights, bottom layer first; one layer for a pruned key.
    pub fn layers(&self) -> Vec<usize> {
        match self.shape {
            Shape::Pruned { .. } => vec![self.h],
            Shape::Layered => layered_heights(self.h).iter().rev().copied().collect(),
        }
    }

    /// Bits of the index below layer `layer` (counted from the bottom).
    pub fn below(&self, layer: usize) -> usize {
        self.layers()[..layer].iter().sum()
    }

    /// Height of the kept subtree of the top layer.
    pub fn kept(&self) -> usize {
        match self.shape {
            Shape::Pruned { b } => b,
            Shape::Layered => layered_heights(self.h)[0],
        }
    }

    /// Bytes of a signature: the randomizer, the forest, then per layer the counter, the chain values
    /// and the path.
    pub fn sig_size(&self) -> usize {
        RANDOMIZER_LEN + FOREST_SIZE + self.layers().len() * LAYER_SIZE + self.h * N
    }

    /// Compressions of one verification of an accepted signature: the cached block of `P`
    /// (SHA-256), the digest, the forest, and per layer the encoding, the chain steps that complete
    /// the 123 signed positions, the one-time leaf and the path.
    pub fn verify_compressions(&self) -> u64 {
        let c = |payload: usize| self.hash.call(payload);
        let pp = (self.hash == HashFn::Sha256) as u64;
        let digest = c(MESSAGE_LEN + self.hash.digest_pad() + RANDOMIZER_LEN);
        let sub = CODEWORD_SUM as u64 * c(N) + c(CHILD_CHAINS * N) + (SUB_HEIGHT as u64 - 1) * c(2 * N);
        let coord = SUBS as u64 * sub + c(SUBS * 2 * N) + (TOP_HEIGHT as u64 - 1) * c(2 * N);
        let layers: u64 = self
            .layers()
            .iter()
            .enumerate()
            .map(|(layer, &height)| {
                let message = if layer == 0 { COORDS * 2 * N } else { N };
                c(message + COUNTER_LEN)
                    + (V * (CHAIN_LEN - 1) - TARGET_SUM) as u64 * c(N)
                    + c(V * N)
                    + height as u64 * c(2 * N)
            })
            .sum();
        pp + digest + COORDS as u64 * coord + layers
    }
}

/// The digest bits: the 16 codeword indices, then the children, the super-children and the index.
pub const fn digest_bits(h: usize) -> usize {
    h + COORDS * COORD_BITS
}

/// The baseline: Keccak-256, one tree of height 24, a full key.
pub const BASELINE_SIG_SIZE: usize = 4244;
/// Permutations of one baseline verification: digest 1, forest 8 * 20, encoding 3 (the 16 forest
/// nodes and the counter), chains 192 - 123, leaf 8, path 24.
pub const BASELINE_VERIFY_PERMUTATIONS: u64 = 265;

const _: () = assert!(W * V == 8 * N);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(RANDOMIZER_LEN + FOREST_SIZE + LAYER_SIZE + 24 * N == BASELINE_SIG_SIZE);
const _: () = assert!(digest_bits(24) == 232 && digest_bits(MAX_H) <= 8 * 32);
const _: () = assert!(PUB_KEY_SIZE == 32);
