// CREDIT: adapted from leanVM's SPHINCS crate (https://github.com/leanEthereum/leanVM, crates/sphincs),
// MIT OR Apache-2.0, see licenses/leanVM-LICENSE-MIT and licenses/leanVM-LICENSE-APACHE.
// Re-parameterized to the leanSphincs candidate (leanSPHINCS.tex): a two-level WOTS forest as the
// few-time signature, WOTS+C with 64 chains of length 4 and target sum 128, and three toggles: the
// lifetime (about 2^24 to 2^32 signatures), the shape (one pruned tree of height 20 to 28, or a
// hypertree of height 24 to 28 whose key builds the top layer only) and the hash (Keccak-256,
// BLAKE2s or SHA-256).

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

/// The master secret of a key.
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
pub const TARGET_SUM: usize = 128;

/// The heights `h` of a pruned key, one per lifetime: the full key lasts about `20 * 2^h` signatures;
/// a pruned key lasts much less (6,926 to 28.35M signatures, formal/sphincs/README.md).
pub const HEIGHTS: [usize; 5] = [20, 22, 24, 26, 28];
/// The layered keys, one per lifetime: `(log2 lifetime, h, forest coordinates)`. The lifetimes
/// `2^24` and `2^26` share the height 24 with `2^28` and use a lighter forest.
pub const UNIFORM: [(usize, usize, usize); 5] = [(24, 24, 6), (26, 24, 7), (28, 24, 8), (30, 26, 8), (32, 28, 8)];
/// The tallest height: the digest's index field and the address fields are sized for it.
pub const MAX_H: usize = 28;
/// The kept subtree heights `b` of a pruned key besides the full key `b = h`: those whose
/// lifetime is proved in Lean (`PRUNED` in scripts/scheme.py); `b = 20` at `h = 20` is the full key.
pub const PRUNED: [usize; 6] = [8, 10, 12, 13, 14, 20];

/// The layer heights of a layered key of height `h`, top layer first: three layers, three equal layers of 8
/// at `h = 24` (about 10 s of key generation on a Ledger with Keccak-256), else a top layer of 10 (about 41 s)
/// and two equal bottom layers of 8 or 9.
pub fn layered_heights(h: usize) -> &'static [usize] {
    match h {
        24 => &[8, 8, 8],
        26 => &[10, 8, 8],
        28 => &[10, 9, 9],
        _ => panic!("no layered split for h = {h}"),
    }
}

/// The few-time signature, a two-level WOTS forest: independent coordinates (`COORDS`, or fewer for
/// the layered keys of the lifetimes `2^24` and `2^26`, [`UNIFORM`]), each a top tree of height
/// `TOP_HEIGHT` over super-children, each of those over `SUBS` sub-trees of height `SUB_HEIGHT`, whose
/// children are WOTS keys of `CHILD_CHAINS` chains of `CHAIN_TOP` steps, signed at a codeword of digit
/// sum `CODEWORD_SUM`.
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
/// Bytes of the forest opening of `coords` coordinates.
pub const fn forest_size(coords: usize) -> usize {
    coords * VALUES_PER_COORD * N
}
/// Bytes of the forest opening with `COORDS` coordinates.
pub const FOREST_SIZE: usize = forest_size(COORDS);
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

/// One of the configurations: a hash, a height, a shape and the forest's number of coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Config {
    hash: HashFn,
    h: usize,
    shape: Shape,
    coords: usize,
}

impl Config {
    /// A key with the `COORDS`-coordinate forest. Panics unless a pruned key has `h` in [`HEIGHTS`]
    /// and keeps `b = h` or `b` in [`PRUNED`], and a layered key has `h` = 24, 26 or 28.
    pub fn new(hash: HashFn, h: usize, shape: Shape) -> Self {
        match shape {
            Shape::Pruned { b } => {
                assert!(HEIGHTS.contains(&h), "h = {h}");
                assert!(b == h || PRUNED.contains(&b), "b = {b}");
            }
            Shape::Layered => assert!(UNIFORM.iter().any(|&(_, hh, c)| hh == h && c == COORDS), "h = {h}"),
        }
        Self { hash, h, shape, coords: COORDS }
    }

    /// The pruned key of lifetime about `2^log2_lifetime` (`h = log2_lifetime - 4`) keeping `2^b` leaves.
    pub fn pruned(hash: HashFn, log2_lifetime: usize, b: usize) -> Self {
        Self::new(hash, log2_lifetime.checked_sub(4).expect("lifetime"), Shape::Pruned { b })
    }

    /// The layered key of lifetime about `2^log2_lifetime` ([`UNIFORM`]): `2^24` and `2^26` have
    /// height 24 and a forest of 6 and 7 coordinates.
    pub fn uniform(hash: HashFn, log2_lifetime: usize) -> Self {
        let &(_, h, coords) = UNIFORM.iter().find(|u| u.0 == log2_lifetime).expect("lifetime");
        Self { hash, h, shape: Shape::Layered, coords }
    }

    /// The forest's number of coordinates.
    pub fn coords(&self) -> usize {
        self.coords
    }

    pub fn hash(&self) -> HashFn {
        self.hash
    }

    pub fn h(&self) -> usize {
        self.h
    }

    pub fn shape(&self) -> Shape {
        self.shape
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
        RANDOMIZER_LEN + forest_size(self.coords) + self.layers().len() * LAYER_SIZE + self.h * N
    }

    /// Compressions of one verification of an accepted signature: the cached block of `P`
    /// (SHA-256), the digest, the forest, and per layer the encoding, the chain steps that complete
    /// the 128 signed positions, the one-time leaf and the path.
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
                let message = if layer == 0 { self.coords * 2 * N } else { N };
                c(message + COUNTER_LEN)
                    + (V * (CHAIN_LEN - 1) - TARGET_SUM) as u64 * c(N)
                    + c(V * N)
                    + height as u64 * c(2 * N)
            })
            .sum();
        pp + digest + self.coords as u64 * coord + layers
    }
}

/// The digest bits: the codeword indices, then the children, the super-children and the index.
pub const fn digest_bits(h: usize, coords: usize) -> usize {
    h + coords * COORD_BITS
}

/// The baseline: Keccak-256, one tree of height 24, a full key.
pub const BASELINE_SIG_SIZE: usize = 4244;
/// Permutations of one baseline verification: digest 1, forest 8 * 20, encoding 3 (the 16 forest
/// nodes and the counter), chains 192 - 128, leaf 8, path 24.
pub const BASELINE_VERIFY_PERMUTATIONS: u64 = 260;

const _: () = assert!(W * V == 8 * N);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(RANDOMIZER_LEN + FOREST_SIZE + LAYER_SIZE + 24 * N == BASELINE_SIG_SIZE);
const _: () = assert!(digest_bits(24, COORDS) == 232 && digest_bits(MAX_H, COORDS) <= 8 * 32);
const _: () = assert!(PUB_KEY_SIZE == 32);
const _: () = assert!(PRUNED[PRUNED.len() - 1] <= HEIGHTS[0]);   // b = 20 at h = 20 is the full key
