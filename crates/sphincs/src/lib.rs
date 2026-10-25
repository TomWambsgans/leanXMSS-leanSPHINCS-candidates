// CREDIT: adapted from leanVM's SPHINCS crate (https://github.com/leanEthereum/leanVM, crates/sphincs),
// MIT OR Apache-2.0, see licenses/leanVM-LICENSE-MIT and licenses/leanVM-LICENSE-APACHE.
// Re-parameterized to the leanSphincs candidate (leanSPHINCS.tex): one XMSS layer (d = 1) of height
// h = 24, a two-level WOTS forest as the few-time signature, WOTS+C with w = 4, 64 chains and target
// sum 123, and pruned keys (a kept subtree plus pseudorandom surrogate siblings).

//! The leanSphincs candidate over Keccak-256.
//!
//! `Th(P, tw, M) = Keccak-256(P | tw | M)` truncated to `n = 16` bytes, with a 16-byte address `tw` (8 bytes of fields, 8 zero bytes).
//! Every hash call goes through [`hash`], which also counts Keccak-f permutations (thread-local) so
//! tests can check the note's costs.

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

/// XMSS height (one layer).
pub const H: usize = 24;

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

/// The digest bits: the 16 codeword indices, then the leaf index and the tree fields.
pub const DIGEST_BITS: usize = H + COORDS * COORD_BITS;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
pub const SIG_SIZE: usize =
    RANDOMIZER_LEN + COORDS * VALUES_PER_COORD * N + COUNTER_LEN + V * N + H * N;
/// Permutations of one verification: digest 1, forest 8 * 20, encoding 3 (the 16 forest nodes and
/// the counter), chains 192 - 123, leaf 8, path 24.
pub const VERIFY_PERMUTATIONS: u64 = 265;

const _: () = assert!(W * V == 8 * N);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(SIG_SIZE == 4244);
const _: () = assert!(DIGEST_BITS == 232 && DIGEST_BITS <= 8 * 32);
const _: () = assert!(PUB_KEY_SIZE == 32);
const _: () = assert!(DIGEST_BITS <= 512);
