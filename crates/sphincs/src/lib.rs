// CREDIT: adapted from leanVM's SPHINCS crate (https://github.com/leanEthereum/leanVM, crates/sphincs),
// MIT OR Apache-2.0, see licenses/leanVM-LICENSE-MIT and licenses/leanVM-LICENSE-APACHE.
// Re-parameterized to the leanSphincs candidate (leansphincs.tex): one XMSS layer (d = 1) of height
// h = 26, plain FORS with k = 24 trees of height a = 10, WOTS+C with w = 4, 64 chains and target sum
// 120, and pruned keys (a kept subtree plus pseudorandom surrogate siblings).

//! The leanSphincs candidate over BLAKE2s.
//!
//! `Th(P, tw, M) = BLAKE2s(tw | P | M)` truncated to `n = 16` bytes. Every hash call goes through
//! [`hash`], which also counts BLAKE2s compressions (thread-local) so tests can check the note's costs.

mod hash;
pub use hash::*;
mod wots;
pub use wots::*;
mod fors;
pub use fors::*;
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
pub const TARGET_SUM: usize = 120;

/// XMSS height (one layer).
pub const H: usize = 26;
/// FORS tree height and number of trees.
pub const A: usize = 10;
pub const K: usize = 24;

pub const MAX_ENCODING_ATTEMPTS: u64 = 1 << 32;

/// The digest bits: the leaf index, then the `k` FORS indices.
pub const DIGEST_BITS: usize = H + K * A;

pub const PUB_KEY_SIZE: usize = N + PUBLIC_PARAM_LEN;
pub const SIG_SIZE: usize = RANDOMIZER_LEN + K * (1 + A) * N + COUNTER_LEN + V * N + H * N;
/// Compressions of one verification: digest 4, FORS 24 * 11 + 7, encoding 1, chains 192 - 120, leaf 17, path 26.
pub const VERIFY_COMPRESSIONS: u64 = 391;

const _: () = assert!(W * V == 8 * N);
const _: () = assert!(TARGET_SUM < V * (CHAIN_LEN - 1));
const _: () = assert!(SIG_SIZE == 5684);
const _: () = assert!(DIGEST_BITS <= 512);
