//! `Th`, the tweaks that name every hash call, and the compression counter.

use std::cell::Cell;

use crate::*;

pub const TWEAK_LEN: usize = 16;
pub type Tweak = [u8; TWEAK_LEN];

pub const PROTOCOL_DOMAIN_SEP: u8 = 1;

// Tweak types (byte 1).
pub const TWEAK_PRF: u8 = 0;
pub const TWEAK_CHAIN: u8 = 1;
pub const TWEAK_LEAF: u8 = 2;
pub const TWEAK_NODE: u8 = 3;
pub const TWEAK_ENC: u8 = 4;
pub const TWEAK_PARAMETER: u8 = 5;
pub const TWEAK_RANDOMIZER: u8 = 7;
pub const TWEAK_FTS_PRF: u8 = 8;
pub const TWEAK_FTS_LEAF: u8 = 9;
pub const TWEAK_FTS_NODE: u8 = 10;
pub const TWEAK_FTS_ROOTS: u8 = 11;
pub const TWEAK_MSG: u8 = 12;
/// A pruned key's surrogate siblings (the kept subtree's position comes from the low bits of `P`).
pub const TWEAK_SURROGATE: u8 = 13;

/// `[protocol_domain_sep:1 | type:1 | layer:1 | zero:1 | p:4 | tree:4 | index:4]`, little endian.
pub fn tweak(t: u8, lay: usize, tau: u32, p: u32, j: u32) -> Tweak {
    debug_assert!(lay < 256);
    let mut tw = [0u8; TWEAK_LEN];
    tw[0] = PROTOCOL_DOMAIN_SEP;
    tw[1] = t;
    tw[2] = lay as u8;
    tw[4..8].copy_from_slice(&p.to_le_bytes());
    tw[8..12].copy_from_slice(&tau.to_le_bytes());
    tw[12..16].copy_from_slice(&j.to_le_bytes());
    tw
}

thread_local! {
    static COMPRESSIONS: Cell<u64> = const { Cell::new(0) };
}

/// BLAKE2s compressions this thread has spent in [`th`], [`th_digests`] and [`hash_full`].
pub fn compressions() -> u64 {
    COMPRESSIONS.with(Cell::get)
}

/// Compressions BLAKE2s spends on `len` bytes.
pub const fn blocks(len: usize) -> u64 {
    if len == 0 { 1 } else { len.div_ceil(64) as u64 }
}

fn count(len: usize) {
    COMPRESSIONS.with(|c| c.set(c.get() + blocks(len)));
}

/// `Th(P, tw, payload)`.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    count(TWEAK_LEN + PUBLIC_PARAM_LEN + payload.len());
    let mut hasher = blake2s::Hasher::new();
    hasher.update(tw).update(pp).update(payload);
    hasher.finalize()[..N].try_into().unwrap()
}

/// `Th` over a concatenation of digests: a Merkle node, a one-time leaf, or the FORS roots.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    count(TWEAK_LEN + PUBLIC_PARAM_LEN + values.len() * N);
    let mut hasher = blake2s::Hasher::new();
    hasher.update(tw).update(pp);
    for value in values {
        hasher.update(value);
    }
    hasher.finalize()[..N].try_into().unwrap()
}

/// The untruncated 32-byte BLAKE2s of `tw | P | parts`, for the message digest.
pub fn hash_full(pp: &PublicParam, tw: &Tweak, parts: &[&[u8]]) -> [u8; 32] {
    count(TWEAK_LEN + PUBLIC_PARAM_LEN + parts.iter().map(|p| p.len()).sum::<usize>());
    let mut hasher = blake2s::Hasher::new();
    hasher.update(tw).update(pp);
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize()
}
