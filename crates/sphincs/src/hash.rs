//! `Th`, the address that names every hash call, and the permutation counter.

use std::cell::Cell;

use crate::*;

pub const ADDRESS_LEN: usize = 16;

// Hash types (low five bits of the last byte of the address).
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
pub const TWEAK_FTS_KEY: u8 = 11;
pub const TWEAK_MSG: u8 = 12;
/// A pruned key's surrogate siblings (the kept subtree's position comes from the low bits of `P`).
pub const TWEAK_SURROGATE: u8 = 13;

/// The address of a hash call: its type, a chain step, and two fields, `hi < 2^24` and `lo`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Tweak {
    t: u8,
    step: u8,
    hi: u32,
    lo: u32,
}

pub fn tweak(t: u8, hi: u32, lo: u32) -> Tweak {
    debug_assert!(t < 32 && hi < 1 << 24);
    Tweak { t, step: 0, hi, lo }
}

impl Tweak {
    /// The same address at chain step `step < 8`.
    pub fn step(self, step: usize) -> Self {
        debug_assert!(step < 8);
        Self { step: step as u8, ..self }
    }
}

/// The 16 bytes that follow `P` in a hash input: `[lo:4 | hi:3 | t + 32 step:1 | 0^8]`, the fields little
/// endian. With `P` they fill 32 bytes, so every value of a payload starts on a 16-byte boundary of the input.
pub fn address(tw: &Tweak) -> [u8; ADDRESS_LEN] {
    let mut out = [0u8; ADDRESS_LEN];
    out[..4].copy_from_slice(&tw.lo.to_le_bytes());
    out[4..7].copy_from_slice(&tw.hi.to_le_bytes()[..3]);
    out[7] = tw.t | tw.step << 5;
    out
}

/// A hasher that has absorbed `P | address`.
fn start(pp: &PublicParam, tw: &Tweak) -> sha3::Hasher {
    let mut hasher = sha3::Hasher::new();
    hasher.update(pp).update(&address(tw));
    hasher
}

thread_local! {
    static PERMUTATIONS: Cell<u64> = const { Cell::new(0) };
}

/// Keccak-f permutations this thread has spent in [`th`], [`th_pair`], [`th_digests`] and [`Midstate`].
pub fn permutations() -> u64 {
    PERMUTATIONS.with(Cell::get)
}

/// Permutations SHA3-256 spends on `len` bytes: `len / 136 + 1`.
pub const fn blocks(len: usize) -> u64 {
    sha3::permutations(len)
}

fn count(len: usize) {
    count_blocks(blocks(len));
}

fn count_blocks(n: u64) {
    PERMUTATIONS.with(|c| c.set(c.get() + n));
}

/// `Th(P, tw, payload)`: SHA3-256 of `P | address | payload`, truncated.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    count(PUBLIC_PARAM_LEN + ADDRESS_LEN + payload.len());
    let mut hasher = start(pp, tw);
    hasher.update(payload);
    hasher.finalize()[..N].try_into().unwrap()
}

/// Two secrets for one hash: the two 16-byte halves of the untruncated SHA3-256 of `P | address | payload`.
pub fn th_pair(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> [Digest; 2] {
    count(PUBLIC_PARAM_LEN + ADDRESS_LEN + payload.len());
    let mut hasher = start(pp, tw);
    hasher.update(payload);
    let out = hasher.finalize();
    [out[..N].try_into().unwrap(), out[N..].try_into().unwrap()]
}

/// `Th` over a concatenation of digests: a Merkle node, a one-time leaf, or the FORS key (the two top nodes of every tree).
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    count(PUBLIC_PARAM_LEN + ADDRESS_LEN + values.len() * N);
    let mut hasher = start(pp, tw);
    for value in values {
        hasher.update(value);
    }
    hasher.finalize()[..N].try_into().unwrap()
}

/// The sponge state after the whole blocks of `P | address | fixed`, for inputs that differ only in
/// what follows. Every whole block of the fixed part is permuted here, once, and each
/// [`Midstate::finish`] pays for the rest and the padding.
#[derive(Clone)]
pub struct Midstate {
    hasher: sha3::Hasher,
    /// The end of the fixed part that is not a whole block, in bytes.
    rest: usize,
}

impl Midstate {
    pub fn new(pp: &PublicParam, tw: &Tweak, fixed: &[&[u8]]) -> Self {
        let mut hasher = start(pp, tw);
        let mut len = PUBLIC_PARAM_LEN + ADDRESS_LEN;
        for part in fixed {
            hasher.update(part);
            len += part.len();
        }
        count_blocks((len / sha3::RATE) as u64);
        Self { hasher, rest: len % sha3::RATE }
    }

    /// The untruncated 32-byte SHA3-256 of the input completed by `tail`.
    pub fn finish(&self, tail: &[u8]) -> [u8; 32] {
        count(self.rest + tail.len());
        let mut hasher = self.hasher.clone();
        hasher.update(tail);
        hasher.finalize()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pins the byte layout of the address and of a hash input.
    #[test]
    fn address_layout() {
        let tw = tweak(TWEAK_FTS_NODE, 0x123456, 0x89abcdef).step(5);
        assert_eq!(address(&tw), [0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xaa, 0, 0, 0, 0, 0, 0, 0, 0]);
        let pp: PublicParam = std::array::from_fn(|i| i as u8 + 1);
        let payload = [9u8; N];
        let mut input = pp.to_vec();
        input.extend_from_slice(&address(&tw));
        input.extend_from_slice(&payload);
        assert_eq!(th(&pp, &tw, &payload)[..], sha3::hash(&input)[..N]);
    }

    /// A midstate gives the same hash as one pass, and pays for each whole block once, whether or
    /// not the fixed part ends on a block boundary.
    #[test]
    fn midstate_matches_one_pass() {
        let pp: PublicParam = std::array::from_fn(|i| 3 * i as u8);
        let tw = tweak(TWEAK_MSG, 1, 0);
        for fixed_len in [104, 120] {
            let (fixed, tail) = (vec![7u8; fixed_len], [9u8; 16]);
            let input = [&pp[..], &address(&tw), &fixed, &tail].concat();
            let before = permutations();
            let state = Midstate::new(&pp, &tw, &[&fixed]);
            assert_eq!(permutations() - before, 1, "the first block");
            for _ in 0..3 {
                let before = permutations();
                assert_eq!(state.finish(&tail), sha3::hash(&input));
                assert_eq!(permutations() - before, 1, "one permutation per tail");
            }
        }
    }
}
