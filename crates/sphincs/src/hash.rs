//! `Th`, the address that names every hash call, and the compression counter.

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
pub const TWEAK_FTS_ROOTS: u8 = 11;
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
/// endian. With `P` they fill half a block, so every value of a payload starts on a 16-byte boundary.
pub fn address(tw: &Tweak) -> [u8; ADDRESS_LEN] {
    let mut out = [0u8; ADDRESS_LEN];
    out[..4].copy_from_slice(&tw.lo.to_le_bytes());
    out[4..7].copy_from_slice(&tw.hi.to_le_bytes()[..3]);
    out[7] = tw.t | tw.step << 5;
    out
}

/// A hasher that has absorbed `P | address`.
fn start(pp: &PublicParam, tw: &Tweak) -> blake2s::Hasher {
    let mut hasher = blake2s::Hasher::new();
    hasher.update(pp).update(&address(tw));
    hasher
}

thread_local! {
    static COMPRESSIONS: Cell<u64> = const { Cell::new(0) };
}

/// BLAKE2s compressions this thread has spent in [`th`], [`th_digests`] and [`Midstate`].
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

fn count_blocks(n: u64) {
    COMPRESSIONS.with(|c| c.set(c.get() + n));
}

/// `Th(P, tw, payload)`: BLAKE2s of `P | address | payload`, truncated.
pub fn th(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Digest {
    count(PUBLIC_PARAM_LEN + ADDRESS_LEN + payload.len());
    let mut hasher = start(pp, tw);
    hasher.update(payload);
    hasher.finalize()[..N].try_into().unwrap()
}

/// Two secrets for one hash: the two 16-byte halves of the untruncated BLAKE2s of `P | address | payload`.
pub fn th_pair(pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> [Digest; 2] {
    count(PUBLIC_PARAM_LEN + ADDRESS_LEN + payload.len());
    let mut hasher = start(pp, tw);
    hasher.update(payload);
    let out = hasher.finalize();
    [out[..N].try_into().unwrap(), out[N..].try_into().unwrap()]
}

/// `Th` over a concatenation of digests: a Merkle node, a one-time leaf, or the FORS roots.
pub fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    count(PUBLIC_PARAM_LEN + ADDRESS_LEN + values.len() * N);
    let mut hasher = start(pp, tw);
    for value in values {
        hasher.update(value);
    }
    hasher.finalize()[..N].try_into().unwrap()
}

/// The hash state after the whole blocks of `P | address | fixed`, for inputs that differ only in
/// what follows. What follows is never empty, so every whole block of the fixed part is compressed
/// here, once, and each [`Midstate::finish`] pays for the rest.
#[derive(Clone)]
pub struct Midstate {
    /// The chaining value after `absorbed` bytes.
    state: [u32; 8],
    absorbed: usize,
    /// The end of the fixed part, less than a block.
    rest: Vec<u8>,
}

impl Midstate {
    pub fn new(pp: &PublicParam, tw: &Tweak, fixed: &[&[u8]]) -> Self {
        let mut input = [&pp[..], &address(tw)].concat();
        for part in fixed {
            input.extend_from_slice(part);
        }
        let (whole, rest) = input.as_chunks::<64>();
        let mut state = blake2s::PARAM_IV;
        for (b, block) in whole.iter().enumerate() {
            let words = std::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
            blake2s::compress(&mut state, &words, (64 * (b + 1)) as u64, false);
        }
        count_blocks(whole.len() as u64);
        Self { state, absorbed: 64 * whole.len(), rest: rest.to_vec() }
    }

    /// The untruncated 32-byte BLAKE2s of the input completed by `tail`, which is not empty.
    pub fn finish(&self, tail: &[u8]) -> [u8; 32] {
        let len = self.rest.len() + tail.len();
        let mut data = [0u8; 128];
        assert!(!tail.is_empty() && len <= data.len());
        data[..self.rest.len()].copy_from_slice(&self.rest);
        data[self.rest.len()..len].copy_from_slice(tail);
        count(len);
        blake2s::hash_from_state_final(&data[..len.div_ceil(64) * 64], &self.state, self.absorbed as u64, len)
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
        assert_eq!(th(&pp, &tw, &payload)[..], blake2s::hash(&input)[..N]);
    }

    /// A midstate gives the same hash as one pass, and pays for each block once, whether or not the
    /// fixed part ends on a block boundary.
    #[test]
    fn midstate_matches_one_pass() {
        let pp: PublicParam = std::array::from_fn(|i| 3 * i as u8);
        let tw = tweak(TWEAK_MSG, 1, 0);
        for fixed_len in [32, 40] {
            let (fixed, tail) = (vec![7u8; fixed_len], [9u8; 16]);
            let input = [&pp[..], &address(&tw), &fixed, &tail].concat();
            let before = compressions();
            let state = Midstate::new(&pp, &tw, &[&fixed]);
            assert_eq!(compressions() - before, 1, "the first block");
            for _ in 0..3 {
                let before = compressions();
                assert_eq!(state.finish(&tail), blake2s::hash(&input));
                assert_eq!(compressions() - before, 1, "one compression per tail");
            }
        }
    }
}
