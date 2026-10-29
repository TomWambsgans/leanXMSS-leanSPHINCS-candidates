//! `Th` over the three hash functions, the address that names every hash call, and the compression
//! counter.
//!
//! Every call hashes `P | address | payload`, each hash with its own layout:
//!
//! - Keccak-256: `P` inline; `n` bytes cost `n / 136 + 1` permutations.
//! - BLAKE2s-256: `P` inline; `n` bytes cost `ceil(n / 64)` compressions (no padding byte), so
//!   `P | address | left | right` is exactly one 64-byte block.
//! - SHA-256: `P` alone in its own zero-padded 64-byte block, compressed once by [`Pp::new`] (once
//!   per key for the signer, once per verification for the verifier); a call then costs `ceil((n + 9) / 64)` compressions for its `n` bytes after
//!   that block, the 9 being the padding byte and the length.

use std::cell::Cell;

use crate::*;

pub const ADDRESS_LEN: usize = 16;

// Hash types (low five bits of byte 7 of the address).
pub const TWEAK_PRF: u8 = 0;
pub const TWEAK_CHAIN: u8 = 1;
pub const TWEAK_LEAF: u8 = 2;
pub const TWEAK_NODE: u8 = 3;
pub const TWEAK_ENC: u8 = 4;
pub const TWEAK_PARAMETER: u8 = 5;
pub const TWEAK_RANDOMIZER: u8 = 7;
pub const TWEAK_MSG: u8 = 12;
/// A pruned key's surrogate siblings (the kept subtree's position comes from the low bits of `P`).
pub const TWEAK_SURROGATE: u8 = 13;
// The forest: seed derivation, chains, child leaves, sub-tree nodes, super-children, top-tree nodes.
pub const TWEAK_FOREST_PRF: u8 = 14;
pub const TWEAK_FCHAIN: u8 = 15;
pub const TWEAK_CHILD_LEAF: u8 = 16;
pub const TWEAK_SUB_NODE: u8 = 17;
pub const TWEAK_SUPER_CHILD: u8 = 18;
pub const TWEAK_TOP_NODE: u8 = 19;
// Type 20 is unused: the forest key is not hashed, the encoding absorbs its nodes (two per coordinate).

/// The hash function of a configuration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HashFn {
    Keccak256,
    Blake2s,
    Sha256,
}

impl HashFn {
    pub const ALL: [HashFn; 3] = [HashFn::Keccak256, HashFn::Blake2s, HashFn::Sha256];

    /// Bytes of a block: what one compression (one Keccak-f permutation) absorbs.
    pub const fn block(self) -> usize {
        match self {
            HashFn::Keccak256 => keccak::RATE,
            HashFn::Blake2s => blake2s::BLOCK,
            HashFn::Sha256 => sha256::BLOCK,
        }
    }

    /// Bytes of a call's input that are hashed per call before its payload: `P | address`, or the
    /// address alone after SHA-256's cached block of `P`.
    pub const fn prefix(self) -> usize {
        match self {
            HashFn::Sha256 => ADDRESS_LEN,
            _ => PUBLIC_PARAM_LEN + ADDRESS_LEN,
        }
    }

    /// Compressions of a call whose input after the cached part is `len` bytes.
    pub const fn cost(self, len: usize) -> u64 {
        match self {
            HashFn::Keccak256 => keccak::permutations(len),
            HashFn::Blake2s => blake2s::compressions(len),
            HashFn::Sha256 => sha256::compressions(len),
        }
    }

    /// Compressions of `Th` with a payload of `payload` bytes.
    pub const fn call(self, payload: usize) -> u64 {
        self.cost(self.prefix() + payload)
    }

    /// Zero bytes between the message and the randomizer in the digest input, so that the
    /// randomizer is alone in the last block: none for Keccak-256 (the whole 80-byte input is one
    /// block) and BLAKE2s (`P | address | m` is exactly one block), 16 for SHA-256 (`address | m` is
    /// 48 bytes).
    pub const fn digest_pad(self) -> usize {
        match self {
            HashFn::Sha256 => 16,
            _ => 0,
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            HashFn::Keccak256 => "Keccak-256",
            HashFn::Blake2s => "BLAKE2s",
            HashFn::Sha256 => "SHA-256",
        }
    }
}

/// The public parameter of a key with its hash function, and for SHA-256 the state after the
/// zero-padded block of `P`, compressed once.
#[derive(Clone)]
pub struct Pp {
    hash: HashFn,
    bytes: PublicParam,
    sha: sha256::Hasher,
}

impl Pp {
    pub fn new(hash: HashFn, bytes: PublicParam) -> Self {
        let mut sha = sha256::Hasher::new();
        if hash == HashFn::Sha256 {
            let mut block = [0u8; sha256::BLOCK];
            block[..PUBLIC_PARAM_LEN].copy_from_slice(&bytes);
            sha.update(&block);
            count_blocks(1);
        }
        Self { hash, bytes, sha }
    }

    pub fn hash(&self) -> HashFn {
        self.hash
    }

    pub fn bytes(&self) -> PublicParam {
        self.bytes
    }
}

/// The address of a hash call: its type, a chain step, the layer and the tree, and two fields,
/// `hi < 2^24` and `lo`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Tweak {
    t: u8,
    step: u8,
    layer: u8,
    tree: u32,
    hi: u32,
    lo: u32,
}

pub fn tweak(t: u8, hi: u32, lo: u32) -> Tweak {
    assert!(t < 32 && hi < 1 << 24);
    Tweak { t, step: 0, layer: 0, tree: 0, hi, lo }
}

impl Tweak {
    /// The same address at chain step `step < 8`.
    pub fn step(self, step: usize) -> Self {
        assert!(step < 8);
        Self { step: step as u8, ..self }
    }

    /// The same address in tree `tree` of layer `layer` (layers counted from the bottom).
    pub fn at(self, layer: usize, tree: u32) -> Self {
        Self { layer: layer as u8, tree, ..self }
    }
}

/// The 16 bytes that follow `P` in a hash input:
/// `[lo:4 | hi:3 | t + 32 step:1 | layer:1 | tree:4 | 0^3]`, the fields little endian. The layer and
/// the tree are 0 in a one-layer key and in the forest.
pub fn address(tw: &Tweak) -> [u8; ADDRESS_LEN] {
    let mut out = [0u8; ADDRESS_LEN];
    out[..4].copy_from_slice(&tw.lo.to_le_bytes());
    out[4..7].copy_from_slice(&tw.hi.to_le_bytes()[..3]);
    out[7] = tw.t | tw.step << 5;
    out[8] = tw.layer;
    out[9..13].copy_from_slice(&tw.tree.to_le_bytes());
    out
}

/// Streaming state of one of the three hashes (a Keccak sponge is larger than the others; the
/// states are short-lived).
#[allow(clippy::large_enum_variant)]
#[derive(Clone)]
enum Hasher {
    Keccak(keccak::Hasher),
    Blake2s(blake2s::Hasher),
    Sha256(sha256::Hasher),
}

impl Hasher {
    fn update(&mut self, data: &[u8]) -> &mut Self {
        match self {
            Hasher::Keccak(h) => {
                h.update(data);
            }
            Hasher::Blake2s(h) => {
                h.update(data);
            }
            Hasher::Sha256(h) => {
                h.update(data);
            }
        }
        self
    }

    /// Compresses a full buffered block before more input: Keccak and SHA-256 already have, BLAKE2s
    /// waits for more input.
    fn flush(&mut self) {
        if let Hasher::Blake2s(h) = self {
            h.flush();
        }
    }

    fn finalize(&self) -> [u8; 32] {
        match self {
            Hasher::Keccak(h) => h.finalize(),
            Hasher::Blake2s(h) => h.finalize(),
            Hasher::Sha256(h) => h.finalize(),
        }
    }
}

/// A hasher that has absorbed `P | address`.
fn start(pp: &Pp, tw: &Tweak) -> Hasher {
    let mut hasher = match pp.hash {
        HashFn::Keccak256 => Hasher::Keccak(keccak::Hasher::new()),
        HashFn::Blake2s => Hasher::Blake2s(blake2s::Hasher::new()),
        HashFn::Sha256 => Hasher::Sha256(pp.sha.clone()),
    };
    if pp.hash != HashFn::Sha256 {
        hasher.update(&pp.bytes);
    }
    hasher.update(&address(tw));
    hasher
}

thread_local! {
    static COMPRESSIONS: Cell<u64> = const { Cell::new(0) };
}

/// Compressions (Keccak-f permutations for Keccak-256) this thread has spent in [`th`],
/// [`th_pair`], [`th_digests`], [`Midstate`] and [`Pp::new`].
pub fn compressions() -> u64 {
    COMPRESSIONS.with(Cell::get)
}

fn count_blocks(n: u64) {
    COMPRESSIONS.with(|c| c.set(c.get() + n));
}

/// `Th(P, tw, payload)`, untruncated.
fn th_full(pp: &Pp, tw: &Tweak, parts: &[&[u8]]) -> [u8; 32] {
    let len: usize = parts.iter().map(|p| p.len()).sum();
    count_blocks(pp.hash.call(len));
    let mut hasher = start(pp, tw);
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize()
}

/// `Th(P, tw, payload)`: the hash of `P | address | payload`, truncated.
pub fn th(pp: &Pp, tw: &Tweak, payload: &[u8]) -> Digest {
    th_full(pp, tw, &[payload])[..N].try_into().unwrap()
}

/// Two secrets for one hash: the two 16-byte halves of the untruncated hash of `P | address | payload`.
pub fn th_pair(pp: &Pp, tw: &Tweak, payload: &[u8]) -> [Digest; 2] {
    let out = th_full(pp, tw, &[payload]);
    [out[..N].try_into().unwrap(), out[N..].try_into().unwrap()]
}

/// `Th` over a concatenation of digests: a Merkle node or a one-time leaf.
pub fn th_digests(pp: &Pp, tw: &Tweak, values: &[Digest]) -> Digest {
    let parts: Vec<&[u8]> = values.iter().map(|v| &v[..]).collect();
    th_full(pp, tw, &parts)[..N].try_into().unwrap()
}

/// The state after the whole blocks of `P | address | fixed`, for inputs that differ only in what
/// follows. Every whole block of the fixed part is compressed here, once, and each
/// [`Midstate::finish`] pays for the rest and the padding.
#[derive(Clone)]
pub struct Midstate {
    hasher: Hasher,
    hash: HashFn,
    /// The end of the fixed part that is not a whole block, in bytes.
    rest: usize,
}

impl Midstate {
    pub fn new(pp: &Pp, tw: &Tweak, fixed: &[&[u8]]) -> Self {
        let mut hasher = start(pp, tw);
        let mut len = pp.hash.prefix();
        for part in fixed {
            hasher.update(part);
            len += part.len();
        }
        hasher.flush();
        let block = pp.hash.block();
        count_blocks((len / block) as u64);
        Self { hasher, hash: pp.hash, rest: len % block }
    }

    /// The untruncated 32-byte hash of the input completed by `tail`, which is not empty.
    pub fn finish(&self, tail: &[u8]) -> [u8; 32] {
        assert!(!tail.is_empty());
        count_blocks(self.hash.cost(self.rest + tail.len()));
        let mut hasher = self.hasher.clone();
        hasher.update(tail);
        hasher.finalize()
    }
}

/// One-shot hash of `data` with `hash`, for the configured seed and tests (not counted).
pub fn hash_bytes(hash: HashFn, data: &[u8]) -> [u8; 32] {
    match hash {
        HashFn::Keccak256 => keccak::hash(data),
        HashFn::Blake2s => blake2s::hash(data),
        HashFn::Sha256 => sha256::hash(data),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The bytes each hash actually hashes for `Th(P, tw, payload)`.
    fn raw_input(hash: HashFn, pp: &PublicParam, tw: &Tweak, payload: &[u8]) -> Vec<u8> {
        let mut input = pp.to_vec();
        if hash == HashFn::Sha256 {
            input.resize(sha256::BLOCK, 0);
        }
        input.extend_from_slice(&address(tw));
        input.extend_from_slice(payload);
        input
    }

    /// Pins the byte layout of the address and of a hash input for each hash.
    #[test]
    fn address_layout() {
        let tw = tweak(TWEAK_SUB_NODE, 0x123456, 0x89abcdef).step(5).at(2, 0x0a0b0c0d);
        assert_eq!(address(&tw), [0xef, 0xcd, 0xab, 0x89, 0x56, 0x34, 0x12, 0xb1, 2, 0x0d, 0x0c, 0x0b, 0x0a, 0, 0, 0]);
        let bytes: PublicParam = std::array::from_fn(|i| i as u8 + 1);
        let payload = [9u8; N];
        for hash in HashFn::ALL {
            let pp = Pp::new(hash, bytes);
            let input = raw_input(hash, &bytes, &tw, &payload);
            assert_eq!(th(&pp, &tw, &payload)[..], hash_bytes(hash, &input)[..N], "{hash:?}");
        }
    }

    /// The costs of the calls the scheme makes, per hash: a chain step, a node, a forest WOTS leaf,
    /// a super-child, a one-time leaf.
    #[test]
    fn call_costs() {
        let costs = |hash: HashFn| [16, 32, 96, 64, 1024].map(|payload| hash.call(payload));
        assert_eq!(costs(HashFn::Keccak256), [1, 1, 1, 1, 8]);
        assert_eq!(costs(HashFn::Blake2s), [1, 1, 2, 2, 17]);
        assert_eq!(costs(HashFn::Sha256), [1, 1, 2, 2, 17]);
        for hash in HashFn::ALL {
            let pp = Pp::new(hash, [1; PUBLIC_PARAM_LEN]);
            for (payload, cost) in [16usize, 32, 96, 64, 1024].into_iter().zip(costs(hash)) {
                let before = compressions();
                th(&pp, &tweak(TWEAK_LEAF, 0, 0), &vec![3u8; payload]);
                assert_eq!(compressions() - before, cost, "{hash:?}, {payload} bytes");
            }
        }
    }

    /// A midstate gives the same hash as one pass, and pays for each whole block once, whether or
    /// not the fixed part ends on a block boundary.
    #[test]
    fn midstate_matches_one_pass() {
        let bytes: PublicParam = std::array::from_fn(|i| 3 * i as u8);
        let tw = tweak(TWEAK_MSG, 1, 0);
        for hash in HashFn::ALL {
            let pp = Pp::new(hash, bytes);
            let block = hash.block();
            for fixed_len in [block - hash.prefix(), 2 * block - hash.prefix() - 32] {
                let (fixed, tail) = (vec![7u8; fixed_len], [9u8; 16]);
                let input = [raw_input(hash, &bytes, &tw, &fixed), tail.to_vec()].concat();
                let before = compressions();
                let state = Midstate::new(&pp, &tw, &[&fixed]);
                assert_eq!(compressions() - before, (fixed_len + hash.prefix()) as u64 / block as u64);
                for _ in 0..3 {
                    let before = compressions();
                    assert_eq!(state.finish(&tail), hash_bytes(hash, &input), "{hash:?}");
                    assert_eq!(compressions() - before, 1, "one compression per tail, {hash:?}");
                }
            }
        }
    }
}
