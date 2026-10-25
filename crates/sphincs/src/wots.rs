//! WOTS+C: `v = 64` chains of `2^w - 1 = 3` steps, and the target-sum code that replaces the
//! Winternitz checksum. A codeword is 64 chunks summing to `T = 123`; the signer searches the least
//! counter whose encoding is a codeword. The encoding hashes the signed message itself, with the
//! counter last: the forest key at the bottom layer, the root of the tree below at a layer above.
//!
//! A one-time key is named by its layer (from the bottom), its tree in that layer and its leaf in
//! that tree ([`OtsKey`]).

use crate::*;

/// Where a one-time key sits: its layer (from the bottom), its tree and its leaf in that tree. At
/// layer `l` the key of index `idx` is at position `e = idx >> below(l)` across the layer, that is
/// tree `e >> h_l`, leaf `e mod 2^(h_l)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OtsKey {
    pub layer: usize,
    pub tree: u32,
    pub leaf: u32,
}

impl OtsKey {
    /// The key at position `e` of a layer of height `height`.
    pub fn at(layer: usize, height: usize, e: u64) -> Self {
        Self { layer, tree: (e >> height) as u32, leaf: (e & ((1 << height) - 1)) as u32 }
    }

    /// An address of this key with type `t` and field `hi`; `lo` is the leaf.
    pub fn tweak(&self, t: u8, hi: u32) -> Tweak {
        tweak(t, hi, self.leaf).at(self.layer, self.tree)
    }
}

/// The starts of the `v` chains of a one-time key. One hash of the seed gives two of
/// them: chains `2 t` and `2 t + 1` are the two halves of the hash at address `t`.
pub fn wots_secrets(pp: &Pp, master: &MasterSecret, key: &OtsKey) -> [Digest; V] {
    let mut secrets = [[0u8; N]; V];
    for t in 0..V / 2 {
        let pair = th_pair(pp, &wots_secret_tweak(key, t), master);
        secrets[2 * t] = pair[0];
        secrets[2 * t + 1] = pair[1];
    }
    secrets
}

/// The address of the hash that gives the starts of chains `2 t` and `2 t + 1`.
pub fn wots_secret_tweak(key: &OtsKey, t: usize) -> Tweak {
    key.tweak(TWEAK_PRF, t as u32)
}

/// The tweak of the step of chain `i` that lands on position `to`, in `1..CHAIN_LEN`.
pub fn chain_tweak(key: &OtsKey, i: usize, to: usize) -> Tweak {
    debug_assert!((1..CHAIN_LEN).contains(&to));
    key.tweak(TWEAK_CHAIN, i as u32).step(to - 1)
}

/// `steps` chain steps of chain `i` from position `start`.
pub fn chain(pp: &Pp, key: &OtsKey, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
    debug_assert!(start + steps < CHAIN_LEN);
    (start + 1..=start + steps).fold(value, |current, to| th(pp, &chain_tweak(key, i, to), &current))
}

/// The Merkle leaf of a one-time key: `Th` over its 64 chain ends.
pub fn wots_leaf_hash(pp: &Pp, key: &OtsKey, ends: &[Digest; V]) -> Digest {
    th_digests(pp, &key.tweak(TWEAK_LEAF, 0), ends)
}

/// The encoding hash after its fixed part, `P | A(enc, 0, leaf) | message`. The counter falls in the
/// last block, so each counter costs one compression.
pub fn encoding_midstate(pp: &Pp, key: &OtsKey, message: &[u8]) -> Midstate {
    Midstate::new(pp, &key.tweak(TWEAK_ENC, 0), &[message])
}

/// The codeword of counter `c` from the encoding's midstate, or `None` if its digest is not one.
pub fn encode_from(state: &Midstate, c: u32) -> Option<[u8; V]> {
    codeword(state.finish(&c.to_le_bytes())[..N].try_into().unwrap())
}

/// `Enc(P, key, message, c)`: `Th(P, A(enc, 0, leaf), message | c)` decoded, or `None` if it is not a
/// codeword.
pub fn encode(pp: &Pp, key: &OtsKey, message: &[u8], c: u32) -> Option<[u8; V]> {
    encode_from(&encoding_midstate(pp, key, message), c)
}

/// The 128 digest bits as 64 chunks of 2 bits, little endian; a codeword if they sum to `T`.
pub fn codeword(digest: &Digest) -> Option<[u8; V]> {
    let d = u128::from_le_bytes(*digest);
    let x: [u8; V] = std::array::from_fn(|i| ((d >> (W * i)) & (CHAIN_LEN as u128 - 1)) as u8);
    (x.iter().map(|&c| c as usize).sum::<usize>() == TARGET_SUM).then_some(x)
}

/// The least admissible counter and its codeword. Deterministic in its inputs, which keeps one
/// key to one codeword.
pub fn wots_encode(pp: &Pp, key: &OtsKey, message: &[u8]) -> Option<(u32, [u8; V])> {
    let state = encoding_midstate(pp, key, message);
    (0..MAX_ENCODING_ATTEMPTS).find_map(|c| encode_from(&state, c as u32).map(|x| (c as u32, x)))
}

/// `Ots.sign` from the master secret: the counter and the chain value each chunk opens.
pub fn wots_sign(pp: &Pp, master: &MasterSecret, key: &OtsKey, message: &[u8]) -> Option<(u32, [Digest; V])> {
    let (c, x) = wots_encode(pp, key, message)?;
    let secrets = wots_secrets(pp, master, key);
    let signature = std::array::from_fn(|i| chain(pp, key, i, 0, x[i] as usize, secrets[i]));
    Some((c, signature))
}

/// `Ots.leaf`: the leaf a claimed signature recovers, or `None` if the counter is not admissible.
pub fn wots_recover(pp: &Pp, key: &OtsKey, message: &[u8], c: u32, signature: &[Digest; V]) -> Option<Digest> {
    let x = encode(pp, key, message, c)?;
    let ends = std::array::from_fn(|i| {
        let start = x[i] as usize;
        chain(pp, key, i, start, CHAIN_LEN - 1 - start, signature[i])
    });
    Some(wots_leaf_hash(pp, key, &ends))
}

/// The chain ends of a one-time key, from the master secret.
pub fn wots_ends(pp: &Pp, master: &MasterSecret, key: &OtsKey) -> [Digest; V] {
    let secrets = wots_secrets(pp, master, key);
    std::array::from_fn(|i| chain(pp, key, i, 0, CHAIN_LEN - 1, secrets[i]))
}

/// The leaf of a one-time key, from the master secret.
pub fn wots_leaf(pp: &Pp, master: &MasterSecret, key: &OtsKey) -> Digest {
    wots_leaf_hash(pp, key, &wots_ends(pp, master, key))
}
