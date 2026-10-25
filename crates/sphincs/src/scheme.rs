//! The XMSS tree (full or pruned), the message digest, and `Gen`, `Sign`, `Ver`.
//!
//! A pruned key keeps one subtree of height `b` and replaces the `h - b` siblings above it by
//! pseudorandom surrogate nodes; the signer grinds its randomizer until the leaf index lands in the
//! kept subtree. A full key is the pruned key with `b = h`. The attempts `R_0 + i * delta` step by a
//! secret odd `delta`, so a signature does not tell which randomizers were rejected before it.

use crate::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PublicKey {
    pub root: Digest,
    pub public_param: PublicParam,
}

impl PublicKey {
    pub fn to_bytes(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0u8; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.root);
        out[N..].copy_from_slice(&self.public_param);
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub randomizer: Randomizer,
    pub forest: ForestOpening,
    pub counter: u32,
    pub wots: [Digest; V],
    pub path: [Digest; H],
}

impl Signature {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(SIG_SIZE);
        out.extend_from_slice(&self.randomizer);
        for coord in &self.forest {
            for sub in &coord.sub {
                for value in &sub.values {
                    out.extend_from_slice(value);
                }
                for node in &sub.path {
                    out.extend_from_slice(node);
                }
            }
            for node in &coord.top {
                out.extend_from_slice(node);
            }
        }
        out.extend_from_slice(&self.counter.to_le_bytes());
        for value in &self.wots {
            out.extend_from_slice(value);
        }
        for node in &self.path {
            out.extend_from_slice(node);
        }
        debug_assert_eq!(out.len(), SIG_SIZE);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != SIG_SIZE {
            return None;
        }
        let mut at = 0;
        let mut take = |len: usize| {
            at += len;
            &bytes[at - len..at]
        };
        let randomizer = take(RANDOMIZER_LEN).try_into().unwrap();
        let forest: ForestOpening = std::array::from_fn(|_| CoordOpening {
            sub: std::array::from_fn(|_| SubOpening {
                values: std::array::from_fn(|_| take(N).try_into().unwrap()),
                path: std::array::from_fn(|_| take(N).try_into().unwrap()),
            }),
            top: std::array::from_fn(|_| take(N).try_into().unwrap()),
        });
        let counter = u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap());
        let wots = std::array::from_fn(|_| take(N).try_into().unwrap());
        let path = std::array::from_fn(|_| take(N).try_into().unwrap());
        Some(Self { randomizer, forest, counter, wots, path })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VerifyError {
    /// The counter does not encode the forest key into a codeword.
    InadmissibleEncoding,
    RootMismatch,
}

/// The state of the digest call after `P | address | m`. With the randomizer the whole input is
/// 80 bytes, within one block, so grinding it costs one permutation per attempt.
pub fn digest_midstate(pp: &PublicParam, m: &Message) -> Midstate {
    Midstate::new(pp, &tweak(TWEAK_MSG, 0, 0), &[m])
}

/// The message digest call, `P | address | m | rho`, untruncated. `P` binds the key, so the root is
/// not hashed.
pub fn digest_block(pp: &PublicParam, rho: &Randomizer, m: &Message) -> [u8; 32] {
    digest_midstate(pp, m).finish(rho)
}

/// The leaf index alone (what grinding computes).
pub fn digest_index(pp: &PublicParam, rho: &Randomizer, m: &Message) -> u64 {
    index_of_block(&digest_block(pp, rho, m))
}

/// The leaf index: `h` bits from bit 208, i.e. the high bits of the last 64-bit word.
pub fn index_of_block(d0: &[u8; 32]) -> u64 {
    u64::from_le_bytes(d0[24..32].try_into().unwrap()) >> (INDEX_OFFSET - 192) & ((1 << H) - 1)
}

/// Bit offset of the leaf index in the digest: the last 16 bytes carry the 16 children, the 8
/// super-children and then the index.
pub const INDEX_OFFSET: usize = 128 + SUBS * COORDS * SUB_HEIGHT + COORDS * TOP_HEIGHT;

/// The message digest, one call: the 16 codeword indices are its first 16 bytes (byte `2c + j` for
/// sub-tree `j` of coordinate `c`), then the last 16 bytes hold the 16 children (3 bits each, in
/// the order `2c + j`), the 8 super-children (4 bits each, from bit 176) and the leaf index (from
/// bit 208). No field lies across two 64-bit words.
pub fn message_digest(pp: &PublicParam, rho: &Randomizer, m: &Message) -> (u64, [CoordMark; COORDS]) {
    let d = digest_block(pp, rho, m);
    let high = u128::from_le_bytes(d[16..32].try_into().unwrap());
    let field = |offset: usize, bits: usize| ((high >> offset) & ((1u128 << bits) - 1)) as usize;
    let marks = std::array::from_fn(|c| CoordMark {
        super_child: field(SUBS * COORDS * SUB_HEIGHT + TOP_HEIGHT * c, TOP_HEIGHT),
        child: std::array::from_fn(|j| field(SUB_HEIGHT * (SUBS * c + j), SUB_HEIGHT)),
        word: std::array::from_fn(|j| d[SUBS * c + j]),
    });
    (index_of_block(&d), marks)
}

pub fn xmss_node(pp: &PublicParam, level: usize, j: u64, left: &Digest, right: &Digest) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, level as u32, j as u32), &[*left, *right])
}

/// The XMSS tree of a key: the kept subtree's levels and the surrogates above it.
#[derive(Clone, Debug)]
pub struct XmssTree {
    /// Height of the kept subtree; `b = h` is a full key.
    pub b: usize,
    /// The kept subtree holds leaves `s * 2^b .. (s + 1) * 2^b`.
    pub s: u64,
    /// The kept subtree, level 0 being its `2^b` leaves.
    levels: Vec<Vec<Digest>>,
    /// The siblings of the path at levels `b..h`, surrogates (no secret below them) unless `b = h`.
    pub surrogates: Vec<Digest>,
    pub root: Digest,
}

impl XmssTree {
    pub fn from_leaves(pp: &PublicParam, b: usize, s: u64, leaves: Vec<Digest>, surrogates: Vec<Digest>) -> Self {
        assert!(b <= H && s < 1 << (H - b));
        assert_eq!(leaves.len(), 1 << b);
        assert_eq!(surrogates.len(), H - b);
        let mut levels = vec![leaves];
        for level in 1..=b {
            let below = &levels[level - 1];
            let first = s << (b - level);
            let up = (0..below.len() / 2)
                .map(|j| xmss_node(pp, level, first + j as u64, &below[2 * j], &below[2 * j + 1]))
                .collect();
            levels.push(up);
        }
        let root = surrogates.iter().enumerate().fold(levels[b][0], |node, (t, sibling)| {
            let level = b + t;
            let j = s >> t;
            let (left, right) = if j & 1 == 0 { (node, *sibling) } else { (*sibling, node) };
            xmss_node(pp, level + 1, j >> 1, &left, &right)
        });
        Self { b, s, levels, surrogates, root }
    }

    pub fn contains(&self, idx: u64) -> bool {
        idx >> self.b == self.s
    }

    /// The authentication path of leaf `idx`, which must be kept.
    pub fn path(&self, idx: u64) -> [Digest; H] {
        assert!(self.contains(idx));
        let local = (idx - (self.s << self.b)) as usize;
        std::array::from_fn(|level| {
            if level < self.b { self.levels[level][(local >> level) ^ 1] } else { self.surrogates[level - self.b] }
        })
    }
}

/// `Tree.fold`: the root a leaf and its path reach.
pub fn tree_fold(pp: &PublicParam, idx: u64, leaf: Digest, path: &[Digest; H]) -> Digest {
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        let (left, right) = if (idx >> level) & 1 == 0 { (current, *sibling) } else { (*sibling, current) };
        xmss_node(pp, level + 1, idx >> (level + 1), &left, &right)
    })
}

/// A non-threshold secret key.
#[derive(Clone)]
pub struct SecretKey {
    pub public_param: PublicParam,
    pub master: MasterSecret,
    pub tree: XmssTree,
}

impl SecretKey {
    pub fn public_key(&self) -> PublicKey {
        PublicKey { root: self.tree.root, public_param: self.public_param }
    }
}

/// `Gen` for a key keeping a subtree of height `b` (`b = h` for a full key).
///
/// The public parameter is derived from the seed, its low bits place the kept subtree, and the
/// surrogates are derived from the seed.
pub fn key_gen(seed: &MasterSecret, b: usize) -> (SecretKey, PublicKey) {
    let public_param = th(&[0; PUBLIC_PARAM_LEN], &tweak(TWEAK_PARAMETER, 0, 0), seed);
    let s = if b == H { 0 } else { u64::from_le_bytes(public_param[..8].try_into().unwrap()) & ((1 << (H - b)) - 1) };
    let leaves = (0..1u64 << b)
        .map(|j| {
            let e = ((s << b) + j) as u32;
            wots_leaf_hash(&public_param, e, &wots_ends(&public_param, seed, e))
        })
        .collect();
    let surrogates = (b..H).map(|level| th(&public_param, &tweak(TWEAK_SURROGATE, level as u32, 0), seed)).collect();
    let tree = XmssTree::from_leaves(&public_param, b, s, leaves, surrogates);
    let sk = SecretKey { public_param, master: *seed, tree };
    let pk = sk.public_key();
    (sk, pk)
}

/// The walk of a message's randomizers, from one hash `Th_pair(P, tw_rand, S | m)`: the first half
/// is the start `R_0`, the second half with its lowest bit set is the step `delta`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RandomizerWalk {
    pub base: Randomizer,
    pub step: Randomizer,
}

pub fn randomizer_walk(pp: &PublicParam, master: &MasterSecret, m: &Message) -> RandomizerWalk {
    let mut payload = [0u8; MASTER_SECRET_LEN + MESSAGE_LEN];
    payload[..MASTER_SECRET_LEN].copy_from_slice(master);
    payload[MASTER_SECRET_LEN..].copy_from_slice(m);
    let [base, mut step] = th_pair(pp, &tweak(TWEAK_RANDOMIZER, 0, 0), &payload);
    step[0] |= 1;
    RandomizerWalk { base, step }
}

/// The randomizer of attempt `i`: `R_0 + i * delta`, as little-endian 128-bit numbers. No hash is
/// needed from one attempt to the next, and `delta` is odd, so the walk does not come back before
/// `2^128` attempts.
pub fn randomizer(walk: &RandomizerWalk, i: u32) -> Randomizer {
    let (base, step) = (u128::from_le_bytes(walk.base), u128::from_le_bytes(walk.step));
    base.wrapping_add(step.wrapping_mul(u128::from(i))).to_le_bytes()
}

/// `Sign`: take the least `i` whose randomizer `R_0 + i * delta` lands in the kept subtree (`i = 0`
/// for a full key), open the forest, sign its key with WOTS+C.
pub fn sign(sk: &SecretKey, m: &Message) -> Signature {
    let pp = &sk.public_param;
    // The digest's fixed part is absorbed once, and the randomizers are `R_0 + i * delta`: an
    // attempt costs one permutation.
    let (walk, digests) = (randomizer_walk(pp, &sk.master, m), digest_midstate(pp, m));
    let rho = (0u32..)
        .map(|i| randomizer(&walk, i))
        .find(|rho| sk.tree.contains(index_of_block(&digests.finish(rho))))
        .unwrap();
    let (idx, marks) = message_digest(pp, &rho, m);
    let forest = Forest::new(pp, &sk.master, idx);
    let opening = forest.open(pp, idx, &marks);
    let (counter, wots) = wots_sign(pp, &sk.master, idx as u32, &forest.key).expect("no admissible WOTS+C encoding");
    Signature { randomizer: rho, forest: opening, counter, wots, path: sk.tree.path(idx) }
}

/// `Ver`.
pub fn verify(pk: &PublicKey, m: &Message, sig: &Signature) -> Result<(), VerifyError> {
    let pp = &pk.public_param;
    let (idx, marks) = message_digest(pp, &sig.randomizer, m);
    let key = forest_recover(pp, idx, &marks, &sig.forest);
    let leaf = wots_recover(pp, idx as u32, &key, sig.counter, &sig.wots).ok_or(VerifyError::InadmissibleEncoding)?;
    if tree_fold(pp, idx, leaf, &sig.path) == pk.root { Ok(()) } else { Err(VerifyError::RootMismatch) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(x: u8) -> MasterSecret {
        std::array::from_fn(|i| x.wrapping_mul(31).wrapping_add(i as u8))
    }

    #[test]
    fn pruned_sign_verify_and_costs() {
        for b in [3usize, 12] {
            let before = permutations();
            let (sk, pk) = key_gen(&seed(b as u8), b);
            let keygen = permutations() - before;
            // P, the kept subtree (232 per WOTS leaf plus the nodes), and a derivation and a node per surrogate.
            assert_eq!(keygen, 1 + (1u64 << b) * 232 + ((1u64 << b) - 1) + 2 * (H - b) as u64);
            for t in 0..3u8 {
                let m: Message = std::array::from_fn(|i| t ^ i as u8);
                let sig = sign(&sk, &m);
                let bytes = sig.to_bytes();
                assert_eq!(bytes.len(), SIG_SIZE);
                assert_eq!(Signature::from_bytes(&bytes).unwrap(), sig);
                let before = permutations();
                assert_eq!(verify(&pk, &m, &sig), Ok(()));
                assert_eq!(permutations() - before, VERIFY_PERMUTATIONS, "verification is constant");
                let mut other = m;
                other[0] ^= 1;
                assert!(verify(&pk, &other, &sig).is_err());
                let mut bad = sig.clone();
                bad.forest[3].sub[0].values[0][0] ^= 1;
                assert!(verify(&pk, &m, &bad).is_err());
            }
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn tampered_signatures_are_rejected() {
        let (sk, pk) = key_gen(&seed(9), 10);
        let m: Message = std::array::from_fn(|i| i as u8);
        let sig = sign(&sk, &m);
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        let bytes = sig.to_bytes();
        for len in [0, SIG_SIZE - 1, SIG_SIZE + 1] {
            let mut b = bytes.clone();
            b.resize(len, 0);
            assert!(Signature::from_bytes(&b).is_none(), "length {len}");
        }
        // Other counters: never accepted, and some encode no codeword at all.
        let mut inadmissible = 0;
        for delta in 1..=40u32 {
            let mut bad = sig.clone();
            bad.counter = sig.counter.wrapping_add(delta);
            match verify(&pk, &m, &bad) {
                Err(VerifyError::InadmissibleEncoding) => inadmissible += 1,
                r => assert_eq!(r, Err(VerifyError::RootMismatch), "counter + {delta}"),
            }
        }
        assert!(inadmissible > 30, "{inadmissible} of 40 altered counters were inadmissible");
        let mut cases: Vec<(&str, Signature)> = Vec::new();
        let mut bad = sig.clone();
        bad.path[7][3] ^= 1;
        cases.push(("auth path", bad));
        let mut bad = sig.clone();
        bad.path[H - 1][0] ^= 0x80;
        cases.push(("top of the auth path", bad));
        let mut bad = sig.clone();
        bad.wots[11][5] ^= 4;
        cases.push(("WOTS value", bad));
        let mut bad = sig.clone();
        bad.forest[2].sub[1].path[SUB_HEIGHT - 1][0] ^= 1;
        cases.push(("sub-tree path", bad));
        let mut bad = sig.clone();
        bad.forest[COORDS - 1].top[TOP_HEIGHT - 1][0] ^= 1;
        cases.push(("top-tree path", bad));
        let mut bad = sig.clone();
        bad.forest[COORDS - 1].sub[1].values[CHILD_CHAINS - 1][N - 1] ^= 1;
        cases.push(("chain value", bad));
        let mut bad = sig.clone();
        bad.randomizer[0] ^= 1;
        cases.push(("randomizer", bad));
        for (what, bad) in cases {
            assert!(verify(&pk, &m, &bad).is_err(), "tampered {what} accepted");
            assert_eq!(Signature::from_bytes(&bad.to_bytes()).unwrap(), bad);
        }
        let mut other = pk;
        other.public_param[0] ^= 1;
        assert!(verify(&other, &m, &sig).is_err(), "another public parameter");
    }

    /// Pins the key and the signature bytes of one small pruned key, so that a change to
    /// the addresses, the hash inputs or the serialization cannot pass unnoticed.
    #[test]
    fn known_answer() {
        let (sk, pk) = key_gen(&seed(1), 11);
        let m: Message = std::array::from_fn(|i| (7 * i) as u8);
        let sig = sign(&sk, &m);
        let digest = keccak::hash(&sig.to_bytes());
        assert_eq!(hex(&pk.to_bytes()), "bca067181df522e8f72775a93784f8082e582128e480149accc2ed4f19edcd00");
        assert_eq!(hex(&digest), "841f5a7f3bdbd25912f955b90384ed999a79cb2cb9db364b0e82be1da59d43c7");
        assert_eq!(sig.counter, 679);
    }

    /// The signature's randomizer is the first attempt of the message's walk that lands, and the
    /// attempts before it are not `R - 1, R - 2, ...`.
    #[test]
    fn the_signer_takes_the_first_landing_attempt() {
        let (sk, _) = key_gen(&seed(4), 10);
        let pp = &sk.public_param;
        for t in 0..4u8 {
            let m: Message = std::array::from_fn(|i| t.wrapping_mul(17) ^ i as u8);
            let walk = randomizer_walk(pp, &sk.master, &m);
            assert_eq!(walk.step[0] & 1, 1);
            let lands = |rho: &Randomizer| sk.tree.contains(digest_index(pp, rho, &m));
            let i = (0u32..).find(|&i| lands(&randomizer(&walk, i))).unwrap();
            let sig = sign(&sk, &m);
            assert_eq!(sig.randomizer, randomizer(&walk, i));
            if i > 0 {
                let previous = u128::from_le_bytes(sig.randomizer).wrapping_sub(u128::from_le_bytes(walk.step));
                assert_eq!(previous.to_le_bytes(), randomizer(&walk, i - 1));
                assert_ne!(previous, u128::from_le_bytes(sig.randomizer).wrapping_sub(1));
            }
        }
    }

    #[test]
    fn a_randomizer_attempt_costs_one_permutation() {
        let (pp, m) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN]);
        let before = permutations();
        let (walk, digests) = (randomizer_walk(&pp, &seed(2), &m), digest_midstate(&pp, &m));
        assert_eq!(permutations() - before, 1, "R_0 and delta, once per message; the digest's fixed part fills no block");
        for i in 0..4 {
            let before = permutations();
            let index = index_of_block(&digests.finish(&randomizer(&walk, i)));
            assert_eq!(permutations() - before, 1);
            assert_eq!(index, digest_index(&pp, &randomizer(&walk, i), &m));
        }
    }

    /// Pins the byte order of the randomizer derivation and of the digest, and the walk.
    #[test]
    fn randomizer_and_digest_inputs() {
        let (pp, m) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN]);
        let walk = randomizer_walk(&pp, &seed(2), &m);
        let input = [&pp[..], &address(&tweak(TWEAK_RANDOMIZER, 0, 0)), &seed(2), &m].concat();
        let output = keccak::hash(&input);
        assert_eq!(walk.base[..], output[..N]);
        assert_eq!(walk.step[0], output[N] | 1, "the step is odd");
        assert_eq!(walk.step[1..], output[N + 1..]);
        assert_eq!(randomizer(&walk, 0), walk.base);
        let mut one = [0u8; N];
        one[0] = 1;
        let ones = RandomizerWalk { base: [0xff; N], step: one };
        assert_eq!(randomizer(&ones, 2), one, "wraps modulo 2^128");
        let mut carry = [0u8; N];
        carry[0] = 0xff;
        let mut three = [0u8; N];
        three[0] = 3;
        assert_eq!(randomizer(&RandomizerWalk { base: carry, step: three }, 1)[..2], [2, 1], "little endian");
        assert_eq!(randomizer(&RandomizerWalk { base: [0; N], step: [0xff; N] }, 5), 5u128.wrapping_neg().to_le_bytes(), "-5");
        let rho = randomizer(&walk, 7);
        let (base, step) = (u128::from_le_bytes(walk.base), u128::from_le_bytes(walk.step));
        assert_eq!(rho, base.wrapping_add(7 * step).to_le_bytes(), "R_0 + 7 delta");
        let input = [&pp[..], &address(&tweak(TWEAK_MSG, 0, 0)), &m, &rho].concat();
        assert_eq!(input.len(), 80, "one block");
        assert_eq!(digest_block(&pp, &rho, &m), keccak::hash(&input));
    }

    /// Pins where the digest's fields are, and that none of them lies across two 64-bit words: the
    /// codeword indices are the first 16 bytes, then the children, the super-children and the index.
    #[test]
    fn digest_fields() {
        let (pp, m, rho) = ([3u8; PUBLIC_PARAM_LEN], [5u8; MESSAGE_LEN], [7u8; N]);
        let d = digest_block(&pp, &rho, &m);
        let word = |w: usize| u64::from_le_bytes(d[8 * w..][..8].try_into().unwrap());
        let (index, marks) = message_digest(&pp, &rho, &m);
        assert_eq!(index, word(3) >> 16 & ((1 << H) - 1));
        for (c, mark) in marks.iter().enumerate() {
            assert_eq!(mark.super_child as u64, word(2 + (48 + 4 * c) / 64) >> ((48 + 4 * c) % 64) & 15);
            for j in 0..SUBS {
                let at = 3 * (2 * c + j);
                assert_eq!(mark.child[j] as u64, word(2) >> at & 7, "child {c} {j}");
                assert_eq!(mark.word[j], d[2 * c + j], "codeword index {c} {j}");
                assert!(at % 64 + SUB_HEIGHT <= 64, "a child lies across two words");
            }
            assert!((48 + 4 * c) % 64 + TOP_HEIGHT <= 64, "a super-child lies across two words");
        }
        assert_eq!(INDEX_OFFSET, 208);
        assert!(INDEX_OFFSET % 64 + H <= 64, "the index lies across two words");
    }

    /// Pins the encoding's input, `P | A(enc, 0, e) | key | counter`, and its costs: 3 permutations
    /// for the verifier, and 2 once plus 1 per counter for the signer.
    #[test]
    fn encoding_absorbs_the_key_and_the_counter() {
        let pp = [3u8; PUBLIC_PARAM_LEN];
        let key: ForestKey = std::array::from_fn(|c| std::array::from_fn(|half| [(2 * c + half) as u8; N]));
        let input = [&pp[..], &address(&tweak(TWEAK_ENC, 0, 77)), key.as_flattened().as_flattened(), &5u32.to_le_bytes()].concat();
        assert_eq!(input.len(), 292);
        let expected = codeword(keccak::hash(&input)[..N].try_into().unwrap());
        let before = permutations();
        assert_eq!(encode(&pp, 77, &key, 5), expected);
        assert_eq!(permutations() - before, 3);
        let before = permutations();
        let state = encoding_midstate(&pp, 77, &key);
        assert_eq!(permutations() - before, 2, "the whole blocks of the key, once");
        let before = permutations();
        assert_eq!(encode_from(&state, 5), expected);
        assert_eq!(permutations() - before, 1, "one permutation per counter");
    }

    #[test]
    fn wots_encoding_takes_about_2197_tries() {
        let pp = [7u8; PUBLIC_PARAM_LEN];
        let tries: u64 =
            (0..100u32).map(|e| u64::from(wots_encode(&pp, e, &[[[e as u8; N]; 2]; COORDS]).unwrap().0) + 1).sum();
        let mean = tries as f64 / 100.0;
        assert!((1100.0..4400.0).contains(&mean), "mean tries {mean}");
    }
}
