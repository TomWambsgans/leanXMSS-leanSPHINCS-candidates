//! The XMSS tree (full or pruned), the message digest, and `Gen`, `Sign`, `Ver`.
//!
//! A pruned key keeps one subtree of height `b` and replaces the `h - b` siblings above it by
//! pseudorandom surrogate nodes; the signer grinds its randomizer until the leaf index lands in the
//! kept subtree. A full key is the pruned key with `b = h`.

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
    pub fors: ForsOpening,
    pub counter: u32,
    pub wots: [Digest; V],
    pub path: [Digest; H],
}

impl Signature {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(SIG_SIZE);
        out.extend_from_slice(&self.randomizer);
        for kappa in 0..K {
            out.extend_from_slice(&self.fors.secrets[kappa]);
            for node in &self.fors.paths[kappa] {
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
        let mut fors = ForsOpening { secrets: [[0; N]; K], paths: [[[0; N]; A]; K] };
        for kappa in 0..K {
            fors.secrets[kappa] = take(N).try_into().unwrap();
            for level in 0..A {
                fors.paths[kappa][level] = take(N).try_into().unwrap();
            }
        }
        let counter = u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap());
        let wots = std::array::from_fn(|_| take(N).try_into().unwrap());
        let path = std::array::from_fn(|_| take(N).try_into().unwrap());
        Some(Self { randomizer, fors, counter, wots, path })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VerifyError {
    /// The counter does not encode the FORS key into a codeword.
    InadmissibleEncoding,
    RootMismatch,
}

/// The message digest's first call: the leaf index lives in its low `h` bits.
pub fn digest_block(pp: &PublicParam, root: &Digest, rho: &Randomizer, m: &Message, call: u32) -> [u8; 32] {
    hash_full(pp, &tweak(TWEAK_MSG, 0, 0, call, 0), &[rho, root, m])
}

/// The leaf index alone, from the digest's first call (what grinding computes).
pub fn digest_index(pp: &PublicParam, root: &Digest, rho: &Randomizer, m: &Message) -> u64 {
    index_of_block(&digest_block(pp, root, rho, m, 0))
}

pub fn index_of_block(d0: &[u8; 32]) -> u64 {
    u64::from_le_bytes(d0[..8].try_into().unwrap()) & ((1 << H) - 1)
}

/// The message digest: `h + k a = 266` bits from two calls, read as the leaf index and the `k`
/// FORS indices (little-endian bit order).
pub fn message_digest(pp: &PublicParam, root: &Digest, rho: &Randomizer, m: &Message) -> (u64, [u32; K]) {
    let mut bits = [0u8; 64];
    bits[..32].copy_from_slice(&digest_block(pp, root, rho, m, 0));
    bits[32..].copy_from_slice(&digest_block(pp, root, rho, m, 1));
    let field = |offset: usize, len: usize| {
        (0..len).fold(0u64, |value, bit| {
            let position = offset + bit;
            value | (u64::from(bits[position / 8] >> (position % 8) & 1) << bit)
        })
    };
    (field(0, H), std::array::from_fn(|kappa| field(H + kappa * A, A) as u32))
}

pub fn xmss_node(pp: &PublicParam, level: usize, j: u64, left: &Digest, right: &Digest) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, 0, 0, level as u32, j as u32), &[*left, *right])
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
    let public_param = th(&[0; PUBLIC_PARAM_LEN], &tweak(TWEAK_PARAMETER, 0, 0, 0, 0), seed);
    let s = if b == H { 0 } else { u64::from_le_bytes(public_param[..8].try_into().unwrap()) & ((1 << (H - b)) - 1) };
    let leaves = (0..1u64 << b)
        .map(|j| {
            let e = ((s << b) + j) as u32;
            wots_leaf_hash(&public_param, e, &wots_ends(&public_param, seed, e))
        })
        .collect();
    let surrogates = (b..H).map(|level| th(&public_param, &tweak(TWEAK_SURROGATE, 0, 0, level as u32, 0), seed)).collect();
    let tree = XmssTree::from_leaves(&public_param, b, s, leaves, surrogates);
    let sk = SecretKey { public_param, master: *seed, tree };
    let pk = sk.public_key();
    (sk, pk)
}

/// The randomizer of attempt `ctr`: `Th(P, tw_rand(ctr), S | m)`.
pub fn randomizer(pp: &PublicParam, master: &MasterSecret, m: &Message, ctr: u32) -> Randomizer {
    let mut payload = [0u8; MASTER_SECRET_LEN + MESSAGE_LEN];
    payload[..MASTER_SECRET_LEN].copy_from_slice(master);
    payload[MASTER_SECRET_LEN..].copy_from_slice(m);
    th(pp, &tweak(TWEAK_RANDOMIZER, 0, 0, ctr, 0), &payload)
}

/// `Sign`: grind the randomizer into the kept subtree (immediate for a full key), open FORS, sign
/// its key with WOTS+C.
pub fn sign(sk: &SecretKey, m: &Message) -> Signature {
    let (pp, root) = (&sk.public_param, &sk.tree.root);
    let rho = (0u32..)
        .map(|ctr| randomizer(pp, &sk.master, m, ctr))
        .find(|rho| sk.tree.contains(digest_index(pp, root, rho, m)))
        .unwrap();
    let (idx, u) = message_digest(pp, root, &rho, m);
    let forest = ForsForest::from_leaves(pp, idx, &fors_leaves(pp, &sk.master, idx));
    let fors = ForsOpening {
        secrets: std::array::from_fn(|kappa| fors_secret(pp, &sk.master, idx, kappa, u[kappa] as usize)),
        paths: forest.paths(&u),
    };
    let (counter, wots) = wots_sign(pp, &sk.master, idx as u32, &forest.key).expect("no admissible WOTS+C encoding");
    Signature { randomizer: rho, fors, counter, wots, path: sk.tree.path(idx) }
}

/// `Ver`.
pub fn verify(pk: &PublicKey, m: &Message, sig: &Signature) -> Result<(), VerifyError> {
    let pp = &pk.public_param;
    let (idx, u) = message_digest(pp, &pk.root, &sig.randomizer, m);
    let fors_key = fors_recover(pp, idx, &u, &sig.fors);
    let leaf = wots_recover(pp, idx as u32, &fors_key, sig.counter, &sig.wots).ok_or(VerifyError::InadmissibleEncoding)?;
    if tree_fold(pp, idx, leaf, &sig.path) == pk.root { Ok(()) } else { Err(VerifyError::RootMismatch) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(x: u8) -> MasterSecret {
        std::array::from_fn(|i| x.wrapping_mul(31).wrapping_add(i as u8))
    }

    #[test]
    fn sizes() {
        assert_eq!(SIG_SIZE, 5684);
        assert_eq!(PUB_KEY_SIZE, 32);
    }

    #[test]
    fn pruned_sign_verify_and_costs() {
        for b in [3usize, 12] {
            let before = compressions();
            let (sk, pk) = key_gen(&seed(b as u8), b);
            let keygen = compressions() - before;
            // P, the kept subtree (273 per WOTS leaf plus the nodes), and a derivation and a node per surrogate.
            assert_eq!(keygen, 1 + (1u64 << b) * 273 + ((1u64 << b) - 1) + 2 * (H - b) as u64);
            for t in 0..3u8 {
                let m: Message = std::array::from_fn(|i| t ^ i as u8);
                let sig = sign(&sk, &m);
                let bytes = sig.to_bytes();
                assert_eq!(bytes.len(), SIG_SIZE);
                assert_eq!(Signature::from_bytes(&bytes).unwrap(), sig);
                let before = compressions();
                assert_eq!(verify(&pk, &m, &sig), Ok(()));
                assert_eq!(compressions() - before, VERIFY_COMPRESSIONS, "verification is constant");
                let mut other = m;
                other[0] ^= 1;
                assert!(verify(&pk, &other, &sig).is_err());
                let mut bad = sig.clone();
                bad.fors.secrets[3][0] ^= 1;
                assert!(verify(&pk, &m, &bad).is_err());
            }
        }
    }

    #[test]
    fn wots_encoding_takes_about_829_tries() {
        let pp = [7u8; PUBLIC_PARAM_LEN];
        let tries: u64 = (0..200u32).map(|e| u64::from(wots_encode(&pp, e, &[e as u8; N]).unwrap().0) + 1).sum();
        let mean = tries as f64 / 200.0;
        assert!((400.0..1600.0).contains(&mean), "mean tries {mean}");
    }
}
