//! The XMSS layers, the message digest, and `Gen`, `Sign`, `Ver`.
//!
//! A pruned key has one tree of height `h`; it keeps one subtree of height `b` and replaces the
//! `h - b` siblings above it by pseudorandom surrogate nodes, and the signer grinds its randomizer
//! until the leaf index lands in the kept subtree. A full key is the pruned key with `b = h`. The
//! attempts `R_0 + i * delta` step by a secret odd `delta`, so a signature does not tell which
//! randomizers were rejected before it.
//!
//! A layered key is a hypertree: the index `idx` names a leaf of the bottom layer, and at each layer
//! a WOTS+C key signs the message of the layer below (the forest key at the bottom, the root of the
//! tree below above it). The key builds the top layer only; the signer builds the trees below on the
//! way, and takes `R_0` as the randomizer.
//!
//! Layers are counted from the bottom. At layer `l`, the one-time key and the tree nodes are named
//! by their position across the layer's trees: leaf `e = idx >> below(l)`, node `e >> level` at a
//! level of the tree.

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

/// What a signature carries for one layer: the WOTS+C counter, the 64 chain values and the path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayerSignature {
    pub counter: u32,
    pub wots: [Digest; V],
    pub path: Vec<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub randomizer: Randomizer,
    pub forest: ForestOpening,
    /// Bottom layer first.
    pub layers: Vec<LayerSignature>,
}

impl Signature {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
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
        for layer in &self.layers {
            out.extend_from_slice(&layer.counter.to_le_bytes());
            for value in &layer.wots {
                out.extend_from_slice(value);
            }
            for node in &layer.path {
                out.extend_from_slice(node);
            }
        }
        out
    }

    pub fn from_bytes(cfg: &Config, bytes: &[u8]) -> Option<Self> {
        if bytes.len() != cfg.sig_size() {
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
        let layers = cfg
            .layers()
            .iter()
            .map(|&height| LayerSignature {
                counter: u32::from_le_bytes(take(COUNTER_LEN).try_into().unwrap()),
                wots: std::array::from_fn(|_| take(N).try_into().unwrap()),
                path: (0..height).map(|_| take(N).try_into().unwrap()).collect(),
            })
            .collect();
        Some(Self { randomizer, forest, layers })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VerifyError {
    /// The layers or a path do not have the configuration's lengths.
    Malformed,
    /// A counter does not encode its message into a codeword.
    InadmissibleEncoding,
    RootMismatch,
}

/// The state of the digest call after `P | address | m`, and for SHA-256 16 zero bytes. With the
/// randomizer the input is 80 bytes, one block of Keccak-256; with BLAKE2s and SHA-256 the
/// randomizer is alone in the last block. Grinding costs one compression per attempt.
pub fn digest_midstate(pp: &Pp, m: &Message) -> Midstate {
    Midstate::new(pp, &tweak(TWEAK_MSG, 0, 0), &[m, &[0u8; 16][..pp.hash.digest_pad()]])
}

/// The message digest call, `P | address | m | rho`, untruncated. `P` binds the key, so the root is
/// not hashed.
pub fn digest_block(pp: &Pp, rho: &Randomizer, m: &Message) -> [u8; 32] {
    digest_midstate(pp, m).finish(rho)
}

/// The leaf index alone (what grinding computes).
pub fn digest_index(pp: &Pp, h: usize, rho: &Randomizer, m: &Message) -> u64 {
    index_of_block(&digest_block(pp, rho, m), h)
}

/// The leaf index: `h` bits from bit 208, in the high bits of the last 64-bit word.
pub fn index_of_block(d0: &[u8; 32], h: usize) -> u64 {
    u64::from_le_bytes(d0[24..32].try_into().unwrap()) >> (INDEX_OFFSET - 192) & ((1 << h) - 1)
}

/// Bit offset of the leaf index in the digest: the last 16 bytes carry the 16 children, the 8
/// super-children and then the index.
pub const INDEX_OFFSET: usize = 128 + SUBS * COORDS * SUB_HEIGHT + COORDS * TOP_HEIGHT;

/// The message digest, one call: the 16 codeword indices are its first 16 bytes (byte `2c + j` for
/// sub-tree `j` of coordinate `c`), then the last 16 bytes hold the 16 children (3 bits each, in
/// the order `2c + j`), the 8 super-children (4 bits each, from bit 176) and the leaf index (from
/// bit 208). No field lies across two 64-bit words.
pub fn message_digest(pp: &Pp, h: usize, rho: &Randomizer, m: &Message) -> (u64, [CoordMark; COORDS]) {
    let d = digest_block(pp, rho, m);
    let high = u128::from_le_bytes(d[16..32].try_into().unwrap());
    let field = |offset: usize, bits: usize| ((high >> offset) & ((1u128 << bits) - 1)) as usize;
    let marks = std::array::from_fn(|c| CoordMark {
        super_child: field(SUBS * COORDS * SUB_HEIGHT + TOP_HEIGHT * c, TOP_HEIGHT),
        child: std::array::from_fn(|j| field(SUB_HEIGHT * (SUBS * c + j), SUB_HEIGHT)),
        word: std::array::from_fn(|j| d[SUBS * c + j]),
    });
    (index_of_block(&d, h), marks)
}

/// The node `j` of level `level` (counted from the layer's one-time leaves) at layer `layer`.
pub fn xmss_node(pp: &Pp, layer: usize, level: usize, j: u64, left: &Digest, right: &Digest) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, level as u32, j as u32).layer(layer), &[*left, *right])
}

/// A tree of one layer: its kept subtree's levels and the surrogates above it.
#[derive(Clone, Debug)]
pub struct XmssTree {
    pub layer: usize,
    pub height: usize,
    /// Height of the kept subtree; `b = height` keeps the whole tree.
    pub b: usize,
    /// The first leaf of the kept subtree, across the layer's trees.
    pub start: u64,
    /// The kept subtree, level 0 being its `2^b` leaves.
    levels: Vec<Vec<Digest>>,
    /// The siblings of the path at levels `b..height`, surrogates (no secret below them).
    pub surrogates: Vec<Digest>,
    pub root: Digest,
}

impl XmssTree {
    /// `start` must be a multiple of `2^b`.
    pub fn from_leaves(
        pp: &Pp, layer: usize, height: usize, b: usize, start: u64, leaves: Vec<Digest>, surrogates: Vec<Digest>,
    ) -> Self {
        assert!(b <= height && start.is_multiple_of(1 << b));
        assert_eq!(leaves.len(), 1 << b);
        assert_eq!(surrogates.len(), height - b);
        let mut levels = vec![leaves];
        for level in 1..=b {
            let below = &levels[level - 1];
            let first = start >> level;
            let up = (0..below.len() / 2)
                .map(|j| xmss_node(pp, layer, level, first + j as u64, &below[2 * j], &below[2 * j + 1]))
                .collect();
            levels.push(up);
        }
        let root = surrogates.iter().enumerate().fold(levels[b][0], |node, (t, sibling)| {
            let level = b + t;
            let j = start >> level;
            let (left, right) = if j & 1 == 0 { (node, *sibling) } else { (*sibling, node) };
            xmss_node(pp, layer, level + 1, j >> 1, &left, &right)
        });
        Self { layer, height, b, start, levels, surrogates, root }
    }

    pub fn contains(&self, e: u64) -> bool {
        e >> self.b == self.start >> self.b
    }

    /// The authentication path of leaf `e`, which must be kept.
    pub fn path(&self, e: u64) -> Vec<Digest> {
        assert!(self.contains(e));
        let local = (e - self.start) as usize;
        (0..self.height)
            .map(|level| {
                if level < self.b { self.levels[level][(local >> level) ^ 1] } else { self.surrogates[level - self.b] }
            })
            .collect()
    }
}

/// `Tree.fold`: the node a leaf and its path reach at layer `layer`.
pub fn tree_fold(pp: &Pp, layer: usize, e: u64, leaf: Digest, path: &[Digest]) -> Digest {
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        let (left, right) = if (e >> level) & 1 == 0 { (current, *sibling) } else { (*sibling, current) };
        xmss_node(pp, layer, level + 1, e >> (level + 1), &left, &right)
    })
}

/// The full tree of layer `layer` that holds leaf `e`, built from the master secret.
pub fn layer_tree(pp: &Pp, master: &MasterSecret, layer: usize, height: usize, e: u64) -> XmssTree {
    let start = e >> height << height;
    let leaves = (0..1u64 << height).map(|j| wots_leaf(pp, master, layer, (start + j) as u32)).collect();
    XmssTree::from_leaves(pp, layer, height, height, start, leaves, Vec::new())
}

/// A non-threshold secret key.
#[derive(Clone)]
pub struct SecretKey {
    pub cfg: Config,
    pub pp: Pp,
    pub master: MasterSecret,
    /// The top layer's tree (the only one for a pruned key).
    pub top: XmssTree,
}

impl SecretKey {
    pub fn public_key(&self) -> PublicKey {
        PublicKey { root: self.top.root, public_param: self.pp.bytes }
    }
}

/// `Gen`: the public parameter is derived from the seed; for a pruned key its low bits place the
/// kept subtree, and the surrogates are derived from the seed. A layered key builds its top layer.
pub fn key_gen(cfg: &Config, seed: &MasterSecret) -> (SecretKey, PublicKey) {
    let public_param = th(&Pp::new(cfg.hash, [0; PUBLIC_PARAM_LEN]), &tweak(TWEAK_PARAMETER, 0, 0), seed);
    let pp = Pp::new(cfg.hash, public_param);
    let layers = cfg.layers();
    let (layer, height, b) = (layers.len() - 1, layers[layers.len() - 1], cfg.kept());
    let s = u64::from_le_bytes(public_param[..8].try_into().unwrap()) & ((1 << (height - b)) - 1);
    let start = s << b;
    let leaves = (0..1u64 << b).map(|j| wots_leaf(&pp, seed, layer, (start + j) as u32)).collect();
    let surrogates = (b..height)
        .map(|level| th(&pp, &tweak(TWEAK_SURROGATE, level as u32, 0).layer(layer), seed))
        .collect();
    let top = XmssTree::from_leaves(&pp, layer, height, b, start, leaves, surrogates);
    let sk = SecretKey { cfg: *cfg, pp, master: *seed, top };
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

pub fn randomizer_walk(pp: &Pp, master: &MasterSecret, m: &Message) -> RandomizerWalk {
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

/// The flattened forest key, the message of the bottom layer's WOTS+C key.
pub fn forest_key_bytes(key: &ForestKey) -> Vec<u8> {
    key.as_flattened().as_flattened().to_vec()
}

/// `Sign`: take the least `i` whose randomizer `R_0 + i * delta` lands in the kept subtree (`i = 0`
/// for a full or layered key), open the forest, sign its key with WOTS+C, then at each layer above
/// sign the root of the tree below.
pub fn sign(sk: &SecretKey, m: &Message) -> Signature {
    let (cfg, pp) = (&sk.cfg, &sk.pp);
    let layers = cfg.layers();
    let top = layers.len() - 1;
    let below_top = cfg.below(top);
    // The digest's fixed part is absorbed once, and the randomizers are `R_0 + i * delta`: an
    // attempt costs one compression.
    let (walk, digests) = (randomizer_walk(pp, &sk.master, m), digest_midstate(pp, m));
    let rho = (0u32..)
        .map(|i| randomizer(&walk, i))
        .find(|rho| sk.top.contains(index_of_block(&digests.finish(rho), cfg.h) >> below_top))
        .unwrap();
    let (idx, marks) = message_digest(pp, cfg.h, &rho, m);
    let forest = Forest::new(pp, &sk.master, idx);
    let opening = forest.open(pp, idx, &marks);
    let mut message = forest_key_bytes(&forest.key);
    let mut signed = Vec::with_capacity(layers.len());
    for (layer, &height) in layers.iter().enumerate() {
        let e = idx >> cfg.below(layer);
        let (counter, wots) =
            wots_sign(pp, &sk.master, layer, e as u32, &message).expect("no admissible WOTS+C encoding");
        let path = if layer == top {
            sk.top.path(e)
        } else {
            let tree = layer_tree(pp, &sk.master, layer, height, e);
            message = tree.root.to_vec();
            tree.path(e)
        };
        signed.push(LayerSignature { counter, wots, path });
    }
    Signature { randomizer: rho, forest: opening, layers: signed }
}

/// `Ver`.
pub fn verify(cfg: &Config, pk: &PublicKey, m: &Message, sig: &Signature) -> Result<(), VerifyError> {
    let layers = cfg.layers();
    if sig.layers.len() != layers.len() || sig.layers.iter().zip(&layers).any(|(s, &h)| s.path.len() != h) {
        return Err(VerifyError::Malformed);
    }
    let pp = &Pp::new(cfg.hash, pk.public_param);
    let (idx, marks) = message_digest(pp, cfg.h, &sig.randomizer, m);
    let key = forest_recover(pp, idx, &marks, &sig.forest);
    let mut message = forest_key_bytes(&key);
    for (layer, signed) in sig.layers.iter().enumerate() {
        let e = idx >> cfg.below(layer);
        let leaf = wots_recover(pp, layer, e as u32, &message, signed.counter, &signed.wots)
            .ok_or(VerifyError::InadmissibleEncoding)?;
        message = tree_fold(pp, layer, e, leaf, &signed.path).to_vec();
    }
    if message[..] == pk.root[..] { Ok(()) } else { Err(VerifyError::RootMismatch) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed(x: u8) -> MasterSecret {
        std::array::from_fn(|i| x.wrapping_mul(31).wrapping_add(i as u8))
    }

    fn keccak(h: usize, b: usize) -> Config {
        Config::new(HashFn::Keccak256, h, Shape::Pruned { b })
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The compressions of `Gen`: the parameter (and SHA-256's block of `P` under `P = 0` and under
    /// `P`), the kept subtree of the top layer and a derivation and a node per surrogate.
    fn keygen_compressions(cfg: &Config) -> u64 {
        let c = |payload: usize| cfg.hash.call(payload);
        let sha = 2 * (cfg.hash == HashFn::Sha256) as u64;
        let leaf = (V / 2) as u64 * c(MASTER_SECRET_LEN) + (V * (CHAIN_LEN - 1)) as u64 * c(N) + c(V * N);
        let (b, height) = (cfg.kept(), *cfg.layers().last().unwrap());
        sha + c(MASTER_SECRET_LEN)
            + (1u64 << b) * leaf
            + ((1u64 << b) - 1) * c(2 * N)
            + (height - b) as u64 * (c(MASTER_SECRET_LEN) + c(2 * N))
    }

    /// Every hash, height and shape (pruned at `b = h / 2`, so that key generation and grinding
    /// both stay small, and layered): a signature has the configuration's size, verifies at the
    /// configuration's cost, and is rejected under another message, a tampered value, or another
    /// public parameter.
    #[test]
    fn every_configuration_signs_and_verifies() {
        for hash in HashFn::ALL {
            for h in HEIGHTS {
                for shape in [Shape::Pruned { b: h / 2 }, Shape::Layered] {
                    let cfg = Config::new(hash, h, shape);
                    let before = compressions();
                    let (sk, pk) = key_gen(&cfg, &seed(h as u8));
                    assert_eq!(compressions() - before, keygen_compressions(&cfg), "{cfg:?}");
                    for t in 0..2u8 {
                        let m: Message = std::array::from_fn(|i| t ^ i as u8);
                        let sig = sign(&sk, &m);
                        let bytes = sig.to_bytes();
                        assert_eq!(bytes.len(), cfg.sig_size(), "{cfg:?}");
                        assert_eq!(Signature::from_bytes(&cfg, &bytes).unwrap(), sig);
                        let before = compressions();
                        assert_eq!(verify(&cfg, &pk, &m, &sig), Ok(()), "{cfg:?}");
                        assert_eq!(compressions() - before, cfg.verify_compressions(), "{cfg:?}");
                        let mut other = m;
                        other[0] ^= 1;
                        assert!(verify(&cfg, &pk, &other, &sig).is_err());
                        let mut bad = sig.clone();
                        bad.forest[3].sub[0].values[0][0] ^= 1;
                        assert!(verify(&cfg, &pk, &m, &bad).is_err());
                        for layer in 0..bad.layers.len() {
                            let mut bad = sig.clone();
                            bad.layers[layer].wots[11][5] ^= 4;
                            assert!(verify(&cfg, &pk, &m, &bad).is_err(), "{cfg:?} layer {layer}");
                            let mut bad = sig.clone();
                            bad.layers[layer].path[0][0] ^= 1;
                            assert!(verify(&cfg, &pk, &m, &bad).is_err(), "{cfg:?} layer {layer}");
                        }
                        let mut other = pk;
                        other.public_param[0] ^= 1;
                        assert!(verify(&cfg, &other, &m, &sig).is_err());
                    }
                }
            }
        }
    }

    /// The baseline (Keccak-256, one tree of height 24): 4,244 bytes and 265 permutations, and a
    /// layer adds 1,028 bytes and 78 permutations.
    #[test]
    fn sizes_and_verification_costs() {
        let full = keccak(24, 24);
        assert_eq!(full.sig_size(), BASELINE_SIG_SIZE);
        assert_eq!(full.verify_compressions(), BASELINE_VERIFY_PERMUTATIONS);
        let layered = Config::new(HashFn::Keccak256, 24, Shape::Layered);
        assert_eq!(layered.sig_size(), BASELINE_SIG_SIZE + 2 * 1028);
        assert_eq!(layered.verify_compressions(), BASELINE_VERIFY_PERMUTATIONS + 2 * 78);
        for h in HEIGHTS {
            assert_eq!(keccak(h, h).sig_size() + 24 * N, BASELINE_SIG_SIZE + h * N);
            let layered = Config::new(HashFn::Keccak256, h, Shape::Layered);
            let heights = layered_heights(h);
            assert_eq!(heights.iter().sum::<usize>(), h);
            assert!(heights[1..].iter().all(|&x| x == 6) && heights[0] <= 12);
            assert_eq!(layered.layers().len(), heights.len());
            assert_eq!(layered.sig_size(), keccak(h, h).sig_size() + (heights.len() - 1) * LAYER_SIZE);
        }
        let table: Vec<(HashFn, u64, u64)> = HashFn::ALL
            .iter()
            .map(|&hash| {
                (hash, Config::new(hash, 24, Shape::Pruned { b: 24 }).verify_compressions(),
                 Config::new(hash, 24, Shape::Layered).verify_compressions())
            })
            .collect();
        assert_eq!(table, vec![
            (HashFn::Keccak256, 265, 421),
            (HashFn::Blake2s, 301, 475),
            (HashFn::Sha256, 302, 476),
        ]);
    }

    #[test]
    fn tampered_signatures_are_rejected() {
        let cfg = keccak(24, 10);
        let (sk, pk) = key_gen(&cfg, &seed(9));
        let m: Message = std::array::from_fn(|i| i as u8);
        let sig = sign(&sk, &m);
        assert_eq!(verify(&cfg, &pk, &m, &sig), Ok(()));
        let bytes = sig.to_bytes();
        for len in [0, cfg.sig_size() - 1, cfg.sig_size() + 1] {
            let mut b = bytes.clone();
            b.resize(len, 0);
            assert!(Signature::from_bytes(&cfg, &b).is_none(), "length {len}");
        }
        // Other counters: never accepted, and some encode no codeword at all.
        let mut inadmissible = 0;
        for delta in 1..=40u32 {
            let mut bad = sig.clone();
            bad.layers[0].counter = sig.layers[0].counter.wrapping_add(delta);
            match verify(&cfg, &pk, &m, &bad) {
                Err(VerifyError::InadmissibleEncoding) => inadmissible += 1,
                r => assert_eq!(r, Err(VerifyError::RootMismatch), "counter + {delta}"),
            }
        }
        assert!(inadmissible > 30, "{inadmissible} of 40 altered counters were inadmissible");
        let mut cases: Vec<(&str, Signature)> = Vec::new();
        let mut bad = sig.clone();
        bad.layers[0].path[7][3] ^= 1;
        cases.push(("auth path", bad));
        let mut bad = sig.clone();
        bad.layers[0].path[23][0] ^= 0x80;
        cases.push(("top of the auth path", bad));
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
            assert!(verify(&cfg, &pk, &m, &bad).is_err(), "tampered {what} accepted");
            assert_eq!(Signature::from_bytes(&cfg, &bad.to_bytes()).unwrap(), bad);
        }
        let mut short = sig.clone();
        short.layers[0].path.pop();
        assert_eq!(verify(&cfg, &pk, &m, &short), Err(VerifyError::Malformed));
        // A signature of another configuration of the same key bytes is not accepted.
        let other = Config::new(HashFn::Blake2s, 24, Shape::Pruned { b: 10 });
        assert!(verify(&other, &pk, &m, &sig).is_err());
    }

    /// Pins the key and the signature bytes of one small pruned key per hash, and of a layered
    /// key, so that a change to the addresses, the hash inputs or the serialization cannot pass
    /// unnoticed. The Keccak-256 answer is the one of the one-layer scheme before the toggles.
    #[test]
    fn known_answers() {
        let m: Message = std::array::from_fn(|i| (7 * i) as u8);
        let pinned = [
            (HashFn::Keccak256, "bca067181df522e8f72775a93784f8082e582128e480149accc2ed4f19edcd00",
             "841f5a7f3bdbd25912f955b90384ed999a79cb2cb9db364b0e82be1da59d43c7", 679),
            (HashFn::Blake2s, "5270d92efe366b967f5d32e29509c06af39e809c5482e50b8b8b76a66fab6507",
             "5c4e99695040c60026fd304aa02e4eeeafdfc29772611628de71855ab20291f4", 2702),
            (HashFn::Sha256, "0429ffe2c7415e6d8399b466638aeda26224f5a6c9b31aa0491e564ef67b649e",
             "476faebb68a92bb0aaf42c9319fc77b37b418fd7a939077965838c25ee2669f3", 267),
        ];
        for (hash, pk_hex, sig_hex, counter) in pinned {
            let cfg = Config::new(hash, 24, Shape::Pruned { b: 11 });
            let (sk, pk) = key_gen(&cfg, &seed(1));
            let sig = sign(&sk, &m);
            let digest = keccak::hash(&sig.to_bytes());
            assert_eq!(hex(&pk.to_bytes()), pk_hex, "{hash:?}");
            assert_eq!(hex(&digest), sig_hex, "{hash:?}");
            assert_eq!(sig.layers[0].counter, counter, "{hash:?}");
        }
        let cfg = Config::new(HashFn::Keccak256, 22, Shape::Layered);
        let (sk, pk) = key_gen(&cfg, &seed(1));
        let digest = keccak::hash(&sign(&sk, &m).to_bytes());
        assert_eq!(hex(&pk.to_bytes()), "6de30da455914e574ec62bef3a4cd7032e582128e480149accc2ed4f19edcd00");
        assert_eq!(hex(&digest), "6e92a089a0fce98222cea747cd7ef9598c88546b00e7323694fd745a0aeb4fd0");
    }

    /// The signature's randomizer is the first attempt of the message's walk that lands, and the
    /// attempts before it are not `R - 1, R - 2, ...`. A layered key takes `R_0`.
    #[test]
    fn the_signer_takes_the_first_landing_attempt() {
        let (sk, _) = key_gen(&keccak(24, 10), &seed(4));
        let pp = &sk.pp;
        for t in 0..4u8 {
            let m: Message = std::array::from_fn(|i| t.wrapping_mul(17) ^ i as u8);
            let walk = randomizer_walk(pp, &sk.master, &m);
            assert_eq!(walk.step[0] & 1, 1);
            let lands = |rho: &Randomizer| sk.top.contains(digest_index(pp, 24, rho, &m));
            let i = (0u32..).find(|&i| lands(&randomizer(&walk, i))).unwrap();
            let sig = sign(&sk, &m);
            assert_eq!(sig.randomizer, randomizer(&walk, i));
            if i > 0 {
                let previous = u128::from_le_bytes(sig.randomizer).wrapping_sub(u128::from_le_bytes(walk.step));
                assert_eq!(previous.to_le_bytes(), randomizer(&walk, i - 1));
                assert_ne!(previous, u128::from_le_bytes(sig.randomizer).wrapping_sub(1));
            }
        }
        let (sk, _) = key_gen(&Config::new(HashFn::Sha256, 22, Shape::Layered), &seed(4));
        let m = [3u8; MESSAGE_LEN];
        assert_eq!(sign(&sk, &m).randomizer, randomizer_walk(&sk.pp, &sk.master, &m).base);
    }

    #[test]
    fn a_randomizer_attempt_costs_one_compression() {
        for hash in HashFn::ALL {
            let pp = Pp::new(hash, [3u8; PUBLIC_PARAM_LEN]);
            let m = [5u8; MESSAGE_LEN];
            let before = compressions();
            let (walk, digests) = (randomizer_walk(&pp, &seed(2), &m), digest_midstate(&pp, &m));
            let fixed = (hash.prefix() + MESSAGE_LEN + hash.digest_pad()) / hash.block();
            assert_eq!(compressions() - before, hash.call(MASTER_SECRET_LEN + MESSAGE_LEN) + fixed as u64);
            for i in 0..4 {
                let before = compressions();
                let index = index_of_block(&digests.finish(&randomizer(&walk, i)), 24);
                assert_eq!(compressions() - before, 1, "{hash:?}");
                assert_eq!(index, digest_index(&pp, 24, &randomizer(&walk, i), &m));
            }
        }
    }

    /// Pins the byte order of the randomizer derivation and of the digest, and the walk.
    #[test]
    fn randomizer_and_digest_inputs() {
        let pp = Pp::new(HashFn::Keccak256, [3u8; PUBLIC_PARAM_LEN]);
        let m = [5u8; MESSAGE_LEN];
        let walk = randomizer_walk(&pp, &seed(2), &m);
        let input = [&pp.bytes[..], &address(&tweak(TWEAK_RANDOMIZER, 0, 0)), &seed(2), &m].concat();
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
        assert_eq!(rho, base.wrapping_add(step.wrapping_mul(7)).to_le_bytes(), "R_0 + 7 delta");
        let input = [&pp.bytes[..], &address(&tweak(TWEAK_MSG, 0, 0)), &m, &rho].concat();
        assert_eq!(input.len(), 80, "one block");
        assert_eq!(digest_block(&pp, &rho, &m), keccak::hash(&input));
        // BLAKE2s: `P | A | m` is one block, the randomizer alone in the second; SHA-256: the block
        // of `P`, then `A | m | 0^16`, then the randomizer.
        let blake = Pp::new(HashFn::Blake2s, pp.bytes);
        assert_eq!(digest_block(&blake, &rho, &m), blake2s::hash(&input));
        let sha = Pp::new(HashFn::Sha256, pp.bytes);
        let input = [&pp.bytes[..], &[0; 48], &address(&tweak(TWEAK_MSG, 0, 0)), &m, &[0; 16], &rho].concat();
        assert_eq!(input.len(), 64 + 64 + 16);
        assert_eq!(digest_block(&sha, &rho, &m), sha256::hash(&input));
    }

    /// Pins where the digest's fields are, and that none of them lies across two 64-bit words: the
    /// codeword indices are the first 16 bytes, then the children, the super-children and the index.
    #[test]
    fn digest_fields() {
        let pp = Pp::new(HashFn::Keccak256, [3u8; PUBLIC_PARAM_LEN]);
        let (m, rho) = ([5u8; MESSAGE_LEN], [7u8; N]);
        let d = digest_block(&pp, &rho, &m);
        let word = |w: usize| u64::from_le_bytes(d[8 * w..][..8].try_into().unwrap());
        for h in HEIGHTS {
            let (index, _) = message_digest(&pp, h, &rho, &m);
            assert_eq!(index, word(3) >> 16 & ((1 << h) - 1));
            assert!(INDEX_OFFSET % 64 + h <= 64, "the index lies across two words");
        }
        let (_, marks) = message_digest(&pp, 24, &rho, &m);
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
    }

    /// Pins the encoding's input, `P | A(enc, 0, e) | message | counter`, and its costs: the
    /// verifier pays the whole input, the signer the whole blocks once and 1 per counter, for the
    /// forest key at the bottom and for a 16-byte root above.
    #[test]
    fn encoding_absorbs_the_message_and_the_counter() {
        let key: ForestKey = std::array::from_fn(|c| std::array::from_fn(|half| [(2 * c + half) as u8; N]));
        let pp = Pp::new(HashFn::Keccak256, [3u8; PUBLIC_PARAM_LEN]);
        let input = [&pp.bytes[..], &address(&tweak(TWEAK_ENC, 0, 77)), &forest_key_bytes(&key), &5u32.to_le_bytes()].concat();
        assert_eq!(input.len(), 292);
        assert_eq!(encode(&pp, 0, 77, &forest_key_bytes(&key), 5), codeword(keccak::hash(&input)[..N].try_into().unwrap()));
        for hash in HashFn::ALL {
            let pp = Pp::new(hash, [3u8; PUBLIC_PARAM_LEN]);
            for (layer, message) in [(0, forest_key_bytes(&key)), (1, vec![9u8; N])] {
                let before = compressions();
                let expected = encode(&pp, layer, 77, &message, 5);
                assert_eq!(compressions() - before, hash.call(message.len() + COUNTER_LEN));
                let before = compressions();
                let state = encoding_midstate(&pp, layer, 77, &message);
                assert_eq!(compressions() - before, ((hash.prefix() + message.len()) / hash.block()) as u64);
                let before = compressions();
                assert_eq!(encode_from(&state, 5), expected);
                assert_eq!(compressions() - before, 1, "one compression per counter, {hash:?}");
            }
        }
    }

    #[test]
    fn wots_encoding_takes_about_2197_tries() {
        let pp = Pp::new(HashFn::Keccak256, [7u8; PUBLIC_PARAM_LEN]);
        let tries: u64 = (0..100u32)
            .map(|e| u64::from(wots_encode(&pp, 0, e, &[e as u8; 256]).unwrap().0) + 1)
            .sum();
        let mean = tries as f64 / 100.0;
        assert!((1100.0..4400.0).contains(&mean), "mean tries {mean}");
    }
}
