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
//! Layers are counted from the bottom. At layer `l`, index `idx` is at position `e = idx >> below(l)`
//! across the layer's trees: tree `e >> h_l` and leaf `e mod 2^(h_l)` in it ([`OtsKey`]). An address
//! carries the layer and the tree, and the leaf or the node index inside the tree.

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
        let forest: ForestOpening = (0..cfg.coords())
            .map(|_| CoordOpening {
                sub: std::array::from_fn(|_| SubOpening {
                    values: std::array::from_fn(|_| take(N).try_into().unwrap()),
                    path: std::array::from_fn(|_| take(N).try_into().unwrap()),
                }),
                top: std::array::from_fn(|_| take(N).try_into().unwrap()),
            })
            .collect();
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
    Midstate::new(pp, &tweak(TWEAK_MSG, 0, 0), &[m, &[0u8; 16][..pp.hash().digest_pad()]])
}

/// The message digest call, `P | address | m | rho`, untruncated. `P` binds the key, so the root is
/// not hashed.
pub fn digest_block(pp: &Pp, rho: &Randomizer, m: &Message) -> [u8; 32] {
    digest_midstate(pp, m).finish(rho)
}

/// The leaf index alone (what grinding computes), for a forest of `coords` coordinates.
pub fn digest_index(pp: &Pp, h: usize, coords: usize, rho: &Randomizer, m: &Message) -> u64 {
    index_of_block(&digest_block(pp, rho, m), h, coords)
}

/// The `bits`-bit field of the digest from bit `offset`, the bits read little endian.
fn digest_field(d: &[u8; 32], offset: usize, bits: usize) -> usize {
    debug_assert!(bits <= 32 && offset + bits <= 256);
    let (start, mut word) = (offset / 8, [0u8; 8]);
    let end = (start + 8).min(32);
    word[..end - start].copy_from_slice(&d[start..end]);
    ((u64::from_le_bytes(word) >> (offset % 8)) & ((1 << bits) - 1)) as usize
}

/// The leaf index: `h` bits from bit [`index_offset`].
pub fn index_of_block(d0: &[u8; 32], h: usize, coords: usize) -> u64 {
    digest_field(d0, index_offset(coords), h) as u64
}

/// Bit offset of the leaf index in the digest: after the `2 coords` codeword indices, children and
/// the `coords` super-children, `26 coords` (208 with `COORDS = 8`).
pub const fn index_offset(coords: usize) -> usize {
    coords * COORD_BITS
}

/// Bit offset of the leaf index with `COORDS` coordinates.
pub const INDEX_OFFSET: usize = index_offset(COORDS);

/// The message digest, one call, its fields packed from bit 0 for a forest of `coords = C`
/// coordinates: the `2C` codeword indices are its first `2C` bytes (byte `2c + j` for sub-tree `j` of
/// coordinate `c`), then the `2C` children (3 bits each, in the order `2c + j`, from bit `16C`), the
/// `C` super-children (4 bits each, from bit `22C`) and the leaf index (from bit `26C`). With
/// `C = 8` these are bits 128, 176 and 208, and no field lies across two 64-bit words.
pub fn message_digest(pp: &Pp, h: usize, coords: usize, rho: &Randomizer, m: &Message) -> (u64, Vec<CoordMark>) {
    let d = digest_block(pp, rho, m);
    let children = 8 * SUBS * coords;
    let supers = children + SUBS * SUB_HEIGHT * coords;
    let marks = (0..coords)
        .map(|c| CoordMark {
            super_child: digest_field(&d, supers + TOP_HEIGHT * c, TOP_HEIGHT),
            child: std::array::from_fn(|j| digest_field(&d, children + SUB_HEIGHT * (SUBS * c + j), SUB_HEIGHT)),
            word: std::array::from_fn(|j| d[SUBS * c + j]),
        })
        .collect();
    (index_of_block(&d, h, coords), marks)
}

/// The node `j` of level `level` (counted from the one-time leaves) of tree `tree` at layer `layer`.
pub fn xmss_node(pp: &Pp, layer: usize, tree: u32, level: usize, j: u64, left: &Digest, right: &Digest) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, level as u32, j as u32).at(layer, tree), &[*left, *right])
}

/// A tree of one layer: its kept subtree's levels and the surrogates above it.
#[derive(Clone, Debug)]
pub struct XmssTree {
    height: usize,
    /// Height of the kept subtree; `b = height` keeps the whole tree.
    b: usize,
    /// The first leaf of the kept subtree.
    start: u64,
    /// The kept subtree, level 0 being its `2^b` leaves.
    levels: Vec<Vec<Digest>>,
    /// The siblings of the path at levels `b..height`, surrogates (no secret below them).
    surrogates: Vec<Digest>,
    root: Digest,
}

impl XmssTree {
    /// `start` must be a multiple of `2^b`.
    pub fn from_leaves(
        pp: &Pp, layer: usize, tree: u32, height: usize, b: usize, start: u64, leaves: Vec<Digest>,
        surrogates: Vec<Digest>,
    ) -> Self {
        assert!(b <= height && start.is_multiple_of(1 << b));
        assert_eq!(leaves.len(), 1 << b);
        assert_eq!(surrogates.len(), height - b);
        let mut levels = vec![leaves];
        for level in 1..=b {
            let below = &levels[level - 1];
            let first = start >> level;
            let up = (0..below.len() / 2)
                .map(|j| xmss_node(pp, layer, tree, level, first + j as u64, &below[2 * j], &below[2 * j + 1]))
                .collect();
            levels.push(up);
        }
        let root = surrogates.iter().enumerate().fold(levels[b][0], |node, (t, sibling)| {
            let level = b + t;
            let j = start >> level;
            let (left, right) = if j & 1 == 0 { (node, *sibling) } else { (*sibling, node) };
            xmss_node(pp, layer, tree, level + 1, j >> 1, &left, &right)
        });
        Self { height, b, start, levels, surrogates, root }
    }

    pub fn root(&self) -> Digest {
        self.root
    }

    pub fn contains(&self, leaf: u64) -> bool {
        leaf >> self.b == self.start >> self.b
    }

    /// The authentication path of a leaf, which must be kept.
    pub fn path(&self, leaf: u64) -> Vec<Digest> {
        assert!(self.contains(leaf));
        let local = (leaf - self.start) as usize;
        (0..self.height)
            .map(|level| {
                if level < self.b { self.levels[level][(local >> level) ^ 1] } else { self.surrogates[level - self.b] }
            })
            .collect()
    }
}

/// `Tree.fold`: the node the leaf of a one-time key and its path reach.
pub fn tree_fold(pp: &Pp, key: &OtsKey, leaf: Digest, path: &[Digest]) -> Digest {
    let e = u64::from(key.leaf);
    path.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        let (left, right) = if (e >> level) & 1 == 0 { (current, *sibling) } else { (*sibling, current) };
        xmss_node(pp, key.layer, key.tree, level + 1, e >> (level + 1), &left, &right)
    })
}

/// The whole tree of height `height` that holds a one-time key, built from the master secret.
pub fn layer_tree(pp: &Pp, master: &MasterSecret, key: &OtsKey, height: usize) -> XmssTree {
    let leaves = (0..1u32 << height)
        .map(|leaf| wots_leaf(pp, master, &OtsKey { leaf, ..*key }))
        .collect();
    XmssTree::from_leaves(pp, key.layer, key.tree, height, height, 0, leaves, Vec::new())
}

/// A secret key, made by [`key_gen`] only.
#[derive(Clone)]
pub struct SecretKey {
    cfg: Config,
    pp: Pp,
    master: MasterSecret,
    /// The top layer's tree (the only one for a pruned key).
    top: XmssTree,
}

impl SecretKey {
    pub fn cfg(&self) -> &Config {
        &self.cfg
    }

    pub fn pp(&self) -> &Pp {
        &self.pp
    }

    pub fn public_key(&self) -> PublicKey {
        PublicKey { root: self.top.root, public_param: self.pp.bytes() }
    }
}

/// The seed a key is built from, `H(tag | configuration | seed)`: one seed used under two
/// configurations (in particular two pruning heights `b`, or two forests) gives unrelated keys, which
/// share no one-time key and no few-time signature. The configuration is the hash, `h`, the shape and
/// `b`, then the number of coordinates when it is not `COORDS`. One hash, outside the cost model.
pub fn configured_seed(cfg: &Config, seed: &MasterSecret) -> MasterSecret {
    let (shape, b) = match cfg.shape() {
        Shape::Pruned { b } => (0, b),
        Shape::Layered => (1, cfg.h()),
    };
    let hash = HashFn::ALL.iter().position(|&f| f == cfg.hash()).unwrap() as u8;
    let mut input = b"leanSPHINCS seed".to_vec();
    input.extend_from_slice(&[hash, cfg.h() as u8, shape, b as u8]);
    if cfg.coords() != COORDS {
        input.push(cfg.coords() as u8);
    }
    input.extend_from_slice(seed);
    hash_bytes(cfg.hash(), &input)
}

/// `Gen`: the key is built from the configured seed. The public parameter is derived from it; for a
/// pruned key its low bits place the kept subtree, and the surrogates are derived from it. A layered
/// key builds its top layer.
pub fn key_gen(cfg: &Config, seed: &MasterSecret) -> (SecretKey, PublicKey) {
    let seed = &configured_seed(cfg, seed);
    let public_param = th(&Pp::new(cfg.hash(), [0; PUBLIC_PARAM_LEN]), &tweak(TWEAK_PARAMETER, 0, 0), seed);
    let pp = Pp::new(cfg.hash, public_param);
    let layers = cfg.layers();
    let (layer, height, b) = (layers.len() - 1, layers[layers.len() - 1], cfg.kept());
    let s = u64::from_le_bytes(public_param[..8].try_into().unwrap()) & ((1 << (height - b)) - 1);
    let start = s << b;
    let leaves = (0..1u64 << b)
        .map(|j| wots_leaf(&pp, seed, &OtsKey { layer, tree: 0, leaf: (start + j) as u32 }))
        .collect();
    let surrogates = (b..height).map(|level| th(&pp, &tweak(TWEAK_SURROGATE, level as u32, 0), seed)).collect();
    let top = XmssTree::from_leaves(&pp, layer, 0, height, b, start, leaves, surrogates);
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
pub fn forest_key_bytes(key: &[[Digest; 2]]) -> Vec<u8> {
    key.as_flattened().as_flattened().to_vec()
}

/// `Sign`: take the least `i` whose randomizer `R_0 + i * delta` lands in the kept subtree (`i = 0`
/// for a full or layered key), open the forest, sign its key with WOTS+C, then at each layer above
/// sign the root of the tree below. The caller keeps the number of signatures within the limit of the
/// configuration (formal/sphincs/README.md); nothing here counts them.
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
        .find(|rho| sk.top.contains(index_of_block(&digests.finish(rho), cfg.h(), cfg.coords()) >> below_top))
        .unwrap();
    let (idx, marks) = message_digest(pp, cfg.h(), cfg.coords(), &rho, m);
    let forest = Forest::new(pp, &sk.master, idx, cfg.coords());
    let opening = forest.open(pp, idx, &marks);
    let mut message = forest_key_bytes(forest.key());
    let mut signed = Vec::with_capacity(layers.len());
    for (layer, &height) in layers.iter().enumerate() {
        let key = OtsKey::at(layer, height, idx >> cfg.below(layer));
        let (counter, wots) = wots_sign(pp, &sk.master, &key, &message).expect("no admissible WOTS+C encoding");
        let path = if layer == top {
            sk.top.path(u64::from(key.leaf))
        } else {
            let tree = layer_tree(pp, &sk.master, &key, height);
            message = tree.root.to_vec();
            tree.path(u64::from(key.leaf))
        };
        signed.push(LayerSignature { counter, wots, path });
    }
    Signature { randomizer: rho, forest: opening, layers: signed }
}

/// `Ver`. A pruned key's `b` plays no part: the same signature verifies under every `b`, and the
/// verifier cannot tell which limit the signer is under.
pub fn verify(cfg: &Config, pk: &PublicKey, m: &Message, sig: &Signature) -> Result<(), VerifyError> {
    let layers = cfg.layers();
    if sig.forest.len() != cfg.coords()
        || sig.layers.len() != layers.len()
        || sig.layers.iter().zip(&layers).any(|(s, &h)| s.path.len() != h)
    {
        return Err(VerifyError::Malformed);
    }
    let pp = &Pp::new(cfg.hash(), pk.public_param);
    let (idx, marks) = message_digest(pp, cfg.h(), cfg.coords(), &sig.randomizer, m);
    let key = forest_recover(pp, idx, &marks, &sig.forest);
    let mut message = forest_key_bytes(&key);
    for (layer, signed) in sig.layers.iter().enumerate() {
        let key = OtsKey::at(layer, layers[layer], idx >> cfg.below(layer));
        let leaf = wots_recover(pp, &key, &message, signed.counter, &signed.wots)
            .ok_or(VerifyError::InadmissibleEncoding)?;
        message = tree_fold(pp, &key, leaf, &signed.path).to_vec();
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

    /// Every configuration of the note, per hash: a pruned key per height (at `b = max(h / 2, 12)`, so
    /// that key generation and grinding both stay small) and every layered key, the lifetimes `2^24`
    /// and `2^26` with their lighter forests included. A signature has the configuration's size,
    /// verifies at the configuration's cost, and is rejected under another message, a tampered value,
    /// or another public parameter.
    #[test]
    fn every_configuration_signs_and_verifies() {
        for hash in HashFn::ALL {
            let pruned = HEIGHTS.map(|h| Config::new(hash, h, Shape::Pruned { b: (h / 2).max(12) }));
            let layered = UNIFORM.map(|(lifetime, _, _)| Config::uniform(hash, lifetime));
            for cfg in pruned.into_iter().chain(layered) {
                let before = compressions();
                let (sk, pk) = key_gen(&cfg, &seed(cfg.h() as u8 + cfg.coords() as u8));
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

    /// The baseline (Keccak-256, one tree of height 24): 4,244 bytes and 260 permutations, and a
    /// layer adds 1,028 bytes and 73 permutations; a forest coordinate is 352 bytes. The layered
    /// keys of `2^24` and `2^26` (height 24, 6 and 7 coordinates) are pinned with every hash.
    #[test]
    fn sizes_and_verification_costs() {
        let full = keccak(24, 24);
        assert_eq!(full.sig_size(), BASELINE_SIG_SIZE);
        assert_eq!(full.verify_compressions(), BASELINE_VERIFY_PERMUTATIONS);
        let layered = Config::new(HashFn::Keccak256, 24, Shape::Layered);
        assert_eq!(layered, Config::uniform(HashFn::Keccak256, 28));
        assert_eq!(layered.sig_size(), BASELINE_SIG_SIZE + 2 * 1028);
        assert_eq!(layered.verify_compressions(), BASELINE_VERIFY_PERMUTATIONS + 2 * 73);
        for h in HEIGHTS {
            assert_eq!(keccak(h, h).sig_size() + 24 * N, BASELINE_SIG_SIZE + h * N);
        }
        for (lifetime, h, coords) in UNIFORM {
            let layered = Config::uniform(HashFn::Keccak256, lifetime);
            assert_eq!((layered.h(), layered.coords()), (h, coords));
            let heights = layered_heights(h);
            assert_eq!(heights.iter().sum::<usize>(), h);
            assert!(heights.len() == 3 && heights[1] == heights[2] && heights[1] >= 6 && heights[0] <= 12);
            assert_eq!(layered.layers().len(), heights.len());
            assert_eq!(
                layered.sig_size(),
                keccak(h, h).sig_size() + (heights.len() - 1) * LAYER_SIZE - (COORDS - coords) * 352
            );
        }
        let light: Vec<(usize, usize, Vec<u64>)> = [24, 26]
            .map(|lifetime| {
                let cfg = Config::uniform(HashFn::Keccak256, lifetime);
                let costs = HashFn::ALL.map(|hash| Config::uniform(hash, lifetime).verify_compressions());
                (lifetime, cfg.sig_size(), costs.to_vec())
            })
            .to_vec();
        assert_eq!(light, vec![(24, 5596, vec![365, 413, 414]), (26, 5948, vec![385, 437, 437])]);
        let table: Vec<(HashFn, u64, u64)> = HashFn::ALL
            .iter()
            .map(|&hash| {
                (hash, Config::new(hash, 24, Shape::Pruned { b: 24 }).verify_compressions(),
                 Config::new(hash, 24, Shape::Layered).verify_compressions())
            })
            .collect();
        assert_eq!(table, vec![
            (HashFn::Keccak256, 260, 406),
            (HashFn::Blake2s, 296, 460),
            (HashFn::Sha256, 297, 461),
        ]);
    }

    /// Only the heights, the kept subtrees and the lifetimes of the note make a configuration.
    #[test]
    fn unsupported_configurations_are_rejected() {
        for (h, b, ok) in [(24, 11, false), (24, 25, false), (18, 10, false), (21, 21, false), (20, 20, true),
                           (20, 14, true), (22, 22, true), (28, 20, true), (28, 9, false)] {
            assert_eq!(std::panic::catch_unwind(|| keccak(h, b)).is_ok(), ok, "h = {h}, b = {b}");
        }
        for (h, ok) in [(20, false), (22, false), (24, true), (25, false), (26, true), (28, true)] {
            let layered = std::panic::catch_unwind(|| Config::new(HashFn::Keccak256, h, Shape::Layered));
            assert_eq!(layered.is_ok(), ok, "layered h = {h}");
        }
        for (lifetime, ok) in [(22, false), (24, true), (25, false), (26, true), (28, true), (30, true), (32, true), (34, false)] {
            let uniform = std::panic::catch_unwind(|| Config::uniform(HashFn::Keccak256, lifetime));
            assert_eq!(uniform.is_ok(), ok, "uniform 2^{lifetime}");
        }
        assert_eq!(Config::pruned(HashFn::Keccak256, 24, 12), keccak(20, 12));
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
    /// unnoticed.
    #[test]
    fn known_answers() {
        let m: Message = std::array::from_fn(|i| (7 * i) as u8);
        let pinned = [
            (HashFn::Keccak256, "ca5d2198161c54565a817acef82364c483b407ccd90523fd2028c5e231630627",
             "d7bf691134f95dedae162429d13a9c923a073fda901482a1586b573f5534f19b", 14251),
            (HashFn::Blake2s, "0dd21226f6aef081f5e48b2e8a40bb49bf624b042ba32a5b376f524acba3e0e2",
             "b0031d85f007e7442900d524663cf3a3eba73ed482ea29bbe39fcd3187b2ba64", 24021),
            (HashFn::Sha256, "90fc4935641952d106f2310f409c07eca88e97561ea87aa49165698d5742a942",
             "28b64621232af734f83f8f40c40e80af95aa083f02394ec2dbcb5352f02b4759", 20215),
        ];
        for (hash, pk_hex, sig_hex, counter) in pinned {
            // `b = 11` is not in `PRUNED`: a small key, quick to build.
            let cfg = Config { hash, h: 24, shape: Shape::Pruned { b: 11 }, coords: COORDS };
            let (sk, pk) = key_gen(&cfg, &seed(1));
            let sig = sign(&sk, &m);
            let digest = keccak::hash(&sig.to_bytes());
            assert_eq!(hex(&pk.to_bytes()), pk_hex, "{hash:?}");
            assert_eq!(hex(&digest), sig_hex, "{hash:?}");
            assert_eq!(sig.layers[0].counter, counter, "{hash:?}");
        }
        // the layered key of height 24 (8 + 8 + 8), then
        // the layered keys of 2^24 and 2^26
        let layered = [
            (28, "d80e15c31c7b5f466c4dc94b877b4ab03fafb0f593515556c4797f672621c2fc",
             "2efe8485f4c5a9bbb93322706000e9b53797d646c838fb79be7a54af1ec69178"),
            (24, "640752f9dad79be4680e60883f40ef32d60017402305fcecac43c4d39c9e81ae",
             "d4d1aa8bf9a2d65eb32edd6699113b23549c5cc80a0e243999dc0138168342db"),
            (26, "e22dca1b13c8744acb34e74ee71fadf7ef5886fa10066a5b183ad71bdc49cd58",
             "a52a1b4447376b8d7e147671082a762cc462e9527b39727b2042c823a281c0e6"),
        ];
        for (lifetime, pk_hex, sig_hex) in layered {
            let cfg = Config::uniform(HashFn::Keccak256, lifetime);
            let (sk, pk) = key_gen(&cfg, &seed(1));
            let digest = keccak::hash(&sign(&sk, &m).to_bytes());
            assert_eq!(hex(&pk.to_bytes()), pk_hex, "2^{lifetime}");
            assert_eq!(hex(&digest), sig_hex, "2^{lifetime}");
        }
    }

    /// One seed under two configurations gives unrelated keys: two pruning heights, or two heights.
    #[test]
    fn configurations_do_not_share_keys() {
        let a = configured_seed(&keccak(24, 12), &seed(5));
        assert_ne!(a, configured_seed(&keccak(24, 13), &seed(5)));
        assert_ne!(a, configured_seed(&keccak(22, 12), &seed(5)));
        assert_ne!(a, configured_seed(&Config::new(HashFn::Keccak256, 24, Shape::Layered), &seed(5)));
        assert_ne!(a, configured_seed(&Config::new(HashFn::Blake2s, 24, Shape::Pruned { b: 12 }), &seed(5)));
        let layered = UNIFORM.map(|(lifetime, _, _)| configured_seed(&Config::uniform(HashFn::Keccak256, lifetime), &seed(5)));
        let distinct: std::collections::BTreeSet<_> = layered.iter().collect();
        assert_eq!(distinct.len(), UNIFORM.len(), "2^24, 2^26 and 2^28 share the height 24, not the key");
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
            let lands = |rho: &Randomizer| sk.top.contains(digest_index(pp, 24, COORDS, rho, &m));
            let i = (0u32..).find(|&i| lands(&randomizer(&walk, i))).unwrap();
            let sig = sign(&sk, &m);
            assert_eq!(sig.randomizer, randomizer(&walk, i));
            if i > 0 {
                let previous = u128::from_le_bytes(sig.randomizer).wrapping_sub(u128::from_le_bytes(walk.step));
                assert_eq!(previous.to_le_bytes(), randomizer(&walk, i - 1));
                assert_ne!(previous, u128::from_le_bytes(sig.randomizer).wrapping_sub(1));
            }
        }
        let (sk, _) = key_gen(&Config::uniform(HashFn::Sha256, 24), &seed(4));
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
                let index = index_of_block(&digests.finish(&randomizer(&walk, i)), 24, COORDS);
                assert_eq!(compressions() - before, 1, "{hash:?}");
                assert_eq!(index, digest_index(&pp, 24, COORDS, &randomizer(&walk, i), &m));
            }
        }
    }

    /// Pins the byte order of the randomizer derivation and of the digest, and the walk.
    #[test]
    fn randomizer_and_digest_inputs() {
        let pp = Pp::new(HashFn::Keccak256, [3u8; PUBLIC_PARAM_LEN]);
        let m = [5u8; MESSAGE_LEN];
        let walk = randomizer_walk(&pp, &seed(2), &m);
        let input = [&pp.bytes()[..], &address(&tweak(TWEAK_RANDOMIZER, 0, 0)), &seed(2), &m].concat();
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
        let input = [&pp.bytes()[..], &address(&tweak(TWEAK_MSG, 0, 0)), &m, &rho].concat();
        assert_eq!(input.len(), 80, "one block");
        assert_eq!(digest_block(&pp, &rho, &m), keccak::hash(&input));
        // BLAKE2s: `P | A | m` is one block, the randomizer alone in the second; SHA-256: the block
        // of `P`, then `A | m | 0^16`, then the randomizer.
        let blake = Pp::new(HashFn::Blake2s, pp.bytes());
        assert_eq!(digest_block(&blake, &rho, &m), blake2s::hash(&input));
        let sha = Pp::new(HashFn::Sha256, pp.bytes());
        let input = [&pp.bytes()[..], &[0; 48], &address(&tweak(TWEAK_MSG, 0, 0)), &m, &[0; 16], &rho].concat();
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
            let (index, _) = message_digest(&pp, h, COORDS, &rho, &m);
            assert_eq!(index, word(3) >> 16 & ((1 << h) - 1));
            assert!(INDEX_OFFSET % 64 + h <= 64, "the index lies across two words");
        }
        let (_, marks) = message_digest(&pp, 24, COORDS, &rho, &m);
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
        // With fewer coordinates the fields are packed the same way from bit 0, read bit by bit here.
        let bit = |i: usize| (d[i / 8] >> (i % 8) & 1) as usize;
        let field = |at: usize, bits: usize| (0..bits).map(|k| bit(at + k) << k).sum::<usize>();
        for coords in [6, 7] {
            let (index, marks) = message_digest(&pp, 24, coords, &rho, &m);
            assert_eq!(index as usize, field(26 * coords, 24), "{coords} coordinates");
            assert_eq!(marks.len(), coords);
            for (c, mark) in marks.iter().enumerate() {
                assert_eq!(mark.super_child, field(22 * coords + 4 * c, 4));
                for j in 0..SUBS {
                    assert_eq!(mark.child[j], field(16 * coords + 3 * (2 * c + j), 3));
                    assert_eq!(mark.word[j], d[2 * c + j]);
                }
            }
            assert!(digest_bits(24, coords) <= 256);
        }
    }

    /// Pins the encoding's input, `P | A(enc, 0, e) | message | counter`, and its costs: the
    /// verifier pays the whole input, the signer the whole blocks once and 1 per counter, for the
    /// forest key at the bottom and for a 16-byte root above.
    #[test]
    fn encoding_absorbs_the_message_and_the_counter() {
        let key: ForestKey = (0..COORDS).map(|c| std::array::from_fn(|half| [(2 * c + half) as u8; N])).collect();
        let pp = Pp::new(HashFn::Keccak256, [3u8; PUBLIC_PARAM_LEN]);
        let input = [&pp.bytes()[..], &address(&tweak(TWEAK_ENC, 0, 77)), &forest_key_bytes(&key), &5u32.to_le_bytes()].concat();
        assert_eq!(input.len(), 292);
        assert_eq!(encode(&pp, &OtsKey { layer: 0, tree: 0, leaf: 77 }, &forest_key_bytes(&key), 5), codeword(keccak::hash(&input)[..N].try_into().unwrap()));
        for hash in HashFn::ALL {
            let pp = Pp::new(hash, [3u8; PUBLIC_PARAM_LEN]);
            for (layer, message) in [(0, forest_key_bytes(&key)), (1, vec![9u8; N])] {
                let ots = OtsKey { layer, tree: 3, leaf: 77 };
                let before = compressions();
                let expected = encode(&pp, &ots, &message, 5);
                assert_eq!(compressions() - before, hash.call(message.len() + COUNTER_LEN));
                let before = compressions();
                let state = encoding_midstate(&pp, &ots, &message);
                assert_eq!(compressions() - before, ((hash.prefix() + message.len()) / hash.block()) as u64);
                let before = compressions();
                assert_eq!(encode_from(&state, 5), expected);
                assert_eq!(compressions() - before, 1, "one compression per counter, {hash:?}");
            }
        }
    }

    #[test]
    fn wots_encoding_takes_about_14670_tries() {
        let pp = Pp::new(HashFn::Keccak256, [7u8; PUBLIC_PARAM_LEN]);
        let tries: u64 = (0..100u32)
            .map(|e| u64::from(wots_encode(&pp, &OtsKey { layer: 0, tree: 0, leaf: e }, &[e as u8; 256]).unwrap().0) + 1)
            .sum();
        let mean = tries as f64 / 100.0;
        assert!((7300.0..29300.0).contains(&mean), "mean tries {mean}");
    }
}
