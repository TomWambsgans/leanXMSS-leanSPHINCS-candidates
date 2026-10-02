//! An operator's secrets and the derivations shared by the protocols.
//!
//! There is no secret key: four seeds `k_0..k_3`, seed `k_t` known to every operator but `t`. Every
//! secret of the key (WOTS chain start, FORS secret) is `Th(P, tw, k_0) ^ ... ^ Th(P, tw, k_3)` for its
//! scheme tweak `tw`; the randomizer seed and the next instance are the same XOR over a tagged hash of
//! the seeds and public data. Any 3 operators hold all seeds; one operator misses its own.

use mpc::engine::Shares;
use sphincs::*;

pub type Seed = [u8; 32];

/// Tags of the threshold derivations (`p` field of a [`TWEAK_THRESHOLD`] tweak).
pub const TAG_MSG: u32 = 0;
pub const TAG_NEXT: u32 = 1;
pub const TAG_RAND: u32 = 2;

/// The data of the randomizer seed's terms: `H(m | s)`, binding the message and the request's `s`.
pub fn msg_data(m: &Message, s: &[u8; 32]) -> [u8; 32] {
    let mut h = blake2s::Hasher::new();
    h.update(b"r0-data").update(m).update(s);
    h.finalize()
}

/// What a key's operators all know, after the DKG.
#[derive(Clone)]
pub struct KeyState {
    pub pk: PublicKey,
    pub tree: XmssTree,
    /// The 64 public chain ends of every kept leaf.
    pub ends: Vec<[Digest; V]>,
}

/// A FORS instance computed in MPC, with the WOTS signature of its key (public data).
#[derive(Clone)]
pub struct Instance {
    pub forest: std::sync::Arc<ForsForest>,
    pub counter: u32,
    pub wots: [Digest; V],
}

/// How the signature's instance is chosen.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mode {
    /// Grind into the kept subtree, then compute the selected instance in MPC.
    Vanilla,
    /// Grind until the message lands on the instance computed in advance.
    Preprocessed,
}

/// The current signature request, from the moment its randomizer seed `s` is agreed: its `R0` may
/// be open, so it is finished, with this `s`, before any other request. Once `done`, it is kept so
/// that this operator still vouches for `s` if the request is run again (some other operator may
/// have aborted before finishing): a rerun gives the same signature (with the same instance) and
/// changes nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pending {
    pub m: Message,
    pub mode: Mode,
    pub s: [u8; 32],
    pub done: bool,
}

impl Pending {
    pub fn blocks(&self, m: &Message, mode: Mode) -> bool {
        !self.done && (self.m, self.mode) != (*m, mode)
    }
}

/// A preprocessed instance: its leaf, the instance, and the randomizer it was drawn from.
#[derive(Clone)]
pub struct Next {
    pub idx: u64,
    pub inst: Instance,
    pub from: Randomizer,
}

/// An operator's secrets and state, kept across protocol runs (in memory only: a deployment must
/// persist `pending`, `last`, `next` and `used` before acting on them).
#[derive(Clone)]
pub struct Operator {
    pub id: usize,
    pub(crate) seeds: [Option<Seed>; 4],
    pub key: Option<KeyState>,
    /// The randomizer of the last finished signature (the root before the first): it draws the
    /// next preprocessed instance.
    pub last: Option<Randomizer>,
    /// The preprocessed next instance, checked by this operator, and consumed by the next
    /// preprocessed signature.
    pub next: Option<Next>,
    /// The instance of this operator's last finished preprocessed signature, for reruns of it.
    pub used: Option<Next>,
    /// The current request (see [`Pending`]).
    pub pending: Option<Pending>,
    /// The randomizers that drew a preprocessed instance already used by a signature (they never
    /// repeat, so a stale instance can't be used twice).
    pub consumed: Vec<Randomizer>,
    /// Test record: the randomizer each signing attempt computed.
    #[cfg(test)]
    pub seen_r: Vec<Randomizer>,
}

impl Operator {
    pub fn new(id: usize) -> Self {
        Self {
            id,
            seeds: [None; 4],
            key: None,
            last: None,
            next: None,
            used: None,
            pending: None,
            consumed: vec![],
            #[cfg(test)]
            seen_r: vec![],
        }
    }

    pub(crate) fn seed(&self, t: usize) -> &Seed {
        self.seeds[t].as_ref().expect("operators don't hold their own seed")
    }

    pub fn key(&self) -> &KeyState {
        self.key.as_ref().expect("no key yet")
    }
}

/// `Th(P, tw, k_t)`: seed `t`'s term of the secret named by `tw`.
pub fn term(pp: &PublicParam, seed: &Seed, tw: &Tweak) -> Digest {
    th(pp, tw, seed)
}

/// Seed `t`'s term of a tagged value of public data (randomizer seed, next instance).
pub fn tagged_term(pp: &PublicParam, seed: &Seed, tag: u32, data: &[u8; 32]) -> Digest {
    let mut payload = [0u8; 64];
    payload[..32].copy_from_slice(seed);
    payload[32..].copy_from_slice(data);
    th(pp, &tweak(TWEAK_THRESHOLD, 0, 0, tag, 0), &payload)
}

/// The three online operators, in order, as MPC parties 0, 1, 2, and the offline one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Roles {
    pub online: [usize; 3],
    pub offline: usize,
}

impl Roles {
    pub fn new(mut online: [usize; 3]) -> Self {
        online.sort();
        let offline = (0..4).find(|o| !online.contains(o)).unwrap();
        Self { online, offline }
    }

    pub fn party(&self, op: usize) -> usize {
        self.online.iter().position(|&o| o == op).expect("not online")
    }

    /// The seeds party `i` combines into its replicated shares: `x_0 = t(o2) ^ t(d)`, `x_1 = t(o0)`,
    /// `x_2 = t(o1)`, party `i` holding `(x_i, x_{i-1})`. Returns `(own seeds, prev seeds)`.
    pub fn share_seeds(&self, i: usize) -> (Vec<usize>, Vec<usize>) {
        let [o0, o1, o2] = self.online;
        let x = [vec![o2, self.offline], vec![o0], vec![o1]];
        (x[i].clone(), x[(i + 2) % 3].clone())
    }

    /// The seed behind MPC key `k_i` (held by parties `i` and `i + 1`): the one party `i + 2` lacks.
    pub fn key_seed(&self, i: usize) -> usize {
        self.online[(i + 2) % 3]
    }
}

impl Operator {
    /// My replicated shares of the secrets `f(seed)` XORed over the four seeds.
    pub(crate) fn shares(&self, roles: &Roles, f: impl Fn(&Seed) -> Digest) -> (Digest, Digest) {
        let (own, prev) = roles.share_seeds(roles.party(self.id));
        let xor = |ts: &[usize]| {
            ts.iter().fold([0u8; N], |mut acc, &t| {
                let v = f(self.seed(t));
                for (a, b) in acc.iter_mut().zip(v) {
                    *a ^= b;
                }
                acc
            })
        };
        (xor(&own), xor(&prev))
    }

    /// My MPC keys for a session: `(k_own, k_prev)`.
    pub(crate) fn mpc_keys(&self, roles: &Roles, session: &[u8; 16]) -> ([u8; 32], [u8; 32]) {
        let i = roles.party(self.id);
        let kdf = |t: usize| {
            let mut h = blake2s::Hasher::new();
            h.update(self.seed(t)).update(b"mpc-key").update(session);
            h.finalize()
        };
        (kdf(roles.key_seed(i)), kdf(roles.key_seed((i + 2) % 3)))
    }
}

/// 16-byte values as 128 bit-vectors over the values (bit `b` of value `k` is bit `k` of vector `b`).
pub fn slice(values: &[Digest]) -> Vec<Vec<u64>> {
    let words = values.len().div_ceil(64);
    let mut out = vec![vec![0u64; words]; 8 * N];
    for (k, v) in values.iter().enumerate() {
        for (b, bits) in out.iter_mut().enumerate() {
            bits[k / 64] |= u64::from((v[b / 8] >> (b % 8)) & 1) << (k % 64);
        }
    }
    out
}

pub fn unslice(bits: &[Vec<u64>], n: usize) -> Vec<Digest> {
    (0..n)
        .map(|k| std::array::from_fn(|byte| (0..8).fold(0u8, |acc, i| acc | ((((bits[8 * byte + i][k / 64] >> (k % 64)) & 1) as u8) << i))))
        .collect()
}

/// Bit-sliced shares of 16-byte values, from per-value `(own, prev)` components.
pub fn sliced_shares(own: &[Digest], prev: &[Digest]) -> Vec<Shares> {
    slice(own).into_iter().zip(slice(prev)).map(|(own, prev)| Shares { own, prev }).collect()
}

/// Values as one long bit-vector (for compact openings).
pub fn pack(values: &[Digest]) -> Vec<u64> {
    let bytes: Vec<u8> = values.concat();
    bytes.chunks(8).map(|c| {
        let mut w = [0u8; 8];
        w[..c.len()].copy_from_slice(c);
        u64::from_le_bytes(w)
    }).collect()
}

pub fn unpack(words: &[u64], n: usize) -> Vec<Digest> {
    let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    (0..n).map(|k| bytes[k * N..(k + 1) * N].try_into().unwrap()).collect()
}
