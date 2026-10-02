//! The trusted dealer that simulates the one-time setup (the paper's `F_Triples`, `F_UV`, `F_Rand`
//! and the authenticated triples of `F_Mul`). It hands each party only that party's material,
//! derived on demand from its master seed; everything after the setup is the real protocol.

use std::sync::atomic::{AtomicBool, Ordering};

use crate::aes::{Prf, Stream};
use crate::auth::{Auth, share, share_bit};
use crate::gf::F;
use crate::mdpf;
use crate::net::{Abort, abort};
use crate::pcg::{self, KeyId, M, Noise, Params};
use crate::ring::F4;

/// The verification variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tier {
    /// LPN-style: every batch has its own noise positions and matrix (`Π^q_Vrfy`).
    Plain,
    /// Stationary syndrome decoding: the batches of a group share the noise positions.
    Ssd,
    /// Doubly stationary: they also share the matrix; the sumcheck (FLIOP) verification.
    Dssd,
}

/// Batches per group under (D)SSD: the paper's 3-party `q = r = 27`. Theorem C.1's rank bound
/// (`c t - r >= (ln r + 45.5) / ln 4`, about 35, at σ = 64 with `c t = 135`) allows `r <= 100`.
pub const GROUP_MAX: usize = 27;

#[derive(Clone, Debug)]
pub struct Config {
    pub pcg: Params,
    pub tier: Tier,
    /// `q`: batches (ring instances) of `2 * 3^n` triples.
    pub batches: usize,
    /// Batches per group: they share the noise positions (SSD) and the matrix (DSSD). 1 for plain,
    /// at most [`GROUP_MAX`].
    pub group: usize,
    /// PIR balancing `b` (plain tier; 1 under (D)SSD).
    pub balance: usize,
    /// Groups whose `F_Mul`s share one round (bounds the memory of the plain and SSD tiers).
    pub chunk: usize,
    pub seed: u128,
    /// The session this one-time setup belongs to, bound into all of its material and messages.
    pub session: u128,
}

impl Config {
    /// A configuration with the largest groups and a fresh session.
    pub fn new(pcg: Params, tier: Tier, batches: usize, seed: u128) -> Self {
        let plain = tier == Tier::Plain;
        Self {
            pcg,
            tier,
            batches,
            group: if plain { 1 } else { batches.min(GROUP_MAX) },
            balance: if plain { 8 } else { 1 },
            chunk: usize::MAX,
            seed,
            session: u128::from_le_bytes(mpc::prf::os_random::<16>()),
        }
    }

    pub fn validate(&self) {
        self.pcg.validate();
        match self.tier {
            Tier::Plain => assert_eq!(self.group, 1, "plain batches stand alone"),
            _ => assert!((1..=GROUP_MAX).contains(&self.group), "(D)SSD groups hold 1 to {GROUP_MAX} batches"),
        }
        assert!(self.batches > 0 && self.balance > 0 && self.chunk > 0);
    }

    pub fn groups(&self) -> usize {
        self.batches.div_ceil(self.group)
    }

    pub fn group_batches(&self, g: usize) -> std::ops::Range<usize> {
        g * self.group..((g + 1) * self.group).min(self.batches)
    }

    /// The public matrix seed of a batch: per batch, or per group (DSSD).
    pub fn matrix_seed(&self, batch: usize) -> u128 {
        let id = if self.tier == Tier::Dssd { batch / self.group } else { batch };
        Prf::labeled(self.seed, &[1, self.session as u64, (self.session >> 64) as u64]).at(id as u64, 0)
    }

    /// Rows of the main FUV domain (a block, balanced).
    pub fn rows(&self) -> usize {
        self.pcg.blk().div_ceil(self.balance)
    }

    pub fn query_code(&self, group: usize, v: usize, b: usize, idx: usize) -> u64 {
        let p = &self.pcg;
        (((group * p.n_vectors() + v) * p.t() + b) * M * M * p.t() + idx) as u64
    }
}

pub struct Dealer {
    pub cfg: Config,
    delta: F,
    delta_sh: [F; M],
    noise: Vec<[Noise; M]>,
    pcg_rng: Prf,
    fuv_rng: Prf,
    pay_rng: Prf,
    fmul_rng: Prf,
    rand_rng: Prf,
    claimed: [AtomicBool; M],
}

/// What a dealer-made random bit-vector word gives one party.
pub struct MaskWord {
    /// The mask in the clear, for its owner.
    pub clear: Option<u64>,
    pub v: u64,
    pub m: [F; 64],
}

impl Dealer {
    pub fn new(cfg: Config) -> Self {
        cfg.validate();
        let p = cfg.pcg;
        let prf = |kind: u64| Prf::labeled(cfg.seed, &[kind, cfg.session as u64, (cfg.session >> 64) as u64]);
        let (pos, val) = (prf(2), prf(3));
        let k = 2 * p.c * p.t();
        // Regular noise: one point per block, nonzero payload, so weight exactly t per polynomial as
        // in FOLEAGE; under (D)SSD the positions are the group's, the payloads the batch's.
        // Definition 2.3 draws (D)SSD payloads from all of F4, which would lower the weight to about
        // 3t/4. Theorem C.1's rank bound holds with nonzero payloads too: a row of c t = 135 iid
        // F4* payloads annihilates a fixed nonzero v in F4^r with probability at most 1/3, so some
        // v exists with probability at most 4^r 3^-135 = 2^-160 at r = 27.
        let noise = (0..cfg.batches)
            .map(|batch| {
                let pos_batch = batch / cfg.group * cfg.group;
                std::array::from_fn(|party| Noise {
                    off: (0..k).map(|i| (pos.at((pos_batch * M + party) as u64, i as u64) % p.blk() as u128) as u32).collect(),
                    val: (0..k).map(|i| 1 + (val.at((batch * M + party) as u64, i as u64) % 3) as u8).collect(),
                })
            })
            .collect();
        let mac = prf(4);
        let delta_sh: [F; M] = std::array::from_fn(|i| F(mac.at(i as u64, 0)));
        Self {
            delta: delta_sh[0] + delta_sh[1] + delta_sh[2],
            delta_sh,
            noise,
            pcg_rng: prf(5),
            fuv_rng: prf(6),
            pay_rng: prf(7),
            fmul_rng: prf(8),
            rand_rng: prf(9),
            claimed: Default::default(),
            cfg,
        }
    }

    /// Hands party `me` its material, once: a second session on the same setup is refused.
    pub fn claim(&self, me: usize) -> Result<(), Abort> {
        if self.claimed[me].swap(true, Ordering::SeqCst) { abort("setup material already used") } else { Ok(()) }
    }

    pub fn mac_key(&self, me: usize) -> F {
        self.delta_sh[me]
    }

    /// A party's own noise (its share of the ST-PCG seed).
    pub fn noise(&self, batch: usize, me: usize) -> Noise {
        self.noise[batch][me].clone()
    }

    fn all_noise(&self, batch: usize) -> [&Noise; M] {
        let n = &self.noise[batch];
        [&n[0], &n[1], &n[2]]
    }

    /// This party's key of a cross-product DPF.
    pub fn pcg_key(&self, batch: usize, me: usize, id: &KeyId) -> crate::dpf::Key {
        let p = &self.cfg.pcg;
        let n = &self.noise[batch];
        let (oe, ve) = n[id.e].get(p, false, id.j, id.be);
        let (of, vf) = n[id.f].get(p, true, id.jp, id.bf);
        let (_, alpha, beta) = pcg::product(p, (id.be, oe, ve), (id.bf, of, vf), id.w);
        let mut rng = Stream::new(self.pcg_rng.at(batch as u64, id.code()));
        let keys = crate::dpf::keygen(p.depth(), p.leaf, alpha, beta, &mut rng);
        keys[usize::from(me == id.f)].clone()
    }

    /// This party's FUV keys for query `idx` of vector `v`, block `b`: the row (domain
    /// [`Config::rows`]) and, when balancing, the column within the row (domain `balance`).
    pub fn fuv_keys(&self, group: usize, v: usize, b: usize, idx: usize, me: usize) -> (mdpf::Key, Option<mdpf::Key>) {
        let cfg = &self.cfg;
        let batch = group * cfg.group;
        let (off, _) = pcg::entry(&cfg.pcg, &self.all_noise(batch), cfg.pcg.vector(v), b, idx);
        let code = cfg.query_code(group, v, b, idx);
        let row = mdpf::keygen(cfg.rows(), off / cfg.balance, self.delta, self.fuv_rng.at(code, 0), me);
        let col = (cfg.balance > 1).then(|| mdpf::keygen(cfg.balance, off % cfg.balance, self.delta, self.fuv_rng.at(code, 1), me));
        (row, col)
    }

    /// This party's authenticated shares of the payload bits of a query in a batch.
    pub fn payload(&self, batch: usize, v: usize, b: usize, idx: usize, me: usize) -> [Auth; 2] {
        let cfg = &self.cfg;
        let (_, val): (usize, F4) = pcg::entry(&cfg.pcg, &self.all_noise(batch), cfg.pcg.vector(v), b, idx);
        let code = cfg.query_code(batch, v, b, idx);
        [0, 1].map(|s| share_bit(u64::from(val >> s), self.delta, [0, 1, 2, 3].map(|k| self.pay_rng.at(code, 4 * s + k)), me))
    }

    /// This party's shares of authenticated multiplication triple `idx`.
    pub fn fmul(&self, idx: u64, me: usize) -> [Auth; 3] {
        let r = |k: u64| self.fmul_rng.at(idx, k);
        let (a, b) = (F(r(0)), F(r(1)));
        [(a, 2), (b, 6), (a * b, 10)].map(|(x, k)| share(x, self.delta, [r(k), r(k + 1), r(k + 2), r(k + 3)], me))
    }

    /// A word of 64 authenticated random bits (`F_Rand`), `kind` separating the uses; its owner,
    /// if any, also gets it in the clear.
    pub fn mask_word(&self, kind: u64, idx: u64, owner: Option<usize>, me: usize) -> MaskWord {
        let code = kind << 56 | idx;
        let base = self.rand_rng.at(code, 0);
        let (v0, v1, x) = (base as u64, (base >> 64) as u64, self.rand_rng.at(code, 1) as u64);
        let v = [v0, v1, x ^ v0 ^ v1][me];
        let m = std::array::from_fn(|l| {
            let bit = (x >> l) & 1;
            let r = [0, 1, 2, 3].map(|k| self.rand_rng.at(code, 2 + 4 * l as u64 + k));
            share_bit(bit, self.delta, r, me).m
        });
        MaskWord { clear: (owner == Some(me)).then_some(x), v, m }
    }

    /// An authenticated random element of F̂ (`F_Rand`).
    pub fn rand(&self, kind: u64, idx: u64, me: usize) -> Auth {
        let code = kind << 56 | idx;
        let x = F(self.rand_rng.at(code, 0));
        share(x, self.delta, [1, 2, 3, 4].map(|k| self.rand_rng.at(code, k)), me)
    }
}
