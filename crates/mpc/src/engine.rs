//! One party of a 3-party session: bit-sliced evaluation, AND gates by Araki et al., openings.
//!
//! Party `i` holds `(x_i, x_{i-1})` of every secret `x = x_0 ^ x_1 ^ x_2`, and two PRF keys:
//! `k_i` (shared with party `i + 1`) and `k_{i-1}` (shared with party `i - 1`). An AND of `u` and
//! `v` sends `z_i = u_i v_i ^ u_i v_{i-1} ^ u_{i-1} v_i ^ rho_i ^ rho_{i-1}` to party `i + 1`,
//! `rho_j = F(k_j, gate)`, and the output share is `(z_i, z_{i-1})`.
//!
//! Every AND is recorded until [`Party::verify`] (BGIN19) has checked all of them; [`Party::open`]
//! refuses to run before that.

use crate::circuit::{Op, Program};
use crate::net::{Abort, Link, abort};
use crate::prf::{Key, Tag, prf_words, tag};

/// A party's share of one secret bit-vector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shares {
    pub own: Vec<u64>,
    pub prev: Vec<u64>,
}

/// Transcript fields of one AND gate, per 64 instances.
pub(crate) const U_OWN: usize = 0;
pub(crate) const U_PREV: usize = 1;
pub(crate) const V_OWN: usize = 2;
pub(crate) const V_PREV: usize = 3;
pub(crate) const Z_OWN: usize = 4;
pub(crate) const Z_PREV: usize = 5;
pub(crate) const RHO_OWN: usize = 6;
pub(crate) const RHO_PREV: usize = 7;

/// The ANDs not yet verified: `data[and * words + w]` holds the eight fields of word `w`.
#[derive(Default)]
pub(crate) struct Transcript {
    pub data: Vec<[u64; 8]>,
    pub n_and: usize,
}

/// Test hooks for a cheating party.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Cheat {
    #[default]
    Honest,
    /// Flip bit `bit` of the `and`-th AND message sent; if `consistent`, also use the flipped value
    /// everywhere else (own output share, own transcript), as a prover covering its tracks would.
    FlipAnd { and: usize, bit: usize, consistent: bool },
}

pub struct Party {
    pub id: usize,
    pub link: Link,
    pub(crate) k_own: Key,
    pub(crate) k_prev: Key,
    pub(crate) session: [u8; 16],
    /// Instances in the batch, and 64-bit words per bit-vector.
    pub n: usize,
    pub words: usize,
    tail: u64,
    pub(crate) transcript: Transcript,
    /// ANDs evaluated in this session so far: the PRF index of the next one.
    ands_done: u64,
    pub(crate) verifications: u64,
    /// Worker threads for the heavy verification passes.
    pub threads: usize,
    pub cheat: Cheat,
}

impl Party {
    /// `k_own` is shared with the next party, `k_prev` with the previous one; `session` must be
    /// fresh for every session (it separates all PRF streams).
    pub fn new(link: Link, k_own: Key, k_prev: Key, session: [u8; 16], n: usize) -> Self {
        assert!(n > 0);
        let tail = if n.is_multiple_of(64) { u64::MAX } else { (1u64 << (n % 64)) - 1 };
        let threads = std::thread::available_parallelism().map_or(1, |p| p.get()).div_ceil(3).max(1);
        Self {
            id: link.id,
            link,
            k_own,
            k_prev,
            session,
            n,
            words: n.div_ceil(64),
            tail,
            transcript: Transcript::default(),
            ands_done: 0,
            verifications: 0,
            threads,
            cheat: Cheat::Honest,
        }
    }

    /// Switches to batches of `n` instances; the ANDs so far must be verified.
    pub fn set_n(&mut self, n: usize) {
        assert!(n > 0 && self.transcript.n_and == 0, "verify before changing the batch size");
        self.n = n;
        self.words = n.div_ceil(64);
        self.tail = if n.is_multiple_of(64) { u64::MAX } else { (1u64 << (n % 64)) - 1 };
    }

    fn mask(&self, v: &mut [u64]) {
        if let Some(last) = v.last_mut() {
            *last &= self.tail;
        }
    }

    /// Shares of a public bit-vector: it is `x_0`, held by party 0 (own) and party 1 (prev).
    pub fn share_public(&self, value: &[u64]) -> Shares {
        let zero = vec![0u64; self.words];
        match self.id {
            0 => Shares { own: value.to_vec(), prev: zero },
            1 => Shares { own: zero, prev: value.to_vec() },
            _ => Shares { own: zero.clone(), prev: zero },
        }
    }

    /// Evaluates `prog` on public inputs (bit-vectors) and secret inputs (shares).
    pub fn eval(&mut self, prog: &Program, pub_in: &[Vec<u64>], sec_in: &[Shares]) -> Result<Vec<Shares>, Abort> {
        assert_eq!(pub_in.len(), prog.n_pub_inputs);
        assert_eq!(sec_in.len(), prog.n_sec_inputs);
        let w = self.words;
        let mut pubs = vec![0u64; prog.n_pub_slots * w];
        let mut own = vec![0u64; prog.n_sec_slots * w];
        let mut prev = vec![0u64; prog.n_sec_slots * w];
        let ones: Vec<u64> = {
            let mut v = vec![u64::MAX; w];
            self.mask(&mut v);
            v
        };
        let rho_tag = tag(&self.session, b"rho");
        for step in &prog.steps {
            for op in &step.local {
                let r = |slot: u32| slot as usize * w..(slot as usize + 1) * w;
                match *op {
                    Op::PubIn { dst, input } => {
                        pubs[r(dst)].copy_from_slice(&pub_in[input as usize]);
                        let d = &mut pubs[r(dst)];
                        if let Some(last) = d.last_mut() {
                            *last &= self.tail;
                        }
                    }
                    Op::SecIn { dst, input } => {
                        own[r(dst)].copy_from_slice(&sec_in[input as usize].own);
                        prev[r(dst)].copy_from_slice(&sec_in[input as usize].prev);
                        for v in [&mut own[r(dst)], &mut prev[r(dst)]] {
                            if let Some(last) = v.last_mut() {
                                *last &= self.tail;
                            }
                        }
                    }
                    Op::PubXor { dst, a, b } => binop(&mut pubs, w, dst, a, b, |x, y| x ^ y),
                    Op::PubAnd { dst, a, b } => binop(&mut pubs, w, dst, a, b, |x, y| x & y),
                    Op::PubNot { dst, a } => {
                        for k in 0..w {
                            pubs[dst as usize * w + k] = pubs[a as usize * w + k] ^ ones[k];
                        }
                    }
                    Op::SecXor { dst, a, b } => {
                        binop(&mut own, w, dst, a, b, |x, y| x ^ y);
                        binop(&mut prev, w, dst, a, b, |x, y| x ^ y);
                    }
                    Op::SecXorPub { dst, a, p } => {
                        copy_slot(&mut own, w, dst, a);
                        copy_slot(&mut prev, w, dst, a);
                        // The public value is x_0: party 0's own component, party 1's prev component.
                        let target = match self.id {
                            0 => Some(&mut own),
                            1 => Some(&mut prev),
                            _ => None,
                        };
                        if let Some(t) = target {
                            for k in 0..w {
                                t[dst as usize * w + k] ^= pubs[p as usize * w + k];
                            }
                        }
                    }
                    Op::SecNot { dst, a } => {
                        copy_slot(&mut own, w, dst, a);
                        copy_slot(&mut prev, w, dst, a);
                        let target = match self.id {
                            0 => Some(&mut own),
                            1 => Some(&mut prev),
                            _ => None,
                        };
                        if let Some(t) = target {
                            for k in 0..w {
                                t[dst as usize * w + k] ^= ones[k];
                            }
                        }
                    }
                    Op::SecAndPub { dst, a, p } => {
                        for k in 0..w {
                            let pk = pubs[p as usize * w + k];
                            own[dst as usize * w + k] = own[a as usize * w + k] & pk;
                            prev[dst as usize * w + k] = prev[a as usize * w + k] & pk;
                        }
                    }
                }
            }
            if step.ands.is_empty() {
                continue;
            }
            // All products first (outputs may reuse input slots), then one round.
            let first_record = self.transcript.data.len();
            let mut msg = Vec::with_capacity(step.ands.len() * w * 8);
            let (mut rho_own, mut rho_prev) = (vec![0u64; w], vec![0u64; w]);
            for (j, g) in step.ands.iter().enumerate() {
                let index = self.ands_done + j as u64;
                prf_words(&self.k_own, &rho_tag, index, &mut rho_own);
                prf_words(&self.k_prev, &rho_tag, index, &mut rho_prev);
                self.mask(&mut rho_own);
                self.mask(&mut rho_prev);
                let flip = match self.cheat {
                    Cheat::FlipAnd { and, bit, consistent } if and == self.transcript.n_and + j => Some((bit % self.n, consistent)),
                    _ => None,
                };
                for k in 0..w {
                    let (ao, ap) = (own[g.a as usize * w + k], prev[g.a as usize * w + k]);
                    let (bo, bp) = (own[g.b as usize * w + k], prev[g.b as usize * w + k]);
                    let mut z = (ao & bo) ^ (ao & bp) ^ (ap & bo) ^ rho_own[k] ^ rho_prev[k];
                    let mut recorded = z;
                    if let Some((bit, consistent)) = flip
                        && bit / 64 == k
                    {
                        z ^= 1 << (bit % 64);
                        if consistent {
                            recorded = z;
                        }
                    }
                    msg.extend_from_slice(&z.to_le_bytes());
                    self.transcript.data.push([ao, ap, bo, bp, recorded, 0, rho_own[k], rho_prev[k]]);
                }
            }
            let (from_prev, _) = self.link.exchange(vec![], msg)?;
            if from_prev.len() != step.ands.len() * w * 8 {
                return abort("malformed AND message");
            }
            for (j, g) in step.ands.iter().enumerate() {
                for k in 0..w {
                    let at = (j * w + k) * 8;
                    let mut z_prev = u64::from_le_bytes(from_prev[at..at + 8].try_into().unwrap());
                    if k + 1 == w {
                        z_prev &= self.tail;
                    }
                    let rec = &mut self.transcript.data[first_record + j * w + k];
                    rec[Z_PREV] = z_prev;
                    own[g.dst as usize * w + k] = rec[Z_OWN];
                    prev[g.dst as usize * w + k] = z_prev;
                }
            }
            self.transcript.n_and += step.ands.len();
            self.ands_done += step.ands.len() as u64;
        }
        Ok(prog
            .outputs
            .iter()
            .map(|&o| Shares { own: own[o as usize * w..(o as usize + 1) * w].to_vec(), prev: prev[o as usize * w..(o as usize + 1) * w].to_vec() })
            .collect())
    }

    /// Verifies every AND since the last verification (BGIN19); aborts unless all three parties' messages
    /// were correct.
    pub fn verify(&mut self) -> Result<(), Abort> {
        crate::verify::verify(self)
    }

    /// Opens secrets to all three parties, which must have been verified. Each missing component is
    /// received from the two parties holding it (once in full, once as a hash) and compared.
    pub fn open(&mut self, xs: &[Shares]) -> Result<Vec<Vec<u64>>, Abort> {
        if self.transcript.n_and != 0 {
            return abort("opening before the ANDs are verified");
        }
        // Wires of the whole batch, or all of the same leading words (e.g. a range of whole words).
        let words = xs.first().map_or(0, |x| x.own.len());
        assert!(words <= self.words && xs.iter().all(|x| x.own.len() == words && x.prev.len() == words));
        let tail = if words == self.words { self.tail } else { u64::MAX };
        let mut to_prev = Vec::with_capacity(xs.len() * words * 8);
        let mut hasher = blake2s::Hasher::new();
        for x in xs {
            for &v in &x.own {
                to_prev.extend_from_slice(&v.to_le_bytes());
            }
            for &v in &x.prev {
                hasher.update(&v.to_le_bytes());
            }
        }
        let (from_prev, from_next) = self.link.exchange(to_prev, hasher.finalize().to_vec())?;
        if from_next.len() != xs.len() * words * 8 || blake2s::hash(&from_next).as_slice() != from_prev.as_slice() {
            return abort("inconsistent opening");
        }
        Ok(xs
            .iter()
            .enumerate()
            .map(|(i, x)| {
                (0..words)
                    .map(|k| {
                        let at = (i * words + k) * 8;
                        let mut v = x.own[k] ^ x.prev[k] ^ u64::from_le_bytes(from_next[at..at + 8].try_into().unwrap());
                        if k + 1 == words {
                            v &= tail;
                        }
                        v
                    })
                    .collect()
            })
            .collect())
    }

    pub(crate) fn tag(&self, purpose: &[u8]) -> Tag {
        let mut p = purpose.to_vec();
        p.extend_from_slice(&self.verifications.to_le_bytes());
        tag(&self.session, &p)
    }
}

fn binop(arena: &mut [u64], w: usize, dst: u32, a: u32, b: u32, f: impl Fn(u64, u64) -> u64) {
    for k in 0..w {
        arena[dst as usize * w + k] = f(arena[a as usize * w + k], arena[b as usize * w + k]);
    }
}

fn copy_slot(arena: &mut [u64], w: usize, dst: u32, a: u32) {
    if dst != a {
        arena.copy_within(a as usize * w..(a as usize + 1) * w, dst as usize * w);
    }
}
