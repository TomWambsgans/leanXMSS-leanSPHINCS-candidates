//! One party of an `n`-party session: bit-sliced evaluation, AND gates with collector resharing,
//! and openings.
//!
//! A secret bit-vector is held as the party's `m = C(n - 1, f)` terms. A public value is the term
//! `T_0` (global index 0), so XOR or NOT with a public value changes that term only.
//!
//! AND of `x` and `y`, gate `g` of the session, with `(T*, c) = collector(g)`:
//! - party `i` computes `u_i = sum_{(A, B) assigned to i} x_A y_B + rho_i + sum r_T`, where `rho_i`
//!   is its share of a zero sharing (`rho_i = sum_{j != i} F(k_ij, g)`, so `sum_i rho_i = 0`) and the
//!   sum runs over the PRSS terms `r_T = F(k_T, g)`, `T != T*`, that it owns;
//! - round 1: every party other than `c` sends `u_i` to `c` (`n - 1` bits);
//! - round 2: `c` forwards `z_T* = sum_i u_i` to the other `f` holders of `T*` (`f` bits);
//! - the output terms are `z_T = r_T` for `T != T*`, and `z_T*`: they add up to `x y`.
//!
//! Every AND is recorded until [`Party::verify`] has checked all of them; [`Party::open`] refuses
//! to run before that. The outputs of [`Party::eval`] carry their provenance: they can be opened, or
//! used as inputs in another session, only once the session that computed them has verified their
//! ANDs. After any abort (a failed check, a malformed message, a party that left) the party is
//! poisoned: every later call fails, so nothing is ever opened after a rejection.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use mpc::circuit::{AndOp, Op, Program};
use mpc::gf128::Gf128;
use mpc::prf::{Key, Tag, prf_field, prf_fields, prf_words, tag};

use crate::net::{Abort, Net, abort};
use crate::setup::{Keys, SessionId};
use crate::structure::{Structure, convert};
use crate::verify::{ceil_log2, tensor};

/// A party's shares of one secret bit-vector: its terms, by local index, and their provenance.
#[derive(Clone, Debug)]
pub struct Shares(pub Vec<Vec<u64>>, pub(crate) Origin);

impl Shares {
    /// Fresh input shares (dealt, or PRF terms of the setup's seeds). Never wrap values computed by
    /// [`Party::eval`] this way: that would skip the check that their ANDs were verified.
    pub fn input(terms: Vec<Vec<u64>>) -> Self {
        Self(terms, Origin::Input)
    }
}

impl PartialEq for Shares {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Shares {}

/// Where shares come from.
#[derive(Clone, Debug)]
pub(crate) enum Origin {
    /// Inputs: their terms are hash-compared among their holders when used.
    Input,
    /// The output of an evaluation: correct once the evaluating party has verified its first `ands`
    /// ANDs (`verified` is that party's count of verified ANDs).
    Eval { ands: u64, verified: Arc<AtomicU64> },
}

/// Transcript fields: the party's terms of an AND's inputs and output.
pub(crate) const X: usize = 0;
pub(crate) const Y: usize = 1;
pub(crate) const Z: usize = 2;

/// The ANDs not yet verified: the terms of word `w` of field `f` of the `a`-th recorded AND are at
/// `((a * words + w) * 3 + f) * m`, `m` consecutive words.
#[derive(Default)]
pub(crate) struct Transcript {
    pub data: Vec<u64>,
    pub n_and: usize,
}

/// Test hooks for a cheating party.
#[cfg(any(test, feature = "testing"))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Cheat {
    #[default]
    Honest,
    /// Flip instance `bit` of the `and`-th recorded AND: in the contribution sent to the collector,
    /// or, as the collector, in the forwarded term: to every holder and in its own term (consistent),
    /// or to one holder only (`split`).
    FlipAnd { and: usize, bit: usize, split: bool },
    /// A consistent `FlipAnd`, then covered in the first verification round with a guess `r1` of its
    /// challenge (e.g. one seen in an earlier session).
    Forge { and: usize, bit: usize, r1: u128 },
    /// Only the cover of `Forge`, for another corrupt party's flip.
    Cover { and: usize, bit: usize, r1: u128 },
    /// Compute the cross products of the `and`-th AND with one own input term flipped at `bit`.
    LocalTerm { and: usize, bit: usize },
}

/// What a party saw opened during the checks, for the tests.
#[cfg(any(test, feature = "testing"))]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Record {
    /// Coins, and the discrepancies of the final checks (zero when they pass).
    pub checks: Vec<(&'static str, u128)>,
    /// The first challenge of the last verification.
    pub r1: Option<u128>,
}

pub struct Party {
    pub id: usize,
    pub s: Arc<Structure>,
    pub net: Net,
    pub(crate) keys: Keys,
    pub(crate) session: [u8; 16],
    /// Instances in the batch, and 64-bit words per bit-vector.
    pub n: usize,
    pub words: usize,
    pub(crate) tail: u64,
    pub(crate) transcript: Transcript,
    /// ANDs evaluated in this session so far: the index of the next one.
    ands_done: u64,
    /// ANDs of this session verified so far, shared with the outputs of [`Party::eval`].
    verified: Arc<AtomicU64>,
    /// Calls to [`Party::verify`] and [`Party::open`] so far: every coin and PRSS tag of a call
    /// carries it, so no tag repeats within a session.
    pub(crate) epoch: u64,
    /// Running hashes, per local term, of every value this party holds for the term that did not
    /// come from its PRSS seed (input terms, and `T*` terms collected or forwarded) since the last
    /// comparison; compared among the term's holders before anything is opened.
    pub(crate) hashes: Vec<blake2s::Hasher>,
    /// Whether the hashes cover values not compared yet.
    pub(crate) pending: bool,
    /// Worker threads for the heavy verification passes.
    pub threads: usize,
    /// Memory for the materialized statement of the check; `None` for the default.
    pub materialize_limit: Option<usize>,
    poisoned: bool,
    #[cfg(any(test, feature = "testing"))]
    pub cheat: Cheat,
    /// A corrupt party, member of the coalition `Some(mask)` (which includes it), that ignores failed
    /// checks (it never aborts on them, and votes to accept), so that the tests see what the honest
    /// parties catch on their own.
    #[cfg(any(test, feature = "testing"))]
    pub complicit: Option<u32>,
    #[cfg(any(test, feature = "testing"))]
    pub record: Record,
}

fn put(out: &mut Vec<u8>, v: &[u64]) {
    for x in v {
        out.extend_from_slice(&x.to_le_bytes());
    }
}

fn word(b: &[u8], k: usize) -> u64 {
    u64::from_le_bytes(b[8 * k..8 * k + 8].try_into().unwrap())
}

fn to_bytes(v: &[Gf128]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_bytes()).collect()
}

impl Party {
    /// `keys` from [`crate::setup::keygen`] or [`crate::setup::deal`]; `session` from
    /// [`crate::setup::establish`] (it separates all PRF streams, and must never repeat).
    pub fn new(net: Net, s: Arc<Structure>, keys: Keys, session: SessionId, n: usize) -> Self {
        assert!(n > 0 && net.n == s.n && keys.prss.len() == s.m() && keys.pair.len() == s.n);
        let threads = std::thread::available_parallelism().map_or(1, |p| p.get()).div_ceil(s.n).max(1);
        let m = s.m();
        Self {
            id: net.id,
            s,
            net,
            keys,
            session: *session.bytes(),
            n,
            words: n.div_ceil(64),
            tail: tail_mask(n),
            transcript: Transcript::default(),
            ands_done: 0,
            verified: Arc::new(AtomicU64::new(0)),
            epoch: 0,
            hashes: (0..m).map(|_| blake2s::Hasher::new()).collect(),
            pending: false,
            threads,
            materialize_limit: None,
            poisoned: false,
            #[cfg(any(test, feature = "testing"))]
            cheat: Cheat::Honest,
            #[cfg(any(test, feature = "testing"))]
            complicit: None,
            #[cfg(any(test, feature = "testing"))]
            record: Record::default(),
        }
    }

    /// Runs `f` unless the party is poisoned, and poisons it if `f` fails.
    fn guarded<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, Abort>) -> Result<T, Abort> {
        if self.poisoned {
            return abort("this party already aborted");
        }
        let out = f(self);
        if out.is_err() {
            self.poisoned = true;
        }
        out
    }

    /// A check: aborts if it failed (unless this is a complicit test party).
    pub(crate) fn check(&self, ok: bool, why: &str) -> Result<(), Abort> {
        if ok || self.complicit() { Ok(()) } else { abort(why) }
    }

    pub(crate) fn complicit(&self) -> bool {
        #[cfg(any(test, feature = "testing"))]
        return self.complicit.is_some();
        #[cfg(not(any(test, feature = "testing")))]
        false
    }

    pub fn session(&self) -> &[u8; 16] {
        &self.session
    }

    /// Switches to batches of `n` instances; the ANDs so far must be verified.
    pub fn set_n(&mut self, n: usize) -> Result<(), Abort> {
        self.guarded(|p| {
            assert!(n > 0);
            if p.transcript.n_and != 0 || p.pending {
                return abort("verify before changing the batch size");
            }
            p.n = n;
            p.words = n.div_ceil(64);
            p.tail = tail_mask(n);
            Ok(())
        })
    }

    /// Shares of a public bit-vector: the term `T_0` is the value, the others are zero.
    pub fn share_public(&self, value: &[u64]) -> Shares {
        let l0 = self.s.local(self.id, 0);
        Shares::input((0..self.s.m()).map(|l| if Some(l) == l0 { value.to_vec() } else { vec![0; self.words] }).collect())
    }

    /// Whether `x` may be used here: inputs always; outputs of this party's own evaluation (verified
    /// or not, as later verifications cover them); and outputs of another session once verified there.
    fn usable(&self, x: &Shares) -> bool {
        match &x.1 {
            Origin::Input => true,
            Origin::Eval { ands, verified } => Arc::ptr_eq(verified, &self.verified) || verified.load(Ordering::Acquire) >= *ands,
        }
    }

    /// Whether `x` may be opened: inputs, and outputs whose ANDs have all been verified.
    fn openable(&self, x: &Shares) -> bool {
        match &x.1 {
            Origin::Input => true,
            Origin::Eval { ands, verified } => verified.load(Ordering::Acquire) >= *ands,
        }
    }

    /// Evaluates `prog` on public inputs (bit-vectors) and secret inputs (shares).
    pub fn eval(&mut self, prog: &Program, pub_in: &[Vec<u64>], sec_in: &[Shares]) -> Result<Vec<Shares>, Abort> {
        self.guarded(|p| p.eval_inner(prog, pub_in, sec_in))
    }

    fn eval_inner(&mut self, prog: &Program, pub_in: &[Vec<u64>], sec_in: &[Shares]) -> Result<Vec<Shares>, Abort> {
        assert_eq!(pub_in.len(), prog.n_pub_inputs);
        assert_eq!(sec_in.len(), prog.n_sec_inputs);
        if !sec_in.iter().all(|x| self.usable(x)) {
            return abort("shares from another session whose ANDs were never verified");
        }
        let (w, m, tail) = (self.words, self.s.m(), self.tail);
        let mw = m * w;
        let mut pubs = vec![0u64; prog.n_pub_slots * w];
        let mut sec = vec![0u64; prog.n_sec_slots * mw];
        let ones: Vec<u64> = (0..w).map(|k| if k + 1 == w { tail } else { u64::MAX }).collect();
        // The term carrying public values, if this party holds it.
        let l0 = self.s.local(self.id, 0);
        for step in &prog.steps {
            for op in &step.local {
                match *op {
                    Op::PubIn { dst, input } => {
                        let d = &mut pubs[dst as usize * w..(dst as usize + 1) * w];
                        d.copy_from_slice(&pub_in[input as usize]);
                        d[w - 1] &= tail;
                    }
                    Op::SecIn { dst, input } => {
                        let x = &sec_in[input as usize].0;
                        assert_eq!(x.len(), m);
                        for (l, t) in x.iter().enumerate() {
                            let d = &mut sec[dst as usize * mw + l * w..dst as usize * mw + (l + 1) * w];
                            d.copy_from_slice(t);
                            d[w - 1] &= tail;
                            let mut b = Vec::with_capacity(8 * w);
                            put(&mut b, d);
                            self.hashes[l].update(&b);
                        }
                        self.pending = true;
                    }
                    Op::PubXor { dst, a, b } => binop(&mut pubs, w, dst, a, b, |x, y| x ^ y),
                    Op::PubAnd { dst, a, b } => binop(&mut pubs, w, dst, a, b, |x, y| x & y),
                    Op::PubNot { dst, a } => {
                        for k in 0..w {
                            pubs[dst as usize * w + k] = pubs[a as usize * w + k] ^ ones[k];
                        }
                    }
                    Op::SecXor { dst, a, b } => binop(&mut sec, mw, dst, a, b, |x, y| x ^ y),
                    Op::SecXorPub { dst, a, p } => {
                        copy_slot(&mut sec, mw, dst, a);
                        if let Some(l0) = l0 {
                            for k in 0..w {
                                sec[dst as usize * mw + l0 * w + k] ^= pubs[p as usize * w + k];
                            }
                        }
                    }
                    Op::SecNot { dst, a } => {
                        copy_slot(&mut sec, mw, dst, a);
                        if let Some(l0) = l0 {
                            for k in 0..w {
                                sec[dst as usize * mw + l0 * w + k] ^= ones[k];
                            }
                        }
                    }
                    Op::SecAndPub { dst, a, p } => {
                        for l in 0..m {
                            for k in 0..w {
                                sec[dst as usize * mw + l * w + k] = sec[a as usize * mw + l * w + k] & pubs[p as usize * w + k];
                            }
                        }
                    }
                }
            }
            if !step.ands.is_empty() {
                self.and_level(&step.ands, &mut sec)?;
            }
        }
        let origin = Origin::Eval { ands: self.ands_done, verified: self.verified.clone() };
        Ok(prog
            .outputs
            .iter()
            .map(|&o| Shares((0..m).map(|l| sec[o as usize * mw + l * w..o as usize * mw + (l + 1) * w].to_vec()).collect(), origin.clone()))
            .collect())
    }

    /// One level of AND gates: products, two rounds, output terms (all inputs read before any
    /// output is written, as outputs may reuse input slots).
    fn and_level(&mut self, ands: &[AndOp], sec: &mut [u64]) -> Result<(), Abort> {
        let s = self.s.clone();
        let (i, n, m, w, tail) = (self.id, s.n, s.m(), self.words, self.tail);
        let mw = m * w;
        let g = ands.len();
        let first = self.ands_done;
        let cs: Vec<(usize, usize)> = (0..g).map(|j| s.collector(first + j as u64)).collect();
        let (r_tag, rho_tag) = (tag(&self.session, b"and-r"), tag(&self.session, b"and-rho"));
        #[cfg(any(test, feature = "testing"))]
        let cheat_at = {
            let rec0 = self.transcript.n_and;
            match self.cheat {
                Cheat::FlipAnd { and, bit, .. } | Cheat::Forge { and, bit, .. } | Cheat::LocalTerm { and, bit } if (rec0..rec0 + g).contains(&and) => Some((and - rec0, bit % self.n)),
                _ => None,
            }
        };
        // New terms (PRSS values, and T* later) and contributions.
        let mut z = vec![0u64; g * mw];
        let mut u = vec![0u64; g * w];
        let (mut tmp, mut acc) = (vec![0u64; w], vec![0u64; w]);
        let base = self.transcript.data.len();
        self.transcript.data.resize(base + g * w * 3 * m, 0);
        for (j, op) in ands.iter().enumerate() {
            let index = first + j as u64;
            let lstar = s.local(i, cs[j].0);
            let zj = &mut z[j * mw..(j + 1) * mw];
            let uj = &mut u[j * w..(j + 1) * w];
            for l in (0..m).filter(|&l| Some(l) != lstar) {
                let r = &mut zj[l * w..(l + 1) * w];
                prf_words(&self.keys.prss[l], &r_tag, index, r);
                r[w - 1] &= tail;
                if s.owner[s.held[i][l]] == i {
                    for k in 0..w {
                        uj[k] ^= r[k];
                    }
                }
            }
            for p in (0..n).filter(|&p| p != i) {
                prf_words(&self.keys.pair[p], &rho_tag, index, &mut tmp);
                for k in 0..w {
                    uj[k] ^= tmp[k];
                }
            }
            uj[w - 1] &= tail;
            let (xa, yb) = (op.a as usize * mw, op.b as usize * mw);
            for (a, bs) in &s.cross[i] {
                acc.copy_from_slice(&sec[yb + bs[0] * w..yb + (bs[0] + 1) * w]);
                for &b in &bs[1..] {
                    for k in 0..w {
                        acc[k] ^= sec[yb + b * w + k];
                    }
                }
                for k in 0..w {
                    uj[k] ^= sec[xa + a * w + k] & acc[k];
                }
            }
            #[cfg(any(test, feature = "testing"))]
            if let (Some((jj, bit)), Cheat::LocalTerm { .. }) = (cheat_at, self.cheat)
                && jj == j
            {
                // The first cross group again, with its x term flipped at `bit`: the error is the
                // product of the flip and the y terms, both known to this party.
                let (_, bs) = &s.cross[i][0];
                let y = bs.iter().fold(0u64, |a, &b| a ^ sec[yb + b * w + bit / 64]);
                uj[bit / 64] ^= y & (1 << (bit % 64));
            }
            let data = &mut self.transcript.data;
            for k in 0..w {
                let r = base + (j * w + k) * 3 * m;
                for l in 0..m {
                    data[r + X * m + l] = sec[xa + l * w + k];
                    data[r + Y * m + l] = sec[yb + l * w + k];
                }
            }
        }
        // Round 1: contributions to the collectors.
        let mut out = vec![vec![]; n];
        for j in 0..g {
            let c = cs[j].1;
            if c != i {
                #[cfg_attr(not(any(test, feature = "testing")), allow(unused_mut))]
                let mut v = u[j * w..(j + 1) * w].to_vec();
                #[cfg(any(test, feature = "testing"))]
                if let Some((jj, bit)) = cheat_at
                    && jj == j
                    && matches!(self.cheat, Cheat::FlipAnd { .. } | Cheat::Forge { .. })
                {
                    v[bit / 64] ^= 1 << (bit % 64);
                }
                put(&mut out[c], &v);
            }
        }
        let got = self.net.exchange(out)?;
        let collected: Vec<usize> = (0..g).filter(|&j| cs[j].1 == i).collect();
        if (0..n).any(|p| p != i && got[p].len() != collected.len() * w * 8) {
            return abort("malformed AND message");
        }
        // Round 2: the collected terms to their other holders.
        let mut fwd = vec![vec![]; n];
        for (q, &j) in collected.iter().enumerate() {
            let lstar = s.local(i, cs[j].0).unwrap();
            let mut v = u[j * w..(j + 1) * w].to_vec();
            for p in (0..n).filter(|&p| p != i) {
                for k in 0..w {
                    v[k] ^= word(&got[p], q * w + k);
                }
            }
            self.check(v[w - 1] & !tail == 0, "malformed AND message")?;
            #[cfg_attr(not(any(test, feature = "testing")), allow(unused_mut))]
            let mut split: Option<(usize, u64)> = None;
            #[cfg(any(test, feature = "testing"))]
            if let Some((jj, bit)) = cheat_at
                && jj == j
            {
                match self.cheat {
                    Cheat::FlipAnd { split: true, .. } => split = Some((bit / 64, 1 << (bit % 64))),
                    Cheat::FlipAnd { .. } | Cheat::Forge { .. } => v[bit / 64] ^= 1 << (bit % 64),
                    _ => {}
                }
            }
            for (k, h) in s.holders(cs[j].0).filter(|&h| h != i).enumerate() {
                match split {
                    Some((at, mask)) if k == 0 => {
                        let mut lie = v.clone();
                        lie[at] ^= mask;
                        put(&mut fwd[h], &lie);
                    }
                    _ => put(&mut fwd[h], &v),
                }
            }
            z[j * mw + lstar * w..j * mw + (lstar + 1) * w].copy_from_slice(&v);
        }
        let got = self.net.exchange(fwd)?;
        let mut pos = vec![0usize; n];
        for j in 0..g {
            let (t, c) = cs[j];
            if c == i {
                continue;
            }
            if let Some(l) = s.local(i, t) {
                if got[c].len() < (pos[c] + w) * 8 {
                    return abort("malformed AND forward");
                }
                let v = &mut z[j * mw + l * w..j * mw + (l + 1) * w];
                for k in 0..w {
                    v[k] = word(&got[c], pos[c] + k);
                }
                let clean = v[w - 1] & !tail == 0;
                self.check(clean, "malformed AND forward")?;
                pos[c] += w;
            }
        }
        if (0..n).any(|c| c != i && got[c].len() != pos[c] * 8) {
            return abort("malformed AND forward");
        }
        // Hash the T* terms held; write the outputs and the transcript.
        for j in 0..g {
            if let Some(l) = s.local(i, cs[j].0) {
                let mut b = Vec::with_capacity(8 * w);
                put(&mut b, &z[j * mw + l * w..j * mw + (l + 1) * w]);
                self.hashes[l].update(&b);
                self.pending = true;
            }
        }
        for (j, op) in ands.iter().enumerate() {
            sec[op.dst as usize * mw..(op.dst as usize + 1) * mw].copy_from_slice(&z[j * mw..(j + 1) * mw]);
            for k in 0..w {
                let r = base + (j * w + k) * 3 * m + Z * m;
                for l in 0..m {
                    self.transcript.data[r + l] = z[j * mw + l * w + k];
                }
            }
        }
        self.transcript.n_and += g;
        self.ands_done += g as u64;
        Ok(())
    }

    /// Verifies every AND since the last verification ([`crate::verify`]); aborts unless all of them
    /// are correct.
    pub fn verify(&mut self) -> Result<(), Abort> {
        self.guarded(crate::verify::verify)?;
        self.verified.store(self.ands_done, Ordering::Release);
        Ok(())
    }

    /// Opens secrets to all parties; every AND and input since the last [`Party::verify`] must have
    /// been verified. Five rounds:
    /// 1. output `k` goes through the king `k mod n`: its `f` helpers send it the sums of the terms it
    ///    misses (`n - 1 + f` bit-vectors per output in total, with round 2);
    /// 2. the king sends the value to all;
    /// 3. a fresh coin, and the holders of every term compare hashes of the terms being opened;
    /// 4. every party checks the values it got against a random linear combination `Y` of them,
    ///    opened robustly (a Shamir opening of one field element): a wrong value is caught;
    /// 5. agreement: everyone sends whether its check passed and a hash of the values, and accepts
    ///    only if all passed with the same values. So an honest party that caught anything makes all
    ///    honest parties abort, and honest parties that output hold the same values. (A corrupt party
    ///    can still make some honest parties abort and not others, by voting differently to them:
    ///    security with selective abort, as without a broadcast channel.)
    pub fn open(&mut self, xs: &[Shares]) -> Result<Vec<Vec<u64>>, Abort> {
        self.guarded(|p| p.open_inner(xs))
    }

    fn open_inner(&mut self, xs: &[Shares]) -> Result<Vec<Vec<u64>>, Abort> {
        if self.transcript.n_and != 0 || self.pending {
            return abort("opening before the ANDs and inputs are verified");
        }
        if !xs.iter().all(|x| self.openable(x)) {
            return abort("opening shares whose ANDs were never verified");
        }
        self.epoch += 1;
        let s = self.s.clone();
        let (i, n, m, w, tail) = (self.id, s.n, s.m(), self.words, self.tail);
        assert!(xs.iter().all(|x| x.0.len() == m && x.0.iter().all(|t| t.len() == w)));
        let kings: Vec<usize> = (0..xs.len()).map(|k| s.king(k)).collect();
        // Round 1: helpers to kings.
        let mut out = vec![vec![]; n];
        for (k, x) in xs.iter().enumerate() {
            if let Some((_, ls)) = s.helpers(kings[k]).iter().find(|(h, _)| *h == i) {
                let v: Vec<u64> = (0..w).map(|q| ls.iter().fold(0, |a, &l| a ^ x.0[l][q])).collect();
                put(&mut out[kings[k]], &v);
            }
        }
        let got = self.net.exchange(out)?;
        let mine: Vec<usize> = (0..xs.len()).filter(|&k| kings[k] == i).collect();
        for p in (0..n).filter(|&p| p != i) {
            let helps = s.helpers(i).iter().any(|(h, _)| *h == p);
            if got[p].len() != if helps { mine.len() * w * 8 } else { 0 } {
                return abort("malformed opening");
            }
        }
        let mut values: Vec<Vec<u64>> = vec![vec![]; xs.len()];
        for (q, &k) in mine.iter().enumerate() {
            let mut v: Vec<u64> = (0..w).map(|c| xs[k].0.iter().fold(0, |a, t| a ^ t[c])).collect();
            for (h, _) in s.helpers(i) {
                for c in 0..w {
                    v[c] ^= word(&got[*h], q * w + c);
                }
            }
            self.check(v[w - 1] & !tail == 0, "malformed opening")?;
            values[k] = v;
        }
        // Round 2: kings to all.
        let mut out = vec![vec![]; n];
        for p in (0..n).filter(|&p| p != i) {
            for &k in &mine {
                put(&mut out[p], &values[k]);
            }
        }
        let got = self.net.exchange(out)?;
        let mut pos = vec![0usize; n];
        for k in 0..xs.len() {
            let king = kings[k];
            if king == i {
                continue;
            }
            if got[king].len() < (pos[king] + w) * 8 {
                return abort("malformed opening");
            }
            values[k] = (0..w).map(|c| word(&got[king], pos[king] + c)).collect();
            self.check(values[k][w - 1] & !tail == 0, "malformed opening")?;
            pos[king] += w;
        }
        if (0..n).any(|p| p != i && got[p].len() != pos[p] * 8) {
            return abort("malformed opening");
        }
        // Round 3: the coin, and the consistency of the terms being opened.
        let per_term: Vec<[u8; 32]> = (0..m)
            .map(|l| {
                let mut h = blake2s::Hasher::new();
                for x in xs {
                    let mut b = Vec::with_capacity(8 * w);
                    put(&mut b, &x.0[l]);
                    h.update(&b);
                }
                h.finalize()
            })
            .collect();
        let digests: Vec<Vec<u8>> = (0..n).map(|q| self.digests(&per_term, q)).collect();
        let share = self.prss_share(b"open-gamma", 0);
        let (v, got) = self.open_shamir(&[share], Some(digests.clone()))?;
        self.check((0..n).all(|q| q == i || got[q] == digests[q]), "inconsistent terms to open")?;
        let key = self.coin_key(b"open-gamma", 0, v[0]);
        // Round 4: the check.
        let c = ceil_log2(self.n);
        let ctag = self.vtag(b"open-gamma-expand", 0);
        let gamma = prf_fields(&key, &ctag, 0, xs.len());
        let sigma = prf_fields(&key, &ctag, 1, c);
        let mut weight = tensor(c, |t| (Gf128::ONE, sigma[t]));
        weight.resize(64 * w, Gf128::ZERO);
        let tables = &s.tables[i];
        let (mut share, mut claimed) = (Gf128::ZERO, Gf128::ZERO);
        let mut terms = vec![0u64; m];
        let mut conv = [Gf128::ZERO; 64];
        for (k, x) in xs.iter().enumerate() {
            let (mut sk, mut ck) = (Gf128::ZERO, Gf128::ZERO);
            for q in 0..w {
                for l in 0..m {
                    terms[l] = x.0[l][q];
                }
                convert(tables, &terms, &mut conv);
                for t in 0..64 {
                    sk += weight[64 * q + t] * conv[t];
                    if values[k][q] >> t & 1 == 1 {
                        ck += weight[64 * q + t];
                    }
                }
            }
            share += gamma[k] * sk;
            claimed += gamma[k] * ck;
        }
        let y = self.open_shamir(&[share], None)?.0[0];
        #[cfg(any(test, feature = "testing"))]
        self.record.checks.push(("open", (y + claimed).0));
        // Round 5: agreement.
        let mut h = blake2s::Hasher::new();
        for v in &values {
            let mut b = Vec::with_capacity(8 * w);
            put(&mut b, v);
            h.update(&b);
        }
        let ok = y == claimed || self.complicit();
        let vote: Vec<u8> = [&[ok as u8][..], &h.finalize()[..]].concat();
        let got = self.net.exchange(vec![vote.clone(); n])?;
        self.check(ok, "inconsistent opening")?;
        let mut agreed = vote.clone();
        agreed[0] = 1;
        self.check((0..n).all(|q| q == i || got[q] == agreed), "no agreement on the opened values")?;
        Ok(values)
    }

    /// The digests in `per_term` (by local term) of the terms this party and party `q` both hold.
    pub(crate) fn digests(&self, per_term: &[[u8; 32]], q: usize) -> Vec<u8> {
        let s = &self.s;
        if q == self.id {
            return vec![];
        }
        s.held[self.id].iter().enumerate().filter(|&(_, &t)| s.holds(q, t)).flat_map(|(l, _)| per_term[l]).collect()
    }

    /// A tag for the PRF streams of the current call: `purpose`, the epoch, `j`. Within a call each
    /// `(purpose, j)` is used once; the AND gates use their own tags, indexed by the gate.
    pub(crate) fn vtag(&self, purpose: &[u8], j: u64) -> Tag {
        let mut p = purpose.to_vec();
        p.extend_from_slice(&self.epoch.to_le_bytes());
        p.extend_from_slice(&j.to_le_bytes());
        tag(&self.session, &p)
    }

    /// This party's Shamir share of a fresh pseudorandom field element `sum_T F(k_T, tag)`.
    pub(crate) fn prss_share(&self, purpose: &[u8], j: u64) -> Gf128 {
        let tag = self.vtag(purpose, j);
        self.keys.prss.iter().zip(&self.s.phi[self.id]).fold(Gf128::ZERO, |acc, (k, &c)| acc + c * prf_field(k, &tag, 0, 0))
    }

    /// Opens Shamir shares to everyone, robustly: all `n` shares must lie on one polynomial of degree
    /// `f`. `extra[p]` rides along to party `p`; what the others sent along is returned.
    pub(crate) fn open_shamir(&mut self, vals: &[Gf128], extra: Option<Vec<Vec<u8>>>) -> Result<(Vec<Gf128>, Vec<Vec<u8>>), Abort> {
        let (i, n) = (self.id, self.s.n);
        let mine = to_bytes(vals);
        let mut extra = extra.unwrap_or_else(|| vec![vec![]; n]);
        let out: Vec<Vec<u8>> = (0..n).map(|p| [&mine[..], &extra[p][..]].concat()).collect();
        let got = self.net.exchange(out)?;
        let len = 16 * vals.len();
        let exact = extra.iter().all(Vec::is_empty);
        if (0..n).any(|p| p != i && (got[p].len() < len || (exact && got[p].len() != len))) {
            return abort("malformed opening of a check value");
        }
        let mut opened = Vec::with_capacity(vals.len());
        for (k, &v) in vals.iter().enumerate() {
            let shares: Vec<Gf128> = (0..n).map(|p| if p == i { v } else { Gf128::from_bytes(got[p][16 * k..16 * k + 16].try_into().unwrap()) }).collect();
            let x = self.s.reconstruct(&shares);
            self.check(x.is_some(), "inconsistent opening of a check value")?;
            #[cfg(any(test, feature = "testing"))]
            let x = x.or_else(|| Some(self.lenient(&shares)));
            opened.push(x.unwrap());
        }
        for p in 0..n {
            extra[p] = if p == i { vec![] } else { got[p][len..].to_vec() };
        }
        Ok((opened, extra))
    }

    /// What a complicit party takes from an inconsistent opening: the value the honest shares fix
    /// (what the adversary learns from them).
    #[cfg(any(test, feature = "testing"))]
    fn lenient(&self, shares: &[Gf128]) -> Gf128 {
        let coalition = self.complicit.expect("only a complicit test party goes on after an inconsistent opening");
        assert!(coalition >> self.id & 1 == 1 && coalition.count_ones() as usize <= self.s.f, "a complicit party's coalition contains it");
        let honest: Vec<usize> = (0..self.s.n).filter(|&j| coalition >> j & 1 == 0).take(self.s.f + 1).collect();
        self.s.interpolate(&honest, shares)
    }

    /// A public random coin: a PRSS value, opened robustly, hashed into a key.
    pub(crate) fn coin(&mut self, purpose: &[u8], j: u64) -> Result<Key, Abort> {
        let share = self.prss_share(purpose, j);
        let v = self.open_shamir(&[share], None)?.0[0];
        Ok(self.coin_key(purpose, j, v))
    }

    pub(crate) fn coin_key(&mut self, purpose: &[u8], j: u64, v: Gf128) -> Key {
        #[cfg(any(test, feature = "testing"))]
        self.record.checks.push(("coin", v.0));
        let mut h = blake2s::Hasher::new();
        h.update(b"rss-coin").update(&self.vtag(purpose, j)).update(&v.to_bytes());
        h.finalize()
    }
}

pub(crate) fn tail_mask(n: usize) -> u64 {
    if n.is_multiple_of(64) { u64::MAX } else { (1u64 << (n % 64)) - 1 }
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
