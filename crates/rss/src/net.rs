//! The simulated network of an `n`-party session: point-to-point channels between all parties, each
//! party a thread, moving in lockstep `exchange`s (one communication round each). Bytes and rounds
//! are counted exactly.
//!
//! Simplification (prototype): channels are in-process and reliable; latency and bandwidth are only
//! the [`NetModel`] estimate. A party that aborts drops its channels, so the others' next receive
//! fails and they abort too.

use std::sync::mpsc::{Receiver, Sender, channel};

pub use mpc::net::{Abort, LAN, NetModel, Stats, WAN, abort};

/// A rewrite of the messages a rushing party sends to honest parties, after it has received the
/// round's messages: `(round, received, outgoing)`.
#[cfg(any(test, feature = "testing"))]
pub type Adapt = std::sync::Arc<dyn Fn(u64, &[Vec<u8>], &mut [Vec<u8>]) + Send + Sync>;

/// A bit flip injected into an outgoing message: to party `to`, or to every recipient (the same bit
/// index in each message, a consistent lie when they all carry the same content).
#[cfg(any(test, feature = "testing"))]
#[derive(Clone, Copy, Debug)]
pub struct Fault {
    pub round: u64,
    pub to: Option<usize>,
    pub bit: usize,
}

/// A corrupt party's network behaviour, for the tests.
#[cfg(any(test, feature = "testing"))]
#[derive(Clone, Default)]
pub struct Tamper {
    pub faults: Vec<Fault>,
    /// Rushing: in every round, send to the other corrupt parties, receive everything, and only then
    /// send to the honest parties (rewritten by `adapt`).
    pub rush: bool,
    /// The corrupt parties, as a bitmask.
    pub corrupt: u32,
    pub adapt: Option<Adapt>,
    /// The (round, recipient) of every message a fault flipped.
    pub hits: Vec<(u64, usize)>,
}

pub struct Net {
    pub id: usize,
    pub n: usize,
    to: Vec<Option<Sender<Vec<u8>>>>,
    from: Vec<Option<Receiver<Vec<u8>>>>,
    pub stats: Stats,
    #[cfg(any(test, feature = "testing"))]
    pub tamper: Tamper,
}

/// The links of an `n`-party session, one per party.
pub fn network(n: usize) -> Vec<Net> {
    let mut nets: Vec<Net> = (0..n)
        .map(|id| Net {
            id,
            n,
            to: (0..n).map(|_| None).collect(),
            from: (0..n).map(|_| None).collect(),
            stats: Stats::default(),
            #[cfg(any(test, feature = "testing"))]
            tamper: Tamper::default(),
        })
        .collect();
    for i in 0..n {
        for j in 0..n {
            if i != j {
                let (tx, rx) = channel();
                nets[i].to[j] = Some(tx);
                nets[j].from[i] = Some(rx);
            }
        }
    }
    nets
}

impl Net {
    /// One round: `out[j]` goes to party `j` (possibly empty; `out[id]` is ignored), then one message
    /// is received from every other party, returned by sender (`[id]` empty).
    #[cfg_attr(not(any(test, feature = "testing")), allow(unused_mut))]
    pub fn exchange(&mut self, mut out: Vec<Vec<u8>>) -> Result<Vec<Vec<u8>>, Abort> {
        assert_eq!(out.len(), self.n);
        out[self.id] = vec![];
        #[cfg(any(test, feature = "testing"))]
        self.flip(&mut out);
        self.stats.rounds += 1;
        self.stats.bytes_sent += out.iter().map(|m| m.len() as u64).sum::<u64>();
        #[cfg(any(test, feature = "testing"))]
        if self.tamper.rush {
            return self.rushing(self.stats.rounds - 1, out);
        }
        for (j, m) in out.into_iter().enumerate() {
            if j != self.id {
                self.send(j, m)?;
            }
        }
        self.receive()
    }

    fn send(&self, j: usize, m: Vec<u8>) -> Result<(), Abort> {
        self.to[j].as_ref().unwrap().send(m).map_err(|_| Abort("a party left".into()))
    }

    fn receive(&self) -> Result<Vec<Vec<u8>>, Abort> {
        (0..self.n)
            .map(|j| if j == self.id { Ok(vec![]) } else { self.from[j].as_ref().unwrap().recv().map_err(|_| Abort("a party left".into())) })
            .collect()
    }

    #[cfg(any(test, feature = "testing"))]
    fn flip(&mut self, out: &mut [Vec<u8>]) {
        let round = self.stats.rounds;
        for f in self.tamper.faults.clone().iter().filter(|f| f.round == round) {
            for (j, m) in out.iter_mut().enumerate() {
                if j != self.id && f.to.is_none_or(|t| t == j) && !m.is_empty() {
                    let bit = f.bit % (8 * m.len());
                    m[bit / 8] ^= 1 << (bit % 8);
                    self.tamper.hits.push((round, j));
                }
            }
        }
    }

    #[cfg(any(test, feature = "testing"))]
    fn rushing(&mut self, round: u64, mut out: Vec<Vec<u8>>) -> Result<Vec<Vec<u8>>, Abort> {
        let corrupt = |j: usize| self.tamper.corrupt >> j & 1 == 1;
        for j in (0..self.n).filter(|&j| j != self.id && corrupt(j)) {
            self.send(j, std::mem::take(&mut out[j]))?;
        }
        let got = self.receive()?;
        if let Some(adapt) = &self.tamper.adapt {
            adapt(round, &got, &mut out);
        }
        for j in (0..self.n).filter(|&j| j != self.id && !corrupt(j)) {
            self.send(j, std::mem::take(&mut out[j]))?;
        }
        Ok(got)
    }
}
