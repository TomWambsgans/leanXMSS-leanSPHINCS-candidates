//! The simulated network of a 3-party session: each party is a thread, and the parties move in
//! lockstep `exchange`s, one communication round each. Bytes and rounds are counted exactly.
//!
//! Simplification (prototype): channels are in-process and reliable; there is no real latency,
//! only the [`NetModel`] estimate. A party that aborts drops its channels, so its neighbors'
//! next receive fails and they abort too.

use std::sync::mpsc::{Receiver, Sender, channel};

/// Why a party stopped: a failed check, or a neighbor that left.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Abort(pub String);

impl std::fmt::Display for Abort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "abort: {}", self.0)
    }
}

impl std::error::Error for Abort {}

pub fn abort<T>(why: impl Into<String>) -> Result<T, Abort> {
    Err(Abort(why.into()))
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Lockstep exchanges, i.e. communication rounds.
    pub rounds: u64,
    /// Payload bytes this party sent.
    pub bytes_sent: u64,
}

impl std::ops::Add for Stats {
    type Output = Self;
    fn add(self, o: Self) -> Self {
        Self { rounds: self.rounds + o.rounds, bytes_sent: self.bytes_sent + o.bytes_sent }
    }
}

/// Wall time of a run on a network: one one-way latency per round, plus the traffic.
#[derive(Clone, Copy, Debug)]
pub struct NetModel {
    pub name: &'static str,
    pub latency_s: f64,
    pub bandwidth_bit_s: f64,
}

pub const LAN: NetModel = NetModel { name: "LAN (1 ms, 1 Gbit/s)", latency_s: 1e-3, bandwidth_bit_s: 1e9 };
pub const WAN: NetModel = NetModel { name: "WAN (50 ms, 100 Mbit/s)", latency_s: 50e-3, bandwidth_bit_s: 1e8 };

impl NetModel {
    pub fn seconds(&self, s: Stats) -> f64 {
        s.rounds as f64 * self.latency_s + s.bytes_sent as f64 * 8.0 / self.bandwidth_bit_s
    }
}

/// A single bit flip injected into one outgoing message, for the cheating tests.
#[cfg(any(test, feature = "testing"))]
#[derive(Clone, Copy, Debug)]
pub struct Fault {
    pub round: u64,
    pub to_next: bool,
    pub bit: usize,
}

/// One party's two links, to its predecessor and successor on the ring `0 -> 1 -> 2 -> 0`.
pub struct Link {
    pub id: usize,
    to_prev: Sender<Vec<u8>>,
    to_next: Sender<Vec<u8>>,
    from_prev: Receiver<Vec<u8>>,
    from_next: Receiver<Vec<u8>>,
    pub stats: Stats,
    #[cfg(any(test, feature = "testing"))]
    pub fault: Option<Fault>,
    /// Whether the fault hit a nonempty message.
    #[cfg(any(test, feature = "testing"))]
    pub fault_applied: bool,
}

impl Link {
    /// One round: send to both neighbors (possibly empty messages), then receive from both.
    #[cfg_attr(not(any(test, feature = "testing")), allow(unused_mut))]
    pub fn exchange(&mut self, mut to_prev: Vec<u8>, mut to_next: Vec<u8>) -> Result<(Vec<u8>, Vec<u8>), Abort> {
        #[cfg(any(test, feature = "testing"))]
        if let Some(f) = self.fault.filter(|f| f.round == self.stats.rounds) {
            let msg = if f.to_next { &mut to_next } else { &mut to_prev };
            if !msg.is_empty() {
                let bit = f.bit % (8 * msg.len());
                msg[bit / 8] ^= 1 << (bit % 8);
                self.fault_applied = true;
            }
        }
        self.stats.rounds += 1;
        self.stats.bytes_sent += (to_prev.len() + to_next.len()) as u64;
        let gone = |_| Abort("a neighbor left".into());
        self.to_prev.send(to_prev).map_err(gone)?;
        self.to_next.send(to_next).map_err(gone)?;
        let from_prev = self.from_prev.recv().map_err(|_| Abort("a neighbor left".into()))?;
        let from_next = self.from_next.recv().map_err(|_| Abort("a neighbor left".into()))?;
        Ok((from_prev, from_next))
    }
}

/// The three links of a session.
pub fn ring() -> [Link; 3] {
    // forward[i]: i -> i + 1, backward[i]: i + 1 -> i.
    let (f_tx, f_rx): (Vec<_>, Vec<_>) = (0..3).map(|_| channel()).unzip();
    let (b_tx, b_rx): (Vec<_>, Vec<_>) = (0..3).map(|_| channel()).unzip();
    let mut f_tx: Vec<Option<Sender<Vec<u8>>>> = f_tx.into_iter().map(Some).collect();
    let mut f_rx: Vec<Option<Receiver<Vec<u8>>>> = f_rx.into_iter().map(Some).collect();
    let mut b_tx: Vec<Option<Sender<Vec<u8>>>> = b_tx.into_iter().map(Some).collect();
    let mut b_rx: Vec<Option<Receiver<Vec<u8>>>> = b_rx.into_iter().map(Some).collect();
    std::array::from_fn(|i| {
        let prev = (i + 2) % 3;
        Link {
            id: i,
            to_next: f_tx[i].take().unwrap(),
            from_prev: f_rx[prev].take().unwrap(),
            to_prev: b_tx[prev].take().unwrap(),
            from_next: b_rx[i].take().unwrap(),
            stats: Stats::default(),
            #[cfg(any(test, feature = "testing"))]
            fault: None,
            #[cfg(any(test, feature = "testing"))]
            fault_applied: false,
        }
    })
}
