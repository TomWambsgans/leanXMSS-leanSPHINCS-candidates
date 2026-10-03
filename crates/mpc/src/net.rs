//! Network accounting shared by the simulated networks: aborts, per-party traffic and rounds, and a
//! latency/bandwidth model of a run's network time.

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
