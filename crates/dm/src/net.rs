//! The simulated network, adapted from `mpc::net`: three party threads on a ring of in-process
//! channels, moving in lockstep exchanges (one round each), bytes and rounds counted exactly.
//! Every message of this protocol is a broadcast: the same bytes to both other parties.
//!
//! Test hooks play a corrupt party: rewrite its outgoing messages, possibly after reading the
//! round's incoming ones (rushing), and record everything it receives.

use std::sync::mpsc::{Receiver, Sender, channel};

pub use mpc::net::{Abort, LAN, NetModel, Stats, WAN, abort};

/// Rewrites the messages to the previous and next party of a round; a rushing party also gets the
/// round's messages from them first.
pub type Tamper = Box<dyn FnMut(u64, Option<&[Vec<u8>; 2]>, &mut Vec<u8>, &mut Vec<u8>) + Send>;

/// What a party received, round by round (from the previous and the next party), and the values it
/// opened.
#[derive(Clone, Debug, Default)]
pub struct View {
    pub received: Vec<[Vec<u8>; 2]>,
    pub opened: Vec<(&'static str, Vec<u128>)>,
}

pub type Recorder = std::sync::Arc<std::sync::Mutex<View>>;

pub struct Link {
    pub id: usize,
    to_prev: Sender<Vec<u8>>,
    to_next: Sender<Vec<u8>>,
    from_prev: Receiver<Vec<u8>>,
    from_next: Receiver<Vec<u8>>,
    pub stats: Stats,
    pub tamper: Option<Tamper>,
    /// Receive before sending (at most one rushing party per session).
    pub rush: bool,
    pub record: Option<Recorder>,
}

impl Link {
    /// Sends `msg` to both other parties and returns the three messages of the round, by sender.
    pub fn broadcast(&mut self, msg: Vec<u8>) -> Result<[Vec<u8>; 3], Abort> {
        let gone = |_| Abort("a party left".into());
        let (mut to_prev, mut to_next) = (msg.clone(), msg.clone());
        let received = if self.rush {
            let r = [self.from_prev.recv().map_err(gone)?, self.from_next.recv().map_err(gone)?];
            if let Some(t) = self.tamper.as_mut() {
                t(self.stats.rounds, Some(&r), &mut to_prev, &mut to_next);
            }
            Some(r)
        } else {
            if let Some(t) = self.tamper.as_mut() {
                t(self.stats.rounds, None, &mut to_prev, &mut to_next);
            }
            None
        };
        self.stats.rounds += 1;
        self.stats.bytes_sent += (to_prev.len() + to_next.len()) as u64;
        // A tampering party records what it told its successor, so a consistent lie stays
        // consistent with its own later messages.
        let own = if self.tamper.is_some() { to_next.clone() } else { msg };
        self.to_prev.send(to_prev).map_err(|_| Abort("a party left".into()))?;
        self.to_next.send(to_next).map_err(|_| Abort("a party left".into()))?;
        let [from_prev, from_next] = match received {
            Some(r) => r,
            None => [self.from_prev.recv().map_err(gone)?, self.from_next.recv().map_err(gone)?],
        };
        if let Some(rec) = &self.record {
            rec.lock().unwrap().received.push([from_prev.clone(), from_next.clone()]);
        }
        let mut out: [Vec<u8>; 3] = Default::default();
        out[self.id] = own;
        out[(self.id + 2) % 3] = from_prev;
        out[(self.id + 1) % 3] = from_next;
        Ok(out)
    }

    /// Records values this party opened (for the tests).
    pub fn note_opened(&self, what: &'static str, vals: impl Iterator<Item = u128>) {
        if let Some(rec) = &self.record {
            rec.lock().unwrap().opened.push((what, vals.collect()));
        }
    }
}

/// The three links of a session.
pub fn ring() -> [Link; 3] {
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
            tamper: None,
            rush: false,
            record: None,
        }
    })
}

/// A message under construction.
#[derive(Default)]
pub struct Writer(pub Vec<u8>);

impl Writer {
    pub fn u64s(&mut self, v: &[u64]) -> &mut Self {
        self.0.reserve(8 * v.len());
        for x in v {
            self.0.extend_from_slice(&x.to_le_bytes());
        }
        self
    }

    pub fn u128s(&mut self, v: &[u128]) -> &mut Self {
        self.0.reserve(16 * v.len());
        for x in v {
            self.0.extend_from_slice(&x.to_le_bytes());
        }
        self
    }

    pub fn bytes(&mut self, v: &[u8]) -> &mut Self {
        self.0.extend_from_slice(v);
        self
    }

    pub fn done(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.0)
    }
}

/// A received message, read front to back; any length mismatch aborts.
pub struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    pub fn new(m: &'a [u8]) -> Self {
        Self(m)
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], Abort> {
        if self.0.len() < n {
            return abort("short message");
        }
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        Ok(a)
    }

    pub fn u64s(&mut self, n: usize) -> Result<Vec<u64>, Abort> {
        Ok(self.take(8 * n)?.as_chunks::<8>().0.iter().map(|c| u64::from_le_bytes(*c)).collect())
    }

    pub fn u128s(&mut self, n: usize) -> Result<Vec<u128>, Abort> {
        Ok(self.take(16 * n)?.as_chunks::<16>().0.iter().map(|c| u128::from_le_bytes(*c)).collect())
    }

    pub fn bytes(&mut self, n: usize) -> Result<&'a [u8], Abort> {
        self.take(n)
    }

    pub fn end(&self) -> Result<(), Abort> {
        if self.0.is_empty() { Ok(()) } else { abort("long message") }
    }
}
