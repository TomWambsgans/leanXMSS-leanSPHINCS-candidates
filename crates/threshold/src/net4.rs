//! The four operators' point-to-point network (for the steps outside a 3-party MPC session):
//! in-process channels, every message counted. A round is one `send_all` then one `recv_all`.

use std::sync::mpsc::{Receiver, Sender, channel};

use mpc::net::{Abort, Stats};

pub struct Net4 {
    pub id: usize,
    to: [Option<Sender<Vec<u8>>>; 4],
    from: [Option<Receiver<Vec<u8>>>; 4],
    pub stats: Stats,
}

impl Net4 {
    /// One round among `members` (which includes `self.id`): sends `msg(to)` to each other member,
    /// returns what each sent (indexed by operator, empty for non-members).
    pub fn round(&mut self, members: &[usize], msg: impl Fn(usize) -> Vec<u8>) -> Result<[Vec<u8>; 4], Abort> {
        self.stats.rounds += 1;
        for &o in members.iter().filter(|&&o| o != self.id) {
            let m = msg(o);
            self.stats.bytes_sent += m.len() as u64;
            self.to[o].as_ref().unwrap().send(m).map_err(|_| Abort("an operator left".into()))?;
        }
        let mut out: [Vec<u8>; 4] = Default::default();
        for &o in members.iter().filter(|&&o| o != self.id) {
            out[o] = self.from[o].as_ref().unwrap().recv().map_err(|_| Abort("an operator left".into()))?;
        }
        Ok(out)
    }

    /// Test hook: a rushing member, which receives every other member's message before choosing its own.
    #[cfg(test)]
    pub fn round_rushing(&mut self, members: &[usize], msg: impl Fn(usize, &[Vec<u8>; 4]) -> Vec<u8>) -> Result<[Vec<u8>; 4], Abort> {
        self.stats.rounds += 1;
        let mut out: [Vec<u8>; 4] = Default::default();
        for &o in members.iter().filter(|&&o| o != self.id) {
            out[o] = self.from[o].as_ref().unwrap().recv().map_err(|_| Abort("an operator left".into()))?;
        }
        for &o in members.iter().filter(|&&o| o != self.id) {
            let m = msg(o, &out);
            self.stats.bytes_sent += m.len() as u64;
            self.to[o].as_ref().unwrap().send(m).map_err(|_| Abort("an operator left".into()))?;
        }
        Ok(out)
    }

    /// Same message to every other member.
    pub fn broadcast(&mut self, members: &[usize], msg: &[u8]) -> Result<[Vec<u8>; 4], Abort> {
        self.round(members, |_| msg.to_vec())
    }
}

/// The four operators' endpoints.
pub fn network() -> [Net4; 4] {
    let mut tx: Vec<Vec<Option<Sender<Vec<u8>>>>> = (0..4).map(|_| (0..4).map(|_| None).collect()).collect();
    let mut rx: Vec<Vec<Option<Receiver<Vec<u8>>>>> = (0..4).map(|_| (0..4).map(|_| None).collect()).collect();
    for a in 0..4 {
        for b in 0..4 {
            if a != b {
                let (t, r) = channel();
                tx[a][b] = Some(t);
                rx[b][a] = Some(r);
            }
        }
    }
    let mut nets = Vec::new();
    for (id, (t, r)) in tx.into_iter().zip(rx).enumerate() {
        let to: [Option<Sender<Vec<u8>>>; 4] = t.try_into().ok().unwrap();
        let from: [Option<Receiver<Vec<u8>>>; 4] = r.try_into().ok().unwrap();
        nets.push(Net4 { id, to, from, stats: Stats::default() });
    }
    nets.try_into().ok().unwrap()
}
