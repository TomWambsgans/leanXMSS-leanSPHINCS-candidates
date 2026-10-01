//! The four operators in one process: every protocol runs one thread per operator over simulated
//! networks, and is retried with each set of three operators until one succeeds (a cheater can only
//! cause aborts, and is not identified).

use mpc::net::{Abort, Link, ring};
use sphincs::*;

use crate::net4::{Net4, network};
use crate::operator::{Operator, Roles};
use crate::protocol::{self, CheatSpec, Mode, Phase, party};

/// The sets of three operators, in the order they are tried.
pub const SETS: [[usize; 3]; 4] = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]];

/// Every operator's phases in one protocol run (empty for an operator that took no part).
pub type Report = Vec<Vec<Phase>>;

pub struct Cluster {
    pub ops: Vec<Operator>,
    pub cheats: Vec<CheatSpec>,
    /// The last signature's randomizer (the root before the first), which draws the next instance.
    pub last: Randomizer,
    sessions: u64,
}

/// The abort after every set failed, with the reasons of the last attempt.
fn all_aborted<T>(results: &[Result<T, Abort>]) -> Abort {
    let reasons: Vec<&str> = results.iter().filter_map(|r| r.as_ref().err().map(|e| e.0.as_str())).collect();
    Abort(format!("every set of three operators aborted, last: {}", reasons.join("; ")))
}

/// Runs `f` on all four operators, one thread each; the three online ones get their MPC link.
fn run<T: Send>(ops: &mut [Operator], online: [usize; 3], f: impl Fn(&mut Operator, &mut Net4, Option<Link>, &Roles) -> Result<T, Abort> + Sync) -> Vec<Result<T, Abort>> {
    let roles = Roles::new(online);
    let mut links: Vec<Option<Link>> = ring().into_iter().map(Some).collect();
    let mut nets: Vec<Option<Net4>> = network().into_iter().map(Some).collect();
    let f = &f;
    std::thread::scope(|scope| {
        let handles: Vec<_> = ops
            .iter_mut()
            .map(|op| {
                let link = online.contains(&op.id).then(|| links[roles.party(op.id)].take().unwrap());
                let mut net = nets[op.id].take().unwrap();
                scope.spawn(move || f(op, &mut net, link, &roles))
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("operator thread panicked")).collect()
    })
}

impl Cluster {
    /// The DKG with a kept subtree of height `b`, retried with each set of three online operators.
    pub fn dkg(b: usize, cheats: Vec<CheatSpec>) -> Result<(Self, [usize; 3], Report), Abort> {
        for online in SETS {
            let mut ops: Vec<Operator> = (0..4).map(Operator::new).collect();
            let results = run(&mut ops, online, |op, net, link, roles| protocol::dkg(op, net, link, roles, b, &cheats));
            if results.iter().all(|r| r.is_ok()) {
                let last = ops[0].key().pk.root;
                return Ok((Self { ops, cheats, last, sessions: 0 }, online, results.into_iter().map(Result::unwrap).collect()));
            }
            if online == SETS[3] {
                return Err(all_aborted(&results));
            }
        }
        unreachable!()
    }

    /// A fresh session id (a real deployment would agree on one, e.g. a counter).
    fn session(&mut self) -> [u8; 16] {
        self.sessions += 1;
        let mut h = blake2s::Hasher::new();
        h.update(b"session").update(&self.ops[0].key().pk.to_bytes()).update(&self.sessions.to_le_bytes());
        h.finalize()[..16].try_into().unwrap()
    }

    /// Signs `m`, trying each set of three operators until one succeeds.
    pub fn sign(&mut self, m: &Message, mode: Mode) -> Result<(Signature, [usize; 3], Report), Abort> {
        for online in SETS {
            let (session, cheats) = (self.session(), self.cheats.clone());
            let results = run(&mut self.ops, online, |op, net, link, roles| {
                let Some(link) = link else { return Ok(None) };
                protocol::sign(op, net, &mut party(op, roles, link, session, &cheats), roles, m, mode).map(Some)
            });
            if results.iter().all(|r| r.is_ok()) {
                let (sigs, report): (Vec<_>, Report) = results.into_iter().map(|r| r.unwrap().map_or((None, vec![]), |(s, p)| (Some(s), p))).unzip();
                let sigs: Vec<Signature> = sigs.into_iter().flatten().collect();
                assert!(sigs.windows(2).all(|w| w[0] == w[1]));
                self.last = sigs[0].randomizer;
                if mode == Mode::Preprocessed {
                    self.ops.iter_mut().for_each(|op| op.next = None);
                }
                return Ok((sigs[0].clone(), online, report));
            }
            if online == SETS[3] {
                return Err(all_aborted(&results));
            }
        }
        unreachable!()
    }

    /// Draws and computes the next instance, retried with each set of three operators.
    pub fn preprocess(&mut self) -> Result<([usize; 3], Report), Abort> {
        let last = self.last;
        for online in SETS {
            let (session, cheats) = (self.session(), self.cheats.clone());
            let results = run(&mut self.ops, online, |op, net, link, roles| {
                let mut party = link.map(|link| party(op, roles, link, session, &cheats));
                protocol::preprocess(op, net, party.as_mut(), roles, &last)
            });
            if results.iter().all(|r| r.is_ok()) {
                return Ok((online, results.into_iter().map(Result::unwrap).collect()));
            }
            if online == SETS[3] {
                return Err(all_aborted(&results));
            }
        }
        unreachable!()
    }
}
