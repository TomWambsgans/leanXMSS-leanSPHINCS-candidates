//! The four operators in one process: every protocol runs one thread per operator over simulated
//! networks, and its MPC part is retried with each set of three operators until one succeeds (a
//! cheater can only cause aborts, and is not identified). All protocol state lives in the
//! operators; the cluster only starts the runs.

use mpc::net::{Abort, Link, ring};
use sphincs::*;

use crate::net4::{Net4, network};
use crate::operator::{Mode, Operator, Pending, Roles};
use crate::protocol::{self, Hooks, Phase};

/// The sets of three operators, in the order they are tried.
pub const SETS: [[usize; 3]; 4] = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]];

/// Every operator's phases in one protocol run (empty for an operator that took no part).
pub type Report = Vec<Vec<Phase>>;

#[derive(Clone)]
pub struct Cluster {
    pub ops: Vec<Operator>,
    pub(crate) hooks: Hooks,
    /// Every attempt and the operators' state after it, for the tests' failure messages.
    #[cfg(test)]
    pub(crate) log: Vec<String>,
}

/// The abort after every set failed, with the reasons of the last attempt.
fn all_aborted<T>(results: &[Result<T, Abort>]) -> Abort {
    let reasons: Vec<&str> = results.iter().filter_map(|r| r.as_ref().err().map(|e| e.0.as_str())).collect();
    Abort(format!("every set of three operators aborted, last: {}", reasons.join("; ")))
}

/// One attempt's line of the test log: each operator's result, pending request and next instance.
#[cfg(test)]
fn log_line<T>(what: &str, online: [usize; 3], ops: &[Operator], results: &[Result<T, Abort>]) -> String {
    let state: Vec<String> = ops
        .iter()
        .zip(results)
        .map(|(o, r)| {
            let res = r.as_ref().err().map_or("ok".to_string(), |e| e.0.clone());
            let pending = o.pending.map(|p| format!("{:02x}/{:?}/{:02x}{}", p.m[0], p.mode, p.s[0], if p.done { " done" } else { "" }));
            let next = o.next.as_ref().map(|n| format!("{} from {:02x}{}", n.idx, n.from[0], if o.consumed.contains(&n.from) { " used" } else { "" }));
            format!("op{} [{res}] pending {pending:?} next {next:?} last {:02x?}", o.id, o.last.map(|l| l[0]))
        })
        .collect();
    format!("{what} {online:?}:\n  {}", state.join("\n  "))
}

/// Runs `f` on all four operators, one thread each; the three online ones get their MPC link.
pub(crate) fn run<T: Send>(ops: &mut [Operator], online: [usize; 3], hooks: &Hooks, f: impl Fn(&mut Operator, &mut Net4, Option<Link>, &Roles) -> Result<T, Abort> + Sync) -> Vec<Result<T, Abort>> {
    let roles = Roles::new(online);
    let seeds = hooks.next_run();
    let mut links: Vec<Option<Link>> = ring().into_iter().map(Some).collect();
    let mut nets: Vec<Option<Net4>> = network().into_iter().map(Some).collect();
    let f = &f;
    std::thread::scope(|scope| {
        let handles: Vec<_> = ops
            .iter_mut()
            .map(|op| {
                let link = online.contains(&op.id).then(|| links[roles.party(op.id)].take().unwrap());
                let mut net = nets[op.id].take().unwrap();
                scope.spawn(move || {
                    #[cfg(test)]
                    mpc::prf::seed_thread(seeds.map(|s| s[op.id]));
                    let _ = seeds;
                    f(op, &mut net, link, &roles)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().expect("operator thread panicked")).collect()
    })
}

impl Cluster {
    /// The DKG with a kept subtree of height `b`: the seeds and coins by the four operators, then
    /// the MPC part, retried with each set of three online operators.
    pub fn dkg(b: usize) -> Result<(Self, [usize; 3], Report), Abort> {
        Self::dkg_with(b, Hooks::default())
    }

    pub(crate) fn dkg_with(b: usize, hooks: Hooks) -> Result<(Self, [usize; 3], Report), Abort> {
        let mut ops: Vec<Operator> = (0..4).map(Operator::new).collect();
        // The four-operator part: a cheater can stop it (it is not identified), not bias it.
        let first = run(&mut ops, SETS[0], &hooks, |op, net, _, _| {
            let mut meter = protocol::Meter::new(net);
            let coins = protocol::dkg_seeds_and_coins(op, net, b, &hooks)?;
            meter.mark("seed generation and coin tossing", None, net);
            Ok((coins, meter.phases))
        });
        if first.iter().any(|r| r.is_err()) {
            let reasons: Vec<&str> = first.iter().filter_map(|r| r.as_ref().err().map(|e| e.0.as_str())).collect();
            return Err(Abort(format!("seed generation and coin tossing aborted: {}", reasons.join("; "))));
        }
        let first: Vec<_> = first.into_iter().map(Result::unwrap).collect();
        for online in SETS {
            let results = run(&mut ops, online, &hooks, |op, net, link, roles| protocol::dkg_mpc(op, net, link, roles, b, &first[op.id].0, &hooks));
            if results.iter().all(|r| r.is_ok()) {
                let report = results.into_iter().zip(&first).map(|(r, (_, p))| [p.clone(), r.unwrap()].concat()).collect();
                return Ok((Self { ops, hooks, #[cfg(test)] log: vec![] }, online, report));
            }
            if online == SETS[3] {
                return Err(all_aborted(&results));
            }
        }
        unreachable!()
    }

    /// A request an operator holds unfinished (its `R0` may be open) and at least two operators
    /// hold, so an honest one does: it is finished before anything else. A lone claim (a cheater's
    /// stale or made-up record) is ignored, so it can't redirect the operators to another message
    /// or instance.
    fn unfinished(&self) -> Option<Pending> {
        let holders = |p: &Pending| self.ops.iter().filter(|o| o.pending.is_some_and(|q| (q.m, q.mode, q.s) == (p.m, p.mode, p.s))).count();
        self.ops.iter().filter_map(|o| o.pending).find(|p| !p.done && holders(p) >= 2)
    }

    /// Signs `m`, trying each set of three operators until one succeeds. An unfinished request is
    /// finished first (see [`Self::unfinished`]).
    pub fn sign(&mut self, m: &Message, mode: Mode) -> Result<(Signature, [usize; 3], Report), Abort> {
        if let Some(p) = self.unfinished().filter(|p| p.blocks(m, mode)) {
            self.sign(&p.m, p.mode)?;
        }
        let hooks = self.hooks.clone();
        for online in SETS {
            let results = run(&mut self.ops, online, &hooks, |op, net, link, roles| match link {
                Some(link) => protocol::sign(op, net, link, roles, m, mode, &hooks).map(Some),
                // The offline operator only learns the signature; its failure fails nothing.
                None => {
                    let _ = protocol::observe_signature(op, net, roles, &hooks);
                    Ok(None)
                }
            });
            #[cfg(test)]
            self.log.push(log_line(&format!("sign {:02x} {mode:?}", m[0]), online, &self.ops, &results));
            if online.iter().all(|&o| results[o].is_ok()) {
                let (sigs, report): (Vec<_>, Report) = results.into_iter().map(|r| r.unwrap().map_or((None, vec![]), |(s, p)| (Some(s), p))).unzip();
                let sigs: Vec<Signature> = sigs.into_iter().flatten().collect();
                assert!(sigs.windows(2).all(|w| w[0] == w[1]));
                return Ok((sigs[0].clone(), online, report));
            }
            if online == SETS[3] {
                return Err(all_aborted(&results));
            }
        }
        unreachable!()
    }

    /// Draws and computes the next instance, retried with each set of three operators. An
    /// unfinished request is finished first (see [`Self::unfinished`]).
    pub fn preprocess(&mut self) -> Result<([usize; 3], Report), Abort> {
        if let Some(p) = self.unfinished() {
            self.sign(&p.m, p.mode)?;
        }
        let hooks = self.hooks.clone();
        for online in SETS {
            let results = run(&mut self.ops, online, &hooks, |op, net, link, roles| protocol::preprocess(op, net, link, roles, &hooks));
            #[cfg(test)]
            self.log.push(log_line("preprocess", online, &self.ops, &results));
            if online.iter().all(|&o| results[o].is_ok()) {
                return Ok((online, results.into_iter().map(|r| r.unwrap_or_default()).collect()));
            }
            if online == SETS[3] {
                return Err(all_aborted(&results));
            }
        }
        unreachable!()
    }

    /// Plants cheating operators, for the tests.
    #[cfg(test)]
    pub(crate) fn set_cheats(&mut self, cheats: Vec<protocol::CheatSpec>) {
        self.hooks.cheats = cheats;
    }
}
