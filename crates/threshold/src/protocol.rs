//! The per-operator steps of the protocols (each operator runs them on its own thread).
//!
//! The online operators agree on what they are about to do before every opening, and what an
//! opening reveals is fixed by the agreement before it (the pending request's `s` fixes `R0`, hence
//! `R` and the FORS positions; the FORS key fixes the WOTS positions), so an aborted attempt never
//! opens more than the final signature reveals. The agreement that makes a request pending, and the
//! one on the public key, are Byzantine agreements of the four operators (n = 4 > 3f: unanimous; the
//! offline operator relays). The others are among the three online operators (a hash round and an
//! "ok" round): with one cheater among three, the two honest ones can be split (that needs n > 3f),
//! which only aborts the attempt.
//!
//! The operators' links must be private (encrypted) and direct: the offline operator knows all
//! three MPC keys of a session, so a relay through it would see every share.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use mpc::blake2s_circuit::{split_prefixes, th_circuit};
use mpc::engine::{Party, Shares};
use mpc::net::{Abort, Link, Stats, abort};
use mpc::prf::os_random;
use mpc::session::establish;
use sphincs::*;

use crate::net4::Net4;
pub use crate::operator::Mode;
use crate::operator::*;

/// Traffic, rounds and time of one phase, for one operator.
#[derive(Clone, Debug, Default)]
pub struct Phase {
    pub name: &'static str,
    pub stats: Stats,
    pub time: Duration,
}

/// Phase accounting: what the MPC link and the four-operator network carried since the last mark.
pub(crate) struct Meter {
    link: Stats,
    net: Stats,
    at: Instant,
    pub phases: Vec<Phase>,
}

impl Meter {
    pub fn new(net: &Net4) -> Self {
        Self { link: Stats::default(), net: net.stats, at: Instant::now(), phases: vec![] }
    }

    pub fn mark(&mut self, name: &'static str, party: Option<&Party>, net: &Net4) {
        let link = party.map_or(self.link, |p| p.link.stats);
        let stats = Stats {
            rounds: link.rounds - self.link.rounds + net.stats.rounds - self.net.rounds,
            bytes_sent: link.bytes_sent - self.link.bytes_sent + net.stats.bytes_sent - self.net.bytes_sent,
        };
        self.phases.push(Phase { name, stats, time: self.at.elapsed() });
        (self.link, self.net, self.at) = (link, net.stats, Instant::now());
    }
}

/// How an operator deviates, for the tests, in the steps outside the MPC.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum Lie {
    #[default]
    None,
    /// Sends another hash to one member in the online agreements.
    AgreeHash,
    /// Says "ok" to one member and "not ok" to the other in the online agreements: one honest
    /// member goes on, the other aborts.
    AgreeSplit,
    /// Reveals to one other holder a seed contribution that does not match its commitment.
    InconsistentReveal,
    /// Rushes the seed reveals (sees the others' first), then reveals so as to copy another seed.
    SeedCopy,
    /// As an online operator, sends the offline one a corrupted full copy (chain ends, instance).
    BadCopy,
    /// As the offline operator, rejects every instance it is sent.
    RefuseInstance,
    /// Claims a pending request with an `s` of its choice.
    FakePending,
    /// Flips a bit of its component in the opening of `R0`, of the FORS secrets, or of the WOTS values.
    FlipR0,
    FlipFors,
    FlipWots,
}

/// A cheating operator, for the tests: a fault on its MPC link, a cheat in its MPC steps, a lie in
/// the other steps.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct CheatSpec {
    pub op: usize,
    pub fault: Option<mpc::net::Fault>,
    pub cheat: mpc::engine::Cheat,
    pub lie: Lie,
}

/// The test hooks of a protocol run (none outside the tests).
#[derive(Clone, Default)]
pub(crate) struct Hooks {
    #[cfg(test)]
    pub cheats: Vec<CheatSpec>,
}

impl Hooks {
    #[inline(always)]
    pub(crate) fn lies(&self, op: usize, lie: Lie) -> bool {
        #[cfg(test)]
        {
            self.cheats.iter().any(|c| c.op == op && c.lie == lie)
        }
        #[cfg(not(test))]
        {
            let _ = (op, lie);
            false
        }
    }
}

/// An online operator's MPC party for a fresh session (established over the link).
#[cfg_attr(not(test), allow(unused_mut))]
pub(crate) fn party(op: &Operator, roles: &Roles, mut link: Link, hooks: &Hooks) -> Result<Party, Abort> {
    #[cfg(test)]
    let mine = hooks.cheats.iter().find(|c| c.op == op.id).copied();
    #[cfg(test)]
    if let Some(c) = mine {
        link.fault = c.fault;
    }
    #[cfg(not(test))]
    let _ = hooks;
    let session = establish(&mut link)?;
    let (k_own, k_prev) = op.mpc_keys(roles, session.bytes());
    let mut party = Party::new(link, k_own, k_prev, session, 1);
    #[cfg(test)]
    if let Some(c) = mine {
        party.cheat = c.cheat;
    }
    Ok(party)
}

/// `Th` on a batch of secret values, each under its own tweak (all ANDs left unverified).
fn mpc_th(party: &mut Party, pp: &PublicParam, tweaks: &[Tweak], x: &[Shares]) -> Result<Vec<Shares>, Abort> {
    party.set_n(tweaks.len())?;
    let prefixes: Vec<[u8; 32]> = tweaks
        .iter()
        .map(|t| {
            let mut p = [0u8; 32];
            p[..16].copy_from_slice(t);
            p[16..].copy_from_slice(pp);
            p
        })
        .collect();
    let (layout, pub_in) = split_prefixes(&prefixes);
    party.eval(&th_circuit(&layout).compile(), &pub_in, x)
}

/// Bit-sliced shares restricted to the values `first .. first + 64 * words` (`first` a multiple of 64).
fn columns(x: &[Shares], first: usize, words: usize) -> Vec<Shares> {
    let w = first / 64;
    x.iter().map(|s| Shares { own: s.own[w..w + words].to_vec(), prev: s.prev[w..w + words].to_vec() }).collect()
}

/// Opens bit-sliced values (128 wires over the batch).
fn open_sliced(party: &mut Party, shares: &[Shares]) -> Result<Vec<Digest>, Abort> {
    let n = party.n;
    Ok(unslice(&party.open(shares)?, n))
}

/// Opens values given as replicated components, packed into one wire; `flip` corrupts my own
/// component (a test cheater).
fn open_values(party: &mut Party, own: &[Digest], prev: &[Digest], flip: bool) -> Result<Vec<Digest>, Abort> {
    let count = own.len();
    party.set_n(128 * count)?;
    let mut own = pack(own);
    if flip {
        own[0] ^= 1;
    }
    let opened = party.open(&[Shares { own, prev: pack(prev) }])?;
    Ok(unpack(&opened[0], count))
}

/// The online operators agree on `value` before an opening: every member sends its hash to the
/// others, then whether all matched; each member continues only if every member said so. With three
/// members a traitor can still split the verdict, which only aborts the run: this agreement guards
/// an opening, while the one that makes a request pending is [`om1`].
fn agree(net: &mut Net4, members: &[usize], value: &[u8], hooks: &Hooks) -> Result<(), Abort> {
    let h = blake2s::hash(value);
    let me = net.id;
    // A lying member sends another hash to the member after it.
    let victim = hooks.lies(me, Lie::AgreeHash).then(|| members[(members.iter().position(|&o| o == me).unwrap() + 1) % members.len()]);
    let got = net.round(members, |to| if Some(to) == victim { blake2s::hash(b"other").to_vec() } else { h.to_vec() })?;
    let ok = members.iter().all(|&o| o == me || got[o] == h);
    let split = hooks.lies(me, Lie::AgreeSplit).then(|| members[(members.iter().position(|&o| o == me).unwrap() + 1) % members.len()]);
    let oks = net.round(members, |to| vec![(ok && Some(to) != split) as u8])?;
    if !ok || members.iter().any(|&o| o != me && oks[o] != [1]) {
        return abort("operators disagree");
    }
    Ok(())
}

/// Byzantine agreement of the four operators (Lamport, Shostak and Pease's OM(1): n = 4 tolerates
/// one traitor) on whether the `members` hold the same value: each member sends the hash of its
/// value to the three others, then every operator relays what it received; a member's hash is the
/// majority of its three reports. The honest operators reach the same verdict, and a missing message
/// counts as empty, so an operator that leaves can't split them either. Operators outside `members`
/// (no value) only relay.
fn om1(net: &mut Net4, members: &[usize], value: Option<&[u8]>, hooks: &Hooks) -> bool {
    let all = [0, 1, 2, 3];
    let me = net.id;
    let h = value.map(blake2s::hash);
    let next_member = members.iter().position(|&o| o == me).map(|i| members[(i + 1) % members.len()]);
    let victim = hooks.lies(me, Lie::AgreeHash).then_some(next_member).flatten();
    let mut got = net.round_lenient(&all, |to| match h {
        Some(_) if Some(to) == victim => blake2s::hash(b"other").to_vec(),
        Some(h) => h.to_vec(),
        None => vec![],
    });
    if let Some(h) = h {
        got[me] = h.to_vec();
    }
    let report = |v: &[u8]| -> Vec<u8> { if v.len() == 32 { v.to_vec() } else { vec![0; 32] } };
    let relay: Vec<u8> = members.iter().flat_map(|&o| report(&got[o])).collect();
    let split = hooks.lies(me, Lie::AgreeSplit).then_some((me + 1) % 4);
    let relays = net.round_lenient(&all, |to| if Some(to) == split { vec![0xff; relay.len()] } else { relay.clone() });
    let agreed: Vec<Vec<u8>> = members
        .iter()
        .enumerate()
        .map(|(k, &o)| {
            if o == me {
                return got[me].clone();
            }
            let mut reports = vec![report(&got[o])];
            for r in all.into_iter().filter(|&r| r != me && r != o) {
                reports.push(report(relays[r].get(32 * k..32 * k + 32).unwrap_or(&[])));
            }
            reports.iter().find(|x| reports.iter().filter(|y| y == x).count() >= 2).cloned().unwrap_or_default()
        })
        .collect();
    agreed.iter().all(|x| x.len() == 32 && x == &agreed[0])
}

/// The four-operator part of the DKG: the seeds, each generated jointly by its three holders, and
/// the coins for the public parameter and the surrogates. Returns `(P, s, surrogates)`.
pub(crate) fn dkg_seeds_and_coins(op: &mut Operator, net: &mut Net4, b: usize, hooks: &Hooks) -> Result<(PublicParam, u64, Vec<Digest>), Abort> {
    let all = [0, 1, 2, 3];
    let me = op.id;
    // 1. Seed k_t is H(t | r_a | r_b | r_c) for contributions of its three holders (every operator
    // but t), committed before they are revealed: no holder can relate it to another seed. Each
    // pair of operators exchanges its contributions to the two seeds both hold.
    let mine: [[u8; 32]; 4] = std::array::from_fn(|_| os_random());
    let commit = |t: usize, from: usize, r: &[u8]| -> Vec<u8> {
        let mut h = blake2s::Hasher::new();
        h.update(b"seed-commit").update(&[t as u8, from as u8]).update(r);
        h.finalize().to_vec()
    };
    let shared = |o: usize| (0..4).filter(move |&t| t != me && t != o);
    let commitments = net.round(&all, |o| shared(o).flat_map(|t| commit(t, me, &mine[t])).collect())?;
    let reveal = |o: usize| -> Vec<u8> {
        let mut out: Vec<u8> = shared(o).flat_map(|t| mine[t]).collect();
        if hooks.lies(me, Lie::InconsistentReveal) && o == (me + 1) % 4 {
            out[0] ^= 1;
        }
        out
    };
    let reveals = if hooks.lies(me, Lie::SeedCopy) {
        // Rushing: the others' contributions first; the best the cheater can do is reveal what it
        // committed (anything else is caught below), so it tries to copy k_{me+1} into k_{me-1}.
        #[cfg(test)]
        {
            net.round_rushing(&all, |o, got| {
                let mut out = reveal(o);
                if o != (me + 1) % 4 && o != (me + 3) % 4 {
                    // Its contribution to k_{me-1}, as seen by `o`: a value that makes it k_{me+1}'s.
                    if let Some(pos) = shared(o).position(|t| t == (me + 3) % 4) {
                        let copy = got[o].get(..32).map_or([0; 32], |s| s.try_into().unwrap());
                        out[32 * pos..32 * pos + 32].copy_from_slice(&copy);
                    }
                }
                out
            })?
        }
        #[cfg(not(test))]
        unreachable!()
    } else {
        net.round(&all, reveal)?
    };
    let mut contributions: [[Option<[u8; 32]>; 4]; 4] = [[None; 4]; 4];
    for t in (0..4).filter(|&t| t != me) {
        contributions[t][me] = Some(mine[t]);
    }
    for o in (0..4).filter(|&o| o != me) {
        let ts: Vec<usize> = shared(o).collect();
        if reveals[o].len() != 32 * ts.len() || commitments[o].len() != 32 * ts.len() {
            return abort("malformed seed contribution");
        }
        for (k, &t) in ts.iter().enumerate() {
            let r: [u8; 32] = reveals[o][32 * k..32 * k + 32].try_into().unwrap();
            if commit(t, o, &r) != commitments[o][32 * k..32 * k + 32] {
                return abort("a seed contribution does not match its commitment");
            }
            contributions[t][o] = Some(r);
        }
    }
    for t in (0..4).filter(|&t| t != me) {
        let mut h = blake2s::Hasher::new();
        h.update(b"seed").update(&[t as u8]);
        for o in (0..4).filter(|&o| o != t) {
            h.update(&contributions[t][o].unwrap());
        }
        op.seeds[t] = Some(h.finalize());
    }
    // Every pair compares the hashes of the seeds both hold (a contributor that revealed different
    // values to different holders is caught here).
    let hashes = |to: usize| (0..4).filter(|&t| t != me && t != to).flat_map(|t| blake2s::hash(op.seed(t))).collect::<Vec<u8>>();
    let got = net.round(&all, hashes)?;
    if (0..4).any(|o| o != me && got[o] != hashes(o)) {
        return abort("inconsistent seeds");
    }
    // 2. Commit-reveal coins for P (whose low bits place the kept subtree, as in `key_gen`) and the
    // surrogates; every reveal is exactly 32 bytes.
    let r: [u8; 32] = os_random();
    let commitments = net.broadcast(&all, &blake2s::hash(&r))?;
    let reveals = net.broadcast(&all, &r)?;
    let mut coins = blake2s::Hasher::new();
    coins.update(b"dkg-coins");
    for o in 0..4 {
        let ro: &[u8] = if o == me { &r } else { &reveals[o] };
        if ro.len() != 32 || (o != me && blake2s::hash(ro).as_slice() != commitments[o].as_slice()) {
            return abort("a reveal does not match its commitment");
        }
        coins.update(ro);
    }
    let coins = coins.finalize();
    let derive = |what: &[u8], i: u32| -> [u8; 16] {
        let mut h = blake2s::Hasher::new();
        h.update(&coins).update(what).update(&i.to_le_bytes());
        h.finalize()[..16].try_into().unwrap()
    };
    let pp: PublicParam = derive(b"P", 0);
    let s = if b == H { 0 } else { u64::from_le_bytes(pp[..8].try_into().unwrap()) & ((1 << (H - b)) - 1) };
    let surrogates: Vec<Digest> = (b..H).map(|level| derive(b"surrogate", level as u32)).collect();
    Ok((pp, s, surrogates))
}

/// The DKG's MPC part, for one set of three online operators (retried with another set on an
/// abort, with the same seeds and coins): the chains in MPC, their ends to the fourth operator,
/// the tree, and a unanimous agreement on the public key.
pub(crate) fn dkg_mpc(op: &mut Operator, net: &mut Net4, link: Option<Link>, roles: &Roles, b: usize, coins: &(PublicParam, u64, Vec<Digest>), hooks: &Hooks) -> Result<Vec<Phase>, Abort> {
    let all = [0, 1, 2, 3];
    let me = op.id;
    let (pp, s, surrogates) = (coins.0, coins.1, coins.2.clone());
    let mut meter = Meter::new(net);
    let leaves = 1usize << b;
    let leaf_of = |k: usize| ((s << b) + (k / V) as u64) as u32;
    let mut party = None;
    let mut ends: Vec<Digest> = vec![];
    if let Some(link) = link {
        let mut p = self::party(op, roles, link, hooks)?;
        let n = leaves * V;
        let (own, prev): (Vec<Digest>, Vec<Digest>) = (0..n).map(|k| op.shares(roles, |seed| term(&pp, seed, &wots_secret_tweak(leaf_of(k), k % V)))).unzip();
        let mut x = sliced_shares(&own, &prev);
        for to in 1..CHAIN_LEN {
            let tweaks: Vec<Tweak> = (0..n).map(|k| chain_tweak(leaf_of(k), k % V, to)).collect();
            x = mpc_th(&mut p, &pp, &tweaks, &x)?;
            // Verified after every step, to bound the transcript.
            p.verify()?;
        }
        ends = open_sliced(&mut p, &x)?;
        meter.mark("MPC: 3 chain steps, verify, open the ends", Some(&p), net);
        party = Some(p);
    }
    // The fourth operator gets the ends in full from two online operators and hashed from the third,
    // and keeps the copy that a second source confirms (one cheater cannot stop it).
    let mut bytes: Vec<u8> = ends.concat();
    if hooks.lies(me, Lie::BadCopy) && !bytes.is_empty() {
        bytes[0] ^= 1;
    }
    let full = |o: usize| roles.online[..2].contains(&o);
    let got = net.round(&all, |to| match to == roles.offline {
        true if full(me) => bytes.clone(),
        true => blake2s::hash(&bytes).to_vec(),
        false => vec![],
    })?;
    if me == roles.offline {
        let [a, b2, c] = roles.online;
        let confirmed = |x: &[u8], other_full: &[u8]| x.len() == leaves * V * N && (blake2s::hash(x).as_slice() == got[c].as_slice() || x == other_full);
        let pick = if confirmed(&got[a], &got[b2]) { &got[a] } else if confirmed(&got[b2], &got[a]) { &got[b2] } else { return abort("no two online operators sent the same chain ends") };
        ends = pick.as_chunks::<N>().0.to_vec();
    }
    // Everyone builds the tree; the four agree (unanimously) on the public key.
    let ends: Vec<[Digest; V]> = ends.as_chunks::<V>().0.to_vec();
    let leaf_hashes = (0..leaves).map(|l| wots_leaf_hash(&pp, ((s << b) + l as u64) as u32, &ends[l])).collect();
    let tree = XmssTree::from_leaves(&pp, b, s, leaf_hashes, surrogates);
    let pk = PublicKey { root: tree.root, public_param: pp };
    if !om1(net, &[0, 1, 2, 3], Some(&pk.to_bytes()), hooks) {
        return abort("the operators hold different public keys");
    }
    meter.mark("ends to the 4th operator, tree, agree on pk", party.as_ref(), net);
    op.last = Some(pk.root);
    op.key = Some(KeyState { pk, tree, ends });
    Ok(meter.phases)
}

/// Computes the FORS instance at leaf `idx` and the WOTS signature of its key, in MPC.
///
/// The FORS leaves and the first WOTS chain step run in one batch, and the second chain step
/// after it (the chain steps don't depend on the FORS key, so 2 hash depths instead of 3). Only the
/// FORS leaves and each chain's signed position are opened, after the root, counter and positions
/// are agreed.
fn compute_instance(op: &Operator, net: &mut Net4, party: &mut Party, roles: &Roles, idx: u64, hooks: &Hooks) -> Result<Instance, Abort> {
    let key = op.key();
    let pp = key.pk.public_param;
    let e = idx as u32;
    let n_fors = K * FORS_LEAVES;
    let fors_secret = |t: usize| op.shares(roles, |seed| term(&pp, seed, &fors_secret_tweak(idx, t / FORS_LEAVES, t % FORS_LEAVES)));
    let chain_start = |i: usize| op.shares(roles, |seed| term(&pp, seed, &wots_secret_tweak(e, i)));
    let (own, prev): (Vec<Digest>, Vec<Digest>) = (0..n_fors).map(fors_secret).chain((0..V).map(chain_start)).unzip();
    let starts = sliced_shares(&own[n_fors..], &prev[n_fors..]);
    let tweaks: Vec<Tweak> = (0..n_fors).map(|t| fors_leaf_tweak(idx, t / FORS_LEAVES, t % FORS_LEAVES)).chain((0..V).map(|i| chain_tweak(e, i, 1))).collect();
    let step1 = mpc_th(party, &pp, &tweaks, &sliced_shares(&own, &prev))?;
    party.verify()?;
    let leaves = unslice(&party.open(&columns(&step1, 0, n_fors / 64))?, n_fors);
    let step1 = columns(&step1, n_fors, 1);
    let step2 = mpc_th(party, &pp, &(0..V).map(|i| chain_tweak(e, i, 2)).collect::<Vec<_>>(), &step1)?;
    party.verify()?;
    // In the clear: the FORS key, the WOTS+C counter; the three agree before any WOTS value opens.
    let forest = ForsForest::from_leaves(&pp, idx, &leaves);
    let (counter, x) = wots_encode(&pp, e, &forest.key).ok_or(Abort("no admissible encoding".into()))?;
    let mut agreed = idx.to_le_bytes().to_vec();
    agreed.extend_from_slice(&forest.key);
    agreed.extend_from_slice(&counter.to_le_bytes());
    agreed.extend_from_slice(&x);
    agree(net, &roles.online, &agreed, hooks)?;
    // Open each chain at its signed position (position 3 is the public end).
    let masked = |values: &[Shares], pos: u8| -> Vec<Shares> {
        let m = (0..V).fold(0u64, |acc, i| acc | (u64::from(x[i] == pos) << i));
        values.iter().map(|s| Shares { own: vec![s.own[0] & m], prev: vec![s.prev[0] & m] }).collect()
    };
    let mut to_open = [masked(&starts, 0), masked(&step1, 1), masked(&step2, 2)].concat();
    if hooks.lies(op.id, Lie::FlipWots) {
        to_open[0].own[0] ^= 1;
    }
    let opened = party.open(&to_open)?;
    let by_pos: Vec<Vec<Digest>> = opened.chunks(8 * N).map(|bits| unslice(bits, V)).collect();
    let local = (idx - (key.tree.s << key.tree.b)) as usize;
    let wots: [Digest; V] = std::array::from_fn(|i| if x[i] == 3 { key.ends[local][i] } else { by_pos[x[i] as usize][i] });
    for i in 0..V {
        let from = x[i] as usize;
        if chain(&pp, e, i, from, CHAIN_LEN - 1 - from, wots[i]) != key.ends[local][i] {
            return abort("an opened WOTS value does not reach its chain end");
        }
    }
    Ok(Instance { forest: Arc::new(forest), counter, wots })
}

/// The least counter whose randomizer `R = Th(P, tw(ctr), R0)` gives a leaf index accepted by
/// `target`, searched on all cores in batches (every operator finds the same one).
pub fn grind(pp: &PublicParam, root: &Digest, r0: &Digest, m: &Message, target: &(dyn Fn(u64) -> bool + Sync)) -> (u32, Randomizer) {
    const BATCH: usize = 4096;
    let randomizer_tweak = |ctr: u32| tweak(TWEAK_THRESHOLD, 0, 0, TAG_RAND, ctr);
    let threads = std::thread::available_parallelism().map_or(1, |p| p.get());
    let next = AtomicU64::new(0);
    let best = AtomicU64::new(u64::MAX);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let mut r_in = vec![0u8; BATCH * 64];
                let mut rs = vec![0u8; BATCH * 32];
                let mut d_in = vec![0u8; BATCH * 128];
                let mut ds = vec![0u8; BATCH * 32];
                loop {
                    let first = next.fetch_add(1, Ordering::Relaxed) * BATCH as u64;
                    if first >= best.load(Ordering::Relaxed) || first > u64::from(u32::MAX) {
                        return;
                    }
                    // R = Th(P, tw(ctr), R0): tw || P || R0.
                    for k in 0..BATCH {
                        let slot = &mut r_in[64 * k..64 * k + 48];
                        slot[..16].copy_from_slice(&randomizer_tweak((first + k as u64) as u32));
                        slot[16..32].copy_from_slice(pp);
                        slot[32..48].copy_from_slice(r0);
                    }
                    blake2s::hash_many_padded(&r_in, 48, &mut rs);
                    // The first digest block, as `digest_block`: tw || P || R || root || m.
                    for k in 0..BATCH {
                        let slot = &mut d_in[128 * k..128 * k + 96];
                        slot[..16].copy_from_slice(&tweak(TWEAK_MSG, 0, 0, 0, 0));
                        slot[16..32].copy_from_slice(pp);
                        slot[32..48].copy_from_slice(&rs[32 * k..32 * k + 16]);
                        slot[48..64].copy_from_slice(root);
                        slot[64..96].copy_from_slice(m);
                    }
                    blake2s::hash_many_padded(&d_in, 96, &mut ds);
                    if let Some(k) = (0..BATCH).find(|&k| target(index_of_block(ds[32 * k..32 * k + 32].try_into().unwrap()))) {
                        best.fetch_min(first + k as u64, Ordering::Relaxed);
                    }
                }
            });
        }
    });
    let ctr = u32::try_from(best.load(Ordering::Relaxed)).expect("no counter found");
    let rho = th(pp, &randomizer_tweak(ctr), r0);
    assert!(target(digest_index(pp, root, &rho, m)));
    (ctr, rho)
}

/// The request's `s`: the pending one if this operator holds it or another member claims it (all
/// claims must match); otherwise fresh, by commit-reveal among the members. Two rounds either way.
fn request_seed(op: &Operator, net: &mut Net4, members: &[usize], m: &Message, mode: Mode, hooks: &Hooks) -> Result<[u8; 32], Abort> {
    let me = op.id;
    let mut pending = op.pending.filter(|p| (p.m, p.mode) == (*m, mode)).map(|p| p.s);
    if hooks.lies(me, Lie::FakePending) {
        pending = Some([0x5a; 32]);
    }
    let r: [u8; 32] = os_random();
    let commitment = |r: &[u8]| {
        let mut h = blake2s::Hasher::new();
        h.update(b"request-seed").update(m).update(&[mode as u8]).update(r);
        h.finalize()
    };
    let first = match pending {
        Some(s) => [b"P".as_slice(), &s].concat(),
        None => [b"C".as_slice(), &commitment(&r)].concat(),
    };
    let got = net.broadcast(members, &first)?;
    let others: Vec<usize> = members.iter().copied().filter(|&o| o != me).collect();
    if others.iter().any(|&o| got[o].len() != 33) {
        return abort("malformed request seed message");
    }
    let claims: Vec<[u8; 32]> = others.iter().filter(|&&o| got[o][0] == b'P').map(|&o| got[o][1..].try_into().unwrap()).collect();
    let fresh = pending.is_none() && claims.is_empty();
    let reveals = net.broadcast(members, if fresh { &r } else { &[] })?;
    if let Some(s) = pending {
        if claims.iter().any(|c| c != &s) {
            return abort("another member claims another pending request");
        }
        return Ok(s);
    }
    if !claims.is_empty() {
        // A request whose R0 may be open is held by both honest online operators of that run (the
        // agreement is unanimous), so every set of three has a holder, who refuses any other s. A
        // claim no holder backs (a cheater's) only picks s for a request never opened: R0 stays
        // unpredictable, and it fixes s for good.
        if claims.iter().all(|c| c == &claims[0]) {
            return Ok(claims[0]);
        }
        return abort("members claim different pending requests");
    }
    let mut h = blake2s::Hasher::new();
    h.update(b"request-s");
    for &o in members {
        let ro: &[u8] = if o == me { &r } else { &reveals[o] };
        if ro.len() != 32 || (o != me && commitment(ro).as_slice() != &got[o][1..]) {
            return abort("a request seed reveal does not match its commitment");
        }
        h.update(ro);
    }
    Ok(h.finalize())
}

/// Signs `m`, for one online operator.
///
/// 1. The members fix the request's `s` (the pending one, or a fresh one) and the four operators
///    agree on `(m, mode, s, session, target)`; the request is then pending until finished.
/// 2. They open `R0 = XOR_t H(k_t, msg, H(m | s))` and grind `R`; they agree on `(R, idx, u)`.
/// 3. Vanilla: the instance is computed in MPC; preprocessed: it is the checked `next`.
/// 4. They open the 24 FORS secrets; the signature is assembled and verified, and sent to the
///    offline operator (which keeps the copy two online operators agree on).
///
/// Any retry of the request (any three operators) uses the same `s`, hence the same `R0` and the
/// same signature: once `R0` is opened, the signature is always finished.
pub(crate) fn sign(op: &mut Operator, net: &mut Net4, link: Link, roles: &Roles, m: &Message, mode: Mode, hooks: &Hooks) -> Result<(Signature, Vec<Phase>), Abort> {
    let key = op.key().clone();
    let (pp, root) = (key.pk.public_param, key.pk.root);
    let members = roles.online;
    let mut meter = Meter::new(net);
    // Local checks first: nothing is sent unless this request may run.
    if op.pending.is_some_and(|p| p.blocks(m, mode)) {
        return abort("another request is pending");
    }
    // A rerun of the request this operator finished (another one may not have) gives the same
    // signature, with the same instance.
    let rerun = op.pending.is_some_and(|p| p.done && (p.m, p.mode) == (*m, mode));
    let next = match mode {
        Mode::Vanilla => None,
        Mode::Preprocessed => match &op.next {
            Some(n) if rerun || !op.consumed.contains(&n.from) => Some((n.idx, n.inst.clone())),
            _ => return abort("no preprocessed instance"),
        },
    };
    let mut party = party(op, roles, link, hooks)?;
    let s = request_seed(op, net, &members, m, mode, hooks)?;
    let mut what = m.to_vec();
    what.push(mode as u8);
    what.extend_from_slice(&s);
    what.extend_from_slice(party.session());
    if let Some((idx, inst)) = &next {
        what.extend_from_slice(&idx.to_le_bytes());
        what.extend_from_slice(&inst.forest.key);
    }
    // Unanimous: the honest online operators either all hold the request pending or none does.
    if !om1(net, &members, Some(&what), hooks) {
        return abort("operators disagree on the request");
    }
    op.pending = Some(Pending { m: *m, mode, s, done: false });
    let (own, prev) = op.shares(roles, |seed| tagged_term(&pp, seed, TAG_MSG, &msg_data(m, &s)));
    let r0 = open_values(&mut party, &[own], &[prev], hooks.lies(op.id, Lie::FlipR0))?[0];
    let tree = &key.tree;
    let (_, rho) = match &next {
        None => grind(&pp, &root, &r0, m, &|idx| tree.contains(idx)),
        Some((target, _)) => grind(&pp, &root, &r0, m, &|idx| idx == *target),
    };
    #[cfg(test)]
    op.seen_r.push(rho);
    let (idx, u) = message_digest(&pp, &root, &rho, m);
    let mut what = rho.to_vec();
    what.extend_from_slice(&idx.to_le_bytes());
    what.extend(u.iter().flat_map(|x| x.to_le_bytes()));
    agree(net, &members, &what, hooks)?;
    let inst = match next {
        None => {
            meter.mark("agree, open R0, grind into the kept subtree", Some(&party), net);
            let inst = compute_instance(op, net, &mut party, roles, idx, hooks)?;
            meter.mark("MPC: FORS instance and WOTS signature", Some(&party), net);
            inst
        }
        Some((_, inst)) => {
            meter.mark("agree, open R0, grind onto the next instance", Some(&party), net);
            inst
        }
    };
    let (own, prev): (Vec<Digest>, Vec<Digest>) = (0..K).map(|kappa| op.shares(roles, |seed| term(&pp, seed, &fors_secret_tweak(idx, kappa, u[kappa] as usize)))).unzip();
    let secrets = open_values(&mut party, &own, &prev, hooks.lies(op.id, Lie::FlipFors))?;
    if (0..K).any(|kappa| fors_leaf(&pp, idx, kappa, u[kappa] as usize, &secrets[kappa]) != inst.forest.leaf(kappa, u[kappa] as usize)) {
        return abort("an opened FORS secret does not match its leaf");
    }
    let sig = Signature {
        randomizer: rho,
        fors: ForsOpening { secrets: secrets.try_into().unwrap(), paths: inst.forest.paths(&u) },
        counter: inst.counter,
        wots: inst.wots,
        path: tree.path(idx),
    };
    if verify(&key.pk, m, &sig).is_err() {
        return abort("the assembled signature does not verify");
    }
    finished(op, m, &sig, mode);
    // The offline operator learns the signature (and with it the new `last`).
    let bytes = [m.as_slice(), &sig.to_bytes()].concat();
    net.round(&[0, 1, 2, 3], |to| if to == roles.offline { bytes.clone() } else { vec![] })?;
    meter.mark("open the 24 FORS secrets", Some(&party), net);
    Ok((sig, meter.phases))
}

/// A signature of this request is finished: the request is done, its randomizer draws the next
/// instance, and a preprocessed instance is consumed (kept only for reruns of this request).
fn finished(op: &mut Operator, m: &Message, sig: &Signature, mode: Mode) {
    if let Some(p) = op.pending.as_mut()
        && (p.m, p.mode) == (*m, mode)
    {
        p.done = true;
    }
    op.last = Some(sig.randomizer);
    if mode == Mode::Preprocessed
        && let Some(n) = &op.next
        && !op.consumed.contains(&n.from)
    {
        op.consumed.push(n.from);
    }
}

/// The offline operator's side of a signing attempt: it relays in the agreement on the request, then
/// keeps a signature that two online operators sent and that verifies. Every online operator
/// finished it before sending, so its own record of the request is no longer needed.
pub(crate) fn observe_signature(op: &mut Operator, net: &mut Net4, roles: &Roles, hooks: &Hooks) -> Result<(), Abort> {
    om1(net, &roles.online, None, hooks);
    let got = net.round(&[0, 1, 2, 3], |_| vec![])?;
    let [a, b, c] = roles.online.map(|o| got[o].clone());
    let agreed = if a == b || a == c { a } else if b == c { b } else { return abort("no two online operators sent the same signature") };
    if agreed.len() != 32 + SIG_SIZE {
        return abort("malformed signature");
    }
    let m: Message = agreed[..32].try_into().unwrap();
    let sig = Signature::from_bytes(agreed[32..].try_into().unwrap()).ok_or(Abort("malformed signature".into()))?;
    if verify(&op.key().pk, &m, &sig).is_err() {
        return abort("the signature does not verify");
    }
    let pp = op.key().pk.public_param;
    let idx = digest_index(&pp, &op.key().pk.root, &sig.randomizer, &m);
    let mode = if op.next.as_ref().is_some_and(|n| n.idx == idx) { Mode::Preprocessed } else { Mode::Vanilla };
    finished(op, &m, &sig, mode);
    if op.pending.is_some_and(|p| (p.m, p.mode) == (m, mode)) {
        op.pending = None;
    }
    Ok(())
}

/// Draws the next instance as the XOR of the terms of `last` (the randomizer of the last finished
/// signature, which never repeats) and computes it; the online operators then send its public data
/// to the fourth, which checks it and keeps it only if it checks (its verdict is its own: it never
/// blocks the others).
pub(crate) fn preprocess(op: &mut Operator, net: &mut Net4, link: Option<Link>, roles: &Roles, hooks: &Hooks) -> Result<Vec<Phase>, Abort> {
    let key = op.key().clone();
    let pp = key.pk.public_param;
    let me = op.id;
    let mut meter = Meter::new(net);
    op.next = None;
    let mut next = None;
    if let Some(link) = link {
        if op.pending.is_some_and(|p| !p.done) {
            return abort("a request is pending");
        }
        let last = op.last.expect("no last randomizer");
        let mut party = party(op, roles, link, hooks)?;
        let mut what = last.to_vec();
        what.extend_from_slice(party.session());
        agree(net, &roles.online, &what, hooks)?;
        let mut data = [0u8; 32];
        data[..16].copy_from_slice(&last);
        let (own, prev) = op.shares(roles, |seed| tagged_term(&pp, seed, TAG_NEXT, &data));
        let drawn = open_values(&mut party, &[own], &[prev], false)?[0];
        let idx = (key.tree.s << key.tree.b) + (u64::from_le_bytes(drawn[..8].try_into().unwrap()) & ((1 << key.tree.b) - 1));
        next = Some(Next { idx, inst: compute_instance(op, net, &mut party, roles, idx, hooks)?, from: last });
        meter.mark("MPC: draw, FORS instance and WOTS signature", Some(&party), net);
    }
    // The public data, in full from the first online operator and hashed from the two others.
    let mut data = vec![];
    if let Some(Next { idx, inst, .. }) = &next {
        data.extend(idx.to_le_bytes());
        data.extend(inst.counter.to_le_bytes());
        data.extend(inst.wots.concat());
        data.extend((0..K * FORS_LEAVES).flat_map(|t| inst.forest.leaf(t / FORS_LEAVES, t % FORS_LEAVES)));
        if hooks.lies(me, Lie::BadCopy) {
            data[20] ^= 1;
        }
    }
    let got = net.round(&[0, 1, 2, 3], |to| match to == roles.offline {
        true if me == roles.online[0] => data.clone(),
        true => blake2s::hash(&data).to_vec(),
        false => vec![],
    })?;
    if me == roles.offline {
        next = check_instance(op, &got, roles).filter(|_| !hooks.lies(me, Lie::RefuseInstance));
        meter.mark("receive and check the instance", None, net);
    } else {
        meter.mark("send the instance to the 4th operator", None, net);
    }
    op.next = next;
    Ok(meter.phases)
}

/// The offline operator's check of a preprocessed instance: a copy confirmed by a second online
/// operator, inside the kept subtree, whose WOTS signature signs its FORS key and reaches the leaf.
fn check_instance(op: &Operator, got: &[Vec<u8>; 4], roles: &Roles) -> Option<Next> {
    let key = op.key();
    let pp = key.pk.public_param;
    let d = &got[roles.online[0]];
    let h = blake2s::hash(d);
    if d.len() != 12 + (V + K * FORS_LEAVES) * N || !roles.online[1..].iter().any(|&o| got[o].as_slice() == h.as_slice()) {
        return None;
    }
    let idx = u64::from_le_bytes(d[..8].try_into().unwrap());
    let counter = u32::from_le_bytes(d[8..12].try_into().unwrap());
    let wots: [Digest; V] = d[12..12 + V * N].as_chunks::<N>().0.try_into().unwrap();
    if !key.tree.contains(idx) {
        return None;
    }
    let forest = ForsForest::from_leaves(&pp, idx, d[12 + V * N..].as_chunks::<N>().0);
    let local = (idx - (key.tree.s << key.tree.b)) as usize;
    let ok = wots_recover(&pp, idx as u32, &forest.key, counter, &wots) == Some(wots_leaf_hash(&pp, idx as u32, &key.ends[local]));
    let from = op.last?;
    ok.then(|| Next { idx, inst: Instance { forest: Arc::new(forest), counter, wots }, from })
}
