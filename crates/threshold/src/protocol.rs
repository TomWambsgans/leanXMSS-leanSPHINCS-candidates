//! The per-operator steps of the protocols (each operator runs them on its own thread).

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use mpc::blake2s_circuit::{split_prefixes, th_circuit};
use mpc::engine::{Cheat, Party, Shares};
use mpc::net::{Abort, Fault, Link, Stats, abort};
use mpc::prf::os_random;
use sphincs::*;

use crate::net4::Net4;
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
    pub fn new() -> Self {
        Self { link: Stats::default(), net: Stats::default(), at: Instant::now(), phases: vec![] }
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

/// A cheating operator, for the tests: its MPC link flips a bit, or its AND messages are wrong.
#[derive(Clone, Copy, Debug)]
pub struct CheatSpec {
    pub op: usize,
    pub fault: Option<Fault>,
    pub cheat: Cheat,
}

/// An online operator's MPC party for a session.
pub(crate) fn party(op: &Operator, roles: &Roles, link: Link, session: [u8; 16], cheats: &[CheatSpec]) -> Party {
    let (k_own, k_prev) = op.mpc_keys(roles, &session);
    let mut party = Party::new(link, k_own, k_prev, session, 1);
    for c in cheats.iter().filter(|c| c.op == op.id) {
        party.link.fault = c.fault;
        party.cheat = c.cheat;
    }
    party
}

/// `Th` on a batch of secret values, each under its own tweak (all ANDs left unverified).
fn mpc_th(party: &mut Party, pp: &PublicParam, tweaks: &[Tweak], x: &[Shares]) -> Result<Vec<Shares>, Abort> {
    party.set_n(tweaks.len());
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

/// Opens values given as replicated components, packed into one wire.
fn open_values(party: &mut Party, own: &[Digest], prev: &[Digest]) -> Result<Vec<Digest>, Abort> {
    party.set_n(128 * own.len());
    let opened = party.open(&[Shares { own: pack(own), prev: pack(prev) }])?;
    Ok(unpack(&opened[0], own.len()))
}

/// Every member sends the hash of `value` to the others; all must agree.
fn agree(net: &mut Net4, members: &[usize], value: &[u8]) -> Result<(), Abort> {
    let h = blake2s::hash(value);
    let got = net.broadcast(members, &h)?;
    if members.iter().any(|&o| o != net.id && got[o] != h) {
        return abort("operators disagree");
    }
    Ok(())
}

/// The DKG, for one operator; `link` is its MPC link if it is one of the three online operators.
pub(crate) fn dkg(op: &mut Operator, net: &mut Net4, link: Option<Link>, roles: &Roles, b: usize, cheats: &[CheatSpec]) -> Result<Vec<Phase>, Abort> {
    let all = [0, 1, 2, 3];
    let me = op.id;
    let mut meter = Meter::new();
    // 1. Seed k_t is sampled by operator t + 1 and sent to the two other holders; every pair compares
    // the hashes of the seeds both hold.
    let dealt: Seed = os_random();
    let got = net.round(&all, |to| if to != (me + 3) % 4 { dealt.to_vec() } else { vec![] })?;
    for t in (0..4).filter(|&t| t != me) {
        let dealer = (t + 1) % 4;
        op.seeds[t] = Some(if dealer == me { dealt } else { got[dealer].as_slice().try_into().map_err(|_| Abort("malformed seed".into()))? });
    }
    let hashes = |to: usize| (0..4).filter(|&t| t != me && t != to).flat_map(|t| blake2s::hash(op.seed(t))).collect::<Vec<u8>>();
    let got = net.round(&all, hashes)?;
    if (0..4).any(|o| o != me && got[o] != hashes(o)) {
        return abort("inconsistent seed dealing");
    }
    // 2. Commit-reveal coins for P (whose low bits place the kept subtree, as in `key_gen`) and the surrogates.
    let r: [u8; 32] = os_random();
    let commitments = net.broadcast(&all, &blake2s::hash(&r))?;
    let reveals = net.broadcast(&all, &r)?;
    let mut coins = blake2s::Hasher::new();
    coins.update(b"dkg-coins");
    for o in 0..4 {
        let ro: &[u8] = if o == me { &r } else { &reveals[o] };
        if o != me && blake2s::hash(ro).as_slice() != commitments[o].as_slice() {
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
    meter.mark("seed dealing and coin tossing", None, net);
    // 3. The three online operators hash the chains to their ends in MPC, verify, and open the ends.
    let leaves = 1usize << b;
    let leaf_of = |k: usize| ((s << b) + (k / V) as u64) as u32;
    let mut party = None;
    let mut ends: Vec<Digest> = vec![];
    if let Some(link) = link {
        let mut p = self::party(op, roles, link, derive(b"session", 0), cheats);
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
    // 4. The fourth operator gets the ends from all three and compares.
    let bytes: Vec<u8> = ends.concat();
    let got = net.round(&all, |to| if to == roles.offline { bytes.clone() } else { vec![] })?;
    if me == roles.offline {
        let first = &got[roles.online[0]];
        if roles.online.iter().any(|&o| &got[o] != first) || first.len() != leaves * V * N {
            return abort("the online operators sent different chain ends");
        }
        ends = first.as_chunks::<N>().0.to_vec();
    }
    // 5. Everyone builds the tree and compares the public key.
    let ends: Vec<[Digest; V]> = ends.as_chunks::<V>().0.to_vec();
    let leaf_hashes = (0..leaves).map(|l| wots_leaf_hash(&pp, ((s << b) + l as u64) as u32, &ends[l])).collect();
    let tree = XmssTree::from_leaves(&pp, b, s, leaf_hashes, surrogates);
    let pk = PublicKey { root: tree.root, public_param: pp };
    agree(net, &all, &pk.to_bytes())?;
    meter.mark("ends to the 4th operator, tree, compare pk", party.as_ref(), net);
    op.key = Some(KeyState { pk, tree, ends });
    Ok(meter.phases)
}

/// Computes the FORS instance at leaf `idx` and the WOTS signature of its key, in MPC.
///
/// The FORS leaves and the first WOTS chain step run in one batch, and the second chain step
/// after it (the chain steps don't depend on the FORS key, so 2 hash depths instead of 3). Only the
/// FORS leaves and each chain's signed position are opened, after the root, counter and positions
/// are agreed.
fn compute_instance(op: &Operator, net: &mut Net4, party: &mut Party, roles: &Roles, idx: u64) -> Result<Instance, Abort> {
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
    // In the clear: the FORS key, the WOTS+C counter; the three compare.
    let forest = ForsForest::from_leaves(&pp, idx, &leaves);
    let (counter, x) = wots_encode(&pp, e, &forest.key).ok_or(Abort("no admissible encoding".into()))?;
    let mut agreed = forest.key.to_vec();
    agreed.extend_from_slice(&counter.to_le_bytes());
    agreed.extend_from_slice(&x);
    agree(net, &roles.online, &agreed)?;
    // Open each chain at its signed position (position 3 is the public end).
    let masked = |values: &[Shares], pos: u8| -> Vec<Shares> {
        let m = (0..V).fold(0u64, |acc, i| acc | (u64::from(x[i] == pos) << i));
        values.iter().map(|s| Shares { own: vec![s.own[0] & m], prev: vec![s.prev[0] & m] }).collect()
    };
    let opened = party.open(&[masked(&starts, 0), masked(&step1, 1), masked(&step2, 2)].concat())?;
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

/// How the signature's instance is chosen.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Grind into the kept subtree, then compute the selected instance in MPC.
    Vanilla,
    /// Grind until the message lands on the instance computed in advance.
    Preprocessed,
}

/// Signs `m`, for one online operator. A retry (any three operators) reproduces the same `R0`,
/// hence the same signature: once `R0` is opened, the signature is always finished.
pub(crate) fn sign(op: &mut Operator, net: &mut Net4, party: &mut Party, roles: &Roles, m: &Message, mode: Mode) -> Result<(Signature, Vec<Phase>), Abort> {
    let key = op.key().clone();
    let (pp, root) = (key.pk.public_param, key.pk.root);
    let mut meter = Meter::new();
    // Opening R0 also checks that the three agree on m: each term's two holders must send the same value.
    let (own, prev) = op.shares(roles, |seed| tagged_term(&pp, seed, TAG_MSG, m));
    let r0 = open_values(party, &[own], &[prev])?[0];
    let tree = &key.tree;
    let (rho, inst) = match mode {
        Mode::Vanilla => {
            let (_, rho) = grind(&pp, &root, &r0, m, &|idx| tree.contains(idx));
            meter.mark("open R0, grind into the kept subtree", Some(party), net);
            let inst = compute_instance(op, net, party, roles, digest_index(&pp, &root, &rho, m))?;
            meter.mark("MPC: FORS instance and WOTS signature", Some(party), net);
            (rho, inst)
        }
        Mode::Preprocessed => {
            let (target, inst) = op.next.clone().ok_or(Abort("no preprocessed instance".into()))?;
            let (_, rho) = grind(&pp, &root, &r0, m, &|idx| idx == target);
            meter.mark("open R0, grind onto the next instance", Some(party), net);
            (rho, inst)
        }
    };
    let (idx, u) = message_digest(&pp, &root, &rho, m);
    let (own, prev): (Vec<Digest>, Vec<Digest>) = (0..K).map(|kappa| op.shares(roles, |seed| term(&pp, seed, &fors_secret_tweak(idx, kappa, u[kappa] as usize)))).unzip();
    let secrets = open_values(party, &own, &prev)?;
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
    meter.mark("open the 24 FORS secrets", Some(party), net);
    Ok((sig, meter.phases))
}

/// Draws the next instance as the XOR of the terms of `last` (the previous randomizer) and
/// computes it; the three online operators then send its public data to the fourth, who checks it.
pub(crate) fn preprocess(op: &mut Operator, net: &mut Net4, party: Option<&mut Party>, roles: &Roles, last: &Randomizer) -> Result<Vec<Phase>, Abort> {
    let key = op.key().clone();
    let pp = key.pk.public_param;
    let mut meter = Meter::new();
    let mut next = None;
    if let Some(party) = party {
        let mut data = [0u8; 32];
        data[..16].copy_from_slice(last);
        let (own, prev) = op.shares(roles, |seed| tagged_term(&pp, seed, TAG_NEXT, &data));
        let drawn = open_values(party, &[own], &[prev])?[0];
        let idx = (key.tree.s << key.tree.b) + (u64::from_le_bytes(drawn[..8].try_into().unwrap()) & ((1 << key.tree.b) - 1));
        next = Some((idx, compute_instance(op, net, party, roles, idx)?));
        meter.mark("MPC: draw, FORS instance and WOTS signature", Some(party), net);
    }
    // The public data: index, WOTS+C counter and signature, FORS leaves.
    let mut data = vec![];
    if let Some((idx, inst)) = &next {
        data.extend(idx.to_le_bytes());
        data.extend(inst.counter.to_le_bytes());
        data.extend(inst.wots.concat());
        data.extend((0..K * FORS_LEAVES).flat_map(|t| inst.forest.leaf(t / FORS_LEAVES, t % FORS_LEAVES)));
    }
    let got = net.round(&[0, 1, 2, 3], |to| if to == roles.offline { data.clone() } else { vec![] })?;
    if op.id == roles.offline {
        let d = &got[roles.online[0]];
        if roles.online.iter().any(|&o| &got[o] != d) || d.len() != 12 + (V + K * FORS_LEAVES) * N {
            return abort("the online operators sent different instances");
        }
        let idx = u64::from_le_bytes(d[..8].try_into().unwrap());
        let counter = u32::from_le_bytes(d[8..12].try_into().unwrap());
        let wots: [Digest; V] = d[12..12 + V * N].as_chunks::<N>().0.try_into().unwrap();
        let forest = ForsForest::from_leaves(&pp, idx, d[12 + V * N..].as_chunks::<N>().0);
        // The WOTS signature must sign this FORS key and reach the public leaf.
        if !key.tree.contains(idx) {
            return abort("the received instance is outside the kept subtree");
        }
        let local = (idx - (key.tree.s << key.tree.b)) as usize;
        if wots_recover(&pp, idx as u32, &forest.key, counter, &wots) != Some(wots_leaf_hash(&pp, idx as u32, &key.ends[local])) {
            return abort("the received instance does not check");
        }
        next = Some((idx, Instance { forest: Arc::new(forest), counter, wots }));
        meter.mark("receive and check the instance", None, net);
    } else {
        meter.mark("send the instance to the 4th operator", None, net);
    }
    op.next = next;
    Ok(meter.phases)
}
