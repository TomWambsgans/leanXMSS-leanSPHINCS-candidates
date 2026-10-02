use mpc::engine::Cheat;
use mpc::net::{Abort, Link};
use sphincs::*;

use crate::cluster::{Cluster, SETS, run};
use crate::net4::Net4;
use crate::operator::*;
use crate::protocol::{self, CheatSpec, Hooks, Lie};

/// Seeded test randomness, from `THRESHOLD_SEED` or a fresh seed; the seed is printed, so a failing
/// run can be replayed with `THRESHOLD_SEED=<seed>`.
fn seeded() -> Hooks {
    let seed = std::env::var("THRESHOLD_SEED").ok().map_or_else(|| u64::from_le_bytes(mpc::prf::os_random()), |s| s.parse().expect("THRESHOLD_SEED: a u64"));
    eprintln!("THRESHOLD_SEED={seed}");
    Hooks::seeded(seed)
}

fn message(i: u8) -> Message {
    std::array::from_fn(|k| i.wrapping_mul(17) ^ k as u8)
}

fn cheat(op: usize, cheat: Cheat, lie: Lie) -> CheatSpec {
    CheatSpec { op, fault: None, cheat, lie }
}

fn honest(c: &Cluster, bad: usize) -> impl Iterator<Item = &Operator> {
    c.ops.iter().filter(move |o| o.id != bad)
}

#[test]
fn dkg_then_vanilla_and_preprocessed_signing() {
    let (mut cluster, online, _) = Cluster::dkg_with(4, seeded()).unwrap();
    assert_eq!(online, [0, 1, 2]);
    let pk = cluster.ops[0].key().pk;
    assert!(cluster.ops.iter().all(|o| o.key().pk == pk), "every operator has the key");
    let mut prev = cluster.ops[0].last;
    for i in 0..2 {
        let m = message(i);
        let (sig, _, _) = cluster.sign(&m, Mode::Vanilla).unwrap();
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        assert_eq!(sig.to_bytes().len(), SIG_SIZE);
        assert!(cluster.ops.iter().all(|o| o.last == Some(advance(prev, &sig.randomizer)) && o.pending.is_none_or(|p| p.done)), "every operator, the offline one too, moves on");
        prev = cluster.ops[0].last;
    }
    for i in 2..4 {
        cluster.preprocess().unwrap();
        let next = cluster.ops[0].next.as_ref().unwrap().idx;
        assert!(cluster.ops.iter().all(|o| o.next.as_ref().unwrap().idx == next));
        let m = message(i);
        let (sig, _, _) = cluster.sign(&m, Mode::Preprocessed).unwrap();
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        assert_eq!(digest_index(&pk.public_param, &pk.root, &sig.randomizer, &m), next, "landed on the preprocessed instance");
        assert!(cluster.ops.iter().all(|o| o.next.is_none() && o.used.as_ref().is_some_and(|u| u.idx == next) && o.consumed.len() == (i - 1) as usize));
        // Asking again gives the same signature (the same instance).
        assert_eq!(cluster.sign(&m, Mode::Preprocessed).unwrap().0, sig);
        let err = cluster.sign(&message(9), Mode::Preprocessed).unwrap_err();
        assert!(err.0.contains("no preprocessed instance"), "{err}");
        assert!(cluster.ops.iter().all(|o| o.pending.is_none_or(|p| p.m == m && p.done)), "refused before anything was agreed");
    }
}

#[test]
fn a_cheater_in_any_step_is_routed_around_and_learns_only_the_signature() {
    let (mut cluster, _, _) = Cluster::dkg_with(3, seeded()).unwrap();
    let pk = cluster.ops[0].key().pk;
    let bad = 1;
    let scenarios = [
        (Cheat::FlipAnd { and: 5000, bit: 3, consistent: true }, Lie::None),
        (Cheat::FlipAnd { and: 5000, bit: 3, consistent: false }, Lie::None),
        (Cheat::BadBeta, Lie::None),
        (Cheat::BadChallenge, Lie::None),
        (Cheat::Honest, Lie::AgreeHash),
        (Cheat::Honest, Lie::AgreeSplit),
        (Cheat::Honest, Lie::FlipR0),
        (Cheat::Honest, Lie::FlipFors),
        (Cheat::Honest, Lie::FlipWots),
        (Cheat::Honest, Lie::FakePending),
    ];
    let mut issued = vec![];
    for (i, (c, lie)) in scenarios.into_iter().enumerate() {
        // Preprocessed signing has no AND gates and no WOTS opening.
        let modes = if matches!(lie, Lie::AgreeHash | Lie::AgreeSplit | Lie::FlipR0 | Lie::FlipFors | Lie::FakePending) { &[Mode::Vanilla, Mode::Preprocessed][..] } else { &[Mode::Vanilla] };
        for &mode in modes {
            if mode == Mode::Preprocessed {
                cluster.set_cheats(vec![]);
                cluster.preprocess().unwrap();
            }
            cluster.set_cheats(vec![cheat(bad, c, lie)]);
            cluster.ops.iter_mut().for_each(|o| o.seen_r.clear());
            let m = message(40 + i as u8);
            let (sig, online, _) = cluster.sign(&m, mode).unwrap_or_else(|e| panic!("{c:?} {lie:?} {mode:?}: {e}"));
            assert_eq!(verify(&pk, &m, &sig), Ok(()));
            issued.push(sig.randomizer);
            // A fake pending claim no holder backs only picks s for a request never opened.
            if lie != Lie::FakePending {
                assert!(!online.contains(&bad), "{c:?} {lie:?} {mode:?}: the cheater's sets abort");
            }
            // Every attempt (aborted or not) computed the randomizer of an issued signature: whatever
            // the cheater saw opened belongs to one (the cluster may first rerun an earlier request
            // the cheater still claims, which gives the same signature again).
            for o in honest(&cluster, bad) {
                assert!(o.seen_r.iter().all(|r| issued.contains(r)), "{c:?} {lie:?} {mode:?}: operator {} saw another R", o.id);
                assert!(!online.contains(&o.id) || o.seen_r.contains(&sig.randomizer));
                assert_eq!(o.last, cluster.ops[online[0]].last, "{c:?} {lie:?} {mode:?}: operator {} missed the signature\n{}", o.id, cluster.log.join("\n"));
            }
            assert!(honest(&cluster, bad).any(|o| !o.seen_r.is_empty()));
        }
    }
    // ... and in preprocessing.
    for (k, (c, lie)) in PREPROCESSING_CHEATS.into_iter().enumerate() {
        cluster.set_cheats(vec![cheat(bad, c, lie)]);
        preprocess_then_sign(&mut cluster, bad, &message(77 + k as u8));
    }
}

/// The cheats a preprocessing can meet.
const PREPROCESSING_CHEATS: [(Cheat, Lie); 3] = [(Cheat::FlipAnd { and: 7, bit: 1, consistent: false }, Lie::None), (Cheat::Honest, Lie::FlipWots), (Cheat::Honest, Lie::AgreeHash)];

/// Preprocesses (with the cluster's cheats, which make the cheater's sets abort), then signs `m` on
/// the new instance with no cheats: the online operators hold the same instance, the signature lands
/// on it, and the honest operators end with the same draw state.
fn preprocess_then_sign(cluster: &mut Cluster, bad: usize, m: &Message) {
    let fail = |c: &Cluster, e: &dyn std::fmt::Display| -> ! { panic!("{e}\n{}", c.log.join("\n")) };
    let (online, _) = cluster.preprocess().unwrap_or_else(|e| fail(cluster, &e));
    assert!(cluster.hooks.cheats.is_empty() || !online.contains(&bad), "the cheater's sets abort");
    let target = cluster.ops[online[0]].next.as_ref().unwrap().idx;
    assert!(online.iter().all(|&o| cluster.ops[o].next.as_ref().is_some_and(|n| n.idx == target)), "the online operators hold the instance");
    cluster.set_cheats(vec![]);
    let pk = cluster.ops[0].key().pk;
    let (sig, _, _) = cluster.sign(m, Mode::Preprocessed).unwrap_or_else(|e| fail(cluster, &e));
    assert_eq!(verify(&pk, m, &sig), Ok(()));
    assert_eq!(digest_index(&pk.public_param, &pk.root, &sig.randomizer, m), target, "landed on the preprocessed instance");
    let last = cluster.ops[(bad + 1) % 4].last;
    assert!(honest(cluster, bad).all(|o| o.last == last), "the honest operators have the same draw state\n{}", cluster.log.join("\n"));
}

/// The preprocessing cheats over many seeds, each from the same state (after the DKG and a signature
/// on a preprocessed instance): the cheater may first hold a record of its own (none, a stale
/// unfinished copy of the last request, or a made-up request), then cheats in the preprocessing,
/// and the next signature must land on the new instance. `THRESHOLD_SEEDS` sets how many seeds
/// (default 50); a failure prints its seed, replayed alone with `THRESHOLD_SEED=<seed>`.
#[test]
fn preprocessing_cheats_over_many_seeds() {
    let mut base = Cluster::dkg_with(3, Hooks::seeded(0)).unwrap().0;
    base.preprocess().unwrap();
    base.sign(&message(1), Mode::Preprocessed).unwrap();
    let last = base.ops[0].pending.unwrap();
    let seeds: Vec<u64> = match std::env::var("THRESHOLD_SEED") {
        Ok(s) => vec![s.parse().unwrap()],
        Err(_) => (1..=std::env::var("THRESHOLD_SEEDS").map_or(50, |n| n.parse().unwrap())).collect(),
    };
    for seed in seeds {
        let mut cluster = base.clone();
        cluster.hooks = Hooks::seeded(seed);
        let bad = (seed % 4) as usize;
        let record = [None, Some(Pending { done: false, ..last }), Some(Pending { m: message(3), mode: Mode::Preprocessed, s: [seed as u8; 32], done: false })][(seed / 4) as usize % 3];
        let (c, lie) = PREPROCESSING_CHEATS[(seed / 12) as usize % 3];
        let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            cluster.ops[bad].pending = record;
            cluster.set_cheats(vec![cheat(bad, c, lie)]);
            preprocess_then_sign(&mut cluster, bad, &message(2));
        }));
        if run.is_err() {
            panic!("THRESHOLD_SEED={seed} (cheater {bad} with record {record:?}, {c:?} {lie:?}) failed");
        }
        if std::env::var("THRESHOLD_SEED").is_ok() {
            eprintln!("{}", cluster.log.join("\n"));
        }
    }
}

#[test]
fn a_lone_unfinished_claim_does_not_redirect_the_cluster() {
    let (mut cluster, _, _) = Cluster::dkg_with(3, seeded()).unwrap();
    let pk = cluster.ops[0].key().pk;
    let bad = 1;
    cluster.preprocess().unwrap();
    let old = message(60);
    cluster.sign(&old, Mode::Preprocessed).unwrap();
    let stale = cluster.ops[0].pending.unwrap();
    let fake = Pending { m: message(61), mode: Mode::Preprocessed, s: [7; 32], done: false };
    for claim in [Pending { done: false, ..stale }, fake] {
        cluster.preprocess().unwrap();
        let target = cluster.ops[0].next.as_ref().unwrap().idx;
        cluster.ops[bad].pending = Some(claim);
        let m = message(62 + claim.m[0]);
        let (sig, _, _) = cluster.sign(&m, Mode::Preprocessed).unwrap_or_else(|e| panic!("{e}\n{}", cluster.log.join("\n")));
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        assert_eq!(digest_index(&pk.public_param, &pk.root, &sig.randomizer, &m), target, "the instance went to the request");
        assert!(honest(&cluster, bad).all(|o| o.pending.is_none_or(|p| p.m != fake.m)), "nobody signed the fake request");
    }
}

/// A cheater picking `s` (a lone claim, adopted when no honest operator holds the request) can make
/// the operators sign an earlier request again as a new one, which repeats its randomizer: the next
/// instance is still a fresh one.
#[test]
fn a_repeated_randomizer_does_not_redraw_a_used_instance() {
    let (mut cluster, _, _) = Cluster::dkg_with(3, seeded()).unwrap();
    let bad = 1;
    let old = message(70);
    let (first, _, _) = cluster.sign(&old, Mode::Vanilla).unwrap();
    let record = cluster.ops[0].pending.unwrap();
    preprocess_then_sign(&mut cluster, bad, &message(71));
    cluster.ops[bad].pending = Some(Pending { done: false, ..record });
    let (again, online, _) = cluster.sign(&old, Mode::Vanilla).unwrap();
    assert!(online.contains(&bad) && again == first, "the cheater's s gave the same signature again");
    preprocess_then_sign(&mut cluster, bad, &message(72));
}

#[test]
fn a_cheater_in_the_dkg_mpc_is_routed_around_with_the_same_seeds() {
    let hooks = Hooks { cheats: vec![cheat(0, Cheat::FlipAnd { and: 5000, bit: 3, consistent: true }, Lie::None)], ..seeded() };
    let (cluster, online, _) = Cluster::dkg_with(3, hooks).unwrap();
    assert_eq!(online, [1, 2, 3]);
    let pk = cluster.ops[1].key().pk;
    assert!(cluster.ops.iter().all(|o| o.key().pk == pk));
    // An online cheater sending the offline operator a corrupted copy of the chain ends: the offline
    // operator keeps the copy a second online operator confirms.
    let hooks = Hooks { cheats: vec![cheat(0, Cheat::Honest, Lie::BadCopy)], ..seeded() };
    let (cluster, online, _) = Cluster::dkg_with(3, hooks).unwrap();
    assert_eq!(online, [0, 1, 2]);
    let pk = cluster.ops[1].key().pk;
    assert!(cluster.ops.iter().all(|o| o.key().pk == pk));
}

#[test]
fn seeds_are_independent_and_no_contributor_can_copy_one() {
    // A rushing contributor that tries to make k_{c-1} a copy of k_{c+1} must reveal what it did not
    // commit to: the honest holders abort.
    let err = Cluster::dkg_with(3, Hooks { cheats: vec![cheat(0, Cheat::Honest, Lie::SeedCopy)], ..seeded() }).err().unwrap();
    assert!(err.0.contains("commitment"), "{err}");
    // A contributor revealing different values to different holders is caught too.
    let err = Cluster::dkg_with(3, Hooks { cheats: vec![cheat(2, Cheat::Honest, Lie::InconsistentReveal)], ..seeded() }).err().unwrap();
    assert!(err.0.contains("commitment") || err.0.contains("inconsistent"), "{err}");
    // Honest seeds: four distinct values, each operator missing exactly its own.
    let (cluster, _, _) = Cluster::dkg_with(3, seeded()).unwrap();
    let seeds: Vec<Seed> = (0..4).map(|t| *cluster.ops[(t + 1) % 4].seed(t)).collect();
    for t in 0..4 {
        for u in 0..t {
            assert_ne!(seeds[t], seeds[u]);
        }
        let op = &cluster.ops[t];
        assert!(op.seeds[t].is_none() && (0..4).filter(|&u| u != t).all(|u| op.seeds[u] == Some(seeds[u])));
    }
}

/// Operators 1 and 2 are asked to sign different messages (the cheater 0 relays `m1` to one and
/// `m2` to the other): they disagree before anything is opened.
#[test]
fn a_split_message_aborts_before_any_opening() {
    let (mut cluster, _, _) = Cluster::dkg_with(3, seeded()).unwrap();
    let hooks = cluster.hooks.clone();
    let (m1, m2) = ([0xA1u8; 32], [0xB2u8; 32]);
    let results = run(&mut cluster.ops, [0, 1, 2], &hooks, |op: &mut Operator, net: &mut Net4, link: Option<Link>, roles: &Roles| -> Result<(), Abort> {
        let m = if op.id == 2 { m2 } else { m1 };
        match link {
            Some(link) => protocol::sign(op, net, link, roles, &m, Mode::Vanilla, &hooks).map(|_| ()),
            None => protocol::observe_signature(op, net, roles, &hooks),
        }
    });
    for o in 0..3 {
        assert!(results[o].is_err(), "operator {o} went on");
    }
    assert!(cluster.ops.iter().all(|o| o.pending.is_none() && o.seen_r.is_empty()), "no R0 was opened");
    // The preprocessed variant: the instance is in the agreement too.
    cluster.preprocess().unwrap();
    let target = cluster.ops[0].next.as_ref().unwrap().idx;
    let mut wrong = cluster.ops[1].next.clone().unwrap();
    wrong.idx ^= 1;
    cluster.ops[1].next = Some(wrong);
    let m = message(5);
    let (sig, online, _) = cluster.sign(&m, Mode::Preprocessed).unwrap();
    assert_eq!(online, [0, 2, 3], "the sets with the stale instance abort");
    let pk = cluster.ops[0].key().pk;
    assert_eq!(digest_index(&pk.public_param, &pk.root, &sig.randomizer, &m), target);
    assert!(cluster.ops[1].seen_r.is_empty(), "operator 1 never opened R0");
}

/// Re-signing one message in vanilla mode before each preprocessing no longer pins the next
/// instance: every signature has a fresh `s`, hence a fresh randomizer.
#[test]
fn re_signing_does_not_pin_the_next_instance() {
    let (mut cluster, _, _) = Cluster::dkg_with(5, seeded()).unwrap();
    let pk = cluster.ops[0].key().pk;
    let m0 = [0x77; 32];
    let (mut idxs, mut rs) = (vec![], vec![]);
    for j in 0..3u8 {
        let (sig, _, _) = cluster.sign(&m0, Mode::Vanilla).unwrap();
        rs.push(sig.randomizer);
        cluster.preprocess().unwrap();
        let mj = [j; 32];
        let (sig, _, _) = cluster.sign(&mj, Mode::Preprocessed).unwrap();
        idxs.push(digest_index(&pk.public_param, &pk.root, &sig.randomizer, &mj));
    }
    assert!(rs.windows(2).all(|w| w[0] != w[1]), "a new signature of m0 every time");
    assert!(idxs.windows(2).any(|w| w[0] != w[1]), "the preprocessed instances differ: {idxs:?}");
}

/// The fourth operator's check is its own: a cheater refusing instances (offline) and corrupting
/// the MPC (online), or sending a bad copy, cannot block preprocessing.
#[test]
fn one_cheater_cannot_block_preprocessing() {
    let (mut cluster, _, _) = Cluster::dkg_with(3, seeded()).unwrap();
    let pk = cluster.ops[0].key().pk;
    for (bad, spec) in [
        (3, vec![cheat(3, Cheat::FlipAnd { and: 100, bit: 0, consistent: true }, Lie::RefuseInstance)]),
        (0, vec![cheat(0, Cheat::Honest, Lie::BadCopy)]),
    ] {
        cluster.set_cheats(spec);
        cluster.preprocess().unwrap();
        cluster.set_cheats(vec![]);
        let m = message(60 + bad as u8);
        let (sig, _, _) = cluster.sign(&m, Mode::Preprocessed).unwrap();
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
    }
}

/// A request whose `R0` was opened is finished, with the same randomizer, before any other.
#[test]
fn a_pending_request_is_finished_first_with_the_same_randomizer() {
    let (mut cluster, _, _) = Cluster::dkg_with(3, seeded()).unwrap();
    let pk = cluster.ops[0].key().pk;
    // Two cheaters (beyond the threat model) make every set abort after R0 is opened.
    cluster.set_cheats(vec![cheat(0, Cheat::Honest, Lie::FlipFors), cheat(3, Cheat::Honest, Lie::FlipFors)]);
    let m = message(90);
    assert!(cluster.sign(&m, Mode::Vanilla).is_err());
    let pending = cluster.ops[1].pending.expect("operator 1 holds the request");
    assert_eq!(pending.m, m);
    assert!(cluster.ops.iter().any(|o| o.pending.is_some_and(|p| !p.done)), "some operator could not finish it");
    let r = cluster.ops[1].seen_r[0];
    assert!(cluster.ops[1].seen_r.iter().all(|x| *x == r));
    // Another request first finishes the pending one, then runs.
    cluster.set_cheats(vec![]);
    let other = message(91);
    let (sig, _, _) = cluster.sign(&other, Mode::Vanilla).unwrap();
    assert_eq!(verify(&pk, &other, &sig), Ok(()));
    assert!(cluster.ops[1].seen_r.contains(&r), "the pending request was finished with its randomizer");
    assert!(cluster.ops.iter().all(|o| o.pending.is_none_or(|p| p.done)));
}

#[test]
fn share_conversion_every_offline_choice() {
    let seeds: [Seed; 4] = std::array::from_fn(|i| [i as u8 * 37 + 1; 32]);
    let ops: Vec<Operator> = (0..4)
        .map(|id| {
            let mut o = Operator::new(id);
            for t in (0..4).filter(|&t| t != id) {
                o.seeds[t] = Some(seeds[t]);
            }
            o
        })
        .collect();
    let f = |s: &Seed| -> Digest { blake2s::hash(s)[..16].try_into().unwrap() };
    let xor = |a: &Digest, b: &Digest| -> Digest { std::array::from_fn(|i| a[i] ^ b[i]) };
    let secret = seeds.iter().fold([0u8; N], |acc, s| xor(&acc, &f(s)));
    for online in SETS {
        let roles = Roles::new(online);
        let sh: Vec<(Digest, Digest)> = (0..3).map(|i| ops[online[i]].shares(&roles, f)).collect();
        for i in 0..3 {
            assert_eq!(sh[i].0, sh[(i + 1) % 3].1, "x_i held by parties i and i+1");
        }
        assert_eq!(xor(&xor(&sh[0].0, &sh[1].0), &sh[2].0), secret);
        let session = [3u8; 16];
        let keys: Vec<([u8; 32], [u8; 32])> = (0..3).map(|i| ops[online[i]].mpc_keys(&roles, &session)).collect();
        for i in 0..3 {
            assert_eq!(keys[i].0, keys[(i + 1) % 3].1, "k_i shared by parties i and i+1");
        }
    }
}
