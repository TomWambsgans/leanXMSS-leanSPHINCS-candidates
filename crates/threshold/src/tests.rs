use mpc::engine::Cheat;
use mpc::net::Fault;
use sphincs::*;

use crate::cluster::Cluster;
use crate::protocol::{CheatSpec, Mode};

fn message(i: u8) -> Message {
    std::array::from_fn(|k| i.wrapping_mul(17) ^ k as u8)
}

#[test]
fn dkg_then_vanilla_and_preprocessed_signing() {
    let (mut cluster, online, _) = Cluster::dkg(4, vec![]).unwrap();
    assert_eq!(online, [0, 1, 2]);
    let pk = cluster.ops[0].key().pk;
    assert!(cluster.ops.iter().all(|o| o.key().pk == pk), "every operator has the key");
    for i in 0..2 {
        let m = message(i);
        let (sig, _, _) = cluster.sign(&m, Mode::Vanilla).unwrap();
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        assert_eq!(sig.to_bytes().len(), SIG_SIZE);
    }
    for i in 2..4 {
        cluster.preprocess().unwrap();
        let next = cluster.ops[0].next.as_ref().unwrap().0;
        assert!(cluster.ops.iter().all(|o| o.next.as_ref().unwrap().0 == next));
        let m = message(i);
        let (sig, _, _) = cluster.sign(&m, Mode::Preprocessed).unwrap();
        assert_eq!(verify(&pk, &m, &sig), Ok(()));
        assert_eq!(digest_index(&pk.public_param, &pk.root, &sig.randomizer, &m), next, "landed on the preprocessed instance");
        assert!(cluster.sign(&m, Mode::Preprocessed).is_err(), "an instance is used once");
    }
}

#[test]
fn a_cheating_operator_is_routed_around() {
    // Operator 0 corrupts an AND message during the DKG: the set {1, 2, 3} runs it instead.
    let cheat = CheatSpec { op: 0, fault: None, cheat: Cheat::FlipAnd { and: 5000, bit: 3, consistent: true } };
    let (mut cluster, online, _) = Cluster::dkg(3, vec![cheat]).unwrap();
    assert_eq!(online, [1, 2, 3]);
    let pk = cluster.ops[0].key().pk;
    cluster.cheats.clear();
    let m = message(9);
    let (honest, online, report) = cluster.sign(&m, Mode::Vanilla).unwrap();
    assert_eq!(online, [0, 1, 2]);
    // The MPC link's last round (one round of the phases is the agreement on the four-operator network).
    let last = report[1].iter().map(|p| p.stats.rounds).sum::<u64>() - 2;
    // Operator 1 cheats: in an AND gate (covering its tracks), in a proof, or in the final opening.
    for fault in [None, Some(Fault { round: 845, to_next: true, bit: 9 }), Some(Fault { round: last, to_next: false, bit: 0 })] {
        let cheat = if fault.is_none() { Cheat::FlipAnd { and: 5000, bit: 3, consistent: true } } else { Cheat::Honest };
        cluster.cheats = vec![CheatSpec { op: 1, fault, cheat }];
        let (sig, online, _) = cluster.sign(&m, Mode::Vanilla).unwrap();
        assert!(!online.contains(&1), "the cheater's sets abort");
        assert_eq!(sig, honest, "a retry gives the same signature");
    }
    // ... and during preprocessing.
    cluster.cheats = vec![CheatSpec { op: 2, fault: Some(Fault { round: 3, to_next: true, bit: 1 }), cheat: Cheat::Honest }];
    let (online, _) = cluster.preprocess().unwrap();
    assert_eq!(online, [0, 1, 3]);
    let (sig, _, _) = cluster.sign(&m, Mode::Preprocessed).unwrap();
    assert_eq!(verify(&pk, &m, &sig), Ok(()));
}
