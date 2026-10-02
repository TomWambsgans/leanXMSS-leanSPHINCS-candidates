//! Sessions: fresh joint session ids, random sharings, and running the three parties' threads.
//!
//! Every PRF stream of a session (the AND masks, the verification coins and the proof shares) is
//! tagged with its id, and dependents derive the session's PRF keys from it. A session id must
//! never repeat: a repeated id reuses the masks on different inputs (leaking shares) and the
//! verification coins (which a prover could then know in advance). So it is
//! `H(nonce_0 | nonce_1 | nonce_2)` with a fresh nonce from every party, which each party computes
//! from its own nonce: no party, nor a coordinator, can make it repeat.

use crate::engine::Shares;
#[cfg(any(test, feature = "testing"))]
use crate::engine::Party;
use crate::net::{Abort, Link, abort};
#[cfg(any(test, feature = "testing"))]
use crate::net::ring;
use crate::prf::{Key, os_random, os_random_words};

/// A session id agreed by [`establish`]; consumed by [`Party::new`], so it is used once.
pub struct SessionId([u8; 16]);

impl SessionId {
    pub fn bytes(&self) -> &[u8; 16] {
        &self.0
    }

    /// Any id, for the tests that check what a repeated id would break.
    #[cfg(any(test, feature = "testing"))]
    pub fn fixed(bytes: [u8; 16]) -> Self {
        Self(bytes)
    }
}

/// One round: every party sends a fresh nonce to both neighbors; the id hashes the three nonces in
/// party order. A party that receives different nonces than its neighbors computes another id, and
/// the session then aborts at its first check.
pub fn establish(link: &mut Link) -> Result<SessionId, Abort> {
    let nonce: [u8; 16] = os_random();
    let (from_prev, from_next) = link.exchange(nonce.to_vec(), nonce.to_vec())?;
    if from_prev.len() != 16 || from_next.len() != 16 {
        return abort("malformed session nonce");
    }
    let mut nonces = [[0u8; 16]; 3];
    nonces[link.id] = nonce;
    nonces[(link.id + 2) % 3] = from_prev.try_into().unwrap();
    nonces[(link.id + 1) % 3] = from_next.try_into().unwrap();
    let mut h = blake2s::Hasher::new();
    h.update(b"leansphincs-mpc-session");
    for n in &nonces {
        h.update(n);
    }
    Ok(SessionId(h.finalize()[..16].try_into().unwrap()))
}

pub fn random_keys() -> [Key; 3] {
    std::array::from_fn(|_| os_random())
}

/// A random replicated sharing of `value`: party `i` gets `(x_i, x_{i-1})`.
pub fn share(value: &[u64]) -> [Shares; 3] {
    let (x0, x1) = (os_random_words(value.len()), os_random_words(value.len()));
    let x2: Vec<u64> = value.iter().zip(&x0).zip(&x1).map(|((v, a), b)| v ^ a ^ b).collect();
    let x = [x0, x1, x2];
    std::array::from_fn(|i| Shares { own: x[i].clone(), prev: x[(i + 2) % 3].clone() })
}

/// A cheating party for the tests: a fault on its link, and a cheat in its MPC steps.
#[cfg(any(test, feature = "testing"))]
#[derive(Clone, Copy, Debug)]
pub struct Bad {
    pub party: usize,
    pub fault: Option<crate::net::Fault>,
    pub cheat: crate::engine::Cheat,
}

/// What one party of a test session ended with: its result, its traffic, whether its fault hit.
#[cfg(any(test, feature = "testing"))]
pub struct Outcome<T> {
    pub result: Result<T, Abort>,
    pub stats: crate::net::Stats,
    pub fault_applied: bool,
}

/// Runs `f` for the three parties of a fresh session (established first), each on its own thread:
/// party `i` gets key `keys[i]` (shared with party `i + 1`) and `keys[i - 1]`, and a batch of `n`.
#[cfg(any(test, feature = "testing"))]
pub fn run<T: Send>(keys: &[Key; 3], n: usize, bad: Option<Bad>, f: impl Fn(&mut Party) -> Result<T, Abort> + Sync) -> [Outcome<T>; 3] {
    let f = &f;
    std::thread::scope(|scope| {
        let handles = ring().map(|mut link| {
            scope.spawn(move || {
                let i = link.id;
                let bad = bad.filter(|b| b.party == i);
                link.fault = bad.and_then(|b| b.fault);
                let session = match establish(&mut link) {
                    Ok(s) => s,
                    Err(e) => return Outcome { result: Err(e), stats: link.stats, fault_applied: link.fault_applied },
                };
                let mut party = Party::new(link, keys[i], keys[(i + 2) % 3], session, n);
                if let Some(b) = bad {
                    party.cheat = b.cheat;
                }
                let result = f(&mut party);
                Outcome { result, stats: party.link.stats, fault_applied: party.link.fault_applied }
            })
        });
        handles.map(|h| h.join().expect("party thread panicked"))
    })
}
