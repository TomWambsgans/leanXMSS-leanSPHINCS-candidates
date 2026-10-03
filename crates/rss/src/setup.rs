//! Sessions, keys and input sharings.
//!
//! - Session ids: `H(nonce_0 | ... | nonce_{n-1})`, a fresh nonce from every party, which each party
//!   computes with its own nonce: nobody can make an id repeat. Every PRF stream of a session (AND
//!   masks, PRSS values, coins) is tagged with it; a repeated id would reuse masks and coins.
//! - Keys: a PRSS seed `k_T` per term (held by the holders of `T`) and a pairwise key `k_ij` per pair
//!   of parties (for the zero sharings), and the seeds of the threshold PRF
//!   `F(x) = XOR_T H(k'_T, x)`. [`keygen`] derives them among the parties; [`deal`] is a trusted
//!   dealer, for tests and benchmarks.
//! - Inputs: [`prf_inputs`], replicated shares of `F` at given addresses, computed locally (the
//!   ceremony's secrets, no dealer); [`share`], a dealer's random sharing (tests, benchmarks).

use mpc::prf::{Key, os_random, os_random_words};

use crate::engine::Shares;
use crate::net::{Abort, Net, abort};
use crate::structure::Structure;

/// A session id agreed by [`establish`]; consumed by [`crate::engine::Party::new`], so used once.
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

/// One round: every party sends a fresh nonce to all others. A party that receives other nonces
/// than the rest computes another id, and the session aborts at its first check.
pub fn establish(net: &mut Net) -> Result<SessionId, Abort> {
    let nonce: [u8; 16] = os_random();
    let got = net.exchange(vec![nonce.to_vec(); net.n])?;
    let mut h = blake2s::Hasher::new();
    h.update(b"leansphincs-rss-session").update(&(net.n as u64).to_le_bytes());
    for (j, m) in got.iter().enumerate() {
        if j == net.id {
            h.update(&nonce);
        } else if m.len() != 16 {
            return abort("malformed session nonce");
        } else {
            h.update(m);
        }
    }
    Ok(SessionId(h.finalize()[..16].try_into().unwrap()))
}

/// A party's keys: the PRSS seeds of its terms (by local index), its pairwise keys (by party), and
/// its seeds of the threshold PRF (by local index).
#[derive(Clone)]
pub struct Keys {
    pub prss: Vec<Key>,
    pub pair: Vec<Key>,
    pub prf: Vec<Key>,
}

/// Keys from a trusted dealer.
pub fn deal(s: &Structure) -> Vec<Keys> {
    let seeds: Vec<Key> = s.terms.iter().map(|_| os_random()).collect();
    let prf: Vec<Key> = s.terms.iter().map(|_| os_random()).collect();
    let mut pair = vec![vec![[0u8; 32]; s.n]; s.n];
    for i in 0..s.n {
        for j in i + 1..s.n {
            let k = os_random();
            (pair[i][j], pair[j][i]) = (k, k);
        }
    }
    (0..s.n)
        .map(|i| Keys { prss: s.held[i].iter().map(|&t| seeds[t]).collect(), pair: pair[i].clone(), prf: s.held[i].iter().map(|&t| prf[t]).collect() })
        .collect()
}

fn derive(label: &[u8], ids: &[u64], parts: &[&[u8]]) -> Key {
    let mut h = blake2s::Hasher::new();
    h.update(label);
    for id in ids {
        h.update(&id.to_le_bytes());
    }
    for p in parts {
        h.update(p);
    }
    h.finalize()
}

/// Key generation among the parties, two rounds. Every holder of a term sends a random contribution
/// to the other holders, every party one to every other party; a key hashes its holders'
/// contributions, so it is uniform unless all of them are corrupt. Then each pair of parties compares
/// hashes of the keys they share: a holder that sent different contributions to different holders
/// is caught.
pub fn keygen(net: &mut Net, s: &Structure) -> Result<Keys, Abort> {
    let (i, n) = (net.id, s.n);
    // Two contributions per term (the PRSS seed, the PRF seed), one per other party.
    let mine: Vec<[u8; 64]> = s.held[i].iter().map(|_| os_random()).collect();
    let pair_mine: Vec<[u8; 32]> = (0..n).map(|_| os_random()).collect();
    // The terms parties i and j both hold, in increasing order.
    let shared = |j: usize| s.held[i].iter().enumerate().filter(move |&(_, &t)| s.holds(j, t)).map(|(l, _)| l);
    let out: Vec<Vec<u8>> = (0..n)
        .map(|j| if j == i { vec![] } else { shared(j).flat_map(|l| mine[l]).chain(pair_mine[j]).collect() })
        .collect();
    let got = net.exchange(out)?;
    let mut contrib: Vec<Vec<[u8; 64]>> = s.held[i].iter().map(|_| vec![[0u8; 64]; n]).collect();
    let mut pair = vec![[0u8; 32]; n];
    for j in (0..n).filter(|&j| j != i) {
        let ls: Vec<usize> = shared(j).collect();
        if got[j].len() != 64 * ls.len() + 32 {
            return abort("malformed key contribution");
        }
        for (k, &l) in ls.iter().enumerate() {
            contrib[l][j] = got[j][64 * k..64 * k + 64].try_into().unwrap();
        }
        let theirs: [u8; 32] = got[j][64 * ls.len()..].try_into().unwrap();
        let (lo, hi) = if i < j { (pair_mine[j], theirs) } else { (theirs, pair_mine[j]) };
        pair[j] = derive(b"rss-pair", &[i.min(j) as u64, i.max(j) as u64], &[&lo, &hi]);
    }
    let seeds = |label: &[u8], half: usize| -> Vec<Key> {
        s.held[i]
            .iter()
            .enumerate()
            .map(|(l, &t)| {
                let parts: Vec<&[u8]> = s.holders(t).map(|h| if h == i { &mine[l][32 * half..32 * half + 32] } else { &contrib[l][h][32 * half..32 * half + 32] }).collect();
                derive(label, &[t as u64], &parts)
            })
            .collect()
    };
    let (prss, prf) = (seeds(b"rss-prss", 0), seeds(b"rss-prf", 1));
    let check = |j: usize| -> Vec<u8> {
        let parts: Vec<&[u8]> = shared(j).flat_map(|l| [&prss[l][..], &prf[l][..]]).chain([&pair[j][..]]).collect();
        derive(b"rss-key-check", &[], &parts).to_vec()
    };
    let got = net.exchange((0..n).map(|j| if j == i { vec![] } else { check(j) }).collect())?;
    if (0..n).any(|j| j != i && got[j] != check(j)) {
        return abort("inconsistent keys");
    }
    Ok(Keys { prss, pair, prf })
}

/// The term `H(k_T, addr)` of the threshold PRF: 16 bytes.
pub fn prf_term(key: &Key, addr: &[u8; 32]) -> [u8; 16] {
    let mut input = [0u8; 64];
    input[..32].copy_from_slice(key);
    input[32..].copy_from_slice(addr);
    blake2s::hash(&input)[..16].try_into().unwrap()
}

/// Party `i`'s replicated shares of `F(addr) = XOR_T H(k_T, addr)` at every address, bit-sliced:
/// input `b` is bit `b` of the 16 bytes, over the instances. Each holder of `T` computes its term
/// locally from the seed `keys.prf`, so the inputs need no dealer and no communication; holders of a
/// term agree because their seeds do (checked by [`keygen`], and the input terms are hash-compared
/// again by the next [`crate::engine::Party::verify`]).
pub fn prf_inputs(s: &Structure, keys: &Keys, addrs: &[[u8; 32]]) -> Vec<Shares> {
    let words = addrs.len().div_ceil(64);
    let mut out: Vec<Shares> = (0..128).map(|_| Shares::input(vec![vec![0u64; words]; s.m()])).collect();
    for (l, key) in keys.prf.iter().enumerate() {
        for (k, addr) in addrs.iter().enumerate() {
            let h = prf_term(key, addr);
            for (b, x) in out.iter_mut().enumerate() {
                x.0[l][k / 64] |= u64::from(h[b / 8] >> (b % 8) & 1) << (k % 64);
            }
        }
    }
    out
}

/// A random replicated sharing of the bit-vector `value`, one [`Shares`] per party.
pub fn share(s: &Structure, value: &[u64]) -> Vec<Shares> {
    let mut terms: Vec<Vec<u64>> = (1..s.terms.len()).map(|_| os_random_words(value.len())).collect();
    let last: Vec<u64> = (0..value.len()).map(|w| terms.iter().fold(value[w], |acc, t| acc ^ t[w])).collect();
    terms.push(last);
    (0..s.n).map(|i| Shares::input(s.held[i].iter().map(|&t| terms[t].clone()).collect())).collect()
}
