//! Running a 3-party session in-process: links, keys, random sharings, and the threads.

use crate::engine::{Party, Shares};
use crate::net::{Abort, ring};
use crate::prf::{Key, os_random};

/// Parties `0, 1, 2` of a fresh session; key `k_i` is held by parties `i` and `i + 1`.
pub fn parties(keys: &[Key; 3], session: [u8; 16], n: usize) -> [Party; 3] {
    let mut links = ring().map(Some);
    std::array::from_fn(|i| Party::new(links[i].take().unwrap(), keys[i], keys[(i + 2) % 3], session, n))
}

pub fn random_keys() -> [Key; 3] {
    std::array::from_fn(|_| os_random())
}

/// A random replicated sharing of `value`: party `i` gets `(x_i, x_{i-1})`.
pub fn share(value: &[u64]) -> [Shares; 3] {
    let rand = || value.iter().map(|_| u64::from_le_bytes(os_random())).collect::<Vec<u64>>();
    let (x0, x1) = (rand(), rand());
    let x2: Vec<u64> = value.iter().zip(&x0).zip(&x1).map(|((v, a), b)| v ^ a ^ b).collect();
    let x = [x0, x1, x2];
    std::array::from_fn(|i| Shares { own: x[i].clone(), prev: x[(i + 2) % 3].clone() })
}

/// Runs `f` for the three parties, each on its own thread.
pub fn run<T: Send>(parties: [Party; 3], f: impl Fn(Party) -> Result<T, Abort> + Sync) -> [Result<T, Abort>; 3] {
    let f = &f;
    std::thread::scope(|scope| {
        let handles = parties.map(|p| scope.spawn(move || f(p)));
        handles.map(|h| h.join().expect("party thread panicked"))
    })
}
