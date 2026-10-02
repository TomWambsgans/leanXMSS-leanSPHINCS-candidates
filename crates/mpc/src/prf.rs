//! Pseudorandomness from BLAKE2s: keyed PRF streams, tags, and OS randomness.

use std::io::Read;

use crate::gf128::Gf128;

pub type Key = [u8; 32];
pub type Tag = [u8; 16];

/// A 16-byte domain tag for `purpose` within `session`.
pub fn tag(session: &[u8; 16], purpose: &[u8]) -> Tag {
    let mut h = blake2s::Hasher::new();
    h.update(b"leansphincs-mpc-tag").update(session).update(purpose);
    h.finalize()[..16].try_into().unwrap()
}

fn block_input(key: &Key, tag: &Tag, index: u64, block: u64, out: &mut [u8]) {
    out[..32].copy_from_slice(key);
    out[32..48].copy_from_slice(tag);
    out[48..56].copy_from_slice(&index.to_le_bytes());
    out[56..64].copy_from_slice(&block.to_le_bytes());
}

/// Fills `out` with the stream `BLAKE2s(key | tag | index | i)`, `i = 0, 1, ...`, 4 words a block.
pub fn prf_words(key: &Key, tag: &Tag, index: u64, out: &mut [u64]) {
    let blocks = out.len().div_ceil(4);
    let mut input = vec![0u8; blocks * 64];
    for b in 0..blocks {
        block_input(key, tag, index, b as u64, &mut input[b * 64..(b + 1) * 64]);
    }
    let mut digests = vec![0u8; blocks * 32];
    blake2s::hash_many::<64>(&input, &mut digests);
    for (w, chunk) in out.iter_mut().zip(digests.as_chunks::<8>().0) {
        *w = u64::from_le_bytes(*chunk);
    }
}

/// One pseudorandom field element per `(index, j)`.
pub fn prf_field(key: &Key, tag: &Tag, index: u64, j: u64) -> Gf128 {
    let mut input = [0u8; 64];
    block_input(key, tag, index, j, &mut input);
    Gf128::from_bytes(&blake2s::hash(&input)[..16].try_into().unwrap())
}

/// `count` pseudorandom field elements for `index`.
pub fn prf_fields(key: &Key, tag: &Tag, index: u64, count: usize) -> Vec<Gf128> {
    let mut words = vec![0u64; count * 2];
    prf_words(key, tag, index, &mut words);
    words.as_chunks::<2>().0.iter().map(|w| Gf128(u128::from(w[0]) | u128::from(w[1]) << 64)).collect()
}

/// A challenge outside `{0, 1}` (the interpolation points of the inputs), so folding keeps both halves.
pub fn prf_challenge(key: &Key, tag: &Tag, index: u64) -> Gf128 {
    (0u64..)
        .map(|j| prf_field(key, tag, index, j))
        .find(|r| r.0 > 1)
        .unwrap()
}

#[cfg(any(test, feature = "testing"))]
thread_local! {
    static TEST_SEED: std::cell::Cell<Option<([u8; 32], u64)>> = const { std::cell::Cell::new(None) };
}

/// Test hook: this thread's randomness comes from `seed` (a BLAKE2s counter stream) instead of the
/// operating system, so that a test run can be replayed; `None` restores the operating system's.
#[cfg(any(test, feature = "testing"))]
pub fn seed_thread(seed: Option<[u8; 32]>) {
    TEST_SEED.with(|c| c.set(seed.map(|s| (s, 0))));
}

/// Fills `out` from the operating system's generator, in one read.
pub fn os_random_fill(out: &mut [u8]) {
    #[cfg(any(test, feature = "testing"))]
    if let Some((seed, mut ctr)) = TEST_SEED.with(|c| c.get()) {
        for chunk in out.chunks_mut(32) {
            let mut h = blake2s::Hasher::new();
            h.update(&seed).update(&ctr.to_le_bytes());
            chunk.copy_from_slice(&h.finalize()[..chunk.len()]);
            ctr += 1;
        }
        TEST_SEED.with(|c| c.set(Some((seed, ctr))));
        return;
    }
    std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(out)).expect("no /dev/urandom");
}

/// Bytes from the operating system's generator.
pub fn os_random<const L: usize>() -> [u8; L] {
    let mut out = [0u8; L];
    os_random_fill(&mut out);
    out
}

/// Words from the operating system's generator, in one read.
pub fn os_random_words(count: usize) -> Vec<u64> {
    let mut bytes = vec![0u8; 8 * count];
    os_random_fill(&mut bytes);
    bytes.as_chunks::<8>().0.iter().map(|b| u64::from_le_bytes(*b)).collect()
}

/// Field elements from the operating system's generator.
pub fn os_random_fields(count: usize) -> Vec<Gf128> {
    os_random_words(2 * count).as_chunks::<2>().0.iter().map(|w| Gf128(u128::from(w[0]) | u128::from(w[1]) << 64)).collect()
}
