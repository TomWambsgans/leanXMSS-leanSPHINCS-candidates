//! Three-party Boolean MPC with an honest majority and malicious security with abort.
//!
//! - Replicated 2-of-3 sharing: party `i` holds `(x_i, x_{i-1})` of `x = x_0 ^ x_1 ^ x_2`.
//! - AND gates by the semi-honest protocol of Araki et al. (CCS 2016): one bit per gate per party.
//! - Before anything is opened, every party proves its AND messages correct with the distributed
//!   zero-knowledge proof of Boyle, Gilboa, Ishai and Nof (CCS 2019, ePrint 2019/1390), Sections 4
//!   and 7, over GF(2^128).
//!
//! Circuits are evaluated bit-sliced: a wire is a bit-vector over every instance of a batch.

pub mod blake2s_circuit;
pub mod circuit;
pub mod engine;
pub mod gf128;
pub mod net;
pub mod prf;
pub mod session;
#[cfg(test)]
mod tests;
mod verify;
