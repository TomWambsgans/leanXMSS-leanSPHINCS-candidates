//! Building blocks of the Boolean MPC in `crates/rss`: circuits with typed wires compiled into a
//! level-by-level program, the BLAKE2s compression and `Th` as circuits, GF(2^128), PRFs keyed by
//! session tags, and network accounting.
//!
//! Circuits are evaluated bit-sliced: a wire is a bit-vector over every instance of a batch.

pub mod blake2s_circuit;
pub mod circuit;
pub mod gf128;
pub mod net;
pub mod prf;
