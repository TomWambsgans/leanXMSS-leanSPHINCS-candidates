//! 3-of-4 threshold signing of the leanSphincs candidate, as in leansphincs.tex ("3-of-4 with a
//! DKG"): any three of four operators sign, malicious security against one with abort, a DKG, and
//! signatures that the plain verifier accepts. Every secret is the XOR of four seed-derived terms
//! ([`operator`]); only the hashes of secrets run in MPC (3-party BGIN19, the `mpc` crate), the rest
//! in the clear ([`protocol`]); a failed attempt is retried with the next set of three ([`cluster`]).
//!
//! Simplifications of this research prototype:
//! - the operators are threads of one process, over simulated networks;
//! - nothing is persisted (a deployment must persist the preprocessed instance before using it);
//! - session ids come from a counter of the orchestrator, not from an agreement among the operators;
//! - a cheater is not identified, so one that aborts the four-operator steps of the DKG (seed dealing,
//!   coin tossing) blocks it.
//!
//! One scheduling change from the note: the FORS leaves and the first WOTS chain step of an instance
//! run in one batch (the chains don't depend on the FORS key), so an instance takes 2 hash depths of
//! rounds instead of 3.

pub mod cluster;
pub mod net4;
pub mod operator;
pub mod protocol;

#[cfg(test)]
mod tests;
