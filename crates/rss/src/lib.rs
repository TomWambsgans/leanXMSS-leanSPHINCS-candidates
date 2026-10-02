//! Boolean MPC among `n = 2f + 1` parties with an honest majority (at most `f` corrupt), malicious
//! security with abort: the generalization of [`mpc`] (three parties) to 3-of-5, 4-of-7, ...
//!
//! - Sharing: replicated (Cramer, Damgard, Ishai, TCC 2005): `x = XOR_T x_T` over the `f`-subsets
//!   `T` of parties, `x_T` held by the `f + 1` parties outside `T`. Any `f` parties miss the term of
//!   their own set; any `f + 1` hold every term. See [`structure`].
//! - AND gates ([`engine`]): each party computes its share of the cross products `x_A y_B`, masks it
//!   with a pairwise zero sharing and the PRSS terms it owns, and sends it to a collector, a holder of
//!   the one non-PRSS output term `T*`; the collector adds the `n` contributions into `z_T*` and
//!   forwards it to the `f` other holders. `(n - 1) + f` bits per AND in total, two rounds per AND
//!   level; the collector and `T*` rotate.
//! - Verification ([`verify`]), before anything is opened: all AND triples at once, by the
//!   sublinear check of Goyal and Song (CRYPTO 2020, ePrint 2020/134, Section 5), over GF(2^128),
//!   compressing by 2 per round. The replicated terms are converted locally to Shamir shares (CDI05),
//!   so each inner product costs one field multiplication per element and each check value has a
//!   robust (error-detecting) opening.
//! - Openings ([`engine::Party::open`]): through a rotating king, then a batched check against a
//!   robustly opened random linear combination.
//!
//! Circuits, the PRF and GF(2^128) come from [`mpc`]; the network is [`net`].

pub mod engine;
pub mod net;
pub mod setup;
pub mod structure;
#[cfg(test)]
mod tests;
pub mod verify;
