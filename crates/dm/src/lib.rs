//! A research prototype of BGHIN26 (Boyle, Gilboa, Hamilis, Ishai, Nof, "Dishonest-Majority Secure
//! Computation via PIR-Authenticated Multiplication Triples", ePrint 2026/257): 3 parties, security
//! with abort against 2 malicious ones, Boolean circuits (BLAKE2s).
//!
//! - Triples: the ST-PCG of [`pcg`] (FOLEAGE over F4, `c = 5`, `t = 27`, `n <= 16`, plus the trace).
//! - Evaluation: GMW with those triples, bit-sliced, one round per AND level ([`protocol`]).
//! - Verification `Π_Vrfy` ([`verify`]): a random combination of all wire relations is `Λ + Γ`,
//!   `Γ` linear in the PCG's sparse vector `e`, computed through authenticated sparse-linear PIR:
//!   per nonzero of `e`, a 3-party DPF unit vector with payload `(1, Δ)` ([`mdpf`]) against the
//!   public database `DB = G^T a_T`, then authenticated products with the payloads (`F_Mul`).
//!   Tiers ([`dealer::Tier`]): plain (PIR balancing `b = 8`), SSD (noise positions shared by groups
//!   of at most 27 batches), DSSD (matrix shared too; a sumcheck FLIOP, batches folded first and
//!   streamed, makes `DB` independent of the circuit). The `F_Mul` MACs are checked before any
//!   check value is opened, the checks before the outputs, and a final round of transcript hashes
//!   precedes the outputs.
//! - Simulated: the one-time setup (PCG and FUV keys, `F_Mul` triples, `F_Rand` masks) comes from a
//!   trusted [`dealer::Dealer`], bound to one session and handed out once; the network is
//!   in-process ([`net`]). Coins are commit-reveal.
//!
//! Soundness, all checks over GF(2^128): the combination's coefficients `A_w B_inst` make the
//! check a nonzero degree-2 polynomial under any additive attack (error `2/2^128`); each MAC check
//! `2/2^128`; the DSSD sumcheck `2/2^128` per round (at most 36). In all, below `2^-120`.

pub mod aes;
pub mod auth;
pub mod bits;
pub mod dealer;
pub mod dpf;
pub mod gf;
pub mod mdpf;
pub mod net;
pub mod par;
pub mod pcg;
pub mod protocol;
pub mod ring;
pub mod verify;

#[cfg(test)]
mod tests;
