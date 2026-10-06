# The forest variant of leanSphincs in Lean

`LeanForest` is a Lean library next to `LeanSphincs` (`lakefile.toml`, namespace `LeanForest`). It
replaces FORS by a two-level WOTS forest: 8 trees of height 4; each leaf of a tree is `H(R0, R1)` of
two subtrees of height 3 over WOTS keys. The digest picks, per tree, a leaf, a WOTS key in each of
its two subtrees and a codeword for each WOTS key (`lut`, entries in `{0..4}` summing to 5); the
signature opens each chain of the two WOTS keys at position `4 - d_i`. The FORS proof
(`LeanSphincs`) is untouched.

Final statement: `LeanForest.Lifetimes.requestedSecurity`, 127 classical bits (SUF-CMA in the ROM)
for the deterministic Lean signer at subtree heights 26, 20, 14, 13, 12, 10, 8.

| b | proved N (forest) | best known attack | ratio | proved N (FORS variant) |
| ---: | ---: | ---: | ---: | ---: |
| 26 | 1,268,000,000 | 1.352e9 | 93.8% | 1,156,000,000 |
| 20 | 23,700,000 | 2.654e7 | 89.3% | 22,380,000 |
| 14 | 438,800 | 4.98e5 | 88.1% | 412,500 |
| 13 | 226,100 | 2.57e5 | 88.0% | 211,900 |
| 12 | 115,800 | 1.32e5 | 87.7% | 108,700 |
| 10 | 30,650 | 3.47e4 | 88.3% | 28,600 |
| 8 | 8,110 | 9.23e3 | 87.9% | 7,530 |

The best known attack column counts the forest covers (README rule) and the WOTS+C unit-neighbour
route, which applies unchanged. Every forest lifetime is above the FORS one.

No `sorry`, no `native_decide`, no new axioms: `LeanForest/Axioms.lean` guards every public theorem
(`propext`, `Classical.choice`, `Quot.sound` only). Certificates are exact rationals checked by the
kernel (`decide +kernel`).

## Build

```
env LEAN_NUM_THREADS=2 nice -n 19 lake build LeanForest
```

Certificates: `python3 scripts/forest_certificates.py emit` (writes `LeanForest/LifetimeCertificates.lean`
and `LeanForest/Lifetimes.lean`); `python3 scripts/forest_certificates.py check B N LX` checks one set
in Python with the same exact arithmetic. Axiom guards: `lake env lean scripts/ForestTheorems.lean`
then `python3 scripts/forest_axioms.py`.

## The proof

The reduction is the one of the FORS variant (`PROOF.md`), forked module by module with the forest
in the hash domains (`Scheme.lean`, `Security*.lean`, `Bridge*.lean`). After the deterministic
signer is replaced by a seed-free one (`BridgeDet*`), a forgery is a first-order hit, a WOTS
second-order event, or one of the forest events of the refined classification
(`BridgeImplicationA`): a contact without guess record, two contacts at different chains of one
index, a recorded contact at a chain opened at or below its step, a near cover with a recorded
contact, or a cover. Budgets are split at `qh ≈ 2^(128 + lx)`.

### Small budgets (`q - keygenCost ≤ qh`)

- **Linear potential** (`BridgePotentialA`..`A8`, `BridgeFleafA3`). A forest step whose written
  coordinate is still unexposed is *latent*: it becomes a contact with chance `2^-128` when that
  coordinate is exposed. Contacts carry the weight `cw` (one if decided, `2^-128` while latent);
  exposures keep every multilinear expression of the weights in the mean (`mean_cw`, `mean_cw2`) and
  the final payoff is bounded through pinned completions (`completion_pin`, `prob_fct`). The potential
  pays guesses, first-order hits, WOTS second-order events, unrecorded forest contacts and pairs of
  contacts, and leaves `(ρ - 1 - x) 2^-128` per forest step query unused (`smallRoute_potentialF`).
- **One-coin cover potential** at baseline `ρ / 2^128` with the exact cover indicator as witness
  (`BridgeForsPotentialOnce`, `BridgeForsGameOnce`), and its H-term certificate (`H0*`: Poissonization,
  splitting into independent indices, first and second moments of the per-tree cover fraction from
  the distribution of the componentwise maximum of codewords, `H0ForestOpt`).
- **Contact bound A4** (`BridgeA4F`, `BridgeA4Sign`, `BridgeA4Final` on the game framework
  `BridgeGameF`). A recorded contact is *settled* once a reveal opens its chain at or below its step;
  settled contacts pay one, unsettled ones pay the reveal rate of the remaining signatures, the coin
  part and the capped near potential:
  `Ψ = Σ_recorded cw · (settled ? 1 : sig + coin + min(1, potN(y))) + y 2^-128 coin + κ 2^-128 Σ_{j<y} potN(j)`.
  The weighted sums keep their mean through ordinary queries (`BridgeWsum.wsum_ordinary`). Through a
  signing call (`sign_contact`): the signer asks no forest step input, so it records no forest step,
  keeps every step answer and exposes a written coordinate only by revealing its chain
  (`BridgeRunFacts`); a completed call reveals upward-closed chains (`closedRuns_loop`); a call opens
  a given chain at or below `min(t + 1, 3)` with chance at most `134 · 2^-b · 2^-15` plus `wbar` per
  cached pair of the message, over every run (`reveal_le_all`, `BridgeRevealAll`, `BridgeRevealRate`:
  at most 134 of the 256 codewords have a given digit at least one); a latent contact exposed by the
  call is decided with chance `2^-128` whatever the call does (`BridgeExposeMean.interp_value_le`).
  The near potential uses the subtree-free near witness (`BridgeForestNear`, certificate `H0NearOpt`).
  A forest step query costs `2^-128 (N rate + 1 - κ)`, paid by the slack of the linear potential once
  `κ ≥ 2 - ρ + x + N rate` (`arm_paysF`).
- Assembly: `sample_boundF` (`BridgeSampleBoundF`), `det_smallF` and the closed form `small_closeFF`
  with the rational check `checkSmallF` (`BridgeDetCloseF`).

### Large budgets

The one-coin bound at the survival-weighted baseline (`BridgeSatW*`, `det_largeW`) with forest covers
(`BridgeDetW.checkCoverW`, `H0ForestOpt`).

### Both routes

`BridgeDetCloseF.det_bitsF`: 127 bits from a Poisson table, the small-route option, the near
certificate, `checkSmallF` at `qh` and a cover of `[qh + 1, 2^127]`.
