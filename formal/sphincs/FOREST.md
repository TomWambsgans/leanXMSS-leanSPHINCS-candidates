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

## Hash inputs

Every hash input is `P ‖ A ‖ payload` (`Scheme.lean`: `tweakableHashInput`, `keygenHashInput`,
`randomizerHashInput`): the 16-byte public parameter, then the 8-byte address
`A = lo (4 bytes) ‖ hi (3 bytes) ‖ (type + 32·step)` with `lo` and `hi` little endian (`fieldBytes`),
then the payload. `Th` keeps the first 16 bytes of the hash. The public key is `root ‖ P`, 32 bytes.
Forest positions: tree `c < 8`, leaf `s < 16`, subtree `j < 2`, WOTS key `a < 8`, chain `i < 6`,
`idx` the 26-bit instance.

| call | type | step | hi | lo | payload |
| --- | ---: | --- | --- | --- | --- |
| WOTS+C chain secret | 0 | 0 | chain | leaf | seed |
| WOTS+C chain step onto position `to` | 1 | `to − 1` | chain | leaf | value |
| WOTS+C leaf | 2 | 0 | 0 | leaf | 64 chain ends |
| tree node | 3 | 0 | level | node | left ‖ right |
| WOTS+C encoding | 4 | 0 | 0 | leaf | message ‖ counter (4 bytes) |
| parameter derivation, under `P = 0` | 5 | 0 | 0 | 0 | seed |
| randomizer base `R0` | 7 | 0 | 0 | 0 | seed ‖ message |
| message digest | 12 | 0 | 0 | 0 | message ‖ eight zero bytes ‖ randomizer |
| surrogate sibling | 13 | 0 | level | 0 | seed |
| forest chain secret | 14 | 0 | `c + 8s + 128j + 256a + 2048i` | `idx` | seed |
| forest chain step from position `t` | 15 | `t` | `c + 8s + 128j + 256a + 2048i` | `idx` | value |
| forest WOTS-key leaf | 16 | 0 | `c + 8s + 128j + 256a` | `idx` | 6 chain tops |
| subtree node, level 1 to 3 | 17 | 0 | `c + 8s + 128j + 256·level + 1024·node` | `idx` | left ‖ right |
| tree leaf `H(R0, R1)` | 18 | 0 | `c + 8s` | `idx` | `R0 ‖ R1` |
| forest tree node, level 1 to 4 | 19 | 0 | `c + 8·level + 64·node` | `idx` | left ‖ right |
| few-time public key | 20 | 0 | 0 | `idx` | 8 tree roots |

The signer derives one randomizer base per message, `R0 = Th(P, A(7, 0, 0), seed ‖ message)` (one
hash query), and attempt `i` uses the randomizer `R0 + i` (addition modulo `2^128`,
`Seeded.signDigestLoop`); it keeps the first attempt whose digest index lands in the kept subtree.
The randomizer comes last in the digest payload: a grinding attempt changes only the last block of
the digest hash. The digest input is 80 bytes: the first block is
`P ‖ A ‖ message ‖ 0^8` and the second the randomizer alone. The root is not hashed (`P` binds the
key); `messageDigestPayload` keeps its root argument for its callers and ignores it.

Separation is unconditional. An input determines its parameter, its address and its payload
(`fieldBytes_injective` in `Bytes.lean`, `fieldInput_injective` in `SecurityDomains.lean`), two
inputs of different types differ whatever their parameters (`fieldInput_ne_of_tag_ne_across` in
`Fresh.lean`, `keygenInput_ne_hashInput`), and an address determines the call:
`hashFields_injective` and `Position.input_separated` (`SecurityPosition.lean`) for verification,
`deriveFields_injective` and `keygenInput_injective` for the seed derivations,
`randomizerHashInput_injective` (`BridgeDet.lean`) for the randomizer base. The address has no layer and
no tree field; the scheme has one of each (`Layer` and `TreeIndex` are `Fin 1`).

`Layout.signature_size`: a signature serializes to 4,276 bytes. `Cost.verification_compressions`:
an accepted signature costs exactly 321 BLAKE2s compressions (2 for the 80-byte digest input, 203
for the forest, 116 for WOTS+C and the path), and no signature costs more
(`verification_compressions_le`).

## The proof

The reduction is the one of the FORS variant (`PROOF.md`), forked module by module with the forest
in the hash domains (`Scheme.lean`, `Security*.lean`, `Bridge*.lean`). After the deterministic
signer is replaced by a seed-free one (`BridgeDet*`), a forgery is a first-order hit, a WOTS
second-order event, or one of the forest events of the refined classification
(`BridgeImplicationA`): a contact without guess record, two contacts at different chains of one
index, a recorded contact at a chain opened at or below its step, a near cover with a recorded
contact, or a cover. Budgets are split at `qh ≈ 2^(128 + lx)`.

### The scan signer `R = R0 + i`

After the seed is eliminated the start `R0` of a message is uniform and hidden, and the signature of
a message uses the first landing randomizer at or after it. For one unsigned message a randomizer is
fresh, cached and rejected, or cached and landing; the law of the signed pair is the walk value of
`LoopWalk.lean` over these statuses (`BridgeScan.scan_boundW`). A cached landed pair is selected
with a probability that depends on the cache (the run of rejected values before it), not `1/(n + R)`,
and one digest query raises the selection mass of the adversary's pairs by at most `(2 − p)/2^128`
(`LoopWalk.creation_le`, `p = 2^-(26−b)`; attained by scanning forward from random starts), against
`1/2^128` for independent attempts. The potentials therefore keep the cached pairs of each unsigned
message as one exclusive group (`GroupFuture.grp`, `BridgeGroups.grpAll`) applied to the one-coin
future of the pairs still to come:

- a new pair is paid by one future coin (`GroupFuture.probe_step`, `termO_newPair`) as long as the
  group of its message keeps mass `1 − τ` on the identity; the witness is only monotone, so the
  coin is `(2 − p)/(2^128 p (1 − τ))` (`H0Fair.wbarOf`, `FairS`), with `τ` from the numbers of cached
  digests and of cached landed pairs (`LoopWalk.mass_le`);
- the number of cached landed pairs of unsigned messages is capped by an exact martingale
  (`lam` in `BridgeForsPotentialOnce`): above the cap the bound is trivial, and the cap term is
  at most `(64/65)^(2^15)` at the start (`H0Fair.lam_start`);
- a signing call is paid by one fresh slot and the group of its message (`sign_term`): no coupling
  and no fair share;
- for the largest budgets one message can hold almost all the mass (its signature is then a known
  pair with certainty). A message with more than half of the budget is *heavy* (`BridgeHeavy`): it
  acts by the law of its signed view (`GroupHeavy.sgn`, exact under its own digest queries) and uses
  one spare fresh slot; the other messages have at most half of the budget
  (`BridgeHeavyW`, `BridgeHeavyRoutes.det_largeH`, certificates with `N + 1` signatures in
  `BridgeHeavyCert`).

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
  at most 134 of the 256 codewords have a given digit at least one; with the scan signer the second
  part is `hitMass`, the probability that the signature uses a cached landed pair, and the coin
  part of the potential is `ν (budget · offSum + C(budget, 2) · rateS)` with
  `rateS = (2 − p)/2^128`: a unit of budget is a contact attempt or a digest query, not both);
  a latent contact exposed by the
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

`BridgeHeavyCert.det_bitsFH`: 127 bits from the small-route table (rate at `qh`), the small-route
option, the near certificate, `checkSmallF` at `qh` (coin summand `(2 − p) qh / 2^129`), and a chain
of covers of `[qh + 1, 2^127)`, each with its own Poisson table: light covers (`checkCoverW`, coin
`wbarOf`) up to about `0.249 · 2^128`, then one heavy cover (`checkCoverH`, `N + 1` signatures, coin
`wbarH`). For `b = 26` there is no grinding and one light cover reaches `2^127`. The splits `lx` and
the limits are those of the signer with one hash per attempt.
