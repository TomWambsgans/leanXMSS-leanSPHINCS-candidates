# Proof route

`LeanForest.requestedSecurity` ([Main.lean](LeanForest/Main.lean)) proves 127 bits of SUF-CMA security for `Seeded.sign` in
each configuration of [README.md](README.md). This file documents the route. Everything below holds
for every `Params` (height `h ≤ 28`, `d` layers, kept subtree height `b`, signature limit `N`); only
the last step, the certificates, is numeric.

Units: S = 2^128 digests, a budget of q hash queries is x = q/S, and the target is q/2^127 = 2x.
The layers below the top have height ℓ = `lowerHeight` ≥ 6 (6, 6, 7, 8 for the layered keys of
h = 22, 24, 26, 28). The top layer has height t = h − ℓ(d − 1) and keeps a subtree of height k = b − ℓ(d − 1) (k = t for a
layered key, k = b for a pruned one). K = 226·2^k + 2(t − k) is the key-generation cost in hash calls
(`keygenCost`, `Prefix.keygenHashCost`, `Prefix.hashCalls_keygenFromSeed`) and q' = q − K. The
landing probability of a digest is p = 2^-(h−b).

0. **Secrets.** One hash of the seed gives two secrets, the two halves of its 32-byte output: two
   chain starts of a one-time key or of a forest WOTS key ([Scheme](LeanForest/Scheme.lean):
   `keygenDomainFields`; [SecuritySeedModel](LeanForest/SecuritySeedModel.lean): `secretHalf`). The proof keeps one uniform 256-bit value per
   secret, of which the low half is the secret (`SeedModel.Material`), and programs the answer of
   each such hash as the two low halves joined (`SeedModel.derivedOutput`). Distinct derivations have
   distinct inputs and read distinct secrets, and a table of answers comes from the same number of
   materials whatever the table, so the programmed answers are independent uniform outputs and the
   game is unchanged (`SeedCoupling.evalDist_prepared_continuation`,
   [SecuritySeedCoupling](LeanForest/SecuritySeedCoupling.lean)). Every secret is then read only
   through a hash input that contains the 256-bit seed, guessed with probability 2^-256 per query
   ([SecuritySeedGuess](LeanForest/SecuritySeedGuess.lean)).

1. **Statement and memo reduction.** [Statement](LeanForest/Statement.lean) is the SUF-CMA game,
   with the signing oracle `Seeded.sign`.
   `Det.forgeAdvantage_le_seedFree` ([BridgeDet](LeanForest/BridgeDet.lean)) bounds the advantage
   by the seed-free win of the memoizing adversary, which never asks for the same message twice, plus
   2q/2^256: the randomizer hash of each message is replaced by a uniform value, split into a table of
   steps and an independent table of starts R0 (`Det.evalDist_rtable_split`). The steps are fixed (the
   seed-free game takes them as a parameter, `PublicData.steps`, and is bounded for every table) and
   the starts averaged (`DetValue.avg_advDet`, [BridgeDetValue](LeanForest/BridgeDetValue.lean)).
   - **The walk.** The signer tries R0, R0 + δ, … with the odd step δ of the message
     (`walk_iterate_ne`). For one unsigned message a randomizer is fresh, cached and rejected, or cached
     and landing; the law of the signed pair is the walk value of [LoopWalk](LeanForest/LoopWalk.lean)
     over these statuses (`GraphView.scan_boundW`, [BridgeScan](LeanForest/BridgeScan.lean)), and one digest query raises the selection mass of
     the adversary's pairs by at most (2 − p)/2^128 (`LoopWalk.creation_le`).
   - **One group per message.** The potentials keep the cached pairs of each unsigned message as one
     exclusive group (`LoopWalk.grp`, [GroupFuture](LeanForest/GroupFuture.lean); `ForestPotential.grpAll`) applied to a one-coin future of the
     pairs still to come: a new pair is paid by one coin `H0.wbarOf` ([H0Fair](LeanForest/H0Fair.lean))
     while the group of its message keeps enough mass on the identity (`FairS`); the number of cached
     landed pairs is capped by an exact martingale (`lam`, at most (64/65)^(2^15) at the start,
     `H0.lam_start`); a signing call is paid by one fresh slot and the group of its message
     (`ForestPotential.sign_term`, [BridgeGroups](LeanForest/BridgeGroups.lean)). A message with more than half of the budget is heavy
     ([BridgeHeavy](LeanForest/BridgeHeavy.lean)) and uses one spare slot instead
     (`BridgeHeavyRoutes.det_largeH`).

2. **Graph view and lazy comparison.** The seed-free game is rewritten over a graph of all the honest
   values ([SecurityGraph](LeanForest/SecurityGraph.lean),
   [SecurityPrunedGraph](LeanForest/SecurityPrunedGraph.lean)): the kept subtree and the spine of the
   top layer, every tree of a lower layer on the path of a landed index (`TreeActive`), every WOTS+C
   key of such a tree that a landed index uses (`KeyActive`, `keyActive_iff`), and every forest
   instance. The signer of the graph view (`GraphView.finishSource`,
   [SecurityGraphView](LeanForest/SecurityGraphView.lean)) searches the WOTS+C counters of all
   layers first (`layerSearch`), each key signing its message read from the public data (the root of
   the tree below, or the forest key at the bottom: `PublicData.keyMessage`), and reveals its chain
   values only once every layer succeeded; its hash calls are ticked exactly
   (`hashCalls_finishSign_exact`, [SecurityGraphCost](LeanForest/SecurityGraphCost.lean)). It is then
   one interpreted lazy run over the hidden chain coordinates
   ([BridgeInterp](LeanForest/BridgeInterp.lean), [BridgeDebt](LeanForest/BridgeDebt.lean)). The
   preparation searches the counter of every WOTS+C key before the run (`searchAll`,
   [BridgeEncodingPrep](LeanForest/BridgeEncodingPrep.lean)), and the chain values at and above the
   prepared word of every retained key are exposed at the start (`AboveWord`,
   [BridgeExpose](LeanForest/BridgeExpose.lean)). An index whose search fails at any of its layers is
   charged as failing (`failSet`); all searches together fail with probability at most 2^-201
   (`expectedFail_le`, [BridgeForestAssembly](LeanForest/BridgeForestAssembly.lean)).

3. **Classification.** The verifier walks the layers from the top
   (`verified_layers`, [SecurityVerifier](LeanForest/SecurityVerifier.lean)).
   `SignatureWitness.accepted_full_classification` ([BridgeClassify](LeanForest/BridgeClassify.lean))
   classifies an accepted forgery layer by layer, from the top: at each layer either the layer's key
   is opened canonically at the canonical message of its key, or the tree of the layer has a hit (a
   Merkle match against a retained reference leaf, or, in the top layer, a match at the boundary of a
   surrogate), or the key has a WOTS exception (an encoding match, a leaf output match or a chain
   exception). When every layer is canonical, the bottom key signed the canonical forest key and the
   forest opening is classified (`Forest.recover_classification`,
   [SecurityForestWitness](LeanForest/SecurityForestWitness.lean)). Every target sits at a fixed
   address; the encoding target of a key reads its message off the graph labels
   (`labelMessage`), which is the canonical message of every retained key. `win_implies_badA`
   ([BridgeImplicationA](LeanForest/BridgeImplicationA.lean)) shows a win is one of:
   - a first-order target hit or a correct guess of a hidden value;
   - a WOTS second-order event at a retained key: a two-edge completion, a contact with a
     unit-neighbour encoding marker, or two contacts;
   - a forest contact without guess record, or a recorded one at a chain opened at or below its step;
   - two forest contacts at different chains of one index;
   - a near cover or a cover of a cached, landed, unsigned digest.

4. **Small budgets (q' ≤ q_h).**
   - **Linear potential** ([BridgePotentialA](LeanForest/BridgePotentialA.lean)–A8,
     [BridgeFleafA3](LeanForest/BridgeFleafA3.lean)): charges ρ/2^128 per query, with
     ρ = max(3/2, 2 − 1/(1 + 4032x), 1 + 66x). It pays first-order hits, WOTS events, unrecorded and
     paired contacts and correct guesses, passes ρ/2^128 per digest query to the cover potential and
     leaves (ρ − 1 − x)/2^128 per forest step query (`smallRoute_potentialF`).
   - **Cover potential:** the one-coin forest potential at baseline ρ/2^128 with the exact cover
     indicator as witness ([BridgeForestPotentialOnce](LeanForest/BridgeForestPotentialOnce.lean),
     [BridgeForestGameOnce](LeanForest/BridgeForestGameOnce.lean)); its H-term is certified by
     Poissonization, splitting into independent indices and moments of the per-tree cover fraction
     ([H0Forest](LeanForest/H0Forest.lean), [H0ForestOpt](LeanForest/H0ForestOpt.lean),
     [Base/Split](LeanForest/Base/Split.lean)), with the per-index weight 2^-h.
   - **Contact bound A4** ([BridgeA4F](LeanForest/BridgeA4F.lean),
     [BridgeA4Sign](LeanForest/BridgeA4Sign.lean), [BridgeA4Final](LeanForest/BridgeA4Final.lean)): a
     recorded contact is settled once a reveal opens its chain at or below its step; a signing call
     opens a given chain with chance at most 123·2^-b·2^-15 plus the coin per cached pair of its
     message (`reveal_le_all`, [BridgeRevealRate](LeanForest/BridgeRevealRate.lean)), and the near
     forecast is capped at one ([BridgeForestNear](LeanForest/BridgeForestNear.lean),
     [H0NearOpt](LeanForest/H0NearOpt.lean)). A forest step query costs 2^-128(N·rate + 1 − κ), paid by
     the slack of the linear potential once κ ≥ 2 − ρ + x + N·rate (`arm_paysF`).
   - **Closing:** `sample_boundF` ([BridgeSampleBoundF](LeanForest/BridgeSampleBoundF.lean)),
     `det_smallF` and the rational check `checkSmallF`
     ([BridgeDetCloseF](LeanForest/BridgeDetCloseF.lean)):
     ρ + 2^128·B + (2M − 1)·q_h/(M·2^129) + κ·q_h·c + 2^-60 ≤ 2, with M = 2^(h−b), B and c the
     certified cover and near terms.

5. **Large budgets (q' > q_h).** Every digest query pays the baseline times the current survival
   weight ([BridgeSatW](LeanForest/BridgeSatW.lean), [BridgeSatWForest](LeanForest/BridgeSatWForest.lean)),
   so the baseline is about 2^-127(1 − x); hits cost at most 1 − (1 − x)^2 in total
   (`det_largeW`, [BridgeSatWRoutes](LeanForest/BridgeSatWRoutes.lean)). Chernoff-split covers
   (`checkCoverW`, [BridgeDetW](LeanForest/BridgeDetW.lean)) bound every budget from q_h: for the full
   and layered keys one cover reaches 2^127; for a pruned key they reach about 0.249·2^128, then one
   heavy cover (`checkCoverH`, N + 1 signatures, [BridgeHeavyCert](LeanForest/BridgeHeavyCert.lean))
   bounds the rest. The keygen credit K enters the
   entries of a cover: q' + K is the actual budget.

6. **Closing.** `ForestPotential.det_bitsFH` ([BridgeHeavyCert](LeanForest/BridgeHeavyCert.lean))
   combines the two routes from checks parameterized by the total height H, the kept subtree height b,
   the keygen credit K and the limit N (hypotheses `totalHeight = H`, `subtreeHeight = b`,
   `keygenHashCost = K`, `signatureLimit = N`). The certificates
   ([Certificates/H22](LeanForest/Certificates/H22.lean) … [H28](LeanForest/Certificates/H28.lean)),
   generated by `scripts/forest_certificates.py`, are checked by the kernel (`decide +kernel`, exact
   rationals) with q_h ≈ 2^(128+lx):

   | h | full key | b = 20 | 14 | 13 | 12 | 10 | 8 | layered |
   | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
   | 22 | −9.375 | −9.0 | −8.0 | −7.875 | −7.75 | −7.5 | −7.25 | −9.375 |
   | 24 | −10.0 | −9.125 | −8.125 | −8.0 | −7.75 | −7.625 | −7.375 | −10.0 |
   | 26 | −10.5 | −9.25 | −8.25 | −8.0 | −7.875 | −7.625 | −7.375 | −10.5 |
   | 28 | −10.875 | −9.375 | −8.25 | −8.125 | −8.0 | −7.75 | −7.5 | −10.875 |

   Each limit is the largest N both routes certify on a grid of lx of step 1/8, rounded down to four
   significant digits. A layered key is certified like the full key of its height with its own,
   smaller, keygen credit, which does not change the limit.

## Gap to the best known attack

The proved limits are 91% to 98% of the cover lifetime for the full and layered keys and 80% to 92%
for pruned keys ([README.md](README.md)). The remaining loss is structural:

- **Added strategies.** The potentials charge each attack strategy separately and add the charges,
  while an attacker gets only the best one. Near q ≈ 2^122, where the attack binds for small b, the
  linear potential must charge a contact query as a full guess plus a likely completion, and the
  large-budget route charges every non-forest query at the full 2^-127.
- **Correct guesses.** The lazy comparison counts a correct guess of a hidden chain value as a
  failure, although in the scheme it is only as useful as a contact.

## Modeling differences and obligations

- The signer of the security statement is `Seeded.sign`, which derives the base randomizer and the
  step from the seed and the message, as Rust does; a successful signature verifies
  (`Completeness.correct`).
- The formal signer returns `none` after 2^32 randomizer trials, or when a counter search fails. Rust
  uses unbounded loops; overflow and failure behavior are not modeled.
- The functional model recomputes tree and forest nodes from the seed. Rust keeps the generated top
  layer and builds the forest of an instance and the lower trees once per signature. The hash-call
  counts are those of the model; the byte inputs and recovered values were ported by source
  inspection; this is not a mechanized Rust refinement or an exact hash-trace equivalence.
- Verification does not enforce membership in the retained subtree. The proof accounts for forgeries
  entering through a surrogate sibling.
- The random oracle stands for the hash: its outputs are uniform 32-byte strings, of which the scheme
  keeps 16 bytes. `VerificationCost.lean` counts compressions on the model inputs
  `P ‖ A ‖ payload`: Keccak-256 `n / 136 + 1`, BLAKE2s `⌈n / 64⌉`, SHA-256 `⌈(n − 16 + 9) / 64⌉` plus
  one block of P per key. Rust absorbs the fixed part of the digest input and of the encoding input
  once and pays one compression per grinding attempt and per counter, as the cost model
  `scripts/scheme.py` does.
- Every hash input is P ‖ A ‖ payload, with the 16-byte address
  A = `lo` ‖ `hi` ‖ (type + 32·step) ‖ layer ‖ tree ‖ 0^3 (`fieldBytes`), the layer counted from the
  bottom (`layerByte`). An input determines P, the address and the payload (`fieldInput_injective`,
  [SecurityDomains](LeanForest/SecurityDomains.lean)), and in-range domains have distinct addresses
  (`hashFields_injective`, [SecurityPosition](LeanForest/SecurityPosition.lean)), so separating
  inputs costs no probability term. The root is not hashed in the digest (P binds the key).
- The digest is one output, read as h + 208 bits whose fields are disjoint and none across two
  64-bit words: the index and the 26-bit field of each of the 8 trees are a bijection of them
  (`fullDigestView_bijective`, [ForestCoverage](LeanForest/ForestCoverage.lean)), so a uniform output
  gives a uniform index and 8 independent uniform fields.

`Axioms.lean` pins the main theorems to their exact axiom lists with `#guard_msgs` and checks that
every declaration of the library depends only on `propext`, `Classical.choice` and `Quot.sound`.
