# Proof route

`LeanForest.requestedSecurity` ([Main.lean](LeanForest/Main.lean)) proves 127 bits of SUF-CMA security for `Seeded.sign` in
each configuration of [README.md](README.md). This file documents the route. Everything below holds
for every `Params` (height `h ≤ 28`, `d` layers, kept subtree height `b`, signature limit `N`); only
the last step, the certificates, is numeric.

Units: S = 2^128 digests, a budget of q hash queries is x = q/S, and the target is q/2^127 = 2x.
The layers below the top have height ℓ = `lowerHeight` ≥ 6 (6, 6, 7, 8, 9 for the layered keys of
h = 20, 22, 24, 26, 28). The top layer has height t = h − ℓ(d − 1) and keeps a subtree of height k = b − ℓ(d − 1) (k = t for a
layered key, k = b for a pruned one). K = 226·2^k + 2(t − k) is the key-generation cost in hash calls
(`keygenCost`, `Prefix.keygenHashCost`, `Prefix.hashCalls_keygenFromSeed`) and q' = q − K. The
landing probability of a digest is p = 2^-(h−b).

## Map of the files

The statement is three files: [Main.lean](LeanForest/Main.lean) (the claim `Secure127` and one
theorem per configuration), [Scheme.lean](LeanForest/Scheme.lean) (the scheme) and
[Statement.lean](LeanForest/Statement.lean) (the game). The proof follows the steps below, one
directory each:

| Step | Directory | Contents |
| --- | --- | --- |
| | [Scheme/](LeanForest/Scheme) | facts about the scheme: lemmas of the specification, correctness, byte layout, sizes and costs, digest fields, encoding searches |
| | [Base/](LeanForest/Base) | generic probability: sampling lemmas, virtual futures, Poisson domination, the split majorant |
| 0 | [Seed/](LeanForest/Seed) | secrets as independent material; guessing the seed |
| 1 | [Reduction/](LeanForest/Reduction) | from the game to the seed-free game of a memoizing adversary |
| 1 | [ScanSigner/](LeanForest/ScanSigner) | the randomizer walk of the signer, the group of a message |
| 2 | [GraphView/](LeanForest/GraphView) | the graph of the honest values, its signer and its exact hash costs |
| 2 | [LazyRun/](LeanForest/LazyRun) | the interpreted lazy run over the hidden coordinates |
| 3 | [Classification/](LeanForest/Classification) | accepted forgeries, from the verifier's trace to the events of a win |
| 4, 5 | [CoverPotential/](LeanForest/CoverPotential) | the one-coin forest cover potential, used by both routes |
| 4, 5 | [CoverBound/](LeanForest/CoverBound) | its H-term: mark averages, per-tree moments, certificates |
| 4 | [SmallBudget/](LeanForest/SmallBudget) | the linear potential (`SmallBudget/Linear/`), the contact bound A4 (`SmallBudget/Contact/`), the closing |
| 5 | [LargeBudget/](LeanForest/LargeBudget) | the survival weight, the covers, the heavy message |
| 6 | [Certificates/](LeanForest/Certificates) | the closing theorem, the certificate checkers and the generated certificates; [Lifetimes.lean](LeanForest/Lifetimes.lean) applies them |

## Steps

0. **Secrets.** One hash of the seed gives two secrets, the two halves of its 32-byte output: two
   chain starts of a one-time key or of a forest WOTS key ([Scheme](LeanForest/Scheme.lean):
   `keygenDomainFields`; [Seed/Model](LeanForest/Seed/Model.lean): `secretHalf`). The proof keeps one uniform 256-bit value per
   secret, of which the low half is the secret (`SeedModel.Material`), and programs the answer of
   each such hash as the two low halves joined (`SeedModel.derivedOutput`). Distinct derivations have
   distinct inputs and read distinct secrets, and a table of answers comes from the same number of
   materials whatever the table, so the programmed answers are independent uniform outputs and the
   game is unchanged (`SeedCoupling.evalDist_prepared_continuation`,
   [Seed/Coupling](LeanForest/Seed/Coupling.lean)). Every secret is then read only
   through a hash input that contains the 256-bit seed, guessed with probability 2^-256 per query
   ([Seed/Guess](LeanForest/Seed/Guess.lean)).

1. **Statement and memo reduction.** [Statement](LeanForest/Statement.lean) is the SUF-CMA game,
   with the signing oracle `Seeded.sign`.
   `Det.forgeAdvantage_le_seedFree` ([Reduction/SeedElimination](LeanForest/Reduction/SeedElimination.lean)) bounds the advantage
   by the seed-free win of the memoizing adversary, which never asks for the same message twice, plus
   2q/2^256: the randomizer hash of each message is replaced by a uniform value, split into a table of
   steps and an independent table of starts R0 (`Det.evalDist_rtable_split`). The steps are fixed (the
   seed-free game takes them as a parameter, `PublicData.steps`, and is bounded for every table) and
   the starts averaged (`DetValue.avg_advDet`, [Reduction/WinValue](LeanForest/Reduction/WinValue.lean)).
   - **The walk.** The signer tries R0, R0 + δ, … with the odd step δ of the message
     (`walk_iterate_ne`). For one unsigned message a randomizer is fresh, cached and rejected, or cached
     and landing; the law of the signed pair is the walk value of [ScanSigner/LoopWalk](LeanForest/ScanSigner/LoopWalk.lean)
     over these statuses (`GraphView.scan_boundW`, [ScanSigner/Scan](LeanForest/ScanSigner/Scan.lean)), and one digest query raises the selection mass of
     the adversary's pairs by at most (2 − p)/2^128 (`LoopWalk.creation_le`).
   - **One group per message.** The potentials keep the cached pairs of each unsigned message as one
     exclusive group (`LoopWalk.grp`, [ScanSigner/Group](LeanForest/ScanSigner/Group.lean); `ForestPotential.grpAll`) applied to a one-coin future of the
     pairs still to come: a new pair is paid by one coin `H0.wbarOf` ([CoverPotential/FairCoin](LeanForest/CoverPotential/FairCoin.lean))
     while the group of its message keeps enough mass on the identity (`FairS`); the number of cached
     landed pairs is capped by an exact martingale (`lam`, at most (64/65)^(2^15) at the start,
     `H0.lam_start`); a signing call is paid by one fresh slot and the group of its message
     (`ForestPotential.sign_term`, [CoverPotential/Groups](LeanForest/CoverPotential/Groups.lean)). A message with more than half of the budget is heavy
     ([LargeBudget/HeavyTerm](LeanForest/LargeBudget/HeavyTerm.lean)) and uses one spare slot instead
     (`ForestPotential.det_largeH`).

2. **Graph view and lazy comparison.** The seed-free game is rewritten over a graph of all the honest
   values ([GraphView/Graph](LeanForest/GraphView/Graph.lean),
   [GraphView/Pruned](LeanForest/GraphView/Pruned.lean)): the kept subtree and the spine of the
   top layer, every tree of a lower layer on the path of a landed index (`TreeActive`), every WOTS+C
   key of such a tree that a landed index uses (`KeyActive`, `keyActive_iff`), and every forest
   instance. The signer of the graph view (`GraphView.finishSource`,
   [GraphView/Signer](LeanForest/GraphView/Signer.lean)) searches the WOTS+C counters of all
   layers first (`layerSearch`), each key signing its message read from the public data (the root of
   the tree below, or the forest key at the bottom: `PublicData.keyMessage`), and reveals its chain
   values only once every layer succeeded; its hash calls are ticked exactly
   (`hashCalls_finishSign_exact`, [GraphView/Cost](LeanForest/GraphView/Cost.lean)). It is then
   one interpreted lazy run over the hidden chain coordinates
   ([LazyRun/Interpreter](LeanForest/LazyRun/Interpreter.lean), [LazyRun/Debt](LeanForest/LazyRun/Debt.lean)). The
   preparation searches the counter of every WOTS+C key before the run (`searchAll`,
   [LazyRun/PreparedEncodings](LeanForest/LazyRun/PreparedEncodings.lean)), and the chain values at and above the
   prepared word of every retained key are exposed at the start (`AboveWord`,
   [LazyRun/Expose](LeanForest/LazyRun/Expose.lean)). An index whose search fails at any of its layers is
   charged as failing (`failSet`); all searches together fail with probability at most 2^-201
   (`expectedFail_le`, [LazyRun/PreparedRun](LeanForest/LazyRun/PreparedRun.lean)).

3. **Classification.** The verifier walks the layers from the top
   (`verified_layers`, [Classification/Verifier](LeanForest/Classification/Verifier.lean)).
   `SignatureWitness.accepted_full_classification` ([Classification/Accepted](LeanForest/Classification/Accepted.lean))
   classifies an accepted forgery layer by layer, from the top: at each layer either the layer's key
   is opened canonically at the canonical message of its key, or the tree of the layer has a hit (a
   Merkle match against a retained reference leaf, or, in the top layer, a match at the boundary of a
   surrogate), or the key has a WOTS exception (an encoding match, a leaf output match or a chain
   exception). When every layer is canonical, the bottom key signed the canonical forest key and the
   forest opening is classified (`Forest.recover_classification`,
   [Classification/Forest](LeanForest/Classification/Forest.lean)). Every target sits at a fixed
   address; the encoding target of a key reads its message off the graph labels
   (`labelMessage`), which is the canonical message of every retained key. `win_implies_badA`
   ([Classification/WinRefined](LeanForest/Classification/WinRefined.lean)) shows a win is one of:
   - a first-order target hit or a correct guess of a hidden value;
   - a WOTS second-order event at a retained key: a two-edge completion, a contact with a
     unit-neighbour encoding marker, or two contacts;
   - a forest contact without guess record, or a recorded one at a chain opened at or below its step;
   - two forest contacts at different chains of one index;
   - a near cover or a cover of a cached, landed, unsigned digest.

4. **Small budgets (q' ≤ q_h).**
   - **Linear potential** ([SmallBudget/Linear](LeanForest/SmallBudget/Linear), from
     [Potential](LeanForest/SmallBudget/Linear/Potential.lean) to
     [ForestSteps](LeanForest/SmallBudget/Linear/ForestSteps.lean)): charges ρ/2^128 per query, with
     ρ = max(3/2, 2 − 1/(1 + 4032x), 1 + 66x). It pays first-order hits, WOTS events, unrecorded and
     paired contacts and correct guesses, passes ρ/2^128 per digest query to the cover potential and
     leaves (ρ − 1 − x)/2^128 per forest step query (`smallRoute_potentialF`).
   - **Cover potential:** the one-coin forest potential at baseline ρ/2^128 with the exact cover
     indicator as witness ([CoverPotential/OneCoin](LeanForest/CoverPotential/OneCoin.lean),
     [CoverPotential/OneCoinGame](LeanForest/CoverPotential/OneCoinGame.lean)); its H-term is certified by
     Poissonization, splitting into independent indices and moments of the per-tree cover fraction
     ([CoverBound/HTerm](LeanForest/CoverBound/HTerm.lean), [CoverBound/HTermOption](LeanForest/CoverBound/HTermOption.lean),
     [Base/Split](LeanForest/Base/Split.lean)), with the per-index weight 2^-h.
   - **Contact bound A4** ([SmallBudget/Contact/Potential](LeanForest/SmallBudget/Contact/Potential.lean),
     [SmallBudget/Contact/Signing](LeanForest/SmallBudget/Contact/Signing.lean), [SmallBudget/Contact/Bound](LeanForest/SmallBudget/Contact/Bound.lean)): a
     recorded contact is settled once a reveal opens its chain at or below its step; a signing call
     opens a given chain with chance at most 123·2^-b·2^-15 plus the coin per cached pair of its
     message (`reveal_le_all`, [SmallBudget/Contact/RevealRate](LeanForest/SmallBudget/Contact/RevealRate.lean)), and the near
     forecast is capped at one ([SmallBudget/Contact/NearWitness](LeanForest/SmallBudget/Contact/NearWitness.lean),
     [CoverBound/NearOption](LeanForest/CoverBound/NearOption.lean)). A forest step query costs 2^-128(N·rate + 1 − κ), paid by
     the slack of the linear potential once κ ≥ 2 − ρ + x + N·rate (`arm_paysF`).
   - **Closing:** `sample_boundF` ([SmallBudget/SampleBound](LeanForest/SmallBudget/SampleBound.lean)),
     `det_smallF` and the rational check `checkSmallF`
     ([SmallBudget/Closing](LeanForest/SmallBudget/Closing.lean)):
     ρ + 2^128·B + (2M − 1)·q_h/(M·2^129) + κ·q_h·c + 2^-60 ≤ 2, with M = 2^(h−b), B and c the
     certified cover and near terms.

5. **Large budgets (q' > q_h).** Every digest query pays the baseline times the current survival
   weight ([LargeBudget/SurvivalWeight](LeanForest/LargeBudget/SurvivalWeight.lean), [LargeBudget/WeightedPotential](LeanForest/LargeBudget/WeightedPotential.lean)),
   so the baseline is about 2^-127(1 − x); hits cost at most 1 − (1 − x)^2 in total
   (`det_largeW`, [LargeBudget/Route](LeanForest/LargeBudget/Route.lean)). Chernoff-split covers
   (`checkCoverW`, [LargeBudget/Covers](LeanForest/LargeBudget/Covers.lean)) bound every budget from q_h: for the full
   and layered keys one cover reaches 2^127; for a pruned key they reach about 0.249·2^128, then one
   heavy cover (`checkCoverH`, N + 1 signatures, [Certificates/Closing](LeanForest/Certificates/Closing.lean))
   bounds the rest. The keygen credit K enters the
   entries of a cover: q' + K is the actual budget.

6. **Closing.** `ForestPotential.det_bitsFH` ([Certificates/Closing](LeanForest/Certificates/Closing.lean))
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

- For SHA-256, Rust pads P with zeros to a full 64-byte block, so that its compression is computed once
  per key: the input is P ‖ 0^48 ‖ A ‖ payload instead of P ‖ A ‖ payload, and the message digest also puts
  16 zero bytes before the randomizer (P ‖ 0^48 ‖ A ‖ m ‖ 0^16 ‖ R), so that R is alone in the last block.
  The map from model inputs is: pad P to a block, and, for a digest input (type 12) with a payload of at
  least 32 bytes, insert 0^16 after its first 32 payload bytes. It is injective (it keeps the length
  classes apart: below 32 payload bytes stays below, 32 or more becomes 48 or more), so distinct model
  inputs stay distinct; real queries outside its image get fresh answers, which the model adversary can
  sample itself. This is argued here, not proved in Lean.
- Rust's key generation builds the key from one hash of a tag, the configuration and the seed
  (configured_seed in crates/sphincs), so that one seed never gives two configurations the same one-time keys. The model's seed
  is that value, uniform in the random-oracle model; the extra hash is outside the hash-call counts. For
  Keccak-256 and BLAKE2s its 52-byte input also parses as a model input (P = the tag), so the reduction
  adds the chance of guessing the 32-byte seed, at most q / 2^256.
- Strong unforgeability carries over to byte strings because Rust's Signature::from_bytes and
  to_bytes are inverse bijections at the configuration's length: fixed widths, no padding, every
  counter value accepted (checked by inspection).
- The signer of the security statement is `Seeded.sign`, which derives the base randomizer and the
  step from the seed and the message, as Rust does; a successful signature verifies
  (`Completeness.correct`).
- The formal signer returns `none` after 2^32 randomizer trials, or when a counter search fails. Rust caps
  the counter search at 2^32 too (and then panics), but its randomizer loop is unbounded (it wraps in a
  release build); these never happen in practice and are not modeled.
- The functional model recomputes tree and forest nodes from the seed. Rust keeps the generated top
  layer and builds the forest of an instance and the lower trees once per signature. The hash-call
  counts are those of the model; the byte inputs and recovered values were ported by source
  inspection; this is not a mechanized Rust refinement or an exact hash-trace equivalence.
- Verification does not enforce membership in the retained subtree. The proof accounts for forgeries
  entering through a surrogate sibling.
- The random oracle stands for the hash: its outputs are uniform 32-byte strings, of which the scheme
  keeps 16 bytes. `Scheme/VerificationCost.lean` counts compressions on the model inputs
  `P ‖ A ‖ payload`: Keccak-256 `n / 136 + 1`, BLAKE2s `⌈n / 64⌉`, SHA-256 `⌈(n − 16 + 9) / 64⌉` plus
  one block of P per key. Rust absorbs the fixed part of the digest input and of the encoding input
  once and pays one compression per grinding attempt and per counter, as the cost model
  `scripts/scheme.py` does.
- Every hash input is P ‖ A ‖ payload, with the 16-byte address
  A = `lo` ‖ `hi` ‖ (type + 32·step) ‖ layer ‖ tree ‖ 0^3 (`fieldBytes`), the layer counted from the
  bottom (`layerByte`). An input determines P, the address and the payload (`fieldInput_injective`,
  [Scheme/Domains](LeanForest/Scheme/Domains.lean)), and in-range domains have distinct addresses
  (`hashFields_injective`, [GraphView/Position](LeanForest/GraphView/Position.lean)), so separating
  inputs costs no probability term. The root is not hashed in the digest (P binds the key).
- The digest is one output, read as h + 208 bits whose fields are disjoint and none across two
  64-bit words: the index and the 26-bit field of each of the 8 trees are a bijection of them
  (`fullDigestView_bijective`, [Scheme/DigestView](LeanForest/Scheme/DigestView.lean)), so a uniform output
  gives a uniform index and 8 independent uniform fields.

`Axioms.lean` pins the main theorems to their exact axiom lists with `#guard_msgs` and checks that
every declaration of the library depends only on `propext`, `Classical.choice` and `Quot.sound`.
