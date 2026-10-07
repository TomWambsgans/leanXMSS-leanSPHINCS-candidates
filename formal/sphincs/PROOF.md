# Proof route

`Lifetimes.requestedSecurity` proves 127 bits of SUF-CMA security for `Seeded.sign` at the limits in
[README.md](README.md). Units: S = 2^128 digests, a budget of q hash queries is x = q/S, and the
target is q/2^127 = 2x. K = 226·2^b + 2(26 − b) is the key-generation cost in hash calls
(`keygenCost`, `Prefix.hashCalls_keygenFromSeed`) and q' = q − K.

0. **Secrets.** One hash of the seed gives two secrets, the two halves of its 32-byte output: two
   chain starts of a one-time key, or two secrets of a FORS tree
   ([Scheme](LeanSphincs/Scheme.lean): `keygenDomainFields`, `secretHalf`, `derivePair`). The proof
   keeps one uniform 256-bit value per secret, of which the low half is the secret
   (`SeedModel.Material`), and programs the answer of each such hash as the two low halves joined
   (`SeedModel.pairOutput`, `programCache`). That map is the restriction of an involution of the
   table (`SeedModel.mix_involutive`), and distinct hashes have distinct inputs
   (`SeedCoupling.hashInputs_injective`), so the programmed answers are independent uniform
   outputs (`SeedCoupling.evalDist_hashAnswers`) and the game is unchanged
   (`SeedCoupling.evalDist_prepared_continuation`). Every secret is still an independent uniform
   value read only through a hash input that contains the 256-bit seed; the later steps see the
   secret at a position (`PreparedScheme.compile_secret`) and are unchanged. An honest hash of
   the seed costs one query whether it gives one secret or two, so the signer's query counts go
   down: 224 calls per one-time key (was 256), 152 for the opened chain values (was 184), 61,393
   for a FORS key and 61,152 for its openings, 122,571 calls per signature before the WOTS
   search (`hashCalls_forsKey_exact`, `hashCalls_forsOpen_exact`, `finishHashCost`,
   [SecurityGraphCost](LeanSphincs/SecurityGraphCost.lean)).

1. **Statement and memo reduction.** [StatementDet](LeanSphincs/StatementDet.lean) is the SUF-CMA game
   of [Statement](LeanSphincs/Statement.lean) with the signing oracle `Seeded.sign`.
   `Det.forgeAdvantageDet_le_seedFree` ([BridgeDet](LeanSphincs/BridgeDet.lean)) bounds the advantage
   by the seed-free win of the memoizing adversary, which never asks for the same message twice, plus
   2q/2^256: the base randomizer R0 of each message is replaced by a uniform value, one per
   message. The FORS loads are N/2^b.
   - **The walk.** The seed-free signer samples R0 and tries R0, R0 + 1, … The statuses of the
     randomizers of one message (unqueried, queried without landing, landed with a known view) fix
     the law of the selected randomizer exactly (`Walk.val`, [BridgeWalk](LeanSphincs/BridgeWalk.lean);
     `loop_bound`, [BridgeSignerFors](LeanSphincs/BridgeSignerFors.lean)): a known landed value is
     selected when R0 lies in the run that leads to it.
   - **One group per message.** The potentials see a base function through the selection of every
     unsigned message (`Walk.grp`, [BridgeGroup](LeanSphincs/BridgeGroup.lean); `stateFn`, `fut`,
     [BridgeStateFn](LeanSphincs/BridgeStateFn.lean)): a start absorbed by a known landed value
     discloses its view, a known non-landing start that is not absorbed is credited a fresh view (a
     scan can still turn it into a known item), an unqueried start is paid by the fresh slot of the
     signature. The group is a convex combination of translates, so the selection probabilities,
     which are martingales under further queries, are used exactly.
   - **Rate.** One digest query raises the group value by at most (2 − p)/2^128 times the average
     gain of one disclosure, p = 2^-(26−b) (`Walk.grp_step`): unqueried starts carry at most
     (1 − p)/p to a point. The bound is met by scanning forward from a fresh start to the first
     landing value. Future digest pairs are therefore forecast with one coin
     w5 = (2 − p)/(2^128 p) each (`H0.wbar5`, [H0Bound5](LeanSphincs/H0Bound5.lean)). The signer
     that drew a fresh randomizer per attempt had rate 2^128/(2^128 − q) instead, which is larger
     at q = 2^127 and smaller for small budgets.
2. **Lazy comparison.** The seed-free game is rewritten over a graph view of all scheme values
   (Security* modules), then as one interpreted lazy run over hidden coordinates
   ([BridgeInterp](LeanSphincs/BridgeInterp.lean), [BridgeDebt](LeanSphincs/BridgeDebt.lean)). Chain
   values at and above the prepared word of a landed leaf are exposed at the start
   ([BridgeExpose](LeanSphincs/BridgeExpose.lean)).
   - **FORS trees have no root hash.** The FORS key hashes the two level-9 nodes of each of the
     24 trees (48 values, `ftsTopsPayload`), and the level-10 node is not computed. The graph has
     the same positions as before; the children of the key hash are the 48 level-9 nodes
     (`Position.children`), and the level-10 node positions stay in the type unread, like the node
     indices beyond the width of a level. A forged opening that reaches the true FORS key either
     gives the key hash another input, which is a first-order hit at the key hash
     (`Fors.TopsMatch`, `topsMatch_hit`), or has the true 48 values. Then, per tree, the node it
     computes from the leaf is the true level-9 node on that side, which is classified as a tree
     of height 9 (canonical secret and path elements 0..8, a leaf match, or a node match at a
     level below 9), and its last path element is the true level-9 node on the other side, read
     off the key-hash input and not hashed (`Fors.tree_classification`,
     [SecurityForsWitness](LeanSphincs/SecurityForsWitness.lean)). A signature reveals that
     node as path element 9, as it did before, so the revealed values are unchanged
     (`GraphView.publicData`, `forsPath`).
3. **Classification.** `win_implies_badA` ([BridgeImplicationA](LeanSphincs/BridgeImplicationA.lean))
   shows a win is one of the following events:
   - a first-order target hit or a correct guess of a hidden value;
   - a WOTS second-order event: a two-edge completion, a contact with a unit-neighbour encoding marker, or two contacts;
   - a FORS leaf contact at a leaf revealed later or with no guess record;
   - two FORS contacts;
   - a near cover or a cover of an unsigned cached digest.
4. **Small budgets (q' ≤ q_h).** The pieces are:
   - **Linear potential:** charges ρ/2^128 per query, with ρ = max(3/2, 2 − 1/(1+4032x), 1+66x). It pays first-order hits, WOTS events, unrecorded and paired contacts and correct guesses, and passes ρ/2^128 per digest query to the cover potential ([BridgePotentialA](LeanSphincs/BridgePotentialA.lean)–A8, [BridgeFleafA3](LeanSphincs/BridgeFleafA3.lean)).
   - **FORS-leaf payment:** from its slack the linear potential also pays (ρ − 1 − x)/2^128 per FORS leaf query.
   - **Cover potential:** the one-coin FORS potential pays covers above that baseline. Its excess is certified by `checkThreshS` ([BridgeForsPotentialOnce](LeanSphincs/BridgeForsPotentialOnce.lean), [H0SplitCert](LeanSphincs/H0SplitCert.lean)).
   - **Contact before reveal:** a contact at a leaf revealed later costs N/(2^b 2^10) per FORS leaf query, paid from the FORS-leaf payment. The part where the revealing signature selects a cached digest keeps a budget term: a unit of budget is a contact attempt or a digest query, not both, so the term is 2^-128·C(q', 2)·(2 − p)/2^128 ([BridgeFleafA4a](LeanSphincs/BridgeFleafA4a.lean)).
   - **Contact at a near-covered leaf:** the per-contact near forecast is capped at one. The shortfall of a FORS leaf query at a near-covered leaf, κ = 2 − ρ + x + N/(2^b 2^10), is paid by κ·2^-128·Σ_{j<y} potNear(j) over budget levels ([BridgeArmA4b](LeanSphincs/BridgeArmA4b.lean)).
   - **Closing:** `checkSmallA` ([BridgeArmSmall](LeanSphincs/BridgeArmSmall.lean)) is
     ρ + 2^128·B + (2 − p)·q_h/2^129 + κ·q_h·c/2 + 2^-60 ≤ 2, where B and c are the certified cover excess and near-cover terms.
5. **Large budgets (q' ≥ q_h).** The one-coin FORS potential is combined with the saturation of hits:
   - Every digest query pays the baseline times the current survival weight ([BridgeSatW](LeanSphincs/BridgeSatW.lean), [BridgeSatWFors](LeanSphincs/BridgeSatWFors.lean)), so the baseline is ≈ 2^-127 (1 − x).
   - Hits cost at most 1 − (1 − x)^2 in total.
   - `det_largeW` ([BridgeSatWRoutes](LeanSphincs/BridgeSatWRoutes.lean)) bounds the forgery probability for q' ≥ q_h.
   - Poisson domination of the virtual future and Chernoff-split certificates (`checkCoverSW`, [H0Split](LeanSphincs/H0Split.lean), [H0SplitCert5](LeanSphincs/H0SplitCert5.lean), [BridgeDetW](LeanSphincs/BridgeDetW.lean)) cover every budget from q_h to 2^127. The table mean allows one extra expected load from cached digests, and (2 − p)·q/2^128 ≤ 1.
6. **Closing.** `det_bits` ([BridgeDetClose](LeanSphincs/BridgeDetClose.lean)) combines the two routes.
   [LifetimeCertificates](LeanSphincs/LifetimeCertificates.lean), generated by
   `scripts/lifetime_certificates.py`, holds the kernel-checked certificates (`decide +kernel`, exact
   rationals) with q_h ≈ 2^(128+lx):

   | b | lx |
   | ---: | ---: |
   | 26 | −11 |
   | 20 | −8.78 |
   | 14 | −7.75 |
   | 13 | −7.5 |
   | 12 | −7.38 |
   | 10 | −7.16 |
   | 8 | −6.97 |

   For b ≤ 20 both routes are close to tight at the chosen N; for b = 26 the large route alone
   limits N.

## Gap to the best known attack

Against the attack that includes the WOTS unit-neighbour route (README), the proved limits are 96%
(b = 26), 94% (b = 20) and 90–91% (b ≤ 14) of the attack lifetime. The remaining loss is structural:

- **The k^24 price.** The FORS potential values a candidate by a witness count over disclosed views
  (k^24 per index with k signatures), which is supermodular as the signing step needs. The attack
  only gains from distinct revealed leaves, and the difference costs about 2.5–3% of N. A
  distinct-leaf price would need a new argument for the signing step.
- **Added strategies.** The potentials charge each attack strategy separately and add the charges,
  while an attacker gets only the best one. Near q ≈ 2^122, where the attack binds for b ≤ 14, the
  linear potential must charge a contact query as a full guess plus a likely completion, and the
  large-budget route charges every non-FORS query at the full 2^-127, while the real attack still
  pays the ~2^116 queries of its marker search. Capturing this needs a potential that tracks the
  best strategy rather than the sum.
- **Correct guesses.** The lazy comparison counts a correct guess of a hidden chain value as a
  failure, although in the scheme it is only as useful as a contact.

Smaller levers were measured and are worth well under 1%: per-key unit-neighbour counts instead of
4032, and a saturation credit for the small route.

## Modeling differences and obligations

- `Randomized.sign` samples a uniform 16-byte base randomizer and walks from it. Rust derives the
  base from the seed and message; that signer is `Seeded.sign`, the one in the security statement.
  Honest completeness is proved for the randomized variant; correctness for the seeded one.
- The formal signer returns `none` after 2^32 randomizer trials. Rust uses `(0u32..)` and
  `.find(...).unwrap()` without this explicit failure case; overflow/wrapping and failure behavior are
  not modeled. Rust also panics on WOTS counter exhaustion.
- The functional model recomputes tree/FORS nodes from the seed. Rust keeps the generated tree and
  rebuilds FORS via stored arrays (`ForsForest::from_leaves`, levels 0..9 of each tree, once per
  signature); the model computes the two level-9 nodes of every tree for the key and each path
  element again for the opening. In the model a subtree of 2^l FORS leaves, l ≥ 1, takes 2^(l−1)
  hashes of the seed, a single leaf (the level-0 sibling of an opening, or a revealed secret)
  takes one, and a one-time key takes 32, as `wots_secrets`, `fors_secret_pair` and `fors_secret`
  do. The hash-call counts above are those of the model; key generation makes the same calls in
  Rust (241 compressions per leaf there, 17 of them for the leaf hash). The byte inputs and recovered values were ported by source
  inspection; this is not a mechanized Rust refinement or an exact hash-trace equivalence. A
  security transfer using total experiment query counts must account for caching.
- Verification does not enforce membership in the retained subtree. The proof accounts for forgeries
  entering through a surrogate sibling.
- `Layout.signature_size` proves the actual serializer length. `VerificationCost.lean` sums BLAKE2s
  block costs of the verifier's logged hash-input lengths: accepted signatures cost exactly 373
  compressions, all signatures at most 373 (4 for the digest, 24·(1 + 9) for the FORS leaves and
  folds, 13 for the FORS key hash of 800 bytes, 116 for WOTS+C and the tree).
- Every hash input is P ‖ A ‖ payload, with the 16-byte address A = `lo` ‖ `hi` ‖ (type + 32·step) ‖ 0^8
  (`fieldBytes`), so every value of a payload starts on a 16-byte boundary.
  The tree domains keep their layer and tree arguments, both always 0 and not serialized
  (`TreeIndex = Fin 1`). An input determines P, the address and the payload
  (`fieldInput_injective`, [SecurityDomains](LeanSphincs/SecurityDomains.lean)), and in-range
  domains have distinct addresses (`hashFields_injective`,
  [SecurityPosition](LeanSphincs/SecurityPosition.lean)), so separating inputs costs no probability
  term. The message digest hashes m ‖ ρ (80 bytes with P and A: the first block ends with m,
  the second is ρ) and the randomizer derivation seed ‖ m, once per
  message: Rust keeps the BLAKE2s state after the first block of the digest and pays one
  compression per grinding attempt; the model hashes whole inputs, and its budgets count oracle
  queries. The root is
  not hashed in the digest (P binds the key); `messageDigestPayload` and the digest functions keep
  their `root` argument, which they ignore.
- The digest's fields are disjoint bits of the two 256-bit outputs, none across two 64-bit words:
  the index is bits 128..153 of call 0 (`blockIndex`), and each call gives 12 FORS indices, six in
  each of its first two 64-bit words, index κ in call ⌊κ/12⌋ at bit 64·⌊(κ mod 12)/6⌋ + 10·(κ mod 6)
  (`digestLeaves_truncate`, [Uniform](LeanSphincs/Uniform.lean)).
  `truncateMessageDigest` collects them as the 266-bit string index ‖ u_0 ‖ … ‖ u_23, which is
  uniform for two independent uniform outputs (`evalDist_digestBlocks_uniform`); the index depends
  on call 0 alone (`digestIndex_truncate`), which is all the grinding and scan lemmas use.

`Axioms.lean` uses `#guard_msgs` to pin each public theorem to its exact axiom list, a subset of
`propext`, `Classical.choice` and `Quot.sound`.
