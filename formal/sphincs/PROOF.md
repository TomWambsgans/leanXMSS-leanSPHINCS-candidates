# Candidate proof route and remaining work

The candidate development is in `LeanSphincs/`. Its SUF-CMA lifetime theorem is **not finished**.
The retained `SphincsSecurity/` proof establishes the older three-layer leanVM instance;
[LEANVM_PROOF.md](LEANVM_PROOF.md) preserves its original route. The source and adapted recovery,
byte-layout, code-counting, uniformity, and search lemmas are credited to leanVM `b7a107256`.

## What is checked

`Scheme.lean` ports the previous agent's draft to a separate namespace and build target.
It changes the chain code, all FORS groups, the single Merkle layer, the two digest blocks,
the Rust hash tags, and the surrogate spine. A `Params` value sets subtree height and lifetime.

`Recovery.lean` adapts leanVM's fixed-oracle WOTS and FORS recovery arguments. `Pruning.lean`
adds the new part: below b, an authentication path ascends computed nodes; above b, the
quotient of the global leaf index equals the subtree position shifted by the spine height.
Thus the verifier hashes the same ordered pair and tweak at every surrogate step.
`Correctness.correct` composes recovery through seeded key generation and signing for every
hash function and every b≤26. `RandomizedCorrectness.verify_of_finishSign` also proves
assembly correctness for any landed randomizer. These are deterministic correctness results,
not security reductions.

`Code.lean` counts the coefficient of z^120 in (1+z+z²+z³)^64 by packing coefficients into
base 2^129 and checking an integer division in the kernel. Packing a word into its 128 bits
injects valid words into accepted digests. At least 2^118 of the 2^128 digests are accepted.
`Search.lean` and `Counter.lean` prove the random-oracle search bound on distinct fresh inputs;
`Encoding.encoding_exhaustion_bound` closes it at 2^(-2^22) for 2^32 attempts.

`Landing.lean` constructs a bijection from local leaves to the grinding test's accepted
indices, proving the exact probability 2^b/2^26. `Digest.lean` tracks previously sampled
randomizers: their mass costs at most 2^32/2^128 per attempt. This leaves at least
2^(-(27-b)) acceptance mass. The halving lemma in `Decay.lean` gives 2^(-2^(b+5)) failure
mass for the seeded loop, conditional on the stated initial cache freshness. At b=10 this
is 2^-32768. `RandomizedDigest.lean` proves the same bound for independent uniform randomizers
sampled with replacement, including repeated-randomizer cache hits.

`Fresh.lean` proves that key generation (including surrogates) leaves the message and encoding
domains unused, and that FORS preparation preserves encoding freshness. `Complete.lean`
composes both exhaustion bounds with actual key generation and randomized signing.
`RandomizedSupport.lean` replays every shared-ROM execution against a function extending its
final cache, connects a successful randomizer search to a landed digest, and applies fixed-function
correctness. `Honest.honest_completeness` therefore proves a failure bound of
2^(-2^(b+5)) + 2^(-4194304) for key generation followed by signing and verification of any
fixed message. `Lifetimes.requested_completeness` specializes this to ≤2^-32767 for all six
instances. This is a single honest experiment, not a theorem about arbitrary adversarially
populated initial caches or simultaneous success of unlimited signing calls.
`honest_completeness_all_messages` also bounds the sum over all 2^256 messages by 2^-256,
matching the original leanVM completeness formulation.

`ForsCoverage.lean` proves the 266-bit digest's index/leaf decomposition is bijective. For
fixed sets R[i,t] of distinct disclosed leaves, a fresh uniform digest is covered with probability

    (sum_i product_t |R[i,t]|) / 2^266.

This uses actual set cardinalities, not the number of repeated signatures. It is the starting
point for the new lifetime analysis, not a justification for treating adversarially cached digest
queries or adaptively selected transcripts as independent.

`SecurityDigest.lean` connects this count to the actual two-call random oracle. It also treats
a cached first block and fresh second block: only ten new bits remain, so the denominator is
2^10 rather than 2^266. `SecurityAdaptive.lean` proves the conditional expectation identity and
an adaptive union bound for trials with two fresh inputs, keeping their current disclosure
table explicit. Cached trials and the honest disclosure distribution still need a reduction.

`LifetimeCoverage.lean` proves a degree-26 upper bound on (1-(1-p)^r)^24 using Bonferroni
inequalities. `LifetimeMoments.lean` expands its binomial moments into Stirling numbers and
descending factorials. `LifetimeBounds.lean` checks six integer certificates for exactly the
requested N values, with no floating point or native proof evaluation. `LifetimeProbability.lean`
expresses these bounds as probabilities and covers every smaller N. They prove the scripts'
binomial occupancy expression is ≤2^-127. The signing-only connection is now checked below;
adversarial hash interleaving and target search remain necessary.

`LifetimeSampling.lean` and `LifetimeIndependent.lean` connect the arithmetic to an explicit
independent uniform FORS experiment. `LifetimeLanding.lean` factors the landed digest law into
a uniform local index and all 24 uniform selectors. `LifetimeGrinding.lean` proves this exact
conditional law for the actual randomized loop and its subsequent two-block digest, handling
repeated randomizers and discharging freshness from key generation.
`LifetimeReuse.lean` permits cached accepted digests already represented in a proof-side prior
set. Every increasing event after one disclosure update is bounded by inserting one uniform
view; repeats and exhaustion leave the set unchanged. `LifetimeDisclosure.lean` iterates this
bound for arbitrary invariant-preserving adaptive transitions. `LifetimeDisclosureCache.lean`
preserves the invariant across actual grinding, for all messages simultaneously.
`FinishFresh.lean` proves that the entire post-digest signing suffix leaves message-domain
cache entries unchanged. `LifetimeSigningDisclosure.lean` therefore covers N complete signing
calls, including repeated/adaptive messages and exhausted WOTS searches. Its proof-side set
records every accepted digest before assembly; erasing that record gives exactly the actual
signer and cache. `LifetimeTerminal.lean` proves the independent-history coverage formula by
projecting uniform coordinate tables to the positions with the target index.
`LifetimeSigningBound.lean` closes all six exact lifetime bounds for these actual signing calls
followed by a fresh independent target. Adversary-prequeried inputs and target search remain open.
`LifetimeInterleaving.lean` characterizes exactly when raw adversarial queries break the
disclosure invariant; it does not treat these bookkeeping defects as negligible failures.
`LifetimeCandidate.lean` gives the exact conditional price in all four digest cache states,
including a cached second block queried before the first.

`LifetimeForecast.lean`, `LifetimeBank.lean`, and `LifetimeFutureBank.lean` assign each queried
message/randomizer pair its conditional coverage probability, including either block queried
first and subsequent cached completions. `LifetimeIdealInterleaving.lean` closes all six bounds
for adaptive digest queries interleaved with independent disclosure samples. The actual signer
needs a further coupling: an adversarially prequeried accepted pair can be a new, biased signing
source. `LifetimeSources.lean` records source identities and proves exact cache/response
provenance; excluding a target's own source does not alone remove this cross-source bias.
`LifetimeSourceSelection.lean` and `LifetimeGrindingCost.lean` bound weighted actual source
selection by its uniform 128-bit randomizer average times the actual expected grinding hash
calls, with pruning, repeats, and arbitrary caches retained. The required weighted coverage
charge and its composition with the disclosure bound remain open.
`LifetimeCachedSources.lean` and `LifetimeConditionalSources.lean` retain each prequeried
source's initial conditional forecast, including either partial-cache order, and charge its
actual selection to grinding work. `LifetimePairForecast.lean` supplies joint two-pair
conditional laws; `LifetimePoolBalance.lean` keeps the exact fresh-versus-cached pool mass.
Discarding the negative fresh-mass correction produces a bound too large for the requested
full-key constant. Centered fluctuation and joint-target accounting remain necessary.

`SecurityTreeWitness.lean` extracts canonical paths, same-address node matches, and surrogate
preimages. `SecurityChainWitness.lean` and `SecurityWotsWitness.lean` classify chain divergence,
two linked prefix edges, two chain contacts, and a unit-neighbor encoding plus a contact.
`SecurityEncoding.lean` supplies the candidate's injective decoder and 4032-neighbor bound.
`SecurityForsWitness.lean` extracts exact FORS secrets/paths or queried leaf/node/root-list
matches. `SecurityVerifier.lean` connects these to the actual accepted verifier execution;
`SecuritySignatureWitness.lean` composes the classification and derives reference certificates
from successful signing. Canonical signatures with the same message and randomizer are identical,
so the strong-forgery case is preserved. No global hash-injectivity hypothesis is used.
`SecurityUnsignedWitness.lean` removes the reference requirement for a coarser witness:
sum 120 across 64 digits forces a digit at most one, so that chain performs two linked edges.
This also happens in honest signatures and must be charged only with an appropriate hidden-prefix
invariant. `SecurityPrefixOracle.lean` and `SecurityPrefixSampling.lean` give exact serialized
prefix parsing and independent secret/low-output/high-output table splits. `SecurityPrefixExecution.lean` and `SecurityPrefixTrace.lean` connect the byte transcript to a
selected prefix experiment. The Frontier/Separation/Public/Signing/SignLayer/FullSign modules
factor the actual public-key computations and full randomized signer through one selected
leaf's cutoff. The cutoff depends only on the least successful encoding of that leaf's fixed
FORS key; it covers all signing indices and preserves exhaustion and private samples.
Combining these prefix experiments without multiplying by the number of chains, and retaining
the costs of honest internal work without exposing it, still needs the aggregate reduction.
`SecurityPrefixCost.lean` and `SecurityPrefixCountedSign.lean` preserve original total signing
costs, including erased internal work. `SecurityPrefixAllocation.lean` partitions one recorded
query trace among disjoint chain addresses. `SecurityPrefixCostTransfer.lean` connects ideal
slice costs to real slice costs with an explicit factor 1−q/2^128; expectations from distinct
ideal experiments cannot be summed merely by invoking trace disjointness.
`SecurityPrefixPrepared.lean` composes the material compiler with the counted signer, while
`SecurityPrefixMaterialSampling.lean` splits one uniform secret coordinate from all remaining
full-output material.
`SecurityPrefixMaterialView.lean`, `SecurityPrefixMaterialCost.lean`, and
`SecurityPrefixErasedKeygen.lean` remove the selected secret from the outside programmed
oracle as well as the explicit secret table. Actual counted signing and public-key generation
equal views built from erased material and the supplied chain frontier.
`SecurityPrefixErasedGame.lean` composes these identities through the entire adaptive material
game, retaining its joint success/cost law and literal selected-coordinate erasure. This is a
fixed-function factoring result; the stopped adaptive-query coupling is still needed. The current two-edge
coefficient and its cost-transfer factor do not close the bound for every large query budget.

`SecurityDomains.lean` proves exact derivation-input injection and separation from verifier
domains. `SecurityPrimitive.lean` bounds an explicit monitor of adaptive fresh queries against
targets chosen before their answers. Connecting hidden-input guesses, cached matches, and the
structural/chain witnesses to this probability accounting is still open.
`SecurityGameSupport.lean` preserves actual cost while extracting supported keygen, adversary,
and verifier runs. `SecurityGameWitness.lean` extracts each logged signing subrun and replays
it against the same final-cache-consistent function, retaining actual private randomization.
This discharges the reference certificate for same-message, same-randomizer strong forgeries.
Tree exceptions retain the actual recovered leaf and a concrete cached matching/preimage query.
`SecuritySeedGuess.lean` proves an adaptive q/2^256 hidden-seed guessing bound with explicit
seed-independent initialization. `SecuritySeedModel.lean` defines full-output independent key
material and exact derivation-cache programming, including all surrogate addresses. Actual
game coupling must establish the independence needed to apply the guessing bound.
`SecuritySeedCoupling.lean` proves parameter-first eager preparation and equality with the
actual experiment's joint success/cost distribution. It also proves equality up to a seed-hit
for ordinary computations. `SecurityPreparedScheme.lean` substitutes honest derivations by material reads with explicit
virtual query charges, while adversarial raw hashes bypass this privileged compiler.
`SecurityMaterialGameCoupling.evalDist_experiment_material` now proves equality of the entire
actual game's success/cost distribution with this material game on the programmed cache.
`SecuritySeedLoss.lean` now caps the seed-independent frontend, proves the cap preserves the
actual experiment under its original query bound, and changes the initial cache through a
stopped seed-guess coupling. The loss is the expected number of ordinary derivation-shaped
queries divided by 2^256. Virtual derivation charges and verification-domain hashes have zero
seed-guess charge. Its derivation and complementary expected query charges sum to at most q;
therefore proving the remaining material game at the complementary 127-bit rate suffices
without adding an unnecessary full-budget seed term. `SecurityQueryCharge.lean` connects local expected potential
increases to the actual shared hash budget. The required forgery-covering potential and its
concrete local bound are still to be constructed.

`SecurityCacheMatch.lean` bounds actual cached target hits from an initially clean cache.
`SecurityTargetAssignment.lean` gives one target per exact tweak: canonical inputs are exempt,
and surrogate positions have no canonical input. `SecurityPosition.lean` proves the finite
candidate structural addresses inject into the exact serialized fields. `SecurityGraph.lean`
prepares any selected subset in dependency order and proves that every preparation query is its
final canonical input; omitted positions retain their initial labels. The retained subtree,
surrogate boundary, and candidate witness events still need the complete graph instantiation.
`SecurityGraphCache.lean` proves that supported graph preparation starts the structural
monitor clean, including when it follows the actual seed-material preparation. Its active
labels satisfy the canonical query equations; inactive labels stay fixed.
`SecuritySurrogateAddress.lean` preserves the exact sibling address in first-divergence
extraction. `SecurityPrunedGraph.lean` instantiates retained and boundary positions, proves
boundary positions are inactive, and turns the addressed cached surrogate witness into the
single appropriate structural target. `SecurityGraphCorrectness.lean` now derives that bridge:
supported preparation and agreement with the final cache imply equality with actual seeded
chain, FORS, retained-tree and surrogate-spine computations, including their canonical inputs.
`SecurityGraphSampling.lean` proves the actual lazy-oracle preparation law equals independent
uniform full-output labels and canonical cache programming. Its continuation theorem retains
any instrumented original costs while leaving pruned boundary labels untouched.
`SecurityHiddenReveal.lean` and `SecurityHiddenCharge.lean` give an adaptive coordinate
reveal/guess bound with an expected charge from a common forced-failure comparison run.
Failed guesses do not justify assuming conditional uniformity in the stopped real run. The
candidate byte interpreter, success-event covering, and shared comparison budget remain to
be composed; costs from different experiments must not be added as if they shared a trace.

`LifetimeTransition.lean` gives an exact future-coverage identity for an actual signing call,
with its selected-source gain and the independent-source mean gain kept separate. It permits
arbitrary adversarial caches, repeated sources, grinding exhaustion and later WOTS failure.
`LifetimeMarginal.lean` bounds the independent marginal; the SecondBank and JointBank modules
control fixed-kernel moments and conditional forecasts. `LifetimeVarianceBudget.lean` checks
the proposed variance coefficient for all six limits, but does not establish its composition
through changing signing histories. The PoolConcentration/PoolRatio/PoolGrinding modules prove
that independent complete randomizer tables are simultaneously balanced except with probability
at most 2^-400, and give exact accepted-randomizer and weighted-source laws.
`LifetimePoolPreparation.lean` now connects these complete first-block tables to the actual
lazy oracle; PoolSigning gives the actual fixed-function grinding law. AdaptiveOccupancy and
PoolOccupancy prove the all-six tail from an explicit conditional index bound.
`LifetimeLocalizedGain.lean` splits an actual insertion into localized gain and an overflow
remainder without replacing the signer or displacing future samples. The localized gain has
uniform target measure at most 2^-74; that is not a pointwise bound for a cached target.
`LifetimePairedOracle.lean` samples both latent digest blocks at their first touch, in either
order, preserving the actual program distribution. PairedMonitor tracks fresh pairs and
proves their event probabilities. `SecurityExponentialCharge.lean` supplies a generic
exponential monitor tied to the original source query count. The changing-history variance
bound and its final shared-budget composition remain open.

## Differences and obligations

- The old proof's thirteenth/fourteenth moments, pinned FORS group, three-layer witnesses,
  and closing constants do not carry over automatically. The candidate needs bounds for its
  24-tree disclosure process, adaptive cached queries, primitive hash events, and the shared
  query allocation. The checked six numerical closers must then be connected to
  `Lifetimes.RequestedSecurity` without assuming the desired advantage bound.
- `Randomized.sign` samples fresh independent 16-byte randomizers with replacement, as
  requested. Rust derives them from the seed and message. The candidate security target is
  for the independent-randomizer variant; transferring it to Rust would require a separate
  derivation reduction. Both seeded and independently randomized grinding bounds are now
  checked; end-to-end honest completeness uses the latter.
- The formal signer returns `none` after 2^32 randomizer trials. Rust uses `(0u32..)` and
  `.find(...).unwrap()` without this explicit failure case; overflow/wrapping and failure behavior
  are not modeled. Rust also panics on WOTS counter exhaustion. These discrepancies have
  been reported without changing the implementation.
- The functional model recomputes tree/FORS nodes from the seed. Rust keeps the generated
  tree and rebuilds FORS via stored arrays. The byte inputs and recovered values were ported
  by source inspection; this is not a mechanized Rust refinement or an exact hash-trace
  equivalence. A security transfer using total experiment query counts must account for caching.
- Verification does not enforce membership in the retained subtree. The security extraction
  must account explicitly for forgeries entering through a surrogate sibling, as well as
  ordinary WOTS/FORS/tree hash events.
- Requested N at b=10 is 33, versus 33,000 in the spec/prior plan. Requested N at b=26 is
  1,200,000,000, versus 2^30 in the current spec. Both requested values are preserved exactly.
- `Layout.signature_size` proves the actual serializer length. `VerificationCost.lean` sums
  BLAKE2s block costs of the verifier's actual logged hash-input lengths. Accepted signatures
  cost exactly 391 compressions; all signatures cost at most 391. This includes the 72 WOTS
  chain steps established by the constant-sum code.

`Axioms.lean` uses `#guard_msgs` to pin each public candidate theorem to its exact dependency
list, a subset of `propext`, `Classical.choice`, and `Quot.sound`. The default build checks
these guards as well as the retained leanVM public-theorem guards.
