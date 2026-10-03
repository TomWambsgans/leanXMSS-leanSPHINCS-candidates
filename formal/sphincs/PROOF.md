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
binomial occupancy expression is ≤2^-127; connecting that expression to the adaptive signing
transcript remains necessary.

`LifetimeSampling.lean` and `LifetimeIndependent.lean` connect the arithmetic to an explicit
independent uniform FORS experiment. `LifetimeLanding.lean` factors the landed digest law into
a uniform local index and all 24 uniform selectors. `LifetimeGrinding.lean` proves this exact
conditional law for the actual randomized loop and its subsequent two-block digest, handling
repeated randomizers and discharging freshness from key generation.
`LifetimeReuse.lean` permits cached accepted digests already represented in a proof-side prior
set. Every increasing event after one disclosure update is bounded by inserting one uniform
view; repeats and exhaustion leave the set unchanged. Preservation through full signing,
iteration over the lifetime, and adversary-prequeried accepted inputs remain separate obligations.

`SecurityTreeWitness.lean` extracts canonical paths, same-address node matches, and surrogate
preimages. `SecurityChainWitness.lean` and `SecurityWotsWitness.lean` classify chain divergence,
two linked prefix edges, two chain contacts, and a unit-neighbor encoding plus a contact.
`SecurityEncoding.lean` supplies the candidate's injective decoder and 4032-neighbor bound.
`SecurityForsWitness.lean` extracts exact FORS secrets/paths or queried leaf/node/root-list
matches. `SecurityVerifier.lean` connects these to the actual accepted verifier execution;
`SecuritySignatureWitness.lean` composes the classification and derives reference certificates
from successful signing. Canonical signatures with the same message and randomizer are identical,
so the strong-forgery case is preserved. No global hash-injectivity hypothesis is used.

`SecurityDomains.lean` proves exact derivation-input injection and separation from verifier
domains. `SecurityPrimitive.lean` bounds an explicit monitor of adaptive fresh queries against
targets chosen before their answers. Connecting hidden-input guesses, cached matches, and the
structural/chain witnesses to this probability accounting is still open.

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
