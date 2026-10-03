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
is 2^-32768. These conditional component results still need composition with key generation
and the rest of signing; they are not an end-to-end completeness theorem.

`ForsCoverage.lean` proves the 266-bit digest's index/leaf decomposition is bijective. For
fixed sets R[i,t] of distinct disclosed leaves, a fresh uniform digest is covered with probability

    (sum_i product_t |R[i,t]|) / 2^266.

This uses actual set cardinalities, not the number of repeated signatures. It is the starting
point for the new lifetime analysis, not a justification for treating adversarially cached digest
queries or adaptively selected transcripts as independent.

## Differences and obligations

- The old proof's thirteenth/fourteenth moments, pinned FORS group, three-layer witnesses,
  and closing constants do not carry over automatically. The candidate needs bounds for its
  24-tree disclosure process, adaptive cached queries, primitive hash events, and the shared
  query allocation. The six exact numerical closers must then prove
  `Lifetimes.RequestedSecurity` without assuming the desired advantage bound.
- `Randomized.sign` samples fresh independent 16-byte randomizers with replacement, as
  requested. Rust derives them from the seed and message. The candidate security target is
  for the independent-randomizer variant; transferring it to Rust would require a separate
  derivation reduction. The currently checked grinding probability theorem concerns the
  seeded loop under explicit freshness hypotheses; the randomized-loop bridge is still open.
- The formal signer returns `none` after 2^32 randomizer trials. Rust uses `(0u32..)` and
  `.find(...).unwrap()` without this explicit failure case; overflow/wrapping and failure behavior
  are not modeled. Rust also panics on WOTS counter exhaustion. These discrepancies have
  been reported without changing the implementation.
- The functional model recomputes tree/FORS nodes from the seed. Rust keeps the generated
  tree and rebuilds FORS via stored arrays. The byte inputs and recovered values were ported
  by source inspection; this is not a mechanized Rust refinement or an exact hash-trace
  equivalence. A security transfer using total experiment query counts must account for caching.
- End-to-end completeness must discharge the fresh-input hypotheses after key generation,
  compose the two searches, and connect to the independently randomized signing experiment.
- Requested N at b=10 is 33, versus 33,000 in the spec/prior plan. Requested N at b=26 is
  1,200,000,000, versus 2^30 in the current spec. Both requested values are preserved exactly.
- `Layout.signature_size` proves the actual serializer length. `Code.verification_chain_steps`
  proves the 72 remaining WOTS chain steps. The complete 391-compression trace is still open.

`Axioms.lean` uses `#guard_msgs` to pin each public candidate theorem to its exact dependency
list, a subset of `propext`, `Classical.choice`, and `Quot.sound`. The default build checks
these guards as well as the retained leanVM public-theorem guards.
