# leanSPHINCS proofs in Lean 4

**Status: candidate correctness, end-to-end honest completeness, and all six exact FORS
lifetime arithmetic bounds are checked. The adaptive SUF-CMA security reduction is unfinished.**
A successful build must not be read as completion of the six security claims.

`LeanSphincs/` models the candidate: one height-26 tree, 24 height-10 FORS trees, 64 WOTS+C
chains with four positions and sum 120, two message-digest calls, and pruning with surrogate
siblings. `Scheme.lean` models the seeded signer; `Randomized.lean` defines the requested
variant with truly uniform independent randomizers. The SUF-CMA game is in
[Statement.lean](LeanSphincs/Statement.lean).

The unchanged `SphincsSecurity/` library is the earlier **three-layer leanVM scheme** from
commit `b7a107256`, credited here and in the checkpoint commits. Its theorem
`sphincs_has_127_bits_of_classical_security` applies only to that older scheme.
Its historical documentation is [LEANVM_README.md](LEANVM_README.md) and
[LEANVM_PROOF.md](LEANVM_PROOF.md).

## Checked candidate claims

Names below are in `LeanSphincs` (with `Completeness` or `Concrete` as indicated).
[Axioms.lean](LeanSphincs/Axioms.lean) pins every public candidate theorem using `#guard_msgs`;
all dependencies are drawn from `propext`, `Classical.choice`, and `Quot.sound`.

| Claim | Theorem / file | Scope |
| --- | --- | --- |
| A successful seeded signature verifies | `Completeness.correct`, [Correctness](LeanSphincs/Correctness.lean) | Every hash function, seed, message, and pruning height 0–26 |
| A signature assembled from any landed randomizer verifies | `Completeness.verify_of_finishSign`, [RandomizedCorrectness](LeanSphincs/RandomizedCorrectness.lean) | Independent of how that randomizer was selected |
| Every successful randomized signature verifies in the shared ROM | `Completeness.verify_of_keygen_sign_support`, [RandomizedSupport](LeanSphincs/RandomizedSupport.lean) | Actual successive keygen, sign and verify runs; any initial cache |
| Honest keygen, signing and verification fail with probability ≤ 2^(-2^(b+5)) + 2^(-4194304) | `Completeness.honest_completeness`, [Honest](LeanSphincs/Honest.lean) | Every fixed message, fresh generated key and empty initial cache; no freshness assumptions remain |
| All six requested instances have honest failure probability ≤ 2^-32767 | `Lifetimes.requested_completeness`, [Honest](LeanSphincs/Honest.lean) | One honest sign-and-verify experiment |
| Sum of honest failure probabilities over all messages ≤ 2^-256 | `Completeness.honest_completeness_all_messages`, [Honest](LeanSphincs/Honest.lean) | Every b≥10; the original leanVM union-bound formulation |
| Computed subtree and surrogate path recover the root | `Completeness.eval_treeFold_pruned_path`, [Pruning](LeanSphincs/Pruning.lean) | Every retained leaf |
| Exact WOTS+C code size | `Completeness.codeCount_exact`, [Code](LeanSphincs/Code.lean) | 410356077965267834847013187094862224 words |
| Valid encodings cannot be moved forward to different valid encodings | `Completeness.encoding_antichain`, [Code](LeanSphincs/Code.lean) | All valid words |
| WOTS+C counter exhaustion ≤ 2^(-4194304) | `Completeness.encoding_exhaustion_bound`, [Encoding](LeanSphincs/Encoding.lean) | Counter inputs must initially be fresh |
| Fresh digest lands with probability 2^(b−26) | `fresh_landing_probability_inv`, [Landing](LeanSphincs/Landing.lean) | A fresh uniform first digest block |
| Seeded grinding exhaustion ≤ 2^(-2^(b+5)) | `Completeness.digest_exhaustion_bound`, [Digest](LeanSphincs/Digest.lean) | Initial randomizer and message inputs fresh; collisions accounted for |
| Independently randomized grinding has the same bound | `Completeness.randomized_digest_exhaustion_bound`, [RandomizedDigest](LeanSphincs/RandomizedDigest.lean) | Initial message inputs fresh; repeated randomizers accounted for |
| Exact FORS coverage probability | `Concrete.fresh_fors_coverage`, [ForsCoverage](LeanSphincs/ForsCoverage.lean) | Fixed disclosure sets and a fresh independent uniform digest |
| Actual fresh two-query digest has that coverage probability | `Security.probEvent_messageDigest_covered`, [SecurityDigest](LeanSphincs/SecurityDigest.lean) | Both inputs fresh; a separate theorem handles cached first blocks |
| Adaptive fresh-digest trials satisfy an explicit union bound | `Security.probEvent_adaptiveCoverageSearch_le`, [SecurityAdaptive](LeanSphincs/SecurityAdaptive.lean) | Requires a bound on the expected disclosure-table coverage rate |
| All six exact FORS lifetime expressions are ≤ 2^-127 | `Lifetime.fors_lifetime_ennreal_*`, [LifetimeProbability](LeanSphincs/LifetimeProbability.lean) | Independent binomial occupancy formula; all n≤N; not yet a game reduction |
| Independent FORS experiments satisfy those six bounds | `Lifetime.independent_forgery_lifetime_*`, [LifetimeIndependent](LeanSphincs/LifetimeIndependent.lean) | Explicit uniform index and disclosure sampling, including pruning |
| Successful grinding gives a uniform kept index and 24 uniform FORS selectors | `Lifetime.conditional_grindDigest_after_keygen`, [LifetimeGrinding](LeanSphincs/LifetimeGrinding.lean) | Actual keygen and randomized grinding; positive finite attempt budget; repeated randomizers included |
| One disclosure update is bounded by inserting an independent uniform view | `Lifetime.grindDigest_disclosure_step_le_uniform`, [LifetimeReuse](LeanSphincs/LifetimeReuse.lean) | Every increasing set event; cached accepted views must already be in the prior set |
| Accepted signatures yield canonical components or concrete exceptional queries | `Security.SignatureWitness.accepted_classification`, [SecuritySignatureWitness](LeanSphincs/SecuritySignatureWitness.lean) | Explicit WOTS reference certificate; includes surrogate, chain, encoding and FORS cases |
| A distinct accepted signature with an honest message/randomizer has an exceptional witness | `Security.SignatureWitness.strong_forgery_same_randomness`, [SecuritySignatureWitness](LeanSphincs/SecuritySignatureWitness.lean) | Reference certificate derived from actual successful honest assembly |
| Adaptive fresh hash queries hit at most two prior targets with probability ≤ q/2^127 | `Security.Primitive.two_target_monitor_bound`, [SecurityPrimitive](LeanSphincs/SecurityPrimitive.lean) | Explicit generic monitor; cached queries and hidden-input guesses still require game-level accounting |
| Serialized signature length = 5684 | `signature_size`, [Layout](LeanSphincs/Layout.lean) | Every signature, including malformed ones |
| Accepted verification uses exactly 391 compressions | `Cost.verification_compressions`, [VerificationCost](LeanSphincs/VerificationCost.lean) | Actual logged hash inputs; every execution costs at most 391 |

## Lifetime targets still open

`Lifetimes.RequestedSecurity` states all six targets in the candidate game. The numerical
FORS expression is now proved for every requested N, but none of the six game-level security
claims is yet proved. Each counts every hash call in the modeled experiment, including honest-party calls,
repeated inputs, and final verification; private sampling is free.

| Subtree height b | Requested signature limit N |
| --- | ---: |
| 26 | 1,200,000,000 |
| 20 | 23,700,000 |
| 13 | 240,000 |
| 14 | 460,000 |
| 12 | 125,000 |
| 10 | 33 |

The b=10 target is the user's literal 33, while the spec says 33,000. The full-key target is
1.2 billion, while the current spec advertises 2^30. Other modeling differences and the remaining
proof obligations are recorded in [PROOF.md](PROOF.md).

## Build

```sh
cd formal/sphincs
env LEAN_NUM_THREADS=2 nice -n 19 lake exe cache get
env LEAN_NUM_THREADS=2 nice -n 19 lake build
```

The default build includes the candidate, its axiom guards, the retained leanVM proof, and the
legacy query-budget regression check. No `sorry`, `native_decide`, or new axioms are used.
