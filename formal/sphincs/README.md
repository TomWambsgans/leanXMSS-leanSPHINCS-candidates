# leanSPHINCS proofs in Lean 4

**Status: candidate correctness and component probability bounds are checked; the six
127-bit lifetime security proofs and end-to-end completeness are unfinished.** A successful
build must not be read as completion of those claims.

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
| Computed subtree and surrogate path recover the root | `Completeness.eval_treeFold_pruned_path`, [Pruning](LeanSphincs/Pruning.lean) | Every retained leaf |
| Exact WOTS+C code size | `Completeness.codeCount_exact`, [Code](LeanSphincs/Code.lean) | 410356077965267834847013187094862224 words |
| Valid encodings cannot be moved forward to different valid encodings | `Completeness.encoding_antichain`, [Code](LeanSphincs/Code.lean) | All valid words |
| WOTS+C counter exhaustion ≤ 2^(-4194304) | `Completeness.encoding_exhaustion_bound`, [Encoding](LeanSphincs/Encoding.lean) | Counter inputs must initially be fresh |
| Fresh digest lands with probability 2^(b−26) | `fresh_landing_probability_inv`, [Landing](LeanSphincs/Landing.lean) | A fresh uniform first digest block |
| Seeded grinding exhaustion ≤ 2^(-2^(b+5)) | `Completeness.digest_exhaustion_bound`, [Digest](LeanSphincs/Digest.lean) | Initial randomizer and message inputs fresh; collisions accounted for |
| Exact FORS coverage probability | `Concrete.fresh_fors_coverage`, [ForsCoverage](LeanSphincs/ForsCoverage.lean) | Fixed disclosure sets and a fresh independent uniform digest |
| Serialized signature length = 5684 | `signature_size`, [Layout](LeanSphincs/Layout.lean) | Every signature, including malformed ones |
| WOTS verification walks exactly 72 chain steps | `Completeness.verification_chain_steps`, [Code](LeanSphincs/Code.lean) | Every admissible encoding; the full 391-compression execution theorem is not yet proved |

## Lifetime targets still open

`Lifetimes.RequestedSecurity` states all six targets in the candidate game. None has yet been
proved. Each counts every hash call in the modeled experiment, including honest-party calls,
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
