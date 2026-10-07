# leanSPHINCS proofs in Lean 4

**Status: the leanSphincs signer has 127 bits of classical SUF-CMA security in the random-oracle
model at the signature limits below (`LeanSphincs.Lifetimes.requestedSecurity`,
[Lifetimes.lean](LeanSphincs/Lifetimes.lean)).** The proof uses only `propext`, `Classical.choice`
and `Quot.sound`; [Axioms.lean](LeanSphincs/Axioms.lean) pins every public theorem to its axioms.

`LeanSphincs/` models the candidate: one height-26 tree, 24 FORS trees of 1024 leaves, 64 WOTS+C
chains with four positions and sum 120, two message-digest calls, and pruning with surrogate
siblings. A FORS tree has no root hash: the FORS key is one hash of the two level-9 nodes of every
tree, Th(P, A(11, 0, idx), n_0[0] ‖ n_0[1] ‖ … ‖ n_23[0] ‖ n_23[1]) (`ftsKey`, `ftsRecover`); the
verifier folds an opened leaf nine levels and reads the other level-9 node as the last path element. Every hash input is the 16-byte public parameter P, an 8-byte address (4 bytes `lo`,
3 bytes `hi`, one byte type + 32·step) and the payload; the message digest hashes m ‖ 0^8 ‖ ρ (the
root is not hashed). One hash of the seed gives two secrets, the two 16-byte halves of its output:
the starts of chains 2t and 2t + 1 of the one-time key at leaf e are the halves of
H(P ‖ A(0, t, e) ‖ seed), and the secrets of leaves 2t and 2t + 1 of tree κ of FORS instance idx are
the halves of H(P ‖ A(8, κ + 512·t, idx) ‖ seed) (`derivePair`, `otsValues`, `ftsNode`). The public
parameter, the surrogates and R0 each take one hash and keep its first half.
[Scheme.lean](LeanSphincs/Scheme.lean) is the functional model; `Seeded.sign`
derives one base randomizer R0 = Th(P, A(7, 0, 0), seed ‖ m) per message and tries R0, R0 + 1, …
(128-bit little-endian addition) until the digest index lands in the kept subtree, as the Rust
signer does, so a repeated request returns the same signature. The SUF-CMA game is [StatementDet.lean](LeanSphincs/StatementDet.lean): every
adversary, every number q ≥ 1 of hash queries (keygen, signing and verification included), forges
with probability at most q / 2^127.

## Proved lifetimes

| Subtree height b | Proved signature limit N | N_att | N / N_att |
| --- | ---: | ---: | ---: |
| 26 (full tree) | 1,156,000,000 | 1,203,133,390 | 96.1% |
| 20 | 22,380,000 | 23,797,911 | 94.0% |
| 14 | 412,500 | 466,871 | 88.4% |
| 13 | 211,900 | 242,291 | 87.5% |
| 12 | 108,700 | 125,715 | 86.5% |
| 10 | 28,600 | 33,809 | 84.6% |
| 8 | 7,530 | 9,074 | 83.0% |

N_att is the lifetime of the best known FORS attack: the largest N with E[max(X, 1/2)] ≤ 1, where X
is the cover rate per digest query of an adaptive forger (distinct revealed leaves, exact multinomial
loads over the 2^b indices) in units of 2^-127, and 1/2 is the rate of the other searches.

That model omits a WOTS attack. The WOTS key signs the FORS public key, which a forger controls
through the FORS opening. Grinding the WOTS counter until the encoding is a unit neighbour of the
published word (one chain lowered, one raised; about 3,300 such words for the worst leaf of a key)
takes about 2^116 hashes, after which a single chain preimage forges, at about 2·2^-128 per query.
With this attack the best known lifetimes are about 100 / 99.8 / 97.3 / 96.5 / 95.6 / 93.7 / 92.1%
of N_att (b = 26 … 8), so the proved limits are 90–96% of them. [PROOF.md](PROOF.md) explains where the
remaining gap comes from.

These attack figures do not depend on how the signer picks its randomizer. With R0 + i, a forger that
scans a message's randomizers up to the first one that lands knows in advance, per digest query, about
twice as often which digest a pruned key will sign (`Walk.grp_step`); the proof pays for it, and it is
far too rare to change the lifetimes above.

## Checked claims

| Claim | Theorem / file |
| --- | --- |
| **127-bit SUF-CMA security at the limits above** | `Lifetimes.requestedSecurity`, [Lifetimes](LeanSphincs/Lifetimes.lean) |
| The bound follows from rational checks on two budget routes | `ForsPotential.det_bits`, [BridgeDetClose](LeanSphincs/BridgeDetClose.lean); certificates in [LifetimeCertificates](LeanSphincs/LifetimeCertificates.lean) |
| The deterministic signer reduces to a seed-free game of an adversary that never repeats a message | `Det.forgeAdvantageDet_le_seedFree`, [BridgeDet](LeanSphincs/BridgeDet.lean) |
| The secrets are independent uniform values hidden behind the seed: the hash answers the proof programs, two secrets each, are independent uniform outputs | `SeedCoupling.evalDist_hashAnswers`, `SeedCoupling.evalDist_prepared_continuation`, [SecuritySeedCoupling](LeanSphincs/SecuritySeedCoupling.lean) |
| Key generation makes exactly 226·2^b + 2(26 − b) hash calls (per leaf: 32 hashes of the seed, 192 chain steps, the leaf hash) | `Prefix.hashCalls_keygenFromSeed`, [SecurityPrefixErasedKeygen](LeanSphincs/SecurityPrefixErasedKeygen.lean) |
| The signer that walks R0, R0 + 1, … selects a cached digest with exactly the walk probability | `GraphView.loop_bound`, [BridgeSignerFors](LeanSphincs/BridgeSignerFors.lean) |
| One digest query adds at most (2 − 2^-(26−b)) / 2^128 selection mass to a message | `Walk.grp_step`, [BridgeGroup](LeanSphincs/BridgeGroup.lean) |
| A successful seeded signature verifies | `Completeness.correct`, [Correctness](LeanSphincs/Correctness.lean) |
| A signature assembled from any landed randomizer verifies | `Completeness.verify_of_finishSign`, [RandomizedCorrectness](LeanSphincs/RandomizedCorrectness.lean) |
| Every successful randomized signature verifies in the shared ROM | `Completeness.verify_of_keygen_sign_support`, [RandomizedSupport](LeanSphincs/RandomizedSupport.lean) |
| Honest keygen, signing and verification fail with probability ≤ 2^(-2^(b+5)) + 2^(-4194304) | `Completeness.honest_completeness`, [Honest](LeanSphincs/Honest.lean) |
| Sum of honest failure probabilities over all messages ≤ 2^-256 (b ≥ 10) | `Completeness.honest_completeness_all_messages`, [Honest](LeanSphincs/Honest.lean) |
| Computed subtree and surrogate path recover the root | `Completeness.eval_treeFold_pruned_path`, [Pruning](LeanSphincs/Pruning.lean) |
| Graph-label programming preserves the random-oracle continuation | `Security.Graph.evalDist_graph_continuation`, [SecurityGraphSampling](LeanSphincs/SecurityGraphSampling.lean) |
| Serialized signature length = 5684 bytes | `signature_size`, [Layout](LeanSphincs/Layout.lean) |
| Accepted verification uses exactly 373 compressions (at most 373 for any signature) | `Cost.verification_compressions`, [VerificationCost](LeanSphincs/VerificationCost.lean) |

The proof route, its modules, the gap to the attack and the modeling differences with the Rust code
are in [PROOF.md](PROOF.md).

## Build

```sh
cd formal/sphincs
env LEAN_NUM_THREADS=1 nice -n 19 lake exe cache get
env LEAN_NUM_THREADS=1 nice -n 19 lake build
```

The default build includes the candidate with its axiom guards, the retained leanVM proof, and the
legacy query-budget regression check. No `sorry`, `native_decide`, or new axioms are used.

The numeric certificates are generated by `python3 scripts/lifetime_certificates.py` (pure Python,
exact rationals), which rewrites `LeanSphincs/LifetimeCertificates.lean`; the kernel re-checks them
with `decide +kernel` during the build.

## The forest variant (leanSphincs-spicy)

`LeanForest/` proves the same statement for the variant that replaces FORS by a two-level WOTS
forest (4,276-byte signatures, 307 compressions to verify), at lifetimes above the ones of this
table: `LeanForest.Lifetimes.requestedSecurity`, see [FOREST.md](FOREST.md). It is not a default
target: `env LEAN_NUM_THREADS=1 nice -n 19 lake build LeanForest` (its certificates take about 18
minutes and 12 GB of memory).

## The leanVM library

The unchanged `SphincsSecurity/` library is the earlier **three-layer leanVM scheme** from commit
`b7a107256`, credited here and in the checkpoint commits. Its theorem
`sphincs_has_127_bits_of_classical_security` applies only to that older scheme. Its documentation is
[LEANVM_README.md](LEANVM_README.md) and [LEANVM_PROOF.md](LEANVM_PROOF.md).
