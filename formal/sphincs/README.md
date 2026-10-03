# leanSPHINCS proofs in Lean 4

**Status: candidate correctness, honest completeness, and all six exact FORS lifetime bounds
after actual signing calls are checked for a fresh independent target. The adaptive SUF-CMA
security reduction is unfinished.**
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
| Candidate probabilities account for all four digest cache states | `Lifetime.probEvent_messageDigest_candidate`, [LifetimeCandidate](LeanSphincs/LifetimeCandidate.lean) | Includes either block queried first and adaptive candidate selection |
| Interleaved digest queries and independent disclosures obey all six bounds | `Lifetime.requested_ideal_interleaving_bounds`, [LifetimeIdealInterleaving](LeanSphincs/LifetimeIdealInterleaving.lean) | Both block orders and cached completions; disclosures are still independent ideal samples |
| Actual prequeried-source weights are bounded using initial conditional forecasts | `Lifetime.expected_prequeried_source_contribution_le`, [LifetimeConditionalSources](LeanSphincs/LifetimeConditionalSources.lean) | All four cache statuses; recorded repeats contribute zero; shared coverage charge remains open |
| Actual signing has an exact future-coverage transition | [LifetimeTransition](LeanSphincs/LifetimeTransition.lean) | Arbitrary caches, repeated sources and exhaustion; the selected-source gain still needs its aggregate probability bound |
| Complete randomizer pools are balanced except with probability ≤ 2^-400 | `Lifetime.probEvent_firstPool_unbalanced`, [LifetimePoolPreparation](LeanSphincs/LifetimePoolPreparation.lean) | Every parameter/root/message triple; exact presampling equality with the lazy ROM |
| Actual adaptive signing has leaf-occupancy overflow probability ≤ 2^-400 + 2^-294 | `Lifetime.actual_interleaved_signing_occupancy`, [LifetimeActualOccupancy](LeanSphincs/LifetimeActualOccupancy.lean) | All six exact limits, empty ROM, arbitrary private/hash interludes; counts accepted positions even when WOTS assembly fails |
| Actual-prefix/independent-suffix occupancy bounds hold for every split | [LifetimeHybridOccupancy](LeanSphincs/LifetimeHybridOccupancy.lean), [LifetimeHybridUnion](LeanSphincs/LifetimeHybridUnion.lean) | All-split sum reserve ≤ 2^-263; a common-space union still requires the stated trace couplings |
| First-touch digest pairs have the uniform full-digest law in either block order | `Lifetime.evalDist_pairedRom`, `Lifetime.evalDist_pairedHash_fresh_digest`, [LifetimePairedOracle](LeanSphincs/LifetimePairedOracle.lean) | The counterpart block is sampled privately; original program outputs and instrumented costs are retained |
| All adaptive digest rectangles contain at most 2^56 candidate pairs except with probability ≤ 2^-400 | [LifetimePairedRectangles](LeanSphincs/LifetimePairedRectangles.lean), [LifetimePairedBankInclusion](LeanSphincs/LifetimePairedBankInclusion.lean) | Original query budget q≤2^127; includes transcript-selected subsets of the final cache |
| Actual-history marginal gains obey a harmonic occupation bound | [LifetimePriorMarginal](LeanSphincs/LifetimePriorMarginal.lean), [LifetimeGainBudget](LeanSphincs/LifetimeGainBudget.lean) | Retains the actual continuation potential; the adaptive variance estimate remains open |
| All six lifetime formulas leave an explicit 1/64 reserve | `Lifetime.requested_fors_reserve`, `Lifetime.normalized_bootstrap_closes`, [LifetimeReserveBudget](LeanSphincs/LifetimeReserveBudget.lean) | Exact arithmetic; the game must still be shown to satisfy the proposed square-root correction inequality |
| Actual signing records have exact digest-source provenance | `Lifetime.signWithSources_forget`, [LifetimeSources](LeanSphincs/LifetimeSources.lean) | Repeated pairs share one cached digest; successful same-pair sources can be excluded |
| Biased cached-source selection is charged to actual grinding work | `Lifetime.expected_signWithSources_weight_le_grinding_cost`, [LifetimeGrindingCost](LeanSphincs/LifetimeGrindingCost.lean) | Explicit weighted source sum and true randomizer entropy; no cache-freshness assumption |
| Adaptive fresh-digest trials satisfy an explicit union bound | `Security.probEvent_adaptiveCoverageSearch_le`, [SecurityAdaptive](LeanSphincs/SecurityAdaptive.lean) | Requires a bound on the expected disclosure-table coverage rate |
| All six exact FORS lifetime expressions are ≤ 2^-127 | `Lifetime.fors_lifetime_ennreal_*`, [LifetimeProbability](LeanSphincs/LifetimeProbability.lean) | Independent binomial occupancy formula; all n≤N; not yet a game reduction |
| Independent FORS experiments satisfy those six bounds | `Lifetime.independent_forgery_lifetime_*`, [LifetimeIndependent](LeanSphincs/LifetimeIndependent.lean) | Explicit uniform index and disclosure sampling, including pruning |
| Successful grinding gives a uniform kept index and 24 uniform FORS selectors | `Lifetime.conditional_grindDigest_after_keygen`, [LifetimeGrinding](LeanSphincs/LifetimeGrinding.lean) | Actual keygen and randomized grinding; positive finite attempt budget; repeated randomizers included |
| One disclosure update is bounded by inserting an independent uniform view | `Lifetime.grindDigest_disclosure_step_le_uniform`, [LifetimeReuse](LeanSphincs/LifetimeReuse.lean) | Every increasing set event; cached accepted views must already be in the prior set |
| N complete signing calls are dominated by N independent disclosure samples | `Lifetime.signing_disclosures_after_keygen_le_uniform`, [LifetimeSigningDisclosure](LeanSphincs/LifetimeSigningDisclosure.lean) | Adaptive/repeated messages, actual keygen/cache and WOTS exhaustion; no adversarial hash interleaving |
| All six exact lifetime bounds hold after those signing calls | `Lifetimes.requested_signing_lifetime_bounds`, [LifetimeSigningBound](LeanSphincs/LifetimeSigningBound.lean) | Fresh independent FORS target; every n≤N; the target search reduction remains open |
| Accepted signatures yield canonical components or concrete exceptional queries | `Security.SignatureWitness.accepted_classification`, [SecuritySignatureWitness](LeanSphincs/SecuritySignatureWitness.lean) | Explicit WOTS reference certificate; includes surrogate, chain, encoding and FORS cases |
| A distinct accepted signature with an honest message/randomizer has an exceptional witness | `Security.SignatureWitness.strong_forgery_same_randomness`, [SecuritySignatureWitness](LeanSphincs/SecuritySignatureWitness.lean) | Reference certificate derived from actual successful honest assembly |
| Actual successful games yield cached forgery witnesses and supported honest signing runs | `Security.SuccessWitness.same_randomness_exception`, [SecurityGameWitness](LeanSphincs/SecurityGameWitness.lean) | Private sampling and actual counted cost retained; exceptional-event probability still unbounded |
| Accepted WOTS leaves have a reference-free query witness | `Security.SuccessWitness.reference_free_classification`, [SecurityUnsignedWitness](LeanSphincs/SecurityUnsignedWitness.lean) | No honest encoding certificate required; bounding the witness needs a hidden-prefix argument |
| Adaptive hidden-seed guesses have probability ≤ q/2^256 | `Security.SeedGuess.adaptive_seed_guess_bound`, [SecuritySeedGuess](LeanSphincs/SecuritySeedGuess.lean) | Explicit seed-independent initial state and private selection strategy |
| Eager preparation preserves the actual game's result and hash cost | `Security.SeedCoupling.evalDist_experiment_prepared`, [SecuritySeedCoupling](LeanSphincs/SecuritySeedCoupling.lean) | Full 256-bit derivation answers, all surrogates; cache remains seed-addressed |
| Full game equals the material-based game with all query costs retained | `Security.MaterialGameCoupling.evalDist_experiment_material`, [SecurityMaterialGameCoupling](LeanSphincs/SecurityMaterialGameCoupling.lean) | Honest derivations use independent material; ordinary adversarial hashes still share the seed-addressed cache |
| Actual seeded security reduces to the independent material game with a shared budget | `Security.SeedLoss.forgeAdvantage_le_cappedMaterial_charge`, [SecuritySeedLoss](LeanSphincs/SecuritySeedLoss.lean) | Seed loss is expected derivation queries/2^256; derivation and other query charges sum to at most q |
| Every actual signing call factors through a selected chain's cutoff | `Security.Prefix.sign_from_referenceCutoff`, [SecurityPrefixFullSign](LeanSphincs/SecurityPrefixFullSign.lean) | Exact counters, private randomizers, FORS openings and exhaustion; aggregate prefix probability accounting remains open |
| Counted signing and public-key generation hide a selected material coordinate given its frontier | `Security.Prefix.counted_prepared_sign_erased`, `Security.Prefix.prepared_keygen_erased`, [SecurityPrefixErasedKeygen](LeanSphincs/SecurityPrefixErasedKeygen.lean) | Explicit erased-material views; ordinary adversarial hash queries still need the stopped coupling |
| The whole material game has that frontier-only honest view | `Security.Prefix.counted_materialGame_erased`, [SecurityPrefixErasedGame](LeanSphincs/SecurityPrefixErasedGame.lean) | Exact joint success/cost law, including adaptive signing and verification; raw adversarial hash answers remain explicit |
| Adaptive hidden-coordinate guesses admit an expected-count bound | `Security.HiddenReveal.adaptive_guess_bound_charge`, [SecurityHiddenCharge](LeanSphincs/SecurityHiddenCharge.lean) | Uniform table with adaptive reveals; count measured in the explicit forced-failure comparison, not a different real-game execution |
| Candidate WOTS/FORS row queries compile to monitored hidden-coordinate guesses | `Security.HiddenGraph.stopped_hidden_input_bound_charge`, [SecurityHiddenGraph](LeanSphincs/SecurityHiddenGraph.lean) | Exact byte parser and active pruned rows; connecting the independent table to the entire game remains open |
| Material and prepared graph outputs split into independent hidden coordinates | `Security.HiddenGraph.evalDist_material_graph_continuation`, [SecurityHiddenGraphSampling](LeanSphincs/SecurityHiddenGraphSampling.lean) | Exact joint sampling law, full outputs/high halves retained; [HiddenGraphRows](LeanSphincs/SecurityHiddenGraphRows.lean) connects canonical cache lookups |
| WOTS reference selection covers counter exhaustion without an honest signature premise | `Security.ReferenceChoice.otsLeaf_classification`, [SecurityReferenceChoice](LeanSphincs/SecurityReferenceChoice.lean) | Uses a valid dummy word on exhaustion; every failed canonical trial is clean for its target |
| Every accepted signature has a chosen canonical opening or an exceptional query | `Security.SignatureWitness.accepted_chosen_classification`, [SecurityReferenceSignature](LeanSphincs/SecurityReferenceSignature.lean) | Unsigned leaves and exhaustion included; [HiddenWitness](LeanSphincs/SecurityHiddenWitness.lean) separates coverage from hidden secret/predecessor queries |
| Failed honest assembly excludes canonical forgeries at that index | `Security.SignatureWitness.accepted_after_failed_finishSign`, [SecurityReferenceFailure](LeanSphincs/SecurityReferenceFailure.lean) | Any later message/randomizer at that index; no extra exhaustion-probability loss |
| Actual randomized signer outputs equal an explicit coordinate-disclosure program | `Security.GraphView.signSource_correct`, [SecurityGraphSigner](LeanSphincs/SecurityGraphSigner.lean) | Exact private-sample law from proved graph values; original internal-cost instrumentation and full-game composition remain open |
| Structural matches cost at most q/2^128 for a fixed clean reference table | `Security.TargetAssignment.counted_structural_target_bound`, [SecurityTargetAssignment](LeanSphincs/SecurityTargetAssignment.lean) | Actual cached queries; canonical input exempt; surrogate targets have no exempt input |
| Adaptive fresh hash queries hit at most two prior targets with probability ≤ q/2^127 | `Security.Primitive.two_target_monitor_bound`, [SecurityPrimitive](LeanSphincs/SecurityPrimitive.lean) | Explicit generic monitor; cached queries and hidden-input guesses still require game-level accounting |
| Local probability charges compose using the actual shared query budget | `Security.forgeAdvantage_le_of_potential`, [SecurityQueryCharge](LeanSphincs/SecurityQueryCharge.lean) | Requires a proved local expected-increase bound and a potential covering successful forgeries |
| Actual graph preparation supplies a clean structural-target cache | `Security.Graph.prepared_structural_target_bound`, [SecurityGraphCache](LeanSphincs/SecurityGraphCache.lean) | Supported preparation and exact seed-material freshness |
| Prepared graph values and inputs equal actual seeded computations | [SecurityGraphCorrectness](LeanSphincs/SecurityGraphCorrectness.lean) | WOTS chains, FORS roots and paths, retained Merkle nodes, surrogate spine and public root |
| Independent graph-label programming preserves the actual random-oracle continuation | `Security.Graph.evalDist_graph_continuation`, [SecurityGraphSampling](LeanSphincs/SecurityGraphSampling.lean) | All original output/count information retained; inactive surrogate labels preserved |
| An outside-subtree surrogate witness has one off-spine target address | `Security.PrunedGraph.cached_surrogate_bad`, [SecurityPrunedGraph](LeanSphincs/SecurityPrunedGraph.lean) | Precise retained/boundary separation, including the actual cached query |
| Serialized signature length = 5684 | `signature_size`, [Layout](LeanSphincs/Layout.lean) | Every signature, including malformed ones |
| Accepted verification uses exactly 391 compressions | `Cost.verification_compressions`, [VerificationCost](LeanSphincs/VerificationCost.lean) | Actual logged hash inputs; every execution costs at most 391 |

## Lifetime targets still open

`Lifetimes.RequestedSecurity` states all six targets in the candidate game. The FORS expression
is connected to actual complete signing calls and a fresh target, but none of the six SUF-CMA
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
