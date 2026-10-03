import LeanSphincs.Bytes
import LeanSphincs.Code
import LeanSphincs.Correctness
import LeanSphincs.Counter
import LeanSphincs.Decay
import LeanSphincs.Digest
import LeanSphincs.Encoding
import LeanSphincs.ForsCoverage
import LeanSphincs.Landing
import LeanSphincs.Layout
import LeanSphincs.Pruning
import LeanSphincs.Randomized
import LeanSphincs.RandomizedCorrectness
import LeanSphincs.Recovery
import LeanSphincs.Scheme
import LeanSphincs.Search
import LeanSphincs.Statement
import LeanSphincs.Uniform
import LeanSphincs.World
import LeanSphincs.Fresh
import LeanSphincs.RandomizedDigest
import LeanSphincs.RandomizedSupport
import LeanSphincs.Complete
import LeanSphincs.Honest
import LeanSphincs.LifetimeCoverage
import LeanSphincs.LifetimeMoments
import LeanSphincs.LifetimeBounds
import LeanSphincs.LifetimeProbability
import LeanSphincs.SecurityDigest
import LeanSphincs.SecurityAdaptive
import LeanSphincs.VerificationCost
import LeanSphincs.LifetimeSampling
import LeanSphincs.LifetimeIndependent
import LeanSphincs.LifetimeLanding
import LeanSphincs.SecurityPrimitive
import LeanSphincs.SecurityTreeWitness
import LeanSphincs.SecurityChainWitness
import LeanSphincs.SecurityEncoding
import LeanSphincs.SecurityWotsWitness
import LeanSphincs.SecurityForsWitness
import LeanSphincs.SecurityDomains
import LeanSphincs.SecurityVerifier
import LeanSphincs.LifetimeGrinding
import LeanSphincs.SecuritySignatureWitness
import LeanSphincs.LifetimeReuse
import LeanSphincs.FinishFresh
import LeanSphincs.LifetimeDisclosure
import LeanSphincs.LifetimeDisclosureCache
import LeanSphincs.LifetimeSigningDisclosure
import LeanSphincs.LifetimeTerminal
import LeanSphincs.LifetimeSigningBound
import LeanSphincs.SecurityGameSupport
import LeanSphincs.SecurityGameWitness
import LeanSphincs.SecuritySeedGuess
import LeanSphincs.SecuritySeedModel
import LeanSphincs.LifetimeInterleaving
import LeanSphincs.LifetimeCandidate
import LeanSphincs.SecurityUnsignedWitness
import LeanSphincs.SecurityPrefixOracle
import LeanSphincs.SecurityPrefixSampling
import LeanSphincs.SecuritySeedCoupling
import LeanSphincs.SecurityQueryCharge

/-!
Exact axiom footprints of every public candidate theorem. The build must fail on any footprint
change, including `sorryAx` or native-evaluation axioms. All current lists are subsets of Lean's
three allowed axioms. The legacy library has its own separate public-root guards.
-/

/-- info: 'LeanSphincs.bytesLE_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.bytesLE_injective

/-- info: 'LeanSphincs.bytesLE_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.bytesLE_length

/-- info: 'LeanSphincs.ofNat_inj_of_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.ofNat_inj_of_lt

/-- info: 'LeanSphincs.fieldBytes_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.fieldBytes_injective

/-- info: 'LeanSphincs.Completeness.fieldInput_ne_of_tag_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.fieldInput_ne_of_tag_ne

/-- info: 'LeanSphincs.Completeness.digit_of_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digit_of_sum

/-- info: 'LeanSphincs.Completeness.weight_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.weight_pow

/-- info: 'LeanSphincs.Completeness.sum_lt_193' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.sum_lt_193

/-- info: 'LeanSphincs.Completeness.sum_encoding_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.sum_encoding_pow

/-- info: 'LeanSphincs.Completeness.codeCount_lt_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.codeCount_lt_base

/-- info: 'LeanSphincs.Completeness.weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.weight_eq

/-- info: 'LeanSphincs.Completeness.codeCount_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.codeCount_target

/-- info: 'LeanSphincs.Completeness.two_pow_le_codeCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.two_pow_le_codeCount

/-- info: 'LeanSphincs.Completeness.sum_digits_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.sum_digits_lt

/-- info: 'LeanSphincs.Completeness.digit_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digit_lt

/-- info: 'LeanSphincs.Completeness.packNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.packNat_lt

/-- info: 'LeanSphincs.Completeness.toNat_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.toNat_pack

/-- info: 'LeanSphincs.Completeness.encoding_val' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.encoding_val

/-- info: 'LeanSphincs.Completeness.digestEncoding_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digestEncoding_pack

/-- info: 'LeanSphincs.Completeness.decodeDigest_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.decodeDigest_pack

/-- info: 'LeanSphincs.Completeness.two_pow_le_card_accepting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.two_pow_le_card_accepting

/-- info: 'LeanSphincs.Completeness.codeCount_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.codeCount_exact

/-- info: 'LeanSphincs.Completeness.encoding_antichain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.encoding_antichain

/-- info: 'LeanSphincs.Completeness.verification_chain_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.verification_chain_steps

/-- info: 'LeanSphincs.Completeness.signLayer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.signLayer_spec

/-- info: 'LeanSphincs.Completeness.only_layer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.only_layer

/-- info: 'LeanSphincs.Completeness.treeIndexAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.treeIndexAt_eq

/-- info: 'LeanSphincs.Completeness.leafIndexAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.leafIndexAt_eq

/-- info: 'LeanSphincs.Completeness.digestIndex_truncate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digestIndex_truncate

/-- info: 'LeanSphincs.Completeness.digestValue_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digestValue_index

/-- info: 'LeanSphincs.Completeness.signDigestLoop_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.signDigestLoop_spec

/-- info: 'LeanSphincs.Completeness.sequenceLayers_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.sequenceLayers_spec

/-- info: 'LeanSphincs.Completeness.sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.sign_spec

/-- info: 'LeanSphincs.Completeness.eval_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_layer

/-- info: 'LeanSphincs.Completeness.verify_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.verify_of_parts

/-- info: 'LeanSphincs.Completeness.verify_of_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.verify_of_sign

/-- info: 'LeanSphincs.Completeness.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.correct

/-- info: 'LeanSphincs.Completeness.encodeInput_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.encodeInput_inj

/-- info: 'LeanSphincs.Completeness.probEvent_otsSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_otsSign

/-- info: 'LeanSphincs.Completeness.pow_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.pow_le_half

/-- info: 'LeanSphincs.Completeness.pow_le_half_ennreal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.pow_le_half_ennreal

/-- info: 'LeanSphincs.Completeness.inv_two_pow_succ_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.inv_two_pow_succ_add

/-- info: 'LeanSphincs.Completeness.inv_two_pow_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.inv_two_pow_anti

/-- info: 'LeanSphincs.Completeness.two_pow_div_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.two_pow_div_two_pow

/-- info: 'LeanSphincs.Completeness.randInput_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randInput_inj

/-- info: 'LeanSphincs.Completeness.msgInput_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.msgInput_inj

/-- info: 'LeanSphincs.Completeness.randInput_ne_msgInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randInput_ne_msgInput

/-- info: 'LeanSphincs.Completeness.cached_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.cached_run

/-- info: 'LeanSphincs.Completeness.digestReject_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digestReject_add

/-- info: 'LeanSphincs.Completeness.digestReject_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digestReject_le_one

/-- info: 'LeanSphincs.Completeness.tsum_uniform_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.tsum_uniform_ite

/-- info: 'LeanSphincs.Completeness.probEvent_truncate_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_truncate_mem_le

/-- info: 'LeanSphincs.Completeness.probEvent_signDigestLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_signDigestLoop

/-- info: 'LeanSphincs.Completeness.digestFactor_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digestFactor_room

/-- info: 'LeanSphincs.Completeness.digestFactor_pow_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digestFactor_pow_bound

/-- info: 'LeanSphincs.Completeness.digest_exhaustion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.digest_exhaustion_bound

/-- info: 'LeanSphincs.Completeness.probEvent_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_accept

/-- info: 'LeanSphincs.Completeness.failMass_encoding_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.failMass_encoding_add_le

/-- info: 'LeanSphincs.Completeness.encoding_exhaustion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.encoding_exhaustion_bound

/-- info: 'LeanSphincs.Concrete.fullDigestView_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Concrete.fullDigestView_injective

/-- info: 'LeanSphincs.Concrete.fullDigestView_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Concrete.fullDigestView_bijective

/-- info: 'LeanSphincs.Concrete.evalDist_fullDigestView_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Concrete.evalDist_fullDigestView_uniform

/-- info: 'LeanSphincs.Concrete.covered_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Concrete.covered_card

/-- info: 'LeanSphincs.Concrete.fresh_fors_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Concrete.fresh_fors_coverage

/-- info: 'LeanSphincs.subtreePosition_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.subtreePosition_lt

/-- info: 'LeanSphincs.subtree_size_mul' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.subtree_size_mul

/-- info: 'LeanSphincs.landed_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.landed_card

/-- info: 'LeanSphincs.evalDist_blockIndex_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.evalDist_blockIndex_uniform

/-- info: 'LeanSphincs.fresh_landing_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.fresh_landing_probability

/-- info: 'LeanSphincs.fresh_landing_probability_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.fresh_landing_probability_inv

/-- info: 'LeanSphincs.digest_vector_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.digest_vector_length

/-- info: 'LeanSphincs.signature_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.signature_size

/-- info: 'LeanSphincs.message_digest_size' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.message_digest_size

/-- info: 'LeanSphincs.Completeness.eval_treePath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_treePath

/-- info: 'LeanSphincs.Completeness.landed_div' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.landed_div

/-- info: 'LeanSphincs.Completeness.eval_treeFold_spine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_treeFold_spine

/-- info: 'LeanSphincs.Completeness.eval_treeFold_pruned_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_treeFold_pruned_path

/-- info: 'LeanSphincs.Completeness.finishSign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.finishSign_spec

/-- info: 'LeanSphincs.Completeness.verify_of_finishSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.verify_of_finishSign

/-- info: 'LeanSphincs.Completeness.eval_oracleHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_oracleHash

/-- info: 'LeanSphincs.Completeness.eval_tweakableHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_tweakableHash

/-- info: 'LeanSphincs.Completeness.eval_deriveKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_deriveKey

/-- info: 'LeanSphincs.Completeness.eval_sequenceFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_sequenceFin

/-- info: 'LeanSphincs.Completeness.chainWalk_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.chainWalk_add

/-- info: 'LeanSphincs.Completeness.walk_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.walk_add

/-- info: 'LeanSphincs.Completeness.eval_recoverChain_walk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_recoverChain_walk

/-- info: 'LeanSphincs.Completeness.eval_oneTimePublicKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_oneTimePublicKey

/-- info: 'LeanSphincs.Completeness.otsSignFrom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.otsSignFrom_spec

/-- info: 'LeanSphincs.Completeness.eval_otsLeaf_of_otsSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_otsLeaf_of_otsSign

/-- info: 'LeanSphincs.Completeness.leafOfNat_val' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.leafOfNat_val

/-- info: 'LeanSphincs.Completeness.node_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.node_succ

/-- info: 'LeanSphincs.Completeness.node_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.node_zero

/-- info: 'LeanSphincs.Completeness.eval_treeFold_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_treeFold_path

/-- info: 'LeanSphincs.Completeness.ftsLeafOfNat_val' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.ftsLeafOfNat_val

/-- info: 'LeanSphincs.Completeness.ftsNodeValue_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.ftsNodeValue_succ

/-- info: 'LeanSphincs.Completeness.ftsNodeValue_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.ftsNodeValue_zero

/-- info: 'LeanSphincs.Completeness.eval_ftsOpen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_ftsOpen

/-- info: 'LeanSphincs.Completeness.eval_ftsFold_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_ftsFold_path

/-- info: 'LeanSphincs.Completeness.eval_ftsRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.eval_ftsRecover

/-- info: 'LeanSphincs.Completeness.failMass_eq_probEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.failMass_eq_probEvent

/-- info: 'LeanSphincs.Completeness.fresh_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.fresh_run

/-- info: 'LeanSphincs.Completeness.probEvent_searchLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_searchLoop

/-- info: 'LeanSphincs.Completeness.probEvent_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_bind_le

/-- info: 'LeanSphincs.Completeness.probEvent_bind_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_bind_le_add

/-- info: 'LeanSphincs.Completeness.bytesLE_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.bytesLE_inj

/-- info: 'LeanSphincs.Completeness.counter_bytes_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.counter_bytes_inj

/-- info: 'LeanSphincs.Completeness.otsSignFrom_eq_searchLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.otsSignFrom_eq_searchLoop

/-- info: 'LeanSphincs.hashOutput_eq_of_extract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.hashOutput_eq_of_extract

/-- info: 'LeanSphincs.splitHashOutput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.splitHashOutput_injective

/-- info: 'LeanSphincs.splitHashOutput_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.splitHashOutput_bijective

/-- info: 'LeanSphincs.evalDist_hashOutput_extract_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.evalDist_hashOutput_extract_uniform

/-- info: 'LeanSphincs.evalDist_truncateHash_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.evalDist_truncateHash_uniform

/-- info: 'LeanSphincs.probEvent_uniform_truncateHash_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.probEvent_uniform_truncateHash_eq

/-- info: 'LeanSphincs.probEvent_uniform_truncateHash_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.probEvent_uniform_truncateHash_mem

/-- info: 'LeanSphincs.Completeness.simulate_lift_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.simulate_lift_hash

/-- info: 'LeanSphincs.Completeness.run_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.run_lift_prob

/-- info: 'LeanSphincs.Completeness.PreservesFresh.pure'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.pure'

/-- info: 'LeanSphincs.Completeness.PreservesFresh.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.bind

/-- info: 'LeanSphincs.Completeness.PreservesFresh.query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.query

/-- info: 'LeanSphincs.Completeness.PreservesFresh.tweakableHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.tweakableHash

/-- info: 'LeanSphincs.Completeness.PreservesFresh.deriveKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.deriveKey

/-- info: 'LeanSphincs.Completeness.PreservesFresh.sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.sequenceFin

/-- info: 'LeanSphincs.Completeness.PreservesFresh.messageDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.messageDigest

/-- info: 'LeanSphincs.Completeness.fieldInput_ne_of_tag_ne_across' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.fieldInput_ne_of_tag_ne_across

/-- info: 'LeanSphincs.Completeness.keygenDomain_tag_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.keygenDomain_tag_ne

/-- info: 'LeanSphincs.Completeness.structuralFresh_of_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.structuralFresh_of_tag

/-- info: 'LeanSphincs.Completeness.structuralFresh_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.structuralFresh_encoding

/-- info: 'LeanSphincs.Completeness.messageInput_ne_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.messageInput_ne_encoding

/-- info: 'LeanSphincs.Completeness.structuralFresh_message' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.structuralFresh_message

/-- info: 'LeanSphincs.Completeness.PreservesFresh.chainWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.chainWalk

/-- info: 'LeanSphincs.Completeness.PreservesFresh.oneTimePublicKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.oneTimePublicKey

/-- info: 'LeanSphincs.Completeness.PreservesFresh.treeNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.treeNode

/-- info: 'LeanSphincs.Completeness.PreservesFresh.surrogate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.surrogate

/-- info: 'LeanSphincs.Completeness.PreservesFresh.spineNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.spineNode

/-- info: 'LeanSphincs.Completeness.PreservesFresh.keygenFromSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.keygenFromSeed

/-- info: 'LeanSphincs.Completeness.PreservesFresh.ftsNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.ftsNode

/-- info: 'LeanSphincs.Completeness.PreservesFresh.ftsKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.ftsKey

/-- info: 'LeanSphincs.Completeness.PreservesFresh.ftsOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.ftsOpen

/-- info: 'LeanSphincs.Completeness.run_randomizedDigest_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.run_randomizedDigest_succ

/-- info: 'LeanSphincs.Completeness.tsum_randomness_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.tsum_randomness_ite

/-- info: 'LeanSphincs.Completeness.probEvent_randomness_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_randomness_mem_le

/-- info: 'LeanSphincs.Completeness.probEvent_randomizedDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.probEvent_randomizedDigest

/-- info: 'LeanSphincs.Completeness.randomized_digest_exhaustion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randomized_digest_exhaustion_bound

/-- info: 'LeanSphincs.Completeness.query_support_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.query_support_cached

/-- info: 'LeanSphincs.Completeness.replay_hash_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.replay_hash_support

/-- info: 'LeanSphincs.Completeness.hash_support_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.hash_support_cache_le

/-- info: 'LeanSphincs.Completeness.randomizedDigest_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randomizedDigest_support

/-- info: 'LeanSphincs.Completeness.randomized_sign_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randomized_sign_replay

/-- info: 'LeanSphincs.Completeness.correct_randomized_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.correct_randomized_assembly

/-- info: 'LeanSphincs.Completeness.verify_of_keygen_sign_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.verify_of_keygen_sign_support

/-- info: 'LeanSphincs.Completeness.encodingFresh_empty' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.encodingFresh_empty

/-- info: 'LeanSphincs.Completeness.encodingFresh_of_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.encodingFresh_of_preserves

/-- info: 'LeanSphincs.Completeness.signLayer_exhaustion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.signLayer_exhaustion_bound

/-- info: 'LeanSphincs.Completeness.finishSign_exhaustion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.finishSign_exhaustion_bound

/-- info: 'LeanSphincs.Completeness.randomOracle_preserves_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randomOracle_preserves_encoding

/-- info: 'LeanSphincs.Completeness.randomizedDigest_preserves_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randomizedDigest_preserves_encoding

/-- info: 'LeanSphincs.Completeness.randomized_sign_exhaustion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.randomized_sign_exhaustion_bound

/-- info: 'LeanSphincs.Completeness.keygen_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.keygen_fresh

/-- info: 'LeanSphincs.Completeness.honest_sign_exhaustion_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.honest_sign_exhaustion_bound

/-- info: 'LeanSphincs.Completeness.honest_sign_exhaustion_negligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.honest_sign_exhaustion_negligible

/-- info: 'LeanSphincs.Completeness.honest_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.honest_completeness

/-- info: 'LeanSphincs.Completeness.honest_completeness_negligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.honest_completeness_negligible

/-- info: 'LeanSphincs.Lifetimes.requested_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetimes.requested_completeness

/-- info: 'LeanSphincs.Lifetime.pow_one_sub_le_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.pow_one_sub_le_quadratic

/-- info: 'LeanSphincs.Lifetime.cubic_le_pow_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.cubic_le_pow_one_sub

/-- info: 'LeanSphincs.Lifetime.cast_choose_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.cast_choose_three

/-- info: 'LeanSphincs.Lifetime.power24_le_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.power24_le_quadratic

/-- info: 'LeanSphincs.Lifetime.fors_power_majorant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_power_majorant

/-- info: 'LeanSphincs.Lifetime.binomialMean_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_add

/-- info: 'LeanSphincs.Lifetime.binomialMean_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_sub

/-- info: 'LeanSphincs.Lifetime.binomialMean_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_mul

/-- info: 'LeanSphincs.Lifetime.binomialMean_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_sum

/-- info: 'LeanSphincs.Lifetime.binomialMean_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_mono

/-- info: 'LeanSphincs.Lifetime.binomialMean_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_const

/-- info: 'LeanSphincs.Lifetime.binomialMean_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_nonneg

/-- info: 'LeanSphincs.Lifetime.binomialMean_mono_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_mono_steps

/-- info: 'LeanSphincs.Lifetime.binomialMean_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_choose

/-- info: 'LeanSphincs.Lifetime.binomialMean_descFactorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_descFactorial

/-- info: 'LeanSphincs.Lifetime.binomialMean_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_power

/-- info: 'LeanSphincs.Lifetime.binomialMean_power_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_power_numerator

/-- info: 'LeanSphincs.Lifetime.binomialMean_fors_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.binomialMean_fors_le

/-- info: 'LeanSphincs.Lifetime.forsBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.forsBound_nonneg

/-- info: 'LeanSphincs.Lifetime.forsBound_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.forsBound_mono

/-- info: 'LeanSphincs.Lifetime.forsBound_le_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.forsBound_le_of_certificate

/-- info: 'LeanSphincs.Lifetime.certificate_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.certificate_full

/-- info: 'LeanSphincs.Lifetime.certificate_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.certificate_pruned20

/-- info: 'LeanSphincs.Lifetime.certificate_pruned13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.certificate_pruned13

/-- info: 'LeanSphincs.Lifetime.certificate_pruned14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.certificate_pruned14

/-- info: 'LeanSphincs.Lifetime.certificate_pruned12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.certificate_pruned12

/-- info: 'LeanSphincs.Lifetime.certificate_pruned10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.certificate_pruned10

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_full

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned20

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned13

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned14

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned12

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned10

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_full_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_full_le

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned20_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned20_le

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned13_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned13_le

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned14_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned14_le

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned12_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned12_le

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_pruned10_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_pruned10_le

/-- info: 'LeanSphincs.Lifetime.ofReal_binomialMean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.ofReal_binomialMean

/-- info: 'LeanSphincs.Lifetime.ofReal_forsBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.ofReal_forsBound

/-- info: 'LeanSphincs.Lifetime.forsBoundENNReal_le_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.forsBoundENNReal_le_of_real

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_ennreal_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_ennreal_full

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned20

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned13

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned14

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned12

/-- info: 'LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fors_lifetime_ennreal_pruned10

/-- info: 'LeanSphincs.Security.joinDigest_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.joinDigest_injective

/-- info: 'LeanSphincs.Security.joinDigest_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.joinDigest_bijective

/-- info: 'LeanSphincs.Security.truncateMessageDigest_eq_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.truncateMessageDigest_eq_join

/-- info: 'LeanSphincs.Security.evalDist_digestBlocks_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.evalDist_digestBlocks_uniform

/-- info: 'LeanSphincs.Security.digestInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.digestInput_injective

/-- info: 'LeanSphincs.Security.run_messageDigest_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.run_messageDigest_fresh

/-- info: 'LeanSphincs.Security.evalDist_messageDigest_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.evalDist_messageDigest_fresh

/-- info: 'LeanSphincs.Security.probEvent_messageDigest_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.probEvent_messageDigest_covered

/-- info: 'LeanSphincs.Security.run_messageDigest_cached_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.run_messageDigest_cached_first

/-- info: 'LeanSphincs.Security.probEvent_messageDigest_cached_first_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.probEvent_messageDigest_cached_first_covered

/-- info: 'LeanSphincs.Security.coverageRate_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.coverageRate_le_one

/-- info: 'LeanSphincs.Security.probEvent_freshCoverageTrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.probEvent_freshCoverageTrial

/-- info: 'LeanSphincs.Security.probEvent_adaptive_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.probEvent_adaptive_coverage

/-- info: 'LeanSphincs.Security.probEvent_adaptiveCoverageSearch_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.probEvent_adaptiveCoverageSearch_le

/-- info: 'LeanSphincs.Cost.hashTrace_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.hashTrace_pure

/-- info: 'LeanSphincs.Cost.hashTrace_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.hashTrace_query_bind

/-- info: 'LeanSphincs.Cost.hashTrace_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.hashTrace_bind

/-- info: 'LeanSphincs.Cost.compressions_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_pure

/-- info: 'LeanSphincs.Cost.compressions_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_bind

/-- info: 'LeanSphincs.Cost.compressions_oracleHash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_oracleHash

/-- info: 'LeanSphincs.Cost.tweakableHashInput_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.tweakableHashInput_length

/-- info: 'LeanSphincs.Cost.compressions_tweakableHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_tweakableHash

/-- info: 'LeanSphincs.Cost.compressions_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_sequenceFin

/-- info: 'LeanSphincs.Cost.compressions_chainWalk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_chainWalk

/-- info: 'LeanSphincs.Cost.compressions_recoverChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_recoverChain

/-- info: 'LeanSphincs.Cost.compressions_leafHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_leafHash

/-- info: 'LeanSphincs.Cost.compressions_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_encode

/-- info: 'LeanSphincs.Cost.compressions_treeFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_treeFold

/-- info: 'LeanSphincs.Cost.compressions_ftsLeafHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_ftsLeafHash

/-- info: 'LeanSphincs.Cost.compressions_ftsFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_ftsFold

/-- info: 'LeanSphincs.Cost.compressions_ftsRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_ftsRecover

/-- info: 'LeanSphincs.Cost.compressions_messageDigestCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_messageDigestCall

/-- info: 'LeanSphincs.Cost.compressions_messageDigest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_messageDigest

/-- info: 'LeanSphincs.Cost.encode_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.encode_valid

/-- info: 'LeanSphincs.Cost.compressions_otsLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_otsLeaf

/-- info: 'LeanSphincs.Cost.compressions_verifyLayers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.compressions_verifyLayers

/-- info: 'LeanSphincs.Cost.verification_compressions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.verification_compressions

/-- info: 'LeanSphincs.Cost.verification_compressions_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Cost.verification_compressions_le

/-- info: 'LeanSphincs.Lifetime.missing_history_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.missing_history_card

/-- info: 'LeanSphincs.Lifetime.hit_history_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.hit_history_card

/-- info: 'LeanSphincs.Lifetime.covered_history_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.covered_history_card

/-- info: 'LeanSphincs.Lifetime.probEvent_history_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_history_covered

/-- info: 'LeanSphincs.Lifetime.probEvent_independentTargetCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_independentTargetCoverage

/-- info: 'LeanSphincs.Lifetime.independent_coverage_lifetime_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independent_coverage_lifetime_bound

/-- info: 'LeanSphincs.Lifetime.probEvent_initialSubtree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_initialSubtree

/-- info: 'LeanSphincs.Lifetime.probEvent_independentTargetCoverageRandom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_independentTargetCoverageRandom

/-- info: 'LeanSphincs.Lifetime.probEvent_independentForgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_independentForgery

/-- info: 'LeanSphincs.Lifetime.independent_forgery_lifetime_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independent_forgery_lifetime_full

/-- info: 'LeanSphincs.Lifetime.independent_forgery_lifetime_pruned20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independent_forgery_lifetime_pruned20

/-- info: 'LeanSphincs.Lifetime.independent_forgery_lifetime_pruned13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independent_forgery_lifetime_pruned13

/-- info: 'LeanSphincs.Lifetime.independent_forgery_lifetime_pruned14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independent_forgery_lifetime_pruned14

/-- info: 'LeanSphincs.Lifetime.independent_forgery_lifetime_pruned12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independent_forgery_lifetime_pruned12

/-- info: 'LeanSphincs.Lifetime.independent_forgery_lifetime_pruned10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.independent_forgery_lifetime_pruned10

/-- info: 'LeanSphincs.Lifetime.local_keptView' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.local_keptView

/-- info: 'LeanSphincs.Lifetime.fullDigestView_card_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fullDigestView_card_factor

/-- info: 'LeanSphincs.Lifetime.probEvent_landed_localDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_landed_localDigest

/-- info: 'LeanSphincs.Lifetime.probEvent_fullDigest_landed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_fullDigest_landed

/-- info: 'LeanSphincs.Lifetime.conditional_landed_digest_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.conditional_landed_digest_uniform

/-- info: 'LeanSphincs.Lifetime.probEvent_messageDigest_landed_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_messageDigest_landed_local

/-- info: 'LeanSphincs.Security.Primitive.fresh_preimage_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.fresh_preimage_probability

/-- info: 'LeanSphincs.Security.Primitive.fresh_targetSet_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.fresh_targetSet_probability

/-- info: 'LeanSphincs.Security.Primitive.freshHit_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.freshHit_probability

/-- info: 'LeanSphincs.Security.Primitive.freshHit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.freshHit_probability_le

/-- info: 'LeanSphincs.Security.Primitive.monitor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.monitor_bound

/-- info: 'LeanSphincs.Security.Primitive.single_target_monitor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.single_target_monitor_bound

/-- info: 'LeanSphincs.Security.Primitive.two_target_monitor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.two_target_monitor_bound

/-- info: 'LeanSphincs.Security.Primitive.initialized_monitor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Primitive.initialized_monitor_bound

/-- info: 'LeanSphincs.Security.queriedInputs_pure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.queriedInputs_pure

/-- info: 'LeanSphincs.Security.queriedInputs_query_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.queriedInputs_query_bind

/-- info: 'LeanSphincs.Security.queriedInputs_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.queriedInputs_bind

/-- info: 'LeanSphincs.Security.queriedInputs_tweakableHash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.queriedInputs_tweakableHash

/-- info: 'LeanSphincs.Security.nodePayload_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.nodePayload_injective

/-- info: 'LeanSphincs.Security.orderedPayload_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.orderedPayload_injective

/-- info: 'LeanSphincs.Security.orderedPayload_cross' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.orderedPayload_cross

/-- info: 'LeanSphincs.Security.merkleValue_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.merkleValue_zero

/-- info: 'LeanSphincs.Security.merkleValue_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.merkleValue_succ

/-- info: 'LeanSphincs.Security.merkleInput_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.merkleInput_mem

/-- info: 'LeanSphincs.Security.merkleFold_treeFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.merkleFold_treeFold

/-- info: 'LeanSphincs.Security.quotient_eq_of_parent_bit_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.quotient_eq_of_parent_bit_eq

/-- info: 'LeanSphincs.Security.merkleFold_classification' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.merkleFold_classification

/-- info: 'LeanSphincs.Security.merkleFold_same_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.merkleFold_same_index

/-- info: 'LeanSphincs.Security.quotient_eq_above' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.quotient_eq_above

/-- info: 'LeanSphincs.Security.canonicalTreePath_surrogate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.canonicalTreePath_surrogate

/-- info: 'LeanSphincs.Security.canonicalTreePath_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.canonicalTreePath_root

/-- info: 'LeanSphincs.Security.surrogatePreimage_queried' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.surrogatePreimage_queried

/-- info: 'LeanSphincs.Security.outside_subtree_treeFold_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.outside_subtree_treeFold_witness

/-- info: 'LeanSphincs.Security.inside_subtree_treeFold_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.inside_subtree_treeFold_witness

/-- info: 'LeanSphincs.Security.queriedInputs_mono_bind_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.queriedInputs_mono_bind_left

/-- info: 'LeanSphincs.Security.queriedInputs_mono_bind_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.queriedInputs_mono_bind_right

/-- info: 'LeanSphincs.Security.queriedInputs_sequenceFin_component' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.queriedInputs_sequenceFin_component

/-- info: 'LeanSphincs.Security.ContainsRun.bind_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ContainsRun.bind_left

/-- info: 'LeanSphincs.Security.ContainsRun.bind_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ContainsRun.bind_right

/-- info: 'LeanSphincs.Security.ContainsRun.sequenceFin_component' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ContainsRun.sequenceFin_component

/-- info: 'LeanSphincs.Security.Chain.honestChain_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.honestChain_succ

/-- info: 'LeanSphincs.Security.Chain.walkValue_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.walkValue_succ

/-- info: 'LeanSphincs.Security.Chain.chainWalk_extract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.chainWalk_extract

/-- info: 'LeanSphincs.Security.Chain.chainWalk_extract_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.chainWalk_extract_above

/-- info: 'LeanSphincs.Security.Chain.chainWalk_query_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.chainWalk_query_mem

/-- info: 'LeanSphincs.Security.Chain.ChainHit.input_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.ChainHit.input_ne

/-- info: 'LeanSphincs.Security.Chain.recover_canonical_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.recover_canonical_above

/-- info: 'LeanSphincs.Security.Chain.recover_frontier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.recover_frontier

/-- info: 'LeanSphincs.Security.Chain.recover_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.recover_value

/-- info: 'LeanSphincs.Security.Chain.recover_contact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.recover_contact

/-- info: 'LeanSphincs.Security.Chain.recover_twoEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.recover_twoEdge

/-- info: 'LeanSphincs.Security.Chain.chain_input_address_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.chain_input_address_injective

/-- info: 'LeanSphincs.Security.Chain.TwoEdge.distinct_queries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Chain.TwoEdge.distinct_queries

/-- info: 'LeanSphincs.Security.EncodingCode.UnitNeighborAt.ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.UnitNeighborAt.ne

/-- info: 'LeanSphincs.Security.EncodingCode.UnitNeighborAt.lowered_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.UnitNeighborAt.lowered_unique

/-- info: 'LeanSphincs.Security.EncodingCode.mem_unitNeighbors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.mem_unitNeighbors

/-- info: 'LeanSphincs.Security.EncodingCode.mem_allUnitNeighbors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.mem_allUnitNeighbors

/-- info: 'LeanSphincs.Security.EncodingCode.unitNeighbors_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.unitNeighbors_card_le

/-- info: 'LeanSphincs.Security.EncodingCode.allUnitNeighbors_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.allUnitNeighbors_card_le

/-- info: 'LeanSphincs.Security.EncodingCode.unitNeighborBound_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.unitNeighborBound_eq

/-- info: 'LeanSphincs.Security.EncodingCode.neighborBound_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.neighborBound_eq

/-- info: 'LeanSphincs.Security.EncodingCode.unitNeighbor_of_backwardWeight_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.unitNeighbor_of_backwardWeight_one

/-- info: 'LeanSphincs.Security.EncodingCode.eq_of_backwardWeight_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.eq_of_backwardWeight_zero

/-- info: 'LeanSphincs.Security.EncodingCode.backwardWeight_two_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.backwardWeight_two_witness

/-- info: 'LeanSphincs.Security.EncodingCode.valid_encoding_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.valid_encoding_classification

/-- info: 'LeanSphincs.Security.EncodingCode.digestEncoding_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.digestEncoding_injective

/-- info: 'LeanSphincs.Security.EncodingCode.decode_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.decode_valid

/-- info: 'LeanSphincs.Security.EncodingCode.decode_some_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.decode_some_injective

/-- info: 'LeanSphincs.Security.EncodingCode.mem_decodingDigests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.mem_decodingDigests

/-- info: 'LeanSphincs.Security.EncodingCode.decodingDigests_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.decodingDigests_card_le

/-- info: 'LeanSphincs.Security.EncodingCode.decodingDigests_uniform_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.decodingDigests_uniform_le

/-- info: 'LeanSphincs.Security.EncodingCode.unit_neighbor_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.EncodingCode.unit_neighbor_probability

/-- info: 'LeanSphincs.Security.Wots.leafPayload_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.leafPayload_injective

/-- info: 'LeanSphincs.Security.Wots.encodingInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.encodingInput_injective

/-- info: 'LeanSphincs.Security.Wots.encode_query_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.encode_query_mem

/-- info: 'LeanSphincs.Security.Wots.decode_of_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.decode_of_encode

/-- info: 'LeanSphincs.Security.Wots.otsLeaf_chain_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.otsLeaf_chain_run

/-- info: 'LeanSphincs.Security.Wots.otsLeaf_leaf_query_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.otsLeaf_leaf_query_mem

/-- info: 'LeanSphincs.Security.Wots.otsLeaf_marker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.otsLeaf_marker

/-- info: 'LeanSphincs.Security.Wots.otsLeaf_chain_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.otsLeaf_chain_classification

/-- info: 'LeanSphincs.Security.Wots.otsLeaf_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.otsLeaf_classification

/-- info: 'LeanSphincs.Security.Wots.same_word_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.same_word_classification

/-- info: 'LeanSphincs.Security.Wots.otsLeaf_signature_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.otsLeaf_signature_classification

/-- info: 'LeanSphincs.Security.Wots.LeafOutputMatch.distinct_inputs' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Wots.LeafOutputMatch.distinct_inputs

/-- info: 'LeanSphincs.Security.flatMap_ofFn_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.flatMap_ofFn_injective

/-- info: 'LeanSphincs.Security.ftsRootsPayload_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.ftsRootsPayload_injective

/-- info: 'LeanSphincs.Security.Fors.merkleFold_ftsFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.merkleFold_ftsFold

/-- info: 'LeanSphincs.Security.Fors.canonical_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.canonical_root

/-- info: 'LeanSphincs.Security.Fors.tree_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.tree_classification

/-- info: 'LeanSphincs.Security.Fors.eval_ftsRecover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.eval_ftsRecover

/-- info: 'LeanSphincs.Security.Fors.recover_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.recover_classification

/-- info: 'LeanSphincs.Security.Fors.leafInput_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.leafInput_mem

/-- info: 'LeanSphincs.Security.Fors.nodeInput_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.nodeInput_mem

/-- info: 'LeanSphincs.Security.Fors.rootsInput_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.rootsInput_mem

/-- info: 'LeanSphincs.Security.Fors.Opening.trueSecretQuery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.Opening.trueSecretQuery

/-- info: 'LeanSphincs.Security.Fors.Exception.queried_output_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Fors.Exception.queried_output_match

/-- info: 'LeanSphincs.Security.fieldInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.fieldInput_injective

/-- info: 'LeanSphincs.Security.tweakableInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.tweakableInput_injective

/-- info: 'LeanSphincs.Security.deriveFields_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.deriveFields_injective

/-- info: 'LeanSphincs.Security.keygenInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.keygenInput_injective

/-- info: 'LeanSphincs.Security.derive_tag_ne_hash_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.derive_tag_ne_hash_tag

/-- info: 'LeanSphincs.Security.keygenInput_ne_hashInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.keygenInput_ne_hashInput

/-- info: 'LeanSphincs.Security.verify_eq_single_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.verify_eq_single_layer

/-- info: 'LeanSphincs.Security.verification_fors_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.verification_fors_run

/-- info: 'LeanSphincs.Security.verified_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.verified_tree

/-- info: 'LeanSphincs.Security.verified_pruned_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.verified_pruned_tree

/-- info: 'LeanSphincs.Completeness.honest_completeness_all_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.honest_completeness_all_messages

/-- info: 'LeanSphincs.Lifetime.digestInput_calls_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestInput_calls_ne

/-- info: 'LeanSphincs.Lifetime.firstRejected_cacheQuery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.firstRejected_cacheQuery

/-- info: 'LeanSphincs.Lifetime.secondFresh_cacheQuery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.secondFresh_cacheQuery

/-- info: 'LeanSphincs.Lifetime.randomizedDigest_accepted_initially_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.randomizedDigest_accepted_initially_fresh

/-- info: 'LeanSphincs.Lifetime.grindDigest_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigest_zero

/-- info: 'LeanSphincs.Lifetime.grindDigest_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigest_succ

/-- info: 'LeanSphincs.Lifetime.probEvent_bind_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_bind_factor

/-- info: 'LeanSphincs.Lifetime.probEvent_branch_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_branch_factor

/-- info: 'LeanSphincs.Lifetime.probEvent_finishGrindingDigest_cached_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_finishGrindingDigest_cached_first

/-- info: 'LeanSphincs.Lifetime.fresh_grinding_acceptance_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fresh_grinding_acceptance_mass

/-- info: 'LeanSphincs.Lifetime.grindDigest_uniform_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigest_uniform_factor

/-- info: 'LeanSphincs.Lifetime.grindDigest_fresh_uniform_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigest_fresh_uniform_factor

/-- info: 'LeanSphincs.Lifetime.probEvent_uniform_bind_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_uniform_bind_ge

/-- info: 'LeanSphincs.Lifetime.grindDigest_success_ge_landing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigest_success_ge_landing

/-- info: 'LeanSphincs.Lifetime.conditional_grindDigest_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.conditional_grindDigest_uniform

/-- info: 'LeanSphincs.Lifetime.keygen_message_inputs_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.keygen_message_inputs_fresh

/-- info: 'LeanSphincs.Lifetime.conditional_grindDigest_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.conditional_grindDigest_after_keygen

/-- info: 'LeanSphincs.Security.keygen_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.keygen_root

/-- info: 'LeanSphincs.Security.keygen_secret_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.keygen_secret_fields

/-- info: 'LeanSphincs.Security.SignatureWitness.verification_fors_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.verification_fors_run

/-- info: 'LeanSphincs.Security.SignatureWitness.canonical_wots_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.canonical_wots_leaf

/-- info: 'LeanSphincs.Security.SignatureWitness.reference_of_signLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.reference_of_signLayer

/-- info: 'LeanSphincs.Security.SignatureWitness.canonicalOpening_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.canonicalOpening_unique

/-- info: 'LeanSphincs.Security.SignatureWitness.finishSign_randomness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.finishSign_randomness

/-- info: 'LeanSphincs.Security.SignatureWitness.canonical_of_finishSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.canonical_of_finishSign

/-- info: 'LeanSphincs.Security.SignatureWitness.canonical_eq_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.canonical_eq_honest

/-- info: 'LeanSphincs.Security.SignatureWitness.accepted_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.accepted_classification

/-- info: 'LeanSphincs.Security.SignatureWitness.strong_forgery_same_randomness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SignatureWitness.strong_forgery_same_randomness

/-- info: 'LeanSphincs.Lifetime.reuseInvariant_of_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reuseInvariant_of_fresh

/-- info: 'LeanSphincs.Lifetime.ReuseInvariant.mono_prior' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.ReuseInvariant.mono_prior

/-- info: 'LeanSphincs.Lifetime.reuseInvariant_rejected_cacheQuery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reuseInvariant_rejected_cacheQuery

/-- info: 'LeanSphincs.Lifetime.run_messageDigest_cached_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.run_messageDigest_cached_both

/-- info: 'LeanSphincs.Lifetime.finishGrindingDigest_cached_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finishGrindingDigest_cached_both

/-- info: 'LeanSphincs.Lifetime.probEvent_finishGrindingDigest_local_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_finishGrindingDigest_local_fresh

/-- info: 'LeanSphincs.Lifetime.fresh_grinding_acceptance_mass_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fresh_grinding_acceptance_mass_local

/-- info: 'LeanSphincs.Lifetime.probEvent_uniform_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_uniform_bind_le

/-- info: 'LeanSphincs.Lifetime.probEvent_branch_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_branch_eq

/-- info: 'LeanSphincs.Lifetime.fresh_grinding_branch_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.fresh_grinding_branch_le_uniform

/-- info: 'LeanSphincs.Lifetime.cached_accepted_adds_no_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.cached_accepted_adds_no_view

/-- info: 'LeanSphincs.Lifetime.grindDigest_new_view_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigest_new_view_le_uniform

/-- info: 'LeanSphincs.Lifetime.grindDigest_disclosure_step_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigest_disclosure_step_le_uniform

/-- info: 'LeanSphincs.Completeness.PreservesFresh.otsSignFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.otsSignFrom

/-- info: 'LeanSphincs.Completeness.PreservesFresh.treePath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.treePath

/-- info: 'LeanSphincs.Completeness.PreservesFresh.signLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.signLayer

/-- info: 'LeanSphincs.Completeness.finishSign_eq_digest_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.finishSign_eq_digest_body

/-- info: 'LeanSphincs.Completeness.finishSignBody_preserves_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.finishSignBody_preserves_message

/-- info: 'LeanSphincs.Completeness.PreservesFresh.cache_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.PreservesFresh.cache_eq

/-- info: 'LeanSphincs.Completeness.finishSignBody_message_cache_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Completeness.finishSignBody_message_cache_eq

/-- info: 'LeanSphincs.Lifetime.uniformDisclosureSet_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniformDisclosureSet_zero

/-- info: 'LeanSphincs.Lifetime.uniformDisclosureSet_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniformDisclosureSet_succ

/-- info: 'LeanSphincs.Lifetime.uniformDisclosureSet_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.uniformDisclosureSet_mono

/-- info: 'LeanSphincs.Lifetime.disclosureProcess_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.disclosureProcess_le_uniform

/-- info: 'LeanSphincs.Lifetime.digestInput_message_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestInput_message_injective

/-- info: 'LeanSphincs.Lifetime.digestInput_randomness_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.digestInput_randomness_injective

/-- info: 'LeanSphincs.Lifetime.reuseInvariant_other_message_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reuseInvariant_other_message_query

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_rejected_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_rejected_query

/-- info: 'LeanSphincs.Lifetime.completedDigestCache_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.completedDigestCache_first

/-- info: 'LeanSphincs.Lifetime.completedDigestCache_second' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.completedDigestCache_second

/-- info: 'LeanSphincs.Lifetime.completedDigestCache_other_randomness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.completedDigestCache_other_randomness

/-- info: 'LeanSphincs.Lifetime.reuseInvariant_completed_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reuseInvariant_completed_digest

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_completed_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_completed_digest

/-- info: 'LeanSphincs.Lifetime.grindDigestState_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigestState_fst

/-- info: 'LeanSphincs.Lifetime.grindDigestState_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigestState_zero

/-- info: 'LeanSphincs.Lifetime.grindDigestState_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigestState_succ

/-- info: 'LeanSphincs.Lifetime.grindDigestState_preserves_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigestState_preserves_global

/-- info: 'LeanSphincs.Lifetime.grindDisclosureStep_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDisclosureStep_preserves

/-- info: 'LeanSphincs.Lifetime.grindDisclosureStep_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDisclosureStep_le_uniform

/-- info: 'LeanSphincs.Lifetime.grinding_disclosures_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grinding_disclosures_le_uniform

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_after_keygen

/-- info: 'LeanSphincs.Lifetime.grinding_disclosures_after_keygen_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grinding_disclosures_after_keygen_le_uniform

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_of_message_cache_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_of_message_cache_eq

/-- info: 'LeanSphincs.Lifetime.finishSignBody_preserves_globalReuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.finishSignBody_preserves_globalReuse

/-- info: 'LeanSphincs.Lifetime.signWithDisclosures_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithDisclosures_forget

/-- info: 'LeanSphincs.Lifetime.grindDigestState_none_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigestState_none_mem

/-- info: 'LeanSphincs.Lifetime.grindDigestState_some_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.grindDigestState_some_mem

/-- info: 'LeanSphincs.Lifetime.signWithDisclosures_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithDisclosures_preserves

/-- info: 'LeanSphincs.Lifetime.signWithDisclosures_le_grinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signWithDisclosures_le_grinding

/-- info: 'LeanSphincs.Lifetime.signingDisclosureStep_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signingDisclosureStep_preserves

/-- info: 'LeanSphincs.Lifetime.signingDisclosureStep_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signingDisclosureStep_le_uniform

/-- info: 'LeanSphincs.Lifetime.signing_disclosures_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signing_disclosures_le_uniform

/-- info: 'LeanSphincs.Lifetime.signing_disclosures_after_keygen_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signing_disclosures_after_keygen_le_uniform

/-- info: 'LeanSphincs.Lifetime.sampleWord_eq_sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.sampleWord_eq_sequenceFin

/-- info: 'LeanSphincs.Lifetime.evalDist_sampleWord_uniform_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_sampleWord_uniform_function

/-- info: 'LeanSphincs.Lifetime.viewCovered_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewCovered_mono

/-- info: 'LeanSphincs.Lifetime.viewCovered_ofFn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.viewCovered_ofFn_iff

/-- info: 'LeanSphincs.Lifetime.probEvent_uniformDisclosureSet_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_uniformDisclosureSet_function

/-- info: 'LeanSphincs.Lifetime.evalDist_selectedLeaves_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_selectedLeaves_uniform

/-- info: 'LeanSphincs.Lifetime.functionCovered_selected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.functionCovered_selected_iff

/-- info: 'LeanSphincs.Lifetime.hitPosition_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.hitPosition_card

/-- info: 'LeanSphincs.Lifetime.probEvent_functionCovered_fixed_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_functionCovered_fixed_indices

/-- info: 'LeanSphincs.Lifetime.evalDist_uniform_views_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.evalDist_uniform_views_split

/-- info: 'LeanSphincs.Lifetime.probEvent_uniformDisclosureSet_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_uniformDisclosureSet_covered

/-- info: 'LeanSphincs.Lifetime.freshDisclosureCoverage_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.freshDisclosureCoverage_bound

/-- info: 'LeanSphincs.Lifetime.signingFreshCoverage_after_keygen_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signingFreshCoverage_after_keygen_bound

/-- info: 'LeanSphincs.Lifetime.signingLifetimeBound_of_fors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.signingLifetimeBound_of_fors

/-- info: 'LeanSphincs.Lifetimes.requested_signing_lifetime_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetimes.requested_signing_lifetime_bounds

/-- info: 'LeanSphincs.Security.erase_countedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.erase_countedRun

/-- info: 'LeanSphincs.Security.mem_support_uncounted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.mem_support_uncounted_iff

/-- info: 'LeanSphincs.Security.experiment_eq_countedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.experiment_eq_countedRun

/-- info: 'LeanSphincs.Security.erase_experiment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.erase_experiment

/-- info: 'LeanSphincs.Security.forgeAdvantage_eq_uncounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.forgeAdvantage_eq_uncounted

/-- info: 'LeanSphincs.Security.hashQueryBound_full_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.hashQueryBound_full_run

/-- info: 'LeanSphincs.Security.world_query_support_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.world_query_support_cache_le

/-- info: 'LeanSphincs.Security.world_support_cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.world_support_cache_le

/-- info: 'LeanSphincs.Security.run_gameCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.run_gameCore

/-- info: 'LeanSphincs.Security.success_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.success_witness

/-- info: 'LeanSphincs.Security.experiment_success_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.experiment_success_witness

/-- info: 'LeanSphincs.Security.SuccessWitness.cache_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.cache_le

/-- info: 'LeanSphincs.Security.SuccessWitness.replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.replay

/-- info: 'LeanSphincs.Security.hash_support_queriedInputs_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.hash_support_queriedInputs_cached

/-- info: 'LeanSphincs.Security.SuccessWitness.verifier_inputs_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.verifier_inputs_cached

/-- info: 'LeanSphincs.Security.SuccessWitness.replay_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.replay_with

/-- info: 'LeanSphincs.Security.SuccessWitness.reference_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.reference_classification

/-- info: 'LeanSphincs.Security.experiment_reference_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.experiment_reference_classification

/-- info: 'LeanSphincs.Security.loggedProgram_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.loggedProgram_pure

/-- info: 'LeanSphincs.Security.loggedProgram_world_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.loggedProgram_world_query

/-- info: 'LeanSphincs.Security.loggedProgram_sign_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.loggedProgram_sign_query

/-- info: 'LeanSphincs.Security.logged_response_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.logged_response_support

/-- info: 'LeanSphincs.Security.SuccessWitness.logged_response_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.logged_response_support

/-- info: 'LeanSphincs.Security.SuccessWitness.logged_signature_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.logged_signature_replay

/-- info: 'LeanSphincs.Security.SuccessWitness.same_randomness_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.same_randomness_exception

/-- info: 'LeanSphincs.Security.SuccessWitness.cached_tree_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.cached_tree_classification

/-- info: 'LeanSphincs.Security.TreeException.cached_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.TreeException.cached_witness

/-- info: 'LeanSphincs.Security.SeedGuess.seedHit_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.seedHit_unique

/-- info: 'LeanSphincs.Security.SeedGuess.parseSeed_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.parseSeed_eq_some_iff

/-- info: 'LeanSphincs.Security.SeedGuess.parseSeed_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.parseSeed_keygen

/-- info: 'LeanSphincs.Security.SeedGuess.parseSeed_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.parseSeed_verifier

/-- info: 'LeanSphincs.Security.SeedGuess.seedHit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.seedHit_probability_le

/-- info: 'LeanSphincs.Security.SeedGuess.seedHitLog_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.seedHitLog_probability_le

/-- info: 'LeanSphincs.Security.SeedGuess.adaptive_seed_guess_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.adaptive_seed_guess_bound

/-- info: 'LeanSphincs.Security.SeedGuess.initialized_adaptive_seed_guess_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedGuess.initialized_adaptive_seed_guess_bound

/-- info: 'LeanSphincs.Security.SeedModel.secretDomain_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.secretDomain_injective

/-- info: 'LeanSphincs.Security.SeedModel.secretDomain_ne_parameter' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.secretDomain_ne_parameter

/-- info: 'LeanSphincs.Security.SeedModel.secretDomain_complete' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.secretDomain_complete

/-- info: 'LeanSphincs.Security.SeedModel.secretInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.secretInput_injective

/-- info: 'LeanSphincs.Security.SeedModel.secretInput_ne_parameterInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.secretInput_ne_parameterInput

/-- info: 'LeanSphincs.Security.SeedModel.programCache_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.programCache_parameter

/-- info: 'LeanSphincs.Security.SeedModel.programCache_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.programCache_secret

/-- info: 'LeanSphincs.Security.SeedModel.programCache_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.programCache_other

/-- info: 'LeanSphincs.Security.SeedModel.programCache_agreeOutside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.programCache_agreeOutside

/-- info: 'LeanSphincs.Security.SeedModel.programCache_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.programCache_verifier

/-- info: 'LeanSphincs.Security.SeedModel.programCache_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.programCache_extends

/-- info: 'LeanSphincs.Security.SeedModel.programCache_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.programCache_agrees

/-- info: 'LeanSphincs.Security.SeedModel.preparedAgreement_of_programCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.preparedAgreement_of_programCache

/-- info: 'LeanSphincs.Security.SeedModel.preparedOracle_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.preparedOracle_agreement

/-- info: 'LeanSphincs.Security.SeedModel.preparedOracle_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.preparedOracle_outside

/-- info: 'LeanSphincs.Security.SeedModel.preparedOracle_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.preparedOracle_verifier

/-- info: 'LeanSphincs.Security.SeedModel.eval_parameter_prepared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.eval_parameter_prepared

/-- info: 'LeanSphincs.Security.SeedModel.eval_secret_prepared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.eval_secret_prepared

/-- info: 'LeanSphincs.Security.SeedModel.eval_tweakableHash_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.eval_tweakableHash_prepared

/-- info: 'LeanSphincs.Security.SeedModel.material_seed_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedModel.material_seed_swap

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_iff_no_defects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_iff_no_defects

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_unrelated_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_unrelated_query

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_fresh_first_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_fresh_first_iff

/-- info: 'LeanSphincs.Lifetime.reuseInvariant_rejected_second_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.reuseInvariant_rejected_second_query

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_fresh_second_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_fresh_second_iff

/-- info: 'LeanSphincs.Lifetime.globalReuseInvariant_fresh_query_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.globalReuseInvariant_fresh_query_iff

/-- info: 'LeanSphincs.Lifetime.query_preserves_globalReuse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.query_preserves_globalReuse_iff

/-- info: 'LeanSphincs.Lifetime.probEvent_query_breaks_globalReuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_query_breaks_globalReuse

/-- info: 'LeanSphincs.Lifetime.probEvent_fresh_first_breaks_globalReuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_fresh_first_breaks_globalReuse

/-- info: 'LeanSphincs.Lifetime.probEvent_fresh_second_breaks_globalReuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_fresh_second_breaks_globalReuse

/-- info: 'LeanSphincs.Lifetime.auditedInterleavingStep_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.auditedInterleavingStep_preserves

/-- info: 'LeanSphincs.Lifetime.goodInterleavingPrefix_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.goodInterleavingPrefix_preserves

/-- info: 'LeanSphincs.Lifetime.run_messageDigest_cached_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.run_messageDigest_cached_second

/-- info: 'LeanSphincs.Lifetime.probEvent_messageDigest_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_messageDigest_candidate

/-- info: 'LeanSphincs.Lifetime.candidatePrice_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.candidatePrice_le_one

/-- info: 'LeanSphincs.Lifetime.probEvent_adaptive_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Lifetime.probEvent_adaptive_candidate

/-- info: 'LeanSphincs.Security.Unsigned.valid_has_two_step_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Unsigned.valid_has_two_step_digit

/-- info: 'LeanSphincs.Security.Unsigned.endpoints_twoEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Unsigned.endpoints_twoEdge

/-- info: 'LeanSphincs.Security.Unsigned.otsLeaf_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Unsigned.otsLeaf_classification

/-- info: 'LeanSphincs.Security.Unsigned.accepted_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Unsigned.accepted_classification

/-- info: 'LeanSphincs.Security.SuccessWitness.reference_free_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SuccessWitness.reference_free_classification

/-- info: 'LeanSphincs.Security.Prefix.input_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.input_injective

/-- info: 'LeanSphincs.Security.Prefix.parse_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.parse_some_iff

/-- info: 'LeanSphincs.Security.Prefix.parse_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.parse_input

/-- info: 'LeanSphincs.Security.Prefix.split_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.split_combine

/-- info: 'LeanSphincs.Security.Prefix.truncate_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.truncate_combine

/-- info: 'LeanSphincs.Security.Prefix.combine_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.combine_split

/-- info: 'LeanSphincs.Security.Prefix.answer_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.answer_input

/-- info: 'LeanSphincs.Security.Prefix.answer_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.answer_outside

/-- info: 'LeanSphincs.Security.Prefix.answer_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.answer_original

/-- info: 'LeanSphincs.Security.Prefix.lows_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.lows_answer

/-- info: 'LeanSphincs.Security.Prefix.evaluate_lows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.evaluate_lows

/-- info: 'LeanSphincs.Security.Prefix.evaluate_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.evaluate_answer

/-- info: 'LeanSphincs.Security.Prefix.eval_answer_of_avoids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.eval_answer_of_avoids

/-- info: 'LeanSphincs.Security.Prefix.replaceSecret_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceSecret_self

/-- info: 'LeanSphincs.Security.Prefix.replaceSecret_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceSecret_twice

/-- info: 'LeanSphincs.Security.Prefix.replaceSecret_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.replaceSecret_current

/-- info: 'LeanSphincs.Security.Prefix.uniform_secrets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.uniform_secrets

/-- info: 'LeanSphincs.Security.Prefix.uniform_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.uniform_rows

/-- info: 'LeanSphincs.Security.Prefix.tableCell_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.tableCell_injective

/-- info: 'LeanSphincs.Security.Prefix.joinFinite_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.joinFinite_prefix

/-- info: 'LeanSphincs.Security.Prefix.uniform_finite_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.Prefix.uniform_finite_table

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_independent_uniform_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_independent_uniform_pair

/-- info: 'LeanSphincs.Security.SeedCoupling.cacheFin_apply_of_not_mem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.cacheFin_apply_of_not_mem

/-- info: 'LeanSphincs.Security.SeedCoupling.cacheFin_apply' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.cacheFin_apply

/-- info: 'LeanSphincs.Security.SeedCoupling.run_sequenceFin_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.run_sequenceFin_fresh

/-- info: 'LeanSphincs.Security.SeedCoupling.sequenceFin_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.sequenceFin_map

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_sequenceFin_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_sequenceFin_congr

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_sequenceFin_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_sequenceFin_uniform

/-- info: 'LeanSphincs.Security.SeedCoupling.cacheTable_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.cacheTable_apply

/-- info: 'LeanSphincs.Security.SeedCoupling.cacheTable_apply_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.cacheTable_apply_of_not_mem

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_queryTable_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_queryTable_fresh

/-- info: 'LeanSphincs.Security.SeedCoupling.secretInputs_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.secretInputs_injective

/-- info: 'LeanSphincs.Security.SeedCoupling.secretInputs_ne_parameter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.secretInputs_ne_parameter

/-- info: 'LeanSphincs.Security.SeedCoupling.cacheTable_eq_programCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.cacheTable_eq_programCache

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_prepareMaterial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_prepareMaterial

/-- info: 'LeanSphincs.Security.SeedCoupling.run'_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.run'_query_bind

/-- info: 'LeanSphincs.Security.SeedCoupling.cacheQuery_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.cacheQuery_comm

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_presample_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_presample_fresh

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_presample_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_presample_query

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_presample_computation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_presample_computation

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_prepared_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_prepared_continuation

/-- info: 'LeanSphincs.Security.SeedCoupling.simulateQ_countHashQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.simulateQ_countHashQueries

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_prepared_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_prepared_counted

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_seeded_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_seeded_prepared

/-- info: 'LeanSphincs.Security.SeedCoupling.countHashQueries_query_bind' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.countHashQueries_query_bind

/-- info: 'LeanSphincs.Security.SeedCoupling.countHashQueries_lift_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.countHashQueries_lift_prob

/-- info: 'LeanSphincs.Security.SeedCoupling.countHashQueries_sampling_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.countHashQueries_sampling_bind

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_seeded_prepared_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_seeded_prepared_counted

/-- info: 'LeanSphincs.Security.SeedCoupling.gameCore_eq_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.gameCore_eq_sampling

/-- info: 'LeanSphincs.Security.SeedCoupling.evalDist_experiment_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.evalDist_experiment_prepared

/-- info: 'LeanSphincs.Security.SeedCoupling.preparedExperiment_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.preparedExperiment_hashQueryBound

/-- info: 'LeanSphincs.Security.SeedCoupling.forgeAdvantage_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.forgeAdvantage_prepared

/-- info: 'LeanSphincs.Security.SeedCoupling.programCache_cacheQuery_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.programCache_cacheQuery_outside

/-- info: 'LeanSphincs.Security.SeedCoupling.run_query_programCache_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.run_query_programCache_outside

/-- info: 'LeanSphincs.Security.SeedCoupling.stopBeforeSeed_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.stopBeforeSeed_pure

/-- info: 'LeanSphincs.Security.SeedCoupling.stopBeforeSeed_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.stopBeforeSeed_query_bind

/-- info: 'LeanSphincs.Security.SeedCoupling.run_stopBeforeSeed_programCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.run_stopBeforeSeed_programCache

/-- info: 'LeanSphincs.Security.SeedCoupling.run'_stopBeforeSeed_programCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.SeedCoupling.run'_stopBeforeSeed_programCache

/-- info: 'LeanSphincs.Security.countedRun_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.countedRun_pure

/-- info: 'LeanSphincs.Security.countedRun_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.countedRun_query_bind

/-- info: 'LeanSphincs.Security.world_query_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.world_query_failure

/-- info: 'LeanSphincs.Security.world_query_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.world_query_mass

/-- info: 'LeanSphincs.Security.countedRun_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.countedRun_failure

/-- info: 'LeanSphincs.Security.countedRun_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.countedRun_mass

/-- info: 'LeanSphincs.Security.expectedHashCost_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.expectedHashCost_pure

/-- info: 'LeanSphincs.Security.expectedHashCost_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.expectedHashCost_query_bind

/-- info: 'LeanSphincs.Security.expectedHashCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.expectedHashCost_le

/-- info: 'LeanSphincs.Security.expected_potential_le_hashCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.expected_potential_le_hashCost

/-- info: 'LeanSphincs.Security.probEvent_le_expected_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.probEvent_le_expected_potential

/-- info: 'LeanSphincs.Security.expected_game_hashCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.expected_game_hashCost_le

/-- info: 'LeanSphincs.Security.forgeAdvantage_le_of_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanSphincs.Security.forgeAdvantage_le_of_potential
