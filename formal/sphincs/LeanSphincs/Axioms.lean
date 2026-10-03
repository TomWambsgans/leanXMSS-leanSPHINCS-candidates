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

/-- info: 'LeanSphincs.Completeness.randomizedDigest_preserves_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
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

/-- info: 'LeanSphincs.Security.probEvent_messageDigest_cached_first_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
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
